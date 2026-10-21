#!/usr/bin/env node
// Takes in one paper shared through the Worker (.github/workflows/ingest.yml runs it):
//   WORKER_URL=… INGEST_SECRET=… TRUSTED_SHARERS=… GH_TOKEN=… node checks/ingest.mjs --id <upload id>
// in a checkout of main whose origin it may push to.
//   1. The upload's record and archive are fetched from the Worker; the archive must be the one the
//      manifest names (size, sha256), and the upload must be confirmed by its sharer (`submitted`).
//   2. The archive is read in memory (checks/tar.mjs): regular files only, exactly the manifest's,
//      each of the size and hash it names.
//   3. A slug someone else shared is refused (by GitHub account id; by login for a paper shared
//      before ids were recorded).
//   4. The folder is written in a scratch directory with share.json, and must pass check_paper.
//   5. A problem anywhere: the result is `refused`, with the problems; the checkout is not touched.
//   6. A trusted sharer's paper (TRUSTED_SHARERS) is committed on main and the site rebuilt
//      (pages.yml); anyone else's goes on a branch, as a pull request for the owner to merge.
// The result is posted back to the Worker, where the sharer's tool reads it.
// Nothing of the archive is run: files are written as data (mode 644), and git and gh are called
// without a shell, with names only from the manifest after checks/tar.mjs's path rule.
import { createHash } from "node:crypto";
import { spawnSync } from "node:child_process";
import { cpSync, existsSync, mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import os from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { checkPaper, GITHUB_LOGIN, MAX_FILE_BYTES, MAX_FILES, MAX_TOTAL_BYTES, SLUG } from "./check_paper.mjs";
import { pathProblem, readTarGz } from "./tar.mjs";
import { trustedSharer } from "./trusted_sharer.mjs";

export const DEFAULT_WORKER_URL = "https://theoremchecker-share.comments-worker.workers.dev";
export const DEFAULT_SITE_URL = "https://jiyuan-tan.github.io/PaperFormalizerPapers/";
export const UPLOAD_ID = /^[a-z2-7]{26}$/u;
export const MAX_ARCHIVE_BYTES = 64 * 1024 * 1024;
const SHA256 = /^[0-9a-f]{64}$/u;
const BOT = ["-c", "user.name=github-actions[bot]", "-c", "user.email=41898282+github-actions[bot]@users.noreply.github.com", "-c", "commit.gpgsign=false"];
/** Pushes that lose a race with another push to main are tried again, on the new main. */
const PUSH_TRIES = 5;
/** What the Worker takes in a result: at most this many problems, each at most this long. */
const MAX_PROBLEMS = 200;
const MAX_PROBLEM_CHARS = 2000;

const sha256 = (b) => createHash("sha256").update(b).digest("hex");

/** Runs `cmd` with `args`, no shell. */
export function runCommand(cmd, args, opts = {}) {
  const r = spawnSync(cmd, args, { cwd: opts.cwd, env: opts.env ?? process.env, encoding: "utf8", maxBuffer: 64 * 1024 * 1024 });
  return { code: r.status ?? 1, out: r.stdout ?? "", err: r.stderr ?? (r.error ? String(r.error) : "") };
}

/** What is wrong with the manifest the sharer's tool sent (the Worker checked it too). Pure. */
export function manifestProblems(m) {
  if (!m || typeof m !== "object" || Array.isArray(m)) return ["the manifest is not an object"];
  const problems = [];
  if (m.v !== 1) problems.push(`the manifest's version is ${JSON.stringify(m.v)}, not 1`);
  if (typeof m.slug !== "string" || !SLUG.test(m.slug)) problems.push(`the slug ${JSON.stringify(m.slug)} is not a slug (lower-case letters, digits, _ and -)`);
  if (typeof m.title !== "string" || m.title.length > 300) problems.push("the title is not a string of at most 300 characters");
  else if (/\p{Cc}/u.test(m.title)) problems.push("the title holds a control character (a line break included)");
  if (typeof m.authors !== "string" || m.authors.length > 1000) problems.push("the authors are not a string of at most 1000 characters");
  else if (/\p{Cc}/u.test(m.authors)) problems.push("the authors hold a control character (a line break included)");
  if (m.arxiv !== null && typeof m.arxiv !== "string") problems.push("arxiv is neither a string nor null");
  if (!m.archive || !Number.isSafeInteger(m.archive.size) || m.archive.size <= 0 || m.archive.size > MAX_ARCHIVE_BYTES || !SHA256.test(m.archive.sha256 ?? "")) problems.push(`the archive is not named by a size of at most ${MAX_ARCHIVE_BYTES} bytes and a sha256`);
  if (!Array.isArray(m.files) || m.files.length === 0) return [...problems, "the manifest lists no file"];
  if (m.files.length > MAX_FILES) problems.push(`the manifest lists ${m.files.length} files, over the limit of ${MAX_FILES}`);
  let total = 0;
  const seen = new Set();
  for (const f of m.files) {
    const shown = JSON.stringify(f?.path);
    const bad = pathProblem(f?.path);
    if (bad) { problems.push(`${shown}: ${bad}`); continue; }
    if (seen.has(f.path)) problems.push(`${shown}: listed twice`);
    seen.add(f.path);
    if (!Number.isSafeInteger(f.size) || f.size < 0 || f.size > MAX_FILE_BYTES) problems.push(`${shown}: its size is not a number of bytes up to ${MAX_FILE_BYTES}`);
    else total += f.size;
    if (!SHA256.test(f.sha256 ?? "")) problems.push(`${shown}: no sha256`);
  }
  if (seen.has("share.json")) problems.push(`"share.json": written by the registry, not part of a bundle`);
  if (total > MAX_TOTAL_BYTES) problems.push(`the files hold ${total} bytes, over the limit of ${MAX_TOTAL_BYTES}`);
  return problems;
}

/** What makes the archive's files other than the manifest's; empty when they are the same. Pure. */
export function archiveProblems(manifest, files) {
  const problems = [];
  const listed = new Map(manifest.files.map((f) => [f.path, f]));
  for (const [p, bytes] of files) {
    const f = listed.get(p);
    if (!f) problems.push(`${JSON.stringify(p)}: in the archive, not in the manifest`);
    else if (bytes.length !== f.size || sha256(bytes) !== f.sha256) problems.push(`${JSON.stringify(p)}: not the file the manifest names (size or sha256)`);
  }
  for (const p of listed.keys()) if (!files.has(p)) problems.push(`${JSON.stringify(p)}: in the manifest, not in the archive`);
  // a path that is also a folder of another cannot be written; two that differ in case only collide
  // on a checkout that ignores case
  const folders = new Set();
  for (const p of files.keys()) {
    const parts = p.split("/");
    for (let i = 1; i < parts.length; i++) folders.add(parts.slice(0, i).join("/"));
  }
  const byCase = new Map();
  for (const p of files.keys()) {
    if (folders.has(p)) problems.push(`${JSON.stringify(p)}: a file and a folder of the same name`);
    const k = p.toLowerCase();
    if (byCase.has(k)) problems.push(`${JSON.stringify(p)}: differs from ${JSON.stringify(byCase.get(k))} in case only`);
    else byCase.set(k, p);
  }
  return problems;
}

/** `problems` as the Worker takes them: at most `MAX_PROBLEMS`, each cut to `MAX_PROBLEM_CHARS`. Pure. */
export function cappedProblems(problems) {
  const cut = (x) => (x.length > MAX_PROBLEM_CHARS ? `${x.slice(0, MAX_PROBLEM_CHARS - 1)}…` : x);
  return problems.length > MAX_PROBLEMS ? [...problems.slice(0, MAX_PROBLEMS - 1).map(cut), `… and ${problems.length - MAX_PROBLEMS + 1} more`] : problems.map(cut);
}

/** `s` as a Markdown code span: nothing in it is a mention, a link or HTML. Pure. */
export const codeSpan = (s) => `\`${String(s).replace(/`/gu, "'")}\``;

/** Who shared the paper of `dir` (its share.json), or null when nobody has. */
function sharerOf(dir) {
  try {
    const s = JSON.parse(readFileSync(path.join(dir, "share.json"), "utf8"));
    return { login: s.shared_by, id: s.shared_by_id ?? null };
  } catch {
    return null;
  }
}

/** The problem with `identity` taking the paper of `dir`; null when it may (a new paper, or its own). */
export function ownerProblem(dir, slug, identity) {
  const was = sharerOf(dir);
  if (was === null) return existsSync(dir) ? `the slug ${slug} is taken (papers/${slug} has no readable share.json)` : null;
  const same = was.id !== null ? String(was.id) === String(identity.id) : String(was.login).toLowerCase() === String(identity.login).toLowerCase();
  return same ? null : `the slug ${slug} is taken by @${was.login}: share it under another slug`;
}

/**
 * Takes in upload `id`. `root`: the checkout of main; `fetch`, `run`, `now`: injectable for tests.
 * Returns the result it posted (or, when the upload is not waiting to be taken in, the reason,
 * posted nowhere: a delivery of an upload already handled changes nothing).
 */
export async function ingest({ id, root, workerUrl = DEFAULT_WORKER_URL, siteUrl = DEFAULT_SITE_URL, secret, trusted = "", fetch: fetchImpl = fetch, run = runCommand, now = () => new Date(), log = console.log }) {
  if (!UPLOAD_ID.test(id ?? "")) throw new Error(`not an upload id: ${JSON.stringify(id)}`);
  if (!secret) throw new Error("INGEST_SECRET is not set");
  const base = `${workerUrl.replace(/\/+$/u, "")}/api/ingest/${id}`;
  const auth = { Authorization: `Bearer ${secret}` };
  const get = async (url) => {
    const r = await fetchImpl(url, { headers: auth });
    if (!r.ok) throw new Error(`${url}: HTTP ${r.status}`);
    return r;
  };
  const post = async (result) => {
    if (result.problems) result = { ...result, problems: cappedProblems(result.problems) };
    const r = await fetchImpl(`${base}/result`, { method: "POST", headers: { ...auth, "Content-Type": "application/json" }, body: JSON.stringify(result) });
    if (!r.ok) throw new Error(`posting the result: HTTP ${r.status}`);
    log(`${id}: ${result.kind}${result.url ? ` ${result.url}` : ""}${result.pr_url ? ` ${result.pr_url}` : ""}${result.problems ? `\n  ${result.problems.map((x) => x.replace(/\s*[\r\n]+\s*/gu, " ")).join("\n  ")}` : ""}`);
    return result;
  };

  const meta = await (await get(base)).json();
  if (meta?.status !== "submitted") {
    log(`${id}: its status is ${JSON.stringify(meta?.status)}, not "submitted": nothing to take in`);
    return { kind: "skipped", reason: `status ${JSON.stringify(meta?.status)}` };
  }
  const refused = (problems) => ({ kind: "refused", problems });
  let stageRoot = null;
  const decide = async () => {
    const m = meta.manifest;
    const identity = meta.identity ?? {};
    const mp = manifestProblems(m);
    if (!identity || !GITHUB_LOGIN.test(String(identity.login ?? "")) || !(Number.isSafeInteger(identity.id) && identity.id > 0)) mp.push("the upload carries no signed-in GitHub account");
    if (mp.length > 0) return refused(mp);

    const archive = Buffer.from(await (await get(`${base}/archive`)).arrayBuffer());
    if (archive.length !== m.archive.size || sha256(archive) !== m.archive.sha256) return refused(["the archive is not the one the manifest names (size or sha256)"]);
    const { files, problems: tp } = readTarGz(archive);
    if (tp.length > 0) return refused(tp);
    const ap = archiveProblems(m, files);
    if (ap.length > 0) return refused(ap);

    // the folder, written and checked away from the checkout
    const slug = m.slug;
    stageRoot = mkdtempSync(path.join(os.tmpdir(), "ingest-"));
    const stage = path.join(stageRoot, slug);
    for (const [p, bytes] of files) {
      mkdirSync(path.dirname(path.join(stage, p)), { recursive: true });
      writeFileSync(path.join(stage, p), bytes, { mode: 0o644 });
    }
    const share = { shared_by: identity.login, shared_by_id: identity.id, shared_at: now().toISOString(), arxiv: m.arxiv ?? null };
    writeFileSync(path.join(stage, "share.json"), `${JSON.stringify(share, null, 2)}\n`, { mode: 0o644 });
    const dest = path.join(root, "papers", slug);
    const owner = ownerProblem(dest, slug, identity);
    if (owner) return refused([owner]);
    const cp = checkPaper(stage);
    if (cp.length > 0) return refused(cp);

    const git = (...args) => {
      const r = run("git", [...BOT, ...args], { cwd: root });
      if (r.code !== 0) throw new Error(`git ${args.join(" ")}: ${r.err.trim() || r.out.trim()}`);
      return r.out.trim();
    };
    const written = [...files.keys(), "share.json"].map((p) => `papers/${slug}/${p}`).sort();
    const commit = () => {
      rmSync(dest, { recursive: true, force: true });
      cpSync(stage, dest, { recursive: true });
      // -f: a bundle's folder named like an ignored one (dist/, node_modules/) is the bundle's too
      git("add", "-A", "-f", "--", `papers/${slug}`);
      const staged = git("ls-files", "--cached", "--", `papers/${slug}`).split("\n").filter(Boolean).sort();
      if (staged.join("\n") !== written.join("\n")) throw new Error(`the commit would not hold the folder as written (${staged.length} of ${written.length} files staged)`);
      if (run("git", ["diff", "--cached", "--quiet"], { cwd: root }).code === 0) return false;
      git("commit", "-q", "-m", `Share ${slug} by @${identity.login}\n\nShared-by: ${identity.login} ${identity.id}`);
      return true;
    };
    const restore = () => {
      run("git", ["reset", "-q", "--hard", "origin/main"], { cwd: root });
      run("git", ["clean", "-fdq", "--", `papers/${slug}`], { cwd: root });
    };
    const pageUrl = `${siteUrl.replace(/\/*$/u, "/")}papers/${slug}/`;

    if (trustedSharer(identity.login, trusted)) {
      for (let attempt = 1; ; attempt++) {
        git("fetch", "-q", "origin", "main");
        git("checkout", "-q", "main");
        git("reset", "-q", "--hard", "origin/main");
        const again = ownerProblem(dest, slug, identity); // main may have moved since the check above
        if (again) return refused([again]);
        if (!commit()) break; // the same folder is already on main
        const pushed = run("git", ["push", "-q", "origin", "HEAD:main"], { cwd: root });
        if (pushed.code === 0) break;
        if (attempt >= PUSH_TRIES) { restore(); throw new Error(`git push: ${pushed.err.trim()}`); }
      }
      const pages = run("gh", ["workflow", "run", "pages.yml", "--ref", "main"], { cwd: root });
      if (pages.code !== 0) log(`${id}: the site was not rebuilt (gh workflow run: ${pages.err.trim()}); it is on main, and the next push rebuilds it`);
      return { kind: "published", url: pageUrl };
    }

    const branch = `share/${slug}-${id.slice(0, 8)}`;
    // another account's share of this slug may be waiting for review: the merge of either would
    // replace the other's paper, which the check of main above cannot see
    const waiting = git("ls-remote", "--heads", "origin", `refs/heads/share/${slug}-*`).split("\n").map((l) => l.split("\t")[1]).filter((r) => r && new RegExp(`^refs/heads/share/${slug}-[a-z2-7]{8}$`, "u").test(r) && r !== `refs/heads/${branch}`);
    for (const ref of waiting) {
      git("fetch", "-q", "origin", ref);
      const shown = run("git", ["show", `FETCH_HEAD:papers/${slug}/share.json`], { cwd: root });
      let other = null;
      try { other = JSON.parse(shown.out).shared_by_id ?? null; } catch { other = null; }
      if (String(other) !== String(identity.id)) return refused([`the slug ${slug} is waiting for review under another account: share it under another slug`]);
    }
    git("fetch", "-q", "origin", "main");
    git("checkout", "-q", "-B", branch, "origin/main");
    try {
      commit();
      git("push", "-q", "origin", `HEAD:refs/heads/${branch}`);
    } finally {
      run("git", ["checkout", "-q", "main"], { cwd: root });
      run("git", ["reset", "-q", "--hard", "HEAD"], { cwd: root });
    }
    // the title and authors are the sharer's words: code spans, so no heading, link, HTML or @mention
    const body = [
      `Shared by @${identity.login} (account id ${identity.id}) through the Share button.`,
      "",
      `- Title: ${codeSpan(m.title || slug)}${m.authors ? `; authors: ${codeSpan(m.authors)}` : ""}`,
      `- ${m.files.length} files, ${m.files.reduce((a, f) => a + f.size, 0)} bytes${m.arxiv ? `, arXiv ${m.arxiv}` : ""}`,
      "",
      "The ingest checks passed: the archive is the manifest's, the folder passes check_paper and its seal holds.",
      `@${identity.login} is not in TRUSTED_SHARERS, so the paper waits for the owner: merging publishes it at ${pageUrl}`,
    ].join("\n");
    const pr = run("gh", ["pr", "create", "--base", "main", "--head", branch, "--title", `Share ${slug} by @${identity.login}`, "--body", body], { cwd: root });
    if (pr.code !== 0) throw new Error(`gh pr create: ${pr.err.trim()}`);
    const prUrl = pr.out.trim().split("\n").filter(Boolean).pop();
    return { kind: "review", pr_url: prUrl };
  };
  let result;
  try {
    result = await decide();
  } catch (err) {
    // the registry could not be updated: the sharer is told, and the run fails for the owner to see
    await post(refused([`the registry could not take the paper in (${err.message}); share it again later`])).catch(() => {});
    throw err;
  } finally {
    if (stageRoot) rmSync(stageRoot, { recursive: true, force: true });
  }
  return post(result);
}

if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  const i = process.argv.indexOf("--id");
  const id = i > 0 ? process.argv[i + 1] : undefined;
  if (!id) {
    console.error("Usage: WORKER_URL=… INGEST_SECRET=… [TRUSTED_SHARERS=…] node checks/ingest.mjs --id <upload id>");
    process.exit(2);
  }
  ingest({
    id,
    root: path.join(path.dirname(fileURLToPath(import.meta.url)), ".."),
    workerUrl: process.env.WORKER_URL || DEFAULT_WORKER_URL,
    siteUrl: process.env.SITE_URL || DEFAULT_SITE_URL,
    secret: process.env.INGEST_SECRET,
    trusted: process.env.TRUSTED_SHARERS ?? "",
  }).then(
    // a refusal is the sharer's to act on (their tool shows it), not a failure of the run
    () => process.exit(0),
    (err) => { console.error(err.message); process.exit(1); },
  );
}

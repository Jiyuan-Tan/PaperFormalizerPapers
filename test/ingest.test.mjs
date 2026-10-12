import assert from "node:assert/strict";
import { existsSync, mkdirSync, readFileSync, writeFileSync } from "node:fs";
import path from "node:path";
import { test } from "node:test";
import { ingest, runCommand } from "../checks/ingest.mjs";
import { copyFixture, filesOf, FIXTURE, git, manifestOf, reseal, SLUG, tarGz, tmp, writeJson } from "./helpers.mjs";

const ID = "abcdefghijklmnopqrstuvwxyz";
const SECRET = "s3cret";
const WORKER = "https://worker.test";
const ALICE = { login: "alice", id: 101 };
const has = (problems, re) => assert.ok(problems.some((p) => re.test(p)), `expected ${re} in:\n${problems.join("\n")}`);

/** The fixture paper as the tool sends it: every file of the bundle (share.json is the registry's). */
const bundle = () => filesOf(FIXTURE).filter(([p]) => p !== "share.json");

/** A registry: a bare origin with main, and a checkout of it (`root`); `seed(root)` adds to main first. */
function registry(seed = () => {}) {
  const dir = tmp();
  const origin = path.join(dir, "origin.git");
  git(dir, "init", "-q", "--bare", "-b", "main", origin);
  const root = path.join(dir, "root");
  git(dir, "clone", "-q", origin, root);
  mkdirSync(path.join(root, "papers"));
  writeFileSync(path.join(root, "papers", ".gitkeep"), "");
  seed(root);
  git(root, "add", "-A");
  git(root, "commit", "-q", "-m", "base");
  git(root, "push", "-q", "origin", "HEAD:main");
  return { root, origin, main: () => git(origin, "rev-parse", "main") };
}

/** The Worker as ingest sees it: the upload's record and archive, and the results posted. */
function worker({ files = bundle(), entries = files, manifest, status = "submitted", identity = ALICE, id = ID } = {}) {
  const archive = tarGz(entries);
  const w = { meta: { id, status, manifest: manifest ?? manifestOf(files, archive), identity, created_at: "2026-10-12T00:00:00Z", submitted_at: "2026-10-12T00:01:00Z" }, archive, results: [] };
  w.fetch = async (url, opts = {}) => {
    assert.equal(opts.headers?.Authorization, `Bearer ${SECRET}`);
    const base = `${WORKER}/api/ingest/${id}`;
    if (url === base && !opts.method) return new Response(JSON.stringify(w.meta));
    if (url === `${base}/archive`) return new Response(w.archive);
    if (url === `${base}/result` && opts.method === "POST") { w.results.push(JSON.parse(opts.body)); return new Response("{}"); }
    return new Response("not found", { status: 404 });
  };
  return w;
}

/** git for real (against the local origin); gh faked and recorded. */
function runner(onGit = () => {}) {
  const gh = [];
  const run = (cmd, args, opts) => {
    if (cmd === "gh") { gh.push(args); return { code: 0, out: args[0] === "pr" ? "https://github.com/o/r/pull/7\n" : "", err: "" }; }
    onGit(args);
    return runCommand(cmd, args, opts);
  };
  return { run, gh };
}

const go = (reg, w, r, extra = {}) => ingest({ id: ID, root: reg.root, workerUrl: WORKER, siteUrl: "https://site.test/papers-site", secret: SECRET, fetch: w.fetch, run: r.run, now: () => new Date("2026-10-12T08:00:00Z"), log: () => {}, ...extra });
const clean = (root) => git(root, "status", "--porcelain");

test("a trusted sharer's paper goes on main, with share.json, and the site is rebuilt", async () => {
  const reg = registry();
  const w = worker();
  const r = runner();
  const res = await go(reg, w, r, { trusted: "bob, Alice" });
  assert.deepEqual(res, { kind: "published", url: "https://site.test/papers-site/papers/cns_simple_dml/" });
  assert.deepEqual(w.results, [res]);
  const share = JSON.parse(git(reg.origin, "show", `main:papers/${SLUG}/share.json`));
  assert.deepEqual(share, { shared_by: "alice", shared_by_id: 101, shared_at: "2026-10-12T08:00:00.000Z", arxiv: null });
  assert.equal(git(reg.origin, "show", `main:papers/${SLUG}/lean/Check.lean`), readFileSync(path.join(FIXTURE, "lean", "Check.lean"), "utf8").trim());
  assert.match(git(reg.origin, "log", "-1", "--format=%an <%ae>%n%B", "main"), /^github-actions\[bot\] <41898282\+github-actions\[bot\]@users\.noreply\.github\.com>\nShare cns_simple_dml by @alice\n\nShared-by: alice 101/u);
  assert.equal(git(reg.origin, "ls-tree", "-r", "main", "--", `papers/${SLUG}`).split("\n").filter((l) => !l.startsWith("100644 blob")).length, 0);
  assert.deepEqual(r.gh, [["workflow", "run", "pages.yml", "--ref", "main"]]);
  assert.equal(clean(reg.root), "");

  // shared again, unchanged: nothing to commit, still published
  const before = reg.main();
  const again = worker();
  assert.equal((await go(reg, again, runner(), { trusted: "*" })).kind, "published");
  assert.equal(reg.main(), before);
});

test("anyone else's paper waits for the owner: a branch and a pull request, main untouched", async () => {
  const reg = registry();
  const main = reg.main();
  const w = worker();
  const r = runner();
  const res = await go(reg, w, r, { trusted: "" });
  assert.deepEqual(res, { kind: "review", pr_url: "https://github.com/o/r/pull/7" });
  assert.deepEqual(w.results, [res]);
  assert.equal(reg.main(), main);
  const branch = `share/${SLUG}-${ID.slice(0, 8)}`;
  assert.equal(JSON.parse(git(reg.origin, "show", `${branch}:papers/${SLUG}/share.json`)).shared_by_id, 101);
  assert.equal(r.gh.length, 1);
  const [pr] = r.gh;
  assert.deepEqual(pr.slice(0, 7), ["pr", "create", "--base", "main", "--head", branch, "--title"]);
  assert.equal(pr[7], "Share cns_simple_dml by @alice");
  assert.match(pr[9], /not in TRUSTED_SHARERS/u);
  assert.equal(git(reg.root, "rev-parse", "--abbrev-ref", "HEAD"), "main");
  assert.equal(clean(reg.root), "");
});

test("a push that loses the race to main is tried again on the new main", async () => {
  const reg = registry();
  let raced = false;
  const r = runner((args) => {
    if (raced || !args.includes("push")) return;
    raced = true;
    const other = path.join(tmp(), "other");
    git(path.dirname(other), "clone", "-q", reg.origin, other);
    writeFileSync(path.join(other, "README.md"), "another push\n");
    git(other, "add", "-A");
    git(other, "commit", "-q", "-m", "meanwhile");
    git(other, "push", "-q", "origin", "HEAD:main");
  });
  const res = await go(reg, worker(), r, { trusted: "*" });
  assert.equal(res.kind, "published");
  assert.equal(git(reg.origin, "show", "main:README.md"), "another push");
  assert.ok(git(reg.origin, "show", `main:papers/${SLUG}/share.json`));
});

/** Refused with a problem matching `re`; nothing reaches origin, the checkout is left as it was. */
async function refused(opts, re, seed) {
  const reg = registry(seed);
  const main = reg.main();
  const w = worker(opts);
  const r = runner();
  const res = await go(reg, w, r, { trusted: "*" });
  assert.equal(res.kind, "refused");
  has(res.problems, re);
  assert.deepEqual(w.results, [res]);
  assert.equal(reg.main(), main);
  assert.equal(git(reg.origin, "branch", "--list"), "* main");
  assert.deepEqual(r.gh, []);
  assert.equal(clean(reg.root), "");
}

test("refused: the archive's files are not the manifest's", async () => {
  const files = bundle();
  const archive = tarGz(files);
  const m = manifestOf(files, archive);
  const changed = m.files.find((f) => f.path === "lean/Check.lean");
  changed.sha256 = "0".repeat(64);
  await refused({ files, manifest: m }, /"lean\/Check\.lean": not the file the manifest names/u);
  // an entry the manifest does not list
  await refused({ files, entries: [...files, ["lean/Extra.lean", Buffer.from("x")]] }, /"lean\/Extra\.lean": in the archive, not in the manifest/u);
  // a file the manifest lists that the archive lacks
  await refused({ files, entries: files.filter(([p]) => p !== "REPORT.md") }, /"REPORT\.md": in the manifest, not in the archive/u);
  // the archive is not the one the manifest names
  const other = manifestOf(files, archive);
  other.archive.sha256 = "f".repeat(64);
  await refused({ files, manifest: other }, /the archive is not the one the manifest names/u);
});

test("refused: an entry that is not a regular file, or a path out of the folder", async () => {
  const files = bundle();
  for (const [e, re] of [
    [{ path: "lean/link", type: "2", linkname: "/etc/passwd" }, /"lean\/link": a symbolic link/u],
    [{ path: "lean/dir", type: "5" }, /"lean\/dir": a directory/u],
    [{ path: "PaxHeader", type: "x", data: Buffer.from("30 path=../../escape\n") }, /a pax header/u],
    [["../escape.md", Buffer.from("x")], /"\.\.\/escape\.md": an empty, \. or \.\. segment/u],
  ]) await refused({ files, entries: [...files, e] }, re);
  // a manifest naming a path out of the folder
  const evil = [...files, ["../escape.md", Buffer.from("x")]];
  await refused({ files: evil, entries: files }, /"\.\.\/escape\.md": an empty, \. or \.\. segment/u);
});

test("refused: a slug someone else shared, by account id (a login can be taken over)", async () => {
  const seed = (id, login) => (root) => {
    mkdirSync(path.join(root, "papers", SLUG), { recursive: true });
    writeJson(path.join(root, "papers", SLUG, "share.json"), { shared_by: login, shared_by_id: id, shared_at: "2026-10-01", arxiv: null });
  };
  await refused({}, /the slug cns_simple_dml is taken by @mallory/u, seed(999, "mallory"));
  // the same login, another account: still taken
  await refused({}, /the slug cns_simple_dml is taken by @alice/u, seed(999, "alice"));
  // the same account under a new login takes its own paper back
  const reg = registry(seed(101, "alice-old"));
  assert.equal((await go(reg, worker(), runner(), { trusted: "*" })).kind, "published");
  // a paper shared before ids were recorded: by login
  const legacy = (login) => (root) => {
    mkdirSync(path.join(root, "papers", SLUG), { recursive: true });
    writeJson(path.join(root, "papers", SLUG, "share.json"), { shared_by: login, shared_at: "2026-10-01", arxiv: null });
  };
  await refused({}, /taken by @carol/u, legacy("carol"));
  assert.equal((await go(registry(legacy("Alice")), worker(), runner(), { trusted: "*" })).kind, "published");
});

test("refused: the folder fails check_paper, or the bundle carries share.json", async () => {
  const files = bundle().map(([p, b]) => [p, p === "lean/Check.lean" ? Buffer.from("-- tampered\n") : b]);
  await refused({ files }, /lean\/Check\.lean: changed after the seal was written/u);
  await refused({ files: [...bundle(), ["share.json", Buffer.from("{}")]] }, /"share\.json": written by the registry/u);
  await refused({ manifest: { ...manifestOf(bundle(), tarGz(bundle())), slug: "Bad Slug" } }, /is not a slug/u);
  await refused({ identity: { login: "alice" } }, /no signed-in GitHub account/u);
});

test("an upload not confirmed by its sharer, or already handled, is left alone", async () => {
  for (const status of ["awaiting_sign_in", "published", "refused"]) {
    const reg = registry();
    const w = worker({ status });
    const r = runner();
    const res = await go(reg, w, r, { trusted: "*" });
    assert.equal(res.kind, "skipped");
    assert.deepEqual(w.results, []);
    assert.deepEqual(r.gh, []);
    assert.ok(!existsSync(path.join(reg.root, "papers", SLUG)));
  }
  await assert.rejects(go(registry(), worker(), runner(), { id: "../../x" }), /not an upload id/u);
  await assert.rejects(go(registry(), worker(), runner(), { secret: "" }), /INGEST_SECRET is not set/u);
});

test("refused: a file and a folder of one name, or two paths differing in case only (no crash)", async () => {
  const files = bundle();
  await refused({ files: [...files, ["lean/Z", Buffer.from("x")], ["lean/Z/y.lean", Buffer.from("y")]] }, /"lean\/Z": a file and a folder of the same name/u);
  await refused({ files: [...files, ["lean/Case.lean", Buffer.from("x")], ["lean/case.lean", Buffer.from("y")]] }, /differs from .* in case only/u);
});

test("refused: a title or authors with a control character", async () => {
  const files = bundle();
  await refused({ files, manifest: manifestOf(files, tarGz(files), { title: "T\n\n## Approved" }) }, /title holds a control character/u);
});

test("a refusal with very many problems still reaches the sharer, cut to what the Worker takes", async () => {
  const files = bundle();
  const m = manifestOf(files, tarGz(files));
  for (let i = 0; i < 240; i++) m.files.push({ path: `lean/Missing${String(i).padStart(3, "0")}.lean`, size: 1, sha256: "0".repeat(64) });
  m.files.sort((a, b) => (a.path < b.path ? -1 : 1));
  const reg = registry();
  const w = worker({ files, manifest: m });
  const res = await go(reg, w, runner(), { trusted: "*" });
  assert.equal(res.kind, "refused");
  assert.equal(w.results[0].problems.length, 200);
  assert.equal(w.results[0].problems.at(-1), "… and 41 more");
});

test("a bundle folder named like an ignored one (dist/) is committed whole", async () => {
  const dir = copyFixture();
  mkdirSync(path.join(dir, "lean", "dist"), { recursive: true });
  writeFileSync(path.join(dir, "lean", "dist", "A.lean"), "-- in a folder named dist\n");
  reseal(dir, (seal) => { seal.files.push({ path: "lean/dist/A.lean" }); });
  const files = filesOf(dir).filter(([p]) => p !== "share.json");
  // a registry whose .gitignore is not anchored, as this one's was
  const reg = registry((root) => writeFileSync(path.join(root, ".gitignore"), "dist/\nnode_modules/\n"));
  const res = await go(reg, worker({ files }), runner(), { trusted: "*" });
  assert.equal(res.kind, "published", JSON.stringify(res));
  assert.equal(git(reg.origin, "show", `main:papers/${SLUG}/lean/dist/A.lean`), "-- in a folder named dist");
  // and this repository's own patterns are anchored to its root
  for (const line of readFileSync(path.join(import.meta.dirname, "..", ".gitignore"), "utf8").split("\n").filter(Boolean)) assert.match(line, /^\//u);
});

test("refused: a slug another account's share is waiting for review under; the same account may share again", async () => {
  const reg = registry();
  const BOB = { login: "bob", id: 202 };
  const first = await go(reg, worker(), runner(), { trusted: "" });
  assert.equal(first.kind, "review");
  const ID2 = "zyxwvutsrqponmlkjihgfedcba";
  const w2 = worker({ id: ID2, identity: BOB });
  const second = await go(reg, w2, runner(), { id: ID2, trusted: "" });
  assert.equal(second.kind, "refused");
  has(second.problems, /waiting for review under another account/u);
  const ID3 = "mmmmmmmmmmmmmmmmmmmmmmmmmm";
  const third = await go(reg, worker({ id: ID3 }), runner(), { id: ID3, trusted: "" });
  assert.equal(third.kind, "review");
});

test("the pull request shows the sharer's title and authors as code: no heading, HTML or @mention", async () => {
  const files = bundle();
  const m = manifestOf(files, tarGz(files), { title: "T** ## Reviewed and approved <!-- `x`", authors: "@octocat @torvalds" });
  const r = runner();
  const res = await go(registry(), worker({ files, manifest: m }), r, { trusted: "" });
  assert.equal(res.kind, "review");
  const body = r.gh[0][9];
  assert.ok(body.includes("Title: `T** ## Reviewed and approved <!-- 'x'`; authors: `@octocat @torvalds`"), body);
  assert.ok(!/^#/mu.test(body), "a heading in the body");
});

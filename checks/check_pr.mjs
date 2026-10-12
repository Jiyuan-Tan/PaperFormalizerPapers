#!/usr/bin/env node
// The rule a pull request must meet to merge itself:
//   PR_AUTHOR=<login> PR_AUTHOR_ID=<numeric id> node checks/check_pr.mjs <base> <head>
// run in a checkout of <head> (the working tree holds the pull request's files); <base> and <head>
// are commits of that repository. It passes when the pull request
//   - adds or changes files under exactly ONE folder papers/<slug>/, and nothing else;
//   - names its author in that folder's share.json (`shared_by` = PR_AUTHOR, and `shared_by_id`,
//     when it has one, = PR_AUTHOR_ID), and, when the paper is already in the registry, is from the
//     person who shared it (by account id when the registry's share.json has one: a login can be
//     renamed and taken by someone else);
//   - holds, in <head>'s tree, only plain non-executable files under that folder (git mode 100644:
//     no submodule, no symbolic link, no executable);
//   - holds a folder that passes check_paper.
// The pull request is DATA: this script and check_paper come from the base branch, git is asked for
// names only (no shell, no diff driver), and nothing of the pull request is run.
import { execFileSync } from "node:child_process";
import { readFileSync } from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { checkPaper, SLUG } from "./check_paper.mjs";

const git = (cwd, args) => execFileSync("git", args, { cwd, encoding: "utf8", maxBuffer: 64 * 1024 * 1024, stdio: ["ignore", "pipe", "pipe"] });

/** The paths the pull request changes: what <head> holds differently from where it left <base>. */
export function changedPaths(cwd, base, head) {
  return git(cwd, ["diff", "--name-only", "-z", "--no-renames", "--no-ext-diff", "--no-textconv", `${base}...${head}`, "--"]).split("\0").filter(Boolean);
}

/** The entries of `folder` in the tree of `head` that are not a plain non-executable file. The
 *  tree is what merges: a submodule entry is no file of the checkout, and a mode is the tree's. */
export function treeProblems(cwd, head, folder) {
  const problems = [];
  for (const entry of git(cwd, ["ls-tree", "-r", "-z", head, "--", folder]).split("\0").filter(Boolean)) {
    const [meta, file] = [entry.slice(0, entry.indexOf("\t")), entry.slice(entry.indexOf("\t") + 1)];
    const [mode, type] = meta.split(" ");
    if (mode === "100644" && type === "blob") continue;
    const what = mode === "160000" ? "a submodule" : mode === "120000" ? "a symbolic link" : mode === "100755" ? "an executable file" : `a ${type} of mode ${mode}`;
    problems.push(`${JSON.stringify(file)}: ${what} — a paper folder holds plain files of git mode 100644 only`);
  }
  return problems;
}

/** What keeps the pull request `base`…`head` of the checkout at `cwd` from merging; empty when nothing does. */
export function checkPr({ cwd, base, head, author, authorId = null }) {
  if (!author) return ["PR_AUTHOR is not set"];
  let changed;
  try {
    changed = changedPaths(cwd, base, head);
  } catch (err) {
    return [`cannot list the changed files (${String(err.stderr || err.message).trim()})`];
  }
  if (changed.length === 0) return ["the pull request changes no file"];
  const problems = [];
  const slugs = new Set();
  for (const f of changed) {
    const m = /^papers\/([^/]+)\/.+/u.exec(f);
    if (!m) problems.push(`${JSON.stringify(f)}: outside papers/<slug>/ — a pull request may only add or change one paper's folder`);
    else slugs.add(m[1]);
  }
  if (slugs.size > 1) problems.push(`the pull request touches ${slugs.size} paper folders (${[...slugs].sort().map((s) => JSON.stringify(s)).join(", ")}): one paper per pull request`);
  if (problems.length > 0 || slugs.size !== 1) return problems;

  const [slug] = slugs;
  if (!SLUG.test(slug)) return [`the folder name ${JSON.stringify(slug)} is not a slug (lower-case letters, digits, _ and -)`];
  const dir = path.join(cwd, "papers", slug);
  try {
    problems.push(...treeProblems(cwd, head, `papers/${slug}`));
  } catch (err) {
    return [`cannot list the files of papers/${slug} (${String(err.stderr || err.message).trim()})`];
  }
  problems.push(...checkPaper(dir).map((p) => (p.endsWith("no such folder") ? `papers/${slug}: removed by the pull request — the owner removes a paper, not a pull request` : `papers/${slug}: ${p}`)));

  const sharer = (text) => {
    try {
      const j = JSON.parse(text);
      return { login: j.shared_by, id: j.shared_by_id ?? null };
    } catch {
      return { login: undefined, id: null };
    }
  };
  let mine = { login: undefined, id: null };
  try {
    mine = sharer(readFileSync(path.join(dir, "share.json"), "utf8"));
  } catch { /* reported by check_paper */ }
  if (mine.login !== author) problems.push(`papers/${slug}/share.json: shared_by is ${JSON.stringify(mine.login)}, and the pull request is from ${JSON.stringify(author)}`);
  if (mine.id !== null && String(mine.id) !== String(authorId)) problems.push(`papers/${slug}/share.json: shared_by_id is ${JSON.stringify(mine.id)}, and the pull request's author has the id ${JSON.stringify(authorId)}`);
  // a paper already in the registry is changed by the person who shared it
  let before = null;
  try {
    before = sharer(git(cwd, ["show", `${base}:papers/${slug}/share.json`]));
  } catch { /* a new paper */ }
  if (before !== null) {
    const same = before.id !== null ? String(before.id) === String(authorId) : before.login === author;
    if (!same) problems.push(`papers/${slug}: already shared by ${JSON.stringify(before.login)} — only they can change it`);
  }
  return problems;
}

if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  const [base, head] = process.argv.slice(2);
  if (!base || !head || base.startsWith("-") || head.startsWith("-")) {
    console.error("Usage: PR_AUTHOR=<login> node checks/check_pr.mjs <base> <head>");
    process.exit(2);
  }
  const problems = checkPr({ cwd: process.cwd(), base, head, author: process.env.PR_AUTHOR ?? "", authorId: process.env.PR_AUTHOR_ID || null });
  for (const p of problems) console.error(p.replace(/\s*[\r\n]+\s*/gu, " "));
  if (problems.length === 0) console.log("ok: one paper folder, shared by the pull request's author, and it passes the check");
  process.exit(problems.length === 0 ? 0 : 1);
}

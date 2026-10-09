#!/usr/bin/env node
// The rule a pull request must meet to merge itself:
//   PR_AUTHOR=<login> node checks/check_pr.mjs <base> <head>
// run in a checkout of <head> (the working tree holds the pull request's files); <base> and <head>
// are commits of that repository. It passes when the pull request
//   - adds or changes files under exactly ONE folder papers/<slug>/, and nothing else;
//   - names its author in that folder's share.json (`shared_by` = PR_AUTHOR), and, when the paper
//     is already in the registry, is from the person who shared it;
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

/** What keeps the pull request `base`…`head` of the checkout at `cwd` from merging; empty when nothing does. */
export function checkPr({ cwd, base, head, author }) {
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
  problems.push(...checkPaper(dir).map((p) => (p.endsWith("no such folder") ? `papers/${slug}: removed by the pull request — the owner removes a paper, not a pull request` : `papers/${slug}: ${p}`)));

  const sharedBy = (text) => {
    try {
      return JSON.parse(text).shared_by;
    } catch {
      return undefined;
    }
  };
  let mine;
  try {
    mine = sharedBy(readFileSync(path.join(dir, "share.json"), "utf8"));
  } catch { /* reported by check_paper */ }
  if (mine !== author) problems.push(`papers/${slug}/share.json: shared_by is ${JSON.stringify(mine)}, and the pull request is from ${JSON.stringify(author)}`);
  // a paper already in the registry is changed by the person who shared it
  let before = null;
  try {
    before = git(cwd, ["show", `${base}:papers/${slug}/share.json`]);
  } catch { /* a new paper */ }
  if (before !== null && sharedBy(before) !== author) problems.push(`papers/${slug}: already shared by ${JSON.stringify(sharedBy(before))} — only they can change it`);
  return problems;
}

if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  const [base, head] = process.argv.slice(2);
  if (!base || !head || base.startsWith("-") || head.startsWith("-")) {
    console.error("Usage: PR_AUTHOR=<login> node checks/check_pr.mjs <base> <head>");
    process.exit(2);
  }
  const problems = checkPr({ cwd: process.cwd(), base, head, author: process.env.PR_AUTHOR ?? "" });
  for (const p of problems) console.error(p.replace(/\s*[\r\n]+\s*/gu, " "));
  if (problems.length === 0) console.log("ok: one paper folder, shared by the pull request's author, and it passes the check");
  process.exit(problems.length === 0 ? 0 : 1);
}

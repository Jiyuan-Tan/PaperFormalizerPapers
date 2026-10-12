#!/usr/bin/env node
// Checks ONE paper folder, `papers/<slug>/`, with no model and no Lean:
//   node checks/check_paper.mjs papers/<slug>      (no argument: every folder of papers/)
// The folder is read as data: nothing in it is run. One line per failure; exit 1 when any.
import { lstatSync, readdirSync, readFileSync } from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { ARXIV_ID, checkSeal, REVIEWS_FILE, SEAL_FILE, SEALED_DIRS } from "./seal.mjs";

export const MAX_TOTAL_BYTES = 60 * 1024 * 1024;
// (the static host's per-file limit is 25 MiB, and it serves a bounded number of files)
export const MAX_FILE_BYTES = 24 * 1024 * 1024;
export const MAX_FILES = 3000;

export const SLUG = /^[a-z0-9][a-z0-9_-]{0,79}$/u;
export const GITHUB_LOGIN = /^[A-Za-z0-9](?:[A-Za-z0-9-]{0,38})$/u;
const ISO_DATE = /^\d{4}-\d{2}-\d{2}(?:T\d{2}:\d{2}(?::\d{2}(?:\.\d+)?)?(?:Z|[+-]\d{2}:\d{2}))?$/u;

/** The layout of a paper folder: what must be there, and what else may be. */
const REQUIRED = ["share.json", "bundle.json", SEAL_FILE, "page/page.json", "REPORT.md", "MATCH.md", "lean", "corrected_paper"];
const TOP_FILES = new Set(["share.json", "bundle.json", SEAL_FILE, REVIEWS_FILE, "REPORT.md", "MATCH.md", "README.md"]);
const TOP_DIRS = new Set(SEALED_DIRS);
/** Types a browser runs when the site serves them: never part of a bundle. An `.svg` is one: opened
 *  on its own it runs its scripts, and GitHub Pages, which serves the site, sets no header that
 *  would keep it from doing so. */
export const ACTIVE_EXT = new Set([".html", ".htm", ".xhtml", ".xht", ".xml", ".js", ".mjs", ".svg"]);
const SHARE_KEYS = ["shared_by", "shared_at", "arxiv"];
/** Optional fields of `share.json`: `shared_by_id`, the sharer's numeric GitHub account id (written
 *  by the ingest; a login can be renamed and taken by someone else, the id cannot), and `subject`. */
const SHARE_OPTIONAL = ["shared_by_id", "subject"];

/** The regular files of `dir` by path from it, with each entry that is not a plain file or folder
 *  reported. Links are never followed. */
function walk(dir, rel, files, problems) {
  for (const e of readdirSync(path.join(dir, rel), { withFileTypes: true }).sort((a, b) => (a.name < b.name ? -1 : 1))) {
    const r = rel ? `${rel}/${e.name}` : e.name;
    const shown = JSON.stringify(r);
    if (e.name.startsWith(".")) problems.push(`${shown}: a dotfile is not part of a bundle`);
    else if (/[\\\p{Cc}]/u.test(e.name)) problems.push(`${shown}: the name holds a backslash or a control character`);
    else if (e.isSymbolicLink()) problems.push(`${shown}: a symbolic link (a bundle holds regular files only)`);
    else if (e.isDirectory()) walk(dir, r, files, problems);
    else if (!e.isFile()) problems.push(`${shown}: not a regular file`);
    else {
      const st = lstatSync(path.join(dir, r));
      if (st.mode & 0o111) problems.push(`${shown}: executable (mode ${(st.mode & 0o777).toString(8)}; a bundle's files are mode 644)`);
      if (ACTIVE_EXT.has(path.extname(e.name).toLowerCase())) problems.push(`${shown}: a ${path.extname(e.name).toLowerCase()} file is not part of a bundle`);
      if (st.size > MAX_FILE_BYTES) problems.push(`${shown}: ${st.size} bytes, over the limit of ${MAX_FILE_BYTES} for one file`);
      files.set(r, st.size);
    }
  }
}

function readJson(dir, rel, problems) {
  try {
    return JSON.parse(readFileSync(path.join(dir, rel), "utf8"));
  } catch (err) {
    problems.push(`${rel}: does not parse as JSON (${err.message})`);
    return null;
  }
}

/** What is wrong with `share.json`'s contents; pure. */
export function shareProblems(share) {
  if (share === null || typeof share !== "object" || Array.isArray(share)) return ["share.json: not an object"];
  const problems = [];
  const extra = Object.keys(share).filter((k) => !SHARE_KEYS.includes(k) && !SHARE_OPTIONAL.includes(k));
  if (extra.length > 0) problems.push(`share.json: unknown field(s) ${extra.map((k) => JSON.stringify(k)).join(", ")}`);
  if (typeof share.shared_by !== "string" || !GITHUB_LOGIN.test(share.shared_by)) problems.push("share.json: shared_by is not a GitHub login");
  if (typeof share.shared_at !== "string" || !ISO_DATE.test(share.shared_at) || Number.isNaN(Date.parse(share.shared_at))) problems.push("share.json: shared_at is not an ISO date");
  if (share.arxiv !== null && (typeof share.arxiv !== "string" || !ARXIV_ID.test(share.arxiv))) problems.push("share.json: arxiv is neither an arXiv identifier nor null");
  if ("shared_by_id" in share && !(Number.isSafeInteger(share.shared_by_id) && share.shared_by_id > 0)) problems.push("share.json: shared_by_id is not a GitHub account id (a positive integer)");
  if ("subject" in share && (typeof share.subject !== "string" || share.subject.length === 0 || share.subject.length > 80)) problems.push("share.json: subject is not a short string");
  return problems;
}

/** What keeps the folder `dir` from being a paper of the registry; empty when nothing does. */
export function checkPaper(dir) {
  const slug = path.basename(path.resolve(dir));
  let top;
  try {
    top = lstatSync(dir);
  } catch {
    return [`${dir}: no such folder`];
  }
  if (top.isSymbolicLink() || !top.isDirectory()) return [`${dir}: not a folder`];
  const problems = [];
  if (!SLUG.test(slug)) problems.push(`the folder name ${JSON.stringify(slug)} is not a slug (lower-case letters, digits, _ and -)`);

  // layout and size
  const files = new Map();
  walk(dir, "", files, problems);
  for (const f of files.keys()) {
    const [head, ...rest] = f.split("/");
    if (rest.length === 0 ? !TOP_FILES.has(head) : !TOP_DIRS.has(head)) problems.push(`${JSON.stringify(f)}: outside the layout of a paper folder`);
  }
  for (const r of REQUIRED) if (TOP_DIRS.has(r) ? ![...files.keys()].some((f) => f.startsWith(`${r}/`)) : !files.has(r)) problems.push(`${r}: missing`);
  const total = [...files.values()].reduce((a, b) => a + b, 0);
  if (total > MAX_TOTAL_BYTES) problems.push(`the folder holds ${total} bytes, over the limit of ${MAX_TOTAL_BYTES}`);
  if (files.size > MAX_FILES) problems.push(`the folder holds ${files.size} files, over the limit of ${MAX_FILES}`);

  // share.json
  const share = files.has("share.json") ? readJson(dir, "share.json", problems) : null;
  if (share !== null) problems.push(...shareProblems(share));

  // page/page.json and bundle.json
  const page = files.has("page/page.json") ? readJson(dir, "page/page.json", problems) : null;
  if (page !== null) {
    if (page?.schema !== 1) problems.push(`page/page.json: schema is ${JSON.stringify(page?.schema)}, not 1`);
    if (page?.slug !== slug) problems.push(`page/page.json: its slug ${JSON.stringify(page?.slug)} is not the folder's (${slug})`);
    if (!Array.isArray(page?.results)) problems.push("page/page.json: no results");
  }
  if (files.has("bundle.json")) readJson(dir, "bundle.json", problems);

  // the seal
  if (files.has(SEAL_FILE)) {
    const { seal, problems: sealProblems } = checkSeal(dir);
    problems.push(...sealProblems);
    if (seal) {
      if (seal.slug !== slug) problems.push(`${SEAL_FILE}: its slug ${JSON.stringify(seal.slug)} is not the folder's (${slug})`);
      if (share && (share.arxiv ?? null) !== seal.arxiv) problems.push(`share.json: arxiv ${JSON.stringify(share.arxiv)} is not the seal's (${JSON.stringify(seal.arxiv)})`);
      // a file of a sealed folder that the seal does not name was added afterwards — the compiled
      // PDF apart (the one the sealed page names), which the tool leaves out: it differs from one
      // compile to the next
      const named = new Set(seal.files.map((f) => f.path));
      const pdf = page?.paper?.pdf;
      const unsealed = [...files.keys()].filter((f) => TOP_DIRS.has(f.split("/")[0]) && !named.has(f) && !(f === pdf && /^corrected_paper\/.+\.pdf$/u.test(f)));
      for (const f of unsealed) problems.push(`${JSON.stringify(f)}: not named by the seal`);
    }
  }
  return problems;
}

if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  let dirs = process.argv.slice(2);
  if (dirs.length === 0) {
    const papers = path.join(path.dirname(fileURLToPath(import.meta.url)), "..", "papers");
    dirs = readdirSync(papers, { withFileTypes: true }).filter((e) => e.isDirectory()).map((e) => path.join(papers, e.name));
    if (dirs.length === 0) console.log("no paper to check");
  }
  let failed = false;
  for (const dir of dirs) {
    const problems = checkPaper(dir);
    for (const p of problems) console.error(`${path.basename(path.resolve(dir))}: ${p}`.replace(/\s*[\r\n]+\s*/gu, " "));
    if (problems.length === 0) console.log(`${path.basename(path.resolve(dir))}: ok`);
    else failed = true;
  }
  process.exit(failed ? 1 : 0);
}

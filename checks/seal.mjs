// The seal check of a paper folder: recompute what `f4_seal.json` names and compare.
//
// This MIRRORS the tool's checker, TheoremChecker `tools/src/verify/f4_seal.ts` (`F4SealSchema`,
// `codeOf`, `checkF4Seal`, `runSealCli`), which is the reference: `theoremchecker seal <dir>` must
// agree with it on every bundle. Keep the two in step when the seal's version changes.
//
// What it establishes: the seal file is whole (its code is the hash of its own contents), it records
// a pass of both reviewers on every statement target, and `f4_reviews.log` and the files it names
// are the ones it was written with. It is a checksum, not a signature: it does not show who ran the
// check, or that a check ran at all.
import { createHash } from "node:crypto";
import { lstatSync, readFileSync, realpathSync } from "node:fs";
import path from "node:path";

export const SEAL_FILE = "f4_seal.json";
export const REVIEWS_FILE = "f4_reviews.log";
/** The folders of a bundle whose files the seal names. */
export const SEALED_DIRS = ["lean", "corrected_paper", "page"];

export const ARXIV_ID = /^(?:\d{4}\.\d{4,5}|[a-z-]+(?:\.[A-Za-z-]+)?\/\d{7})(?:v\d+)?$/u;
const SEALED_PATH = /^(?:lean|corrected_paper|page)(?:\/(?!\.{1,2}(?:\/|$))[^/\\\p{Cc}]+)+$/u;

export const sha256 = (data) => createHash("sha256").update(data).digest("hex");

const str = (v) => typeof v === "string";
/** An object with exactly the string fields `keys`. */
const record = (keys) => (v) => v !== null && typeof v === "object" && !Array.isArray(v) && Object.keys(v).length === keys.length && keys.every((k) => str(v[k]));
const listOf = (item) => (v) => Array.isArray(v) && v.every(item);
const receipt = record(["verdict", "evidence_hash"]);
const peer = (v) => v === "codex" || v === "claude";
const SHAPE = {
  version: (v) => v === 1,
  slug: str,
  paper_sha256: str,
  arxiv: (v) => v === null || (str(v) && ARXIV_ID.test(v)),
  review_standard: str,
  targets: listOf((t) => t !== null && typeof t === "object" && Object.keys(t).length === 3 && str(t.id) && receipt(t.codex) && receipt(t.claude)),
  unreviewed: listOf(str),
  delivery: listOf((d) => record(["node_id", "reviewer", "verdict", "evidence_hash"])(d) && peer(d.reviewer)),
  cited: listOf((c) => record(["node_id", "reviewer", "check_status", "cite_id", "locator", "evidence_hash"])(c) && peer(c.reviewer)),
  reviews_sha256: (v) => v === null || str(v),
  files: listOf((f) => record(["path", "sha256"])(f) && SEALED_PATH.test(f.path)),
  code: str,
};

/** The fields of `seal` that are not a seal's; empty when it has the seal's shape. */
export function shapeProblems(seal) {
  if (seal === null || typeof seal !== "object" || Array.isArray(seal)) return ["(root)"];
  return [...Object.keys(SHAPE).filter((k) => !(k in seal) || !SHAPE[k](seal[k])), ...Object.keys(seal).filter((k) => !(k in SHAPE))];
}

/** The code of a seal: sha256 over its fields in a fixed order (`codeOf` of the tool). */
export function sealCode(s) {
  const r = (x) => [x.verdict, x.evidence_hash];
  return sha256(JSON.stringify([
    s.version,
    s.slug,
    s.paper_sha256,
    s.review_standard,
    s.targets.map((t) => [t.id, r(t.codex), r(t.claude)]),
    s.unreviewed,
    s.delivery.map((d) => [d.node_id, d.reviewer, d.verdict, d.evidence_hash]),
    s.cited.map((c) => [c.node_id, c.reviewer, c.check_status, c.cite_id, c.locator, c.evidence_hash]),
    s.reviews_sha256,
    s.arxiv,
    s.files.map((f) => [f.path, f.sha256]),
  ]));
}

/** What keeps the seal of the bundle at `dir` from holding; empty when it holds. */
export function checkSeal(dir) {
  let seal;
  try {
    seal = JSON.parse(readFileSync(path.join(dir, SEAL_FILE), "utf8"));
  } catch (err) {
    return { seal: null, problems: [`${SEAL_FILE}: cannot be read (${err.message})`] };
  }
  const shape = shapeProblems(seal);
  if (shape.length > 0) return { seal: null, problems: [`${SEAL_FILE}: not an F4 seal (${shape.join(", ")})`] };
  const problems = [];
  if (sealCode(seal) !== seal.code) problems.push(`${SEAL_FILE}: the code is not the hash of the seal's contents: the file was changed after it was written`);
  if (seal.targets.length === 0) problems.push(`${SEAL_FILE}: no target carries a pass of both reviewers`);
  for (const t of seal.targets) {
    if (t.codex.verdict !== "matched" || t.claude.verdict !== "matched") problems.push(`${SEAL_FILE}: ${t.id}: not passed by both reviewers`);
    else if (t.codex.evidence_hash !== t.claude.evidence_hash) problems.push(`${SEAL_FILE}: ${t.id}: the two reviewers passed different statements`);
  }
  if (seal.unreviewed.length > 0) problems.push(`${SEAL_FILE}: not passed by both reviewers: ${seal.unreviewed.join(", ")}`);

  // the reviews, hashed as the tool reads them (as text)
  let reviews = null;
  try {
    if (lstatSync(path.join(dir, REVIEWS_FILE)).isFile()) reviews = readFileSync(path.join(dir, REVIEWS_FILE), "utf8");
  } catch { /* none */ }
  if (seal.reviews_sha256 !== null) {
    if (reviews === null) problems.push(`${REVIEWS_FILE}: missing: the seal names the reviews it was written with`);
    else if (sha256(reviews) !== seal.reviews_sha256) problems.push(`${REVIEWS_FILE}: not the file the seal was written with`);
  } else if (reviews !== null) problems.push(`${REVIEWS_FILE}: not named by the seal: it was added afterwards`);

  // Only a regular file of the bundle itself is read: a link, or a path through one, counts as missing.
  const root = realpathSync(dir);
  for (const f of seal.files) {
    const full = path.join(dir, f.path);
    let plain = false;
    try {
      plain = lstatSync(full).isFile() && realpathSync(full) === path.join(root, f.path);
    } catch { /* missing */ }
    if (!plain) problems.push(`${f.path}: missing from the bundle (the seal names it)`);
    else if (sha256(readFileSync(full)) !== f.sha256) problems.push(`${f.path}: changed after the seal was written`);
  }
  return { seal, problems };
}

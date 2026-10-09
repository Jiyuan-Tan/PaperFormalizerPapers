import assert from "node:assert/strict";
import { execFileSync, spawnSync } from "node:child_process";
import { chmodSync, cpSync, renameSync, rmSync, symlinkSync, writeFileSync, appendFileSync } from "node:fs";
import path from "node:path";
import { test } from "node:test";
import { checkPaper } from "../checks/check_paper.mjs";
import { sealCode } from "../checks/seal.mjs";
import { copyFixture, FIXTURE, readJson, reseal, ROOT, writeJson } from "./helpers.mjs";

const has = (problems, re) => assert.ok(problems.some((p) => re.test(p)), `expected ${re} in:\n${problems.join("\n")}`);

test("the fixture passes", () => {
  assert.deepEqual(checkPaper(FIXTURE), []);
  assert.match(execFileSync("node", [path.join(ROOT, "checks", "check_paper.mjs"), FIXTURE], { encoding: "utf8" }), /cns_simple_dml: ok/u);
});

test("the seal's code is the tool's (a known seal)", () => {
  const seal = readJson(path.join(FIXTURE, "f4_seal.json"));
  assert.equal(sealCode(seal), seal.code);
  assert.equal(seal.code, "e84ecbe79ae9198cbba86caecbbfcb33177a996201b08bda6b854da613b5ca59");
});

test("a sealed file changed after the seal was written", () => {
  const dir = copyFixture();
  appendFileSync(path.join(dir, "lean", "Check.lean"), "\n-- changed\n");
  const problems = checkPaper(dir);
  has(problems, /lean\/Check\.lean: changed after the seal was written/u);
  const cli = spawnSync("node", [path.join(ROOT, "checks", "check_paper.mjs"), dir], { encoding: "utf8" });
  assert.equal(cli.status, 1);
  assert.match(cli.stderr, /^cns_simple_dml: lean\/Check\.lean: changed after the seal was written$/mu);
});

test("the seal file edited: its code no longer matches", () => {
  const dir = copyFixture();
  const seal = readJson(path.join(dir, "f4_seal.json"));
  seal.targets.pop();
  writeJson(path.join(dir, "f4_seal.json"), seal);
  has(checkPaper(dir), /the code is not the hash of the seal's contents/u);
});

test("the reviews changed", () => {
  const dir = copyFixture();
  appendFileSync(path.join(dir, "f4_reviews.log"), "more\n");
  has(checkPaper(dir), /f4_reviews\.log: not the file the seal was written with/u);
});

test("a missing file: required, and named by the seal", () => {
  const a = copyFixture();
  rmSync(path.join(a, "REPORT.md"));
  has(checkPaper(a), /^REPORT\.md: missing$/u);
  const b = copyFixture();
  rmSync(path.join(b, "lean", "Papers.lean"));
  has(checkPaper(b), /lean\/Papers\.lean: missing from the bundle/u);
  const c = copyFixture();
  rmSync(path.join(c, "page"), { recursive: true });
  has(checkPaper(c), /^page\/page\.json: missing$/u);
});

test("the folder's name is not the bundle's slug", () => {
  const dir = copyFixture("another_paper");
  const problems = checkPaper(dir);
  has(problems, /page\/page\.json: its slug "cns_simple_dml" is not the folder's \(another_paper\)/u);
  has(problems, /f4_seal\.json: its slug/u);
});

test("page.json of another schema", () => {
  const dir = copyFixture();
  const file = path.join(dir, "page", "page.json");
  writeJson(file, { ...readJson(file), schema: 2 });
  reseal(dir);
  assert.deepEqual(checkPaper(dir), ["page/page.json: schema is 2, not 1"]);
});

test("a symbolic link", () => {
  const dir = copyFixture();
  symlinkSync("/etc/passwd", path.join(dir, "lean", "passwd.lean"));
  has(checkPaper(dir), /"lean\/passwd\.lean": a symbolic link/u);
  // a sealed file replaced by a link to its own copy is still not the file
  const b = copyFixture();
  renameSync(path.join(b, "lean", "Check.lean"), path.join(b, "lean", "Moved.lean"));
  symlinkSync("Moved.lean", path.join(b, "lean", "Check.lean"));
  const problems = checkPaper(b);
  has(problems, /"lean\/Check\.lean": a symbolic link/u);
  has(problems, /lean\/Check\.lean: missing from the bundle/u);
});

test("files outside the layout", () => {
  const dir = copyFixture();
  writeFileSync(path.join(dir, "EXTRA.md"), "x");
  writeFileSync(path.join(dir, ".hidden"), "x");
  cpSync(path.join(dir, "lean"), path.join(dir, "other"), { recursive: true });
  writeFileSync(path.join(dir, "lean", "Added.lean"), "-- not sealed\n");
  writeFileSync(path.join(dir, "corrected_paper", "evil.html"), "<script>1</script>");
  const problems = checkPaper(dir);
  has(problems, /"EXTRA\.md": outside the layout/u);
  has(problems, /"\.hidden": a dotfile/u);
  has(problems, /"other\/Check\.lean": outside the layout/u);
  has(problems, /"lean\/Added\.lean": not named by the seal/u);
  has(problems, /"corrected_paper\/evil\.html": a \.html file is not part of a bundle/u);
});

test("an executable file", () => {
  const dir = copyFixture();
  chmodSync(path.join(dir, "lean", "Check.lean"), 0o755);
  has(checkPaper(dir), /"lean\/Check\.lean": executable/u);
});

test("share.json", () => {
  const dir = copyFixture();
  const file = path.join(dir, "share.json");
  writeFileSync(file, "{ not json");
  has(checkPaper(dir), /share\.json: does not parse as JSON/u);
  writeJson(file, { shared_by: "no such login!", shared_at: "yesterday", arxiv: "nope", source_included: "yes", extra: 1 });
  const problems = checkPaper(dir);
  for (const re of [/shared_by is not a GitHub login/u, /shared_at is not an ISO date/u, /arxiv is neither/u, /source_included is not true or false/u, /unknown field\(s\) "extra"/u]) has(problems, re);
  // the arXiv identifier is the sealed one
  writeJson(file, { shared_by: "fixture-user", shared_at: "2026-10-09T12:00:00Z", arxiv: "2105.15197", source_included: true });
  has(checkPaper(dir), /share\.json: arxiv "2105\.15197" is not the seal's \(null\)/u);
  reseal(dir, (seal) => { seal.arxiv = "2105.15197"; });
  assert.deepEqual(checkPaper(dir), []);
});

test("a paper shared without its source", () => {
  const dir = copyFixture();
  rmSync(path.join(dir, "corrected_paper"), { recursive: true });
  has(checkPaper(dir), /source_included is true, and corrected_paper\/ is absent/u);
  writeJson(path.join(dir, "share.json"), { ...readJson(path.join(dir, "share.json")), source_included: false });
  assert.deepEqual(checkPaper(dir), []);
});

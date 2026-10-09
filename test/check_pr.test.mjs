import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { cpSync, mkdirSync, rmSync, writeFileSync } from "node:fs";
import path from "node:path";
import { test } from "node:test";
import { checkPr } from "../checks/check_pr.mjs";
import { copyFixture, FIXTURE, git, readJson, ROOT, SLUG, tmp, writeJson } from "./helpers.mjs";

/** A repository with a base commit (after `before(dir)`) and a head commit (after `change(dir)`). */
function repo(change, before = () => {}) {
  const dir = tmp();
  git(dir, "init", "-q", "-b", "main");
  mkdirSync(path.join(dir, "papers"));
  writeFileSync(path.join(dir, "papers", ".gitkeep"), "");
  writeFileSync(path.join(dir, "README.md"), "registry\n");
  before(dir);
  git(dir, "add", "-A");
  git(dir, "commit", "-q", "-m", "base");
  const base = git(dir, "rev-parse", "HEAD");
  git(dir, "checkout", "-q", "-b", "share");
  change(dir);
  git(dir, "add", "-A");
  git(dir, "commit", "-q", "-m", "share a paper");
  return { cwd: dir, base, head: git(dir, "rev-parse", "HEAD") };
}
const add = (dir, slug = SLUG) => copyFixture(slug, path.join(dir, "papers"));
const has = (problems, re) => assert.ok(problems.some((p) => re.test(p)), `expected ${re} in:\n${problems.join("\n")}`);

test("a pull request adding one paper, from the person named in share.json", () => {
  const r = repo((dir) => add(dir));
  assert.deepEqual(checkPr({ ...r, author: "fixture-user" }), []);
  const cli = spawnSync("node", [path.join(ROOT, "checks", "check_pr.mjs"), r.base, r.head], { cwd: r.cwd, encoding: "utf8", env: { ...process.env, PR_AUTHOR: "fixture-user" } });
  assert.equal(cli.status, 0, cli.stderr);
});

test("the base branch moved on: only the pull request's own changes count", () => {
  const r = repo((dir) => add(dir));
  git(r.cwd, "checkout", "-q", "main");
  writeFileSync(path.join(r.cwd, "README.md"), "registry, edited by the owner\n");
  git(r.cwd, "commit", "-q", "-am", "owner");
  const base = git(r.cwd, "rev-parse", "HEAD");
  git(r.cwd, "checkout", "-q", "share");
  assert.deepEqual(checkPr({ ...r, base, author: "fixture-user" }), []);
});

test("two paper folders in one pull request", () => {
  const r = repo((dir) => { add(dir); add(dir, "second_paper"); });
  has(checkPr({ ...r, author: "fixture-user" }), /touches 2 paper folders \("cns_simple_dml", "second_paper"\)/u);
});

test("a file outside papers/<slug>/", () => {
  const r = repo((dir) => {
    add(dir);
    writeFileSync(path.join(dir, "README.md"), "changed\n");
    mkdirSync(path.join(dir, ".github", "workflows"), { recursive: true });
    writeFileSync(path.join(dir, ".github", "workflows", "x.yml"), "on: push\n");
    writeFileSync(path.join(dir, "papers", "loose.md"), "x\n");
  });
  const problems = checkPr({ ...r, author: "fixture-user" });
  has(problems, /^"README\.md": outside papers\/<slug>\//u);
  has(problems, /^"\.github\/workflows\/x\.yml": outside/u);
  has(problems, /^"papers\/loose\.md": outside/u);
  const cli = spawnSync("node", [path.join(ROOT, "checks", "check_pr.mjs"), r.base, r.head], { cwd: r.cwd, encoding: "utf8", env: { ...process.env, PR_AUTHOR: "fixture-user" } });
  assert.equal(cli.status, 1);
});

test("shared_by is not the pull request's author", () => {
  const r = repo((dir) => add(dir));
  const problems = checkPr({ ...r, author: "someone-else" });
  assert.deepEqual(problems, ['papers/cns_simple_dml/share.json: shared_by is "fixture-user", and the pull request is from "someone-else"']);
  has(checkPr({ ...r, author: "" }), /PR_AUTHOR is not set/u);
});

test("a paper someone else shared cannot be taken over", () => {
  const r = repo(
    (dir) => { const f = path.join(dir, "papers", SLUG, "share.json"); writeJson(f, { ...readJson(f), shared_by: "intruder" }); },
    (dir) => add(dir),
  );
  has(checkPr({ ...r, author: "intruder" }), /already shared by "fixture-user" — only they can change it/u);
  // the person who shared it may update it
  const own = repo(
    (dir) => { const f = path.join(dir, "papers", SLUG, "share.json"); writeJson(f, { ...readJson(f), shared_at: "2026-11-01" }); },
    (dir) => add(dir),
  );
  assert.deepEqual(checkPr({ ...own, author: "fixture-user" }), []);
});

test("the folder must pass the paper check, and cannot be removed", () => {
  const bad = repo((dir) => { add(dir); writeFileSync(path.join(dir, "papers", SLUG, "lean", "Check.lean"), "-- tampered\n"); });
  has(checkPr({ ...bad, author: "fixture-user" }), /^papers\/cns_simple_dml: lean\/Check\.lean: changed after the seal was written/u);
  const gone = repo((dir) => rmSync(path.join(dir, "papers", SLUG), { recursive: true }), (dir) => add(dir));
  has(checkPr({ ...gone, author: "fixture-user" }), /removed by the pull request/u);
});

test("a file name is never a command", () => {
  const r = repo((dir) => { add(dir); cpSync(path.join(FIXTURE, "MATCH.md"), path.join(dir, "papers", SLUG, "$(touch pwned);`id`.md")); });
  const problems = checkPr({ ...r, author: "fixture-user" });
  has(problems, /outside the layout of a paper folder/u);
});

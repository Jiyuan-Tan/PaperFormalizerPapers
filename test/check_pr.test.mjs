import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { cpSync, mkdirSync, rmSync, writeFileSync } from "node:fs";
import path from "node:path";
import { test } from "node:test";
import { checkPr } from "../checks/check_pr.mjs";
import { trustedSharer } from "../checks/trusted_sharer.mjs";
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

test("the tree holds plain files only: a submodule, a symbolic link or an executable entry is refused, whatever the checkout shows", () => {
  // entries written into the index alone: the working tree holds the paper as the check wants it
  const entry = (mode, file) => {
    const r = repo((dir) => add(dir));
    const blob = git(r.cwd, "rev-parse", `:papers/${SLUG}/MATCH.md`);
    git(r.cwd, "update-index", "--add", "--cacheinfo", `${mode},${mode === "160000" ? "1".repeat(40) : blob},papers/${SLUG}/${file}`);
    git(r.cwd, "commit", "-q", "-m", "one more entry");
    return { ...r, head: git(r.cwd, "rev-parse", "HEAD") };
  };
  const sub = entry("160000", "lean/sub");
  has(checkPr({ ...sub, author: "fixture-user" }), /^"papers\/cns_simple_dml\/lean\/sub": a submodule — a paper folder holds plain files of git mode 100644 only$/u);
  has(checkPr({ ...entry("120000", "README.md"), author: "fixture-user" }), /^"papers\/cns_simple_dml\/README\.md": a symbolic link/u);
  has(checkPr({ ...entry("100755", "MATCH.md"), author: "fixture-user" }), /^"papers\/cns_simple_dml\/MATCH\.md": an executable file/u);
});

test("who merges without the owner: the logins of TRUSTED_SHARERS, or everyone with *; nobody when it is unset", () => {
  assert.equal(trustedSharer("alice", undefined), false);
  assert.equal(trustedSharer("alice", ""), false);
  assert.equal(trustedSharer("alice", "bob, Alice"), true);
  assert.equal(trustedSharer("alice", "bob,alice-2"), false);
  assert.equal(trustedSharer("alice", " * "), true);
  assert.equal(trustedSharer("", "*"), false);
  const cli = (env) => spawnSync("node", [path.join(ROOT, "checks", "trusted_sharer.mjs")], { encoding: "utf8", env: { PATH: process.env.PATH, ...env } }).stdout;
  assert.equal(cli({ PR_AUTHOR: "alice" }), "trusted=false\n");
  assert.equal(cli({ PR_AUTHOR: "alice", TRUSTED_SHARERS: "alice" }), "trusted=true\n");
  // a login is a value, never a line of shell or of the output file
  assert.equal(cli({ PR_AUTHOR: "x\ntrusted=true", TRUSTED_SHARERS: "alice" }), "trusted=false\n");
});

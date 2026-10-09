import { execFileSync } from "node:child_process";
import { cpSync, mkdtempSync, readFileSync, writeFileSync } from "node:fs";
import os from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { sealCode, sha256 } from "../checks/seal.mjs";

export const ROOT = path.join(path.dirname(fileURLToPath(import.meta.url)), "..");
export const SLUG = "cns_simple_dml";
export const FIXTURE = path.join(ROOT, "test", "fixtures", "papers", SLUG);

export const tmp = () => mkdtempSync(path.join(os.tmpdir(), "tcpapers-"));
export const readJson = (file) => JSON.parse(readFileSync(file, "utf8"));
export const writeJson = (file, value) => writeFileSync(file, `${JSON.stringify(value, null, 2)}\n`);

/** A copy of the fixture paper in a fresh `papers/` folder (named `slug`); returns its path. */
export function copyFixture(slug = SLUG, papers = path.join(tmp(), "papers")) {
  const dir = path.join(papers, slug);
  cpSync(FIXTURE, dir, { recursive: true });
  return dir;
}

/** Writes the seal of `dir` again over its files as they are now, after `change(seal)`. */
export function reseal(dir, change = () => {}) {
  const seal = readJson(path.join(dir, "f4_seal.json"));
  change(seal);
  seal.files = seal.files.map((f) => ({ path: f.path, sha256: sha256(readFileSync(path.join(dir, f.path))) }));
  seal.code = sealCode(seal);
  writeJson(path.join(dir, "f4_seal.json"), seal);
}

export const git = (cwd, ...args) => execFileSync("git", ["-c", "user.name=test", "-c", "user.email=test@example.org", "-c", "commit.gpgsign=false", ...args], { cwd, encoding: "utf8", stdio: ["ignore", "pipe", "pipe"] }).trim();

import { execFileSync } from "node:child_process";
import { cpSync, mkdtempSync, readdirSync, readFileSync, writeFileSync } from "node:fs";
import os from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { gunzipSync, gzipSync } from "node:zlib";
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

/** The regular files under `dir`, by `/`-separated path from it, sorted. */
export function filesOf(dir, rel = "", out = []) {
  for (const e of readdirSync(path.join(dir, rel), { withFileTypes: true })) {
    const r = rel ? `${rel}/${e.name}` : e.name;
    if (e.isDirectory()) filesOf(dir, r, out);
    else out.push([r, readFileSync(path.join(dir, r))]);
  }
  return out.sort(([a], [b]) => (a < b ? -1 : 1));
}

/** A pax header's record `key=value`, its length included. */
export function paxRecord(key, value) {
  const body = ` ${key}=${value}\n`;
  let n = Buffer.byteLength(body) + 1;
  while (String(n).length + Buffer.byteLength(body) !== n) n = String(n).length + Buffer.byteLength(body);
  return Buffer.from(`${n}${body}`);
}

/**
 * A gzip'd ustar archive of `entries`, written as the tool's share writes one: each entry
 * `[path, bytes]`, or `{ path, data, type, linkname }` for an entry of another type; a path over
 * 100 bytes is split at a `/` into the ustar prefix and name, and one whose last part is over 100
 * bytes goes before its file as a pax header's `path` record.
 */
export function tarGz(entries) {
  const blocks = [];
  for (const e of entries) {
    const { path: p, data = Buffer.alloc(0), type = "0", linkname = "" } = Array.isArray(e) ? { path: e[0], data: e[1] } : e;
    const h = Buffer.alloc(512);
    let name = p, prefix = "";
    if (type !== "x" && Buffer.byteLength(p.slice(p.lastIndexOf("/") + 1)) > 100) {
      blocks.push(gunzipSync(tarGz([{ path: "PaxHeader", type: "x", data: paxRecord("path", p) }])).subarray(0, -1024));
      name = "long-name";
    } else if (Buffer.byteLength(p) > 100) {
      const cut = p.lastIndexOf("/", 155);
      prefix = p.slice(0, cut); name = p.slice(cut + 1);
    }
    h.write(name, 0, 100, "utf8");
    h.write("0000644\0", 100); h.write("0000000\0", 108); h.write("0000000\0", 116);
    h.write(`${data.length.toString(8).padStart(11, "0")}\0`, 124);
    h.write("00000000000\0", 136);
    h.write("        ", 148);
    h.write(type, 156);
    h.write(linkname, 157, 100);
    h.write("ustar\0", 257); h.write("00", 263);
    h.write(prefix, 345, 155, "utf8");
    let sum = 0;
    for (const b of h) sum += b;
    h.write(`${sum.toString(8).padStart(6, "0")}\0 `, 148);
    blocks.push(h, data, Buffer.alloc((512 - (data.length % 512)) % 512));
  }
  blocks.push(Buffer.alloc(1024));
  return gzipSync(Buffer.concat(blocks));
}

/** The manifest the tool sends for `files` (`[path, bytes]`) and their `archive`. */
export function manifestOf(files, archive, extra = {}) {
  return {
    v: 1, slug: SLUG, title: "A fixture paper", authors: "A. Author", arxiv: null,
    files: files.map(([p, b]) => ({ path: p, size: b.length, sha256: sha256(b) })),
    archive: { size: archive.length, sha256: sha256(archive) },
    ...extra,
  };
}

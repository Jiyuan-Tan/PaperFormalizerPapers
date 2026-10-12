// Reads the archive a share arrives in: a gzip'd ustar tar of regular files with bundle-relative
// paths (the tool's `share` writes it). The archive is DATA from anyone with a GitHub account, so
// the reader is strict rather than general: it unpacks into memory, never onto disk, and an entry
// that is not a plain file (a directory, a link, a pax or GNU extension header, a device) is a
// problem, not something to interpret.
import { gunzipSync } from "node:zlib";

const BLOCK = 512;

/** What is wrong with a bundle-relative path; null when nothing is. Pure. */
export function pathProblem(p) {
  if (typeof p !== "string" || p.length === 0) return "an empty path";
  if (p.startsWith("/")) return "an absolute path";
  if (/[\\\p{Cc}]/u.test(p)) return "a backslash or a control character";
  for (const seg of p.split("/")) {
    if (seg === "" || seg === "." || seg === "..") return "an empty, . or .. segment";
    if (seg.startsWith(".")) return "a dotfile";
  }
  return null;
}

/** The string of a NUL-terminated header field. */
function field(buf, at, len) {
  const b = buf.subarray(at, at + len);
  const end = b.indexOf(0);
  return (end < 0 ? b : b.subarray(0, end)).toString("utf8");
}

/** A numeric header field (octal, space- or NUL-terminated); null when it is not one (GNU's
 *  base-256 form included: no file of a bundle is that large). */
function octal(buf, at, len) {
  const s = field(buf, at, len).trim();
  return /^[0-7]{1,12}$/u.test(s) ? Number.parseInt(s, 8) : s === "" ? 0 : null;
}

/** The header's checksum holds: the sum of its bytes with the checksum field read as spaces. */
function checksumHolds(h) {
  const want = octal(h, 148, 8);
  let sum = 0;
  for (let i = 0; i < BLOCK; i++) sum += i >= 148 && i < 156 ? 0x20 : h[i];
  return want === sum;
}

const TYPES = { "1": "a hard link", "2": "a symbolic link", "3": "a character device", "4": "a block device", "5": "a directory", "6": "a FIFO", "7": "a contiguous file", x: "a pax header", g: "a pax global header", L: "a GNU long name", K: "a GNU long link name" };

/**
 * The files of the gzip'd tar `gz`: `files` maps each path to its bytes; `problems` says, one line
 * each, what makes the archive unacceptable (empty when nothing does). Unpacks at most `maxBytes`
 * (a gzip bomb stops there). Pure.
 */
export function readTarGz(gz, { maxBytes = 70 * 1024 * 1024 } = {}) {
  const files = new Map();
  const problems = [];
  let tar;
  try {
    tar = gunzipSync(gz, { maxOutputLength: maxBytes });
  } catch (err) {
    return { files, problems: [`the archive does not unpack as gzip within ${maxBytes} bytes (${err.code ?? err.message})`] };
  }
  let at = 0;
  let ended = false;
  while (at + BLOCK <= tar.length) {
    const h = tar.subarray(at, at + BLOCK);
    if (h.every((b) => b === 0)) { ended = true; break; }
    if (!checksumHolds(h)) { problems.push(`the header at byte ${at} is not a tar header (its checksum does not hold)`); break; }
    const magic = field(h, 257, 6);
    if (magic !== "ustar") { problems.push(`the header at byte ${at} is not a ustar header`); break; }
    const name = field(h, 0, 100);
    const prefix = field(h, 345, 155);
    const p = prefix ? `${prefix}/${name}` : name;
    const size = octal(h, 124, 12);
    const type = String.fromCharCode(h[156]);
    if (size === null) { problems.push(`${JSON.stringify(p)}: its size field is not octal`); break; }
    const dataEnd = at + BLOCK + size;
    if (dataEnd > tar.length) { problems.push(`${JSON.stringify(p)}: the archive ends inside it`); break; }
    if (type !== "0" && type !== "\0") problems.push(`${JSON.stringify(p)}: ${TYPES[type] ?? `an entry of type ${JSON.stringify(type)}`} (a bundle holds regular files only)`);
    else {
      const bad = pathProblem(p);
      if (bad) problems.push(`${JSON.stringify(p)}: ${bad}`);
      else if (files.has(p)) problems.push(`${JSON.stringify(p)}: in the archive twice`);
      else files.set(p, Buffer.from(tar.subarray(at + BLOCK, dataEnd)));
    }
    at = at + BLOCK + Math.ceil(size / BLOCK) * BLOCK;
  }
  if (!ended && problems.length === 0) problems.push("the archive has no end-of-archive marker (it is truncated)");
  return { files, problems };
}

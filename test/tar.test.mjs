import assert from "node:assert/strict";
import { test } from "node:test";
import { gunzipSync, gzipSync } from "node:zlib";
import { pathProblem, readTarGz } from "../checks/tar.mjs";
import { tarGz } from "./helpers.mjs";

const has = (problems, re) => assert.ok(problems.some((p) => re.test(p)), `expected ${re} in:\n${problems.join("\n")}`);

test("regular files come back byte for byte, a long path through the ustar prefix", () => {
  const long = `lean/${"Deep/".repeat(25)}File.lean`;
  assert.ok(Buffer.byteLength(long) > 100);
  const bin = Buffer.from([0, 1, 2, 255, 254]);
  const { files, problems } = readTarGz(tarGz([["a.md", Buffer.from("hello\n")], [long, Buffer.alloc(1300, "x")], ["corrected_paper/main.pdf", bin], ["empty.txt", Buffer.alloc(0)]]));
  assert.deepEqual(problems, []);
  assert.deepEqual([...files.keys()], ["a.md", long, "corrected_paper/main.pdf", "empty.txt"]);
  assert.equal(files.get("a.md").toString(), "hello\n");
  assert.equal(files.get(long).length, 1300);
  assert.deepEqual(files.get("corrected_paper/main.pdf"), bin);
});

test("an entry that is not a regular file is refused, whatever it is", () => {
  for (const [type, what] of [["2", /a symbolic link/u], ["1", /a hard link/u], ["5", /a directory/u], ["x", /a pax header/u], ["g", /a pax global header/u], ["L", /a GNU long name/u], ["3", /a character device/u]]) {
    const { files, problems } = readTarGz(tarGz([["ok.md", Buffer.from("x")], { path: "bad", type, linkname: "../../etc/passwd" }]));
    has(problems, what);
    assert.ok(!files.has("bad"));
  }
});

test("paths that leave the folder or hide in it are refused", () => {
  for (const [p, re] of [["../escape.md", /\.\. segment/u], ["/etc/passwd", /absolute/u], ["a/./b", /\. or \.\. segment/u], ["a//b", /empty/u], [".git/config", /dotfile/u], ["lean/.hidden", /dotfile/u], ["a\\b", /backslash/u], ["a\u0007b", /control/u]]) {
    has(readTarGz(tarGz([[p, Buffer.from("x")]])).problems, re);
  }
  assert.equal(pathProblem("lean/Papers/A.lean"), null);
  has(readTarGz(tarGz([["a.md", Buffer.from("1")], ["a.md", Buffer.from("2")]])).problems, /in the archive twice/u);
});

test("what is not a whole ustar archive is refused", () => {
  has(readTarGz(Buffer.from("not gzip")).problems, /does not unpack as gzip/u);
  has(readTarGz(gzipSync(Buffer.alloc(512, 7))).problems, /checksum does not hold/u);
  const whole = tarGz([["a.md", Buffer.alloc(2000, "x")]]);
  // cut inside the file's data, and without the end-of-archive marker
  has(readTarGz(gzipSync(gunzipSync(whole).subarray(0, 1024))).problems, /ends inside it/u);
  has(readTarGz(gzipSync(gunzipSync(whole).subarray(0, 512 + 2048))).problems, /no end-of-archive marker/u);
  // a gzip bomb stops at the limit
  has(readTarGz(gzipSync(Buffer.alloc(4096)), { maxBytes: 1024 }).problems, /within 1024 bytes/u);
});

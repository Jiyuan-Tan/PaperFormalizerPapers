import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import { afterEach, beforeEach, describe, test } from "node:test";
import worker, { esc, LIMITS, manifestProblems } from "../worker/worker.js";

const BASE = "https://share.example/";
const SITE = "https://site.example/papers-site/";
const sha = (b) => createHash("sha256").update(b).digest("hex");

/** An in-memory R2 bucket: put checks a given sha256 the way R2 does, and a conditional put
 *  (`onlyIf.etagMatches`) writes only over that version, answering null otherwise. */
class FakeR2 {
  constructor() { this.objects = new Map(); this.etags = new Map(); this.n = 0; }
  async put(key, value, opts = {}) {
    let bytes;
    if (typeof value === "string") bytes = Buffer.from(value);
    else if (value && typeof value.getReader === "function") bytes = Buffer.from(await new Response(value).arrayBuffer());
    else bytes = Buffer.from(value);
    if (opts.sha256 && sha(bytes) !== opts.sha256) throw new Error("put: The SHA-256 checksum you specified did not match what we received.");
    await new Promise((r) => setImmediate(r)); // a write takes a turn: concurrent requests interleave
    if (opts.onlyIf?.etagMatches !== undefined && this.etags.get(key) !== opts.onlyIf.etagMatches) return null;
    const etag = `e${++this.n}`;
    this.objects.set(key, bytes);
    this.etags.set(key, etag);
    return { key, etag };
  }
  async get(key) {
    const b = this.objects.get(key);
    if (!b) return null;
    return { etag: this.etags.get(key), text: async () => b.toString("utf8"), body: new Response(b).body };
  }
  async delete(key) { this.objects.delete(key); this.etags.delete(key); }
}

let env, calls, github;
const realFetch = globalThis.fetch;

beforeEach(() => {
  env = {
    SHARES: new FakeR2(),
    GITHUB_CLIENT_ID: "Ov23test", GITHUB_CLIENT_SECRET: "client-secret", GITHUB_DISPATCH_TOKEN: "dispatch-token",
    SESSION_SECRET: "session-secret-for-tests", INGEST_SECRET: "ingest-secret",
    REGISTRY: "Owner/Registry", SITE_URL: SITE, WORKER_URL: BASE,
  };
  calls = [];
  github = { user: { login: "alice", id: 4242 }, token: "gho_tok", dispatchStatus: 204 };
  globalThis.fetch = async (input, init = {}) => {
    const url = String(input);
    calls.push({ url, method: init.method || "GET", headers: init.headers || {}, body: init.body });
    if (url === "https://github.com/login/oauth/access_token") {
      const b = JSON.parse(init.body);
      return Response.json(b.code === "good-code" ? { access_token: github.token } : { error: "bad_verification_code" });
    }
    if (url === "https://api.github.com/user") return github.user ? Response.json(github.user) : new Response("no", { status: 401 });
    if (url.startsWith("https://api.github.com/applications/")) return new Response(null, { status: 204 });
    if (url === "https://api.github.com/repos/Owner/Registry/dispatches") return new Response(null, { status: github.dispatchStatus });
    throw new Error(`unexpected fetch ${url}`);
  };
});
afterEach(() => { globalThis.fetch = realFetch; });

const call = (path, init = {}) => worker.fetch(new Request(new URL(path, BASE), init), env);

const archive = Buffer.from("not really a tarball, but bytes");
function manifest(over = {}) {
  return {
    v: 1, slug: "my_paper", title: "A <b>bold</b> paper", authors: "A. Author & B. Author", arxiv: "2401.00001",
    files: [
      { path: "bundle.json", size: 10, sha256: "a".repeat(64) },
      { path: "page/page.json", size: 20, sha256: "b".repeat(64) },
    ],
    archive: { size: archive.length, sha256: sha(archive) },
    ...over,
  };
}

async function upload(mf = manifest()) {
  const r = await call("/api/uploads", { method: "POST", headers: { "Content-Type": "application/json" }, body: JSON.stringify(mf) });
  return { r, body: await r.json() };
}
const auth = (t) => ({ Authorization: `Bearer ${t}` });
const put = (id, token, bytes = archive, len = bytes.length) =>
  call(`/api/uploads/${id}`, { method: "PUT", headers: { ...auth(token), "Content-Type": "application/gzip", "Content-Length": String(len) }, body: bytes });
const cookiesOf = (r) => r.headers.getSetCookie().map((c) => c.split(";")[0]).filter((c) => !c.endsWith("="));

/** Upload + archive + sign-in: the claim page's cookies, the upload, and the page's HTML. */
async function signedIn() {
  const { body: up } = await upload();
  assert.equal((await put(up.id, up.poll_token)).status, 200);
  const r1 = await call(`/claim/${up.id}`, { redirect: "manual" });
  assert.equal(r1.status, 302);
  const loc = new URL(r1.headers.get("Location"));
  const oauthCookie = cookiesOf(r1).join("; ");
  const r2 = await call(`/auth/callback?code=good-code&state=${encodeURIComponent(loc.searchParams.get("state"))}`, { headers: { Cookie: oauthCookie } });
  assert.equal(r2.status, 302, await r2.clone().text());
  assert.equal(r2.headers.get("Location"), `${BASE}claim/${up.id}`);
  const session = cookiesOf(r2).join("; ");
  const page = await call(`/claim/${up.id}`, { headers: { Cookie: session } });
  return { up, session, loc, oauthCookie, page, html: await page.text() };
}
const csrfOf = (html) => /name="csrf" value="([^"]+)"/.exec(html)[1];
const confirm = (id, session, csrf) => call(`/claim/${id}`, { method: "POST", headers: { Cookie: session, "Content-Type": "application/x-www-form-urlencoded" }, body: new URLSearchParams({ csrf }).toString() });
const ingest = (path, init = {}) => call(path, { ...init, headers: { ...auth("ingest-secret"), ...(init.headers || {}) } });

describe("the whole share", () => {
  test("upload → archive → sign-in → confirm → dispatch → ingest → result → poll", async () => {
    const { up, session, loc, html, page } = await signedIn();
    assert.match(up.id, /^[a-z2-7]{26}$/);
    assert.match(up.poll_token, /^[A-Za-z0-9_-]{43}$/);
    assert.match(up.check_code, /^[A-HJ-NP-Z2-9]{4}$/);
    assert.equal(up.claim_url, `${BASE}claim/${up.id}`);
    assert.equal(up.upload_url, `${BASE}api/uploads/${up.id}`);
    // the sign-in asks for no permission at all
    assert.equal(loc.origin + loc.pathname, "https://github.com/login/oauth/authorize");
    assert.equal(loc.searchParams.get("client_id"), "Ov23test");
    assert.equal(loc.searchParams.get("redirect_uri"), `${BASE}auth/callback`);
    assert.equal(loc.searchParams.has("scope"), false);
    // the token was revoked after one use
    const revoke = calls.find((c) => c.url === "https://api.github.com/applications/Ov23test/token");
    assert.equal(revoke.method, "DELETE");
    assert.deepEqual(JSON.parse(revoke.body), { access_token: "gho_tok" });
    // the page says who, what and where, escaped
    assert.match(page.headers.get("Content-Security-Policy"), /default-src 'none'/);
    assert.match(page.headers.get("Content-Security-Policy"), /form-action 'self'/);
    assert.ok(html.includes("@alice"));
    assert.ok(html.includes(up.check_code));
    assert.ok(html.includes(`${SITE}papers/my_paper/`));
    assert.ok(html.includes("A &lt;b&gt;bold&lt;/b&gt; paper"));
    assert.ok(html.includes("A. Author &amp; B. Author"));
    assert.ok(!html.includes("<b>bold</b>"));
    assert.ok(html.includes("TeX source and PDF"));

    let poll = await (await call(`/api/uploads/${up.id}`, { headers: auth(up.poll_token) })).json();
    assert.equal(poll.status, "awaiting_sign_in");

    const done = await confirm(up.id, session, csrfOf(html));
    assert.equal(done.status, 200);
    assert.match(await done.text(), /Submitted/);
    const dispatch = calls.find((c) => c.url.endsWith("/dispatches"));
    assert.equal(dispatch.headers.Authorization, "Bearer dispatch-token");
    assert.deepEqual(JSON.parse(dispatch.body), { event_type: "share", client_payload: { id: up.id } });

    poll = await (await call(`/api/uploads/${up.id}`, { headers: auth(up.poll_token) })).json();
    assert.deepEqual(poll, { status: "submitted", check_code: up.check_code, login: "alice" });

    const meta = await (await ingest(`/api/ingest/${up.id}`)).json();
    assert.equal(meta.status, "submitted");
    assert.deepEqual(meta.identity, { login: "alice", id: 4242 });
    assert.equal(meta.manifest.slug, "my_paper");
    assert.equal(meta.manifest.files.length, 2);
    assert.equal(meta.poll_hash, undefined);
    const arch = await ingest(`/api/ingest/${up.id}/archive`);
    assert.equal(arch.status, 200);
    assert.deepEqual(Buffer.from(await arch.arrayBuffer()), archive);

    const res = await ingest(`/api/ingest/${up.id}/result`, { method: "POST", headers: { "Content-Type": "application/json" }, body: JSON.stringify({ kind: "review", pr_url: "https://github.com/Owner/Registry/pull/7" }) });
    assert.equal(res.status, 200);
    assert.equal(env.SHARES.objects.has(`bundles/${up.id}.tar.gz`), false);
    poll = await (await call(`/api/uploads/${up.id}`, { headers: auth(up.poll_token) })).json();
    assert.deepEqual(poll.result, { kind: "review", pr_url: "https://github.com/Owner/Registry/pull/7" });
    assert.equal(poll.status, "review");
    // a second result is refused
    assert.equal((await ingest(`/api/ingest/${up.id}/result`, { method: "POST", body: JSON.stringify({ kind: "published" }) })).status, 409);
    // the claim page now says where it stands, with no form
    const after = await (await call(`/claim/${up.id}`, { headers: { Cookie: session } })).text();
    assert.match(after, /waiting for the owner/);
    assert.ok(!after.includes("<form"));
  });

  test("a refusal's problems reach the poll, escaped on the page", async () => {
    const { up, session, html } = await signedIn();
    await confirm(up.id, session, csrfOf(html));
    await ingest(`/api/ingest/${up.id}/result`, { method: "POST", body: JSON.stringify({ kind: "refused", problems: ["<script>x</script> is bad"] }) });
    const poll = await (await call(`/api/uploads/${up.id}`, { headers: auth(up.poll_token) })).json();
    assert.deepEqual(poll.result, { kind: "refused", problems: ["<script>x</script> is bad"] });
    const page = await (await call(`/claim/${up.id}`, { headers: { Cookie: session } })).text();
    assert.ok(page.includes("&lt;script&gt;x&lt;/script&gt; is bad"));
    assert.ok(!page.includes("<script>"));
  });
});

describe("the tool's calls", () => {
  test("a manifest over the limits or malformed is refused", async () => {
    const big = manifest({ files: [{ path: "a", size: LIMITS.fileBytes + 1, sha256: "a".repeat(64) }] });
    for (const mf of [
      manifest({ slug: "Bad Slug" }), manifest({ v: 2 }), manifest({ title: "x".repeat(301) }),
      manifest({ archive: { size: LIMITS.archiveBytes + 1, sha256: "a".repeat(64) } }), big,
      manifest({ files: [{ path: "../x", size: 1, sha256: "a".repeat(64) }] }),
      manifest({ files: [{ path: "a/.git/config", size: 1, sha256: "a".repeat(64) }] }),
      manifest({ files: [{ path: "/abs", size: 1, sha256: "a".repeat(64) }] }),
      manifest({ files: [{ path: "b", size: 1, sha256: "a".repeat(64) }, { path: "a", size: 1, sha256: "a".repeat(64) }] }),
      manifest({ files: [{ path: "a", size: 1, sha256: "a".repeat(64) }, { path: "a", size: 1, sha256: "a".repeat(64) }] }),
      manifest({ files: Array.from({ length: 3001 }, (_, i) => ({ path: `f${String(i).padStart(5, "0")}`, size: 1, sha256: "a".repeat(64) })) }),
      manifest({ files: Array.from({ length: 3 }, (_, i) => ({ path: `f${i}`, size: 21 * 1024 * 1024, sha256: "a".repeat(64) })) }),
    ]) {
      const { r, body } = await upload(mf);
      assert.equal(r.status, 400, JSON.stringify(mf).slice(0, 120));
      assert.ok(body.problems.length > 0);
    }
    assert.deepEqual(manifestProblems(manifest()), []);
    const r = await call("/api/uploads", { method: "POST", body: "{not json" });
    assert.equal(r.status, 400);
  });

  test("the archive needs the token and exactly the manifest's size and sha256", async () => {
    const { body: up } = await upload();
    assert.equal((await put(up.id, "wrong-token")).status, 404);
    assert.equal((await call(`/api/uploads/${up.id}`, { headers: auth("wrong-token") })).status, 404);
    assert.equal((await put(up.id, up.poll_token, archive, archive.length + 1)).status, 400);
    // one attempt: an archive that is not the manifest's ends the upload, refused
    const poll = async (u) => (await call(`/api/uploads/${u.id}`, { headers: auth(u.poll_token) })).json();
    assert.deepEqual(await poll(up), { status: "refused", check_code: up.check_code, result: { kind: "refused", problems: ["the archive did not match its manifest"] } });
    assert.equal((await put(up.id, up.poll_token)).status, 409);
    const { body: up2 } = await upload();
    const forged = Buffer.from(archive); forged[0] ^= 1;
    assert.equal((await put(up2.id, up2.poll_token, forged)).status, 400);
    assert.equal(env.SHARES.objects.has(`bundles/${up2.id}.tar.gz`), false);
    assert.equal((await put(up2.id, up2.poll_token)).status, 409);
    assert.equal((await poll(up2)).status, "refused");
    const { body: up3 } = await upload();
    assert.equal((await put(up3.id, up3.poll_token)).status, 200);
    assert.equal((await put(up3.id, up3.poll_token)).status, 409);
  });

  test("a manifest is read no further than its limit, with or without a Content-Length", async () => {
    const big = JSON.stringify(manifest({ title: "x".repeat(10) })) + " ".repeat(2 * 1024 * 1024 + 1);
    const chunked = new ReadableStream({ start(c) { c.enqueue(new TextEncoder().encode(big)); c.close(); } });
    const r = await call("/api/uploads", { method: "POST", headers: { "Content-Type": "application/json" }, body: chunked, duplex: "half" });
    assert.equal(r.status, 413);
  });

  test("a title or authors with a control character is refused", async () => {
    // a line break would carry a forged heading into the pull request's body
    for (const over of [{ title: "T**\n\n## Approved by the owner" }, { authors: "A\u0007B" }]) {
      const { r, body } = await upload(manifest(over));
      assert.equal(r.status, 400);
      assert.match(body.problems.join(" "), /control character/);
    }
  });

  test("an upload nobody signs in for expires after an hour", async () => {
    const { body: up } = await upload();
    const key = `meta/${up.id}.json`;
    const meta = JSON.parse(env.SHARES.objects.get(key).toString());
    meta.expires_at = new Date(Date.now() - 1000).toISOString();
    env.SHARES.objects.set(key, Buffer.from(JSON.stringify(meta)));
    const poll = await (await call(`/api/uploads/${up.id}`, { headers: auth(up.poll_token) })).json();
    assert.equal(poll.status, "expired");
    assert.equal((await put(up.id, up.poll_token)).status, 409);
  });

  test("an unknown or malformed id is not found", async () => {
    assert.equal((await call("/api/uploads/abc", { headers: auth("x") })).status, 404);
    assert.equal((await call("/claim/abc")).status, 404);
  });

  test("the rate limiter answers 429 when over, on the archive too", async () => {
    const { body: up } = await upload();
    env.UPLOAD_RATELIMIT = { limit: async () => ({ success: false }) };
    assert.equal((await upload()).r.status, 429);
    assert.equal((await put(up.id, up.poll_token)).status, 429);
  });
});

describe("sign-in and confirmation", () => {
  test("a tampered or foreign state, a missing nonce cookie and a bad code are refused", async () => {
    const { body: up } = await upload();
    await put(up.id, up.poll_token);
    const r1 = await call(`/claim/${up.id}`, { redirect: "manual" });
    const state = new URL(r1.headers.get("Location")).searchParams.get("state");
    const cookie = cookiesOf(r1).join("; ");
    const [payload, sig] = state.split(".");
    const forged = Buffer.from(JSON.stringify({ ...JSON.parse(Buffer.from(payload, "base64url")), id: "a".repeat(26) })).toString("base64url");
    for (const [q, c] of [
      [`code=good-code&state=${forged}.${sig}`, cookie],
      [`code=good-code&state=${encodeURIComponent(state)}`, ""],
      [`code=good-code&state=${encodeURIComponent(state)}`, "tc_oauth=someone-elses"],
      [`code=bad-code&state=${encodeURIComponent(state)}`, cookie],
      [`state=${encodeURIComponent(state)}`, cookie],
    ]) {
      const r = await call(`/auth/callback?${q}`, { headers: c ? { Cookie: c } : {} });
      assert.notEqual(r.status, 302, q);
      assert.equal(r.headers.getSetCookie().some((x) => x.startsWith("tc_session=") && !x.startsWith("tc_session=;")), false);
    }
  });

  test("an expired state is refused", async () => {
    const { body: up } = await upload();
    const realNow = Date.now;
    const r1 = await call(`/claim/${up.id}`, { redirect: "manual" });
    const state = new URL(r1.headers.get("Location")).searchParams.get("state");
    try {
      Date.now = () => realNow() + 11 * 60 * 1000;
      const r = await call(`/auth/callback?code=good-code&state=${encodeURIComponent(state)}`, { headers: { Cookie: cookiesOf(r1).join("; ") } });
      assert.equal(r.status, 400);
    } finally { Date.now = realNow; }
  });

  test("a GitHub answer without a numeric id is no identity", async () => {
    github.user = { login: "bob" };
    const { body: up } = await upload();
    const r1 = await call(`/claim/${up.id}`, { redirect: "manual" });
    const state = new URL(r1.headers.get("Location")).searchParams.get("state");
    const r = await call(`/auth/callback?code=good-code&state=${encodeURIComponent(state)}`, { headers: { Cookie: cookiesOf(r1).join("; ") } });
    assert.equal(r.status, 502);
  });

  test("a confirmation without the page's CSRF value, or from another session, is refused", async () => {
    const { up, session, html } = await signedIn();
    assert.equal((await confirm(up.id, session, "forged")).status, 403);
    // the same CSRF value under a forged session cookie
    const forgedSession = session.replace(/\.[^.]+$/, ".AAAA");
    assert.equal((await confirm(up.id, forgedSession, csrfOf(html))).status, 401);
    assert.equal(calls.some((c) => c.url.endsWith("/dispatches")), false);
    const poll = await (await call(`/api/uploads/${up.id}`, { headers: auth(up.poll_token) })).json();
    assert.equal(poll.status, "awaiting_sign_in");
  });

  test("a CSRF value is bound to its upload", async () => {
    const a = await signedIn();
    const { body: other } = await upload();
    await put(other.id, other.poll_token);
    assert.equal((await confirm(other.id, a.session, csrfOf(a.html))).status, 403);
  });

  test("a failed dispatch shares nothing and keeps the form", async () => {
    github.dispatchStatus = 500;
    const { up, session, html } = await signedIn();
    const r = await confirm(up.id, session, csrfOf(html));
    const text = await r.text();
    assert.match(text, /could not be reached/);
    assert.match(text, /<form/);
    const poll = await (await call(`/api/uploads/${up.id}`, { headers: auth(up.poll_token) })).json();
    assert.equal(poll.status, "awaiting_sign_in");
    assert.equal(poll.login, undefined);
  });

  test("two confirmations at once dispatch once; the second is told it was already confirmed", async () => {
    const { up, session, html } = await signedIn();
    const csrf = csrfOf(html);
    const [a, b] = await Promise.all([confirm(up.id, session, csrf), confirm(up.id, session, csrf)]);
    const texts = [await a.text(), await b.text()];
    assert.equal(calls.filter((c) => c.url.endsWith("/dispatches")).length, 1, "dispatches");
    // the loser either read the share submitted already, or lost the conditional write: no form either way
    assert.equal(texts.filter((t) => /<form/.test(t)).length, 0, texts.join("\n----\n"));
    assert.ok(texts.every((t) => /Submitted/.test(t)), texts.join("\n----\n"));
    const poll = await (await call(`/api/uploads/${up.id}`, { headers: auth(up.poll_token) })).json();
    assert.equal(poll.status, "submitted");
  });

  test("a confirmation that loses the write to another one dispatches nothing", async () => {
    const { up, session, html } = await signedIn();
    // another confirmation records the share between this one's read and its write
    const bucket = env.SHARES, realPut = bucket.put.bind(bucket);
    bucket.put = async (key, value, opts = {}) => {
      if (opts.onlyIf && key === `meta/${up.id}.json`) {
        const meta = JSON.parse(bucket.objects.get(key).toString());
        await realPut(key, JSON.stringify({ ...meta, status: "submitted", identity: { login: "bob", id: 7 } }));
      }
      return realPut(key, value, opts);
    };
    const text = await (await confirm(up.id, session, csrfOf(html))).text();
    assert.match(text, /already confirmed/);
    assert.equal(calls.filter((c) => c.url.endsWith("/dispatches")).length, 0);
    const poll = await (await call(`/api/uploads/${up.id}`, { headers: auth(up.poll_token) })).json();
    assert.equal(poll.login, "bob");
  });

  test("the GitHub token is revoked even when asking who signed in fails", async () => {
    const realUser = github.user;
    const { body: up } = await upload();
    assert.equal((await put(up.id, up.poll_token)).status, 200);
    const r1 = await call(`/claim/${up.id}`, { redirect: "manual" });
    const state = new URL(r1.headers.get("Location")).searchParams.get("state");
    const inner = globalThis.fetch;
    globalThis.fetch = async (input, init) => { if (String(input) === "https://api.github.com/user") throw new Error("network down"); return inner(input, init); };
    const r2 = await call(`/auth/callback?code=good-code&state=${encodeURIComponent(state)}`, { headers: { Cookie: cookiesOf(r1).join("; ") } });
    globalThis.fetch = inner;
    github.user = realUser;
    assert.equal(r2.status, 502);
    assert.ok(calls.some((c) => c.url.startsWith("https://api.github.com/applications/") && c.method === "DELETE"), "the token was not revoked");
  });

  test("the claim page says how to switch GitHub accounts", async () => {
    const { html } = await signedIn();
    assert.match(html, /sign out of <a href="https:\/\/github.com\/logout">github.com<\/a> too/);
  });

  test("a claim before the archive arrived says to wait, with no form", async () => {
    const { body: up } = await upload();
    const r1 = await call(`/claim/${up.id}`, { redirect: "manual" });
    const state = new URL(r1.headers.get("Location")).searchParams.get("state");
    const r2 = await call(`/auth/callback?code=good-code&state=${encodeURIComponent(state)}`, { headers: { Cookie: cookiesOf(r1).join("; ") } });
    const text = await (await call(`/claim/${up.id}`, { headers: { Cookie: cookiesOf(r2).join("; ") } })).text();
    assert.match(text, /not finished/);
    assert.ok(!text.includes("<form"));
  });

  test("logout clears the session and redirects only within the worker", async () => {
    let r = await call("/auth/logout?to=/claim/abc", { redirect: "manual" });
    assert.equal(r.headers.get("Location"), "/claim/abc");
    assert.ok(r.headers.getSetCookie().some((c) => c.startsWith("tc_session=;")));
    for (const to of ["//evil.example", "https://evil.example", "/\\evil.example"]) {
      r = await call(`/auth/logout?to=${encodeURIComponent(to)}`, { redirect: "manual" });
      assert.equal(r.headers.get("Location"), "/");
    }
  });
});

describe("the ingest endpoints", () => {
  test("take a base64 secret (+, / and =) as the bearer token", async () => {
    env.INGEST_SECRET = "ab+cd/ef==";
    const { body: up } = await upload();
    assert.equal((await call(`/api/ingest/${up.id}`, { headers: auth("ab+cd/ef==") })).status, 200);
    assert.equal((await call(`/api/ingest/${up.id}`, { headers: auth("ab+cd/ef") })).status, 401);
  });

  test("need the ingest secret", async () => {
    const { body: up } = await upload();
    for (const p of [`/api/ingest/${up.id}`, `/api/ingest/${up.id}/archive`]) {
      assert.equal((await call(p)).status, 401);
      assert.equal((await call(p, { headers: auth("ingest-secreT") })).status, 401);
    }
    assert.equal((await call(`/api/ingest/${up.id}/result`, { method: "POST", headers: auth(up.poll_token), body: "{}" })).status, 401);
  });

  test("refuse a result before the sharer confirmed, or a malformed one", async () => {
    const { up, session, html } = await signedIn();
    assert.equal((await ingest(`/api/ingest/${up.id}/result`, { method: "POST", body: JSON.stringify({ kind: "published" }) })).status, 409);
    await confirm(up.id, session, csrfOf(html));
    for (const body of [{ kind: "awaiting_upload" }, { kind: "published", url: "javascript:alert(1)" }, { kind: "refused", problems: "nope" }]) {
      assert.equal((await ingest(`/api/ingest/${up.id}/result`, { method: "POST", body: JSON.stringify(body) })).status, 400);
    }
    assert.equal((await ingest(`/api/ingest/${up.id}/result`, { method: "POST", body: JSON.stringify({ kind: "published", url: `${SITE}papers/my_paper/` }) })).status, 200);
  });
});

test("esc escapes the five HTML characters", () => {
  assert.equal(esc(`<a href="x" onclick='y'>&</a>`), "&lt;a href=&quot;x&quot; onclick=&#39;y&#39;&gt;&amp;&lt;/a&gt;");
});

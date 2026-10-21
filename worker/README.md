# Share worker

The one server-side piece of sharing: `worker.js`, a Cloudflare Worker at
`https://theoremchecker-share.comments-worker.workers.dev/`. It needs no npm package; the tests are
`test/worker.test.mjs` (`npm test` from the repository root).

## What it does

1. **Receives a bundle.** The sharer's PaperFormalizer sends a manifest (`POST /api/uploads`: slug,
   title, authors, arXiv id, every file's path, size and sha256, the archive's size and sha256) and
   gets back an upload id, a poll token, a four-letter check code and a claim link. It then sends the
   archive (`PUT /api/uploads/<id>`, with the poll token). R2 stores it and checks its sha256.
2. **Learns who is sharing.** The claim link (`/claim/<id>`) signs the sharer in with GitHub through
   a **classic OAuth App authorized with no scope**: the consent screen says "public data only", and
   the token can do nothing but read public data. The worker asks GitHub `/user` for the login and
   numeric id, then revokes the token at once; what it keeps is a signed session cookie (one hour).
   A GitHub App would show "Act on your behalf" whatever its permissions, so it is never used here.
3. **Asks for confirmation.** The claim page shows the title, the slug, the size, the check code
   (the sharer's own page shows the same code) and "as @login", and says that the TeX source, the
   PDF, the Lean and the report become public. Only the button on that page, with its CSRF value,
   submits.
4. **Hands over to the registry.** On confirmation it sends a `repository_dispatch` (`share`, with
   the upload id) to the registry, with the owner's dispatch token. The ingest workflow reads the
   manifest and the archive back (`/api/ingest/<id>`, `/api/ingest/<id>/archive`, with
   `INGEST_SECRET`), checks and adds the paper, and posts the outcome (`/api/ingest/<id>/result`:
   published, review or refused). The archive is then deleted.
5. **Reports.** The tool polls `GET /api/uploads/<id>` with its poll token until the outcome is in.

An upload nobody confirms within the hour expires. Nothing here writes to GitHub as the sharer.

## Deploy

All commands run from this directory, with `wrangler` logged in to the owner's Cloudflare account
(`npx wrangler whoami`).

1. **R2.** Enable R2 in the Cloudflare dashboard once (R2 → enable; the free tier needs a card on
   file). Then:

       npx wrangler r2 bucket create paperformalizer-share
       npx wrangler r2 bucket lifecycle add paperformalizer-share bundles-2d bundles/ --expire-days 2 --force
       npx wrangler r2 bucket lifecycle add paperformalizer-share meta-30d meta/ --expire-days 30 --force

   The worker deletes each archive itself once ingested; the rules sweep what is left behind.

2. **The OAuth App.** GitHub → Settings → Developer settings → **OAuth Apps** (not GitHub Apps) →
   New OAuth App:
   - Homepage URL: `https://paperformalizer.org/`
   - Authorization callback URL: `https://theoremchecker-share.comments-worker.workers.dev/auth/callback`
   - Device flow: off.

   Put its client id (`Ov23…`) in `wrangler.toml` as `GITHUB_CLIENT_ID`, and generate a client
   secret for step 4.

3. **The dispatch token.** GitHub → Settings → Developer settings → Fine-grained tokens → Generate:
   resource owner `Jiyuan-Tan`, repository access "Only select repositories" →
   `PaperFormalizerPapers`, permissions **Contents: Read and write** (Metadata: read is added by
   itself), nothing else. Note its expiry date: sharing stops when it expires, until a new one is
   set.

4. **Secrets** (each prompts for its value):

       npx wrangler secret put GITHUB_CLIENT_SECRET
       npx wrangler secret put GITHUB_DISPATCH_TOKEN
       openssl rand -base64 48 | npx wrangler secret put SESSION_SECRET
       S=$(openssl rand -hex 32)
       printf %s "$S" | npx wrangler secret put INGEST_SECRET

   The INGEST_SECRET value is also the registry's Actions secret of that name:

       printf %s "$S" | gh secret set INGEST_SECRET -R Jiyuan-Tan/PaperFormalizerPapers; unset S

5. **Deploy:** `npx wrangler deploy`. Check it: `curl https://theoremchecker-share.comments-worker.workers.dev/`
   answers a one-line page.

Rotating `SESSION_SECRET` signs everyone out (pending uploads stay claimable). Rotating
`INGEST_SECRET` needs both places changed together.

## Limits

The worker refuses a manifest over the registry's limits before anything is stored: 3000 files,
60 MiB in all, 24 MiB per file, a 64 MiB archive, a slug of `^[a-z0-9][a-z0-9_-]{0,79}$`, paths
relative with no dot segment or dotfile. The archive must be sent with a `Content-Length` equal to
the manifest's size (no chunked upload). Per-IP rate limits: 5 uploads and 20 sign-in or claim
requests a minute (`wrangler.toml`).

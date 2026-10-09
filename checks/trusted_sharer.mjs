#!/usr/bin/env node
// Whether a pull request that passes the check may merge itself:
//   PR_AUTHOR=<login> TRUSTED_SHARERS=<login>,<login>,… node checks/trusted_sharer.mjs
// prints `trusted=true` or `trusted=false` (a line for $GITHUB_OUTPUT). TRUSTED_SHARERS is the
// repository variable of that name: the GitHub logins whose shares merge without the owner, or `*`
// for everyone. Unset or empty: nobody — every pull request waits for the owner.
// The seal is a checksum, not a signature: an account can make a bundle that passes the check with
// content of its own, so who may publish unattended is the owner's choice.
import path from "node:path";
import { fileURLToPath } from "node:url";

/** Pure. A GitHub login is compared without regard to case. */
export function trustedSharer(author, list) {
  const names = String(list ?? "").split(",").map((s) => s.trim().toLowerCase()).filter(Boolean);
  return Boolean(author) && (names.includes("*") || names.includes(String(author).toLowerCase()));
}

if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  console.log(`trusted=${trustedSharer(process.env.PR_AUTHOR, process.env.TRUSTED_SHARERS)}`);
}

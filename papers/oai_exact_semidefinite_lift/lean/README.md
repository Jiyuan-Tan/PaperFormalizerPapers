# Lean formalization — oai_exact_semidefinite_lift

A standalone Lake project: `Papers/OaiExactSemidefiniteLift/` is the Lean development of the corrected paper (16 file(s)). It depends on the public libraries listed below and on nothing else; what it uses of the author's own library is copied here.

## Build

Lean toolchain: `leanprover/lean4:v4.33.0` (`lean-toolchain`; `elan` installs it). From this directory:

```
lake exe cache get   # fetches the libraries and Mathlib's compiled files
lake build
lake env lean Check.lean   # the axioms of each result
```

`lake build` builds `Papers` and `Toolkit` (`Papers.OaiExactSemidefiniteLift` is the paper). There is no `lake-manifest.json`: Lake writes it on the first command, from the revisions the lakefile pins.

## Libraries it requires

- `Causalean` (Causal inference and statistics foundations (identification, estimation, semiparametrics, concentration).): `https://github.com/Jiyuan-Tan/CausalSmith` at `a7085d88d2e4b30003db7097ca374f4718da0f01`; it brings in `FoML`, `Optlib`
- `mathlib` (the Lean mathematical library): `https://github.com/leanprover-community/mathlib4` at `db584cd6d46c92f209a44c0f1c829460d327499d`

Note: built against a local copy of Causalean (its commit 5ca94e0ac387): 4 file(s) of it are reached, recorded by content hash in `built-against.json`. That they are the files of the public revision a7085d88d2e4 this bundle requires was NOT verified (not possible offline): `paperformalizer report oai_exact_semidefinite_lift --verify-public` compares them over the network; by hand: `git hash-object <file>` in the local checkout against the blob hashes of `https://github.com/Jiyuan-Tan/CausalSmith` at `a7085d88d2e4b30003db7097ca374f4718da0f01`.

## The paper's results

- Theorem 1.1: `Papers.OaiExactSemidefiniteLift.exact_semidefinite_lift` (`Papers/OaiExactSemidefiniteLift/TMain.lean:30`)
- Lemma 2.1: `Papers.OaiExactSemidefiniteLift.gram_identity` (`Papers/OaiExactSemidefiniteLift/Helpers/Gram.lean:132`)
- Lemma 2.2: `Papers.OaiExactSemidefiniteLift.slice_equivalence` (`Papers/OaiExactSemidefiniteLift/Helpers/Slice.lean:432`)
- Lemma 3.1: `Papers.OaiExactSemidefiniteLift.matching_exists` (`Papers/OaiExactSemidefiniteLift/Helpers/Matching.lean:278`)
- Proposition 4.1: `Papers.OaiExactSemidefiniteLift.lift_equivalence` (`Papers/OaiExactSemidefiniteLift/Helpers/Lift.lean:22`)

`MATCH.md`, one directory up, sets each statement beside its declaration.

## Checking the axioms

`Check.lean` prints the axioms of each result above (`lake env lean Check.lean`, after the build): none may appear beyond `propext`, `Classical.choice` and `Quot.sound`. The source must contain no `sorry`, `admit` or `axiom`.

## What is in this directory

From the author's own library, copied here (2 module(s)): `Toolkit.Foundations.Algebra.HyperbolicPolynomials`, `Toolkit.Foundations.Algebra.PolynomialCoeffSigns`.

Imported from the required libraries: `Causalean` (2 module(s)), `Mathlib` (126 module(s)).

## Self-containment

Checked when this directory was written: every import of every file resolves to a file here or to a module of a required library, no path in a lakefile leaves this directory, and nothing names the machine it was built on.


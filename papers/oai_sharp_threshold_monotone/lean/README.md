# Lean formalization — oai_sharp_threshold_monotone

A standalone Lake project: `Papers/OaiSharpThresholdMonotone/` is the Lean development of the corrected paper (19 file(s)). It depends on the public libraries listed below and on nothing else; what it uses of the author's own library is copied here.

## Build

Lean toolchain: `leanprover/lean4:v4.33.0` (`lean-toolchain`; `elan` installs it). From this directory:

```
lake exe cache get   # fetches the libraries and Mathlib's compiled files
lake build
lake env lean Check.lean   # the axioms of each result
```

`lake build` builds `Papers` (`Papers.OaiSharpThresholdMonotone` is the paper). There is no `lake-manifest.json`: Lake writes it on the first command, from the revisions the lakefile pins.

## Libraries it requires

- `Causalean` (Causal inference and statistics foundations (identification, estimation, semiparametrics, concentration).): `https://github.com/Jiyuan-Tan/CausalSmith` at `a7085d88d2e4b30003db7097ca374f4718da0f01`; it brings in `FoML`, `Optlib`
- `mathlib` (the Lean mathematical library): `https://github.com/leanprover-community/mathlib4` at `db584cd6d46c92f209a44c0f1c829460d327499d`

Note: built against a local copy of Causalean (its commit 5ca94e0ac387, with 1 of the files reached changed since): 18 file(s) of it are reached, recorded by content hash in `built-against.json`. That they are the files of the public revision a7085d88d2e4 this bundle requires was NOT verified (not possible offline): `paperformalizer report oai_sharp_threshold_monotone --verify-public` compares them over the network; by hand: `git hash-object <file>` in the local checkout against the blob hashes of `https://github.com/Jiyuan-Tan/CausalSmith` at `a7085d88d2e4b30003db7097ca374f4718da0f01`.

## The paper's results

- Theorem 1.1: `Papers.OaiSharpThresholdMonotone.propertyQuantile_width_le` (`Papers/OaiSharpThresholdMonotone/TThreshold.lean:48`)
- Theorem 1.2: `Papers.OaiSharpThresholdMonotone.variance_le_log_sq_inv_mul_totalInfluence` (`Papers/OaiSharpThresholdMonotone/TVariance.lean:18`)
- Lemma 2.1: `Papers.OaiSharpThresholdMonotone.sum_lowDegree_fourierCoeff_sq_le` (`Papers/OaiSharpThresholdMonotone/Helpers/LowDegree.lean:215`)
- Lemma 3.1: `Papers.OaiSharpThresholdMonotone.restriction_mass_and_influence` (`Papers/OaiSharpThresholdMonotone/Helpers/Restriction.lean:233`)
- Proposition 3.2: `Papers.OaiSharpThresholdMonotone.block_average_lowDegree_mass_le` (`Papers/OaiSharpThresholdMonotone/Helpers/BlockAverage.lean:150`)
- Lemma 3.3: `Papers.OaiSharpThresholdMonotone.captured_lowDegree_mass_le` (`Papers/OaiSharpThresholdMonotone/Helpers/BlockCapture.lean:19`)

`MATCH.md`, one directory up, sets each statement beside its declaration.

## Checking the axioms

`Check.lean` prints the axioms of each result above (`lake env lean Check.lean`, after the build): none may appear beyond `propext`, `Classical.choice` and `Quot.sound`. The source must contain no `sorry`, `admit` or `axiom`.

## What is in this directory

Nothing from the author's own library.

Imported from the required libraries: `Causalean` (6 module(s)), `Mathlib` (13 module(s)).

## Self-containment

Checked when this directory was written: every import of every file resolves to a file here or to a module of a required library, no path in a lakefile leaves this directory, and nothing names the machine it was built on.


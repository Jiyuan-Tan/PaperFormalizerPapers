# Lean formalization — oai_close_separable_cstar

A standalone Lake project: `Papers/OaiCloseSeparableCstar/` is the Lean development of the corrected paper (26 file(s)). It depends on the public libraries listed below and on nothing else; what it uses of the author's own library is copied here.

## Build

Lean toolchain: `leanprover/lean4:v4.33.0` (`lean-toolchain`; `elan` installs it). From this directory:

```
lake exe cache get   # fetches the libraries and Mathlib's compiled files
lake build
lake env lean Check.lean   # the axioms of each result
```

`lake build` builds `Papers` (`Papers.OaiCloseSeparableCstar` is the paper). There is no `lake-manifest.json`: Lake writes it on the first command, from the revisions the lakefile pins.

## Libraries it requires

- `mathlib` (the Lean mathematical library): `https://github.com/leanprover-community/mathlib4` at `db584cd6d46c92f209a44c0f1c829460d327499d`

## The paper's results

- Theorem 1.1: `Papers.OaiCloseSeparableCstar.exists_close_not_conjugate` (`Papers/OaiCloseSeparableCstar/TMain.lean:50`)
- Proposition 2.1: `Papers.OaiCloseSeparableCstar.seqAlg_properties` (`Papers/OaiCloseSeparableCstar/TSequences.lean:24`)
- Lemma 2.3: `Papers.OaiCloseSeparableCstar.tensorIdentity_invariant` (`Papers/OaiCloseSeparableCstar/Helpers/Invariant.lean:153`)
- Corollary 2.4: `Papers.OaiCloseSeparableCstar.seqAlg_obstruction` (`Papers/OaiCloseSeparableCstar/TObstruction.lean:68`)
- Lemma 3.1: `Papers.OaiCloseSeparableCstar.exists_treeRep` (`Papers/OaiCloseSeparableCstar/Helpers/Tree.lean:29`)
- Lemma 4.1: `Papers.OaiCloseSeparableCstar.absorption` (`Papers/OaiCloseSeparableCstar/Helpers/LpOperators.lean:55`)
- Lemma 4.2: `Papers.OaiCloseSeparableCstar.ambient_properties` (`Papers/OaiCloseSeparableCstar/Helpers/Ambient.lean:117`)
- Lemma 4.3: `Papers.OaiCloseSeparableCstar.goodInclusion` (`Papers/OaiCloseSeparableCstar/Helpers/GoodInclusion.lean:488`)
- Lemma 4.4: `Papers.OaiCloseSeparableCstar.norm_sum_leftReg_gen_le` (`Papers/OaiCloseSeparableCstar/Helpers/FreeNorm.lean:182`)
- Lemma 4.5: `Papers.OaiCloseSeparableCstar.badInclusion` (`Papers/OaiCloseSeparableCstar/Helpers/BadInclusion.lean:182`)

`MATCH.md`, one directory up, sets each statement beside its declaration.

## Checking the axioms

`Check.lean` prints the axioms of each result above (`lake env lean Check.lean`, after the build): none may appear beyond `propext`, `Classical.choice` and `Quot.sound`. The source must contain no `sorry`, `admit` or `axiom`.

## What is in this directory

Nothing from the author's own library.

Imported from the required libraries: `Mathlib` (14 module(s)).

## Self-containment

Checked when this directory was written: every import of every file resolves to a file here or to a module of a required library, no path in a lakefile leaves this directory, and nothing names the machine it was built on.


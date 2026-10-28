# Lean formalization — oai_reconstruction_milnor_theory

A standalone Lake project: `Papers/OaiReconstructionMilnorTheory/` is the Lean development of the corrected paper (37 file(s)). It depends on the public libraries listed below and on nothing else; what it uses of the author's own library is copied here.

## Build

Lean toolchain: `leanprover/lean4:v4.33.0` (`lean-toolchain`; `elan` installs it). From this directory:

```
lake exe cache get   # fetches the libraries and Mathlib's compiled files
lake build
lake env lean Check.lean   # the axioms of each result
```

`lake build` builds `Papers` (`Papers.OaiReconstructionMilnorTheory` is the paper). There is no `lake-manifest.json`: Lake writes it on the first command, from the revisions the lakefile pins.

## Libraries it requires

- `mathlib` (the Lean mathematical library): `https://github.com/leanprover-community/mathlib4` at `db584cd6d46c92f209a44c0f1c829460d327499d`

## The paper's results

- Theorem 1.1: `Papers.OaiReconstructionMilnorTheory.milnor_reconstruction_bijective` (`Papers/OaiReconstructionMilnorTheory/TMain.lean:23`)
- Lemma 2.1: `Papers.OaiReconstructionMilnorTheory.finrank_powSubfield_eq_pow_trdeg` (`Papers/OaiReconstructionMilnorTheory/Helpers/PDegree.lean:117`)
- Lemma 2.2: `Papers.OaiReconstructionMilnorTheory.pBasis_structure` (`Papers/OaiReconstructionMilnorTheory/Helpers/PBasis.lean:522`)
- Lemma 2.3: `Papers.OaiReconstructionMilnorTheory.mem_adjoin_of_milnorSymbol_eq_zero` (`Papers/OaiReconstructionMilnorTheory/Helpers/Symbols.lean:119`)
- Lemma 2.4: `Papers.OaiReconstructionMilnorTheory.milnorSymbol_affine_eq_zero` (`Papers/OaiReconstructionMilnorTheory/Helpers/Symbols.lean:136`)
- Proposition 3.1: `Papers.OaiReconstructionMilnorTheory.intersection_unique_power` (`Papers/OaiReconstructionMilnorTheory/Helpers/Intersection.lean:28`)
- Lemma 4.1: `Papers.OaiReconstructionMilnorTheory.scalar_eq_one_of_preserves_lines` (`Papers/OaiReconstructionMilnorTheory/Helpers/ScalarLine.lean:186`)
- Proposition 4.2: `Papers.OaiReconstructionMilnorTheory.exists_unique_line_correction` (`Papers/OaiReconstructionMilnorTheory/Helpers/Lines.lean:36`)
- Proposition 5.1: `Papers.OaiReconstructionMilnorTheory.projective_lift` (`Papers/OaiReconstructionMilnorTheory/Helpers/ProjectiveLift.lean:47`)
- Lemma 5.2: `Papers.OaiReconstructionMilnorTheory.iInter_pow_eq_base` (`Papers/OaiReconstructionMilnorTheory/Helpers/PerfectCore.lean:218`)

`MATCH.md`, one directory up, sets each statement beside its declaration.

## Checking the axioms

`Check.lean` prints the axioms of each result above (`lake env lean Check.lean`, after the build): none may appear beyond `propext`, `Classical.choice` and `Quot.sound`. The source must contain no `sorry`, `admit` or `axiom`.

## What is in this directory

Nothing from the author's own library.

Imported from the required libraries: `Mathlib` (48 module(s)).

## Self-containment

Checked when this directory was written: every import of every file resolves to a file here or to a module of a required library, no path in a lakefile leaves this directory, and nothing names the machine it was built on.


# Lean formalization — oai_near_inclusions_von

A standalone Lake project: `Papers/OaiNearInclusionsVon/` is the Lean development of the corrected paper (49 file(s)). It depends on the public libraries listed below and on nothing else; what it uses of the author's own library is copied here.

## Build

Lean toolchain: `leanprover/lean4:v4.33.0` (`lean-toolchain`; `elan` installs it). From this directory:

```
lake exe cache get   # fetches the libraries and Mathlib's compiled files
lake build
lake env lean Check.lean   # the axioms of each result
```

`lake build` builds `Papers` and `Toolkit` (`Papers.OaiNearInclusionsVon` is the paper). There is no `lake-manifest.json`: Lake writes it on the first command, from the revisions the lakefile pins.

## Libraries it requires

- `mathlib` (the Lean mathematical library): `https://github.com/leanprover-community/mathlib4` at `db584cd6d46c92f209a44c0f1c829460d327499d`

## The paper's results

- Theorem 1.1: `Papers.OaiNearInclusionsVon.near_inclusion_not_implemented_by_small_unitaries` (`Papers/OaiNearInclusionsVon/TMain.lean:43`)
- Proposition 2.1: `Papers.OaiNearInclusionsVon.circle_family_exists` (`Papers/OaiNearInclusionsVon/TCircle.lean:22`)
- Proposition 3.1: `Papers.OaiNearInclusionsVon.near_inclusion_bound` (`Papers/OaiNearInclusionsVon/TNear.lean:28`)
- Lemma 4.1: `Papers.OaiNearInclusionsVon.clock_shift_not_near_commuting` (`Papers/OaiNearInclusionsVon/Helpers/Clock.lean:554`)
- Lemma 4.2: `Papers.OaiNearInclusionsVon.corner_commuting_approximants` (`Papers/OaiNearInclusionsVon/Helpers/CornerFinalization.lean:225`)

`MATCH.md`, one directory up, sets each statement beside its declaration.

## Checking the axioms

`Check.lean` prints the axioms of each result above (`lake env lean Check.lean`, after the build): none may appear beyond `propext`, `Classical.choice` and `Quot.sound`. The source must contain no `sorry`, `admit` or `axiom`.

## What is in this directory

From the author's own library, copied here (4 module(s)): `Toolkit.Foundations.Analysis.Normed.CStarNormBounds`, `Toolkit.Foundations.Analysis.Normed.FiniteDimensionalOperators`, `Toolkit.Foundations.Analysis.Normed.WeakOperatorLimits`, `Toolkit.Foundations.Analysis.SpecialFunctions.ComplexExpLevelSet`.

Imported from the required libraries: `Mathlib` (174 module(s)).

## Moved into the author's library

Results first proved for this paper and since moved into the library, where the paper now uses them:

- `Toolkit.Foundations.Analysis.Normed.exists_norm_le_one_tendsto_inner_of_forall_norm_le_one`
- `Toolkit.Foundations.Analysis.Normed.min_norm_norm_sub_one_le_norm_sub_of_mem_spectrum`
- `Toolkit.Foundations.Analysis.SpecialFunctions.eq_of_cexp_eq_one_of_isPreconnected`
- `Toolkit.Foundations.Analysis.Normed.mem_unitary_of_forall_norm_apply_eq`
- `Toolkit.Foundations.Analysis.Normed.iSup_eigenspace_eq_top_of_isStarNormal`
- `Toolkit.Foundations.Analysis.Normed.norm_mul_mul_star_mul_star_sub_one_eq_norm_commutator`
- `Toolkit.Foundations.Analysis.Normed.norm_mul_sub_mul_le_of_mem_unitary`
- `Toolkit.Foundations.Analysis.Normed.mem_vonNeumannAlgebra_of_tendsto_inner`
- `Toolkit.Foundations.Analysis.Normed.norm_pow_mul_sub_mul_pow_le_mul_norm_commutator`

## Self-containment

Checked when this directory was written: every import of every file resolves to a file here or to a module of a required library, no path in a lakefile leaves this directory, and nothing names the machine it was built on.


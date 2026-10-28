# Lean formalization — oai_capacity_criterion_state

A standalone Lake project: `Papers/OaiCapacityCriterionState/` is the Lean development of the corrected paper (36 file(s)). It depends on the public libraries listed below and on nothing else; what it uses of the author's own library is copied here.

## Build

Lean toolchain: `leanprover/lean4:v4.33.0` (`lean-toolchain`; `elan` installs it). From this directory:

```
lake exe cache get   # fetches the libraries and Mathlib's compiled files
lake build
lake env lean Check.lean   # the axioms of each result
```

`lake build` builds `Papers` (`Papers.OaiCapacityCriterionState` is the paper). There is no `lake-manifest.json`: Lake writes it on the first command, from the revisions the lakefile pins.

## Libraries it requires

- `mathlib` (the Lean mathematical library): `https://github.com/leanprover-community/mathlib4` at `db584cd6d46c92f209a44c0f1c829460d327499d`

## The paper's results

- Theorem 1.1: `OaiCapacityCriterionState.reconstructs_iff_capacity_pos` (`Papers/OaiCapacityCriterionState/TMain.lean:26`)
- Lemma 3.1: `OaiCapacityCriterionState.exists_flow_of_labels` (`Papers/OaiCapacityCriterionState/Helpers/Flow.lean:199`)
- Lemma 4.1: `OaiCapacityCriterionState.local_moment_bounds` (`Papers/OaiCapacityCriterionState/Helpers/LocalMoments.lean:607`)

`MATCH.md`, one directory up, sets each statement beside its declaration.

## Checking the axioms

`Check.lean` prints the axioms of each result above (`lake env lean Check.lean`, after the build): none may appear beyond `propext`, `Classical.choice` and `Quot.sound`. The source must contain no `sorry`, `admit` or `axiom`.

## What is in this directory

Nothing from the author's own library.

Imported from the required libraries: `Mathlib` (34 module(s)).

## Self-containment

Checked when this directory was written: every import of every file resolves to a file here or to a module of a required library, no path in a lakefile leaves this directory, and nothing names the machine it was built on.


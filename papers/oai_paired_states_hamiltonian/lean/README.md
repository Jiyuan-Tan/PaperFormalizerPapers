# Lean formalization — oai_paired_states_hamiltonian

A standalone Lake project: `Papers/OaiPairedStatesHamiltonian/` is the Lean development of the corrected paper (101 file(s)). It depends on the public libraries listed below and on nothing else; what it uses of the author's own library is copied here.

## Build

Lean toolchain: `leanprover/lean4:v4.33.0` (`lean-toolchain`; `elan` installs it). From this directory:

```
lake exe cache get   # fetches the libraries and Mathlib's compiled files
lake build
lake env lean Check.lean   # the axioms of each result
```

`lake build` builds `Papers` (`Papers.OaiPairedStatesHamiltonian` is the paper). There is no `lake-manifest.json`: Lake writes it on the first command, from the revisions the lakefile pins.

## Libraries it requires

- `mathlib` (the Lean mathematical library): `https://github.com/leanprover-community/mathlib4` at `db584cd6d46c92f209a44c0f1c829460d327499d`

## The paper's results

- Theorem 1.1: `OaiPairedStatesHamiltonian.isHamiltonian_of_mainDomain` (`Papers/OaiPairedStatesHamiltonian/TMain.lean:23`)
- Lemma 2.1: `OaiPairedStatesHamiltonian.SphereMap.dual_compl_spanning` (`Papers/OaiPairedStatesHamiltonian/Helpers/Duality.lean:42`)
- Theorem 2.2: `OaiPairedStatesHamiltonian.exists_tree_partition` (`Papers/OaiPairedStatesHamiltonian/TPartition.lean:29`)
- Proposition 3.1: `OaiPairedStatesHamiltonian.exists_pair_of_noSeparatingTriangle` (`Papers/OaiPairedStatesHamiltonian/Helpers/Pairs.lean:106`)
- Lemma 4.1: `OaiPairedStatesHamiltonian.delta_sum_of_simple_cycle` (`Papers/OaiPairedStatesHamiltonian/Helpers/Disk.lean:123`)
- Proposition 5.1: `OaiPairedStatesHamiltonian.exists_pair_qs_forest` (`Papers/OaiPairedStatesHamiltonian/Helpers/ForestState.lean:173`)
- Lemma 5.2: `OaiPairedStatesHamiltonian.sum_Z_terms_eq_zero_of_cyclic` (`Papers/OaiPairedStatesHamiltonian/Helpers/Cancel.lean:78`)
- Lemma 5.3: `OaiPairedStatesHamiltonian.exists_positive_spoke_weights` (`Papers/OaiPairedStatesHamiltonian/Helpers/Circulation.lean:391`)
- Lemma 6.1: `OaiPairedStatesHamiltonian.qs_component_contains_unique_root` (`Papers/OaiPairedStatesHamiltonian/Helpers/RootComponents.lean:44`)
- Lemma 6.2: `OaiPairedStatesHamiltonian.selectedSet_isForest` (`Papers/OaiPairedStatesHamiltonian/Helpers/PForest.lean:23`)
- Corollary 7.1: `OaiPairedStatesHamiltonian.exists_hamiltonian_avoiding_edge` (`Papers/OaiPairedStatesHamiltonian/TEdgeAvoidance.lean:24`)
- Corollary 7.2: `OaiPairedStatesHamiltonian.p4Hamiltonian_of_pfaffian` (`Papers/OaiPairedStatesHamiltonian/TPfaffianPaths.lean:53`)

`MATCH.md`, one directory up, sets each statement beside its declaration.

## Checking the axioms

`Check.lean` prints the axioms of each result above (`lake env lean Check.lean`, after the build): none may appear beyond `propext`, `Classical.choice` and `Quot.sound`. The source must contain no `sorry`, `admit` or `axiom`.

## What is in this directory

Nothing from the author's own library.

Imported from the required libraries: `Mathlib` (28 module(s)).

## Self-containment

Checked when this directory was written: every import of every file resolves to a file here or to a module of a required library, no path in a lakefile leaves this directory, and nothing names the machine it was built on.


# Lean formalization — oai_geometric_erdos_similarity

A standalone Lake project: `Papers/OaiGeometricErdosSimilarity/` is the Lean development of the corrected paper (22 file(s)). It depends on the public libraries listed below and on nothing else; what it uses of the author's own library is copied here.

## Build

Lean toolchain: `leanprover/lean4:v4.33.0` (`lean-toolchain`; `elan` installs it). From this directory:

```
lake exe cache get   # fetches the libraries and Mathlib's compiled files
lake build
lake env lean Check.lean   # the axioms of each result
```

`lake build` builds `Papers` (`Papers.OaiGeometricErdosSimilarity` is the paper). There is no `lake-manifest.json`: Lake writes it on the first command, from the revisions the lakefile pins.

## Libraries it requires

- `Causalean` (Causal inference and statistics foundations (identification, estimation, semiparametrics, concentration).): `https://github.com/Jiyuan-Tan/CausalSmith` at `a7085d88d2e4b30003db7097ca374f4718da0f01`; it brings in `FoML`, `Optlib`
- `mathlib` (the Lean mathematical library): `https://github.com/leanprover-community/mathlib4` at `db584cd6d46c92f209a44c0f1c829460d327499d`

Note: built against a local copy of Causalean (its commit 5ca94e0ac387, with 1 of the files reached changed since): 10 file(s) of it are reached, recorded by content hash in `built-against.json`. That they are the files of the public revision a7085d88d2e4 this bundle requires was NOT verified (not possible offline): `paperformalizer report oai_geometric_erdos_similarity --verify-public` compares them over the network; by hand: `git hash-object <file>` in the local checkout against the blob hashes of `https://github.com/Jiyuan-Tan/CausalSmith` at `a7085d88d2e4b30003db7097ca374f4718da0f01`.

## The paper's results

- Theorem 1.1: `Papers.OaiGeometricErdosSimilarity.exists_compact_avoiding_geometric_affine_copies` (`Papers/OaiGeometricErdosSimilarity/TMain.lean:451`)
- Proposition 2.1: `Papers.OaiGeometricErdosSimilarity.exists_open_periodic_hitting_set` (`Papers/OaiGeometricErdosSimilarity/TPeriodic.lean:588`)
- Lemma 3.1: `Papers.OaiGeometricErdosSimilarity.blockEndpoint_sub_windowStart_le` (`Papers/OaiGeometricErdosSimilarity/Helpers/Windows.lean:145`)
- Lemma 3.2: `Papers.OaiGeometricErdosSimilarity.stableSet_measurable_density_and_keys` (`Papers/OaiGeometricErdosSimilarity/Helpers/Stability.lean:332`)
- Lemma 3.3: `Papers.OaiGeometricErdosSimilarity.gridKey_injective_on_translated_window` (`Papers/OaiGeometricErdosSimilarity/Helpers/Windows.lean:249`)
- Lemma 4.1: `Papers.OaiGeometricErdosSimilarity.expected_periodicDensity_randomSet_eq` (`Papers/OaiGeometricErdosSimilarity/Helpers/Tables.lean:366`)
- Lemma 4.2: `Papers.OaiGeometricErdosSimilarity.localTest_imp_mem_randomSet` (`Papers/OaiGeometricErdosSimilarity/Helpers/LocalRouting.lean:307`)
- Lemma 4.3: `Papers.OaiGeometricErdosSimilarity.condPr_forall_localTest_false_eq` (`Papers/OaiGeometricErdosSimilarity/Helpers/Routing.lean:620`)
- Lemma 5.1: `Papers.OaiGeometricErdosSimilarity.condPr_exists_scale_miss_le` (`Papers/OaiGeometricErdosSimilarity/Helpers/Scales.lean:92`)

`MATCH.md`, one directory up, sets each statement beside its declaration.

## Checking the axioms

`Check.lean` prints the axioms of each result above (`lake env lean Check.lean`, after the build): none may appear beyond `propext`, `Classical.choice` and `Quot.sound`. The source must contain no `sorry`, `admit` or `axiom`.

## What is in this directory

Nothing from the author's own library.

Imported from the required libraries: `Causalean` (1 module(s)), `Mathlib` (16 module(s)).

## Self-containment

Checked when this directory was written: every import of every file resolves to a file here or to a module of a required library, no path in a lakefile leaves this directory, and nothing names the machine it was built on.


# Lean formalization — oai_graph_decompositions_integral

A standalone Lake project: `Papers/OaiGraphDecompositionsIntegral/` is the Lean development of the corrected paper (54 file(s)). It depends on the public libraries listed below and on nothing else; what it uses of the author's own library is copied here.

## Build

Lean toolchain: `leanprover/lean4:v4.33.0` (`lean-toolchain`; `elan` installs it). From this directory:

```
lake exe cache get   # fetches the libraries and Mathlib's compiled files
lake build
lake env lean Check.lean   # the axioms of each result
```

`lake build` builds `Papers` and `Toolkit` (`Papers.OaiGraphDecompositionsIntegral` is the paper). There is no `lake-manifest.json`: Lake writes it on the first command, from the revisions the lakefile pins.

## Libraries it requires

- `Causalean` (Causal inference and statistics foundations (identification, estimation, semiparametrics, concentration).): `https://github.com/Jiyuan-Tan/CausalSmith` at `a7085d88d2e4b30003db7097ca374f4718da0f01`; it brings in `FoML`, `Optlib`
- `mathlib` (the Lean mathematical library): `https://github.com/leanprover-community/mathlib4` at `db584cd6d46c92f209a44c0f1c829460d327499d`

Note: built against a local copy of Causalean (its commit 5ca94e0ac387, with 1 of the files reached changed since): 13 file(s) of it are reached, recorded by content hash in `built-against.json`. That they are the files of the public revision a7085d88d2e4 this bundle requires was NOT verified (not possible offline): `paperformalizer report oai_graph_decompositions_integral --verify-public` compares them over the network; by hand: `git hash-object <file>` in the local checkout against the blob hashes of `https://github.com/Jiyuan-Tan/CausalSmith` at `a7085d88d2e4b30003db7097ca374f4718da0f01`.

## The paper's results

- Theorem 1.1: `Papers.OaiGraphDecompositionsIntegral.main` (`Papers/OaiGraphDecompositionsIntegral/TMain.lean:34`)
- Corollary 2.2: `Papers.OaiGraphDecompositionsIntegral.typical_cover` (`Papers/OaiGraphDecompositionsIntegral/TTypicalCover.lean:20`)
- Lemma 2.3: `Papers.OaiGraphDecompositionsIntegral.q_lower` (`Papers/OaiGraphDecompositionsIntegral/Helpers/QLower.lean:247`)
- Lemma 2.4: `Papers.OaiGraphDecompositionsIntegral.degeneracy_split` (`Papers/OaiGraphDecompositionsIntegral/Helpers/Degeneracy.lean:212`)
- Lemma 3.1: `Papers.OaiGraphDecompositionsIntegral.compression` (`Papers/OaiGraphDecompositionsIntegral/Helpers/Compression.lean:160`)
- Proposition 3.2: `Papers.OaiGraphDecompositionsIntegral.transfer` (`Papers/OaiGraphDecompositionsIntegral/TTransfer.lean:24`)
- Proposition 4.1: `Papers.OaiGraphDecompositionsIntegral.degree_embedding` (`Papers/OaiGraphDecompositionsIntegral/TDegreeEmbedding.lean:25`)
- Proposition 4.2: `Papers.OaiGraphDecompositionsIntegral.stars` (`Papers/OaiGraphDecompositionsIntegral/TStars.lean:56`)

`MATCH.md`, one directory up, sets each statement beside its declaration.

## Checking the axioms

`Check.lean` prints the axioms of each result above (`lake env lean Check.lean`, after the build): none may appear beyond `propext`, `Classical.choice` and `Quot.sound`. The source must contain no `sorry`, `admit` or `axiom`.

## What is in this directory

From the author's own library, copied here (1 module(s)): `Toolkit.Foundations.Probability.BiasedCube`.

Imported from the required libraries: `Causalean` (11 module(s)), `Mathlib` (46 module(s)).

## Self-containment

Checked when this directory was written: every import of every file resolves to a file here or to a module of a required library, no path in a lakefile leaves this directory, and nothing names the machine it was built on.


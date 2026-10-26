# Lean formalization — oai_metric_markov_cotype

A standalone Lake project: `Papers/OaiMetricMarkovCotype/` is the Lean development of the corrected paper (22 file(s)). It depends on the public libraries listed below and on nothing else; what it uses of the author's own library is copied here.

## Build

Lean toolchain: `leanprover/lean4:v4.33.0` (`lean-toolchain`; `elan` installs it). From this directory:

```
lake exe cache get   # fetches the libraries and Mathlib's compiled files
lake build
lake env lean Check.lean   # the axioms of each result
```

`lake build` builds `Papers` and `Toolkit` (`Papers.OaiMetricMarkovCotype` is the paper). There is no `lake-manifest.json`: Lake writes it on the first command, from the revisions the lakefile pins.

## Libraries it requires

- `Causalean` (Causal inference and statistics foundations (identification, estimation, semiparametrics, concentration).): `https://github.com/Jiyuan-Tan/CausalSmith` at `a7085d88d2e4b30003db7097ca374f4718da0f01`; it brings in `FoML`, `Optlib`
- `mathlib` (the Lean mathematical library): `https://github.com/leanprover-community/mathlib4` at `db584cd6d46c92f209a44c0f1c829460d327499d`
- `StatLean` (Mathematical statistics: estimation, hypothesis testing, asymptotic statistics, nonparametrics, time series (adapted Stat-Lean).): no public repository carries the adapted copy this was built with, so it is included in `vendor/StatLean/` with its licence (`vendor/StatLean/UPSTREAM.md`: where it comes from)

Note: built against a local copy of Causalean (its commit 5ca94e0ac387, with 1 of the files reached changed since): 15 file(s) of it are reached, recorded by content hash in `built-against.json`. That they are the files of the public revision a7085d88d2e4 this bundle requires was NOT verified (not possible offline): `paperformalizer report oai_metric_markov_cotype --verify-public` compares them over the network; by hand: `git hash-object <file>` in the local checkout against the blob hashes of `https://github.com/Jiyuan-Tan/CausalSmith` at `a7085d88d2e4b30003db7097ca374f4718da0f01`.

## The paper's results

- Theorem 1.2: `Papers.OaiMetricMarkovCotype.metricMarkovCotypeConstant_realEllOne_le` (`Papers/OaiMetricMarkovCotype/TMain.lean:47`)
- Lemma 2.1: `Papers.OaiMetricMarkovCotype.cut_decomposition` (`Papers/OaiMetricMarkovCotype/Helpers/Cuts.lean:569`)
- Lemma 3.1: `Papers.OaiMetricMarkovCotype.flat_cubic_bound` (`Papers/OaiMetricMarkovCotype/Helpers/Flat.lean:161`)
- Corollary 3.2: `Papers.OaiMetricMarkovCotype.martingale_cubic_energy_bound` (`Papers/OaiMetricMarkovCotype/TMartingale.lean:198`)
- Lemma 4.1: `Papers.OaiMetricMarkovCotype.geometric_endpoint_comparison` (`Papers/OaiMetricMarkovCotype/Helpers/Comparison.lean:518`)
- Corollary 6.1: `Papers.OaiMetricMarkovCotype.metricMarkovCotypeConstant_complexEllOne_le` (`Papers/OaiMetricMarkovCotype/TComplex.lean:275`)
- Corollary 6.2: `Papers.OaiMetricMarkovCotype.lipschitz_extension_hilbert_to_ellOne` (`Papers/OaiMetricMarkovCotype/TExtension.lean:69`)

`MATCH.md`, one directory up, sets each statement beside its declaration.

## Checking the axioms

`Check.lean` prints the axioms of each result above (`lake env lean Check.lean`, after the build): none may appear beyond `propext`, `Classical.choice` and `Quot.sound`. The source must contain no `sorry`, `admit` or `axiom`.

## What is in this directory

From the author's own library, copied here (11 module(s)): `Toolkit.Foundations.Probability.Conditioning.MarkovTransitions`, `Toolkit.Foundations.Probability.LimitTheorems.BoundedMartingaleDifferences`, `Toolkit.Foundations.Probability.LimitTheorems.FiniteMarkovChain`, `Toolkit.Foundations.Probability.LongRunVariance`, `Toolkit.Foundations.Probability.PoissonEquation`, `Toolkit.Foundations.Probability.Processes.ConditionalExpectation`, `Toolkit.Foundations.Probability.Processes.DeterministicIteration`, `Toolkit.Foundations.Probability.Processes.NaturalFiltration`, `Toolkit.Foundations.Probability.Processes.PathLaw`, `Toolkit.Foundations.Probability.Processes.PathProjection`, `Toolkit.Foundations.Probability.Processes.RandomUpdate`.

Imported from the required libraries: `Batteries` (1 module(s)), `Causalean` (3 module(s)), `Mathlib` (285 module(s)), `StatLean` (1 module(s)).

## Self-containment

Checked when this directory was written: every import of every file resolves to a file here or to a module of a required library, no path in a lakefile leaves this directory, and nothing names the machine it was built on.


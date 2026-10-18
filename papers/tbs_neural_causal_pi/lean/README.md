# Lean formalization — tbs_neural_causal_pi

A standalone Lake project: `Papers/TbsNeuralCausalPi/` is the Lean development of the corrected paper (275 file(s)). It depends on the public libraries listed below and on nothing else; what it uses of the author's own library is copied here.

## Build

Lean toolchain: `leanprover/lean4:v4.33.0` (`lean-toolchain`; `elan` installs it). From this directory:

```
lake exe cache get   # fetches the libraries and Mathlib's compiled files
lake build
lake env lean Check.lean   # the axioms of each result
```

`lake build` builds `Papers` and `Toolkit` (`Papers.TbsNeuralCausalPi` is the paper). There is no `lake-manifest.json`: Lake writes it on the first command, from the revisions the lakefile pins.

## Libraries it requires

- `Causalean` (Causal inference and statistics foundations (identification, estimation, semiparametrics, concentration).): `https://github.com/Jiyuan-Tan/CausalSmith` at `a7085d88d2e4b30003db7097ca374f4718da0f01`; it brings in `FoML`, `Optlib`
- `mathlib` (the Lean mathematical library): `https://github.com/leanprover-community/mathlib4` at `db584cd6d46c92f209a44c0f1c829460d327499d`
- `StatLean` (Mathematical statistics: estimation, hypothesis testing, asymptotic statistics, nonparametrics, time series (adapted Stat-Lean).): no public repository carries the adapted copy this was built with, so it is included in `vendor/StatLean/` with its licence (`vendor/StatLean/UPSTREAM.md`: where it comes from)

Note: built against a local copy of Causalean (its commit 5ca94e0ac387): 66 file(s) of it are reached, recorded by content hash in `built-against.json`. That they are the files of the public revision a7085d88d2e4 this bundle requires was NOT verified (not possible offline): `theoremchecker report tbs_neural_causal_pi --verify-public` compares them over the network; by hand: `git hash-object <file>` in the local checkout against the blob hashes of `https://github.com/Jiyuan-Tan/CausalSmith` at `a7085d88d2e4b30003db7097ca374f4718da0f01`.

## The paper's results

- Theorem 3.3: `Papers.TbsNeuralCausalPi.approximation_wasserstein_bound` (`Papers/TbsNeuralCausalPi/TApproximation.lean:30`)
- Theorem 3.6: `Papers.TbsNeuralCausalPi.wide_generator_approximation` (`Papers/TbsNeuralCausalPi/TWideNn.lean:112`)
- Corollary 3.6.1: `Papers.TbsNeuralCausalPi.deep_generator_approximation` (`Papers/TbsNeuralCausalPi/TCorFix3c402872.lean:21`)
- Corollary 3.8: `Papers.TbsNeuralCausalPi.deep_ncm_approximation` (`Papers/TbsNeuralCausalPi/TDeepNn.lean:303`)
- Proposition 4.1: `Papers.TbsNeuralCausalPi.counterexample_identifiable` (`Papers/TbsNeuralCausalPi/TCounterexample.lean:53`)
- Theorem 4.2: `Papers.TbsNeuralCausalPi.consistency` (`Papers/TbsNeuralCausalPi/TConsistency.lean:189`)
- Proposition 4.3: `Papers.TbsNeuralCausalPi.lipschitz_dose_response_gap` (`Papers/TbsNeuralCausalPi/TLipAte.lean:48`)
- Corollary 4.4: `Papers.TbsNeuralCausalPi.rate_of_convergence` (`Papers/TbsNeuralCausalPi/TRate.lean:87`)
- Proposition B.1: `Papers.TbsNeuralCausalPi.exists_canonical_representation` (`Papers/TbsNeuralCausalPi/TEquivalentGConstrianed.lean:39`)
- Proposition B.2: `Papers.TbsNeuralCausalPi.exists_measure_representing_holder_curve` (`Papers/TbsNeuralCausalPi/Helpers/HilbertCurve.lean:386`)
- Lemma B.3: `Papers.TbsNeuralCausalPi.hilbert_ordering` (`Papers/TbsNeuralCausalPi/Helpers/HilbertCurve.lean:121`)
- Proposition C.1: `Papers.TbsNeuralCausalPi.counterexample_backdoor` (`Papers/TbsNeuralCausalPi/TCounterexampleForal.lean:60`)
- Proposition C.2: `Papers.TbsNeuralCausalPi.convgOpt_limits_mem` (`Papers/TbsNeuralCausalPi/Helpers/ConvgOpt.lean:193`)
- Lemma C.3: `Papers.TbsNeuralCausalPi.regression_gap_le_wasserstein` (`Papers/TbsNeuralCausalPi/Helpers/RegressionComparison.lean:335`)
- Lemma E.1: `Papers.TbsNeuralCausalPi.wasserstein_map_le` (`Papers/TbsNeuralCausalPi/Helpers/WassersteinBounds.lean:154`)
- Lemma E.2: `Papers.TbsNeuralCausalPi.wasserstein_mixture_le` (`Papers/TbsNeuralCausalPi/Helpers/WassersteinBounds.lean:303`)
- Lemma E.3: `Papers.TbsNeuralCausalPi.wasserstein_pi_le` (`Papers/TbsNeuralCausalPi/Helpers/WassersteinBounds.lean:467`)
- Lemma E.4: `Papers.TbsNeuralCausalPi.wasserstein_gumbelSoftmax_le` (`Papers/TbsNeuralCausalPi/Helpers/GumbelSoftmax.lean:515`)
- Lemma E.5: `Papers.TbsNeuralCausalPi.sinkhorn_approx` (`Papers/TbsNeuralCausalPi/Helpers/Sinkhorn.lean:164`)
- Lemma E.6: `Papers.TbsNeuralCausalPi.uniform_empirical_wasserstein` (`Papers/TbsNeuralCausalPi/Helpers/EmpiricalWasserstein.lean:190`)

`MATCH.md`, one directory up, sets each statement beside its declaration.

## Checking the axioms

`Check.lean` prints the axioms of each result above (`lake env lean Check.lean`, after the build): none may appear beyond `propext`, `Classical.choice` and `Quot.sound`. The source must contain no `sorry`, `admit` or `axiom`.

## What is in this directory

From the author's own library, copied here (15 module(s)): `Toolkit.Foundations.LinearAlgebra.AffineGeneralPosition`, `Toolkit.Foundations.MeasureTheory.KantorovichRubinstein`, `Toolkit.Foundations.MeasureTheory.Quantization`, `Toolkit.Foundations.MeasureTheory.Wasserstein`, `Toolkit.Foundations.Optimization.Convex.FiniteTransport`, `Toolkit.Foundations.Probability.Conditioning.ConditioningOnEvent`, `Toolkit.Foundations.Probability.Independence.ProductConditioning`, `Toolkit.Foundations.Topology.BarycentricSubdivision`, `Toolkit.Foundations.Topology.ChainVertexWeights`, `Toolkit.Foundations.Topology.EquivariantGeneralPosition`, `Toolkit.Foundations.Topology.EquivariantTransversality`, `Toolkit.Foundations.Topology.PiecewiseAffine`, `Toolkit.Foundations.Topology.PiecewiseAffineApproximation`, `Toolkit.Foundations.Topology.SimplicialAction`, `Toolkit.Foundations.Topology.SubdivisionMesh`.

Imported from the required libraries: `Causalean` (16 module(s)), `Mathlib` (446 module(s)), `StatLean` (2 module(s)).

## Self-containment

Checked when this directory was written: every import of every file resolves to a file here or to a module of a required library, no path in a lakefile leaves this directory, and nothing names the machine it was built on.


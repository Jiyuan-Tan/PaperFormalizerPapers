module
public import Papers.TbsNeuralCausalPi.Helpers.ObservationalCompactConcentration
public import Papers.TbsNeuralCausalPi.Helpers.ObservationalSamplingRate
/-! # Complete observational sampling from the cited concentration theorem

Positive total latent dimension uses the conditional joint-law estimate,
including its critical dimension-two logarithm. Zero total dimension uses
the finite complete-observation table, retaining categorical randomness.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory Filter
open scoped NNReal ENNReal Topology

variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}

-- @node: canonical_observational_sampling_rate_of_fournier
/-- Assume [the Fournier–Guillin small-deviation bound](hyp:hFournierGuillin_of_gate),
with [nonnegative bounds K and L](hyp:K,L), [model variables bounded at K](hyp:hK),
and [continuous mechanisms Lipschitz with bound L](hyp:hL). For [a family of
observational samples indexed by sample size](hyp:sample) whose draws are
[measurable](hyp:hsample), [independent at each sample size](hyp:hind), and
[distributed according to the model's observational law](hyp:hlaw), [there
exist positive constants A and B such that eventually the probability that
the empirical Wasserstein-1 error exceeds A times the observational tolerance
in the total latent dimension is at most B times the inverse fourth power
of the sample size](goal). -/
lemma canonical_observational_sampling_rate_of_fournier
    (hFournierGuillin_of_gate : FournierGuillinSmallDeviation)
    {Omega : Type*} [MeasurableSpace Omega]
    (Q : Measure Omega) [IsProbabilityMeasure Q] (M : EuclideanSCM kind dims)
    (K L : ℝ≥0) (hK : VariablesBoundedAt M K)
    (hL : ContinuousMechanismsLipschitz M L)
    (sample : ∀ m, Fin m → Omega → Joint kind)
    (hsample : ∀ m i, Measurable (sample m i))
    (hind : ∀ m, ProbabilityTheory.iIndepFun (sample m) Q)
    (hlaw : ∀ m i, Q.map (sample m i) = observationalLaw M) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ᶠ m : ℕ in atTop,
      Q {w | ¬ wasserstein1 (observationalLaw M)
        (empiricalMeasure (fun i => sample m i w)) ≤
          ENNReal.ofReal (A * observationalRateScale (∑ j, dims j) m)} ≤
        ENNReal.ofReal (B * (m : ℝ)^(-(4 : ℤ))) := by
  by_cases hd : ∑ j, dims j = 0
  · obtain ⟨A, B, hA, hB, htail⟩ :=
      zero_latent_observational_sampling_rate Q M hd sample hsample hind hlaw
    refine ⟨A, B, hA, hB, ?_⟩
    simpa only [hd, observationalRateScale, max_eq_left (by omega : 0 ≤ 2),
      Nat.cast_ofNat, zpow_neg, zpow_ofNat, div_eq_mul_inv, mul_assoc] using htail
  · have hdpos : 0 < ∑ j, dims j := Nat.pos_of_ne_zero hd
    obtain ⟨B, rate, hB, hrate, hexp⟩ :=
      categoricalStratum_vector_exponential_bound_of_fournier
        hFournierGuillin_of_gate M K hK hdpos
    have htail := categoricalStratum_compact_latent_tails_of_exponential_bound
      M K hK hdpos B rate hB hrate hexp
    exact canonical_observational_sampling_rate_of_compact_latent_tails
      Q M K L hK hL sample hsample hind hlaw B hB htail

end Papers.TbsNeuralCausalPi

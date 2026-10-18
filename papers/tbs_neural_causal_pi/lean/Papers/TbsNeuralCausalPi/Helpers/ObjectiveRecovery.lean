module
public import Papers.TbsNeuralCausalPi.Helpers.ObjectiveTransport
public import Papers.TbsNeuralCausalPi.Helpers.BoundedPopulationTransport
public import Papers.TbsNeuralCausalPi.Helpers.EstimationCandidateBounds
/-! # Objective recovery on the original bounded structural domains -/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
noncomputable section
variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
  {C : Fin b → Set (Fin n)}

/-- If [the scale factor is positive](hyp:hq) and [the product of a and x,
replaced by one when nonpositive, is less than one](hyp:hsmall), then
[multiplying this extended value by the scale factor equals first scaling
a and then applying the same positive-extension rule](goal). -/
-- @node: positive_extension_scale_of_lt_one
lemma positive_extension_scale_of_lt_one {a q x : ℝ} (hq : 0 < q)
    (hsmall : (if 0 < a * x then a * x else 1) < 1) :
    q * (if 0 < a * x then a * x else 1) =
      (if 0 < (q * a) * x then (q * a) * x else 1) := by
  have hax : 0 < a * x := by
    by_contra h
    simpa only [if_neg h, lt_self_iff_false] using hsmall
  have hqax : 0 < (q * a) * x := by
    simpa only [mul_assoc] using mul_pos hq hax
  rw [if_pos hax, if_pos hqax, mul_assoc]

/-- For [the latent generator input dimensions in each block](hyp:dC),
[a common variable bound K](hyp:K), and [a restriction parameter L](hyp:L),
if [K is positive](hyp:hK), [every categorical label count is at most K](hyp:hlabels),
and [the candidate satisfies the output and generator restrictions at K
and L](hyp:hR), then [all variables of its canonical structural causal model
are bounded by K](goal). -/
-- @node: restrictedCandidate_variablesBoundedAt_original
lemma restrictedCandidate_variablesBoundedAt_original {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C}
    (dC : ∀ j, Fin (counts j) → ℕ) (K L : ℝ≥0) (hK : 0 < K)
    (hlabels : ∀ i k, kind i = Sum.inr k → (k : ℝ) ≤ K)
    (D c1 c2 : ℕ) (L1 L2 : ℕ → ℕ) (tau : ℕ → ℝ) (r : ℕ)
    (R : NCMIn kind dims dag G C counts F0
      (generatorClassN counts dC K D c1 c2 L1 L2 tau r))
    (hR : restrictedCandidate K L R) :
    VariablesBoundedAt R.canonical.toEuclideanSCM K := by
  refine ⟨by exact_mod_cast hK, ?_⟩
  filter_upwards [ncm_generatorClassN_latent_ae_bound dC K D c1 c2 L1 L2 tau r R]
    with u hu
  refine ⟨?_, hu⟩
  intro i j
  exact canonical_evalSteps_coordinate_bound R.canonical K hlabels
    (restrictedCandidate_continuous_output_bound K L R hR)
    (noIntervention kind) (by simp [noIntervention]) u (n * n + n) i j

/-- For [a common Lipschitz bound L](hyp:L) and [a common variable bound K](hyp:K)
with [K positive](hyp:hK), [there is a positive constant Q, uniform across
comparison models, such that under the stated structural independence,
Gumbel, Lipschitz, and boundedness assumptions, a total mechanism and latent-law
error at most delta bounds the observational Wasserstein distance by Q times
delta and the absolute finite objective difference by the larger of the
objective's Lipschitz constant and one times Q times delta, for every
admissible intervention distribution and integrable Lipschitz objective](goal).

Mechanism errors are measured on the original structural cubes, and latent-law
errors use the non-Gumbel block marginals. The intervention domain need only
have full probability. -/
-- @node: bounded_objective_recovery_bound
lemma bounded_objective_recovery_bound (L K : ℝ≥0) (hK : 0 < K) :
    ∃ Q : ℝ≥0, 0 < Q ∧
      ∀ (M N : CanonicalSCM kind dims dag G C),
      M ∈ canonicalClass (domainLipClass M L) →
      LatentBlocksIndependent M.toEuclideanSCM →
      LatentGumbelDecomposition M.toEuclideanSCM →
      CategoricalGumbelArgmax M.toEuclideanSCM M.f →
      ContinuousMechanismsLipschitz M.toEuclideanSCM L →
      CategoricalPropensityLipschitz M.toEuclideanSCM M.f L →
      VariablesBoundedAt M.toEuclideanSCM K →
      VariablesBoundedAt N.toEuclideanSCM K →
      (∀ i d, kind i = Sum.inl d → ∀ x ∈ M.domain i, ‖M.f i x‖ ≤ K) →
      (∀ i d, kind i = Sum.inl d → ∀ x ∈ N.domain i, ‖N.f i x‖ ≤ K) →
      ∀ {I : Type*} [MeasurableSpace I] (t : I → LawIntervention kind)
        (muT : Measure I) [IsProbabilityMeasure muT] (domain : Set I),
      populationObjectiveDomain K domain t muT →
      ∀ (F : Joint kind → ℝ) (LF : ℝ≥0), LipschitzWith LF F →
      objectiveDefined M.toEuclideanSCM t muT F →
      objectiveDefined N.toEuclideanSCM t muT F →
      ∀ delta : ℝ, 0 ≤ delta →
      (∑ i, supDistOn (M.domain i (some (-(K : ℝ), K))) (M.f i) (N.f i)) +
        (∑ j, wasserstein1 (M.blockLaw j : Measure (L1Vec (dims j)))
          (N.blockLaw j : Measure (L1Vec (dims j)))) ≤ ENNReal.ofReal delta →
      wasserstein1 (observationalLaw N.toEuclideanSCM)
        (observationalLaw M.toEuclideanSCM) ≤ ENNReal.ofReal ((Q : ℝ) * delta) ∧
      |objectiveIntegral N.toEuclideanSCM t muT F -
        objectiveIntegral M.toEuclideanSCM t muT F| ≤
          max (LF : ℝ) 1 * ((Q : ℝ) * delta) := by
  obtain ⟨Q, hQ, htransport⟩ := bounded_interventional_wasserstein_bound
    (kind := kind) (dims := dims) (dag := dag) (G := G) (C := C) L K hK
  refine ⟨Q, hQ, ?_⟩
  intro M N hclass hind hdecomp hcat hcont hprop hM hN hMout hNout
    I _ t muT _ domain hdomain F LF hF hMi hNi delta hdelta herr
  have hW : ∀ t' : LawIntervention kind,
      (∀ i v, t'.val i = some v → ∀ j, |v.ofLp j| ≤ K) →
      wasserstein1 (interventionalLaw M.toEuclideanSCM t')
        (interventionalLaw N.toEuclideanSCM t') ≤ ENNReal.ofReal ((Q : ℝ) * delta) := by
    intro t' ht'
    have h := (htransport M N hdomain.1 hclass hind hdecomp hcat hcont hprop
      hM hN hMout hNout t' ht').trans (mul_le_mul' le_rfl herr)
    simpa only [ENNReal.ofReal_mul Q.coe_nonneg, ENNReal.ofReal_coe_nnreal] using h
  have hsymm : ∀ t', wasserstein1 (interventionalLaw N.toEuclideanSCM t')
      (interventionalLaw M.toEuclideanSCM t') =
      wasserstein1 (interventionalLaw M.toEuclideanSCM t')
        (interventionalLaw N.toEuclideanSCM t') := by
    intro t'
    exact wasserstein1_symm
      (⟨_, by
        let := N.toEuclideanSCM.probability
        exact Measure.isProbabilityMeasure_map (by fun_prop)⟩ : ProbabilityMeasure (Joint kind))
      (⟨_, by
        let := M.toEuclideanSCM.probability
        exact Measure.isProbabilityMeasure_map (by fun_prop)⟩ : ProbabilityMeasure (Joint kind))
  constructor
  · exact (hsymm (noIntervention kind)).trans_le
      (hW (noIntervention kind) (by simp [noIntervention]))
  · apply objectiveIntegral_abs_sub_le_of_interventional_transport
      N.toEuclideanSCM M.toEuclideanSCM t muT F hF
      (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) (le_max_left _ _)
      hNi hMi (mul_nonneg Q.coe_nonneg hdelta)
    have hmem : ∀ᵐ s ∂muT, s ∈ domain := ae_iff.mpr hdomain.2.2
    filter_upwards [hmem] with s hs
    exact (hsymm (t s)).trans_le (hW (t s) (hdomain.2.1 s hs))

end
end Papers.TbsNeuralCausalPi

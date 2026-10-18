module
public import Papers.TbsNeuralCausalPi.TApproximation
public import Papers.TbsNeuralCausalPi.Helpers.DeepModelAssembly
public import Papers.TbsNeuralCausalPi.Helpers.BoundedEvaluation
/-! # Observational transport from distances on the bounded input cubes

Projection of structural inputs preserves valid categorical labels. For models
whose observed and non-Gumbel variables lie in the cube, it also preserves the
observational law. Thus the full-domain approximation theorem controls the
cube-domain distance used by consistency, with identical categorical Gumbels.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
open scoped NNReal ENNReal
noncomputable section

variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
  {C : Fin b → Set (Fin n)}

/-- For [a nonnegative box radius K](hyp:K), if [every categorical node's number
of labels is at most K](hyp:hlabels) and [x is an admissible input at node i](hyp:hx),
[clamping x to the box of radius K gives an admissible input in the bounded
structural domain at i](goal). -/
-- @node: structuralBoxProjection_mem_bounded_domain
lemma structuralBoxProjection_mem_bounded_domain
    (M : CanonicalSCM kind dims dag G C) (K : ℝ≥0)
    (hlabels : ∀ i k, kind i = Sum.inr k → (k : ℝ) ≤ K)
    (i : Fin n) (x : Input kind dims dag C i) (hx : x ∈ M.domain i) :
    structuralBoxProjection M K i x ∈ M.domain i (some (-(K : ℝ), K)) := by
  refine ⟨(structuralBoxProjection_mem_domain M K hlabels i x hx).1, ?_⟩
  intro j
  change max (-(K : ℝ)) (min (x.ofLp j) K) ∈ Set.Icc (-(K : ℝ)) K
  exact ⟨le_max_left _ _, max_le (by linarith [K.coe_nonneg]) (min_le_right _ _)⟩

/-- For [a nonnegative box radius K](hyp:K), if [every categorical node's number
of labels is at most K](hyp:hlabels), [the uniform mechanism discrepancy between
the two truncated models on the full admissible domain at i is at most the
original models' discrepancy on the admissible cube of radius K](goal). -/
-- @node: supDistOn_boxTruncatedSCM_le
lemma supDistOn_boxTruncatedSCM_le
    (M N : CanonicalSCM kind dims dag G C) (K : ℝ≥0)
    (hlabels : ∀ i k, kind i = Sum.inr k → (k : ℝ) ≤ K) (i : Fin n) :
    supDistOn ((boxTruncatedSCM M K hlabels).domain i)
      ((boxTruncatedSCM M K hlabels).f i) ((boxTruncatedSCM N K hlabels).f i) ≤
        supDistOn (M.domain i (some (-(K : ℝ), K))) (M.f i) (N.f i) := by
  apply iSup_le
  intro x
  exact le_iSup_of_le
    ⟨structuralBoxProjection M K i x.val,
      structuralBoxProjection_mem_bounded_domain M K hlabels i x.val x.property⟩ le_rfl

/-- For [a nonnegative box radius K](hyp:K), if [every categorical node's number
of labels is at most K](hyp:hlabels) and [the observed variables and non-Gumbel
latent coordinates are bounded by K](hyp:hbound), [box truncation leaves the
observational law unchanged](goal). -/
-- @node: boxTruncatedSCM_observationalLaw_eq
lemma boxTruncatedSCM_observationalLaw_eq
    (M : CanonicalSCM kind dims dag G C) (K : ℝ≥0)
    (hlabels : ∀ i k, kind i = Sum.inr k → (k : ℝ) ≤ K)
    (hbound : VariablesBoundedAt M.toEuclideanSCM K) :
    observationalLaw (boxTruncatedSCM M K hlabels).toEuclideanSCM =
      observationalLaw M.toEuclideanSCM := by
  apply Measure.map_congr
  exact (boxTruncatedSCM_observational_eval_eq M K K hlabels le_rfl hbound).mono
    (fun _ hu => hu.1)

/-- For [nonnegative Lipschitz and variable bounds L and K](hyp:L,K) with
[K positive](hyp:hK), [there is a positive constant A bounding the observational
Wasserstein distance by A times the sum of mechanism errors on admissible input
cubes of radius K and latent block Wasserstein distances, whenever the labels
fit in the cube, the true model has L-Lipschitz structural maps, independent
latent blocks, a Gumbel decomposition and categorical argmax representation,
L-Lipschitz continuous mechanisms and categorical propensities, and both models'
observed and non-Gumbel latent variables are bounded by K](goal). -/
-- @node: bounded_observational_wasserstein_bound
lemma bounded_observational_wasserstein_bound (L K : ℝ≥0) (hK : 0 < K) :
    ∃ A : ℝ≥0, 0 < A ∧
      ∀ (M N : CanonicalSCM kind dims dag G C),
      (∀ i k, kind i = Sum.inr k → (k : ℝ) ≤ K) →
      M ∈ canonicalClass (domainLipClass M L) →
      LatentBlocksIndependent M.toEuclideanSCM →
      LatentGumbelDecomposition M.toEuclideanSCM →
      CategoricalGumbelArgmax M.toEuclideanSCM M.f →
      ContinuousMechanismsLipschitz M.toEuclideanSCM L →
      CategoricalPropensityLipschitz M.toEuclideanSCM M.f L →
      VariablesBoundedAt M.toEuclideanSCM K →
      VariablesBoundedAt N.toEuclideanSCM K →
      wasserstein1 (observationalLaw M.toEuclideanSCM)
        (observationalLaw N.toEuclideanSCM) ≤
        (A : ℝ≥0∞) * ((∑ i,
          supDistOn (M.domain i (some (-(K : ℝ), K))) (M.f i) (N.f i)) +
          ∑ j, wasserstein1 (M.blockLaw j : Measure (L1Vec (dims j)))
            (N.blockLaw j : Measure (L1Vec (dims j)))) := by
  obtain ⟨A, hA⟩ := approximation_wasserstein_bound (kind := kind) (dag := dag)
    (G := G) L K (by exact_mod_cast hK)
  refine ⟨A + 1, by positivity, ?_⟩
  intro M N hlabels hclass hind hdecomp hcat hcont hprop hbound hNbound
  let MB := boxTruncatedSCM M K hlabels
  let NB := boxTruncatedSCM N K hlabels
  obtain ⟨hi, hd, hc, hco, hp, hb, hlaw⟩ := boxTruncatedSCM_atoms M L K K
    hlabels le_rfl hclass hind hdecomp hcat hcont hprop hbound
  have h := hA b dims C (fun _ => Set.univ) MB NB
    (boxTruncatedSCM_regular M L K hlabels hclass) (fun _ => Set.mem_univ _)
    hi hd hc hco hp hb (noIntervention kind)
  change wasserstein1 (observationalLaw MB.toEuclideanSCM)
    (observationalLaw NB.toEuclideanSCM) ≤ _ at h
  rw [boxTruncatedSCM_observationalLaw_eq M K hlabels hbound,
    boxTruncatedSCM_observationalLaw_eq N K hlabels hNbound] at h
  apply h.trans
  apply mul_le_mul'
  · exact_mod_cast (le_add_of_nonneg_right (by positivity : (0 : ℝ≥0) ≤ 1) : A ≤ A + 1)
  · apply add_le_add
    · exact Finset.sum_le_sum (fun i _ => supDistOn_boxTruncatedSCM_le M N K hlabels i)
    · exact deep_ncm_latent_error_le_sum MB NB

/-- For [nonnegative Lipschitz and variable bounds L and K](hyp:L,K) with
[K positive](hyp:hK), [there is a positive constant A bounding interventional
Wasserstein distance by A times the sum of mechanism errors on admissible input
cubes of radius K and latent block Wasserstein distances, uniformly over
interventions with coordinates bounded by K, provided the labels fit in the
cube, the true model has L-Lipschitz structural maps, independent latent blocks,
a Gumbel decomposition and categorical argmax representation, L-Lipschitz
continuous mechanisms and categorical propensities, both models have observed
and non-Gumbel latent variables bounded by K, and both models' continuous
mechanisms have output norm at most K throughout their admissible domains](goal). -/
-- @node: bounded_interventional_wasserstein_bound
lemma bounded_interventional_wasserstein_bound (L K : ℝ≥0) (hK : 0 < K) :
    ∃ A : ℝ≥0, 0 < A ∧
      ∀ (M N : CanonicalSCM kind dims dag G C),
      (∀ i k, kind i = Sum.inr k → (k : ℝ) ≤ K) →
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
      ∀ t : LawIntervention kind,
      (∀ i v, t.val i = some v → ∀ j, |v.ofLp j| ≤ K) →
      wasserstein1 (interventionalLaw M.toEuclideanSCM t)
        (interventionalLaw N.toEuclideanSCM t) ≤
        (A : ℝ≥0∞) * ((∑ i,
          supDistOn (M.domain i (some (-(K : ℝ), K))) (M.f i) (N.f i)) +
          ∑ j, wasserstein1 (M.blockLaw j : Measure (L1Vec (dims j)))
            (N.blockLaw j : Measure (L1Vec (dims j)))) := by
  obtain ⟨A, hA⟩ := approximation_wasserstein_bound (kind := kind) (dag := dag)
    (G := G) L K (by exact_mod_cast hK)
  refine ⟨A + 1, by positivity, ?_⟩
  intro M N hlabels hclass hind hdecomp hcat hcont hprop hbound hNbound hMout hNout t ht
  let MB := boxTruncatedSCM M K hlabels
  let NB := boxTruncatedSCM N K hlabels
  obtain ⟨hi, hd, hc, hco, hp, hb, _⟩ := boxTruncatedSCM_atoms M L K K
    hlabels le_rfl hclass hind hdecomp hcat hcont hprop hbound
  have h := hA b dims C (fun _ => Set.univ) MB NB
    (boxTruncatedSCM_regular M L K hlabels hclass) (fun _ => Set.mem_univ _)
    hi hd hc hco hp hb t
  rw [boxTruncatedSCM_interventionalLaw_eq_of_output_bound M K hlabels hMout hbound t ht,
    boxTruncatedSCM_interventionalLaw_eq_of_output_bound N K hlabels hNout hNbound t ht] at h
  apply h.trans
  apply mul_le_mul'
  · exact_mod_cast (le_add_of_nonneg_right (by positivity : (0 : ℝ≥0) ≤ 1) : A ≤ A + 1)
  · exact add_le_add
      (Finset.sum_le_sum (fun i _ => supDistOn_boxTruncatedSCM_le M N K hlabels i))
      (deep_ncm_latent_error_le_sum MB NB)

end
end Papers.TbsNeuralCausalPi

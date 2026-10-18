module
public import Papers.TbsNeuralCausalPi.Helpers.EmpiricalTransportMeasurability
public import Papers.TbsNeuralCausalPi.Helpers.FixedLabelCompactLatents
public import Papers.TbsNeuralCausalPi.Helpers.DiscreteWasserstein
/-! # Conditional joint latent laws in their total non-Gumbel dimension

Reindexing is an isometry for the one-norm. The conditional law is the actual
joint law, with no product assumption after conditioning. Its bounded support
supplies exponential moments uniformly over the finitely many label strata.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}

-- @node: jointLatentCoordinateEquiv
/-- For [block dimensions](hyp:dims), the [coordinate bijection](goal) identifies
each block-and-within-block index with a single index in the total dimension. -/
def jointLatentCoordinateEquiv (dims : Fin b → ℕ) :
    (Σ j, Fin (dims j)) ≃ Fin (∑ j, dims j) :=
  (Fintype.equivFin _).trans (finCongr (by simp))

-- @node: jointLatentVectorEquiv
/-- For [block dimensions](hyp:dims), the [latent vector isometry](goal) flattens
the joint latent coordinates into a vector of the total dimension, preserving
linear operations and the one-norm. -/
def jointLatentVectorEquiv (dims : Fin b → ℕ) :
    Latent dims ≃ₗᵢ[ℝ] L1Vec (∑ j, dims j) :=
  LinearIsometryEquiv.piLpCongrLeft 1 ℝ ℝ (jointLatentCoordinateEquiv dims)

-- @node: jointLatentVectorEquiv_measurable
/-- [Flattening the joint latent coordinates into a vector is measurable](goal). -/
@[fun_prop] lemma jointLatentVectorEquiv_measurable :
    Measurable (jointLatentVectorEquiv dims) := by
  fun_prop

-- @node: jointLatentVectorEquiv_symm_measurable
/-- [Recovering the joint latent coordinates from their flattened vector is
measurable](goal). -/
@[fun_prop] lemma jointLatentVectorEquiv_symm_measurable :
    Measurable (jointLatentVectorEquiv dims).symm := by
  fun_prop

-- @node: jointLatentVectorEquiv_mem_cube
/-- For [a nonnegative radius](hyp:K) and a joint latent vector, [the flattened vector
lies in the cube of that radius exactly when every original latent coordinate
has absolute value at most that radius](goal). -/
lemma jointLatentVectorEquiv_mem_cube (K : ℝ≥0) (z : Latent dims) :
    jointLatentVectorEquiv dims z ∈ boundedCube (∑ j, dims j) K ↔
      z ∈ jointLatentCube dims K := by
  change (∀ a, |z.ofLp ((jointLatentCoordinateEquiv dims).symm a)| ≤ K) ↔
    ∀ a, |z.ofLp a| ≤ K
  constructor
  · intro h a
    simpa only [Equiv.symm_apply_apply] using h (jointLatentCoordinateEquiv dims a)
  · intro h a
    exact h _

-- @node: jointLatentCube_norm_le
/-- For [a nonnegative radius](hyp:K) and a joint latent vector in its cube, [its one-norm
is at most the total number of coordinates times the radius](goal). -/
lemma jointLatentCube_norm_le (K : ℝ≥0) (z : jointLatentCube dims K) :
    ‖z.val‖ ≤ (∑ j, dims j) * (K : ℝ) := by
  rw [PiLp.norm_eq_of_L1]
  calc
    _ ≤ ∑ _a : Σ j, Fin (dims j), (K : ℝ) := by
      apply Finset.sum_le_sum
      intro a _
      simpa only [Real.norm_eq_abs] using z.property a
    _ = _ := by simp

-- @node: categoricalStratumVectorLatentLaw
/-- Given [a structural causal model](hyp:M), [a nonnegative bound](hyp:K)
[on its variables](hyp:hK), and [a categorical label stratum](hyp:c), the
[vector latent law](goal) is the compact conditional joint latent law flattened
into a vector with the one-norm. -/
def categoricalStratumVectorLatentLaw (M : EuclideanSCM kind dims)
    (K : ℝ≥0) (hK : VariablesBoundedAt M K) (c : CategoricalStratum kind) :
    ProbabilityMeasure (L1Vec (∑ j, dims j)) :=
  (categoricalStratumCompactLatentLaw M K hK c).map
    ((jointLatentVectorEquiv dims).continuous.measurable.comp measurable_subtype_coe).aemeasurable

-- @node: categoricalStratumVectorLatentLaw_cube
/-- For [a nonnegative radius](hyp:K), if [the model's variables are bounded by
that radius](hyp:hK), [the vector latent law for any categorical stratum assigns
probability one to the cube of that radius](goal). -/
lemma categoricalStratumVectorLatentLaw_cube (M : EuclideanSCM kind dims)
    (K : ℝ≥0) (hK : VariablesBoundedAt M K) (c : CategoricalStratum kind) :
    (categoricalStratumVectorLatentLaw M K hK c : Measure (L1Vec (∑ j, dims j)))
      (boundedCube (∑ j, dims j) K) = 1 := by
  have hcube : MeasurableSet (boundedCube (∑ j, dims j) (K : ℝ)) := by
    change MeasurableSet {x : L1Vec (∑ j, dims j) | ∀ a, |x.ofLp a| ≤ K}
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun a => measurableSet_le (by fun_prop) measurable_const)
  rw [categoricalStratumVectorLatentLaw, ProbabilityMeasure.toMeasure_map,
    Measure.map_apply (by fun_prop) hcube]
  have he : ((jointLatentVectorEquiv dims) ∘ (Subtype.val : jointLatentCube dims K → _)) ⁻¹'
      boundedCube (∑ j, dims j) K = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    exact (jointLatentVectorEquiv_mem_cube K z.val).mpr z.property
  rw [he, measure_univ]

-- @node: categoricalStratumVectorLatentLaw_map
/-- For [a nonnegative bound](hyp:K), if [the model's variables satisfy it](hyp:hK) and
[the categorical stratum has positive observational probability](hyp:hc),
[its vector latent law is the conditional joint latent law pushed forward by
the coordinate isometry](goal). -/
lemma categoricalStratumVectorLatentLaw_map (M : EuclideanSCM kind dims)
    (K : ℝ≥0) (hK : VariablesBoundedAt M K) (c : CategoricalStratum kind)
    (hc : (observationalLaw M) (observedCategoricalStratum ⁻¹' {c}) ≠ 0) :
    (categoricalStratumVectorLatentLaw M K hK c : Measure (L1Vec (∑ j, dims j))) =
      (categoricalStratumLatentLaw M c).map (jointLatentVectorEquiv dims) := by
  rw [← categoricalStratumCompactLatentLaw_map M K hK c hc,
    Measure.map_map (by fun_prop) measurable_subtype_coe]
  rfl

-- @node: categoricalStratumVectorLatentLaw_ae_norm_le
/-- For [a nonnegative bound](hyp:K), if [the model's variables satisfy it](hyp:hK),
[the one-norm under any stratum's vector latent law is almost surely at most
the total latent dimension times that bound](goal). -/
lemma categoricalStratumVectorLatentLaw_ae_norm_le (M : EuclideanSCM kind dims)
    (K : ℝ≥0) (hK : VariablesBoundedAt M K) (c : CategoricalStratum kind) :
    ∀ᵐ z ∂(categoricalStratumVectorLatentLaw M K hK c : Measure (L1Vec (∑ j, dims j))),
      ‖z‖ ≤ (∑ j, dims j) * (K : ℝ) := by
  rw [categoricalStratumVectorLatentLaw, ProbabilityMeasure.toMeasure_map]
  apply (ae_map_iff (by fun_prop) (measurableSet_le (by fun_prop) measurable_const)).mpr
  exact Filter.Eventually.of_forall (fun z => by
    dsimp only [Function.comp_apply]
    rw [(jointLatentVectorEquiv dims).norm_map]
    exact jointLatentCube_norm_le K z)

-- @node: categoricalStratumVectorLatentLaw_integrable_exp_sq
/-- For [a nonnegative bound](hyp:K) [on the model's variables](hyp:hK),
[the exponential of the squared one-norm is integrable under every stratum's
vector latent law](goal), including strata of zero probability. -/
lemma categoricalStratumVectorLatentLaw_integrable_exp_sq (M : EuclideanSCM kind dims)
    (K : ℝ≥0) (hK : VariablesBoundedAt M K) (c : CategoricalStratum kind) :
    Integrable (fun z : L1Vec (∑ j, dims j) => Real.exp (‖z‖ ^ 2))
      (categoricalStratumVectorLatentLaw M K hK c : Measure (L1Vec (∑ j, dims j))) := by
  apply Integrable.of_bound (by fun_prop) (Real.exp (((∑ j, dims j) * (K : ℝ)) ^ 2))
  filter_upwards [categoricalStratumVectorLatentLaw_ae_norm_le M K hK c] with z hz
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  exact pow_le_pow_left₀ (norm_nonneg z) hz 2

-- @node: categoricalStratumVectorLatentLaw_exp_sq_integral_le
/-- For [a nonnegative bound](hyp:K), if [the model's variables satisfy it](hyp:hK),
[the expected exponential of the squared one-norm under any stratum's vector
latent law is at most the exponential of the squared product of total latent
dimension and that bound](goal). -/
lemma categoricalStratumVectorLatentLaw_exp_sq_integral_le (M : EuclideanSCM kind dims)
    (K : ℝ≥0) (hK : VariablesBoundedAt M K) (c : CategoricalStratum kind) :
    (∫ z, Real.exp (‖z‖ ^ 2) ∂(categoricalStratumVectorLatentLaw M K hK c : Measure (L1Vec (∑ j, dims j)))) ≤
      Real.exp (((∑ j, dims j) * (K : ℝ)) ^ 2) := by
  have h := integral_mono_ae
    (categoricalStratumVectorLatentLaw_integrable_exp_sq M K hK c)
    (integrable_const (Real.exp (((∑ j, dims j) * (K : ℝ)) ^ 2)))
    ((categoricalStratumVectorLatentLaw_ae_norm_le M K hK c).mono (fun z hz =>
      Real.exp_le_exp.mpr (pow_le_pow_left₀ (norm_nonneg z) hz 2)))
  simpa only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul] using h

-- @node: jointLatentVectorEquiv_empirical_wasserstein
/-- For any joint latent measure and finite sample, [flattening both the
measure and the sample preserves their Wasserstein distance of order one](goal). -/
lemma jointLatentVectorEquiv_empirical_wasserstein
    (mu : Measure (Latent dims)) {N : ℕ} (z : Fin N → Latent dims) :
    wasserstein1 (mu.map (jointLatentVectorEquiv dims))
      (empiricalMeasure (fun i => jointLatentVectorEquiv dims (z i))) =
      wasserstein1 mu (empiricalMeasure z) := by
  rw [← empiricalMeasure_map_eq z (jointLatentVectorEquiv dims) (by fun_prop)]
  exact wasserstein1_map_isometryEquiv (jointLatentVectorEquiv dims).toIsometryEquiv _ _

-- @node: categoricalStratumVectorLatentLaw_empirical_wasserstein
/-- For [a nonnegative bound](hyp:K), if [the model's variables satisfy it](hyp:hK) and
[the stratum has positive observational probability](hyp:hc), [the Wasserstein
distance of order one between its vector latent law and a flattened empirical
sample equals the corresponding distance in the original latent coordinates](goal). -/
lemma categoricalStratumVectorLatentLaw_empirical_wasserstein (M : EuclideanSCM kind dims)
    (K : ℝ≥0) (hK : VariablesBoundedAt M K) (c : CategoricalStratum kind)
    (hc : (observationalLaw M) (observedCategoricalStratum ⁻¹' {c}) ≠ 0)
    {N : ℕ} (z : Fin N → Latent dims) :
    wasserstein1 (categoricalStratumVectorLatentLaw M K hK c : Measure (L1Vec (∑ j, dims j)))
      (empiricalMeasure (fun i => jointLatentVectorEquiv dims (z i))) =
      wasserstein1 (categoricalStratumLatentLaw M c) (empiricalMeasure z) := by
  rw [categoricalStratumVectorLatentLaw_map M K hK c hc]
  exact jointLatentVectorEquiv_empirical_wasserstein _ z

-- @node: categoricalStratum_vector_empirical_failure_eq
/-- For [a nonnegative bound](hyp:K) [on the model's variables](hyp:hK) and
[a stratum of positive observational probability](hyp:hc), [the probability
that an independent sample's empirical Wasserstein distance of order one
exceeds the nonnegative part of a given threshold is unchanged by flattening
the latent coordinates](goal). -/
lemma categoricalStratum_vector_empirical_failure_eq (M : EuclideanSCM kind dims)
    (K : ℝ≥0) (hK : VariablesBoundedAt M K) (c : CategoricalStratum kind)
    (hc : (observationalLaw M) (observedCategoricalStratum ⁻¹' {c}) ≠ 0)
    (N : ℕ) (t : ℝ) :
    (Measure.pi (fun _ : Fin N => categoricalStratumLatentLaw M c))
      {z | ¬ wasserstein1 (categoricalStratumLatentLaw M c)
        (empiricalMeasure z) ≤ ENNReal.ofReal t} =
    (Measure.pi (fun _ : Fin N =>
      (categoricalStratumVectorLatentLaw M K hK c : Measure (L1Vec (∑ j, dims j)))))
      {x | ¬ wasserstein1 (categoricalStratumVectorLatentLaw M K hK c : Measure (L1Vec (∑ j, dims j)))
        (empiricalMeasure x) ≤ ENNReal.ofReal t} := by
  let := categoricalStratumLatentLaw_probability M c hc
  have hB := measurableSet_empirical_wasserstein_failure_of_compact_mass
    (categoricalStratumVectorLatentLaw M K hK c : Measure (L1Vec (∑ j, dims j)))
    (boundedCube (∑ j, dims j) K) (boundedCube_isCompact _ _)
    (categoricalStratumVectorLatentLaw_cube M K hK c) N t
  rw [categoricalStratumVectorLatentLaw_map M K hK c hc] at hB ⊢
  rw [← Measure.pi_map_pi (fun _ : Fin N =>
    (jointLatentVectorEquiv_measurable (dims := dims)).aemeasurable),
    Measure.map_apply (by fun_prop) hB]
  congr 1
  ext z
  change (¬ wasserstein1 _ (empiricalMeasure z) ≤ _) ↔
    (¬ wasserstein1 _ (empiricalMeasure (fun i => jointLatentVectorEquiv dims (z i))) ≤ _)
  rw [jointLatentVectorEquiv_empirical_wasserstein]

-- @node: categoricalStratumVectorLatentLaw_zero_mass
/-- For [a nonnegative bound](hyp:K), if [the model's variables satisfy it](hyp:hK) and
[the stratum has zero observational probability](hyp:hc), [its vector latent
law is the point mass at the zero vector](goal). -/
lemma categoricalStratumVectorLatentLaw_zero_mass (M : EuclideanSCM kind dims)
    (K : ℝ≥0) (hK : VariablesBoundedAt M K) (c : CategoricalStratum kind)
    (hc : (observationalLaw M) (observedCategoricalStratum ⁻¹' {c}) = 0) :
    (categoricalStratumVectorLatentLaw M K hK c : Measure (L1Vec (∑ j, dims j))) = Measure.dirac 0 := by
  change ((categoricalStratumCompactLatentLaw M K hK c : Measure (jointLatentCube dims K)).map
    ((jointLatentVectorEquiv dims) ∘ Subtype.val)) = _
  rw [categoricalStratumCompactLatentLaw_zero_mass M K hK c hc,
    Measure.map_dirac' (by fun_prop)]
  congr 1

-- @node: categoricalStratumVectorObservation
/-- Given [a structural causal model](hyp:M), [a categorical stratum](hyp:c),
and [a flattened latent vector](hyp:z), the [vector observation map](goal)
recovers the joint observation by unflattening the vector and evaluating the
model with those categorical labels fixed. -/
def categoricalStratumVectorObservation (M : EuclideanSCM kind dims)
    (c : CategoricalStratum kind) (z : L1Vec (∑ j, dims j)) : Joint kind :=
  fixedLabelObservation M (categoricalStratumAssignment c) ((jointLatentVectorEquiv dims).symm z)

-- @node: categoricalStratumVectorObservation_lipschitz
/-- For [a nonnegative constant](hyp:L), if [the continuous mechanisms are
Lipschitz with that constant](hyp:hL), [each stratum's vector observation map is Lipschitz with
the fixed-label propagation budget through the full evaluation horizon](goal). -/
lemma categoricalStratumVectorObservation_lipschitz (M : EuclideanSCM kind dims)
    (L : ℝ≥0) (hL : ContinuousMechanismsLipschitz M L) (c : CategoricalStratum kind) :
    LipschitzWith (fixedLabelLipschitzBudget M L (n * n + n))
      (categoricalStratumVectorObservation M c) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  exact ((categoricalStratumObservation_lipschitz M L hL c).dist_le_mul _ _).trans_eq
    (congrArg (fun r : ℝ => (fixedLabelLipschitzBudget M L (n * n + n) : ℝ) * r)
      ((jointLatentVectorEquiv dims).symm.dist_map x y))

-- @node: categoricalStratum_vector_conditional_observation_law
/-- For [a nonnegative bound](hyp:K), if [the model's variables satisfy it](hyp:hK) and
[the stratum has positive observational probability](hyp:hc), [the
observational law conditional on that stratum is its vector latent law pushed
forward by the fixed-label vector observation map](goal). -/
lemma categoricalStratum_vector_conditional_observation_law (M : EuclideanSCM kind dims)
    (K : ℝ≥0) (hK : VariablesBoundedAt M K) (c : CategoricalStratum kind)
    (hc : (observationalLaw M) (observedCategoricalStratum ⁻¹' {c}) ≠ 0) :
    cond (observationalLaw M) (observedCategoricalStratum ⁻¹' {c}) =
      (categoricalStratumVectorLatentLaw M K hK c : Measure (L1Vec (∑ j, dims j))).map
        (categoricalStratumVectorObservation M c) := by
  rw [categoricalStratumVectorLatentLaw_map M K hK c hc,
    Measure.map_map (by fun_prop [categoricalStratumVectorObservation]) (by fun_prop),
    categoricalStratum_conditional_observation_law]
  congr 1
  funext z
  exact (congrArg (fixedLabelObservation M (categoricalStratumAssignment c))
    ((jointLatentVectorEquiv dims).symm_apply_apply z)).symm

-- @node: categoricalStratum_vector_empirical_failure_le
/-- Given [nonnegative variable and Lipschitz bounds](hyp:K,L), suppose
[the variables satisfy the first bound](hyp:hK), [the continuous mechanisms
are Lipschitz with the second](hyp:hL), [the stratum has positive observational
probability](hyp:hc), [the sample size is positive](hyp:hN), and [the latent
threshold times the full fixed-label Lipschitz budget is at most the observed
threshold](hyp:hst). Then [the conditional observed empirical Wasserstein
failure probability at the observed threshold is at most the vector latent
failure probability at the latent threshold, with both thresholds replaced by
their nonnegative parts](goal). -/
lemma categoricalStratum_vector_empirical_failure_le (M : EuclideanSCM kind dims)
    (K L : ℝ≥0) (hK : VariablesBoundedAt M K)
    (hL : ContinuousMechanismsLipschitz M L) (c : CategoricalStratum kind)
    (hc : (observationalLaw M) (observedCategoricalStratum ⁻¹' {c}) ≠ 0)
    {N : ℕ} (hN : 0 < N) (s t : ℝ)
    (hst : (fixedLabelLipschitzBudget M L (n * n + n) : ℝ) * s ≤ t) :
    (Measure.pi (fun _ : Fin N =>
      cond (observationalLaw M) (observedCategoricalStratum ⁻¹' {c})))
      {x | ¬ wasserstein1
        (cond (observationalLaw M) (observedCategoricalStratum ⁻¹' {c}))
        (empiricalMeasure x) ≤ ENNReal.ofReal t} ≤
    (Measure.pi (fun _ : Fin N =>
      (categoricalStratumVectorLatentLaw M K hK c : Measure (L1Vec (∑ j, dims j)))))
      {z | ¬ wasserstein1
        (categoricalStratumVectorLatentLaw M K hK c : Measure (L1Vec (∑ j, dims j)))
        (empiricalMeasure z) ≤ ENNReal.ofReal s} := by
  have hB := categoricalStratum_measurableSet_empirical_failure M K L hK hL c hc N t
  have hf := categoricalStratumVectorObservation_lipschitz M L hL c
  have hfm : Measurable (categoricalStratumVectorObservation M c) := by
    first | fun_prop | exact hf.continuous.measurable
  rw [categoricalStratum_vector_conditional_observation_law M K hK c hc] at hB ⊢
  rw [← Measure.pi_map_pi (fun _ : Fin N => hfm.aemeasurable),
    Measure.map_apply (by fun_prop) hB]
  apply measure_mono
  intro z hz hgood
  apply hz
  have hscaled : (fixedLabelLipschitzBudget M L (n * n + n) : ℝ≥0∞) *
      wasserstein1
        (categoricalStratumVectorLatentLaw M K hK c : Measure (L1Vec (∑ j, dims j)))
        (empiricalMeasure z) ≤
      (fixedLabelLipschitzBudget M L (n * n + n) : ℝ≥0∞) * ENNReal.ofReal s := by
    gcongr
  apply ((empirical_pushforward_wasserstein_le
    (categoricalStratumVectorLatentLaw M K hK c : Measure (L1Vec (∑ j, dims j))))
    hN z (categoricalStratumVectorObservation M c) _ hf).trans hscaled |>.trans
  rw [show (fixedLabelLipschitzBudget M L (n * n + n) : ℝ≥0∞) =
    ENNReal.ofReal (fixedLabelLipschitzBudget M L (n * n + n) : ℝ) by simp,
    ← ENNReal.ofReal_mul (fixedLabelLipschitzBudget M L (n * n + n)).coe_nonneg]
  exact ENNReal.ofReal_le_ofReal hst

end
end Papers.TbsNeuralCausalPi

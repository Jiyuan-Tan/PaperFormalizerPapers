module
public import Papers.TbsNeuralCausalPi.Helpers.DescendantAdjustment
public import Papers.TbsNeuralCausalPi.Helpers.DoseResponseNonDescendant
/-! # Marginal transport in the descendant dose-response decomposition

The covariate projection contracts the paper's one-norm. Pulling a regression
section back to the observed vector controls its marginal mean contrast without
requiring a globally Lipschitz extension outside the carrying coordinate box.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory Filter
open scoped NNReal ENNReal
noncomputable section
set_option linter.style.longLine false
set_option linter.unusedVariables false
variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
  {C : Fin b → Set (Fin n)}

/-- [The projection retaining the treatment's non-descendants and setting all other
coordinates to zero is measurable](goal). -/
-- @node: nonDescendantProjection_measurable
@[fun_prop] lemma nonDescendantProjection_measurable (T : Fin n) :
    Measurable (nonDescendantProjection (dag := dag) (kind := kind) T) := by
  first | fun_prop | skip
  apply scm_toLp_measurable.comp
  apply measurable_pi_lambda
  rintro ⟨i,j⟩
  dsimp [nonDescendantProjection]
  split_ifs <;> fun_prop

/-- [The projection retaining only the treatment's non-descendants is
one-Lipschitz for the sum of absolute coordinate differences](goal). -/
-- @node: nonDescendantProjection_lipschitz
lemma nonDescendantProjection_lipschitz (T : Fin n) :
    LipschitzWith 1 (nonDescendantProjection (dag := dag) (kind := kind) T) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, PiLp.dist_eq_of_L1]
  apply Finset.sum_le_sum
  rintro ⟨i,j⟩ _
  dsimp [nonDescendantProjection]
  split_ifs
  · exact le_rfl
  · simpa only [dist_self] using (dist_nonneg : 0 ≤ dist (x.ofLp ⟨i,j⟩) (y.ofLp ⟨i,j⟩))

/-- If [a set is compact](hyp:hS), [has probability one under the probability
law](hyp:hmu), and [a real-valued function is Lipschitz on that set](hyp:hf)
with [nonnegative Lipschitz constant c](hyp:c), then [the function is integrable
under the full law, regardless of its values outside the set](goal). -/
-- @node: integrable_of_lipschitzOn_compact_carrying
lemma integrable_of_lipschitzOn_compact_carrying
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (mu : Measure X) [IsProbabilityMeasure mu] (S : Set X) (hS : IsCompact S)
    (hmu : mu S = 1) (f : X → ℝ) (c : ℝ≥0) (hf : LipschitzOnWith c f S) :
    Integrable f mu := by
  have hcarry : ∀ᵐ x ∂mu, x ∈ S :=
    (ae_mem_iff_measure_eq hS.measurableSet.nullMeasurableSet).2 (by simpa using hmu)
  have hi := hf.continuousOn.integrableOn_compact (μ := mu) hS
  simpa only [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hcarry] using hi

/-- [The set of joint observations satisfying every categorical node's
admissible-label constraint is closed](goal). -/
-- @node: admissibleJoint_isClosed
lemma admissibleJoint_isClosed : IsClosed {v : Joint kind | admissibleJoint v} := by
  have heq : {v : Joint kind | admissibleJoint v} =
      ⋂ (i : Fin n) (k : ℕ) (_ : kind i = .inr k),
        ⋃ label : Fin k, ⋂ j : Fin (valueDim (kind i)),
          {v : Joint kind | v.ofLp ⟨i,j⟩ = (label.val + 1 : ℕ)} := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion]
    constructor
    · intro hv i k hk
      have h := hv i (WithLp.toLp 1 (fun j => v.ofLp ⟨i,j⟩)) rfl
      split at h
      · rename_i d hi
        simp [hk] at hi
      · rename_i k' hi
        have he : k' = k := Sum.inr.inj (hi.symm.trans hk)
        subst k'
        exact h
    · intro hv i w hw
      have hw' : WithLp.toLp 1 (fun j => v.ofLp ⟨i,j⟩) = w := Option.some.inj hw
      subst w
      split
      · trivial
      · rename_i k hk
        exact hv i k hk
  rw [heq]
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro k
  apply isClosed_iInter
  intro hk
  apply isClosed_iUnion_of_finite
  intro label
  apply isClosed_iInter
  intro j
  exact isClosed_eq (by fun_prop) continuous_const

/-- [The set of admissible joint observations whose coordinates all have
absolute value at most K is compact](goal). -/
-- @node: admissibleJoint_box_isCompact
lemma admissibleJoint_box_isCompact (K : ℝ) :
    IsCompact {v : Joint kind | (∀ j, |v.ofLp j| ≤ K) ∧ admissibleJoint v} :=
  (joint_coordinate_box_isCompact K).inter_right admissibleJoint_isClosed

/-- [For every latent realization, evaluation without intervention satisfies
all categorical state constraints](goal). -/
-- @node: observationalEval_admissibleJoint
lemma observationalEval_admissibleJoint (M : EuclideanSCM kind dims)
    (u : Exogenous kind dims) :
    admissibleJoint (intervenedEval M (fun _ => none) u) := by
  intro i w hw
  have hw' : WithLp.toLp 1 (fun j =>
      (intervenedEval M (fun _ => none) u).ofLp ⟨i,j⟩) = w := Option.some.inj hw
  subst w
  split
  · trivial
  · rename_i k hk
    exact evalSteps_categorical_label M u i k hk _ (scm_topoOrder_lt_horizon M i)

/-- If [the model's variables are bounded in absolute value by K](hyp:hb), then
[its observational law assigns probability one to the joint observations with
that coordinate bound and admissible categorical labels](goal). -/
-- @node: observationalLaw_admissibleJoint_box
lemma observationalLaw_admissibleJoint_box (M : EuclideanSCM kind dims)
    (K : ℝ) (hb : VariablesBoundedAt M K) :
    (observationalLaw M) {v | (∀ j, |v.ofLp j| ≤ K) ∧ admissibleJoint v} = 1 := by
  letI := M.probability
  haveI : IsProbabilityMeasure (observationalLaw M) :=
    Measure.isProbabilityMeasure_map (evalSteps_measurable M _ _).aemeasurable
  have hbox : ∀ᵐ v ∂observationalLaw M, ∀ j, |v.ofLp j| ≤ K :=
    (ae_mem_iff_measure_eq (joint_coordinate_box_isCompact (kind := kind) K).measurableSet.nullMeasurableSet).2
      (by simpa using observationalLaw_bounded_coordinates M K hb)
  have hadm : ∀ᵐ v ∂observationalLaw M, admissibleJoint v := by
    apply (ae_map_iff (evalSteps_measurable M _ _).aemeasurable
      admissibleJoint_isClosed.measurableSet).2
    exact Eventually.of_forall (observationalEval_admissibleJoint M)
  exact (ae_mem_iff_measure_eq (admissibleJoint_box_isCompact (kind := kind) K).measurableSet.nullMeasurableSet).1
    (hbox.and hadm) |>.trans (measure_univ)

/-- If [the model's variables are bounded by K](hyp:hb), [the real-valued
function is measurable](hyp:hf), and [it is Lipschitz on the non-descendant
projection of the admissible coordinate box](hyp:hLip) with [nonnegative constant
c](hyp:c), then [the function is integrable under the model's observational
non-descendant marginal](goal). -/
-- @node: nonDescendant_section_integrable
lemma nonDescendant_section_integrable (M : EuclideanSCM kind dims)
    (T : Fin n) (K : ℝ) (hb : VariablesBoundedAt M K)
    (f : Joint kind → ℝ) (hf : Measurable f) (c : ℝ≥0)
    (hLip : LipschitzOnWith c f
      ((nonDescendantProjection (dag := dag) T) '' {v : Joint kind | (∀ j, |v.ofLp j| ≤ K) ∧ admissibleJoint v})) :
    Integrable f ((observationalLaw M).map (nonDescendantProjection (dag := dag) T)) := by
  letI := M.probability
  haveI : IsProbabilityMeasure (observationalLaw M) :=
    Measure.isProbabilityMeasure_map (evalSteps_measurable M _ _).aemeasurable
  have hp := nonDescendantProjection_lipschitz (dag := dag) (kind := kind) T
  have hcomp : LipschitzOnWith c (f ∘ nonDescendantProjection (dag := dag) T)
      {v : Joint kind | (∀ j, |v.ofLp j| ≤ K) ∧ admissibleJoint v} := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    exact (hLip.dist_le_mul _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩).trans
      (mul_le_mul_of_nonneg_left (by simpa using hp.dist_le_mul x y) c.coe_nonneg)
  apply (integrable_map_measure hf.aestronglyMeasurable
    (nonDescendantProjection_measurable T).aemeasurable).2
  exact integrable_of_lipschitzOn_compact_carrying (observationalLaw M) _
    (admissibleJoint_box_isCompact K) (observationalLaw_admissibleJoint_box M K hb) _ c hcomp

/-- If [the first model's variables are bounded by K](hyp:hb), [the second
model's variables have the same bound](hyp:hbh), [the real-valued test function
is measurable](hyp:hf), and [it is Lipschitz on the non-descendant projection of
the admissible coordinate box](hyp:hLip) with [nonnegative constant c](hyp:c),
then [the absolute difference of its expectations under the two non-descendant
marginals is at most c times the Wasserstein distance of order one between the
observational laws](goal). -/
-- @node: nonDescendant_marginal_mean_gap_le
lemma nonDescendant_marginal_mean_gap_le (M Mhat : EuclideanSCM kind dims)
    (T : Fin n) (K : ℝ) (hb : VariablesBoundedAt M K) (hbh : VariablesBoundedAt Mhat K)
    (f : Joint kind → ℝ) (hf : Measurable f) (c : ℝ≥0)
    (hLip : LipschitzOnWith c f
      ((nonDescendantProjection (dag := dag) T) '' {v : Joint kind | (∀ j, |v.ofLp j| ≤ K) ∧ admissibleJoint v})) :
    |(∫ a, f a ∂(observationalLaw M).map (nonDescendantProjection (dag := dag) T)) -
      ∫ a, f a ∂(observationalLaw Mhat).map (nonDescendantProjection (dag := dag) T)| ≤
      c * (wasserstein1 (observationalLaw Mhat) (observationalLaw M)).toReal := by
  letI : BorelSpace (Joint kind) := ⟨rfl⟩
  letI := M.probability
  letI := Mhat.probability
  haveI : IsProbabilityMeasure (observationalLaw M) :=
    Measure.isProbabilityMeasure_map (evalSteps_measurable M _ _).aemeasurable
  haveI : IsProbabilityMeasure (observationalLaw Mhat) :=
    Measure.isProbabilityMeasure_map (evalSteps_measurable Mhat _ _).aemeasurable
  let mu : ProbabilityMeasure (Joint kind) := ⟨observationalLaw Mhat, inferInstance⟩
  let nu : ProbabilityMeasure (Joint kind) := ⟨observationalLaw M, inferInstance⟩
  have hp := nonDescendantProjection_lipschitz (dag := dag) (kind := kind) T
  have hcomp : LipschitzOnWith c (f ∘ nonDescendantProjection (dag := dag) T)
      {v : Joint kind | (∀ j, |v.ofLp j| ≤ K) ∧ admissibleJoint v} := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    exact (hLip.dist_le_mul _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩).trans
      (mul_le_mul_of_nonneg_left (by simpa using hp.dist_le_mul x y) c.coe_nonneg)
  have hm := observationalLaw_admissibleJoint_box M K hb
  have hh := observationalLaw_admissibleJoint_box Mhat K hbh
  have hc := admissibleJoint_box_isCompact (kind := kind) K
  have hpos := regression_compact_support_contrast_le mu nu _ hc hh hm
    (f ∘ nonDescendantProjection (dag := dag) T) c hcomp
  have hneg := regression_compact_support_contrast_le mu nu _ hc hh hm
    (fun v => -f (nonDescendantProjection (dag := dag) T v)) c hcomp.neg
  simp only [integral_neg] at hneg
  rw [integral_map (nonDescendantProjection_measurable T).aemeasurable hf.aestronglyMeasurable,
    integral_map (nonDescendantProjection_measurable T).aemeasurable hf.aestronglyMeasurable]
  dsimp [mu, nu, Function.comp_def] at hpos hneg
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Suppose [the outcome is scalar](hyp:hY), [the first model has independent
latent blocks](hyp:hind), [the second model also has independent latent
blocks](hyp:hindhat), and [the graph has no hidden confounding](hyp:hnoconf).
For [a common nonnegative regularity constant L](hyp:L), assume [the first
model's continuous mechanisms are L-Lipschitz](hyp:hcont), [the second model's
continuous mechanisms are L-Lipschitz](hyp:hconthat), [the first model's
categorical propensities are L-Lipschitz](hyp:hprop), [the second model's
categorical propensities are L-Lipschitz](hyp:hprophat), [the first model's
variables are bounded by K](hyp:hbound), and [the second model's variables are
bounded by K](hyp:hboundhat). If [the dose intervention is admissible](hyp:ht)
and [the second model's descendant mean at that dose is Lipschitz on the
projected admissible coordinate box](hyp:hLip) with [nonnegative constant
c](hyp:c), then [the difference of the descendant means is integrable under
the first model's non-descendant marginal, the dose-response difference equals
its integral plus the change in the second model's mean induced by changing
that marginal, and this marginal term has absolute value at most c times the
observational Wasserstein distance of order one](goal). -/
-- @node: descendant_dose_response_marginal_decomposition
lemma descendant_dose_response_marginal_decomposition
    (M Mhat : CanonicalSCM kind dims dag G C) (T Y : Fin n)
    (hY : valueDim (kind Y) = 1) (K : ℝ) (L : ℝ≥0)
    (hind : LatentBlocksIndependent M.toEuclideanSCM)
    (hindhat : LatentBlocksIndependent Mhat.toEuclideanSCM)
    (hnoconf : NoHiddenConfounding G)
    (hcont : ContinuousMechanismsLipschitz M.toEuclideanSCM L)
    (hconthat : ContinuousMechanismsLipschitz Mhat.toEuclideanSCM L)
    (hprop : CategoricalPropensityLipschitz M.toEuclideanSCM M.f L)
    (hprophat : CategoricalPropensityLipschitz Mhat.toEuclideanSCM Mhat.f L)
    (hbound : VariablesBoundedAt M.toEuclideanSCM K)
    (hboundhat : VariablesBoundedAt Mhat.toEuclideanSCM K)
    (t : ℝ) (ht : AdmissibleIntervention kind (singleIntervention T t))
    (c : ℝ≥0)
    (hLip : LipschitzOnWith c (fun a => descendantMean Mhat T Y hY a t)
      ((nonDescendantProjection (dag := dag) T) '' {v : Joint kind | (∀ j, |v.ofLp j| ≤ K) ∧ admissibleJoint v})) :
    let nuA := (observationalLaw M.toEuclideanSCM).map (nonDescendantProjection (dag := dag) T)
    let muA := (observationalLaw Mhat.toEuclideanSCM).map (nonDescendantProjection (dag := dag) T)
    let d := fun a => descendantMean M T Y hY a t - descendantMean Mhat T Y hY a t
    let marginal := (∫ a, descendantMean Mhat T Y hY a t ∂nuA) -
      ∫ a, descendantMean Mhat T Y hY a t ∂muA
    Integrable d nuA ∧
      meanOutcome M.toEuclideanSCM T Y hY t - meanOutcome Mhat.toEuclideanSCM T Y hY t =
        (∫ a, d a ∂nuA) + marginal ∧
      |marginal| ≤ c * (wasserstein1 (observationalLaw Mhat.toEuclideanSCM)
        (observationalLaw M.toEuclideanSCM)).toReal := by
  dsimp only
  have hm : Measurable (fun a => descendantMean Mhat T Y hY a t) := by
    fun_prop
  have hcross := nonDescendant_section_integrable M.toEuclideanSCM T K hbound
    (fun a => descendantMean Mhat T Y hY a t) hm c hLip
  have hnu := descendantMean_adjustment_and_integrable M T Y hY K L
    hind hnoconf hcont hprop hbound t ht
  have hmu := descendantMean_adjustment_and_integrable Mhat T Y hY K L
    hindhat hnoconf hconthat hprophat hboundhat t ht
  refine ⟨hnu.1.sub hcross, ?_, ?_⟩
  · rw [hnu.2, hmu.2, integral_sub hnu.1 hcross]
    ring
  · exact nonDescendant_marginal_mean_gap_le M.toEuclideanSCM Mhat.toEuclideanSCM
      T K hbound hboundhat (fun a => descendantMean Mhat T Y hY a t) hm c hLip

end
end Papers.TbsNeuralCausalPi

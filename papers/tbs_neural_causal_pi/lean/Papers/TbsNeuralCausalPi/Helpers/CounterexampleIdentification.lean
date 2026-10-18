module
public import Papers.TbsNeuralCausalPi.Helpers.CounterexampleObservations
public import Papers.TbsNeuralCausalPi.Helpers.CounterexampleConditional
/-! # Observable adjustment functional for the backdoor witness

The adjustment score is a function of the observed vector alone. Independent
selection identifies a potential-outcome mean by inverse weighting, and the
six-atom observational law evaluates the witness score exactly. The remaining
SCM identification step must establish the independent-selection representation
for every observationally equivalent model.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

-- @node: selection_inverse_weighting_inner
/-- If [the selection weight is nonzero](hyp:hp) and [the integral of the selection
indicator equals that weight](hyp:hlaw), then [the integral of the selected outcome
divided by the weight equals the outcome itself](goal). -/
lemma selection_inverse_weighting_inner
    {Z : Type*} [MeasurableSpace Z] (κ : Measure Z)
    (S : Z → Prop) [DecidablePred S] (y p : ℝ) (hp : p ≠ 0)
    (hlaw : (∫ z, (if S z then (1 : ℝ) else 0) ∂κ) = p) :
    (∫ z, (if S z then y / p else 0) ∂κ) = y := by
  have heq : (fun z => if S z then y / p else 0) =
      (fun z => (y / p) * (if S z then (1 : ℝ) else 0)) := by
    funext z
    split_ifs <;> simp
  rw [heq, integral_const_mul, hlaw, div_mul_cancel₀ _ hp]

-- @node: independent_selection_inverse_weighting
/-- Suppose [the private-input vector is measurable](hyp:hV), [the selection noise
is measurable](hyp:hG), [these two random objects are independent](hyp:hind), and
[the selection event is measurable](hyp:hS). If [the outcome is measurable](hyp:hY)
and [the selection-weight function is measurable](hyp:hp), [every selection weight is
nonzero](hyp:hpos), [each weight equals the selection indicator's integral over
the noise distribution at that private input](hyp:hlaw), and [the selected outcome
divided by its weight is integrable under the product of the two marginal
distributions](hyp:hI), then [its mean under the original probability distribution
equals the unweighted outcome mean](goal). -/
lemma independent_selection_inverse_weighting
    {Ω X Z : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (V : Ω → X) (G : Ω → Z) (hV : Measurable V) (hG : Measurable G)
    (hind : IndepFun V G μ)
    (S : X × Z → Prop) [DecidablePred S] (hS : MeasurableSet {v | S v})
    (Y p : X → ℝ) (hY : Measurable Y) (hp : Measurable p)
    (hpos : ∀ x, p x ≠ 0)
    (hlaw : ∀ x, (∫ z, (if S (x, z) then (1 : ℝ) else 0) ∂μ.map G) = p x)
    (hI : Integrable (fun v : X × Z => if S v then Y v.1 / p v.1 else 0)
      ((μ.map V).prod (μ.map G))) :
    (∫ u, (if S (V u, G u) then Y (V u) / p (V u) else 0) ∂μ) =
      ∫ u, Y (V u) ∂μ := by
  let := Measure.isProbabilityMeasure_map (μ := μ) hV.aemeasurable
  let := Measure.isProbabilityMeasure_map (μ := μ) hG.aemeasurable
  let F : X × Z → ℝ := fun v => if S v then Y v.1 / p v.1 else 0
  have hF : Measurable F := by
    apply Measurable.ite hS
    · exact (hY.comp measurable_fst).div (hp.comp measurable_fst)
    · exact measurable_const
  calc
    _ = ∫ v, F v ∂μ.map (fun u => (V u, G u)) :=
      (integral_map (hV.prodMk hG).aemeasurable hF.aestronglyMeasurable).symm
    _ = ∫ v, F v ∂(μ.map V).prod (μ.map G) := by
      rw [hind.map_prod_eq_prod_map_map hV.aemeasurable hG.aemeasurable]
    _ = ∫ x, ∫ z, F (x, z) ∂μ.map G ∂μ.map V := integral_prod F hI
    _ = ∫ x, Y x ∂μ.map V := by
      apply integral_congr_ae
      apply ae_of_all
      intro x
      exact selection_inverse_weighting_inner (μ.map G) (fun z => S (x, z))
        (Y x) (p x) (hpos x) (hlaw x)
    _ = _ := integral_map hV.aemeasurable hY.aestronglyMeasurable

-- @node: independent_selection_identification_of_integrable_observation
/-- Suppose [the private-input vector is measurable](hyp:hV), [the selection noise
is measurable](hyp:hG), [they are independent](hyp:hind), and [the selection event
is measurable](hyp:hS). If [the outcome is measurable](hyp:hY) and [the
selection-weight function is measurable](hyp:hp), [every weight is nonzero](hyp:hpos), [each weight
equals the selection indicator's integral over the noise distribution at that
private input](hyp:hlaw), and [the selected outcome divided by its weight is
integrable under the original probability distribution](hyp:hobs), then [the
unweighted outcome is integrable and its mean equals the mean of that weighted
selected outcome](goal). -/
lemma independent_selection_identification_of_integrable_observation
    {Ω X Z : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (V : Ω → X) (G : Ω → Z) (hV : Measurable V) (hG : Measurable G)
    (hind : IndepFun V G μ)
    (S : X × Z → Prop) [DecidablePred S] (hS : MeasurableSet {v | S v})
    (Y p : X → ℝ) (hY : Measurable Y) (hp : Measurable p)
    (hpos : ∀ x, p x ≠ 0)
    (hlaw : ∀ x, (∫ z, (if S (x, z) then (1 : ℝ) else 0) ∂μ.map G) = p x)
    (hobs : Integrable (fun u => if S (V u, G u) then Y (V u) / p (V u) else 0) μ) :
    Integrable (fun u => Y (V u)) μ ∧
      (∫ u, (if S (V u, G u) then Y (V u) / p (V u) else 0) ∂μ) =
        ∫ u, Y (V u) ∂μ := by
  let := Measure.isProbabilityMeasure_map (μ := μ) hV.aemeasurable
  let := Measure.isProbabilityMeasure_map (μ := μ) hG.aemeasurable
  let F : X × Z → ℝ := fun v => if S v then Y v.1 / p v.1 else 0
  have hF : Measurable F := by
    apply Measurable.ite hS
    · exact (hY.comp measurable_fst).div (hp.comp measurable_fst)
    · exact measurable_const
  have hI : Integrable F ((μ.map V).prod (μ.map G)) := by
    rw [← hind.map_prod_eq_prod_map_map hV.aemeasurable hG.aemeasurable]
    exact (integrable_map_measure hF.aestronglyMeasurable
      (hV.prodMk hG).aemeasurable).mpr hobs
  have hinner : (fun x => ∫ z, F (x, z) ∂μ.map G) = Y := by
    funext x
    exact selection_inverse_weighting_inner (μ.map G) (fun z => S (x, z))
      (Y x) (p x) (hpos x) (hlaw x)
  have hYI := hI.integral_prod_left
  rw [hinner] at hYI
  exact ⟨hYI.comp_aemeasurable hV.aemeasurable,
    independent_selection_inverse_weighting μ V G hV hG hind S hS Y p hY hp hpos hlaw hI⟩

-- @node: independent_selection_weight_integrable
/-- If [the selection event is measurable](hyp:hS), [the outcome is
measurable](hyp:hY), [the selection-weight function is measurable](hyp:hp),
[the lower bound on weights is strictly positive](hyp:ha), [the absolute outcome
is everywhere bounded by the outcome bound](hyp:hB), and [every weight is at least
the lower bound](hyp:hpa), then [the selected outcome divided by its weight is
integrable under the product of the two probability distributions](goal). -/
lemma independent_selection_weight_integrable
    {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]
    (ν : Measure X) (κ : Measure Z) [IsProbabilityMeasure ν] [IsProbabilityMeasure κ]
    (S : X × Z → Prop) [DecidablePred S] (hS : MeasurableSet {v | S v})
    (Y p : X → ℝ) (hY : Measurable Y) (hp : Measurable p)
    (B a : ℝ) (ha : 0 < a) (hB : ∀ x, ‖Y x‖ ≤ B) (hpa : ∀ x, a ≤ p x) :
    Integrable (fun v : X × Z => if S v then Y v.1 / p v.1 else 0) (ν.prod κ) := by
  have hm : Measurable (fun v : X × Z => if S v then Y v.1 / p v.1 else 0) := by
    apply Measurable.ite hS
    · exact (hY.comp measurable_fst).div (hp.comp measurable_fst)
    · exact measurable_const
  apply Integrable.of_bound hm.aestronglyMeasurable (B / a)
  apply ae_of_all
  intro v
  have hBn : 0 ≤ B := (norm_nonneg (Y v.1)).trans (hB v.1)
  split_ifs
  · rw [norm_div, Real.norm_eq_abs (p v.1), abs_of_pos (ha.trans_le (hpa v.1))]
    exact div_le_div₀ hBn (hB v.1) ha (hpa v.1)
  · simpa using div_nonneg hBn ha.le

-- @node: independent_selection_inverse_weighting_of_bounded
/-- Suppose [the private-input vector is measurable](hyp:hV), [the selection noise
is measurable](hyp:hG), [they are independent](hyp:hind), and [the selection event
is measurable](hyp:hS). If [the outcome is measurable](hyp:hY) and [the
selection-weight function is measurable](hyp:hp), [the weight lower bound is positive](hyp:ha),
[the absolute outcome is uniformly bounded by the outcome bound](hyp:hB),
[every weight is at least the lower bound](hyp:hpa), and [each weight equals the
selection indicator's integral over the noise distribution at that private
input](hyp:hlaw), then [the mean of the selected outcome divided by its weight
equals the unweighted outcome mean](goal). -/
lemma independent_selection_inverse_weighting_of_bounded
    {Ω X Z : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (V : Ω → X) (G : Ω → Z) (hV : Measurable V) (hG : Measurable G)
    (hind : IndepFun V G μ)
    (S : X × Z → Prop) [DecidablePred S] (hS : MeasurableSet {v | S v})
    (Y p : X → ℝ) (hY : Measurable Y) (hp : Measurable p)
    (B a : ℝ) (ha : 0 < a) (hB : ∀ x, ‖Y x‖ ≤ B) (hpa : ∀ x, a ≤ p x)
    (hlaw : ∀ x, (∫ z, (if S (x, z) then (1 : ℝ) else 0) ∂μ.map G) = p x) :
    (∫ u, (if S (V u, G u) then Y (V u) / p (V u) else 0) ∂μ) =
      ∫ u, Y (V u) ∂μ := by
  let := Measure.isProbabilityMeasure_map (μ := μ) hV.aemeasurable
  let := Measure.isProbabilityMeasure_map (μ := μ) hG.aemeasurable
  exact independent_selection_inverse_weighting μ V G hV hG hind S hS Y p hY hp
    (fun x => (ha.trans_le (hpa x)).ne') hlaw
    (independent_selection_weight_integrable _ _ S hS Y p hY hp B a ha hB hpa)

-- @node: counterexampleTrueTreatmentProbability_overlap
/-- At every covariate value, [the constructed true model's treatment probability
and its complementary probability are both strictly positive](goal). -/
lemma counterexampleTrueTreatmentProbability_overlap (x : ℝ) :
    0 < counterexampleTrueTreatmentProbability x ∧
      0 < 1 - counterexampleTrueTreatmentProbability x := by
  have h := counterexampleTrueTreatmentProbability_bounds x
  constructor <;> linarith [h.1, h.2]

-- @node: counterexampleAdjustmentScore
/-- For [an observed covariate, treatment, and outcome vector](hyp:v), the
[adjustment score](goal) first [computes the true model's treatment probability
at the observed covariate](step:1), then [subtracts the outcome weighted by the
complementary probability when treatment equals one from the outcome weighted
by the treatment probability when treatment equals two, using zero for each
inactive treatment term](step:2). -/
def counterexampleAdjustmentScore (v : Joint backdoorKind) : ℝ :=
  let p := counterexampleTrueTreatmentProbability (v.ofLp ⟨0, ⟨0, by decide⟩⟩)
  (if v.ofLp ⟨1, ⟨0, by decide⟩⟩ = 2 then backdoorOutcome v / p else 0) -
    (if v.ofLp ⟨1, ⟨0, by decide⟩⟩ = 1 then backdoorOutcome v / (1 - p) else 0)

-- @node: counterexampleAdjustmentScore_measurable
/-- [The observable inverse-probability adjustment score is measurable](goal). -/
@[fun_prop] lemma counterexampleAdjustmentScore_measurable :
    Measurable counterexampleAdjustmentScore := by
  unfold counterexampleAdjustmentScore backdoorOutcome
  apply Measurable.sub
  · apply Measurable.ite (measurableSet_eq_fun (by fun_prop) measurable_const)
    · fun_prop
    · fun_prop
  · apply Measurable.ite (measurableSet_eq_fun (by fun_prop) measurable_const)
    · fun_prop
    · fun_prop

-- @node: counterexampleAdjustmentScore_finite_integral
/-- [The mean adjustment score under the six-atom observation distribution with
zero shift is 19/30](goal). -/
lemma counterexampleAdjustmentScore_finite_integral :
    (∫ z, counterexampleAdjustmentScore (counterexampleJointOfVector z)
      ∂counterexampleFiniteObservationLaw 0) = (19/30 : ℝ) := by
  have hi : ∀ i : Fin 6,
      Integrable (fun z => counterexampleAdjustmentScore (counterexampleJointOfVector z))
        (counterexampleAtomWeight i • Measure.dirac (counterexampleObservationAtom 0 i)) := by
    intro i
    apply Integrable.smul_measure
    · exact integrable_dirac (by simp)
    · simp [counterexampleAtomWeight]
  rw [counterexampleFiniteObservationLaw, integral_finsetSum_measure (by
    intro i _
    exact hi i)]
  simp only [integral_smul_measure, integral_dirac]
  norm_num [Fin.sum_univ_succ, counterexampleAtomWeight, counterexampleObservationAtom,
    counterexampleAdjustmentScore, counterexampleJointOfVector, backdoorOutcome,
    counterexampleTrueTreatmentProbability, counterexampleClamp, Matrix.cons_val_two,
    Matrix.cons_val_three]

-- @node: counterexampleTrueSCM_adjustment_integral
/-- [The mean adjustment score under the constructed true structural causal
model's observational distribution is 19/30](goal). -/
lemma counterexampleTrueSCM_adjustment_integral :
    (∫ v, counterexampleAdjustmentScore v
      ∂observationalLaw counterexampleTrueSCM.toEuclideanSCM) = (19/30 : ℝ) := by
  rw [counterexampleTrueSCM_observationalLaw, counterexampleTrueFiniteObservationLaw_eq]
  rw [integral_map counterexampleJointOfVector_measurable.aemeasurable
    counterexampleAdjustmentScore_measurable.aestronglyMeasurable]
  exact counterexampleAdjustmentScore_finite_integral

-- @node: counterexample_adjustment_integral_of_observational_eq
/-- If [a structural causal model has the same observational distribution as the
constructed true model](hyp:hobs), then [its mean adjustment score is 19/30](goal).

The model may have a different number and dimension of private latent blocks. -/
lemma counterexample_adjustment_integral_of_observational_eq
    {b : ℕ} {dims : Fin b → ℕ} (M : EuclideanSCM backdoorKind dims)
    (hobs : observationalLaw M = observationalLaw counterexampleTrueSCM.toEuclideanSCM) :
    (∫ v, counterexampleAdjustmentScore v ∂observationalLaw M) = (19/30 : ℝ) := by
  rw [hobs]
  exact counterexampleTrueSCM_adjustment_integral

-- @node: counterexampleTrueSCM_ATE_eq_adjustment
/-- [The constructed true structural causal model's average treatment effect
equals the mean adjustment score under its observational distribution](goal). -/
lemma counterexampleTrueSCM_ATE_eq_adjustment :
    backdoorATE counterexampleTrueSCM.toEuclideanSCM =
      ∫ v, counterexampleAdjustmentScore v
        ∂observationalLaw counterexampleTrueSCM.toEuclideanSCM := by
  rw [counterexampleTrueSCM_ATE, counterexampleTrueSCM_adjustment_integral]

end
end Papers.TbsNeuralCausalPi

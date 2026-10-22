module
public import Papers.TbsExtremeEffects.Helpers.TailSurvival
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator

/-! Consistency for conditional sign means, using bounded truncations.
No global integrability of the untruncated outcomes is needed. -/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
variable {q d : ℕ}

-- @node: integrable_sign_truncation
/-- For a [measurable outcome](hyp:hY), the [positive or negative outcome truncated between zero and `k` is integrable](goal). -/
lemma integrable_sign_truncation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {Y : Ω → ℝ} (hY : Measurable Y)
    (negative : Bool) (k : ℕ) :
    Integrable (fun w => min (max (if negative then -Y w else Y w) 0) (k : ℝ)) μ := by
  apply Integrable.mono' (integrable_const (k : ℝ))
  · apply Measurable.aestronglyMeasurable
    cases negative <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop
  · apply Eventually.of_forall
    intro w
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (le_max_right _ _) (Nat.cast_nonneg k))]
    exact min_le_right _ _

-- @node: conditionalObservedPart_eq_potentialPart_on_treatment
/-- Under [consistency of observed and potential outcomes](hyp:hConsistency), on units receiving treatment `a`, the [truncated conditional observed outcome equals its potential-outcome counterpart](goal), almost surely. -/
lemma conditionalObservedPart_eq_potentialPart_on_treatment (M : ExtremeModel q d)
    (hConsistency : Consistency M) (a negative : Bool) (k : ℕ) :
    ∀ᵐ w ∂M.mu, M.D w = a →
      conditionalObservedPart M negative k w =
        conditionalPotentialPart M a negative (sigmaXDU M) k w := by
  let O : M.Om → ℝ := fun w =>
    min (max (if negative then -M.Y w else M.Y w) 0) (k : ℝ)
  let P : M.Om → ℝ := fun w =>
    min (max (if negative then -potentialOutcome M a w else potentialOutcome M a w) 0) (k : ℝ)
  let A : Set M.Om := {w | M.D w = a}
  have hA : MeasurableSet[sigmaXDU M] A := by
    have hproj : Measurable (fun z : (Fin q → ℝ) × Bool × (Fin d → ℝ) => z.2.1) := by
      fun_prop
    exact ⟨{z : (Fin q → ℝ) × Bool × (Fin d → ℝ) | z.2.1 = a},
      hproj (measurableSet_singleton a), rfl⟩
  have hPmeas : Measurable (potentialOutcome M a) := by
    cases a
    · exact M.measurable_Y0
    · exact M.measurable_Y1
  have heq : A.indicator O =ᵐ[M.mu] A.indicator P := by
    filter_upwards [hConsistency] with w hw
    by_cases hwa : M.D w = a
    · have hy : M.Y w = potentialOutcome M a w := by
        cases a <;> simpa [hwa, potentialOutcome] using hw
      simp only [Set.indicator_of_mem (show w ∈ A from hwa), O, P, hy]
    · simp only [Set.indicator_of_notMem (show w ∉ A from hwa)]
  have hc := (condExp_indicator (m := sigmaXDU M)
    (integrable_sign_truncation M.mu M.measurable_Y negative k) hA).symm.trans
    ((condExp_congr_ae (m := sigmaXDU M) heq).trans
      (condExp_indicator (integrable_sign_truncation M.mu hPmeas negative k) hA))
  filter_upwards [hc] with w hw hwa
  simpa only [Set.indicator_of_mem (show w ∈ A from hwa),
    conditionalObservedPart, conditionalPotentialPart, O, P] using hw

-- @node: condMeanY_eq_potentialMean_on_treatment
/-- Under [consistency of observed and potential outcomes](hyp:hConsistency), on units receiving treatment `a`, the [conditional mean of the observed outcome equals the corresponding potential mean](goal), almost surely. -/
lemma condMeanY_eq_potentialMean_on_treatment (M : ExtremeModel q d)
    (hConsistency : Consistency M) (a : Bool) :
    ∀ᵐ w ∂M.mu, M.D w = a →
      condMeanY M w = conditionalPotentialMean M a (sigmaXDU M) w := by
  have hp := ae_all_iff.mpr (fun k : ℕ =>
    conditionalObservedPart_eq_potentialPart_on_treatment M hConsistency a false k)
  have hn := ae_all_iff.mpr (fun k : ℕ =>
    conditionalObservedPart_eq_potentialPart_on_treatment M hConsistency a true k)
  filter_upwards [hp, hn] with w hwp hwn hwa
  have hpos : (fun k => conditionalObservedPart M false k w) =
      (fun k => conditionalPotentialPart M a false (sigmaXDU M) k w) :=
    funext fun k => hwp k hwa
  have hneg : (fun k => conditionalObservedPart M true k w) =
      (fun k => conditionalPotentialPart M a true (sigmaXDU M) k w) :=
    funext fun k => hwn k hwa
  unfold condMeanY conditionalPotentialMean
  rw [hpos, hneg]

-- @node: regression_eq_potentialMean_on_treatment
/-- Under [outcome consistency](hyp:hConsistency), a [conditional-mean version](hyp:hMean), and [identification side conditions](hyp:hSide), on units receiving treatment `a`, the [regression function equals the potential conditional mean given covariates and noise](goal), almost surely. -/
lemma regression_eq_potentialMean_on_treatment (M : ExtremeModel q d)
    (hConsistency : Consistency M) (hMean : ConditionalMeanVersion M)
    (hSide : IdentificationSideConditions M) (a : Bool) :
    ∀ᵐ w ∂M.mu, M.D w = a →
      M.f (M.X w) a (M.U w) = conditionalPotentialMean M a (sigmaXU M) w := by
  filter_upwards [hMean.2.2, condMeanY_eq_potentialMean_on_treatment M hConsistency a,
    (hSide.2.1 a).2.2] with w hf hc he hwa
  simpa only [hwa] using hf.trans ((hc hwa).trans he)

end Papers.TbsExtremeEffects

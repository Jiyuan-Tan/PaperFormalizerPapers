module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLBoundaryResidualRates
/-! Second-order cancellation of the fitted baseline treatment residual.
The lower policy boundary uses this residual rather than a pooled policy residual.
Clipping and componentwise nuisance rates imply its weighted root-n negligibility. -/
public section
set_option linter.unnecessarySeqFocus false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- This identity includes the structural zero and indices outside the carrier.
-- @node: fitted_positive_treatment_centering_identity
/-- If [the clipping constant is positive](hyp:hc) and [every fitted baseline assignment probability at the selected covariate value is at least that constant](hyp:hclip), [the reference assignment probability times the reference-minus-fitted treatment level divided by the fitted assignment probability, plus the fitted-minus-reference treatment level, equals the product of the assignment-probability error and treatment-level error divided by the fitted assignment probability, including structurally zero indices](goal). -/
lemma fitted_positive_treatment_centering_identity (L : LevelData Z X)
    (e0 e : NuisanceBin L) (i : ℕ) (x : X) (c : ℝ) (hc : 0 < c)
    (hclip : ∀ a, c ≤ e.piLev a x) :
    positiveValue e0.piLev i x *
        (positiveValue e0.pLev i x - positiveValue e.pLev i x) /
          positiveValue e.piLev i x +
        (positiveValue e.pLev i x - positiveValue e0.pLev i x) =
      (positiveValue e.piLev i x - positiveValue e0.piLev i x) *
        (positiveValue e.pLev i x - positiveValue e0.pLev i x) /
          positiveValue e.piLev i x := by
  by_cases hi : 1 ≤ i ∧ i ≤ L.K
  · simp only [positiveValue, dif_pos hi]
    have hp : e.piLev ⟨i, hi⟩ x ≠ 0 := ne_of_gt (hc.trans_le (hclip ⟨i, hi⟩))
    field_simp
    <;> ring
  · simp only [positiveValue, dif_neg hi]
    simp

-- The surviving term is the product of assignment and treatment errors.
-- @node: fitted_positive_treatment_centering_integrated_L2_bound
/-- For [admissible reference](hyp:he0) and [fitted nuisances](hyp:he), if [the clipping constant is positive](hyp:hc) and [all fitted baseline assignment probabilities are almost surely at least that constant](hyp:hclip), [the centered treatment remainder—the reference assignment probability times the reference-minus-fitted treatment level divided by the fitted assignment probability, plus the fitted-minus-reference treatment level—is integrable, and its integrated absolute value is at most the product of the assignment-probability and treatment-level L² errors divided by the clipping constant](goal). -/
lemma fitted_positive_treatment_centering_integrated_L2_bound
    (L : LevelData Z X) (e0 e : NuisanceBin L)
    (he0 : BinAdmissible M L e0) (he : BinAdmissible M L e)
    (i : ℕ) (c : ℝ) (hc : 0 < c)
    (hclip : ∀ a, ∀ᵐ x ∂xLaw M, c ≤ e.piLev a x) :
    let R := fun x => positiveValue e0.piLev i x *
      (positiveValue e0.pLev i x - positiveValue e.pLev i x) /
        positiveValue e.piLev i x +
      (positiveValue e.pLev i x - positiveValue e0.pLev i x)
    Integrable R (xLaw M) ∧
      (∫ x, |R x| ∂xLaw M) ≤
        finiteL2Error M (positiveValue e.piLev i) (positiveValue e0.piLev i) *
          finiteL2Error M (positiveValue e.pLev i) (positiveValue e0.pLev i) / c := by
  dsimp only
  let R := fun x => positiveValue e0.piLev i x *
    (positiveValue e0.pLev i x - positiveValue e.pLev i x) /
      positiveValue e.piLev i x +
    (positiveValue e.pLev i x - positiveValue e0.pLev i x)
  let dp := fun x => positiveValue e.pLev i x - positiveValue e0.pLev i x
  let dt := fun x => positiveValue e.piLev i x - positiveValue e0.piLev i x
  have hp : MemLp dp 2 (xLaw M) := ((fitted_positive_treatment_assignment_memLp M L e he i).1).sub
    (fitted_positive_treatment_assignment_memLp M L e0 he0 i).1
  have ht : MemLp dt 2 (xLaw M) := ((fitted_positive_treatment_assignment_memLp M L e he i).2).sub
    (fitted_positive_treatment_assignment_memLp M L e0 he0 i).2
  have hi : Integrable (fun x => |dt x| * |dp x| / c) (xLaw M) := by
    simpa only [dt, dp, Pi.mul_apply, abs_mul] using
      (ht.integrable_mul hp).abs.div_const c
  have hbound : ∀ᵐ x ∂xLaw M, |R x| ≤ |dt x| * |dp x| / c := by
    filter_upwards [ae_all_iff.mpr hclip] with x hx
    exact fitted_positive_ipw_residual_centering_error e0.piLev e.piLev
      e0.pLev e.pLev x c hc hx i
  have hm : AEStronglyMeasurable R (xLaw M) := by
    first | fun_prop | skip
    have h0 := fitted_positive_treatment_assignment_memLp M L e0 he0 i
    have hh := fitted_positive_treatment_assignment_memLp M L e he i
    exact (((h0.2.aestronglyMeasurable.aemeasurable.mul
      (h0.1.aestronglyMeasurable.aemeasurable.sub hh.1.aestronglyMeasurable.aemeasurable)).div
        hh.2.aestronglyMeasurable.aemeasurable).add
          hp.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
  have hR : Integrable R (xLaw M) := hi.mono' hm (by
    simpa only [Real.norm_eq_abs] using hbound)
  refine ⟨hR, ?_⟩
  calc
    _ ≤ ∫ x, |dt x| * |dp x| / c ∂xLaw M := integral_mono_ae hR.abs hi hbound
    _ = (∫ x, |dt x| * |dp x| ∂xLaw M) / c := integral_div _ _
    _ ≤ _ := by
      have hb := Causalean.Stat.integral_abs_mul_le_eLpNorm_mul_eLpNorm ht hp
      rw [← l2Error_eq_eLpNorm M _ _ ht, ← l2Error_eq_eLpNorm M _ _ hp] at hb
      exact div_le_div_of_nonneg_right (by simpa only [abs_mul] using hb) hc.le

-- Bounded fitted branch weights need not agree with the population branch.
-- @node: fitted_positive_treatment_centering_weighted_L2_bound
/-- For [admissible reference](hyp:he0) and [fitted nuisances](hyp:he), assume [a positive clipping constant](hyp:hc), [a nonnegative weight bound](hyp:hW), and [fitted baseline assignment probabilities almost surely at least the clipping constant](hyp:hclip). For [a measurable weight](hyp:hw) [almost surely bounded in absolute value by the weight bound](hyp:hwb), [the weighted centered treatment remainder is integrable, and the absolute value of its mean is at most the weight bound divided by the clipping constant times the product of the assignment-probability and treatment-level L² errors](goal). -/
lemma fitted_positive_treatment_centering_weighted_L2_bound
    (L : LevelData Z X) (e0 e : NuisanceBin L)
    (he0 : BinAdmissible M L e0) (he : BinAdmissible M L e)
    (i : ℕ) (c W : ℝ) (hc : 0 < c) (hW : 0 ≤ W)
    (hclip : ∀ a, ∀ᵐ x ∂xLaw M, c ≤ e.piLev a x)
    (w : X → ℝ) (hw : Measurable w) (hwb : ∀ᵐ x ∂xLaw M, ‖w x‖ ≤ W) :
    let R := fun x => positiveValue e0.piLev i x *
      (positiveValue e0.pLev i x - positiveValue e.pLev i x) /
        positiveValue e.piLev i x +
      (positiveValue e.pLev i x - positiveValue e0.pLev i x)
    Integrable (fun x => w x * R x) (xLaw M) ∧
      |∫ x, w x * R x ∂xLaw M| ≤
        (W / c) * (finiteL2Error M (positiveValue e.piLev i) (positiveValue e0.piLev i) *
          finiteL2Error M (positiveValue e.pLev i) (positiveValue e0.pLev i)) := by
  dsimp only
  let R := fun x => positiveValue e0.piLev i x *
    (positiveValue e0.pLev i x - positiveValue e.pLev i x) /
      positiveValue e.piLev i x +
    (positiveValue e.pLev i x - positiveValue e0.pLev i x)
  obtain ⟨hi, hb⟩ := fitted_positive_treatment_centering_integrated_L2_bound
    M L e0 e he0 he i c hc hclip
  dsimp only at hi hb
  have hiw := hi.bdd_mul hw.aestronglyMeasurable hwb
  refine ⟨hiw, ?_⟩
  calc
    _ ≤ ∫ x, |w x * R x| ∂xLaw M := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x => w x * R x)
    _ ≤ ∫ x, W * |R x| ∂xLaw M := by
      apply integral_mono_ae hiw.abs (hi.abs.const_mul W)
      filter_upwards [hwb] with x hx
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (by simpa only [Real.norm_eq_abs] using hx)
        (abs_nonneg _)
    _ = W * ∫ x, |R x| ∂xLaw M := integral_const_mul _ _
    _ ≤ W * (_ / c) := mul_le_mul_of_nonneg_left hb hW
    _ = _ := by ring

-- Componentwise quarter-power rates suffice even for random fitted weights.
-- @node: nuisanceRates_positive_treatment_centering_weighted_root_n_negligible
/-- Suppose [the reference nuisance is admissible](hyp:he0), [every fitted nuisance is admissible](hyp:heh), [the clipping constant is positive](hyp:hc), [the weight bound is nonnegative](hyp:hW), and [every fitted baseline assignment probability is almost surely at least the clipping constant](hyp:hclip). For [random covariate weights at each sample size](hyp:w) that are [measurable in covariates](hyp:hw) and [uniformly almost surely bounded by the weight bound](hyp:hwb), if the [treatment-level](hyp:hrp) and [assignment-probability](hyp:hrpi) componentwise L² errors are negligible relative to inverse fourth-root sample size, [the weighted mean centered treatment remainder along sample sizes twice the iteration index plus two, multiplied by the square root of the iteration index plus one, converges to zero in probability](goal). -/
lemma nuisanceRates_positive_treatment_centering_weighted_root_n_negligible
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (L : LevelData Z X) (e0 : NuisanceBin L) (eh : ℕ → A → NuisanceBin L)
    (he0 : BinAdmissible M L e0) (heh : ∀ n a, BinAdmissible M L (eh n a))
    (i : ℕ) (c W : ℝ) (hc : 0 < c) (hW : 0 ≤ W)
    (hclip : ∀ n a b, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).piLev b x)
    (w : ℕ → A → X → ℝ) (hw : ∀ n a, Measurable (w n a))
    (hwb : ∀ n a, ∀ᵐ x ∂xLaw M, ‖w n a x‖ ≤ W)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) e0.piLev) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
        ∫ x, w (2*(n+1)) a x *
          (positiveValue e0.piLev i x *
            (positiveValue e0.pLev i x - positiveValue (eh (2*(n+1)) a).pLev i x) /
              positiveValue (eh (2*(n+1)) a).piLev i x +
            (positiveValue (eh (2*(n+1)) a).pLev i x - positiveValue e0.pLev i x))
          ∂xLaw M) atTop (fun _ _ => 0) := by
  let reg := fun n a => finiteL2Error M (positiveValue (eh (2*(n+1)) a).pLev i)
    (positiveValue e0.pLev i)
  let wt := fun n a => finiteL2Error M (positiveValue (eh (2*(n+1)) a).piLev i)
    (positiveValue e0.piLev i)
  have hr := nuisanceRates_positiveValue M μ L.K _ _ hrp i
  have ht := nuisanceRates_positiveValue M μ L.K _ _ hrpi i
  apply dml_quadratic_bias_root_n_negligible μ _ reg wt (W / c + 1)
    (by positivity) hr ht
  intro n a
  have hb := (fitted_positive_treatment_centering_weighted_L2_bound
    M L e0 (eh (2*(n+1)) a) he0 (heh _ a) i c W hc hW
    (hclip _ a) (w (2*(n+1)) a) (hw _ a) (hwb _ a)).2
  dsimp only at hb
  apply hb.trans
  have hn : 0 ≤ reg n a * wt n a := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc
    _ = (W / c) * (reg n a * wt n a) := by dsimp only [reg, wt]; ring
    _ ≤ (W / c + 1) * (reg n a * wt n a) :=
      mul_le_mul_of_nonneg_right (by linarith) hn
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (sq_nonneg _))
      (by positivity)

-- At j=1 the policy residual at index zero vanishes. The lower boundary
-- instead has the baseline treatment residual; it must be debiased as well.
-- @node: fitted_regular_lower_boundary_residual_identity
/-- [The lower-boundary residual plus its pooled-policy discrepancy equals the baseline inverse-probability-weighted treatment residual plus the fitted-minus-reference treatment level in the first band; in every other band it equals the instrument-probability-weighted policy residual at the preceding index plus its fitted-minus-reference pooled-policy level](goal). -/
lemma fitted_regular_lower_boundary_residual_identity
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (e0 e : NuisanceBin L) (k j : ℕ) (x : X) :
    let rp := positiveValue e0.piLev k x *
      (positiveValue e0.pLev k x - positiveValue e.pLev k x) / positiveValue e.piLev k x
    let Q := ∑ z, instProb M z x * RqBin dphi L e k (j-1) (x,z,M.prop z x,0)
    (if j = 1 then rp else 0) + Q +
        (pooledQBin phi L e k (j-1) x - pooledQBin phi L e0 k (j-1) x) =
      if j = 1 then rp + (positiveValue e.pLev k x - positiveValue e0.pLev k x)
      else Q + (pooledQBin phi L e k (j-1) x - pooledQBin phi L e0 k (j-1) x) := by
  dsimp only
  by_cases hj : j = 1
  · subst j
    simp [RqBin, pooledQBin]
  · simp only [if_neg hj, zero_add]

-- This supplies the EL input of the regular-score bias envelope. The
-- baseline contribution is derived from denominator and regression errors.
-- @node: fitted_regular_lower_boundary_residual_error_bound
/-- If [the clipping constant is positive](hyp:hc) and [all fitted baseline assignment probabilities at the covariate value are at least that constant](hyp:hclip), [the absolute lower-boundary residual plus pooled-policy discrepancy is bounded in the first band by the product of absolute assignment-probability and treatment-level errors divided by the clipping constant; in other bands its bound is exactly the absolute instrument-probability-weighted policy residual plus the pooled-policy discrepancy](goal). -/
lemma fitted_regular_lower_boundary_residual_error_bound
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (e0 e : NuisanceBin L) (k j : ℕ) (x : X) (c : ℝ) (hc : 0 < c)
    (hclip : ∀ a, c ≤ e.piLev a x) :
    let rp := positiveValue e0.piLev k x *
      (positiveValue e0.pLev k x - positiveValue e.pLev k x) / positiveValue e.piLev k x
    let Q := ∑ z, instProb M z x * RqBin dphi L e k (j-1) (x,z,M.prop z x,0)
    |(if j = 1 then rp else 0) + Q +
        (pooledQBin phi L e k (j-1) x - pooledQBin phi L e0 k (j-1) x)| ≤
      if j = 1 then
        |positiveValue e.piLev k x - positiveValue e0.piLev k x| *
          |positiveValue e.pLev k x - positiveValue e0.pLev k x| / c
      else |Q + (pooledQBin phi L e k (j-1) x - pooledQBin phi L e0 k (j-1) x)| := by
  dsimp only
  rw [fitted_regular_lower_boundary_residual_identity M phi dphi L e0 e k j x]
  by_cases hj : j = 1
  · simp only [if_pos hj]
    exact fitted_positive_ipw_residual_centering_error e0.piLev e.piLev
      e0.pLev e.pLev x c hc hclip k
  · simp only [if_neg hj, le_refl]

-- Apply the derived rate to the actual lower-boundary expression in the
-- regular-score conditional expectation, including its zero-index policy term.
-- @node: nuisanceRates_regular_first_lower_boundary_root_n_negligible
/-- Suppose [the reference nuisance is admissible](hyp:he0), [all fitted nuisances are admissible](hyp:heh), [the clipping constant is positive](hyp:hc), [the weight bound is nonnegative](hyp:hW), and [all fitted baseline assignment probabilities are almost surely at least the clipping constant](hyp:hclip). For [random covariate weights at each sample size](hyp:w) that are [measurable in covariates](hyp:hw) and [uniformly almost surely bounded by the weight bound](hyp:hwb), if the [treatment-level](hyp:hrp) and [assignment-probability](hyp:hrpi) componentwise L² errors are negligible relative to inverse fourth-root sample size, [the weighted mean first-band lower-boundary remainder, including its policy residual and pooled-policy discrepancy at index zero, converges to zero in probability after multiplication by the square root of the iteration index plus one along sample sizes twice that index plus two](goal). -/
lemma nuisanceRates_regular_first_lower_boundary_root_n_negligible
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (e0 : NuisanceBin L) (eh : ℕ → A → NuisanceBin L)
    (he0 : BinAdmissible M L e0) (heh : ∀ n a, BinAdmissible M L (eh n a))
    (k : ℕ) (c W : ℝ) (hc : 0 < c) (hW : 0 ≤ W)
    (hclip : ∀ n a b, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).piLev b x)
    (w : ℕ → A → X → ℝ) (hw : ∀ n a, Measurable (w n a))
    (hwb : ∀ n a, ∀ᵐ x ∂xLaw M, ‖w n a x‖ ≤ W)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) e0.piLev) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
        ∫ x, w (2*(n+1)) a x *
          (positiveValue e0.piLev k x *
            (positiveValue e0.pLev k x - positiveValue (eh (2*(n+1)) a).pLev k x) /
              positiveValue (eh (2*(n+1)) a).piLev k x +
            (∑ z, instProb M z x * RqBin dphi L (eh (2*(n+1)) a) k 0
              (x,z,M.prop z x,0)) +
            (pooledQBin phi L (eh (2*(n+1)) a) k 0 x - pooledQBin phi L e0 k 0 x))
          ∂xLaw M) atTop (fun _ _ => 0) := by
  simpa only [RqBin, pooledQBin, if_pos rfl, true_or, ite_true, mul_zero,
    Finset.sum_const_zero, add_zero] using
    nuisanceRates_positive_treatment_centering_weighted_root_n_negligible
      M μ L e0 eh he0 heh k c W hc hW hclip w hw hwb hrp hrpi

end Papers.TbsPrteOptimalTransport

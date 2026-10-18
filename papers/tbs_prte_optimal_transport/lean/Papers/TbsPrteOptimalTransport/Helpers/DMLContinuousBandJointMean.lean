module
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousBandJointBias
public import Papers.TbsPrteOptimalTransport.Helpers.DMLRemainderRates
public import Papers.TbsPrteOptimalTransport.Helpers.DMLIndicatorRates
public import Papers.TbsPrteOptimalTransport.Helpers.DMLObservedResidualConvergence
/-! L2 bounds for joint continuous band regression and denominator errors.
The exact assignment cancellation leaves products of L2 errors, rather than
requiring uniform convergence of the fitted regressions. -/
public section
set_option linter.style.haveILetI false
set_option linter.style.openClassical false
set_option linter.style.whitespace false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSimpArgs false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: continuous_band_assignment_defect_L2_bound
/-- Suppose [all fitted positive-level assignment probabilities are measurable](hyp:hpi),
[the covariate weight v is measurable](hyp:hv) and [square integrable](hyp:hv2),
[c is positive](hyp:hc), [the fitted assignment probability at the selected level is at least c almost surely](hyp:hclip), and
[its error relative to the true level assignment probability is square integrable](hyp:hden).
Then [the absolute mean of v times one minus the true-to-fitted assignment-probability ratio is at most the product of the assignment-probability L2 error and the L2 norm of v, divided by c](goal). -/
lemma continuous_band_assignment_defect_L2_bound
    (L : LevelData Z X) (pi : PositiveIndex L.K → X → ℝ)
    (hpi : ∀ i, Measurable (pi i)) (i : PositiveIndex L.K)
    (v : X → ℝ) (hv : Measurable v) (hv2 : MemLp v 2 (xLaw M))
    (c : ℝ) (hc : 0 < c) (hclip : ∀ᵐ x ∂xLaw M, c ≤ pi i x)
    (hden : MemLp (fun x => pi i x - (levelSetProb M L).1 i x) 2 (xLaw M)) :
    |∫ o : Obs X Z, v o.1 *
      (1 - (∑ z ∈ L.S i, instProb M z o.1) / positiveValue pi i o.1)
        ∂observationLaw M| ≤
      finiteL2Error M (pi i) ((levelSetProb M L).1 i) *
        finiteL2Error M v (fun _ => 0) / c := by
  have hp : Measurable ((levelSetProb M L).1 i) := by
    fun_prop
  have he := clipped_assignment_regression_L2_remainder (xLaw M)
    ((levelSetProb M L).1 i) (pi i) v c hc hp (hpi i) hclip hden hv2
  have hn : finiteL2Error M v (fun _ => 0) = (eLpNorm v 2 (xLaw M)).toReal := by
    simpa only [sub_zero] using l2Error_eq_eLpNorm M v (fun _ => 0)
      (by simpa only [sub_zero] using hv2)
  rw [l2Error_eq_eLpNorm M _ _ hden, hn]
  have heq : (∫ o : Obs X Z, v o.1 *
      (1 - (∑ z ∈ L.S i, instProb M z o.1) / positiveValue pi i o.1)
        ∂observationLaw M) =
      ∫ x, (1 - (levelSetProb M L).1 i x / pi i x) * v x ∂xLaw M := by
    simp only [positiveValue, dif_pos i.property]
    change (∫ o : Obs X Z, v o.1 *
      (1 - (levelSetProb M L).1 i o.1 / pi i o.1) ∂observationLaw M) = _
    rw [observationLaw_covariate_integral M
      (fun x => v x * (1 - (levelSetProb M L).1 i x / pi i x)) (by fun_prop)]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [levelSetProb]
    ring
  rw [heq]
  exact he.2

-- The two primitive coefficients contain the joint changes of band means,
-- boundary CDF regressions and their propensity multipliers.
-- @node: population_continuous_band_joint_regression_L2_bias_bound
/-- Suppose two nuisance specifications agree in [level assignment probabilities](hyp:hpi),
[level treatment probabilities](hyp:hp), [quantile boundaries](hyp:hn), [instrument propensities](hyp:hprop),
[shares](hyp:hshare), and [band denominators](hyp:htau).
Let [the upper coefficient equal the covariate weight times the upper level treatment probability times the change in the upper regression coefficient](hyp:hvp), and
[the lower coefficient equal the weight times the negative lower level treatment probability times the change in the lower regression coefficient, with zero at level zero](hyp:hvm).
If [the common assignment probabilities are measurable](hyp:hpm), [the upper coefficient is measurable](hyp:hvpm),
[the lower coefficient is measurable](hyp:hvmm), [c is positive](hyp:hc), [all common assignment probabilities are at least c almost surely](hyp:hclip),
[the upper coefficient is bounded in absolute value by Bp almost surely](hyp:hBp),
[the lower coefficient is bounded in absolute value by Bm almost surely](hyp:hBm), and
[all assignment-probability errors relative to truth are square integrable](hyp:hden), then
[the absolute mean weighted component-score difference is bounded by the sum of the upper and lower assignment-probability L2 errors times their respective coefficient L2 norms, divided by c](goal). -/
lemma population_continuous_band_joint_regression_L2_bias_bound
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X) (e b : NuisanceCont L)
    (hpi : e.piLev = b.piLev) (hp : e.pLev = b.pLev) (hn : e.nu = b.nu)
    (hprop : e.prop = b.prop) (hshare : e.share = b.share) (htau : e.tauLev = b.tauLev)
    (k : Fin L.K) (j : ℕ) (w vp vm : X → ℝ)
    (hvp : ∀ x, vp x = w x * (positiveValue b.pLev (k+1) x *
      (alphaHigh M L e k j x - alphaHigh M L b k j x)))
    (hvm : ∀ x, vm x = w x * (if k.val = 0 then 0 else -positiveValue b.pLev k x *
      (alphaLow M L e k j x - alphaLow M L b k j x)))
    (hpm : ∀ i, Measurable (b.piLev i)) (hvpm : Measurable vp) (hvmm : Measurable vm)
    (c Bp Bm : ℝ) (hc : 0 < c)
    (hclip : ∀ i, ∀ᵐ x ∂xLaw M, c ≤ b.piLev i x)
    (hBp : ∀ᵐ x ∂xLaw M, ‖vp x‖ ≤ Bp) (hBm : ∀ᵐ x ∂xLaw M, ‖vm x‖ ≤ Bm)
    (hden : ∀ i, MemLp (fun x => b.piLev i x - (levelSetProb M L).1 i x)
      2 (xLaw M)) :
    |∫ o : Obs X Z, w o.1 *
      (contScoreComponents M phi dphi L e k j o -
        contScoreComponents M phi dphi L b k j o) ∂observationLaw M| ≤
      (finiteL2Error M (positiveValue b.piLev (k.val+1))
          (positiveValue (trueNuisance M L).piLev (k.val+1)) *
        finiteL2Error M vp (fun _ => 0) +
       finiteL2Error M (positiveValue b.piLev k.val)
          (positiveValue (trueNuisance M L).piLev k.val) *
        finiteL2Error M vm (fun _ => 0)) / c := by
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  have hvp2 : MemLp vp 2 (xLaw M) := MemLp.of_bound hvpm.aestronglyMeasurable Bp hBp
  have hvm2 : MemLp vm 2 (xLaw M) := MemLp.of_bound hvmm.aestronglyMeasurable Bm hBm
  obtain ⟨_, heq⟩ := population_continuous_band_joint_regression_bias M phi dphi L e b
    hpi hp hn hprop hshare htau k j w vp vm hvp hvm hpm hvpm hvmm
    c Bp Bm hc hclip hBp hBm
  have hplus := continuous_band_assignment_defect_L2_bound M L b.piLev hpm
    ⟨k.val+1, by omega⟩ vp hvpm hvp2 c hc (hclip _) (hden _)
  have hminus : |∫ o : Obs X Z, vm o.1 *
      (1 - (∑ z ∈ L.S k, instProb M z o.1) / positiveValue b.piLev k o.1)
        ∂observationLaw M| ≤
      finiteL2Error M (positiveValue b.piLev k.val)
        (positiveValue (trueNuisance M L).piLev k.val) *
          finiteL2Error M vm (fun _ => 0) / c := by
    by_cases hk0 : k.val = 0
    · have hz : vm = fun _ => (0 : ℝ) := by
        funext x
        simp only [hvm, hk0, if_true, mul_zero]
      simp only [hz, zero_mul, integral_zero, abs_zero]
      exact div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hc.le
    · have hi : 1 ≤ k.val ∧ k.val ≤ L.K := by omega
      simpa only [finiteL2Error, trueNuisance, positiveValue, dif_pos hi] using
        continuous_band_assignment_defect_L2_bound M L b.piLev hpm
          ⟨k.val, hi⟩ vm hvmm hvm2 c hc (hclip _) (hden _)
  have hplus' : |∫ o : Obs X Z, vp o.1 *
      (1 - (∑ z ∈ L.S (k+1), instProb M z o.1) / positiveValue b.piLev (k+1) o.1)
        ∂observationLaw M| ≤
      finiteL2Error M (positiveValue b.piLev (k.val+1))
        (positiveValue (trueNuisance M L).piLev (k.val+1)) *
          finiteL2Error M vp (fun _ => 0) / c := by
    simpa only [finiteL2Error, trueNuisance, positiveValue,
      dif_pos (show 1 ≤ k.val+1 ∧ k.val+1 ≤ L.K by omega)] using hplus
  rw [heq]
  exact (abs_sub _ _).trans ((add_le_add hplus' hminus).trans_eq (by ring))

-- The coefficient-rate premises are for the primitive signed regression
-- differences displayed above, not for a score bias or a limiting law.
-- @node: nuisanceRates_continuous_band_joint_regression_bias_root_n_negligible
/-- Suppose two random nuisance sequences agree at every sample size and realization in
[level assignment probabilities](hyp:hpi), [level treatment probabilities](hyp:hp), [quantile boundaries](hyp:hn),
[instrument propensities](hyp:hprop), [shares](hyp:hshare), and [band denominators](hyp:htau).
Let [the upper signed coefficient equal the weight times the upper level treatment probability times the upper regression-coefficient difference](hyp:hvp), and
[the lower signed coefficient equal the weight times the negative lower level treatment probability times the lower regression-coefficient difference, with zero at level zero](hyp:hvm).
Assume [the common assignment probabilities are measurable](hyp:hpm), [both signed coefficients are measurable](hyp:hvmeas),
[c is positive](hyp:hc), [all common assignment probabilities are at least c almost surely](hyp:hclip),
[both signed coefficients are bounded in absolute value by B almost surely](hyp:hB),
[all assignment-probability errors relative to truth are square integrable](hyp:hden),
[each common assignment probability's L2 error relative to truth is negligible in probability compared with the inverse fourth root of the sample size](hyp:hrpi), and
[each signed coefficient's L2 norm is negligible in probability compared with the inverse fourth root of the sample size](hyp:hrv).
Then [the mean weighted component-score difference at sample sizes twice the quantity n + 1, multiplied by the square root of n + 1, converges to zero in probability](goal). -/
lemma nuisanceRates_continuous_band_joint_regression_bias_root_n_negligible
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (eh bh : ℕ → A → NuisanceCont L)
    (hpi : ∀ n a, (eh n a).piLev = (bh n a).piLev)
    (hp : ∀ n a, (eh n a).pLev = (bh n a).pLev)
    (hn : ∀ n a, (eh n a).nu = (bh n a).nu)
    (hprop : ∀ n a, (eh n a).prop = (bh n a).prop)
    (hshare : ∀ n a, (eh n a).share = (bh n a).share)
    (htau : ∀ n a, (eh n a).tauLev = (bh n a).tauLev)
    (k : Fin L.K) (j : ℕ) (w : ℕ → A → X → ℝ)
    (v : ℕ → A → Bool → X → ℝ)
    (hvp : ∀ n a x, v n a true x = w n a x * (positiveValue (bh n a).pLev (k+1) x *
      (alphaHigh M L (eh n a) k j x - alphaHigh M L (bh n a) k j x)))
    (hvm : ∀ n a x, v n a false x = w n a x *
      (if k.val = 0 then 0 else -positiveValue (bh n a).pLev k x *
        (alphaLow M L (eh n a) k j x - alphaLow M L (bh n a) k j x)))
    (hpm : ∀ n a i, Measurable ((bh n a).piLev i))
    (hvmeas : ∀ n a s, Measurable (v n a s))
    (c B : ℝ) (hc : 0 < c)
    (hclip : ∀ n a i, ∀ᵐ x ∂xLaw M, c ≤ (bh n a).piLev i x)
    (hB : ∀ n a s, ∀ᵐ x ∂xLaw M, ‖v n a s x‖ ≤ B)
    (hden : ∀ n a i, MemLp
      (fun x => (bh n a).piLev i x - (levelSetProb M L).1 i x) 2 (xLaw M))
    (hrpi : FiniteNuisanceRates M μ (fun n a => (bh n a).piLev) (trueNuisance M L).piLev)
    (hrv : FiniteNuisanceRates M μ v (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
        (∫ o : Obs X Z, w (2*(n+1)) a o.1 *
          (contScoreComponents M phi dphi L (eh (2*(n+1)) a) k j o -
            contScoreComponents M phi dphi L (bh (2*(n+1)) a) k j o)
          ∂observationLaw M)) atTop (fun _ _ => 0) := by
  have hr (s : Bool) := dml_quarter_rate_product μ
    (fun n a => finiteL2Error M
      (positiveValue (bh (2*(n+1)) a).piLev (if s then k.val+1 else k.val))
      (positiveValue (trueNuisance M L).piLev (if s then k.val+1 else k.val)))
    (fun n a => finiteL2Error M (v (2*(n+1)) a s) (fun _ => 0))
    (nuisanceRates_positiveValue M μ L.K _ _ hrpi (if s then k.val+1 else k.val))
    (hrv s)
  have hsum := (hr true).add_eventually_nonneg_rate
    (Eventually.of_forall (fun _ => Real.rpow_nonneg (by positivity) _)) (hr false)
  apply dml_root_n_bias_tendsto_probability μ
  apply Causalean.Stat.IsLittleOp.of_abs_le_const_mul (by positivity : 0 < 1 / c) hsum
  intro n a
  have hb := population_continuous_band_joint_regression_L2_bias_bound M phi dphi L
    (eh (2*(n+1)) a) (bh (2*(n+1)) a) (hpi _ a) (hp _ a) (hn _ a)
    (hprop _ a) (hshare _ a) (htau _ a) k j (w (2*(n+1)) a)
    (v (2*(n+1)) a true) (v (2*(n+1)) a false)
    (hvp _ a) (hvm _ a) (hpm _ a) (hvmeas _ a true) (hvmeas _ a false)
    c B B hc (hclip _ a) (hB _ a true) (hB _ a false) (hden _ a)
  simp only [Bool.true_eq, Bool.false_eq_true, if_true, if_false]
  apply hb.trans
  rw [one_div, div_eq_mul_inv, mul_comm]
  exact mul_le_mul_of_nonneg_left (le_abs_self _) (inv_nonneg.mpr hc.le)

end Papers.TbsPrteOptimalTransport

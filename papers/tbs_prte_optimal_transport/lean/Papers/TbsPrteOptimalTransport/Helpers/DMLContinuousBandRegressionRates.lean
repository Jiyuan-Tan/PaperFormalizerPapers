module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousRieszRates
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousBandJointMean
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousMovingPropensity
/-! Signed coefficient rates for the continuous band regression bias.
Clipped propensity multipliers preserve representer error rates. Combining
these rates with assignment denominator rates makes the joint bias negligible. -/
public section
set_option linter.style.haveILetI false
set_option linter.style.openClassical false
set_option linter.unusedFintypeInType false
set_option linter.unusedTactic false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]
  [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z) (μ : Measure A)

-- @node: encoded_continuous_signed_band_regression_coefficient_quarter_rate
/-- If [the reference nuisance is admissible](hyp:he0), [both fitted sequences
are admissible](hyp:heh,hbh), [both have encoded little-o fourth-root error
rates relative to the reference](hyp:hre,hrb), and [the weights are
measurable](hyp:hw) and [bounded in absolute value by one almost
everywhere](hyp:hwb), then [the weights times the second fit's treatment
propensities times the upper representer differences, together with their
negative lower counterparts, zero at level zero, have coordinatewise L²
little-o fourth-root rates toward zero](goal). -/
lemma encoded_continuous_signed_band_regression_coefficient_quarter_rate
    (L : LevelData Z X) (e0 : NuisanceCont L)
    (eh bh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L e0)
    (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hbh : ∀ n a, ContAdmissible M L (bh n a))
    (hre : FiniteNuisanceRates M μ (fun n a => contComponent M L (eh n a))
      (contComponent M L e0))
    (hrb : FiniteNuisanceRates M μ (fun n a => contComponent M L (bh n a))
      (contComponent M L e0))
    (w : ℕ → A → X → ℝ) (hw : ∀ n a, Measurable (w n a))
    (hwb : ∀ n a, ∀ᵐ x ∂xLaw M, |w n a x| ≤ 1) :
    FiniteNuisanceRates M μ
      (fun n a (i : Bool × (ℕ × ℕ)) x => w n a x *
        (if i.1 then positiveValue (bh n a).pLev (i.2.1+1) x *
          (alphaHigh M L (eh n a) i.2.1 i.2.2 x -
            alphaHigh M L (bh n a) i.2.1 i.2.2 x)
        else if i.2.1 = 0 then 0 else -positiveValue (bh n a).pLev i.2.1 x *
          (alphaLow M L (eh n a) i.2.1 i.2.2 x -
            alphaLow M L (bh n a) i.2.1 i.2.2 x))) (fun _ _ => 0) := by
  let W := fun n a (i : Bool × (ℕ × ℕ)) x => w n a x *
    (if i.1 then positiveValue (bh n a).pLev (i.2.1+1) x
      else if i.2.1 = 0 then 0 else -positiveValue (bh n a).pLev i.2.1 x)
  have hW n a i : Measurable (W n a i) := by
    try fun_prop
    dsimp only [W]
    split_ifs
    · exact (hw n a).mul ((fitted_continuous_full_coordinates M L _ (hbh n a) _).1.1)
    · fun_prop
    · exact (hw n a).mul ((fitted_continuous_full_coordinates M L _ (hbh n a) _).1.1.neg)
  have hWB n a i : ∀ᵐ x ∂xLaw M, |W n a i x| ≤ 1 := by
    have hp k := (fitted_continuous_full_coordinates M L _ (hbh n a) k).1.2
    filter_upwards [hwb n a, hp (i.2.1+1), hp i.2.1] with x hx hp1 hp0
    dsimp only [W]
    rw [abs_mul]
    apply (mul_le_mul_of_nonneg_right hx (abs_nonneg _)).trans
    simp only [one_mul]
    split_ifs <;> simp_all only [abs_neg, abs_zero, zero_le_one]
  have hs := encoded_continuous_weighted_alpha_difference_quarter_rate M μ L e0 eh bh
    he0 heh hbh hre hrb W hW hWB
  intro i
  cases hi : i.1 <;>
    simpa only [W, hi, Bool.false_eq_true, if_false, if_true, mul_assoc,
      ite_mul, zero_mul] using hs i

-- @node: encoded_continuous_band_joint_regression_bias_root_n_negligible
/-- Suppose [truth is admissible](hyp:he0), [both fitted sequences are
admissible](hyp:heh,hbh), and [both have encoded little-o fourth-root error
rates relative to truth](hyp:hre,hrb), with identical [assignment
denominators](hyp:hpi), [treatment propensities](hyp:hp), [quantile
boundaries](hyp:hn), [instrument propensities](hyp:hprop), [shares](hyp:hshare),
and [level thresholds](hyp:htau). If [the weights are measurable](hyp:hw) and
[bounded in absolute value by one almost everywhere](hyp:hwb), [the clipping
constant is positive](hyp:hc), and [all second-fit assignment denominators are
at least that constant almost everywhere](hyp:hclip), then [the mean weighted
component-score difference at fit size twice n plus two, scaled by the square
root of n plus one, converges to zero in probability](goal). -/
lemma encoded_continuous_band_joint_regression_bias_root_n_negligible
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (eh bh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hbh : ∀ n a, ContAdmissible M L (bh n a))
    (hre : FiniteNuisanceRates M μ (fun n a => contComponent M L (eh n a))
      (contComponent M L (trueNuisance M L)))
    (hrb : FiniteNuisanceRates M μ (fun n a => contComponent M L (bh n a))
      (contComponent M L (trueNuisance M L)))
    (hpi : ∀ n a, (eh n a).piLev = (bh n a).piLev)
    (hp : ∀ n a, (eh n a).pLev = (bh n a).pLev)
    (hn : ∀ n a, (eh n a).nu = (bh n a).nu)
    (hprop : ∀ n a, (eh n a).prop = (bh n a).prop)
    (hshare : ∀ n a, (eh n a).share = (bh n a).share)
    (htau : ∀ n a, (eh n a).tauLev = (bh n a).tauLev)
    (k : Fin L.K) (j : ℕ) (w : ℕ → A → X → ℝ)
    (hw : ∀ n a, Measurable (w n a))
    (hwb : ∀ n a, ∀ᵐ x ∂xLaw M, |w n a x| ≤ 1)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a i, ∀ᵐ x ∂xLaw M, c ≤ (bh n a).piLev i x) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
        (∫ o : Obs X Z, w (2*(n+1)) a o.1 *
          (contScoreComponents M phi dphi L (eh (2*(n+1)) a) k j o -
            contScoreComponents M phi dphi L (bh (2*(n+1)) a) k j o)
          ∂observationLaw M)) atTop (fun _ _ => 0) := by
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  let v := fun n a (s : Bool) x => w n a x *
    (if s then positiveValue (bh n a).pLev (k.val+1) x *
      (alphaHigh M L (eh n a) k j x - alphaHigh M L (bh n a) k j x)
    else if k.val = 0 then 0 else -positiveValue (bh n a).pLev k x *
      (alphaLow M L (eh n a) k j x - alphaLow M L (bh n a) k j x))
  have hv n a s : Measurable (v n a s) := by
    try fun_prop
    have hpp := (fitted_continuous_full_coordinates M L _ (hbh n a) (k.val+1)).1.1
    have hpm := (fitted_continuous_full_coordinates M L _ (hbh n a) k).1.1
    have hep := continuous_admissible_alphaHigh_measurable M L _ (heh n a) k j
    have hbp := continuous_admissible_alphaHigh_measurable M L _ (hbh n a) k j
    have hem := continuous_admissible_alphaLow_measurable M L _ (heh n a) k j
    have hbm := continuous_admissible_alphaLow_measurable M L _ (hbh n a) k j
    dsimp only [v]
    split_ifs
    · exact (hw n a).mul (hpp.mul (hep.sub hbp))
    · fun_prop
    · exact (hw n a).mul (hpm.neg.mul (hem.sub hbm))
  have hB n a s : ∀ᵐ x ∂xLaw M,
      ‖v n a s x‖ ≤ 10 * (|M.yMin| + |M.yMax|) := by
    have hp k := (fitted_continuous_full_coordinates M L _ (hbh n a) k).1.2
    have he := continuous_admissible_alpha_abs_bounds M L _ (heh n a) k j
    have hb := continuous_admissible_alpha_abs_bounds M L _ (hbh n a) k j
    filter_upwards [hwb n a, hp (k.val+1), hp k.val, he.1, he.2, hb.1, hb.2]
      with x hx hpp hpm hep hem hbp hbm
    have hplus : |alphaHigh M L (eh n a) k j x - alphaHigh M L (bh n a) k j x| ≤
        10 * (|M.yMin| + |M.yMax|) := (abs_sub _ _).trans (by linarith)
    have hminus : |alphaLow M L (eh n a) k j x - alphaLow M L (bh n a) k j x| ≤
        10 * (|M.yMin| + |M.yMax|) := (abs_sub _ _).trans (by linarith)
    dsimp only [v]
    rw [Real.norm_eq_abs, abs_mul]
    apply (mul_le_mul_of_nonneg_right hx (abs_nonneg _)).trans
    rw [one_mul]
    split_ifs
    · rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right hpp (abs_nonneg _)).trans
        (by simpa only [one_mul] using hplus)
    · simp only [abs_zero]; positivity
    · rw [abs_mul, abs_neg]
      exact (mul_le_mul_of_nonneg_right hpm (abs_nonneg _)).trans
        (by simpa only [one_mul] using hminus)
  have hpm n a i : Measurable ((bh n a).piLev i) := by
    first | fun_prop | exact (hbh n a).2.2.2.2.2.1 i
  have hden n a i : MemLp
      (fun x => (bh n a).piLev i x - (levelSetProb M L).1 i x) 2 (xLaw M) := by
    have hfit : MemLp ((bh n a).piLev i) 2 (xLaw M) := by
      apply MemLp.of_bound (hpm n a i).aestronglyMeasurable 1
      filter_upwards [(hbh n a).2.2.2.2.1 i] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
      exact hx.2
    have htrue : MemLp ((levelSetProb M L).1 i) 2 (xLaw M) := by
      apply MemLp.of_bound (by
        first | fun_prop | exact (he0.2.2.2.2.2.1 i).aestronglyMeasurable) 1
      filter_upwards [he0.2.2.2.2.1 i] with x hx
      change ‖(trueNuisance M L).piLev i x‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
      exact hx.2
    exact hfit.sub htrue
  have hrv : FiniteNuisanceRates M μ v (fun _ _ => 0) := by
    intro s
    exact encoded_continuous_signed_band_regression_coefficient_quarter_rate
      M μ L (trueNuisance M L) eh bh he0 heh hbh hre hrb w hw hwb (s, (k.val,j))
  have hrpi := (continuous_component_rates_to_oracle_rates M μ L bh _ hrb).2.2.1
  exact nuisanceRates_continuous_band_joint_regression_bias_root_n_negligible
    M μ phi dphi L eh bh hpi hp hn hprop hshare htau k j w v
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) hpm hv c
    (10 * (|M.yMin| + |M.yMax|)) hc hclip hB hden hrpi hrv

-- The product-score weight is supplied by the fitted nuisance construction;
-- its measurability and bound are derived rather than added as assumptions.
-- @node: encoded_continuous_gamma_band_joint_regression_bias_root_n_negligible
/-- Assume [truth is admissible](hyp:he0), [both fitted sequences are
admissible](hyp:heh,hbh), and [both have encoded little-o fourth-root error
rates relative to truth](hyp:hre,hrb). If the sequences share [assignment
denominators](hyp:hpi), [treatment propensities](hyp:hp), [quantile
boundaries](hyp:hn), [instrument propensities](hyp:hprop), [shares](hyp:hshare),
and [level thresholds](hyp:htau), [the clipping constant is positive](hyp:hc),
and [all second-fit assignment denominators are at least that constant almost
everywhere](hyp:hclip), then [the mean difference of the preceding band's
component scores weighted by the first fit's assignment share, evaluated at
fit size twice n plus two and scaled by the square root of n plus one,
converges to zero in probability](goal). -/
lemma encoded_continuous_gamma_band_joint_regression_bias_root_n_negligible
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (eh bh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hbh : ∀ n a, ContAdmissible M L (bh n a))
    (hre : FiniteNuisanceRates M μ (fun n a => contComponent M L (eh n a))
      (contComponent M L (trueNuisance M L)))
    (hrb : FiniteNuisanceRates M μ (fun n a => contComponent M L (bh n a))
      (contComponent M L (trueNuisance M L)))
    (hpi : ∀ n a, (eh n a).piLev = (bh n a).piLev)
    (hp : ∀ n a, (eh n a).pLev = (bh n a).pLev)
    (hn : ∀ n a, (eh n a).nu = (bh n a).nu)
    (hprop : ∀ n a, (eh n a).prop = (bh n a).prop)
    (hshare : ∀ n a, (eh n a).share = (bh n a).share)
    (htau : ∀ n a, (eh n a).tauLev = (bh n a).tauLev)
    (k : Fin L.K) (j : ℕ) (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a i, ∀ᵐ x ∂xLaw M, c ≤ (bh n a).piLev i x) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
        (∫ o : Obs X Z, regularValue (eh (2*(n+1)) a).gamma k j o.1 *
          (contScoreComponents M phi dphi L (eh (2*(n+1)) a) k (j-1) o -
            contScoreComponents M phi dphi L (bh (2*(n+1)) a) k (j-1) o)
          ∂observationLaw M)) atTop (fun _ _ => 0) := by
  apply encoded_continuous_band_joint_regression_bias_root_n_negligible
    M μ phi dphi L eh bh he0 heh hbh hre hrb hpi hp hn hprop hshare htau
    k (j-1) (fun n a => regularValue (eh n a).gamma k j) _ _ c hc hclip
  · intro n a
    first | fun_prop | skip
    rcases heh n a with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hm, _⟩
    unfold regularValue
    split_ifs
    · exact hm _
    · fun_prop
  · intro n a
    rcases heh n a with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hb, _⟩
    unfold regularValue
    split_ifs with h
    · filter_upwards [hb ⟨(k,j),h⟩] with x hx
      rw [abs_of_nonneg hx.1]
      exact hx.2
    · exact Eventually.of_forall (fun _ => by norm_num)

end Papers.TbsPrteOptimalTransport

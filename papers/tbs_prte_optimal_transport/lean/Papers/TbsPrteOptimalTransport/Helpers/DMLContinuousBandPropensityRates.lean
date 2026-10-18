module
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousBandPropensityBias
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousBandJointMean
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousRieszRates
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousMovingPropensity
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousTreatmentResidual
/-! Propensity and assignment-denominator products in the continuous band bias.
The exact finite-instrument mean leaves a product of two nuisance errors;
their quarter rates make this product negligible at root-n scale. -/
@[expose] public section
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.whitespace false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: population_continuous_band_joint_propensity_L2_bias_bound
/-- Suppose two nuisances agree in [assignment denominators](hyp:hpi), [quantile
boundaries](hyp:hn), [upper and lower band outcome means](hyp:hJp,hJm), [upper
and lower band probabilities](hyp:hMp,hMm), [instrument propensities](hyp:hprop),
[shares](hyp:hshare), and [level thresholds](hyp:htau), with [the band number
below the level's band count](hyp:hj). Assume [the upper coefficient is the
weight times the reference upper representer times the upper treatment
propensity difference](hyp:hvp), [the lower coefficient is zero at level zero
and otherwise minus the weight times the reference lower representer times
the lower treatment propensity difference](hyp:hvm), [the reference assignment
denominators are measurable](hyp:hpm), [both coefficients are
measurable](hyp:hvpm,hvmm), [the clipping constant is positive](hyp:hc), [the
denominators are at least that constant almost everywhere](hyp:hclip), [the
upper and lower coefficients satisfy their respective almost everywhere
bounds](hyp:hBp,hBm), and [the denominator errors are square integrable](hyp:hden).
Then [the absolute mean weighted component-score difference is bounded by the
sum of the upper and lower products of denominator L² error and coefficient
L² norm, divided by the clipping constant](goal). -/
lemma population_continuous_band_joint_propensity_L2_bias_bound
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X) (e b : NuisanceCont L)
    (hpi : e.piLev = b.piLev) (hn : e.nu = b.nu)
    (hJp : e.Jplus = b.Jplus) (hJm : e.Jminus = b.Jminus)
    (hMp : e.Mplus = b.Mplus) (hMm : e.Mminus = b.Mminus)
    (hprop : e.prop = b.prop) (hshare : e.share = b.share) (htau : e.tauLev = b.tauLev)
    (k : Fin L.K) (j : ℕ) (hj : j < L.l k) (w vp vm : X → ℝ)
    (hvp : ∀ x, vp x = w x * (alphaHigh M L b k j x *
      (positiveValue e.pLev (k+1) x - positiveValue b.pLev (k+1) x)))
    (hvm : ∀ x, vm x = w x * (if k.val = 0 then 0 else -alphaLow M L b k j x *
      (positiveValue e.pLev k x - positiveValue b.pLev k x)))
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
  obtain ⟨_, heq⟩ := population_continuous_band_joint_propensity_bias M phi dphi L e b
    hpi hn hJp hJm hMp hMm hprop hshare htau k j hj w vp vm hvp hvm hpm hvpm hvmm
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
-- @node: nuisanceRates_continuous_band_joint_propensity_bias_root_n_negligible
/-- Suppose the fitted sequences agree in [assignment denominators](hyp:hpi),
[quantile boundaries](hyp:hn), [upper and lower band means](hyp:hJp,hJm), [upper
and lower band probabilities](hyp:hMp,hMm), [instrument propensities](hyp:hprop),
[shares](hyp:hshare), and [level thresholds](hyp:htau), and [the band number is
below the level's band count](hyp:hj). Let [the signed coefficient family](hyp:v)
have [upper coefficients equal to the weight times the second fit's upper
representer times the upper treatment propensity difference](hyp:hvp) and
[lower coefficients equal to zero at level zero and otherwise minus the
weight times the second fit's lower representer times the lower treatment
propensity difference](hyp:hvm). If [the second fit's denominators are
measurable](hyp:hpm), [the coefficients are measurable](hyp:hvmeas), [the clipping
constant is positive](hyp:hc), [the denominators are uniformly bounded below
by it almost everywhere](hyp:hclip), [the coefficients are uniformly bounded
almost everywhere](hyp:hB), [denominator errors are square integrable](hyp:hden),
[denominator errors have little-o fourth-root rates relative to truth](hyp:hrpi),
and [coefficients have little-o fourth-root rates toward zero](hyp:hrv), then
[the mean weighted component-score difference at fit size twice n plus two,
scaled by the square root of n plus one, converges to zero in probability](goal). -/
lemma nuisanceRates_continuous_band_joint_propensity_bias_root_n_negligible
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (eh bh : ℕ → A → NuisanceCont L)
    (hpi : ∀ n a, (eh n a).piLev = (bh n a).piLev)
    (hn : ∀ n a, (eh n a).nu = (bh n a).nu)
    (hJp : ∀ n a, (eh n a).Jplus = (bh n a).Jplus)
    (hJm : ∀ n a, (eh n a).Jminus = (bh n a).Jminus)
    (hMp : ∀ n a, (eh n a).Mplus = (bh n a).Mplus)
    (hMm : ∀ n a, (eh n a).Mminus = (bh n a).Mminus)
    (hprop : ∀ n a, (eh n a).prop = (bh n a).prop)
    (hshare : ∀ n a, (eh n a).share = (bh n a).share)
    (htau : ∀ n a, (eh n a).tauLev = (bh n a).tauLev)
    (k : Fin L.K) (j : ℕ) (hj : j < L.l k) (w : ℕ → A → X → ℝ)
    (v : ℕ → A → Bool → X → ℝ)
    (hvp : ∀ n a x, v n a true x = w n a x * (alphaHigh M L (bh n a) k j x *
      (positiveValue (eh n a).pLev (k+1) x - positiveValue (bh n a).pLev (k+1) x)))
    (hvm : ∀ n a x, v n a false x = w n a x *
      (if k.val = 0 then 0 else -alphaLow M L (bh n a) k j x *
        (positiveValue (eh n a).pLev k x - positiveValue (bh n a).pLev k x)))
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
  have hb := population_continuous_band_joint_propensity_L2_bias_bound M phi dphi L
    (eh (2*(n+1)) a) (bh (2*(n+1)) a) (hpi _ a) (hn _ a) (hJp _ a) (hJm _ a) (hMp _ a) (hMm _ a)
    (hprop _ a) (hshare _ a) (htau _ a) k j hj (w (2*(n+1)) a)
    (v (2*(n+1)) a true) (v (2*(n+1)) a false)
    (hvp _ a) (hvm _ a) (hpm _ a) (hvmeas _ a true) (hvmeas _ a false)
    c B B hc (hclip _ a) (hB _ a true) (hB _ a false) (hden _ a)
  simp only [Bool.true_eq, Bool.false_eq_true, if_true, if_false]
  apply hb.trans
  rw [one_div, div_eq_mul_inv, mul_comm]
  exact mul_le_mul_of_nonneg_left (le_abs_self _) (inv_nonneg.mpr hc.le)


-- Rates are derived from the encoded primitive nuisances. The representer
-- may move with the estimated quantile, and no extra coefficient rate is assumed.
-- @node: encoded_continuous_signed_band_propensity_coefficient_quarter_rate
/-- If [the reference nuisance is admissible](hyp:he0), [both fitted sequences
are admissible](hyp:heh,hbh), [both have encoded little-o fourth-root error
rates relative to the reference](hyp:hre,hrb), and [the weights are
measurable](hyp:hw) and [bounded in absolute value by one almost
everywhere](hyp:hwb), then [the weight times the second fit's upper representer
times the upper treatment propensity difference, and its signed lower
counterpart, zero at level zero, have L² little-o fourth-root rates toward
zero](goal). -/
lemma encoded_continuous_signed_band_propensity_coefficient_quarter_rate
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (L : LevelData Z X) (e0 : NuisanceCont L)
    (eh bh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L e0)
    (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hbh : ∀ n a, ContAdmissible M L (bh n a))
    (hre : FiniteNuisanceRates M μ (fun n a => contComponent M L (eh n a))
      (contComponent M L e0))
    (hrb : FiniteNuisanceRates M μ (fun n a => contComponent M L (bh n a))
      (contComponent M L e0))
    (k j : ℕ) (w : ℕ → A → X → ℝ)
    (hw : ∀ n a, Measurable (w n a))
    (hwb : ∀ n a, ∀ᵐ x ∂xLaw M, |w n a x| ≤ 1) :
    FiniteNuisanceRates M μ
      (fun n a (s : Bool) x => w n a x *
        (if s then alphaHigh M L (bh n a) k j x *
          (positiveValue (eh n a).pLev (k+1) x - positiveValue (bh n a).pLev (k+1) x)
        else if k = 0 then 0 else -alphaLow M L (bh n a) k j x *
          (positiveValue (eh n a).pLev k x - positiveValue (bh n a).pLev k x)))
      (fun _ _ => 0) := by
  let P := fun (e : NuisanceCont L) (s : Bool) => positiveValue e.pLev (if s then k+1 else k)
  let R := fun (e : NuisanceCont L) (s : Bool) x =>
    if s then alphaHigh M L e k j x else alphaLow M L e k j x
  have hp (e : NuisanceCont L) (he : ContAdmissible M L e) s :
      MemLp (P e s) 2 (xLaw M) :=
    (fitted_continuous_full_coordinate_memLp M L e he _).1
  have ha (e : NuisanceCont L) (he : ContAdmissible M L e) s :
      MemLp (R e s) 2 (xLaw M) := by
    cases s
    · exact fitted_continuous_alphaLow_memLp M L e he k j
    · exact fitted_continuous_alphaHigh_memLp M L e he k j
  have hra : FiniteNuisanceRates M μ (fun n a => R (bh n a)) (R e0) := by
    intro s
    cases s
    · exact encoded_continuous_alphaLow_quarter_rate M μ L e0 bh he0 hbh hrb (k,j)
    · exact encoded_continuous_alphaHigh_quarter_rate M μ L e0 bh he0 hbh hrb (k,j)
  have rates (eh' : ℕ → A → NuisanceCont L)
      (hh : ∀ n a, ContAdmissible M L (eh' n a))
      (hr : FiniteNuisanceRates M μ (fun n a => contComponent M L (eh' n a))
        (contComponent M L e0)) :
      FiniteNuisanceRates M μ (fun n a s x => P (eh' n a) s x * R (bh n a) s x)
        (fun s x => P e0 s x * R e0 s x) := by
    have hrp := (continuous_component_rates_to_oracle_rates M μ L eh' e0 hr).2.1
    apply nuisanceRates_bounded_product M μ _ _ _ _
      (fun n a => hp _ (hh n a)) (fun n a => ha _ (hbh n a))
      (hp _ he0) (ha _ he0) (5 * (|M.yMin| + |M.yMax|)) (by positivity)
    · intro n a s
      exact (fitted_continuous_full_coordinates M L _ (hh n a) _).1.2
    · intro s
      cases s
      · exact (continuous_admissible_alpha_abs_bounds M L e0 he0 k j).2
      · exact (continuous_admissible_alpha_abs_bounds M L e0 he0 k j).1
    · intro s
      exact nuisanceRates_positiveValue M μ L.K _ _ hrp _
    · exact hra
  have hprod (e : NuisanceCont L) (he : ContAdmissible M L e)
      (b : NuisanceCont L) (hb : ContAdmissible M L b) s :
      MemLp (fun x => P e s x * R b s x) 2 (xLaw M) := by
    apply (ha b hb s).norm.mono' ((hp e he s).1.mul (ha b hb s).1)
    filter_upwards [(fitted_continuous_full_coordinates M L e he (if s then k+1 else k)).1.2] with x hx
    change ‖P e s x * R b s x‖ ≤ ‖R b s x‖
    rw [norm_mul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right hx (norm_nonneg _)).trans_eq (one_mul _)
  let F := fun n a s x => P (eh n a) s x * R (bh n a) s x -
    P (bh n a) s x * R (bh n a) s x
  have hrF : FiniteNuisanceRates M μ F (fun _ _ => 0) := by
    simpa only [sub_self] using nuisanceRates_sub M μ _ _ _ _
      (fun n a => hprod _ (heh n a) _ (hbh n a))
      (fun n a => hprod _ (hbh n a) _ (hbh n a))
      (hprod _ he0 _ he0) (hprod _ he0 _ he0) (rates eh heh hre) (rates bh hbh hrb)
  let W := fun n a (s : Bool) x => if s then w n a x else if k = 0 then 0 else -w n a x
  have hW n a s : Measurable (W n a s) := by
    first | fun_prop | skip
    dsimp only [W]
    split_ifs <;> fun_prop
  have hWB n a s : ∀ᵐ x ∂xLaw M, |W n a s x| ≤ 1 := by
    filter_upwards [hwb n a] with x hx
    dsimp only [W]
    split_ifs <;> simp_all only [abs_neg, abs_zero, zero_le_one]
  have hs := nuisanceRates_bounded_error_multiplier M μ F (fun _ _ => 0) W
    (fun n a s => (hprod _ (heh n a) _ (hbh n a) s).sub
      (hprod _ (hbh n a) _ (hbh n a) s))
    (fun _ => MemLp.zero') hW hWB hrF
  convert hs using 1
  funext n a s x
  dsimp only [F, W, P, R]
  cases s <;> by_cases hk : k = 0 <;> simp only [hk, if_true, if_false,
    Bool.false_eq_true, sub_zero, zero_mul]
  all_goals ring

-- @node: encoded_continuous_band_joint_propensity_bias_root_n_negligible
/-- Assume [truth is admissible](hyp:he0), [both fitted sequences are
admissible](hyp:heh,hbh), and [both have encoded little-o fourth-root error
rates relative to truth](hyp:hre,hrb). If they agree in [assignment
denominators](hyp:hpi), [quantile boundaries](hyp:hn), [upper and lower band
means](hyp:hJp,hJm), [upper and lower band probabilities](hyp:hMp,hMm),
[instrument propensities](hyp:hprop), [shares](hyp:hshare), and [level
thresholds](hyp:htau), [the band number is below the level's band count](hyp:hj),
[the weights are measurable](hyp:hw) and [bounded in absolute value by one
almost everywhere](hyp:hwb), [the clipping constant is positive](hyp:hc), and
[all second-fit assignment denominators are at least that constant almost
everywhere](hyp:hclip), then [the weighted component-score mean difference at
fit size twice n plus two, scaled by the square root of n plus one, converges
to zero in probability](goal). -/
lemma encoded_continuous_band_joint_propensity_bias_root_n_negligible
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
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
    (hn : ∀ n a, (eh n a).nu = (bh n a).nu)
    (hJp : ∀ n a, (eh n a).Jplus = (bh n a).Jplus)
    (hJm : ∀ n a, (eh n a).Jminus = (bh n a).Jminus)
    (hMp : ∀ n a, (eh n a).Mplus = (bh n a).Mplus)
    (hMm : ∀ n a, (eh n a).Mminus = (bh n a).Mminus)
    (hprop : ∀ n a, (eh n a).prop = (bh n a).prop)
    (hshare : ∀ n a, (eh n a).share = (bh n a).share)
    (htau : ∀ n a, (eh n a).tauLev = (bh n a).tauLev)
    (k : Fin L.K) (j : ℕ) (hj : j < L.l k)
    (w : ℕ → A → X → ℝ) (hw : ∀ n a, Measurable (w n a))
    (hwb : ∀ n a, ∀ᵐ x ∂xLaw M, |w n a x| ≤ 1)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a i, ∀ᵐ x ∂xLaw M, c ≤ (bh n a).piLev i x) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
        (∫ o : Obs X Z, w (2*(n+1)) a o.1 *
          (contScoreComponents M phi dphi L (eh (2*(n+1)) a) k j o -
            contScoreComponents M phi dphi L (bh (2*(n+1)) a) k j o)
          ∂observationLaw M)) atTop (fun _ _ => 0) := by
  let v := fun n a (s : Bool) x => w n a x *
    (if s then alphaHigh M L (bh n a) k j x *
      (positiveValue (eh n a).pLev (k.val+1) x - positiveValue (bh n a).pLev (k.val+1) x)
    else if k.val = 0 then 0 else -alphaLow M L (bh n a) k j x *
      (positiveValue (eh n a).pLev k x - positiveValue (bh n a).pLev k x))
  have hv n a s : Measurable (v n a s) := by
    first | fun_prop | skip
    have hpp := (fitted_continuous_full_coordinates M L _ (heh n a) (k.val+1)).1.1
    have hbp := (fitted_continuous_full_coordinates M L _ (hbh n a) (k.val+1)).1.1
    have hpm := (fitted_continuous_full_coordinates M L _ (heh n a) k).1.1
    have hbm := (fitted_continuous_full_coordinates M L _ (hbh n a) k).1.1
    have ha := continuous_admissible_alphaHigh_measurable M L _ (hbh n a) k j
    have hb := continuous_admissible_alphaLow_measurable M L _ (hbh n a) k j
    dsimp only [v]
    split_ifs
    · exact (hw n a).mul (ha.mul (hpp.sub hbp))
    · fun_prop
    · exact (hw n a).mul (hb.neg.mul (hpm.sub hbm))
  have hB n a s : ∀ᵐ x ∂xLaw M, ‖v n a s x‖ ≤
      10 * (|M.yMin| + |M.yMax|) := by
    have he i := (fitted_continuous_full_coordinates M L _ (heh n a) i).1.2
    have hb i := (fitted_continuous_full_coordinates M L _ (hbh n a) i).1.2
    have ha := continuous_admissible_alpha_abs_bounds M L _ (hbh n a) k j
    filter_upwards [hwb n a, he (k.val+1), hb (k.val+1), he k.val, hb k.val,
      ha.1, ha.2] with x hwx hep hbp hem hbm hap ham
    have hdp : |positiveValue (eh n a).pLev (k.val+1) x -
        positiveValue (bh n a).pLev (k.val+1) x| ≤ 2 :=
      (abs_sub _ _).trans (by linarith)
    have hdm : |positiveValue (eh n a).pLev k x -
        positiveValue (bh n a).pLev k x| ≤ 2 :=
      (abs_sub _ _).trans (by linarith)
    dsimp only [v]
    rw [Real.norm_eq_abs, abs_mul]
    apply (mul_le_mul_of_nonneg_right hwx (abs_nonneg _)).trans
    rw [one_mul]
    split_ifs
    · rw [abs_mul]
      exact (mul_le_mul hap hdp (abs_nonneg _) (by positivity)).trans_eq (by ring)
    · simp only [abs_zero]; positivity
    · rw [abs_mul, abs_neg]
      exact (mul_le_mul ham hdm (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have hpm n a i : Measurable ((bh n a).piLev i) := by
    first | fun_prop | exact (hbh n a).2.2.2.2.2.1 i
  have hden n a i : MemLp
      (fun x => (bh n a).piLev i x - (levelSetProb M L).1 i x) 2 (xLaw M) := by
    have hfit := (fitted_continuous_treatment_assignment_memLp M L _ (hbh n a) i.val).2
    have htrue := (fitted_continuous_treatment_assignment_memLp M L _ he0 i.val).2
    have hd := hfit.sub htrue
    change MemLp (fun x => positiveValue (bh n a).piLev i.val x -
      positiveValue (trueNuisance M L).piLev i.val x) 2 (xLaw M) at hd
    simpa only [trueNuisance, positiveValue, dif_pos i.property] using hd
  have hrv : FiniteNuisanceRates M μ v (fun _ _ => 0) :=
    encoded_continuous_signed_band_propensity_coefficient_quarter_rate
      M μ L _ eh bh he0 heh hbh hre hrb k j w hw hwb
  have hrpi := (continuous_component_rates_to_oracle_rates M μ L bh _ hrb).2.2.1
  exact nuisanceRates_continuous_band_joint_propensity_bias_root_n_negligible
    M μ phi dphi L eh bh hpi hn hJp hJm hMp hMm hprop hshare htau
    k j hj w v (fun _ _ _ => rfl) (fun _ _ _ => rfl) hpm hv c
    (10 * (|M.yMin| + |M.yMax|)) hc hclip hB hden hrpi hrv

-- @node: continuousBandPropensityHybrid
/-- The [band propensity hybrid](goal) combines [a base nuisance](hyp:e) with
[a reference nuisance](hyp:b) by replacing only the base's level treatment
propensities with those of the reference. -/
def continuousBandPropensityHybrid {L : LevelData Z X} (e b : NuisanceCont L) :
    NuisanceCont L := {e with pLev := b.pLev}

-- @node: continuous_band_propensity_hybrid_admissible
/-- If [the base nuisance is admissible](hyp:he) and [the reference nuisance is
admissible](hyp:hb), then [restoring the reference level treatment propensities
in the base nuisance preserves admissibility](goal). -/
lemma continuous_band_propensity_hybrid_admissible
    (L : LevelData Z X) (e b : NuisanceCont L)
    (he : ContAdmissible M L e) (hb : ContAdmissible M L b) :
    ContAdmissible M L (continuousBandPropensityHybrid e b) := by
  rcases he with ⟨h1, h2, _, _, h5, h6, h7, h8, h9, h10, h11, h12,
    h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25,
    h26, h27, h28, h29, h30, h31⟩
  exact ⟨h1, h2, hb.2.2.1, hb.2.2.2.1, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22,
    h23, h24, h25, h26, h27, h28, h29, h30, h31⟩

-- @node: continuous_band_propensity_hybrid_component
/-- [Each encoded coordinate of the propensity hybrid equals the reference
coordinate when its type is 1 and equals the base coordinate otherwise](goal). -/
lemma continuous_band_propensity_hybrid_component
    (L : LevelData Z X) (e b : NuisanceCont L) (i : ℕ × ℕ × ℕ × Z) :
    contComponent M L (continuousBandPropensityHybrid e b) i =
      if i.1 = 1 then contComponent M L b i else contComponent M L e i := by
  rcases i with ⟨r, k, j, z⟩
  rcases r with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | r <;>
    funext x <;> simp [contComponent, continuousBandPropensityHybrid, minusFullValue, nuValue]
  split <;> first | omega | rfl

-- @node: encoded_continuous_band_propensity_hybrid_rates
/-- If [the fitted encoded errors have little-o fourth-root rates relative to
a reference nuisance](hyp:hr), then [restoring the reference level treatment
propensities preserves those coordinatewise L² rates](goal). -/
lemma encoded_continuous_band_propensity_hybrid_rates
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (L : LevelData Z X) (e0 : NuisanceCont L) (eh : ℕ → A → NuisanceCont L)
    (hr : FiniteNuisanceRates M μ (fun n a => contComponent M L (eh n a))
      (contComponent M L e0)) :
    FiniteNuisanceRates M μ
      (fun n a => contComponent M L (continuousBandPropensityHybrid (eh n a) e0))
      (contComponent M L e0) := by
  intro i
  apply Causalean.Stat.IsLittleOp.of_abs_le_const_mul one_pos (hr i)
  intro n a
  dsimp only
  rw [continuous_band_propensity_hybrid_component M, one_mul]
  split_ifs
  · simp only [finiteL2Error, sub_self, zero_pow (by norm_num : 2 ≠ 0), integral_zero,
      Real.sqrt_zero, abs_zero]
    exact abs_nonneg _
  · exact le_rfl

-- The regression and quantile coordinates still move. Restoring only pLev
-- is justified by the joint propensity/assignment cancellation proved above.
-- @node: encoded_continuous_gamma_band_propensity_restoration_root_n_negligible
/-- Suppose [truth is admissible](hyp:he0), [every fitted nuisance is
admissible](hyp:heh), [the encoded fitted errors have little-o fourth-root
rates relative to truth](hyp:hr), [the band number is between one and the
level's band count](hyp:hj), [the clipping constant is positive](hyp:hc), and
[all fitted assignment denominators are at least that constant almost
everywhere](hyp:hclip). Then [the mean change in the preceding band's
component score from restoring true treatment propensities, weighted by the
fitted assignment share at fit size twice n plus two and scaled by the square
root of n plus one, converges to zero in probability](goal). -/
lemma encoded_continuous_gamma_band_propensity_restoration_root_n_negligible
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hr : FiniteNuisanceRates M μ (fun n a => contComponent M L (eh n a))
      (contComponent M L (trueNuisance M L)))
    (k : Fin L.K) (j : ℕ) (hj : 1 ≤ j ∧ j ≤ L.l k)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a i, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).piLev i x) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
        (∫ o : Obs X Z, regularValue (eh (2*(n+1)) a).gamma k j o.1 *
          (contScoreComponents M phi dphi L (eh (2*(n+1)) a) k (j-1) o -
            contScoreComponents M phi dphi L
              (continuousBandPropensityHybrid (eh (2*(n+1)) a) (trueNuisance M L))
              k (j-1) o) ∂observationLaw M)) atTop (fun _ _ => 0) := by
  apply encoded_continuous_band_joint_propensity_bias_root_n_negligible
    M μ phi dphi L eh
    (fun n a => continuousBandPropensityHybrid (eh n a) (trueNuisance M L))
    he0 heh (fun n a => continuous_band_propensity_hybrid_admissible M L _ _ (heh n a) he0)
    hr (encoded_continuous_band_propensity_hybrid_rates M μ L _ eh hr)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) k (j-1) (by omega)
    (fun n a => regularValue (eh n a).gamma k j) _ _ c hc hclip
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

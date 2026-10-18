module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousBandProductMean
public import StatLean.AsymptoticStatistics.ForMathlib.TendstoInMeasureAlgebra
/-! Joint regression remainders of the continuous band product score.
The common-gamma hybrid decomposition combines the assignment cross-error
with the regression and denominator cancellation at root-n scale. -/
public section
set_option linter.style.openClassical false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
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

-- @node: continuous_band_weighted_joint_regression_integrable
/-- Suppose [both nuisances are admissible](hyp:he,hb) and agree in [assignment
denominators](hyp:hpi), [treatment propensities](hyp:hp), [quantile
boundaries](hyp:hn), [instrument propensities](hyp:hprop), [shares](hyp:hshare),
and [level thresholds](hyp:htau). For [a measurable covariate weight](hyp:hw)
[bounded in absolute value by one almost everywhere](hyp:hwb), if [the clipping
constant is positive](hyp:hc) and [the second nuisance's assignment denominators
are almost everywhere at least that constant](hyp:hclip), then [the weighted
component-score difference is integrable under the observation law](goal). -/
lemma continuous_band_weighted_joint_regression_integrable
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X) (e b : NuisanceCont L)
    (he : ContAdmissible M L e) (hb : ContAdmissible M L b)
    (hpi : e.piLev = b.piLev) (hp : e.pLev = b.pLev) (hn : e.nu = b.nu)
    (hprop : e.prop = b.prop) (hshare : e.share = b.share) (htau : e.tauLev = b.tauLev)
    (k : Fin L.K) (j : ℕ) (w : X → ℝ) (hw : Measurable w)
    (hwb : ∀ᵐ x ∂xLaw M, |w x| ≤ 1)
    (c : ℝ) (hc : 0 < c) (hclip : ∀ i, ∀ᵐ x ∂xLaw M, c ≤ b.piLev i x) :
    Integrable (fun o : Obs X Z => w o.1 *
      (contScoreComponents M phi dphi L e k j o -
        contScoreComponents M phi dphi L b k j o)) (observationLaw M) := by
  let v := fun (s : Bool) x => w x *
    (if s then positiveValue b.pLev (k.val+1) x *
      (alphaHigh M L e k j x - alphaHigh M L b k j x)
    else if k.val = 0 then 0 else -positiveValue b.pLev k x *
      (alphaLow M L e k j x - alphaLow M L b k j x))
  have hv s : Measurable (v s) := by
    try fun_prop
    have hpp := (fitted_continuous_full_coordinates M L _ hb (k.val+1)).1.1
    have hpm := (fitted_continuous_full_coordinates M L _ hb k).1.1
    have hep := continuous_admissible_alphaHigh_measurable M L _ he k j
    have hbp := continuous_admissible_alphaHigh_measurable M L _ hb k j
    have hem := continuous_admissible_alphaLow_measurable M L _ he k j
    have hbm := continuous_admissible_alphaLow_measurable M L _ hb k j
    dsimp only [v]
    split_ifs
    · exact (hw).mul (hpp.mul (hep.sub hbp))
    · fun_prop
    · exact (hw).mul (hpm.neg.mul (hem.sub hbm))
  have hB s : ∀ᵐ x ∂xLaw M,
      ‖v s x‖ ≤ 10 * (|M.yMin| + |M.yMax|) := by
    have hp k := (fitted_continuous_full_coordinates M L _ hb k).1.2
    have he := continuous_admissible_alpha_abs_bounds M L _ he k j
    have hb := continuous_admissible_alpha_abs_bounds M L _ hb k j
    filter_upwards [hwb, hp (k.val+1), hp k.val, he.1, he.2, hb.1, hb.2]
      with x hx hpp hpm hep hem hbp hbm
    have hplus : |alphaHigh M L e k j x - alphaHigh M L b k j x| ≤
        10 * (|M.yMin| + |M.yMax|) := (abs_sub _ _).trans (by linarith)
    have hminus : |alphaLow M L e k j x - alphaLow M L b k j x| ≤
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
  have hpm i : Measurable (b.piLev i) := by
    first | fun_prop | exact hb.2.2.2.2.2.1 i
  exact (population_continuous_band_joint_regression_bias M phi dphi L e b
    hpi hp hn hprop hshare htau k j w (v true) (v false)
    (fun _ => rfl) (fun _ => rfl) hpm (hv true) (hv false)
    c (10 * (|M.yMin| + |M.yMax|)) (10 * (|M.yMin| + |M.yMax|))
    hc hclip (hB true) (hB false)).1

-- @node: continuous_band_product_joint_regression_integrable
/-- If [both nuisances are admissible](hyp:he,hb) and have the same [assignment
denominators](hyp:hpi), [treatment propensities](hyp:hp), [quantile
boundaries](hyp:hn), [instrument propensities](hyp:hprop), [shares](hyp:hshare),
[level thresholds](hyp:htau), and [assignment shares](hyp:hg), then, for [a band
index between one and the level's band count](hyp:hj), [a positive clipping
constant](hyp:hc), and [assignment denominators of the second nuisance bounded
below by that constant almost everywhere](hyp:hclip), [the product-score
difference is integrable under the observation law](goal). -/
lemma continuous_band_product_joint_regression_integrable
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X) (e b : NuisanceCont L)
    (he : ContAdmissible M L e) (hb : ContAdmissible M L b)
    (hpi : e.piLev = b.piLev) (hp : e.pLev = b.pLev) (hn : e.nu = b.nu)
    (hprop : e.prop = b.prop) (hshare : e.share = b.share) (htau : e.tauLev = b.tauLev)
    (hg : e.gamma = b.gamma) (k : Fin L.K) (j : ℕ) (hj : 1 ≤ j ∧ j ≤ L.l k)
    (c : ℝ) (hc : 0 < c) (hclip : ∀ i, ∀ᵐ x ∂xLaw M, c ≤ b.piLev i x) :
    Integrable (fun o : Obs X Z => psiProd M phi dphi L e k j o -
      psiProd M phi dphi L b k j o) (observationLaw M) := by
  have hi : Integrable (fun o : Obs X Z => regularValue e.gamma k j o.1 *
      (contScoreComponents M phi dphi L e k (j-1) o -
        contScoreComponents M phi dphi L b k (j-1) o)) (observationLaw M) := by
    apply continuous_band_weighted_joint_regression_integrable M phi dphi L
      e b he hb hpi hp hn
      hprop hshare htau k (j-1) _ _ _ c hc hclip
    · first | fun_prop | skip
      rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hm, _⟩
      change Measurable (fun x => regularValue e.gamma k j x)
      simpa only [regularValue, dif_pos (show k.val ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k from
        ⟨by omega, hj⟩)] using hm ⟨(k,j),by omega,hj⟩
    · rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hb, _⟩
      filter_upwards [hb ⟨(k,j),by omega,hj⟩] with x hx
      simp only [regularValue, dif_pos (show k.val ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k from
        ⟨by omega, hj⟩)]
      rw [abs_of_nonneg hx.1]
      exact hx.2
  exact (continuous_band_product_fixed_gamma_difference_mean M phi dphi L e b
    he hb hg k j (by omega) hj hi).1

-- @node: encoded_continuous_band_product_joint_regression_root_n_negligible
/-- Suppose [truth is admissible](hyp:he0), [both fitted sequences are
admissible](hyp:heh,hbh), and [both have encoded little-o fourth-root rates
relative to truth](hyp:hre,hrb). If the fits agree in [assignment
denominators](hyp:hpi), [treatment propensities](hyp:hp), [quantile
boundaries](hyp:hn), [instrument propensities](hyp:hprop), [shares](hyp:hshare),
[level thresholds](hyp:htau), and [assignment shares](hyp:hg), [the band index
is between one and the level's band count](hyp:hj), [the clipping constant is
positive](hyp:hc), and [all second-sequence assignment denominators are bounded
below by it almost everywhere](hyp:hclip), then [the mean product-score
difference at fit size twice n plus two, multiplied by the square root of n
plus one, converges to zero in probability](goal). -/
lemma encoded_continuous_band_product_joint_regression_root_n_negligible
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
    (hp : ∀ n a, (eh n a).pLev = (bh n a).pLev)
    (hn : ∀ n a, (eh n a).nu = (bh n a).nu)
    (hprop : ∀ n a, (eh n a).prop = (bh n a).prop)
    (hshare : ∀ n a, (eh n a).share = (bh n a).share)
    (htau : ∀ n a, (eh n a).tauLev = (bh n a).tauLev)
    (hg : ∀ n a, (eh n a).gamma = (bh n a).gamma)
    (k : Fin L.K) (j : ℕ) (hj : 1 ≤ j ∧ j ≤ L.l k)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a i, ∀ᵐ x ∂xLaw M, c ≤ (bh n a).piLev i x) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
        ∫ o : Obs X Z, psiProd M phi dphi L (eh (2*(n+1)) a) k j o -
          psiProd M phi dphi L (bh (2*(n+1)) a) k j o ∂observationLaw M)
      atTop (fun _ _ => 0) := by
  have hreg := encoded_continuous_gamma_band_joint_regression_bias_root_n_negligible
    M μ phi dphi L eh bh he0 heh hbh hre hrb hpi hp hn hprop hshare htau k j c hc hclip
  have hcross := encoded_continuous_band_target_difference_cross_root_n_negligible
    M μ L eh bh he0 heh hbh hre hrb k j (by omega) hj
  have hsum := (show TendstoInMeasure μ _ atTop (fun _ => (0 : ℝ)) from hreg).add_zero
    (show TendstoInMeasure μ _ atTop (fun _ => (0 : ℝ)) from hcross)
  have hmean n a := continuous_band_product_fixed_gamma_difference_mean M phi dphi L
    (eh n a) (bh n a) (heh n a) (hbh n a) (hg n a) k j (by omega) hj
  have hi n a : Integrable (fun o : Obs X Z => regularValue (eh n a).gamma k j o.1 *
      (contScoreComponents M phi dphi L (eh n a) k (j-1) o -
        contScoreComponents M phi dphi L (bh n a) k (j-1) o)) (observationLaw M) := by
    apply continuous_band_weighted_joint_regression_integrable M phi dphi L
      (eh n a) (bh n a) (heh n a) (hbh n a) (hpi n a) (hp n a) (hn n a)
      (hprop n a) (hshare n a) (htau n a) k (j-1) _ _ _ c hc (hclip n a)
    · first | fun_prop | skip
      rcases heh n a with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hm, _⟩
      change Measurable (fun x => regularValue (eh n a).gamma k j x)
      simpa only [regularValue, dif_pos (show k.val ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k from
        ⟨by omega, hj⟩)] using hm ⟨(k,j),by omega,hj⟩
    · rcases heh n a with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hb, _⟩
      filter_upwards [hb ⟨(k,j),by omega,hj⟩] with x hx
      simp only [regularValue, dif_pos (show k.val ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k from
        ⟨by omega, hj⟩)]
      rw [abs_of_nonneg hx.1]
      exact hx.2
  change TendstoInMeasure μ _ atTop (fun _ => (0 : ℝ))
  convert hsum using 1
  funext n a
  rw [(hmean (2*(n+1)) a (hi _ a)).2, mul_add]

-- @node: encoded_continuous_band_product_joint_regression_block_root_n_negligible
/-- Assume [truth is admissible](hyp:he0), [both fitted sequences are
admissible](hyp:heh,hbh), and [both have encoded little-o fourth-root error
rates](hyp:hre,hrb), with common [assignment denominators](hyp:hpi), [treatment
propensities](hyp:hp), [quantile boundaries](hyp:hn), [instrument
propensities](hyp:hprop), [shares](hyp:hshare), [level thresholds](hyp:htau),
and [assignment shares](hyp:hg). If [every index in the finite block has band
number between one and its level's band count](hyp:hj), [the clipping constant
is positive](hyp:hc), and [all second-sequence assignment denominators exceed
or equal it almost everywhere](hyp:hclip), then [the mean sum of product-score
differences over the block, evaluated at fit size twice n plus two and scaled
by the square root of n plus one, converges to zero in probability](goal). -/
lemma encoded_continuous_band_product_joint_regression_block_root_n_negligible
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
    (hp : ∀ n a, (eh n a).pLev = (bh n a).pLev)
    (hn : ∀ n a, (eh n a).nu = (bh n a).nu)
    (hprop : ∀ n a, (eh n a).prop = (bh n a).prop)
    (hshare : ∀ n a, (eh n a).share = (bh n a).share)
    (htau : ∀ n a, (eh n a).tauLev = (bh n a).tauLev)
    (hg : ∀ n a, (eh n a).gamma = (bh n a).gamma)
    (t : Finset (Fin L.K × ℕ))
    (hj : ∀ i ∈ t, 1 ≤ i.2 ∧ i.2 ≤ L.l i.1)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a i, ∀ᵐ x ∂xLaw M, c ≤ (bh n a).piLev i x) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
        ∫ o : Obs X Z, ∑ i ∈ t,
          (psiProd M phi dphi L (eh (2*(n+1)) a) i.1 i.2 o -
            psiProd M phi dphi L (bh (2*(n+1)) a) i.1 i.2 o) ∂observationLaw M)
      atTop (fun _ _ => 0) := by
  let F := fun (i : Fin L.K × ℕ) n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
    ∫ o : Obs X Z, psiProd M phi dphi L (eh (2*(n+1)) a) i.1 i.2 o -
      psiProd M phi dphi L (bh (2*(n+1)) a) i.1 i.2 o ∂observationLaw M
  have hF (i : Fin L.K × ℕ) (hit : i ∈ t) :
      TendstoInMeasure μ (F i) atTop (fun _ => (0 : ℝ)) :=
    encoded_continuous_band_product_joint_regression_root_n_negligible
      M μ phi dphi L eh bh he0 heh hbh hre hrb hpi hp hn hprop hshare htau hg
      i.1 i.2 (hj i hit) c hc hclip
  have hs : TendstoInMeasure μ (fun n a => ∑ i ∈ t, F i n a)
      atTop (fun _ => (0 : ℝ)) := by
    induction t using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      intro eps heps
      simpa only [edist_self, not_le.mpr heps, Set.ofPred_false, measure_empty]
        using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (𝓝 0))
    | @insert i t hit ih =>
      have hi := hF i (Finset.mem_insert_self i t)
      have ht := ih (fun b hb => hj b (Finset.mem_insert_of_mem hb))
        (fun b hb => hF b (Finset.mem_insert_of_mem hb))
      simpa only [Finset.sum_insert hit] using hi.add_zero ht
  have hi n a i (hit : i ∈ t) := continuous_band_product_joint_regression_integrable
    M phi dphi L (eh n a) (bh n a) (heh n a) (hbh n a)
    (hpi n a) (hp n a) (hn n a) (hprop n a) (hshare n a) (htau n a) (hg n a)
    i.1 i.2 (hj i hit) c hc (hclip n a)
  change TendstoInMeasure μ _ atTop (fun _ => (0 : ℝ))
  convert hs using 1
  funext n a
  rw [integral_finsetSum t (fun i hit => hi (2*(n+1)) a i hit), Finset.mul_sum]

end Papers.TbsPrteOptimalTransport

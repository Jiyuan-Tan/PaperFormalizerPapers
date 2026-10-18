module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLFittedSuccessResidual
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationBinaryRegularProducts
/-! Exact fitted treatment residual means and quadratic DML score bias. -/
public section

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set
open scoped Classical

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- The population denominator cancels before expectations are taken.
-- @node: fitted_Rp_population_decomposition
/-- For [a level between one and the total number of levels](hyp:hk) whose
[true instrument mass at the observed covariates is nonzero](hyp:hpi), [the fitted
treatment residual equals the true residual times the true-to-fitted level-mass
ratio, plus the level-membership indicator times the true-minus-fitted level
propensity divided by the fitted level mass](goal). -/
lemma fitted_Rp_population_decomposition (L : LevelData Z X) (e : NuisanceBin L)
    (k : ℕ) (hk : 1 ≤ k ∧ k ≤ L.K) (o : Obs X Z)
    (hpi : (levelSetProb M L).1 k o.1 ≠ 0) :
    Rp L e k o =
      ((levelSetProb M L).1 k o.1 / positiveValue e.piLev k o.1) *
        Rp L (eta0Bin M L) k o +
      indicator (o.2.1 ∈ L.S k) *
        ((L.pLev k o.1 - positiveValue e.pLev k o.1) /
          positiveValue e.piLev k o.1) := by
  have hk0 : k ≠ 0 := by omega
  simp only [Rp, if_neg hk0, positiveValue, dif_pos hk, eta0Bin]
  simp only [div_eq_mul_inv]
  field_simp
  <;> ring

-- The structural conditional treatment mean centers the population term;
-- instrument-event averaging identifies the remaining regression error.
-- @node: fitted_Rp_weighted_integral
/-- Under [threshold crossing](hyp:h) and [invariant baseline and policy level
ordering](hyp:hOrder), take [a valid positive level](hyp:hk) and a [measurable
covariate weight](hyp:hw). If [the fitted level mass](hyp:hq), [fitted level
propensity](hyp:hP), and [true level propensity](hyp:hP0) are measurable,
[the true level mass is almost surely nonzero](hyp:hpi), and both [the weighted,
mass-ratio-scaled true residual](hyp:hpop) and [the weighted level-membership
propensity correction](hyp:hsel) are integrable, then [the weighted fitted
residual is integrable and its mean equals the covariate average of the weight
times the true-to-fitted level-mass ratio times the true-minus-fitted level
propensity](goal). -/
lemma fitted_Rp_weighted_integral (h : ThresholdCrossing M)
    (q : Z → X → ℝ) (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop q L) (e : NuisanceBin L)
    (k : ℕ) (hk : 1 ≤ k ∧ k ≤ L.K) (w : X → ℝ)
    (hw : Measurable w) (hq : Measurable (positiveValue e.piLev k))
    (hP : Measurable (positiveValue e.pLev k))
    (hP0 : Measurable (L.pLev k))
    (hpi : ∀ᵐ o : Obs X Z ∂observationLaw M, (levelSetProb M L).1 k o.1 ≠ 0)
    (hpop : Integrable (fun o : Obs X Z =>
      (w o.1 * ((levelSetProb M L).1 k o.1 / positiveValue e.piLev k o.1)) *
        Rp L (eta0Bin M L) k o) (observationLaw M))
    (hsel : Integrable (fun o : Obs X Z =>
      (w o.1 * ((L.pLev k o.1 - positiveValue e.pLev k o.1) /
        positiveValue e.piLev k o.1)) * indicator (o.2.1 ∈ L.S k))
      (observationLaw M)) :
    Integrable (fun o : Obs X Z => w o.1 * Rp L e k o) (observationLaw M) ∧
    (∫ o : Obs X Z, w o.1 * Rp L e k o ∂observationLaw M) =
      ∫ x, w x * ((levelSetProb M L).1 k x / positiveValue e.piLev k x) *
        (L.pLev k x - positiveValue e.pLev k x) ∂xLaw M := by
  have hprob : Measurable (fun x => (levelSetProb M L).1 k x) := by
    first | fun_prop | skip
    exact Finset.measurable_sum _ (fun z _ =>
      (Kernel.measurable_coe _ (measurableSet_singleton z)).ennreal_toReal)
  have hz := population_Rp_weighted_integral_zero M h q L hOrder k
    (fun x => w x * ((levelSetProb M L).1 k x / positiveValue e.piLev k x))
    (by fun_prop) hpop
  have hid : (fun o : Obs X Z => w o.1 * Rp L e k o) =ᵐ[observationLaw M]
      (fun o => (w o.1 * ((levelSetProb M L).1 k o.1 / positiveValue e.piLev k o.1)) *
        Rp L (eta0Bin M L) k o +
      (w o.1 * ((L.pLev k o.1 - positiveValue e.pLev k o.1) /
        positiveValue e.piLev k o.1)) * indicator (o.2.1 ∈ L.S k)) := by
    filter_upwards [hpi] with o ho
    rw [fitted_Rp_population_decomposition M L e k hk o ho]
    ring
  let f : Z × X → ℝ := fun zx =>
    (w zx.2 * ((L.pLev k zx.2 - positiveValue e.pLev k zx.2) /
      positiveValue e.piLev k zx.2)) * indicator (zx.1 ∈ L.S k)
  have hf : Measurable f := by fun_prop
  have hm := population_instrument_integral M f hf hsel
  have hsum : ∀ x, (∑ z, instProb M z x * f (z, x)) =
      w x * ((levelSetProb M L).1 k x / positiveValue e.piLev k x) *
        (L.pLev k x - positiveValue e.pLev k x) := by
    intro x
    simp only [f, indicator, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.sum_mul]
    change (levelSetProb M L).1 k x * _ = _
    ring
  refine ⟨(hpop.fun_add hsel).congr hid.symm, ?_⟩
  rw [integral_congr_ae hid, integral_add hpop hsel, hz, zero_add]
  simpa only [hsum, f] using hm

-- Clipping and overlap discharge the analytic premises of the exact mean.
-- @node: fitted_Rp_weighted_integral_of_clipping
/-- For [a valid positive level](hyp:hk), assume [baseline overlap](hyp:hov),
[a positive clipping constant](hyp:hc), [a nonnegative weight bound](hyp:hW),
[threshold crossing](hyp:h), [invariant baseline and policy level ordering](hyp:hOrder),
and admissibility of [the true nuisances](hyp:he0) and [the fitted nuisances](hyp:he).
If [the fitted level mass is almost surely at least the clipping constant](hyp:hclip)
and the weight is [measurable](hyp:hw) and [almost surely bounded in absolute
value by the weight bound](hyp:hb), then [the weighted fitted treatment residual
is integrable and its mean equals the covariate average of the weight times the
true-to-fitted level-mass ratio times the true-minus-fitted level propensity](goal). -/
lemma fitted_Rp_weighted_integral_of_clipping (L : LevelData Z X) (e : NuisanceBin L)
    (k : ℕ) (hk : 1 ≤ k ∧ k ≤ L.K) (cpi c W : ℝ)
    (hov : BaselineOverlapWitness M L cpi) (hc : 0 < c) (hW : 0 ≤ W)
    (h : ThresholdCrossing M) (q : Z → X → ℝ)
    (hOrder : LevelOrderInvariant M.prop q L)
    (he0 : BinAdmissible M L (eta0Bin M L))
    (he : BinAdmissible M L e)
    (hclip : ∀ᵐ x ∂xLaw M, c ≤ positiveValue e.piLev k x)
    (w : X → ℝ) (hw : Measurable w) (hb : ∀ᵐ x ∂xLaw M, ‖w x‖ ≤ W) :
    Integrable (fun o : Obs X Z => w o.1 * Rp L e k o) (observationLaw M) ∧
    (∫ o : Obs X Z, w o.1 * Rp L e k o ∂observationLaw M) =
      ∫ x, w x * ((levelSetProb M L).1 k x / positiveValue e.piLev k x) *
        (L.pLev k x - positiveValue e.pLev k x) ∂xLaw M := by
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  have hlev : Measurable (L.pLev k) := by
    first | fun_prop | exact (he0.2.2.2.1 ⟨k, hk⟩).1
  have hq : Measurable (positiveValue e.piLev k) := by
    first | fun_prop | skip
    change Measurable (fun x => positiveValue e.piLev k x)
    simpa only [positiveValue, dif_pos hk] using (he.2.2.2.1 ⟨k, hk⟩).2.2
  have hP : Measurable (positiveValue e.pLev k) := by
    first | fun_prop | skip
    change Measurable (fun x => positiveValue e.pLev k x)
    simpa only [positiveValue, dif_pos hk] using (he.2.2.2.1 ⟨k, hk⟩).1
  have hprob : Measurable (fun x => (levelSetProb M L).1 k x) := by
    first | fun_prop | skip
    exact Finset.measurable_sum _ (fun z _ =>
      (Kernel.measurable_coe _ (measurableSet_singleton z)).ennreal_toReal)
  have hratio : ∀ᵐ x ∂xLaw M,
      ‖w x * ((levelSetProb M L).1 k x / positiveValue e.piLev k x)‖ ≤ W / c := by
    filter_upwards [hb, hclip, he0.2.2.1 ⟨k, hk⟩] with x hx hcx h0x
    have hp : (levelSetProb M L).1 k x ∈ Icc (0 : ℝ) 1 := h0x.2.2
    have hqx : 0 < positiveValue e.piLev k x := hc.trans_le hcx
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_nonneg hp.1, abs_of_pos hqx]
    have hwx : |w x| ≤ W := by simpa only [Real.norm_eq_abs] using hx
    calc
      _ ≤ W * (1 / positiveValue e.piLev k x) := by
        exact mul_le_mul hwx (div_le_div_of_nonneg_right hp.2 hqx.le)
          (div_nonneg hp.1 hqx.le) hW
      _ = W / positiveValue e.piLev k x := by ring
      _ ≤ W / c := div_le_div_of_nonneg_left hW hc hcx
  have hpop := population_binary_weighted_Rp_integrable M L cpi hov he0 k
    (fun x => w x * ((levelSetProb M L).1 k x / positiveValue e.piLev k x))
    (by fun_prop) (W / c) hratio
  have hsel : Integrable (fun o : Obs X Z =>
      (w o.1 * ((L.pLev k o.1 - positiveValue e.pLev k o.1) /
        positiveValue e.piLev k o.1)) * indicator (o.2.1 ∈ L.S k))
      (observationLaw M) := by
    have hi : Measurable (fun o : Obs X Z => indicator (o.2.1 ∈ L.S k)) := by fun_prop
    apply Integrable.of_bound (by fun_prop) (W * (2 / c))
    filter_upwards [observationLaw_covariate_ae M _ hb,
      observationLaw_covariate_ae M _ hclip,
      observationLaw_covariate_ae M _ (he0.2.2.1 ⟨k, hk⟩),
      observationLaw_covariate_ae M _ (he.2.2.1 ⟨k, hk⟩)] with o ho hcq h0 h1
    have hp0 : L.pLev k o.1 ∈ Icc (0 : ℝ) 1 := h0.1
    have hp1 : positiveValue e.pLev k o.1 ∈ Icc (0 : ℝ) 1 := by
      simpa only [positiveValue, dif_pos hk] using h1.1
    have hd : |L.pLev k o.1 - positiveValue e.pLev k o.1| ≤ 2 := by
      rw [abs_le]
      constructor <;> linarith [hp0.1, hp0.2, hp1.1, hp1.2]
    have ha : |indicator (o.2.1 ∈ L.S k)| ≤ 1 := by
      first | fun_prop | skip
      unfold indicator
      split_ifs <;> norm_num
    have hq0 : 0 < positiveValue e.piLev k o.1 := hc.trans_le hcq
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_div, abs_of_pos hq0]
    calc
      _ ≤ W * (2 / positiveValue e.piLev k o.1) * 1 := by
        gcongr
        simpa only [Real.norm_eq_abs] using ho
      _ ≤ W * (2 / c) := by
        rw [mul_one]
        gcongr
  exact fitted_Rp_weighted_integral M h q L hOrder e k hk w hw hq hP hlev
    (Filter.Eventually.of_forall fun o =>
      (hov.1.trans_le (hov.2 o.1 k hk.1 hk.2)).ne') hpop hsel

-- Adding the fitted regression to its residual cancels the first-order
-- regression error. This is a score identity, not a plug-in target bound.
-- @node: fitted_treatment_score_exact_bias
/-- At [a valid positive level](hyp:hk), assume [baseline overlap](hyp:hov),
[a positive clipping constant](hyp:hc), [a nonnegative weight bound](hyp:hW),
[threshold crossing](hyp:h), [invariant baseline and policy level ordering](hyp:hOrder),
and admissible [true](hyp:he0) and [fitted](hyp:he) nuisances. For [an almost surely
clipped fitted level mass](hyp:hclip) and a [measurable weight](hyp:hw)
[almost surely bounded by the weight bound](hyp:hb), [the mean weighted fitted
treatment score minus the weighted true level propensity equals the covariate
average of the weight times one minus the true-to-fitted level-mass ratio times
the fitted-minus-true level propensity](goal). -/
lemma fitted_treatment_score_exact_bias (L : LevelData Z X) (e : NuisanceBin L)
    (k : ℕ) (hk : 1 ≤ k ∧ k ≤ L.K) (cpi c W : ℝ)
    (hov : BaselineOverlapWitness M L cpi) (hc : 0 < c) (hW : 0 ≤ W)
    (h : ThresholdCrossing M) (q : Z → X → ℝ)
    (hOrder : LevelOrderInvariant M.prop q L)
    (he0 : BinAdmissible M L (eta0Bin M L))
    (he : BinAdmissible M L e)
    (hclip : ∀ᵐ x ∂xLaw M, c ≤ positiveValue e.piLev k x)
    (w : X → ℝ) (hw : Measurable w) (hb : ∀ᵐ x ∂xLaw M, ‖w x‖ ≤ W) :
    (∫ o : Obs X Z, w o.1 * (positiveValue e.pLev k o.1 + Rp L e k o)
      ∂observationLaw M) - (∫ x, w x * L.pLev k x ∂xLaw M) =
      ∫ x, w x * (1 - (levelSetProb M L).1 k x / positiveValue e.piLev k x) *
        (positiveValue e.pLev k x - L.pLev k x) ∂xLaw M := by
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  have hlev : Measurable (L.pLev k) := by
    first | fun_prop | exact (he0.2.2.2.1 ⟨k, hk⟩).1
  have hq : Measurable (positiveValue e.piLev k) := by
    first | fun_prop | skip
    change Measurable (fun x => positiveValue e.piLev k x)
    simpa only [positiveValue, dif_pos hk] using (he.2.2.2.1 ⟨k, hk⟩).2.2
  have hP : Measurable (positiveValue e.pLev k) := by
    first | fun_prop | skip
    change Measurable (fun x => positiveValue e.pLev k x)
    simpa only [positiveValue, dif_pos hk] using (he.2.2.2.1 ⟨k, hk⟩).1
  have hprob : Measurable (fun x => (levelSetProb M L).1 k x) := by
    first | fun_prop | skip
    exact Finset.measurable_sum _ (fun z _ =>
      (Kernel.measurable_coe _ (measurableSet_singleton z)).ennreal_toReal)
  have hP0 := hlev
  have iP : Integrable (fun x => w x * positiveValue e.pLev k x) (xLaw M) := by
    apply Integrable.of_bound (by fun_prop) W
    filter_upwards [hb, he.2.2.1 ⟨k, hk⟩] with x hx heX
    have hp : positiveValue e.pLev k x ∈ Icc (0 : ℝ) 1 := by
      simpa only [positiveValue, dif_pos hk] using heX.1
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hp.1]
    exact (mul_le_mul_of_nonneg_right (by simpa only [Real.norm_eq_abs] using hx) hp.1).trans
      (mul_le_of_le_one_right hW hp.2)
  have iP0 : Integrable (fun x => w x * L.pLev k x) (xLaw M) := by
    apply Integrable.of_bound (by fun_prop) W
    filter_upwards [hb, he0.2.2.1 ⟨k, hk⟩] with x hx heX
    have hp : L.pLev k x ∈ Icc (0 : ℝ) 1 := heX.1
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hp.1]
    exact (mul_le_mul_of_nonneg_right (by simpa only [Real.norm_eq_abs] using hx) hp.1).trans
      (mul_le_of_le_one_right hW hp.2)
  have irec : Integrable (fun x =>
      ((positiveValue e.piLev k x)⁻¹ * (levelSetProb M L).1 k x) *
        (w x * L.pLev k x - w x * positiveValue e.pLev k x)) (xLaw M) := by
    apply Integrable.bdd_mul (iP0.sub' iP)
      (by fun_prop : AEStronglyMeasurable
        (fun x => (positiveValue e.piLev k x)⁻¹ * (levelSetProb M L).1 k x) (xLaw M))
      (c := 1 / c)
    filter_upwards [hclip, he0.2.2.1 ⟨k, hk⟩] with x hx heX
    have hp : (levelSetProb M L).1 k x ∈ Icc (0 : ℝ) 1 := heX.2.2
    have hqx : 0 < positiveValue e.piLev k x := hc.trans_le hx
    rw [Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos hqx, abs_of_nonneg hp.1]
    calc
      _ ≤ (positiveValue e.piLev k x)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left hp.2 (inv_nonneg.mpr hqx.le)
      _ ≤ 1 / c := by
        rw [mul_one, ← one_div]
        exact div_le_div_of_nonneg_left (by norm_num) hc hx
  have ir : Integrable (fun x => w x *
      ((levelSetProb M L).1 k x / positiveValue e.piLev k x) *
        (L.pLev k x - positiveValue e.pLev k x)) (xLaw M) := by
    convert irec using 1
    ext x
    simp only [div_eq_mul_inv]
    ring
  have hobs := M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY))
  have hmap : (observationLaw M).map Prod.fst = xLaw M := by
    simpa only [observationLaw, xLaw, Function.comp_def] using
      Measure.map_map measurable_fst hobs
  have iPo : Integrable (fun o : Obs X Z => w o.1 * positiveValue e.pLev k o.1)
      (observationLaw M) := by
    rw [← hmap] at iP
    exact (integrable_map_measure (hw.mul hP).aestronglyMeasurable
      measurable_fst.aemeasurable).mp iP
  have hPo : (∫ o : Obs X Z, w o.1 * positiveValue e.pLev k o.1 ∂observationLaw M) =
      ∫ x, w x * positiveValue e.pLev k x ∂xLaw M := by
    rw [← hmap]
    exact (integral_map measurable_fst.aemeasurable
      (hw.mul hP).aestronglyMeasurable).symm
  obtain ⟨iRP, hRP⟩ := fitted_Rp_weighted_integral_of_clipping M L e k hk cpi c W
    hov hc hW h q hOrder he0 he hclip w hw hb
  simp_rw [mul_add]
  rw [integral_add iPo iRP, hPo, hRP, ← integral_add iP ir,
    ← integral_sub (iP.fun_add ir) iP0]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

-- @node: fitted_treatment_score_bias_L2_bound
/-- At [a valid positive level](hyp:hk), assume [baseline overlap](hyp:hov),
[a positive clipping constant](hyp:hc), [a nonnegative weight bound](hyp:hW),
[threshold crossing](hyp:h), [invariant baseline and policy level ordering](hyp:hOrder),
and admissible [true](hyp:he0) and [fitted](hyp:he) nuisances. If [the fitted level
mass is almost surely at least the clipping constant](hyp:hclip), the weight is
[measurable](hyp:hw) and [almost surely bounded by the weight bound](hyp:hb), and
the errors in [level mass](hyp:heP) and [level propensity](hyp:heR) are square
integrable, then [the absolute weighted treatment-score bias is at most the weight
bound times the product of those two L2 errors divided by the clipping constant](goal). -/
lemma fitted_treatment_score_bias_L2_bound (L : LevelData Z X) (e : NuisanceBin L)
    (k : ℕ) (hk : 1 ≤ k ∧ k ≤ L.K) (cpi c W : ℝ)
    (hov : BaselineOverlapWitness M L cpi) (hc : 0 < c) (hW : 0 ≤ W)
    (h : ThresholdCrossing M) (q : Z → X → ℝ)
    (hOrder : LevelOrderInvariant M.prop q L)
    (he0 : BinAdmissible M L (eta0Bin M L))
    (he : BinAdmissible M L e)
    (hclip : ∀ᵐ x ∂xLaw M, c ≤ positiveValue e.piLev k x)
    (w : X → ℝ) (hw : Measurable w) (hb : ∀ᵐ x ∂xLaw M, ‖w x‖ ≤ W)
    (heP : MemLp (fun x => positiveValue e.piLev k x - (levelSetProb M L).1 k x) 2 (xLaw M))
    (heR : MemLp (fun x => positiveValue e.pLev k x - L.pLev k x) 2 (xLaw M)) :
    |(∫ o : Obs X Z, w o.1 * (positiveValue e.pLev k o.1 + Rp L e k o)
      ∂observationLaw M) - (∫ x, w x * L.pLev k x ∂xLaw M)| ≤
      W * ((eLpNorm (fun x => positiveValue e.piLev k x - (levelSetProb M L).1 k x)
        2 (xLaw M)).toReal *
        (eLpNorm (fun x => positiveValue e.pLev k x - L.pLev k x)
          2 (xLaw M)).toReal / c) := by
  rw [fitted_treatment_score_exact_bias M L e k hk cpi c W
    hov hc hW h q hOrder he0 he hclip w hw hb]
  have hq : Measurable (positiveValue e.piLev k) := by
    first | fun_prop | skip
    change Measurable (fun x => positiveValue e.piLev k x)
    simpa only [positiveValue, dif_pos hk] using (he.2.2.2.1 ⟨k, hk⟩).2.2
  have hp : Measurable (fun x => (levelSetProb M L).1 k x) := by
    first | fun_prop | skip
    exact Finset.measurable_sum _ (fun z _ =>
      (Kernel.measurable_coe _ (measurableSet_singleton z)).ennreal_toReal)
  exact (weighted_clipped_assignment_regression_L2_bound (xLaw M) w _ _ _ c W
    hc hW hw hp hq hclip hb heP heR).2

end Papers.TbsPrteOptimalTransport

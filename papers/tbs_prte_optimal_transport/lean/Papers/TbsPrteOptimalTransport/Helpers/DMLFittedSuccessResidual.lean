module
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationInstrumentMoments
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationBinaryRegularity
public import Papers.TbsPrteOptimalTransport.Helpers.IPWRegressionRemainder
/-! Exact fitted treated-success residual means for the binary DML expansion.
Population residual centering and instrument-event averaging identify the
regression error multiplied by the true-to-fitted assignment ratio. -/
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
-- @node: fitted_RP_population_decomposition
/-- If [the index is a positive level within the level count](hyp:hk) and
[the true baseline-set probability is nonzero at the observed covariate](hyp:hpi),
[the fitted success residual equals the true residual times the true-to-fitted assignment
probability ratio, plus the baseline-set indicator times the true-minus-fitted success
probability divided by the fitted assignment probability](goal). -/
lemma fitted_RP_population_decomposition (L : LevelData Z X) (e : NuisanceBin L)
    (k : ℕ) (hk : 1 ≤ k ∧ k ≤ L.K) (o : Obs X Z)
    (hpi : (levelSetProb M L).1 k o.1 ≠ 0) :
    RP L e k o =
      ((levelSetProb M L).1 k o.1 / positiveValue e.piLev k o.1) *
        RP L (eta0Bin M L) k o +
      indicator (o.2.1 ∈ L.S k) *
        ((treatedSuccess M L k o.1 - positiveValue e.P1 k o.1) /
          positiveValue e.piLev k o.1) := by
  have hk0 : k ≠ 0 := by omega
  simp only [RP, if_neg hk0, positiveValue, dif_pos hk, eta0Bin]
  simp only [div_eq_mul_inv]
  field_simp
  <;> ring

-- No conditional score moment is assumed: the first term centers by the
-- defining selected outcome law, and the second uses the instrument kernel.
-- @node: fitted_RP_weighted_integral
/-- Suppose [the index is a positive level within the level count](hyp:hk),
[the weight is measurable](hyp:hw),
[the fitted assignment and success probabilities are measurable](hyp:hq,hP), and
[the true baseline-set probability is nonzero almost surely under the observation law](hyp:hpi).
If [the weighted true residual scaled by the true-to-fitted assignment ratio is integrable](hyp:hpop)
and [the baseline-set indicator times the weighted true-minus-fitted success probability
divided by fitted assignment probability is integrable](hyp:hsel),
[the weighted fitted success residual is integrable and its mean equals the covariate mean
of the weight times the true-to-fitted assignment ratio times the true-minus-fitted success
probability](goal). -/
lemma fitted_RP_weighted_integral (L : LevelData Z X) (e : NuisanceBin L)
    (k : ℕ) (hk : 1 ≤ k ∧ k ≤ L.K) (w : X → ℝ)
    (hw : Measurable w) (hq : Measurable (positiveValue e.piLev k))
    (hP : Measurable (positiveValue e.P1 k))
    (hpi : ∀ᵐ o : Obs X Z ∂observationLaw M, (levelSetProb M L).1 k o.1 ≠ 0)
    (hpop : Integrable (fun o : Obs X Z =>
      (w o.1 * ((levelSetProb M L).1 k o.1 / positiveValue e.piLev k o.1)) *
        RP L (eta0Bin M L) k o) (observationLaw M))
    (hsel : Integrable (fun o : Obs X Z =>
      (w o.1 * ((treatedSuccess M L k o.1 - positiveValue e.P1 k o.1) /
        positiveValue e.piLev k o.1)) * indicator (o.2.1 ∈ L.S k))
      (observationLaw M)) :
    Integrable (fun o : Obs X Z => w o.1 * RP L e k o) (observationLaw M) ∧
    (∫ o : Obs X Z, w o.1 * RP L e k o ∂observationLaw M) =
      ∫ x, w x * ((levelSetProb M L).1 k x / positiveValue e.piLev k x) *
        (treatedSuccess M L k x - positiveValue e.P1 k x) ∂xLaw M := by
  have hprob : Measurable (fun x => (levelSetProb M L).1 k x) := by
    exact Finset.measurable_sum _ (fun z _ =>
      (Kernel.measurable_coe _ (measurableSet_singleton z)).ennreal_toReal)
  have hz := population_RP_weighted_integral_zero M L k
    (fun x => w x * ((levelSetProb M L).1 k x / positiveValue e.piLev k x))
    (by fun_prop) hpop
  have hid : (fun o : Obs X Z => w o.1 * RP L e k o) =ᵐ[observationLaw M]
      (fun o => (w o.1 * ((levelSetProb M L).1 k o.1 / positiveValue e.piLev k o.1)) *
        RP L (eta0Bin M L) k o +
      (w o.1 * ((treatedSuccess M L k o.1 - positiveValue e.P1 k o.1) /
        positiveValue e.piLev k o.1)) * indicator (o.2.1 ∈ L.S k)) := by
    filter_upwards [hpi] with o ho
    rw [fitted_RP_population_decomposition M L e k hk o ho]
    ring
  let f : Z × X → ℝ := fun zx =>
    (w zx.2 * ((treatedSuccess M L k zx.2 - positiveValue e.P1 k zx.2) /
      positiveValue e.piLev k zx.2)) * indicator (zx.1 ∈ L.S k)
  have hf : Measurable f := by
    dsimp only [f]
    have hi : Measurable (fun zx : Z × X => indicator (zx.1 ∈ L.S k)) := by
      unfold indicator
      exact Measurable.ite ((L.S k).finite_toSet.measurableSet.preimage measurable_fst)
        measurable_const measurable_const
    fun_prop
  have hm := population_instrument_integral M f hf hsel
  have hsum : ∀ x, (∑ z, instProb M z x * f (z, x)) =
      w x * ((levelSetProb M L).1 k x / positiveValue e.piLev k x) *
        (treatedSuccess M L k x - positiveValue e.P1 k x) := by
    intro x
    simp only [f, indicator, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.sum_mul]
    change (levelSetProb M L).1 k x * _ = _
    ring
  refine ⟨(hpop.fun_add hsel).congr hid.symm, ?_⟩
  rw [integral_congr_ae hid, integral_add hpop hsel, hz, zero_add]
  simpa only [hsum, f] using hm

-- Clipping and overlap discharge the analytic premises of the exact mean.
-- @node: fitted_RP_weighted_integral_of_clipping
/-- Suppose [the index is a positive level within the level count](hyp:hk),
[baseline overlap holds](hyp:hov), [the clipping threshold is positive](hyp:hc),
[the weight bound is nonnegative](hyp:hW), [the outcome is binary almost surely](hyp:hy), and
[the true and fitted binary nuisance records are admissible](hyp:he0,he).
If [the fitted assignment probability is almost surely at least the clipping threshold](hyp:hclip),
[the weight is measurable](hyp:hw), and [its absolute value is almost surely at most the
weight bound](hyp:hb), [the weighted fitted success residual is integrable and its mean equals
the covariate mean of the weight times the true-to-fitted assignment ratio times the
true-minus-fitted success probability](goal). -/
lemma fitted_RP_weighted_integral_of_clipping (L : LevelData Z X) (e : NuisanceBin L)
    (k : ℕ) (hk : 1 ≤ k ∧ k ≤ L.K) (cpi c W : ℝ)
    (hov : BaselineOverlapWitness M L cpi) (hc : 0 < c) (hW : 0 ≤ W)
    (hy : OutcomeBinaryAE M) (he0 : BinAdmissible M L (eta0Bin M L))
    (he : BinAdmissible M L e)
    (hclip : ∀ᵐ x ∂xLaw M, c ≤ positiveValue e.piLev k x)
    (w : X → ℝ) (hw : Measurable w) (hb : ∀ᵐ x ∂xLaw M, ‖w x‖ ≤ W) :
    Integrable (fun o : Obs X Z => w o.1 * RP L e k o) (observationLaw M) ∧
    (∫ o : Obs X Z, w o.1 * RP L e k o ∂observationLaw M) =
      ∫ x, w x * ((levelSetProb M L).1 k x / positiveValue e.piLev k x) *
        (treatedSuccess M L k x - positiveValue e.P1 k x) ∂xLaw M := by
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  have hq : Measurable (positiveValue e.piLev k) := by
    change Measurable (fun x => positiveValue e.piLev k x)
    simpa only [positiveValue, dif_pos hk] using (he.2.2.2.1 ⟨k, hk⟩).2.2
  have hP : Measurable (positiveValue e.P1 k) := by
    change Measurable (fun x => positiveValue e.P1 k x)
    simpa only [positiveValue, dif_pos hk] using (he.2.2.2.1 ⟨k, hk⟩).2.1
  have hprob : Measurable (fun x => (levelSetProb M L).1 k x) := by
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
  have hpop := population_binary_weighted_RP_integrable M L cpi hov hy he0 k
    (fun x => w x * ((levelSetProb M L).1 k x / positiveValue e.piLev k x))
    (by fun_prop) (W / c) hratio
  have hsel : Integrable (fun o : Obs X Z =>
      (w o.1 * ((treatedSuccess M L k o.1 - positiveValue e.P1 k o.1) /
        positiveValue e.piLev k o.1)) * indicator (o.2.1 ∈ L.S k))
      (observationLaw M) := by
    have hi : Measurable (fun o : Obs X Z => indicator (o.2.1 ∈ L.S k)) := by
      unfold indicator
      exact Measurable.ite ((L.S k).finite_toSet.measurableSet.preimage
        (measurable_fst.comp measurable_snd)) measurable_const measurable_const
    apply Integrable.of_bound (by fun_prop) (W * (2 / c))
    filter_upwards [observationLaw_covariate_ae M _ hb,
      observationLaw_covariate_ae M _ hclip,
      observationLaw_covariate_ae M _ (he0.2.2.1 ⟨k, hk⟩),
      observationLaw_covariate_ae M _ (he.2.2.1 ⟨k, hk⟩)] with o ho hcq h0 h1
    have hp0 : treatedSuccess M L k o.1 ∈ Icc (0 : ℝ) 1 := h0.2.1
    have hp1 : positiveValue e.P1 k o.1 ∈ Icc (0 : ℝ) 1 := by
      simpa only [positiveValue, dif_pos hk] using h1.2.1
    have hd : |treatedSuccess M L k o.1 - positiveValue e.P1 k o.1| ≤ 2 := by
      rw [abs_le]
      constructor <;> linarith [hp0.1, hp0.2, hp1.1, hp1.2]
    have ha : |indicator (o.2.1 ∈ L.S k)| ≤ 1 := by
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
  exact fitted_RP_weighted_integral M L e k hk w hw hq hP
    (Filter.Eventually.of_forall fun o =>
      (hov.1.trans_le (hov.2 o.1 k hk.1 hk.2)).ne') hpop hsel

-- Adding the fitted regression to its residual cancels the first-order
-- regression error. This is a score identity, not a plug-in target bound.
-- @node: fitted_success_score_exact_bias
/-- Suppose [the index is a positive level within the level count](hyp:hk),
[baseline overlap holds](hyp:hov), [the clipping threshold is positive](hyp:hc),
[the weight bound is nonnegative](hyp:hW), [the outcome is binary almost surely](hyp:hy), and
[the true and fitted binary nuisance records are admissible](hyp:he0,he).
If [the fitted assignment probability is almost surely at least the clipping threshold](hyp:hclip),
[the weight is measurable](hyp:hw), and [its absolute value is almost surely at most the
weight bound](hyp:hb), [the bias of the weighted augmented success score equals the covariate
mean of the weight times one minus the true-to-fitted assignment probability ratio times the
fitted-minus-true success probability](goal). -/
lemma fitted_success_score_exact_bias (L : LevelData Z X) (e : NuisanceBin L)
    (k : ℕ) (hk : 1 ≤ k ∧ k ≤ L.K) (cpi c W : ℝ)
    (hov : BaselineOverlapWitness M L cpi) (hc : 0 < c) (hW : 0 ≤ W)
    (hy : OutcomeBinaryAE M) (he0 : BinAdmissible M L (eta0Bin M L))
    (he : BinAdmissible M L e)
    (hclip : ∀ᵐ x ∂xLaw M, c ≤ positiveValue e.piLev k x)
    (w : X → ℝ) (hw : Measurable w) (hb : ∀ᵐ x ∂xLaw M, ‖w x‖ ≤ W) :
    (∫ o : Obs X Z, w o.1 * (positiveValue e.P1 k o.1 + RP L e k o)
      ∂observationLaw M) - (∫ x, w x * treatedSuccess M L k x ∂xLaw M) =
      ∫ x, w x * (1 - (levelSetProb M L).1 k x / positiveValue e.piLev k x) *
        (positiveValue e.P1 k x - treatedSuccess M L k x) ∂xLaw M := by
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  have hq : Measurable (positiveValue e.piLev k) := by
    change Measurable (fun x => positiveValue e.piLev k x)
    simpa only [positiveValue, dif_pos hk] using (he.2.2.2.1 ⟨k, hk⟩).2.2
  have hP : Measurable (positiveValue e.P1 k) := by
    change Measurable (fun x => positiveValue e.P1 k x)
    simpa only [positiveValue, dif_pos hk] using (he.2.2.2.1 ⟨k, hk⟩).2.1
  have hprob : Measurable (fun x => (levelSetProb M L).1 k x) := by
    exact Finset.measurable_sum _ (fun z _ =>
      (Kernel.measurable_coe _ (measurableSet_singleton z)).ennreal_toReal)
  have hP0 := treatedSuccess_measurable M L k
  have iP : Integrable (fun x => w x * positiveValue e.P1 k x) (xLaw M) := by
    apply Integrable.of_bound (by fun_prop) W
    filter_upwards [hb, he.2.2.1 ⟨k, hk⟩] with x hx heX
    have hp : positiveValue e.P1 k x ∈ Icc (0 : ℝ) 1 := by
      simpa only [positiveValue, dif_pos hk] using heX.2.1
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hp.1]
    exact (mul_le_mul_of_nonneg_right (by simpa only [Real.norm_eq_abs] using hx) hp.1).trans
      (mul_le_of_le_one_right hW hp.2)
  have iP0 : Integrable (fun x => w x * treatedSuccess M L k x) (xLaw M) := by
    apply Integrable.of_bound (by fun_prop) W
    filter_upwards [hb, he0.2.2.1 ⟨k, hk⟩] with x hx heX
    have hp : treatedSuccess M L k x ∈ Icc (0 : ℝ) 1 := heX.2.1
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hp.1]
    exact (mul_le_mul_of_nonneg_right (by simpa only [Real.norm_eq_abs] using hx) hp.1).trans
      (mul_le_of_le_one_right hW hp.2)
  have irec : Integrable (fun x =>
      ((positiveValue e.piLev k x)⁻¹ * (levelSetProb M L).1 k x) *
        (w x * treatedSuccess M L k x - w x * positiveValue e.P1 k x)) (xLaw M) := by
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
        (treatedSuccess M L k x - positiveValue e.P1 k x)) (xLaw M) := by
    convert irec using 1
    ext x
    simp only [div_eq_mul_inv]
    ring
  have hobs := M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY))
  have hmap : (observationLaw M).map Prod.fst = xLaw M := by
    simpa only [observationLaw, xLaw, Function.comp_def] using
      Measure.map_map measurable_fst hobs
  have iPo : Integrable (fun o : Obs X Z => w o.1 * positiveValue e.P1 k o.1)
      (observationLaw M) := by
    rw [← hmap] at iP
    exact (integrable_map_measure (hw.mul hP).aestronglyMeasurable
      measurable_fst.aemeasurable).mp iP
  have hPo : (∫ o : Obs X Z, w o.1 * positiveValue e.P1 k o.1 ∂observationLaw M) =
      ∫ x, w x * positiveValue e.P1 k x ∂xLaw M := by
    rw [← hmap]
    exact (integral_map measurable_fst.aemeasurable
      (hw.mul hP).aestronglyMeasurable).symm
  obtain ⟨iRP, hRP⟩ := fitted_RP_weighted_integral_of_clipping M L e k hk cpi c W
    hov hc hW hy he0 he hclip w hw hb
  simp_rw [mul_add]
  rw [integral_add iPo iRP, hPo, hRP, ← integral_add iP ir,
    ← integral_sub (iP.fun_add ir) iP0]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

-- A bounded fitted branch or product coefficient preserves the quadratic
-- IPW bias bound even when it has either sign.
-- @node: weighted_clipped_assignment_regression_L2_bound
/-- Suppose [the clipping threshold is positive](hyp:hc), [the weight bound is nonnegative](hyp:hW),
[the weight is measurable](hyp:hw), [the true and fitted assignment functions are measurable](hyp:hp,hq),
[the fitted assignment is almost surely at least the clipping threshold](hyp:hclip), and
[the weight's absolute value is almost surely at most the weight bound](hyp:hb).
If [the assignment error](hyp:heP) and [the regression error](hyp:heR) are square integrable,
[the weight times one minus the true-to-fitted assignment ratio times the regression error is
integrable, and the absolute value of its integral is at most the weight bound times the two
error L2 norms divided by the clipping threshold](goal). -/
lemma weighted_clipped_assignment_regression_L2_bound {B : Type*} [MeasurableSpace B]
    (ν : Measure B) (w p q err : B → ℝ) (c W : ℝ)
    (hc : 0 < c) (hW : 0 ≤ W) (hw : Measurable w)
    (hp : Measurable p) (hq : Measurable q)
    (hclip : ∀ᵐ x ∂ν, c ≤ q x) (hb : ∀ᵐ x ∂ν, ‖w x‖ ≤ W)
    (heP : MemLp (fun x => q x - p x) 2 ν) (heR : MemLp err 2 ν) :
    Integrable (fun x => w x * (1 - p x / q x) * err x) ν ∧
    |∫ x, w x * (1 - p x / q x) * err x ∂ν| ≤
      W * ((eLpNorm (fun x => q x - p x) 2 ν).toReal *
        (eLpNorm err 2 ν).toReal / c) := by
  have hi := (clipped_assignment_regression_L2_remainder ν p q err c hc hp hq
    hclip heP heR).1.bdd_mul hw.aestronglyMeasurable hb
  have hi' : Integrable (fun x => w x * (1 - p x / q x) * err x) ν := by
    simpa only [mul_assoc] using hi
  have hd : Integrable (fun x => W * (|(q x - p x) * err x| / c)) ν :=
    ((heP.integrable_mul heR).abs.div_const c).const_mul W
  have hbound : ∀ᵐ x ∂ν, |w x * (1 - p x / q x) * err x| ≤
      W * (|(q x - p x) * err x| / c) := by
    filter_upwards [hb, hclip] with x hx hqx
    have hr := clipped_assignment_regression_remainder_bound hc hqx (p := p x) (e := err x)
    simpa only [mul_assoc, abs_mul] using
      mul_le_mul (by simpa only [Real.norm_eq_abs] using hx) hr
        (abs_nonneg ((1 - p x / q x) * err x)) hW
  refine ⟨hi', ?_⟩
  calc
    _ ≤ ∫ x, |w x * (1 - p x / q x) * err x| ∂ν := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun x => w x * (1 - p x / q x) * err x)
    _ ≤ ∫ x, W * (|(q x - p x) * err x| / c) ∂ν :=
      integral_mono_ae hi'.abs hd hbound
    _ = W * ((∫ x, |(q x - p x) * err x| ∂ν) / c) := by
      rw [integral_const_mul, integral_div]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right
        (Causalean.Stat.integral_abs_mul_le_eLpNorm_mul_eLpNorm heP heR) hc.le) hW

-- The nuisance errors, rather than an assumed score-bias rate, control
-- the expectation of the actual fitted regression plus residual score.
-- @node: fitted_success_score_bias_L2_bound
/-- Suppose [the index is a positive level within the level count](hyp:hk),
[baseline overlap holds](hyp:hov), [the clipping threshold is positive](hyp:hc),
[the weight bound is nonnegative](hyp:hW), [the outcome is binary almost surely](hyp:hy), and
[the true and fitted binary nuisance records are admissible](hyp:he0,he).
If [the fitted assignment probability is almost surely at least the clipping threshold](hyp:hclip),
[the weight is measurable](hyp:hw), [its absolute value is almost surely at most the weight
bound](hyp:hb), and [the assignment error](hyp:heP) and [the success regression error](hyp:heR)
are square integrable, [the absolute bias of the weighted augmented success score is at most
the weight bound times the product of those error L2 norms divided by the clipping threshold](goal). -/
lemma fitted_success_score_bias_L2_bound (L : LevelData Z X) (e : NuisanceBin L)
    (k : ℕ) (hk : 1 ≤ k ∧ k ≤ L.K) (cpi c W : ℝ)
    (hov : BaselineOverlapWitness M L cpi) (hc : 0 < c) (hW : 0 ≤ W)
    (hy : OutcomeBinaryAE M) (he0 : BinAdmissible M L (eta0Bin M L))
    (he : BinAdmissible M L e)
    (hclip : ∀ᵐ x ∂xLaw M, c ≤ positiveValue e.piLev k x)
    (w : X → ℝ) (hw : Measurable w) (hb : ∀ᵐ x ∂xLaw M, ‖w x‖ ≤ W)
    (heP : MemLp (fun x => positiveValue e.piLev k x - (levelSetProb M L).1 k x) 2 (xLaw M))
    (heR : MemLp (fun x => positiveValue e.P1 k x - treatedSuccess M L k x) 2 (xLaw M)) :
    |(∫ o : Obs X Z, w o.1 * (positiveValue e.P1 k o.1 + RP L e k o)
      ∂observationLaw M) - (∫ x, w x * treatedSuccess M L k x ∂xLaw M)| ≤
      W * ((eLpNorm (fun x => positiveValue e.piLev k x - (levelSetProb M L).1 k x)
        2 (xLaw M)).toReal *
        (eLpNorm (fun x => positiveValue e.P1 k x - treatedSuccess M L k x)
          2 (xLaw M)).toReal / c) := by
  rw [fitted_success_score_exact_bias M L e k hk cpi c W hov hc hW hy he0 he hclip w hw hb]
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

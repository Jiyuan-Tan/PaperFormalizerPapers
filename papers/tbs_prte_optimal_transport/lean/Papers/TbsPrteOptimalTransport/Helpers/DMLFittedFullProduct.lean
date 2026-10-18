module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLFittedSuccessResidual
/-! Fitted full-interval binary product scores: exact second-order bias,
including the fixed zero-success boundary. -/
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

-- @node: fitted_positive_success_measurable
/-- For [an admissible binary nuisance record](hyp:he),
[the fitted success probability, extended by zero outside the positive level indices,
is measurable at every level](goal). -/
@[fun_prop] lemma fitted_positive_success_measurable (L : LevelData Z X)
    (e : NuisanceBin L) (he : BinAdmissible M L e) (k : ℕ) :
    Measurable (positiveValue e.P1 k) := by
  first | fun_prop | skip
  change Measurable (fun x => positiveValue e.P1 k x)
  unfold positiveValue
  split_ifs with hk
  · exact (he.2.2.2.1 ⟨k, hk⟩).2.1
  · fun_prop

-- The boundary at zero and out-of-range indices are fixed, not estimated.
-- @node: fitted_positive_success_range
/-- For [an admissible binary nuisance record](hyp:he),
[the fitted success probability extended by zero lies between zero and one almost surely
under the covariate distribution, at every level index](goal). -/
lemma fitted_positive_success_range (L : LevelData Z X) (e : NuisanceBin L)
    (he : BinAdmissible M L e) (k : ℕ) :
    ∀ᵐ x ∂xLaw M, positiveValue e.P1 k x ∈ Icc (0 : ℝ) 1 := by
  by_cases hk : 1 ≤ k ∧ k ≤ L.K
  · simpa only [positiveValue, dif_pos hk] using
      (he.2.2.1 ⟨k, hk⟩).mono (fun _ hx => hx.2.1)
  · simp only [positiveValue, dif_neg hk]
    exact Filter.Eventually.of_forall (fun _ => ⟨le_rfl, zero_le_one⟩)

-- A bounded covariate function pulls back integrably to the observations.
-- @node: observation_covariate_integrable_of_bound
/-- If [a covariate function is measurable](hyp:hf) and
[its absolute value is almost surely bounded by the specified constant](hyp:hb),
[evaluating it on the covariate of an observation is integrable under the observation law](goal). -/
lemma observation_covariate_integrable_of_bound (f : X → ℝ) (hf : Measurable f)
    (B : ℝ) (hb : ∀ᵐ x ∂xLaw M, ‖f x‖ ≤ B) :
    Integrable (fun o : Obs X Z => f o.1) (observationLaw M) := by
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  exact Integrable.of_bound
    (by first | fun_prop | exact (hf.comp measurable_fst).aestronglyMeasurable)
    B (observationLaw_covariate_ae M _ hb)

-- The fixed lower boundary contributes exactly zero; clipping is required
-- only at the positive indices where an IPW denominator is actually used.
-- @node: fitted_success_score_exact_bias_with_zero
/-- Suppose [the index is no greater than the level count](hyp:hk),
[baseline overlap holds](hyp:hov), [the clipping threshold is positive](hyp:hc),
[the weight bound is nonnegative](hyp:hW), [the outcome is binary almost surely](hyp:hy),
and [both the true and fitted binary nuisance records are admissible](hyp:he0,he).
If [the fitted assignment probability is at least the clipping threshold almost surely whenever
the index is positive](hyp:hclip), [the weight is measurable](hyp:hw), and
[its absolute value is almost surely at most the weight bound](hyp:hb),
[the weighted augmented success score is integrable and its bias equals the covariate mean
of the weight times one minus the true-to-fitted assignment probability ratio times the fitted
success probability error, including at the fixed zero boundary](goal). -/
lemma fitted_success_score_exact_bias_with_zero (L : LevelData Z X) (e : NuisanceBin L)
    (k : ℕ) (hk : k ≤ L.K) (cpi c W : ℝ)
    (hov : BaselineOverlapWitness M L cpi) (hc : 0 < c) (hW : 0 ≤ W)
    (hy : OutcomeBinaryAE M) (he0 : BinAdmissible M L (eta0Bin M L))
    (he : BinAdmissible M L e)
    (hclip : 1 ≤ k → ∀ᵐ x ∂xLaw M, c ≤ positiveValue e.piLev k x)
    (w : X → ℝ) (hw : Measurable w) (hb : ∀ᵐ x ∂xLaw M, ‖w x‖ ≤ W) :
    Integrable (fun o : Obs X Z => w o.1 * (positiveValue e.P1 k o.1 + RP L e k o))
      (observationLaw M) ∧
    (∫ o : Obs X Z, w o.1 * (positiveValue e.P1 k o.1 + RP L e k o)
      ∂observationLaw M) - (∫ x, w x * positiveValue (eta0Bin M L).P1 k x ∂xLaw M) =
      ∫ x, w x * (1 - (levelSetProb M L).1 k x / positiveValue e.piLev k x) *
        (positiveValue e.P1 k x - positiveValue (eta0Bin M L).P1 k x) ∂xLaw M := by
  by_cases hk0 : k = 0
  · subst k
    simp [positiveValue, RP, integrable_zero]
  · have hkp : 1 ≤ k ∧ k ≤ L.K := ⟨by omega, hk⟩
    have hm := fitted_positive_success_measurable M L e he k
    have hi : Integrable (fun o : Obs X Z => w o.1 * positiveValue e.P1 k o.1)
        (observationLaw M) := by
      apply observation_covariate_integrable_of_bound M
        (fun x => w x * positiveValue e.P1 k x) (by fun_prop) W
      filter_upwards [hb, fitted_positive_success_range M L e he k] with x hx hp
      rw [norm_mul, Real.norm_eq_abs (positiveValue e.P1 k x), abs_of_nonneg hp.1]
      exact (mul_le_mul_of_nonneg_right hx hp.1).trans
        (mul_le_of_le_one_right hW hp.2)
    have hr := fitted_RP_weighted_integral_of_clipping M L e k hkp cpi c W
      hov hc hW hy he0 he (hclip hkp.1) w hw hb
    refine ⟨by simpa only [mul_add] using hi.fun_add hr.1, ?_⟩
    simpa only [positiveValue, dif_pos hkp, eta0Bin] using
      fitted_success_score_exact_bias M L e k hkp cpi c W
        hov hc hW hy he0 he (hclip hkp.1) w hw hb

-- @node: fitted_binFullJ_measurable
/-- For [an admissible binary nuisance record](hyp:he),
[the difference between the fitted success probabilities at consecutive levels,
using their zero extensions, is measurable](goal). -/
@[fun_prop] lemma fitted_binFullJ_measurable (L : LevelData Z X) (e : NuisanceBin L)
    (he : BinAdmissible M L e) (k : ℕ) : Measurable (binFullJ L e k) := by
  first | fun_prop | skip
  exact (fitted_positive_success_measurable M L e he (k+1)).sub
    (fitted_positive_success_measurable M L e he k)

-- This contrast is bounded even before monotone rearrangement; sorting is
-- needed for coherent nonnegative gaps, not for this analytic bound.
-- @node: fitted_binFullJ_norm_bound
/-- For [an admissible binary nuisance record](hyp:he),
[the absolute difference between the zero-extended fitted success probabilities at consecutive
levels is at most one almost surely under the covariate distribution](goal). -/
lemma fitted_binFullJ_norm_bound (L : LevelData Z X) (e : NuisanceBin L)
    (he : BinAdmissible M L e) (k : ℕ) :
    ∀ᵐ x ∂xLaw M, ‖binFullJ L e k x‖ ≤ 1 := by
  filter_upwards [fitted_positive_success_range M L e he (k+1),
    fitted_positive_success_range M L e he k] with x hp hm
  simp only [binFullJ, Real.norm_eq_abs, abs_le]
  constructor <;> linarith [hp.1, hp.2, hm.1, hm.2]

-- Finite instrument averaging computes the fitted event term using the true
-- signed instrument probability, independently of the fitted gamma.
-- @node: fitted_full_product_event_mean
/-- For [an admissible binary nuisance record](hyp:he),
[the fitted consecutive-level success contrast times the difference of the higher-policy and
higher-baseline event indicators minus its fitted signed probability is integrable; its mean
equals the covariate mean of that contrast times the true signed probability minus its fit](goal). -/
lemma fitted_full_product_event_mean (L : LevelData Z X) (e : NuisanceBin L)
    (he : BinAdmissible M L e) (k : Fin L.K) :
    Integrable (fun o : Obs X Z => binFullJ L e k o.1 *
      (indicator (o.2.1 ∈ higherPolicy L k) - indicator (o.2.1 ∈ higherBaseline L k) -
        e.gammaFull k o.1)) (observationLaw M) ∧
    (∫ o : Obs X Z, binFullJ L e k o.1 *
      (indicator (o.2.1 ∈ higherPolicy L k) - indicator (o.2.1 ∈ higherBaseline L k) -
        e.gammaFull k o.1) ∂observationLaw M) =
      ∫ x, binFullJ L e k x * (gammaFull M L k x - e.gammaFull k x) ∂xLaw M := by
  have heCopy := he
  rcases heCopy with ⟨_, _, _, _, _, _, _, _, _, hgb, hgm, _, _⟩
  have hj := fitted_binFullJ_measurable M L e he k
  let f : Z × X → ℝ := fun zx => binFullJ L e k zx.2 *
    (indicator (zx.1 ∈ higherPolicy L k) - indicator (zx.1 ∈ higherBaseline L k) -
      e.gammaFull k zx.2)
  have hf : Measurable f := by
    dsimp only [f]
    have hp : Measurable (fun zx : Z × X => indicator (zx.1 ∈ higherPolicy L k)) := by
      unfold indicator
      exact Measurable.ite ((higherPolicy L k).finite_toSet.measurableSet.preimage
        measurable_fst) measurable_const measurable_const
    have hb : Measurable (fun zx : Z × X => indicator (zx.1 ∈ higherBaseline L k)) := by
      unfold indicator
      exact Measurable.ite ((higherBaseline L k).finite_toSet.measurableSet.preimage
        measurable_fst) measurable_const measurable_const
    fun_prop
  have hi : Integrable (fun o : Obs X Z => f (o.2.1, o.1)) (observationLaw M) := by
    haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
    apply Integrable.of_bound
      (by first | fun_prop | exact (hf.comp (measurable_snd.fst.prodMk
        measurable_fst)).aestronglyMeasurable) 3
    filter_upwards [observationLaw_covariate_ae M _ (fitted_binFullJ_norm_bound M L e he k),
      observationLaw_covariate_ae M _ (hgb k)] with o ho hg
    have hgn : |e.gammaFull k o.1| ≤ 1 := abs_le.mpr hg
    have hind (p : Prop) [Decidable p] : |indicator p| ≤ 1 := by
      unfold indicator
      split_ifs <;> norm_num
    have hd : |indicator (o.2.1 ∈ higherPolicy L k) -
        indicator (o.2.1 ∈ higherBaseline L k) - e.gammaFull k o.1| ≤ 3 := by
      have hd0 := abs_sub (indicator (o.2.1 ∈ higherPolicy L k))
        (indicator (o.2.1 ∈ higherBaseline L k))
      have hp := hind (o.2.1 ∈ higherPolicy L k)
      have hb := hind (o.2.1 ∈ higherBaseline L k)
      exact (abs_sub _ _).trans (by linarith)
    dsimp only [f]
    rw [norm_mul, Real.norm_eq_abs]
    exact (mul_le_mul ho hd (abs_nonneg _) (by norm_num)).trans (by norm_num)
  have hmass (x : X) : ∑ z, instProb M z x = 1 := by
    haveI := M.instKernel_markov
    simpa only [instProb] using
      (show ∑ z, (M.instKernel x {z}).toReal = 1 from by
        rw [← ENNReal.toReal_sum (fun z _ => measure_ne_top _ _),
          sum_measure_singleton]
        simp)
  have hsel (C : Finset Z) (x : X) :
      (∑ z, instProb M z x * indicator (z ∈ C)) = ∑ z ∈ C, instProb M z x := by
    simp only [indicator, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hs (x : X) : (∑ z, instProb M z x * f (z, x)) =
      binFullJ L e k x * (gammaFull M L k x - e.gammaFull k x) := by
    simp only [f, mul_left_comm (instProb M _ x), ← Finset.mul_sum,
      mul_sub, Finset.sum_sub_distrib, hsel, ← Finset.sum_mul, hmass, one_mul, gammaFull]
  exact ⟨hi, by simpa only [hs, f] using population_instrument_integral M f hf hi⟩

-- The full product's regression and weight corrections are both included.
-- No score-mean or remainder bound is supplied as a premise.
-- @node: fitted_full_product_exact_bias
/-- Under [baseline overlap](hyp:hov), [a positive clipping threshold](hyp:hc),
[an almost surely binary outcome](hyp:hy),
[admissible true and fitted binary nuisance records](hyp:he0,he), and
[fitted assignment probabilities bounded below by the threshold almost surely at every positive
level](hyp:hclip), [the full-interval binary product score is integrable and its bias relative
to the true signed probability times the true success contrast equals the fitted-signed-probability
weighted assignment-regression remainder at the upper endpoint minus that at the lower endpoint,
minus the covariate mean of the signed-probability error times the success-contrast error](goal). -/
lemma fitted_full_product_exact_bias (L : LevelData Z X) (e : NuisanceBin L)
    (k : Fin L.K) (cpi c : ℝ)
    (hov : BaselineOverlapWitness M L cpi) (hc : 0 < c)
    (hy : OutcomeBinaryAE M) (he0 : BinAdmissible M L (eta0Bin M L))
    (he : BinAdmissible M L e)
    (hclip : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x) :
    Integrable (psiFullProdBin L e k) (observationLaw M) ∧
    (∫ o, psiFullProdBin L e k o ∂observationLaw M) -
      (∫ x, gammaFull M L k x * binFullJ L (eta0Bin M L) k x ∂xLaw M) =
      (∫ x, e.gammaFull k x *
        (1 - (levelSetProb M L).1 (k+1) x / positiveValue e.piLev (k+1) x) *
        (positiveValue e.P1 (k+1) x - positiveValue (eta0Bin M L).P1 (k+1) x)
        ∂xLaw M) -
      (∫ x, e.gammaFull k x *
        (1 - (levelSetProb M L).1 k x / positiveValue e.piLev k x) *
        (positiveValue e.P1 k x - positiveValue (eta0Bin M L).P1 k x) ∂xLaw M) -
      ∫ x, (e.gammaFull k x - gammaFull M L k x) *
        (binFullJ L e k x - binFullJ L (eta0Bin M L) k x) ∂xLaw M := by
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  have heCopy := he
  rcases heCopy with ⟨_, _, _, _, _, _, _, _, _, hgb, hgm, _, _⟩
  have he0Copy := he0
  rcases he0Copy with ⟨_, _, _, _, _, _, _, _, _, hg0b, hg0m, _, _⟩
  have hg : Measurable (e.gammaFull k) := hgm k
  have hg0 : Measurable (gammaFull M L k) := hg0m k
  have hb : ∀ᵐ x ∂xLaw M, ‖e.gammaFull k x‖ ≤ 1 := by
    filter_upwards [hgb k] with x hx
    exact abs_le.mpr hx
  have hb0 : ∀ᵐ x ∂xLaw M, ‖gammaFull M L k x‖ ≤ 1 := by
    filter_upwards [hg0b k] with x hx
    exact abs_le.mpr hx
  have hclip' (i : ℕ) (hi : i ≤ L.K) (hi1 : 1 ≤ i) :
      ∀ᵐ x ∂xLaw M, c ≤ positiveValue e.piLev i x := by
    simpa only [positiveValue, dif_pos (show 1 ≤ i ∧ i ≤ L.K from ⟨hi1, hi⟩)]
      using hclip ⟨i, hi1, hi⟩
  have hp := fitted_success_score_exact_bias_with_zero M L e (k+1)
    (by omega) cpi c 1 hov hc zero_le_one hy he0 he
    (hclip' _ (by omega)) (e.gammaFull k) hg hb
  have hm := fitted_success_score_exact_bias_with_zero M L e k k.isLt.le
    cpi c 1 hov hc zero_le_one hy he0 he
    (hclip' _ k.isLt.le) (e.gammaFull k) hg hb
  have hevent := fitted_full_product_event_mean M L e he k
  have hj := fitted_binFullJ_measurable M L e he k
  have hj0 := fitted_binFullJ_measurable M L (eta0Bin M L) he0 k
  have hjb := fitted_binFullJ_norm_bound M L e he k
  have hj0b := fitted_binFullJ_norm_bound M L (eta0Bin M L) he0 k
  have iP0 (i : ℕ) : Integrable
      (fun x => e.gammaFull k x * positiveValue (eta0Bin M L).P1 i x) (xLaw M) := by
    have hP := fitted_positive_success_measurable M L (eta0Bin M L) he0 i
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards [hb, fitted_positive_success_range M L (eta0Bin M L) he0 i]
      with x hx hpx
    rw [norm_mul, Real.norm_eq_abs (positiveValue (eta0Bin M L).P1 i x),
      abs_of_nonneg hpx.1]
    exact (mul_le_mul_of_nonneg_right hx hpx.1).trans (by simpa using hpx.2)
  have iGJ0 : Integrable
      (fun x => e.gammaFull k x * binFullJ L (eta0Bin M L) k x) (xLaw M) := by
    simpa only [binFullJ, mul_sub] using (iP0 (k+1)).sub' (iP0 k)
  have hGJ0 : (∫ x, e.gammaFull k x * binFullJ L (eta0Bin M L) k x ∂xLaw M) =
      (∫ x, e.gammaFull k x * positiveValue (eta0Bin M L).P1 (k+1) x ∂xLaw M) -
      (∫ x, e.gammaFull k x * positiveValue (eta0Bin M L).P1 k x ∂xLaw M) := by
    simp only [binFullJ, mul_sub]
    exact integral_sub (iP0 (k+1)) (iP0 k)
  have iG0J0 : Integrable
      (fun x => gammaFull M L k x * binFullJ L (eta0Bin M L) k x) (xLaw M) := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards [hb0, hj0b] with x hx hjx
    rw [norm_mul]
    exact (mul_le_mul hx hjx (norm_nonneg _) zero_le_one).trans (by norm_num)
  have iEvent : Integrable
      (fun x => binFullJ L e k x * (gammaFull M L k x - e.gammaFull k x))
      (xLaw M) := by
    apply Integrable.of_bound (by fun_prop) 2
    filter_upwards [hjb, hb0, hb] with x hjx hg0x hgx
    have hd : ‖gammaFull M L k x - e.gammaFull k x‖ ≤ 2 :=
      (norm_sub_le _ _).trans (by linarith)
    rw [norm_mul]
    exact (mul_le_mul hjx hd
      (norm_nonneg _) zero_le_one).trans (by norm_num)
  have hcross :
      (∫ x, binFullJ L e k x * (gammaFull M L k x - e.gammaFull k x) ∂xLaw M) +
      (∫ x, e.gammaFull k x * binFullJ L (eta0Bin M L) k x ∂xLaw M) -
      (∫ x, gammaFull M L k x * binFullJ L (eta0Bin M L) k x ∂xLaw M) =
      -(∫ x, (e.gammaFull k x - gammaFull M L k x) *
        (binFullJ L e k x - binFullJ L (eta0Bin M L) k x) ∂xLaw M) := by
    rw [← integral_add iEvent iGJ0, ← integral_sub (iEvent.fun_add iGJ0) iG0J0,
      ← integral_neg]
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  have hid (o : Obs X Z) : psiFullProdBin L e k o =
      e.gammaFull k o.1 * (positiveValue e.P1 (k+1) o.1 + RP L e (k+1) o) -
      e.gammaFull k o.1 * (positiveValue e.P1 k o.1 + RP L e k o) +
      binFullJ L e k o.1 * (indicator (o.2.1 ∈ higherPolicy L k) -
        indicator (o.2.1 ∈ higherBaseline L k) - e.gammaFull k o.1) := by
    simp only [psiFullProdBin, fullValue, dif_pos k.isLt, binFullJ]
    ring
  refine ⟨?_, ?_⟩
  · change Integrable (fun o => psiFullProdBin L e k o) (observationLaw M)
    simp_rw [hid]
    exact (hp.1.sub' hm.1).fun_add hevent.1
  simp_rw [hid]
  rw [integral_add (hp.1.sub' hm.1) hevent.1, integral_sub hp.1 hm.1, hevent.2]
  linarith [hp.2, hm.2, hGJ0, hcross]

-- Bounded clipped nuisances supply all L2 membership automatically. Thus the
-- bound has no additional moment assumptions and can use the stated rates.
-- @node: fitted_full_product_bias_L2_bound
/-- Under [baseline overlap](hyp:hov), [a positive clipping threshold](hyp:hc),
[an almost surely binary outcome](hyp:hy),
[admissible true and fitted binary nuisance records](hyp:he0,he), and
[fitted assignment probabilities bounded below by the threshold almost surely at every positive
level](hyp:hclip), [the absolute bias of the full-interval binary product score is bounded by
the sum of the upper and lower endpoint assignment-error and success-error L2 norm products
divided by the clipping threshold, plus the L2 norm product of the signed-probability and
success-contrast errors](goal). -/
lemma fitted_full_product_bias_L2_bound (L : LevelData Z X) (e : NuisanceBin L)
    (k : Fin L.K) (cpi c : ℝ)
    (hov : BaselineOverlapWitness M L cpi) (hc : 0 < c)
    (hy : OutcomeBinaryAE M) (he0 : BinAdmissible M L (eta0Bin M L))
    (he : BinAdmissible M L e)
    (hclip : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x) :
    |(∫ o, psiFullProdBin L e k o ∂observationLaw M) -
      (∫ x, gammaFull M L k x * binFullJ L (eta0Bin M L) k x ∂xLaw M)| ≤
      (eLpNorm (fun x => positiveValue e.piLev (k+1) x -
          positiveValue (eta0Bin M L).piLev (k+1) x) 2 (xLaw M)).toReal *
        (eLpNorm (fun x => positiveValue e.P1 (k+1) x -
          positiveValue (eta0Bin M L).P1 (k+1) x) 2 (xLaw M)).toReal / c +
      (eLpNorm (fun x => positiveValue e.piLev k x -
          positiveValue (eta0Bin M L).piLev k x) 2 (xLaw M)).toReal *
        (eLpNorm (fun x => positiveValue e.P1 k x -
          positiveValue (eta0Bin M L).P1 k x) 2 (xLaw M)).toReal / c +
      (eLpNorm (fun x => e.gammaFull k x - gammaFull M L k x) 2 (xLaw M)).toReal *
        (eLpNorm (fun x => binFullJ L e k x - binFullJ L (eta0Bin M L) k x)
          2 (xLaw M)).toReal := by
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  have heCopy := he
  rcases heCopy with ⟨_, _, _, _, _, _, _, _, _, hgb, hgm, _, _⟩
  have he0Copy := he0
  rcases he0Copy with ⟨_, _, _, _, _, _, _, _, _, hg0b, hg0m, _, _⟩
  have hg : Measurable (e.gammaFull k) := hgm k
  have hg0 : Measurable (gammaFull M L k) := hg0m k
  have hb : ∀ᵐ x ∂xLaw M, ‖e.gammaFull k x‖ ≤ 1 := by
    filter_upwards [hgb k] with x hx
    exact abs_le.mpr hx
  have hb0 : ∀ᵐ x ∂xLaw M, ‖gammaFull M L k x‖ ≤ 1 := by
    filter_upwards [hg0b k] with x hx
    exact abs_le.mpr hx
  have hP (e' : NuisanceBin L) (he' : BinAdmissible M L e') (i : ℕ) :
      MemLp (positiveValue e'.P1 i) 2 (xLaw M) := by
    apply MemLp.of_bound (by fun_prop) 1
    filter_upwards [fitted_positive_success_range M L e' he' i] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
    exact hx.2
  have hPi (e' : NuisanceBin L) (he' : BinAdmissible M L e') (i : ℕ) :
      MemLp (positiveValue e'.piLev i) 2 (xLaw M) := by
    by_cases hi : 1 ≤ i ∧ i ≤ L.K
    · have hm : Measurable (positiveValue e'.piLev i) := by
        first | fun_prop | skip
        change Measurable (fun x => positiveValue e'.piLev i x)
        simpa only [positiveValue, dif_pos hi] using (he'.2.2.2.1 ⟨i, hi⟩).2.2
      apply MemLp.of_bound hm.aestronglyMeasurable 1
      filter_upwards [he'.2.2.1 ⟨i, hi⟩] with x hx
      have hxpi : positiveValue e'.piLev i x ∈ Icc (0 : ℝ) 1 := by
        simpa only [positiveValue, dif_pos hi] using hx.2.2
      rw [Real.norm_eq_abs, abs_of_nonneg hxpi.1]
      exact hxpi.2
    · change MemLp (fun x => positiveValue e'.piLev i x) 2 (xLaw M)
      simp only [positiveValue, dif_neg hi]
      exact memLp_const 0
  have hreg (i : ℕ) (hi : i ≤ L.K) :
      |∫ x, e.gammaFull k x *
        (1 - (levelSetProb M L).1 i x / positiveValue e.piLev i x) *
        (positiveValue e.P1 i x - positiveValue (eta0Bin M L).P1 i x) ∂xLaw M| ≤
      (eLpNorm (fun x => positiveValue e.piLev i x -
          positiveValue (eta0Bin M L).piLev i x) 2 (xLaw M)).toReal *
        (eLpNorm (fun x => positiveValue e.P1 i x -
          positiveValue (eta0Bin M L).P1 i x) 2 (xLaw M)).toReal / c := by
    by_cases hi0 : i = 0
    · subst i
      simp [positiveValue]
    · have hip : 1 ≤ i ∧ i ≤ L.K := ⟨by omega, hi⟩
      have hmPi : Measurable (positiveValue e.piLev i) := by
        first | fun_prop | skip
        change Measurable (fun x => positiveValue e.piLev i x)
        simpa only [positiveValue, dif_pos hip] using (he.2.2.2.1 ⟨i, hip⟩).2.2
      have hprob : Measurable (fun x => (levelSetProb M L).1 i x) := by
        first | fun_prop | skip
        exact Finset.measurable_sum _ (fun z _ =>
          (Kernel.measurable_coe _ (measurableSet_singleton z)).ennreal_toReal)
      have hcl : ∀ᵐ x ∂xLaw M, c ≤ positiveValue e.piLev i x := by
        simpa only [positiveValue, dif_pos hip] using hclip ⟨i, hip⟩
      have hd := (hPi e he i).sub (hPi (eta0Bin M L) he0 i)
      change MemLp (fun x => positiveValue e.piLev i x -
        positiveValue (eta0Bin M L).piLev i x) 2 (xLaw M) at hd
      have hd' : MemLp (fun x => positiveValue e.piLev i x - (levelSetProb M L).1 i x)
          2 (xLaw M) := by
        simpa only [positiveValue, dif_pos hip, eta0Bin] using hd
      have hr := (hP e he i).sub (hP (eta0Bin M L) he0 i)
      change MemLp (fun x => positiveValue e.P1 i x -
        positiveValue (eta0Bin M L).P1 i x) 2 (xLaw M) at hr
      simpa only [one_mul, positiveValue, dif_pos hip, eta0Bin] using
        (weighted_clipped_assignment_regression_L2_bound (xLaw M) (e.gammaFull k)
          _ _ _ c 1 hc zero_le_one hg hprob hmPi hcl hb hd' hr).2
  have hge : MemLp (fun x => e.gammaFull k x - gammaFull M L k x) 2 (xLaw M) :=
    (MemLp.of_bound hg.aestronglyMeasurable 1 hb).sub
      (MemLp.of_bound hg0.aestronglyMeasurable 1 hb0)
  have hje : MemLp (fun x => binFullJ L e k x - binFullJ L (eta0Bin M L) k x)
      2 (xLaw M) := by
    exact (MemLp.of_bound (by fun_prop) 1 (fitted_binFullJ_norm_bound M L e he k)).sub
      (MemLp.of_bound (by fun_prop) 1 (fitted_binFullJ_norm_bound M L (eta0Bin M L) he0 k))
  have hcross : |∫ x, (e.gammaFull k x - gammaFull M L k x) *
      (binFullJ L e k x - binFullJ L (eta0Bin M L) k x) ∂xLaw M| ≤
      (eLpNorm (fun x => e.gammaFull k x - gammaFull M L k x) 2 (xLaw M)).toReal *
        (eLpNorm (fun x => binFullJ L e k x - binFullJ L (eta0Bin M L) k x)
          2 (xLaw M)).toReal := by
    calc
      _ ≤ ∫ x, |(e.gammaFull k x - gammaFull M L k x) *
          (binFullJ L e k x - binFullJ L (eta0Bin M L) k x)| ∂xLaw M := by
        simpa only [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (fun x => (e.gammaFull k x - gammaFull M L k x) *
            (binFullJ L e k x - binFullJ L (eta0Bin M L) k x))
      _ ≤ _ := Causalean.Stat.integral_abs_mul_le_eLpNorm_mul_eLpNorm hge hje
  rw [(fitted_full_product_exact_bias M L e k cpi c hov hc hy he0 he hclip).2]
  apply (abs_sub _ _).trans
  apply (add_le_add (abs_sub _ _) le_rfl).trans
  exact add_le_add (add_le_add (hreg (k+1) (by omega)) (hreg k k.isLt.le)) hcross

end Papers.TbsPrteOptimalTransport

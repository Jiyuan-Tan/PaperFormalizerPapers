module
public import Papers.TbsPrteOptimalTransport.Helpers.JointPooledPopulation
/-! Weighted tower transfer for fitted pooled policy residuals. -/
public section
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false

set_option linter.style.haveILetI false
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

-- @node: population_RqBin_fitted_weighted_finite_mean
/-- Under [threshold crossing](hyp:h), suppose [the covariate weight is measurable](hyp:hw),
[the fitted propensity is jointly measurable in instrument and covariates](hyp:hp), [the
policy derivative evaluated at that fitted propensity is jointly measurable](hyp:hd), and
[the fitted pooled denominator is measurable](hyp:htau). If [the weighted pooled residual
with treatment replaced by its true propensity is integrable](hyp:hi) and [the weight
times the inverse fitted denominator, the band indicator, the fitted policy derivative,
and the true-centered treatment is integrable](hyp:hr), [the weighted observed pooled
residual is integrable and its mean equals the covariate integral of the finite sum of
propensity-substituted residuals weighted by true conditional instrument probabilities
and the covariate weight](goal). -/
lemma population_RqBin_fitted_weighted_finite_mean (h : ThresholdCrossing M)
    (dphi : Z → X → ℝ → ℝ) (L : LevelData Z X) (e : NuisanceBin L)
    (a : RegularIndex L) (w : X → ℝ) (hw : Measurable w)
    (hp : Measurable (fun zx : Z × X => e.prop zx.1 zx.2))
    (hd : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (e.prop zx.1 zx.2)))
    (htau : Measurable (e.tauLev a))
    (hi : Integrable (fun o : Obs X Z => w o.1 * RqBin dphi L e a.val.1 a.val.2
      (o.1, o.2.1, M.prop o.2.1 o.1, 0)) (observationLaw M))
    (hr : Integrable (fun o : Obs X Z =>
      w o.1 * ((e.tauLev a o.1)⁻¹ * indicator (o.2.1 ∈ L.T a.val.1 a.val.2) *
        dphi o.2.1 o.1 (e.prop o.2.1 o.1)) *
        (o.2.2.1 - M.prop o.2.1 o.1)) (observationLaw M)) :
    Integrable (fun o => w o.1 * RqBin dphi L e a.val.1 a.val.2 o) (observationLaw M) ∧
    (∫ o, w o.1 * RqBin dphi L e a.val.1 a.val.2 o ∂observationLaw M) =
      ∫ x, w x * ∑ z, instProb M z x * RqBin dphi L e a.val.1 a.val.2
        (x, z, M.prop z x, 0) ∂xLaw M := by
  let C : Z × X → ℝ := fun zx => w zx.2 * (e.tauLev a zx.2)⁻¹ *
    indicator (zx.1 ∈ L.T a.val.1 a.val.2) * dphi zx.1 zx.2 (e.prop zx.1 zx.2)
  have hC : Measurable C := by
    have ht : Measurable (fun zx : Z × X => e.tauLev a zx.2) := htau.comp measurable_snd
    have hid : Measurable (fun zx : Z × X => indicator (zx.1 ∈ L.T a.val.1 a.val.2)) := by
      unfold indicator
      exact Measurable.ite ((L.T a.val.1 a.val.2).finite_toSet.measurableSet.preimage
        measurable_fst) measurable_const measurable_const
    dsimp only [C]
    first | fun_prop | exact (((hw.comp measurable_snd).mul ht.inv).mul hid).mul hd
  have hf : Measurable (fun zx : Z × X => w zx.2 * RqBin dphi L e a.val.1 a.val.2
      (zx.2, zx.1, M.prop zx.1 zx.2, 0)) := by
    simp only [RqBin_fitted_residual_factorization]
    convert! hC.mul (h.2.1.sub hp) using 1
    funext zx
    dsimp only [C, Pi.mul_apply, Pi.sub_apply, Function.uncurry]
    ring
  have heq : ∀ o : Obs X Z, w o.1 * RqBin dphi L e a.val.1 a.val.2 o =
      w o.1 * RqBin dphi L e a.val.1 a.val.2 (o.1, o.2.1, M.prop o.2.1 o.1, 0) +
        C (o.2.1, o.1) * (o.2.2.1 - M.prop o.2.1 o.1) := by
    intro o
    simp only [RqBin_fitted_residual_factorization, C]
    ring
  have hz := population_treatment_weighted_integral_zero M h C hC (by
    convert! hr using 1
    funext o
    dsimp only [C, Pi.mul_apply, Pi.sub_apply, Function.uncurry]
    ring)
  constructor
  · change Integrable (fun o => w o.1 * RqBin dphi L e a.val.1 a.val.2 o) _
    rw [show (fun o => w o.1 * RqBin dphi L e a.val.1 a.val.2 o) = _ from funext heq]
    convert! hi.fun_add hr using 1
    funext o
    dsimp only [C, Pi.mul_apply, Pi.sub_apply, Function.uncurry]
    ring
  · conv_lhs => enter [2, o]; rw [heq o]
    have hrC : Integrable (fun o : Obs X Z => C (o.2.1, o.1) *
        (o.2.2.1 - M.prop o.2.1 o.1)) (observationLaw M) := by
      convert! hr using 1
      funext o
      dsimp only [C]
      ring
    rw [integral_add hi hrC, hz, add_zero]
    have hm := population_instrument_integral M _ hf hi
    convert! hm using 1
    congr 1
    funext x
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    ring


-- @node: population_RqBin_weighted_finite_mean_of_binary_admissible
/-- Under [threshold crossing](hyp:h), suppose [the policy map is valid](hyp:hphi), [its
derivative is the specified policy derivative](hyp:hDiff), [that derivative is bounded
and Lipschitz](hyp:hDerivative), and [the fitted binary nuisance is admissible](hyp:he).
If [the pooled-denominator lower bound is positive](hyp:hc), [the fitted denominator is
at least that bound almost everywhere](hyp:hden), and [the covariate weight is
measurable](hyp:hw) and [almost everywhere bounded in absolute value](hyp:hwB), [both the
weighted observed pooled residual and its true-instrument-probability-weighted finite
sum with treatment replaced by its true propensity are integrable under their respective
observation and covariate laws, and their means agree](goal). -/
lemma population_RqBin_weighted_finite_mean_of_binary_admissible (h : ThresholdCrossing M)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e : NuisanceBin L) (he : BinAdmissible M L e)
    (a : RegularIndex L) (c : ℝ) (hc : 0 < c)
    (hden : ∀ᵐ x ∂xLaw M, c ≤ e.tauLev a x)
    (w : X → ℝ) (hw : Measurable w) (W : ℝ)
    (hwB : ∀ᵐ x ∂xLaw M, ‖w x‖ ≤ W) :
    Integrable (fun o => w o.1 * RqBin dphi L e a.val.1 a.val.2 o) (observationLaw M) ∧
    Integrable (fun x => w x * ∑ z, instProb M z x * RqBin dphi L e a.val.1 a.val.2
      (x, z, M.prop z x, 0)) (xLaw M) ∧
    (∫ o, w o.1 * RqBin dphi L e a.val.1 a.val.2 o ∂observationLaw M) =
      ∫ x, w x * ∑ z, instProb M z x * RqBin dphi L e a.val.1 a.val.2
        (x, z, M.prop z x, 0) ∂xLaw M := by
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  let pc : Z → X → ℝ := fun z x => max 0 (min 1 (e.prop z x))
  let ep : NuisanceBin L := {e with prop := pc}
  have hpc : Measurable (fun zx : Z × X => pc zx.1 zx.2) := by
    apply measurable_from_prod_countable_right
    intro z
    have hm := he.2.1 z
    dsimp only [pc]
    fun_prop
  have hpcR : ∀ z x, pc z x ∈ Icc (0 : ℝ) 1 := fun z x =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hdq := policy_derivative_graph_measurable phi dphi hphi hDiff pc hpc hpcR
  have htau : Measurable (e.tauLev a) := (he.2.2.2.2.2.1 a).1
  let C : Z × X → ℝ := fun zx => (e.tauLev a zx.2)⁻¹ *
    indicator (zx.1 ∈ L.T a.val.1 a.val.2) * dphi zx.1 zx.2 (pc zx.1 zx.2)
  have hC : Measurable C := by
    have ht : Measurable (fun zx : Z × X => e.tauLev a zx.2) := htau.comp measurable_snd
    have hid : Measurable (fun zx : Z × X => indicator (zx.1 ∈ L.T a.val.1 a.val.2)) := by
      unfold indicator
      exact Measurable.ite ((L.T a.val.1 a.val.2).finite_toSet.measurableSet.preimage
        measurable_fst) measurable_const measurable_const
    dsimp only [C]
    first | fun_prop | exact (ht.inv.mul hid).mul hdq
  obtain ⟨B, Lip, hB, hLip, hb⟩ := hDerivative
  have hCo : Measurable (fun o : Obs X Z => C (o.2.1, o.1)) := by fun_prop
  have hCb : ∀ᵐ o : Obs X Z ∂observationLaw M, |C (o.2.1, o.1)| ≤ B/c := by
    filter_upwards [observationLaw_covariate_ae M _ hden] with o ho
    have hpos : 0 < e.tauLev a o.1 := hc.trans_le ho
    have hd : |dphi o.2.1 o.1 (pc o.2.1 o.1)| ≤ B :=
      (hb o.2.1 o.1 (pc o.2.1 o.1) (pc o.2.1 o.1)
        (hpcR o.2.1 o.1) (hpcR o.2.1 o.1)).1
    have hi : |indicator (o.2.1 ∈ L.T a.val.1 a.val.2)| ≤ 1 := by
      unfold indicator
      split_ifs <;> norm_num
    dsimp only [C]
    rw [abs_mul, abs_mul, abs_inv, abs_of_pos hpos]
    calc
      _ ≤ c⁻¹ * 1 * B := by gcongr
      _ = _ := by ring
  have htreatment : ∀ᵐ o : Obs X Z ∂observationLaw M, o.2.2.1 ∈ Icc (0 : ℝ) 1 := by
    have hobs := M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY))
    apply (ae_map_iff hobs.aemeasurable
      (measurableSet_Icc.preimage measurable_snd.snd.fst)).2
    exact Eventually.of_forall (fun s => by
      rcases M.rangeW s with hs | hs <;> simp [hs])
  have hip : Integrable (fun o : Obs X Z => RqBin dphi L ep a.val.1 a.val.2
      (o.1, o.2.1, M.prop o.2.1 o.1, 0)) (observationLaw M) := by
    simp only [RqBin_fitted_residual_factorization]
    change Integrable (fun o : Obs X Z => C (o.2.1, o.1) *
      (M.prop o.2.1 o.1 - pc o.2.1 o.1)) _
    have hm : Measurable (fun o : Obs X Z => C (o.2.1, o.1) *
        (M.prop o.2.1 o.1 - pc o.2.1 o.1)) := by
      first | fun_prop | exact hCo.mul ((h.2.1.sub hpc).comp
        (measurable_snd.fst.prodMk measurable_fst))
    apply Integrable.of_bound hm.aestronglyMeasurable (B/c * 2)
    filter_upwards [hCb] with o ho
    have hp := M.rangeProp o.2.1 o.1
    have hq := hpcR o.2.1 o.1
    have hd : |M.prop o.2.1 o.1 - pc o.2.1 o.1| ≤ 2 := by
      rw [abs_le]
      constructor <;> linarith [hp.1, hp.2, hq.1, hq.2]
    simp only [Real.norm_eq_abs, abs_mul]
    gcongr
  have hrp : Integrable (fun o : Obs X Z => C (o.2.1, o.1) *
      (o.2.2.1 - M.prop o.2.1 o.1)) (observationLaw M) := by
    have hm : Measurable (fun o : Obs X Z => C (o.2.1, o.1) *
        (o.2.2.1 - M.prop o.2.1 o.1)) := by
      first | fun_prop | exact hCo.mul (measurable_snd.snd.fst.sub
        (h.2.1.comp (measurable_snd.fst.prodMk measurable_fst)))
    apply Integrable.of_bound hm.aestronglyMeasurable (B/c * 2)
    filter_upwards [hCb, htreatment] with o ho hw
    have hp := M.rangeProp o.2.1 o.1
    have hd : |o.2.2.1 - M.prop o.2.1 o.1| ≤ 2 := by
      rw [abs_le]
      constructor <;> linarith [hw.1, hw.2, hp.1, hp.2]
    simp only [Real.norm_eq_abs, abs_mul]
    gcongr
  have hwobs : AEStronglyMeasurable (fun o : Obs X Z => w o.1)
      (observationLaw M) := (hw.comp measurable_fst).aestronglyMeasurable
  have hwbound := observationLaw_covariate_ae M _ hwB
  have hipw := hip.bdd_mul hwobs hwbound
  have hrpw := hrp.bdd_mul hwobs hwbound
  have hmean := population_RqBin_fitted_weighted_finite_mean M h dphi L ep a w hw
    hpc hdq htau hipw (by simpa only [C, ep, mul_assoc] using hrpw)
  have heq : ∀ᵐ x ∂xLaw M, ∀ z, pc z x = e.prop z x := by
    filter_upwards [ae_all_iff.mpr he.1] with x hx
    intro z
    simp only [pc, min_eq_right (hx z).2, max_eq_right (hx z).1]
  have heqo : (fun o : Obs X Z => w o.1 * RqBin dphi L ep a.val.1 a.val.2 o)
      =ᵐ[observationLaw M] (fun o => w o.1 * RqBin dphi L e a.val.1 a.val.2 o) := by
    filter_upwards [observationLaw_covariate_ae M _ heq] with o ho
    rw [RqBin_fitted_residual_factorization dphi L ep a o,
      RqBin_fitted_residual_factorization dphi L e a o]
    change w o.1 * ((e.tauLev a o.1)⁻¹ * indicator (o.2.1 ∈ L.T a.val.1 a.val.2) *
      dphi o.2.1 o.1 (pc o.2.1 o.1) * (o.2.2.1 - pc o.2.1 o.1)) = _
    rw [ho o.2.1]
  have hif : Integrable (fun x => ∑ z, instProb M z x *
      RqBin dphi L ep a.val.1 a.val.2 (x, z, M.prop z x, 0)) (xLaw M) := by
    haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
    apply integrable_finsetSum
    intro z hz
    simp only [RqBin_fitted_residual_factorization]
    change Integrable (fun x => instProb M z x *
      (C (z,x) * (M.prop z x - pc z x))) _
    have hmass : Measurable (instProb M z) :=
      (Kernel.measurable_coe _ (measurableSet_singleton z)).ennreal_toReal
    have hm : Measurable (fun x => instProb M z x *
        (C (z,x) * (M.prop z x - pc z x))) := by
      first | fun_prop | exact hmass.mul ((hC.comp (measurable_const.prodMk measurable_id)).mul
        ((h.2.1.sub hpc).comp (measurable_const.prodMk measurable_id)))
    apply Integrable.of_bound hm.aestronglyMeasurable (B/c * 2)
    filter_upwards [hden] with x hx
    have hpos : 0 < e.tauLev a x := hc.trans_le hx
    have hi : |indicator (z ∈ L.T a.val.1 a.val.2)| ≤ 1 := by
      unfold indicator
      split_ifs <;> norm_num
    have hd : |dphi z x (pc z x)| ≤ B :=
      (hb z x (pc z x) (pc z x) (hpcR z x) (hpcR z x)).1
    have hdiff : |M.prop z x - pc z x| ≤ 2 := by
      rw [abs_le]
      constructor <;> linarith [(M.rangeProp z x).1, (M.rangeProp z x).2,
        (hpcR z x).1, (hpcR z x).2]
    haveI := M.instKernel_markov
    have hmassb : |instProb M z x| ≤ 1 := by
      rw [instProb, abs_of_nonneg ENNReal.toReal_nonneg]
      exact measureReal_le_one
    dsimp only [C]
    simp only [Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos hpos]
    calc
      _ ≤ 1 * (c⁻¹ * 1 * B * 2) := by gcongr
      _ = _ := by ring
  have hfeq : (fun x => ∑ z, instProb M z x * RqBin dphi L ep a.val.1 a.val.2
      (x,z,M.prop z x,0)) =ᵐ[xLaw M]
      (fun x => ∑ z, instProb M z x * RqBin dphi L e a.val.1 a.val.2
        (x,z,M.prop z x,0)) := by
    filter_upwards [heq] with x hx
    apply Finset.sum_congr rfl
    intro z _
    rw [RqBin_fitted_residual_factorization dphi L ep a (x,z,M.prop z x,0),
      RqBin_fitted_residual_factorization dphi L e a (x,z,M.prop z x,0)]
    change instProb M z x * ((e.tauLev a x)⁻¹ * indicator (z ∈ L.T a.val.1 a.val.2) *
      dphi z x (pc z x) * (M.prop z x - pc z x)) = _
    rw [hx z]
  have hifw := hif.bdd_mul hw.aestronglyMeasurable hwB
  have hfeqw' : (fun x => w x * ∑ z, instProb M z x * RqBin dphi L ep
      a.val.1 a.val.2 (x,z,M.prop z x,0)) =ᵐ[xLaw M]
      (fun x => w x * ∑ z, instProb M z x * RqBin dphi L e
        a.val.1 a.val.2 (x,z,M.prop z x,0)) := by
    filter_upwards [hfeq] with x hx
    rw [hx]
  refine ⟨hmean.1.congr heqo, hifw.congr hfeqw', ?_⟩
  rw [← integral_congr_ae heqo, hmean.2, integral_congr_ae hfeqw']

-- @node: pooledQBin_weighted_integrable_of_binary_admissible
/-- For [a valid policy map](hyp:hphi) and [an admissible fitted binary nuisance](hyp:he),
if [the covariate weight is measurable](hyp:hw) and [almost everywhere bounded in absolute
value](hyp:hwB), [the weighted fitted pooled policy level is integrable under both the
covariate and observation laws, and its integrals under these laws coincide](goal). -/
lemma pooledQBin_weighted_integrable_of_binary_admissible
    (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (L : LevelData Z X) (e : NuisanceBin L) (he : BinAdmissible M L e)
    (a : RegularIndex L) (w : X → ℝ) (hw : Measurable w) (W : ℝ)
    (hwB : ∀ᵐ x ∂xLaw M, ‖w x‖ ≤ W) :
    Integrable (fun x => w x * pooledQBin phi L e a.val.1 a.val.2 x) (xLaw M) ∧
    Integrable (fun o : Obs X Z => w o.1 * pooledQBin phi L e a.val.1 a.val.2 o.1)
      (observationLaw M) ∧
    (∫ o : Obs X Z, w o.1 * pooledQBin phi L e a.val.1 a.val.2 o.1
      ∂observationLaw M) = ∫ x, w x * pooledQBin phi L e a.val.1 a.val.2 x ∂xLaw M := by
  have hq := pooledQBin_integrable_of_binary_admissible M phi hphi L e he a
  have hi := hq.1.bdd_mul hw.aestronglyMeasurable hwB
  have hobs := M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY))
  have hmap : (observationLaw M).map Prod.fst = xLaw M := by
    simpa only [observationLaw, xLaw, Function.comp_def] using
      Measure.map_map measurable_fst hobs
  have him : Integrable (fun x => w x * pooledQBin phi L e a.val.1 a.val.2 x)
      ((observationLaw M).map Prod.fst) := by rwa [hmap]
  refine ⟨hi, (integrable_map_measure him.aestronglyMeasurable
    measurable_fst.aemeasurable).mp him, ?_⟩
  rw [← hmap]
  exact (integral_map measurable_fst.aemeasurable him.aestronglyMeasurable).symm

-- This identity includes the fitted pooled level and its fitted residual;
-- a regular score's moving branch coefficient may serve as the weight.
-- @node: population_binary_weighted_pooled_fitted_mean
/-- Under [threshold crossing](hyp:h), [a valid policy map](hyp:hphi), [the specified policy
derivative](hyp:hDiff), [boundedness and Lipschitz continuity of that derivative](hyp:hDerivative),
and [admissibility of the fitted binary nuisance](hyp:he), suppose [the denominator lower
bound is positive](hyp:hc), [the fitted pooled denominator is at least that bound almost
everywhere](hyp:hden), and [the covariate weight is measurable](hyp:hw) and [almost everywhere
bounded in absolute value](hyp:hwB). Then [the weighted fitted pooled level plus its
residual is integrable under the observation law, the corresponding expression with the
residual replaced by its true-instrument-probability-weighted finite sum at the true
propensity is integrable under the covariate law, and the two means are equal](goal). -/
lemma population_binary_weighted_pooled_fitted_mean (h : ThresholdCrossing M)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e : NuisanceBin L) (he : BinAdmissible M L e)
    (a : RegularIndex L) (c : ℝ) (hc : 0 < c)
    (hden : ∀ᵐ x ∂xLaw M, c ≤ e.tauLev a x)
    (w : X → ℝ) (hw : Measurable w) (W : ℝ)
    (hwB : ∀ᵐ x ∂xLaw M, ‖w x‖ ≤ W) :
    Integrable (fun o : Obs X Z => w o.1 *
      (pooledQBin phi L e a.val.1 a.val.2 o.1 + RqBin dphi L e a.val.1 a.val.2 o))
      (observationLaw M) ∧
    Integrable (fun x => w x * (pooledQBin phi L e a.val.1 a.val.2 x +
      ∑ z, instProb M z x * RqBin dphi L e a.val.1 a.val.2
        (x,z,M.prop z x,0))) (xLaw M) ∧
    (∫ o : Obs X Z, w o.1 * (pooledQBin phi L e a.val.1 a.val.2 o.1 +
      RqBin dphi L e a.val.1 a.val.2 o) ∂observationLaw M) =
      ∫ x, w x * (pooledQBin phi L e a.val.1 a.val.2 x +
        ∑ z, instProb M z x * RqBin dphi L e a.val.1 a.val.2
          (x,z,M.prop z x,0)) ∂xLaw M := by
  have hq := pooledQBin_weighted_integrable_of_binary_admissible M phi hphi L e he a
    w hw W hwB
  have hr := population_RqBin_weighted_finite_mean_of_binary_admissible M h
    phi dphi hphi hDiff hDerivative L e he a c hc hden w hw W hwB
  refine ⟨?_, ?_, ?_⟩
  · simpa only [mul_add] using hq.2.1.fun_add hr.1
  · simpa only [mul_add] using hq.1.fun_add hr.2.1
  · simp_rw [mul_add]
    rw [integral_add hq.2.1 hr.1, integral_add hq.1 hr.2.1, hq.2.2, hr.2.2]

-- Uniform overlap comes from the path and population overlap, including
-- simultaneous share, propensity, and denominator perturbations.
-- @node: population_binary_weighted_pooled_path_local_mean
/-- Assume [threshold crossing](hyp:h), [a valid policy map](hyp:hphi), [the specified policy
derivative](hyp:hDiff), [boundedness and Lipschitz continuity of that derivative](hyp:hDerivative),
[invariance of the level order under the policy propensity](hyp:hOrder), [policy
overlap](hyp:hov), and [an admissible binary nuisance direction at the truth](hyp:hd).
For [covariate weights measurable at each path displacement](hyp:hw) and [uniformly bounded
in absolute value almost everywhere](hyp:hwB), [throughout some neighborhood of zero the
mean of the weighted fitted pooled level plus its observed residual equals the covariate
mean obtained by replacing that residual with its finite sum over instruments, weighted
by true conditional instrument probabilities and evaluated at the true propensity](goal). -/
lemma population_binary_weighted_pooled_path_local_mean (h : ThresholdCrossing M)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : PolicyOverlap M L cpi) (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del))
    (a : RegularIndex L) (w : ℝ → X → ℝ)
    (hw : ∀ t, Measurable (w t)) (W : ℝ)
    (hwB : ∀ t, ∀ᵐ x ∂xLaw M, ‖w t x‖ ≤ W) :
    ∀ᶠ t : ℝ in nhds 0,
      (∫ o : Obs X Z, w t o.1 *
        (pooledQBin phi L (eta0Bin M L + t • del) a.val.1 a.val.2 o.1 +
          RqBin dphi L (eta0Bin M L + t • del) a.val.1 a.val.2 o)
          ∂observationLaw M) =
        ∫ x, w t x * (pooledQBin phi L (eta0Bin M L + t • del) a.val.1 a.val.2 x +
          ∑ z, instProb M z x * RqBin dphi L (eta0Bin M L + t • del)
            a.val.1 a.val.2 (x,z,M.prop z x,0)) ∂xLaw M := by
  have hden : ∀ᵐ x ∂xLaw M, cpi ≤ (eta0Bin M L).tauLev a x := by
    apply Eventually.of_forall
    intro x
    exact hov.2 x a.val.1 a.val.2 a.property.1 a.property.2.1 a.property.2.2
      (ordered_policy_level_nonempty M (policyProp phi M.prop) L hOrder
        a.val.1 a.val.2 a.property.1 a.property.2.1 a.property.2.2)
  obtain ⟨r, hr, hadm⟩ := hd.admissible
  filter_upwards [continuousAt_id.abs.eventually_lt_const (by simpa using hr),
    binary_pooled_denominator_uniform_neighborhood M L (eta0Bin M L) del hd a
      cpi hov.1 hden] with t ht hdt
  exact (population_binary_weighted_pooled_fitted_mean M h phi dphi hphi hDiff
    hDerivative L _ (hadm t ht) a (cpi/2) (by have := hov.1; positivity)
      hdt (w t) (hw t) W (hwB t)).2.2

end Papers.TbsPrteOptimalTransport

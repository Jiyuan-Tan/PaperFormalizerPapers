module
public import Papers.TbsPrteOptimalTransport.Helpers.JointPooledIntegration
/-! Tower transfer for pooled policy residuals along simultaneous nuisance paths. -/
public section
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false

set_option linter.style.haveILetI false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: RqBin_fitted_residual_factorization
/-- [At a regular level, the fitted policy residual equals the observed treatment
minus its fitted propensity, multiplied by the policy derivative at that
propensity, the indicator that the instrument belongs to the level, and the
reciprocal fitted pooled denominator](goal). -/
lemma RqBin_fitted_residual_factorization (dphi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (e : NuisanceBin L) (a : RegularIndex L) (o : Obs X Z) :
    RqBin dphi L e a.val.1 a.val.2 o =
      ((e.tauLev a o.1)⁻¹ * indicator (o.2.1 ∈ L.T a.val.1 a.val.2) *
        dphi o.2.1 o.1 (e.prop o.2.1 o.1)) * (o.2.2.1 - e.prop o.2.1 o.1) := by
  have hbad : ¬ (a.val.2 = 0 ∨ L.l a.val.1 < a.val.2) := by
    have := a.property
    omega
  simp only [RqBin, if_neg hbad, regularValue, dif_pos a.property]
  have hid : ∀ z, dphi z o.1 (e.prop z o.1) * indicator (o.2.1 = z) *
      (o.2.2.1 - e.prop z o.1) =
      if o.2.1 = z then dphi o.2.1 o.1 (e.prop o.2.1 o.1) *
        (o.2.2.1 - e.prop o.2.1 o.1) else 0 := by
    intro z
    by_cases hz : o.2.1 = z
    · subst z
      simp [indicator]
    · simp [indicator, hz]
  simp_rw [hid]
  simp [indicator, mul_assoc]

-- A fitted policy residual is centered at the true treatment mean, before
-- averaging over the true instrument kernel. Its denominator may also be fitted.
-- @node: population_RqBin_fitted_finite_mean
/-- Under [the threshold-crossing model](hyp:h), suppose [the fitted propensity
is measurable](hyp:hp), [the policy derivative evaluated at that propensity is
measurable](hyp:hd), and [the fitted pooled denominator is measurable](hyp:htau).
If [the residual evaluated at the true treatment mean is integrable](hyp:hi) and
[the derivative-weighted treatment deviation from its true mean is integrable](hyp:hr),
then [the fitted policy residual is integrable and its observation expectation
equals its finite instrument average at the true treatment mean, integrated over
covariates](goal). -/
lemma population_RqBin_fitted_finite_mean (h : ThresholdCrossing M)
    (dphi : Z → X → ℝ → ℝ) (L : LevelData Z X) (e : NuisanceBin L)
    (a : RegularIndex L)
    (hp : Measurable (fun zx : Z × X => e.prop zx.1 zx.2))
    (hd : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (e.prop zx.1 zx.2)))
    (htau : Measurable (e.tauLev a))
    (hi : Integrable (fun o : Obs X Z => RqBin dphi L e a.val.1 a.val.2
      (o.1, o.2.1, M.prop o.2.1 o.1, 0)) (observationLaw M))
    (hr : Integrable (fun o : Obs X Z =>
      ((e.tauLev a o.1)⁻¹ * indicator (o.2.1 ∈ L.T a.val.1 a.val.2) *
        dphi o.2.1 o.1 (e.prop o.2.1 o.1)) *
        (o.2.2.1 - M.prop o.2.1 o.1)) (observationLaw M)) :
    Integrable (RqBin dphi L e a.val.1 a.val.2) (observationLaw M) ∧
    (∫ o, RqBin dphi L e a.val.1 a.val.2 o ∂observationLaw M) =
      ∫ x, ∑ z, instProb M z x * RqBin dphi L e a.val.1 a.val.2
        (x, z, M.prop z x, 0) ∂xLaw M := by
  let C : Z × X → ℝ := fun zx => (e.tauLev a zx.2)⁻¹ *
    indicator (zx.1 ∈ L.T a.val.1 a.val.2) * dphi zx.1 zx.2 (e.prop zx.1 zx.2)
  have hC : Measurable C := by
    have ht : Measurable (fun zx : Z × X => e.tauLev a zx.2) := htau.comp measurable_snd
    have hid : Measurable (fun zx : Z × X => indicator (zx.1 ∈ L.T a.val.1 a.val.2)) := by
      unfold indicator
      exact Measurable.ite ((L.T a.val.1 a.val.2).finite_toSet.measurableSet.preimage
        measurable_fst) measurable_const measurable_const
    dsimp only [C]
    first | fun_prop | exact (ht.inv.mul hid).mul hd
  have hf : Measurable (fun zx : Z × X => RqBin dphi L e a.val.1 a.val.2
      (zx.2, zx.1, M.prop zx.1 zx.2, 0)) := by
    simp only [RqBin_fitted_residual_factorization]
    exact hC.mul (h.2.1.sub hp)
  have heq : ∀ o : Obs X Z, RqBin dphi L e a.val.1 a.val.2 o =
      RqBin dphi L e a.val.1 a.val.2 (o.1, o.2.1, M.prop o.2.1 o.1, 0) +
        C (o.2.1, o.1) * (o.2.2.1 - M.prop o.2.1 o.1) := by
    intro o
    simp only [RqBin_fitted_residual_factorization, C]
    ring
  have hz := population_treatment_weighted_integral_zero M h C hC hr
  constructor
  · change Integrable (fun o => RqBin dphi L e a.val.1 a.val.2 o) _
    rw [show (fun o => RqBin dphi L e a.val.1 a.val.2 o) = _ from funext heq]
    exact hi.fun_add hr
  · conv_lhs => enter [2, o]; rw [heq o]
    rw [integral_add hi hr, hz, add_zero]
    exact population_instrument_integral M _ hf hi

-- Clipping gives a measurable representative on every covariate fiber.
-- Admissibility identifies it with the supplied nuisance almost everywhere;
-- overlap and the bounded policy derivative provide all integrability here.
-- @node: population_RqBin_finite_mean_of_binary_admissible
/-- Under [the threshold-crossing model](hyp:h), let [the policy be measurable
and probability valued](hyp:hphi), [have the specified derivative](hyp:hDiff),
and [have a uniformly bounded Lipschitz derivative](hyp:hDerivative). If [the
fitted binary nuisance is admissible](hyp:he), [the denominator bound is
positive](hyp:hc), and [the fitted pooled denominator exceeds that bound almost
everywhere](hyp:hden), then [both the observation policy residual and its finite
conditional instrument average at the true treatment mean are integrable, and
their respective population expectations are equal](goal). -/
lemma population_RqBin_finite_mean_of_binary_admissible (h : ThresholdCrossing M)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e : NuisanceBin L) (he : BinAdmissible M L e)
    (a : RegularIndex L) (c : ℝ) (hc : 0 < c)
    (hden : ∀ᵐ x ∂xLaw M, c ≤ e.tauLev a x) :
    Integrable (RqBin dphi L e a.val.1 a.val.2) (observationLaw M) ∧
    Integrable (fun x => ∑ z, instProb M z x * RqBin dphi L e a.val.1 a.val.2
      (x, z, M.prop z x, 0)) (xLaw M) ∧
    (∫ o, RqBin dphi L e a.val.1 a.val.2 o ∂observationLaw M) =
      ∫ x, ∑ z, instProb M z x * RqBin dphi L e a.val.1 a.val.2
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
  have hw : ∀ᵐ o : Obs X Z ∂observationLaw M, o.2.2.1 ∈ Icc (0 : ℝ) 1 := by
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
    filter_upwards [hCb, hw] with o ho hw
    have hp := M.rangeProp o.2.1 o.1
    have hd : |o.2.2.1 - M.prop o.2.1 o.1| ≤ 2 := by
      rw [abs_le]
      constructor <;> linarith [hw.1, hw.2, hp.1, hp.2]
    simp only [Real.norm_eq_abs, abs_mul]
    gcongr
  have hmean := population_RqBin_fitted_finite_mean M h dphi L ep a hpc hdq htau hip hrp
  have heq : ∀ᵐ x ∂xLaw M, ∀ z, pc z x = e.prop z x := by
    filter_upwards [ae_all_iff.mpr he.1] with x hx
    intro z
    simp only [pc, min_eq_right (hx z).2, max_eq_right (hx z).1]
  have heqo : (fun o : Obs X Z => RqBin dphi L ep a.val.1 a.val.2 o)
      =ᵐ[observationLaw M] (fun o => RqBin dphi L e a.val.1 a.val.2 o) := by
    filter_upwards [observationLaw_covariate_ae M _ heq] with o ho
    rw [RqBin_fitted_residual_factorization dphi L ep a o,
      RqBin_fitted_residual_factorization dphi L e a o]
    change (e.tauLev a o.1)⁻¹ * indicator (o.2.1 ∈ L.T a.val.1 a.val.2) *
      dphi o.2.1 o.1 (pc o.2.1 o.1) * (o.2.2.1 - pc o.2.1 o.1) = _
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
  refine ⟨hmean.1.congr heqo, hif.congr hfeq, ?_⟩
  rw [← integral_congr_ae heqo, hmean.2]
  apply integral_congr_ae
  filter_upwards [heq] with x hx
  apply Finset.sum_congr rfl
  intro z _
  rw [RqBin_fitted_residual_factorization dphi L ep a (x,z,M.prop z x,0),
    RqBin_fitted_residual_factorization dphi L e a (x,z,M.prop z x,0)]
  change instProb M z x * ((e.tauLev a x)⁻¹ * indicator (z ∈ L.T a.val.1 a.val.2) *
    dphi z x (pc z x) * (M.prop z x - pc z x)) = _
  rw [hx z]

-- @node: pooledQBin_integrable_of_binary_admissible
/-- If [the policy is measurable and probability valued](hyp:hphi) and [the
binary nuisance is admissible](hyp:he), then [its fitted pooled policy level is
integrable under both the covariate and observation laws, with equal expectations
under these two laws](goal). -/
lemma pooledQBin_integrable_of_binary_admissible
    (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (L : LevelData Z X) (e : NuisanceBin L) (he : BinAdmissible M L e)
    (a : RegularIndex L) :
    Integrable (pooledQBin phi L e a.val.1 a.val.2) (xLaw M) ∧
    Integrable (fun o : Obs X Z => pooledQBin phi L e a.val.1 a.val.2 o.1)
      (observationLaw M) ∧
    (∫ o : Obs X Z, pooledQBin phi L e a.val.1 a.val.2 o.1 ∂observationLaw M) =
      ∫ x, pooledQBin phi L e a.val.1 a.val.2 x ∂xLaw M := by
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  let pc : Z → X → ℝ := fun z x => max 0 (min 1 (e.prop z x))
  have hpcR : ∀ z x, pc z x ∈ Icc (0 : ℝ) 1 := fun z x =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  let Q : X → ℝ := fun x => ∑ z ∈ L.T a.val.1 a.val.2,
    e.share a z x * phi z x (pc z x)
  have hQ : Measurable Q := by
    apply Finset.measurable_sum
    intro z hz
    have hm := he.2.1 z
    have hpc : Measurable (fun x => pc z x) := by dsimp only [pc]; fun_prop
    have hpol : Measurable (fun x => phi z x (pc z x)) :=
      hphi.1.comp (measurable_const.prodMk
        (measurable_id.prodMk (hpc.subtype_mk (h := hpcR z))))
    exact (he.2.2.2.2.2.2.2.1 a z).mul hpol
  have heq : Q =ᵐ[xLaw M] pooledQBin phi L e a.val.1 a.val.2 := by
    filter_upwards [ae_all_iff.mpr he.1] with x hx
    have hj0 : a.val.2 ≠ 0 := by have := a.property; omega
    have hj : ¬ L.l a.val.1 < a.val.2 := not_lt.mpr a.property.2.2
    simp only [pooledQBin, if_neg hj0, if_neg hj, dif_pos a.property, Q]
    apply Finset.sum_congr rfl
    intro z hz
    simp only [pc, min_eq_right (hx z).2, max_eq_right (hx z).1]
  have hiQ : Integrable Q (xLaw M) := by
    apply Integrable.of_bound hQ.aestronglyMeasurable (L.T a.val.1 a.val.2).card
    filter_upwards [ae_all_iff.mpr (he.2.2.2.2.2.2.1 a)] with x hx
    rw [Real.norm_eq_abs]
    calc
      _ ≤ ∑ z ∈ L.T a.val.1 a.val.2, |e.share a z x * phi z x (pc z x)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ z ∈ L.T a.val.1 a.val.2, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro z hz
        have hq := hphi.2 z x (pc z x) (hpcR z x)
        rw [abs_mul, abs_of_nonneg (hx z).1, abs_of_nonneg hq.1]
        exact mul_le_one₀ (hx z).2 hq.1 hq.2
      _ = _ := by simp
  have hi := hiQ.congr heq
  have hobs := M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY))
  have hmap : (observationLaw M).map Prod.fst = xLaw M := by
    simpa only [observationLaw, xLaw, Function.comp_def] using
      Measure.map_map measurable_fst hobs
  have him : Integrable (pooledQBin phi L e a.val.1 a.val.2)
      ((observationLaw M).map Prod.fst) := by rwa [hmap]
  refine ⟨hi, (integrable_map_measure him.aestronglyMeasurable
    measurable_fst.aemeasurable).mp him, ?_⟩
  rw [← hmap]
  exact (integral_map measurable_fst.aemeasurable him.aestronglyMeasurable).symm

-- @node: population_binary_pooled_observation_joint_orthogonality
/-- Under [the threshold-crossing model](hyp:h), suppose [the policy is measurable
and probability valued](hyp:hphi), [has the specified derivative](hyp:hDiff), and
[has a uniformly bounded Lipschitz derivative](hyp:hDerivative). With [invariant
ordering of baseline and policy levels](hyp:hOrder), [policy overlap](hyp:hov),
and [an admissible joint direction at the population nuisance](hyp:hd), [the
observation expectation of the perturbed pooled policy level plus the fitted
policy residual has derivative zero at zero](goal). -/
lemma population_binary_pooled_observation_joint_orthogonality
    (h : ThresholdCrossing M) (phi dphi : Z → X → ℝ → ℝ)
    (hphi : IsPolicyMap phi) (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : PolicyOverlap M L cpi) (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del))
    (a : RegularIndex L) :
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z,
      pooledQBin phi L (eta0Bin M L + t • del) a.val.1 a.val.2 o.1 +
        RqBin dphi L (eta0Bin M L + t • del) a.val.1 a.val.2 o
          ∂observationLaw M) 0 0 := by
  have hf := population_binary_pooled_joint_integral_orthogonality M
    phi dphi hphi hDiff hDerivative L hOrder cpi hov del hd a
  have hden : ∀ᵐ x ∂xLaw M, cpi ≤ (eta0Bin M L).tauLev a x := by
    apply Eventually.of_forall
    intro x
    exact hov.2 x a.val.1 a.val.2 a.property.1 a.property.2.1 a.property.2.2
      (ordered_policy_level_nonempty M (policyProp phi M.prop) L hOrder
        a.val.1 a.val.2 a.property.1 a.property.2.1 a.property.2.2)
  obtain ⟨r, hr, hadm⟩ := hd.admissible
  apply hf.congr_of_eventuallyEq
  filter_upwards [continuousAt_id.abs.eventually_lt_const (by simpa using hr),
    binary_pooled_denominator_uniform_neighborhood M L (eta0Bin M L) del hd a
      cpi hov.1 hden] with t ht hden
  have he := hadm t ht
  have hq := pooledQBin_integrable_of_binary_admissible M phi hphi L _ he a
  have hm := population_RqBin_finite_mean_of_binary_admissible M h phi dphi hphi hDiff
    hDerivative L _ he a (cpi/2) (by have := hov.1; positivity) hden
  rw [integral_add hq.2.1 hm.1, hq.2.2, hm.2.2]
  rw [integral_add hq.1 hm.2.1]

end Papers.TbsPrteOptimalTransport

module
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationSuccessResidual
/-! Population treatment and policy residuals centered by the structural conditional mean. -/
public section
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set
open scoped Classical

universe u v
variable {Ω : Type u} {X Z : Type v} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: population_treatment_conditional_mean
/-- Under [the threshold-crossing assumption](hyp:h), [the conditional mean of treatment
given instrument and covariates equals the structural propensity almost surely](goal). -/
lemma population_treatment_conditional_mean (h : ThresholdCrossing M) :
    M.law.toMeasure[M.W | MeasurableSpace.comap (fun s => (M.Zv s, M.Xv s))
      inferInstance] =ᵐ[M.law.toMeasure] (fun s => M.prop (M.Zv s) (M.Xv s)) := by
  have hi : Integrable M.W M.law.toMeasure := by
    apply (integrable_const (1 : ℝ)).mono' M.measW.aestronglyMeasurable
    filter_upwards [] with s
    rcases M.rangeW s with hs | hs <;> simp [hs]
  have hm := M.measZ.prodMk M.measX
  have hc := condExp_ae_eq_integral_condDistrib' hm hi
  have ht := ae_of_ae_map hm.aemeasurable h.2.2.2
  filter_upwards [hc, ht] with s hs ht
  exact hs.trans ht

-- The weight depends on the observed instrument and covariate, so this also
-- handles instrument-specific policy derivatives and pooled residuals.
-- @node: population_treatment_weighted_integral_zero
/-- Under [threshold crossing](hyp:h), if [an instrument-and-covariate weight is
measurable](hyp:hw) and [its product with treatment minus the structural propensity is
integrable](hyp:hi), then [the weighted treatment residual has population mean zero](goal). -/
lemma population_treatment_weighted_integral_zero (h : ThresholdCrossing M)
    (w : Z × X → ℝ) (hw : Measurable w)
    (hi : Integrable (fun o : Obs X Z => w (o.2.1, o.1) *
      (o.2.2.1 - M.prop o.2.1 o.1)) (observationLaw M)) :
    (∫ o : Obs X Z, w (o.2.1, o.1) * (o.2.2.1 - M.prop o.2.1 o.1)
      ∂observationLaw M) = 0 := by
  let f : Obs X Z → ℝ := fun o => w (o.2.1, o.1) *
    (o.2.2.1 - M.prop o.2.1 o.1)
  have hf : Measurable f := by
    dsimp only [f]
    exact (hw.comp (measurable_snd.fst.prodMk measurable_fst)).mul
      (measurable_snd.snd.fst.sub
        (h.2.1.comp (measurable_snd.fst.prodMk measurable_fst)))
  have hobs := M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY))
  have hi' : Integrable (fun s => f (M.Xv s, M.Zv s, M.W s, M.Y s))
      M.law.toMeasure :=
    (integrable_map_measure hf.aestronglyMeasurable hobs.aemeasurable).mp hi
  let m := MeasurableSpace.comap (fun s => (M.Zv s, M.Xv s)) inferInstance
  let : MeasurableSpace Ω := mΩ
  have hm : m ≤ mΩ := (M.measZ.prodMk M.measX).comap_le
  have hw' : StronglyMeasurable[m] (fun s => w (M.Zv s, M.Xv s)) :=
    hw.stronglyMeasurable.comp_measurable (comap_measurable _)
  have hp : StronglyMeasurable[m] (fun s => M.prop (M.Zv s) (M.Xv s)) :=
    h.2.1.stronglyMeasurable.comp_measurable (comap_measurable _)
  have hwi : Integrable M.W M.law.toMeasure := by
    apply (integrable_const (1 : ℝ)).mono' M.measW.aestronglyMeasurable
    filter_upwards [] with s
    rcases M.rangeW s with hs | hs <;> simp [hs]
  have hpi : Integrable (fun s => M.prop (M.Zv s) (M.Xv s)) M.law.toMeasure := by
    apply (integrable_const (1 : ℝ)).mono' (hp.mono hm).aestronglyMeasurable
    filter_upwards [] with s
    rw [Real.norm_eq_abs, abs_of_nonneg (M.rangeProp _ _).1]
    exact (M.rangeProp _ _).2
  have hz := score_weighted_conditional_residual_zero M.law.toMeasure m hm
    (fun s => w (M.Zv s, M.Xv s)) M.W (fun s => M.prop (M.Zv s) (M.Xv s))
    hw' hwi hpi hi' (population_treatment_conditional_mean M h) hp
  change (∫ o, f o ∂observationLaw M) = 0
  rw [observationLaw, integral_map hobs.aemeasurable hf.aestronglyMeasurable]
  exact hz

-- @node: population_Rp_weighted_integral_zero
/-- Under [threshold crossing](hyp:h) and [a common level ordering for baseline and policy
propensities](hyp:hOrder), if [a covariate weight is measurable](hyp:hw) and [its product
with the population binary level-treatment residual is integrable](hyp:hi), then
[that weighted residual has population mean zero](goal). -/
lemma population_Rp_weighted_integral_zero (h : ThresholdCrossing M)
    (q : Z → X → ℝ) (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop q L) (k : ℕ)
    (w : X → ℝ) (hw : Measurable w)
    (hi : Integrable (fun o : Obs X Z => w o.1 * Rp L (eta0Bin M L) k o)
      (observationLaw M)) :
    (∫ o : Obs X Z, w o.1 * Rp L (eta0Bin M L) k o ∂observationLaw M) = 0 := by
  by_cases hk : 1 ≤ k ∧ k ≤ L.K
  · have hk0 : k ≠ 0 := by omega
    let weight : Z × X → ℝ := fun zx => w zx.2 * indicator (zx.1 ∈ L.S k) /
      (levelSetProb M L).1 k zx.2
    have hpi : Measurable (fun x => (levelSetProb M L).1 k x) := by
      change Measurable (fun x => ∑ z ∈ L.S k, (M.instKernel x {z}).toReal)
      exact Finset.measurable_sum _ (fun z _ =>
        (Kernel.measurable_coe _ (measurableSet_singleton z)).ennreal_toReal)
    have hsel : MeasurableSet {zx : Z × X | zx.1 ∈ (L.S k : Set Z)} :=
      (L.S k).finite_toSet.measurableSet.preimage measurable_fst
    have hweight : Measurable weight := by
      dsimp only [weight]
      unfold indicator
      exact ((hw.comp measurable_snd).mul
        (Measurable.ite hsel measurable_const measurable_const)).div
          (hpi.comp measurable_snd)
    have hid : ∀ o : Obs X Z, w o.1 * Rp L (eta0Bin M L) k o =
        weight (o.2.1, o.1) * (o.2.2.1 - M.prop o.2.1 o.1) := by
      intro o
      simp only [Rp, if_neg hk0, positiveValue, dif_pos hk, eta0Bin, weight]
      by_cases hz : o.2.1 ∈ L.S k
      · have heq := (hOrder.2.2.2.2.2.1 o.1 k o.2.1 hk.2).mp hz
        rw [heq]
        ring
      · simp [indicator, hz]
    simp_rw [hid] at hi ⊢
    exact population_treatment_weighted_integral_zero M h weight hweight hi
  · have hz : ∀ o : Obs X Z, Rp L (eta0Bin M L) k o = 0 := by
      intro o
      by_cases hk0 : k = 0 <;> simp [Rp, hk0, positiveValue, hk]
    simp_rw [hz, mul_zero]
    simp

-- The continuous and binary scores use exactly the same treatment residual.
-- @node: population_RpCont_eq_Rp
/-- [At every level and observation, the continuous-score treatment residual at the true
nuisance equals the binary-score treatment residual at the population binary nuisance](goal). -/
lemma population_RpCont_eq_Rp (L : LevelData Z X) (k : ℕ) (o : Obs X Z) :
    RpCont L (trueNuisance M L) k o = Rp L (eta0Bin M L) k o := rfl

-- @node: population_RpCont_weighted_integral_zero
/-- Under [threshold crossing](hyp:h) and [a common level ordering for baseline and policy
propensities](hyp:hOrder), if [a covariate weight is measurable](hyp:hw) and [its product
with the population continuous level-treatment residual is integrable](hyp:hi), then
[that weighted residual has population mean zero](goal). -/
lemma population_RpCont_weighted_integral_zero (h : ThresholdCrossing M)
    (q : Z → X → ℝ) (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop q L) (k : ℕ)
    (w : X → ℝ) (hw : Measurable w)
    (hi : Integrable (fun o : Obs X Z => w o.1 * RpCont L (trueNuisance M L) k o)
      (observationLaw M)) :
    (∫ o : Obs X Z, w o.1 * RpCont L (trueNuisance M L) k o ∂observationLaw M) = 0 := by
  simp_rw [population_RpCont_eq_Rp] at hi ⊢
  exact population_Rp_weighted_integral_zero M h q L hOrder k w hw hi

-- Only the summand for the realized instrument survives. This algebraic
-- identity exposes the conditionally centered treatment residual.
-- @node: population_RqBin_residual_factorization
/-- [The population binary policy residual equals treatment minus the realized
instrument's structural propensity, multiplied by the policy derivative at that
propensity and the instrument's policy-cell indicator divided by the cell probability;
the multiplier is zero for a zero or out-of-range policy-cell index](goal). -/
lemma population_RqBin_residual_factorization (dphi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (k j : ℕ) (o : Obs X Z) :
    RqBin dphi L (eta0Bin M L) k j o =
      (if j = 0 ∨ L.l k < j then 0 else
        (regularValue (eta0Bin M L).tauLev k j o.1)⁻¹ *
          indicator (o.2.1 ∈ L.T k j) * dphi o.2.1 o.1 (M.prop o.2.1 o.1)) *
      (o.2.2.1 - M.prop o.2.1 o.1) := by
  unfold RqBin
  split_ifs with hj
  · simp
  · have hs : (∑ z ∈ L.T k j,
        dphi z o.1 (M.prop z o.1) * indicator (o.2.1 = z) *
          (o.2.2.1 - M.prop z o.1)) =
        indicator (o.2.1 ∈ L.T k j) * dphi o.2.1 o.1 (M.prop o.2.1 o.1) *
          (o.2.2.1 - M.prop o.2.1 o.1) := by
      classical
      have hid : ∀ z, dphi z o.1 (M.prop z o.1) * indicator (o.2.1 = z) *
          (o.2.2.1 - M.prop z o.1) =
          if o.2.1 = z then dphi o.2.1 o.1 (M.prop o.2.1 o.1) *
            (o.2.2.1 - M.prop o.2.1 o.1) else 0 := by
        intro z
        by_cases hz : o.2.1 = z
        · subst z
          simp [indicator]
        · simp [indicator, hz]
      simp_rw [hid]
      simp [indicator]
    change (regularValue (eta0Bin M L).tauLev k j o.1)⁻¹ *
        (∑ z ∈ L.T k j, dphi z o.1 (M.prop z o.1) * indicator (o.2.1 = z) *
          (o.2.2.1 - M.prop z o.1)) = _
    rw [hs]
    ring

-- @node: population_RqCont_eq_RqBin
/-- [For every level, policy-cell index, and observation, the continuous policy residual
at the true nuisance equals the binary policy residual at the population binary nuisance](goal). -/
lemma population_RqCont_eq_RqBin (dphi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (k j : ℕ) (o : Obs X Z) :
    RqCont dphi L (trueNuisance M L) k j o =
      RqBin dphi L (eta0Bin M L) k j o := rfl

-- @node: population_RqBin_weighted_integral_zero
/-- Under [threshold crossing](hyp:h), if [the policy derivative evaluated at the
structural propensity is measurable in instrument and covariates](hyp:hdphi), [the
covariate weight is measurable](hyp:hw), and [the weighted population binary policy
residual is integrable](hyp:hi), then [that weighted residual has population mean zero](goal). -/
lemma population_RqBin_weighted_integral_zero (h : ThresholdCrossing M)
    (dphi : Z → X → ℝ → ℝ)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (L : LevelData Z X) (k j : ℕ) (w : X → ℝ) (hw : Measurable w)
    (hi : Integrable (fun o : Obs X Z => w o.1 * RqBin dphi L (eta0Bin M L) k j o)
      (observationLaw M)) :
    (∫ o : Obs X Z, w o.1 * RqBin dphi L (eta0Bin M L) k j o
      ∂observationLaw M) = 0 := by
  let weight : Z × X → ℝ := fun zx => w zx.2 *
    (if j = 0 ∨ L.l k < j then 0 else
      (regularValue (eta0Bin M L).tauLev k j zx.2)⁻¹ *
        indicator (zx.1 ∈ L.T k j) * dphi zx.1 zx.2 (M.prop zx.1 zx.2))
  have htau : Measurable (fun x => regularValue (eta0Bin M L).tauLev k j x) := by
    unfold regularValue
    split_ifs
    · change Measurable (fun x => ∑ z ∈ L.T k j, (M.instKernel x {z}).toReal)
      exact Finset.measurable_sum _ (fun z _ =>
        (Kernel.measurable_coe _ (measurableSet_singleton z)).ennreal_toReal)
    · fun_prop
  have hweight : Measurable weight := by
    dsimp only [weight]
    split_ifs
    · fun_prop
    · have hsel : MeasurableSet {zx : Z × X | zx.1 ∈ (L.T k j : Set Z)} :=
        (L.T k j).finite_toSet.measurableSet.preimage measurable_fst
      have hind : Measurable (fun zx : Z × X => indicator (zx.1 ∈ L.T k j)) := by
        unfold indicator
        exact Measurable.ite hsel measurable_const measurable_const
      exact (hw.comp measurable_snd).mul
        (((htau.comp measurable_snd).inv.mul hind).mul hdphi)
  have hid : ∀ o : Obs X Z, w o.1 * RqBin dphi L (eta0Bin M L) k j o =
      weight (o.2.1, o.1) * (o.2.2.1 - M.prop o.2.1 o.1) := by
    intro o
    rw [population_RqBin_residual_factorization]
    dsimp only [weight]
    ring
  simp_rw [hid] at hi ⊢
  exact population_treatment_weighted_integral_zero M h weight hweight hi

-- @node: population_RqCont_weighted_integral_zero
/-- Under [threshold crossing](hyp:h), if [the policy derivative evaluated at the
structural propensity is measurable in instrument and covariates](hyp:hdphi), [the
covariate weight is measurable](hyp:hw), and [the weighted population continuous policy
residual is integrable](hyp:hi), then [that weighted residual has population mean zero](goal). -/
lemma population_RqCont_weighted_integral_zero (h : ThresholdCrossing M)
    (dphi : Z → X → ℝ → ℝ)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (L : LevelData Z X) (k j : ℕ) (w : X → ℝ) (hw : Measurable w)
    (hi : Integrable (fun o : Obs X Z => w o.1 * RqCont dphi L (trueNuisance M L) k j o)
      (observationLaw M)) :
    (∫ o : Obs X Z, w o.1 * RqCont dphi L (trueNuisance M L) k j o
      ∂observationLaw M) = 0 := by
  simp_rw [population_RqCont_eq_RqBin] at hi ⊢
  exact population_RqBin_weighted_integral_zero M h dphi hdphi L k j w hw hi

end Papers.TbsPrteOptimalTransport

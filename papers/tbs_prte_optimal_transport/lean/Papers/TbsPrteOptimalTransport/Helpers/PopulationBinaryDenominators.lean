module
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationBinaryWeightAssembly
public import Papers.TbsPrteOptimalTransport.Helpers.DenominatorOrthogonality
/-! Population residual centering with arbitrary measurable fitted denominators.

The numerators remain at the truth. Each result derives centering from the
constructed regression or treatment law, without assuming score orthogonality.
-/
public section
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set
open scoped Classical

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: population_RP_denominator_kernel_integral_zero
/-- [At each covariate value, the conditional mean of the population treated-success
residual is zero even after its level-probability denominator is replaced by an
arbitrary function](goal). -/
lemma population_RP_denominator_kernel_integral_zero (L : LevelData Z X) (pi : PositiveIndex L.K → X → ℝ)
    (k : ℕ) (x : X) :
    (∫ a : ℝ × ℝ × Z, RP L ({eta0Bin M L with piLev := pi}) k (x, a.2.2, a.2.1, a.1)
      ∂condDistrib (fun s => (M.Y s, M.W s, M.Zv s)) M.Xv M.law.toMeasure x) = 0 := by
  by_cases hk : 1 ≤ k ∧ k ≤ L.K
  · have hk0 : k ≠ 0 := by omega
    let C : Set (ℝ × ℝ × Z) := {a | a.2.2 ∈ (L.S k : Set Z)}
    have hC : MeasurableSet C :=
      (L.S k).finite_toSet.measurableSet.preimage (measurable_snd.comp measurable_snd)
    have hid : (fun a : ℝ × ℝ × Z => RP L ({eta0Bin M L with piLev := pi}) k (x, a.2.2, a.2.1, a.1)) =
        (fun a => (positiveValue ({eta0Bin M L with piLev := pi}).piLev k x)⁻¹ *
          C.indicator (fun a => a.1 * a.2.1 - treatedSuccess M L k x) a) := by
      funext a
      simp only [RP, if_neg hk0, positiveValue, dif_pos hk, eta0Bin]
      simp [indicator, C, Set.indicator, div_eq_mul_inv]
    rw [hid, integral_const_mul, integral_indicator hC,
      treatedSuccess_eq_selected_average M L k hk0 x, integral_sub_average, mul_zero]
  · have hz : ∀ a : ℝ × ℝ × Z,
        RP L ({eta0Bin M L with piLev := pi}) k (x, a.2.2, a.2.1, a.1) = 0 := by
      intro a
      by_cases hk0 : k = 0
      · simp [RP, hk0]
      · simp [RP, hk0, positiveValue, hk]
    simp_rw [hz]
    simp

-- @node: population_RP_denominator_measurable
/-- If [every replacement level-probability denominator is measurable](hyp:hpi), then
[the treated-success residual with population numerators and these replacement
denominators is measurable as a function of the observation](goal). -/
@[fun_prop] lemma population_RP_denominator_measurable (L : LevelData Z X) (pi : PositiveIndex L.K → X → ℝ) (hpi : ∀ a, Measurable (pi a)) (k : ℕ) :
    Measurable (RP L ({eta0Bin M L with piLev := pi}) k) := by
  first
  | fun_prop
  |
    have hsel : MeasurableSet {o : Obs X Z | o.2.1 ∈ (L.S k : Set Z)} :=
      (L.S k).finite_toSet.measurableSet.preimage (measurable_fst.comp measurable_snd)
    have hi : Measurable (fun o : Obs X Z => indicator (o.2.1 ∈ L.S k)) := by
      unfold indicator
      exact Measurable.ite hsel measurable_const measurable_const
    by_cases hk : 1 ≤ k ∧ k ≤ L.K
    · have hk0 : k ≠ 0 := by omega
      change Measurable (fun o => RP L ({eta0Bin M L with piLev := pi}) k o)
      simp only [RP, if_neg hk0, positiveValue, dif_pos hk, eta0Bin]
      exact (hi.div ((hpi ⟨k, hk⟩).comp measurable_fst)).mul
        ((measurable_snd.snd.snd.mul measurable_snd.snd.fst).sub
          ((treatedSuccess_measurable M L k).comp measurable_fst))
    · have hz : RP L ({eta0Bin M L with piLev := pi}) k = (fun _ => (0 : ℝ)) := by
        funext o
        by_cases hk0 : k = 0 <;> simp [RP, hk0, positiveValue, hk]
      rw [hz]
      fun_prop

-- Tower property for the constructed population regression. Covariate weights
-- may be signed; integrability is the sole analytic requirement on the product.
-- @node: population_RP_denominator_weighted_integral_zero
/-- If [the replacement level-probability denominators are measurable](hyp:hpi), [the
covariate weight is measurable](hyp:hw), and [the weighted treated-success residual
with these denominators and population numerators is integrable](hyp:hi), then
[that weighted residual has population mean zero](goal). -/
lemma population_RP_denominator_weighted_integral_zero (L : LevelData Z X) (pi : PositiveIndex L.K → X → ℝ)
    (hpi : ∀ a, Measurable (pi a)) (k : ℕ)
    (w : X → ℝ) (hw : Measurable w)
    (hi : Integrable (fun o : Obs X Z => w o.1 * RP L ({eta0Bin M L with piLev := pi}) k o)
      (observationLaw M)) :
    (∫ o : Obs X Z, w o.1 * RP L ({eta0Bin M L with piLev := pi}) k o ∂observationLaw M) = 0 := by
  let f : Obs X Z → ℝ := fun o => w o.1 * RP L ({eta0Bin M L with piLev := pi}) k o
  have hf : Measurable f := by
    dsimp only [f]
    exact (hw.comp measurable_fst).mul
      (population_RP_denominator_measurable M L pi hpi k)
  have hobs : Measurable (fun s => (M.Xv s, M.Zv s, M.W s, M.Y s)) := by
    first | fun_prop | exact M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY))
  have hi' : Integrable (fun s => f (M.Xv s, M.Zv s, M.W s, M.Y s)) M.law.toMeasure :=
    (integrable_map_measure hf.aestronglyMeasurable hobs.aemeasurable).mp hi
  have hjoint : Measurable (fun s => (M.Y s, M.W s, M.Zv s)) := by
    first | fun_prop | exact M.measY.prodMk (M.measW.prodMk M.measZ)
  have hpair : StronglyMeasurable (fun p : X × (ℝ × ℝ × Z) =>
      f (p.1, p.2.2.2, p.2.2.1, p.2.1)) := by
    fun_prop
  have hc := condExp_prod_ae_eq_integral_condDistrib M.measX hjoint.aemeasurable hpair hi'
  have hz : M.law.toMeasure[(fun s => f (M.Xv s, M.Zv s, M.W s, M.Y s)) |
      MeasurableSpace.comap M.Xv inferInstance] =ᵐ[M.law.toMeasure] (fun _ => (0 : ℝ)) := by
    filter_upwards [hc] with s hs
    rw [hs]
    dsimp only [f]
    rw [integral_const_mul, population_RP_denominator_kernel_integral_zero, mul_zero]
  change (∫ o, f o ∂observationLaw M) = 0
  calc
    _ = ∫ s, f (M.Xv s, M.Zv s, M.W s, M.Y s) ∂M.law.toMeasure :=
      integral_map hobs.aemeasurable hf.aestronglyMeasurable
    _ = ∫ s, M.law.toMeasure[(fun s => f (M.Xv s, M.Zv s, M.W s, M.Y s)) |
        MeasurableSpace.comap M.Xv inferInstance] s ∂M.law.toMeasure :=
      (integral_condExp M.measX.comap_le).symm
    _ = ∫ _ : Ω, (0 : ℝ) ∂M.law.toMeasure := integral_congr_ae hz
    _ = 0 := by simp


-- @node: population_Rp_denominator_weighted_integral_zero
/-- Under [threshold crossing](hyp:h) and [invariant baseline and policy level ordering](hyp:hOrder),
if [the replacement baseline-level probability denominators are measurable](hyp:hpi),
[the covariate weight is measurable](hyp:hw), and [the weighted baseline treatment
residual with these denominators and population numerators is integrable](hyp:hi),
then [this weighted treatment residual has population mean zero](goal). -/
lemma population_Rp_denominator_weighted_integral_zero (h : ThresholdCrossing M)
    (q : Z → X → ℝ) (L : LevelData Z X) (pi : PositiveIndex L.K → X → ℝ)
    (hpi : ∀ a, Measurable (pi a))
    (hOrder : LevelOrderInvariant M.prop q L) (k : ℕ)
    (w : X → ℝ) (hw : Measurable w)
    (hi : Integrable (fun o : Obs X Z => w o.1 * Rp L ({eta0Bin M L with piLev := pi}) k o)
      (observationLaw M)) :
    (∫ o : Obs X Z, w o.1 * Rp L ({eta0Bin M L with piLev := pi}) k o ∂observationLaw M) = 0 := by
  by_cases hk : 1 ≤ k ∧ k ≤ L.K
  · have hk0 : k ≠ 0 := by omega
    let weight : Z × X → ℝ := fun zx => w zx.2 * indicator (zx.1 ∈ L.S k) /
      pi ⟨k, hk⟩ zx.2
    have hsel : MeasurableSet {zx : Z × X | zx.1 ∈ (L.S k : Set Z)} :=
      (L.S k).finite_toSet.measurableSet.preimage measurable_fst
    have hweight : Measurable weight := by
      dsimp only [weight]
      unfold indicator
      exact ((hw.comp measurable_snd).mul
        (Measurable.ite hsel measurable_const measurable_const)).div
          ((hpi ⟨k, hk⟩).comp measurable_snd)
    have hid : ∀ o : Obs X Z, w o.1 * Rp L ({eta0Bin M L with piLev := pi}) k o =
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
  · have hz : ∀ o : Obs X Z, Rp L ({eta0Bin M L with piLev := pi}) k o = 0 := by
      intro o
      by_cases hk0 : k = 0 <;> simp [Rp, hk0, positiveValue, hk]
    simp_rw [hz, mul_zero]
    simp

-- @node: population_RqBin_denominator_residual_factorization
/-- [The population policy-level residual with replacement policy-class denominators
equals treatment minus its true propensity, multiplied by the policy derivative at
that propensity and the policy-class indicator, divided by the replacement class
probability; the multiplier is zero for a zero or out-of-range policy index](goal). -/
lemma population_RqBin_denominator_residual_factorization (dphi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (tau : RegularIndex L → X → ℝ) (k j : ℕ) (o : Obs X Z) :
    RqBin dphi L ({eta0Bin M L with tauLev := tau}) k j o =
      (if j = 0 ∨ L.l k < j then 0 else
        (regularValue ({eta0Bin M L with tauLev := tau}).tauLev k j o.1)⁻¹ *
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
    change (regularValue ({eta0Bin M L with tauLev := tau}).tauLev k j o.1)⁻¹ *
        (∑ z ∈ L.T k j, dphi z o.1 (M.prop z o.1) * indicator (o.2.1 = z) *
          (o.2.2.1 - M.prop z o.1)) = _
    rw [hs]
    ring

-- @node: population_RqBin_denominator_weighted_integral_zero
/-- Under [threshold crossing](hyp:h), if [the policy derivative evaluated at the true
propensity is measurable](hyp:hdphi), [the replacement policy-class denominators are
measurable](hyp:htau), [the covariate weight is measurable](hyp:hw), and [the weighted
policy residual with these denominators and population numerators is integrable](hyp:hi),
then [this weighted policy residual has population mean zero](goal). -/
lemma population_RqBin_denominator_weighted_integral_zero (h : ThresholdCrossing M)
    (dphi : Z → X → ℝ → ℝ)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (L : LevelData Z X) (tau : RegularIndex L → X → ℝ)
    (htau : ∀ a, Measurable (tau a)) (k j : ℕ) (w : X → ℝ) (hw : Measurable w)
    (hi : Integrable (fun o : Obs X Z => w o.1 * RqBin dphi L ({eta0Bin M L with tauLev := tau}) k j o)
      (observationLaw M)) :
    (∫ o : Obs X Z, w o.1 * RqBin dphi L ({eta0Bin M L with tauLev := tau}) k j o
      ∂observationLaw M) = 0 := by
  let weight : Z × X → ℝ := fun zx => w zx.2 *
    (if j = 0 ∨ L.l k < j then 0 else
      (regularValue ({eta0Bin M L with tauLev := tau}).tauLev k j zx.2)⁻¹ *
        indicator (zx.1 ∈ L.T k j) * dphi zx.1 zx.2 (M.prop zx.1 zx.2))
  have htau : Measurable (fun x => regularValue ({eta0Bin M L with tauLev := tau}).tauLev k j x) := by
    unfold regularValue
    split_ifs
    · exact htau _
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
  have hid : ∀ o : Obs X Z, w o.1 * RqBin dphi L ({eta0Bin M L with tauLev := tau}) k j o =
      weight (o.2.1, o.1) * (o.2.2.1 - M.prop o.2.1 o.1) := by
    intro o
    rw [population_RqBin_denominator_residual_factorization]
    dsimp only [weight]
    ring
  simp_rw [hid] at hi ⊢
  exact population_treatment_weighted_integral_zero M h weight hweight hi


-- @node: population_binary_denominator_component_correction_zero
/-- Under [threshold crossing](hyp:h), [measurability of the policy derivative at the true
propensity](hyp:hdphi), and [invariant level ordering](hyp:hOrder), suppose [the replacement
baseline-class denominators](hyp:hpi), [replacement policy-class denominators](hyp:htau),
and [covariate weight](hyp:hw) are measurable, as are the resulting [interior-boundary](hyp:hD),
[dominance](hyp:hE), and [active-set indicators](hyp:hI). If the weighted [upper and lower
treated-success residuals](hyp:hPplus,hPminus), [upper and lower treatment residuals](hyp:hpplus,hpminus),
and [upper and preceding policy residuals](hyp:hqplus,hqminus) are integrable with these
denominators, then [the weighted component score minus its positive-part term is
integrable and has mean zero](goal). -/
lemma population_binary_denominator_component_correction_zero (h : ThresholdCrossing M)
    (phi dphi : Z → X → ℝ → ℝ)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (L : LevelData Z X) (pi : PositiveIndex L.K → X → ℝ)
    (tau : RegularIndex L → X → ℝ)
    (hpi : ∀ a, Measurable (pi a)) (htau : ∀ a, Measurable (tau a))
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (k j : ℕ) (w : X → ℝ) (hw : Measurable w)
    (hD : Measurable (Dbd phi L ({eta0Bin M L with piLev := pi, tauLev := tau}) k j))
    (hE : Measurable (Edom phi L ({eta0Bin M L with piLev := pi, tauLev := tau}) k j))
    (hI : Measurable (Iact phi L ({eta0Bin M L with piLev := pi, tauLev := tau}) k j))
    (hPplus : Integrable (fun o : Obs X Z => w o.1 * RP L ({eta0Bin M L with piLev := pi, tauLev := tau}) (k + 1) o)
      (observationLaw M))
    (hPminus : Integrable (fun o : Obs X Z => w o.1 * RP L ({eta0Bin M L with piLev := pi, tauLev := tau}) k o)
      (observationLaw M))
    (hpplus : Integrable (fun o : Obs X Z => w o.1 * Rp L ({eta0Bin M L with piLev := pi, tauLev := tau}) (k + 1) o)
      (observationLaw M))
    (hpminus : Integrable (fun o : Obs X Z => w o.1 * Rp L ({eta0Bin M L with piLev := pi, tauLev := tau}) k o)
      (observationLaw M))
    (hqplus : Integrable (fun o : Obs X Z => w o.1 * RqBin dphi L ({eta0Bin M L with piLev := pi, tauLev := tau}) k j o)
      (observationLaw M))
    (hqminus : Integrable (fun o : Obs X Z => w o.1 * RqBin dphi L ({eta0Bin M L with piLev := pi, tauLev := tau}) k (j - 1) o)
      (observationLaw M)) :
    Integrable (fun o : Obs X Z => w o.1 *
      (binScoreComponents phi dphi L ({eta0Bin M L with piLev := pi, tauLev := tau}) k j o - hMinus phi L ({eta0Bin M L with piLev := pi, tauLev := tau}) k j o.1))
      (observationLaw M) ∧
    (∫ o : Obs X Z, w o.1 *
      (binScoreComponents phi dphi L ({eta0Bin M L with piLev := pi, tauLev := tau}) k j o - hMinus phi L ({eta0Bin M L with piLev := pi, tauLev := tau}) k j o.1)
      ∂observationLaw M) = 0 := by
  let D := Dbd phi L ({eta0Bin M L with piLev := pi, tauLev := tau}) k j
  let E := Edom phi L ({eta0Bin M L with piLev := pi, tauLev := tau}) k j
  let I := Iact phi L ({eta0Bin M L with piLev := pi, tauLev := tau}) k j
  have hEI : Measurable (fun x => E x * I x) := hE.mul hI
  have hDb : ∀ x, ‖D x‖ ≤ 1 := by
    intro x
    simp only [D, Dbd, indicator]
    split_ifs <;> norm_num
  have hIb : ∀ x, ‖I x‖ ≤ 1 := by
    intro x
    simp only [I, Iact, indicator]
    split_ifs <;> norm_num
  have hEIb : ∀ x, ‖E x * I x‖ ≤ 1 := by
    intro x
    simp only [E, I, Edom, Iact, indicator]
    split_ifs <;> norm_num
  have hmul (c : X → ℝ) (hc : Measurable c) (hcb : ∀ x, ‖c x‖ ≤ 1)
      (r : Obs X Z → ℝ) (hr : Integrable (fun o => w o.1 * r o) (observationLaw M)) :
      Integrable (fun o => (w o.1 * c o.1) * r o) (observationLaw M) := by
    have hi := hr.bdd_mul (hc.comp measurable_fst).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun o : Obs X Z => hcb o.1))
    convert hi using 1
    ext o
    simp only [Function.comp_apply]
    ring
  have iPp := hmul D hD hDb _ hPplus
  have iPm := hmul D hD hDb _ hPminus
  have ipp := hmul D hD hDb _ hpplus
  have ipm := hmul (fun x => E x * I x) hEI hEIb _ hpminus
  have iqp := hmul I hI hIb _ hqplus
  have iqm := hmul (fun x => E x * I x) hEI hEIb _ hqminus
  have zPp := population_RP_denominator_weighted_integral_zero M L pi hpi (k + 1) (fun x => w x * D x) (hw.mul hD) iPp
  have zPm := population_RP_denominator_weighted_integral_zero M L pi hpi k (fun x => w x * D x) (hw.mul hD) iPm
  have zpp := population_Rp_denominator_weighted_integral_zero M h (policyProp phi M.prop) L pi hpi hOrder (k + 1)
    (fun x => w x * D x) (hw.mul hD) ipp
  have zpm := population_Rp_denominator_weighted_integral_zero M h (policyProp phi M.prop) L pi hpi hOrder k
    (fun x => w x * (E x * I x)) (hw.mul hEI) ipm
  have zqp := population_RqBin_denominator_weighted_integral_zero M h dphi hdphi L tau htau k j
    (fun x => w x * I x) (hw.mul hI) iqp
  have zqm := population_RqBin_denominator_weighted_integral_zero M h dphi hdphi L tau htau k (j - 1)
    (fun x => w x * (E x * I x)) (hw.mul hEI) iqm
  change (∫ o : Obs X Z, w o.1 * D o.1 * RP L
    {eta0Bin M L with piLev := pi, tauLev := tau} (k + 1) o ∂observationLaw M) = 0 at zPp
  change (∫ o : Obs X Z, w o.1 * D o.1 * RP L
    {eta0Bin M L with piLev := pi, tauLev := tau} k o ∂observationLaw M) = 0 at zPm
  change (∫ o : Obs X Z, w o.1 * D o.1 * Rp L
    {eta0Bin M L with piLev := pi, tauLev := tau} (k + 1) o ∂observationLaw M) = 0 at zpp
  change (∫ o : Obs X Z, w o.1 * (E o.1 * I o.1) * Rp L
    {eta0Bin M L with piLev := pi, tauLev := tau} k o ∂observationLaw M) = 0 at zpm
  change (∫ o : Obs X Z, w o.1 * I o.1 * RqBin dphi L
    {eta0Bin M L with piLev := pi, tauLev := tau} k j o ∂observationLaw M) = 0 at zqp
  change (∫ o : Obs X Z, w o.1 * (E o.1 * I o.1) * RqBin dphi L
    {eta0Bin M L with piLev := pi, tauLev := tau} k (j - 1) o ∂observationLaw M) = 0 at zqm
  let low := fun o : Obs X Z => if j = 1 then
    (w o.1 * (E o.1 * I o.1)) * Rp L ({eta0Bin M L with piLev := pi, tauLev := tau}) k o else 0
  have ilow : Integrable low (observationLaw M) := by
    dsimp only [low]
    split_ifs
    · exact ipm
    · exact integrable_zero _ _ _
  have zlow : (∫ o, low o ∂observationLaw M) = 0 := by
    dsimp only [low]
    split_ifs
    · exact zpm
    · simp
  have hid : (fun o : Obs X Z => w o.1 *
      (binScoreComponents phi dphi L ({eta0Bin M L with piLev := pi, tauLev := tau}) k j o - hMinus phi L ({eta0Bin M L with piLev := pi, tauLev := tau}) k j o.1)) =
      (fun o => (w o.1 * D o.1) * RP L ({eta0Bin M L with piLev := pi, tauLev := tau}) (k + 1) o -
        (w o.1 * D o.1) * RP L ({eta0Bin M L with piLev := pi, tauLev := tau}) k o -
        (w o.1 * D o.1) * Rp L ({eta0Bin M L with piLev := pi, tauLev := tau}) (k + 1) o - low o +
        (w o.1 * I o.1) * RqBin dphi L ({eta0Bin M L with piLev := pi, tauLev := tau}) k j o -
        (w o.1 * (E o.1 * I o.1)) * RqBin dphi L ({eta0Bin M L with piLev := pi, tauLev := tau}) k (j - 1) o) := by
    funext o
    dsimp only [binScoreComponents, D, E, I, low]
    split_ifs <;> ring
  rw [hid]
  refine ⟨(((iPp.sub' iPm).sub' ipp).sub' ilow).fun_add iqp |>.sub' iqm, ?_⟩
  rw [integral_sub ((((iPp.sub' iPm).sub' ipp).sub' ilow).fun_add iqp) iqm,
    integral_add (((iPp.sub' iPm).sub' ipp).sub' ilow) iqp,
    integral_sub ((iPp.sub' iPm).sub' ipp) ilow,
    integral_sub (iPp.sub' iPm) ipp, integral_sub iPp iPm,
    zPp, zPm, zpp, zlow, zqp, zqm]
  ring

-- @node: population_binary_denominator_component_weighted_mean
/-- Under [threshold crossing](hyp:h), [measurability of the policy derivative at the true
propensity](hyp:hdphi), and [invariant level ordering](hyp:hOrder), assume measurable
[replacement baseline-class denominators](hyp:hpi), [replacement policy-class denominators](hyp:htau),
[covariate weight](hyp:hw), [interior-boundary indicator](hyp:hD), [dominance indicator](hyp:hE),
and [active-set indicator](hyp:hI). If the weighted [upper and lower treated-success
residuals](hyp:hPplus,hPminus), [upper and lower treatment residuals](hyp:hpplus,hpminus),
[upper and preceding policy residuals](hyp:hqplus,hqminus), and [positive-part term](hyp:hh)
are integrable, then [the weighted component score with the replacement denominators
has the same mean as its weighted positive-part term](goal). -/
lemma population_binary_denominator_component_weighted_mean (h : ThresholdCrossing M)
    (phi dphi : Z → X → ℝ → ℝ)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (L : LevelData Z X) (pi : PositiveIndex L.K → X → ℝ)
    (tau : RegularIndex L → X → ℝ)
    (hpi : ∀ a, Measurable (pi a)) (htau : ∀ a, Measurable (tau a))
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (k j : ℕ) (w : X → ℝ) (hw : Measurable w)
    (hD : Measurable (Dbd phi L ({eta0Bin M L with piLev := pi, tauLev := tau}) k j))
    (hE : Measurable (Edom phi L ({eta0Bin M L with piLev := pi, tauLev := tau}) k j))
    (hI : Measurable (Iact phi L ({eta0Bin M L with piLev := pi, tauLev := tau}) k j))
    (hPplus : Integrable (fun o : Obs X Z => w o.1 * RP L ({eta0Bin M L with piLev := pi, tauLev := tau}) (k + 1) o)
      (observationLaw M))
    (hPminus : Integrable (fun o : Obs X Z => w o.1 * RP L ({eta0Bin M L with piLev := pi, tauLev := tau}) k o)
      (observationLaw M))
    (hpplus : Integrable (fun o : Obs X Z => w o.1 * Rp L ({eta0Bin M L with piLev := pi, tauLev := tau}) (k + 1) o)
      (observationLaw M))
    (hpminus : Integrable (fun o : Obs X Z => w o.1 * Rp L ({eta0Bin M L with piLev := pi, tauLev := tau}) k o)
      (observationLaw M))
    (hqplus : Integrable (fun o : Obs X Z => w o.1 * RqBin dphi L ({eta0Bin M L with piLev := pi, tauLev := tau}) k j o)
      (observationLaw M))
    (hqminus : Integrable (fun o : Obs X Z => w o.1 * RqBin dphi L ({eta0Bin M L with piLev := pi, tauLev := tau}) k (j - 1) o)
      (observationLaw M))
    (hh : Integrable (fun o : Obs X Z => w o.1 * hMinus phi L ({eta0Bin M L with piLev := pi, tauLev := tau}) k j o.1)
      (observationLaw M)) :
    (∫ o : Obs X Z, w o.1 * binScoreComponents phi dphi L ({eta0Bin M L with piLev := pi, tauLev := tau}) k j o
      ∂observationLaw M) =
      ∫ o : Obs X Z, w o.1 * hMinus phi L ({eta0Bin M L with piLev := pi, tauLev := tau}) k j o.1 ∂observationLaw M := by
  obtain ⟨hi, hz⟩ := population_binary_denominator_component_correction_zero M h phi dphi hdphi L pi tau hpi htau hOrder
    k j w hw hD hE hI hPplus hPminus hpplus hpminus hqplus hqminus
  have hid : (fun o : Obs X Z => w o.1 * binScoreComponents phi dphi L ({eta0Bin M L with piLev := pi, tauLev := tau}) k j o) =
      (fun o => w o.1 * hMinus phi L ({eta0Bin M L with piLev := pi, tauLev := tau}) k j o.1 + w o.1 *
        (binScoreComponents phi dphi L ({eta0Bin M L with piLev := pi, tauLev := tau}) k j o -
          hMinus phi L ({eta0Bin M L with piLev := pi, tauLev := tau}) k j o.1)) := by
    funext o
    ring
  rw [hid, integral_add hh hi, hz, add_zero]


-- Every denominator correction stays centered along the entire path.
-- The integrability inputs concern primitive residuals, not score derivatives.
-- @node: population_binary_component_denominator_path_orthogonality
/-- Under [threshold crossing](hyp:h), [measurability of the policy derivative at the true
propensity](hyp:hdphi), and [invariant level ordering](hyp:hOrder), suppose [the baseline-class
denominator path](hyp:hpi) and [policy-class denominator path](hyp:htau) are measurable
in covariates at every path value. If [the covariate weight](hyp:hw), [interior-boundary
indicator](hyp:hD), [dominance indicator](hyp:hE), and [active-set indicator](hyp:hI) are
measurable, [all six weighted treated-success, treatment, and policy residuals are
integrable at every path value](hyp:hInt), and [the weighted population positive-part
term is integrable](hyp:hh), then [the mean weighted component score has derivative
zero at zero along the denominator path](goal). -/
lemma population_binary_component_denominator_path_orthogonality
    (h : ThresholdCrossing M) (phi dphi : Z → X → ℝ → ℝ)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (L : LevelData Z X) (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (pi : ℝ → PositiveIndex L.K → X → ℝ) (tau : ℝ → RegularIndex L → X → ℝ)
    (hpi : ∀ t a, Measurable (pi t a)) (htau : ∀ t a, Measurable (tau t a))
    (k j : ℕ) (w : X → ℝ) (hw : Measurable w)
    (hD : Measurable (Dbd phi L (eta0Bin M L) k j))
    (hE : Measurable (Edom phi L (eta0Bin M L) k j))
    (hI : Measurable (Iact phi L (eta0Bin M L) k j))
    (hInt : ∀ t : ℝ,
      let et := {eta0Bin M L with piLev := pi t, tauLev := tau t}
      Integrable (fun o : Obs X Z => w o.1 * RP L et (k+1) o) (observationLaw M) ∧
      Integrable (fun o : Obs X Z => w o.1 * RP L et k o) (observationLaw M) ∧
      Integrable (fun o : Obs X Z => w o.1 * Rp L et (k+1) o) (observationLaw M) ∧
      Integrable (fun o : Obs X Z => w o.1 * Rp L et k o) (observationLaw M) ∧
      Integrable (fun o : Obs X Z => w o.1 * RqBin dphi L et k j o) (observationLaw M) ∧
      Integrable (fun o : Obs X Z => w o.1 * RqBin dphi L et k (j-1) o) (observationLaw M))
    (hh : Integrable (fun o : Obs X Z => w o.1 * hMinus phi L (eta0Bin M L) k j o.1)
      (observationLaw M)) :
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z, w o.1 * binScoreComponents phi dphi L
      {eta0Bin M L with piLev := pi t, tauLev := tau t} k j o ∂observationLaw M) 0 0 := by
  have heq : (fun t : ℝ => ∫ o : Obs X Z, w o.1 * binScoreComponents phi dphi L
      {eta0Bin M L with piLev := pi t, tauLev := tau t} k j o ∂observationLaw M) =
      (fun _ : ℝ => ∫ o : Obs X Z, w o.1 * hMinus phi L (eta0Bin M L) k j o.1
        ∂observationLaw M) := by
    funext t
    obtain ⟨iPp, iPm, ipp, ipm, iqp, iqm⟩ := hInt t
    exact population_binary_denominator_component_weighted_mean M h phi dphi hdphi
      L (pi t) (tau t) (hpi t) (htau t) hOrder k j w hw hD hE hI
      iPp iPm ipp ipm iqp iqm hh
  rw [heq]
  exact hasDerivAt_const 0 _

end Papers.TbsPrteOptimalTransport

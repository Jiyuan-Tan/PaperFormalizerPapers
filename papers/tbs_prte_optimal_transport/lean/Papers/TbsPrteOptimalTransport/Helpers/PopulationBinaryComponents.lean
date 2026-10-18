module
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationTreatmentResidual
public import Papers.TbsPrteOptimalTransport.Helpers.RegularProductOrthogonality
/-! Population centering and product-weight cancellation for binary subinterval scores. -/
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
  [Nonempty X] [Nonempty Z]
variable (M : LatentIVModel Ω X Z)

-- @node: binary_Dbd_measurable
/-- If [the upper pooled policy level is measurable](hyp:hq), [the preceding pooled
policy level is measurable](hyp:hl), and [the upper baseline propensity minus the
full-interval treated-success increment is measurable](hyp:hb), then [the indicator
that this boundary lies strictly between the two pooled levels is measurable](goal). -/
@[fun_prop] lemma binary_Dbd_measurable
    (phi : Z → X → ℝ → ℝ) (L : LevelData Z X) (e : NuisanceBin L) (k j : ℕ)
    (hq : Measurable (pooledQBin phi L e k j))
    (hl : Measurable (pooledQBin phi L e k (j - 1)))
    (hb : Measurable (fun x => positiveValue e.pLev (k + 1) x - binFullJ L e k x)) :
    Measurable (Dbd phi L e k j) := by
  unfold Dbd indicator
  exact Measurable.ite ((measurableSet_lt hl hb).inter (measurableSet_lt hb hq))
    measurable_const measurable_const

-- @node: binary_Edom_measurable
/-- If [the preceding pooled policy level is measurable](hyp:hl) and [the upper baseline
propensity minus the full-interval treated-success increment is measurable](hyp:hb),
then [the indicator that the preceding pooled level strictly exceeds this boundary
is measurable](goal). -/
@[fun_prop] lemma binary_Edom_measurable
    (phi : Z → X → ℝ → ℝ) (L : LevelData Z X) (e : NuisanceBin L) (k j : ℕ)
    (hl : Measurable (pooledQBin phi L e k (j - 1)))
    (hb : Measurable (fun x => positiveValue e.pLev (k + 1) x - binFullJ L e k x)) :
    Measurable (Edom phi L e k j) := by
  unfold Edom indicator
  exact Measurable.ite (measurableSet_lt hb hl) measurable_const measurable_const

-- @node: binary_Iact_measurable
/-- If [the upper pooled policy level is measurable](hyp:hq), [the preceding pooled level
is measurable](hyp:hl), and [the upper baseline propensity minus the full-interval
treated-success increment is measurable](hyp:hb), then [the indicator that the upper
pooled level strictly exceeds both lower boundaries is measurable](goal). -/
@[fun_prop] lemma binary_Iact_measurable
    (phi : Z → X → ℝ → ℝ) (L : LevelData Z X) (e : NuisanceBin L) (k j : ℕ)
    (hq : Measurable (pooledQBin phi L e k j))
    (hl : Measurable (pooledQBin phi L e k (j - 1)))
    (hb : Measurable (fun x => positiveValue e.pLev (k + 1) x - binFullJ L e k x)) :
    Measurable (Iact phi L e k j) := by
  unfold Iact indicator
  exact Measurable.ite (measurableSet_lt (hl.max hb) hq) measurable_const measurable_const

variable [Fintype Z] [DecidableEq Z]

-- Every branch coefficient is bounded by one. Thus integrability of the
-- covariate-weighted primitive residuals suffices for all six corrections.
-- @node: population_binary_component_correction_zero
/-- Under [threshold crossing](hyp:h), [measurability of the policy derivative evaluated
at the true propensity](hyp:hdphi), and [invariant baseline and policy level ordering](hyp:hOrder),
suppose [the covariate weight is measurable](hyp:hw), [the interior-boundary indicator
is measurable](hyp:hD), [the dominance indicator is measurable](hyp:hE), and [the active-set
indicator is measurable](hyp:hI). If the weighted [treated-success residuals at the
upper and lower baseline levels are integrable](hyp:hPplus,hPminus), [treatment residuals
at those levels are integrable](hyp:hpplus,hpminus), and [policy residuals at the upper
and preceding policy levels are integrable](hyp:hqplus,hqminus), then [the weighted
component score minus its population positive-part term is integrable and has mean zero](goal). -/
lemma population_binary_component_correction_zero (h : ThresholdCrossing M)
    (phi dphi : Z → X → ℝ → ℝ)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (L : LevelData Z X) (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (k j : ℕ) (w : X → ℝ) (hw : Measurable w)
    (hD : Measurable (Dbd phi L (eta0Bin M L) k j))
    (hE : Measurable (Edom phi L (eta0Bin M L) k j))
    (hI : Measurable (Iact phi L (eta0Bin M L) k j))
    (hPplus : Integrable (fun o : Obs X Z => w o.1 * RP L (eta0Bin M L) (k + 1) o)
      (observationLaw M))
    (hPminus : Integrable (fun o : Obs X Z => w o.1 * RP L (eta0Bin M L) k o)
      (observationLaw M))
    (hpplus : Integrable (fun o : Obs X Z => w o.1 * Rp L (eta0Bin M L) (k + 1) o)
      (observationLaw M))
    (hpminus : Integrable (fun o : Obs X Z => w o.1 * Rp L (eta0Bin M L) k o)
      (observationLaw M))
    (hqplus : Integrable (fun o : Obs X Z => w o.1 * RqBin dphi L (eta0Bin M L) k j o)
      (observationLaw M))
    (hqminus : Integrable (fun o : Obs X Z => w o.1 * RqBin dphi L (eta0Bin M L) k (j - 1) o)
      (observationLaw M)) :
    Integrable (fun o : Obs X Z => w o.1 *
      (binScoreComponents phi dphi L (eta0Bin M L) k j o - hMinus phi L (eta0Bin M L) k j o.1))
      (observationLaw M) ∧
    (∫ o : Obs X Z, w o.1 *
      (binScoreComponents phi dphi L (eta0Bin M L) k j o - hMinus phi L (eta0Bin M L) k j o.1)
      ∂observationLaw M) = 0 := by
  let D := Dbd phi L (eta0Bin M L) k j
  let E := Edom phi L (eta0Bin M L) k j
  let I := Iact phi L (eta0Bin M L) k j
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
  have zPp := population_RP_weighted_integral_zero M L (k + 1) (fun x => w x * D x) (hw.mul hD) iPp
  have zPm := population_RP_weighted_integral_zero M L k (fun x => w x * D x) (hw.mul hD) iPm
  have zpp := population_Rp_weighted_integral_zero M h (policyProp phi M.prop) L hOrder (k + 1)
    (fun x => w x * D x) (hw.mul hD) ipp
  have zpm := population_Rp_weighted_integral_zero M h (policyProp phi M.prop) L hOrder k
    (fun x => w x * (E x * I x)) (hw.mul hEI) ipm
  have zqp := population_RqBin_weighted_integral_zero M h dphi hdphi L k j
    (fun x => w x * I x) (hw.mul hI) iqp
  have zqm := population_RqBin_weighted_integral_zero M h dphi hdphi L k (j - 1)
    (fun x => w x * (E x * I x)) (hw.mul hEI) iqm
  let low := fun o : Obs X Z => if j = 1 then
    (w o.1 * (E o.1 * I o.1)) * Rp L (eta0Bin M L) k o else 0
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
      (binScoreComponents phi dphi L (eta0Bin M L) k j o - hMinus phi L (eta0Bin M L) k j o.1)) =
      (fun o => (w o.1 * D o.1) * RP L (eta0Bin M L) (k + 1) o -
        (w o.1 * D o.1) * RP L (eta0Bin M L) k o -
        (w o.1 * D o.1) * Rp L (eta0Bin M L) (k + 1) o - low o +
        (w o.1 * I o.1) * RqBin dphi L (eta0Bin M L) k j o -
        (w o.1 * (E o.1 * I o.1)) * RqBin dphi L (eta0Bin M L) k (j - 1) o) := by
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

-- @node: population_binary_component_weighted_mean
/-- Under [threshold crossing](hyp:h), [measurability of the policy derivative at the true
propensity](hyp:hdphi), and [invariant baseline and policy ordering](hyp:hOrder), assume
[a measurable covariate weight](hyp:hw) and measurable [interior-boundary](hyp:hD),
[dominance](hyp:hE), and [active-set indicators](hyp:hI). If the weighted [upper and lower
treated-success residuals](hyp:hPplus,hPminus), [upper and lower treatment residuals](hyp:hpplus,hpminus),
[upper and preceding policy residuals](hyp:hqplus,hqminus), and [population positive-part
term](hyp:hh) are integrable, then [the weighted component score has the same mean as
the weighted population positive-part term](goal). -/
lemma population_binary_component_weighted_mean (h : ThresholdCrossing M)
    (phi dphi : Z → X → ℝ → ℝ)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (L : LevelData Z X) (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (k j : ℕ) (w : X → ℝ) (hw : Measurable w)
    (hD : Measurable (Dbd phi L (eta0Bin M L) k j))
    (hE : Measurable (Edom phi L (eta0Bin M L) k j))
    (hI : Measurable (Iact phi L (eta0Bin M L) k j))
    (hPplus : Integrable (fun o : Obs X Z => w o.1 * RP L (eta0Bin M L) (k + 1) o)
      (observationLaw M))
    (hPminus : Integrable (fun o : Obs X Z => w o.1 * RP L (eta0Bin M L) k o)
      (observationLaw M))
    (hpplus : Integrable (fun o : Obs X Z => w o.1 * Rp L (eta0Bin M L) (k + 1) o)
      (observationLaw M))
    (hpminus : Integrable (fun o : Obs X Z => w o.1 * Rp L (eta0Bin M L) k o)
      (observationLaw M))
    (hqplus : Integrable (fun o : Obs X Z => w o.1 * RqBin dphi L (eta0Bin M L) k j o)
      (observationLaw M))
    (hqminus : Integrable (fun o : Obs X Z => w o.1 * RqBin dphi L (eta0Bin M L) k (j - 1) o)
      (observationLaw M))
    (hh : Integrable (fun o : Obs X Z => w o.1 * hMinus phi L (eta0Bin M L) k j o.1)
      (observationLaw M)) :
    (∫ o : Obs X Z, w o.1 * binScoreComponents phi dphi L (eta0Bin M L) k j o
      ∂observationLaw M) =
      ∫ o : Obs X Z, w o.1 * hMinus phi L (eta0Bin M L) k j o.1 ∂observationLaw M := by
  obtain ⟨hi, hz⟩ := population_binary_component_correction_zero M h phi dphi hdphi L hOrder
    k j w hw hD hE hI hPplus hPminus hpplus hpminus hqplus hqminus
  have hid : (fun o : Obs X Z => w o.1 * binScoreComponents phi dphi L (eta0Bin M L) k j o) =
      (fun o => w o.1 * hMinus phi L (eta0Bin M L) k j o.1 + w o.1 *
        (binScoreComponents phi dphi L (eta0Bin M L) k j o -
          hMinus phi L (eta0Bin M L) k j o.1)) := by
    funext o
    ring
  rw [hid, integral_add hh hi, hz, add_zero]

-- No conditional score identity is assumed: the population residuals above
-- give exact invariance of the integrated product score along its weight path.
-- @node: population_binary_regular_product_weight_path
/-- Under [threshold crossing](hyp:h), [measurability of the policy derivative at the true
propensity](hyp:hdphi), and [invariant level ordering](hyp:hOrder), assume [the selected
weight direction is measurable](hyp:hw) and the [interior-boundary](hyp:hD), [dominance](hyp:hE),
and [active-set indicators](hyp:hI) are measurable. If the direction-weighted [upper
and lower treated-success residuals](hyp:hPplus,hPminus), [upper and lower treatment
residuals](hyp:hpplus,hpminus), and [upper and preceding policy residuals](hyp:hqplus,hqminus)
are integrable, and [the population product score is integrable](hyp:hbase), then
[adding any scalar multiple of this direction to the regular product weight leaves
the integrated product score unchanged](goal). -/
lemma population_binary_regular_product_weight_path (h : ThresholdCrossing M)
    (phi dphi : Z → X → ℝ → ℝ)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (L : LevelData Z X) (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (k j : ℕ) (d : RegularIndex L → X → ℝ) (hw : Measurable (regularValue d k j))
    (hD : Measurable (Dbd phi L (eta0Bin M L) k j))
    (hE : Measurable (Edom phi L (eta0Bin M L) k j))
    (hI : Measurable (Iact phi L (eta0Bin M L) k j))
    (hPplus : Integrable (fun o : Obs X Z => regularValue d k j o.1 * RP L (eta0Bin M L) (k + 1) o)
      (observationLaw M))
    (hPminus : Integrable (fun o : Obs X Z => regularValue d k j o.1 * RP L (eta0Bin M L) k o)
      (observationLaw M))
    (hpplus : Integrable (fun o : Obs X Z => regularValue d k j o.1 * Rp L (eta0Bin M L) (k + 1) o)
      (observationLaw M))
    (hpminus : Integrable (fun o : Obs X Z => regularValue d k j o.1 * Rp L (eta0Bin M L) k o)
      (observationLaw M))
    (hqplus : Integrable (fun o : Obs X Z => regularValue d k j o.1 *
      RqBin dphi L (eta0Bin M L) k j o)
      (observationLaw M))
    (hqminus : Integrable (fun o : Obs X Z => regularValue d k j o.1 *
      RqBin dphi L (eta0Bin M L) k (j - 1) o)
      (observationLaw M))
    (hbase : Integrable (fun o => psiProdBin phi dphi L (eta0Bin M L) k j o) (observationLaw M))
    (t : ℝ) :
    (∫ o, psiProdBin phi dphi L
      {eta0Bin M L with gamma := fun a x => (eta0Bin M L).gamma a x + t * d a x} k j o
      ∂observationLaw M) = ∫ o, psiProdBin phi dphi L (eta0Bin M L) k j o ∂observationLaw M := by
  obtain ⟨hi, hz⟩ := population_binary_component_correction_zero M h phi dphi hdphi L hOrder
    k j (regularValue d k j) hw hD hE hI hPplus hPminus hpplus hpminus hqplus hqminus
  simp_rw [binary_regular_product_weight_path, mul_assoc]
  rw [integral_add hbase (hi.const_mul t), integral_const_mul, hz, mul_zero, add_zero]

-- @node: population_binary_regular_product_weight_orthogonality
/-- Under [threshold crossing](hyp:h), [measurability of the policy derivative at the true
propensity](hyp:hdphi), and [invariant level ordering](hyp:hOrder), suppose [the selected
weight direction is measurable](hyp:hw) and the [interior-boundary](hyp:hD), [dominance](hyp:hE),
and [active-set indicators](hyp:hI) are measurable. If the direction-weighted [upper
and lower treated-success residuals](hyp:hPplus,hPminus), [upper and lower treatment
residuals](hyp:hpplus,hpminus), and [upper and preceding policy residuals](hyp:hqplus,hqminus)
are integrable, and [the population product score is integrable](hyp:hbase), then
[the mean regular product score has derivative zero at zero along the linear path
in its product weight](goal). -/
lemma population_binary_regular_product_weight_orthogonality (h : ThresholdCrossing M)
    (phi dphi : Z → X → ℝ → ℝ)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (L : LevelData Z X) (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (k j : ℕ) (d : RegularIndex L → X → ℝ) (hw : Measurable (regularValue d k j))
    (hD : Measurable (Dbd phi L (eta0Bin M L) k j))
    (hE : Measurable (Edom phi L (eta0Bin M L) k j))
    (hI : Measurable (Iact phi L (eta0Bin M L) k j))
    (hPplus : Integrable (fun o : Obs X Z => regularValue d k j o.1 * RP L (eta0Bin M L) (k + 1) o)
      (observationLaw M))
    (hPminus : Integrable (fun o : Obs X Z => regularValue d k j o.1 * RP L (eta0Bin M L) k o)
      (observationLaw M))
    (hpplus : Integrable (fun o : Obs X Z => regularValue d k j o.1 * Rp L (eta0Bin M L) (k + 1) o)
      (observationLaw M))
    (hpminus : Integrable (fun o : Obs X Z => regularValue d k j o.1 * Rp L (eta0Bin M L) k o)
      (observationLaw M))
    (hqplus : Integrable (fun o : Obs X Z => regularValue d k j o.1 *
      RqBin dphi L (eta0Bin M L) k j o)
      (observationLaw M))
    (hqminus : Integrable (fun o : Obs X Z => regularValue d k j o.1 *
      RqBin dphi L (eta0Bin M L) k (j - 1) o)
      (observationLaw M))
    (hbase : Integrable (fun o => psiProdBin phi dphi L (eta0Bin M L) k j o) (observationLaw M)) :
    HasDerivAt (fun t : ℝ => ∫ o, psiProdBin phi dphi L
      {eta0Bin M L with gamma := fun a x => (eta0Bin M L).gamma a x + t * d a x} k j o
      ∂observationLaw M) 0 0 := by
  have heq : (fun t : ℝ => ∫ o, psiProdBin phi dphi L
      {eta0Bin M L with gamma := fun a x => (eta0Bin M L).gamma a x + t * d a x} k j o
      ∂observationLaw M) =
      (fun _ : ℝ => ∫ o, psiProdBin phi dphi L (eta0Bin M L) k j o ∂observationLaw M) := by
    funext t
    exact population_binary_regular_product_weight_path M h phi dphi hdphi L hOrder
      k j d hw hD hE hI hPplus hPminus hpplus hpminus hqplus hqminus hbase t
  rw [heq]
  exact hasDerivAt_const 0 _

end Papers.TbsPrteOptimalTransport

module
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousQuantileOrdering
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousPropensityBounds
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationContinuousFullDenominators
/-! Quantile changes in propensity representers retain zero population mean. -/
public section
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: population_continuous_plus_boundary_value_measurable
/-- For [a level below the number of levels](hyp:hk) and [a boundary index no greater than that level's band count](hyp:hj), if [the population band boundary is measurable](hyp:ha), [the population upper-side boundary indicator mean is measurable in covariates](goal). -/
@[fun_prop] lemma population_continuous_plus_boundary_value_measurable
    (L : LevelData Z X) (k j : ℕ) (hk : k < L.K) (hj : j ≤ L.l k)
    (ha : Measurable (bandBoundary M L k j)) :
    Measurable (boundaryValue (trueNuisance M L).Mplus k j) := by
  first | fun_prop | skip
  change Measurable (fun x => boundaryValue (trueNuisance M L).Mplus k j x)
  simpa only [boundaryValue, dif_pos (show k < L.K ∧ j ≤ L.l k from ⟨hk, hj⟩),
    trueNuisance] using population_boundary_indicator_mean_measurable M L true k j ha

-- @node: population_continuous_minus_boundary_value_measurable
/-- For [a level below the number of levels](hyp:hk) and [a boundary index no greater than that level's band count](hyp:hj), if [the population band boundary is measurable](hyp:ha), [the population lower-side boundary indicator mean, with its zero convention at level zero, is measurable in covariates](goal). -/
@[fun_prop] lemma population_continuous_minus_boundary_value_measurable
    (L : LevelData Z X) (k j : ℕ) (hk : k < L.K) (hj : j ≤ L.l k)
    (ha : Measurable (bandBoundary M L k j)) :
    Measurable (minusBoundaryValue (trueNuisance M L).Mminus k j) := by
  first | fun_prop | skip
  change Measurable (fun x => minusBoundaryValue (trueNuisance M L).Mminus k j x)
  by_cases hk0 : k = 0
  · subst k
    simp only [minusBoundaryValue, show ¬ (1 ≤ 0) by omega, false_and, dite_false, if_false]
    fun_prop
  · simpa only [minusBoundaryValue,
      dif_pos (show 1 ≤ k ∧ k < L.K ∧ j ≤ L.l k from ⟨by omega, hk, hj⟩),
      trueNuisance] using population_boundary_indicator_mean_measurable M L false k j ha

-- Changing only nu in a propensity representer leaves a linear combination
-- of population CDF values. Clipped pi gives integrability; the tower property
-- then centers the actual treatment residual, even with a fitted denominator.
-- @node: population_continuous_quantile_propensity_difference_zero
/-- Suppose [threshold crossing holds](hyp:h), [the policy preserves the propensity level ordering](hyp:hL), [each fitted assignment denominator is measurable](hyp:hpi), [the denominator floor is positive](hyp:hc), and [each fitted assignment denominator is almost surely above that floor](hyp:hclip). For [a level below the number of levels](hyp:hk) and [a band index strictly below that level's band count](hyp:hj), suppose [the lower population boundary is measurable](hyp:ha), [the upper population boundary is measurable](hyp:hb), [the lower displacement equals the fitted lower quantile minus its population boundary](hyp:hda), [the upper displacement equals the fitted upper quantile minus its population boundary](hyp:hdb), and [the weighted lower and upper displacements are measurable](hyp:hma,hmb) and [integrable under the covariate law](hyp:ia,ib). Then [the weighted sum of the lower and upper propensity residuals multiplied by the changes in their coefficients induced by these quantile displacements is integrable and has population mean zero, retaining the fitted assignment denominators and omitting the lower term at level zero](goal). -/
lemma population_continuous_quantile_propensity_difference_zero
    (h : ThresholdCrossing M) (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L)
    (pi : PositiveIndex L.K → X → ℝ) (hpi : ∀ a, Measurable (pi a))
    (nu : BoundaryIndex L → X → ℝ)
    (c : ℝ) (hc : 0 < c) (hclip : ∀ a, ∀ᵐ x ∂xLaw M, c ≤ pi a x)
    (k j : ℕ) (hk : k < L.K) (hj : j < L.l k)
    (ha : Measurable (bandBoundary M L k j))
    (hb : Measurable (bandBoundary M L k (j+1)))
    (w da db : X → ℝ)
    (hda : ∀ x, da x = nuValue M {trueNuisance M L with nu := nu} k j x -
      bandBoundary M L k j x)
    (hdb : ∀ x, db x = nuValue M {trueNuisance M L with nu := nu} k (j+1) x -
      bandBoundary M L k (j+1) x)
    (hma : Measurable (fun x => w x * da x))
    (hmb : Measurable (fun x => w x * db x))
    (ia : Integrable (fun x => w x * da x) (xLaw M))
    (ib : Integrable (fun x => w x * db x) (xLaw M)) :
    let e := {trueNuisance M L with piLev := pi, nu := nu}
    let b := {trueNuisance M L with piLev := pi}
    Integrable (fun o : Obs X Z => w o.1 *
      ((if k = 0 then 0 else (alphaLow M L e k j o.1 - alphaLow M L b k j o.1) *
        RpCont L b k o) +
        (alphaHigh M L e k j o.1 - alphaHigh M L b k j o.1) * RpCont L b (k+1) o))
      (observationLaw M) ∧
    (∫ o : Obs X Z, w o.1 *
      ((if k = 0 then 0 else (alphaLow M L e k j o.1 - alphaLow M L b k j o.1) *
        RpCont L b k o) +
        (alphaHigh M L e k j o.1 - alphaHigh M L b k j o.1) * RpCont L b (k+1) o)
      ∂observationLaw M) = 0 := by
  dsimp only
  let e := {trueNuisance M L with piLev := pi, nu := nu}
  let b := {trueNuisance M L with piLev := pi}
  let va := fun x => w x * da x
  let vb := fun x => w x * db x
  let ap := boundaryValue (trueNuisance M L).Mplus k j
  let bp := boundaryValue (trueNuisance M L).Mplus k (j+1)
  let am := minusBoundaryValue (trueNuisance M L).Mminus k j
  let bm := minusBoundaryValue (trueNuisance M L).Mminus k (j+1)
  have map := population_continuous_plus_boundary_value_measurable M L k j hk hj.le ha
  have mam := population_continuous_minus_boundary_value_measurable M L k j hk hj.le ha
  have mbp := population_continuous_plus_boundary_value_measurable M L k (j+1) hk (by omega) hb
  have mbm := population_continuous_minus_boundary_value_measurable M L k (j+1) hk (by omega) hb
  have iap : Integrable (fun x => va x * ap x) (xLaw M) := by
    simpa only [mul_comm] using ia.bdd_mul map.aestronglyMeasurable
      (Eventually.of_forall fun x => (population_continuous_boundary_values_norm_le_one M L k j x).1)
  have iam : Integrable (fun x => va x * am x) (xLaw M) := by
    simpa only [mul_comm] using ia.bdd_mul mam.aestronglyMeasurable
      (Eventually.of_forall fun x => (population_continuous_boundary_values_norm_le_one M L k j x).2)
  have ibp : Integrable (fun x => vb x * bp x) (xLaw M) := by
    simpa only [mul_comm] using ib.bdd_mul mbp.aestronglyMeasurable
      (Eventually.of_forall fun x => (population_continuous_boundary_values_norm_le_one M L k (j+1) x).1)
  have ibm : Integrable (fun x => vb x * bm x) (xLaw M) := by
    simpa only [mul_comm] using ib.bdd_mul mbm.aestronglyMeasurable
      (Eventually.of_forall fun x => (population_continuous_boundary_values_norm_le_one M L k (j+1) x).2)
  let vp := fun x => va x * ap x - vb x * bp x
  let vm := fun x => -(va x * am x) + vb x * bm x + va x * indicator (1 ≤ j) - vb x
  have hmp : Measurable vp := by fun_prop
  have hmm : Measurable vm := by fun_prop
  have ip : Integrable vp (xLaw M) := iap.sub' ibp
  have im : Integrable vm (xLaw M) :=
    ((iam.neg.fun_add ibm).fun_add (ia.mul_const _)).sub' ib
  have ep x : w x * (alphaHigh M L e k j x - alphaHigh M L b k j x) = vp x := by
    dsimp only [alphaHigh, vp, va, vb, ap, bp]
    change w x * ((meanValue (trueNuisance M L).Jplus k j x +
      nuValue M {trueNuisance M L with nu := nu} k j x * ap x -
      nuValue M {trueNuisance M L with nu := nu} k (j+1) x * bp x) -
      (meanValue (trueNuisance M L).Jplus k j x +
      nuValue M (trueNuisance M L) k j x * ap x -
      nuValue M (trueNuisance M L) k (j+1) x * bp x)) =
      w x * da x * ap x - w x * db x * bp x
    rw [population_nuValue_eq_bandBoundary M L k j hk hj.le,
      population_nuValue_eq_bandBoundary M L k (j+1) hk (by omega)]
    rw [hda, hdb]
    ring
  have em x : w x * (alphaLow M L e k j x - alphaLow M L b k j x) = vm x := by
    dsimp only [alphaLow, vm, va, vb, am, bm]
    change w x * ((-minusMeanValue (trueNuisance M L).Jminus k j x -
      nuValue M {trueNuisance M L with nu := nu} k j x * am x +
      nuValue M {trueNuisance M L with nu := nu} k (j+1) x * bm x +
      indicator (1 ≤ j) * nuValue M {trueNuisance M L with nu := nu} k j x -
      nuValue M {trueNuisance M L with nu := nu} k (j+1) x) -
      (-minusMeanValue (trueNuisance M L).Jminus k j x -
      nuValue M (trueNuisance M L) k j x * am x +
      nuValue M (trueNuisance M L) k (j+1) x * bm x +
      indicator (1 ≤ j) * nuValue M (trueNuisance M L) k j x -
      nuValue M (trueNuisance M L) k (j+1) x)) =
      -(w x * da x * am x) + w x * db x * bm x +
      w x * da x * indicator (1 ≤ j) - w x * db x
    rw [population_nuValue_eq_bandBoundary M L k j hk hj.le,
      population_nuValue_eq_bandBoundary M L k (j+1) hk (by omega)]
    rw [hda, hdb]
    ring
  have irp := population_RpCont_integrable_of_integrable_weight M h q L hL pi hpi c hc hclip
    (k+1) vp hmp ip
  have irm := population_RpCont_integrable_of_integrable_weight M h q L hL pi hpi c hc hclip
    k vm hmm im
  have zp := population_RpCont_fitted_denominator_weighted_zero M h q L pi hpi hL
    (k+1) vp hmp irp
  have zm := population_RpCont_fitted_denominator_weighted_zero M h q L pi hpi hL k vm hmm irm
  change Integrable (fun o : Obs X Z => w o.1 *
    ((if k = 0 then 0 else (alphaLow M L e k j o.1 - alphaLow M L b k j o.1) * RpCont L b k o) +
      (alphaHigh M L e k j o.1 - alphaHigh M L b k j o.1) * RpCont L b (k+1) o))
    (observationLaw M) ∧
    (∫ o : Obs X Z, w o.1 *
    ((if k = 0 then 0 else (alphaLow M L e k j o.1 - alphaLow M L b k j o.1) * RpCont L b k o) +
      (alphaHigh M L e k j o.1 - alphaHigh M L b k j o.1) * RpCont L b (k+1) o)
      ∂observationLaw M) = 0
  by_cases hk0 : k = 0
  · simp only [if_pos hk0, zero_add, ← mul_assoc, ep]
    exact ⟨irp, zp⟩
  · simp only [hk0, if_false, mul_add, ← mul_assoc, ep, em]
    exact ⟨irm.fun_add irp, by rw [integral_add irm irp, zm, zp, add_zero]⟩

-- The fixed lower endpoint has zero displacement. Every estimated endpoint
-- has a bounded measurable direction, derived from the admissible interval.
-- @node: continuous_admissible_weighted_quantile_displacement_regular
/-- Suppose [the continuous nuisance direction is admissible at the truth](hyp:hd), [the level is below the number of levels](hyp:hk), and [the boundary index is no greater than that level's band count](hyp:hj). Then [for all path values sufficiently close to zero, the quantile displacement multiplied by any regular component of the perturbed product weight is measurable and integrable under the covariate law](goal). -/
lemma continuous_admissible_weighted_quantile_displacement_regular
    (L : LevelData Z X) (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del))
    (k j : ℕ) (hk : k < L.K) (hj : j ≤ L.l k) (g : RegularIndex L) :
    ∀ᶠ t : ℝ in 𝓝 0,
      let path := trueNuisance M L + t • del
      let d := fun x => nuValue M {trueNuisance M L with nu := path.nu} k j x -
        bandBoundary M L k j x
      Measurable (fun x => path.gamma g x * d x) ∧
        Integrable (fun x => path.gamma g x * d x) (xLaw M) := by
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  obtain ⟨C, hC, hdir⟩ := continuous_quantile_direction_regular M L _ del hd
  obtain ⟨r, hr, hpath⟩ := hd.admissible
  filter_upwards [continuousAt_id.abs.eventually_lt_const (by simpa using hr)] with t ht
  have had := hpath t ht
  rcases had with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hgb, hgm, _⟩
  dsimp only
  by_cases hj0 : j = 0
  · subst j
    simp only [nuValue, if_true, bandBoundary, true_or, sub_self, mul_zero]
    exact ⟨measurable_const, integrable_zero _ _ _⟩
  · let a : BoundaryIndex L := ⟨(k,j), hk, by omega, hj⟩
    have hdval (x : X) :
        nuValue M {trueNuisance M L with nu := (trueNuisance M L + t • del).nu} k j x -
          bandBoundary M L k j x = t * del.nu a x := by
      simp only [nuValue, hj0, if_false,
        dif_pos (show k < L.K ∧ 1 ≤ j ∧ j ≤ L.l k from ⟨hk, by omega, hj⟩)]
      change bandBoundary M L k j x + t * del.nu a x - bandBoundary M L k j x = _
      ring
    simp_rw [hdval]
    have hdm := (hdir a).1
    have hm : Measurable (fun x => (trueNuisance M L + t • del).gamma g x *
        (t * del.nu a x)) := by fun_prop
    refine ⟨hm, Integrable.of_bound hm.aestronglyMeasurable (|t| * C) ?_⟩
    filter_upwards [hgb g, (hdir a).2] with x hx hy
    rw [norm_mul, norm_mul, Real.norm_eq_abs, abs_of_nonneg hx.1]
    calc
      _ ≤ 1 * (|t| * C) := mul_le_mul hx.2
        (mul_le_mul_of_nonneg_left hy (abs_nonneg t)) (by positivity) zero_le_one
      _ = _ := one_mul _

-- This is the propensity-representer part of the quantile telescope in the
-- full band score. Neither the fitted product weight nor pi is frozen.
-- @node: population_continuous_admissible_quantile_propensity_orthogonality
/-- Suppose [threshold crossing holds](hyp:h), [the policy preserves the propensity level ordering](hyp:hL), [baseline overlap holds](hyp:hov), and [the continuous nuisance direction is admissible at the truth](hyp:hd). For [a level below the number of levels](hyp:hk) and [a band index strictly below that level's band count](hyp:hj), assume [the lower population boundary is measurable](hyp:ha) and [the upper population boundary is measurable](hyp:hb). Then [the population mean of the product-weighted change in the propensity-residual terms caused by moving the quantiles has derivative zero at the truth, with product weights and assignment denominators varying along the same path and the lower residual omitted at level zero](goal). -/
lemma population_continuous_admissible_quantile_propensity_orthogonality
    (h : ThresholdCrossing M) (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (cpi : ℝ)
    (hov : BaselineOverlapWitness M L cpi) (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del))
    (k j : ℕ) (hk : k < L.K) (hj : j < L.l k) (g : RegularIndex L)
    (ha : Measurable (bandBoundary M L k j))
    (hb : Measurable (bandBoundary M L k (j+1))) :
    let path := fun t : ℝ => trueNuisance M L + t • del
    let e := fun t => {trueNuisance M L with piLev := (path t).piLev, nu := (path t).nu}
    let b := fun t => {trueNuisance M L with piLev := (path t).piLev}
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z, (path t).gamma g o.1 *
      ((if k = 0 then 0 else (alphaLow M L (e t) k j o.1 - alphaLow M L (b t) k j o.1) *
        RpCont L (b t) k o) +
        (alphaHigh M L (e t) k j o.1 - alphaHigh M L (b t) k j o.1) * RpCont L (b t) (k+1) o)
      ∂observationLaw M) 0 0 := by
  dsimp only
  apply (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
  obtain ⟨r, hr, hpath⟩ := hd.admissible
  filter_upwards [continuous_assignment_path_uniform_lower_bound M L cpi hov del hd,
    continuous_admissible_weighted_quantile_displacement_regular M L del hd k j hk hj.le g,
    continuous_admissible_weighted_quantile_displacement_regular M L del hd k (j+1) hk (by omega) g,
    continuousAt_id.abs.eventually_lt_const (by simpa using hr)] with t hclip hda hdb ht
  have had := hpath t ht
  rcases had with ⟨_, _, _, _, _, hpim, _⟩
  exact (population_continuous_quantile_propensity_difference_zero M h q L hL
    (trueNuisance M L + t • del).piLev hpim (trueNuisance M L + t • del).nu
    (cpi/2) (div_pos hov.1 (by norm_num)) hclip k j hk hj ha hb
    ((trueNuisance M L + t • del).gamma g)
    (fun x => nuValue M {trueNuisance M L with nu := (trueNuisance M L + t • del).nu} k j x -
      bandBoundary M L k j x)
    (fun x => nuValue M {trueNuisance M L with nu := (trueNuisance M L + t • del).nu} k (j+1) x -
      bandBoundary M L k (j+1) x)
    (fun _ => rfl) (fun _ => rfl) hda.1 hdb.1 hda.2 hdb.2).2

end Papers.TbsPrteOptimalTransport

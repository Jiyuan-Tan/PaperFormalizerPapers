module
public import Papers.TbsPrteOptimalTransport.Helpers.ObservedBandBoundary
/-! First-band IFJ/IFM boundary cancellation along admissible nuisance paths. -/
public section
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
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

-- This telescoping path changes the quantiles, retaining the fitted assignment
-- denominator and product weight. Every local clipping and ordering condition
-- is derived from admissibility; only the upper endpoint uses a density bound.
-- @node: population_continuous_first_band_admissible_quantile_block_orthogonality
/-- Assume [bounded densities near the band boundaries](hyp:h), [baseline assignment overlap](hyp:hov),
and [a direction admissible at the true continuous nuisance](hyp:hd).
For [an interval index below the number of propensity intervals](hyp:hk) with
[at least one quantile boundary](hyp:hj), if [the selected side is the plus side or the interval index is nonzero](hyp:hactive)
and [the first upper boundary is measurable](hyp:hb),
[the population mean of the first-band quantile score difference, multiplied by the moving product weight, has derivative zero at zero](goal).

The difference compares moving quantiles with true boundaries while retaining the same moving assignment denominators; the lower boundary is the minimum outcome. -/
lemma population_continuous_first_band_admissible_quantile_block_orthogonality
    (L : LevelData Z X) (h : BoundaryDensitiesBounded M L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del))
    (k : ℕ) (hk : k < L.K) (hj : 1 ≤ L.l k)
    (g : RegularIndex L) (plus : Bool) (hactive : plus = true ∨ k ≠ 0)
    (hb : Measurable (bandBoundary M L k 1)) :
    let path := fun t : ℝ => trueNuisance M L + t • del
    let e := fun t => {trueNuisance M L with piLev := (path t).piLev, nu := (path t).nu}
    let b := fun t => {trueNuisance M L with piLev := (path t).piLev}
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z, (path t).gamma g o.1 *
      ((IFJ M L (e t) plus k 0 o + nuValue M (e t) k 0 o.1 * IFM M L (e t) plus k 0 o -
        nuValue M (e t) k 1 o.1 * IFM M L (e t) plus k 1 o) -
      (IFJ M L (b t) plus k 0 o + M.yMin * IFM M L (b t) plus k 0 o -
        bandBoundary M L k 1 o.1 * IFM M L (b t) plus k 1 o))
      ∂observationLaw M) 0 0 := by
  dsimp only
  let path := fun t : ℝ => trueNuisance M L + t • del
  let e := fun t => {trueNuisance M L with piLev := (path t).piLev, nu := (path t).nu}
  let a : BoundaryIndex L := ⟨(k,1), hk, le_rfl, hj⟩
  obtain ⟨_, _, hdir⟩ := continuous_quantile_direction_regular M L _ del hd
  have horder := continuous_admissible_first_band_ordered_path M L del hd k hk hj
  have hbase : ∀ᵐ x ∂xLaw M, bandBoundary M L k 0 x ≤ bandBoundary M L k 1 x := by
    simpa only [bandBoundary, true_or, if_true, zero_mul, add_zero] using horder.self_of_nhds
  obtain ⟨r, C, hr, hden⟩ := h
  have hcpi : 0 < cpi := hov.1
  have ha : Measurable (bandBoundary M L k 0) := by
    change Measurable (fun _ : X => M.yMin)
    fun_prop
  have hz := population_continuous_band_quantile_block_local_orthogonality M L e
    (fun t => (path t).piLev) (fun t => (path t).gamma g) plus k 0 hk (by omega)
    hactive 0 (del.nu a) (by fun_prop) (hdir a).1
    (MemLp.zero)
    (continuous_quantile_direction_memLp M L _ del hd a) ha hb hbase
    1 (cpi / 2) r |C| zero_le_one (by positivity) hr (abs_nonneg C)
    (by
      obtain ⟨s, hs, hpath⟩ := hd.admissible
      filter_upwards [continuous_assignment_path_uniform_lower_bound M L cpi hov del hd,
        horder, continuousAt_id.abs.eventually_lt_const (by simpa using hs)] with t ht ho hst
      have had := hpath t hst
      rcases had with ⟨_, _, _, _, _, hpim, _, _, _, _, _, _, hgb, hgm, _⟩
      refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, hpim, ht, hgm g, ?_⟩
      · intro x
        simp [nuValue, bandBoundary]
      · intro x
        have hvalid : k < L.K ∧ 1 ≤ 1 ∧ 1 ≤ L.l k := ⟨hk, le_rfl, hj⟩
        simp only [e, nuValue, dif_pos hvalid]
        change (trueNuisance M L).nu a x + t * del.nu a x = _
        rfl
      · simpa only [bandBoundary, true_or, if_true, Pi.zero_apply, mul_zero, add_zero] using ho
      · filter_upwards [hgb g] with x hx
        change |(trueNuisance M L + t • del).gamma g x| ≤ 1
        simpa only [abs_of_nonneg hx.1] using hx.2)
    (Or.inl rfl)
    (by
      have hi : (if plus then k + 1 else k) = k + 1 ∨
          (1 ≤ k ∧ (if plus then k + 1 else k) = k) := by
        cases plus
        · simp only [Bool.false_eq_true, false_or] at hactive
          exact Or.inr ⟨by omega, rfl⟩
        · exact Or.inl rfl
      filter_upwards [hden k hk 1 le_rfl hj _ hi] with x hx
      intro u v hu huv hv
      exact (hx u v hu huv hv).trans
        (mul_le_mul_of_nonneg_right (le_abs_self C) (sub_nonneg.mpr huv)))
  simpa only [bandBoundary, true_or, if_true, zero_add] using hz

-- The centered first-band difference is integrable throughout the admissible
-- neighborhood. This permits subtracting the plus and minus population means.
-- @node: population_continuous_first_band_admissible_quantile_block_integrable
/-- Under [baseline assignment overlap](hyp:hov) and [a direction admissible at the true continuous nuisance](hyp:hd),
for [an interval index below the number of propensity intervals](hyp:hk) with
[at least one quantile boundary](hyp:hj) and [a measurable first upper boundary](hyp:hb),
[the first-band quantile score difference on either selected side, multiplied by the moving product weight, is integrable for all perturbations sufficiently near zero](goal).

The difference uses moving quantiles versus true boundaries, with the same moving assignment denominators in both scores and the minimum outcome as lower boundary. -/
lemma population_continuous_first_band_admissible_quantile_block_integrable
    (L : LevelData Z X) (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del))
    (k : ℕ) (hk : k < L.K) (hj : 1 ≤ L.l k)
    (g : RegularIndex L) (plus : Bool)
    (hb : Measurable (bandBoundary M L k 1)) :
    let path := fun t : ℝ => trueNuisance M L + t • del
    let e := fun t => {trueNuisance M L with piLev := (path t).piLev, nu := (path t).nu}
    let b := fun t => {trueNuisance M L with piLev := (path t).piLev}
    ∀ᶠ t : ℝ in 𝓝 0, Integrable (fun o : Obs X Z => (path t).gamma g o.1 *
      ((IFJ M L (e t) plus k 0 o + nuValue M (e t) k 0 o.1 * IFM M L (e t) plus k 0 o -
        nuValue M (e t) k 1 o.1 * IFM M L (e t) plus k 1 o) -
      (IFJ M L (b t) plus k 0 o + M.yMin * IFM M L (b t) plus k 0 o -
        bandBoundary M L k 1 o.1 * IFM M L (b t) plus k 1 o)))
      (observationLaw M) := by
  dsimp only
  let path := fun t : ℝ => trueNuisance M L + t • del
  let e := fun t => {trueNuisance M L with piLev := (path t).piLev, nu := (path t).nu}
  let a : BoundaryIndex L := ⟨(k,1), hk, le_rfl, hj⟩
  have hcpi : 0 < cpi := hov.1
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  obtain ⟨_, _, hdir⟩ := continuous_quantile_direction_regular M L _ del hd
  have hdm := (hdir a).1
  have hid : Integrable (del.nu a) (xLaw M) :=
    (continuous_quantile_direction_memLp M L _ del hd a).integrable (by norm_num)
  have horder := continuous_admissible_first_band_ordered_path M L del hd k hk hj
  have hbase : ∀ᵐ x ∂xLaw M, M.yMin ≤ bandBoundary M L k 1 x := by
    simpa only [zero_mul, add_zero] using horder.self_of_nhds
  obtain ⟨r, hr, hpath⟩ := hd.admissible
  filter_upwards [continuous_assignment_path_uniform_lower_bound M L cpi hov del hd,
    horder, continuousAt_id.abs.eventually_lt_const (by simpa using hr)] with t ht ho htr
  have had : ContAdmissible M L (path t) := hpath t htr
  rcases had with ⟨_, _, _, _, _, hpim, _, _, _, _, _, _, hgb, hgm, _⟩
  have hwm := hgm g
  have hwb : ∀ᵐ x ∂xLaw M, |(path t).gamma g x| ≤ 1 := by
    filter_upwards [hgb g] with x hx
    simpa only [abs_of_nonneg hx.1] using hx.2
  have ha : Measurable (bandBoundary M L k 0) := by
    change Measurable (fun _ : X => M.yMin)
    fun_prop
  have hvalid : k < L.K ∧ 1 ≤ 1 ∧ 1 ≤ L.l k := ⟨hk, le_rfl, hj⟩
  have hna x : nuValue M (e t) k 0 x = M.yMin := by simp [nuValue]
  have hnb x : nuValue M (e t) k 1 x = bandBoundary M L k 1 x + t * del.nu a x := by
    simp only [e, nuValue, Nat.one_ne_zero, if_false, dif_pos hvalid]
    rfl
  have iwb : Integrable (fun x => (path t).gamma g x * (t * del.nu a x)) (xLaw M) :=
    (hid.const_mul t).bdd_mul hwm.aestronglyMeasurable
      (by simpa only [Real.norm_eq_abs] using hwb)
  have ia := population_IFM_fitted_denominator_integrable M L (path t).piLev hpim
    (cpi / 2) (by positivity) ht plus k 0 hk (by omega) ha
    (fun _ => 0) (by fun_prop) (integrable_zero _ _ _)
  have ib := population_IFM_fitted_denominator_integrable M L (path t).piLev hpim
    (cpi / 2) (by positivity) ht plus k 1 hk hj hb
    (fun x => (path t).gamma g x * (t * del.nu a x)) (by fun_prop) iwb
  by_cases hactive : plus = true ∨ k ≠ 0
  · let i : ℕ := if plus then k + 1 else k
    have hi : 1 ≤ i ∧ i ≤ L.K := by
      cases plus
      · simp only [Bool.false_eq_true, false_or] at hactive
        simp only [i, Bool.false_eq_true, if_false]
        omega
      · simp only [i, if_true]
        omega
    have hskip : (!plus && k == 0) = false := by
      cases plus
      · simp only [Bool.false_eq_true, false_or] at hactive
        simp [hactive]
      · simp
    have hcm : Measurable (positiveValue (path t).piLev i) := by
      unfold positiveValue
      simpa only [positiveValue, dif_pos hi] using hpim ⟨i, hi⟩
    have hcl : ∀ᵐ x ∂xLaw M, cpi / 2 ≤ positiveValue (path t).piLev i x := by
      simpa only [positiveValue, dif_pos hi] using ht ⟨i, hi⟩
    have ir := population_observed_band_boundary_integrable M L i
      (fun _ => M.yMin) (bandBoundary M L k 1) (fun _ => M.yMin)
      (fun x => bandBoundary M L k 1 x + t * del.nu a x)
      ((path t).gamma g) (positiveValue (path t).piLev i)
      (by fun_prop) hb (by fun_prop) (by fun_prop) hwm hcm hbase ho
      (by simp only [sub_self]; exact integrable_zero _ _ _)
      (by simpa only [add_sub_cancel_left] using hid.const_mul t)
      1 (cpi / 2) zero_le_one (by positivity) hwb hcl
    have hir : Integrable (fun o : Obs X Z => (path t).gamma g o.1 *
        ((if !plus && k == 0 then 0 else
          indicator (o.2.1 ∈ L.S (if plus then k + 1 else k)) * o.2.2.1 /
            positiveValue (path t).piLev (if plus then k + 1 else k) o.1) *
          continuousDebiasedBandBoundary (bandBoundary M L k 0 o.1)
            (bandBoundary M L k 1 o.1)
            (nuValue M (e t) k 0 o.1) (nuValue M (e t) k 1 o.1) o.2.2.2))
        (observationLaw M) := by
      simpa only [hskip, Bool.false_eq_true, if_false, hna, hnb, i,
        bandBoundary, true_or, if_true] using ir
    have hz := (population_continuous_band_quantile_difference_mean M L (e t)
      (path t).piLev hpim rfl rfl rfl rfl rfl plus k 0 hk (by omega) ha hb
      ((path t).gamma g) (fun _ => 0) (fun x => t * del.nu a x)
      (by fun_prop) (by fun_prop)
      (by intro x; simp only [hna, bandBoundary, true_or, if_true, sub_self])
      (by intro x; rw [hnb]; ring)
      (by simpa only [mul_zero] using ia) ib hir).1
    simpa only [bandBoundary, true_or, if_true, zero_add] using hz
  · have hk0 : k = 0 := by tauto
    have hp : plus = false := by
      cases plus
      · rfl
      · exact False.elim (hactive (Or.inl rfl))
    subst k
    subst plus
    simp only [IFJ, IFM, Bool.not_false, Bool.true_and, beq_self_eq_true,
      if_true, true_and, add_zero, mul_zero, sub_zero]
    haveI : IsProbabilityMeasure (observationLaw M) := by
      unfold observationLaw
      exact Measure.isProbabilityMeasure_map
        (M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY))).aemeasurable
    exact integrable_const 0

-- Both treatment sides are now assembled under the moving product weight.
-- The missing minus side at k=0 is identically zero by the score construction.
-- @node: population_continuous_first_band_admissible_signed_quantile_block_orthogonality
/-- Assume [bounded densities near the band boundaries](hyp:h), [baseline assignment overlap](hyp:hov),
and [a direction admissible at the true continuous nuisance](hyp:hd).
For [an interval index below the number of propensity intervals](hyp:hk) with
[at least one quantile boundary](hyp:hj) and [a measurable first upper boundary](hyp:hb),
[the population mean of the plus-side minus minus-side first-band quantile score differences, multiplied by the moving product weight, has derivative zero at zero](goal).

Each difference compares moving quantiles with true boundaries using the same moving assignment denominators and the minimum outcome as lower boundary. -/
lemma population_continuous_first_band_admissible_signed_quantile_block_orthogonality
    (L : LevelData Z X) (h : BoundaryDensitiesBounded M L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del))
    (k : ℕ) (hk : k < L.K) (hj : 1 ≤ L.l k)
    (g : RegularIndex L) (hb : Measurable (bandBoundary M L k 1)) :
    let path := fun t : ℝ => trueNuisance M L + t • del
    let e := fun t => {trueNuisance M L with piLev := (path t).piLev, nu := (path t).nu}
    let b := fun t => {trueNuisance M L with piLev := (path t).piLev}
    let block := fun plus t (o : Obs X Z) =>
      (IFJ M L (e t) plus k 0 o + nuValue M (e t) k 0 o.1 * IFM M L (e t) plus k 0 o -
        nuValue M (e t) k 1 o.1 * IFM M L (e t) plus k 1 o) -
      (IFJ M L (b t) plus k 0 o + M.yMin * IFM M L (b t) plus k 0 o -
        bandBoundary M L k 1 o.1 * IFM M L (b t) plus k 1 o)
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z, (path t).gamma g o.1 *
      (block true t o - block false t o) ∂observationLaw M) 0 0 := by
  let path := fun t : ℝ => trueNuisance M L + t • del
  let e := fun t => {trueNuisance M L with piLev := (path t).piLev, nu := (path t).nu}
  let b := fun t => {trueNuisance M L with piLev := (path t).piLev}
  let block := fun plus t (o : Obs X Z) =>
    (IFJ M L (e t) plus k 0 o + nuValue M (e t) k 0 o.1 * IFM M L (e t) plus k 0 o -
      nuValue M (e t) k 1 o.1 * IFM M L (e t) plus k 1 o) -
    (IFJ M L (b t) plus k 0 o + M.yMin * IFM M L (b t) plus k 0 o -
      bandBoundary M L k 1 o.1 * IFM M L (b t) plus k 1 o)
  change HasDerivAt (fun t : ℝ => ∫ o : Obs X Z, (path t).gamma g o.1 *
    (block true t o - block false t o) ∂observationLaw M) 0 0
  have zp : HasDerivAt (fun t : ℝ => ∫ o : Obs X Z,
      (path t).gamma g o.1 * block true t o ∂observationLaw M) 0 0 :=
    population_continuous_first_band_admissible_quantile_block_orthogonality
      M L h cpi hov del hd k hk hj g true (Or.inl rfl) hb
  have zm : HasDerivAt (fun t : ℝ => ∫ o : Obs X Z,
      (path t).gamma g o.1 * block false t o ∂observationLaw M) 0 0 := by
    by_cases hk0 : k = 0
    · have hz : ∀ t, ∀ o : Obs X Z, block false t o = 0 := by
        intro t o
        simp only [block, hk0, IFJ, IFM, Bool.not_false, Bool.true_and,
          beq_self_eq_true, if_true, true_and, mul_zero, add_zero, sub_zero]
      simpa only [hz, mul_zero, integral_zero] using (hasDerivAt_const (0 : ℝ) (0 : ℝ))
    · exact population_continuous_first_band_admissible_quantile_block_orthogonality
        M L h cpi hov del hd k hk hj g false (Or.inr hk0) hb
  have hz := zp.sub zm
  simp only [sub_zero] at hz
  apply hz.congr_of_eventuallyEq
  filter_upwards [population_continuous_first_band_admissible_quantile_block_integrable
    M L cpi hov del hd k hk hj g true hb,
    population_continuous_first_band_admissible_quantile_block_integrable
    M L cpi hov del hd k hk hj g false hb] with t ip im
  change Integrable (fun o : Obs X Z => (path t).gamma g o.1 * block true t o)
    (observationLaw M) at ip
  change Integrable (fun o : Obs X Z => (path t).gamma g o.1 * block false t o)
    (observationLaw M) at im
  symm
  change (∫ o : Obs X Z, (path t).gamma g o.1 * block true t o ∂observationLaw M) -
    (∫ o : Obs X Z, (path t).gamma g o.1 * block false t o ∂observationLaw M) = _
  rw [← integral_sub ip im]
  apply integral_congr_ae
  exact Eventually.of_forall fun o => (mul_sub _ _ _).symm

-- Both interior endpoints use the existing density estimate. Ordering is kept
-- explicit here because the clipped nuisance class does not itself order nu.
-- @node: population_continuous_interior_band_admissible_quantile_block_orthogonality
/-- Under [bounded densities near the band boundaries](hyp:h), [baseline assignment overlap](hyp:hov),
and [a direction admissible at the true continuous nuisance](hyp:hd), take
[an interval index below the number of propensity intervals](hyp:hk) and a band whose
[lower boundary index is at least one](hyp:hj0) and [is strictly below the interval's number of boundaries](hyp:hj).
If [the selected side is the plus side or the interval index is nonzero](hyp:hactive),
[the lower boundary is measurable](hyp:ha), [the upper boundary is measurable](hyp:hb),
and [the moving lower quantile does not exceed the moving upper quantile almost everywhere for all perturbations sufficiently near zero](hyp:horder),
[the population mean of the interior-band quantile score difference, multiplied by the moving product weight, has derivative zero at zero](goal).

The score difference compares moving quantiles with true boundaries while keeping the same moving assignment denominators. -/
lemma population_continuous_interior_band_admissible_quantile_block_orthogonality
    (L : LevelData Z X) (h : BoundaryDensitiesBounded M L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del))
    (k : ℕ) (hk : k < L.K) (j : ℕ) (hj0 : 1 ≤ j) (hj : j < L.l k)
    (g : RegularIndex L) (plus : Bool) (hactive : plus = true ∨ k ≠ 0)
    (ha : Measurable (bandBoundary M L k j))
    (hb : Measurable (bandBoundary M L k (j + 1)))
    (horder : ∀ᶠ t : ℝ in 𝓝 0, ∀ᵐ x ∂xLaw M,
      nuValue M (trueNuisance M L + t • del) k j x ≤
        nuValue M (trueNuisance M L + t • del) k (j + 1) x) :
    let path := fun t : ℝ => trueNuisance M L + t • del
    let e := fun t => {trueNuisance M L with piLev := (path t).piLev, nu := (path t).nu}
    let b := fun t => {trueNuisance M L with piLev := (path t).piLev}
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z, (path t).gamma g o.1 *
      ((IFJ M L (e t) plus k j o + nuValue M (e t) k j o.1 * IFM M L (e t) plus k j o -
        nuValue M (e t) k (j + 1) o.1 * IFM M L (e t) plus k (j + 1) o) -
      (IFJ M L (b t) plus k j o + bandBoundary M L k j o.1 * IFM M L (b t) plus k j o -
        bandBoundary M L k (j + 1) o.1 * IFM M L (b t) plus k (j + 1) o))
      ∂observationLaw M) 0 0 := by
  dsimp only
  let path := fun t : ℝ => trueNuisance M L + t • del
  let e := fun t => {trueNuisance M L with piLev := (path t).piLev, nu := (path t).nu}
  let a : BoundaryIndex L := ⟨(k, j), hk, hj0, Nat.le_of_lt hj⟩
  let b : BoundaryIndex L := ⟨(k, j + 1), hk, by omega, hj⟩
  have hva : k < L.K ∧ 1 ≤ j ∧ j ≤ L.l k := ⟨hk, hj0, by omega⟩
  have hvb : k < L.K ∧ 1 ≤ j + 1 ∧ j + 1 ≤ L.l k := ⟨hk, by omega, hj⟩
  have hna t x : nuValue M (e t) k j x = bandBoundary M L k j x + t * del.nu a x := by
    simp only [e, nuValue, show j ≠ 0 by omega, if_false, dif_pos hva]
    rfl
  have hnb t x : nuValue M (e t) k (j + 1) x =
      bandBoundary M L k (j + 1) x + t * del.nu b x := by
    simp only [e, nuValue, Nat.add_one_ne_zero, if_false, dif_pos hvb]
    rfl
  have hordered : ∀ᶠ t : ℝ in 𝓝 0, ∀ᵐ x ∂xLaw M,
      bandBoundary M L k j x + t * del.nu a x ≤
        bandBoundary M L k (j + 1) x + t * del.nu b x := by
    filter_upwards [horder] with t ht
    change ∀ᵐ x ∂xLaw M, nuValue M (e t) k j x ≤ nuValue M (e t) k (j + 1) x at ht
    simpa only [hna, hnb] using ht
  have hbase : ∀ᵐ x ∂xLaw M, bandBoundary M L k j x ≤ bandBoundary M L k (j + 1) x := by
    simpa only [zero_mul, add_zero] using hordered.self_of_nhds
  obtain ⟨_, _, hdir⟩ := continuous_quantile_direction_regular M L _ del hd
  obtain ⟨r, C, hr, hden⟩ := h
  have hcpi : 0 < cpi := hov.1
  have hz := population_continuous_band_quantile_block_local_orthogonality M L e
    (fun t => (path t).piLev) (fun t => (path t).gamma g) plus k j hk (by omega)
    hactive (del.nu a) (del.nu b) (hdir a).1 (hdir b).1
    (continuous_quantile_direction_memLp M L _ del hd a)
    (continuous_quantile_direction_memLp M L _ del hd b) ha hb hbase
    1 (cpi / 2) r |C| zero_le_one (by positivity) hr (abs_nonneg C)
    (by
      obtain ⟨s, hs, hpath⟩ := hd.admissible
      filter_upwards [continuous_assignment_path_uniform_lower_bound M L cpi hov del hd,
        hordered, continuousAt_id.abs.eventually_lt_const (by simpa using hs)] with t ht ho hst
      have had := hpath t hst
      rcases had with ⟨_, _, _, _, _, hpim, _, _, _, _, _, _, hgb, hgm, _⟩
      refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, hpim, ht, hgm g, ?_⟩
      · exact hna t
      · exact hnb t
      · exact ho
      · filter_upwards [hgb g] with x hx
        change |(trueNuisance M L + t • del).gamma g x| ≤ 1
        simpa only [abs_of_nonneg hx.1] using hx.2)
    (Or.inr (by
      have hi : (if plus then k + 1 else k) = k + 1 ∨
          (1 ≤ k ∧ (if plus then k + 1 else k) = k) := by
        cases plus
        · simp only [Bool.false_eq_true, false_or] at hactive
          exact Or.inr ⟨by omega, rfl⟩
        · exact Or.inl rfl
      filter_upwards [hden k hk j hj0 (by omega) _ hi] with x hx
      intro u v hu huv hv
      exact (hx u v hu huv hv).trans
        (mul_le_mul_of_nonneg_right (le_abs_self C) (sub_nonneg.mpr huv))))
    (by
      have hi : (if plus then k + 1 else k) = k + 1 ∨
          (1 ≤ k ∧ (if plus then k + 1 else k) = k) := by
        cases plus
        · simp only [Bool.false_eq_true, false_or] at hactive
          exact Or.inr ⟨by omega, rfl⟩
        · exact Or.inl rfl
      filter_upwards [hden k hk (j + 1) (by omega) hj _ hi] with x hx
      intro u v hu huv hv
      exact (hx u v hu huv hv).trans
        (mul_le_mul_of_nonneg_right (le_abs_self C) (sub_nonneg.mpr huv)))
  exact hz

-- @node: population_continuous_interior_band_admissible_quantile_block_integrable
/-- Under [baseline assignment overlap](hyp:hov) and [a direction admissible at the true continuous nuisance](hyp:hd),
take [an interval index below the number of propensity intervals](hyp:hk) and a band whose
[lower boundary index is at least one](hyp:hj0) and [is strictly below the interval's number of boundaries](hyp:hj).
If [the lower boundary is measurable](hyp:ha), [the upper boundary is measurable](hyp:hb),
and [the moving lower quantile does not exceed the moving upper quantile almost everywhere for all perturbations sufficiently near zero](hyp:horder),
[the interior-band quantile score difference on either selected side, multiplied by the moving product weight, is integrable for all perturbations sufficiently near zero](goal).

The difference compares moving quantiles with true boundaries under the same moving assignment denominators. -/
lemma population_continuous_interior_band_admissible_quantile_block_integrable
    (L : LevelData Z X) (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del))
    (k : ℕ) (hk : k < L.K) (j : ℕ) (hj0 : 1 ≤ j) (hj : j < L.l k)
    (g : RegularIndex L) (plus : Bool)
    (ha : Measurable (bandBoundary M L k j))
    (hb : Measurable (bandBoundary M L k (j + 1)))
    (horder : ∀ᶠ t : ℝ in 𝓝 0, ∀ᵐ x ∂xLaw M,
      nuValue M (trueNuisance M L + t • del) k j x ≤
        nuValue M (trueNuisance M L + t • del) k (j + 1) x) :
    let path := fun t : ℝ => trueNuisance M L + t • del
    let e := fun t => {trueNuisance M L with piLev := (path t).piLev, nu := (path t).nu}
    let b := fun t => {trueNuisance M L with piLev := (path t).piLev}
    ∀ᶠ t : ℝ in 𝓝 0, Integrable (fun o : Obs X Z => (path t).gamma g o.1 *
      ((IFJ M L (e t) plus k j o + nuValue M (e t) k j o.1 * IFM M L (e t) plus k j o -
        nuValue M (e t) k (j + 1) o.1 * IFM M L (e t) plus k (j + 1) o) -
      (IFJ M L (b t) plus k j o + bandBoundary M L k j o.1 * IFM M L (b t) plus k j o -
        bandBoundary M L k (j + 1) o.1 * IFM M L (b t) plus k (j + 1) o)))
      (observationLaw M) := by
  dsimp only
  let path := fun t : ℝ => trueNuisance M L + t • del
  let e := fun t => {trueNuisance M L with piLev := (path t).piLev, nu := (path t).nu}
  let a : BoundaryIndex L := ⟨(k, j), hk, hj0, Nat.le_of_lt hj⟩
  let b : BoundaryIndex L := ⟨(k, j + 1), hk, by omega, hj⟩
  have hva : k < L.K ∧ 1 ≤ j ∧ j ≤ L.l k := ⟨hk, hj0, Nat.le_of_lt hj⟩
  have hvb : k < L.K ∧ 1 ≤ j + 1 ∧ j + 1 ≤ L.l k := ⟨hk, by omega, hj⟩
  have hcpi : 0 < cpi := hov.1
  have : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  obtain ⟨_, _, hdir⟩ := continuous_quantile_direction_regular M L _ del hd
  have hdam := (hdir a).1
  have hdbm := (hdir b).1
  have hia : Integrable (del.nu a) (xLaw M) :=
    (continuous_quantile_direction_memLp M L _ del hd a).integrable (by norm_num)
  have hib : Integrable (del.nu b) (xLaw M) :=
    (continuous_quantile_direction_memLp M L _ del hd b).integrable (by norm_num)
  have hna t x : nuValue M (e t) k j x = bandBoundary M L k j x + t * del.nu a x := by
    simp only [e, nuValue, show j ≠ 0 by omega, if_false, dif_pos hva]
    rfl
  have hnb t x : nuValue M (e t) k (j + 1) x =
      bandBoundary M L k (j + 1) x + t * del.nu b x := by
    simp only [e, nuValue, Nat.add_one_ne_zero, if_false, dif_pos hvb]
    rfl
  have hordered : ∀ᶠ t : ℝ in 𝓝 0, ∀ᵐ x ∂xLaw M,
      bandBoundary M L k j x + t * del.nu a x ≤
        bandBoundary M L k (j + 1) x + t * del.nu b x := by
    filter_upwards [horder] with t ht
    change ∀ᵐ x ∂xLaw M, nuValue M (e t) k j x ≤ nuValue M (e t) k (j + 1) x at ht
    simpa only [hna, hnb] using ht
  have hbase : ∀ᵐ x ∂xLaw M, bandBoundary M L k j x ≤ bandBoundary M L k (j + 1) x := by
    simpa only [zero_mul, add_zero] using hordered.self_of_nhds
  obtain ⟨r, hr, hpath⟩ := hd.admissible
  filter_upwards [continuous_assignment_path_uniform_lower_bound M L cpi hov del hd,
    hordered, continuousAt_id.abs.eventually_lt_const (by simpa using hr)] with t ht ho htr
  have had : ContAdmissible M L (path t) := hpath t htr
  rcases had with ⟨_, _, _, _, _, hpim, _, _, _, _, _, _, hgb, hgm, _⟩
  have hwm := hgm g
  have hwb : ∀ᵐ x ∂xLaw M, |(path t).gamma g x| ≤ 1 := by
    filter_upwards [hgb g] with x hx
    simpa only [abs_of_nonneg hx.1] using hx.2
  have iwa : Integrable (fun x => (path t).gamma g x * (t * del.nu a x)) (xLaw M) :=
    (hia.const_mul t).bdd_mul hwm.aestronglyMeasurable
      (by simpa only [Real.norm_eq_abs] using hwb)
  have iwb : Integrable (fun x => (path t).gamma g x * (t * del.nu b x)) (xLaw M) :=
    (hib.const_mul t).bdd_mul hwm.aestronglyMeasurable
      (by simpa only [Real.norm_eq_abs] using hwb)
  have ia := population_IFM_fitted_denominator_integrable M L (path t).piLev hpim
    (cpi / 2) (by positivity) ht plus k j hk (by omega) ha
    (fun x => (path t).gamma g x * (t * del.nu a x)) (by fun_prop) iwa
  have ib := population_IFM_fitted_denominator_integrable M L (path t).piLev hpim
    (cpi / 2) (by positivity) ht plus k (j + 1) hk hj hb
    (fun x => (path t).gamma g x * (t * del.nu b x)) (by fun_prop) iwb
  by_cases hactive : plus = true ∨ k ≠ 0
  · let i : ℕ := if plus then k + 1 else k
    have hi : 1 ≤ i ∧ i ≤ L.K := by
      cases plus
      · simp only [Bool.false_eq_true, false_or] at hactive
        simp only [i, Bool.false_eq_true, if_false]
        omega
      · simp only [i, if_true]
        omega
    have hskip : (!plus && k == 0) = false := by
      cases plus
      · simp only [Bool.false_eq_true, false_or] at hactive
        simp [hactive]
      · simp
    have hcm : Measurable (positiveValue (path t).piLev i) := by
      unfold positiveValue
      simpa only [positiveValue, dif_pos hi] using hpim ⟨i, hi⟩
    have hcl : ∀ᵐ x ∂xLaw M, cpi / 2 ≤ positiveValue (path t).piLev i x := by
      simpa only [positiveValue, dif_pos hi] using ht ⟨i, hi⟩
    have ir := population_observed_band_boundary_integrable M L i
      (bandBoundary M L k j) (bandBoundary M L k (j + 1)) (fun x => bandBoundary M L k j x + t * del.nu a x)
      (fun x => bandBoundary M L k (j + 1) x + t * del.nu b x)
      ((path t).gamma g) (positiveValue (path t).piLev i)
      ha hb (by fun_prop) (by fun_prop) hwm hcm hbase ho
      (by simpa only [add_sub_cancel_left] using hia.const_mul t)
      (by simpa only [add_sub_cancel_left] using hib.const_mul t)
      1 (cpi / 2) zero_le_one (by positivity) hwb hcl
    have hir : Integrable (fun o : Obs X Z => (path t).gamma g o.1 *
        ((if !plus && k == 0 then 0 else
          indicator (o.2.1 ∈ L.S (if plus then k + 1 else k)) * o.2.2.1 /
            positiveValue (path t).piLev (if plus then k + 1 else k) o.1) *
          continuousDebiasedBandBoundary (bandBoundary M L k j o.1)
            (bandBoundary M L k (j + 1) o.1)
            (nuValue M (e t) k j o.1) (nuValue M (e t) k (j + 1) o.1) o.2.2.2))
        (observationLaw M) := by
      simpa only [hskip, Bool.false_eq_true, if_false, hna, hnb, i,
        bandBoundary, true_or, if_true] using ir
    have hz := (population_continuous_band_quantile_difference_mean M L (e t)
      (path t).piLev hpim rfl rfl rfl rfl rfl plus k j hk (by omega) ha hb
      ((path t).gamma g) (fun x => t * del.nu a x) (fun x => t * del.nu b x)
      (by fun_prop) (by fun_prop)
      (by intro x; rw [hna]; ring)
      (by intro x; rw [hnb]; ring)
      (by simpa only [mul_zero] using ia) ib hir).1
    exact hz
  · have hk0 : k = 0 := by tauto
    have hp : plus = false := by
      cases plus
      · rfl
      · exact False.elim (hactive (Or.inl rfl))
    subst k
    subst plus
    simp only [IFJ, IFM, Bool.not_false, Bool.true_and, beq_self_eq_true,
      if_true, true_and, add_zero, mul_zero, sub_zero]
    have : IsProbabilityMeasure (observationLaw M) := by
      unfold observationLaw
      exact Measure.isProbabilityMeasure_map
        (M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY))).aemeasurable
    exact integrable_const 0

-- Signed cancellation follows by integrable subtraction of the two sides.
-- @node: population_continuous_interior_band_admissible_signed_quantile_block_orthogonality
/-- Assume [bounded densities near the band boundaries](hyp:h), [baseline assignment overlap](hyp:hov),
and [a direction admissible at the true continuous nuisance](hyp:hd).
For [an interval index below the number of propensity intervals](hyp:hk) and a band whose
[lower boundary index is at least one](hyp:hj0) and [is strictly below the interval's number of boundaries](hyp:hj),
suppose [the lower boundary is measurable](hyp:ha), [the upper boundary is measurable](hyp:hb),
and [the moving lower quantile does not exceed the moving upper quantile almost everywhere for all perturbations sufficiently near zero](hyp:horder).
Then [the population mean of the plus-side minus minus-side interior-band quantile score differences, multiplied by the moving product weight, has derivative zero at zero](goal).

Each difference compares moving quantiles with true boundaries using the same moving assignment denominators. -/
lemma population_continuous_interior_band_admissible_signed_quantile_block_orthogonality
    (L : LevelData Z X) (h : BoundaryDensitiesBounded M L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del))
    (k : ℕ) (hk : k < L.K) (j : ℕ) (hj0 : 1 ≤ j) (hj : j < L.l k)
    (g : RegularIndex L) (ha : Measurable (bandBoundary M L k j))
    (hb : Measurable (bandBoundary M L k (j + 1)))
    (horder : ∀ᶠ t : ℝ in 𝓝 0, ∀ᵐ x ∂xLaw M,
      nuValue M (trueNuisance M L + t • del) k j x ≤
        nuValue M (trueNuisance M L + t • del) k (j + 1) x) :
    let path := fun t : ℝ => trueNuisance M L + t • del
    let e := fun t => {trueNuisance M L with piLev := (path t).piLev, nu := (path t).nu}
    let b := fun t => {trueNuisance M L with piLev := (path t).piLev}
    let block := fun plus t (o : Obs X Z) =>
      (IFJ M L (e t) plus k j o + nuValue M (e t) k j o.1 * IFM M L (e t) plus k j o -
        nuValue M (e t) k (j + 1) o.1 * IFM M L (e t) plus k (j + 1) o) -
      (IFJ M L (b t) plus k j o + bandBoundary M L k j o.1 * IFM M L (b t) plus k j o -
        bandBoundary M L k (j + 1) o.1 * IFM M L (b t) plus k (j + 1) o)
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z, (path t).gamma g o.1 *
      (block true t o - block false t o) ∂observationLaw M) 0 0 := by
  let path := fun t : ℝ => trueNuisance M L + t • del
  let e := fun t => {trueNuisance M L with piLev := (path t).piLev, nu := (path t).nu}
  let b := fun t => {trueNuisance M L with piLev := (path t).piLev}
  let block := fun plus t (o : Obs X Z) =>
    (IFJ M L (e t) plus k j o + nuValue M (e t) k j o.1 * IFM M L (e t) plus k j o -
      nuValue M (e t) k (j + 1) o.1 * IFM M L (e t) plus k (j + 1) o) -
    (IFJ M L (b t) plus k j o + bandBoundary M L k j o.1 * IFM M L (b t) plus k j o -
      bandBoundary M L k (j + 1) o.1 * IFM M L (b t) plus k (j + 1) o)
  change HasDerivAt (fun t : ℝ => ∫ o : Obs X Z, (path t).gamma g o.1 *
    (block true t o - block false t o) ∂observationLaw M) 0 0
  have zp : HasDerivAt (fun t : ℝ => ∫ o : Obs X Z,
      (path t).gamma g o.1 * block true t o ∂observationLaw M) 0 0 :=
    population_continuous_interior_band_admissible_quantile_block_orthogonality
      M L h cpi hov del hd k hk j hj0 hj g true (Or.inl rfl) ha hb horder
  have zm : HasDerivAt (fun t : ℝ => ∫ o : Obs X Z,
      (path t).gamma g o.1 * block false t o ∂observationLaw M) 0 0 := by
    by_cases hk0 : k = 0
    · have hz : ∀ t, ∀ o : Obs X Z, block false t o = 0 := by
        intro t o
        simp only [block, hk0, IFJ, IFM, Bool.not_false, Bool.true_and,
          beq_self_eq_true, if_true, true_and, mul_zero, add_zero, sub_zero]
      simpa only [hz, mul_zero, integral_zero] using (hasDerivAt_const (0 : ℝ) (0 : ℝ))
    · exact population_continuous_interior_band_admissible_quantile_block_orthogonality
        M L h cpi hov del hd k hk j hj0 hj g false (Or.inr hk0) ha hb horder
  have hz := zp.sub zm
  simp only [sub_zero] at hz
  apply hz.congr_of_eventuallyEq
  filter_upwards [population_continuous_interior_band_admissible_quantile_block_integrable
    M L cpi hov del hd k hk j hj0 hj g true ha hb horder,
    population_continuous_interior_band_admissible_quantile_block_integrable
    M L cpi hov del hd k hk j hj0 hj g false ha hb horder] with t ip im
  change Integrable (fun o : Obs X Z => (path t).gamma g o.1 * block true t o)
    (observationLaw M) at ip
  change Integrable (fun o : Obs X Z => (path t).gamma g o.1 * block false t o)
    (observationLaw M) at im
  symm
  change (∫ o : Obs X Z, (path t).gamma g o.1 * block true t o ∂observationLaw M) -
    (∫ o : Obs X Z, (path t).gamma g o.1 * block false t o ∂observationLaw M) = _
  rw [← integral_sub ip im]
  apply integral_congr_ae
  exact Eventually.of_forall fun o => (mul_sub _ _ _).symm

end Papers.TbsPrteOptimalTransport

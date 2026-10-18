module
public import Papers.TbsExtremeEffects.Helpers.Hill.QuantileContinuity
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Construction and full tail range of the reciprocal-survival quantile. -/

public section
namespace Papers.TbsExtremeEffects
open Filter Set MeasureTheory
open scoped Topology

/-- If [survival is continuous on the tail ray](hyp:hc), [vanishes at infinity](hyp:hzero), and [the target level is positive](hyp:hy) and [no greater than survival at the tail start](hyp:hya), then [some point on that ray attains the target survival level](goal). -/
-- @node: hill_survival_tail_level_attained
lemma hill_survival_tail_level_attained (S : ℝ → ℝ) {a y : ℝ}
    (hc : ContinuousOn S (Ici a)) (hzero : Tendsto S atTop (𝓝 0))
    (hy : 0 < y) (hya : y ≤ S a) : ∃ x ≥ a, S x = y := by
  obtain ⟨b, hb⟩ := eventually_atTop.mp ((tendsto_order.mp hzero).2 y hy)
  let r := max a b
  have har : a ≤ r := le_max_left _ _
  have hry : S r ≤ y := (hb r (le_max_right _ _)).le
  obtain ⟨x, hx, hxy⟩ := intermediate_value_Icc' har
    (hc.mono (fun z hz => hz.1)) ⟨hry, hya⟩
  exact ⟨x, hx.1, hxy⟩

/-- If [the base level is positive](hyp:hv₀), [survival strictly decreases on the tail ray](hyp:hS), [it remains positive there](hyp:hpos), and [the quantile has reciprocal survival for all tail levels](hyp:hQ), then [every radius above a tail quantile is itself reached by a weakly larger quantile level](goal). -/
-- @node: hill_quantile_tail_range_of_strict_survival
lemma hill_quantile_tail_range_of_strict_survival (S Q : ℝ → ℝ) {a v₀ : ℝ}
    (hv₀ : 0 < v₀) (hS : StrictAntiOn S (Ici a))
    (hpos : ∀ x ≥ a, 0 < S x)
    (hQ : ∀ v ≥ v₀, a ≤ Q v ∧ S (Q v) = v⁻¹) :
    ∀ w ≥ v₀, ∀ x > Q w, ∃ z ≥ w, Q z = x := by
  intro w hw x hx
  have hwpos : 0 < w := hv₀.trans_le hw
  have hax : a ≤ x := (hQ w hw).1.trans hx.le
  have hSx : 0 < S x := hpos x hax
  have hlt : S x < w⁻¹ := by
    rw [← (hQ w hw).2]
    exact hS (hQ w hw).1 hax hx
  have hwz : w ≤ (S x)⁻¹ := by
    have := (inv_lt_inv₀ (inv_pos.mpr hwpos) hSx).2 hlt
    simpa only [inv_inv] using this.le
  obtain ⟨haQ, hSQ⟩ := hQ ((S x)⁻¹) (hw.trans hwz)
  refine ⟨(S x)⁻¹, hwz, hS.injOn haQ hax ?_⟩
  simpa only [inv_inv] using hSQ

/-- If [the base level is positive](hyp:hv₀), [survival is continuous on the tail ray](hyp:hc), [strictly decreases there](hyp:hS), [stays positive there](hyp:hpos), [tends to zero at infinity](hyp:hzero), and [the reciprocal base level does not exceed initial survival](hyp:hbase), then [there is a quantile with reciprocal survival and full tail range](goal). -/
-- @node: hill_exists_reciprocal_survival_quantile
lemma hill_exists_reciprocal_survival_quantile (S : ℝ → ℝ) {a v₀ : ℝ}
    (hv₀ : 0 < v₀) (hc : ContinuousOn S (Ici a))
    (hS : StrictAntiOn S (Ici a)) (hpos : ∀ x ≥ a, 0 < S x)
    (hzero : Tendsto S atTop (𝓝 0)) (hbase : v₀⁻¹ ≤ S a) :
    ∃ Q : ℝ → ℝ, ∀ w ≥ v₀,
      a ≤ Q w ∧ S (Q w) = w⁻¹ ∧
      (∀ x > Q w, ∃ z ≥ w, Q z = x) := by
  classical
  have hex : ∀ v : ℝ, ∃ x : ℝ, v₀ ≤ v → a ≤ x ∧ S x = v⁻¹ := by
    intro v
    by_cases hv : v₀ ≤ v
    · obtain ⟨x, hax, hx⟩ := hill_survival_tail_level_attained S hc hzero
        (inv_pos.mpr (hv₀.trans_le hv))
        (((inv_le_inv₀ (hv₀.trans_le hv) hv₀).2 hv).trans hbase)
      exact ⟨x, fun _ => ⟨hax, hx⟩⟩
    · exact ⟨a, fun h => (hv h).elim⟩
  choose Q hQ using hex
  refine ⟨Q, ?_⟩
  intro w hw
  exact ⟨(hQ w hw).1, (hQ w hw).2,
    hill_quantile_tail_range_of_strict_survival S Q hv₀ hS hpos hQ w hw⟩

/-- [The survival probability of every finite radial law tends to zero as the radius tends to infinity](goal). -/
-- @node: hill_finite_survival_tendsto_zero
lemma hill_finite_survival_tendsto_zero (nu : Measure ℝ) [IsFiniteMeasure nu] :
    Tendsto (fun r => nu.real (Ioi r)) atTop (𝓝 0) := by
  have hempty : (⋂ r : ℝ, Ioi r) = ∅ := by
    ext x
    simp only [mem_iInter, mem_Ioi, mem_empty_iff_false, iff_false]
    exact fun h => (lt_irrefl x) (h x)
  have hlim := tendsto_measure_iInter_atTop
    (fun r : ℝ => (measurableSet_Ioi (a := r)).nullMeasurableSet (μ := nu))
    (fun r s hrs => Ioi_subset_Ioi hrs) ⟨0, measure_ne_top nu _⟩
  rw [hempty, measure_empty] at hlim
  simpa only [Function.comp_def, ENNReal.toReal_zero, Measure.real] using
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim

/-- If [the density is measurable](hyp:hf), [the law agrees with that density beyond the cutoff](hyp:hLaw), [the chosen ray starts beyond the cutoff](hyp:ha), [the density is continuous on that ray](hyp:hc), and [it is positive there](hyp:hp), then [the survival function is continuous and strictly decreasing on the ray](goal). -/
-- @node: hill_survival_strictAntiOn_of_positive_tail_density
lemma hill_survival_strictAntiOn_of_positive_tail_density
    (nu : Measure ℝ) [IsFiniteMeasure nu] (f : ℝ → ℝ) {cutoff a : ℝ}
    (hf : Measurable f)
    (hLaw : ∀ r > cutoff, nu (Ioi r) =
      (volume.withDensity (fun x => ENNReal.ofReal (f x))) (Ioi r))
    (ha : cutoff < a) (hc : ∀ r ≥ a, ContinuousAt f r)
    (hp : ∀ r ≥ a, 0 < f r) :
    ContinuousOn (fun r => nu.real (Ioi r)) (Ici a) ∧
      StrictAntiOn (fun r => nu.real (Ioi r)) (Ici a) := by
  have hderiv : ∀ r ≥ a, HasDerivAt (fun y => nu.real (Ioi y)) (-f r) r := by
    intro r hr
    exact hill_survival_hasDerivAt_of_tail_density nu f hf hLaw
      (ha.trans_le hr) (hc r hr) (hp r hr).le
  have hcont : ContinuousOn (fun r => nu.real (Ioi r)) (Ici a) :=
    fun r hr => (hderiv r hr).continuousAt.continuousWithinAt
  refine ⟨hcont, strictAntiOn_of_deriv_neg (convex_Ici a) hcont ?_⟩
  intro r hr
  have har : a ≤ r := interior_subset hr
  rw [(hderiv r har).deriv]
  exact neg_neg_of_pos (hp r har)

/-- If [the density is measurable](hyp:hf), [the radial law agrees with that density beyond the cutoff](hyp:hLaw), [the tail ray begins past the cutoff](hyp:ha), [the density is continuous there](hyp:hc), and [positive there](hyp:hp), then [there are a base level and quantile with reciprocal radial survival and full tail range](goal). -/
-- @node: hill_exists_quantile_of_positive_tail_density
lemma hill_exists_quantile_of_positive_tail_density
    (nu : Measure ℝ) [IsFiniteMeasure nu] (f : ℝ → ℝ) {cutoff a : ℝ}
    (hf : Measurable f)
    (hLaw : ∀ r > cutoff, nu (Ioi r) =
      (volume.withDensity (fun x => ENNReal.ofReal (f x))) (Ioi r))
    (ha : cutoff < a) (hc : ∀ r ≥ a, ContinuousAt f r)
    (hp : ∀ r ≥ a, 0 < f r) :
    ∃ (Q : ℝ → ℝ) (v₀ : ℝ), 1 < v₀ ∧ ∀ w ≥ v₀,
      a ≤ Q w ∧ nu.real (Ioi (Q w)) = w⁻¹ ∧
      (∀ x > Q w, ∃ z ≥ w, Q z = x) := by
  let S : ℝ → ℝ := fun r => nu.real (Ioi r)
  obtain ⟨hcont, hanti⟩ := hill_survival_strictAntiOn_of_positive_tail_density
    nu f hf hLaw ha hc hp
  have hpos : ∀ r ≥ a, 0 < S r := by
    intro r hr
    have hlt := hanti hr (by linarith : a ≤ r + 1) (by linarith : r < r + 1)
    exact (measureReal_nonneg : 0 ≤ nu.real (Ioi (r + 1))).trans_lt hlt
  let v₀ := max 2 (S a)⁻¹
  have hv₀ : 1 < v₀ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hbase : v₀⁻¹ ≤ S a := by
    have h := (inv_le_inv₀ (zero_lt_one.trans hv₀) (inv_pos.mpr (hpos a le_rfl))).2
      (le_max_right 2 (S a)⁻¹)
    simpa only [inv_inv] using h
  obtain ⟨Q, hQ⟩ := hill_exists_reciprocal_survival_quantile S (zero_lt_one.trans hv₀)
    hcont hanti hpos (hill_finite_survival_tendsto_zero nu) hbase
  exact ⟨Q, v₀, hv₀, hQ⟩

end Papers.TbsExtremeEffects

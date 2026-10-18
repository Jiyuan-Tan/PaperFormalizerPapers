module
public import Papers.TbsPrteOptimalTransport.Basic
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.SpecificLimits.Basic
/-! Measurability of the policy derivative on a measurable propensity graph.
Difference quotients approach from inside the policy domain, including its endpoints. -/
public section
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Set Filter
open scoped Topology

universe v

-- @node: policy_derivative_graph_measurable
/-- If [the policy map is jointly measurable and maps unit-interval
propensities to the unit interval](hyp:hp), [its derivative with respect to
propensity is given by the derivative function on the unit interval](hyp:hd),
[the propensity is jointly measurable in instrument and covariates](hyp:hm),
and [all propensity values lie in the unit interval](hyp:hr), then
[the policy derivative evaluated at that propensity is jointly measurable in
instrument and covariates](goal). -/
lemma policy_derivative_graph_measurable {X Z : Type v}
    [MeasurableSpace X] [MeasurableSpace Z]
    (phi dphi : Z → X → ℝ → ℝ) (hp : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (p : Z → X → ℝ)
    (hm : Measurable (fun zx : Z × X => p zx.1 zx.2))
    (hr : ∀ z x, p z x ∈ Icc (0 : ℝ) 1) :
    Measurable (fun zx : Z × X => dphi zx.1 zx.2 (p zx.1 zx.2)) := by
  let r : Z × X → ℝ := fun zx => if p zx.1 zx.2 ≤ 1 / 2 then 1 else 0
  have hmr : Measurable r := by
    exact Measurable.ite (measurableSet_le hm measurable_const) measurable_const measurable_const
  let e : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have he : ∀ n, 0 < e n ∧ e n ≤ 1 := by
    intro n
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    dsimp [e]
    constructor
    · positivity
    · apply (div_le_one₀ (by positivity)).2
      linarith
  let a : ℕ → Z × X → ℝ := fun n zx => (1 - e n) * p zx.1 zx.2 + e n * r zx
  have hma : ∀ n, Measurable (a n) := by
    intro n
    fun_prop
  have ha : ∀ n zx, a n zx ∈ Icc (0 : ℝ) 1 ∧ a n zx ≠ p zx.1 zx.2 := by
    intro n zx
    have hh := hr zx.1 zx.2
    have hn := he n
    dsimp [a, r]
    split_ifs with hc
    · constructor
      · constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hn.2) hh.1,
          mul_nonneg (sub_nonneg.mpr hn.2) (sub_nonneg.mpr hh.2)]
      · intro heq
        nlinarith
    · constructor
      · constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hn.2) hh.1,
          mul_nonneg (sub_nonneg.mpr hn.2) (sub_nonneg.mpr hh.2)]
      · intro heq
        have hc' : 1 / 2 < p zx.1 zx.2 := lt_of_not_ge hc
        nlinarith
  have hv : ∀ f : Z × X → ℝ, Measurable f →
      (∀ zx, f zx ∈ Icc (0 : ℝ) 1) →
      Measurable (fun zx : Z × X => phi zx.1 zx.2 (f zx)) := by
    intro f hf hfr
    exact hp.1.comp (measurable_fst.prodMk
      (measurable_snd.prodMk (hf.subtype_mk (h := hfr))))
  let q : ℕ → Z × X → ℝ := fun n zx =>
    (phi zx.1 zx.2 (a n zx) - phi zx.1 zx.2 (p zx.1 zx.2)) / (a n zx - p zx.1 zx.2)
  apply measurable_of_tendsto_metrizable (f := q)
  · intro n
    exact ((hv (a n) (hma n) (fun zx => (ha n zx).1)).sub
      (hv (fun zx => p zx.1 zx.2) hm (fun zx => hr zx.1 zx.2))).div
        ((hma n).sub hm)
  · apply tendsto_pi_nhds.mpr
    intro zx
    have ht : Tendsto e atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have ht' : Tendsto (fun n => a n zx) atTop (nhds (p zx.1 zx.2)) := by
      have hh := (((tendsto_const_nhds (x := (1 : ℝ))).sub ht).mul_const (p zx.1 zx.2)).add
        (ht.mul_const (r zx))
      simpa only [sub_zero, one_mul, zero_mul, add_zero] using hh
    have hwithin : Tendsto (fun n => a n zx) atTop
        (nhdsWithin (p zx.1 zx.2) (Icc 0 1 \ {p zx.1 zx.2})) := by
      apply tendsto_nhdsWithin_iff.mpr
      exact ⟨ht', Filter.Eventually.of_forall (fun n =>
        ⟨(ha n zx).1, by simpa only [mem_singleton_iff] using (ha n zx).2⟩)⟩
    have hh := (hasDerivWithinAt_iff_tendsto_slope.mp
      (hd zx.1 zx.2 (p zx.1 zx.2) (hr zx.1 zx.2))).comp hwithin
    simpa only [q, Function.comp_def, slope_def_field] using hh

end Papers.TbsPrteOptimalTransport

module

public import Papers.HawkesD75660b.Helpers.AnalyticBorel.RootedTreeDerivative
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-! Identification of the rooted-tree series on its subcritical branch. -/

@[expose] public section

noncomputable section

open Filter Topology

namespace Papers.HawkesD75660b.AnalyticBorel

/-- For [a real argument z](hyp:z), the [rooted-tree normalization ratio](goal)
is the rooted-tree series value times the exponential of its negative, divided
by z. -/
-- @node: Papers.HawkesD75660b.AnalyticBorel.rootedTreeNormalizationRatio
def rootedTreeNormalizationRatio (z : ℝ) : ℝ :=
  rootedTreeSeries z * Real.exp (-rootedTreeSeries z) / z

/-- If [z is positive](hyp:hz) and [less than exp(−1)](hyp:hzlt), then
[the rooted-tree normalization ratio has derivative zero at z](goal). -/
-- @node: Papers.HawkesD75660b.AnalyticBorel.rootedTreeNormalizationRatio_hasDerivAt
lemma rootedTreeNormalizationRatio_hasDerivAt {z : ℝ} (hz : 0 < z)
    (hzlt : z < Real.exp (-1)) : HasDerivAt rootedTreeNormalizationRatio 0 z := by
  have ht := rootedTreeSeries_hasDerivAt (by rwa [abs_of_pos hz])
  have hd : HasDerivAt rootedTreeSeries (deriv rootedTreeSeries z) z := by
    rwa [ht.deriv]
  have hc := rootedTreeSeries_differential hz.le hzlt
  convert (hd.mul ((Real.hasDerivAt_exp _).comp z hd.neg)).div (hasDerivAt_id z)
    hz.ne' using 1 <;> try rfl
  dsimp
  symm
  apply (div_eq_zero_iff).mpr
  left
  linear_combination (Real.exp (-rootedTreeSeries z)) * hc

/-- [The rooted-tree normalization ratio tends to one as its argument approaches
zero from above](goal). -/
-- @node: Papers.HawkesD75660b.AnalyticBorel.rootedTreeNormalizationRatio_tendsto
lemma rootedTreeNormalizationRatio_tendsto :
    Tendsto rootedTreeNormalizationRatio (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hs := rootedTreeSeries_hasDerivAt_zero.tendsto_slope_zero_right
  simp only [rootedTreeSeries_zero, zero_add, sub_zero, smul_eq_mul] at hs
  have he : Tendsto (fun x => Real.exp (-rootedTreeSeries x))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have h := (Real.continuous_exp.continuousAt.comp
      rootedTreeSeries_hasDerivAt_zero.continuousAt.neg).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa [Function.comp_def, Pi.neg_apply, rootedTreeSeries_zero] using h
  convert hs.mul he using 1
  · funext x
    simp [rootedTreeNormalizationRatio, div_eq_mul_inv, mul_comm, mul_assoc]
  · norm_num

/-- If [z is nonnegative](hyp:hz) and [less than exp(−1)](hyp:hzlt), then
[the rooted-tree series value at z, multiplied by the exponential of its
negative, equals z](goal). -/
-- @node: Papers.HawkesD75660b.AnalyticBorel.rootedTreeSeries_treeArgument
lemma rootedTreeSeries_treeArgument {z : ℝ} (hz : 0 ≤ z)
    (hzlt : z < Real.exp (-1)) :
    rootedTreeSeries z * Real.exp (-rootedTreeSeries z) = z := by
  rcases hz.eq_or_lt with hz0 | hzpos
  · rw [← hz0, rootedTreeSeries_zero]
    simp
  have hd (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) (Real.exp (-1))) :=
    rootedTreeNormalizationRatio_hasDerivAt hx.1 hx.2
  have hc (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) (Real.exp (-1))) :
      rootedTreeNormalizationRatio x = rootedTreeNormalizationRatio z :=
    isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (0 : ℝ) (Real.exp (-1))).isPreconnected
      (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt)
      (fun x hx => (hd x hx).deriv) hx ⟨hzpos, hzlt⟩
  have hev : rootedTreeNormalizationRatio =ᶠ[𝓝[>] (0 : ℝ)]
      (fun _ => rootedTreeNormalizationRatio z) := by
    have hb : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), x < Real.exp (-1) :=
      (eventually_lt_nhds (Real.exp_pos (-1))).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hb] with x hx hb
    exact hc x ⟨hx, hb⟩
  have heq : rootedTreeNormalizationRatio z = 1 :=
    tendsto_nhds_unique tendsto_const_nhds
      (rootedTreeNormalizationRatio_tendsto.congr' hev)
  exact (div_eq_one_iff_eq hzpos.ne').mp heq

/-- If [ρ lies strictly between zero and one](hyp:hρ), then [the rooted-tree
series evaluated at ρ times exp(−ρ) equals ρ](goal). -/
-- @node: Papers.HawkesD75660b.AnalyticBorel.rootedTreeSeries_borel_argument
lemma rootedTreeSeries_borel_argument {ρ : ℝ} (hρ : 0 < ρ ∧ ρ < 1) :
    rootedTreeSeries (ρ * Real.exp (-ρ)) = ρ := by
  have hz : 0 ≤ ρ * Real.exp (-ρ) := (mul_pos hρ.1 (Real.exp_pos _)).le
  have hzlt := borel_tree_argument_lt hρ
  apply treeArgument_injOn
    (show rootedTreeSeries (ρ * Real.exp (-ρ)) ∈ Set.Icc (0 : ℝ) 1 from
      ⟨tsum_nonneg (rootedTreeTerm_nonneg hz), (rootedTreeSeries_lt_one hz hzlt).le⟩)
    ⟨hρ.1.le, hρ.2.le⟩
  exact rootedTreeSeries_treeArgument hz hzlt

end Papers.HawkesD75660b.AnalyticBorel

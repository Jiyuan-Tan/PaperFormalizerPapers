module
public import Papers.TbsExtremeEffects.Helpers.Hill.QuantileDerivative
public import Mathlib.Topology.Order.MonotoneContinuity

/-! Continuity of a reciprocal-survival tail quantile from its range property. -/

public section
namespace Papers.TbsExtremeEffects
open Filter Set
open scoped Topology

/-- If [the base level is positive](hyp:hv₀), [survival is antitone](hyp:hS), and [the quantile has reciprocal survival above the base level](hyp:hInverse), then [the quantile is strictly increasing on that tail](goal). -/
-- @node: hill_quantile_strictMonoOn_of_reciprocal_survival
lemma hill_quantile_strictMonoOn_of_reciprocal_survival (S Q : ℝ → ℝ)
    {v₀ : ℝ} (hv₀ : 0 < v₀) (hS : Antitone S)
    (hInverse : ∀ v ≥ v₀, S (Q v) = v⁻¹) : StrictMonoOn Q (Ici v₀) := by
  intro v hv w hw hvw
  have hvpos : 0 < v := hv₀.trans_le hv
  have hwpos : 0 < w := hv₀.trans_le hw
  have hrecip : w⁻¹ < v⁻¹ := (inv_lt_inv₀ hwpos hvpos).2 hvw
  by_contra hnot
  have hle := hS (le_of_not_gt hnot)
  rw [hInverse v hv, hInverse w hw] at hle
  exact (not_le_of_gt hrecip) hle

/-- If [the base level is positive](hyp:hv₀), [survival is antitone](hyp:hS), [the quantile has reciprocal survival on the tail](hyp:hInverse), [every radius above the initial quantile is in its tail range](hyp:hRange), and [the evaluation level is above the base level](hyp:hv), then [the quantile is continuous at that level](goal). -/
-- @node: hill_quantile_continuousAt_of_tail_range
lemma hill_quantile_continuousAt_of_tail_range (S Q : ℝ → ℝ)
    {v₀ v : ℝ} (hv₀ : 0 < v₀) (hS : Antitone S)
    (hInverse : ∀ w ≥ v₀, S (Q w) = w⁻¹)
    (hRange : ∀ x > Q v₀, ∃ w ≥ v₀, Q w = x) (hv : v₀ < v) :
    ContinuousAt Q v := by
  have hmono := hill_quantile_strictMonoOn_of_reciprocal_survival S Q hv₀ hS hInverse
  have hQlt : Q v₀ < Q v := hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hv.le) hv
  apply hmono.continuousAt_of_exists_between (Ici_mem_nhds hv)
  · intro b hb
    obtain ⟨x, hxlow, hxhigh⟩ := exists_between (max_lt hQlt hb)
    obtain ⟨w, hw, hQw⟩ := hRange x ((le_max_left _ _).trans_lt hxlow)
    exact ⟨w, hw, by rw [hQw]; exact ⟨((le_max_right _ _).trans_lt hxlow).le, hxhigh⟩⟩
  · intro b hb
    obtain ⟨x, hxlow, hxhigh⟩ := exists_between hb
    obtain ⟨w, hw, hQw⟩ := hRange x (hQlt.trans hxlow)
    exact ⟨w, hw, by rw [hQw]; exact ⟨hxlow, hxhigh.le⟩⟩

/-- If [the quantile has reciprocal survival from the base level onward](hyp:hInverse) and [the evaluation level is strictly above that base](hyp:hv), then [the reciprocal-survival identity holds in a neighborhood of the evaluation level](goal). -/
-- @node: hill_quantile_eventually_reciprocal_survival
lemma hill_quantile_eventually_reciprocal_survival (S Q : ℝ → ℝ)
    {v₀ v : ℝ} (hInverse : ∀ w ≥ v₀, S (Q w) = w⁻¹) (hv : v₀ < v) :
    ∀ᶠ w in 𝓝 v, S (Q w) = w⁻¹ := by
  filter_upwards [Ici_mem_nhds hv] with w hw
  exact hInverse w hw

end Papers.TbsExtremeEffects

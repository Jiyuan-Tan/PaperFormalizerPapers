module
public import Papers.TsAdaptiveEstimationInference.Helpers.IterTRAESetup
/-! Extend eventual rate bounds over a finite prefix by boundedness. -/
public section
namespace Papers.TsAdaptiveEstimationInference
open Filter
open scoped Topology

/-- If [both rate scales are positive from the minimum sample size onward](hyp:hpositive),
[both quantities are uniformly bounded on their events over that range](hyp:hbounded),
and [eventually both satisfy their respective rate bounds with one positive
constant](hyp:htail), then [one positive constant gives both rate bounds on every
event from the minimum sample size onward](goal). -/
-- @node: iterTrae_rates_finite_prefix
lemma iterTrae_rates_finite_prefix {Ω : Type*} (E : ℕ → Set Ω)
    (u v : ℕ → Ω → ℝ) (r s : ℕ → ℝ) (Nmin : ℕ) (M : ℝ)
    (hpositive : ∀ n, Nmin ≤ n → 0 < r n ∧ 0 < s n)
    (hbounded : ∀ n, Nmin ≤ n → ∀ ω ∈ E n, u n ω ≤ M ∧ v n ω ≤ M)
    (htail : ∃ C > 0, ∀ᶠ n in atTop, ∀ ω ∈ E n,
      u n ω ≤ C * r n ∧ v n ω ≤ C * s n) :
    ∃ C > 0, ∀ n, Nmin ≤ n → ∀ ω ∈ E n,
      u n ω ≤ C * r n ∧ v n ω ≤ C * s n := by
  classical
  obtain ⟨Ct, hCt, htail⟩ := htail
  obtain ⟨N, hN⟩ := eventually_atTop.1 htail
  let F := fun n => max 0 (max (M / r n) (M / s n))
  have hF (n : ℕ) : 0 ≤ F n := le_max_left _ _
  let C := Ct + ∑ n ∈ Finset.range N, F n
  have hsum : 0 ≤ ∑ n ∈ Finset.range N, F n :=
    Finset.sum_nonneg fun n _ => hF n
  have hCtC : Ct ≤ C := by dsimp [C]; linarith
  refine ⟨C, hCt.trans_le hCtC, ?_⟩
  intro n hn ω hω
  obtain ⟨hr, hs⟩ := hpositive n hn
  by_cases hnN : N ≤ n
  · obtain ⟨hu, hv⟩ := hN n hnN ω hω
    exact ⟨hu.trans (mul_le_mul_of_nonneg_right hCtC hr.le),
      hv.trans (mul_le_mul_of_nonneg_right hCtC hs.le)⟩
  · have hFC : F n ≤ C := by
      have hi : F n ≤ ∑ k ∈ Finset.range N, F k :=
        Finset.single_le_sum (fun k _ => hF k) (Finset.mem_range.mpr (by omega))
      dsimp [C]
      linarith
    have hrC : M / r n ≤ C :=
      ((le_max_left _ _).trans (le_max_right _ _)).trans hFC
    have hsC : M / s n ≤ C :=
      ((le_max_right _ _).trans (le_max_right _ _)).trans hFC
    obtain ⟨hu, hv⟩ := hbounded n hn ω hω
    exact ⟨hu.trans ((div_le_iff₀ hr).1 hrC), hv.trans ((div_le_iff₀ hs).1 hsC)⟩

end Papers.TsAdaptiveEstimationInference

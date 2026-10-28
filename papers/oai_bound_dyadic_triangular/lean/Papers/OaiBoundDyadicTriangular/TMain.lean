module

public import Papers.OaiBoundDyadicTriangular.Helpers.StepSummation
public import Papers.OaiBoundDyadicTriangular.Helpers.DyadicApproximation

/-! # The dyadic triangular bound -/

public section

open MeasureTheory
open scoped BigOperators

namespace Papers.OaiBoundDyadicTriangular

-- @node: mainInputs_continuityInputs
/-- If [each input function is measurable after extension by zero outside the
nonnegative quadrant, bounded on that quadrant, and zero there outside a
bounded rectangle](hyp:hF), then [each belongs to L³ for Lebesgue measure on
the quadrant](goal). -/
lemma mainInputs_continuityInputs (F : Fin 3 → ℝ × ℝ → ℝ) (hF : MainInputs F) :
    ContinuityInputs F := by
  intro v
  obtain ⟨hMeasurable, ⟨C, hC⟩, R, hR⟩ := hF v
  let B : Set (ℝ × ℝ) := Set.Icc 0 R ×ˢ Set.Icc 0 R
  have hB : MeasurableSet B := measurableSet_Icc.prod measurableSet_Icc
  have hFinite : volume B ≠ ⊤ := (isCompact_Icc.prod isCompact_Icc).measure_ne_top
  have hBox : MemLp (B.indicator (fun _ => max C 0)) 3 (volume : Measure (ℝ × ℝ)) :=
    memLp_indicator_const 3 hB (max C 0) (Or.inr hFinite)
  have hMeas : AEStronglyMeasurable ((Rplus ×ˢ Rplus).indicator (F v))
      (volume : Measure (ℝ × ℝ)) := by fun_prop
  have hDom (x : ℝ × ℝ) : ‖(Rplus ×ˢ Rplus).indicator (F v) x‖ ≤
      B.indicator (fun _ => max C 0) x := by
    by_cases hx : x ∈ Rplus ×ˢ Rplus
    · rw [Set.indicator_of_mem hx]
      by_cases hb : x ∈ B
      · rw [Set.indicator_of_mem hb, Real.norm_eq_abs]
        exact (hC x hx).trans (le_max_left _ _)
      · rw [Set.indicator_of_notMem hb]
        have hOutside : R < x.1 ∨ R < x.2 := by
          change 0 ≤ x.1 ∧ 0 ≤ x.2 at hx
          change ¬(x.1 ∈ Set.Icc 0 R ∧ x.2 ∈ Set.Icc 0 R) at hb
          simp only [Set.mem_Icc] at hb
          push Not at hb
          by_cases h : x.1 ≤ R
          · exact Or.inr (hb ⟨hx.1, h⟩ hx.2)
          · exact Or.inl (lt_of_not_ge h)
        rw [hR x hx hOutside, norm_zero]
    · rw [Set.indicator_of_notMem hx, norm_zero]
      by_cases hb : x ∈ B
      · rw [Set.indicator_of_mem hb]
        exact le_max_right _ _
      · rw [Set.indicator_of_notMem hb]
  exact (memLp_indicator_iff_restrict (measurableSet_Ici.prod measurableSet_Ici)).mp
    (hBox.mono' hMeas (Filter.Eventually.of_forall hDom))

-- @node: thm:main
/-- If [the set of integer scales S is finite](hyp:hS), [each of the three
input functions is measurable after extension by zero outside the nonnegative
quadrant, bounded there, and zero there outside a bounded rectangle](hyp:hInputs),
and [the Haar signs equal one on left halves and minus one on right
halves](hyp:hHalves), then [for any finite selection of admissible interval
triples at each scale, the sum over S and those triples of the absolute local
triangular forms is at most forty times the product of the three L³ norms on
the nonnegative quadrant](goal). -/
theorem dyadic_triangular_bound (S : Set ℤ) (F : Fin 3 → ℝ × ℝ → ℝ)
    (hS : MainScales S) (hInputs : MainInputs F) (hHalves : HaarHalvesConvention) :
    ∀ T : ℤ → Finset admissibleSet,
      ∑ k ∈ hS.toFinset, ∑ n ∈ T k, |localForm k n.val F| ≤
        40 * ∏ v : Fin 3, (eLpNorm (F v) 3 quadrantMeasure).toReal := by
  classical
  by_cases hEmpty : hS.toFinset = ∅
  · intro T
    simp only [hEmpty, Finset.sum_empty]
    exact mul_nonneg (by norm_num)
      (Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg)
  · have hF := mainInputs_continuityInputs F hInputs
    have hne : hS.toFinset.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEmpty
    obtain ⟨G, m, hG, hm, hDiff, hNorm⟩ := common_dyadic_L3_sequence F hF
      (hS.toFinset.min' hne - 1)
    have hScale (j : ℕ) (k : ℤ) (hk : k ∈ hS.toFinset) : m j + 1 ≤ k := by
      have hmin := Finset.min'_le hS.toFinset k hk
      have hj := hm j
      omega
    intro T
    exact dyadic_bound_of_step_approximation hS.toFinset F G m hF hG hScale
      hHalves hDiff hNorm T

end Papers.OaiBoundDyadicTriangular

module

public import Papers.OaiBoundDyadicTriangular.Helpers.ScaleHolder

/-!
# One-scale summability and continuity

Finite partial sums encode the full nonnegative series bound. The trilinear
difference bound gives continuity in the L3 seminorms into l1 of the triples.
-/

public section

open MeasureTheory
open scoped BigOperators

namespace Papers.OaiBoundDyadicTriangular

-- @node: lem:continuity
/-- At [any integer scale](hyp:hScale), if [all three input functions belong
to L3 for quadrant Lebesgue measure](hyp:hInputs) and [the Haar sign is plus one
on each interval's first half and minus one on its second half](hyp:hHalves),
[every finite sum of absolute local forms over admissible triples is bounded
by the product of the three L3 norms; moreover, for any other three L3 inputs,
the corresponding sum of absolute differences is bounded by the sum of three
products obtained by replacing inputs in order, each product using the L3 norm
of the changed input's difference, the earlier inputs from the new triple, and
the later inputs from the original triple](goal). -/
lemma localForm_one_scale_bound (k : ℤ) (F : Fin 3 → ℝ × ℝ → ℝ)
    (hScale : ContinuityScale k) (hInputs : ContinuityInputs F)
    (hHalves : HaarHalvesConvention) :
    (∀ T : Finset admissibleSet,
      ∑ n ∈ T, |localForm k n.val F| ≤
        ∏ v : Fin 3, (eLpNorm (F v) 3 quadrantMeasure).toReal) ∧
    (∀ (G : Fin 3 → ℝ × ℝ → ℝ), ContinuityInputs G → ∀ T : Finset admissibleSet,
      ∑ n ∈ T, |localForm k n.val F - localForm k n.val G| ≤
        (eLpNorm (fun x => F 0 x - G 0 x) 3 quadrantMeasure).toReal *
          (eLpNorm (F 1) 3 quadrantMeasure).toReal *
          (eLpNorm (F 2) 3 quadrantMeasure).toReal +
        (eLpNorm (G 0) 3 quadrantMeasure).toReal *
          (eLpNorm (fun x => F 1 x - G 1 x) 3 quadrantMeasure).toReal *
          (eLpNorm (F 2) 3 quadrantMeasure).toReal +
        (eLpNorm (G 0) 3 quadrantMeasure).toReal *
          (eLpNorm (G 1) 3 quadrantMeasure).toReal *
          (eLpNorm (fun x => F 2 x - G 2 x) 3 quadrantMeasure).toReal) := by
  constructor
  · exact fun T => localForm_one_scale_sum_bound k F hInputs T
  · intro G hG T
    have h₀ : ContinuityInputs ![fun x => F 0 x - G 0 x, F 1, F 2] := by
      intro v
      fin_cases v
      · exact (hInputs 0).sub (hG 0)
      · exact hInputs 1
      · exact hInputs 2
    have h₁ : ContinuityInputs ![G 0, fun x => F 1 x - G 1 x, F 2] := by
      intro v
      fin_cases v
      · exact hG 0
      · exact (hInputs 1).sub (hG 1)
      · exact hInputs 2
    have h₂ : ContinuityInputs ![G 0, G 1, fun x => F 2 x - G 2 x] := by
      intro v
      fin_cases v
      · exact hG 0
      · exact hG 1
      · exact (hInputs 2).sub (hG 2)
    have hb₀ := localForm_one_scale_sum_bound k _ h₀ T
    have hb₁ := localForm_one_scale_sum_bound k _ h₁ T
    have hb₂ := localForm_one_scale_sum_bound k _ h₂ T
    have he : ∑ n ∈ T, |localForm k n.val F - localForm k n.val G| ≤
        (∑ n ∈ T, |localForm k n.val ![fun x => F 0 x - G 0 x, F 1, F 2]|) +
        (∑ n ∈ T, |localForm k n.val ![G 0, fun x => F 1 x - G 1 x, F 2]|) +
        (∑ n ∈ T, |localForm k n.val ![G 0, G 1, fun x => F 2 x - G 2 x]|) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro n _
      rw [localForm_sub_expansion k n.val F G hInputs hG]
      exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    apply he.trans
    simpa [Fin.prod_univ_three] using (add_le_add (add_le_add hb₀ hb₁) hb₂)

end Papers.OaiBoundDyadicTriangular

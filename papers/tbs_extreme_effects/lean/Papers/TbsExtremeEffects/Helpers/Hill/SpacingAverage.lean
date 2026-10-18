module
public import Papers.TbsExtremeEffects.Helpers.Hill.SpacingProcess

/-! The finite-prefix identities connecting exponential spacings, their centered
partial sums, and the weighted order-statistic average. -/

public section
namespace Papers.TbsExtremeEffects
open scoped BigOperators

/-- [A prefix length no greater than the vector length](hyp:hi) and [agreement of the finite-vector entries with the shifted sequence on that prefix](hyp:hfg) imply [that the finite prefix sum equals the sequence sum over ranks one through the prefix length](goal). -/
-- @node: hill_fin_prefix_sum_eq_Icc
lemma hill_fin_prefix_sum_eq_Icc {n i : ℕ} (hi : i ≤ n)
    (f : Fin n → ℝ) (g : ℕ → ℝ)
    (hfg : ∀ j : Fin n, (j : ℕ) < i → f j = g ((j : ℕ) + 1)) :
    (∑ j : Fin n, if (j : ℕ) < i then f j else 0) =
      ∑ j ∈ Finset.Icc 1 i, g j := by
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun (j : Fin n) _ => (j : ℕ) + 1)
  · intro j hj
    have hj' := (Finset.mem_filter.mp hj).2
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro j hj l hl he
    apply Fin.ext
    omega
  · intro j hj
    obtain ⟨hj1, hji⟩ := Finset.mem_Icc.mp hj
    refine ⟨⟨j - 1, by omega⟩, ?_, by simp; omega⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  · intro j hj
    exact hfg j (Finset.mem_filter.mp hj).2

/-- For [a finite sequence of spacings](hyp:S), [there exist centered partial sums and corresponding averages](goal) such that the first equality defines the partial sums, the second relates each sum to its average, and the third identifies the average with the weighted log-spacing expression whenever the stated spacing representation holds. -/
-- @node: hill_spacing_average_data
lemma hill_spacing_average_data {Ω : Type*} {n : ℕ} (S : Fin n → Ω → ℝ) :
    ∃ (A B : ℕ → Ω → ℝ),
      (∀ i w, B i w = ∑ j : Fin n, if (j : ℕ) < i then S j w - 1 else 0) ∧
      (∀ w i, B i w = (i : ℝ) * (A i w - 1)) ∧
      (∀ (i : ℕ), i ≤ n → ∀ (w : Ω) (Y : ℕ → ℝ),
        (∀ j : Fin n, (j : ℕ) < i →
          S j w = ((j : ℕ) + 1 : ℝ) * (Y ((j : ℕ) + 1) - Y ((j : ℕ) + 2))) →
        A i w = (i : ℝ)⁻¹ * ∑ j ∈ Finset.Icc 1 i,
          (j : ℝ) * (Y j - Y (j + 1))) := by
  let B : ℕ → Ω → ℝ := fun i w =>
    ∑ j : Fin n, if (j : ℕ) < i then S j w - 1 else 0
  let A : ℕ → Ω → ℝ := fun i w => if i = 0 then 0 else 1 + B i w / (i : ℝ)
  refine ⟨A, B, fun _ _ => rfl, ?_, ?_⟩
  · intro w i
    by_cases hi : i = 0
    · subst i
      simp [B]
    · have hiR : (i : ℝ) ≠ 0 := by exact_mod_cast hi
      dsimp [A]
      rw [if_neg hi]
      field_simp
      ring
  · intro i hin w Y hSpacing
    by_cases hi : i = 0
    · subst i
      simp [A]
    have hiR : (i : ℝ) ≠ 0 := by exact_mod_cast hi
    have hsum := hill_fin_prefix_sum_eq_Icc hin (fun j => S j w - 1)
      (fun j => (j : ℝ) * (Y j - Y (j + 1)) - 1) (by
        intro j hj
        rw [hSpacing j hj]
        push_cast
        rfl)
    have hB : B i w = (∑ j ∈ Finset.Icc 1 i,
        (j : ℝ) * (Y j - Y (j + 1))) - (i : ℝ) := by
      dsimp [B]
      rw [hsum, Finset.sum_sub_distrib]
      simp
    dsimp [A]
    rw [if_neg hi]
    rw [hB]
    field_simp
    ring

end Papers.TbsExtremeEffects

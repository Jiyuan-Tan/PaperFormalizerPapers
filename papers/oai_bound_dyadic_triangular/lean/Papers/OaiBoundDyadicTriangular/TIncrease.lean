module

public import Papers.OaiBoundDyadicTriangular.Helpers.ChildMatrices
public import Papers.OaiBoundDyadicTriangular.TGap
public import Papers.OaiBoundDyadicTriangular.TTrace

/-! # Local energy increment controls the triangular trace -/

public section

open scoped BigOperators

namespace Papers.OaiBoundDyadicTriangular

-- @node: prop:increase
/-- Suppose the three input functions are [bounded on the nonnegative
quadrant](hyp:hBounded), [vanish there outside bounded rectangles](hyp:hCompact),
and [are constant on dyadic atom rectangles at scale m](hyp:hAtoms), [the three
interval indices have bitwise exclusive-or zero](hyp:hTriple), [k is at least
m plus one](hyp:hScale), and [the Haar signs equal one on left halves and minus
one on right halves](hyp:hHalves). Then [the local energy increment is
nonnegative, and the absolute local triangular trace is at most ten times the
square root of two divided by three times that increment](goal). -/
theorem energyIncrement_controls_trace (F : Fin 3 → ℝ × ℝ → ℝ) (k m : ℤ)
    (n : Fin 3 → ℕ) (hBounded : StepBounded F) (hCompact : StepCompact F)
    (hAtoms : StepAtoms F m) (hTriple : IncreaseTriple n) (hScale : IncreaseScale k m)
    (hHalves : HaarHalvesConvention) :
    0 ≤ energyIncrement F k m n ∧
    |localTrace F k m n| ≤ 10 * Real.sqrt 2 / 3 * energyIncrement F k m n := by
  let q : Fin 3 → ℝ := fun v =>
    hessForm (rowGram (atomRowStar F k m n v)) (rowGram_isHermitian _)
      (rowPerturbation (atomRowStar F k m n v) (haarDiag k m n v))
  have hSum : 1 / (2 * Real.sqrt 2) * (∑ v, q v) ≤ energyIncrement F k m n := by
    calc
      _ = ∑ v : Fin 3, 1 / (2 * Real.sqrt 2) * q v := Finset.mul_sum ..
      _ ≤ ∑ v : Fin 3, ((1 / 4 : ℝ) *
          (∑ b ∈ childBits, vertexEnergy F (k - 1) m
            (fun w => 2 * n w + (b w).val) v) - vertexEnergy F k m n v) :=
        Finset.sum_le_sum fun v _ => vertexEnergy_child_gap F k m hScale n v
      _ = energyIncrement F k m n := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_comm]
        simp only [energyIncrement, sum_children_eq_childBits, localEnergy]
  have hq : 0 ≤ ∑ v, q v := Finset.sum_nonneg fun v _ => hessForm_nonneg _ _ _
  have hδ : 0 ≤ energyIncrement F k m n :=
    (mul_nonneg (by positivity) hq).trans hSum
  refine ⟨hδ, ?_⟩
  have hqδ : (∑ v, q v) ≤ (2 * Real.sqrt 2) * energyIncrement F k m n := by
    rw [mul_comm (2 * Real.sqrt 2)]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.sqrt 2)).mp
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using hSum
  have hD := fun v => haarDiag_order_bounds k m hScale n v
  have hTrace := (abs_trace_le_hessForm_sum
    (weightedEdge F k m n 0) (weightedEdge F k m n 1) (weightedEdge F k m n 2)
    (haarDiag k m n 0) (haarDiag k m n 1) (haarDiag k m n 2)
    ⟨haarDiag_isSymm k m n 0, haarDiag_isSymm k m n 1, haarDiag_isSymm k m n 2⟩
    ⟨(hD 0).1, (hD 0).2, (hD 1).1, (hD 1).2, (hD 2).1, (hD 2).2⟩).2
  have ht : |localTrace F k m n| ≤ (5 / 3 : ℝ) * ∑ v, q v := by
    simpa only [localTrace, q, Fin.sum_univ_three, atomRowStar,
      show (0 : Fin 3) + 2 = 2 from rfl,
      show (1 : Fin 3) + 2 = 0 from rfl,
      show (2 : Fin 3) + 2 = 1 from rfl] using hTrace
  calc
    _ ≤ (5 / 3 : ℝ) * ∑ v, q v := ht
    _ ≤ (5 / 3 : ℝ) * ((2 * Real.sqrt 2) * energyIncrement F k m n) :=
      mul_le_mul_of_nonneg_left hqδ (by norm_num)
    _ = _ := by ring

end Papers.OaiBoundDyadicTriangular

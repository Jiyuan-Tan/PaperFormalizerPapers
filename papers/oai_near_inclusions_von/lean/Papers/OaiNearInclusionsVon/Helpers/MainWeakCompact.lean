module

public import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Papers.OaiNearInclusionsVon.Helpers.MainFactorAlgebras
public import Toolkit.Foundations.Analysis.Normed.WeakOperatorLimits

/-! Weak operator cluster points and preservation of uniform error bounds. -/

public section

set_option linter.style.longLine false

namespace Papers.OaiNearInclusionsVon

open Filter
open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- If [d is nonnegative](hyp:hd), [the operator-norm distance between two nets
is eventually at most d](hyp:herr), [the first net's matrix coefficients converge
to those of B](hyp:hB), and [the second net's matrix coefficients converge to
those of C](hyp:hC), [the operator-norm distance between B and C is at most d](goal). -/
-- @node: wot_error_limit_le
lemma wot_error_limit_le {ι : Type*} {l : Filter ι} [NeBot l]
    (T S : ι → H →L[ℂ] H) (B C : H →L[ℂ] H) (d : ℝ) (hd : 0 ≤ d)
    (herr : ∀ᶠ j in l, ‖T j - S j‖ ≤ d)
    (hB : ∀ x y, Tendsto (fun j => inner ℂ y (T j x)) l (𝓝 (inner ℂ y (B x))))
    (hC : ∀ x y, Tendsto (fun j => inner ℂ y (S j x)) l (𝓝 (inner ℂ y (C x)))) :
    ‖B - C‖ ≤ d := by
  apply (B - C).opNorm_le_bound hd
  intro x
  rw [← (InnerProductSpace.toDual ℂ H).norm_map ((B - C) x)]
  apply ((InnerProductSpace.toDual ℂ H) ((B - C) x)).opNorm_le_bound
    (mul_nonneg hd (norm_nonneg x))
  intro y
  have hl := ((hB x y).sub (hC x y)).norm
  have he : ∀ᶠ j in l, ‖inner ℂ y (T j x) - inner ℂ y (S j x)‖ ≤
      (d * ‖x‖) * ‖y‖ := by
    filter_upwards [herr] with j hj
    rw [← inner_sub_right]
    calc
      ‖inner ℂ y (T j x - S j x)‖ ≤ ‖y‖ * ‖(T j - S j) x‖ := norm_inner_le_norm _ _
      _ ≤ ‖y‖ * (d * ‖x‖) := mul_le_mul_of_nonneg_left
        (((T j - S j).le_opNorm x).trans
          (mul_le_mul_of_nonneg_right hj (norm_nonneg x))) (norm_nonneg y)
      _ = _ := mul_comm _ _
  have hh := le_of_tendsto hl he
  change ‖inner ℂ ((B - C) x) y‖ ≤ _
  rw [norm_inner_symm, sub_apply, inner_sub_right]
  exact hh

/-- Suppose [every operator in the first sequence has norm at most one](hyp:hT),
[each belongs to the von Neumann algebra A](hyp:hA), [its operator-norm distance
from the corresponding operator in a second sequence is at most d](hyp:herr),
and [the second sequence's matrix coefficients converge to those of C](hyp:hC).
Then [A contains an operator whose operator-norm distance from C is at most d](goal). -/
-- @node: exists_vonNeumann_cluster_close
lemma exists_vonNeumann_cluster_close (A : VonNeumannAlgebra H)
    (T S : ℕ → H →L[ℂ] H) (C : H →L[ℂ] H) (d : ℝ)
    (hT : ∀ j, ‖T j‖ ≤ 1) (hA : ∀ j, T j ∈ A)
    (herr : ∀ j, ‖T j - S j‖ ≤ d)
    (hC : ∀ x y, Tendsto (fun j => inner ℂ y (S j x)) atTop
      (𝓝 (inner ℂ y (C x)))) :
    ∃ B : H →L[ℂ] H, B ∈ A ∧ ‖B - C‖ ≤ d := by
  let u : Ultrafilter ℕ := Ultrafilter.of atTop
  obtain ⟨B, _, hB⟩ := Toolkit.Foundations.Analysis.Normed.exists_norm_le_one_tendsto_inner_of_forall_norm_le_one T hT u
  refine ⟨B, Toolkit.Foundations.Analysis.Normed.mem_vonNeumannAlgebra_of_tendsto_inner A T B (Eventually.of_forall hA) hB, ?_⟩
  exact wot_error_limit_le T S B C d ((norm_nonneg _).trans (herr 0))
    (Eventually.of_forall herr) hB (fun x y => (hC x y).mono_left (Ultrafilter.of_le _))

end Papers.OaiNearInclusionsVon

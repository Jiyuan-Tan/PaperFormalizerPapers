module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic

/-! # Uniform loss bounds along a flow path

These deterministic estimates implement the path-energy step in the capacity
converse. They bound each correlation diagonal by the entire path energy, then
sum its geometric weight. No depth-dependent moment budgets are assumed.
-/

public section

open scoped BigOperators

namespace OaiCapacityCriterionState

-- @node: finite_path_correlation_le_energy
/-- If [the sum of squared entries along a path of length n is at most E](hyp:henergy),
[the sum of products of entries separated by any fixed nonnegative lag k, over
the first n minus k positions, is also at most E](goal). -/
lemma finite_path_correlation_le_energy (X : ℕ → ℝ) (n k : ℕ) (E : ℝ)
    (henergy : ∑ i ∈ Finset.range n, X i ^ 2 ≤ E) :
    ∑ i ∈ Finset.range (n - k), X i * X (i + k) ≤ E := by
  classical
  have hleft : (∑ i ∈ Finset.range (n - k), X i ^ 2) ≤ E :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.sub_le n k))
      (fun i _ _ => sq_nonneg (X i))).trans henergy
  have hright : (∑ i ∈ Finset.range (n - k), X (i + k) ^ 2) ≤ E := by
    have himage : (Finset.range (n - k)).image (fun i => i + k) ⊆ Finset.range n := by
      intro j hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      simp only [Finset.mem_range] at *
      omega
    have heq : (∑ i ∈ Finset.range (n - k), X (i + k) ^ 2) =
        ∑ j ∈ (Finset.range (n - k)).image (fun i => i + k), X j ^ 2 := by
      rw [Finset.sum_image]
      intro i _ j _ hij
      dsimp only at hij
      omega
    rw [heq]
    exact (Finset.sum_le_sum_of_subset_of_nonneg himage
      (fun i _ _ => sq_nonneg (X i))).trans henergy
  have hterm : (∑ i ∈ Finset.range (n - k), X i * X (i + k)) ≤
      ∑ i ∈ Finset.range (n - k), (X i ^ 2 + X (i + k) ^ 2) / 2 := by
    apply Finset.sum_le_sum
    intro i _
    nlinarith [sq_nonneg (X i - X (i + k))]
  rw [← Finset.sum_div, Finset.sum_add_distrib] at hterm
  linarith

-- @node: finite_geometric_sum_bound
/-- If [the geometric ratio is nonnegative](hyp:hlam) and
[strictly less than one](hyp:hlam1), [the sum of its first n powers, starting with
the zeroth power, is at most the reciprocal of one minus the ratio](goal). -/
lemma finite_geometric_sum_bound (lam : ℝ) (hlam : 0 ≤ lam) (hlam1 : lam < 1)
    (n : ℕ) : (∑ k ∈ Finset.range n, lam ^ k) ≤ 1 / (1 - lam) := by
  have hid : (1 - lam) * (∑ k ∈ Finset.range n, lam ^ k) = 1 - lam ^ n := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, mul_add, ih, pow_succ]; ring
  apply (le_div_iff₀ (sub_pos.mpr hlam1)).mpr
  nlinarith [pow_nonneg hlam n]

-- @node: finite_path_kernel_bound
/-- If [the energy budget E is nonnegative](hyp:hE), [the geometric ratio is
nonnegative](hyp:hlam) and [less than one](hyp:hlam1), and
[the sum of squared path entries over n positions is at most E](hyp:henergy),
[the sum over lags below n of the lagged path correlation weighted by the ratio
raised to that lag is at most E divided by one minus the ratio](goal). -/
lemma finite_path_kernel_bound (X : ℕ → ℝ) (n : ℕ) (E lam : ℝ)
    (hE : 0 ≤ E) (hlam : 0 ≤ lam) (hlam1 : lam < 1)
    (henergy : ∑ i ∈ Finset.range n, X i ^ 2 ≤ E) :
    (∑ k ∈ Finset.range n, lam ^ k *
      ∑ i ∈ Finset.range (n - k), X i * X (i + k)) ≤ E / (1 - lam) := by
  calc
    _ ≤ ∑ k ∈ Finset.range n, lam ^ k * E := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_left
        (finite_path_correlation_le_energy X n k E henergy) (pow_nonneg hlam k)
    _ = (∑ k ∈ Finset.range n, lam ^ k) * E := (Finset.sum_mul _ _ _).symm
    _ ≤ (1 / (1 - lam)) * E :=
      mul_le_mul_of_nonneg_right (finite_geometric_sum_bound lam hlam hlam1 n) hE
    _ = E / (1 - lam) := by ring

-- @node: finite_path_terminal_bound
/-- If [the terminal bound R is nonnegative](hyp:hR), [the geometric ratio is
nonnegative](hyp:hlam) and [less than one](hyp:hlam1), and
[each of the first n path entries is at most R](hyp:hX), [their geometrically
weighted sum, read backward from position n minus one, is at most R divided by
one minus the ratio](goal). -/
lemma finite_path_terminal_bound (X : ℕ → ℝ) (n : ℕ) (R lam : ℝ)
    (hR : 0 ≤ R) (hlam : 0 ≤ lam) (hlam1 : lam < 1)
    (hX : ∀ i < n, X i ≤ R) :
    (∑ k ∈ Finset.range n, lam ^ k * X (n - 1 - k)) ≤ R / (1 - lam) := by
  by_cases hn : n = 0
  · subst n
    simp only [Finset.range_zero, Finset.sum_empty]
    exact div_nonneg hR (sub_pos.mpr hlam1).le
  calc
    _ ≤ ∑ k ∈ Finset.range n, lam ^ k * R := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left (hX _ (by omega)) (pow_nonneg hlam k)
    _ = (∑ k ∈ Finset.range n, lam ^ k) * R := (Finset.sum_mul _ _ _).symm
    _ ≤ (1 / (1 - lam)) * R :=
      mul_le_mul_of_nonneg_right (finite_geometric_sum_bound lam hlam hlam1 n) hR
    _ = R / (1 - lam) := by ring

-- @node: exists_uniform_path_loss_scale
/-- If [the geometric ratio is less than one](hyp:hlam),
[the loss multiplier C is nonnegative](hyp:hC), [the quadratic budget Q is
nonnegative](hyp:hQ), and [the terminal budget R is nonnegative](hyp:hR),
[there exists a positive scale ε at most one for which C times the sum of
Qε² and Rε, divided by one minus the ratio, is at most one half](goal). -/
lemma exists_uniform_path_loss_scale (lam C Q R : ℝ) (hlam : lam < 1)
    (hC : 0 ≤ C) (hQ : 0 ≤ Q) (hR : 0 ≤ R) :
    ∃ eps : ℝ, 0 < eps ∧ eps ≤ 1 ∧
      C * (Q * eps ^ 2 / (1 - lam) + R * eps / (1 - lam)) ≤ 1 / 2 := by
  let A := C * (Q + R)
  have hA : 0 ≤ A := mul_nonneg hC (add_nonneg hQ hR)
  let eps := min 1 ((1 - lam) / (2 * (A + 1)))
  have heps : 0 < eps := lt_min zero_lt_one
    (div_pos (sub_pos.mpr hlam) (by positivity))
  have heps1 : eps ≤ 1 := min_le_left _ _
  have hb : eps * (2 * (A + 1)) ≤ 1 - lam :=
    (le_div_iff₀ (by positivity : 0 < 2 * (A + 1))).mp (min_le_right _ _)
  refine ⟨eps, heps, heps1, ?_⟩
  have hs : eps ^ 2 ≤ eps := by nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hs (mul_nonneg hC hQ)
  rw [← add_div, ← mul_div_assoc]
  apply (div_le_iff₀ (sub_pos.mpr hlam)).mpr
  dsimp [A] at hb
  nlinarith

-- @node: finite_flow_path_loss_bound
/-- For finitely many paths, suppose [their weights are nonnegative](hyp:hw) and
[sum to M](hyp:hmass), [the energy budget E is nonnegative](hyp:hE),
[the terminal bound R is nonnegative](hyp:hR), [the geometric ratio is
nonnegative](hyp:hlam) and [less than one](hyp:hlam1),
[each path has squared energy at most E over its first n positions](hyp:henergy),
and [every entry in those positions is at most R](hyp:hX). Then [the weighted
sum of each path's geometrically weighted lag correlations and backward terminal
sum is at most M times the sum of E and R divided by one minus the ratio](goal). -/
lemma finite_flow_path_loss_bound {ι : Type*} [Fintype ι]
    (weights : ι → ℝ) (X : ι → ℕ → ℝ) (n : ℕ) (M E R lam : ℝ)
    (hw : ∀ p, 0 ≤ weights p) (hmass : ∑ p, weights p = M)
    (hE : 0 ≤ E) (hR : 0 ≤ R) (hlam : 0 ≤ lam) (hlam1 : lam < 1)
    (henergy : ∀ p, ∑ i ∈ Finset.range n, X p i ^ 2 ≤ E)
    (hX : ∀ p i, i < n → X p i ≤ R) :
    (∑ p, weights p *
      ((∑ k ∈ Finset.range n, lam ^ k *
          ∑ i ∈ Finset.range (n - k), X p i * X p (i + k)) +
        ∑ k ∈ Finset.range n, lam ^ k * X p (n - 1 - k))) ≤
      M * (E / (1 - lam) + R / (1 - lam)) := by
  calc
    _ ≤ ∑ p, weights p * (E / (1 - lam) + R / (1 - lam)) := by
      apply Finset.sum_le_sum
      intro p _
      apply mul_le_mul_of_nonneg_left _ (hw p)
      exact add_le_add
        (finite_path_kernel_bound (X p) n E lam hE hlam hlam1 (henergy p))
        (finite_path_terminal_bound (X p) n R lam hR hlam hlam1 (hX p))
    _ = _ := by rw [← Finset.sum_mul, hmass]

-- @node: information_survives_uniform_path_loss
/-- If [the initial mass M is nonnegative](hyp:hM), [C times the sum of the
energy and terminal budgets divided by one minus the geometric ratio is at most
one half](hyp:hsmall), [the loss is at most C times M times that normalized
budget sum](hyp:hloss), and [remaining information equals M minus the loss](hyp:htelescope),
[the remaining information is at least half of M](goal). -/
lemma information_survives_uniform_path_loss (M C E R lam info loss : ℝ)
    (hM : 0 ≤ M)
    (hsmall : C * (E / (1 - lam) + R / (1 - lam)) ≤ 1 / 2)
    (hloss : loss ≤ C * (M * (E / (1 - lam) + R / (1 - lam))))
    (htelescope : info = M - loss) : M / 2 ≤ info := by
  have h := mul_le_mul_of_nonneg_left hsmall hM
  rw [htelescope]
  nlinarith

end OaiCapacityCriterionState

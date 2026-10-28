module

public import Papers.OaiCapacityCriterionState.Helpers.CapacityLabels
public import Papers.OaiCapacityCriterionState.Helpers.PathLoss

/-! # Path energy of the conserved flow profile

The root contributes the square of the flow mass; the remaining path energy
is bounded by admissibility. Thus the geometric loss estimates apply uniformly
in the terminal depth, including on trees with early leaves.
-/

public section

open scoped BigOperators

namespace OaiCapacityCriterionState

-- @node: normalizedFlow_path_energy_le
/-- If [the path potential along a sequence is at most one](hyp:hpotential),
[the sum of squared normalized vertex flows from the root through any finite
depth is at most the squared total flow mass plus one](goal). -/
lemma normalizedFlow_path_energy_le {B : ℕ} (T : BoundedTree B) (lam : ℝ)
    (theta : List (Fin B) → ℝ)
    (xi : ℕ → Fin B) (hpotential : pathPotential lam theta xi ≤ 1) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1),
      normalizedFlow T lam theta (rayPrefix xi i) ^ 2 ≤
        flowMass T theta ^ 2 + 1 := by
  have hsplit (f : ℕ → ℝ) : (∑ i ∈ Finset.range (n + 1), f i) =
      f 0 + ∑ i ∈ Finset.range n, f (i + 1) := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]; ring
  have heq (i : ℕ) : normalizedFlow T lam theta (rayPrefix xi (i + 1)) =
      normalizedEdgeFlow lam theta (rayPrefix xi (i + 1)) := by
    simp only [normalizedFlow, rayPrefix, List.cons_ne_nil, if_false]
  have hedge : (∑ i ∈ Finset.range n,
      normalizedFlow T lam theta (rayPrefix xi (i + 1)) ^ 2) ≤ 1 := by
    simp_rw [heq, normalizedEdgeFlow_rayPrefix]
    rw [← flowPrefixEnergy_rayPrefix]
    exact flowPrefixEnergy_ray_le_one lam theta xi hpotential n
  rw [hsplit]
  simpa only [rayPrefix, normalizedFlow, if_true] using
    add_le_add (le_refl (flowMass T theta ^ 2)) hedge

-- @node: scaled_normalizedFlow_path_energy_le
/-- If [the path potential along a sequence is at most one](hyp:hpotential),
[the sum of squared normalized vertex flows, each multiplied by a real scale,
from the root through any finite depth is at most the squared scale times the
sum of squared total flow mass and one](goal). -/
lemma scaled_normalizedFlow_path_energy_le {B : ℕ} (T : BoundedTree B) (lam : ℝ)
    (theta : List (Fin B) → ℝ) (eps : ℝ)
    (xi : ℕ → Fin B) (hpotential : pathPotential lam theta xi ≤ 1) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1),
      (eps * normalizedFlow T lam theta (rayPrefix xi i)) ^ 2 ≤
        (flowMass T theta ^ 2 + 1) * eps ^ 2 := by
  simp_rw [mul_pow]
  rw [← Finset.mul_sum]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left
    (normalizedFlow_path_energy_le T lam theta xi hpotential n) (sq_nonneg eps)

-- @node: normalizedFlow_ray_bound
/-- If [the channel parameter lies strictly between zero and one](hyp:hlam),
[the edge weights form a flow](hyp:htheta), and [every tree ray has path
potential at most one](hyp:hpotential), then along [any ray of the tree](hyp:hxi)
[the normalized vertex flow at every depth is at most one plus the total flow
mass](goal). -/
lemma normalizedFlow_ray_bound {B : ℕ} (T : BoundedTree B) (lam : ℝ)
    (hlam : MainLambda lam) (theta : List (Fin B) → ℝ) (htheta : IsFlow T theta)
    (hpotential : ∀ xi ∈ T.rays, pathPotential lam theta xi ≤ 1)
    (xi : ℕ → Fin B) (hxi : xi ∈ T.rays) (n : ℕ) :
    normalizedFlow T lam theta (rayPrefix xi n) ≤ 1 + flowMass T theta := by
  cases n with
  | zero => simp only [rayPrefix, normalizedFlow, if_true]; linarith
  | succ n =>
      have hne : rayPrefix xi (n + 1) ≠ [] := List.cons_ne_nil _ _
      have hb := admissible_flow_edge_bound T lam hlam theta htheta hpotential
        (rayPrefix xi (n + 1)) (hxi (n + 1)) hne
      have hp : 0 < sqParam lam ^ (rayPrefix xi (n + 1)).length :=
        pow_pos (sqParam_mem_Ioo lam hlam).1 _
      have hnorm : normalizedEdgeFlow lam theta (rayPrefix xi (n + 1)) ≤ 1 :=
        (div_le_one hp).mpr hb
      have hm := flowMass_nonneg T theta htheta
      rw [normalizedFlow, if_neg hne]
      linarith

end OaiCapacityCriterionState

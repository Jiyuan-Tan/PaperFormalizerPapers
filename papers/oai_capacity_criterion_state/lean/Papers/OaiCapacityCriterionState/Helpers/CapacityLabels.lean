module

public import Papers.OaiCapacityCriterionState.Helpers.FlowBounds
public import Papers.OaiCapacityCriterionState.Helpers.Flow

/-! # Nonlinear labels from admissible flows

Squared normalized edge masses accumulate to at most one on every finite
branch. The unused energy in a budget of two supplies positive denominators
for nonlinear flow labels, including at the root.
-/

@[expose] public section

open scoped BigOperators

namespace OaiCapacityCriterionState

variable {B : ℕ}

-- @node: normalizedEdgeFlow
/-- For a [branching bound](hyp:B), [channel parameter](hyp:lam), [edge-mass assignment](hyp:theta),
and [vertex](hyp:v), the [normalized edge flow](goal) is the edge mass divided by the
squared channel parameter raised to the vertex depth. -/
noncomputable def normalizedEdgeFlow (lam : ℝ) (theta : List (Fin B) → ℝ)
    (v : List (Fin B)) : ℝ := theta v / sqParam lam ^ v.length

-- @node: flowPrefixEnergy
/-- For a [branching bound](hyp:B), [channel parameter](hyp:lam), and [edge-mass assignment](hyp:theta),
the [prefix energy](goal) is [zero at the root](step:1) and, [at a child, the parent's
prefix energy plus the squared normalized edge flow into that child](step:2). -/
noncomputable def flowPrefixEnergy (lam : ℝ) (theta : List (Fin B) → ℝ) :
    List (Fin B) → ℝ
  | [] => 0
  | a :: v => flowPrefixEnergy lam theta v + normalizedEdgeFlow lam theta (a :: v) ^ 2

-- @node: normalizedEdgeFlow_nonneg
/-- If [the edge masses form a nonnegative conserved flow supported on the tree](hyp:htheta),
then [the normalized edge flow at every vertex is nonnegative](goal). -/
lemma normalizedEdgeFlow_nonneg (T : BoundedTree B) (lam : ℝ)
    (theta : List (Fin B) → ℝ) (htheta : IsFlow T theta) (v : List (Fin B)) :
    0 ≤ normalizedEdgeFlow lam theta v :=
  div_nonneg (htheta.1 v) (pow_nonneg (sq_nonneg lam) _)

-- @node: normalizedEdgeFlow_rayPrefix
/-- [The normalized edge flow at a ray's depth-n prefix equals its edge mass multiplied
by the channel parameter raised to minus twice n](goal). -/
lemma normalizedEdgeFlow_rayPrefix (lam : ℝ) (theta : List (Fin B) → ℝ)
    (xi : ℕ → Fin B) (n : ℕ) :
    normalizedEdgeFlow lam theta (rayPrefix xi n) =
      lam ^ (-(2 * (n : ℤ))) * theta (rayPrefix xi n) := by
  have hlen : (rayPrefix xi n).length = n := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [rayPrefix, List.length_cons, ih]
  have hexp : (2 : ℤ) * (n : ℤ) = ((2 * n : ℕ) : ℤ) := by omega
  rw [normalizedEdgeFlow, hlen, zpow_neg, hexp, zpow_natCast,
    sqParam, pow_mul, div_eq_mul_inv, mul_comm]

-- @node: flowPrefixEnergy_rayPrefix
/-- [The prefix energy at depth n along a ray equals the sum, over depths one through n,
of the squared edge masses rescaled by the channel parameter raised to minus twice their depth](goal). -/
lemma flowPrefixEnergy_rayPrefix (lam : ℝ) (theta : List (Fin B) → ℝ)
    (xi : ℕ → Fin B) (n : ℕ) :
    flowPrefixEnergy lam theta (rayPrefix xi n) =
      ∑ i ∈ Finset.range n,
        (lam ^ (-(2 * ((i + 1 : ℕ) : ℤ))) * theta (rayPrefix xi (i + 1))) ^ 2 := by
  induction n with
  | zero => simp [rayPrefix, flowPrefixEnergy]
  | succ n ih =>
      rw [Finset.sum_range_succ]
      change flowPrefixEnergy lam theta (rayPrefix xi n) +
        normalizedEdgeFlow lam theta (rayPrefix xi (n + 1)) ^ 2 = _
      rw [ih, normalizedEdgeFlow_rayPrefix]

-- @node: flowPrefixEnergy_nonneg
/-- [The prefix energy is nonnegative at every vertex, for any channel parameter and edge masses](goal). -/
lemma flowPrefixEnergy_nonneg (lam : ℝ) (theta : List (Fin B) → ℝ)
    (v : List (Fin B)) : 0 ≤ flowPrefixEnergy lam theta v := by
  induction v with
  | nil => exact le_rfl
  | cons a v ih => exact add_nonneg ih (sq_nonneg _)

-- @node: flowPrefixEnergy_ray_le_one
/-- If [a ray's total path potential is at most one](hyp:hxi), then [its prefix energy
at every finite depth is at most one](goal). -/
lemma flowPrefixEnergy_ray_le_one (lam : ℝ) (theta : List (Fin B) → ℝ)
    (xi : ℕ → Fin B) (hxi : pathPotential lam theta xi ≤ 1) (n : ℕ) :
    flowPrefixEnergy lam theta (rayPrefix xi n) ≤ 1 := by
  rw [flowPrefixEnergy_rayPrefix]
  apply ENNReal.ofReal_le_one.mp
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _)]
  exact (ENNReal.sum_le_tsum (Finset.range n)).trans hxi

-- @node: admissible_flow_prefixEnergy_le_one
/-- If [the edge masses form a nonnegative conserved flow supported on the tree](hyp:htheta)
and [every ray in the tree has path potential at most one](hyp:hpotential), then
[the prefix energy at a vertex is at most one](goal) whenever [that vertex belongs to the tree](hyp:hv). -/
lemma admissible_flow_prefixEnergy_le_one (T : BoundedTree B) (lam : ℝ)
    (theta : List (Fin B) → ℝ) (htheta : IsFlow T theta)
    (hpotential : ∀ xi ∈ T.rays, pathPotential lam theta xi ≤ 1)
    (v : List (Fin B)) (hv : v ∈ T.verts) :
    flowPrefixEnergy lam theta v ≤ 1 := by
  induction v with
  | nil => norm_num [flowPrefixEnergy]
  | cons a v ih =>
      by_cases hp : 0 < theta (a :: v)
      · obtain ⟨xi, hxi, heq⟩ := IsFlow.exists_ray_through_positive T theta htheta
          (a :: v) hv (List.cons_ne_nil _ _) hp
        rw [← heq]
        exact flowPrefixEnergy_ray_le_one lam theta xi (hpotential xi hxi) _
      · have hz : theta (a :: v) = 0 := le_antisymm (le_of_not_gt hp) (htheta.1 _)
        simpa only [flowPrefixEnergy, normalizedEdgeFlow, hz, zero_div, zero_pow
          (by decide : 2 ≠ 0), add_zero] using ih (T.prefix_closed a v hv)

-- @node: normalizedEdgeFlow_children
/-- If [the channel parameter lies strictly between zero and one](hyp:hlam),
[the edge masses form a nonnegative conserved flow supported on the tree](hyp:htheta),
and [the vertex belongs to the tree](hyp:hv) and [is not the root](hyp:hne), then
[its normalized edge flow equals the sum of its children's normalized edge flows,
each multiplied by the squared channel parameter](goal). -/
lemma normalizedEdgeFlow_children (T : BoundedTree B) (lam : ℝ)
    (hlam : MainLambda lam) (theta : List (Fin B) → ℝ) (htheta : IsFlow T theta)
    (v : List (Fin B)) (hv : v ∈ T.verts) (hne : v ≠ []) :
    ∑ w ∈ T.children v, sqParam lam * normalizedEdgeFlow lam theta w =
      normalizedEdgeFlow lam theta v := by
  classical
  calc
    _ = ∑ w ∈ T.children v, theta w / sqParam lam ^ v.length := by
      apply Finset.sum_congr rfl
      intro w hw
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hw
      simp only [normalizedEdgeFlow, List.length_cons, pow_succ]
      field_simp [ne_of_gt (sqParam_mem_Ioo lam hlam).1]
    _ = _ := by
      simp_rw [div_eq_mul_inv]
      rw [← Finset.sum_mul, ← htheta.2.2 v hv hne]
      rfl

-- @node: normalizedFlow
/-- For a [tree](hyp:T) with [branching bound](hyp:B), [channel parameter](hyp:lam),
[edge-mass assignment](hyp:theta), and [vertex](hyp:v), the [normalized flow](goal)
equals the total outgoing flow at the root and the normalized edge flow elsewhere. -/
noncomputable def normalizedFlow (T : BoundedTree B) (lam : ℝ)
    (theta : List (Fin B) → ℝ) (v : List (Fin B)) : ℝ :=
  if v = [] then flowMass T theta else normalizedEdgeFlow lam theta v

-- @node: normalizedFlow_nonneg
/-- If [the edge masses form a nonnegative conserved flow supported on the tree](hyp:htheta),
then [the normalized flow is nonnegative at every vertex, including the root](goal). -/
lemma normalizedFlow_nonneg (T : BoundedTree B) (lam : ℝ)
    (theta : List (Fin B) → ℝ) (htheta : IsFlow T theta) (v : List (Fin B)) :
    0 ≤ normalizedFlow T lam theta v := by
  unfold normalizedFlow
  split_ifs
  · exact flowMass_nonneg T theta htheta
  · exact normalizedEdgeFlow_nonneg T lam theta htheta v

-- @node: normalizedFlow_children
/-- If [the channel parameter lies strictly between zero and one](hyp:hlam),
[the edge masses form a nonnegative conserved flow supported on the tree](hyp:htheta),
and [the vertex belongs to the tree](hyp:hv), then [its normalized flow equals the sum
of its children's normalized edge flows, each multiplied by the squared channel parameter](goal). -/
lemma normalizedFlow_children (T : BoundedTree B) (lam : ℝ)
    (hlam : MainLambda lam) (theta : List (Fin B) → ℝ) (htheta : IsFlow T theta)
    (v : List (Fin B)) (hv : v ∈ T.verts) :
    ∑ w ∈ T.children v, sqParam lam * normalizedEdgeFlow lam theta w =
      normalizedFlow T lam theta v := by
  classical
  by_cases hne : v = []
  · subst v
    simp only [normalizedFlow, if_true, flowMass]
    apply Finset.sum_congr rfl
    intro w hw
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hw
    simp only [normalizedEdgeFlow, List.length_cons, List.length_nil, Nat.zero_add, pow_one]
    field_simp [ne_of_gt (sqParam_mem_Ioo lam hlam).1]
  · rw [normalizedFlow, if_neg hne]
    exact normalizedEdgeFlow_children T lam hlam theta htheta v hv hne

-- @node: nonlinearLabel_edge_identity
/-- If [the square of x is less than d](hyp:h), then [dividing x by the square root of
the difference between d and x squared, and then dividing that ratio by the square root of one plus its square,
gives x divided by the square root of d](goal). -/
lemma nonlinearLabel_edge_identity (x d : ℝ) (h : x ^ 2 < d) :
    (x / Real.sqrt (d - x ^ 2)) /
        Real.sqrt (1 + (x / Real.sqrt (d - x ^ 2)) ^ 2) = x / Real.sqrt d := by
  have hd : 0 < d := (sq_nonneg x).trans_lt h
  have hsub : 0 < d - x ^ 2 := sub_pos.mpr h
  have hs : Real.sqrt (d - x ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hsub)
  have hid : 1 + (x / Real.sqrt (d - x ^ 2)) ^ 2 = d / (d - x ^ 2) := by
    rw [div_pow, Real.sq_sqrt hsub.le]
    field_simp
    ring
  rw [hid, Real.sqrt_div hd.le]
  field_simp

-- @node: flowCapacityLabel
/-- For a [tree](hyp:T) with [branching bound](hyp:B), [channel parameter](hyp:lam),
[edge-mass assignment](hyp:theta), and [vertex](hyp:v), the [flow capacity label](goal)
is the normalized flow divided by the square root of two minus the prefix energy. -/
noncomputable def flowCapacityLabel (T : BoundedTree B) (lam : ℝ)
    (theta : List (Fin B) → ℝ) (v : List (Fin B)) : ℝ :=
  normalizedFlow T lam theta v / Real.sqrt (2 - flowPrefixEnergy lam theta v)

-- @node: flowCapacityLabel_nonneg
/-- If [the edge masses form a nonnegative conserved flow supported on the tree](hyp:htheta),
then [the flow capacity label is nonnegative at every vertex](goal). -/
lemma flowCapacityLabel_nonneg (T : BoundedTree B) (lam : ℝ)
    (theta : List (Fin B) → ℝ) (htheta : IsFlow T theta) (v : List (Fin B)) :
    0 ≤ flowCapacityLabel T lam theta v :=
  div_nonneg (normalizedFlow_nonneg T lam theta htheta v) (Real.sqrt_nonneg _)

-- @node: flowCapacityLabel_child_identity
/-- If [the edge masses form a nonnegative conserved flow supported on the tree](hyp:htheta),
[every ray has path potential at most one](hyp:hpotential), and [the child belongs to the tree](hyp:hv),
then [the child's capacity label divided by the square root of one plus its square equals
the child's normalized edge flow divided by the square root of two minus the parent's prefix energy](goal). -/
lemma flowCapacityLabel_child_identity (T : BoundedTree B) (lam : ℝ)
    (theta : List (Fin B) → ℝ) (htheta : IsFlow T theta)
    (hpotential : ∀ xi ∈ T.rays, pathPotential lam theta xi ≤ 1)
    (a : Fin B) (v : List (Fin B)) (hv : a :: v ∈ T.verts) :
    flowCapacityLabel T lam theta (a :: v) /
        Real.sqrt (1 + flowCapacityLabel T lam theta (a :: v) ^ 2) =
      normalizedEdgeFlow lam theta (a :: v) /
        Real.sqrt (2 - flowPrefixEnergy lam theta v) := by
  have he := admissible_flow_prefixEnergy_le_one T lam theta htheta hpotential (a :: v) hv
  have hx : normalizedEdgeFlow lam theta (a :: v) ^ 2 <
      2 - flowPrefixEnergy lam theta v := by
    change flowPrefixEnergy lam theta v + normalizedEdgeFlow lam theta (a :: v) ^ 2 ≤ 1 at he
    linarith
  simp only [flowCapacityLabel, normalizedFlow, List.cons_ne_nil, if_false]
  rw [flowPrefixEnergy, show 2 - (flowPrefixEnergy lam theta v +
      normalizedEdgeFlow lam theta (a :: v) ^ 2) =
        (2 - flowPrefixEnergy lam theta v) - normalizedEdgeFlow lam theta (a :: v) ^ 2 by ring]
  exact nonlinearLabel_edge_identity _ _ hx

-- @node: flowCapacityLabel_recursion
/-- If [the channel parameter lies strictly between zero and one](hyp:hlam),
[the edge masses form a nonnegative conserved flow supported on the tree](hyp:htheta),
and [every ray has path potential at most one](hyp:hpotential), then [the capacity labels
are nonnegative on the tree and each parent label is at most the sum of the child labels
divided by the square root of one plus their squares and multiplied by the squared channel parameter](goal). -/
lemma flowCapacityLabel_recursion (T : BoundedTree B) (lam : ℝ)
    (hlam : MainLambda lam) (theta : List (Fin B) → ℝ) (htheta : IsFlow T theta)
    (hpotential : ∀ xi ∈ T.rays, pathPotential lam theta xi ≤ 1) :
    FlowLabelRecursion T lam (flowCapacityLabel T lam theta) := by
  classical
  intro v hv
  refine ⟨flowCapacityLabel_nonneg T lam theta htheta v, le_of_eq ?_⟩
  calc
    flowCapacityLabel T lam theta v =
        (∑ w ∈ T.children v, sqParam lam * normalizedEdgeFlow lam theta w) /
          Real.sqrt (2 - flowPrefixEnergy lam theta v) := by
      rw [normalizedFlow_children T lam hlam theta htheta v hv]
      rfl
    _ = ∑ w ∈ T.children v, sqParam lam *
        (normalizedEdgeFlow lam theta w / Real.sqrt (2 - flowPrefixEnergy lam theta v)) := by
      simp only [div_eq_mul_inv, Finset.sum_mul, mul_assoc]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro w hw
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw
      rw [mul_div_assoc, flowCapacityLabel_child_identity T lam theta htheta hpotential
        a v (Finset.mem_filter.mp ha).2]

-- @node: flowCapacityLabel_le_normalizedFlow
/-- If [the edge masses form a nonnegative conserved flow supported on the tree](hyp:htheta)
and [every ray has path potential at most one](hyp:hpotential), then [the capacity label
is at most the normalized flow](goal) at [each vertex belonging to the tree](hyp:hv). -/
lemma flowCapacityLabel_le_normalizedFlow (T : BoundedTree B) (lam : ℝ)
    (theta : List (Fin B) → ℝ) (htheta : IsFlow T theta)
    (hpotential : ∀ xi ∈ T.rays, pathPotential lam theta xi ≤ 1)
    (v : List (Fin B)) (hv : v ∈ T.verts) :
    flowCapacityLabel T lam theta v ≤ normalizedFlow T lam theta v := by
  have he := admissible_flow_prefixEnergy_le_one T lam theta htheta hpotential v hv
  have hd : 1 ≤ Real.sqrt (2 - flowPrefixEnergy lam theta v) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (by linarith :
      (1 : ℝ) ≤ 2 - flowPrefixEnergy lam theta v)
  have hn := normalizedFlow_nonneg T lam theta htheta v
  apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hd)).mpr
  nlinarith

-- @node: flowCapacityLabel_ray_energy_le_one
/-- If [the edge masses form a nonnegative conserved flow supported on the tree](hyp:htheta),
[every ray has path potential at most one](hyp:hpotential), and [the chosen ray belongs
to the tree](hyp:hxi), then [the sum of squared capacity labels along its first n nonroot
vertices is at most one](goal). -/
lemma flowCapacityLabel_ray_energy_le_one (T : BoundedTree B) (lam : ℝ)
    (theta : List (Fin B) → ℝ) (htheta : IsFlow T theta)
    (hpotential : ∀ xi ∈ T.rays, pathPotential lam theta xi ≤ 1)
    (xi : ℕ → Fin B) (hxi : xi ∈ T.rays) (n : ℕ) :
    ∑ i ∈ Finset.range n, flowCapacityLabel T lam theta (rayPrefix xi (i + 1)) ^ 2 ≤ 1 := by
  calc
    _ ≤ ∑ i ∈ Finset.range n, normalizedEdgeFlow lam theta (rayPrefix xi (i + 1)) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have h := flowCapacityLabel_le_normalizedFlow T lam theta htheta hpotential
        (rayPrefix xi (i + 1)) (hxi (i + 1))
      have heq : normalizedFlow T lam theta (rayPrefix xi (i + 1)) =
          normalizedEdgeFlow lam theta (rayPrefix xi (i + 1)) := by
        simp only [normalizedFlow, rayPrefix, List.cons_ne_nil, if_false]
      rw [heq] at h
      exact (sq_le_sq₀ (flowCapacityLabel_nonneg T lam theta htheta _)
        (normalizedEdgeFlow_nonneg T lam theta htheta _)).mpr h
    _ = flowPrefixEnergy lam theta (rayPrefix xi n) := by
      rw [flowPrefixEnergy_rayPrefix]
      simp_rw [normalizedEdgeFlow_rayPrefix]
    _ ≤ 1 := flowPrefixEnergy_ray_le_one lam theta xi (hpotential xi hxi) n

-- @node: flowCapacityLabel_root_pos
/-- If [the total outgoing flow at the root is positive](hyp:hmass), then [the root's
flow capacity label is positive](goal). -/
lemma flowCapacityLabel_root_pos (T : BoundedTree B) (lam : ℝ)
    (theta : List (Fin B) → ℝ) (hmass : 0 < flowMass T theta) :
    0 < flowCapacityLabel T lam theta [] := by
  simpa only [flowCapacityLabel, normalizedFlow, if_true, flowPrefixEnergy, sub_zero] using
    div_pos hmass (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))

-- @node: capacity_pos_iff_positive_labels
/-- If [the tree is infinite with a positive finite branching bound](hyp:hT) and
[the channel parameter lies strictly between zero and one](hyp:hlam), then [the tree's
3-capacity is positive exactly when there are nonnegative vertex labels with a positive
root label such that each parent label is at most the sum of the child labels divided by
the square root of one plus their squares and multiplied by the squared channel parameter](goal). -/
theorem capacity_pos_iff_positive_labels (T : BoundedTree B) (lam : ℝ)
    (hT : MainTree T) (hlam : MainLambda lam) :
    0 < capacity3 T lam ↔ ∃ z : List (Fin B) → ℝ,
      FlowLabelRecursion T lam z ∧ 0 < z [] := by
  constructor
  · intro hcap
    obtain ⟨theta, htheta, hpotential, hmass⟩ := (capacity_pos_iff_exists_flow T lam).mp hcap
    exact ⟨flowCapacityLabel T lam theta,
      flowCapacityLabel_recursion T lam hlam theta htheta hpotential,
      flowCapacityLabel_root_pos T lam theta hmass⟩
  · rintro ⟨z, hz, hroot⟩
    exact (ENNReal.ofReal_pos.mpr hroot).trans_le
      (exists_flow_of_labels T lam z hT hlam hz).2

end OaiCapacityCriterionState

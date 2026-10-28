module

public import Papers.OaiCapacityCriterionState.Helpers.Trees
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Conservation and rescaling of admissible flows

Flow mass is conserved across every nonroot level. Rescaling a flow multiplies
its path potential by the square of the scale, so a positive flow with a uniform
finite potential bound supplies a positive-capacity certificate.
-/

@[expose] public section

open scoped BigOperators

namespace OaiCapacityCriterionState

variable {B : ℕ}

-- @node: BoundedTree.children_disjoint
/-- If [two words are distinct](hyp:hvw), then [their sets of children in the tree
are disjoint](goal). -/
lemma BoundedTree.children_disjoint (T : BoundedTree B)
    {v w : List (Fin B)} (hvw : v ≠ w) :
    Disjoint (T.children v) (T.children w) := by
  classical
  apply Finset.disjoint_left.mpr
  intro u hu hv
  obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hu
  obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hv
  exact hvw (List.cons.inj (ha.trans hb.symm)).2

-- @node: BoundedTree.sum_level_succ
/-- [The sum of any real-valued function over level n + 1 equals the sum, over
vertices at level n, of its sums over their children](goal). -/
lemma BoundedTree.sum_level_succ (T : BoundedTree B)
    (f : List (Fin B) → ℝ) (n : ℕ) :
    ∑ w ∈ T.level (n + 1), f w =
      ∑ v ∈ T.level n, ∑ w ∈ T.children v, f w := by
  classical
  rw [BoundedTree.level, Finset.sum_biUnion]
  intro v _ w _ hvw
  exact T.children_disjoint hvw

-- @node: flowMass_nonneg
/-- If [the vertex weights form a flow on the tree](hyp:htheta), then [their total
outgoing mass at the root is nonnegative](goal). -/
lemma flowMass_nonneg (T : BoundedTree B) (theta : List (Fin B) → ℝ)
    (htheta : IsFlow T theta) : 0 ≤ flowMass T theta := by
  classical
  exact Finset.sum_nonneg fun v _ => htheta.1 v

-- @node: flowMass_eq_sum_level
/-- If [the vertex weights form a flow on the tree](hyp:htheta), then [the total
outgoing mass at the root equals the sum of the weights at level n + 1](goal). -/
lemma flowMass_eq_sum_level (T : BoundedTree B) (theta : List (Fin B) → ℝ)
    (htheta : IsFlow T theta) (n : ℕ) :
    flowMass T theta = ∑ v ∈ T.level (n + 1), theta v := by
  classical
  induction n with
  | zero => simp [BoundedTree.level, flowMass]
  | succ n ih =>
      rw [T.sum_level_succ, ih]
      apply Finset.sum_congr rfl
      intro v hv
      obtain ⟨hvT, hlen⟩ := (T.mem_level_iff v (n + 1)).mp hv
      exact htheta.2.2 v hvT (by intro heq; simp [heq] at hlen)

-- @node: flow_le_flowMass
/-- If [the vertex weights form a flow](hyp:htheta) and [the word is a vertex of
the tree](hyp:hv) [other than the root](hyp:hne), then [its weight is at most the
total outgoing mass at the root](goal). -/
lemma flow_le_flowMass (T : BoundedTree B) (theta : List (Fin B) → ℝ)
    (htheta : IsFlow T theta) (v : List (Fin B)) (hv : v ∈ T.verts)
    (hne : v ≠ []) : theta v ≤ flowMass T theta := by
  classical
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero
    (show v.length ≠ 0 by simpa using hne)
  rw [flowMass_eq_sum_level T theta htheta n]
  exact Finset.single_le_sum (fun w _ => htheta.1 w)
    ((T.mem_level_iff v (n + 1)).mpr ⟨hv, hn⟩)

-- @node: IsFlow.mul_const
/-- If [the vertex weights form a flow](hyp:htheta) and [the scaling constant is
nonnegative](hyp:hc), then [multiplying every weight by that constant gives another
flow on the same tree](goal). -/
lemma IsFlow.mul_const (T : BoundedTree B) (theta : List (Fin B) → ℝ)
    (htheta : IsFlow T theta) {c : ℝ} (hc : 0 ≤ c) :
    IsFlow T (fun v => c * theta v) := by
  classical
  refine ⟨fun v => mul_nonneg hc (htheta.1 v), ?_, ?_⟩
  · intro v hv
    change c * theta v = 0
    rw [htheta.2.1 v hv, mul_zero]
  · intro v hv hne
    change c * theta v = ∑ w ∈ T.children v, c * theta w
    rw [htheta.2.2 v hv hne, Finset.mul_sum]

-- @node: flowMass_mul
/-- [Multiplying every vertex weight by a real constant multiplies the total
outgoing mass at the root by the same constant](goal). -/
lemma flowMass_mul (T : BoundedTree B) (theta : List (Fin B) → ℝ) (c : ℝ) :
    flowMass T (fun v => c * theta v) = c * flowMass T theta := by
  classical
  exact (Finset.mul_sum _ _ _).symm

-- @node: pathPotential_mul
/-- [Multiplying every vertex weight by a real constant multiplies the path
potential along any infinite sequence by the square of that constant](goal). -/
lemma pathPotential_mul (lam : ℝ) (theta : List (Fin B) → ℝ)
    (c : ℝ) (xi : ℕ → Fin B) :
    pathPotential lam (fun v => c * theta v) xi =
      ENNReal.ofReal (c ^ 2) * pathPotential lam theta xi := by
  unfold pathPotential
  simp_rw [show ∀ a b : ℝ, (a * (c * b)) ^ 2 = c ^ 2 * (a * b) ^ 2
    from fun a b => by ring, ENNReal.ofReal_mul (sq_nonneg c)]
  exact ENNReal.tsum_mul_left

-- @node: capacity_pos_iff_exists_flow
/-- [The tree has strictly positive capacity at the given parameter if and only
if it admits a flow with path potential at most one along every infinite ray and
strictly positive total outgoing mass at the root](goal). -/
lemma capacity_pos_iff_exists_flow (T : BoundedTree B) (lam : ℝ) :
    0 < capacity3 T lam ↔
      ∃ theta : List (Fin B) → ℝ, IsFlow T theta ∧
        (∀ xi ∈ T.rays, pathPotential lam theta xi ≤ 1) ∧
        0 < flowMass T theta := by
  constructor
  · intro hpos
    by_contra h
    have hzero : capacity3 T lam ≤ 0 := by
      apply iSup_le
      intro theta
      apply iSup_le
      intro ht
      apply iSup_le
      intro hp
      have hm : flowMass T theta ≤ 0 := by
        by_contra hm
        exact h ⟨theta, ht, hp, lt_of_not_ge hm⟩
      exact le_of_eq (ENNReal.ofReal_eq_zero.mpr hm)
    exact (not_lt_of_ge hzero) hpos
  · rintro ⟨theta, ht, hp, hm⟩
    exact (ENNReal.ofReal_pos.mpr hm).trans_le
      (le_iSup_of_le theta (le_iSup_of_le ht (le_iSup_of_le hp le_rfl)))

-- @node: capacity_pos_of_bounded_flow_potential
/-- If [the vertex weights form a flow](hyp:htheta) with [strictly positive total
outgoing mass at the root](hyp:hmass), and [K is nonnegative](hyp:hK) with [the path
potential along every infinite ray bounded above by K](hyp:hpotential), then
[the tree has strictly positive capacity at the given parameter](goal). -/
theorem capacity_pos_of_bounded_flow_potential (T : BoundedTree B) (lam : ℝ)
    (theta : List (Fin B) → ℝ) (htheta : IsFlow T theta)
    (hmass : 0 < flowMass T theta) (K : ℝ) (hK : 0 ≤ K)
    (hpotential : ∀ xi ∈ T.rays, pathPotential lam theta xi ≤ ENNReal.ofReal K) :
    0 < capacity3 T lam := by
  let c : ℝ := 1 / (K + 1)
  have hc : 0 < c := by dsimp [c]; positivity
  apply (capacity_pos_iff_exists_flow T lam).mpr
  refine ⟨fun v => c * theta v, IsFlow.mul_const T theta htheta hc.le, ?_, ?_⟩
  · intro xi hxi
    rw [pathPotential_mul]
    calc
      _ ≤ ENNReal.ofReal (c ^ 2) * ENNReal.ofReal K :=
        mul_le_mul le_rfl (hpotential xi hxi) zero_le zero_le
      _ = ENNReal.ofReal (c ^ 2 * K) := (ENNReal.ofReal_mul (sq_nonneg c)).symm
      _ ≤ 1 := by
        apply ENNReal.ofReal_le_one.mpr
        dsimp [c]
        have hden : 0 < (K + 1) ^ 2 := sq_pos_of_pos (by positivity)
        rw [div_pow, one_pow, div_mul_eq_mul_div, one_mul]
        apply (div_le_one hden).mpr
        nlinarith [sq_nonneg K]
  · rw [flowMass_mul]
    exact mul_pos hc hmass

-- @node: rayPrefix_prepend
/-- [The length n + 1 prefix of the sequence obtained by prepending a symbol to
an infinite sequence equals the original length n prefix followed by that symbol,
when prefixes are written in reverse chronological order](goal). -/
lemma rayPrefix_prepend (a : Fin B) (xi : ℕ → Fin B) (n : ℕ) :
    rayPrefix (fun k => Nat.casesOn k a xi) (n + 1) = rayPrefix xi n ++ [a] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change xi n :: rayPrefix (fun k => Nat.casesOn k a xi) (n + 1) =
        (xi n :: rayPrefix xi n) ++ [a]
      rw [ih]
      rfl

-- @node: rayWithPrefix
/-- For [an alphabet of B symbols](hyp:B), [the infinite sequence with a prescribed
finite prefix and an infinite continuation](goal) is constructed recursively:
[an empty prefix leaves the continuation unchanged](step:1), while [a nonempty
prefix is handled by moving its first symbol to the front of the continuation and
recursing on the remaining prefix](step:2). The prescribed prefix is stored in
reverse chronological order. -/
def rayWithPrefix : List (Fin B) → (ℕ → Fin B) → ℕ → Fin B
  | [], xi => xi
  | a :: v, xi => rayWithPrefix v (fun k => Nat.casesOn k a xi)

-- @node: rayPrefix_rayWithPrefix
/-- [After attaching a finite prefix to an infinite continuation, the prefix of
length n plus the prescribed prefix's length is the continuation's length n prefix
followed by the prescribed prefix, in reverse chronological order](goal). -/
lemma rayPrefix_rayWithPrefix (v : List (Fin B)) (xi : ℕ → Fin B) (n : ℕ) :
    rayPrefix (rayWithPrefix v xi) (n + v.length) = rayPrefix xi n ++ v := by
  induction v generalizing xi n with
  | nil => simp [rayWithPrefix]
  | cons a v ih =>
      rw [rayWithPrefix, List.length_cons,
        show n + (v.length + 1) = (n + 1) + v.length by omega,
        ih (fun k => Nat.casesOn k a xi) (n + 1)]
      rw [rayPrefix_prepend, List.append_assoc]
      rfl

-- @node: BoundedTree.rayPrefix_mem_of_le
/-- If [m is at most n](hyp:hmn) and [the length n prefix of an infinite sequence
is a vertex of the tree](hyp:hn), then [its length m prefix is also a vertex of
the tree](goal). -/
lemma BoundedTree.rayPrefix_mem_of_le (T : BoundedTree B) (xi : ℕ → Fin B)
    {m n : ℕ} (hmn : m ≤ n) (hn : rayPrefix xi n ∈ T.verts) :
    rayPrefix xi m ∈ T.verts := by
  induction n with
  | zero =>
      have hm : m = 0 := Nat.eq_zero_of_le_zero hmn
      simpa only [hm] using hn
  | succ n ih =>
      rcases Nat.eq_or_lt_of_le hmn with rfl | hlt
      · exact hn
      · exact ih (Nat.le_of_lt_succ hlt) (T.prefix_closed _ _ hn)

-- @node: IsFlow.exists_positive_child
/-- If [the vertex weights form a flow](hyp:htheta) and [the word is a vertex of
the tree](hyp:hv) [other than the root](hyp:hne) with [strictly positive
weight](hyp:hpos), then [it has a child in the tree with strictly positive
weight](goal). -/
lemma IsFlow.exists_positive_child (T : BoundedTree B)
    (theta : List (Fin B) → ℝ) (htheta : IsFlow T theta)
    (v : List (Fin B)) (hv : v ∈ T.verts) (hne : v ≠ [])
    (hpos : 0 < theta v) :
    ∃ a : Fin B, a :: v ∈ T.verts ∧ 0 < theta (a :: v) := by
  classical
  rw [htheta.2.2 v hv hne] at hpos
  obtain ⟨w, hw, hwp⟩ :=
    (Finset.sum_pos_iff_of_nonneg (fun w _ => htheta.1 w)).mp hpos
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw
  exact ⟨a, (Finset.mem_filter.mp ha).2, hwp⟩

-- @node: IsFlow.exists_ray_through_positive
/-- If [the vertex weights form a flow](hyp:htheta) and [the word is a vertex of
the tree](hyp:hv) [other than the root](hyp:hne) with [strictly positive
weight](hyp:hpos), then [there is an infinite ray in the tree whose prefix at the
word's depth is exactly that word](goal). -/
lemma IsFlow.exists_ray_through_positive (T : BoundedTree B)
    (theta : List (Fin B) → ℝ) (htheta : IsFlow T theta)
    (v : List (Fin B)) (hv : v ∈ T.verts) (hne : v ≠ [])
    (hpos : 0 < theta v) :
    ∃ xi ∈ T.rays, rayPrefix xi v.length = v := by
  classical
  let V := {w : List (Fin B) // w ∈ T.verts ∧ w ≠ [] ∧ 0 < theta w}
  let step (w : V) : Fin B :=
    Classical.choose (IsFlow.exists_positive_child T theta htheta w.1
      w.2.1 w.2.2.1 w.2.2.2)
  have hstep (w : V) : step w :: w.1 ∈ T.verts ∧ 0 < theta (step w :: w.1) :=
    Classical.choose_spec (IsFlow.exists_positive_child T theta htheta w.1
      w.2.1 w.2.2.1 w.2.2.2)
  let branch : ℕ → V := Nat.rec ⟨v, hv, hne, hpos⟩
    (fun _ w => ⟨step w :: w.1, (hstep w).1, List.cons_ne_nil _ _, (hstep w).2⟩)
  let tail : ℕ → Fin B := fun n => step (branch n)
  have hbranch (n : ℕ) : rayPrefix tail n ++ v = (branch n).1 := by
    induction n with
    | zero => rfl
    | succ n ih =>
        change (tail n :: rayPrefix tail n) ++ v = step (branch n) :: (branch n).1
        rw [List.cons_append, ih]
  let xi := rayWithPrefix v tail
  have hprefix (n : ℕ) : rayPrefix xi (n + v.length) = (branch n).1 := by
    rw [rayPrefix_rayWithPrefix, hbranch]
  have hstart : rayPrefix xi v.length = v := by
    simpa only [Nat.zero_add, branch, Nat.rec_zero] using hprefix 0
  refine ⟨xi, ?_, hstart⟩
  intro n
  by_cases hn : n ≤ v.length
  · exact T.rayPrefix_mem_of_le xi hn (by rw [hstart]; exact hv)
  · have hn' : v.length ≤ n := le_of_not_ge hn
    have heq : n - v.length + v.length = n := Nat.sub_add_cancel hn'
    rw [← heq, hprefix]
    exact (branch (n - v.length)).2.1

-- @node: pathPotential_term_le_one
/-- If [the path potential along an infinite sequence is at most one](hyp:hxi),
then [at depth n + 1, the square of the vertex weight multiplied by the parameter
raised to minus twice that depth is at most one](goal). -/
lemma pathPotential_term_le_one (lam : ℝ) (theta : List (Fin B) → ℝ)
    (xi : ℕ → Fin B) (hxi : pathPotential lam theta xi ≤ 1) (n : ℕ) :
    (lam ^ (-(2 * ((n + 1 : ℕ) : ℤ))) * theta (rayPrefix xi (n + 1))) ^ 2 ≤ 1 := by
  apply ENNReal.ofReal_le_one.mp
  exact (ENNReal.le_tsum n).trans hxi

-- @node: admissible_flow_edge_bound
/-- If [the parameter lies strictly between zero and one](hyp:hlam), [the vertex
weights form a flow](hyp:htheta), and [every infinite ray has path potential at
most one](hyp:hpotential), then at [any vertex of the tree](hyp:hv) [other than
the root](hyp:hne), [the weight is at most the squared parameter raised to the
vertex's depth](goal). -/
lemma admissible_flow_edge_bound (T : BoundedTree B) (lam : ℝ)
    (hlam : MainLambda lam) (theta : List (Fin B) → ℝ) (htheta : IsFlow T theta)
    (hpotential : ∀ xi ∈ T.rays, pathPotential lam theta xi ≤ 1)
    (v : List (Fin B)) (hv : v ∈ T.verts) (hne : v ≠ []) :
    theta v ≤ sqParam lam ^ v.length := by
  by_cases hpos : 0 < theta v
  · obtain ⟨xi, hxi, heq⟩ :=
      IsFlow.exists_ray_through_positive T theta htheta v hv hne hpos
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero
      (show v.length ≠ 0 by simpa using hne)
    change v.length = n + 1 at hn
    have hterm := pathPotential_term_le_one lam theta xi (hpotential xi hxi) n
    rw [← hn, heq] at hterm
    have hexp : (2 : ℤ) * (v.length : ℤ) = ((2 * v.length : ℕ) : ℤ) := by
      push_cast
      rfl
    have hpower : lam ^ (-(2 * (v.length : ℤ))) = (sqParam lam ^ v.length)⁻¹ := by
      rw [zpow_neg, hexp, zpow_natCast, sqParam, pow_mul]
    rw [hpower] at hterm
    have hbound : (sqParam lam ^ v.length)⁻¹ * theta v ≤ 1 := by
      nlinarith
    have hr : 0 < sqParam lam ^ v.length := pow_pos (pow_pos hlam.1 _) _
    apply (div_le_one hr).mp
    simpa only [div_eq_mul_inv, mul_comm] using hbound
  · exact (le_of_not_gt hpos).trans (pow_nonneg (sq_nonneg lam) _)

-- @node: admissible_flow_mass_le_level
/-- If [the parameter lies strictly between zero and one](hyp:hlam), [the vertex
weights form a flow](hyp:htheta), and [every infinite ray has path potential at
most one](hyp:hpotential), then [the total outgoing mass at the root is at most
the number of vertices at level n + 1 times the squared parameter raised to
n + 1](goal). -/
lemma admissible_flow_mass_le_level (T : BoundedTree B) (lam : ℝ)
    (hlam : MainLambda lam) (theta : List (Fin B) → ℝ) (htheta : IsFlow T theta)
    (hpotential : ∀ xi ∈ T.rays, pathPotential lam theta xi ≤ 1) (n : ℕ) :
    flowMass T theta ≤ (T.level (n + 1)).card * sqParam lam ^ (n + 1) := by
  classical
  rw [flowMass_eq_sum_level T theta htheta n]
  calc
    _ ≤ ∑ v ∈ T.level (n + 1), sqParam lam ^ (n + 1) := by
      apply Finset.sum_le_sum
      intro v hv
      obtain ⟨hvT, hlen⟩ := (T.mem_level_iff v (n + 1)).mp hv
      simpa only [hlen] using admissible_flow_edge_bound T lam hlam theta htheta
        hpotential v hvT (by intro heq; simp [heq] at hlen)
    _ = _ := by simp

-- @node: capacity_le_level
/-- If [the parameter lies strictly between zero and one](hyp:hlam), then [the
tree's capacity is at most the number of vertices at level n + 1 times the squared
parameter raised to n + 1](goal). -/
theorem capacity_le_level (T : BoundedTree B) (lam : ℝ)
    (hlam : MainLambda lam) (n : ℕ) :
    capacity3 T lam ≤ ENNReal.ofReal
      ((T.level (n + 1)).card * sqParam lam ^ (n + 1)) := by
  apply iSup_le
  intro theta
  apply iSup_le
  intro ht
  apply iSup_le
  intro hp
  exact ENNReal.ofReal_le_ofReal (admissible_flow_mass_le_level T lam hlam theta ht hp n)

end OaiCapacityCriterionState

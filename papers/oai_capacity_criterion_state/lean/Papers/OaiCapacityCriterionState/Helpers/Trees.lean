module

public import Mathlib.Data.List.Infix
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Finset.Union
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! # Bounded rooted trees, flows, and nonlinear capacity

Vertices are reversed Ulam--Harris words. The root is the empty word and the
parent operation deletes the head. Infinite trees are selected by `MainTree`.
All infinite potentials and suprema take values in the extended nonnegative reals.
-/

@[expose] public section

open scoped BigOperators ENNReal

namespace OaiCapacityCriterionState

/-- A deterministic prefix-closed tree; the alphabet enforces the child bound. -/
structure BoundedTree (B : ℕ) where -- @realizes B(natural child bound; positivity in MainTree)
  verts : Set (List (Fin B)) -- @realizes T(deterministic vertices; infinitude in MainTree)
  nil_mem : [] ∈ verts -- @realizes \rho(the empty word is the root vertex)
  prefix_closed : ∀ a v, a :: v ∈ verts → v ∈ verts

-- @env: S1
variable {B : ℕ}

/-- The [depth](goal) of [a vertex word](hyp:v) is its length.
@realizes |v|(nonnegative integer depth, the word length)
@realizes |e|(edge depth is the length of its nonempty child endpoint) -/
def depth (v : List (Fin B)) : ℕ := v.length

namespace BoundedTree

open Classical in
/-- In [a bounded tree](hyp:T), the [children](goal) of [a vertex word](hyp:v)
are the tree vertices obtained by prepending one letter to that word.
@realizes \children(v)(at most B child vertices, obtained by prepending a letter) -/
noncomputable def children (T : BoundedTree B) (v : List (Fin B)) :
    Finset (List (Fin B)) :=
  (Finset.univ.filter (fun a : Fin B => a :: v ∈ T.verts)).image (fun a => a :: v)

-- @node: def:tree-notation
/-- The [levels](goal) of [a bounded tree](hyp:T) are defined recursively:
[level zero consists of the root](step:1), and [each subsequent level is the union
of the children of the preceding level's vertices](step:2).
@realizes L_n(the finite set of tree vertices at depth n) -/
noncomputable def level (T : BoundedTree B) : ℕ → Finset (List (Fin B))
  | 0 => {[]}
  | n + 1 => (T.level n).biUnion T.children

-- @node: mem_level_iff
/-- [A word belongs to level n of a bounded tree exactly when it is a tree vertex
and its length equals n](goal). -/
lemma mem_level_iff (T : BoundedTree B) (v : List (Fin B)) (n : ℕ) :
    v ∈ T.level n ↔ v ∈ T.verts ∧ v.length = n := by
  classical
  induction n generalizing v with
  | zero =>
      simp only [level, Finset.mem_singleton, List.length_eq_zero_iff]
      constructor
      · intro h
        subst v
        exact ⟨T.nil_mem, rfl⟩
      · exact fun h => h.2
  | succ n ih =>
      simp only [level, Finset.mem_biUnion]
      constructor
      · rintro ⟨w, hw, hv⟩
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
        have hav := (Finset.mem_filter.mp ha).2
        exact ⟨hav, by simpa using congrArg Nat.succ (ih w |>.mp hw).2⟩
      · rintro ⟨hv, hlen⟩
        cases v with
        | nil => simp at hlen
        | cons a w =>
            refine ⟨w, (ih w).mpr ⟨T.prefix_closed a w hv, by simpa using hlen⟩, ?_⟩
            exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, rfl⟩

/-- The [balls around the root](goal) of [a bounded tree](hyp:T) are defined
recursively: [the radius-zero ball consists of the root](step:1), and
[the radius-(n + 1) ball adds level n + 1 to the radius-n ball](step:2). -/
noncomputable def ball (T : BoundedTree B) : ℕ → Finset (List (Fin B))
  | 0 => {[]}
  | n + 1 => T.ball n ∪ T.level (n + 1)

-- @node: mem_ball_iff
/-- [A word belongs to the radius-n ball of a bounded tree exactly when it is a
tree vertex and its length is at most n](goal). -/
lemma mem_ball_iff (T : BoundedTree B) (v : List (Fin B)) (n : ℕ) :
    v ∈ T.ball n ↔ v ∈ T.verts ∧ v.length ≤ n := by
  classical
  induction n with
  | zero =>
      simp only [ball, Finset.mem_singleton, Nat.le_zero, List.length_eq_zero_iff]
      constructor
      · intro h
        subst v
        exact ⟨T.nil_mem, rfl⟩
      · exact fun h => h.2
  | succ n ih =>
      rw [ball, Finset.mem_union, ih, mem_level_iff]
      constructor
      · rintro (⟨hv, hlen⟩ | ⟨hv, hlen⟩)
        · exact ⟨hv, Nat.le.step hlen⟩
        · exact ⟨hv, hlen.le⟩
      · rintro ⟨hv, hlen⟩
        rcases Nat.eq_or_lt_of_le hlen with heq | hlt
        · exact Or.inr ⟨hv, heq⟩
        · exact Or.inl ⟨hv, Nat.le_of_lt_succ hlt⟩

end BoundedTree

-- @node: ass:main-tree
/-- The [main tree condition](goal) on [a bounded tree](hyp:T) requires
[a strictly positive branching bound](step:1) and [infinitely many vertices](step:2). -/
def MainTree (T : BoundedTree B) : Prop :=
  0 < B ∧ -- @realizes B(strictly positive finite branching bound)
  T.verts.Infinite -- @realizes T(infinite rooted tree)

-- @node: ass:main-lambda
/-- For [a real channel parameter](hyp:lam), the [main parameter condition](goal)
requires [strict positivity](step:1) and [a value strictly less than one](step:2).
@realizes \lambda(channel parameter restricted to (0,1)) -/
def MainLambda (lam : ℝ) : Prop := 0 < lam ∧ lam < 1

-- @node: def:r
/-- The [squared channel parameter](goal) is the square of [the real channel
parameter](hyp:lam).
@realizes r(the squared channel parameter; range (0,1) under MainLambda) -/
def sqParam (lam : ℝ) : ℝ := lam ^ 2

-- @node: sqParam_mem_Ioo
/-- If [the channel parameter is strictly between zero and one](hyp:hlam),
[its square is also strictly between zero and one](goal). -/
lemma sqParam_mem_Ioo (lam : ℝ) (hlam : MainLambda lam) :
    sqParam lam ∈ Set.Ioo 0 1 := by
  obtain ⟨hpos, hlt⟩ := hlam
  change 0 < lam ^ 2 ∧ lam ^ 2 < 1
  constructor
  · positivity
  · nlinarith [mul_pos hpos (sub_pos.mpr hlt)]

-- @node: ass:flow-label-recursion
/-- For [a bounded tree](hyp:T), [a real channel parameter](hyp:lam), and
[real labels assigned to vertex words](hyp:z), the [flow-label recursion
condition](goal) requires, at every tree vertex, [a nonnegative label](step:1)
and [a label no larger than the sum over its children of the squared channel
parameter times the child's label divided by the square root of one plus the
square of that label](step:2). -/
def FlowLabelRecursion (T : BoundedTree B) (lam : ℝ)
    (z : List (Fin B) → ℝ) : Prop :=
  ∀ v ∈ T.verts,
    0 ≤ z v ∧ -- @realizes z_v(finite nonnegative real labels on vertices)
    z v ≤ ∑ w ∈ T.children v, sqParam lam * z w / Real.sqrt (1 + z w ^ 2)

-- @node: def:flow
/-- For [a bounded tree](hyp:T), [a real assignment to vertex words](hyp:theta)
is [a flow](goal) when [all its values are nonnegative](step:1), [its values
outside the tree vanish](step:2), and [at every nonroot tree vertex its value
equals the sum of the values at its children](step:3).

Flow values are indexed by child endpoints; the unused root value is immaterial. -/
def IsFlow (T : BoundedTree B) (theta : List (Fin B) → ℝ) : Prop :=
  (∀ v, 0 ≤ theta v) ∧ -- @realizes \theta(nonnegative) @realizes |\theta|(nonnegative sum)
  (∀ v ∉ T.verts, theta v = 0) ∧
  ∀ v ∈ T.verts, v ≠ [] → theta v =
    ∑ w ∈ T.children v, theta w -- @realizes \theta(conservation at every nonroot vertex)

/-- For [a bounded tree](hyp:T) and [a real assignment to vertex words](hyp:theta),
the [flow mass](goal) is the sum of the assigned values at the root's children.
@realizes |\theta|(sum of outgoing flow at the root) -/
noncomputable def flowMass (T : BoundedTree B) (theta : List (Fin B) → ℝ) : ℝ :=
  ∑ w ∈ T.children [], theta w

/-- The [finite prefixes](goal) of [an infinite sequence of child labels](hyp:xi)
are stored in reverse order: [the length-zero prefix is empty](step:1), and
[the length-(n + 1) prefix prepends the nth label to the length-n prefix](step:2).
@realizes \xi(an infinite word; membership in rays requires every prefix to lie in T) -/
def rayPrefix (xi : ℕ → Fin B) : ℕ → List (Fin B)
  | 0 => []
  | n + 1 => xi n :: rayPrefix xi n

-- @node: def:edge-boundary
/-- The [rays](goal) of [a bounded tree](hyp:T) are the infinite sequences of
child labels whose every finite prefix, stored in reverse order, is a tree vertex.
@realizes \partial T(infinite paths from the root)
@realizes \xi(every finite prefix is a tree vertex) -/
def BoundedTree.rays (T : BoundedTree B) : Set (ℕ → Fin B) :=
  {xi | ∀ n, rayPrefix xi n ∈ T.verts}

-- @node: BoundedTree.mem_of_append_mem
/-- If [concatenating a word with a terminal word gives a tree vertex](hyp:h),
[the terminal word is itself a tree vertex](goal). -/
lemma BoundedTree.mem_of_append_mem (T : BoundedTree B)
    (u v : List (Fin B)) (h : u ++ v ∈ T.verts) : v ∈ T.verts := by
  induction u with
  | nil => simpa using h
  | cons a u ih => exact ih (T.prefix_closed a (u ++ v) h)

-- @node: BoundedTree.infinite_extension_child
/-- If [a word has infinitely many extensions in a bounded tree](hyp:hv),
[some child of that word also has infinitely many extensions in the tree](goal). -/
lemma BoundedTree.infinite_extension_child (T : BoundedTree B) (v : List (Fin B))
    (hv : {u : List (Fin B) | u ++ v ∈ T.verts}.Infinite) :
    ∃ a : Fin B, {u : List (Fin B) | u ++ (a :: v) ∈ T.verts}.Infinite := by
  classical
  by_contra h
  have hfin : ∀ a : Fin B, {u : List (Fin B) | u ++ (a :: v) ∈ T.verts}.Finite := by
    simpa only [not_exists, Set.not_infinite] using h
  have hcover : {u : List (Fin B) | u ++ v ∈ T.verts} ⊆
      {[]} ∪ ⋃ a : Fin B,
        (fun u : List (Fin B) => u ++ [a]) '' {u | u ++ (a :: v) ∈ T.verts} := by
    intro u hu
    rcases List.eq_nil_or_concat' u with rfl | ⟨w, a, rfl⟩
    · exact Or.inl (Set.mem_singleton [])
    · apply Or.inr
      exact Set.mem_iUnion.mpr ⟨a, w, by simpa [List.append_assoc] using hu, rfl⟩
  exact hv ((Set.finite_singleton []).union
    (Set.finite_iUnion fun a => (hfin a).image _ ) |>.subset hcover)

-- @node: rays_nonempty
/-- If [a bounded tree has a strictly positive branching bound and infinitely
many vertices](hyp:hT), [it has an infinite ray from the root](goal). -/
lemma rays_nonempty (T : BoundedTree B) (hT : MainTree T) :
    T.rays.Nonempty := by
  classical
  let step (v : {v : List (Fin B) | {u : List (Fin B) | u ++ v ∈ T.verts}.Infinite}) :
      Fin B := Classical.choose (T.infinite_extension_child v.1 v.2)
  let branch : ℕ → {v : List (Fin B) | {u : List (Fin B) | u ++ v ∈ T.verts}.Infinite} :=
    Nat.rec ⟨[], by simpa using hT.2⟩ fun _ v =>
      ⟨step v :: v.1, Classical.choose_spec (T.infinite_extension_child v.1 v.2)⟩
  let xi : ℕ → Fin B := fun n => step (branch n)
  have hprefix : ∀ n, rayPrefix xi n = (branch n).1 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        change xi n :: rayPrefix xi n = step (branch n) :: (branch n).1
        rw [ih]
  refine ⟨xi, fun n => ?_⟩
  rw [hprefix]
  obtain ⟨u, hu⟩ := (branch n).2.nonempty
  exact T.mem_of_append_mem u (branch n).1 hu

/-- For [a real channel parameter](hyp:lam), [real values assigned to vertex
words](hyp:theta), and [an infinite sequence of child labels](hyp:xi), the
[path potential](goal) is the extended nonnegative sum, over positive depths,
of the squares of the assigned values along the sequence, each first rescaled
by the channel parameter raised to minus twice its depth.
@realizes V_\lambda(extended nonnegative sum of squared rescaled edge flows) -/
noncomputable def pathPotential (lam : ℝ) (theta : List (Fin B) → ℝ)
    (xi : ℕ → Fin B) : ℝ≥0∞ :=
  ∑' n : ℕ, ENNReal.ofReal
    ((lam ^ (-(2 * ((n + 1 : ℕ) : ℤ))) * theta (rayPrefix xi (n + 1))) ^ 2)

-- @node: def:capacity
/-- For [a bounded tree](hyp:T) and [a real channel parameter](hyp:lam), the
[nonlinear capacity of order three](goal) is the supremum of root flow masses
over nonnegative conserved flows whose path potential is at most one on every ray,
with masses interpreted as extended nonnegative real numbers.
@realizes \Capacity_{3,\lambda}(supremum of admissible flow masses) -/
noncomputable def capacity3 (T : BoundedTree B) (lam : ℝ) : ℝ≥0∞ :=
  ⨆ (theta : List (Fin B) → ℝ) (_ : IsFlow T theta)
    (_ : ∀ xi ∈ T.rays, pathPotential lam theta xi ≤ 1),
    ENNReal.ofReal (flowMass T theta)

end OaiCapacityCriterionState

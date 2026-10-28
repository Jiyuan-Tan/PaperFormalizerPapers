module
public import Papers.OaiGeometricErdosSimilarity.Helpers.Stability
public import Mathlib.Data.List.OfFn

/-! # Transporting the route to the first default vertex -/

@[expose] public section

namespace Papers.OaiGeometricErdosSimilarity

attribute [local instance] Classical.propDecidable
variable {q : ℝ} {M d g r0 n0 : ℕ}

-- @node: chooseChild_eq_of_first_one
/-- If [the branching number is at least two](hyp:hM), [a child index is nondefault](hyp:hi), [its selector bit is true](hyp:hone), and [all earlier child bits are false](hyp:hzero), then [the ordered search selects that child](goal). -/
lemma chooseChild_eq_of_first_one (hM : BranchingDomain M)
    (ξ : NondefaultEdge M d → Bool) (U : InternalVertex M d) (i : Fin M)
    (hi : i.val + 1 < M) (hone : ξ (nondefaultChildEdge U i hi) = true)
    (hzero : ∀ j : Fin M, ∀ hj : j < i,
      ξ (nondefaultChildEdge U j (by omega)) = false) : chooseChild hM ξ U = i := by
  unfold chooseChild
  have hfind : (List.finRange M).find? (fun j =>
      if hj : j.val + 1 < M then ξ (nondefaultChildEdge U j hj) else false) = some i := by
    rw [← List.ofFn_id, List.find?_ofFn_eq_some]
    refine ⟨by simpa only [dif_pos hi] using hone, i, rfl, ?_⟩
    intro j hj
    have hjM : j.val + 1 < M := by omega
    simp [hjM, hzero j hj]
  rw [hfind]
  rfl

-- @node: chooseChild_earlier_zero
/-- If [the branching number is at least two](hyp:hM) and [a child index precedes the selected child](hyp:hj), then [its nondefault selector bit is false](goal), including when the selected child is the default. -/
lemma chooseChild_earlier_zero (hM : BranchingDomain M)
    (ξ : NondefaultEdge M d → Bool) (U : InternalVertex M d)
    (j : Fin M) (hj : j < chooseChild hM ξ U) :
    ξ (nondefaultChildEdge U j (by have := (chooseChild hM ξ U).isLt; omega)) = false := by
  have hjbound : j.val + 1 < M := by have := (chooseChild hM ξ U).isLt; omega
  change ξ (nondefaultChildEdge U j hjbound) = false
  unfold chooseChild at hj
  generalize hf : (List.finRange M).find? (fun i =>
    if hi : i.val + 1 < M then ξ (nondefaultChildEdge U i hi) else false) = o at hj
  cases o with
  | none =>
      have hall := List.find?_eq_none.mp hf
      have hjM : j.val + 1 < M := by
        change j < defaultChild hM at hj
        change j.val < M - 1 at hj
        omega
      simpa [hjM] using hall j (List.mem_finRange j)
  | some i =>
      change j < i at hj
      rw [← List.ofFn_id, List.find?_ofFn_eq_some] at hf
      obtain ⟨_, k, rfl, hk⟩ := hf
      have hjM : j.val + 1 < M := by have := k.isLt; omega
      simpa [hjM] using hk j hj

-- @node: chooseChild_selected_one
/-- If [the branching number is at least two](hyp:hM) and [the selected child is not the default child](hyp:hne), then [its index is nondefault and its selector bit is true](goal). -/
lemma chooseChild_selected_one (hM : BranchingDomain M)
    (ξ : NondefaultEdge M d → Bool) (U : InternalVertex M d)
    (hne : chooseChild hM ξ U ≠ defaultChild hM) :
    ∃ hi : (chooseChild hM ξ U).val + 1 < M,
      ξ (nondefaultChildEdge U (chooseChild hM ξ U) hi) = true := by
  unfold chooseChild at hne ⊢
  generalize hf : (List.finRange M).find? (fun i =>
    if hi : i.val + 1 < M then ξ (nondefaultChildEdge U i hi) else false) = o at hne ⊢
  cases o with
  | none => exact False.elim (hne rfl)
  | some i =>
      have hp := List.find?_some hf
      change (if hi : i.val + 1 < M then ξ (nondefaultChildEdge U i hi) else false) = true at hp
      split at hp
      · exact ⟨‹_›, hp⟩
      · contradiction

-- @node: walkVertices_mem_prefix
/-- If [the branching number is at least two](hyp:hM) and [a vertex occurs in the walk from a starting vertex with the given step budget](hyp:hw), then [the starting vertex's path is a prefix of that vertex's path](goal). -/
lemma walkVertices_mem_prefix (hM : BranchingDomain M) (ξ : NondefaultEdge M d → Bool)
    (fuel : ℕ) (v w : TreeVertex M d) (hw : w ∈ walkVertices hM ξ fuel v) :
    (vertexPath v).IsPrefix (vertexPath w) := by
  induction fuel generalizing v with
  | zero =>
      simp only [walkVertices, List.mem_singleton] at hw
      subst w
      exact ⟨[], by simp⟩
  | succ fuel ih =>
      by_cases hv : v.1.val < d
      · simp only [walkVertices, dif_pos hv, List.mem_cons] at hw
        rcases hw with rfl | hw
        · exact ⟨[], by simp⟩
        · apply List.IsPrefix.trans _ (ih _ hw)
          rw [vertexPath_child]
          exact List.prefix_append _ _
      · simp only [walkVertices, dif_neg hv, List.mem_singleton] at hw
        subst w
        exact ⟨[], by simp⟩

-- @node: defaultAtVertex
/-- Given [a branching number of at least two](hyp:hM), [a Boolean assignment to nondefault edges](hyp:ξ), and [a vertex to test](hyp:v), the [default test](goal) returns that vertex as an internal vertex if it selects its default child, and returns no vertex otherwise. -/
noncomputable def defaultAtVertex (hM : BranchingDomain M)
    (ξ : NondefaultEdge M d → Bool) (v : TreeVertex M d) : Option (InternalVertex M d) :=
  if hv : v.1.val < d then
    if chooseChild hM ξ ⟨v, hv⟩ = defaultChild hM then some ⟨v, hv⟩ else none
  else none

-- @node: defaultAtVertex_eq_some
/-- When [the branching number is at least two](hyp:hM), [the default test at a vertex returns a specified internal vertex exactly when the two vertices coincide and that internal vertex selects its default child](goal). -/
lemma defaultAtVertex_eq_some (hM : BranchingDomain M)
    (ξ : NondefaultEdge M d → Bool) (v : TreeVertex M d) (U : InternalVertex M d) :
    defaultAtVertex hM ξ v = some U ↔
      v = U.val ∧ chooseChild hM ξ U = defaultChild hM := by
  unfold defaultAtVertex
  split
  · rename_i hv
    split
    · rename_i hc
      constructor
      · intro h
        have hU : (⟨v, hv⟩ : InternalVertex M d) = U := Option.some.inj h
        subst U
        exact ⟨rfl, hc⟩
      · rintro ⟨rfl, _⟩
        rfl
    · rename_i hc
      constructor
      · intro h; cases h
      · rintro ⟨rfl, h⟩
        exact (hc h).elim
  · rename_i hv
    constructor
    · intro h; cases h
    · rintro ⟨rfl, _⟩
      exact (hv U.property).elim

-- @node: firstDefaultFrom_mem
/-- If [the branching number is at least two](hyp:hM) and [the search along a walk returns a specified vertex as its first default vertex](hyp:h), then [that vertex belongs to the walk and selects its default child](goal). -/
lemma firstDefaultFrom_mem (hM : BranchingDomain M) (ξ : NondefaultEdge M d → Bool)
    (fuel : ℕ) (v : TreeVertex M d) (U : InternalVertex M d)
    (h : (walkVertices hM ξ fuel v).findSome? (defaultAtVertex hM ξ) = some U) :
    U.val ∈ walkVertices hM ξ fuel v ∧ chooseChild hM ξ U = defaultChild hM := by
  obtain ⟨w, hw, htest⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨rfl, hchoose⟩ := (defaultAtVertex_eq_some hM ξ w U).mp htest
  exact ⟨hw, hchoose⟩

-- @node: preorderLt_sibling
/-- If [one child index is smaller than another](hyp:hij), then [the edge to the earlier child precedes the edge to the later child in preorder](goal). -/
lemma preorderLt_sibling (U : InternalVertex M d) (i j : Fin M) (hij : i < j) :
    preorderLt (childEdge U i) (childEdge U j) := by
  change List.Lex (· < ·) (vertexPath (child U i)) (vertexPath (child U j))
  rw [vertexPath_child, vertexPath_child]
  exact List.Lex.append_left _ (List.Lex.rel hij) _

-- @node: preorderLt_child_of_le_prefix
/-- If [a child index j is no greater than a child index a](hyp:hj) and [the path to child a of an internal vertex P is a prefix of the path to an internal vertex U](hyp:hp), then [the edge to child j of P precedes every specified child edge of U in preorder](goal). -/
lemma preorderLt_child_of_le_prefix (P U : InternalVertex M d) (a j i : Fin M)
    (hj : j ≤ a) (hp : (vertexPath (child P a)).IsPrefix (vertexPath U.val)) :
    preorderLt (childEdge P j) (childEdge U i) := by
  obtain ⟨s, hs⟩ := hp
  change List.Lex (· < ·) (vertexPath (child P j)) (vertexPath (child U i))
  rw [vertexPath_child, vertexPath_child, ← hs, vertexPath_child]
  rw [List.append_assoc, List.append_assoc]
  apply List.Lex.append_left
  rcases lt_or_eq_of_le hj with hj | rfl
  · exact List.Lex.rel hj
  · simp only [List.singleton_append]
    apply List.Lex.cons
    cases s <;> exact List.Lex.nil

-- @node: walkVertices_last_eq_of_fuel
/-- If [the branching number is at least two](hyp:hM) and [each of two step budgets covers the remaining depth from a starting vertex](hyp:h,h'), then [the walks with those budgets end at the same vertex](goal). -/
lemma walkVertices_last_eq_of_fuel (hM : BranchingDomain M)
    (ξ : NondefaultEdge M d → Bool) (fuel fuel' : ℕ) (v : TreeVertex M d)
    (h : d - v.1.val ≤ fuel) (h' : d - v.1.val ≤ fuel') :
    (walkVertices hM ξ fuel v).getLast (walkVertices_ne_nil hM ξ fuel v) =
      (walkVertices hM ξ fuel' v).getLast (walkVertices_ne_nil hM ξ fuel' v) := by
  induction fuel generalizing fuel' v with
  | zero =>
      have hv : ¬v.1.val < d := by omega
      cases fuel' <;> simp [walkVertices, hv]
  | succ fuel ih =>
      by_cases hv : v.1.val < d
      · cases fuel' with
        | zero => omega
        | succ fuel' =>
            simp only [walkVertices, dif_pos hv]
            rw [List.getLast_cons (walkVertices_ne_nil hM ξ fuel _),
              List.getLast_cons (walkVertices_ne_nil hM ξ fuel' _)]
            apply ih
            all_goals change d - (v.1.val + 1) ≤ _; omega
      · cases fuel' <;> simp [walkVertices, hv]

-- @node: routeFrom_step
/-- When [the branching number is at least two](hyp:hM), [routing from an internal vertex reaches the same leaf as routing from its selected child](goal), for the same random table and real point. -/
lemma routeFrom_step (hM : BranchingDomain M) (ω : Outcome q M d g r0 n0) (z : ℝ)
    (U : InternalVertex M d) :
    routeFrom hM ω z U.val =
      routeFrom hM ω z (child U (chooseChild hM (exposedValues ω z) U)) := by
  apply Subtype.ext
  change (walkVertices hM (exposedValues ω z) d U.val).getLast _ = _
  calc
    _ = (walkVertices hM (exposedValues ω z) (d + 1) U.val).getLast
        (walkVertices_ne_nil hM (exposedValues ω z) (d + 1) U.val) :=
      walkVertices_last_eq_of_fuel hM (exposedValues ω z) d (d + 1) U.val
        (Nat.sub_le _ _) ((Nat.sub_le _ _).trans (Nat.le_succ d))
    _ = _ := by
      simp only [walkVertices, dif_pos U.property]
      rw [List.getLast_cons (walkVertices_ne_nil hM (exposedValues ω z) d _)]
      rfl

-- @node: routeFrom_eq_of_mem_walkVertices
/-- If [the branching number is at least two](hyp:hM) and [a vertex occurs in the selector walk from a starting vertex at the given real point](hyp:hw), then [routing from either vertex reaches the same leaf](goal). -/
lemma routeFrom_eq_of_mem_walkVertices (hM : BranchingDomain M)
    (ω : Outcome q M d g r0 n0) (z : ℝ) (fuel : ℕ) (v w : TreeVertex M d)
    (hw : w ∈ walkVertices hM (exposedValues ω z) fuel v) :
    routeFrom hM ω z v = routeFrom hM ω z w := by
  induction fuel generalizing v with
  | zero =>
      simp only [walkVertices, List.mem_singleton] at hw
      subst w
      rfl
  | succ fuel ih =>
      by_cases hv : v.1.val < d
      · simp only [walkVertices, dif_pos hv, List.mem_cons] at hw
        rcases hw with rfl | hw
        · rfl
        · exact (routeFrom_step hM ω z ⟨v, hv⟩).trans (ih _ hw)
      · simp only [walkVertices, dif_neg hv, List.mem_singleton] at hw
        subst w
        rfl

-- @node: walkVertices_transport_firstDefault
/-- If [the branching number is at least two](hyp:hM), [a walk under one selector assignment first selects a default child at U](hyp:hfound), and [a second assignment agrees with the first on every nondefault edge preceding a specified child edge of U in preorder](hyp:hagree), then [the walk under the second assignment, with the same start and step budget, also visits U](goal). -/
lemma walkVertices_transport_firstDefault (hM : BranchingDomain M)
    (ξ ζ : NondefaultEdge M d → Bool) (fuel : ℕ) (v : TreeVertex M d)
    (U : InternalVertex M d) (i : Fin M)
    (hfound : (walkVertices hM ξ fuel v).findSome? (defaultAtVertex hM ξ) = some U)
    (hagree : ∀ e : NondefaultEdge M d, preorderLt e.val (localEdge U i) → ζ e = ξ e) :
    U.val ∈ walkVertices hM ζ fuel v := by
  induction fuel generalizing v with
  | zero =>
      have hat : defaultAtVertex hM ξ v = some U := by
        simpa [walkVertices] using hfound
      have hvU := ((defaultAtVertex_eq_some hM ξ v U).mp hat).1
      simpa [walkVertices] using hvU.symm
  | succ fuel ih =>
      by_cases hv : v.1.val < d
      · by_cases hc : chooseChild hM ξ ⟨v, hv⟩ = defaultChild hM
        · have hat : defaultAtVertex hM ξ v = some U := by
            simpa [walkVertices, defaultAtVertex, hv, hc] using hfound
          have hvU := ((defaultAtVertex_eq_some hM ξ v U).mp hat).1
          simp only [walkVertices, dif_pos hv, List.mem_cons]
          exact Or.inl hvU.symm
        · have htail : (walkVertices hM ξ fuel
              (child ⟨v, hv⟩ (chooseChild hM ξ ⟨v, hv⟩))).findSome?
                (defaultAtVertex hM ξ) = some U := by
            simpa [walkVertices, hv, defaultAtVertex, hc] using hfound
          have hp := walkVertices_mem_prefix hM ξ fuel _ U.val
            (firstDefaultFrom_mem hM ξ fuel _ U htail).1
          obtain ⟨ha, hone⟩ := chooseChild_selected_one hM ξ ⟨v, hv⟩ hc
          have hchosen : chooseChild hM ζ ⟨v, hv⟩ = chooseChild hM ξ ⟨v, hv⟩ := by
            apply chooseChild_eq_of_first_one hM ζ ⟨v, hv⟩ _ ha
            · rw [hagree _ (preorderLt_child_of_le_prefix ⟨v, hv⟩ U _ _ i le_rfl hp)]
              exact hone
            · intro j hj
              rw [hagree _ (preorderLt_child_of_le_prefix ⟨v, hv⟩ U _ j i hj.le hp)]
              exact chooseChild_earlier_zero hM ξ ⟨v, hv⟩ j hj
          simp only [walkVertices, dif_pos hv, hchosen, List.mem_cons]
          exact Or.inr (ih _ htail)
      · have hnone : defaultAtVertex hM ξ v = none := by simp [defaultAtVertex, hv]
        simp [walkVertices, hv, hnone] at hfound

-- @node: firstDefault_earlier_zero
/-- If [the branching number is at least two](hyp:hM), [the full walk from the root under one selector assignment first selects a default child at U](hyp:hU), [a second assignment agrees on all nondefault edges preceding child edge i of U](hyp:hagree), and [j is smaller than i](hyp:hj), then [the second assignment's bit on child edge j of U is false](goal). -/
lemma firstDefault_earlier_zero (hM : BranchingDomain M)
    (ξ ζ : NondefaultEdge M d → Bool) (U : InternalVertex M d) (i : Fin M)
    (hU : (walkVertices hM ξ d (root M d)).findSome? (defaultAtVertex hM ξ) = some U)
    (hagree : ∀ e : NondefaultEdge M d, preorderLt e.val (localEdge U i) → ζ e = ξ e)
    (j : Fin M) (hj : j < i) :
    ζ (nondefaultChildEdge U j (by have := i.isLt; omega)) = false := by
  have hfound : (walkVertices hM ξ d (root M d)).findSome? (defaultAtVertex hM ξ) = some U := hU
  have hc := (firstDefaultFrom_mem hM ξ d (root M d) U hfound).2
  have hjdef : j < chooseChild hM ξ U := by
    rw [hc]
    change j.val < M - 1
    have := i.isLt
    omega
  rw [hagree _ (preorderLt_sibling U j i hj)]
  exact chooseChild_earlier_zero hM ξ U j hjdef

variable {p : ℝ}

-- @node: routeReaches
/-- Given [a branching number of at least two](hyp:hM), [a random table](hyp:ω), [a real point at which selectors are evaluated](hyp:z), and [an internal vertex](hyp:U), the [route-reaching condition](goal) means that the full selector walk from the root visits that vertex. -/
def routeReaches (hM : BranchingDomain M) (ω : Outcome q M d g r0 n0) (z : ℝ)
    (U : InternalVertex M d) : Prop :=
  U.val ∈ walkVertices hM (exposedValues ω z) d (root M d)

-- @node: rejects
/-- Given [a random table](hyp:ω), [a real point at which to evaluate it](hyp:z), and [a tree edge](hyp:e), the [rejection condition](goal) means that the edge is nondefault and its selector entry is false at the grid key for that point and the end of the edge's window. -/
def rejects (ω : Outcome q M d g r0 n0) (z : ℝ) (e : TreeEdge M d) : Prop :=
  ∃ he : (childIndex e).val + 1 < M,
    selectorEntry ω ⟨e, he⟩ (gridKeyFin q (windowEnd q M d g r0 n0 e) z) = false

-- @node: lem:routing
/-- Assume [the geometric ratio lies strictly between zero and one](hyp:hq), [the branching number is at least two](hyp:hM), [the tree depth is positive](hyp:hd), [the gap is positive](hyp:hg), [the base length is positive](hyp:hr), and [the terminal probability lies strictly between zero and one](hyp:hp). If [x is a stable center](hyp:hx), [the selector assignment has a default along its root route at x](hyp:hξ), and [U is its first default vertex](hyp:hU), then [for every random table realizing that assignment at x, every nondefault child of U, every scale in that child's window, and every dilation between one and two, the translated local point's route visits U and rejects all earlier children, and passing the local test puts that point in the random set](goal). -/
lemma localTest_imp_mem_randomSet (hq : QDomain q) (hM : BranchingDomain M)
    (hd : DepthDomain d) (hg : GapDomain g) (hr : BaseLengthDomain r0)
    (hp : TerminalProbabilityDomain p) (x : ℝ) (hx : StableCenterCondition q M d g r0 n0 x)
    (ξ : NondefaultEdge M d → Bool) (hξ : RoutingDefaultAtom q M d g r0 hM x ξ)
    (U : InternalVertex M d) (hU : firstDefault q M d g r0 hM x ξ = some U) :
    ∀ ω : Outcome q M d g r0 n0, atomEvent q M d g r0 n0 x ξ ω →
      ∀ (i : Fin M) (hi : i.val + 1 < M), ∀ n ∈ windowSet q M d g r0 n0 (localEdge U i),
      ∀ t ∈ Set.Icc (1 : ℝ) 2,
        (routeReaches hM ω (localPoint x t q n) U ∧
          ∀ j : Fin M, j < i → rejects ω (localPoint x t q n) (localEdge U j)) ∧
        (localTest hM ω U i hi (localPoint x t q n) = true →
          localPoint x t q n ∈ randomSet hM ω) := by
  intro ω hω i hi n hn t ht
  have hagree (e : NondefaultEdge M d) (he : preorderLt e.val (localEdge U i)) :
      exposedValues ω (localPoint x t q n) e = ξ e := by
    have hkey : gridKeyFin q (windowEnd q M d g r0 n0 e.val) (localPoint x t q n) =
        gridKeyFin q (windowEnd q M d g r0 n0 e.val) x := by
      apply Fin.ext
      exact stableCenter_preceding_keys q g r0 hq hr hx.2.1 x ⟨hx⟩
        (localEdge U i) n hn t ht e.val he
    unfold exposedValues exposedAddr
    rw [hkey]
    exact hω e
  have hfound : (walkVertices hM ξ d (root M d)).findSome? (defaultAtVertex hM ξ) =
      some U := hU
  have hreach := walkVertices_transport_firstDefault hM ξ
    (exposedValues ω (localPoint x t q n)) d (root M d) U i hfound hagree
  have hzero (j : Fin M) (hj : j < i) :
      exposedValues ω (localPoint x t q n)
        (nondefaultChildEdge U j (by omega)) = false :=
    firstDefault_earlier_zero hM ξ (exposedValues ω (localPoint x t q n)) U i hU hagree j hj
  refine ⟨⟨hreach, ?_⟩, ?_⟩
  · intro j hj
    have hjM : j.val + 1 < M := by omega
    refine ⟨nondefaultChildEdge_property U j hjM, ?_⟩
    exact hzero j hj
  · intro htest
    obtain ⟨hone, hterminal⟩ := Bool.and_eq_true_iff.mp htest
    have hchosen : chooseChild hM (exposedValues ω (localPoint x t q n)) U = i :=
      chooseChild_eq_of_first_one hM _ U i hi hone hzero
    have hleaf : route hM ω (localPoint x t q n) =
        localLeaf hM ω U i (localPoint x t q n) := by
      change routeFrom hM ω (localPoint x t q n) (root M d) =
        routeFrom hM ω (localPoint x t q n) (child U i)
      calc
        _ = routeFrom hM ω (localPoint x t q n) U.val :=
          routeFrom_eq_of_mem_walkVertices hM ω (localPoint x t q n) d _ _ hreach
        _ = routeFrom hM ω (localPoint x t q n)
            (child U (chooseChild hM (exposedValues ω (localPoint x t q n)) U)) :=
          routeFrom_step hM ω (localPoint x t q n) U
        _ = _ := by rw [hchosen]
    change terminalEntry ω (route hM ω (localPoint x t q n)) _ = true
    exact (congrArg (fun L : Leaf M d => terminalEntry ω L
      (gridKeyFin q (leafEndpoint q M d g r0 n0 L) (localPoint x t q n))) hleaf).trans hterminal

end Papers.OaiGeometricErdosSimilarity

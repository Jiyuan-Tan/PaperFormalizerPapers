module

public import Papers.OaiCapacityCriterionState.Helpers.BroadcastPosterior
public import Papers.OaiCapacityCriterionState.Helpers.FiniteExperiments
public import Mathlib.Logic.Equiv.Prod

/-! # Rooted subtrees and branch decompositions

Removing the suffix naming a vertex gives its rooted descendant tree. Levels
and nonroot balls split into the disjoint branches at the root. These finite
equivalences provide the observation and configuration spaces for factoring
the broadcast experiment over its child subtrees.
-/

@[expose] public section

open scoped BigOperators

namespace OaiCapacityCriterionState

variable {B : ℕ}

-- @node: BoundedTree.subtree
/-- For [a tree with bounded branching](hyp:T) and [a vertex address](hyp:v)
[belonging to that tree](hyp:hv), the [descendant tree rooted at that vertex](goal)
has [the addresses whose concatenation with the vertex address belongs to the original tree](step:1),
[the empty address as its root](step:2), and [closure under taking parents](step:3). -/
def BoundedTree.subtree (T : BoundedTree B) (v : List (Fin B))
    (hv : v ∈ T.verts) : BoundedTree B where
  verts := {u | u ++ v ∈ T.verts}
  nil_mem := by simpa using hv
  prefix_closed := by
    intro a u hu
    exact T.prefix_closed a (u ++ v) hu

-- @node: BoundedTree.subtree_root
/-- For [a tree with bounded branching](hyp:T), [the descendant tree at its root
is the original tree](goal). -/
lemma BoundedTree.subtree_root (T : BoundedTree B) :
    T.subtree [] T.nil_mem = T := by
  cases T
  simp [BoundedTree.subtree]

-- @node: BoundedTree.subtree_subtree
/-- In [a tree with bounded branching](hyp:T), take [an address](hyp:v)
[belonging to the tree](hyp:hv), and [a further address](hyp:u)
[belonging to its descendant tree](hyp:hu). Then [taking these two descendant
trees successively equals taking the descendant tree at their concatenated address](goal). -/
lemma BoundedTree.subtree_subtree (T : BoundedTree B) (v : List (Fin B))
    (hv : v ∈ T.verts) (u : List (Fin B)) (hu : u ∈ (T.subtree v hv).verts) :
    (T.subtree v hv).subtree u hu = T.subtree (u ++ v) hu := by
  unfold BoundedTree.subtree
  congr 1
  ext w
  simp only [Set.mem_ofPred_eq, List.append_assoc]

-- @node: BoundedTree.subtree_mem_level
/-- In [a tree with bounded branching](hyp:T), fix [an address](hyp:v)
[belonging to the tree](hyp:hv), [a relative address](hyp:u), and [a depth](hyp:n).
Then [the relative address lies at that depth in the descendant tree exactly when
its concatenation with the root address lies at that depth plus the root address's length
in the original tree](goal). -/
lemma BoundedTree.subtree_mem_level (T : BoundedTree B) (v : List (Fin B))
    (hv : v ∈ T.verts) (u : List (Fin B)) (n : ℕ) :
    u ∈ (T.subtree v hv).level n ↔ u ++ v ∈ T.level (n + v.length) := by
  simp only [BoundedTree.mem_level_iff, BoundedTree.subtree, Set.mem_ofPred_eq,
    List.length_append, Nat.add_right_cancel_iff]

-- @node: BoundedTree.subtree_mem_ball
/-- In [a tree with bounded branching](hyp:T), fix [an address](hyp:v)
[belonging to the tree](hyp:hv), [a relative address](hyp:u), and [a radius](hyp:n).
Then [the relative address lies in the descendant tree's ball of that radius exactly
when its concatenation with the root address lies in the original tree's ball of
radius increased by the root address's length](goal). -/
lemma BoundedTree.subtree_mem_ball (T : BoundedTree B) (v : List (Fin B))
    (hv : v ∈ T.verts) (u : List (Fin B)) (n : ℕ) :
    u ∈ (T.subtree v hv).ball n ↔ u ++ v ∈ T.ball (n + v.length) := by
  simp only [BoundedTree.mem_ball_iff, BoundedTree.subtree, Set.mem_ofPred_eq,
    List.length_append, Nat.add_le_add_iff_right]

-- @node: BoundedTree.subtree_children
/-- In [a tree with bounded branching](hyp:T), fix [an address](hyp:v)
[belonging to the tree](hyp:hv) and [a relative address](hyp:u).
Then [appending the root address to each child of the relative address in the
descendant tree gives exactly the children of the concatenated address in the original tree](goal). -/
lemma BoundedTree.subtree_children (T : BoundedTree B) (v : List (Fin B))
    (hv : v ∈ T.verts) (u : List (Fin B)) :
    ((T.subtree v hv).children u).image (fun w => w ++ v) = T.children (u ++ v) := by
  classical
  simp only [BoundedTree.children, BoundedTree.subtree, Set.mem_ofPred_eq,
    List.cons_append, Finset.image_image, Function.comp_def]
  rfl

open Classical in
-- @node: BoundedTree.rootChildren
/-- For [a tree with bounded branching](hyp:T), the [set of root-child labels](goal)
consists of the labels whose one-entry addresses belong to the tree. -/
noncomputable def BoundedTree.rootChildren (T : BoundedTree B) : Finset (Fin B) :=
  Finset.univ.filter (fun a => [a] ∈ T.verts)

-- @node: BoundedTree.rootChild_mem
/-- For [a tree with bounded branching](hyp:T) and [a root-child label](hyp:a),
[the corresponding one-entry address belongs to the tree](goal). -/
lemma BoundedTree.rootChild_mem (T : BoundedTree B) (a : T.rootChildren) :
    [a.val] ∈ T.verts := by
  classical
  exact (Finset.mem_filter.mp (show a.val ∈ Finset.univ.filter
    (fun b : Fin B => [b] ∈ T.verts) from a.property)).2

-- @node: BoundedTree.rootLevelMap
/-- For [a tree with bounded branching](hyp:T), [a depth](hyp:n), and
[a root-child label paired with a vertex at that depth in its descendant tree](hyp:x),
the [level-embedding map](goal) appends the child label to the relative address,
giving a vertex one level deeper in the original tree. -/
def BoundedTree.rootLevelMap (T : BoundedTree B) (n : ℕ)
    (x : Σ a : T.rootChildren, (T.subtree [a.val] (T.rootChild_mem a)).level n) :
    T.level (n + 1) :=
  ⟨x.2.val ++ [x.1.val], (T.subtree_mem_level _ _ _ n).mp x.2.property⟩

-- @node: BoundedTree.rootLevelMap_bijective
/-- For [a tree with bounded branching](hyp:T) and [a depth](hyp:n),
[appending each root-child label to a vertex at that depth in its descendant tree
is a bijection onto the next level of the original tree](goal). -/
lemma BoundedTree.rootLevelMap_bijective (T : BoundedTree B) (n : ℕ) :
    Function.Bijective (T.rootLevelMap n) := by
  classical
  constructor
  · intro x y h
    have heq := congrArg Subtype.val h
    change x.2.val ++ [x.1.val] = y.2.val ++ [y.1.val] at heq
    have hlen : x.2.val.length = y.2.val.length :=
      ((T.subtree _ _).mem_level_iff _ n |>.mp x.2.property).2.trans
        ((T.subtree _ _).mem_level_iff _ n |>.mp y.2.property).2.symm
    have hparts := List.append_inj heq hlen
    have ha : x.1 = y.1 := Subtype.ext (List.singleton_inj.mp hparts.2)
    cases x with
    | mk a u =>
      cases y with
      | mk b w =>
        dsimp at ha
        subst b
        exact congrArg (Sigma.mk a) (Subtype.ext hparts.1)
  · intro w
    obtain ⟨hw, hlen⟩ := (T.mem_level_iff w.val (n + 1)).mp w.property
    rcases List.eq_nil_or_concat' w.val with heq | ⟨u, a, heq⟩
    · simp [heq] at hlen
    · have ha : [a] ∈ T.verts := T.mem_of_append_mem u [a] (heq ▸ hw)
      let a' : T.rootChildren := ⟨a, by
        change a ∈ Finset.univ.filter (fun b : Fin B => [b] ∈ T.verts)
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩⟩
      have hu : u ∈ (T.subtree [a] ha).level n := by
        apply (T.subtree_mem_level [a] ha u n).mpr
        simpa only [heq, List.length_singleton] using w.property
      exact ⟨⟨a', ⟨u, hu⟩⟩, Subtype.ext heq.symm⟩

-- @node: BoundedTree.rootLevelEquiv
/-- For [a tree with bounded branching](hyp:T) and [a depth](hyp:n), the
[level correspondence](goal) identifies root-child labels paired with vertices
at that depth in their descendant trees with vertices at the next level of the original tree,
by appending the child label to the relative address. -/
noncomputable def BoundedTree.rootLevelEquiv (T : BoundedTree B) (n : ℕ) :
    (Σ a : T.rootChildren, (T.subtree [a.val] (T.rootChild_mem a)).level n) ≃
      T.level (n + 1) :=
  Equiv.ofBijective (T.rootLevelMap n) (T.rootLevelMap_bijective n)

-- @node: BoundedTree.rootBallMap
/-- For [a tree with bounded branching](hyp:T), [a radius](hyp:n), and
[a root-child label paired with a vertex in its descendant tree's ball of that radius](hyp:x),
the [ball-embedding map](goal) appends the child label to the relative address,
giving a nonroot vertex in the original tree's ball of radius one greater. -/
def BoundedTree.rootBallMap (T : BoundedTree B) (n : ℕ)
    (x : Σ a : T.rootChildren, (T.subtree [a.val] (T.rootChild_mem a)).ball n) :
    (T.ball (n + 1)).erase [] := by
  classical
  refine ⟨x.2.val ++ [x.1.val], Finset.mem_erase.mpr ⟨?_, ?_⟩⟩
  · simp
  · exact (T.subtree_mem_ball _ _ _ n).mp x.2.property

-- @node: BoundedTree.rootBallMap_bijective
/-- For [a tree with bounded branching](hyp:T) and [a radius](hyp:n),
[appending each root-child label to a vertex in its descendant tree's ball is a
bijection onto the original tree's ball of radius one greater with the root removed](goal). -/
lemma BoundedTree.rootBallMap_bijective (T : BoundedTree B) (n : ℕ) :
    Function.Bijective (T.rootBallMap n) := by
  classical
  constructor
  · intro x y h
    have heq := congrArg Subtype.val h
    change x.2.val ++ [x.1.val] = y.2.val ++ [y.1.val] at heq
    have hparts := List.append_inj' heq (by simp)
    have ha : x.1 = y.1 := Subtype.ext (List.singleton_inj.mp hparts.2)
    cases x with
    | mk a u =>
      cases y with
      | mk b w =>
        dsimp at ha
        subst b
        exact congrArg (Sigma.mk a) (Subtype.ext hparts.1)
  · intro w
    obtain ⟨hne, hw⟩ := Finset.mem_erase.mp w.property
    rcases List.eq_nil_or_concat' w.val with heq | ⟨u, a, heq⟩
    · exact (hne heq).elim
    · have ha : [a] ∈ T.verts :=
        T.mem_of_append_mem u [a] (heq ▸ (T.mem_ball_iff _ _ |>.mp hw).1)
      let a' : T.rootChildren := ⟨a, by
        change a ∈ Finset.univ.filter (fun b : Fin B => [b] ∈ T.verts)
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩⟩
      have hu : u ∈ (T.subtree [a] ha).ball n := by
        apply (T.subtree_mem_ball [a] ha u n).mpr
        simpa only [heq, List.length_singleton] using hw
      exact ⟨⟨a', ⟨u, hu⟩⟩, Subtype.ext heq.symm⟩

-- @node: BoundedTree.rootBallEquiv
/-- For [a tree with bounded branching](hyp:T) and [a radius](hyp:n), the
[nonroot-ball correspondence](goal) identifies root-child labels paired with
vertices in their descendant trees' balls of that radius with the original tree's
ball of radius one greater excluding the root, by appending each child label. -/
noncomputable def BoundedTree.rootBallEquiv (T : BoundedTree B) (n : ℕ) :
    (Σ a : T.rootChildren, (T.subtree [a.val] (T.rootChild_mem a)).ball n) ≃
      (T.ball (n + 1)).erase [] :=
  Equiv.ofBijective (T.rootBallMap n) (T.rootBallMap_bijective n)

-- @node: BoundedTree.rootBallSplit
/-- For [a tree with bounded branching](hyp:T) and [a radius](hyp:n), the
[root-and-branches correspondence](goal) identifies a distinguished root together
with the separate child-subtree balls of that radius with the original tree's ball
of radius one greater. It [sends the distinguished point to the root](step:1)
and [sends a branch vertex to its relative address followed by its child label](step:2). -/
noncomputable def BoundedTree.rootBallSplit (T : BoundedTree B) (n : ℕ) :
    (Unit ⊕ Σ a : T.rootChildren, (T.subtree [a.val] (T.rootChild_mem a)).ball n) ≃
      T.ball (n + 1) := by
  classical
  let f : (Unit ⊕ Σ a : T.rootChildren,
      (T.subtree [a.val] (T.rootChild_mem a)).ball n) → T.ball (n + 1) :=
    fun x => match x with
    | .inl _ => ⟨[], (T.mem_ball_iff _ _).mpr ⟨T.nil_mem, Nat.zero_le _⟩⟩
    | .inr x => ⟨(T.rootBallMap n x).val,
        Finset.mem_of_mem_erase (T.rootBallMap n x).property⟩
  apply Equiv.ofBijective f
  constructor
  · intro x y h
    cases x with
    | inl x =>
      cases y with
      | inl y => rfl
      | inr y =>
        exact (Finset.ne_of_mem_erase (T.rootBallMap n y).property
          (congrArg Subtype.val h).symm).elim
    | inr x =>
      cases y with
      | inl y =>
        exact (Finset.ne_of_mem_erase (T.rootBallMap n x).property
          (congrArg Subtype.val h)).elim
      | inr y =>
        exact congrArg Sum.inr ((T.rootBallMap_bijective n).1
          (Subtype.ext (congrArg (fun z : T.ball (n + 1) => z.val) h)))
  · intro w
    by_cases hroot : w.val = []
    · exact ⟨.inl (), Subtype.ext hroot.symm⟩
    · obtain ⟨x, hx⟩ := (T.rootBallMap_bijective n).2
        ⟨w.val, Finset.mem_erase.mpr ⟨hroot, w.property⟩⟩
      exact ⟨.inr x, Subtype.ext (congrArg (fun z : (T.ball (n + 1)).erase [] => z.val) hx)⟩

-- @node: BoundedTree.rootConfigEquiv
/-- For [a tree with bounded branching](hyp:T) and [a radius](hyp:n), the
[configuration correspondence](goal) bijectively decomposes a four-state assignment
on the ball of radius one greater into its root state and one assignment on each
child-subtree ball of the given radius. -/
noncomputable def BoundedTree.rootConfigEquiv (T : BoundedTree B) (n : ℕ) :
    (T.ball (n + 1) → Fin 4) ≃
      (Fin 4 × ∀ a : T.rootChildren,
        (T.subtree [a.val] (T.rootChild_mem a)).ball n → Fin 4) :=
  (Equiv.arrowCongr (T.rootBallSplit n).symm (Equiv.refl (Fin 4))).trans
    ((Equiv.sumArrowEquivProdArrow _ _ _).trans
      (Equiv.prodCongr (Equiv.piUnique (fun _ : Unit => Fin 4))
        (Equiv.piCurry (fun _ _ => Fin 4))))

-- @node: BoundedTree.rootConfigEquiv_root
/-- For [a tree with bounded branching](hyp:T), [a radius](hyp:n), and
[a four-state configuration on the ball of radius one greater](hyp:c),
[the root component of its decomposition equals its state at the root](goal). -/
lemma BoundedTree.rootConfigEquiv_root (T : BoundedTree B) (n : ℕ)
    (c : T.ball (n + 1) → Fin 4) :
    (T.rootConfigEquiv n c).1 = configSpin T (n + 1) c [] := by
  classical
  have hroot : [] ∈ T.ball (n + 1) := (T.mem_ball_iff _ _).mpr ⟨T.nil_mem, Nat.zero_le _⟩
  simp only [configSpin, dif_pos hroot]
  rfl

-- @node: BoundedTree.rootConfigEquiv_branch
/-- For [a tree with bounded branching](hyp:T), [a radius](hyp:n),
[a configuration on the ball of radius one greater](hyp:c), [a root child](hyp:a),
and [a vertex in that child's descendant ball of the given radius](hyp:u),
[the decomposed branch configuration at that vertex equals the original configuration
at its relative address followed by the child label](goal). -/
lemma BoundedTree.rootConfigEquiv_branch (T : BoundedTree B) (n : ℕ)
    (c : T.ball (n + 1) → Fin 4) (a : T.rootChildren)
    (u : (T.subtree [a.val] (T.rootChild_mem a)).ball n) :
    (T.rootConfigEquiv n c).2 a u = configSpin T (n + 1) c (u.val ++ [a.val]) := by
  classical
  have hu : u.val ++ [a.val] ∈ T.ball (n + 1) := by
    simpa only [List.length_singleton] using (T.subtree_mem_ball _ _ _ n).mp u.property
  simp only [configSpin, dif_pos hu]
  rfl

-- @node: configSpin_root_branch
/-- For [a tree with bounded branching](hyp:T), [a radius](hyp:n),
[a configuration on the ball of radius one greater](hyp:c), [a root child](hyp:a),
and [a relative address](hyp:u) [in that child's descendant ball](hyp:hu),
[evaluating the branch configuration at the relative address gives the same state
as evaluating the original configuration at the address followed by the child label](goal). -/
lemma configSpin_root_branch (T : BoundedTree B) (n : ℕ)
    (c : T.ball (n + 1) → Fin 4) (a : T.rootChildren)
    (u : List (Fin B)) (hu : u ∈ (T.subtree [a.val] (T.rootChild_mem a)).ball n) :
    configSpin (T.subtree [a.val] (T.rootChild_mem a)) n
      ((T.rootConfigEquiv n c).2 a) u = configSpin T (n + 1) c (u ++ [a.val]) := by
  classical
  rw [configSpin, dif_pos hu]
  exact T.rootConfigEquiv_branch n c a ⟨u, hu⟩

-- @node: broadcastJoint_root_branches
/-- For [a tree with bounded branching](hyp:T), [a channel parameter](hyp:lam),
[a depth](hyp:n), and [a configuration through depth one greater](hyp:c),
[its joint broadcast weight equals one quarter times the product over root children
of the root-to-child transition weight multiplied by four times the branch's joint
broadcast weight through the given depth](goal). -/
lemma broadcastJoint_root_branches (T : BoundedTree B) (lam : ℝ) (n : ℕ)
    (c : T.ball (n + 1) → Fin 4) :
    broadcastJoint T lam (n + 1) c =
      (1 / 4) * ∏ a : T.rootChildren,
        (channel lam (T.rootConfigEquiv n c).1
          (configSpin (T.subtree [a.val] (T.rootChild_mem a)) n
            ((T.rootConfigEquiv n c).2 a) []) *
          (4 * broadcastJoint (T.subtree [a.val] (T.rootChild_mem a)) lam n
            ((T.rootConfigEquiv n c).2 a))) := by
  classical
  unfold broadcastJoint
  congr 1
  rw [← Finset.prod_coe_sort, ← (T.rootBallEquiv n).prod_comp, Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro a _
  let S := T.subtree [a.val] (T.rootChild_mem a)
  let d := (T.rootConfigEquiv n c).2 a
  have hroot : [] ∈ S.ball n := (S.mem_ball_iff _ _).mpr ⟨S.nil_mem, Nat.zero_le _⟩
  let f : List (Fin B) → ℝ := fun u =>
    channel lam (configSpin T (n + 1) c (u ++ [a.val]).tail)
      (configSpin T (n + 1) c (u ++ [a.val]))
  change (∏ u : S.ball n, f u.val) = _
  rw [Finset.prod_coe_sort, ← Finset.mul_prod_erase _ _ hroot]
  have hfroot : f [] = channel lam (T.rootConfigEquiv n c).1
      (configSpin S n d []) := by
    dsimp [f]
    rw [T.rootConfigEquiv_root, configSpin_root_branch T n c a [] hroot]
    rfl
  rw [hfroot]
  congr 1
  have hprod : (∏ u ∈ (S.ball n).erase [], f u) =
      ∏ u ∈ (S.ball n).erase [],
        channel lam (configSpin S n d u.tail) (configSpin S n d u) := by
    apply Finset.prod_congr rfl
    intro u hu
    obtain ⟨hne, hum⟩ := Finset.mem_erase.mp hu
    have hp : u.tail ∈ S.ball n := by
      obtain ⟨huT, hlen⟩ := (S.mem_ball_iff _ _).mp hum
      cases u with
      | nil => exact (hne rfl).elim
      | cons b u =>
          exact (S.mem_ball_iff _ _).mpr
            ⟨S.prefix_closed b u huT, by simpa using Nat.le_of_succ_le hlen⟩
    dsimp [f]
    rw [configSpin_root_branch T n c a u hum,
      configSpin_root_branch T n c a u.tail hp]
    cases u with
    | nil => exact (hne rfl).elim
    | cons b u => rfl
  rw [hprod]
  ring

-- @node: BoundedTree.rootObservationEquiv
/-- For [a tree with bounded branching](hyp:T) and [a depth](hyp:n), the
[observation correspondence](goal) bijectively decomposes a four-state observation
at the next level into one observation at the given level in each child subtree. -/
noncomputable def BoundedTree.rootObservationEquiv (T : BoundedTree B) (n : ℕ) :
    (T.level (n + 1) → Fin 4) ≃
      (∀ a : T.rootChildren,
        (T.subtree [a.val] (T.rootChild_mem a)).level n → Fin 4) :=
  (Equiv.arrowCongr (T.rootLevelEquiv n).symm (Equiv.refl (Fin 4))).trans
    (Equiv.piCurry (fun _ _ => Fin 4))

-- @node: BoundedTree.rootObservationEquiv_apply
/-- For [a tree with bounded branching](hyp:T), [a depth](hyp:n),
[an observation at the next level](hyp:obs), [a root child](hyp:a), and
[a vertex at the given level in that child's subtree](hyp:u),
[the decomposed observation at that vertex equals the original observation at the
vertex obtained by appending the child label](goal). -/
lemma BoundedTree.rootObservationEquiv_apply (T : BoundedTree B) (n : ℕ)
    (obs : T.level (n + 1) → Fin 4) (a : T.rootChildren)
    (u : (T.subtree [a.val] (T.rootChild_mem a)).level n) :
    T.rootObservationEquiv n obs a u = obs (T.rootLevelEquiv n ⟨a, u⟩) := rfl

-- @node: root_observation_constraint
/-- For [a tree with bounded branching](hyp:T), [a depth](hyp:n),
[a configuration through the next level](hyp:c), and [an observation at that level](hyp:obs),
[the configuration matches the observation everywhere on that level if and only if
every decomposed branch configuration matches its decomposed branch observation](goal). -/
lemma root_observation_constraint (T : BoundedTree B) (n : ℕ)
    (c : T.ball (n + 1) → Fin 4) (obs : T.level (n + 1) → Fin 4) :
    (∀ w : T.level (n + 1), configSpin T (n + 1) c w.val = obs w) ↔
      ∀ a : T.rootChildren, ∀ u : (T.subtree [a.val] (T.rootChild_mem a)).level n,
        configSpin (T.subtree [a.val] (T.rootChild_mem a)) n
          ((T.rootConfigEquiv n c).2 a) u.val = T.rootObservationEquiv n obs a u := by
  constructor
  · intro h a u
    have hu : u.val ∈ (T.subtree [a.val] (T.rootChild_mem a)).ball n :=
      ((T.subtree _ _).mem_ball_iff _ _).mpr
        ⟨((T.subtree _ _).mem_level_iff _ _ |>.mp u.property).1,
          ((T.subtree _ _).mem_level_iff _ _ |>.mp u.property).2.le⟩
    rw [configSpin_root_branch T n c a u.val hu]
    exact h (T.rootLevelEquiv n ⟨a, u⟩)
  · intro h w
    obtain ⟨⟨a, u⟩, rfl⟩ := (T.rootLevelEquiv n).surjective w
    have hu : u.val ∈ (T.subtree [a.val] (T.rootChild_mem a)).ball n :=
      ((T.subtree _ _).mem_ball_iff _ _).mpr
        ⟨((T.subtree _ _).mem_level_iff _ _ |>.mp u.property).1,
          ((T.subtree _ _).mem_level_iff _ _ |>.mp u.property).2.le⟩
    have hh := h a u
    rw [configSpin_root_branch T n c a u.val hu] at hh
    exact hh

-- @node: channel_broadcastLikelihood_config_sum
/-- For [a tree with bounded branching](hyp:T), [a channel parameter](hyp:lam),
[a depth](hyp:n), [an input state](hyp:i), and [an observation at that depth](hyp:obs),
[the channel-composed broadcast likelihood equals the sum over configurations matching
the observation of the transition weight from the input state to the configuration's
root state multiplied by four times its joint broadcast weight](goal). -/
lemma channel_broadcastLikelihood_config_sum (T : BoundedTree B) (lam : ℝ) (n : ℕ)
    (i : Fin 4) (obs : T.level n → Fin 4) :
    channelLikelihood lam (broadcastLikelihood T lam n) i obs =
      ∑ c : T.ball n → Fin 4,
        if ∀ v : T.level n, configSpin T n c v.val = obs v then
          channel lam i (configSpin T n c []) * (4 * broadcastJoint T lam n c) else 0 := by
  classical
  unfold channelLikelihood broadcastLikelihood levelJoint
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  simp only [ite_and, mul_ite, mul_zero]
  simp

-- @node: broadcastLikelihood_root_branches
/-- For [a tree with bounded branching](hyp:T), [a channel parameter](hyp:lam),
[a depth](hyp:n), [a root state](hyp:i), and [an observation at the next level](hyp:obs),
[the broadcast likelihood conditional on that root state equals the product of the
channel-composed child-subtree likelihoods of the decomposed observations at the given depth](goal). -/
lemma broadcastLikelihood_root_branches (T : BoundedTree B) (lam : ℝ) (n : ℕ)
    (i : Fin 4) (obs : T.level (n + 1) → Fin 4) :
    broadcastLikelihood T lam (n + 1) i obs =
      ∏ a : T.rootChildren,
        channelLikelihood lam
          (broadcastLikelihood (T.subtree [a.val] (T.rootChild_mem a)) lam n) i
          (T.rootObservationEquiv n obs a) := by
  classical
  have hconfig (c : T.ball (n + 1) → Fin 4) :
      (if configSpin T (n + 1) c [] = i ∧
          (∀ v : T.level (n + 1), configSpin T (n + 1) c v.val = obs v) then
        broadcastJoint T lam (n + 1) c else 0) =
      (if (T.rootConfigEquiv n c).1 = i then
        (1 / 4) * ∏ a : T.rootChildren,
          (if ∀ u : (T.subtree [a.val] (T.rootChild_mem a)).level n,
              configSpin (T.subtree [a.val] (T.rootChild_mem a)) n
                ((T.rootConfigEquiv n c).2 a) u.val = T.rootObservationEquiv n obs a u then
            channel lam (T.rootConfigEquiv n c).1
              (configSpin (T.subtree [a.val] (T.rootChild_mem a)) n
                ((T.rootConfigEquiv n c).2 a) []) *
              (4 * broadcastJoint (T.subtree [a.val] (T.rootChild_mem a)) lam n
                ((T.rootConfigEquiv n c).2 a)) else 0) else 0) := by
    simp only [← T.rootConfigEquiv_root, root_observation_constraint, broadcastJoint_root_branches]
    rw [ite_and]
    by_cases hi : (T.rootConfigEquiv n c).1 = i
    · simp only [if_pos hi]
      rw [Finset.prod_ite_zero]
      simp only [Finset.mem_univ, forall_true_left]
      split_ifs <;> simp
    · simp only [if_neg hi]
  unfold broadcastLikelihood levelJoint
  simp_rw [hconfig]
  rw [← (T.rootConfigEquiv n).symm.sum_comp, Fintype.sum_prod_type]
  simp only [Equiv.apply_symm_apply]
  simp_rw [Finset.sum_ite_irrel]
  simp only [Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp_rw [← Finset.mul_sum]
  rw [← mul_assoc, show (4 : ℝ) * (1 / 4) = 1 by norm_num, one_mul]
  rw [← Fintype.prod_sum (fun (a : T.rootChildren)
    (d : (T.subtree [a.val] (T.rootChild_mem a)).ball n → Fin 4) =>
      if ∀ u : (T.subtree [a.val] (T.rootChild_mem a)).level n,
        configSpin (T.subtree [a.val] (T.rootChild_mem a)) n d u.val =
          T.rootObservationEquiv n obs a u then
        channel lam i (configSpin (T.subtree [a.val] (T.rootChild_mem a)) n d []) *
          (4 * broadcastJoint (T.subtree [a.val] (T.rootChild_mem a)) lam n d) else 0)]
  apply Finset.prod_congr rfl
  intro a _
  exact (channel_broadcastLikelihood_config_sum _ lam n i _).symm

-- @node: broadcastPosteriorLaw_root_branches
/-- For [a tree with bounded branching](hyp:T), [a channel parameter](hyp:lam),
and [a depth](hyp:n), [the posterior law from observing the next level equals the
posterior law of the experiment whose likelihood, conditional on each root state,
is the product of the channel-composed child-subtree likelihoods at the given depth](goal). -/
lemma broadcastPosteriorLaw_root_branches (T : BoundedTree B) (lam : ℝ) (n : ℕ) :
    broadcastPosteriorLaw T lam (n + 1) =
      experimentLaw (fun i (obs : ∀ a : T.rootChildren,
          (T.subtree [a.val] (T.rootChild_mem a)).level n → Fin 4) =>
        ∏ a : T.rootChildren,
          channelLikelihood lam
            (broadcastLikelihood (T.subtree [a.val] (T.rootChild_mem a)) lam n) i (obs a)) := by
  classical
  rw [broadcastPosteriorLaw, ← experimentLaw_reindex (T.rootObservationEquiv n)]
  congr 1
  funext i obs
  exact broadcastLikelihood_root_branches T lam n i obs

end OaiCapacityCriterionState

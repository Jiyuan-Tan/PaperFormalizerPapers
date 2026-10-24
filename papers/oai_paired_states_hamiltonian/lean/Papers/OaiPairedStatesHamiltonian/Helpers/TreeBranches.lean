module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! Branches of a finite tree after removing one vertex. -/

public section

namespace OaiPairedStatesHamiltonian

-- @node: walk_avoiding_vertex_relation
/-- Given [a walk between two vertices](hyp:p) that [never visits a specified vertex](hyp:hk),
[its endpoints are related by a possibly empty sequence of adjacent steps whose endpoints all
avoid that vertex](goal). -/
lemma walk_avoiding_vertex_relation {V : Type} {G : SimpleGraph V} {k u v : V}
    (p : G.Walk u v) (hk : k ∉ p.support) :
    Relation.ReflTransGen (fun x y => x ≠ k ∧ y ≠ k ∧ G.Adj x y) u v := by
  induction p with
  | nil => exact .refl
  | @cons u w v h p ih =>
    have hu : u ≠ k := by
      intro he
      apply hk
      simpa only [he] using (p.cons h).start_mem_support
    have ht : k ∉ p.support := by
      intro hm
      exact hk (by simp only [SimpleGraph.Walk.support_cons, List.mem_cons]; exact Or.inr hm)
    exact (Relation.ReflTransGen.single ⟨hu,
      fun he => ht (he ▸ p.start_mem_support), h⟩).trans (ih ht)

-- @node: relation_avoiding_vertex_walk
/-- If [the starting vertex differs from a specified excluded vertex](hyp:hu) and [the endpoints
are joined by a possibly empty sequence of adjacent steps avoiding that vertex](hyp:h), then
[there is a walk between the endpoints that never visits the excluded vertex](goal). -/
lemma relation_avoiding_vertex_walk {V : Type} {G : SimpleGraph V} {k u v : V}
    (hu : u ≠ k)
    (h : Relation.ReflTransGen (fun x y => x ≠ k ∧ y ≠ k ∧ G.Adj x y) u v) :
    ∃ p : G.Walk u v, k ∉ p.support := by
  induction h with
  | refl => exact ⟨.nil, by simpa using Ne.symm hu⟩
  | @tail w v h hstep ih =>
    obtain ⟨p, hp⟩ := ih
    refine ⟨p.concat hstep.2.2, ?_⟩
    simpa only [SimpleGraph.Walk.support_concat, List.mem_append,
      List.mem_singleton, not_or] using And.intro hp (Ne.symm hstep.2.1)

-- @node: tree_branch_neighbor_unique
/-- In [an acyclic graph](hyp:hG), if [one vertex is adjacent to a specified vertex](hyp:ha),
[another vertex is also adjacent to it](hyp:hb), and [the two neighbors are connected by steps
that avoid the specified vertex](hyp:h), then [the two neighbors are equal](goal). -/
lemma tree_branch_neighbor_unique {V : Type} {G : SimpleGraph V} (hG : G.IsAcyclic)
    {k a b : V} (ha : G.Adj k a) (hb : G.Adj k b)
    (h : Relation.ReflTransGen (fun x y => x ≠ k ∧ y ≠ k ∧ G.Adj x y) a b) : a = b := by
  classical
  obtain ⟨p, hp⟩ := relation_avoiding_vertex_walk ha.ne.symm h
  have hq : k ∉ (p.toPath : G.Walk a b).support :=
    fun hm => hp (p.support_toPath_subset_support hm)
  have hpath := p.toPath.property.cons (h := ha) hq
  have he := hG.eq_snd_of_adj_start hpath hb
    (p.toPath.val.cons ha).end_mem_support
  simpa using he.symm

-- @node: tree_branch_existsUnique
/-- In [a tree](hyp:hG), for [a target vertex different from a specified vertex](hyp:hv),
[there is exactly one neighbor of the specified vertex that can reach the target by a possibly
empty sequence of adjacent steps avoiding the specified vertex](goal). -/
lemma tree_branch_existsUnique {V : Type} {G : SimpleGraph V} (hG : G.IsTree)
    (k v : V) (hv : v ≠ k) :
    ∃! a, G.Adj k a ∧
      Relation.ReflTransGen (fun x y => x ≠ k ∧ y ≠ k ∧ G.Adj x y) a v := by
  classical
  obtain ⟨p, hp, _⟩ := hG.existsUnique_path k v
  cases p with
  | nil => exact (hv rfl).elim
  | @cons _ a _ h p =>
    obtain ⟨hpath, havoid⟩ := (SimpleGraph.Walk.cons_isPath_iff h p).mp hp
    refine ⟨a, ⟨h, walk_avoiding_vertex_relation p havoid⟩, ?_⟩
    intro b hb
    have hreverse : Relation.ReflTransGen
        (fun x y => x ≠ k ∧ y ≠ k ∧ G.Adj x y) v a := by
      exact walk_avoiding_vertex_relation p.reverse (by simpa using havoid)
    exact tree_branch_neighbor_unique hG.isAcyclic hb.1 h (hb.2.trans hreverse)

end OaiPairedStatesHamiltonian

module

public import Papers.OaiPairedStatesHamiltonian.Helpers.ForestState
public import Papers.OaiPairedStatesHamiltonian.Helpers.OppositeEdges

/-! Every opposite-edge tree component contains exactly one root. -/

public section

namespace OaiPairedStatesHamiltonian

set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.unusedVariables false
open Classical
attribute [local instance] propDecidable



-- @node: qs_component_root_count
/-- Suppose [the map is a sphere triangulation](hyp:hT), [the two face colors differ across
every edge](hyp:hcol), [the two states form a pair](hyp:hpair), [the second state's
opposite-edge graph is a forest](hyp:hforest), and [there are no separating triangles](hyp:hsep).
Then [the chosen component of that graph contains exactly one root, meaning a vertex of
the distinguished face, and has one fewer edge than vertices](goal). -/
lemma qs_component_root_count (T : SphereMap) (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (hcol : PartitionColoring T col) (t0 : T.Face)
    (r s : State T col t0) (hpair : IsPair T col t0 r s)
    (hforest : QsForest T col t0 s) (hsep : TreesNoSeparatingTriangle T)
    (component : (Qs T col t0 s).ConnectedComponent) :
    let KV := Finset.univ.filter (fun v => (Qs T col t0 s).connectedComponentMk v = component)
    let q := KV.card -- @realizes q(number of vertices in an opposite-edge component)
    let a := (KV ∩ roots T t0).card -- @realizes a(number of roots in that component)
    a = 1 ∧ ((Qs T col t0 s).induce {v | v ∈ KV}).edgeFinset.card = q - 1 := by
  exact qs_component_root_count_by_edges T hT col hcol t0 r s hpair hforest component


-- @node: lem:root-components
/-- Suppose [the map is a sphere triangulation](hyp:hT), [the two face colors differ across
every edge](hyp:hcol), [the two states form a pair](hyp:hpair), [the second state's
opposite-edge graph is a forest](hyp:hforest), and [there are no separating triangles](hyp:hsep).
Then [each component of the second state's opposite-edge graph contains exactly one vertex
of the distinguished face, that is, exactly one root](goal). -/
lemma qs_component_contains_unique_root (T : SphereMap) (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (hcol : PartitionColoring T col) (t0 : T.Face)
    (r s : State T col t0) (hpair : IsPair T col t0 r s)
    (hforest : QsForest T col t0 s) (hsep : TreesNoSeparatingTriangle T) :
    ∀ c : (Qs T col t0 s).ConnectedComponent,
      ∃! v : T.Vertex, v ∈ roots T t0 ∧ (Qs T col t0 s).connectedComponentMk v = c := by
  intro c
  let KV := Finset.univ.filter (fun v => (Qs T col t0 s).connectedComponentMk v = c)
  have hcard : (KV ∩ roots T t0).card = 1 :=
    (qs_component_root_count T hT col hcol t0 r s hpair hforest hsep c).1
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hcard
  have hmem : ∀ w, w ∈ KV ∩ roots T t0 ↔
      w ∈ roots T t0 ∧ (Qs T col t0 s).connectedComponentMk w = c := by
    intro w
    simp only [Finset.mem_inter, KV, Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_comm
  refine ⟨v, (hmem v).mp ?_, ?_⟩
  · rw [hv]
    exact Finset.mem_singleton_self v
  · intro w hw
    have hwmem := (hmem w).mpr hw
    rw [hv] at hwmem
    exact Finset.mem_singleton.mp hwmem


end OaiPairedStatesHamiltonian

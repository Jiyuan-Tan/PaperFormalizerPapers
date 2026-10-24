module

public import Papers.OaiPairedStatesHamiltonian.Helpers.MapOperations

/-! Forests and spanning trees with multigraph edge identities. -/

@[expose] public section

namespace OaiPairedStatesHamiltonian

set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.unusedVariables false
open Classical
attribute [local instance] propDecidable


-- @node: ass:spanning-forest-properties
/-- For a [sphere map](hyp:M) and a [set of its edges](hyp:S), the
[spanning-forest condition](goal) says that no closed trail has all its edges in that set. -/
noncomputable def SpanningForestProperties (M : SphereMap) (S : Set M.Edge) : Prop :=
  ∀ ds : List M.Dart, M.IsClosedTrail ds → ¬ (∀ d ∈ ds, M.edgeOf d ∈ S)

-- @node: def:spanning-forest
/-- A [set of edges](hyp:S) of a [sphere map](hyp:M) is a [spanning forest](goal)
when no closed trail lies entirely in that edge set. -/
structure IsSpanningForest (M : SphereMap) (S : Set M.Edge) : Prop where
  acyclic : SpanningForestProperties M S

namespace SphereMap
variable (M : SphereMap)
-- @node: SphereMap.subgraph_symm
/-- If distinct vertices are joined in one direction by a dart whose edge belongs to the selected
edge set, then [they are distinct in the reverse order and are joined by a reverse dart whose
edge also belongs to the set](goal). -/
lemma subgraph_symm (S : Set M.Edge) (u v : M.Vertex) :
    (u ≠ v ∧ ∃ d, M.edgeOf d ∈ S ∧ M.vert d = u ∧ M.head d = v) →
    (v ≠ u ∧ ∃ d, M.edgeOf d ∈ S ∧ M.vert d = v ∧ M.head d = u) := by
  rintro ⟨hne, d, hd, hu, hv⟩
  refine ⟨hne.symm, M.edgeInv d, ?_, hv, ?_⟩
  · have he : M.edgeOf (M.edgeInv d) = M.edgeOf d := by
      exact Quotient.sound (Equiv.Perm.sameCycle_apply_left.mpr
        (Equiv.Perm.SameCycle.refl M.edgeInv d))
    rw [he]
    exact hd
  · simpa only [head, RotationSystem.head, M.edgeInv_involutive d] using hu

/-- For a [sphere map](hyp:M) and a [selected edge set](hyp:S), the [associated spanning simple
graph](goal) retains every vertex and joins distinct vertices exactly when a selected edge joins them. -/
noncomputable def spanningGraph (S : Set M.Edge) : SimpleGraph M.Vertex where
  Adj u v := u ≠ v ∧ ∃ d, M.edgeOf d ∈ S ∧ M.vert d = u ∧ M.head d = v
  symm := ⟨fun u v h => M.subgraph_symm S u v h⟩
  loopless := ⟨fun v h => h.1 rfl⟩

/-- For a [sphere map](hyp:M) and an [edge set](hyp:S), the [spanning-tree condition](goal)
requires [that the edge set be a spanning forest](step:1) and [that its associated spanning
simple graph be connected](step:2). -/
noncomputable def IsSpanningTree (S : Set M.Edge) : Prop :=
  IsSpanningForest M S ∧ (M.spanningGraph S).Connected
end SphereMap

-- @node: ass:pin-4
/-- The [singleton-tree property](goal) says that every simple graph on a single vertex
[is a tree](step:1) and [has an empty edge set](step:2). -/
noncomputable def SingletonTreeEdgeless : Prop := ∀ G : SimpleGraph Unit, G.IsTree ∧ G.edgeSet = ∅
-- @node: def:singleton-tree
/-- The [singleton tree](goal) is the simple graph with one vertex and no edges. -/
noncomputable def singletonTree : SimpleGraph Unit := ⊥

/-- [Every simple graph on a single vertex is a tree and has no edges](goal). -/
lemma singletonTreeEdgeless_of_mathlib : SingletonTreeEdgeless := by
  intro G
  exact ⟨SimpleGraph.IsTree.of_subsingleton,
    SimpleGraph.edgeSet_eq_empty.mpr (Subsingleton.elim G ⊥)⟩


end OaiPairedStatesHamiltonian

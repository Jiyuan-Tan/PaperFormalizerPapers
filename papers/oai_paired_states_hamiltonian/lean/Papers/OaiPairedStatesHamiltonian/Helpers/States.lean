module

public import Papers.OaiPairedStatesHamiltonian.Helpers.PairOrientations

/-! Independent orientations of paired cycles and opposite-edge darts. -/

@[expose] public section

namespace OaiPairedStatesHamiltonian

set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.unusedVariables false
open Classical
attribute [local instance] propDecidable

variable (T : SphereMap) (col : T.Face → Bool) (t0 : T.Face)

-- @node: pairedEdges_cycleDecomposition
/-- If [the map is a sphere triangulation](hyp:hT) and [adjacent faces have opposite colors](hyp:hcol),
then [the edges of any paired state decompose into vertex-disjoint cycles of length at least three,
all of whose vertices are nonroot vertices and together cover every nonroot vertex; paired states
with the same undirected group correspond bijectively to independent binary choices of orientation
for these cycles, and their darts are exactly the union of the resulting oriented cycles](goal). -/
lemma pairedEdges_cycleDecomposition (hT : IsSphereTriangulation T)
    (hcol : PartitionColoring T col) (p : Pair T col t0) :
    ∃ cs : Finset T.Cycle,
      (∀ C ∈ cs, 3 ≤ C.val.length) ∧
      (∀ C ∈ cs, ∀ d ∈ C.val, T.vert d ∈ nonRoot T t0) ∧
      (∀ C ∈ cs, ∀ C' ∈ cs, C ≠ C' →
        Disjoint (C.val.map T.vert).toFinset (C'.val.map T.vert).toFinset) ∧
      cs.biUnion (fun C => C.val.toFinset) = pairedEdges T col t0 hT p.val.1 p.val.2 p.property ∧
      cs.biUnion (fun C => (C.val.map T.vert).toFinset) = nonRoot T t0 ∧
      ∃ orient : {q : Pair T col t0 // groupKey T col t0 hT q = groupKey T col t0 hT p} ≃ (cs → Bool),
        ∀ q, pairedEdges T col t0 hT q.val.val.1 q.val.val.2 q.val.property =
          cs.attach.biUnion (fun C => if orient q C then C.val.val.toFinset
            else (reverseDarts T C.val.val).toFinset) := by
  let cs := pairedCycles T col t0 hT hcol p
  obtain ⟨hlength, hnonroot, hdisjoint, hdarts, hvertices⟩ :=
    pairedCycles_spec T col t0 hT hcol p
  let e := pairCycleEquiv T col t0 hT hcol p
  let orient := (pairGroupOrbitEquiv T col t0 hT hcol p).trans
    (Equiv.arrowCongr e (Equiv.refl Bool))
  refine ⟨cs, hlength, hnonroot, hdisjoint, hdarts, hvertices, orient, ?_⟩
  intro q
  have h := switchPair_cycle_union T col t0 hT hcol p
    (pairOrbitFlags T col t0 hT hcol p q.val q.property)
  rw [switchPair_of_flags T col t0 hT hcol p q.val q.property] at h
  exact h

-- @node: def:qs-orientation
/-- For a [sphere map](hyp:T) with [face coloring](hyp:col) and [outer face](hyp:t0), given
[a sphere triangulation](hyp:hT), [two states](hyp:r,s), and [the fact that they form a pair](hyp:h),
the [oriented opposite-edge dart set](goal) is formed, for each black nonouter triangle, by
[identifying the third vertex distinct from both states' chosen vertices](step:1) and
[taking the dart from the first state's chosen vertex to that third vertex](step:2). -/
noncomputable def orientedQs (hT : IsSphereTriangulation T) (r s : State T col t0)
    (h : IsPair T col t0 r s) : Finset T.Dart :=
  Finset.univ.image (fun t : blackNonOuter T col t0 =>
    let u := thirdVertex T hT t.val (r.val t).val (s.val t).val
      (r.property.incident t) (s.property.incident t) (pair_vertex_ne T col t0 r s h t)
    faceDart T hT t.val (r.val t).val u.val (r.property.incident t)
      u.property.1 (Ne.symm u.property.2.1))


end OaiPairedStatesHamiltonian

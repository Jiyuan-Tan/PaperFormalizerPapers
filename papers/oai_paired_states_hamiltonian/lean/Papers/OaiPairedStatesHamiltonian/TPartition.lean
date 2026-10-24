module

public import Papers.OaiPairedStatesHamiltonian.Helpers.PartitionAssembly
public import Papers.OaiPairedStatesHamiltonian.Helpers.TreeGluing
public import Papers.OaiPairedStatesHamiltonian.Helpers.TrianglePartitionMatching
public import Papers.OaiPairedStatesHamiltonian.Helpers.ReverseCycleSides

/-! The prescribed facial triangle tree partition. -/

public section

namespace OaiPairedStatesHamiltonian

set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.unusedVariables false
open Classical
attribute [local instance] propDecidable


-- @node: thm:partition
/-- Suppose a [sphere map](hyp:T) [is a connected simple triangulation with at least
four vertices](hyp:hT), a [two-coloring of its faces](hyp:col) [assigns different colors
across every edge](hyp:hcol), [the vertex set is finite](hyp:hfin), and [every simple graph
on a single vertex is a tree with no edges](hyp:hpin). For a [chosen face](hyp:t0) and
[chosen edge](hyp:e0) [incident to that face](hyp:he0), [there is a partition of the
vertices into two sets, each inducing a tree, with both endpoints of the chosen edge
in the first set and every other vertex of the chosen face in the second](goal). -/
theorem exists_tree_partition (T : SphereMap) (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (hcol : PartitionColoring T col)
    (hfin : T.FiniteVertices) (hpin : SingletonTreeEdgeless)
    (t0 : T.Face) (e0 : T.Edge) (he0 : T.edgeOnFace e0 t0) :
    ∃ U : Set T.Vertex, (T.toSimpleGraph.induce U).IsTree ∧
      (T.toSimpleGraph.induce Uᶜ).IsTree ∧
      (∀ v ∈ T.edgeEndpoints e0, v ∈ U) ∧
      (∀ v ∈ T.faceVertices t0, v ∉ T.edgeEndpoints e0 → v ∉ U) := by
  induction hn : Fintype.card T.Vertex using Nat.strong_induction_on generalizing T with
  | h n ih =>
    by_cases hsep : TreesNoSeparatingTriangle T
    · exact exists_tree_partition_of_noSeparatingTriangle T hT col hcol hsep t0 e0 he0
    · obtain ⟨C, hC, ht0⟩ := T.exists_separatingTriangle_with_face_left hT hsep t0
      obtain ⟨outer, hout, hN, hlt, c, hc, hcolors⟩ :=
        T.exists_colored_triangle_cap hT col hcol C hC
      let N := T.cycleCappedMap hT C outer hout
      have hltN : Fintype.card N.Vertex < n := by rw [← hn]; exact hlt
      obtain ⟨f, e, hef, he, hfverts, heends⟩ :=
        T.exists_cycleCap_original_prescription hT C outer hout t0 ht0 e0 he0
      obtain ⟨A0, hA0, hA0c, hends, hthird⟩ :=
        ih (Fintype.card N.Vertex) hltN N hN c hc (show Finite N.Vertex from inferInstance) f e hef rfl
      obtain ⟨A, hAL, hAT, hAcT, hAends, hAthird⟩ :=
        T.triangleCap_partition_lift hT C hC.props.1 outer hout t0 ht0 e0 f e
          hfverts heends A0 hA0 hA0c hends hthird
      let D := reverseCycle T C
      have hD : IsSeparatingTriangle T D := T.reverseCycle_isSeparatingTriangle hT C hC
      obtain ⟨outerR, houtR, hNR, hltR, cR, hcR, hcolorsR⟩ :=
        T.exists_colored_triangle_cap hT col hcol D hD
      let NR := T.cycleCappedMap hT D outerR houtR
      have hltNR : Fintype.card NR.Vertex < n := by rw [← hn]; exact hltR
      have hregions : T.leftRegion D = (T.leftRegion C)ᶜ := T.reverseCycle_leftRegion hT C
      have hvertices : (D.val.map T.vert).toFinset = (C.val.map T.vert).toFinset :=
        T.reverseCycle_vertices C
      have hboundary := T.triangle_cycle_labels_not_monochromatic hT C hC.props.1 A
        hAT.isAcyclic hAcT.isAcyclic
      have hboundaryD : ¬ (↑(D.val.map T.vert).toFinset : Set T.Vertex) ⊆ A ∧
          ¬ (↑(D.val.map T.vert).toFinset : Set T.Vertex) ⊆ Aᶜ := by
        rw [hvertices]
        exact hboundary
      obtain ⟨B, hBR, hBT, hBcT, hagree⟩ := T.exists_triangleCap_partition_matching hT D
        hD.props.1 outerR houtR hNR A hboundaryD (fun f e he =>
          ih (Fintype.card NR.Vertex) hltNR NR hNR cR hcR (show Finite NR.Vertex from inferInstance) f e he rfl)
      rw [hregions] at hBR hBcT
      let L := T.regionVertexSet (T.leftRegion C)
      let R := T.regionVertexSet (T.leftRegion C)ᶜ
      have hcover : L ∪ R = Set.univ := by
        apply Set.eq_univ_of_forall
        exact T.region_vertices_cover hT _
      have hboundaryLR : L ∩ R = (↑(C.val.map T.vert).toFinset : Set T.Vertex) := by
        ext v
        exact (T.cycle_region_vertices_inter hT C outer hout v).trans List.mem_toFinset.symm
      have hagreeLR : ∀ v ∈ L ∩ R, v ∈ A ↔ v ∈ B := by
        intro v hv
        have hvC : v ∈ (C.val.map T.vert).toFinset := by
          change v ∈ (↑(C.val.map T.vert).toFinset : Set T.Vertex)
          rw [← hboundaryLR]
          exact hv
        have hvD : v ∈ D.val.map T.vert := List.mem_toFinset.mp (hvertices.symm ▸ hvC)
        exact hagree v hvD
      obtain ⟨u, v, w, htriangle, huv, huw, hvw⟩ :=
        T.triangle_cycle_vertex_triangle hT C hC.props.1
      have hglue := tree_partition_gluing_triangle T.toSimpleGraph L R A B hcover hAL hBR
        hagreeLR (T.cycle_side_no_cross_edges hT C outer hout) hAT hBT hAcT hBcT
        u v w huv huw hvw (hboundaryLR.trans htriangle)
      refine ⟨A ∪ B, hglue.1, hglue.2.1, ?_, ?_⟩
      · intro x hx
        exact Or.inl (hAends x hx)
      · intro x hx hnends hlabel
        have hxL : x ∈ L := (T.regionVertexSet_iff_face_incidence hT _ x).mpr
          ⟨t0, ht0, hx⟩
        have hxA : x ∈ A := by
          rw [← hglue.2.2.1]
          exact ⟨hlabel, hxL⟩
        exact hAthird x hx hnends hxA


end OaiPairedStatesHamiltonian

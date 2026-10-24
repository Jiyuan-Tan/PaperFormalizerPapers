module

public import Papers.OaiPairedStatesHamiltonian.Helpers.DensityComponents
public import Mathlib.Combinatorics.SimpleGraph.Finite

/-! Finite component and incidence counts for the capacity-two inequality. -/

@[expose] public section

namespace OaiPairedStatesHamiltonian

open Classical
attribute [local instance] propDecidable
set_option linter.style.openClassical false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

namespace SphereMap
variable (T : SphereMap)

-- @node: SphereMap.densityComponentVertices_card_sum
/-- [The sum of the vertex counts of all connected components of the induced
map equals the number of selected vertices](goal). -/
lemma densityComponentVertices_card_sum (U : Finset T.Vertex) :
    (∑ K, (T.densityComponentVertices U K).card) = U.card := by
  have hc (K : (T.induce (↑U : Set T.Vertex)).Component) :
      (T.densityComponentVertices U K).card =
        (Finset.univ.filter (fun v : (T.induce (↑U : Set T.Vertex)).Vertex =>
          (T.induce (↑U : Set T.Vertex)).toSimpleGraph.connectedComponentMk v = K)).card :=
    Finset.card_image_of_injective _ Subtype.val_injective
  simp_rw [hc]
  calc
    _ = Fintype.card (T.induce (↑U : Set T.Vertex)).Vertex := by
      simpa using (Finset.card_eq_sum_card_fiberwise
        (s := Finset.univ) (t := Finset.univ)
        (f := (T.induce (↑U : Set T.Vertex)).toSimpleGraph.connectedComponentMk)
        (fun _ _ => Finset.mem_univ _)).symm
    _ = U.card := by
      simp only [induce, inducedRotation, Fintype.card_subtype,
        Finset.mem_coe, Finset.filter_mem_eq_inter, Finset.univ_inter]

-- @node: SphereMap.face_vertices_same_densityComponent
/-- If [the map is a sphere triangulation](hyp:hT), [all vertices of a face are
selected](hyp:hf), and [a first vertex](hyp:hv) and [a second vertex](hyp:hw)
both belong to that face, then [the two vertices lie in the same connected
component of the induced map](goal). -/
lemma face_vertices_same_densityComponent (hT : IsSphereTriangulation T)
    (U : Finset T.Vertex) (f : T.Face) (hf : T.faceVertices f ⊆ U)
    (v w : T.Vertex) (hv : v ∈ T.faceVertices f) (hw : w ∈ T.faceVertices f) :
    (T.induce (↑U : Set T.Vertex)).toSimpleGraph.connectedComponentMk ⟨v, hf hv⟩ =
      (T.induce (↑U : Set T.Vertex)).toSimpleGraph.connectedComponentMk ⟨w, hf hw⟩ := by
  rw [T.induce_toSimpleGraph]
  by_cases he : v = w
  · subst w; rfl
  · obtain ⟨d, hd, he', _⟩ := exists_faceDart T hT f v w hv hw he
    exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      (G := T.toSimpleGraph.induce (↑U : Set T.Vertex)) ⟨he, d, hd, he'⟩

-- @node: SphereMap.face_mem_densityComponent
/-- If [the map is a sphere triangulation](hyp:hT) and [all vertices of an
original face are selected](hyp:hf), then [there is exactly one connected
component of the induced map containing all vertices of that face](goal). -/
lemma face_mem_densityComponent (hT : IsSphereTriangulation T)
    (U : Finset T.Vertex) (f : T.Face) (hf : T.faceVertices f ⊆ U) :
    ∃! K, T.faceVertices f ⊆ T.densityComponentVertices U K := by
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (by rw [(hT.props.2.2.2 f).2]; omega)
  let K := (T.induce (↑U : Set T.Vertex)).toSimpleGraph.connectedComponentMk ⟨v, hf hv⟩
  refine ⟨K, ?_, ?_⟩
  · intro w hw
    exact (T.mem_densityComponentVertices U K w).mpr
      ⟨hf hw, T.face_vertices_same_densityComponent hT U f hf w v hw hv⟩
  · intro L hL
    exact ((T.mem_densityComponentVertices U L v).mp (hL hv)).choose_spec.symm

-- @node: SphereMap.densityRetainsEdge
/-- For [a sphere map](hyp:T), [a selected finite vertex set](hyp:U), and [an
edge](hyp:e), the [edge retention condition](goal) says that the edge has a
directed occurrence whose tail and head both belong to the selected set. -/
noncomputable def densityRetainsEdge (U : Finset T.Vertex) (e : T.Edge) : Prop :=
  ∃ d, T.vert d ∈ U ∧ T.head d ∈ U ∧ T.edgeOf d = e

-- @node: SphereMap.densityRetainsEdge_edgeOf
/-- [The edge represented by a directed occurrence is retained by a selected
vertex set exactly when both its tail and its head belong to that set](goal). -/
lemma densityRetainsEdge_edgeOf (U : Finset T.Vertex) (d : T.Dart) :
    T.densityRetainsEdge U (T.edgeOf d) ↔ T.vert d ∈ U ∧ T.head d ∈ U := by
  constructor
  · rintro ⟨e, hv, hw, he⟩
    rcases (T.edgeOf_eq_iff e d).mp he with rfl | rfl
    · exact ⟨hv, hw⟩
    · change T.head e ∈ U ∧ T.vert (T.edgeInv (T.edgeInv e)) ∈ U
      rw [T.edgeInv_involutive]
      exact ⟨hw, hv⟩
  · rintro ⟨hv, hw⟩
    exact ⟨d, hv, hw, rfl⟩

-- @node: SphereMap.density_induced_edge_card
/-- [The number of edges of the induced map equals the number of original
edges having both endpoints in the selected vertex set](goal). -/
lemma density_induced_edge_card (U : Finset T.Vertex) :
    Fintype.card (T.induce (↑U : Set T.Vertex)).Edge =
      (Finset.univ.filter (T.densityRetainsEdge U)).card := by
  apply Finset.card_bij (fun e _ => T.inducedEdgeMap (↑U : Set T.Vertex) e)
  · intro e he
    induction e using Quotient.inductionOn with | h d =>
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, d.val,
        d.property.1, d.property.2, rfl⟩
  · intro a ha b hb hab
    exact T.inducedEdgeMap_injective _ hab
  · intro e he
    obtain ⟨d, hv, hw, rfl⟩ := (Finset.mem_filter.mp he).2
    exact ⟨(T.induce (↑U : Set T.Vertex)).edgeOf ⟨d, hv, hw⟩, Finset.mem_univ _, rfl⟩

-- @node: SphereMap.edge_mem_densityComponent
/-- If [an original edge is retained by the selected vertex set](hyp:he), then
[exactly one connected component of the induced map retains that edge when
restricting to the vertices of that component](goal). -/
lemma edge_mem_densityComponent (U : Finset T.Vertex) (e : T.Edge)
    (he : T.densityRetainsEdge U e) :
    ∃! K, T.densityRetainsEdge (T.densityComponentVertices U K) e := by
  obtain ⟨d, hv, hw, rfl⟩ := he
  let a : (T.induce (↑U : Set T.Vertex)).Dart := ⟨d, hv, hw⟩
  let K := (T.induce (↑U : Set T.Vertex)).toSimpleGraph.connectedComponentMk
    ((T.induce (↑U : Set T.Vertex)).vert a)
  have hh := (T.induce (↑U : Set T.Vertex)).toRotationSystem.dart_component_eq_head a
  have hhead : ((T.induce (↑U : Set T.Vertex)).head a).val = T.head d :=
    T.induce_head_val _ a
  have htail : (T.induce (↑U : Set T.Vertex)).vert a = ⟨T.vert d, hv⟩ := rfl
  have hhead' : (T.induce (↑U : Set T.Vertex)).head a = ⟨T.head d, hw⟩ :=
    Subtype.ext hhead
  have hh' : (T.induce (↑U : Set T.Vertex)).toSimpleGraph.connectedComponentMk
      ⟨T.vert d, hv⟩ =
      (T.induce (↑U : Set T.Vertex)).toSimpleGraph.connectedComponentMk ⟨T.head d, hw⟩ :=
    hh.trans (congrArg (T.induce (↑U : Set T.Vertex)).toSimpleGraph.connectedComponentMk hhead')
  refine ⟨K, ?_, ?_⟩
  · exact (T.densityRetainsEdge_edgeOf _ d).mpr
      ⟨(T.mem_densityComponentVertices U K _).mpr ⟨hv, rfl⟩,
        (T.mem_densityComponentVertices U K _).mpr ⟨hw, hh'.symm⟩⟩
  · intro L hL
    have hl := (T.densityRetainsEdge_edgeOf _ d).mp hL
    exact ((T.mem_densityComponentVertices U L _).mp hl.1).choose_spec.symm

end SphereMap

-- @node: sum_filter_card_of_unique_partition
/-- If [every member of each group satisfies a selection criterion](hyp:hsub)
and [every element satisfying that criterion belongs to exactly one
group](hyp:hex), then [the sum of the group sizes equals the total number of
elements satisfying the criterion](goal), for finite sets of elements and
group indices. -/
lemma sum_filter_card_of_unique_partition {α β : Type} [Fintype α] [Fintype β]
    (p : α → Prop) (q : β → α → Prop)
    (hsub : ∀ b a, q b a → p a) (hex : ∀ a, p a → ∃! b, q b a) :
    (∑ b, (Finset.univ.filter (q b)).card) = (Finset.univ.filter p).card := by
  classical
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hp : p a
  · obtain ⟨b, hb, hu⟩ := hex a hp
    have hq (c : β) : q c a ↔ c = b := ⟨fun hc => hu c hc, fun hc => hc ▸ hb⟩
    simp [hp, hq]
  · have hq (b : β) : ¬ q b a := fun h => hp (hsub b a h)
    simp [hp, hq]

namespace SphereMap
variable (T : SphereMap)

-- @node: SphereMap.density_component_edges_sum
/-- [The sum of the edge counts of the maps induced by the vertex sets of all
connected components equals the edge count of the whole induced map](goal). -/
lemma density_component_edges_sum (U : Finset T.Vertex) :
    (∑ K, Fintype.card (T.induce (↑(T.densityComponentVertices U K) : Set T.Vertex)).Edge) =
      Fintype.card (T.induce (↑U : Set T.Vertex)).Edge := by
  simp_rw [T.density_induced_edge_card]
  apply sum_filter_card_of_unique_partition
  · intro K e he
    obtain ⟨d, hv, hw, hd⟩ := he
    exact ⟨d, T.densityComponentVertices_subset U K hv,
      T.densityComponentVertices_subset U K hw, hd⟩
  · exact T.edge_mem_densityComponent U

-- @node: SphereMap.density_component_faces_sum
/-- If [the map is a sphere triangulation](hyp:hT), then [summing the number of
original black faces wholly contained in each connected component of the
induced map gives the number of original black faces wholly contained in the
selected vertex set](goal). -/
lemma density_component_faces_sum (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (U : Finset T.Vertex) :
    (∑ K, (Finset.univ.filter (fun f => col f = true ∧
      T.faceVertices f ⊆ T.densityComponentVertices U K)).card) =
      (Finset.univ.filter (fun f => col f = true ∧ T.faceVertices f ⊆ U)).card := by
  convert sum_filter_card_of_unique_partition
    (fun f : T.Face => col f = true ∧ T.faceVertices f ⊆ U)
    (fun K : (T.induce (↑U : Set T.Vertex)).Component =>
      fun f => col f = true ∧ T.faceVertices f ⊆ T.densityComponentVertices U K) ?_ ?_ using 1
  · apply Finset.sum_congr
    · ext K; simp
    · intro K hK
      congr 1
      ext f; simp
  · congr 1
    ext f; simp
  · intro K f hf
    exact ⟨hf.1, hf.2.trans (T.densityComponentVertices_subset U K)⟩
  · intro f hf
    obtain ⟨K, hK, hu⟩ := T.face_mem_densityComponent hT U f hf.2
    exact ⟨K, ⟨hf.1, hK⟩, fun L hL => hu L hL.2⟩

-- @node: SphereMap.density_bound_containing_face
/-- Suppose [the map is a sphere triangulation](hyp:hT), [adjacent faces have
opposite colors](hyp:hcol), and [there is no separating triangle](hyp:hsep).
If [a designated original face is black](hyp:hf0) and [all of its vertices
belong to the selected set](hyp:hroot), then [the number of induced edges minus
the number of original black faces wholly contained in the selected set is at
most twice the number of selected vertices minus four](goal). -/
lemma density_bound_containing_face (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (hcol : PartitionColoring T col)
    (hsep : PairsNoSeparatingTriangle T) (U : Finset T.Vertex)
    (f0 : T.Face) (hf0 : col f0 = true) (hroot : T.faceVertices f0 ⊆ U) :
    (Fintype.card (T.induce (↑U : Set T.Vertex)).Edge : ℤ) -
      (Finset.univ.filter (fun f => col f = true ∧ T.faceVertices f ⊆ U)).card ≤
        2 * U.card - 4 := by
  obtain ⟨K0, hK0, _⟩ := T.face_mem_densityComponent hT U f0 hroot
  let KV := T.densityComponentVertices U
  let e := fun K => Fintype.card (T.induce (↑(KV K) : Set T.Vertex)).Edge
  let b := fun K => (Finset.univ.filter
    (fun f => col f = true ∧ T.faceVertices f ⊆ KV K)).card
  have hbound (K : (T.induce (↑U : Set T.Vertex)).Component) :
      (e K : ℤ) - b K ≤ 2 * (KV K).card - if K = K0 then 4 else 0 := by
    have hd := induced_component_density T hT col hcol hsep U K
    change (4 ≤ (KV K).card → _ ) ∧ (e K : ℤ) - b K ≤ 2 * (KV K).card at hd
    by_cases hk : K = K0
    · subst K
      simp only [if_true]
      have hp : 3 ≤ (KV K0).card := by
        have hc := Finset.card_le_card hK0
        rw [(hT.props.2.2.2 f0).2] at hc
        exact hc
      by_cases hp4 : 4 ≤ (KV K0).card
      · exact (hd.1 hp4).2.2.1
      · have hp3 : (KV K0).card = 3 := by omega
        have he := T.density_induced_edge_le_choose hT (KV K0)
        rw [hp3] at he
        norm_num at he
        have hb : 1 ≤ b K0 := Finset.card_pos.mpr
          ⟨f0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf0, hK0⟩⟩
        dsimp only [e] at *
        omega
    · simpa only [hk, if_false, sub_zero] using hd.2
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun K _ => hbound K)
  simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at hs
  have he := T.density_component_edges_sum U
  have hb := T.density_component_faces_sum hT col U
  have hv := T.densityComponentVertices_card_sum U
  change (∑ K, e K) = _ at he
  change (∑ K, b K) = _ at hb
  change (∑ K, (KV K).card) = _ at hv
  have hez := congrArg (fun n : ℕ => (n : ℤ)) he
  have hbz := congrArg (fun n : ℕ => (n : ℤ)) hb
  have hvz := congrArg (fun n : ℕ => (n : ℤ)) hv
  push_cast at hez hbz hvz
  rw [hez, hbz, ← Finset.mul_sum, hvz] at hs
  exact hs

-- @node: SphereMap.density_induced_edge_card_colored
/-- If [faces on opposite sides of every edge have opposite colors](hyp:hcol),
then [the number of induced edges equals the number of original directed edge
occurrences incident to black faces whose tail and head are both
selected](goal). -/
lemma density_induced_edge_card_colored (col : T.Face → Bool)
    (hcol : PartitionColoring T col) (U : Finset T.Vertex) :
    Fintype.card (T.induce (↑U : Set T.Vertex)).Edge =
      (Finset.univ.filter (fun d => col (T.faceOf d) = true ∧
        T.vert d ∈ U ∧ T.head d ∈ U)).card := by
  let N := T.induce (↑U : Set T.Vertex)
  let D := {d : T.Dart // col (T.faceOf d) = true ∧ T.vert d ∈ U ∧ T.head d ∈ U}
  let g : D → N.Edge := fun d => N.edgeOf ⟨d.val, d.property.2⟩
  have hinj : Function.Injective g := by
    intro d e he
    have he' := congrArg (T.inducedEdgeMap (↑U : Set T.Vertex)) he
    change T.edgeOf d.val = T.edgeOf e.val at he'
    rcases (T.edgeOf_eq_iff d.val e.val).mp he' with he | he
    · exact Subtype.ext he.symm
    · have hc := hcol d.val
      rw [d.property.1, ← he, e.property.1] at hc
      exact (hc rfl).elim
  have hsurj : Function.Surjective g := by
    intro e
    induction e using Quotient.inductionOn with | h d =>
      by_cases hd : col (T.faceOf d.val) = true
      · exact ⟨⟨d.val, hd, d.property⟩, rfl⟩
      · have hi : col (T.faceOf (T.edgeInv d.val)) = true := by
          have hc := hcol d.val
          cases hf : col (T.faceOf d.val) <;>
            cases hg : col (T.faceOf (T.edgeInv d.val)) <;> simp_all
        let a : D := ⟨T.edgeInv d.val, hi, d.property.2, by
          change T.vert (T.edgeInv (T.edgeInv d.val)) ∈ U
          rw [T.edgeInv_involutive]
          exact d.property.1⟩
        refine ⟨a, ?_⟩
        apply T.inducedEdgeMap_injective (↑U : Set T.Vertex)
        change T.edgeOf (T.edgeInv d.val) = T.edgeOf d.val
        exact ((T.edgeOf_eq_iff d.val (T.edgeInv d.val)).mpr (Or.inr rfl)).symm
  exact (Fintype.card_congr (Equiv.ofBijective g ⟨hinj, hsurj⟩)).symm.trans
    (Fintype.card_subtype _)

-- @node: SphereMap.triangle_retained_incidence_count
/-- If [the map is a sphere triangulation](hyp:hT), then for any original face
and selected vertex set, [the number of its directed edge occurrences with
both endpoints selected, plus the smaller of two and the number of its
unselected vertices, equals two plus one if all its vertices are selected,
and equals two otherwise](goal). -/
lemma triangle_retained_incidence_count (hT : IsSphereTriangulation T)
    (f : T.Face) (U : Finset T.Vertex) :
    ((T.faceDarts f).filter (fun d => T.vert d ∈ U ∧ T.head d ∈ U)).card +
      min 2 ((T.faceVertices f) \ U).card =
        2 + if T.faceVertices f ⊆ U then 1 else 0 := by
  have hcard : (T.faceDarts f).card = 3 :=
    (T.faceLength_eq_card_faceDarts f).symm.trans (hT.props.2.2.2 f).1
  obtain ⟨d, hd⟩ := Finset.card_pos.mp (by omega : 0 < (T.faceDarts f).card)
  have hcyc : T.facePerm.IsCycleOn (↑(T.faceDarts f) : Set T.Dart) := by
    simpa [faceDarts] using T.dual_rot_fibre hT.props.1 f
  let e := T.facePerm d
  let a := T.facePerm e
  have he : e ∈ T.faceDarts f := hcyc.1.1 hd
  have ha : a ∈ T.faceDarts f := hcyc.1.1 he
  have hthree : T.facePerm a = d := by
    have h := hcyc.pow_card_apply hd
    rw [hcard] at h
    simpa only [pow_succ', pow_zero, Equiv.Perm.one_apply, Equiv.Perm.mul_apply, e, a] using h
  have hnext (b : T.Dart) : T.vert (T.facePerm b) = T.head b := T.rot_vertex _
  have hvde : T.vert d ≠ T.vert e := by
    rw [hnext]
    exact hT.props.2.1.1 d
  have hvea : T.vert e ≠ T.vert a := by
    change T.vert e ≠ T.vert (T.facePerm e)
    rw [hnext e]
    exact hT.props.2.1.1 e
  have hvad : T.vert a ≠ T.vert d := by
    have h : T.vert a ≠ T.vert (T.facePerm a) := by
      rw [hnext a]
      exact hT.props.2.1.1 a
    rw [hthree] at h
    exact h
  have hde : d ≠ e := fun h => hvde (congrArg T.vert h)
  have hea : e ≠ a := fun h => hvea (congrArg T.vert h)
  have had : a ≠ d := fun h => hvad (congrArg T.vert h)
  have hds : T.faceDarts f = {d, e, a} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨hd, he, ha⟩
    · simp [hcard, hde, Ne.symm had, hea]
  have hvs : T.faceVertices f = {T.vert d, T.vert e, T.vert a} := by
    rw [triangulation_faceVertices_eq_image T hT, hds]
    simp
  have hhd : T.head d = T.vert e := (hnext d).symm
  have hhe : T.head e = T.vert a := (hnext e).symm
  have hha : T.head a = T.vert d := (hnext a).symm.trans (congrArg T.vert hthree)
  rw [hds, hvs]
  by_cases hdU : T.vert d ∈ U <;> by_cases heU : T.vert e ∈ U <;>
    by_cases haU : T.vert a ∈ U <;>
    simp [Finset.sdiff_eq_filter, Finset.filter_insert, Finset.filter_singleton,
      Finset.insert_subset_iff, Finset.singleton_subset_iff, hhd, hhe, hha,
      hdU, heU, haU, hde, hea, hvde, hvea, Ne.symm had, Ne.symm hvad]

-- @node: SphereMap.density_incidence_identity
/-- If [the map is a sphere triangulation](hyp:hT) and [adjacent faces have
opposite colors](hyp:hcol), then [the number of induced edges plus the sum over
original black faces of the smaller of two and their number of unselected
vertices equals twice the total number of black faces plus the number of
black faces whose vertices are all selected](goal). -/
lemma density_incidence_identity (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (hcol : PartitionColoring T col) (U : Finset T.Vertex) :
    Fintype.card (T.induce (↑U : Set T.Vertex)).Edge +
      (∑ f ∈ Finset.univ.filter (fun f => col f = true),
        min 2 ((T.faceVertices f) \ U).card) =
      2 * blackFaceCount T col +
        (Finset.univ.filter (fun f => col f = true ∧ T.faceVertices f ⊆ U)).card := by
  let B := Finset.univ.filter (fun f => col f = true)
  have he : Fintype.card (T.induce (↑U : Set T.Vertex)).Edge =
      ∑ f ∈ B, ((T.faceDarts f).filter (fun d => T.vert d ∈ U ∧ T.head d ∈ U)).card := by
    rw [T.density_induced_edge_card_colored col hcol U]
    have hc := Finset.card_eq_sum_card_fiberwise
      (s := Finset.univ.filter (fun d => col (T.faceOf d) = true ∧
        T.vert d ∈ U ∧ T.head d ∈ U)) (t := B) (f := T.faceOf) (by
        intro d hd
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hd).2.1⟩)
    rw [hc]
    apply Finset.sum_congr rfl
    intro f hf
    congr 1
    ext d
    have hb := (Finset.mem_filter.mp hf).2
    simp only [faceDarts, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨hc, hv, hw⟩, he⟩
      exact ⟨he, hv, hw⟩
    · rintro ⟨he, hv, hw⟩
      exact ⟨⟨he.symm ▸ hb, hv, hw⟩, he⟩
  rw [he, ← Finset.sum_add_distrib]
  simp_rw [T.triangle_retained_incidence_count hT]
  simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
    Finset.sum_boole]
  simp [B, blackFaceCount, Nat.mul_comm, Finset.filter_filter]

end SphereMap
end OaiPairedStatesHamiltonian

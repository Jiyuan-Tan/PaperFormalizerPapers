module

public import Papers.OaiPairedStatesHamiltonian.Helpers.States
public import Mathlib.Combinatorics.SimpleGraph.Finite

/-! Connectivity, Euler counts, and retained original faces of induced components. -/

@[expose] public section

namespace OaiPairedStatesHamiltonian

set_option linter.style.openClassical false
open Classical
attribute [local instance] propDecidable
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

namespace SphereMap
variable (T : SphereMap)

-- @node: SphereMap.densityComponentVertices
/-- For [a sphere map](hyp:T), [a finite vertex set](hyp:U), and [a connected
component of the map induced by that set](hyp:K), the [component vertex set](goal)
consists of the original vertices represented in that component. -/
noncomputable def densityComponentVertices (U : Finset T.Vertex)
    (K : (T.induce (↑U : Set T.Vertex)).Component) : Finset T.Vertex :=
  (Finset.univ.filter (fun v : (T.induce (↑U : Set T.Vertex)).Vertex =>
    (T.induce (↑U : Set T.Vertex)).toSimpleGraph.connectedComponentMk v = K)).image
      Subtype.val

-- @node: SphereMap.mem_densityComponentVertices
/-- [A vertex belongs to a component's vertex set exactly when it belongs to
the inducing set and, viewed as a vertex of the induced map, has that connected
component](goal). -/
lemma mem_densityComponentVertices (U : Finset T.Vertex)
    (K : (T.induce (↑U : Set T.Vertex)).Component) (v : T.Vertex) :
    v ∈ T.densityComponentVertices U K ↔
      ∃ hv : v ∈ U, (T.induce (↑U : Set T.Vertex)).toSimpleGraph.connectedComponentMk
        ⟨v, hv⟩ = K := by
  simp only [densityComponentVertices, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.property, hw⟩
  · rintro ⟨hv, hk⟩
    exact ⟨⟨v, hv⟩, hk, rfl⟩

-- @node: SphereMap.densityComponentVertices_subset
/-- [The vertex set of any component of an induced map is contained in the
vertex set used to induce the map](goal). -/
lemma densityComponentVertices_subset (U : Finset T.Vertex)
    (K : (T.induce (↑U : Set T.Vertex)).Component) :
    T.densityComponentVertices U K ⊆ U := by
  intro v hv
  exact ((T.mem_densityComponentVertices U K v).mp hv).choose

-- @node: SphereMap.densityComponentVertices_unique
/-- If [a vertex belongs to one induced component's vertex set](hyp:hv) and
[also belongs to another induced component's vertex set](hyp:hw), then
[the two components are equal](goal). -/
lemma densityComponentVertices_unique (U : Finset T.Vertex)
    (K L : (T.induce (↑U : Set T.Vertex)).Component) (v : T.Vertex)
    (hv : v ∈ T.densityComponentVertices U K) (hw : v ∈ T.densityComponentVertices U L) :
    K = L := by
  obtain ⟨hv, hk⟩ := (T.mem_densityComponentVertices U K v).mp hv
  obtain ⟨hw, hl⟩ := (T.mem_densityComponentVertices U L v).mp hw
  exact hk.symm.trans hl

-- @node: SphereMap.densityEdgePair
/-- For [a sphere map](hyp:T) and [a finite inducing vertex set](hyp:U), the
[edge endpoint map](goal) sends each edge of the induced map to the unordered
pair of its endpoints. -/
noncomputable def densityEdgePair (U : Finset T.Vertex) :
    (T.induce (↑U : Set T.Vertex)).Edge → Sym2 (T.induce (↑U : Set T.Vertex)).Vertex :=
  Quotient.lift (fun d => s((T.induce (↑U : Set T.Vertex)).vert d,
    (T.induce (↑U : Set T.Vertex)).head d)) (by
    intro d e h
    rcases ((T.induce (↑U : Set T.Vertex)).edgeOf_eq_iff d e).mp
      (Quotient.sound h) with rfl | rfl
    · rfl
    · change s(_, _) = s(_, (T.induce (↑U : Set T.Vertex)).vert
        ((T.induce (↑U : Set T.Vertex)).edgeInv
          ((T.induce (↑U : Set T.Vertex)).edgeInv d)))
      rw [(T.induce (↑U : Set T.Vertex)).edgeInv_involutive]
      exact Sym2.eq_swap)

-- @node: SphereMap.density_induced_edge_le_choose
/-- For [a sphere triangulation](hyp:hT), [the number of edges induced by a
finite vertex set is at most the number of unordered pairs of distinct vertices
in that set](goal). -/
lemma density_induced_edge_le_choose (hT : IsSphereTriangulation T) (U : Finset T.Vertex) :
    Fintype.card (T.induce (↑U : Set T.Vertex)).Edge ≤ U.card.choose 2 := by
  let N := T.induce (↑U : Set T.Vertex)
  have hinj : Function.Injective (T.densityEdgePair U) := by
    intro e f
    induction e using Quotient.inductionOn with | h d =>
      induction f using Quotient.inductionOn with | h a =>
        intro he
        have he' := congrArg (Sym2.map (Subtype.val : N.Vertex → T.Vertex)) he
        change s(T.vert d.val, (N.head d).val) =
          s(T.vert a.val, (N.head a).val) at he'
        rw [T.induce_head_val, T.induce_head_val] at he'
        apply T.inducedEdgeMap_injective (↑U : Set T.Vertex)
        exact hT.props.2.1.2 _ _ he'
  have hc : Fintype.card N.Edge ≤ N.toSimpleGraph.edgeFinset.card := by
    apply Finset.card_le_card_of_injOn (T.densityEdgePair U)
    · intro e he
      induction e using Quotient.inductionOn with | h d =>
        apply SimpleGraph.mem_edgeFinset.mpr
        refine ⟨?_, d, rfl, rfl⟩
        intro hv
        apply hT.props.2.1.1 d.val
        have hh := congrArg Subtype.val hv
        exact hh.trans (T.induce_head_val _ d)
    · exact hinj.injOn
  have bound := N.toSimpleGraph.card_edgeFinset_le_card_choose_two
  have hv : Fintype.card N.Vertex = U.card := by
    simp only [N, induce, inducedRotation, Fintype.card_subtype,
      Finset.mem_coe, Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [hv] at bound
  exact hc.trans bound


-- @node: SphereMap.densityComponent_connected
/-- [The map induced by the original vertices of a connected component of an
induced map is connected](goal). -/
lemma densityComponent_connected (U : Finset T.Vertex)
    (K : (T.induce (↑U : Set T.Vertex)).Component) :
    (T.induce (↑(T.densityComponentVertices U K) : Set T.Vertex)).IsConnectedMap := by
  let N := T.induce (↑U : Set T.Vertex)
  let KV := T.densityComponentVertices U K
  let phi : K.toSimpleGraph →g (T.induce (↑KV : Set T.Vertex)).toSimpleGraph :=
    { toFun := fun v => ⟨v.val.val, (T.mem_densityComponentVertices U K v.val.val).mpr
        ⟨v.val.property, (SimpleGraph.ConnectedComponent.mem_supp_iff K _).mp v.property⟩⟩
      map_rel' := by
        intro v w h
        rw [T.induce_toSimpleGraph]
        change T.toSimpleGraph.Adj v.val.val w.val.val
        have h' : N.toSimpleGraph.Adj v.val w.val := h
        rw [T.induce_toSimpleGraph] at h'
        exact h' }
  apply K.connected_toSimpleGraph.map phi
  intro v
  obtain ⟨hv, hk⟩ := (T.mem_densityComponentVertices U K v.val).mp v.property
  exact ⟨⟨⟨v.val, hv⟩, (SimpleGraph.ConnectedComponent.mem_supp_iff K _).mpr hk⟩, Subtype.ext rfl⟩

-- @node: SphereMap.densityComponent_euler
/-- [For the map induced by a component's original vertices, the number of
vertices plus the number of faces equals the number of edges plus two](goal). -/
lemma densityComponent_euler (U : Finset T.Vertex)
    (K : (T.induce (↑U : Set T.Vertex)).Component) :
    let KV := T.densityComponentVertices U K
    let N := T.induce (↑KV : Set T.Vertex)
    KV.card + Fintype.card N.Face = Fintype.card N.Edge + 2 := by
  dsimp only
  let N := T.induce (↑(T.densityComponentVertices U K) : Set T.Vertex)
  have hN := T.densityComponent_connected U K
  let : Nonempty N.Vertex := hN.nonempty
  let : Subsingleton N.Component := hN.preconnected.subsingleton_connectedComponent
  let : Unique N.Component := uniqueOfSubsingleton
    (N.toSimpleGraph.connectedComponentMk (Classical.arbitrary N.Vertex))
  have h := N.global_euler
  rw [show Fintype.card N.Component = 1 from Fintype.card_unique] at h
  have hv : Fintype.card N.Vertex = (T.densityComponentVertices U K).card := by
    simp only [N, induce, inducedRotation, Fintype.card_subtype,
      Finset.mem_coe, Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [hv] at h
  omega

-- @node: SphereMap.inducedFaceClass_eq_of_retained
/-- If [both endpoints of every dart of one original face lie in the retained
vertex set](hyp:hf) and [that face and another original face have the same
induced face class](hyp:he), then [the original faces are equal](goal). -/
lemma inducedFaceClass_eq_of_retained (U : Set T.Vertex) (f g : T.Face)
    (hf : ∀ d, T.faceOf d = f → T.vert d ∈ U ∧ T.head d ∈ U)
    (he : T.inducedFaceClass U f = T.inducedFaceClass U g) : f = g := by
  have step (a b : T.Face) (h : T.inducedFaceRelation U a b) : a = f ↔ b = f := by
    obtain ⟨d, hd, rfl, rfl⟩ := h
    constructor
    · intro he
      exact (hd (hf d he)).elim
    · intro he
      have hi := hf (T.edgeInv d) he
      apply False.elim
      apply hd
      have hi2 := hi.2
      change T.vert (T.edgeInv (T.edgeInv d)) ∈ U at hi2
      rw [T.edgeInv_involutive] at hi2
      exact ⟨hi2, hi.1⟩
  have invariant {a b : T.Face}
      (h : Relation.EqvGen (T.inducedFaceRelation U) a b) : a = f ↔ b = f := by
    induction h with
    | rel a b h => exact step a b h
    | refl => rfl
    | symm a b h ih => exact ih.symm
    | trans a b c h h' ih ih' => exact ih.trans ih'
  exact ((invariant (Quotient.exact he)).mp rfl).symm

-- @node: SphereMap.retained_original_face_card_le
/-- [The number of original faces whose vertices all lie in a retained vertex
set is at most the number of induced face classes](goal). -/
lemma retained_original_face_card_le (U : Finset T.Vertex) :
    (Finset.univ.filter (fun f => T.faceVertices f ⊆ U)).card ≤
      Fintype.card (T.InducedFace (↑U : Set T.Vertex)) := by
  let faces := Finset.univ.filter (fun f => T.faceVertices f ⊆ U)
  have hinj : Function.Injective
      (fun f : faces => T.inducedFaceClass (↑U : Set T.Vertex) f.val) := by
    intro f g he
    apply Subtype.ext
    apply T.inducedFaceClass_eq_of_retained _ f.val g.val ?_ he
    intro d hd
    have hsub := (Finset.mem_filter.mp f.property).2
    have tail (e : T.Dart) : T.vert e ∈ T.faceVertices (T.faceOf e) := by
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, rfl⟩
    refine ⟨hsub (hd ▸ tail d), hsub ?_⟩
    have h := tail (T.facePerm d)
    rw [T.dual_rot_vertex] at h
    have hv : T.vert (T.facePerm d) = T.head d := T.rot_vertex (T.edgeInv d)
    simpa only [hv, hd] using h
  have hc := Fintype.card_le_of_injective _ hinj
  simpa only [faces, Fintype.card_coe] using hc

-- @node: SphereMap.retained_colored_face_card_le
/-- [The number of retained true-colored original faces plus the number of
retained false-colored original faces is at most the number of induced face
classes](goal), where a face is retained when all its vertices lie in the
inducing vertex set. -/
lemma retained_colored_face_card_le (U : Finset T.Vertex) (col : T.Face → Bool) :
    (Finset.univ.filter (fun f => col f = true ∧ T.faceVertices f ⊆ U)).card +
      (Finset.univ.filter (fun f => col f = false ∧ T.faceVertices f ⊆ U)).card ≤
        Fintype.card (T.InducedFace (↑U : Set T.Vertex)) := by
  have h := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun f => T.faceVertices f ⊆ U)) (fun f => col f = true)
  simp only [Finset.filter_filter, Bool.not_eq_true] at h
  have swap (b : Bool) :
      Finset.univ.filter (fun f => col f = b ∧ T.faceVertices f ⊆ U) =
        Finset.univ.filter (fun f => T.faceVertices f ⊆ U ∧ col f = b) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_comm]
  rw [swap true, swap false, h]
  exact T.retained_original_face_card_le U

end SphereMap

end OaiPairedStatesHamiltonian

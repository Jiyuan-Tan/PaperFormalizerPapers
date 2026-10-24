module

public import Papers.OaiPairedStatesHamiltonian.Helpers.InducedCore
public import Papers.OaiPairedStatesHamiltonian.Helpers.GradientRestriction

/-! Counting induced global faces using the orthogonal gradient decomposition.
All original vertices remain during the count; omitted isolated vertices are
removed together with their punctures and components at the final step. -/

@[expose] public section
namespace OaiPairedStatesHamiltonian
namespace SphereMap

set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
open Classical
attribute [local instance] propDecidable
variable (M : SphereMap) (U : Set M.Vertex)

-- @node: SphereMap.globalVertexGradientMap
/-- For [a sphere map](hyp:M), the [global vertex-gradient linear map](goal) sends real
vertex values to the head value minus the tail value along a chosen orientation of each edge. -/
noncomputable def globalVertexGradientMap : (M.Vertex → ℝ) →ₗ[ℝ] (M.Edge → ℝ) where
  toFun a e := M.vertexGradient a (M.edgeRepresentative e)
  map_add' a b := by ext e; simp [RotationSystem.vertexGradient]; ring
  map_smul' c a := by ext e; simp [RotationSystem.vertexGradient]; ring

-- @node: SphereMap.globalFaceGradientMap
/-- For [a sphere map](hyp:M), the [global face-gradient linear map](goal) sends real face
values to their difference across each edge, taking the face of its chosen directed
representative minus the face of the reversed representative. -/
noncomputable def globalFaceGradientMap : (M.Face → ℝ) →ₗ[ℝ] (M.Edge → ℝ) where
  toFun b e := b (M.faceOf (M.edgeRepresentative e)) -
    b (M.faceOf (M.edgeInv (M.edgeRepresentative e)))
  map_add' a b := by ext e; simp; ring
  map_smul' c a := by ext e; simp; ring

-- @node: SphereMap.inducedFacePullback
/-- For [a sphere map](hyp:M) and [a chosen vertex set](hyp:U), the
[face-value pullback](goal) assigns to each original face the value of the merged face
containing it after the other edges are removed. -/
noncomputable def inducedFacePullback :
    (M.InducedFace U → ℝ) →ₗ[ℝ] (M.Face → ℝ) where
  toFun b f := b (M.inducedFaceClass U f)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

-- @node: SphereMap.inducedKeptEdge
/-- For [a sphere map](hyp:M) and [a chosen vertex set](hyp:U), the
[retained edge set](goal) consists of edges whose two endpoints both belong to that set. -/
noncomputable def inducedKeptEdge : Set M.Edge :=
  {e | M.vert (M.edgeRepresentative e) ∈ U ∧ M.head (M.edgeRepresentative e) ∈ U}

-- @node: SphereMap.inducedKeptEdge_dart
/-- [The edge represented by a directed edge is retained exactly when both its tail and
its head belong to the chosen vertex set](goal). -/
lemma inducedKeptEdge_dart (d : M.Dart) :
    M.edgeOf d ∈ M.inducedKeptEdge U ↔ M.vert d ∈ U ∧ M.head d ∈ U := by
  let r := M.edgeRepresentative (M.edgeOf d)
  have hr : M.edgeOf r = M.edgeOf d := M.edgeRepresentative_spec _
  change (M.vert r ∈ U ∧ M.head r ∈ U) ↔ _
  rcases (M.edgeOf_eq_iff r d).mp hr with h | h
  · rw [h]
  · rw [h]
    simp only [head, RotationSystem.head]
    rw [M.edgeInv_involutive r]
    exact and_comm

-- @node: SphereMap.induced_keptEdgeEquiv
/-- For [a sphere map](hyp:M) and [a chosen vertex set](hyp:U), the
[retained-edge correspondence](goal) is a bijection between edges of the induced rotation
system and original edges having both endpoints in the chosen set. -/
noncomputable def induced_keptEdgeEquiv :
    (M.inducedRotation U).Edge ≃ M.inducedKeptEdge U := by
  let f : (M.inducedRotation U).Edge → M.Edge :=
    Quotient.map Subtype.val (fun {d e} h => (M.inducedInv_sameCycle_iff U d e).mp h)
  have hf (e : (M.inducedRotation U).Edge) : f e ∈ M.inducedKeptEdge U := by
    induction e using Quotient.inductionOn with
    | h d => exact (M.inducedKeptEdge_dart U d.val).mpr d.property
  apply Equiv.ofBijective (fun e => (⟨f e, hf e⟩ : M.inducedKeptEdge U))
  constructor
  · intro e k h
    have h := congrArg Subtype.val h
    induction e using Quotient.inductionOn with
    | h d =>
      induction k using Quotient.inductionOn with
      | h e => exact Quotient.sound ((M.inducedInv_sameCycle_iff U d e).mpr (Quotient.exact h))
  · intro e
    let d := M.edgeRepresentative e.val
    have hd : M.vert d ∈ U ∧ M.head d ∈ U := e.property
    exact ⟨orbitOf (M.inducedInv U) ⟨d, hd⟩, Subtype.ext (M.edgeRepresentative_spec _)⟩

-- @node: SphereMap.inducedGradientMap
/-- For [a sphere map](hyp:M) and [a chosen vertex set](hyp:U), the
[induced mixed-gradient linear map](goal) adds the vertex gradient to the gradient of
pulled-back merged-face values and restricts the result to retained edges. -/
noncomputable def inducedGradientMap :
    ((M.Vertex → ℝ) × (M.InducedFace U → ℝ)) →ₗ[ℝ] (M.inducedKeptEdge U → ℝ) :=
  restrictedGradientMap M.globalVertexGradientMap M.globalFaceGradientMap
    (M.inducedFacePullback U) (M.inducedKeptEdge U)

-- @node: SphereMap.inducedFacePullback_factor
/-- If [real face values have zero face gradient on every removed edge](hyp:hb), then
[they are the pullback of some values on the merged faces of the induced map](goal). -/
lemma inducedFacePullback_factor (b : M.Face → ℝ)
    (hb : ∀ e, e ∉ M.inducedKeptEdge U → M.globalFaceGradientMap b e = 0) :
    ∃ c, M.inducedFacePullback U c = b := by
  have across (d : M.Dart) (hd : ¬ (M.vert d ∈ U ∧ M.head d ∈ U)) :
      b (M.faceOf d) = b (M.faceOf (M.edgeInv d)) := by
    have he : M.edgeOf d ∉ M.inducedKeptEdge U :=
      fun h => hd ((M.inducedKeptEdge_dart U d).mp h)
    have hz := hb (M.edgeOf d) he
    let r := M.edgeRepresentative (M.edgeOf d)
    have hr : M.edgeOf r = M.edgeOf d := M.edgeRepresentative_spec _
    change b (M.faceOf r) - b (M.faceOf (M.edgeInv r)) = 0 at hz
    rcases (M.edgeOf_eq_iff r d).mp hr with h | h
    · exact (congrArg (fun d => b (M.faceOf d)) h).trans
        ((sub_eq_zero.mp hz).trans (congrArg (fun d => b (M.faceOf (M.edgeInv d))) h).symm)
    · rw [h, M.edgeInv_involutive]
      exact (sub_eq_zero.mp hz).symm
  have invariant (f g : M.Face) (h : Relation.EqvGen (M.inducedFaceRelation U) f g) :
      b f = b g := by
    induction h with
    | rel f g h => obtain ⟨d, hd, rfl, rfl⟩ := h; exact across d hd
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih jk => exact ih.trans jk
  exact ⟨Quotient.lift b invariant, rfl⟩

-- @node: SphereMap.inducedGradientMap_surjective
/-- [Every assignment of real values to retained edges is the sum of a vertex gradient
and a pulled-back merged-face gradient on those edges](goal). -/
lemma inducedGradientMap_surjective : Function.Surjective (M.inducedGradientMap U) := by
  apply restrictedGradientMap_surjective
  · intro z
    obtain ⟨x, hx⟩ := M.globalMixedGradient_surjective z
    exact ⟨x.1, x.2, hx.symm⟩
  · intro a b
    exact M.edgeGradients_orthogonal a (fun f => b (M.boundaryFace (Sum.inl f)))
  · exact M.inducedFacePullback_factor U

-- @node: SphereMap.inducedFullRotation
/-- For [a sphere map](hyp:M) and [a chosen vertex set](hyp:U), the
[full-vertex induced rotation system](goal) keeps all original vertices but retains only
directed edges whose two endpoints lie in the chosen set. -/
noncomputable def inducedFullRotation : RotationSystem :=
  M.toRotationSystem.restrictDarts {d | M.vert d ∈ U ∧ M.head d ∈ U} (by
    intro d
    change (M.vert (M.edgeInv d) ∈ U ∧ M.vert (M.edgeInv (M.edgeInv d)) ∈ U) ↔
      (M.vert d ∈ U ∧ M.vert (M.edgeInv d) ∈ U)
    rw [M.edgeInv_involutive d]
    exact and_comm)

-- @node: SphereMap.inducedGradientMap_ker_constants
/-- If [a pair of vertex values and merged-face values has zero induced mixed
gradient](hyp:hx), then [the vertex values are constant within each connected component
of the full-vertex induced rotation system, and the merged-face values are constant
across all merged faces](goal). -/
lemma inducedGradientMap_ker_constants
    (x : (M.Vertex → ℝ) × (M.InducedFace U → ℝ)) (hx : M.inducedGradientMap U x = 0) :
    (∀ u v, (M.inducedFullRotation U).toSimpleGraph.connectedComponentMk u =
      (M.inducedFullRotation U).toSimpleGraph.connectedComponentMk v → x.1 u = x.1 v) ∧
    (∀ f g, x.2 f = x.2 g) := by
  let a := x.1
  let b := M.inducedFacePullback U x.2
  let A := M.globalVertexGradientMap
  let B := M.globalFaceGradientMap
  have hboutside (e : M.Edge) (he : e ∉ M.inducedKeptEdge U) : B b e = 0 := by
    let d := M.edgeRepresentative e
    have hd : ¬ (M.vert d ∈ U ∧ M.head d ∈ U) := he
    have hf : M.inducedFaceClass U (M.faceOf d) =
        M.inducedFaceClass U (M.faceOf (M.edgeInv d)) :=
      Quotient.sound (Relation.EqvGen.rel _ _ ⟨d, hd, rfl, rfl⟩)
    change x.2 (M.inducedFaceClass U (M.faceOf d)) -
      x.2 (M.inducedFaceClass U (M.faceOf (M.edgeInv d))) = 0
    rw [hf, sub_self]
  have hab (e : M.Edge) (he : e ∈ M.inducedKeptEdge U) : A a e + B b e = 0 :=
    congrFun hx ⟨e, he⟩
  have horth : (∑ e, A a e * B b e) = 0 :=
    M.edgeGradients_orthogonal a (fun f => b (M.boundaryFace (Sum.inl f)))
  have hterm (e : M.Edge) : A a e * B b e = -(B b e) ^ 2 := by
    by_cases he : e ∈ M.inducedKeptEdge U
    · have h := hab e he
      rw [show A a e = -B b e by linarith]
      ring
    · rw [hboutside e he]
      ring
  have hsq : (∑ e, (B b e) ^ 2) = 0 := by
    simp_rw [hterm] at horth
    rw [Finset.sum_neg_distrib] at horth
    exact neg_eq_zero.mp horth
  have hB : B b = 0 := by
    ext e
    exact sq_eq_zero_iff.mp
      ((Finset.sum_eq_zero_iff_of_nonneg (fun e _ => sq_nonneg (B b e))).mp hsq e
        (Finset.mem_univ _))
  have hA (e : M.Edge) (he : e ∈ M.inducedKeptEdge U) : A a e = 0 := by
    simpa only [hB, Pi.zero_apply, add_zero] using hab e he
  have hv (d : (M.inducedFullRotation U).Dart) :
      (M.inducedFullRotation U).vertexGradient a d = 0 := by
    have he := hA (M.edgeOf d.val) ((M.inducedKeptEdge_dart U d.val).mpr d.property)
    let r := M.edgeRepresentative (M.edgeOf d.val)
    change M.vertexGradient a r = 0 at he
    change M.vertexGradient a d.val = 0
    rcases (M.edgeOf_eq_iff r d.val).mp (M.edgeRepresentative_spec _) with h | h
    · exact (congrArg (M.vertexGradient a) h).trans he
    · rw [h, M.vertexGradient_inv, he, neg_zero]
  have hb : ∀ d, M.facialGradient (fun f => b (M.boundaryFace (Sum.inl f))) d = 0 := by
    have hz : M.mixedGradient (0, fun f => b (M.boundaryFace (Sum.inl f))) = 0 := by
      ext e
      simpa only [RotationSystem.mixedGradient, RotationSystem.vertexGradient,
        RotationSystem.facialGradient, LinearMap.coe_mk, AddHom.coe_mk,
        Pi.zero_apply, sub_self, zero_add, B, globalFaceGradientMap, faceOf] using congrFun hB e
    exact (M.mixedGradient_ker_gradients_zero _ hz).2
  refine ⟨(M.inducedFullRotation U).vertexGradient_zero_sameComponent a hv, ?_⟩
  intro f g
  obtain ⟨f, rfl⟩ := Quotient.exists_rep f
  obtain ⟨g, rfl⟩ := Quotient.exists_rep g
  exact M.globalFacialGradient_zero_constant b hb f g

-- @node: SphereMap.inducedGradientMap_kernel_finrank
/-- [The real dimension of the kernel of the induced mixed-gradient map equals the
number of connected components of the full-vertex induced rotation system plus one](goal). -/
lemma inducedGradientMap_kernel_finrank :
    Module.finrank ℝ (LinearMap.ker (M.inducedGradientMap U)) =
      Fintype.card (M.inducedFullRotation U).Component + 1 := by
  let Q := M.inducedFullRotation U
  let f0 : M.InducedFace U := M.inducedFaceClass U (Classical.choice M.face_nonempty)
  let ev : LinearMap.ker (M.inducedGradientMap U) →ₗ[ℝ] ((Q.Component → ℝ) × ℝ) :=
    { toFun := fun x => (fun K => x.val.1 (Q.componentVertexRepresentative K), x.val.2 f0)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective ev := by
    intro x y he
    have hx := M.inducedGradientMap_ker_constants U x.val x.property
    have hy := M.inducedGradientMap_ker_constants U y.val y.property
    apply Subtype.ext
    apply Prod.ext
    · funext v
      let K := Q.toSimpleGraph.connectedComponentMk v
      have hK : Q.toSimpleGraph.connectedComponentMk v =
          Q.toSimpleGraph.connectedComponentMk (Q.componentVertexRepresentative K) :=
        (Q.componentVertexRepresentative_spec K).symm
      exact (hx.1 _ _ hK).trans ((congrFun (congrArg Prod.fst he) K).trans (hy.1 _ _ hK).symm)
    · funext f
      exact (hx.2 f f0).trans ((congrArg Prod.snd he).trans (hy.2 f0 f))
  have hsurj : Function.Surjective ev := by
    rintro ⟨c, r⟩
    let x : (M.Vertex → ℝ) × (M.InducedFace U → ℝ) :=
      (fun v => c (Q.toSimpleGraph.connectedComponentMk v), fun _ => r)
    have hx : M.inducedGradientMap U x = 0 := by
      ext e
      let d : Q.Dart := ⟨M.edgeRepresentative e.val, e.property⟩
      have hc := Q.dart_component_eq_head d
      change c (Q.toSimpleGraph.connectedComponentMk (Q.head d)) -
        c (Q.toSimpleGraph.connectedComponentMk (Q.vert d)) + (r - r) = 0
      rw [hc]
      ring
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Prod.ext
    · funext K
      exact congrArg c (Q.componentVertexRepresentative_spec K)
    · rfl
  have h := (LinearEquiv.ofBijective ev ⟨hinj, hsurj⟩).finrank_eq
  simpa only [Module.finrank_prod, Module.finrank_pi, Module.finrank_self] using h

-- @node: SphereMap.induced_full_global_euler
/-- [The number of original vertices plus the number of merged induced faces equals
the number of retained edges plus one plus the number of connected components when
all original vertices are kept](goal). -/
lemma induced_full_global_euler :
    Nat.card M.Vertex + Nat.card (M.InducedFace U) =
      Nat.card (M.inducedRotation U).Edge + 1 + Nat.card (M.inducedFullRotation U).Component := by
  have hn := LinearMap.finrank_range_add_finrank_ker (M.inducedGradientMap U)
  have hr := LinearMap.range_eq_top.mpr (M.inducedGradientMap_surjective U)
  rw [hr, finrank_top, M.inducedGradientMap_kernel_finrank U] at hn
  simp only [Module.finrank_prod, Module.finrank_pi] at hn
  have he := Nat.card_congr (M.induced_keptEdgeEquiv U)
  simp only [Nat.card_eq_fintype_card] at he ⊢
  omega

-- @node: SphereMap.inducedFullRotation_component_card
/-- [The number of connected components when all original vertices are kept equals
the number of components of the induced rotation system plus the number of vertices
outside the chosen set](goal). -/
lemma inducedFullRotation_component_card :
    Nat.card (M.inducedFullRotation U).Component =
      Nat.card (M.inducedRotation U).Component + Nat.card {v : M.Vertex // v ∉ U} := by
  let Q := M.inducedFullRotation U
  have tails (d : Q.Dart) : Q.vert d ∈ U := d.property.1
  let N := Q.restrictVertices U tails
  let e : N.Relabel (M.inducedRotation U) :=
    { vertex := Equiv.refl _
      dart := Equiv.refl _
      vert := fun _ => rfl
      inv := by
        intro d
        apply Subtype.ext
        exact (Classical.choose_spec (M.exists_inducedInv U) d).symm
      rot := fun _ => rfl }
  have hc := Nat.card_congr (Q.restrictVertices_componentEquiv U tails)
  rw [Nat.card_sum] at hc
  have he := Nat.card_congr e.graphIso.connectedComponentEquiv
  change Nat.card Q.Component = Nat.card N.Component + Nat.card {v : M.Vertex // v ∉ U} at hc
  rw [he] at hc
  exact hc

-- @node: SphereMap.induced_placement_card
/-- [The number of connected components of the induced rotation system plus the number
of merged induced faces equals the number of its local boundaries plus one](goal). -/
lemma induced_placement_card :
    Nat.card ((M.inducedRotation U).Component ⊕ M.InducedFace U) =
      Nat.card (M.inducedRotation U).LocalBoundary + 1 := by
  have hfull := M.induced_full_global_euler U
  have hcomp := M.inducedFullRotation_component_card U
  have hvertex := Nat.card_congr (Equiv.sumCompl (fun v : M.Vertex => v ∈ U))
  have heuler := (M.inducedRotation U).componentEuler_global_card (M.induced_genus U)
  rw [Nat.card_sum] at hvertex ⊢
  change Nat.card (M.inducedRotation U).Vertex + Nat.card {v : M.Vertex // v ∉ U} =
    Nat.card M.Vertex at hvertex
  omega

end SphereMap
end OaiPairedStatesHamiltonian

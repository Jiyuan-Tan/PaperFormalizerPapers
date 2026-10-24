module

public import Papers.OaiPairedStatesHamiltonian.Helpers.SphereMaps
public import Mathlib.Combinatorics.SimpleGraph.Maps

/-! Dual rotation systems and their sphere placements. -/

@[expose] public section

namespace OaiPairedStatesHamiltonian

set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
open Classical
attribute [local instance] propDecidable


namespace SphereMap
variable (M : SphereMap)

-- @node: SphereMap.dual_rot_vertex
/-- For any directed edge, [advancing once around its facial boundary preserves its incident face](goal). -/
lemma dual_rot_vertex (d : M.Dart) : M.faceOf (M.facePerm d) = M.faceOf d := by
  apply congrArg (fun o => M.boundaryFace (Sum.inl o))
  exact Quotient.sound (Equiv.Perm.sameCycle_apply_left.mpr
    (Equiv.Perm.SameCycle.refl M.facePerm d))
-- @node: SphereMap.dual_rot_fibre
/-- In a [connected sphere map](hyp:hM), [the facial successor permutation acts as a single cycle on the directed edges incident to any given face](goal). -/
lemma dual_rot_fibre (hM : M.IsConnectedMap) (f : M.Face) :
    M.facePerm.IsCycleOn {d | M.faceOf d = f} := by
  refine ⟨⟨?_, M.facePerm.injective.injOn, ?_⟩, ?_⟩
  · intro d hd
    exact (M.dual_rot_vertex d).trans hd
  · intro d hd
    refine ⟨M.facePerm.symm d, ?_, M.facePerm.apply_symm_apply d⟩
    change M.faceOf (M.facePerm.symm d) = f
    rw [← M.dual_rot_vertex (M.facePerm.symm d), M.facePerm.apply_symm_apply]
    exact hd
  · intro d hd e he
    letI : Nonempty M.Dart := ⟨d⟩
    have hq := Classical.choose_spec (M.exists_faceEquivOrbit hM)
    apply Quotient.exact (s := Equiv.Perm.SameCycle.setoid M.facePerm)
    change orbitOf M.facePerm d = orbitOf M.facePerm e
    change M.faceOf d = f at hd
    change M.faceOf e = f at he
    rw [← hq d, ← hq e, hd, he]

/-- For [a sphere map](hyp:M) that is [connected](hyp:hM), the [dual rotation system](goal) uses primal faces as vertices, retains the primal darts and edge reversal, and rotates darts by the primal facial successor permutation. -/
noncomputable def dualRotation (hM : M.IsConnectedMap) : RotationSystem where
  Vertex := M.Face -- @realizes M^*(dual vertices are actual primal faces)
    -- @realizes G^*(same dual construction for the embedding of G)
  Dart := M.Dart
  vert := M.faceOf
  edgeInv := M.edgeInv
  edgeInv_involutive := M.edgeInv_involutive
  edgeInv_fixedPointFree := M.edgeInv_fixedPointFree
  rot := M.facePerm
  rot_vertex := M.dual_rot_vertex
  rot_fibre := M.dual_rot_fibre hM

/-- For [a sphere map](hyp:M) that is [connected](hyp:hM) and [a directed edge](hyp:d), the [dual face at that directed edge](goal) is its primal tail vertex. -/
noncomputable def dualFaceAt (hM : M.IsConnectedMap) (d : M.Dart) : M.Vertex := M.vert d
-- @node: SphereMap.dual_facePerm_vertex
/-- In a [connected sphere map](hyp:hM), [advancing a directed edge by the dual facial successor preserves its primal tail vertex](goal). -/
lemma dual_facePerm_vertex (hM : M.IsConnectedMap) (d : M.Dart) :
    M.vert ((M.dualRotation hM).facePerm d) = M.vert d := by
  change M.vert (M.rot (M.edgeInv (M.edgeInv d))) = M.vert d
  rw [M.edgeInv_involutive, M.rot_vertex]

-- @node: SphereMap.exists_dualBoundaryFace
/-- For a [connected sphere map](hyp:hM), [there exists a placement of dual local boundaries at primal vertices that sends each dart's facial orbit to its primal tail and sends every dual puncture to every primal vertex](goal). -/
lemma exists_dualBoundaryFace (hM : M.IsConnectedMap) :
    ∃ place : (M.dualRotation hM).LocalBoundary → M.Vertex,
      (∀ d, place (Sum.inl (orbitOf (M.dualRotation hM).facePerm d)) = M.dualFaceAt hM d) ∧
      (∀ v : (M.dualRotation hM).Puncture, ∀ w : M.Vertex, place (Sum.inr v) = w) := by
  let : Nonempty M.Vertex := hM.nonempty
  have invariant (d e : M.Dart)
      (h : (M.dualRotation hM).facePerm.SameCycle d e) : M.vert d = M.vert e := by
    obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    clear h
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ']
      change M.vert d = M.vert ((M.dualRotation hM).facePerm
        (((M.dualRotation hM).facePerm ^ n) d))
      exact ih.trans (M.dual_facePerm_vertex hM _).symm
  let place : (M.dualRotation hM).LocalBoundary → M.Vertex := Sum.elim
    (Quotient.lift M.vert invariant) (fun _ => Classical.arbitrary M.Vertex)
  refine ⟨place, fun _ => rfl, ?_⟩
  intro v w
  have no_dart (d : M.Dart) : False := by
    let : Nonempty M.Dart := ⟨d⟩
    obtain ⟨q, hq⟩ := M.exists_faceEquivOrbit hM
    obtain ⟨e, he⟩ := Quotient.exists_rep (q v.val)
    have hface : M.faceOf e = v.val := q.injective ((hq e).trans he)
    exact v.property e hface
  by_contra hne
  obtain ⟨p⟩ := hM.preconnected (place (Sum.inr v)) w
  obtain ⟨_, d, _, _⟩ := p.adj_snd (p.not_nil_of_ne hne)
  exact no_dart d
/-- For [a sphere map](hyp:M) that is [connected](hyp:hM), the [dual boundary placement](goal) is a chosen map from dual local boundaries to primal vertices, sending each dart's facial orbit to its primal tail and every dual puncture to the unique primal vertex in that case. -/
noncomputable def dualBoundaryFace (hM : M.IsConnectedMap) :
    (M.dualRotation hM).LocalBoundary → M.Vertex :=
  Classical.choose (M.exists_dualBoundaryFace hM)
-- @node: SphereMap.dualBoundaryFace_dart
/-- In a [connected sphere map](hyp:hM), [the dual boundary placement sends the dual facial orbit of any directed edge to its primal tail vertex](goal). -/
lemma dualBoundaryFace_dart (hM : M.IsConnectedMap) (d : M.Dart) :
    M.dualBoundaryFace hM (Sum.inl (orbitOf (M.dualRotation hM).facePerm d)) = M.vert d := by
  exact (Classical.choose_spec (M.exists_dualBoundaryFace hM)).1 d

-- @node: SphereMap.dualPlacement_dart_adj
/-- In a [connected sphere map](hyp:hM), [the dual placement graph joins the dual component containing a directed edge's primal face to that edge's primal tail vertex](goal). -/
lemma dualPlacement_dart_adj (hM : M.IsConnectedMap) (d : M.Dart) :
    ((M.dualRotation hM).placementGraph M.Vertex (M.dualBoundaryFace hM)).Adj
      (Sum.inl ((M.dualRotation hM).toSimpleGraph.connectedComponentMk (M.faceOf d)))
      (Sum.inr (M.vert d)) := by
  exact ⟨Sum.inl (orbitOf (M.dualRotation hM).facePerm d), rfl,
    M.dualBoundaryFace_dart hM d⟩

-- @node: SphereMap.dualPlacement_primal_reachable
/-- For a [connected sphere map](hyp:hM), [any two primal vertices are joined by a path in the dual placement graph](goal). -/
lemma dualPlacement_primal_reachable (hM : M.IsConnectedMap) (u v : M.Vertex) :
    ((M.dualRotation hM).placementGraph M.Vertex (M.dualBoundaryFace hM)).Reachable
      (Sum.inr u) (Sum.inr v) := by
  obtain ⟨p⟩ := hM.preconnected u v
  induction p with
  | nil => exact .rfl
  | @cons u w v huw p ih =>
    obtain ⟨hne, d, rfl, rfl⟩ := huw
    have he : (M.dualRotation hM).toSimpleGraph.connectedComponentMk (M.faceOf d) =
        (M.dualRotation hM).toSimpleGraph.connectedComponentMk (M.faceOf (M.edgeInv d)) := by
      by_cases h : M.faceOf d = M.faceOf (M.edgeInv d)
      · exact congrArg (M.dualRotation hM).toSimpleGraph.connectedComponentMk h
      · exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
          (G := (M.dualRotation hM).toSimpleGraph) ⟨h, d, rfl, rfl⟩
    have ha := M.dualPlacement_dart_adj hM d
    have hb := M.dualPlacement_dart_adj hM (M.edgeInv d)
    rw [← he] at hb
    exact (ha.symm.reachable.trans hb.reachable).trans ih

-- @node: SphereMap.dual_placement_connected
/-- For a [connected sphere map](hyp:hM), [the dual placement graph is connected](goal). -/
lemma dual_placement_connected (hM : M.IsConnectedMap) :
    ((M.dualRotation hM).placementGraph M.Vertex (M.dualBoundaryFace hM)).Connected := by
  let : Nonempty M.Vertex := hM.nonempty
  let G := (M.dualRotation hM).placementGraph M.Vertex (M.dualBoundaryFace hM)
  let v : M.Vertex := Classical.arbitrary M.Vertex
  have reaches : ∀ x, G.Reachable (Sum.inr v) x := by
    intro x
    cases x with
    | inr w => exact M.dualPlacement_primal_reachable hM v w
    | inl K =>
      obtain ⟨f, rfl⟩ := K.exists_rep
      have boundary : ∃ b : (M.dualRotation hM).LocalBoundary,
          (M.dualRotation hM).compOf b =
            (M.dualRotation hM).toSimpleGraph.connectedComponentMk f := by
        by_cases hf : ∃ d, M.faceOf d = f
        · obtain ⟨d, hd⟩ := hf
          exact ⟨Sum.inl (orbitOf (M.dualRotation hM).facePerm d),
            congrArg (M.dualRotation hM).toSimpleGraph.connectedComponentMk hd⟩
        · exact ⟨Sum.inr ⟨f, fun d hd => hf ⟨d, hd⟩⟩, rfl⟩
      obtain ⟨b, hb⟩ := boundary
      have ha : G.Adj
          (Sum.inl ((M.dualRotation hM).toSimpleGraph.connectedComponentMk f))
          (Sum.inr (M.dualBoundaryFace hM b)) := ⟨b, hb, rfl⟩
      exact (M.dualPlacement_primal_reachable hM v _).trans ha.symm.reachable
  exact ⟨fun x y => (reaches x).symm.trans (reaches y)⟩
-- @node: SphereMap.dual_facePerm_eq
/-- For a [connected sphere map](hyp:hM), [the dual facial successor permutation equals the primal vertex rotation permutation](goal). -/
lemma dual_facePerm_eq (hM : M.IsConnectedMap) : (M.dualRotation hM).facePerm = M.rot := by
  ext d
  change M.rot (M.edgeInv (M.edgeInv d)) = M.rot d
  exact congrArg M.rot (M.edgeInv_involutive d)

-- @node: SphereMap.faceOf_surjective
/-- In a [connected sphere map](hyp:hM) with at least one directed edge, [every face is incident to some directed edge](goal). -/
lemma faceOf_surjective (hM : M.IsConnectedMap) [Nonempty M.Dart] :
    Function.Surjective M.faceOf := by
  obtain ⟨q, hq⟩ := M.exists_faceEquivOrbit hM
  intro f
  obtain ⟨d, hd⟩ := Quotient.exists_rep (q f)
  exact ⟨d, q.injective ((hq d).trans hd)⟩

-- @node: SphereMap.vertex_subsingleton_of_no_darts
/-- In a [connected sphere map](hyp:hM) with no directed edges, [any two vertices are equal](goal). -/
lemma vertex_subsingleton_of_no_darts (hM : M.IsConnectedMap) [IsEmpty M.Dart] :
    Subsingleton M.Vertex := by
  refine ⟨fun u v => ?_⟩
  by_contra hne
  obtain ⟨p⟩ := hM.preconnected u v
  obtain ⟨_, d, _, _⟩ := p.adj_snd (p.not_nil_of_ne hne)
  exact isEmptyElim d

-- @node: SphereMap.face_subsingleton_of_no_darts
/-- In a [connected sphere map](hyp:hM) with no directed edges, [any two faces are equal](goal). -/
lemma face_subsingleton_of_no_darts (hM : M.IsConnectedMap) [IsEmpty M.Dart] :
    Subsingleton M.Face := by
  let : Subsingleton M.Vertex := M.vertex_subsingleton_of_no_darts hM
  obtain ⟨q, hq⟩ := M.exists_faceEquivBoundary hM
  have no_orbit (o : M.FaceOrbit) : False := by
    obtain ⟨d, _⟩ := Quotient.exists_rep o
    exact isEmptyElim d
  have heq (b c : M.LocalBoundary) : b = c := by
    cases b with
    | inl o => exact (no_orbit o).elim
    | inr v =>
      cases c with
      | inl o => exact (no_orbit o).elim
      | inr w => exact congrArg Sum.inr (Subtype.ext (Subsingleton.elim _ _))
  exact ⟨fun f g => q.injective (heq _ _)⟩

set_option backward.isDefEq.respectTransparency false in
-- @node: SphereMap.dualBoundaryFace_bijective
/-- For a [connected sphere map](hyp:hM), [the dual boundary placement is a bijection between dual local boundaries and primal vertices](goal). -/
lemma dualBoundaryFace_bijective (hM : M.IsConnectedMap) :
    Function.Bijective (M.dualBoundaryFace hM) := by
  constructor
  · intro b c hbc
    cases b with
    | inl o =>
      obtain ⟨d, rfl⟩ := Quotient.exists_rep o
      cases c with
      | inl p =>
        obtain ⟨e, rfl⟩ := Quotient.exists_rep p
        have hv : M.vert d = M.vert e :=
          (M.dualBoundaryFace_dart hM d).symm.trans
            (hbc.trans (M.dualBoundaryFace_dart hM e))
        apply congrArg Sum.inl
        apply Quotient.sound
        rw [M.dual_facePerm_eq hM]
        exact (M.rot_fibre (M.vert d)).2 rfl hv.symm
      | inr f =>
        let : Nonempty M.Dart := ⟨d⟩
        obtain ⟨e, he⟩ := M.faceOf_surjective hM f.val
        exact (f.property e he).elim
    | inr f =>
      cases c with
      | inl o =>
        obtain ⟨d, _⟩ := Quotient.exists_rep o
        let : Nonempty M.Dart := ⟨d⟩
        obtain ⟨e, he⟩ := M.faceOf_surjective hM f.val
        exact (f.property e he).elim
      | inr g =>
        have hn (d : M.Dart) : False := by
          let : Nonempty M.Dart := ⟨d⟩
          obtain ⟨e, he⟩ := M.faceOf_surjective hM f.val
          exact f.property e he
        let : IsEmpty M.Dart := ⟨hn⟩
        let : Subsingleton M.Face := M.face_subsingleton_of_no_darts hM
        exact congrArg Sum.inr (Subtype.ext (Subsingleton.elim (α := M.Face) f.val g.val))
  · intro v
    by_cases hv : ∃ d, M.vert d = v
    · obtain ⟨d, hd⟩ := hv
      exact ⟨Sum.inl (orbitOf (M.dualRotation hM).facePerm d),
        (M.dualBoundaryFace_dart hM d).trans hd⟩
    · have hn (d : M.Dart) : False := by
        by_cases he : v = M.vert d
        · exact hv ⟨d, he.symm⟩
        · obtain ⟨p⟩ := hM.preconnected v (M.vert d)
          obtain ⟨_, e, he, _⟩ := p.adj_snd (p.not_nil_of_ne he)
          exact hv ⟨e, he⟩
      let : Nonempty M.Vertex := hM.nonempty
      obtain ⟨q, hq⟩ := M.exists_faceEquivBoundary hM
      let f := q.symm (Sum.inr ⟨v, fun d hd => hv ⟨d, hd⟩⟩)
      let p : (M.dualRotation hM).Puncture := ⟨f, fun d _ => hn d⟩
      exact ⟨Sum.inr p, (Classical.choose_spec (M.exists_dualBoundaryFace hM)).2 p v⟩

-- @node: SphereMap.dual_component_subsingleton
/-- For a [connected sphere map](hyp:hM), [any two connected components of its dual rotation system are equal](goal). -/
lemma dual_component_subsingleton (hM : M.IsConnectedMap) :
    Subsingleton (M.dualRotation hM).Component := by
  let R := M.dualRotation hM
  let q := Equiv.ofBijective (M.dualBoundaryFace hM) (M.dualBoundaryFace_bijective hM)
  let label : R.Component ⊕ M.Vertex → R.Component :=
    Sum.elim id (fun v => R.compOf (q.symm v))
  have step {x y} (h : (R.placementGraph M.Vertex (M.dualBoundaryFace hM)).Adj x y) :
      label x = label y := by
    cases x with
    | inl K =>
      cases y with
      | inl L => exact False.elim h
      | inr v =>
        obtain ⟨b, hb, hv⟩ := h
        change K = R.compOf (q.symm v)
        rw [← hv]
        change K = R.compOf (q.symm (q b))
        rw [q.symm_apply_apply]
        exact hb.symm
    | inr v =>
      cases y with
      | inr w => exact False.elim h
      | inl K =>
        obtain ⟨b, hb, hv⟩ := h
        change R.compOf (q.symm v) = K
        rw [← hv]
        change R.compOf (q.symm (q b)) = K
        rw [q.symm_apply_apply]
        exact hb
  refine ⟨fun K L => ?_⟩
  obtain ⟨p⟩ := (M.dual_placement_connected hM).preconnected (Sum.inl K) (Sum.inl L)
  have invariant {x y} (p : (R.placementGraph M.Vertex (M.dualBoundaryFace hM)).Walk x y) :
      label x = label y := by
    induction p with
    | nil => rfl
    | cons h p ih => exact (step h).trans ih
  exact invariant p

-- @node: SphereMap.dual_component_card
/-- For a [connected sphere map](hyp:hM), [the dual rotation system has exactly one connected component](goal). -/
lemma dual_component_card (hM : M.IsConnectedMap) :
    Fintype.card (M.dualRotation hM).Component = 1 := by
  let : Nonempty M.Vertex := hM.nonempty
  obtain ⟨b, hb⟩ := (M.dualBoundaryFace_bijective hM).2 (Classical.arbitrary M.Vertex)
  let : Subsingleton (M.dualRotation hM).Component := M.dual_component_subsingleton hM
  let : Unique (M.dualRotation hM).Component := uniqueOfSubsingleton ((M.dualRotation hM).compOf b)
  exact Fintype.card_unique

-- @node: SphereMap.dual_placement_card
/-- For a [connected sphere map](hyp:hM), [the total number of dual components and primal vertices equals the number of dual local boundaries plus one](goal). -/
lemma dual_placement_card (hM : M.IsConnectedMap) :
    Nat.card ((M.dualRotation hM).Component ⊕ M.Vertex) =
      Nat.card (M.dualRotation hM).LocalBoundary + 1 := by
  have hb := Fintype.card_congr
    (Equiv.ofBijective (M.dualBoundaryFace hM) (M.dualBoundaryFace_bijective hM))
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_sum,
    M.dual_component_card hM, hb, Nat.add_comm]

-- @node: SphereMap.dual_genus
/-- For a [connected sphere map](hyp:hM), [each component of the dual rotation system satisfies the genus-zero Euler identity: its vertex count plus local-boundary count equals its edge count plus two](goal). -/
lemma dual_genus (hM : M.IsConnectedMap) : (M.dualRotation hM).componentEuler := by
  let : Nonempty M.Vertex := hM.nonempty
  let : Subsingleton M.Component := hM.preconnected.subsingleton_connectedComponent
  let : Unique M.Component := uniqueOfSubsingleton
    (M.toSimpleGraph.connectedComponentMk (Classical.arbitrary M.Vertex))
  have hc : Fintype.card M.Component = 1 := Fintype.card_unique
  have he := M.global_euler
  rw [hc] at he
  let R := M.dualRotation hM
  let : Subsingleton R.Component := M.dual_component_subsingleton hM
  intro K
  have fibre_card {α : Type} [Fintype α] (f : α → R.Component) :
      Fintype.card {a // f a = K} = Fintype.card α := by
    have h (a : α) : f a = K := Subsingleton.elim _ _
    simp [Fintype.card_subtype, h]
  change Fintype.card {v : R.Vertex // R.toSimpleGraph.connectedComponentMk v = K} +
    Fintype.card {b : R.LocalBoundary // R.compOf b = K} =
      Fintype.card {e : R.Edge // R.edgeComponent e = K} + 2
  rw [fibre_card, fibre_card, fibre_card]
  have hb := Fintype.card_congr
    (Equiv.ofBijective (M.dualBoundaryFace hM) (M.dualBoundaryFace_bijective hM))
  change Fintype.card M.Face + Fintype.card R.LocalBoundary = Fintype.card M.Edge + 2
  rw [hb]
  omega

/-- For [a sphere map](hyp:M) that is [connected](hyp:hM), the [dual sphere map](goal) uses primal faces as vertices and primal vertices as faces, retains darts and edges, and uses the dual rotation and boundary placement. -/
noncomputable def dual (hM : M.IsConnectedMap) : SphereMap where
  toRotationSystem := M.dualRotation hM
  genusZero := M.dual_genus hM
  Face := M.Vertex
  boundaryFace := M.dualBoundaryFace hM
  placement_connected := M.dual_placement_connected hM
  placement_card := M.dual_placement_card hM

/-- For [a sphere map](hyp:M) that is [connected](hyp:hM) and [a primal edge](hyp:e), the [corresponding dual edge](goal) is that same edge viewed in the dual sphere map. -/
noncomputable def dualEdge (hM : M.IsConnectedMap) (e : M.Edge) : (M.dual hM).Edge := e
  -- @realizes e^*(the prescribed primal edge retains its identity in the dual)

end SphereMap

end OaiPairedStatesHamiltonian

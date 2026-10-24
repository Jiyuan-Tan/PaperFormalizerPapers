module

public import Papers.OaiPairedStatesHamiltonian.Helpers.GraphClasses
public import Papers.OaiPairedStatesHamiltonian.Helpers.Duality

/-! Small edge cuts and the colored dual triangulation of a main-domain graph. -/

@[expose] public section

namespace OaiPairedStatesHamiltonian

set_option linter.style.openClassical false
open Classical
attribute [local instance] propDecidable

variable {V : Type} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-- For [a finite simple graph](hyp:G) and [a set of vertices chosen as one side of a cut](hyp:S),
[the cut darts](goal) are the ordered adjacent pairs whose first vertex lies on that side
and whose second vertex lies outside it. -/
-- @node: cutDarts
noncomputable def cutDarts (S : Finset V) : Finset (V × V) :=
  Finset.univ.filter (fun p => G.Adj p.1 p.2 ∧ p.1 ∈ S ∧ p.2 ∉ S)

-- @node: cutDarts_card_eq_sum
/-- [The number of edges directed from a chosen vertex set to its complement equals
the sum, over vertices in that set, of their numbers of neighbors outside the set](goal). -/
lemma cutDarts_card_eq_sum (S : Finset V) :
    (cutDarts G S).card =
      ∑ v ∈ S, ((G.neighborFinset v).filter (fun w => w ∉ S)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := S) (by
    intro p hp
    exact (Finset.mem_filter.mp hp).2.2.1)]
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.card_bij (fun p _ => p.2)
  · intro p hp
    obtain ⟨hp, hfirst⟩ := Finset.mem_filter.mp hp
    simp only [cutDarts, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset v p.2).mpr (hfirst ▸ hp.1), hp.2.2⟩
  · intro p hp q hq heq
    have hpv := (Finset.mem_filter.mp hp).2
    have hqv := (Finset.mem_filter.mp hq).2
    exact Prod.ext (hpv.trans hqv.symm) heq
  · intro w hw
    obtain ⟨hadj, hw⟩ := Finset.mem_filter.mp hw
    refine ⟨(v, w), ?_, rfl⟩
    simp only [Finset.mem_filter, cutDarts, Finset.mem_univ, true_and]
    exact ⟨⟨(G.mem_neighborFinset v w).mp hadj, hv, hw⟩, True.intro⟩

/-- If [every vertex has exactly three neighbors](hyp:hcubic) and
[a vertex belongs to the chosen set](hyp:hv), then [its number of neighbors outside
the set plus the size of the set is at least four](goal). -/
-- @node: cubic_outside_neighbor_bound
lemma cubic_outside_neighbor_bound (hcubic : G.IsRegularOfDegree 3)
    (S : Finset V) (v : V) (hv : v ∈ S) :
    4 ≤ ((G.neighborFinset v).filter (fun w => w ∉ S)).card + S.card := by
  have hsub : (G.neighborFinset v).filter (fun w => w ∈ S) ⊆ S.erase v := by
    intro w hw
    obtain ⟨hadj, hw⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_erase.mpr ⟨(G.ne_of_adj ((G.mem_neighborFinset v w).mp hadj)).symm, hw⟩
  have hi := Finset.card_le_card hsub
  have he := Finset.card_erase_add_one hv
  have hs := Finset.card_filter_add_card_filter_not (s := G.neighborFinset v) (fun w => w ∈ S)
  rw [G.card_neighborFinset_eq_degree, hcubic.degree_eq] at hs
  omega

-- @node: cubic_small_cut_side_card
/-- If [every vertex has exactly three neighbors](hyp:hcubic), [a vertex set is
nonempty](hyp:hne), and [at most two edges leave that set](hyp:hcut), then
[the set contains at least three vertices](goal). -/
lemma cubic_small_cut_side_card (hcubic : G.IsRegularOfDegree 3)
    (S : Finset V) (hne : S.Nonempty) (hcut : (cutDarts G S).card ≤ 2) :
    3 ≤ S.card := by
  have hpos := Finset.card_pos.mpr hne
  by_contra hn
  have hn : S.card = 1 ∨ S.card = 2 := by omega
  rw [cutDarts_card_eq_sum] at hcut
  rcases hn with hn | hn
  · have hsum : ∑ _ ∈ S, 3 ≤
        ∑ v ∈ S, ((G.neighborFinset v).filter (fun w => w ∉ S)).card := by
      apply Finset.sum_le_sum
      intro v hv
      have h := cubic_outside_neighbor_bound G hcubic S v hv
      omega
    simp only [Finset.sum_const, smul_eq_mul, hn, one_mul] at hsum
    omega
  · have hsum : ∑ _ ∈ S, 2 ≤
        ∑ v ∈ S, ((G.neighborFinset v).filter (fun w => w ∉ S)).card := by
      apply Finset.sum_le_sum
      intro v hv
      have h := cubic_outside_neighbor_bound G hcubic S v hv
      omega
    simp only [Finset.sum_const, smul_eq_mul, hn] at hsum
    omega

/-- If [every vertex has exactly three neighbors](hyp:hcubic), [the graph is
three-vertex-connected](hyp:hconn), and a vertex set [is nonempty](hyp:hne) and
[has nonempty complement](hyp:hproper), then [at least three edges cross from
the set to its complement](goal). -/
-- @node: cubic_threeConnected_cut_card
lemma cubic_threeConnected_cut_card (hcubic : G.IsRegularOfDegree 3)
    (hconn : IsVertexConnected G 3) (S : Finset V)
    (hne : S.Nonempty) (hproper : Sᶜ.Nonempty) :
    3 ≤ (cutDarts G S).card := by
  by_contra hcut
  have hcut : (cutDarts G S).card ≤ 2 := by omega
  let B := (cutDarts G S).image Prod.fst
  have hB : B.card ≤ 2 := (Finset.card_image_le).trans hcut
  have hS := cubic_small_cut_side_card G hcubic S hne hcut
  have hnot : ¬ S ⊆ B := by
    intro h
    have := Finset.card_le_card h
    omega
  obtain ⟨u, hu, huB⟩ := Finset.not_subset.mp hnot
  obtain ⟨v, hv⟩ := hproper
  have hvS : v ∉ S := Finset.mem_compl.mp hv
  have hBS : B ⊆ S := by
    intro w hw
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hw
    exact (Finset.mem_filter.mp hp).2.2.1
  have hvB : v ∉ B := fun h => hvS (hBS h)
  have hconnected := hconn.2 B (by omega)
  obtain ⟨p⟩ := hconnected.preconnected ⟨u, huB⟩ ⟨v, hvB⟩
  have step {a b : {w : V | w ∉ B}}
      (hab : (G.induce {w | w ∉ B}).Adj a b) (ha : a.val ∈ S) : b.val ∈ S := by
    by_contra hb
    apply a.property
    exact Finset.mem_image.mpr ⟨(a.val, b.val),
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab, ha, hb⟩, rfl⟩
  have path {a b : {w : V | w ∉ B}}
      (p : (G.induce {w | w ∉ B}).Walk a b) : a.val ∈ S → b.val ∈ S := by
    induction p with
    | nil => exact id
    | cons hab p ih => exact fun ha => ih (step hab ha)
  exact hvS (path p hu)

-- @node: cutDarts_sym2_injOn
/-- [Distinct edges directed from a chosen vertex set to its complement have
distinct unordered endpoint pairs](goal). -/
lemma cutDarts_sym2_injOn (S : Finset V) :
    Set.InjOn (fun p : V × V => s(p.1, p.2)) (cutDarts G S) := by
  intro p hp q hq he
  rcases Sym2.mk_eq_mk_iff.mp he with he | he
  · exact he
  · have hpS := (Finset.mem_filter.mp hp).2.2.1
    have hqS := (Finset.mem_filter.mp hq).2.2.2
    have hfirst : p.1 = q.2 := congrArg Prod.fst he
    exact (hqS (hfirst ▸ hpS)).elim

-- @node: cutDarts_card_le_crossing_cover
/-- If [a finite collection of unordered vertex pairs contains every edge from
a chosen vertex set to its complement](hyp:hcross), then [the number of edges
crossing that cut is at most the size of the collection](goal). -/
lemma cutDarts_card_le_crossing_cover (S : Finset V) (E : Finset (Sym2 V))
    (hcross : ∀ u ∈ S, ∀ v ∉ S, G.Adj u v → s(u, v) ∈ E) :
    (cutDarts G S).card ≤ E.card := by
  have hsub : (cutDarts G S).image (fun p => s(p.1, p.2)) ⊆ E := by
    intro e he
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨ha, hu, hv⟩ := (Finset.mem_filter.mp hp).2
    exact hcross p.1 hu p.2 hv ha
  have hc := Finset.card_image_iff.mpr (cutDarts_sym2_injOn G S)
  rw [← hc]
  exact Finset.card_le_card hsub

/-- If [every vertex has exactly three neighbors](hyp:hcubic), [the graph is
three-vertex-connected](hyp:hconn), and [a collection of unordered vertex pairs
has size at most two](hyp:hE), then [deleting the edges represented by those
pairs leaves a connected graph](goal). -/
-- @node: cubic_threeConnected_deleteEdges_connected
lemma cubic_threeConnected_deleteEdges_connected (hcubic : G.IsRegularOfDegree 3)
    (hconn : IsVertexConnected G 3) (E : Finset (Sym2 V)) (hE : E.card ≤ 2) :
    (G.deleteEdges (E : Set (Sym2 V))).Connected := by
  let H := G.deleteEdges (E : Set (Sym2 V))
  letI : Nonempty V := Fintype.card_pos_iff.mp (by have := hconn.1; omega)
  refine ⟨?_⟩
  intro u v
  by_contra huv
  let S := Finset.univ.filter (fun w => H.Reachable u w)
  have hu : u ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, .rfl⟩
  have hv : v ∉ S := fun h => huv (Finset.mem_filter.mp h).2
  have hcross : ∀ a ∈ S, ∀ b ∉ S, G.Adj a b → s(a, b) ∈ E := by
    intro a ha b hb hab
    by_contra he
    have hadj : H.Adj a b := SimpleGraph.deleteEdges_adj.mpr ⟨hab, he⟩
    exact hb (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ((Finset.mem_filter.mp ha).2).trans hadj.reachable⟩)
  have hlo := cubic_threeConnected_cut_card G hcubic hconn S ⟨u, hu⟩
    ⟨v, Finset.mem_compl.mpr hv⟩
  have hhi := cutDarts_card_le_crossing_cover G S E hcross
  omega

namespace SphereMap

set_option backward.isDefEq.respectTransparency false

/-- If [a map on the sphere is connected](hyp:hM) and [the spanning graph formed
by the edges outside a chosen set is connected](hyp:hE), then [the chosen edges
form a spanning forest in the dual map](goal). -/
-- @node: SphereMap.dual_forest_of_complement_connected
lemma dual_forest_of_complement_connected (M : SphereMap) (hM : M.IsConnectedMap)
    (E : Set M.Edge) (hE : (M.spanningGraph Eᶜ).Connected) :
    IsSpanningForest (M.dual hM) E := by
  obtain ⟨A, hAE, hA⟩ := M.exists_spanningTree_subset_of_connected Eᶜ hE
  have hdual := (M.dual_compl_spanning hM ⟨inferInstance, inferInstance⟩).1 A hA
  constructor
  intro ds hds hmem
  apply hdual.1.acyclic ds hds
  intro d hd
  exact fun ha => hAE ha (hmem d hd)

/-- If [a map on the sphere is connected](hyp:hM) and [deleting any set of at most
two edges leaves its spanning graph connected](hyp:hdel), then [the dual map
has no loops or parallel edges](goal). -/
-- @node: SphereMap.dual_isSimple_of_small_deletions
lemma dual_isSimple_of_small_deletions (M : SphereMap) (hM : M.IsConnectedMap)
    (hdel : ∀ E : Finset M.Edge, E.card ≤ 2 →
      (M.spanningGraph (↑E : Set M.Edge)ᶜ).Connected) :
    (M.dual hM).IsSimple := by
  constructor
  · intro d
    have hf := M.dual_forest_of_complement_connected hM (↑({M.edgeOf d} : Finset M.Edge))
      (hdel {M.edgeOf d} (by simp))
    exact (M.dual hM).forest_no_loop _ hf d (by
      change M.edgeOf d ∈ (↑({M.edgeOf d} : Finset M.Edge))
      simp)
  · intro d e he
    have hf := M.dual_forest_of_complement_connected hM
      (↑({M.edgeOf d, M.edgeOf e} : Finset M.Edge) : Set M.Edge)
      (hdel {M.edgeOf d, M.edgeOf e} (by
        have := Finset.card_insert_le (M.edgeOf d) {M.edgeOf e}
        simpa using this))
    exact (M.dual hM).forest_no_parallel _ hf d e
      (by change M.edgeOf d ∈ ({M.edgeOf d, M.edgeOf e} : Finset M.Edge); simp)
      (by change M.edgeOf e ∈ ({M.edgeOf d, M.edgeOf e} : Finset M.Edge); simp) he

/-- For a map on the sphere whose underlying graph is isomorphic to
[a cubic, bipartite, planar, three-vertex-connected graph](hyp:hG), if
[a chosen set of edges has size at most two](hyp:hE), then [the spanning graph
formed by all remaining edges is connected](goal). -/
-- @node: SphereMap.small_complement_connected_of_mainDomain
lemma small_complement_connected_of_mainDomain (M : SphereMap)
    (i : M.toSimpleGraph ≃g G) (hG : MainDomain G)
    (E : Finset M.Edge) (hE : E.card ≤ 2) :
    (M.spanningGraph (↑E : Set M.Edge)ᶜ).Connected := by
  let F : Finset (Sym2 V) := E.image (fun e => Sym2.map i (M.edgeEndpointPair e))
  have hF : F.card ≤ 2 := (Finset.card_image_le).trans hE
  have hc := cubic_threeConnected_deleteEdges_connected G hG.1 hG.2.2.2 F hF
  let f : G.deleteEdges (↑F : Set (Sym2 V)) →g M.spanningGraph (↑E : Set M.Edge)ᶜ :=
    { toFun := i.symm
      map_rel' := by
        intro u v huv
        obtain ⟨huv, hnot⟩ := SimpleGraph.deleteEdges_adj.mp huv
        have hadj := i.symm.map_rel_iff.mpr huv
        obtain ⟨hne, d, hd, he⟩ := hadj
        refine ⟨hne, d, ?_, hd, he⟩
        intro hmem
        apply hnot
        apply Finset.mem_image.mpr
        refine ⟨M.edgeOf d, hmem, ?_⟩
        change s(i (M.vert d), i (M.head d)) = s(u, v)
        exact Sym2.eq_iff.mpr (Or.inl
          ⟨(congrArg i hd).trans (i.apply_symm_apply u),
            (congrArg i he).trans (i.apply_symm_apply v)⟩) }
  exact hc.map f i.symm.surjective

/-- If [a map on the sphere has no loops or parallel edges](hyp:hs), then
[the number of darts starting at any vertex equals that vertex's degree in
the underlying simple graph](goal). -/
-- @node: SphereMap.dart_fibre_card_eq_degree
lemma dart_fibre_card_eq_degree (M : SphereMap) (hs : M.IsSimple) (v : M.Vertex) :
    (Finset.univ.filter (fun d : M.Dart => M.vert d = v)).card =
      M.toSimpleGraph.degree v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_bij (fun d _ => M.head d)
  · intro d hd
    have hv := (Finset.mem_filter.mp hd).2
    exact (M.toSimpleGraph.mem_neighborFinset _ _).mpr
      ⟨hv ▸ hs.1 d, d, hv, rfl⟩
  · intro d hd e he hh
    exact M.dart_eq_of_endpoints hs d e
      ((Finset.mem_filter.mp hd).2.trans (Finset.mem_filter.mp he).2.symm) hh
  · intro w hw
    obtain ⟨hne, d, hd, hh⟩ := (M.toSimpleGraph.mem_neighborFinset _ _).mp hw
    exact ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩, hh⟩

/-- If [a map on the sphere is connected](hyp:hM), then [the face containing
any dart in the dual is labeled by the starting vertex of that dart in the
original map](goal). -/
-- @node: SphereMap.dual_faceOf
lemma dual_faceOf (M : SphereMap) (hM : M.IsConnectedMap) (d : M.Dart) :
    (M.dual hM).faceOf d = M.vert d := M.dualBoundaryFace_dart hM d

/-- If [a map on the sphere is connected](hyp:hM), [has no loops or parallel
edges](hyp:hs), and [has exactly three neighbors at every vertex](hyp:hc), then
[each face of its dual has boundary length three](goal). -/
-- @node: SphereMap.dual_faceLength_eq_three
lemma dual_faceLength_eq_three (M : SphereMap) (hM : M.IsConnectedMap)
    (hs : M.IsSimple) (hc : M.toSimpleGraph.IsRegularOfDegree 3) (v : M.Vertex) :
    (M.dual hM).faceLength v = 3 := by
  rw [(M.dual hM).faceLength_eq_card_faceDarts]
  change (Finset.univ.filter (fun d => (M.dual hM).faceOf d = v)).card = 3
  simp_rw [M.dual_faceOf hM]
  convert (M.dart_fibre_card_eq_degree hs v).trans (hc.degree_eq v) using 1
  congr 1
  ext d
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- Suppose [a map on the sphere is connected](hyp:hM), [has no loops or
parallel edges](hyp:hs), [has exactly three neighbors at every vertex](hyp:hc),
and [its dual has no loops or parallel edges](hyp:hds). If two darts
[start at the same vertex](hyp:hv) and [belong to the same face](hyp:hf), then
[they are the same dart](goal). -/
-- @node: SphereMap.dual_face_tail_injective_of_cubic
lemma dual_face_tail_injective_of_cubic (M : SphereMap) (hM : M.IsConnectedMap)
    (hs : M.IsSimple) (hc : M.toSimpleGraph.IsRegularOfDegree 3)
    (hds : (M.dual hM).IsSimple) (d e : M.Dart)
    (hv : M.vert d = M.vert e) (hf : M.faceOf d = M.faceOf e) : d = e := by
  let S := Finset.univ.filter (fun a : M.Dart => M.vert a = M.vert d)
  have hcard : S.card = 3 :=
    (M.dart_fibre_card_eq_degree hs _).trans (hc.degree_eq _)
  have hrot : M.rot.IsCycleOn (↑S : Set M.Dart) := by
    simpa only [S, Finset.coe_filter, Finset.mem_univ, true_and] using M.rot_fibre (M.vert d)
  have hd : d ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  have he : e ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv.symm⟩
  have hnext (a : M.Dart) : M.faceOf (M.rot a) ≠ M.faceOf a := by
    intro h
    have hi := M.dual_rot_vertex (M.edgeInv a)
    change M.faceOf (M.rot (M.edgeInv (M.edgeInv a))) = _ at hi
    rw [M.edgeInv_involutive] at hi
    exact hds.1 a (h.symm.trans hi)
  obtain ⟨n, hn, hne⟩ := hrot.exists_pow_eq hd he
  have hn' : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases hn' with rfl | rfl | rfl
  · simpa using hne
  · have heq : M.rot d = e := by simpa using hne
    exact (hnext d (heq ▸ hf.symm)).elim
  · have heq : M.rot e = d := by
      rw [← hne]
      have hpow := hrot.pow_card_apply hd
      rw [hcard] at hpow
      simpa only [pow_succ', Equiv.Perm.mul_apply] using hpow
    exact (hnext e (heq ▸ hf)).elim

/-- If [a map on the sphere is connected](hyp:hM), [has no loops or parallel
edges](hyp:hs), [has exactly three neighbors at every vertex](hyp:hc), and
[its dual has no loops or parallel edges](hyp:hds), then [every face of the
dual has a boundary of length three with three distinct vertices](goal). -/
-- @node: SphereMap.dual_faceBoundaryIsThreeCycle
lemma dual_faceBoundaryIsThreeCycle (M : SphereMap) (hM : M.IsConnectedMap)
    (hs : M.IsSimple) (hc : M.toSimpleGraph.IsRegularOfDegree 3)
    (hds : (M.dual hM).IsSimple) (v : M.Vertex) :
    (M.dual hM).faceBoundaryIsThreeCycle v := by
  let N := M.dual hM
  have hlength := M.dual_faceLength_eq_three hM hs hc v
  refine ⟨hlength, ?_⟩
  have hempty : (Finset.univ.filter (fun w : N.Vertex =>
      ∃ hw : ∀ d, N.vert d ≠ w, N.boundaryFace (Sum.inr ⟨w, hw⟩) = v)) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro w hw
    obtain ⟨hn, heq⟩ := (Finset.mem_filter.mp hw).2
    obtain ⟨d, hd⟩ := Finset.card_pos.mp (show 0 < (N.faceDarts v).card by
      rw [← N.faceLength_eq_card_faceDarts]; exact hlength ▸ (by decide))
    have hf : N.faceOf d = v := (Finset.mem_filter.mp hd).2
    have horbit := M.dualBoundaryFace_bijective hM
    have heq' : M.dualBoundaryFace hM (Sum.inl (orbitOf N.facePerm d)) =
        M.dualBoundaryFace hM (Sum.inr ⟨w, hn⟩) := hf.trans heq.symm
    cases horbit.1 heq'
  change ((N.faceDarts v).image N.vert ∪ _).card = 3
  rw [hempty, Finset.union_empty, Finset.card_image_iff.mpr]
  · rw [← N.faceLength_eq_card_faceDarts]
    exact hlength
  · intro d hd e he hv
    have hdv : M.vert d = v := (M.dual_faceOf hM d).symm.trans (Finset.mem_filter.mp hd).2
    have hev : M.vert e = v := (M.dual_faceOf hM e).symm.trans (Finset.mem_filter.mp he).2
    exact M.dual_face_tail_injective_of_cubic hM hs hc hds d e (hdv.trans hev.symm) hv

/-- If [a map on the sphere is connected](hyp:hM) and its underlying graph is
isomorphic to [a cubic, bipartite, planar, three-vertex-connected graph](hyp:hG),
then [its dual has no loops or parallel edges](goal). -/
-- @node: SphereMap.dual_isSimple_of_mainDomain
lemma dual_isSimple_of_mainDomain (M : SphereMap) (hM : M.IsConnectedMap)
    (i : M.toSimpleGraph ≃g G) (hG : MainDomain G) : (M.dual hM).IsSimple := by
  apply M.dual_isSimple_of_small_deletions hM
  exact M.small_complement_connected_of_mainDomain G i hG

/-- If [a map on the sphere is connected](hyp:hM), [has no loops or parallel
edges](hyp:hs), and its underlying graph is isomorphic to [a cubic, bipartite,
planar, three-vertex-connected graph](hyp:hG), then [its dual is a sphere
triangulation](goal). -/
-- @node: SphereMap.dual_isSphereTriangulation_of_mainDomain
lemma dual_isSphereTriangulation_of_mainDomain (M : SphereMap) (hM : M.IsConnectedMap)
    (hs : M.IsSimple) (i : M.toSimpleGraph ≃g G) (hG : MainDomain G) :
    IsSphereTriangulation (M.dual hM) := by
  have hc : M.toSimpleGraph.IsRegularOfDegree 3 := by
    intro v
    exact (i.degree_eq v).symm.trans (hG.1.degree_eq (i v))
  have hds := M.dual_isSimple_of_mainDomain G hM i hG
  obtain ⟨v⟩ := hM.nonempty
  have hnonzero : 0 < (Finset.univ.filter (fun d : M.Dart => M.vert d = v)).card := by
    rw [M.dart_fibre_card_eq_degree hs, hc.degree_eq]
    decide
  obtain ⟨d, hd⟩ := Finset.card_pos.mp hnonzero
  let : Nonempty (M.dual hM).Vertex := ⟨M.faceOf d⟩
  have hdc : (M.dual hM).IsConnectedMap := by
    constructor
    intro f g
    exact SimpleGraph.ConnectedComponent.exact ((M.dual_component_subsingleton hM).elim _ _)
  refine ⟨hdc, hds, ?_, M.dual_faceBoundaryIsThreeCycle hM hs hc hds⟩
  have hsum := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset M.Dart) (Finset.univ : Finset M.Vertex) M.vert
  simp only [Finset.mem_univ, Finset.filter_true, M.dart_fibre_card_eq_degree hs,
    hc.degree_eq, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hsum
  have htwo := M.dart_card_eq_twice_edge_card
  have heuler := M.connected_euler hM
  have hvertices : 4 ≤ Fintype.card M.Vertex := by
    have hi := Fintype.card_congr i.toEquiv
    have hfour := hG.2.2.2.1
    omega
  change 4 ≤ Fintype.card M.Face
  omega

/-- If [a map on the sphere is connected](hyp:hM), [has no loops or parallel
edges](hyp:hs), and its underlying graph is isomorphic to [a cubic, bipartite,
planar, three-vertex-connected graph](hyp:hG), then [the faces of its dual can
be colored with two colors so that the faces across every edge have opposite
colors](goal). -/
-- @node: SphereMap.dual_partitionColoring_of_mainDomain
lemma dual_partitionColoring_of_mainDomain (M : SphereMap) (hM : M.IsConnectedMap)
    (hs : M.IsSimple) (i : M.toSimpleGraph ≃g G) (hG : MainDomain G) :
    ∃ col : (M.dual hM).Face → Bool, PartitionColoring (M.dual hM) col := by
  obtain ⟨c⟩ := hG.2.1
  have hinj : Function.Injective (fun a : Fin 2 => decide (a = 0)) := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all
  refine ⟨fun v => decide (c (i v) = 0), ?_⟩
  intro d heq
  have hadj : G.Adj (i (M.vert d)) (i (M.head d)) :=
    i.map_rel_iff.mpr ⟨hs.1 d, d, rfl, rfl⟩
  apply c.valid hadj
  apply hinj
  simp only [M.dual_faceOf hM] at heq
  have hinv : (M.dual hM).edgeInv d = M.edgeInv d := rfl
  rw [hinv] at heq
  exact heq

end SphereMap

/-- For [a cubic, bipartite, planar, three-vertex-connected graph](hyp:hG),
[there exists a connected map on the sphere with no loops or parallel edges,
an isomorphism from its underlying graph to the given graph, and a dual with
no loops or parallel edges](goal). -/
-- @node: exists_main_embedding_with_simple_dual
lemma exists_main_embedding_with_simple_dual (hG : MainDomain G) :
    ∃ M : SphereMap, ∃ hM : M.IsConnectedMap,
      M.IsSimple ∧ ∃ i : M.toSimpleGraph ≃g G, (M.dual hM).IsSimple := by
  obtain ⟨M, hs, ⟨i⟩⟩ := hG.2.2.1
  have hc := M.small_complement_connected_of_mainDomain G i hG ∅ (by simp)
  have hle : M.spanningGraph (↑(∅ : Finset M.Edge) : Set M.Edge)ᶜ ≤ M.toSimpleGraph := by
    rintro u v ⟨hne, d, hd, hu, hv⟩
    exact ⟨hne, d, hu, hv⟩
  have hM : M.IsConnectedMap := hc.mono hle
  exact ⟨M, hM, hs, i, M.dual_isSimple_of_mainDomain G hM i hG⟩

/-- For [a cubic, bipartite, planar, three-vertex-connected graph](hyp:hG),
[there exists a connected map on the sphere with no loops or parallel edges
whose underlying graph is isomorphic to the given graph and whose dual is a
sphere triangulation admitting a two-coloring of its faces with opposite
colors across every edge](goal). -/
-- @node: exists_main_colored_dual_triangulation
lemma exists_main_colored_dual_triangulation (hG : MainDomain G) :
    ∃ M : SphereMap, ∃ hM : M.IsConnectedMap, ∃ i : M.toSimpleGraph ≃g G,
      M.IsSimple ∧ IsSphereTriangulation (M.dual hM) ∧
      ∃ col : (M.dual hM).Face → Bool, PartitionColoring (M.dual hM) col := by
  obtain ⟨M, hM, hs, i, hds⟩ := exists_main_embedding_with_simple_dual G hG
  exact ⟨M, hM, i, hs, M.dual_isSphereTriangulation_of_mainDomain G hM hs i hG,
    M.dual_partitionColoring_of_mainDomain G hM hs i hG⟩

end OaiPairedStatesHamiltonian

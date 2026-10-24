module

public import Papers.OaiPairedStatesHamiltonian.Helpers.DensityBoundary
public import Mathlib.Combinatorics.Hall.Basic

/-! Local component, region, density and incidence-flow counts. -/

public section

namespace OaiPairedStatesHamiltonian

set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
open Classical
attribute [local instance] propDecidable


-- @node: signed_bool_sum
/-- [Assigning plus one to true entries and minus one to false entries in a
finite set gives a sum equal to the number of true entries minus the number of
false entries](goal). -/
lemma signed_bool_sum {α : Type} (s : Finset α) (c : α → Bool) :
    (∑ a ∈ s, (if c a then 1 else -1 : ℤ)) =
      ((s.filter (fun a => c a = true)).card : ℤ) -
        (s.filter (fun a => c a = false)).card := by
  simp [Finset.sum_ite, Bool.not_eq_true, sub_eq_add_neg]

-- @node: SphereMap.faceRegion_across_deleted
/-- If [the edge of a directed edge occurrence is outside the retained edge
set](hyp:hd), then [the faces on its two sides belong to the region of a given
starting face either both or neither](goal). -/
lemma SphereMap.faceRegion_across_deleted (T : SphereMap) (S : Set T.Edge)
    (f : T.Face) (d : T.Dart) (hd : T.edgeOf d ∉ S) :
    T.faceOf d ∈ T.faceRegion S f ↔ T.faceOf (T.edgeInv d) ∈ T.faceRegion S f := by
  constructor
  · intro h
    exact h.tail ⟨d, hd, rfl, rfl⟩
  · intro h
    apply h.tail
    refine ⟨T.edgeInv d, ?_, rfl, ?_⟩
    · simpa only [(T.edgeOf_eq_iff d (T.edgeInv d)).mpr (Or.inr rfl)] using hd
    · rw [T.edgeInv_involutive]

-- @node: region_colored_dart_count
/-- If [the map is a sphere triangulation](hyp:hT), then [the number of directed
edge occurrences incident to faces of a chosen color in a given region is three
times the number of faces of that color in the region](goal). -/
lemma region_colored_dart_count (T : SphereMap) (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (R : Set T.Face) (b : Bool) :
    (Finset.univ.filter (fun d => T.faceOf d ∈ R ∧ col (T.faceOf d) = b)).card =
      3 * (Finset.univ.filter (fun f => f ∈ R ∧ col f = b)).card := by
  have h := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset T.Dart) (Finset.univ.filter (fun f => f ∈ R ∧ col f = b)) T.faceOf
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
  rw [← h]
  have hf (f : T.Face) : (Finset.univ.filter (fun d => T.faceOf d = f)).card = 3 :=
    (T.faceLength_eq_card_faceDarts f).symm.trans (hT.props.2.2.2 f).1
  simp_rw [hf]
  simp [Nat.mul_comm]

-- @node: region_internal_signs_cancel
/-- If [faces on opposite sides of every edge have opposite colors](hyp:hcol),
then [the signed sum over directed occurrences of deleted edges incident to
faces in a deleted-edge region is zero, assigning plus one to black faces and
minus one to white faces](goal). -/
lemma region_internal_signs_cancel (T : SphereMap)
    (col : T.Face → Bool) (hcol : PartitionColoring T col) (S : Set T.Edge) (f : T.Face) :
    (∑ d ∈ Finset.univ.filter (fun d => T.edgeOf d ∉ S ∧
      T.faceOf d ∈ T.faceRegion S f), (if col (T.faceOf d) then 1 else -1 : ℤ)) = 0 := by
  apply Finset.sum_involution (fun d _ => T.edgeInv d)
  · intro d hd
    have hc := hcol d
    cases h : col (T.faceOf d) <;>
      cases hi : col (T.faceOf (T.edgeInv d)) <;> simp_all
  · intro d hd hn
    exact T.edgeInv_fixedPointFree d
  · intro d hd
    obtain ⟨_, he, hf⟩ := Finset.mem_filter.mp hd
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
    · simpa only [(T.edgeOf_eq_iff d (T.edgeInv d)).mpr (Or.inr rfl)] using he
    · exact (T.faceRegion_across_deleted S f d he).mp hf
  · intro d hd
    exact T.edgeInv_involutive d

-- @node: region_boundary_signed_count
/-- If [the map is a sphere triangulation](hyp:hT) and [faces on opposite sides
of every edge have opposite colors](hyp:hcol), then [the signed sum over the
retained sides of a deleted-edge region, with black contributing plus one and
white minus one, equals three times the number of black faces minus the number
of white faces in that region](goal). -/
lemma region_boundary_signed_count (T : SphereMap) (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (hcol : PartitionColoring T col) (S : Set T.Edge) (f : T.Face) :
    (∑ d ∈ T.regionSides S (T.faceRegion S f), (if col (T.faceOf d) then 1 else -1 : ℤ)) =
      3 * (((Finset.univ.filter (fun g => g ∈ T.faceRegion S f ∧ col g = true)).card : ℤ) -
        (Finset.univ.filter (fun g => g ∈ T.faceRegion S f ∧ col g = false)).card) := by
  have hfull := signed_bool_sum
    (Finset.univ.filter (fun d => T.faceOf d ∈ T.faceRegion S f)) (fun d => col (T.faceOf d))
  simp only [Finset.filter_filter] at hfull
  rw [region_colored_dart_count T hT col _ true,
    region_colored_dart_count T hT col _ false] at hfull
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ.filter (fun d => T.faceOf d ∈ T.faceRegion S f))
    (fun d => T.edgeOf d ∈ S) (fun d => (if col (T.faceOf d) then 1 else -1 : ℤ))
  simp only [Finset.filter_filter] at hsplit
  have hcancel := region_internal_signs_cancel T col hcol S f
  have hboundary : (∑ d ∈ T.regionSides S (T.faceRegion S f),
      (if col (T.faceOf d) then 1 else -1 : ℤ)) =
      ∑ d ∈ Finset.univ.filter (fun d => T.faceOf d ∈ T.faceRegion S f ∧ T.edgeOf d ∈ S),
        (if col (T.faceOf d) then 1 else -1 : ℤ) := by
    congr 1
    ext d
    simp [SphereMap.regionSides, and_comm]
  rw [hboundary]
  have hi : (Finset.univ.filter (fun d => T.faceOf d ∈ T.faceRegion S f ∧ T.edgeOf d ∉ S)) =
      Finset.univ.filter (fun d => T.edgeOf d ∉ S ∧ T.faceOf d ∈ T.faceRegion S f) := by
    ext d
    simp [and_comm]
  rw [hi, hcancel, add_zero, hfull] at hsplit
  rw [hsplit]
  push_cast
  ring

-- @node: signed_bool_sum_twice
/-- [The sum obtained by assigning plus one to true entries and minus one to
false entries in a finite set equals twice the number of true entries minus
the size of the set](goal). -/
lemma signed_bool_sum_twice {α : Type} (s : Finset α) (c : α → Bool) :
    (∑ a ∈ s, (if c a then 1 else -1 : ℤ)) =
      2 * ((s.filter (fun a => c a = true)).card : ℤ) - s.card := by
  have h := Finset.card_filter_add_card_filter_not (s := s) (fun a => c a = true)
  simp only [Bool.not_eq_true] at h
  have hz := signed_bool_sum s c
  omega

-- @node: boundary_defect_of_signed_count
/-- If [a finite set has at least four elements](hyp:hd) and [three times an
integer equals its signed Boolean sum, with true contributing plus one and
false minus one](hyp:hx), then [the absolute value of that integer is at most
the size of the set minus four](goal). -/
lemma boundary_defect_of_signed_count {α : Type} (s : Finset α) (c : α → Bool)
    (x : ℤ) (hd : 4 ≤ s.card)
    (hx : 3 * x = ∑ a ∈ s, (if c a then 1 else -1 : ℤ)) :
    |x| ≤ (s.card : ℤ) - 4 := by
  have hs := signed_bool_sum_twice s c
  have hk := Finset.card_filter_le (s := s) (p := fun a => c a = true)
  rw [abs_le]
  by_cases hfour : s.card = 4
  · constructor <;> omega
  · by_cases hfive : s.card = 5
    · constructor <;> omega
    · constructor <;> omega

-- @node: face_region_defect
/-- Suppose [the map is a sphere triangulation](hyp:hT), [adjacent faces have
opposite colors](hyp:hcol), [there is no separating triangle](hyp:hsep), [the
graph induced by the selected vertices is connected](hyp:hU), and [at least
four vertices are selected](hyp:hcard). For the deleted-edge region of any
original face, [if its boundary has at least four side occurrences, each side
has sign plus one or minus one according to its incident face color, the sum
of these signs is three times the black-minus-white face count in the region,
and the absolute value of that face-count difference is at most the boundary
side count minus four](goal). -/
lemma face_region_defect (T : SphereMap) (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (hcol : PartitionColoring T col) (hsep : PairsNoSeparatingTriangle T)
    (U : Finset T.Vertex) (hU : (T.toSimpleGraph.induce (↑U : Set T.Vertex)).Connected)
    (hcard : 4 ≤ U.card) (face : T.Face) :
    let R := T.faceRegion (T.retainedEdges U) face
    let sides := T.regionSides (T.retainedEdges U) R
    let d := sides.card -- @realizes d(boundary edge-side count, repetitions of bridge sides retained)
    let b' := (Finset.univ.filter (fun f => f ∈ R ∧ col f = true)).card
      -- @realizes b'(original black faces in the selected component-face region)
    let w' := (Finset.univ.filter (fun f => f ∈ R ∧ col f = false)).card
      -- @realizes w'(original white faces in that region)
    let sigma : sides → ℤ := fun j => if col (T.faceOf j.val) then 1 else -1
      -- @realizes \sigma_j(sign on each boundary-side occurrence)
    4 ≤ d → (∀ j, sigma j = 1 ∨ sigma j = -1) ∧
      3 * ((b' : ℤ) - w') = ∑ j, sigma j ∧
      |(b' : ℤ) - w'| ≤ (d : ℤ) - 4 := by
  dsimp only
  intro hd
  have hcount := region_boundary_signed_count T hT col hcol (T.retainedEdges U) face
  refine ⟨?_, ?_, ?_⟩
  · intro j
    cases col (T.faceOf j.val) <;> simp
  · exact hcount.symm.trans (Finset.sum_coe_sort _
      (fun d : T.Dart => (if col (T.faceOf d) then 1 else -1 : ℤ))).symm
  · exact boundary_defect_of_signed_count _ (fun d => col (T.faceOf d)) _ hd hcount.symm

-- @node: induced_face_length_color_bound
/-- Suppose [the map is a sphere triangulation](hyp:hT), [adjacent faces have
opposite colors](hyp:hcol), [there is no separating triangle](hyp:hsep), [the
induced map is connected](hyp:hc), and [at least four vertices are
selected](hyp:hv). For each induced face, [four minus twice the number of
retained original black faces represented by it, plus the number of all
original black faces minus all original white faces represented by it, is at
most its boundary length](goal). -/
lemma induced_face_length_color_bound (T : SphereMap) (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (hcol : PartitionColoring T col) (hsep : PairsNoSeparatingTriangle T)
    (U : Finset T.Vertex) (hc : (T.induce (↑U : Set T.Vertex)).IsConnectedMap)
    (hv : 4 ≤ U.card) (q : (T.induce (↑U : Set T.Vertex)).Face) :
    (4 : ℤ) - 2 * (Finset.univ.filter (fun t => col t = true ∧
        T.faceVertices t ⊆ U ∧ T.inducedFaceClass (↑U : Set T.Vertex) t = q)).card +
      (((Finset.univ.filter (fun t => col t = true ∧
          T.inducedFaceClass (↑U : Set T.Vertex) t = q)).card : ℤ) -
        (Finset.univ.filter (fun t => col t = false ∧
          T.inducedFaceClass (↑U : Set T.Vertex) t = q)).card) ≤
      ((T.induce (↑U : Set T.Vertex)).faceLength q : ℤ) := by
  let N := T.induce (↑U : Set T.Vertex)
  by_cases hthree : N.faceLength q = 3
  · obtain ⟨f, hret, he⟩ := T.induced_triangle_face_retained hT hsep U hc hv q hthree
    have hfiber (g : T.Face) : T.inducedFaceClass (↑U : Set T.Vertex) g = q ↔ g = f := by
      constructor
      · intro hg
        have hm := (T.inducedFaceClass_eq_iff_faceRegion U f g).mp (he.trans hg.symm)
        simpa only [T.faceRegion_eq_singleton_of_retained U f hret,
          Set.mem_singleton_iff] using hm
      · rintro rfl
        exact he
    have hcolor (b : Bool) :
        Finset.univ.filter (fun t => col t = b ∧
          T.inducedFaceClass (↑U : Set T.Vertex) t = q) =
        if col f = b then {f} else ∅ := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hfiber]
      split_ifs with hb
      · simp only [Finset.mem_singleton]
        exact ⟨And.right, fun ht => by subst t; exact ⟨hb, rfl⟩⟩
      · simp only [Finset.notMem_empty, iff_false, not_and]
        intro ht heq
        subst t
        exact hb ht
    have hblack :
        Finset.univ.filter (fun t => col t = true ∧ T.faceVertices t ⊆ U ∧
          T.inducedFaceClass (↑U : Set T.Vertex) t = q) =
        if col f = true then {f} else ∅ := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hfiber]
      split_ifs with hb
      · simp only [Finset.mem_singleton]
        exact ⟨fun h => h.2.2, fun ht => by subst t; exact ⟨hb, hret, rfl⟩⟩
      · simp only [Finset.notMem_empty, iff_false, not_and]
        intro ht hret' heq
        subst t
        exact hb ht
    rw [hblack, hcolor true, hcolor false]
    change _ ≤ (N.faceLength q : ℤ)
    rw [hthree]
    cases hh : col f <;> norm_num
  · have hlen : 4 ≤ N.faceLength q := by
      have hv' : 3 ≤ Fintype.card N.Vertex := by rw [T.induce_vertex_card U]; omega
      have h := N.faceLength_three_le hc (T.induce_isSimple hT.props.2.1 _) hv' q
      omega
    induction q using Quotient.inductionOn with
    | h g =>
      have hgraph : (T.toSimpleGraph.induce (↑U : Set T.Vertex)).Connected := by
        simpa only [SphereMap.IsConnectedMap, T.induce_toSimpleGraph] using hc
      have hsides : 4 ≤ (T.regionSides (T.retainedEdges U)
          (T.faceRegion (T.retainedEdges U) g)).card := by
        rw [T.regionSides_card_eq_induced_faceLength]
        exact hlen
      have hdef := (face_region_defect T hT col hcol hsep U hgraph hv g hsides).2.2
      have hregion (b : Bool) :
          Finset.univ.filter (fun t => t ∈ T.faceRegion (T.retainedEdges U) g ∧ col t = b) =
          Finset.univ.filter (fun t => col t = b ∧
            T.inducedFaceClass (↑U : Set T.Vertex) t =
              T.inducedFaceClass (↑U : Set T.Vertex) g) := by
        ext t
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          ← T.inducedFaceClass_eq_iff_faceRegion]
        exact ⟨fun h => ⟨h.2, h.1.symm⟩, fun h => ⟨h.2.symm, h.1⟩⟩
      rw [hregion true, hregion false, T.regionSides_card_eq_induced_faceLength] at hdef
      have hupper := (abs_le.mp hdef).2
      have hnonneg : (0 : ℤ) ≤ (Finset.univ.filter (fun t => col t = true ∧
          T.faceVertices t ⊆ U ∧ T.inducedFaceClass (↑U : Set T.Vertex) t =
            T.inducedFaceClass (↑U : Set T.Vertex) g)).card := Nat.cast_nonneg _
      change _ ≤ (N.faceLength (T.inducedFaceClass (↑U : Set T.Vertex) g) : ℤ)
      dsimp only [N, SphereMap.inducedFaceClass] at hupper hnonneg ⊢
      linarith only [hupper, hnonneg]

-- @node: induced_boundary_density
/-- If [the map is a sphere triangulation](hyp:hT), [adjacent faces have opposite
colors](hyp:hcol), [there is no separating triangle](hyp:hsep), [the induced
map is connected](hyp:hc), and [at least four vertices are selected](hyp:hv),
then [twice the number of induced edges is at least four times the number of
induced faces minus twice the number of original black faces whose vertices
are all selected](goal). -/
lemma induced_boundary_density (T : SphereMap) (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (hcol : PartitionColoring T col) (hsep : PairsNoSeparatingTriangle T)
    (U : Finset T.Vertex) (hc : (T.induce (↑U : Set T.Vertex)).IsConnectedMap)
    (hv : 4 ≤ U.card) :
    (2 * Fintype.card (T.induce (↑U : Set T.Vertex)).Edge : ℤ) ≥
      4 * Fintype.card (T.induce (↑U : Set T.Vertex)).Face -
        2 * (Finset.univ.filter (fun t => col t = true ∧ T.faceVertices t ⊆ U)).card := by
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun q _ => induced_face_length_color_bound T hT col hcol hsep U hc hv q)
  have hblack := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ.filter (fun t => col t = true ∧ T.faceVertices t ⊆ U))
    (Finset.univ : Finset (T.induce (↑U : Set T.Vertex)).Face)
    (T.inducedFaceClass (↑U : Set T.Vertex))
  simp only [Finset.filter_filter, Finset.mem_univ, and_true,
    and_assoc] at hblack
  have hzero : (∑ q : (T.induce (↑U : Set T.Vertex)).Face,
      (((Finset.univ.filter (fun t => col t = true ∧
        T.inducedFaceClass (↑U : Set T.Vertex) t = q)).card : ℤ) -
      (Finset.univ.filter (fun t => col t = false ∧
        T.inducedFaceClass (↑U : Set T.Vertex) t = q)).card)) = 0 :=
    T.sum_induced_face_color_defect hT U col hcol
  rw [Finset.sum_add_distrib, hzero, add_zero] at hsum
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Nat.cast_sum] at hsum
  rw [hblack, (T.induce (↑U : Set T.Vertex)).sum_face_lengths_eq_twice_edges] at hsum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  push_cast at hsum
  simpa only [mul_comm] using hsum


-- @node: induced_component_density
/-- Suppose [the map is a sphere triangulation](hyp:hT), [adjacent faces have
opposite colors](hyp:hcol), and [there is no separating triangle](hyp:hsep).
In any connected component of the map induced by a selected vertex set, write
p, m, and f for its vertex, edge, and inherited face counts, and b and w for
the original black and white faces wholly contained in its vertices; [if p
is at least four, then p plus f equals m plus two, twice m is at least four f
minus twice b, m minus b is at most twice p minus four, and b plus w is at most
f; regardless of p, m minus b is at most twice p](goal). -/
lemma induced_component_density (T : SphereMap) (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (hcol : PartitionColoring T col) (hsep : PairsNoSeparatingTriangle T)
    (U : Finset T.Vertex)
    (K : (T.induce (↑U : Set T.Vertex)).toSimpleGraph.ConnectedComponent) :
      -- @realizes K(component of the inherited induced map)
    let TU := T.induce (↑U : Set T.Vertex)
    let KV := (Finset.univ.filter (fun v : TU.Vertex => TU.toSimpleGraph.connectedComponentMk v = K)).image
      (fun v => v.val)
    let KM := T.induce (↑KV : Set T.Vertex)
    let p := KV.card -- @realizes p(number of vertices of the component)
    let m := Fintype.card KM.Edge -- @realizes m(number of edges of the component)
    let f := Fintype.card KM.Face -- @realizes f(number of inherited component faces)
    let b := (Finset.univ.filter (fun t => col t = true ∧ T.faceVertices t ⊆ KV)).card
      -- @realizes b(actual black-face count, equal to triangular black component faces when p >= 4)
    let w := (Finset.univ.filter (fun t => col t = false ∧ T.faceVertices t ⊆ KV)).card
      -- @realizes w(actual white triangular component-face count when p >= 4)
    let b_act := (Finset.univ.filter (fun t => col t = true ∧ T.faceVertices t ⊆ KV)).card
      -- @realizes b_{\rm act}(actual black faces in this component)
    (4 ≤ p → p + f = m + 2 ∧ (2 * m : ℤ) ≥ 4 * f - 2 * b ∧
      (m : ℤ) - b ≤ 2 * p - 4 ∧ b + w ≤ f) ∧ (m : ℤ) - b_act ≤ 2 * p := by
  let KV := T.densityComponentVertices U K
  let KM := T.induce (↑KV : Set T.Vertex)
  let p := KV.card
  let m := Fintype.card KM.Edge
  let f := Fintype.card KM.Face
  let b := (Finset.univ.filter (fun t => col t = true ∧ T.faceVertices t ⊆ KV)).card
  let w := (Finset.univ.filter (fun t => col t = false ∧ T.faceVertices t ⊆ KV)).card
  change (4 ≤ p → p + f = m + 2 ∧ (2 * m : ℤ) ≥ 4 * f - 2 * b ∧
    (m : ℤ) - b ≤ 2 * p - 4 ∧ b + w ≤ f) ∧ (m : ℤ) - b ≤ 2 * p
  have heuler : p + f = m + 2 := T.densityComponent_euler U K
  have hfaces : b + w ≤ f := T.retained_colored_face_card_le KV col
  have hboundary (hp : 4 ≤ p) : (2 * m : ℤ) ≥ 4 * f - 2 * b := by
    exact induced_boundary_density T hT col hcol hsep KV
      (T.densityComponent_connected U K) hp
  have hlarge (hp : 4 ≤ p) : (m : ℤ) - b ≤ 2 * p - 4 := by
    have hb := hboundary hp
    have he : (p : ℤ) + f = m + 2 := by exact_mod_cast heuler
    omega
  refine ⟨fun hp => ⟨heuler, hboundary hp, hlarge hp, hfaces⟩, ?_⟩
  by_cases hp : 4 ≤ p
  · have h := hlarge hp
    omega
  · have hm : m ≤ p.choose 2 := T.density_induced_edge_le_choose hT KV
    by_cases hp2 : 2 ≤ p
    · have hc := Nat.choose_le_choose 2 (show p ≤ 3 by omega)
      norm_num at hc
      omega
    · have hc : p.choose 2 = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [hc] at hm
      omega


end OaiPairedStatesHamiltonian

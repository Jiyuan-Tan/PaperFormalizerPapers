module

public import Papers.OaiPairedStatesHamiltonian.Helpers.Selection
public import Papers.OaiPairedStatesHamiltonian.Helpers.Disk

/-! Orienting selected cycles and applying the signed disk identities. -/

@[expose] public section

namespace OaiPairedStatesHamiltonian

open Classical
attribute [local instance] propDecidable
set_option linter.style.openClassical false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

namespace SphereMap

-- @node: SphereMap.cycle_directed_or_reverse
/-- If [at most one directed edge in the chosen set leaves each
vertex](hyp:hout) and [each edge of the simple cycle has at least one
orientation in that set](hyp:hcover), then [either all forward sides of the
cycle belong to the set or all reverse sides do](goal). -/
lemma cycle_directed_or_reverse (M : SphereMap) (O : Finset M.Dart)
    (hout : ∀ d ∈ O, ∀ e ∈ O, M.vert d = M.vert e → d = e)
    (C : M.Cycle) (hcover : ∀ d ∈ C.val, d ∈ O ∨ M.edgeInv d ∈ O) :
    (∀ d ∈ C.val, d ∈ O) ∨ (∀ d ∈ C.val, M.edgeInv d ∈ O) := by
  have hn : 0 < C.val.length := List.length_pos_iff.mpr C.property.1.1
  let d (i : Fin C.val.length) := C.val.get i
  have step (i : Fin C.val.length) (hi : M.edgeInv (d i) ∈ O) :
      M.edgeInv (d ⟨(i.val + 1) % C.val.length, M.nextIndex_lt C.val i⟩) ∈ O := by
    let j : Fin C.val.length := ⟨(i.val + 1) % C.val.length, M.nextIndex_lt C.val i⟩
    rcases hcover (d j) (List.get_mem _ _) with hj | hj
    · have he : M.edgeInv (d i) = d j := hout _ hi _ hj (C.property.1.2.2 i)
      have hedge : M.edgeOf (d i) = M.edgeOf (d j) :=
        (M.edgeOf_eq_iff _ _).mpr (Or.inr he.symm)
      have hd : d i = d j := List.inj_on_of_nodup_map C.property.1.2.1
        (List.get_mem _ _) (List.get_mem _ _) hedge
      exact (M.edgeInv_fixedPointFree (d i) (he.trans hd.symm)).elim
    · exact hj
  have all_back (i : Fin C.val.length) (hi : M.edgeInv (d i) ∈ O)
      (j : Fin C.val.length) : M.edgeInv (d j) ∈ O := by
    have iterate (k : ℕ) :
        M.edgeInv (d ⟨(i.val + k) % C.val.length, Nat.mod_lt _ hn⟩) ∈ O := by
      induction k with
      | zero => simpa only [Nat.add_zero, Nat.mod_eq_of_lt i.isLt] using hi
      | succ k ih =>
        have hs := step ⟨(i.val + k) % C.val.length, Nat.mod_lt _ hn⟩ ih
        have hm : ((i.val + k) % C.val.length + 1) % C.val.length =
            (i.val + (k + 1)) % C.val.length := by
          simp only [Nat.add_mod, Nat.mod_mod, ← Nat.add_assoc]
        simpa only [hm] using hs
    have hk := iterate (C.val.length - i.val + j.val)
    have he : i.val + (C.val.length - i.val + j.val) = C.val.length + j.val := by omega
    simpa only [he, Nat.add_mod, Nat.mod_self, Nat.zero_add,
      Nat.mod_eq_of_lt j.isLt] using hk
  by_cases hb : ∃ i, M.edgeInv (d i) ∈ O
  · obtain ⟨i, hi⟩ := hb
    right
    intro e he
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp he
    exact all_back i hi j
  · left
    intro e he
    rcases hcover e he with h | h
    · exact h
    · obtain ⟨i, rfl⟩ := List.mem_iff_get.mp he
      exact (hb ⟨i, h⟩).elim

end SphereMap

variable (T : SphereMap) (hT : IsSphereTriangulation T)
  (col : T.Face → Bool) (hcol : PartitionColoring T col) (t0 : T.Face)

-- @node: selectedDart_head_incident
/-- If the map is a sphere triangulation, adjacent faces have opposite
colors, and [the prescribed edge lies on the outer face](hyp:he0),
then [the head of the selected directed edge for a nonouter black triangle
is a vertex of that triangle different from the vertex assigned by the
state](goal). -/
lemma selectedDart_head_incident (s : State T col t0) (e0 : T.Edge)
    (he0 : T.edgeOnFace e0 t0) (t : blackNonOuter T col t0) :
    T.head (selectedDart T hT col hcol t0 s e0 he0 t) ∈ T.faceVertices t.val ∧
      T.head (selectedDart T hT col hcol t0 s e0 he0 t) ≠ (s.val t).val := by
  let d := selectedDart T hT col hcol t0 s e0 he0 t
  have hs := selectedDart_spec T hT col hcol t0 s e0 he0 t
  constructor
  · rcases hs.2 with hf | hf
    · exact hf ▸ (faceDart_endpoints_incident T hT d).2
    · have h := (faceDart_endpoints_incident T hT (T.edgeInv d)).1
      exact hf ▸ h
  · rw [← hs.1]
    exact Ne.symm (hT.props.2.1.1 d)

-- @node: selectedEdgeChoice
/-- For [a sphere map](hyp:T) with [a sphere triangulation](hyp:hT), [a Boolean
face coloring](hyp:col) in which [adjacent faces have opposite
colors](hyp:hcol), [an outer face](hyp:t0), [a state assigning vertices to
nonouter black triangles](hyp:s), and [a prescribed edge](hyp:e0)
[incident to the outer face](hyp:he0), the [second-vertex choice](goal)
assigns each nonouter black triangle the head of its selected directed edge,
a vertex different from the one assigned by the state. -/
noncomputable def selectedEdgeChoice (s : State T col t0) (e0 : T.Edge)
    (he0 : T.edgeOnFace e0 t0) : EdgeChoice T col t0 s := fun t =>
  ⟨T.head (selectedDart T hT col hcol t0 s e0 he0 t),
    selectedDart_head_incident T hT col hcol t0 s e0 he0 t⟩

-- @node: selectedDart_eq_faceDart
/-- If the map is a sphere triangulation, adjacent faces have opposite
colors, and [the prescribed edge lies on the outer face](hyp:he0),
then [the selected directed edge for a nonouter black triangle equals the
triangle's directed edge from its state-assigned vertex to its chosen second
vertex](goal). -/
lemma selectedDart_eq_faceDart (s : State T col t0) (e0 : T.Edge)
    (he0 : T.edgeOnFace e0 t0) (t : blackNonOuter T col t0) :
    selectedDart T hT col hcol t0 s e0 he0 t =
      faceDart T hT t.val (s.val t).val
        (selectedEdgeChoice T hT col hcol t0 s e0 he0 t).val
        (s.property.incident t)
        (selectedEdgeChoice T hT col hcol t0 s e0 he0 t).property.1
        (Ne.symm (selectedEdgeChoice T hT col hcol t0 s e0 he0 t).property.2) := by
  let d := selectedDart T hT col hcol t0 s e0 he0 t
  have hd := selectedDart_spec T hT col hcol t0 s e0 he0 t
  obtain ⟨hv, hw, hf⟩ := Classical.choose_spec (exists_faceDart T hT t.val
    (s.val t).val (selectedEdgeChoice T hT col hcol t0 s e0 he0 t).val
    (s.property.incident t)
    (selectedEdgeChoice T hT col hcol t0 s e0 he0 t).property.1
    (Ne.symm (selectedEdgeChoice T hT col hcol t0 s e0 he0 t).property.2))
  apply T.dart_eq_of_endpoints hT.props.2.1
  · exact hd.1.trans hv.symm
  · exact hw.symm

-- @node: orientedP0_mem_chosenEdges
/-- If the map is a sphere triangulation, adjacent faces have opposite
colors, [the prescribed edge lies on the outer face](hyp:he0), and
[a directed edge belongs to the oriented selected set with the prescribed
edge removed](hyp:hd), then [it belongs to the edges chosen from the state
and the selected second vertices](goal). -/
lemma orientedP0_mem_chosenEdges (s : State T col t0) (e0 : T.Edge)
    (he0 : T.edgeOnFace e0 t0) (d : T.Dart)
    (hd : d ∈ orientedP0 T hT col hcol t0 s e0 he0) :
    d ∈ ChosenEdges T col t0 hT s (selectedEdgeChoice T hT col hcol t0 s e0 he0) := by
  obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hd).1
  exact Finset.mem_image.mpr ⟨t, Finset.mem_univ _,
    (selectedDart_eq_faceDart T hT col hcol t0 s e0 he0 t).symm⟩

-- @node: selectedSet0_edge_orientation
/-- If the map is a sphere triangulation, adjacent faces have opposite
colors, [the prescribed edge lies on the outer face](hyp:he0), and
[the undirected edge underlying a given directed edge belongs to the selected
set with the prescribed edge removed](hyp:hd), then [that directed edge or
its reverse belongs to the corresponding oriented selected set](goal). -/
lemma selectedSet0_edge_orientation (s : State T col t0) (e0 : T.Edge)
    (he0 : T.edgeOnFace e0 t0) (d : T.Dart)
    (hd : T.edgeOf d ∈ selectedSet0 T hT col hcol t0 s e0 he0) :
    d ∈ orientedP0 T hT col hcol t0 s e0 he0 ∨
      T.edgeInv d ∈ orientedP0 T hT col hcol t0 s e0 he0 := by
  have hne := (Finset.mem_erase.mp hd).1
  have hm := (Finset.mem_erase.mp hd).2
  rcases Finset.mem_insert.mp hm with he | he
  · exact (hne he).elim
  · obtain ⟨t, _, ht⟩ := Finset.mem_image.mp he
    have hs : selectedDart T hT col hcol t0 s e0 he0 t ∈
        orientedP0 T hT col hcol t0 s e0 he0 := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩,
        ht.symm ▸ hne⟩
    rcases (T.edgeOf_eq_iff _ _).mp ht with he | he
    · exact Or.inl (he.symm ▸ hs)
    · right
      have hi : T.edgeInv d = selectedDart T hT col hcol t0 s e0 he0 t :=
        (congrArg T.edgeInv he).trans (T.edgeInv_involutive _)
      exact hi.symm ▸ hs

-- @node: selectedSet0_cycle_directed
/-- If the map is a sphere triangulation, adjacent faces have opposite
colors, [the prescribed edge lies on the outer face](hyp:he0), and
[every cycle edge is selected after removing the prescribed edge](hyp:hC),
then [either the cycle or its reversal has every directed edge in the
oriented selected set](goal). -/
lemma selectedSet0_cycle_directed (s : State T col t0) (e0 : T.Edge)
    (he0 : T.edgeOnFace e0 t0) (C : T.Cycle)
    (hC : ∀ d ∈ C.val, T.edgeOf d ∈ selectedSet0 T hT col hcol t0 s e0 he0) :
    ∃ D : T.Cycle, (D = C ∨ D = reverseCycle T C) ∧
      ∀ d ∈ D.val, d ∈ orientedP0 T hT col hcol t0 s e0 he0 := by
  have hout := orientedP0_tail_injective T hT col hcol t0 s e0 he0
  rcases T.cycle_directed_or_reverse (orientedP0 T hT col hcol t0 s e0 he0)
      (fun d hd e he h => hout d e hd he h) C
      (fun d hd => selectedSet0_edge_orientation T hT col hcol t0 s e0 he0 d (hC d hd))
      with h | h
  · exact ⟨C, Or.inl rfl, h⟩
  · refine ⟨reverseCycle T C, Or.inr rfl, ?_⟩
    intro d hd
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
    exact h e (List.mem_reverse.mp he)

-- @node: orientedP0_cycle_delta_sum
/-- If the map is a sphere triangulation, adjacent faces have opposite
colors, [the prescribed edge lies on the outer face](hyp:he0), and
[every directed edge of the cycle belongs to the oriented selected
set](hyp:hC), then [the cycle's signed boundary sum under the normalized
coloring is either three or minus three](goal). -/
lemma orientedP0_cycle_delta_sum (s : State T col t0) (e0 : T.Edge)
    (he0 : T.edgeOnFace e0 t0) (C : T.Cycle)
    (hC : ∀ d ∈ C.val, d ∈ orientedP0 T hT col hcol t0 s e0 he0) :
    (C.val.map (delta T (normalizedColoring T col t0))).sum = 3 ∨
      (C.val.map (delta T (normalizedColoring T col t0))).sum = -3 := by
  have hchosen (d : T.Dart) (hd : d ∈ C.val) :
      d ∈ ChosenEdges T col t0 hT s (selectedEdgeChoice T hT col hcol t0 s e0 he0) :=
    orientedP0_mem_chosenEdges T hT col hcol t0 s e0 he0 d (hC d hd)
  have hs : t0 ∈ T.leftRegion C ∪ T.rightRegion C :=
    (T.cycle_sides_partition C).2.symm ▸ Set.mem_univ t0
  rcases hs with hcw | hccw
  · exact Or.inl (delta_sum_of_clockwise T hT col hcol t0 s
      (selectedEdgeChoice T hT col hcol t0 s e0 he0) C hchosen hcw)
  · exact Or.inr (delta_sum_of_counterclockwise T hT col hcol t0 s
      (selectedEdgeChoice T hT col hcol t0 s e0 he0) C hchosen hccw)

-- @node: selectedSet0_cycle_nonzero_direction
/-- If the map is a sphere triangulation, adjacent faces have opposite
colors, [the prescribed edge lies on the outer face](hyp:he0), and
[every cycle edge is selected after removing the prescribed edge](hyp:hC),
then [the cycle or its reversal lies entirely in the oriented selected set
and has a nonzero signed boundary sum under the normalized coloring](goal). -/
lemma selectedSet0_cycle_nonzero_direction (s : State T col t0) (e0 : T.Edge)
    (he0 : T.edgeOnFace e0 t0) (C : T.Cycle)
    (hC : ∀ d ∈ C.val, T.edgeOf d ∈ selectedSet0 T hT col hcol t0 s e0 he0) :
    ∃ D : T.Cycle, (D = C ∨ D = reverseCycle T C) ∧
      (∀ d ∈ D.val, d ∈ orientedP0 T hT col hcol t0 s e0 he0) ∧
      (D.val.map (delta T (normalizedColoring T col t0))).sum ≠ 0 := by
  obtain ⟨D, hD, hd⟩ := selectedSet0_cycle_directed T hT col hcol t0 s e0 he0 C hC
  refine ⟨D, hD, hd, ?_⟩
  rcases orientedP0_cycle_delta_sum T hT col hcol t0 s e0 he0 D hd with h | h
  · rw [h]
    norm_num
  · rw [h]
    norm_num

-- @node: selectedDart_edgeOnFace
/-- If the map is a sphere triangulation, adjacent faces have opposite
colors, and [the prescribed edge lies on the outer face](hyp:he0),
then [the edge underlying the selected directed edge of a nonouter black
triangle is incident to that triangle](goal). -/
lemma selectedDart_edgeOnFace (s : State T col t0) (e0 : T.Edge)
    (he0 : T.edgeOnFace e0 t0) (t : blackNonOuter T col t0) :
    T.edgeOnFace (T.edgeOf (selectedDart T hT col hcol t0 s e0 he0 t)) t.val := by
  let d := selectedDart T hT col hcol t0 s e0 he0 t
  rcases (selectedDart_spec T hT col hcol t0 s e0 he0 t).2 with hf | hf
  · exact ⟨d, rfl, hf⟩
  · exact ⟨T.edgeInv d,
      (T.edgeOf_eq_iff _ _).mpr (Or.inr (T.edgeInv_involutive d).symm), hf⟩

-- @node: selectedDart_edge_injective
/-- If the map is a sphere triangulation, adjacent faces have opposite
colors, and [the prescribed edge lies on the outer face](hyp:he0),
then [distinct nonouter black triangles supply distinct selected undirected
edges](goal). -/
lemma selectedDart_edge_injective (s : State T col t0) (e0 : T.Edge)
    (he0 : T.edgeOnFace e0 t0) :
    Function.Injective (fun t : blackNonOuter T col t0 =>
      T.edgeOf (selectedDart T hT col hcol t0 s e0 he0 t)) := by
  intro t u he
  dsimp only at he
  apply Subtype.ext
  apply black_face_of_edge_unique T (normalizedColoring T col t0)
    (normalizedColoring_partition T col hcol t0) _ t.val u.val
    (nonOuter_black T col t0 t) (nonOuter_black T col t0 u)
    (selectedDart_edgeOnFace T hT col hcol t0 s e0 he0 t)
  rw [he]
  exact selectedDart_edgeOnFace T hT col hcol t0 s e0 he0 u

-- @node: selectedDart_edge_ne_outer
/-- If the map is a sphere triangulation, adjacent faces have opposite
colors, and [the prescribed edge lies on the outer face](hyp:he0),
then [the edge selected by any nonouter black triangle differs from the
prescribed edge](goal). -/
lemma selectedDart_edge_ne_outer (s : State T col t0) (e0 : T.Edge)
    (he0 : T.edgeOnFace e0 t0) (t : blackNonOuter T col t0) :
    T.edgeOf (selectedDart T hT col hcol t0 s e0 he0 t) ≠ e0 := by
  intro he
  have hf := black_face_of_edge_unique T (normalizedColoring T col t0)
    (normalizedColoring_partition T col hcol t0) e0 t.val t0
    (nonOuter_black T col t0 t) (normalizedColoring_self T col t0)
    (he ▸ selectedDart_edgeOnFace T hT col hcol t0 s e0 he0 t) he0
  exact (Finset.mem_filter.mp t.property).2.2 hf

-- @node: selectedSet0_eq_image
/-- If the map is a sphere triangulation, adjacent faces have opposite
colors, and [the prescribed edge lies on the outer face](hyp:he0),
then [the selected set with the prescribed edge removed is exactly the set
of undirected edges supplied by all nonouter black triangles](goal). -/
lemma selectedSet0_eq_image (s : State T col t0) (e0 : T.Edge)
    (he0 : T.edgeOnFace e0 t0) :
    selectedSet0 T hT col hcol t0 s e0 he0 =
      Finset.univ.image (fun t => T.edgeOf (selectedDart T hT col hcol t0 s e0 he0 t)) := by
  have hn : e0 ∉ Finset.univ.image
      (fun t => T.edgeOf (selectedDart T hT col hcol t0 s e0 he0 t)) := by
    rintro he
    obtain ⟨t, _, ht⟩ := Finset.mem_image.mp he
    exact selectedDart_edge_ne_outer T hT col hcol t0 s e0 he0 t ht
  exact Finset.erase_insert hn

-- @node: orientedP0_eq_image
/-- If the map is a sphere triangulation, adjacent faces have opposite
colors, and [the prescribed edge lies on the outer face](hyp:he0),
then [the oriented selected set is exactly the set of selected directed
edges supplied by all nonouter black triangles](goal). -/
lemma orientedP0_eq_image (s : State T col t0) (e0 : T.Edge)
    (he0 : T.edgeOnFace e0 t0) :
    orientedP0 T hT col hcol t0 s e0 he0 =
      Finset.univ.image (selectedDart T hT col hcol t0 s e0 he0) := by
  apply Finset.filter_eq_self.mpr
  intro d hd
  obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hd
  exact selectedDart_edge_ne_outer T hT col hcol t0 s e0 he0 t

-- @node: orientedP0_existsUnique_tail
/-- If the map is a sphere triangulation, adjacent faces have opposite
colors, and [the prescribed edge lies on the outer face](hyp:he0),
then [exactly one directed edge in the oriented selected set leaves the
given nonroot vertex](goal). -/
lemma orientedP0_existsUnique_tail (s : State T col t0) (e0 : T.Edge)
    (he0 : T.edgeOnFace e0 t0) (v : nonRoot T t0) :
    ∃! d : T.Dart, d ∈ orientedP0 T hT col hcol t0 s e0 he0 ∧ T.vert d = v.val := by
  obtain ⟨t, ht⟩ := s.property.bijective.2 v
  let d := selectedDart T hT col hcol t0 s e0 he0 t
  have hd : d ∈ orientedP0 T hT col hcol t0 s e0 he0 := by
    rw [orientedP0_eq_image T hT col hcol t0 s e0 he0]
    exact Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩
  have hv : T.vert d = v.val :=
    (selectedDart_spec T hT col hcol t0 s e0 he0 t).1.trans (congrArg Subtype.val ht)
  refine ⟨d, ⟨hd, hv⟩, ?_⟩
  intro e he
  exact orientedP0_tail_injective T hT col hcol t0 s e0 he0 e d he.1 hd
    (he.2.trans hv.symm)

-- @node: selectedSet0_card
/-- If the map is a sphere triangulation, adjacent faces have opposite
colors, and [the prescribed edge lies on the outer face](hyp:he0),
then [the number of selected edges after removing the prescribed edge equals
the number of nonroot vertices](goal). -/
lemma selectedSet0_card (s : State T col t0) (e0 : T.Edge)
    (he0 : T.edgeOnFace e0 t0) :
    (selectedSet0 T hT col hcol t0 s e0 he0).card = (nonRoot T t0).card := by
  rw [selectedSet0_eq_image T hT col hcol t0 s e0 he0,
    Finset.card_image_of_injective _ (selectedDart_edge_injective T hT col hcol t0 s e0 he0),
    Finset.card_univ]
  exact (Fintype.card_congr (Equiv.ofBijective s.val s.property.bijective)).trans
    (Fintype.card_coe _)

-- @node: selectedSet_black_incidence_iff
/-- If the map is a sphere triangulation, adjacent faces have opposite
colors, and [the prescribed edge lies on the outer face](hyp:he0),
then [an edge is selected and incident to the given nonouter black triangle
if and only if it is the edge supplied by that triangle](goal). -/
lemma selectedSet_black_incidence_iff (s : State T col t0) (e0 : T.Edge)
    (he0 : T.edgeOnFace e0 t0) (t : blackNonOuter T col t0) (e : T.Edge) :
    (e ∈ selectedSet T hT col hcol t0 s e0 he0 ∧ T.edgeOnFace e t.val) ↔
      e = T.edgeOf (selectedDart T hT col hcol t0 s e0 he0 t) := by
  constructor
  · rintro ⟨he, hf⟩
    rcases Finset.mem_insert.mp he with rfl | he
    · have ht := black_face_of_edge_unique T (normalizedColoring T col t0)
        (normalizedColoring_partition T col hcol t0) e t.val t0
        (nonOuter_black T col t0 t) (normalizedColoring_self T col t0) hf he0
      exact ((Finset.mem_filter.mp t.property).2.2 ht).elim
    · obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp he
      have hut : u = t := Subtype.ext (black_face_of_edge_unique T
        (normalizedColoring T col t0) (normalizedColoring_partition T col hcol t0)
        _ u.val t.val (nonOuter_black T col t0 u) (nonOuter_black T col t0 t)
        (selectedDart_edgeOnFace T hT col hcol t0 s e0 he0 u) hf)
      rw [hut]
  · rintro rfl
    exact ⟨Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩),
      selectedDart_edgeOnFace T hT col hcol t0 s e0 he0 t⟩

-- @node: selectedSet_black_face_existsUnique
/-- If the map is a sphere triangulation, adjacent faces have opposite
colors, and [the prescribed edge lies on the outer face](hyp:he0),
then [exactly one edge in the full selected set is incident to the given
nonouter black triangle](goal). -/
lemma selectedSet_black_face_existsUnique (s : State T col t0) (e0 : T.Edge)
    (he0 : T.edgeOnFace e0 t0) (t : blackNonOuter T col t0) :
    ∃! e : T.Edge, e ∈ selectedSet T hT col hcol t0 s e0 he0 ∧ T.edgeOnFace e t.val := by
  refine ⟨T.edgeOf (selectedDart T hT col hcol t0 s e0 he0 t),
    (selectedSet_black_incidence_iff T hT col hcol t0 s e0 he0 t _).mpr rfl, ?_⟩
  intro e he
  exact (selectedSet_black_incidence_iff T hT col hcol t0 s e0 he0 t e).mp he

-- @node: selectedSet_card
/-- If the map is a sphere triangulation, adjacent faces have opposite
colors, and [the prescribed edge lies on the outer face](hyp:he0),
then [the full selected set has one more edge than there are nonroot
vertices](goal). -/
lemma selectedSet_card (s : State T col t0) (e0 : T.Edge)
    (he0 : T.edgeOnFace e0 t0) :
    (selectedSet T hT col hcol t0 s e0 he0).card = (nonRoot T t0).card + 1 := by
  have hc := selectedSet0_card T hT col hcol t0 s e0 he0
  have he : e0 ∈ selectedSet T hT col hcol t0 s e0 he0 := Finset.mem_insert_self _ _
  exact (Finset.card_erase_add_one he).symm.trans (congrArg (fun n => n + 1) hc)

end OaiPairedStatesHamiltonian

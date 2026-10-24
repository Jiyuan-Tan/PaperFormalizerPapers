module

public import Papers.OaiPairedStatesHamiltonian.Helpers.DiskCounts
public import Papers.OaiPairedStatesHamiltonian.Helpers.ClockwiseMatching
public import Papers.OaiPairedStatesHamiltonian.Helpers.CycleSeparation

/-! The signed disk identity for state-directed cycles. -/

public section

namespace OaiPairedStatesHamiltonian

set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.unusedVariables false
open Classical
attribute [local instance] propDecidable

-- @node: chosenEdges_tail_nonRoot
/-- In a [sphere triangulation](hyp:hT), if [a directed edge is selected by the state's edge choice](hyp:hd), then [its tail is not a vertex of the distinguished outer face](goal). -/
lemma chosenEdges_tail_nonRoot (T : SphereMap) (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (t0 : T.Face) (r : State T col t0)
    (choice : EdgeChoice T col t0 r) (d : T.Dart)
    (hd : d ∈ ChosenEdges T col t0 hT r choice) : T.vert d ∉ roots T t0 := by
  obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hd
  have htail := (Classical.choose_spec (exists_faceDart T hT t.val (r.val t).val
    (choice t).val (r.property.incident t) (choice t).property.1
    (Ne.symm (choice t).property.2))).1
  change T.vert (faceDart T hT _ _ _ _ _ _) ∉ roots T t0
  rw [show T.vert (faceDart T hT _ _ _ _ _ _) = (r.val t).val from htail]
  exact (Finset.mem_sdiff.mp (r.val t).property).2

-- @node: delta_sum_eq_boundary_count
/-- For any list of directed edges, [the sum of their color signs equals twice the number whose incident face is colored true, minus the list's length](goal). -/
lemma delta_sum_eq_boundary_count (T : SphereMap) (col : T.Face → Bool)
    (ds : List T.Dart) :
    (ds.map (delta T col)).sum =
      2 * ((ds.filter (fun d => col (T.faceOf d) = true)).length : ℤ) - ds.length := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
    cases hd : col (T.faceOf d) <;> simp [delta, hd, ih] <;> ring

-- @node: delta_sum_of_counterclockwise
/-- In a [sphere triangulation](hyp:hT) with [a face coloring that gives opposite colors across every edge](hyp:hcol), suppose [every directed edge of a simple cycle is selected by the state](hyp:hC) and [the cycle is counterclockwise relative to the outer face](hyp:hccw). Then [its color signs, normalized so the outer face is black, sum to minus three](goal). -/
lemma delta_sum_of_counterclockwise (T : SphereMap) (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (hcol : PartitionColoring T col) (t0 : T.Face)
    (r : State T col t0) (choice : EdgeChoice T col t0 r) (C : T.Cycle)
    (hC : ∀ d ∈ C.val, d ∈ ChosenEdges T col t0 hT r choice)
    (hccw : T.IsCounterclockwise t0 C) :
    (C.val.map (delta T (normalizedColoring T col t0))).sum = -3 := by
  obtain ⟨hh, heuler, hsides, hmatching⟩ :=
    state_disk_count_identities T hT col hcol t0 r choice C hC hccw
  rw [delta_sum_eq_boundary_count]
  have heuler' :
      ((Finset.univ.filter (fun f => f ∈ T.leftRegion C ∧
        normalizedColoring T col t0 f = true)).card : ℤ) +
      (Finset.univ.filter (fun f => f ∈ T.leftRegion C ∧
        normalizedColoring T col t0 f = false)).card =
      2 * (Finset.univ.filter (T.strictlyOnSide (T.leftRegion C) C)).card + C.val.length - 2 := by
    have h := congrArg (fun n : ℕ => (n : ℤ)) heuler
    rw [Nat.cast_sub (by omega)] at h
    push_cast at h
    exact h
  have hmatching' := congrArg (fun n : ℕ => (n : ℤ)) hmatching
  push_cast at hmatching'
  omega

-- @node: delta_sum_of_clockwise
/-- In a [sphere triangulation](hyp:hT) with [a face coloring that gives opposite colors across every edge](hyp:hcol), suppose [every directed edge of a simple cycle is selected by the state](hyp:hC) and [the cycle is clockwise relative to the outer face](hyp:hcw). Then [its color signs, normalized so the outer face is black, sum to three](goal). -/
lemma delta_sum_of_clockwise (T : SphereMap) (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (hcol : PartitionColoring T col) (t0 : T.Face)
    (r : State T col t0) (choice : EdgeChoice T col t0 r) (C : T.Cycle)
    (hC : ∀ d ∈ C.val, d ∈ ChosenEdges T col t0 hT r choice)
    (hcw : T.IsClockwise t0 C) :
    (C.val.map (delta T (normalizedColoring T col t0))).sum = 3 := by
  obtain ⟨outer, hout⟩ := T.exists_face_outside_cycle_leftRegion hT.props.1 C
  have hh := simple_cycle_length_ge_three T hT C
  have heuler := cycle_disk_euler_count T hT (normalizedColoring T col t0) C outer hout
  have hsides := cycle_signed_side_count T hT (normalizedColoring T col t0)
    (normalizedColoring_partition T col hcol t0) C outer hout
  have hmatching := state_cycle_matching_count_of_exterior T hT col hcol t0 r choice C hC outer hout
  let I := Finset.univ.filter (T.strictlyOnSide (T.leftRegion C) C)
  let B := Finset.univ.filter (fun f => f ∈ T.leftRegion C ∧
    normalizedColoring T col t0 f = true)
  have hroots : roots T t0 ⊆ I := by
    intro v hv
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · intro hb
      obtain ⟨d, hd, hdv⟩ := List.mem_map.mp hb
      exact chosenEdges_tail_nonRoot T hT col t0 r choice d (hC d hd) (hdv ▸ hv)
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, t0, hcw, hv⟩
  have hrootcard : (I \ roots T t0).card + 3 = I.card := by
    have h := Finset.card_sdiff_add_card_eq_card hroots
    rw [show (roots T t0).card = 3 from (hT.props.2.2.2 t0).2] at h
    exact h
  have houter : t0 ∈ B :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcw, normalizedColoring_self T col t0⟩
  have hblack := Finset.card_erase_add_one houter
  have hmatching_nat : B.card + 2 = I.card +
      (C.val.filter (fun d => normalizedColoring T col t0 (T.faceOf d) = true)).length := by
    change (B.erase t0).card = (I \ roots T t0).card + _ at hmatching
    omega
  have heuler' :
      ((Finset.univ.filter (fun f => f ∈ T.leftRegion C ∧
        normalizedColoring T col t0 f = true)).card : ℤ) +
      (Finset.univ.filter (fun f => f ∈ T.leftRegion C ∧
        normalizedColoring T col t0 f = false)).card =
      2 * (Finset.univ.filter (T.strictlyOnSide (T.leftRegion C) C)).card + C.val.length - 2 := by
    have h := congrArg (fun n : ℕ => (n : ℤ)) heuler
    rw [Nat.cast_sub (by omega)] at h
    push_cast at h
    exact h
  have hmatching' := congrArg (fun n : ℕ => (n : ℤ)) hmatching_nat
  dsimp only [B, I] at hmatching'
  push_cast at hmatching'
  rw [delta_sum_eq_boundary_count]
  omega

-- @node: lem:disk
/-- In a [sphere triangulation](hyp:hT) with [opposite face colors across every edge](hyp:hcol), assume [every directed edge of a simple cycle is selected by the state](hyp:hC). Then [all cycle tails avoid the outer-face vertices, and the sum of color signs normalized at the outer face is minus three for a counterclockwise cycle and three for a clockwise cycle](goal). -/
lemma delta_sum_of_simple_cycle (T : SphereMap) (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (hcol : PartitionColoring T col) (t0 : T.Face)
    (r : State T col t0) (choice : EdgeChoice T col t0 r) (C : T.Cycle)
    (hC : ∀ d ∈ C.val, d ∈ ChosenEdges T col t0 hT r choice) :
    (∀ d ∈ C.val, T.vert d ∉ roots T t0) ∧
    (T.IsCounterclockwise t0 C → (C.val.map (delta T (normalizedColoring T col t0))).sum = -3) ∧
    (T.IsClockwise t0 C → (C.val.map (delta T (normalizedColoring T col t0))).sum = 3) := by
  refine ⟨?_, delta_sum_of_counterclockwise T hT col hcol t0 r choice C hC, ?_⟩
  · intro d hd
    exact chosenEdges_tail_nonRoot T hT col t0 r choice d (hC d hd)
  · exact delta_sum_of_clockwise T hT col hcol t0 r choice C hC


end OaiPairedStatesHamiltonian

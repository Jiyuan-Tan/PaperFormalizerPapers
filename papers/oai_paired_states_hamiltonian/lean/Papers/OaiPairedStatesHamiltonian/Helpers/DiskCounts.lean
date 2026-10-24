module

public import Papers.OaiPairedStatesHamiltonian.Helpers.CycleDiskEuler
public import Papers.OaiPairedStatesHamiltonian.Helpers.CycleSideCount
public import Papers.OaiPairedStatesHamiltonian.Helpers.DiskMatching

/-! The local Euler, side and matching identities in a state-directed disk. -/

public section

namespace OaiPairedStatesHamiltonian

set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.unusedVariables false
open Classical
attribute [local instance] propDecidable

-- @node: simple_cycle_length_ge_three
/-- In a [sphere triangulation](hyp:hT), [every simple cycle has at least three directed edges](goal). -/
lemma simple_cycle_length_ge_three (T : SphereMap) (hT : IsSphereTriangulation T)
    (C : T.Cycle) : 3 ≤ C.val.length := by
  obtain ⟨ds, htrail, hverts⟩ := C
  change 3 ≤ ds.length
  cases ds with
  | nil => exact False.elim (htrail.1 rfl)
  | cons d ds =>
    cases ds with
    | nil =>
      have hs := htrail.2.2 ⟨0, by simp⟩
      have hloop : T.head d = T.vert d := by simpa using hs
      exact False.elim (hT.props.2.1.1 d hloop.symm)
    | cons e ds =>
      cases ds with
      | nil =>
        have hd := htrail.2.2 ⟨0, by simp⟩
        have he := htrail.2.2 ⟨1, by simp⟩
        have hd' : T.head d = T.vert e := by simpa using hd
        have he' : T.head e = T.vert d := by simpa using he
        have hedge : T.edgeOf d = T.edgeOf e := hT.props.2.1.2 d e (by
          rw [hd', he']
          exact Sym2.eq_swap)
        have hn : T.edgeOf d ≠ T.edgeOf e := by simpa using htrail.2.1
        exact False.elim (hn hedge)
      | cons f ds => simp


-- @node: state_disk_count_identities
/-- In a [sphere triangulation](hyp:hT) with [opposite face colors across every edge](hyp:hcol), suppose [a simple cycle consists of state-selected directed edges](hyp:hC) and [is counterclockwise relative to the outer face](hyp:hccw). Counting black and white faces in its left disk after normalizing the outer face to black, [the boundary length is at least three, the total face count is twice the strictly interior vertex count plus the boundary length minus two, three times the black-minus-white face count is twice the number of boundary darts with a black left face minus the boundary length, and the black face count equals the interior vertex count plus that boundary count](goal). -/
lemma state_disk_count_identities (T : SphereMap) (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (hcol : PartitionColoring T col) (t0 : T.Face)
    (r : State T col t0) (choice : EdgeChoice T col t0 r) (C : T.Cycle)
    (hC : ∀ d ∈ C.val, d ∈ ChosenEdges T col t0 hT r choice)
    (hccw : T.IsCounterclockwise t0 C) :
    let R := T.leftRegion C
    let B := (Finset.univ.filter (fun f => f ∈ R ∧ normalizedColoring T col t0 f = true)).card
      -- @realizes B(original black faces in the bounded disk)
    let W := (Finset.univ.filter (fun f => f ∈ R ∧ normalizedColoring T col t0 f = false)).card
      -- @realizes W(original white faces in the bounded disk)
    let I := (Finset.univ.filter (T.strictlyOnSide R C)).card
      -- @realizes I(vertices strictly inside the bounded disk)
    let h := C.val.length -- @realizes h(length of the simple boundary cycle, at least three)
    let l := (C.val.filter (fun d => normalizedColoring T col t0 (T.faceOf d) = true)).length
      -- @realizes l(boundary edges whose incident black face is in the disk)
    3 ≤ h ∧ B + W = 2 * I + h - 2 ∧ 3 * ((B : ℤ) - W) = 2 * l - h ∧ B = I + l := by
  have hout : t0 ∉ T.leftRegion C := fun hin =>
    Set.disjoint_left.mp (T.cycle_sides_partition C).1 hin hccw
  refine ⟨simple_cycle_length_ge_three T hT C, ?_, ?_,
    state_disk_matching_count T hT col hcol t0 r choice C hC hccw⟩
  · exact cycle_disk_euler_count T hT (normalizedColoring T col t0) C t0 hout
  · exact cycle_signed_side_count T hT (normalizedColoring T col t0)
      (normalizedColoring_partition T col hcol t0) C t0 hout




end OaiPairedStatesHamiltonian

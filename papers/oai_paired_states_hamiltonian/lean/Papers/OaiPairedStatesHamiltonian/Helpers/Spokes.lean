module

public import Papers.OaiPairedStatesHamiltonian.Helpers.SpokeLocalSides
public import Papers.OaiPairedStatesHamiltonian.Helpers.FaceSideLabels

/-! Shortcutting spoke cycles and their signed incidence weights. -/

@[expose] public section

namespace OaiPairedStatesHamiltonian

set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.unusedVariables false
open Classical
attribute [local instance] propDecidable

variable (T : SphereMap) (col : T.Face → Bool) (t0 : T.Face)

/-- For a [sphere map](hyp:T) with [face coloring](hyp:col) and [designated outer face](hyp:t0),
assuming [the map is a sphere triangulation](hyp:hT) and [adjacent faces have opposite colors](hyp:hcol),
the [projection of a spoke cycle](goal) shortcuts [the chosen spoke cycle](hyp:C) through each black
triangle to produce a cycle in the original map. -/
noncomputable def spokeCycleProjection (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col)
    (C : (spokeGraphBounded T col t0 hT hcol).Cycle) : T.Cycle :=
  ⟨projectSpokeDarts T (blackNonOuter T col t0) C.val, project_spoke_cycle T col t0 hT hcol C⟩
  -- @realizes C(simple spoke cycle, orientation inherited by shortcut inside each black triangle)

-- @node: spokeProjectedSide_iff_leftRegion
/-- If [the map is a sphere triangulation](hyp:hT) and [adjacent faces have opposite colors](hyp:hcol),
then [a face has the projected left-side label exactly when it lies in the global left region of
the spoke cycle](goal), including faces behind components disjoint from the cycle. -/
lemma spokeProjectedSide_iff_leftRegion (hT : IsSphereTriangulation T)
    (hcol : PartitionColoring T col)
    (C : (spokeGraphBounded T col t0 hT hcol).Cycle)
    (f : (spokeGraphBounded T col t0 hT hcol).Face) :
    spokeProjectedSide T col t0 hT hcol C f ↔
      f ∈ (spokeGraphBounded T col t0 hT hcol).leftRegion C := by
  exact (spokeGraphBounded T col t0 hT hcol).cycle_side_label C
    (spokeProjectedSide T col t0 hT hcol C)
    (spokeProjectedSide_cycle_dart T col t0 hT hcol C)
    (spokeProjectedSide_across_noncycle T col t0 hT hcol C) f

-- @node: spokeCycle_orientation
/-- If [the map is a sphere triangulation](hyp:hT) and [adjacent faces have opposite colors](hyp:hcol),
then [a spoke cycle is counterclockwise relative to the spoke outer face exactly when its projection
is counterclockwise relative to the original outer face](goal). -/
lemma spokeCycle_orientation (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col)
    (C : (spokeGraphBounded T col t0 hT hcol).Cycle) :
    (spokeGraphBounded T col t0 hT hcol).IsCounterclockwise (spokeOuter T col t0 hT hcol) C ↔
      T.IsCounterclockwise t0 (spokeCycleProjection T col t0 hT hcol C) := by
  change spokeOuter T col t0 hT hcol ∈
      (spokeGraphBounded T col t0 hT hcol).rightRegion C ↔
    t0 ∈ T.rightRegion (spokeCycleProjection T col t0 hT hcol C)
  rw [(spokeGraphBounded T col t0 hT hcol).rightRegion_iff_not_leftRegion,
    T.rightRegion_iff_not_leftRegion]
  apply not_congr
  exact (spokeProjectedSide_iff_leftRegion T col t0 hT hcol C _).symm.trans
    (spokeProjectedSide_outer T col t0 hT hcol C)

-- @node: corner_incident
/-- [The vertex of any corner of a selected face belongs to the vertex set of that face](goal). -/
lemma corner_incident (faces : Finset T.Face) (d : SpokeCorner T faces) :
    T.vert d.val ∈ T.faceVertices (T.faceOf d.val) := by
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨d.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, rfl⟩

/-- In a [sphere map](hyp:T) with [face coloring](hyp:col) and [outer face](hyp:t0), the
[signed weight of a spoke dart](goal), for [incidence weights](hyp:a) and [a directed spoke](hyp:d),
is obtained by [reading the weight at its face and vertex](step:1) and
[negating it when the dart's direction flag is true, leaving it unchanged otherwise](step:2). -/
noncomputable def signedSpokeDart (a : IncidenceWeights T col t0)
    (d : SpokeDart T (blackNonOuter T col t0)) : ℝ :=
  let w := a ⟨T.faceOf d.1.val, d.1.property⟩ ⟨T.vert d.1.val, corner_incident T _ d.1⟩
  if d.2 then -w else w

/-- For a [sphere map](hyp:T), [face coloring](hyp:col), and [outer face](hyp:t0), with
[a sphere triangulation](hyp:hT) and [opposite colors across each edge](hyp:hcol), the
[signed spoke-cycle weight](goal) sums [the incidence weights](hyp:a), with their directional signs,
over all darts of [the spoke cycle](hyp:C). -/
noncomputable def signedSpokeWeight (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col)
    (a : IncidenceWeights T col t0) (C : (spokeGraphBounded T col t0 hT hcol).Cycle) : ℝ :=
  (C.val.map (signedSpokeDart T col t0 a)).sum


end OaiPairedStatesHamiltonian

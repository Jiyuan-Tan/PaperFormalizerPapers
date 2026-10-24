module

public import Papers.OaiPairedStatesHamiltonian.Helpers.CycleReversal
public import Papers.OaiPairedStatesHamiltonian.Helpers.Disk
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Complex.Basic

/-! Integral pair phases and the finite complex exponential sum. -/

@[expose] public section

namespace OaiPairedStatesHamiltonian

set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.unusedVariables false
open Classical
attribute [local instance] propDecidable


variable (T : SphereMap) (col : T.Face → Bool) (t0 : T.Face)

/-- For [a sphere map](hyp:T), [a face coloring](hyp:col), [an outer face](hyp:t0),
[a sphere triangulation assumption](hyp:hT), and [two states](hyp:r,s) that
[assign distinct vertices at every black nonouter face](hyp:h), the [pair delta sum](goal)
sums the normalized-coloring sign of the directed edge from the first state's
vertex to the second state's vertex over all black nonouter faces. -/
noncomputable def pairDeltaSum (hT : IsSphereTriangulation T) (r s : State T col t0)
    (h : IsPair T col t0 r s) : ℤ :=
  ∑ t : blackNonOuter T col t0,
    delta T (normalizedColoring T col t0)
      (faceDart T hT t.val (r.val t).val (s.val t).val
        (r.property.incident t) (s.property.incident t) (pair_vertex_ne T col t0 r s h t))
-- @node: def:j
/-- For [a sphere map](hyp:T), [a face coloring](hyp:col), [an outer face](hyp:t0),
[a sphere triangulation assumption](hyp:hT), and [two states](hyp:r,s) with
[distinct assigned vertices at every black nonouter face](hyp:h), the [integer
phase index](goal) is the pair delta sum divided by three using integer division. -/
noncomputable def J (hT : IsSphereTriangulation T) (r s : State T col t0)
    (h : IsPair T col t0 r s) : ℤ := pairDeltaSum T col t0 hT r s h / 3
  -- @realizes J(one third of the delta sum, integral by the companion lemma)

-- @node: cycle_delta_sum_dvd_three
/-- In [a sphere triangulation](hyp:hT) with [a partition coloring](hyp:hcol),
[the sum of the coloring signs along any simple directed cycle is divisible by three](goal). -/
lemma cycle_delta_sum_dvd_three (hT : IsSphereTriangulation T)
    (hcol : PartitionColoring T col) (C : T.Cycle) :
    (3 : ℤ) ∣ (C.val.map (delta T col)).sum := by
  obtain ⟨outer, hout⟩ := T.exists_face_outside_cycle_leftRegion hT.props.1 C
  have hs := cycle_signed_side_count T hT col hcol C outer hout
  rw [delta_sum_eq_boundary_count]
  exact ⟨_, hs.symm⟩

-- @node: pairDeltaSum_eq_sum_pairedEdges
/-- In [a sphere triangulation](hyp:hT), for two states that [assign distinct vertices
at every black nonouter face](hyp:h), [the face-indexed pair delta sum equals the
sum of normalized-coloring signs over their set of directed paired edges](goal). -/
lemma pairDeltaSum_eq_sum_pairedEdges (hT : IsSphereTriangulation T)
    (r s : State T col t0) (h : IsPair T col t0 r s) :
    pairDeltaSum T col t0 hT r s h =
      ∑ d ∈ pairedEdges T col t0 hT r s h, delta T (normalizedColoring T col t0) d := by
  unfold pairDeltaSum pairedEdges
  symm
  apply Finset.sum_image
  intro t ht u hu he
  apply r.property.bijective.1
  apply Subtype.ext
  have htail (v : blackNonOuter T col t0) :=
    (Classical.choose_spec (exists_faceDart T hT v.val (r.val v).val (s.val v).val
      (r.property.incident v) (s.property.incident v)
      (pair_vertex_ne T col t0 r s h v))).1
  exact (htail t).symm.trans ((congrArg T.vert he).trans (htail u))

-- @node: three_dvd_sum_delta
/-- In [a sphere triangulation](hyp:hT) with [a partition coloring](hyp:hcol), if
[two states assign distinct vertices at every black nonouter face](hyp:h), then
[their pair delta sum is divisible by three](goal). -/
lemma three_dvd_sum_delta (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col)
    (r s : State T col t0) (h : IsPair T col t0 r s) :
    (3 : ℤ) ∣ pairDeltaSum T col t0 hT r s h := by
  obtain ⟨cs, hlength, hnonroot, hdisjoint, hcover, hvertices⟩ :=
    pairedEdges_directed_cycleDecomposition T col t0 hT hcol ⟨(r, s), h⟩
  have hd : (↑cs : Set T.Cycle).PairwiseDisjoint (fun C => C.val.toFinset) := by
    intro C hC D hD hne
    apply Finset.disjoint_left.mpr
    intro d hdC hdD
    exact Finset.disjoint_left.mp (hdisjoint C hC D hD hne)
      (List.mem_toFinset.mpr (List.mem_map.mpr ⟨d, List.mem_toFinset.mp hdC, rfl⟩))
      (List.mem_toFinset.mpr (List.mem_map.mpr ⟨d, List.mem_toFinset.mp hdD, rfl⟩))
  rw [pairDeltaSum_eq_sum_pairedEdges, ← hcover, Finset.sum_biUnion hd]
  apply Finset.dvd_sum
  intro C hC
  rw [List.sum_toFinset _ (C.property.2.of_map T.vert)]
  exact cycle_delta_sum_dvd_three T (normalizedColoring T col t0) hT
    (normalizedColoring_partition T col hcol t0) C
-- @node: three_mul_J
/-- In [a sphere triangulation](hyp:hT) with [a partition coloring](hyp:hcol), for
[two states assigning distinct vertices at every black nonouter face](hyp:h),
[three times their integer phase index equals their pair delta sum](goal). -/
lemma three_mul_J (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col)
    (r s : State T col t0) (h : IsPair T col t0 r s) :
    3 * J T col t0 hT r s h = pairDeltaSum T col t0 hT r s h := by
  exact Int.mul_ediv_cancel_of_dvd (three_dvd_sum_delta T col t0 hT hcol r s h)

-- @node: def:z
/-- For [a sphere map](hyp:T), [a face coloring](hyp:col), [an outer face](hyp:t0),
[a sphere triangulation assumption](hyp:hT), [real face-vertex incidence weights](hyp:a),
and [a real argument](hyp:x), the [complex pair partition sum](goal) sums over all
ordered state pairs the imaginary unit raised to the integer phase index, multiplied
by the exponential of the argument times the second state's total incidence weight. -/
noncomputable def Z (hT : IsSphereTriangulation T) (a : IncidenceWeights T col t0) (x : ℝ) : ℂ :=
  ∑ p : Pair T col t0,
    Complex.I ^ (J T col t0 hT p.val.1 p.val.2 p.property) *
      Complex.exp ((x * omega T col t0 a p.val.2 : ℝ) : ℂ)
  -- @realizes Z(finite sum over every ordered pair)
  -- @realizes x(arbitrary real argument)
  -- @realizes \ii(the complex imaginary unit in the phase)

/-- For [a sphere map](hyp:T), [a face coloring](hyp:col), [an outer face](hyp:t0),
[real face-vertex incidence weights](hyp:a), and [a list of black nonouter
face-vertex incidences](hyp:C), the [list's total weight](goal) is the sum of
the weights of its incidences, counting repetitions. -/
noncomputable def cycleWeight (a : IncidenceWeights T col t0)
    (C : List (Σ t : blackNonOuter T col t0, T.faceVertices t.val)) : ℝ :=
  (C.map (fun i => a i.1 i.2)).sum



-- @node: exists_pairCycleIncidence
/-- In [a sphere triangulation](hyp:hT) with [a partition coloring](hyp:hcol), if
[a dart's undirected edge belongs to a pair's undirected paired edges](hyp:hd),
then [some black nonouter face contains the dart's head as a vertex and has that
undirected edge on its boundary](goal). -/
lemma exists_pairCycleIncidence (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col)
    (p : Pair T col t0) (d : T.Dart) (hd : T.edgeOf d ∈ undirectedPairedEdges T col t0 hT p) :
    ∃ t : blackNonOuter T col t0, T.head d ∈ T.faceVertices t.val ∧ T.edgeOnFace (T.edgeOf d) t.val := by
  obtain ⟨e, he, hed⟩ := Finset.mem_image.mp hd
  obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp he
  have hs := Classical.choose_spec (exists_faceDart T hT t.val
    (p.val.1.val t).val (p.val.2.val t).val
    (p.val.1.property.incident t) (p.val.2.property.incident t)
    (pair_vertex_ne T col t0 p.val.1 p.val.2 p.property t))
  let e := faceDart T hT t.val (p.val.1.val t).val (p.val.2.val t).val
    (p.val.1.property.incident t) (p.val.2.property.incident t)
    (pair_vertex_ne T col t0 p.val.1 p.val.2 p.property t)
  change FaceDart T t.val (p.val.1.val t).val (p.val.2.val t).val e at hs
  change T.edgeOf e = T.edgeOf d at hed
  refine ⟨t, ?_, ?_⟩
  · rcases (T.edgeOf_eq_iff e d).mp hed with rfl | rfl
    · rw [hs.2.1]
      exact p.val.2.property.incident t
    · have hhead : T.head (T.edgeInv e) = T.vert e :=
        congrArg T.vert (T.edgeInv_involutive e)
      rw [hhead, hs.1]
      exact p.val.1.property.incident t
  · rcases hs.2.2 with hf | hf
    · exact ⟨e, hed, hf⟩
    · refine ⟨T.edgeInv e, ?_, hf⟩
      exact (((T.edgeOf_eq_iff e (T.edgeInv e)).mpr (Or.inr rfl)).symm).trans hed

/-- For [a sphere map](hyp:T), [a face coloring](hyp:col), [an outer face](hyp:t0),
[a sphere triangulation assumption](hyp:hT), [a partition coloring assumption](hyp:hcol),
[a pair](hyp:p), and [a dart](hyp:d) whose [undirected edge is among the pair's
paired edges](hyp:hd), the [chosen head incidence](goal) consists of a black nonouter
face having that edge on its boundary, together with the dart's head as a vertex of that face. -/
noncomputable def pairCycleIncidence (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col)
    (p : Pair T col t0) (d : T.Dart) (hd : T.edgeOf d ∈ undirectedPairedEdges T col t0 hT p) :
    Σ t : blackNonOuter T col t0, T.faceVertices t.val :=
  ⟨Classical.choose (exists_pairCycleIncidence T col t0 hT hcol p d hd),
    ⟨T.head d, (Classical.choose_spec (exists_pairCycleIncidence T col t0 hT hcol p d hd)).1⟩⟩

/-- For [a sphere map](hyp:T), [a face coloring](hyp:col), [an outer face](hyp:t0),
[a sphere triangulation assumption](hyp:hT), [a partition coloring assumption](hyp:hcol),
[incidence weights](hyp:a), [a pair](hyp:p), and [a directed cycle](hyp:C) whose
[undirected edges all belong to the pair's paired edge set](hyp:hC), the [oriented
cycle weight](goal) sums the weights of the chosen head incidences along the cycle
in its given direction. -/
noncomputable def orientedPairCycleWeight (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col)
    (a : IncidenceWeights T col t0) (p : Pair T col t0) (C : T.Cycle)
    (hC : ∀ d ∈ C.val, T.edgeOf d ∈ undirectedPairedEdges T col t0 hT p) : ℝ :=
  cycleWeight T col t0 a (C.val.attach.map (fun d => pairCycleIncidence T col t0 hT hcol p d.val (hC d.val d.property)))

-- @node: reverseCycle_paired
/-- In [a sphere triangulation](hyp:hT), if [every undirected edge of a cycle belongs
to a pair's paired edge set](hyp:hC), then [every undirected edge of the reversed
cycle also belongs to that set](goal). -/
lemma reverseCycle_paired (hT : IsSphereTriangulation T) (p : Pair T col t0) (C : T.Cycle)
    (hC : ∀ d ∈ C.val, T.edgeOf d ∈ undirectedPairedEdges T col t0 hT p) :
    ∀ d ∈ (reverseCycle T C).val, T.edgeOf d ∈ undirectedPairedEdges T col t0 hT p := by
  intro d hd
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
  have hedge : T.edgeOf (T.edgeInv e) = T.edgeOf e :=
    ((T.edgeOf_eq_iff e (T.edgeInv e)).mpr (Or.inr rfl)).symm
  rw [hedge]
  exact hC e (List.mem_reverse.mp he)

/-- For [a sphere map](hyp:T), [a face coloring](hyp:col), [an outer face](hyp:t0),
[a sphere triangulation assumption](hyp:hT), [a partition coloring assumption](hyp:hcol),
[incidence weights](hyp:a), [a pair](hyp:p), and [a cycle](hyp:C) whose [undirected
edges all belong to the pair's paired edge set](hyp:hC), the [counterclockwise cycle
weight](goal) is [the head-incidence sum in the given direction if the cycle is
counterclockwise relative to the outer face](step:1), and [the head-incidence sum
in the reversed direction otherwise](step:2). -/
noncomputable def counterclockwiseCycleWeight (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col)
    (a : IncidenceWeights T col t0) (p : Pair T col t0) (C : T.Cycle)
    (hC : ∀ d ∈ C.val, T.edgeOf d ∈ undirectedPairedEdges T col t0 hT p) : ℝ :=
  if T.IsCounterclockwise t0 C then orientedPairCycleWeight T col t0 hT hcol a p C hC
  else orientedPairCycleWeight T col t0 hT hcol a p (reverseCycle T C) (reverseCycle_paired T col t0 hT p C hC)
  -- @realizes L_+(sum of a(t,head) in the counterclockwise orientation of a component cycle)

/-- For [a sphere map](hyp:T), [a face coloring](hyp:col), [an outer face](hyp:t0),
[a sphere triangulation assumption](hyp:hT), [a partition coloring assumption](hyp:hcol),
[incidence weights](hyp:a), [a pair](hyp:p), and [a cycle](hyp:C) whose [undirected
edges all belong to the pair's paired edge set](hyp:hC), the [clockwise cycle
weight](goal) is [the head-incidence sum in the given direction if the cycle is
clockwise relative to the outer face](step:1), and [the head-incidence sum in the
reversed direction otherwise](step:2). -/
noncomputable def clockwiseCycleWeight (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col)
    (a : IncidenceWeights T col t0) (p : Pair T col t0) (C : T.Cycle)
    (hC : ∀ d ∈ C.val, T.edgeOf d ∈ undirectedPairedEdges T col t0 hT p) : ℝ :=
  if T.IsClockwise t0 C then orientedPairCycleWeight T col t0 hT hcol a p C hC
  else orientedPairCycleWeight T col t0 hT hcol a p (reverseCycle T C) (reverseCycle_paired T col t0 hT p C hC)
  -- @realizes L_-(sum of a(t,head) in the clockwise orientation of that cycle)

-- @node: def:cycle-weights
/-- For [a sphere map](hyp:T), [a face coloring](hyp:col), [an outer face](hyp:t0),
[a sphere triangulation assumption](hyp:hT), [a partition coloring assumption](hyp:hcol),
[incidence weights](hyp:a), [a pair](hyp:p), and [a cycle](hyp:C) whose [undirected
edges all belong to the pair's paired edge set](hyp:hC), the [pair of directional
cycle weights](goal) consists of [the counterclockwise head-incidence sum](step:1)
followed by [the clockwise head-incidence sum](step:2). -/
noncomputable def cycleWeights (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col)
    (a : IncidenceWeights T col t0) (p : Pair T col t0) (C : T.Cycle)
    (hC : ∀ d ∈ C.val, T.edgeOf d ∈ undirectedPairedEdges T col t0 hT p) : ℝ × ℝ :=
  (counterclockwiseCycleWeight T col t0 hT hcol a p C hC,
    clockwiseCycleWeight T col t0 hT hcol a p C hC)

end OaiPairedStatesHamiltonian

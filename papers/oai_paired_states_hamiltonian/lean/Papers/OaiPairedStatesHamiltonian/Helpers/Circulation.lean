module

public import Papers.OaiPairedStatesHamiltonian.Helpers.Spokes
public import Papers.OaiPairedStatesHamiltonian.Helpers.CycleSideCount
public import Papers.OaiPairedStatesHamiltonian.Helpers.ComponentMaps

/-! Positive circulation from prescribed face boundaries and paths in the dual. -/

@[expose] public section

namespace OaiPairedStatesHamiltonian

set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
open Classical
attribute [local instance] propDecidable


namespace SphereMap
variable (M : SphereMap)
/-- In [the sphere map](hyp:M), [being a simple dual path](goal) from
[the starting face to the ending face](hyp:f,g) means that [the dart list](hyp:ds)
[can be empty only when the endpoints agree](step:1), [starts with the starting face on its left](step:2),
[ends with the ending face on its right](step:3), [crosses consecutively between matching faces](step:4),
and [visits no face twice, including the ending face](step:5). -/
noncomputable def IsDualPath (f g : M.Face) (ds : List M.Dart) : Prop :=
  (ds = [] → f = g) ∧
  (∀ d, ds.head? = some d → M.faceOf d = f) ∧
  (∀ d, ds.getLast? = some d → M.faceOf (M.edgeInv d) = g) ∧
  (∀ p ∈ ds.zip ds.tail, M.faceOf (M.edgeInv p.1) = M.faceOf p.2) ∧
  (ds.map M.faceOf ++ [g]).Nodup

/-- In [the sphere map](hyp:M), [the dual path weight](goal) at [a dart](hyp:d),
given [an outer face](hyp:outer) and [a dart list for each face](hyp:paths), is the total
number of forward crossings minus reverse crossings in the lists for all non-outer faces. -/
noncomputable def dualPathWeight (outer : M.Face) (paths : M.Face → List M.Dart) (d : M.Dart) : ℝ :=
  ∑ f ∈ Finset.univ.erase outer,
    (((paths f).count d : ℝ) - ((paths f).count (M.edgeInv d) : ℝ))

-- @node: SphereMap.dualPathWeight_edgeInv
/-- [Reversing a dart negates its dual path weight](goal), for any outer face and family of face paths. -/
lemma dualPathWeight_edgeInv (outer : M.Face) (paths : M.Face → List M.Dart)
    (d : M.Dart) : M.dualPathWeight outer paths (M.edgeInv d) =
      -M.dualPathWeight outer paths d := by
  unfold dualPathWeight
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro f hf
  rw [M.edgeInv_involutive]
  exact (neg_sub _ _).symm

-- @node: SphereMap.dart_count_flux_cons
/-- [Prepending a dart to a list increases its net crossing count around a face by one
if that face is on the dart's left, and decreases it by one if it is on its right](goal). -/
lemma dart_count_flux_cons (ds : List M.Dart) (e : M.Dart) (f : M.Face) :
    (∑ d ∈ M.faceDarts f,
      (((e :: ds).count d : ℝ) - ((e :: ds).count (M.edgeInv d) : ℝ))) =
    ((if f = M.faceOf e then 1 else 0) -
      (if f = M.faceOf (M.edgeInv e) then 1 else 0)) +
    ∑ d ∈ M.faceDarts f, ((ds.count d : ℝ) - (ds.count (M.edgeInv d) : ℝ)) := by
  have hi (d : M.Dart) : e = M.edgeInv d ↔ d = M.edgeInv e := by
    constructor
    · intro h
      exact (M.edgeInv_involutive d).symm.trans (congrArg M.edgeInv h.symm)
    · intro h
      rw [h, M.edgeInv_involutive]
  simp only [List.count_cons, beq_iff_eq, Nat.cast_add, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero, hi]
  simp_rw [show ∀ d : M.Dart,
    (ds.count d : ℝ) + (if e = d then (1 : ℝ) else 0) -
      ((ds.count (M.edgeInv d) : ℝ) + (if d = M.edgeInv e then (1 : ℝ) else 0)) =
      ((if e = d then (1 : ℝ) else 0) - (if d = M.edgeInv e then 1 else 0)) +
        ((ds.count d : ℝ) - ds.count (M.edgeInv d)) by intro d; ring]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp [SphereMap.faceDarts, eq_comm]

-- @node: SphereMap.dual_walk_dart_list
/-- If [the map is connected](hyp:hM), then any walk between two faces in the dual graph
[has a dart list with the same sequence of faces, the correct starting and ending faces,
and consecutive crossings, empty only if the endpoints agree; its net crossing count around each face is the indicator of
the starting face minus the indicator of the ending face](goal). -/
lemma dual_walk_dart_list (hM : M.IsConnectedMap) {f g : M.Face}
    (p : (M.dualRotation hM).toSimpleGraph.Walk f g) :
    ∃ ds : List M.Dart,
      (ds = [] → f = g) ∧
      (∀ d, ds.head? = some d → M.faceOf d = f) ∧
      (∀ d, ds.getLast? = some d → M.faceOf (M.edgeInv d) = g) ∧
      (∀ q ∈ ds.zip ds.tail, M.faceOf (M.edgeInv q.1) = M.faceOf q.2) ∧
      ds.map M.faceOf ++ [g] = p.support ∧
      ∀ a, (∑ d ∈ M.faceDarts a, ((ds.count d : ℝ) - (ds.count (M.edgeInv d) : ℝ))) =
        (if a = f then 1 else 0) - (if a = g then 1 else 0) := by
  induction p with
  | nil => exact ⟨[], by simp [SimpleGraph.Walk.support_nil]⟩
  | @cons f g k hadj p ih =>
    obtain ⟨_, e, he, hei⟩ := hadj
    change M.faceOf e = f at he
    change M.faceOf (M.edgeInv e) = g at hei
    obtain ⟨ds, hnil, hhead, hlast, hzip, hsupp, hflux⟩ := ih
    refine ⟨e :: ds, by simp, ?_, ?_, ?_, ?_, ?_⟩
    · intro d hd
      have hd : e = d := Option.some.inj hd
      exact hd ▸ he
    · intro d hd
      cases ds with
      | nil =>
        have hd : e = d := Option.some.inj hd
        exact hd ▸ (hei.trans (hnil rfl))
      | cons a ds => exact hlast d (by simpa using hd)
    · intro q hq
      cases ds with
      | nil => simp at hq
      | cons a ds =>
        simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact hei.trans (hhead a rfl).symm
        · exact hzip q hq
    · simpa only [List.map_cons, List.cons_append, he,
        SimpleGraph.Walk.support_cons] using congrArg (List.cons f) hsupp
    · intro a
      rw [M.dart_count_flux_cons, hflux, he, hei]
      ring

-- @node: SphereMap.exists_simple_dual_paths
/-- If [the map is connected](hyp:hM), [each face can be assigned a simple dual path to
the outer face, with the outer face assigned the empty path, such that each path's net
crossing count around any face is its starting-face indicator minus its outer-face indicator](goal). -/
lemma exists_simple_dual_paths (hM : M.IsConnectedMap) (outer : M.Face) :
    ∃ paths : M.Face → List M.Dart,
      (∀ f, M.IsDualPath f outer (paths f)) ∧ paths outer = [] ∧
      ∀ f a, (∑ d ∈ M.faceDarts a,
        (((paths f).count d : ℝ) - ((paths f).count (M.edgeInv d) : ℝ))) =
          (if a = f then 1 else 0) - (if a = outer then 1 else 0) := by
  have hex (f : M.Face) : ∃ ds : List M.Dart, M.IsDualPath f outer ds ∧
      ∀ a, (∑ d ∈ M.faceDarts a, ((ds.count d : ℝ) - (ds.count (M.edgeInv d) : ℝ))) =
        (if a = f then 1 else 0) - (if a = outer then 1 else 0) := by
    have hr : (M.dualRotation hM).toSimpleGraph.Reachable f outer :=
      SimpleGraph.ConnectedComponent.exact ((M.dual_component_subsingleton hM).elim _ _)
    obtain ⟨p, hp⟩ := hr.exists_isPath
    obtain ⟨ds, hn, hh, hl, hz, hs, hf⟩ := M.dual_walk_dart_list hM p
    exact ⟨ds, ⟨hn, hh, hl, hz, hs ▸ hp.support_nodup⟩, hf⟩
  choose paths hpaths hflux using hex
  refine ⟨paths, hpaths, ?_, hflux⟩
  have hn := (hpaths outer).2.2.2.2
  have hh := (hpaths outer).2.1
  cases hd : paths outer with
  | nil => rfl
  | cons d ds =>
    have hf := hh d (by rw [hd]; rfl)
    rw [hd, List.map_cons, List.cons_append] at hn
    have hn := (List.nodup_cons.mp hn).1
    exact (hn (by simp [hf])).elim

-- @node: SphereMap.cycle_stokes
/-- If [the map is connected](hyp:hM), [the outer face lies outside the cycle's left region](hyp:hout),
and [reversing a dart negates its weight](hyp:hw), then [the sum of face circulations
over the left region equals the sum of weights along the cycle](goal). -/
lemma cycle_stokes (hM : M.IsConnectedMap) (C : M.Cycle)
    (outer : M.Face) (hout : outer ∉ M.leftRegion C)
    (w : M.Dart → ℝ) (hw : ∀ d, w (M.edgeInv d) = -w d) :
    (∑ f ∈ Finset.univ.filter (fun f => f ∈ M.leftRegion C), ∑ d ∈ M.faceDarts f, w d) =
      (C.val.map w).sum := by
  have hfiber := Finset.sum_fiberwise_eq_sum_filter (Finset.univ : Finset M.Dart)
    (Finset.univ.filter (fun f => f ∈ M.leftRegion C)) M.faceOf w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hfiber
  change (∑ f ∈ Finset.univ.filter (fun f => f ∈ M.leftRegion C),
    ∑ d ∈ Finset.univ.filter (fun d => M.faceOf d = f), w d) = _
  rw [hfiber]
  have hcancel : (∑ d ∈ Finset.univ.filter (fun d =>
      M.faceOf d ∈ M.leftRegion C ∧ M.edgeOf d ∉ C.val.map M.edgeOf), w d) = 0 := by
    apply Finset.sum_involution (fun d _ => M.edgeInv d)
    · intro d hd
      rw [hw, add_neg_cancel]
    · intro d hd hn
      exact M.edgeInv_fixedPointFree d
    · intro d hd
      obtain ⟨_, hf, he⟩ := Finset.mem_filter.mp hd
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (M.leftRegion_across_noncycle hM C d he).mp hf, ?_⟩
      have hi : M.edgeOf (M.edgeInv d) = M.edgeOf d :=
        (M.edgeOf_eq_iff (M.edgeInv d) d).mpr (Or.inr (M.edgeInv_involutive d).symm)
      simpa only [hi] using he
    · intro d hd
      exact M.edgeInv_involutive d
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ.filter (fun d => M.faceOf d ∈ M.leftRegion C))
    (fun d => M.edgeOf d ∈ C.val.map M.edgeOf) w
  simp only [Finset.filter_filter] at hsplit
  rw [cycle_region_boundary_darts M hM C outer hout, hcancel, add_zero] at hsplit
  rw [← hsplit]
  exact List.sum_toFinset w (C.property.2.of_map M.vert)

-- @node: SphereMap.counterclockwise_outer_not_left
/-- In [a connected map](hyp:hM), if [a cycle is counterclockwise relative to the outer face](hyp:hC),
then [the outer face does not belong to the cycle's left region](goal). -/
lemma counterclockwise_outer_not_left (hM : M.IsConnectedMap) (outer : M.Face)
    (C : M.Cycle) (hC : M.IsCounterclockwise outer C) : outer ∉ M.leftRegion C := by
  obtain ⟨b, hb, hbf⟩ := hC
  rintro ⟨c, hc, hcf⟩
  have he : b = c := M.boundary_unique_in_component b c
    (hM.preconnected.subsingleton_connectedComponent.elim _ _)
    ((M.faceBehind_connected hM _ b outer hbf).trans
      (M.faceBehind_connected hM _ c outer hcf).symm)
  exact hb.2 (he ▸ hc)

-- @node: SphereMap.dualPathWeight_face_sum
/-- If [each face path has net crossing count equal to its starting-face indicator minus
its outer-face indicator](hyp:hflux), then [the dual path weights have circulation one
around each non-outer face and minus the number of non-outer faces around the outer face](goal). -/
lemma dualPathWeight_face_sum (outer : M.Face) (paths : M.Face → List M.Dart)
    (hflux : ∀ f a, (∑ d ∈ M.faceDarts a,
      (((paths f).count d : ℝ) - ((paths f).count (M.edgeInv d) : ℝ))) =
        (if a = f then 1 else 0) - (if a = outer then 1 else 0)) (a : M.Face) :
    (∑ d ∈ M.faceDarts a, M.dualPathWeight outer paths d) =
      if a = outer then -((Fintype.card M.Face - 1 : ℕ) : ℝ) else 1 := by
  unfold dualPathWeight
  rw [Finset.sum_comm]
  simp_rw [hflux]
  by_cases ha : a = outer
  · subst a
    have hterm (f : M.Face) (hf : f ∈ Finset.univ.erase outer) :
        ((if outer = f then 1 else 0) - (if outer = outer then 1 else 0) : ℝ) = -1 := by
      simp [Ne.symm (Finset.mem_erase.mp hf).1]
    rw [Finset.sum_congr rfl hterm]
    simp
  · simp [ha, Finset.sum_ite_eq]

/-- If [the map is connected](hyp:hM), [there are simple dual paths from every face to
the outer face, with an empty path at the outer face, whose weights give circulation one
on every non-outer face and minus their number on the outer face, and strictly positive
circulation along every counterclockwise cycle](goal). -/
-- @node: SphereMap.prescribed_circulation_by_dual_paths
lemma prescribed_circulation_by_dual_paths (hM : M.IsConnectedMap) (outer : M.Face) :
    ∃ paths : M.Face → List M.Dart,
      (∀ f, M.IsDualPath f outer (paths f)) ∧ paths outer = [] ∧
      (∀ f, (∑ d ∈ M.faceDarts f, M.dualPathWeight outer paths d) =
        if f = outer then -((Fintype.card M.Face - 1 : ℕ) : ℝ) else 1) ∧
      (∀ C : M.Cycle, M.IsCounterclockwise outer C →
        0 < (C.val.map (M.dualPathWeight outer paths)).sum) := by
  obtain ⟨paths, hpaths, houter, hflux⟩ := M.exists_simple_dual_paths hM outer
  have hfaces := M.dualPathWeight_face_sum outer paths hflux
  refine ⟨paths, hpaths, houter, hfaces, ?_⟩
  intro C hC
  have hout := M.counterclockwise_outer_not_left hM outer C hC
  rw [← M.cycle_stokes hM C outer hout _ (M.dualPathWeight_edgeInv outer paths)]
  simp_rw [hfaces]
  apply Finset.sum_pos'
  · intro f hf
    have hf : f ≠ outer := fun h => hout (h ▸ (Finset.mem_filter.mp hf).2)
    simp [hf]
  · obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil C.val C.property.1.1
    have hf := M.cycle_face_mem_leftRegion C d hd
    refine ⟨M.faceOf d, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf⟩, ?_⟩
    have hne : M.faceOf d ≠ outer := fun h => hout (h ▸ hf)
    simp [hne]
/-- For [the sphere map](hyp:M), [the componentwise dual path weight](goal) at [a dart](hyp:d)
uses [the global outer face](hyp:outer) and [a family of face paths in each component](hyp:paths):
[first select the component containing the dart's vertex](step:1), then
[evaluate that component's dual path weight using its inherited outer face and the corresponding local dart](step:2). -/
noncomputable def componentwiseDualPathWeight (outer : M.Face)
    (paths : (K : M.Component) → (M.componentMap K).Face → List (M.componentMap K).Dart)
    (d : M.Dart) : ℝ :=
  let K := M.toSimpleGraph.connectedComponentMk (M.vert d)
  (M.componentMap K).dualPathWeight (M.componentOuter K outer) (paths K) (M.componentDart d)

-- @node: SphereMap.componentwiseDualPathWeight_on_component
/-- [The global componentwise weight of a dart belonging to a given component equals
its local dual path weight in that component, using the inherited outer face](goal). -/
lemma componentwiseDualPathWeight_on_component (outer : M.Face)
    (paths : (K : M.Component) → (M.componentMap K).Face → List (M.componentMap K).Dart)
    (K : M.Component) (d : (M.componentMap K).Dart) :
    M.componentwiseDualPathWeight outer paths d.val =
      (M.componentMap K).dualPathWeight (M.componentOuter K outer) (paths K) d := by
  rcases d with ⟨d, hd, hh⟩
  change M.toSimpleGraph.connectedComponentMk (M.vert d) = K at hd
  cases hd
  rfl

-- @node: SphereMap.componentwiseDualPathWeight_edgeInv
/-- [Reversing any dart negates its componentwise dual path weight](goal). -/
lemma componentwiseDualPathWeight_edgeInv (outer : M.Face)
    (paths : (K : M.Component) → (M.componentMap K).Face → List (M.componentMap K).Dart)
    (d : M.Dart) : M.componentwiseDualPathWeight outer paths (M.edgeInv d) =
      -M.componentwiseDualPathWeight outer paths d := by
  let K := M.toSimpleGraph.connectedComponentMk (M.vert d)
  let e : (M.componentMap K).Dart := M.componentDart d
  have hi : ((M.componentMap K).edgeInv e).val = M.edgeInv d :=
    Classical.choose_spec (M.exists_inducedInv _) e
  rw [← hi, M.componentwiseDualPathWeight_on_component,
    (M.componentMap K).dualPathWeight_edgeInv]
  exact congrArg Neg.neg (M.componentwiseDualPathWeight_on_component outer paths K e).symm

set_option backward.isDefEq.respectTransparency false in
-- @node: SphereMap.componentwiseDualPathWeight_cycle
/-- [The sum of componentwise weights along a component cycle viewed globally equals
the sum of local dual path weights along the original cycle](goal). -/
lemma componentwiseDualPathWeight_cycle (outer : M.Face)
    (paths : (K : M.Component) → (M.componentMap K).Face → List (M.componentMap K).Dart)
    (K : M.Component) (C : (M.componentMap K).Cycle) :
    ((M.ofComponentCycle K C).val.map (M.componentwiseDualPathWeight outer paths)).sum =
      (C.val.map ((M.componentMap K).dualPathWeight (M.componentOuter K outer) (paths K))).sum := by
  change ((C.val.map Subtype.val).map _).sum = _
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro d hd
  exact M.componentwiseDualPathWeight_on_component outer paths K d

/-- [There are simple paths to each component's inherited outer face, empty there, whose
local weights have circulation one on every other local face and minus their number on
the local outer face; the assembled global weights change sign under dart reversal and
have strictly positive circulation along every counterclockwise cycle](goal). -/
-- @node: SphereMap.prescribed_component_circulations
lemma prescribed_component_circulations (outer : M.Face) :
    ∃ paths : (K : M.Component) → (M.componentMap K).Face → List (M.componentMap K).Dart,
      (∀ K,
        let N := M.componentMap K
        let o := M.componentOuter K outer
        (∀ f, N.IsDualPath f o (paths K f)) ∧ paths K o = [] ∧
        (∀ f, (∑ d ∈ N.faceDarts f, N.dualPathWeight o (paths K) d) =
          if f = o then -((Fintype.card N.Face - 1 : ℕ) : ℝ) else 1)) ∧
      (∀ d, M.componentwiseDualPathWeight outer paths (M.edgeInv d) =
        -M.componentwiseDualPathWeight outer paths d) ∧
      (∀ C : M.Cycle, M.IsCounterclockwise outer C →
        0 < (C.val.map (M.componentwiseDualPathWeight outer paths)).sum) := by
  have hpaths (K : M.Component) :=
    (M.componentMap K).prescribed_circulation_by_dual_paths
      (M.componentMap_connected K) (M.componentOuter K outer)
  choose paths hspec using hpaths
  refine ⟨paths, ?_, M.componentwiseDualPathWeight_edgeInv outer paths, ?_⟩
  · intro K
    exact ⟨(hspec K).1, (hspec K).2.1, (hspec K).2.2.1⟩
  · intro C hC
    obtain ⟨K, D, rfl⟩ := M.cycle_in_component C
    rw [M.componentwiseDualPathWeight_cycle]
    exact (hspec K).2.2.2 D ((M.component_cycle_orientation K outer D).mpr hC)
end SphereMap

/-- If [the sphere map is a triangulation](hyp:hT), [its face coloring is a partition coloring](hyp:hcol),
and [the given spoke dart weights change sign under reversal](hyp:hw), then
[there are face-vertex incidence weights whose signed spoke dart weights equal the given weights on every dart](goal). -/
-- @node: exists_incidenceWeights_of_antisymmetric
lemma exists_incidenceWeights_of_antisymmetric (T : SphereMap) (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (hcol : PartitionColoring T col) (t0 : T.Face)
    (w : (spokeGraphBounded T col t0 hT hcol).Dart → ℝ)
    (hw : ∀ d, w ((spokeGraphBounded T col t0 hT hcol).edgeInv d) = -w d) :
    ∃ a : IncidenceWeights T col t0, ∀ d, signedSpokeDart T col t0 a d = w d := by
  have hinj (f : T.Face) : Set.InjOn T.vert (↑(T.faceDarts f) : Set T.Dart) := by
    apply Finset.card_image_iff.mp
    rw [← triangulation_faceVertices_eq_image T hT f]
    exact (hT.props.2.2.2 f).2.trans
      ((T.faceLength_eq_card_faceDarts f).symm.trans (hT.props.2.2.2 f).1).symm
  have hcorner (t : blackNonOuter T col t0) (v : T.faceVertices t.val) :
      ∃ d : SpokeCorner T (blackNonOuter T col t0),
        T.faceOf d.val = t.val ∧ T.vert d.val = v.val := by
    have hv := v.property
    simp only [triangulation_faceVertices_eq_image T hT t.val] at hv
    obtain ⟨d, hd, hdv⟩ := Finset.mem_image.mp hv
    have hdf := (Finset.mem_filter.mp hd).2
    exact ⟨⟨d, hdf.symm ▸ t.property⟩, hdf, hdv⟩
  choose corner hface hvert using hcorner
  let a : IncidenceWeights T col t0 := fun t v => w (corner t v, false)
  refine ⟨a, ?_⟩
  rintro ⟨c, b⟩
  let t : blackNonOuter T col t0 := ⟨T.faceOf c.val, c.property⟩
  let v : T.faceVertices t.val := ⟨T.vert c.val, corner_incident T _ c⟩
  have hc : corner t v = c := by
    apply Subtype.ext
    apply hinj t.val
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hface t v⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
    · exact hvert t v
  change (if b then -a t v else a t v) = w (c, b)
  have ha : a t v = w (c, false) := by
    dsimp only [a]
    rw [hc]
  rw [ha]
  cases b with
  | false => rfl
  | true =>
    have hflip : (spokeGraphBounded T col t0 hT hcol).edgeInv (c, false) = (c, true) :=
      (Classical.choose_spec (exists_spokePerms T hT (blackNonOuter T col t0)
        (bounded_faces_disjoint T col t0 hcol))).1 (c, false)
    exact (hflip ▸ hw (c, false)).symm

/-- If [the sphere map is a triangulation](hyp:hT) and [its face coloring is a partition coloring](hyp:hcol),
then [there are face-vertex incidence weights giving strictly positive signed spoke
weight to every cycle counterclockwise relative to the inherited outer face of the bounded spoke graph](goal). -/
-- @node: lem:circulation
lemma exists_positive_spoke_weights (T : SphereMap) (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (hcol : PartitionColoring T col) (t0 : T.Face) :
    ∃ a : IncidenceWeights T col t0,
      ∀ C : (spokeGraphBounded T col t0 hT hcol).Cycle,
        (spokeGraphBounded T col t0 hT hcol).IsCounterclockwise (spokeOuter T col t0 hT hcol) C →
          0 < signedSpokeWeight T col t0 hT hcol a C := by
  let M := spokeGraphBounded T col t0 hT hcol
  let outer := spokeOuter T col t0 hT hcol
  obtain ⟨paths, hfaces, hanti, hpositive⟩ := M.prescribed_component_circulations outer
  obtain ⟨a, ha⟩ := exists_incidenceWeights_of_antisymmetric T hT col hcol t0
    (M.componentwiseDualPathWeight outer paths) hanti
  refine ⟨a, ?_⟩
  intro C hC
  unfold signedSpokeWeight
  have heq : C.val.map (signedSpokeDart T col t0 a) =
      C.val.map (M.componentwiseDualPathWeight outer paths) := by
    apply List.map_congr_left
    intro d hd
    exact ha d
  rw [heq]
  exact hpositive C hC


end OaiPairedStatesHamiltonian

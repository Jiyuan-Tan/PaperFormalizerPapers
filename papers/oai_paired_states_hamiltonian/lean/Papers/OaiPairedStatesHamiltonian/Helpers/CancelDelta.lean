module

public import Papers.OaiPairedStatesHamiltonian.Helpers.CancelSwitch

/-! Local triangle signs and the phase change under an opposite-cycle switch. -/

public section

namespace OaiPairedStatesHamiltonian

set_option linter.style.openClassical false
open Classical
attribute [local instance] propDecidable

variable (T : SphereMap)

-- @node: triangle_face_tail_injective
/-- In [a sphere triangulation](hyp:hT), [distinct darts belonging to the same face have distinct starting vertices](goal). -/
lemma triangle_face_tail_injective (hT : IsSphereTriangulation T) (f : T.Face) :
    Set.InjOn T.vert (T.faceDarts f) := by
  apply Finset.card_image_iff.mp
  rw [← triangulation_faceVertices_eq_image T hT f,
    (hT.props.2.2.2 f).2, ← T.faceLength_eq_card_faceDarts,
    (hT.props.2.2.2 f).1]

-- @node: triangle_face_endpoint_injective
/-- In [a sphere triangulation](hyp:hT), if [two darts belong to the same face](hyp:hf) and [have the same starting vertex or the same ending vertex](hyp:hv), then [the darts are equal](goal). -/
lemma triangle_face_endpoint_injective (hT : IsSphereTriangulation T) (d e : T.Dart)
    (hf : T.faceOf d = T.faceOf e)
    (hv : T.vert d = T.vert e ∨ T.head d = T.head e) : d = e := by
  have hd : d ∈ T.faceDarts (T.faceOf d) := by simp [SphereMap.faceDarts]
  have he : e ∈ T.faceDarts (T.faceOf d) := by simp [SphereMap.faceDarts, hf]
  rcases hv with hv | hv
  · exact triangle_face_tail_injective T hT _ hd he hv
  · apply T.facePerm.injective
    apply triangle_face_tail_injective T hT (T.faceOf d)
    · simpa [SphereMap.faceDarts] using T.dual_rot_vertex d
    · simp [SphereMap.faceDarts, T.dual_rot_vertex e, hf]
    · exact (T.rot_vertex _).trans (hv.trans (T.rot_vertex _).symm)

-- @node: delta_edgeInv
/-- If [the face coloring assigns opposite colors across every edge](hyp:hc), then [reversing a dart negates its color sign](goal). -/
lemma delta_edgeInv (col : T.Face → Bool) (hc : PartitionColoring T col) (d : T.Dart) :
    delta T col (T.edgeInv d) = -delta T col d := by
  have h := hc d
  cases hd : col (T.faceOf d) <;> cases he : col (T.faceOf (T.edgeInv d)) <;>
    simp_all [delta]

-- @node: delta_triangle_shared_endpoint
/-- In [a sphere triangulation](hyp:hT) with [opposite face colors across every edge](hyp:hc), suppose [d has face f on one of its sides](hyp:hd), [e also has face f on one of its sides](hyp:he), [the darts share a starting vertex or share an ending vertex](hyp:hv), and [they are distinct](hyp:hne). Then [the color sign of e is the negative of the color sign of d](goal). -/
lemma delta_triangle_shared_endpoint (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (hc : PartitionColoring T col) (f : T.Face)
    (d e : T.Dart) (hd : T.faceOf d = f ∨ T.faceOf (T.edgeInv d) = f)
    (he : T.faceOf e = f ∨ T.faceOf (T.edgeInv e) = f)
    (hv : T.vert d = T.vert e ∨ T.head d = T.head e) (hne : d ≠ e) :
    delta T col e = -delta T col d := by
  have hinv : T.vert (T.edgeInv d) = T.vert (T.edgeInv e) ∨
      T.head (T.edgeInv d) = T.head (T.edgeInv e) := by
    rcases hv with hv | hv
    · apply Or.inr
      change T.vert (T.edgeInv (T.edgeInv d)) = T.vert (T.edgeInv (T.edgeInv e))
      rw [T.edgeInv_involutive, T.edgeInv_involutive]
      exact hv
    · exact Or.inl hv
  have hne' : T.edgeInv d ≠ T.edgeInv e := fun h => hne (T.edgeInv.injective h)
  rcases hd with hd | hd
  · have hei : T.faceOf (T.edgeInv e) = f := he.resolve_left (fun he =>
      hne (triangle_face_endpoint_injective T hT d e (hd.trans he.symm) hv))
    have hsign : delta T col (T.edgeInv e) = delta T col d := by simp [delta, hei, hd]
    rw [delta_edgeInv T col hc] at hsign
    omega
  · have he : T.faceOf e = f := he.resolve_right (fun he =>
      hne' (triangle_face_endpoint_injective T hT _ _ (hd.trans he.symm) hinv))
    calc
      delta T col e = delta T col (T.edgeInv d) := by simp [delta, he, hd]
      _ = -delta T col d := delta_edgeInv T col hc d

-- @node: delta_opposite_switch
/-- In [a sphere triangulation](hyp:hT) with [opposite face colors across every edge](hyp:hc), suppose [v differs from u](hyp:hvu), [u differs from w](hyp:huw), and three darts run along sides of face f: [d from v to w](hyp:hd), [a from v to u](hyp:ha), and [b from u to w](hyp:hb). Then [the color sign of b minus the color sign of d equals twice the color sign of a](goal). -/
lemma delta_opposite_switch (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (hc : PartitionColoring T col) (f : T.Face)
    (v w u : T.Vertex) (hvu : v ≠ u) (huw : u ≠ w)
    (d a b : T.Dart) (hd : FaceDart T f v w d)
    (ha : FaceDart T f v u a) (hb : FaceDart T f u w b) :
    delta T col b - delta T col d = 2 * delta T col a := by
  have hda := delta_triangle_shared_endpoint T hT col hc f d a hd.2.2 ha.2.2
    (Or.inl (hd.1.trans ha.1.symm)) (fun he => huw
      (ha.2.1.symm.trans ((congrArg T.head he).symm.trans hd.2.1)))
  have hdb := delta_triangle_shared_endpoint T hT col hc f d b hd.2.2 hb.2.2
    (Or.inr (hd.2.1.trans hb.2.1.symm)) (fun he => hvu
      (hd.1.symm.trans ((congrArg T.vert he).trans hb.1)))
  omega

variable (col : T.Face → Bool) (t0 : T.Face)

-- @node: opposite_cycle_switch_delta
/-- In [a sphere triangulation](hyp:hT) with [opposite face colors across every edge](hyp:hc), suppose [r is paired with s](hyp:h), [q is paired with s](hyp:hq), [every dart of a simple directed cycle is an opposite dart for r and s](hyp:hC), and [q replaces r's selection by the third vertex exactly on faces whose opposite darts lie on that cycle](hyp:hswitch). Then [the paired dart-sign sum for q and s minus that for r and s is twice the sum of the cycle's dart signs, using the normalized coloring throughout](goal). -/
lemma opposite_cycle_switch_delta (hT : IsSphereTriangulation T)
    (hc : PartitionColoring T col) (r s q : State T col t0)
    (h : IsPair T col t0 r s) (hq : IsPair T col t0 q s) (C : T.Cycle)
    (hC : ∀ d ∈ C.val, ∃ t, oppositeDart T col t0 hT r s h t = d)
    (hswitch : ∀ t : blackNonOuter T col t0,
      (q.val t).val = if oppositeDart T col t0 hT r s h t ∈ C.val then
        (oppositeThirdVertex T col t0 hT r s h t).val else (r.val t).val) :
    pairDeltaSum T col t0 hT q s hq - pairDeltaSum T col t0 hT r s h =
      2 * (C.val.map (delta T (normalizedColoring T col t0))).sum := by
  let A := Finset.univ.filter (fun t => oppositeDart T col t0 hT r s h t ∈ C.val)
  have heq : A.image (oppositeDart T col t0 hT r s h) = C.val.toFinset := by
    ext d
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      List.mem_toFinset, A]
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ht
    · intro hd
      obtain ⟨t, rfl⟩ := hC d hd
      exact ⟨t, hd, rfl⟩
  have hlocal (t : blackNonOuter T col t0) :
      delta T (normalizedColoring T col t0) (pairedDart T col t0 hT q s hq t) -
        delta T (normalizedColoring T col t0) (pairedDart T col t0 hT r s h t) =
        if oppositeDart T col t0 hT r s h t ∈ C.val then
          2 * delta T (normalizedColoring T col t0) (oppositeDart T col t0 hT r s h t)
        else 0 := by
    have ht := hswitch t
    by_cases hd : oppositeDart T col t0 hT r s h t ∈ C.val
    · rw [if_pos hd] at ht ⊢
      apply delta_opposite_switch T hT _ (normalizedColoring_partition T col hc t0)
        t.val (r.val t).val (s.val t).val (oppositeThirdVertex T col t0 hT r s h t).val
        (Ne.symm (oppositeThirdVertex T col t0 hT r s h t).property.2.1)
        (oppositeThirdVertex T col t0 hT r s h t).property.2.2
      · exact pairedDart_spec T col t0 hT r s h t
      · exact oppositeDart_spec T col t0 hT r s h t
      · have hh := pairedDart_spec T col t0 hT q s hq t
        exact ⟨hh.1.trans ht, hh.2⟩
    · rw [if_neg hd] at ht ⊢
      have hdarts : pairedDart T col t0 hT q s hq t = pairedDart T col t0 hT r s h t := by
        apply T.dart_eq_of_endpoints hT.props.2.1
        · exact (pairedDart_spec T col t0 hT q s hq t).1.trans
            (ht.trans (pairedDart_spec T col t0 hT r s h t).1.symm)
        · exact (pairedDart_spec T col t0 hT q s hq t).2.1.trans
            (pairedDart_spec T col t0 hT r s h t).2.1.symm
      rw [hdarts, sub_self]
  unfold pairDeltaSum
  rw [← Finset.sum_sub_distrib]
  change (∑ t, (delta T (normalizedColoring T col t0) (pairedDart T col t0 hT q s hq t) -
    delta T (normalizedColoring T col t0) (pairedDart T col t0 hT r s h t))) = _
  simp_rw [hlocal]
  rw [← Finset.sum_filter]
  change (∑ t ∈ A, 2 * delta T (normalizedColoring T col t0)
    (oppositeDart T col t0 hT r s h t)) = _
  rw [← Finset.mul_sum]
  congr 1
  rw [← List.sum_toFinset _ (C.property.2.of_map T.vert), ← heq]
  symm
  apply Finset.sum_image
  intro t ht u hu he
  exact oppositeDart_tail_injective T col t0 hT r s h t u (congrArg T.vert he)

-- @node: opposite_cycle_switch_phase
/-- In [a sphere triangulation](hyp:hT) with [opposite face colors across every edge](hyp:hc), suppose [r is paired with s](hyp:h), [q is paired with s](hyp:hq), [every dart of a simple directed cycle is an opposite dart for r and s](hyp:hC), and [q replaces r's selection by the third vertex exactly on faces whose opposite darts lie on that cycle](hyp:hswitch). Then [the phase index of q and s minus that of r and s is two modulo four](goal). -/
lemma opposite_cycle_switch_phase (hT : IsSphereTriangulation T)
    (hc : PartitionColoring T col) (r s q : State T col t0)
    (h : IsPair T col t0 r s) (hq : IsPair T col t0 q s) (C : T.Cycle)
    (hC : ∀ d ∈ C.val, ∃ t, oppositeDart T col t0 hT r s h t = d)
    (hswitch : ∀ t : blackNonOuter T col t0,
      (q.val t).val = if oppositeDart T col t0 hT r s h t ∈ C.val then
        (oppositeThirdVertex T col t0 hT r s h t).val else (r.val t).val) :
    (J T col t0 hT q s hq - J T col t0 hT r s h) % 4 = 2 := by
  let choice : EdgeChoice T col t0 r := fun t =>
    ⟨(oppositeThirdVertex T col t0 hT r s h t).val,
      (oppositeThirdVertex T col t0 hT r s h t).property.1,
      (oppositeThirdVertex T col t0 hT r s h t).property.2.1⟩
  have hchosen : ∀ d ∈ C.val, d ∈ ChosenEdges T col t0 hT r choice := by
    intro d hd
    obtain ⟨t, rfl⟩ := hC d hd
    exact Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩
  have hdelta := delta_sum_of_simple_cycle T hT col hc t0 r choice C hchosen
  have hd := opposite_cycle_switch_delta T col t0 hT hc r s q h hq C hC hswitch
  have hr := three_mul_J T col t0 hT hc r s h
  have hq' := three_mul_J T col t0 hT hc q s hq
  have hsides : t0 ∈ T.leftRegion C ∨ t0 ∈ T.rightRegion C := by
    change t0 ∈ T.leftRegion C ∪ T.rightRegion C
    rw [(T.cycle_sides_partition C).2]
    exact Set.mem_univ t0
  rcases hsides with hcw | hccw
  · have he := hdelta.2.2 hcw
    rw [he] at hd
    have hj : J T col t0 hT q s hq - J T col t0 hT r s h = 2 := by omega
    rw [hj]
    norm_num
  · have he := hdelta.2.1 hccw
    rw [he] at hd
    have hj : J T col t0 hT q s hq - J T col t0 hT r s h = -2 := by omega
    rw [hj]
    norm_num

end OaiPairedStatesHamiltonian

module

public import Papers.OaiPairedStatesHamiltonian.Helpers.DensityFlowCounts
public import Mathlib.Combinatorics.Hall.Basic

/-! Local component, region, density and incidence-flow counts. -/

public section

namespace OaiPairedStatesHamiltonian

set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.unusedVariables false
open Classical
attribute [local instance] propDecidable


-- @node: incidence_flow_inequality
/-- For [a sphere triangulation](hyp:hT) with [oppositely colored adjacent
faces](hyp:hcol) and [no simple three-edge cycle with vertices strictly on
both sides](hyp:hsep),
[the complement of any set of nonroot vertices has induced-edge count minus
retained black-face count at most twice its vertex count minus four; moreover,
twice the size of the nonroot set is at most the sum over nonouter black faces
of their incidences with that set, capped at two per face](goal).

The vertices of the designated outer face are roots, and colors are normalized
so that this face is black. -/
lemma incidence_flow_inequality (T : SphereMap) (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (hcol : PartitionColoring T col) (t0 : T.Face)
    (hsep : PairsNoSeparatingTriangle T) (S : Finset (nonRoot T t0)) :
      -- @realizes S(subset of the nonroot vertices in the incidence-flow inequality)
    let U := Finset.univ \ S.image Subtype.val -- @realizes U(complement of S, containing the roots)
    let e := fun U : Finset T.Vertex => Fintype.card (T.induce (↑U : Set T.Vertex)).Edge
      -- @realizes e(induced-edge count function e(U))
    let b := fun U : Finset T.Vertex =>
      (Finset.univ.filter (fun t => normalizedColoring T col t0 t = true ∧ T.faceVertices t ⊆ U)).card
      -- @realizes b(actual black-face count function b(U))
    (e U : ℤ) - b U ≤ 2 * U.card - 4 ∧
      2 * S.card ≤ ∑ t : blackNonOuter T col t0,
        min 2 ((T.faceVertices t.val) ∩ S.image Subtype.val).card := by
  let U := Finset.univ \ S.image Subtype.val
  let c := normalizedColoring T col t0
  have hc : PartitionColoring T c := normalizedColoring_partition T col hcol t0
  have hroot : T.faceVertices t0 ⊆ U := by
    intro v hv
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hS
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hS
    exact (Finset.mem_sdiff.mp w.property).2 hv
  have hbound := T.density_bound_containing_face hT c hc hsep U t0
    (normalizedColoring_self T col t0) hroot
  refine ⟨hbound, ?_⟩
  have hi := T.density_incidence_identity hT c hc U
  have hzero : min 2 ((T.faceVertices t0) \ U).card = 0 := by
    rw [Finset.sdiff_eq_empty_iff_subset.mpr hroot]
    simp
  have hblack : blackNonOuter T col t0 =
      (Finset.univ.filter (fun f => c f = true)).erase t0 := by
    ext f
    simp [blackNonOuter, c, and_comm]
  have hsum : (∑ t : blackNonOuter T col t0,
        min 2 ((T.faceVertices t.val) ∩ S.image Subtype.val).card) =
      ∑ f ∈ Finset.univ.filter (fun f => c f = true),
        min 2 ((T.faceVertices f) \ U).card := by
    have hdiff (f : T.Face) : (T.faceVertices f) ∩ S.image Subtype.val =
        (T.faceVertices f) \ U := by
      ext v
      simp [U]
    simp_rw [hdiff]
    calc
      _ = ∑ f ∈ blackNonOuter T col t0, min 2 ((T.faceVertices f) \ U).card := by
        convert Finset.sum_coe_sort (blackNonOuter T col t0)
          (fun f => min 2 ((T.faceVertices f) \ U).card) using 1
      _ = _ := by
        rw [hblack]
        exact Finset.sum_erase _ hzero
  have hcards : U.card + S.card = Fintype.card T.Vertex := by
    have hs : (S.image Subtype.val).card = S.card :=
      Finset.card_image_of_injective _ Subtype.val_injective
    have h := Finset.card_sdiff_add_card_eq_card (s := S.image Subtype.val)
      (Finset.subset_univ (S.image Subtype.val))
    simpa only [hs, Finset.card_univ] using h
  have hvertices := (standingCounts_of_triangulation T hT c hc).2.2
  rw [hsum]
  have hiz := congrArg (fun n : ℕ => (n : ℤ)) hi
  push_cast at hiz
  omega

-- @node: capacityTwo_incidence
/-- If [the two finite sides of a relation have equal size](hyp:hcard) and
[every subset of the right side has twice its size bounded by the sum of its
neighbor counts on the left, capped at two per left element](hyp:hcap), then
[there is a set of related pairs in which every element on each side occurs
in exactly two pairs](goal). -/
lemma capacityTwo_incidence {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (r : α → β → Prop) (hcard : Fintype.card α = Fintype.card β)
    (hcap : ∀ B : Finset β, 2 * B.card ≤
      ∑ a : α, min 2 (Finset.univ.filter (fun b => r a b ∧ b ∈ B)).card) :
    ∃ E : Finset (α × β), (∀ i ∈ E, r i.1 i.2) ∧
      (∀ a, (E.filter (fun i => i.1 = a)).card = 2) ∧
      (∀ b, (E.filter (fun i => i.2 = b)).card = 2) := by
  classical
  let I := {i : α × β // r i.1 i.2}
  let rel : (β × Fin 2 ⊕ I) → (α × Fin 2 ⊕ I) → Prop
    | .inl b, .inr e => e.val.2 = b.1
    | .inr e, .inl a => e.val.1 = a.1
    | .inr e, .inr f => e = f
    | _, _ => False
  have hall (s : Finset (β × Fin 2 ⊕ I)) :
      s.card ≤ (Finset.univ.filter (fun y => ∃ x ∈ s, rel x y)).card := by
    let B := s.toLeft.image Prod.fst
    let K := s.toRight.image (fun e => e.val.1)
    let D := (Finset.univ : Finset I).filter (fun e => e.val.2 ∈ B)
    let J := D \ s.toRight
    have hs : s.toLeft.card ≤ 2 * B.card := by
      calc
        _ ≤ (B.product (Finset.univ : Finset (Fin 2))).card := by
          apply Finset.card_le_card
          intro b hb
          exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨b, hb, rfl⟩, Finset.mem_univ _⟩
        _ = _ := by simp [Nat.mul_comm]
    have hrow (a : α) :
        min 2 (Finset.univ.filter (fun b => r a b ∧ b ∈ B)).card ≤
          (J.filter (fun e => e.val.1 = a)).card + if a ∈ K then 2 else 0 := by
      by_cases ha : a ∈ K
      · simp only [ha, if_true]
        exact (min_le_left _ _).trans (Nat.le_add_left _ _)
      · simp only [ha, if_false, Nat.add_zero]
        apply (min_le_right _ _).trans
        apply le_of_eq
        symm
        apply Finset.card_bij
          (fun e _ => e.val.2)
        · intro e he
          obtain ⟨he, hea⟩ := Finset.mem_filter.mp he
          obtain ⟨heD, heF⟩ := Finset.mem_sdiff.mp he
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hea ▸ e.property,
            (Finset.mem_filter.mp heD).2⟩
        · intro e he f hf hef
          apply Subtype.ext
          exact Prod.ext ((Finset.mem_filter.mp he).2.trans
            (Finset.mem_filter.mp hf).2.symm) hef
        · intro b hb
          have hr := (Finset.mem_filter.mp hb).2.1
          refine ⟨⟨(a, b), hr⟩, Finset.mem_filter.mpr ⟨?_, rfl⟩, rfl⟩
          apply Finset.mem_sdiff.mpr
          refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            (Finset.mem_filter.mp hb).2.2⟩, ?_⟩
          intro he
          exact ha (Finset.mem_image.mpr ⟨⟨(a, b), hr⟩, he, rfl⟩)
    have hj : (∑ a : α, (J.filter (fun e => e.val.1 = a)).card) = J.card := by
      simpa using (Finset.card_eq_sum_card_fiberwise
        (s := J) (t := Finset.univ) (f := fun e : I => e.val.1)
        (fun _ _ => Finset.mem_univ _)).symm
    have hk : (∑ a : α, if a ∈ K then 2 else 0) = 2 * K.card := by
      simp [Finset.sum_ite, Nat.mul_comm]
    have hbound : 2 * B.card ≤ J.card + 2 * K.card := by
      calc
        _ ≤ _ := hcap B
        _ ≤ ∑ a : α, ((J.filter (fun e => e.val.1 = a)).card +
            if a ∈ K then 2 else 0) := Finset.sum_le_sum (fun a _ => hrow a)
        _ = _ := by rw [Finset.sum_add_distrib, hj, hk]
    have hn : ((K.product (Finset.univ : Finset (Fin 2))).disjSum
        (D ∪ s.toRight)) ⊆ Finset.univ.filter (fun y => ∃ x ∈ s, rel x y) := by
      intro y hy
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      cases y with
      | inl a =>
        have ha : a.1 ∈ K := by simpa using hy
        obtain ⟨e, he, hea⟩ := Finset.mem_image.mp ha
        exact ⟨Sum.inr e, Finset.mem_toRight.mp he, hea⟩
      | inr e =>
        have he' : e ∈ D ∨ e ∈ s.toRight := by simpa using hy
        rcases he' with he | he
        · obtain ⟨b, hb, hbe⟩ := Finset.mem_image.mp (Finset.mem_filter.mp he).2
          exact ⟨Sum.inl b, Finset.mem_toLeft.mp hb, hbe.symm⟩
        · exact ⟨Sum.inr e, Finset.mem_toRight.mp he, rfl⟩
    have hc := Finset.card_le_card hn
    rw [Finset.card_disjSum] at hc
    have hp : (K.product (Finset.univ : Finset (Fin 2))).card = K.card * 2 := by simp
    rw [hp] at hc
    have hu : (D ∪ s.toRight).card = J.card + s.toRight.card := by
      exact (Finset.card_sdiff_add_card D s.toRight).symm
    rw [hu] at hc
    have hsplit := s.card_toLeft_add_card_toRight
    omega
  obtain ⟨f, hf, hrel⟩ :=
    (Fintype.all_card_le_filter_rel_iff_exists_injective rel).mp hall
  have hex (b : β × Fin 2) : ∃ e : I, f (Sum.inl b) = Sum.inr e ∧ e.val.2 = b.1 := by
    have h := hrel (Sum.inl b)
    cases he : f (Sum.inl b) with
    | inl a => simp [he, rel] at h
    | inr e => exact ⟨e, rfl, by simpa [he, rel] using h⟩
  choose edge hedge hbeta using hex
  have hinj : Function.Injective edge := by
    intro b c h
    apply Sum.inl_injective
    apply hf
    rw [hedge, hedge, h]
  let chosen : Finset I := Finset.univ.image edge
  have hcol (b : β) : (chosen.filter (fun e => e.val.2 = b)).card = 2 := by
    have heq : chosen.filter (fun e => e.val.2 = b) =
        Finset.univ.image (fun j : Fin 2 => edge (b, j)) := by
      ext e
      constructor
      · intro he
        obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp he).1
        have hb : c.1 = b := (hbeta c).symm.trans (Finset.mem_filter.mp he).2
        exact Finset.mem_image.mpr ⟨c.2, Finset.mem_univ _, by rw [← hb]⟩
      · intro he
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp he
        exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨(b, j), Finset.mem_univ _, rfl⟩,
          hbeta (b, j)⟩
    rw [heq, Finset.card_image_of_injective]
    · simp
    · intro j k h
      exact congrArg Prod.snd (hinj h)
  have hslot (b : β × Fin 2) :
      ∃ j : Fin 2, f (Sum.inr (edge b)) = Sum.inl ((edge b).val.1, j) := by
    have h := hrel (Sum.inr (edge b))
    cases he : f (Sum.inr (edge b)) with
    | inl a =>
      have ha : (edge b).val.1 = a.1 := by simpa [he, rel] using h
      exact ⟨a.2, by simpa [ha] using he⟩
    | inr e =>
      have heq : edge b = e := by simpa [he, rel] using h
      have hn := hf ((hedge b).trans ((congrArg Sum.inr heq).trans he.symm))
      cases hn
  let slot (e : I) : Fin 2 := (f (Sum.inr e)).elim Prod.snd (fun _ => 0)
  have hused (e : I) (he : e ∈ chosen) :
      f (Sum.inr e) = Sum.inl (e.val.1, slot e) := by
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨j, hj⟩ := hslot b
    simpa only [slot, hj, Sum.elim_inl] using hj
  have hrow_le (a : α) : (chosen.filter (fun e => e.val.1 = a)).card ≤ 2 := by
    have hc : (chosen.filter (fun e => e.val.1 = a)).card ≤
        (Finset.univ : Finset (Fin 2)).card := by
      apply Finset.card_le_card_of_injOn slot (fun _ _ => Finset.mem_univ _)
      intro e he g hg h
      apply Sum.inr_injective
      apply hf
      rw [hused e (Finset.mem_filter.mp he).1,
        hused g (Finset.mem_filter.mp hg).1,
        (Finset.mem_filter.mp he).2, (Finset.mem_filter.mp hg).2, h]
    simpa using hc
  have htotal : chosen.card = Fintype.card β * 2 := by
    dsimp only [chosen]
    rw [Finset.card_image_of_injective _ hinj]
    simp
  have hsum : (∑ a : α, (chosen.filter (fun e => e.val.1 = a)).card) = ∑ _a : α, 2 := by
    have hc := Finset.card_eq_sum_card_fiberwise
      (s := chosen) (t := Finset.univ) (f := fun e : I => e.val.1)
      (fun _ _ => Finset.mem_univ _)
    rw [← hc, htotal]
    simp [hcard]
  have hrow (a : α) : (chosen.filter (fun e => e.val.1 = a)).card = 2 :=
    (Finset.sum_eq_sum_iff_of_le (fun a _ => hrow_le a)).mp hsum a (Finset.mem_univ _)
  refine ⟨chosen.image Subtype.val, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hi
    exact e.property
  · intro a
    rw [Finset.filter_image]
    rw [Finset.card_image_of_injective _ Subtype.val_injective]
    exact hrow a
  · intro b
    rw [Finset.filter_image]
    rw [Finset.card_image_of_injective _ Subtype.val_injective]
    exact hcol b


-- @node: exists_degreeTwo_incidence
/-- For [a sphere triangulation](hyp:hT) with [oppositely colored adjacent
faces](hyp:hcol) and [no simple three-edge cycle with vertices strictly on
both sides](hyp:hsep),
[one can select distinct incident pairs of nonouter black faces and nonroot
vertices so that every such face and every such vertex occurs in exactly two
selected pairs](goal).

Colors are normalized so that the designated outer face is black, and its
vertices are the roots. -/
lemma exists_degreeTwo_incidence (T : SphereMap) (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (hcol : PartitionColoring T col) (t0 : T.Face)
    (hsep : PairsNoSeparatingTriangle T) :
    ∃ chosen : Finset (blackNonOuter T col t0 × nonRoot T t0),
      (∀ i ∈ chosen, i.2.val ∈ T.faceVertices i.1.val) ∧
      (∀ t, (chosen.filter (fun i => i.1 = t)).card = 2) ∧
      (∀ v, (chosen.filter (fun i => i.2 = v)).card = 2) := by
  have hcard : Fintype.card (blackNonOuter T col t0) = Fintype.card (nonRoot T t0) := by
    have hc := stateSetsCard_of_triangulation T hT col hcol t0
    simpa only [Fintype.card_coe] using hc.1.trans hc.2.symm
  refine capacityTwo_incidence (α := blackNonOuter T col t0) (β := nonRoot T t0)
    (fun t v => v.val ∈ T.faceVertices t.val) hcard ?_
  intro S
  have hc := (incidence_flow_inequality T hT col hcol t0 hsep S).2
  have hcount (t : blackNonOuter T col t0) :
      (Finset.univ.filter (fun v : nonRoot T t0 =>
        v.val ∈ T.faceVertices t.val ∧ v ∈ S)).card =
      ((T.faceVertices t.val) ∩ S.image Subtype.val).card := by
    apply Finset.card_bij (fun v _ => v.val)
    · intro v hv
      obtain ⟨_, hface, hS⟩ := Finset.mem_filter.mp hv
      exact Finset.mem_inter.mpr ⟨hface, Finset.mem_image.mpr ⟨v, hS, rfl⟩⟩
    · intro v hv w hw h
      exact Subtype.ext h
    · intro v hv
      obtain ⟨hface, hS⟩ := Finset.mem_inter.mp hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hS
      exact ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hface, hw⟩, rfl⟩
  calc
    _ ≤ _ := hc
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t ht
      apply congrArg (min 2)
      calc
        _ = _ := (hcount t).symm
        _ = _ := by
          apply congrArg Finset.card
          ext v
          simp


end OaiPairedStatesHamiltonian

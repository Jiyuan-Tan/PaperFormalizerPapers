module

public import Papers.OaiNearInclusionsVon.Helpers.MainRepresentation
public import Papers.OaiNearInclusionsVon.Helpers.MatrixLimits

/-! Fresh-generator conjugation and joint WOT limits for the main construction. -/

@[expose] public section

set_option linter.style.longLine false

namespace Papers.OaiNearInclusionsVon

open Filter
open scoped Topology

-- @node: reduced_append_fresh
/-- If [a word is reduced](hyp:hw) and [a generator occurs nowhere in that
word](hyp:hj), [appending that generator with either sign leaves the word
reduced](goal). -/
lemma reduced_append_fresh (w : List (ℕ × Bool)) (hw : FreeGroup.IsReduced w)
    (j : ℕ) (b : Bool) (hj : ∀ a ∈ w, a.1 ≠ j) :
    FreeGroup.IsReduced (w ++ [(j, b)]) := by
  apply List.IsChain.append hw (FreeGroup.IsReduced.singleton)
  intro a ha c hc hac
  have ha' : a ∈ w := List.mem_of_mem_getLast? ha
  have hc' : c = (j, b) := by simpa using hc.symm
  subst c
  exact False.elim (hj a ha' hac)

-- @node: conjugate_toWord_of_fresh
/-- If [a free-group element is not the identity](hyp:hx) and [a generator
occurs nowhere in its reduced word](hyp:hj), [the reduced word of its conjugate
by that generator consists of the positive generator, the original reduced word,
and the negative generator, in that order](goal). -/
lemma conjugate_toWord_of_fresh (x : FreeGrp) (hx : x ≠ 1) (j : ℕ)
    (hj : ∀ a ∈ x.toWord, a.1 ≠ j) :
    (gen j * x * (gen j)⁻¹).toWord = (j, true) :: (x.toWord ++ [(j, false)]) := by
  have hw := reduced_append_fresh x.toWord FreeGroup.isReduced_toWord j false hj
  have hne : x.toWord ≠ [] := fun h => hx (FreeGroup.toWord_eq_nil_iff.mp h)
  have hred : FreeGroup.IsReduced ((j, true) :: (x.toWord ++ [(j, false)])) := by
    obtain ⟨a, l, heq⟩ := List.exists_cons_of_ne_nil hne
    rw [heq, List.cons_append] at hw ⊢
    apply FreeGroup.isReduced_cons_cons.mpr
    refine ⟨fun h => False.elim (hj a (by simp [heq]) h.symm), hw⟩
  rw [FreeGroup.toWord_mul, FreeGroup.toWord_mul, gen, FreeGroup.toWord_of,
    FreeGroup.toWord_inv, FreeGroup.toWord_of]
  change FreeGroup.reduce (FreeGroup.reduce ((j, true) :: x.toWord) ++ [(j, false)]) = _
  rw [← FreeGroup.reduce_singleton (j, false), FreeGroup.reduce_append_reduce_reduce,
    FreeGroup.reduce_singleton]
  exact hred.reduce_eq

-- @node: conjugate_gen_eventually_ne
/-- If [a free-group element is not the identity](hyp:hx), [its conjugates by
generators of sufficiently large index differ from any prescribed fixed
free-group element](goal). -/
lemma conjugate_gen_eventually_ne (x y : FreeGrp) (hx : x ≠ 1) :
    ∀ᶠ j : ℕ in atTop, gen j * x * (gen j)⁻¹ ≠ y := by
  let letters := (x.toWord ++ y.toWord).map Prod.fst
  have hfresh : ∀ᶠ j : ℕ in atTop, ∀ a ∈ letters, a ≠ j := by
    refine eventually_atTop.2 ⟨letters.foldr max 0 + 1, ?_⟩
    intro j hj a ha heq
    have hle : ∀ (l : List ℕ) (a : ℕ), a ∈ l → a ≤ l.foldr max 0 := by
      intro l
      induction l with
      | nil => simp
      | cons b l ih =>
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact le_max_left _ _
        · exact (ih a ha).trans (le_max_right _ _)
    have := hle letters a ha
    omega
  filter_upwards [hfresh] with j hj
  have hxj : ∀ a ∈ x.toWord, a.1 ≠ j := by
    intro a ha
    exact hj a.1 (List.mem_map.mpr ⟨a, List.mem_append_left _ ha, rfl⟩)
  intro heq
  have hword := conjugate_toWord_of_fresh x hx j hxj
  rw [heq] at hword
  have hmem : (j, true) ∈ y.toWord := by rw [hword]; exact List.mem_cons_self
  exact hj j (List.mem_map.mpr ⟨(j, true), List.mem_append_right _ hmem, rfl⟩) rfl

-- @node: projE_apply_coordinate
/-- For any vector in the free-group Hilbert space, [its root projection is
the vector retaining its identity coordinate and setting every other coordinate
to zero](goal). -/
lemma projE_apply_coordinate (η : TreeSpace) : projE η = lp.single 2 1 (η 1) := by
  rw [projE, Submodule.starProjection_singleton]
  simp only [treeBasis, lp.inner_single_left, lp.norm_single (show (0 : ENNReal) < 2 by norm_num),
    norm_one, one_pow, div_one, RCLike.inner_apply, map_one, mul_one]
  ext x
  by_cases h : 1 = x <;> simp [lp.single_apply, h]

-- @node: lp_bounded_wot_of_single_tests
/-- Consider [a sequence of bounded operators on a Hilbert direct sum](hyp:T)
and [a candidate limiting operator](hyp:R). If [the sequence has a common
operator-norm bound](hyp:hC) and [every matrix coefficient between vectors
supported at individual coordinates converges to that of the candidate](hyp:h),
then for [any two vectors in the direct sum](hyp:ξ,η), [their matrix coefficient
also converges to that of the candidate limiting operator](goal). -/
lemma lp_bounded_wot_of_single_tests
    {I E : Type*} [DecidableEq I] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (T : ℕ → lp (fun _ : I => E) 2 →L[ℂ] lp (fun _ : I => E) 2)
    (R : lp (fun _ : I => E) 2 →L[ℂ] lp (fun _ : I => E) 2)
    (C : ℝ) (hC : ∀ j, ‖T j‖ ≤ C)
    (h : ∀ i j v w, Tendsto
      (fun k => inner ℂ (lp.single 2 i v) (T k (lp.single 2 j w))) atTop
      (𝓝 (inner ℂ (lp.single 2 i v) (R (lp.single 2 j w)))))
    (ξ η : lp (fun _ : I => E) 2) :
    Tendsto (fun k => inner ℂ ξ (T k η)) atTop (𝓝 (inner ℂ ξ (R η))) := by
  have hsingle (j : I) (w : E) (ξ : lp (fun _ : I => E) 2) :
      Tendsto (fun k => inner ℂ ξ (T k (lp.single 2 j w))) atTop
        (𝓝 (inner ℂ ξ (R (lp.single 2 j w)))) := by
    let M : Submodule ℂ (lp (fun _ : I => E) 2) :=
      { carrier := {x | Tendsto (fun k => inner ℂ (lp.single 2 j w) ((T k).adjoint x))
          atTop (𝓝 (inner ℂ (lp.single 2 j w) (R.adjoint x)))}
        zero_mem' := by simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
        add_mem' := fun hx hy => by simpa only [Set.mem_ofPred_eq, map_add, inner_add_right] using hx.add hy
        smul_mem' := fun c x hx => by simpa only [Set.mem_ofPred_eq, map_smul, inner_smul_right] using hx.const_mul c }
    have hmem : ξ ∈ M := by
      apply lp_mem_closed_submodule M
        (bounded_wot_test_isClosed (fun k => (T k).adjoint) R.adjoint C
          (fun k => by simpa using hC k) (lp.single 2 j w))
      intro i v
      change Tendsto (fun k => inner ℂ (lp.single 2 j w) ((T k).adjoint (lp.single 2 i v)))
        atTop (𝓝 (inner ℂ (lp.single 2 j w) (R.adjoint (lp.single 2 i v))))
      have ht := (h i j v w).star
      simpa only [RCLike.star_def, inner_conj_symm, ContinuousLinearMap.adjoint_inner_right] using ht
    have ht := (show Tendsto (fun k => inner ℂ (lp.single 2 j w) ((T k).adjoint ξ))
      atTop (𝓝 (inner ℂ (lp.single 2 j w) (R.adjoint ξ))) from hmem).star
    simpa only [RCLike.star_def, ContinuousLinearMap.adjoint_inner_right, inner_conj_symm] using ht
  let M : Submodule ℂ (lp (fun _ : I => E) 2) :=
    { carrier := {x | Tendsto (fun k => inner ℂ ξ (T k x)) atTop (𝓝 (inner ℂ ξ (R x)))}
      zero_mem' := by simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
      add_mem' := fun hx hy => by simpa only [Set.mem_ofPred_eq, map_add, inner_add_right] using hx.add hy
      smul_mem' := fun c x hx => by simpa only [Set.mem_ofPred_eq, map_smul, inner_smul_right] using hx.const_mul c }
  exact lp_mem_closed_submodule M (bounded_wot_test_isClosed T R C hC ξ)
    (fun j w => hsingle j w ξ) η

-- @node: treeConjugation
/-- For [a free-group element](hyp:g), the [conjugation operator on the
free-group Hilbert space](goal) moves the coordinate at each group element to
the coordinate at its conjugate by that element. -/
noncomputable def treeConjugation (g : FreeGrp) : TreeSpace →L[ℂ] TreeSpace :=
  lpReindex ((Equiv.mulLeft g⁻¹).trans (Equiv.mulRight g))

-- @node: treeConjugation_single
/-- For [a conjugating free-group element](hyp:g), [a coordinate indexed by a
free-group element](hyp:x), and [a complex amplitude](hyp:v), [the conjugation
operator sends the vector supported at that coordinate to the vector with the
same amplitude supported at the conjugated coordinate](goal). -/
lemma treeConjugation_single (g x : FreeGrp) (v : ℂ) :
    treeConjugation g (lp.single 2 x v) = lp.single 2 (g * x * g⁻¹) v := by
  ext y
  simp only [treeConjugation, lpReindex_apply, Equiv.trans_apply,
    Equiv.coe_mulLeft, Equiv.coe_mulRight, lp.single_apply]
  have heq : x = g⁻¹ * y * g ↔ g * x * g⁻¹ = y := by
    constructor <;> intro h
    · rw [h]; group
    · rw [← h]; group
  simp only [Pi.single_apply, eq_comm, heq]

-- @node: treeConjugation_gen_tendsto_wot
/-- For [any two vectors in the free-group Hilbert space](hyp:ξ,η), [the matrix
coefficient of conjugation by the generator of index j converges, as j increases,
to the matrix coefficient of the root projection](goal). -/
lemma treeConjugation_gen_tendsto_wot (ξ η : TreeSpace) :
    Tendsto (fun j => inner ℂ ξ (treeConjugation (gen j) η)) atTop
      (𝓝 (inner ℂ ξ (projE η))) := by
  apply lp_bounded_wot_of_single_tests _ _ 1
    (fun j => by
      rw [treeConjugation, lpReindex_eq_isometry]
      exact (lpReindexIsometry (E := ℂ) _).norm_toContinuousLinearMap_le) ?_ ξ η
  intro x y v w
  rw [projE_apply_coordinate]
  by_cases hy : y = 1
  · subst y
    simpa only [treeConjugation_single, mul_one, mul_inv_cancel, lp.single_apply, Pi.single_eq_same] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => inner ℂ (lp.single 2 x v : TreeSpace)
        (lp.single 2 (1 : FreeGrp) w)) atTop
          (𝓝 (inner ℂ (lp.single 2 x v : TreeSpace) (lp.single 2 (1 : FreeGrp) w))))
  · have hescape := conjugate_gen_eventually_ne y x hy
    have heq : ∀ᶠ j : ℕ in atTop,
        inner ℂ (lp.single 2 x v) (treeConjugation (gen j) (lp.single 2 y w)) = 0 := by
      filter_upwards [hescape] with j hj
      rw [treeConjugation_single, lp.inner_single_left, lp.single_apply]
      simp [hj]
    have hzero : (lp.single 2 y w : TreeSpace) 1 = 0 := by simp [lp.single_apply, hy]
    rw [hzero, lp.single_zero, inner_zero_right]
    exact tendsto_const_nhds.congr' (heq.mono fun _ h => h.symm)

variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℂ D] [CompleteSpace D]

-- @node: hspFiber
/-- For [a complex Hilbert space of coefficient vectors](hyp:D) and [a bounded
operator on its two-tree Hilbert space](hyp:B), the [fiberwise extension to the
regular Hilbert space](goal) applies that same operator at every coordinate
indexed by the product group. -/
noncomputable def hspFiber (B : Lsp D →L[ℂ] Lsp D) : Hsp D →L[ℂ] Hsp D :=
  lp.mapCLM 2 (fun _ : ProdGrp => B) (norm_nonneg B) (fun _ => le_rfl)

-- @node: hspMaskFiber
/-- For [a complex Hilbert space of coefficient vectors](hyp:D), [a predicate
selecting coordinates of the product group](hyp:P), and [a bounded operator on
the two-tree Hilbert space](hyp:B), the [masked fiber operator](goal) applies
the operator at selected coordinates and is zero at all other coordinates. -/
noncomputable def hspMaskFiber (P : ProdGrp → Prop) [DecidablePred P]
    (B : Lsp D →L[ℂ] Lsp D) : Hsp D →L[ℂ] Hsp D :=
  lp.mapCLM 2 (fun x : ProdGrp => if P x then B else 0) (norm_nonneg B)
    (fun x => by split_ifs <;> simp)

-- @node: hspMaskFiber_single
/-- For [a predicate selecting product-group coordinates](hyp:P), [a bounded
fiber operator](hyp:B), [a product-group coordinate](hyp:y), and [a fiber
vector](hyp:w), [the masked fiber operator sends the vector supported at that
coordinate to the operator's image there if the coordinate is selected, and to
zero otherwise](goal). -/
lemma hspMaskFiber_single (P : ProdGrp → Prop) [DecidablePred P]
    (B : Lsp D →L[ℂ] Lsp D) (y : ProdGrp) (w : Lsp D) :
    hspMaskFiber P B (lp.single 2 y w) =
      if P y then lp.single 2 y (B w) else 0 := by
  ext x
  by_cases hy : P y <;> by_cases hxy : x = y <;>
    simp [hspMaskFiber, lp.single_apply, hy, hxy]

-- @node: regularFiber_single
/-- For [a product-group element](hyp:g), [a product-group coordinate](hyp:y),
[a bounded fiber operator](hyp:B), and [a fiber vector](hyp:w), [applying the
fiber operator followed by right and left regular translation by the group
element sends the vector supported at that coordinate to the conjugated
coordinate, with fiber value equal to the operator's image of the original
vector](goal). -/
lemma regularFiber_single (g y : ProdGrp) (B : Lsp D →L[ℂ] Lsp D) (w : Lsp D) :
    (lamAmp g * rhoAmp g * hspFiber B : Hsp D →L[ℂ] Hsp D) (lp.single 2 y w) =
      lp.single 2 (g * y * g⁻¹) (B w) := by
  apply lp.ext
  funext x
  simp only [mul_apply_eq_comp, lamAmp, rhoAmp, hspFiber, lpReindex_apply,
    Equiv.coe_mulLeft, Equiv.coe_mulRight]
  change B ((lp.single 2 y w : Hsp D) (g⁻¹ * x * g)) = _
  have heq : g⁻¹ * x * g = y ↔ x = g * y * g⁻¹ := by
    constructor <;> intro h
    · rw [← h]; group
    · rw [h]; group
  simp only [lp.single_apply, Pi.single_apply, heq]
  split_ifs <;> simp only [map_zero]

-- @node: regularFiber_tendsto_wot
/-- Consider [a sequence of conjugating product-group elements](hyp:g),
[a predicate selecting coordinates](hyp:P), [a sequence of bounded fiber
operators](hyp:B), and [a candidate fiber limit](hyp:R). If [the fiber operators
have a common norm bound](hyp:hC), [they converge weakly to the candidate](hyp:hB),
[every selected coordinate is fixed by every conjugation](hyp:hfix), and
[each unselected coordinate eventually moves away from any fixed coordinate](hyp:hescape),
then for [any two vectors in the regular Hilbert space](hyp:ξ,η), [the matrix
coefficients of conjugation combined with the fiber operators converge to those
of the candidate fiber limit restricted to the selected coordinates](goal). -/
lemma regularFiber_tendsto_wot
    (g : ℕ → ProdGrp) (P : ProdGrp → Prop) [DecidablePred P]
    (B : ℕ → Lsp D →L[ℂ] Lsp D) (R : Lsp D →L[ℂ] Lsp D)
    (C : ℝ) (hC : ∀ j, ‖B j‖ ≤ C)
    (hB : ∀ ξ η, Tendsto (fun j => inner ℂ ξ (B j η)) atTop (𝓝 (inner ℂ ξ (R η))))
    (hfix : ∀ y, P y → ∀ j, g j * y * (g j)⁻¹ = y)
    (hescape : ∀ y, ¬ P y → ∀ x, ∀ᶠ j in atTop, g j * y * (g j)⁻¹ ≠ x)
    (ξ η : Hsp D) :
    Tendsto (fun j => inner ℂ ξ ((lamAmp (g j) * rhoAmp (g j) * hspFiber (B j) : Hsp D →L[ℂ] Hsp D) η))
      atTop (𝓝 (inner ℂ ξ (hspMaskFiber P R η))) := by
  apply lp_bounded_wot_of_single_tests _ _ C ?_ ?_ ξ η
  · intro j
    have hl : lamAmp (D := D) (g j) ∈ unitary _ := lpReindex_mem_unitary _
    have hr : rhoAmp (D := D) (g j) ∈ unitary _ := lpReindex_mem_unitary _
    rw [mul_assoc, CStarRing.norm_mem_unitary_mul _ hl,
      CStarRing.norm_mem_unitary_mul _ hr]
    exact (lp.norm_mapCLM_le 2 _ (norm_nonneg _) _).trans (hC j)
  · intro x y v w
    simp only [regularFiber_single, hspMaskFiber_single]
    by_cases hy : P y
    · simp only [hy, ite_true, hfix y hy]
      by_cases hxy : x = y
      · subst x
        simpa only [lp.inner_single_left, lp.single_apply, Pi.single_eq_same] using hB v w
      · simp only [lp.inner_single_left, lp.single_apply, Pi.single_eq_of_ne hxy,
          inner_zero_right]
        exact tendsto_const_nhds
    · simp only [hy, ite_false, inner_zero_right]
      apply tendsto_const_nhds.congr'
      filter_upwards [hescape y hy x] with j hj
      simp [lp.inner_single_left, lp.single_apply, hj]

-- @node: firstFactor_conjugation_escape
/-- If [the first component of a product-group element is not the identity](hyp:hy),
[conjugating it by generators of sufficiently large index in the first factor
gives an element different from any prescribed fixed product-group element](goal). -/
lemma firstFactor_conjugation_escape (y : ProdGrp) (hy : y.1 ≠ 1) (x : ProdGrp) :
    ∀ᶠ j in atTop, (gen j, 1) * y * (gen j, 1)⁻¹ ≠ x := by
  filter_upwards [conjugate_gen_eventually_ne y.1 x.1 hy] with j hj
  exact fun h => hj (congrArg Prod.fst h)

-- @node: secondFactor_conjugation_escape
/-- If [the second component of a product-group element is not the identity](hyp:hy),
[conjugating it by generators of sufficiently large index in the second factor
gives an element different from any prescribed fixed product-group element](goal). -/
lemma secondFactor_conjugation_escape (y : ProdGrp) (hy : y.2 ≠ 1) (x : ProdGrp) :
    ∀ᶠ j in atTop, (1, gen j) * y * (1, gen j)⁻¹ ≠ x := by
  filter_upwards [conjugate_gen_eventually_ne y.2 x.2 hy] with j hj
  exact fun h => hj (congrArg Prod.snd h)

-- @node: mainCornerE1
/-- For [a clock dimension](hyp:n), the [first corner projection](goal) retains
only product-group coordinates whose first component is the identity and
projects the first tree coordinate onto its root. -/
noncomputable def mainCornerE1 (n : ClockNat) : mainH n →L[ℂ] mainH n :=
  hspMaskFiber (fun x : ProdGrp => x.1 = 1) (ampFst projE)

-- @node: mainCornerE2
/-- For [a clock dimension](hyp:n), the [second corner projection](goal) retains
only product-group coordinates whose second component is the identity and
projects the second tree coordinate onto its root. -/
noncomputable def mainCornerE2 (n : ClockNat) : mainH n →L[ℂ] mainH n :=
  hspMaskFiber (fun x : ProdGrp => x.2 = 1) (ampSnd projE)

-- @node: mainCornerR1
/-- For [a clock dimension](hyp:n), the [first corner unitary](goal) applies
the clock unitary to the finite-dimensional coefficient vector at every tree
and product-group coordinate. -/
noncomputable def mainCornerR1 (n : ClockNat) : mainH n →L[ℂ] mainH n :=
  hspFiber (ampD (clockU n))

-- @node: mainCornerR2
/-- For [a clock dimension](hyp:n), the [second corner unitary](goal) applies
the shift unitary to the finite-dimensional coefficient vector at every tree
and product-group coordinate. -/
noncomputable def mainCornerR2 (n : ClockNat) : mainH n →L[ℂ] mainH n :=
  hspFiber (ampD (shiftV n))

-- @node: main_jointLimitA_eq_corner
/-- For [a clock dimension](hyp:n), [the first matrix-limit operator applied
fiberwise only at coordinates with identity first component equals the scalar
parameter times the first corner projection composed with the first corner
unitary](goal). -/
lemma main_jointLimitA_eq_corner (n : ClockNat) :
    hspMaskFiber (fun x : ProdGrp => x.1 = 1) (matrixLimitA (clockU n)) =
      tParam • (mainCornerE1 n * mainCornerR1 n) := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply lp.ext
  funext x
  change (if x.1 = 1 then matrixLimitA (clockU n) else 0) (ξ x) =
    tParam • ((if x.1 = 1 then ampFst projE else 0) (ampD (clockU n) (ξ x)))
  by_cases hx : x.1 = 1 <;> simp [hx, matrixLimitA, mul_apply_eq_comp]

-- @node: main_jointLimitB_eq_corner
/-- For [a clock dimension](hyp:n), [the second matrix-limit operator applied
fiberwise only at coordinates with identity second component equals the scalar
parameter times the second corner projection composed with the second corner
unitary](goal). -/
lemma main_jointLimitB_eq_corner (n : ClockNat) :
    hspMaskFiber (fun x : ProdGrp => x.2 = 1) (matrixLimitB (shiftV n)) =
      tParam • (mainCornerE2 n * mainCornerR2 n) := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply lp.ext
  funext x
  change (if x.2 = 1 then matrixLimitB (shiftV n) else 0) (ξ x) =
    tParam • ((if x.2 = 1 then ampSnd projE else 0) (ampD (shiftV n) (ξ x)))
  by_cases hx : x.2 = 1 <;> simp [hx, matrixLimitB, mul_apply_eq_comp]

-- @node: main_jointLimitA_tendsto_wot
/-- If [the circle representation and Laurent coefficients form a circle
family](hyp:hπ), then for [any clock dimension](hyp:n) and [any two vectors in
the main Hilbert space](hyp:ξ,η), [the matrix coefficients of the amplified
representation at successive generators of the first factor, followed by right
and left regular translation, converge to those of the scalar parameter times
the first corner projection composed with the first corner unitary](goal). -/
lemma main_jointLimitA_tendsto_wot (π : CircleRep) (A : LaurentData)
    (hπ : IsCircleFamily π A) (n : ClockNat) (ξ η : mainH n) :
    Tendsto (fun j => inner ℂ ξ
      ((lamAmp (gen j, 1) * rhoAmp (gen j, 1) * mainFAmp A n (gen j, 1) : mainH n →L[ℂ] mainH n) η))
      atTop (𝓝 (inner ℂ ξ
        ((tParam • (mainCornerE1 n * mainCornerR1 n)) η))) := by
  rw [← main_jointLimitA_eq_corner]
  have hUV := mainNearUnitaryPair n
  letI : FiniteDimensional ℂ (ClockSpace n) := hUV.2.1
  have hf (j : ℕ) : mainFAmp A n (gen j, 1) = hspFiber (matrixRepA A (clockU n) (gen j)) := by
    simp only [mainFAmp, mainF, prodMap, matrixRepB_one π A hπ _ (shiftV_mem_unitary n), mul_one, hspFiber]
  simp only [hf]
  apply regularFiber_tendsto_wot _ _ _ _ S0
    (fun j => matrixRepA_norm_le π A hπ _ (clockU_mem_unitary n) (gen j))
    (matrixRepA_gen_tendsto_wot π A hπ _ _ hUV
      (matrixRepsAbsConv_of_circleFamily π A hπ _ _ (clockU_mem_unitary n) (shiftV_mem_unitary n)))
    ?_ firstFactor_conjugation_escape ξ η
  intro y hy j
  ext <;> simp [hy]

-- @node: main_jointLimitB_tendsto_wot
/-- If [the circle representation and Laurent coefficients form a circle
family](hyp:hπ), then for [any clock dimension](hyp:n) and [any two vectors in
the main Hilbert space](hyp:ξ,η), [the matrix coefficients of the amplified
representation at successive generators of the second factor, followed by right
and left regular translation, converge to those of the scalar parameter times
the second corner projection composed with the second corner unitary](goal). -/
lemma main_jointLimitB_tendsto_wot (π : CircleRep) (A : LaurentData)
    (hπ : IsCircleFamily π A) (n : ClockNat) (ξ η : mainH n) :
    Tendsto (fun j => inner ℂ ξ
      ((lamAmp (1, gen j) * rhoAmp (1, gen j) * mainFAmp A n (1, gen j) : mainH n →L[ℂ] mainH n) η))
      atTop (𝓝 (inner ℂ ξ
        ((tParam • (mainCornerE2 n * mainCornerR2 n)) η))) := by
  rw [← main_jointLimitB_eq_corner]
  have hUV := mainNearUnitaryPair n
  letI : FiniteDimensional ℂ (ClockSpace n) := hUV.2.1
  have hf (j : ℕ) : mainFAmp A n (1, gen j) = hspFiber (matrixRepB A (shiftV n) (gen j)) := by
    simp only [mainFAmp, mainF, prodMap, matrixRepA_one π A hπ _ (clockU_mem_unitary n), one_mul, hspFiber]
  simp only [hf]
  apply regularFiber_tendsto_wot _ _ _ _ S0
    (fun j => matrixRepB_norm_le π A hπ _ (shiftV_mem_unitary n) (gen j))
    (matrixRepB_gen_tendsto_wot π A hπ _ _ hUV
      (matrixRepsAbsConv_of_circleFamily π A hπ _ _ (clockU_mem_unitary n) (shiftV_mem_unitary n)))
    ?_ secondFactor_conjugation_escape ξ η
  intro y hy j
  ext <;> simp [hy]

end Papers.OaiNearInclusionsVon

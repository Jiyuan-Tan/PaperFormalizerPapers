module

public import Papers.OaiNearInclusionsVon.Helpers.MainJointLimits
public import Papers.OaiNearInclusionsVon.Helpers.CornerTransport
public import Papers.OaiNearInclusionsVon.Helpers.AmplificationBicommutant

/-! The common coordinate corner and its identification with the clock space. -/

@[expose] public section

set_option linter.style.longLine false
-- The nested corner spaces need the usual depth for deferred instance synthesis.
set_option maxSynthPendingDepth 32

namespace Papers.OaiNearInclusionsVon

variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℂ D] [CompleteSpace D]

-- @node: amplify_projE_apply
/-- For [a square-summable vector x indexed by the free group, with values in D](hyp:x),
[the amplification of the projection onto the identity coordinate sends x
to the vector supported only at the group identity, with value equal to the
identity coordinate of x](goal). -/
lemma amplify_projE_apply (x : lp (fun _ : FreeGrp => D) 2) :
    amplify projE x = lp.single 2 1 (x 1) := by
  apply lp.ext
  funext i
  apply ext_inner_left ℂ
  intro v
  have h := congrArg (fun T : lp (fun _ : FreeGrp => D) 2 →L[ℂ] TreeSpace => T x i)
    (lpScalarSlice_amplify projE v)
  change inner ℂ v (amplify projE x i) = projE (lpScalarSlice v x) i at h
  rw [projE_apply_coordinate] at h
  by_cases hi : i = 1
  · subst i
    simpa [lp.single_apply, lpScalarSlice_apply] using h
  · simpa [lp.single_apply, hi, Ne.symm hi] using h

-- @node: hspMaskFiber_star
/-- [The adjoint of the operator that applies B at coordinates satisfying P
and is zero elsewhere applies the adjoint of B at those same coordinates and
is zero elsewhere](goal). -/
lemma hspMaskFiber_star (P : ProdGrp → Prop) [DecidablePred P]
    (B : Lsp D →L[ℂ] Lsp D) :
    star (hspMaskFiber P B) = hspMaskFiber P (star B) := by
  unfold hspMaskFiber
  rw [lpMap_star]
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext i
  change (star (if P i then B else 0)) (x i) = (if P i then star B else 0) (x i)
  by_cases hi : P i <;> simp [hi]

-- @node: hspMaskFiber_isStarProjection
/-- If [B is an orthogonal projection](hyp:hB), then [the operator that applies
B at coordinates satisfying P and is zero elsewhere is also an orthogonal
projection](goal). -/
lemma hspMaskFiber_isStarProjection (P : ProdGrp → Prop) [DecidablePred P]
    (B : Lsp D →L[ℂ] Lsp D) (hB : IsStarProjection B) :
    IsStarProjection (hspMaskFiber P B) := by
  constructor
  · change hspMaskFiber P B * hspMaskFiber P B = hspMaskFiber P B
    apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext i
    change (if P i then B else 0) ((if P i then B else 0) (x i)) =
      (if P i then B else 0) (x i)
    split_ifs
    · exact congrArg (fun T : Lsp D →L[ℂ] Lsp D => T (x i)) hB.isIdempotentElem.eq
    · simp
  · change star (hspMaskFiber P B) = hspMaskFiber P B
    rw [hspMaskFiber_star, hB.isSelfAdjoint.star_eq]

-- @node: ampFst_projE_isStarProjection
/-- [The amplification of the identity-coordinate projection on the first
tree-space factor is an orthogonal projection](goal). -/
lemma ampFst_projE_isStarProjection : IsStarProjection (ampFst (D := D) projE) := by
  have hp : IsStarProjection projE := isStarProjection_starProjection
  constructor
  · change amplify projE * amplify projE = amplify (E := lp (fun _ : FreeGrp => D) 2) projE
    rw [← amplify_mul, hp.isIdempotentElem.eq]
  · change star (amplify (E := lp (fun _ : FreeGrp => D) 2) projE) = amplify (E := lp (fun _ : FreeGrp => D) 2) projE
    rw [← amplify_star, hp.isSelfAdjoint.star_eq]

-- @node: ampSnd_projE_isStarProjection
/-- [The amplification of the identity-coordinate projection on the second
tree-space factor is an orthogonal projection](goal). -/
lemma ampSnd_projE_isStarProjection : IsStarProjection (ampSnd (D := D) projE) := by
  have hp : IsStarProjection projE := isStarProjection_starProjection
  constructor
  · change ampSnd projE * ampSnd projE = ampSnd (D := D) projE
    apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext i
    change amplify projE (amplify projE (x i)) = amplify projE (x i)
    have he : amplify (E := D) projE * amplify projE = amplify projE := by
      rw [← amplify_mul, hp.isIdempotentElem.eq]
    exact congrArg (fun T : lp (fun _ : FreeGrp => D) 2 →L[ℂ]
      lp (fun _ : FreeGrp => D) 2 => T (x i)) he
  · change star (ampSnd (D := D) projE) = ampSnd projE
    rw [show star (ampSnd (D := D) projE) = ampSnd (star projE) from ampSnd_star _]
    rw [hp.isSelfAdjoint.star_eq]

-- @node: mainCorner_projections
/-- [For every index k in the clock-size sequence φ, the two main corner
operators are commuting orthogonal projections](goal). -/
lemma mainCorner_projections (φ : ℕ → ClockNat) :
    CornerProjections (fun k => mainCornerE1 (φ k)) (fun k => mainCornerE2 (φ k)) := by
  intro k
  refine ⟨hspMaskFiber_isStarProjection _ _ ampFst_projE_isStarProjection,
    hspMaskFiber_isStarProjection _ _ ampSnd_projE_isStarProjection, ?_⟩
  change mainCornerE1 (φ k) * mainCornerE2 (φ k) =
    mainCornerE2 (φ k) * mainCornerE1 (φ k)
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext i
  change (if i.1 = 1 then ampFst projE else 0)
      ((if i.2 = 1 then ampSnd projE else 0) (x i)) =
    (if i.2 = 1 then ampSnd projE else 0)
      ((if i.1 = 1 then ampFst projE else 0) (x i))
  by_cases h₁ : i.1 = 1 <;> by_cases h₂ : i.2 = 1 <;> simp only [h₁, h₂, if_true, if_false, map_zero, zero_apply]
  exact congrArg (fun T : Lsp (ClockSpace (φ k)) →L[ℂ] Lsp (ClockSpace (φ k)) => T (x i))
    (ampFst_commute_ampSnd projE projE).eq

-- @node: hspFiber_mem_unitary
/-- If [B is unitary](hyp:hB), then [the operator applying B independently at
every outer coordinate is unitary](goal). -/
lemma hspFiber_mem_unitary (B : Lsp D →L[ℂ] Lsp D) (hB : B ∈ unitary _) :
    hspFiber B ∈ unitary _ :=
  lpMap_mem_unitary _ (norm_nonneg B) _ (fun _ => hB)

-- @node: hspFiber_commute_mask
/-- If [B and C commute](hyp:hBC), then [applying B at every outer coordinate
commutes with applying C only at coordinates satisfying P and zero elsewhere](goal). -/
lemma hspFiber_commute_mask (B C : Lsp D →L[ℂ] Lsp D) (hBC : Commute B C)
    (P : ProdGrp → Prop) [DecidablePred P] :
    Commute (hspFiber B) (hspMaskFiber P C) := by
  change hspFiber B * hspMaskFiber P C = hspMaskFiber P C * hspFiber B
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext i
  change B ((if P i then C else 0) (x i)) = (if P i then C else 0) (B (x i))
  by_cases hi : P i
  · simp only [hi, if_true]
    exact congrArg (fun T : Lsp D →L[ℂ] Lsp D => T (x i)) hBC.eq
  · simp [hi]

-- @node: mainCorner_unitaries
/-- [At every index in the clock-size sequence φ, the lifted clock and shift
operators are unitary and each commutes with both main corner projections](goal). -/
lemma mainCorner_unitaries (φ : ℕ → ClockNat) :
    CornerUnitaries (fun k => mainCornerE1 (φ k)) (fun k => mainCornerE2 (φ k))
      (fun k => mainCornerR1 (φ k)) (fun k => mainCornerR2 (φ k)) := by
  intro k
  exact ⟨hspFiber_mem_unitary (D := ClockSpace (φ k)) _ (ampD_mem_unitary _ (clockU_mem_unitary _)),
    hspFiber_mem_unitary (D := ClockSpace (φ k)) _ (ampD_mem_unitary _ (shiftV_mem_unitary _)),
    hspFiber_commute_mask (D := ClockSpace (φ k)) _ _ (ampFst_commute_ampD _ _).symm _,
    hspFiber_commute_mask (D := ClockSpace (φ k)) _ _ (ampSnd_commute_ampD _ _).symm _,
    hspFiber_commute_mask (D := ClockSpace (φ k)) _ _ (ampFst_commute_ampD _ _).symm _,
    hspFiber_commute_mask (D := ClockSpace (φ k)) _ _ (ampSnd_commute_ampD _ _).symm _⟩

-- @node: mainCornerEmbed
/-- For [clock size n](hyp:n), [the main corner embedding](goal) is the complex
linear isometry that [places a clock vector at outer coordinate (1, 1) and at
the identity in each tree-space coordinate, with zero at all other coordinates](step:1)
and [preserves its norm](step:2). -/
noncomputable def mainCornerEmbed (n : ClockNat) : ClockSpace n →ₗᵢ[ℂ] mainH n where
  toLinearMap := (lp.lsingle (𝕜 := ℂ) (E := fun _ : ProdGrp => Lsp (ClockSpace n)) 2 (1, 1)).comp
    ((lp.lsingle (E := fun _ : FreeGrp => lp (fun _ : FreeGrp => ClockSpace n) 2) 2 1).comp
      (lp.lsingle (E := fun _ : FreeGrp => ClockSpace n) 2 1))
  norm_map' x := by
    change ‖(lp.single 2 (1, 1) (lp.single 2 1 (lp.single 2 1 x)) : mainH n)‖ = ‖x‖
    simp only [lp.norm_single (by norm_num : (0 : ENNReal) < 2)]

-- @node: mainCorner_product_apply
/-- [Applying the product of the two main corner projections to x extracts
its outer coordinate (1, 1) and both identity tree-space coordinates, then
embeds that clock vector back into the main space](goal). -/
lemma mainCorner_product_apply (n : ClockNat) (x : mainH n) :
    (mainCornerE1 n * mainCornerE2 n) x = mainCornerEmbed n (x (1, 1) 1 1) := by
  apply lp.ext
  funext i
  change (if i.1 = 1 then ampFst projE else 0)
      ((if i.2 = 1 then ampSnd projE else 0) (x i)) =
    (lp.single 2 (1, 1) (lp.single 2 1 (lp.single 2 1 (x (1, 1) 1 1))) : mainH n) i
  by_cases h₁ : i.1 = 1 <;> by_cases h₂ : i.2 = 1
  · have hi : i = (1, 1) := Prod.ext h₁ h₂
    subst i
    simp only [lp.single_apply, ite_true]
    change amplify projE (ampSnd projE (x (1, 1))) = _
    rw [amplify_projE_apply]
    congr 1
    exact amplify_projE_apply (x (1, 1) 1)
  · have hi : (1, 1) ≠ i := fun h => h₂ (congrArg Prod.snd h.symm)
    simp [h₁, h₂, lp.single_apply, hi]
  · have hi : (1, 1) ≠ i := fun h => h₁ (congrArg Prod.fst h.symm)
    simp [h₁, h₂, lp.single_apply, hi]
  · have hi : (1, 1) ≠ i := fun h => h₁ (congrArg Prod.fst h.symm)
    simp [h₁, h₂, lp.single_apply, hi]

-- @node: mainCornerEmbed_coordinate
/-- [Reading the outer coordinate (1, 1) and both identity tree-space coordinates
of the main corner embedding of x recovers x](goal). -/
lemma mainCornerEmbed_coordinate (n : ClockNat) (x : ClockSpace n) :
    mainCornerEmbed n x (1, 1) 1 1 = x := by
  change (lp.single 2 (1, 1) (lp.single 2 1 (lp.single 2 1 x)) : mainH n) (1, 1) 1 1 = x
  simp

-- @node: mainCornerIsometry
/-- For [a sequence φ of clock sizes](hyp:φ) and [an index k](hyp:k), [the main
corner isometry](goal) [maps the clock space at size φ(k) into the range of the
product of the two main corner projections by the coordinate embedding](step:1)
and [preserves norms](step:2). -/
noncomputable def mainCornerIsometry (φ : ℕ → ClockNat) (k : ℕ) :
    ClockSpace (φ k) →ₗᵢ[ℂ]
      cornerRange (fun k => mainCornerE1 (φ k)) (fun k => mainCornerE2 (φ k)) k where
  toLinearMap := (mainCornerEmbed (φ k)).toLinearMap.codRestrict _ (fun x => by
    refine ⟨mainCornerEmbed (φ k) x, ?_⟩
    change (mainCornerE1 (φ k) * mainCornerE2 (φ k)) (mainCornerEmbed (φ k) x) = _
    rw [mainCorner_product_apply, mainCornerEmbed_coordinate]
    rfl)
  norm_map' x := (mainCornerEmbed (φ k)).norm_map x

-- @node: mainCornerIsometry_surjective
/-- [Every vector in the range of the product of the two main corner
projections at index k is the image of a clock vector under the main corner
isometry for φ](goal). -/
lemma mainCornerIsometry_surjective (φ : ℕ → ClockNat) (k : ℕ) :
    Function.Surjective (mainCornerIsometry φ k) := by
  intro x
  obtain ⟨y, hy⟩ := x.property
  refine ⟨y (1, 1) 1 1, Subtype.ext ?_⟩
  change mainCornerEmbed (φ k) (y (1, 1) 1 1) = (x : mainH (φ k))
  rw [← mainCorner_product_apply]
  exact hy

-- @node: mainCornerEquiv
/-- For [a sequence φ of clock sizes](hyp:φ) and [an index k](hyp:k), [the main
corner equivalence](goal) is the bijective complex linear isometry from the
clock space at size φ(k) onto the range of the product of the two main corner
projections, obtained from the coordinate embedding. -/
noncomputable def mainCornerEquiv (φ : ℕ → ClockNat) (k : ℕ) :
    ClockSpace (φ k) ≃ₗᵢ[ℂ]
      cornerRange (fun k => mainCornerE1 (φ k)) (fun k => mainCornerE2 (φ k)) k :=
  LinearIsometryEquiv.ofSurjective (mainCornerIsometry φ k) (mainCornerIsometry_surjective φ k)

-- @node: mainCorner_completeSpace
/-- [The range of the product of the two main corner projections at index k
of the clock-size sequence φ is complete in its inherited norm](goal). -/
lemma mainCorner_completeSpace (φ : ℕ → ClockNat) (k : ℕ) :
    CompleteSpace (cornerRange (fun k => mainCornerE1 (φ k))
      (fun k => mainCornerE2 (φ k)) k) :=
  (mainCornerEquiv φ k).toIsometryEquiv.completeSpace_iff.mp inferInstance

-- @node: mainCorner_dimension
/-- [At every index of the clock-size sequence φ, the range of the product of
the two main corner projections is nonzero and finite-dimensional over the
complex numbers](goal). -/
lemma mainCorner_dimension (φ : ℕ → ClockNat) :
    CornerDimension (fun k => mainCornerE1 (φ k)) (fun k => mainCornerE2 (φ k)) := by
  intro k
  let e := mainCornerEquiv φ k
  letI : NeZero (φ k).val := ⟨by have := (φ k).property; unfold ClockIndex at this; omega⟩
  letI : Nontrivial (cornerRange (fun k => mainCornerE1 (φ k))
      (fun k => mainCornerE2 (φ k)) k) := e.injective.nontrivial
  exact ⟨Submodule.nontrivial_iff_ne_bot.mp inferInstance,
    FiniteDimensional.of_injective e.symm.toLinearMap e.symm.injective⟩

-- @node: mainCornerEmbed_intertwines
/-- [Applying Y to the coefficient-space factor at every coordinate of the
main corner embedding of x gives the main corner embedding of Y applied to x](goal). -/
lemma mainCornerEmbed_intertwines (n : ClockNat) (Y : ClockSpace n →L[ℂ] ClockSpace n)
    (x : ClockSpace n) :
    hspFiber (ampD Y) (mainCornerEmbed n x) = mainCornerEmbed n (Y x) := by
  apply lp.ext
  funext i
  apply lp.ext
  funext j
  apply lp.ext
  funext l
  change Y ((mainCornerEmbed n x) i j l) = mainCornerEmbed n (Y x) i j l
  change Y ((lp.single 2 (1, 1) (lp.single 2 1 (lp.single 2 1 x)) : mainH n) i j l) =
    (lp.single 2 (1, 1) (lp.single 2 1 (lp.single 2 1 (Y x))) : mainH n) i j l
  by_cases hi : i = (1, 1) <;> by_cases hj : j = 1 <;>
    by_cases hl : l = 1 <;> simp [lp.single_apply, Pi.single_apply, hi, hj, hl]

set_option maxHeartbeats 800000 in
-- @node: mainCorner_restrict_first
/-- [Restricting the first lifted unitary to the common corner and applying
it to the image of x under the main corner equivalence gives the image of the
clock operator applied to x](goal). -/
lemma mainCorner_restrict_first (φ : ℕ → ClockNat) (k : ℕ) (x : ClockSpace (φ k)) :
    cornerRestrict (fun k => mainCornerE1 (φ k)) (fun k => mainCornerE2 (φ k))
      (fun k => mainCornerR1 (φ k)) k ((mainCornerEquiv φ k) x) =
        (mainCornerEquiv φ k) (clockU (φ k) x) := by
  apply Subtype.ext
  exact ((cornerRestrict_apply (H := fun k => mainH (φ k)) (fun k => mainCornerE1 (φ k)) (fun k => mainCornerE2 (φ k))
    (fun k => mainCornerR1 (φ k)) (fun k => mainCornerR2 (φ k))
    (mainCorner_projections φ) (mainCorner_unitaries φ) k ((mainCornerEquiv φ k) x)).1).trans
    (mainCornerEmbed_intertwines (φ k) (clockU (φ k)) x)

set_option maxHeartbeats 800000 in
-- @node: mainCorner_restrict_second
/-- [Restricting the second lifted unitary to the common corner and applying
it to the image of x under the main corner equivalence gives the image of the
shift operator applied to x](goal). -/
lemma mainCorner_restrict_second (φ : ℕ → ClockNat) (k : ℕ) (x : ClockSpace (φ k)) :
    cornerRestrict (fun k => mainCornerE1 (φ k)) (fun k => mainCornerE2 (φ k))
      (fun k => mainCornerR2 (φ k)) k ((mainCornerEquiv φ k) x) =
        (mainCornerEquiv φ k) (shiftV (φ k) x) := by
  apply Subtype.ext
  exact ((cornerRestrict_apply (H := fun k => mainH (φ k)) (fun k => mainCornerE1 (φ k)) (fun k => mainCornerE2 (φ k))
    (fun k => mainCornerR1 (φ k)) (fun k => mainCornerR2 (φ k))
    (mainCorner_projections φ) (mainCorner_unitaries φ) k ((mainCornerEquiv φ k) x)).2).trans
    (mainCornerEmbed_intertwines (φ k) (shiftV (φ k)) x)

open Filter
open scoped Topology

set_option maxHeartbeats 800000 in
/-- Given [two sequences of von Neumann algebras on the main spaces](hyp:A₁,A₂)
and [two sequences of bounded operators on those spaces](hyp:T₁,T₂), suppose
[every operator in the first algebra commutes with every operator in the second
at each index](hyp:hA) and [the two operator sequences belong to their respective
algebras and converge in norm to the respective projected lifted clock and shift
operators](hyp:hT). Then [there are commuting unitary operators on each clock
space whose summed norm distances from the clock and shift operators tend to
zero](goal). -/
-- @node: mainCorner_commuting_approximants
lemma mainCorner_commuting_approximants (φ : ℕ → ClockNat)
    (A₁ A₂ : ∀ k, VonNeumannAlgebra (mainH (φ k)))
    (T₁ T₂ : ∀ k, mainH (φ k) →L[ℂ] mainH (φ k))
    (hA : CornerAlgebras A₁ A₂)
    (hT : CornerApproximation A₁ A₂ T₁ T₂
      (fun k => mainCornerE1 (φ k)) (fun k => mainCornerE2 (φ k))
      (fun k => mainCornerR1 (φ k)) (fun k => mainCornerR2 (φ k))) :
    ∃ (Uhat Vhat : ∀ k, ClockSpace (φ k) →L[ℂ] ClockSpace (φ k)),
      (∀ k, Uhat k ∈ unitary _ ∧ Vhat k ∈ unitary _ ∧ Commute (Uhat k) (Vhat k)) ∧
      Tendsto (fun k => ‖Uhat k - clockU (φ k)‖ + ‖Vhat k - shiftV (φ k)‖)
        atTop (𝓝 0) := by
  with_reducible exact (corner_commuting_approximants_transport
    (H := fun k => mainH (φ k)) (D := fun k => ClockSpace (φ k))
    (fun k => mainCornerE1 (φ k)) (fun k => mainCornerE2 (φ k))
    (fun k => mainCornerR1 (φ k)) (fun k => mainCornerR2 (φ k)) T₁ T₂ A₁ A₂
    (mainCorner_projections φ) (mainCorner_dimension φ) (mainCorner_unitaries φ) hA hT
    (mainCornerEquiv φ) (fun k => clockU (φ k)) (fun k => shiftV (φ k))
    (mainCorner_restrict_first φ) (mainCorner_restrict_second φ))

end Papers.OaiNearInclusionsVon

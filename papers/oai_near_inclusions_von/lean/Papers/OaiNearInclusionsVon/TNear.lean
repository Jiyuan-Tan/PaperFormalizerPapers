module

public import Papers.OaiNearInclusionsVon.Helpers.NearExpansion

/-! The universal near-inclusion bound for Laurent substitution. -/

public section

set_option linter.style.longLine false

namespace Papers.OaiNearInclusionsVon


variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℂ D] [CompleteSpace D]

set_option maxHeartbeats 800000 in
/-- If [π and A satisfy the circle-family conditions](hyp:hπ),
[U and V are unitary operators on a nonzero finite-dimensional space](hyp:hUV),
and [both matrix substitution series converge absolutely for every free-group
element](hyp:habs), then [the near-inclusion weights are summable, the
one-sided gap from the source algebra to the target algebra is at most the
universal near-inclusion constant times the norm of the commutator of U
and V, and, for every product-group element, the diagonal-unitary conjugate
of amplified left translation differs from amplified left translation
followed by the product substitution acting on each coordinate by at most
that same bound in operator norm](goal). -/
-- @node: prop:near
theorem near_inclusion_bound (π : CircleRep) (A : LaurentData) (hπ : IsCircleFamily π A)
    (U V : D →L[ℂ] D) (hUV : NearUnitaryPair U V)
    (habs : MatrixRepsAbsConv A U V) :
    let hb := prodMap_norm_bound π A hπ U V ⟨hUV.2.2.1, hUV.2.2.2⟩
    Summable nearWeight ∧
    nearInclusionGap (sourceAlg A U V hb : Set (Hsp D →L[ℂ] Hsp D))
      (targetAlg (D := D) : Set (Hsp D →L[ℂ] Hsp D)) ≤ nearC * ‖U * V - V * U‖ ∧
    ∀ g : ProdGrp,
      ‖diagUnitary A U V hb * lamAmp g * star (diagUnitary A U V hb) -
        lamAmp g * lp.mapCLM 2 (fun _ : ProdGrp => prodMap A U V g)
          (norm_nonneg _) (fun _ => le_rfl)‖ ≤ nearC * ‖U * V - V * U‖ := by
  dsimp only
  let : FiniteDimensional ℂ D := hUV.2.1
  let : Nontrivial D := hUV.1
  let : Nontrivial (Lsp D) := by
    obtain ⟨v, hv⟩ := exists_ne (0 : D)
    refine ⟨⟨lp.single 2 (1 : FreeGrp) (lp.single 2 (1 : FreeGrp) v), 0, ?_⟩⟩
    intro h
    apply hv
    have he := congrArg (fun ξ : Lsp D => ξ 1 1) h
    simpa using he
  let hb := prodMap_norm_bound π A hπ U V ⟨hUV.2.2.1, hUV.2.2.2⟩
  let W := diagUnitary A U V hb
  have hW : W ∈ unitary (Hsp D →L[ℂ] Hsp D) :=
    diagUnitary_mem_unitary π A hπ U V hUV hb
  refine ⟨nearWeight_summable, ?_, near_group_reordering_bound π A hπ U V hUV hb⟩
  apply nearInclusionGap_le_of_forall
    (sourceAlg A U V hb) (targetAlg (D := D))
    (nearC * ‖U * V - V * U‖)
    (mul_nonneg nearC_nonneg (norm_nonneg _))
  intro Z hZ hnorm
  -- The carrier identification is the sole remaining substrate dependency.
  change Z ∈ (sourceAlg A U V hb : Set (Hsp D →L[ℂ] Hsp D)) at hZ
  rw [sourceAlg_carrier π A hπ U V hUV hb] at hZ
  obtain ⟨X, hX, hZeq⟩ := hZ
  have hXZ : ‖X‖ ≤ ‖Z‖ := by
    rw [hZeq]
    change ‖X‖ ≤ ‖W * amplify X * star W‖
    rw [CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem hW),
      CStarRing.norm_mem_unitary_mul _ hW, amplify_norm_eq]
  let B := nearCoeffBlock (D := D) π A hπ X
  have hZexp : Z = ∑' q, nearZTerm B U V q :=
    hZeq.trans (nearZ_expansion π A hπ X U V hUV.2.2.1 hUV.2.2.2 hb)
  have hB (q) : ‖B q‖ ≤ nearCoeffWeight q * ‖Z‖ :=
    (nearCoeffBlock_norm_le π A hπ X q).trans
      (mul_le_mul_of_nonneg_left hXZ (nearCoeffWeight_nonneg q))
  have hYmem : (∑' q, nearYTerm B U V q) ∈ targetAlg (D := D) :=
    mem_targetAlg_of_matrixRep_blocks π A hπ U V hUV.2.2.1 hUV.2.2.2
      X hX _ (nearY_expansion_blocks π A hπ X U V hUV.2.2.1 hUV.2.2.2)
  refine ⟨∑' q, nearYTerm B U V q, hYmem, ?_⟩
  calc
    ‖Z - ∑' q, nearYTerm B U V q‖ ≤ nearC * ‖U * V - V * U‖ * ‖Z‖ := by
      simpa only [← hZexp] using
        near_laurent_series_reordering_le B U V hUV.2.2.1 hUV.2.2.2 ‖Z‖ hB
    _ ≤ nearC * ‖U * V - V * U‖ := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hnorm
        (mul_nonneg nearC_nonneg (norm_nonneg _))

end Papers.OaiNearInclusionsVon

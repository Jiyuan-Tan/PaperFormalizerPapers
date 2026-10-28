module

public import Papers.OaiNearInclusionsVon.Helpers.LaurentUnitary
public import Papers.OaiNearInclusionsVon.Helpers.AmplificationBicommutant

/-! Identify the conjugated amplified group algebra with its concrete carrier. -/

@[expose] public section

namespace Papers.OaiNearInclusionsVon

variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℂ D] [CompleteSpace D]

/-- [Left translation by a product-group element on the vector-valued
sequence space equals the amplification of scalar left translation](goal). -/
-- @node: lamAmp_eq_amplify
lemma lamAmp_eq_amplify (g : ProdGrp) : lamAmp (D := D) g = amplify (lamReg g) := by
  apply lp.ext_continuousLinearMap (by norm_num)
  intro y
  apply ContinuousLinearMap.ext
  intro v
  apply lp.ext
  funext x
  simp only [ContinuousLinearMap.comp_apply, lp.singleContinuousLinearMap_apply]
  rw [(amplify_spec (lamReg g)).1]
  simp only [lamAmp, lamReg, lpReindex_apply, Equiv.coe_mulLeft]
  by_cases h : y = g⁻¹ * x <;> simp [lp.single_apply, h]

/-- [The adjoint of amplified left translation by a group element is
amplified left translation by its inverse](goal). -/
-- @node: lamAmp_star
lemma lamAmp_star (g : ProdGrp) :
    star (lamAmp (D := D) g) = lamAmp (D := D) g⁻¹ := by
  unfold lamAmp
  rw [lpReindex_star]
  congr 1
  ext x <;> simp

/-- [The set of amplified left translations conjugated by W and its adjoint
is unchanged by taking adjoints of all its elements](goal). -/
-- @node: conjugated_lamAmp_range_star
lemma conjugated_lamAmp_range_star (W : Hsp D →L[ℂ] Hsp D) :
    star (Set.range (fun g : ProdGrp => W * lamAmp g * star W)) =
      Set.range (fun g : ProdGrp => W * lamAmp g * star W) := by
  have hg (g : ProdGrp) : star (W * lamAmp g * star W) =
      W * lamAmp (D := D) g⁻¹ * star W := by
    simp [star_mul, lamAmp_star, mul_assoc]
  ext T
  change star T ∈ Set.range (fun g : ProdGrp => W * lamAmp g * star W) ↔
    T ∈ Set.range (fun g : ProdGrp => W * lamAmp g * star W)
  constructor
  · rintro ⟨g, h⟩
    exact ⟨g⁻¹, by simpa only [hg, star_star] using congrArg star h⟩
  · rintro ⟨g, h⟩
    exact ⟨g⁻¹, by simpa only [hg] using congrArg star h⟩

set_option maxHeartbeats 800000 in
-- Unfolding the nested sequence-space carriers needs a larger reduction budget.
/-- If [π and A satisfy the circle-family conditions](hyp:hπ),
[U and V are unitary operators on a nonzero finite-dimensional space](hyp:hUV),
and [every product substitution has norm at most the square of the total
coefficient weight](hyp:hb), then [the source algebra consists exactly of
the amplifications of operators in the double commutant of scalar left
translations, conjugated by the diagonal unitary and its adjoint](goal). -/
-- @node: sourceAlg_carrier
lemma sourceAlg_carrier (π : CircleRep) (A : LaurentData) (hπ : IsCircleFamily π A)
    (U V : D →L[ℂ] D) (hUV : NearUnitaryPair U V)
    (hb : ∀ x : ProdGrp, ‖prodMap A U V x‖ ≤ S0 ^ 2) :
    (sourceAlg A U V hb : Set (Hsp D →L[ℂ] Hsp D)) =
      {Z | ∃ X ∈ commutant (commutant (Set.range lamReg)),
        Z = diagUnitary A U V hb * amplify (E := Lsp D) X * star (diagUnitary A U V hb)} := by
  let : Nontrivial D := hUV.1
  let : Nontrivial (Lsp D) := by
    obtain ⟨v, hv⟩ := exists_ne (0 : D)
    refine ⟨⟨lp.single 2 (1 : FreeGrp) (lp.single 2 (1 : FreeGrp) v), 0, ?_⟩⟩
    intro h
    apply hv
    have he := congrArg (fun ξ : Lsp D => ξ 1 1) h
    simpa using he
  let W := diagUnitary A U V hb
  have hW : W ∈ unitary (Hsp D →L[ℂ] Hsp D) :=
    diagUnitary_mem_unitary π A hπ U V hUV hb
  have hgen : Set.range (fun g : ProdGrp => W * lamAmp g * star W) =
      (fun X => W * amplify (E := Lsp D) X * star W) '' Set.range lamReg := by
    ext Z
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨lamReg g, ⟨g, rfl⟩, by simp only [lamAmp_eq_amplify]⟩
    · rintro ⟨X, ⟨g, rfl⟩, rfl⟩
      exact ⟨g, by simp only [lamAmp_eq_amplify]⟩
  simp only [sourceAlg, VonNeumannAlgebra.coe_commutant]
  change Set.centralizer
    (StarSubalgebra.centralizer ℂ (Set.range (fun g : ProdGrp =>
      W * lamAmp g * star W)) : Set (Hsp D →L[ℂ] Hsp D)) = _
  rw [StarSubalgebra.coe_centralizer, conjugated_lamAmp_range_star, Set.union_self, hgen]
  exact conjugated_amplification_bicommutant (Set.range lamReg) W hW

end Papers.OaiNearInclusionsVon

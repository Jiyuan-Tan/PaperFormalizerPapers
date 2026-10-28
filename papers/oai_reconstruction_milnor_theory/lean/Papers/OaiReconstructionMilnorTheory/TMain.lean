module

public import Papers.OaiReconstructionMilnorTheory.Helpers
public import Papers.OaiReconstructionMilnorTheory.Helpers.FieldReconstruction

/-! # Reconstruction of function fields from Milnor groups modulo p -/

public section

namespace Papers.OaiReconstructionMilnorTheory

variable (p : ℕ) {K L : Type*} [Field K] [Field L]

-- @node: thm:main
/-- Suppose [p is prime](hyp:hp), [K and L are finitely generated
characteristic-p extensions of their respective algebraically closed
subfields k and l](hyp:hfields), and [both extensions have transcendence
degree at least two](hyp:hdim). Then [every field isomorphism carrying k
onto l induces a compatible isomorphism on degree-one Milnor groups modulo p;
every compatible isomorphism is induced by such a field isomorphism up to
an invertible scalar modulo p; and two such field isomorphisms whose induced
maps differ by an invertible scalar are equal](goal). -/
theorem milnor_reconstruction_bijective (k : Subfield K) (l : Subfield L)
    (hp : PrimeChar p) (hfields : MainFields p k l) (hdim : MainDimension k l) :
    (∀ α : K ≃+* L, IsBaseIso k l (⇑α) → IsCompatibleIso p (inducedMap p α)) ∧
    (∀ Θ : MilnorOne K p → MilnorOne L p, IsCompatibleIso p Θ →
      ∃ α : K ≃+* L, IsBaseIso k l (⇑α) ∧
        ∃ r : (Coeff p)ˣ, Θ = scalarAct p r (inducedMap p α)) ∧
    (∀ α β : K ≃+* L, IsBaseIso k l (⇑α) → IsBaseIso k l (⇑β) →
      ∀ r : (Coeff p)ˣ, inducedMap p β = scalarAct p r (inducedMap p α) → α = β) := by
  refine ⟨fun α _ => inducedMap_isCompatibleIso p α, ?_, ?_⟩
  · intro Θ hΘ
    obtain ⟨n, hn, _⟩ := exists_unique_line_correction p k l hp
      ⟨hfields.1, hfields.2, hdim.1, hdim.2⟩ Θ hΘ
    obtain ⟨φ, hφ, _⟩ := hΘ.relations
    have hφbij : Function.Bijective φ := by rw [hφ]; exact hΘ.linear.2
    let F : MilnorOne K p →ₗ[Coeff p] MilnorOne L p := (n : Coeff p) • φ
    have hFbij : Function.Bijective F := n.isUnit.smul_bijective.comp hφbij
    let Ψ : MilnorOne K p ≃+ MilnorOne L p := AddEquiv.ofBijective F.toAddMonoidHom hFbij
    have hΨ : (Ψ : MilnorOne K p → MilnorOne L p) = scalarAct p n Θ := by
      funext x
      change (n : Coeff p) • φ x = (n : Coeff p) • Θ x
      rw [hφ]
    have hlines : ∀ S, IsProjLine p K S → IsProjLine p L (Ψ '' S) := by
      rw [hΨ]
      exact hn
    obtain ⟨α, hα⟩ := fieldIso_exists_of_lines p hp hfields.1.2.1 hfields.2.2.1
      (mainFields_projectiveLiftSpaces p k l hp hfields hdim) Ψ hlines
    refine ⟨α, fieldIso_preservesBase p k l hp hfields α, n⁻¹, ?_⟩
    funext x
    have hx : inducedMap p α x = (n : Coeff p) • Θ x := by
      rw [hα, hΨ]
      rfl
    change Θ x = ((n⁻¹ : (Coeff p)ˣ) : Coeff p) • inducedMap p α x
    rw [hx, ← mul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  · intro α β _ _ r hr
    let : FiniteDimensional ↥(powSubfield p L) L :=
      geometricField_finiteDimensional_powSubfield p ↥l L hp hfields.2
    have hdegree := (finrank_powSubfield_eq_pow_trdeg p ↥l L hp hfields.2).2
    change Module.finrank ↥(powSubfield p L) L = p ^ (Algebra.trdeg ↥l L).toNat at hdegree
    let : Algebra.EssFiniteType ↥l L := IntermediateField.fg_top_iff.mp hfields.2.2.2
    have hd : 2 ≤ (Algebra.trdeg ↥l L).toNat := by
      simpa only [Cardinal.toNat_ofNat] using
        Cardinal.toNat_le_toNat hdim.2 (trdeg_lt_aleph0 ↥l L)
    have hdimL : 2 ≤ Module.finrank ↥(powSubfield p L) L := by
      rw [hdegree]
      exact (show 2 ≤ p by exact hp.two_le).trans
        (Nat.le_pow (by omega))
    exact fieldIso_eq_of_inducedMap_scalar p hp hfields.2.2.1 hdimL α β r hr

end Papers.OaiReconstructionMilnorTheory


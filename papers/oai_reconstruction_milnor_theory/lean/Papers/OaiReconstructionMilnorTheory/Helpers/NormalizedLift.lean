module

public import Papers.OaiReconstructionMilnorTheory.Helpers.FieldGeometry
public import Papers.OaiReconstructionMilnorTheory.Helpers.PerfectCore

/-! # Recovering a field isomorphism from a normalized additive lift

The multiplicative law on Milnor classes makes the two additive maps associated
with multiplication by a nonzero element projectively equal. Scalar uniqueness,
evaluated at one, upgrades this equality to equality of field elements.
-/

@[expose] public section

namespace Papers.OaiReconstructionMilnorTheory

variable (p : ℕ) {K L : Type*} [Field K] [Field L]

-- @node: normalizedLift_map_mul
/-- If L is finite dimensional over its power subfield and
[this dimension is at least two](hyp:hd),
[the additive equivalence S sends one to one](hyp:h1), and [S induces the additive
map Ψ on the Milnor classes of all nonzero elements](hyp:hcls), then
[S sends the product of f and g to the product of their images](goal). -/
lemma normalizedLift_map_mul [FiniteDimensional ↥(powSubfield p L) L]
    (hd : 2 ≤ Module.finrank ↥(powSubfield p L) L)
    (Ψ : MilnorOne K p →+ MilnorOne L p) (S : K ≃+ L)
    (h1 : S 1 = 1)
    (hcls : ∀ x, x ≠ 0 → cls p (S x) = Ψ (cls p x)) (f g : K) :
    S (f * g) = S f * S g := by
  by_cases hf : f = 0
  · simp [hf]
  have hSf : S f ≠ 0 := fun h => hf (S.injective (h.trans S.map_zero.symm))
  let T : L →+ L :=
    { toFun := fun w => (S f)⁻¹ * S (f * S.symm w)
      map_zero' := by simp
      map_add' := by intros; simp only [map_add, mul_add] }
  have hlines (w : L) : ∃ a : ↥(powSubfield p L), T w = a • w := by
    by_cases hw : w = 0
    · exact ⟨0, by simp [hw]⟩
    have hv : S.symm w ≠ 0 := fun h => hw (by simpa using congrArg S h)
    have hfv : S (f * S.symm w) ≠ 0 := fun h =>
      mul_ne_zero hf hv (S.injective (h.trans S.map_zero.symm))
    have heq : cls p (S (f * S.symm w)) = cls p (S f * w) := by
      rw [hcls _ (mul_ne_zero hf hv), cls_mul p f _ hf hv, map_add,
        cls_mul p (S f) w hSf hw, ← hcls f hf, ← hcls _ hv, S.apply_symm_apply]
    let a : ↥(powSubfield p L) :=
      ⟨S (f * S.symm w) / (S f * w),
        cls_eq_ratio_mem_powSubfield p L hfv (mul_ne_zero hSf hw) heq⟩
    refine ⟨a, ?_⟩
    change (S f)⁻¹ * S (f * S.symm w) =
      (S (f * S.symm w) / (S f * w)) * w
    field_simp
  obtain ⟨c, hc⟩ := projective_additive_scalar hd T hlines
  have hSsymm1 : S.symm 1 = 1 := S.injective (by simpa using h1.symm)
  have hc1 : (c : L) = 1 := by
    have h := hc 1
    change (S f)⁻¹ * S (f * S.symm 1) = (c : L) * 1 at h
    simpa only [hSsymm1, mul_one, inv_mul_cancel₀ hSf] using h.symm
  have h := hc (S g)
  change (S f)⁻¹ * S (f * S.symm (S g)) = (c : L) * S g at h
  rw [S.symm_apply_apply, hc1, one_mul] at h
  calc
    S (f * g) = S f * ((S f)⁻¹ * S (f * g)) := by rw [← mul_assoc, mul_inv_cancel₀ hSf, one_mul]
    _ = S f * S g := by rw [h]

-- @node: normalizedLiftRingEquiv
/-- For [an exponent p](hyp:p), a target field finite dimensional over its power
subfield with [dimension at least two](hyp:hd), [an additive map Ψ on first Milnor groups](hyp:Ψ),
and [an additive equivalence S between K and L](hyp:S) that [sends one to one](hyp:h1)
and [induces Ψ on all nonzero elements' Milnor classes](hyp:hcls),
[the recovered field isomorphism](goal) is S equipped with its multiplicative law. -/
noncomputable def normalizedLiftRingEquiv [FiniteDimensional ↥(powSubfield p L) L]
    (hd : 2 ≤ Module.finrank ↥(powSubfield p L) L)
    (Ψ : MilnorOne K p →+ MilnorOne L p) (S : K ≃+ L)
    (h1 : S 1 = 1) (hcls : ∀ x, x ≠ 0 → cls p (S x) = Ψ (cls p x)) : K ≃+* L :=
  { S with map_mul' := normalizedLift_map_mul p hd Ψ S h1 hcls }

-- @node: normalizedLiftRingEquiv_inducedMap
/-- If L is finite dimensional over its power subfield and
[this dimension is at least two](hyp:hd),
[S sends one to one](hyp:h1), and [S induces Ψ on the Milnor classes of all nonzero
elements](hyp:hcls), then [the field isomorphism recovered from S induces exactly
Ψ on first Milnor groups](goal). -/
lemma normalizedLiftRingEquiv_inducedMap [FiniteDimensional ↥(powSubfield p L) L]
    (hd : 2 ≤ Module.finrank ↥(powSubfield p L) L)
    (Ψ : MilnorOne K p →+ MilnorOne L p) (S : K ≃+ L)
    (h1 : S 1 = 1) (hcls : ∀ x, x ≠ 0 → cls p (S x) = Ψ (cls p x)) :
    inducedMap p (normalizedLiftRingEquiv p hd Ψ S h1 hcls) = Ψ := by
  funext x
  obtain ⟨f, hf, rfl⟩ := cls_surjective_nonzero p x
  rw [inducedMap_cls p _ hf]
  exact hcls f hf

-- @node: fieldIso_image_iterated_powers
/-- [A field isomorphism α maps the set of p-to-the-m-th powers in K exactly
onto the set of p-to-the-m-th powers in L](goal). -/
lemma fieldIso_image_iterated_powers (α : K ≃+* L) (m : ℕ) :
    α '' (Set.range fun x : K => x ^ (p ^ m)) =
      Set.range fun y : L => y ^ (p ^ m) := by
  ext y
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨α x, (map_pow α x _).symm⟩
  · rintro ⟨y, rfl⟩
    exact ⟨α.symm y ^ (p ^ m), ⟨α.symm y, rfl⟩, by simp⟩

-- @node: fieldIso_mem_perfectCore
/-- [The image of x under a field isomorphism α is a p-to-the-m-th power for
every positive integer m exactly when x has the same property](goal). -/
lemma fieldIso_mem_perfectCore (α : K ≃+* L) (x : K) :
    α x ∈ (⋂ m : ℕ, ⋂ (_ : 1 ≤ m), Set.range fun y : L => y ^ (p ^ m)) ↔
    x ∈ (⋂ m : ℕ, ⋂ (_ : 1 ≤ m), Set.range fun y : K => y ^ (p ^ m)) := by
  simp only [Set.mem_iInter, Set.mem_range]
  constructor
  · intro hx m hm
    obtain ⟨y, hy⟩ := hx m hm
    exact ⟨α.symm y, by simpa only [map_pow, α.symm_apply_apply] using congrArg α.symm hy⟩
  · intro hx m hm
    obtain ⟨y, hy⟩ := hx m hm
    exact ⟨α y, by simpa only [map_pow] using congrArg α hy⟩

-- @node: fieldIso_preservesBase
/-- If [p is prime](hyp:hp) and [K and L are finitely generated extensions of
the algebraically closed subfields k and l, both in characteristic p](hyp:hfields),
then [every field isomorphism α from K to L maps k exactly onto l and hence is
an isomorphism preserving the designated bases](goal). -/
lemma fieldIso_preservesBase (k : Subfield K) (l : Subfield L)
    (hp : PrimeChar p) (hfields : MainFields p k l) (α : K ≃+* L) :
    IsBaseIso k l (⇑α) := by
  have hk := iInter_pow_eq_base p ↥k K hp hfields.1
  have hl := iInter_pow_eq_base p ↥l L hp hfields.2
  have hrk : Set.range (algebraMap ↥k K) = (k : Set K) := Subtype.range_coe
  have hrl : Set.range (algebraMap ↥l L) = (l : Set L) := Subtype.range_coe
  rw [hrk] at hk
  rw [hrl] at hl
  refine ⟨⟨α, rfl⟩, ?_⟩
  change α '' (k : Set K) = (l : Set L)
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [← hl]
    exact (fieldIso_mem_perfectCore p α x).mpr (hk.symm ▸ hx)
  · intro hy
    refine ⟨α.symm y, ?_, α.apply_symm_apply y⟩
    rw [← hk]
    apply (fieldIso_mem_perfectCore p α (α.symm y)).mp
    simpa only [α.apply_symm_apply, hl] using hy

end Papers.OaiReconstructionMilnorTheory

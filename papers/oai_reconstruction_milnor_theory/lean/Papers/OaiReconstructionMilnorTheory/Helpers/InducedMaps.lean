module

public import Papers.OaiReconstructionMilnorTheory.Helpers.Isomorphisms
public import Mathlib.Algebra.Group.TypeTags.Hom

/-! # Field isomorphisms acting on Milnor classes and Steinberg relations -/

@[expose] public section

namespace Papers.OaiReconstructionMilnorTheory

variable (p : ℕ) {K L : Type*} [Field K] [Field L]

-- @node: inducedMap_power_subgroup
/-- For an exponent p and [a field isomorphism α from K to L](hyp:α),
[α sends every p-th power of a nonzero element of K to a p-th power of a
nonzero element of L](goal). -/
lemma inducedMap_power_subgroup (α : K ≃+* L) :
    (powMonoidHom p : Kˣ →* Kˣ).range ≤
      ((powMonoidHom p : Lˣ →* Lˣ).range).comap (Units.map α.toMonoidHom) := by
  rintro u ⟨v, rfl⟩
  exact ⟨Units.map α.toMonoidHom v, (map_pow _ _ _).symm⟩

-- @node: inducedLinearMap
/-- For [an exponent p](hyp:p) and [a field isomorphism α](hyp:α) from
[a field K](hyp:K) to [a field L](hyp:L), [the induced coefficient-linear map
between the degree-one Milnor groups modulo p](goal) sends the class of each
nonzero element of K to the class of its image under α. -/
noncomputable def inducedLinearMap (α : K ≃+* L) :
    MilnorOne K p →ₗ[Coeff p] MilnorOne L p :=
  AddMonoidHom.toZModLinearMap p
    (show MilnorOne K p →+ MilnorOne L p from
      (QuotientGroup.map _ _ (Units.map α.toMonoidHom)
        (inducedMap_power_subgroup p α)).toAdditive)

-- @node: inducedLinearMap_cls
/-- For an exponent p and [a field isomorphism α from K to L](hyp:α),
if [f is nonzero](hyp:hf), then [the induced linear map sends the Milnor class
of f modulo p to the class of α of f](goal). -/
lemma inducedLinearMap_cls (α : K ≃+* L) {f : K} (hf : f ≠ 0) :
    inducedLinearMap p α (cls p f) = cls p (α f) := by
  have haf : α f ≠ 0 := (map_ne_zero α).mpr hf
  unfold cls MilnorOne
  rw [dif_neg hf, dif_neg haf]
  change Additive.ofMul (QuotientGroup.mk (Units.map α.toMonoidHom (Units.mk0 f hf))) = _
  congr 2
  ext
  rfl

-- @node: inducedLinearMap_eq
/-- For an exponent p and [a field isomorphism α from K to L](hyp:α),
[the induced linear map on degree-one Milnor groups modulo p agrees pointwise
with the induced map defined by choosing representatives](goal). -/
lemma inducedLinearMap_eq (α : K ≃+* L) : ⇑(inducedLinearMap p α) = inducedMap p α := by
  funext x
  have hrep : cls p ((Quotient.out (Additive.toMul x) : Kˣ) : K) = x := by
    unfold cls MilnorOne
    rw [dif_neg (Units.ne_zero _)]
    have hu : Units.mk0 ((Quotient.out (Additive.toMul x) : Kˣ) : K) (Units.ne_zero _) =
        Quotient.out (Additive.toMul x) := by ext; rfl
    rw [hu]
    exact congrArg Additive.ofMul (Quotient.out_eq (Additive.toMul x))
  change inducedLinearMap p α x = cls p (α _)
  conv_lhs => rw [← hrep]
  exact inducedLinearMap_cls p α (Units.ne_zero _)

-- @node: inducedMap_cls
/-- For an exponent p and [a field isomorphism α from K to L](hyp:α),
if [f is nonzero](hyp:hf), then [the induced map sends the Milnor class of f
modulo p to the class of α of f](goal). -/
lemma inducedMap_cls (α : K ≃+* L) {f : K} (hf : f ≠ 0) :
    inducedMap p α (cls p f) = cls p (α f) := by
  rw [← inducedLinearMap_eq]
  exact inducedLinearMap_cls p α hf

-- @node: cls_surjective_nonzero
/-- For an exponent p and [a degree-one Milnor class x of K modulo p](hyp:x),
[there is a nonzero field element f whose class equals x](goal). -/
lemma cls_surjective_nonzero (x : MilnorOne K p) : ∃ f : K, f ≠ 0 ∧ cls p f = x := by
  let u : Kˣ := Quotient.out (Additive.toMul x)
  refine ⟨u, u.ne_zero, ?_⟩
  unfold cls MilnorOne
  rw [dif_neg u.ne_zero]
  have hu : Units.mk0 (u : K) u.ne_zero = u := by ext; rfl
  rw [hu]
  exact congrArg Additive.ofMul (Quotient.out_eq (Additive.toMul x))

-- @node: inducedMap_symm_apply
/-- For an exponent p, [a field isomorphism α from K to L](hyp:α), and
[a degree-one Milnor class x of K modulo p](hyp:x), [applying the map induced
by α and then the map induced by its inverse returns x](goal). -/
lemma inducedMap_symm_apply (α : K ≃+* L) (x : MilnorOne K p) :
    inducedMap p α.symm (inducedMap p α x) = x := by
  obtain ⟨f, hf, rfl⟩ := cls_surjective_nonzero p x
  rw [inducedMap_cls p α hf, inducedMap_cls p α.symm ((map_ne_zero α).mpr hf),
    α.symm_apply_apply]

-- @node: inducedMap_bijective
/-- For an exponent p and [a field isomorphism α from K to L](hyp:α),
[the induced map between their degree-one Milnor groups modulo p is bijective](goal). -/
lemma inducedMap_bijective (α : K ≃+* L) : Function.Bijective (inducedMap p α) :=
  ⟨Function.LeftInverse.injective (inducedMap_symm_apply p α),
    Function.RightInverse.surjective (inducedMap_symm_apply p α.symm)⟩

-- @node: inducedMap_steinberg_le
/-- For an exponent p and [a field isomorphism α from K to L](hyp:α),
[the tensor map obtained by applying the induced Milnor linear map in both
factors sends the Steinberg relation space for K into that for L](goal). -/
lemma inducedMap_steinberg_le (α : K ≃+* L) :
    Submodule.map (TensorProduct.map (inducedLinearMap p α) (inducedLinearMap p α))
      (steinbergRel p K) ≤ steinbergRel p L := by
  rw [Submodule.map_le_iff_le_comap, steinbergRel, Submodule.span_le]
  rintro z ⟨f, hf, hf1, rfl⟩
  change TensorProduct.map _ _ _ ∈ steinbergRel p L
  rw [TensorProduct.map_tmul, inducedLinearMap_cls p α hf,
    inducedLinearMap_cls p α (sub_ne_zero.mpr (Ne.symm hf1))]
  apply Submodule.subset_span
  refine ⟨α f, (map_ne_zero α).mpr hf, ?_, ?_⟩
  · exact fun h => hf1 (α.injective (h.trans α.map_one.symm))
  · simp only [map_sub, map_one]

-- @node: inducedMap_steinberg_eq
/-- For an exponent p and [a field isomorphism α from K to L](hyp:α),
[the image of the Steinberg relation space for K under the tensor map applying
the induced Milnor linear map in both factors is exactly the relation space
for L](goal). -/
lemma inducedMap_steinberg_eq (α : K ≃+* L) :
    Submodule.map (TensorProduct.map (inducedLinearMap p α) (inducedLinearMap p α))
      (steinbergRel p K) = steinbergRel p L := by
  apply le_antisymm (inducedMap_steinberg_le p α)
  intro z hz
  let T := TensorProduct.map (inducedLinearMap p α) (inducedLinearMap p α)
  let U := TensorProduct.map (inducedLinearMap p α.symm) (inducedLinearMap p α.symm)
  have hTU : T.comp U = LinearMap.id := by
    apply TensorProduct.ext'
    intro x y
    simp only [T, U, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply]
    simp only [inducedLinearMap_eq]
    have h (w : MilnorOne L p) : inducedMap p α (inducedMap p α.symm w) = w := by
      simpa only [RingEquiv.symm_symm] using inducedMap_symm_apply p α.symm w
    rw [h x, h y]
  refine ⟨U z, inducedMap_steinberg_le p α.symm ⟨z, hz, rfl⟩, ?_⟩
  exact congrArg (fun f : _ →ₗ[Coeff p] _ => f z) hTU

-- @node: inducedMap_isCompatibleIso
/-- For an exponent p and [a field isomorphism α from K to L](hyp:α),
[the induced map on degree-one Milnor groups modulo p is a coefficient-linear
bijection whose tensor map takes the Steinberg relation space for K onto
that for L](goal). -/
lemma inducedMap_isCompatibleIso (α : K ≃+* L) : IsCompatibleIso p (inducedMap p α) := by
  refine ⟨⟨?_, inducedMap_bijective p α⟩, inducedLinearMap p α,
    inducedLinearMap_eq p α, inducedMap_steinberg_eq p α⟩
  rw [← inducedLinearMap_eq]
  exact (inducedLinearMap p α).isLinear

end Papers.OaiReconstructionMilnorTheory

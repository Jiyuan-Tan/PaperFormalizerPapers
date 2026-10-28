module

public import Papers.OaiReconstructionMilnorTheory.Helpers.Isomorphisms
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.Algebra.Field.ZMod

/-! # Inversion and scalar multiplication of compatible isomorphisms -/

@[expose] public section

namespace Papers.OaiReconstructionMilnorTheory

variable (p : ℕ) {K L : Type*} [Field K] [Field L]

-- @node: compatibleLinearEquiv
/-- For [a modulus p](hyp:p) and [a map Θ between first Milnor groups modulo p](hyp:Θ)
that [is a linear bijection whose tensor square maps the source Steinberg relations
onto the target Steinberg relations](hyp:hΘ), [the associated linear equivalence](goal)
is the same map equipped with its linearity and bijectivity. -/
noncomputable def compatibleLinearEquiv (Θ : MilnorOne K p → MilnorOne L p)
    (hΘ : IsCompatibleIso p Θ) : MilnorOne K p ≃ₗ[Coeff p] MilnorOne L p :=
  LinearEquiv.ofBijective
    { toFun := Θ
      map_add' := hΘ.linear.1.map_add
      map_smul' := hΘ.linear.1.map_smul } hΘ.linear.2

-- @node: compatibleLinearEquiv_apply
/-- If [Θ is a linear bijection whose tensor square maps the source Steinberg relations
onto the target Steinberg relations](hyp:hΘ), then [its associated linear equivalence
sends every first Milnor class x to Θ applied to x](goal). -/
lemma compatibleLinearEquiv_apply (Θ : MilnorOne K p → MilnorOne L p)
    (hΘ : IsCompatibleIso p Θ) (x : MilnorOne K p) :
    compatibleLinearEquiv p Θ hΘ x = Θ x := rfl

-- @node: compatibleLinearEquiv_relations
/-- If [Θ is a linear bijection whose tensor square maps the source Steinberg relations
onto the target Steinberg relations](hyp:hΘ), then [the tensor square of its associated
linear equivalence maps the source Steinberg relation submodule exactly onto the target one](goal). -/
lemma compatibleLinearEquiv_relations (Θ : MilnorOne K p → MilnorOne L p)
    (hΘ : IsCompatibleIso p Θ) :
    (steinbergRel p K).map (TensorProduct.map
      (compatibleLinearEquiv p Θ hΘ).toLinearMap
      (compatibleLinearEquiv p Θ hΘ).toLinearMap) = steinbergRel p L := by
  obtain ⟨φ, hφ, hrel⟩ := hΘ.relations
  have heq : φ = (compatibleLinearEquiv p Θ hΘ).toLinearMap := by
    ext x
    exact congrFun hφ x
  rwa [heq] at hrel

-- @node: compatibleLinearEquiv_symm_compatible
/-- If [Θ is a linear bijection whose tensor square maps the source Steinberg relations
onto the target Steinberg relations](hyp:hΘ), then [the inverse of its associated linear
equivalence is also a linear bijection whose tensor square maps the target Steinberg
relations onto the source Steinberg relations](goal). -/
lemma compatibleLinearEquiv_symm_compatible (Θ : MilnorOne K p → MilnorOne L p)
    (hΘ : IsCompatibleIso p Θ) :
    IsCompatibleIso p (compatibleLinearEquiv p Θ hΘ).symm := by
  let e := compatibleLinearEquiv p Θ hΘ
  refine ⟨⟨⟨e.symm.map_add, e.symm.map_smul⟩, e.symm.bijective⟩,
    ⟨e.symm.toLinearMap, rfl, ?_⟩⟩
  rw [← compatibleLinearEquiv_relations p Θ hΘ, ← Submodule.map_comp]
  have hid : (TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap).comp
      (TensorProduct.map e.toLinearMap e.toLinearMap) = LinearMap.id := by
    ext x y
    simp
  change (steinbergRel p K).map
    ((TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap).comp
      (TensorProduct.map e.toLinearMap e.toLinearMap)) = _
  rw [hid, Submodule.map_id]

-- @node: scalarAct_bijective
/-- If [Θ is a bijection between first Milnor groups modulo p](hyp:hΘ), then
[multiplying each value of Θ by any invertible coefficient r gives a bijection](goal). -/
lemma scalarAct_bijective (r : (Coeff p)ˣ)
    (Θ : MilnorOne K p → MilnorOne L p) (hΘ : Function.Bijective Θ) :
    Function.Bijective (scalarAct p r Θ) := by
  constructor
  · intro x y h
    apply hΘ.1
    have heq := congrArg (fun z => (↑r⁻¹ : Coeff p) • z) h
    simpa [scalarAct, smul_smul] using heq
  · intro y
    obtain ⟨x, hx⟩ := hΘ.2 ((↑r⁻¹ : Coeff p) • y)
    refine ⟨x, ?_⟩
    simp [scalarAct, hx, smul_smul]

-- @node: scalarAct_compatible
/-- If [p is prime](hyp:hp) and [Θ is a linear bijection whose tensor square maps the
source Steinberg relations onto the target Steinberg relations](hyp:hΘ), then
[multiplying each value of Θ by any invertible coefficient r again gives a linear
bijection whose tensor square maps the source Steinberg relations onto the target ones](goal). -/
lemma scalarAct_compatible (hp : PrimeChar p) (r : (Coeff p)ˣ)
    (Θ : MilnorOne K p → MilnorOne L p) (hΘ : IsCompatibleIso p Θ) :
    IsCompatibleIso p (scalarAct p r Θ) := by
  let : Fact p.Prime := ⟨hp⟩
  let e := compatibleLinearEquiv p Θ hΘ
  let φ : MilnorOne K p →ₗ[Coeff p] MilnorOne L p := (r : Coeff p) • e.toLinearMap
  refine ⟨⟨⟨?_, ?_⟩, scalarAct_bijective p r Θ hΘ.linear.2⟩,
    ⟨φ, rfl, ?_⟩⟩
  · exact φ.map_add
  · exact φ.map_smul
  · change (steinbergRel p K).map
      (TensorProduct.map ((r : Coeff p) • e.toLinearMap)
        ((r : Coeff p) • e.toLinearMap)) = _
    rw [TensorProduct.map_smul_left, TensorProduct.map_smul_right, smul_smul]
    rw [Submodule.map_smul (TensorProduct.map e.toLinearMap e.toLinearMap)
      (steinbergRel p K) ((r : Coeff p) * (r : Coeff p))
      (mul_ne_zero (Units.ne_zero r) (Units.ne_zero r))]
    exact compatibleLinearEquiv_relations p Θ hΘ

-- @node: def:scalar-action
/-- For [a modulus p](hyp:p) that [is prime](hyp:hp), [the action of invertible coefficients
on compatible Milnor isomorphisms](goal) [multiplies each value of an isomorphism by the
acting coefficient](step:1), with [the coefficient one acting as the identity](step:2)
and [a product of coefficients acting by successive scalar multiplications](step:3). -/
@[instance_reducible]
noncomputable def scalarCompatibleAction (hp : PrimeChar p) :
    MulAction (Coeff p)ˣ
      {Θ : MilnorOne K p → MilnorOne L p // IsCompatibleIso p Θ} where
  smul r Θ := ⟨scalarAct p r Θ.val, scalarAct_compatible p hp r Θ.val Θ.property⟩
  one_smul Θ := Subtype.ext (funext (fun x => one_smul (Coeff p) (Θ.val x)))
  mul_smul r s Θ := Subtype.ext (funext (fun x =>
    mul_smul (r : Coeff p) (s : Coeff p) (Θ.val x)))

end Papers.OaiReconstructionMilnorTheory

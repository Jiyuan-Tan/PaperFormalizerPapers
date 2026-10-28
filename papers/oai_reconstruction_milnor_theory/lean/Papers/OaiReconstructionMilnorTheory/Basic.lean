module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Milnor groups modulo the characteristic and power-subfield geometry

The group and tensor quotients are concrete. Characteristic, degree, and generation
conditions are named propositions, threaded by the statements that require them.
-/

@[expose] public section

namespace Papers.OaiReconstructionMilnorTheory

open scoped TensorProduct

-- @env: S1
variable (p : ℕ) -- @realizes p(carrier ℕ; primality via PrimeChar)
variable (F : Type*) [Field F] -- @realizes F(field carrier; characteristic via FieldCharP)

-- @node: ass:prime
/-- For [the modulus p](hyp:p), [the prime-characteristic condition](goal) means that p is prime. -/
def PrimeChar : Prop := p.Prime -- @realizes p(prime modulus)

-- @node: ass:field-characteristic
/-- For [a field F](hyp:F) and [a modulus p](hyp:p), [the characteristic condition](goal)
means that F has characteristic p. -/
def FieldCharP : Prop := CharP F p -- @realizes F(characteristic p)

-- @node: def:coefficients
/-- For [a modulus p](hyp:p), [the coefficient ring](goal) is the ring of integers modulo p. -/
abbrev Coeff : Type := ZMod p -- @realizes \Fp(ZMod p) @realizes \Lambda(F_p)

-- @node: def:milnor-one
/-- For [a field F](hyp:F) and [a modulus p](hyp:p), [the first Milnor group modulo p](goal)
is the multiplicative group of nonzero elements of F modulo p-th powers, written additively. -/
def MilnorOne (F : Type*) [Field F] (p : ℕ) : Type _ := -- @realizes V_F(units mod p-th powers)
  Additive (Fˣ ⧸ (powMonoidHom p : Fˣ →* Fˣ).range)

/-- For [a field F](hyp:F) and [a modulus p](hyp:p), the quotient of nonzero elements by
p-th powers has [an abelian group structure written additively](goal). -/
instance : AddCommGroup (MilnorOne F p) :=
  inferInstanceAs (AddCommGroup (Additive (Fˣ ⧸ (powMonoidHom p : Fˣ →* Fˣ).range)))

-- @node: milnorOne_nsmul_eq_zero
/-- [Adding any element of the first Milnor group modulo p to itself p times gives zero](goal). -/
lemma milnorOne_nsmul_eq_zero (x : MilnorOne F p) : p • x = 0 := by
  change Additive.ofMul (x.toMul ^ p) = Additive.ofMul 1
  congr 1
  induction x.toMul using QuotientGroup.induction_on with
  | H u =>
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).2 ⟨u, rfl⟩

/-- For [a field F](hyp:F) and [a modulus p](hyp:p), the first Milnor group modulo p has
[a module structure over the integers modulo p](goal). -/
noncomputable instance : Module (Coeff p) (MilnorOne F p) :=
  AddCommGroup.zmodModule (milnorOne_nsmul_eq_zero p F)

variable {F}

open Classical in
-- @node: def:class-notation
/-- For [a modulus p](hyp:p) and [an element f of the field](hyp:f), [the class of f](goal)
is zero when f is zero and otherwise is its multiplicative class modulo p-th powers. -/
noncomputable def cls (f : F) : MilnorOne F p := -- @realizes [f](multiplicative class)
  if h : f = 0 then 0 else Additive.ofMul (QuotientGroup.mk (Units.mk0 f h))

-- @node: cls_mul
/-- If [f is nonzero](hyp:hf) and [g is nonzero](hyp:hg), then
[the class of their product is the sum of their classes modulo p-th powers](goal). -/
lemma cls_mul (f : F) (g : F) -- @realizes f(carrier F) @realizes g(carrier F)
    (hf : f ≠ 0) (hg : g ≠ 0) : -- @realizes f(nonzero) @realizes g(nonzero)
    cls p (f * g) = cls p f + cls p g := by
  unfold cls MilnorOne
  rw [dif_neg hf, dif_neg hg, dif_neg (mul_ne_zero hf hg)]
  change (QuotientGroup.mk (Units.mk0 (f * g) _) :
    Fˣ ⧸ (powMonoidHom p : Fˣ →* Fˣ).range) =
      QuotientGroup.mk (Units.mk0 f hf) * QuotientGroup.mk (Units.mk0 g hg)
  rw [← QuotientGroup.mk_mul]
  congr 1
  ext
  rfl

-- @node: cls_zpow
/-- If [f is nonzero](hyp:hf), then [the class of f raised to any integer power r is
r times the class of f in the first Milnor group modulo p](goal). -/
lemma cls_zpow (f : F) (hf : f ≠ 0) (r : ℤ) : -- @realizes r(integer exponent)
    cls p (f ^ r) = r • cls p f := by
  unfold cls MilnorOne
  rw [dif_neg hf, dif_neg (zpow_ne_zero r hf)]
  change (QuotientGroup.mk (Units.mk0 (f ^ r) _) :
    Fˣ ⧸ (powMonoidHom p : Fˣ →* Fˣ).range) =
      (QuotientGroup.mk (Units.mk0 f hf)) ^ r
  rw [← QuotientGroup.mk_zpow]
  congr 1
  ext
  simp

variable (F)

-- @node: def:steinberg-relations
-- @realizes R_F(Steinberg span)
/-- For [a field F](hyp:F) and [a modulus p](hyp:p), [the Steinberg relation submodule](goal)
is spanned over the integers modulo p by tensors of the classes of f and 1 minus f,
where f ranges over elements of F other than zero and one. -/
noncomputable def steinbergRel :
    Submodule (Coeff p) (MilnorOne F p ⊗[Coeff p] MilnorOne F p) :=
  Submodule.span (Coeff p) {x | ∃ f : F, f ≠ 0 ∧ f ≠ 1 ∧
    x = cls p f ⊗ₜ[Coeff p] cls p (1 - f)} -- @realizes f(nonzero, not one)

-- @node: def:milnor-two
/-- For [a field F](hyp:F) and [a modulus p](hyp:p), [the second Milnor group modulo p](goal)
is the tensor square of the first Milnor group over the integers modulo p,
quotiented by the Steinberg relation submodule. -/
def MilnorTwo : Type _ := -- @realizes W_F(tensor quotient by R_F)
  (MilnorOne F p ⊗[Coeff p] MilnorOne F p) ⧸ steinbergRel p F

/-- For [a field F](hyp:F) and [a modulus p](hyp:p), the second Milnor group modulo p
inherits [an additive abelian group structure](goal) from its tensor quotient. -/
noncomputable instance : AddCommGroup (MilnorTwo p F) :=
  inferInstanceAs (AddCommGroup ((MilnorOne F p ⊗[Coeff p] MilnorOne F p) ⧸ steinbergRel p F))

/-- For [a field F](hyp:F) and [a modulus p](hyp:p), the second Milnor group modulo p
inherits [a module structure over the integers modulo p](goal) from its tensor quotient. -/
noncomputable instance : Module (Coeff p) (MilnorTwo p F) :=
  inferInstanceAs (Module (Coeff p) ((MilnorOne F p ⊗[Coeff p] MilnorOne F p) ⧸ steinbergRel p F))

variable {F}

-- @node: def:milnor-symbol
/-- For [a modulus p](hyp:p) and field elements [f](hyp:f) and [g](hyp:g), with
[f nonzero](hyp:_hf) and [g nonzero](hyp:_hg), [their Milnor symbol](goal) is the image
of the tensor of their classes in the second Milnor group modulo p. -/
noncomputable def milnorSymbol (f g : F) -- @realizes f(carrier F) @realizes g(carrier F)
    (_hf : f ≠ 0) -- @realizes f(nonzero symbol input)
    (_hg : g ≠ 0) : -- @realizes g(nonzero symbol input)
    MilnorTwo p F := -- @realizes \{f,g\}_F(tensor class)
  (steinbergRel p F).mkQ (cls p f ⊗ₜ[Coeff p] cls p g)

variable (F)

-- @node: def:outline-power-subfield
/-- For [a field F](hyp:F) and [an exponent p](hyp:p), [the power subfield](goal)
is the smallest subfield of F containing all p-th powers. -/
def powSubfield : Subfield F := -- @realizes C_F(F^p) @realizes C(F^p)
  Subfield.closure (Set.range fun x : F => x ^ p)

-- @node: def:projective-lines
/-- For [a field F](hyp:F), [a modulus p](hyp:p), and [a set S of first Milnor classes](hyp:S),
[the projective-line condition](goal) means that there is a vector subspace W of F over
its power subfield such that [W has dimension two](step:1) and
[S consists exactly of the classes of nonzero elements of W](step:2). -/
def IsProjLine (S : Set (MilnorOne F p)) : Prop :=
  ∃ W : Submodule ↥(powSubfield p F) F,
    Module.finrank ↥(powSubfield p F) W = 2 ∧
    S = {x | ∃ f ∈ W, f ≠ 0 ∧ cls p f = x}

variable {F}

-- @node: def:projective-points
/-- For [a modulus p](hyp:p) and [a first Milnor class x](hyp:x), [the projective point
represented by x](goal) consists of zero together with all nonzero field elements whose class is x. -/
def projPoint (x : MilnorOne F p) : Set F := -- @realizes \PP_C(F)(point represented by x)
  {f | f = 0 ∨ (f ≠ 0 ∧ cls p f = x)}

-- @env: S2
variable (κ F : Type*) [Field κ] [Field F] [Algebra κ F] -- @realizes \kappa(base via algebraMap)

-- @node: ass:geometric-field
/-- For [a modulus p](hyp:p), [a base field κ](hyp:κ), and [an extension field F](hyp:F),
[the geometric-field condition](goal) requires that [κ is algebraically closed](step:1),
[F has characteristic p](step:2), and [F is finitely generated as a field over κ](step:3). -/
def GeometricField : Prop :=
  IsAlgClosed κ ∧ -- @realizes \kappa(algebraically closed base)
  CharP F p ∧ -- @realizes F(characteristic p in the geometric setting)
  (⊤ : IntermediateField κ F).FG -- @realizes F(finitely generated over κ)

-- @node: def:power-degree-setup
/-- For [an exponent p](hyp:p), [a base field κ](hyp:κ), and [an extension field F](hyp:F),
[the power-degree setup](goal) pairs the power subfield of F with its transcendence
degree over κ, converted to a natural number. -/
noncomputable def powerDegreeSetup : Subfield F × ℕ :=
  (powSubfield p F, (Algebra.trdeg κ F).toNat) -- @realizes C(F^p) @realizes d(transcendence degree)

-- @env: S3
variable {κ F} {r : ℕ}

-- @node: def:p-basis-power-subfield
/-- For [an exponent p](hyp:p) and [a field F](hyp:F), [the power subfield used for
p-bases](goal) is the smallest subfield containing every p-th power in F. -/
abbrev pBasisPowSubfield (F : Type*) [Field F] : Subfield F :=
  powSubfield p F -- @realizes C(F^p in the p-basis setting)

-- @node: ass:p-independent-degree
/-- For [a modulus p](hyp:p), [a field F](hyp:F), and [a list s of r field elements](hyp:s),
[the p-independence degree condition](goal) says that adjoining the list to the power
subfield gives an extension of degree p to the power r. -/
def PIndependentDegree (F : Type*) [Field F] {r : ℕ}
    (s : Fin r → F) : Prop := -- @realizes s_j(finite list of field elements)
  Module.finrank ↥(powSubfield p F)
    ↥(IntermediateField.adjoin ↥(powSubfield p F) (Set.range s)) =
      p ^ r -- @realizes s_j(p-independent list) @realizes r(list length)

-- @node: ass:p-basis-generation
/-- For [a modulus p](hyp:p), [a field F](hyp:F), and [a finite list s of field elements](hyp:s),
[the p-basis generation condition](goal) says that adjoining s to the power subfield generates all of F. -/
def PBasisGeneration (F : Type*) [Field F] {r : ℕ} (s : Fin r → F) : Prop :=
  IntermediateField.adjoin ↥(powSubfield p F) (Set.range s) = ⊤ -- @realizes s_j(generates F over C)

-- @node: def:p-independent
/-- For [a modulus p](hyp:p), [a field F](hyp:F), and [a list s of r field elements](hyp:s),
[p-independence](goal) requires [the extension generated by s over the power subfield
to have degree p to the power r](step:1). -/
structure IsPIndependent (F : Type*) [Field F] {r : ℕ} (s : Fin r → F) : Prop where
  degree : PIndependentDegree p F s

-- @node: def:p-basis
/-- For [a modulus p](hyp:p), [a field F](hyp:F), and [a list s of r field elements](hyp:s),
[being a p-basis](goal) requires [the extension generated by s over the power subfield
to have degree p to the power r](step:1) and [s to generate all of F over that subfield](step:2). -/
structure IsPBasis (F : Type*) [Field F] {r : ℕ} (s : Fin r → F) : Prop where
  degree : PIndependentDegree p F s
  generation : PBasisGeneration p F s

-- @node: ass:p-basis-field
/-- For [a modulus p](hyp:p) and [a field F](hyp:F), [the p-basis characteristic condition](goal)
means that F has characteristic p. -/
def PBasisFieldChar (F : Type*) [Field F] : Prop := CharP F p

-- @node: ass:p-basis-adjunction
/-- For [an exponent p](hyp:p), [an intermediate field M between the power subfield and F](hyp:M),
and [an element s of F](hyp:s), [the p-basis adjunction condition](goal) means that s does not belong to M. -/
def PBasisAdjunction (M : IntermediateField ↥(pBasisPowSubfield p F) F) (s : F) : Prop :=
  s ∉ M -- @realizes M(intermediate field over F^p) @realizes s(element outside M)

-- @node: ass:p-basis-finite-degree
/-- For [an exponent p](hyp:p) and [a field F](hyp:F), [the finite-degree condition for p-bases](goal)
means that F is finite dimensional as a vector space over its power subfield. -/
def PBasisFiniteDegree (F : Type*) [Field F] : Prop :=
  FiniteDimensional ↥(pBasisPowSubfield p F) F

end Papers.OaiReconstructionMilnorTheory

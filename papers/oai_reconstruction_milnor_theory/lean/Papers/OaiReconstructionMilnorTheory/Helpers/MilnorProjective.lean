module

public import Papers.OaiReconstructionMilnorTheory.Helpers.InducedMaps
public import Papers.OaiReconstructionMilnorTheory.Helpers.Symbols
public import Papers.OaiReconstructionMilnorTheory.Helpers.ScalarLine
public import Papers.OaiReconstructionMilnorTheory.Helpers.ProjectiveLift

/-! # Identifying Milnor classes with power-subfield projective points -/

@[expose] public section

namespace Papers.OaiReconstructionMilnorTheory

variable (p : ℕ) {K L : Type*} [Field K] [Field L]

-- @node: cls_eq_iff_projective_eq
/-- If [p is prime](hyp:hp), [K has characteristic p](hyp:hK),
[x is nonzero](hyp:hx), and [y is nonzero](hyp:hy), then [x and y have the same first Milnor
class exactly when they represent the same projective point over the subfield
of p-th powers](goal). -/
lemma cls_eq_iff_projective_eq (hp : PrimeChar p) (hK : CharP K p)
    {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    cls p x = cls p y ↔
      Projectivization.mk ↥(powSubfield p K) x hx =
        Projectivization.mk ↥(powSubfield p K) y hy := by
  rw [Projectivization.mk_eq_mk_iff']
  constructor
  · intro h
    exact ⟨⟨x / y, cls_eq_ratio_mem_powSubfield p K hx hy h⟩, div_mul_cancel₀ x hy⟩
  · rintro ⟨a, ha⟩
    change (a : K) * y = x at ha
    have ha0 : (a : K) ≠ 0 := by
      intro h
      exact hx (by simpa [h] using ha.symm)
    rw [← ha]
    change cls p ((a : K) * y) = cls p y
    rw [cls_mul p _ _ ha0 hy, cls_eq_zero_of_mem_powSubfield p hp hK a.property ha0, zero_add]

-- @node: projectiveClass
/-- For [an exponent p](hyp:p) and [a projective point q over the power subfield](hyp:q),
[the Milnor class of q](goal) is the first Milnor class of a chosen nonzero representative. -/
noncomputable def projectiveClass (q : Projectivization ↥(powSubfield p K) K) : MilnorOne K p :=
  cls p q.rep

-- @node: projectiveClass_mk
/-- If [p is prime](hyp:hp), [K has characteristic p](hyp:hK), and
[x is nonzero](hyp:hx), then [the Milnor class assigned to the projective point
represented by x equals the first Milnor class of x](goal). -/
lemma projectiveClass_mk (hp : PrimeChar p) (hK : CharP K p) (x : K) (hx : x ≠ 0) :
    projectiveClass p (Projectivization.mk ↥(powSubfield p K) x hx) = cls p x := by
  apply (cls_eq_iff_projective_eq p hp hK _ _).mpr
  exact Projectivization.mk_rep _

-- @node: projectiveClass_eq_of_mem
/-- If [p is prime](hyp:hp), [K has characteristic p](hyp:hK),
[x is nonzero](hyp:hx), and [x belongs to the one-dimensional subspace represented
by q](hyp:hmem), then [the first Milnor class of x equals the Milnor class assigned to q](goal). -/
lemma projectiveClass_eq_of_mem (hp : PrimeChar p) (hK : CharP K p)
    (q : Projectivization ↥(powSubfield p K) K) {x : K} (hx : x ≠ 0)
    (hmem : x ∈ q.submodule) : cls p x = projectiveClass p q := by
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one
    (Projectivization.finrank_submodule q) hmem hx
  have heq : Projectivization.mk ↥(powSubfield p K) x hx = q :=
    Projectivization.submodule_injective hspan.symm
  rw [← heq, projectiveClass_mk p hp hK]

-- @node: projectiveClass_bijective
/-- If [p is prime](hyp:hp) and [K has characteristic p](hyp:hK), then
[assigning a Milnor class to each projective point over the power subfield is a bijection](goal). -/
lemma projectiveClass_bijective (hp : PrimeChar p) (hK : CharP K p) :
    Function.Bijective
      (projectiveClass p : Projectivization ↥(powSubfield p K) K → MilnorOne K p) := by
  constructor
  · intro x y h
    have heq := (cls_eq_iff_projective_eq p hp hK x.rep_nonzero y.rep_nonzero).mp h
    simpa only [Projectivization.mk_rep] using heq
  · intro x
    obtain ⟨f, hf, rfl⟩ := cls_surjective_nonzero p x
    exact ⟨Projectivization.mk _ f hf, projectiveClass_mk p hp hK f hf⟩

-- @node: projectiveClassEquiv
/-- For [a prime exponent p](hyp:p,hp) with [K of characteristic p](hyp:hK),
[the equivalence between projective points over the power subfield and first
Milnor classes](goal) sends each point to the class of a nonzero representative. -/
noncomputable def projectiveClassEquiv (hp : PrimeChar p) (hK : CharP K p) :
    Projectivization ↥(powSubfield p K) K ≃ MilnorOne K p :=
  Equiv.ofBijective (projectiveClass p) (projectiveClass_bijective p hp hK)

-- @node: projectiveClass_mem_subspace
/-- If [p is prime](hyp:hp) and [K has characteristic p](hyp:hK), then
[the class of q is represented by a nonzero element of W exactly when the
one-dimensional subspace represented by q is contained in W](goal). -/
lemma projectiveClass_mem_subspace (hp : PrimeChar p) (hK : CharP K p)
    (W : Submodule ↥(powSubfield p K) K) (q : Projectivization ↥(powSubfield p K) K) :
    projectiveClass p q ∈ {x | ∃ f ∈ W, f ≠ 0 ∧ cls p f = x} ↔ q.submodule ≤ W := by
  constructor
  · rintro ⟨f, hfW, hf, heq⟩
    have hq : Projectivization.mk ↥(powSubfield p K) f hf = q := by
      have h := (cls_eq_iff_projective_eq p hp hK hf q.rep_nonzero).mp heq
      simpa only [Projectivization.mk_rep] using h
    rw [← hq, Projectivization.submodule_mk]
    apply Submodule.span_le.mpr
    rintro z (rfl : z = f)
    exact hfW
  · intro h
    refine ⟨q.rep, h ?_, q.rep_nonzero, rfl⟩
    rw [Projectivization.submodule_eq]
    exact Submodule.mem_span_singleton_self _

-- @node: milnorProjectiveMap
/-- For [a prime exponent p](hyp:p,hp), [K of characteristic p](hyp:hK),
[L of characteristic p](hyp:hL), and [a bijection Ψ between their first Milnor
classes](hyp:Ψ), [the induced projective equivalence](goal) transports Ψ through
the identifications of Milnor classes with projective points over the power subfields. -/
noncomputable def milnorProjectiveMap (hp : PrimeChar p) (hK : CharP K p) (hL : CharP L p)
    (Ψ : MilnorOne K p ≃ MilnorOne L p) :
    Projectivization ↥(powSubfield p K) K ≃ Projectivization ↥(powSubfield p L) L :=
  ((projectiveClassEquiv p hp hK).trans Ψ).trans (projectiveClassEquiv p hp hL).symm

-- @node: milnorProjectiveMap_class
/-- If [p is prime](hyp:hp), [K has characteristic p](hyp:hK), and
[L has characteristic p](hyp:hL), then [the class of the image of q under the
projective equivalence induced by Ψ equals Ψ applied to the class of q](goal). -/
lemma milnorProjectiveMap_class (hp : PrimeChar p) (hK : CharP K p) (hL : CharP L p)
    (Ψ : MilnorOne K p ≃ MilnorOne L p) (q : Projectivization ↥(powSubfield p K) K) :
    projectiveClass p (milnorProjectiveMap p hp hK hL Ψ q) = Ψ (projectiveClass p q) :=
  (projectiveClassEquiv p hp hL).apply_symm_apply _

-- @node: milnorProjectiveMap_lines
/-- If [p is prime](hyp:hp), [K has characteristic p](hyp:hK),
[L has characteristic p](hyp:hL), and [Ψ sends every projective line of Milnor
classes onto a projective line](hyp:hlines), then [the induced map of projective
points is bijective and sends every projective line onto a projective line](goal). -/
lemma milnorProjectiveMap_lines (hp : PrimeChar p) (hK : CharP K p) (hL : CharP L p)
    (Ψ : MilnorOne K p ≃ MilnorOne L p)
    (hlines : ∀ S, IsProjLine p K S → IsProjLine p L (Ψ '' S)) :
    ProjectiveLiftBijection (milnorProjectiveMap p hp hK hL Ψ) := by
  refine ⟨(milnorProjectiveMap p hp hK hL Ψ).bijective, ?_⟩
  intro W hW
  let S : Set (MilnorOne K p) := {x | ∃ f ∈ W, f ≠ 0 ∧ cls p f = x}
  obtain ⟨W', hW', heq⟩ := hlines S ⟨W, hW, rfl⟩
  refine ⟨W', hW', ?_⟩
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    apply (projectiveClass_mem_subspace p hp hL W' _).mp
    rw [milnorProjectiveMap_class]
    rw [← heq]
    exact ⟨projectiveClass p x, (projectiveClass_mem_subspace p hp hK W x).mpr hx, rfl⟩
  · intro hq
    have hmem := (projectiveClass_mem_subspace p hp hL W' q).mpr hq
    rw [← heq] at hmem
    obtain ⟨x, hx, hxq⟩ := hmem
    let qx := (projectiveClassEquiv p hp hK).symm x
    have hqx : projectiveClass p qx = x := (projectiveClassEquiv p hp hK).apply_symm_apply x
    refine ⟨qx, ?_, ?_⟩
    · apply (projectiveClass_mem_subspace p hp hK W qx).mp
      rwa [hqx]
    · apply (projectiveClass_bijective p hp hL).1
      rw [milnorProjectiveMap_class, hqx]
      exact hxq

end Papers.OaiReconstructionMilnorTheory

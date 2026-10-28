module

public import Papers.OaiReconstructionMilnorTheory.Helpers.FieldGeometry
public import Papers.OaiReconstructionMilnorTheory.Helpers.LineRecoveryPropagation
public import Mathlib.FieldTheory.FinTrdeg

/-! # From uniform affine corrections to containment of every projective line -/

public section

namespace Papers.OaiReconstructionMilnorTheory

variable (p : ℕ) {K L : Type*} [Field K] [Field L]

/-- If [S is a projective line](hyp:hS), then [adding the fixed class v to every
point of S gives a projective line](goal). -/
-- @node: lineRecovery_translate_line
lemma lineRecovery_translate_line (v : MilnorOne K p)
    {S : Set (MilnorOne K p)} (hS : IsProjLine p K S) :
    IsProjLine p K ((fun x => v + x) '' S) := by
  obtain ⟨a, ha, rfl⟩ := cls_surjective_nonzero p v
  obtain ⟨W, hW, rfl⟩ := hS
  let e : K ≃ₗ[↥(powSubfield p K)] K :=
    (LinearEquiv.smulOfNeZero K K a ha).restrictScalars ↥(powSubfield p K)
  refine ⟨W.map e.toLinearMap, (e.finrank_map_eq W).trans hW, ?_⟩
  ext z
  constructor
  · rintro ⟨_, ⟨f, hf, hf0, rfl⟩, rfl⟩
    exact ⟨a * f, ⟨f, hf, rfl⟩, mul_ne_zero ha hf0, cls_mul p a f ha hf0⟩
  · rintro ⟨_, ⟨f, hf, rfl⟩, hzero, rfl⟩
    change a * f ≠ 0 at hzero
    have hf0 : f ≠ 0 := (mul_ne_zero_iff.mp hzero).2
    exact ⟨cls p f, ⟨f, hf, hf0, rfl⟩, (cls_mul p a f ha hf0).symm⟩

/-- Suppose [p is prime](hyp:hp) and [K has characteristic p](hyp:hK). If [S is a
projective line](hyp:hS) and [contains the zero class](hyp:hzero), then [there is
an element x outside the power subfield such that S consists exactly of the
classes of nonzero elements in the span of one and x over that subfield](goal). -/
-- @node: lineRecovery_zero_line_plane
lemma lineRecovery_zero_line_plane (hp : PrimeChar p) (hK : CharP K p)
    {S : Set (MilnorOne K p)} (hS : IsProjLine p K S) (hzero : 0 ∈ S) :
    ∃ x : K, x ∉ powSubfield p K ∧
      S = {z | ∃ f ∈ Submodule.span ↥(powSubfield p K) ({1, x} : Set K),
        f ≠ 0 ∧ cls p f = z} := by
  obtain ⟨W, hW, rfl⟩ := hS
  let C := powSubfield p K
  let : FiniteDimensional C W := Module.finite_of_finrank_eq_succ hW
  obtain ⟨f, hf, hf0, hcls⟩ := hzero
  have h1 : cls p (1 : K) = 0 :=
    cls_eq_zero_of_mem_powSubfield p hp hK C.one_mem one_ne_zero
  have h1W : (1 : K) ∈ W :=
    scalarLine_mem_of_cls_eq p K W one_ne_zero hf0 (h1.trans hcls.symm) hf
  obtain ⟨x, hxW, hxC⟩ : ∃ x ∈ W, x ∉ C := by
    by_contra! h
    have hle : W ≤ Submodule.span C ({1} : Set K) := by
      intro x hx
      exact Submodule.mem_span_singleton.mpr ⟨⟨x, h x hx⟩, mul_one x⟩
    have hdim := Submodule.finrank_mono hle
    rw [hW, finrank_span_singleton (K := C) (one_ne_zero : (1 : K) ≠ 0)] at hdim
    omega
  have hle : Submodule.span C ({1, x} : Set K) ≤ W := Submodule.span_le.mpr (by
    intro z hz
    rcases hz with rfl | hz
    · exact h1W
    · exact (Set.mem_singleton_iff.mp hz) ▸ hxW)
  have heq : Submodule.span C ({1, x} : Set K) = W :=
    Submodule.eq_of_le_of_finrank_eq hle ((scalarLine_plane_finrank p K hxC).trans hW.symm)
  exact ⟨x, hxC, by rw [heq]⟩

/-- If [p is prime](hyp:hp), [n is at least one](hyp:hn), and [n is less than
p](hyp:hnp), then [there is an invertible coefficient modulo p equal to n](goal). -/
-- @node: lineRecovery_exponent_unit
lemma lineRecovery_exponent_unit (hp : PrimeChar p) {n : ℕ} (hn : 1 ≤ n) (hnp : n < p) :
    ∃ r : (Coeff p)ˣ, (r : Coeff p) = n := by
  let : Fact p.Prime := ⟨hp⟩
  have hn0 : (n : Coeff p) ≠ 0 := by
    intro hz
    have := CharP.natCast_injOn_Iio (Coeff p) p hnp hp.pos (by simpa using hz)
    omega
  exact ⟨Units.mk0 (n : Coeff p) hn0, rfl⟩

/-- If [the invertible coefficient r equals n modulo p](hyp:hr) and [R assigns
each source element a nonzero representative of its image class under Θ](hyp:hR),
then [the image of the class of x under Θ multiplied by r is the class of
R(x) to the n-th power](goal). -/
-- @node: lineRecovery_corrected_class
lemma lineRecovery_corrected_class
    (Θ : MilnorOne K p → MilnorOne L p) (r : (Coeff p)ˣ) {n : ℕ}
    (hr : (r : Coeff p) = n) (R : K → L)
    (hR : ∀ x, R x ≠ 0 ∧ Θ (cls p x) = cls p (R x)) (x : K) :
    scalarAct p r Θ (cls p x) = cls p (R x ^ n) := by
  unfold scalarAct
  rw [hr, (hR x).2]
  simpa only [zpow_natCast, natCast_zsmul, Nat.cast_smul_eq_nsmul] using
    (cls_zpow p (R x) (hR x).1 (n : ℤ)).symm

/-- Suppose [p is prime](hyp:hp), [K has characteristic p](hyp:hK), [L has
characteristic p](hyp:hL), [Θ is a compatible Milnor isomorphism](hyp:hΘ), and
[R assigns each source element a nonzero representative of its image
class](hyp:hR). Assume [n is at least one](hyp:hn), [n is less than p](hyp:hnp),
and [the invertible coefficient r equals n modulo p](hyp:hr). If [for every x
outside the source power subfield and every nonzero a in that subfield,
R(x + a) to the n-th power is an affine combination of one and R(x) to the
n-th power over the target power subfield](hyp:haff), [S is a projective
line](hyp:hS), and [S contains zero](hyp:hzero), then [the image of S under Θ
multiplied by r is contained in a target projective line](goal). -/
-- @node: lineRecovery_zero_line_containment
lemma lineRecovery_zero_line_containment (hp : PrimeChar p)
    (hK : CharP K p) (hL : CharP L p)
    (Θ : MilnorOne K p → MilnorOne L p) (hΘ : IsCompatibleIso p Θ)
    (R : K → L) (hR : ∀ x, R x ≠ 0 ∧ Θ (cls p x) = cls p (R x))
    {n : ℕ} (hn : 1 ≤ n) (hnp : n < p) (r : (Coeff p)ˣ) (hr : (r : Coeff p) = n)
    (haff : ∀ x, x ∉ powSubfield p K → ∀ a, a ∈ powSubfield p K → a ≠ 0 →
      AffPow (powSubfield p L) (R x) (R (x + a)) n)
    {S : Set (MilnorOne K p)} (hS : IsProjLine p K S) (hzero : 0 ∈ S) :
    ∃ T, IsProjLine p L T ∧ scalarAct p r Θ '' S ⊆ T := by
  obtain ⟨x, hx, rfl⟩ := lineRecovery_zero_line_plane p hp hK hS hzero
  let C := powSubfield p L
  let P := Submodule.span C ({1, R x ^ n} : Set L)
  let T : Set (MilnorOne L p) := {z | ∃ g ∈ P, g ≠ 0 ∧ cls p g = z}
  have hRx := lineRecovery_image_nonconstant p hp hK hL Θ hΘ hx (hR x).1 (hR x).2
  have hP : Module.finrank C P = 2 :=
    scalarLine_plane_finrank p L (scalarLine_pow_not_mem p L hp hL hRx hn hnp)
  refine ⟨T, ⟨P, hP, rfl⟩, ?_⟩
  rintro _ ⟨_, ⟨f, hf, hf0, rfl⟩, rfl⟩
  obtain ⟨c, d, hcd⟩ := Submodule.mem_span_pair.mp hf
  change (c : K) * 1 + (d : K) * x = f at hcd
  have h1P : (1 : L) ∈ P := Submodule.subset_span (by simp)
  have hxP : R x ^ n ∈ P := Submodule.subset_span (by simp)
  have hx0 : x ≠ 0 := fun hz => hx (hz ▸ (powSubfield p K).zero_mem)
  by_cases hd : (d : K) = 0
  · have hfC : f ∈ powSubfield p K := by
      have hfc : f = (c : K) := by simpa [hd] using hcd.symm
      exact hfc ▸ c.property
    have hcls : cls p f = 0 := cls_eq_zero_of_mem_powSubfield p hp hK hfC hf0
    have hcls1 : cls p (1 : L) = 0 :=
      cls_eq_zero_of_mem_powSubfield p hp hL C.one_mem one_ne_zero
    refine ⟨1, h1P, one_ne_zero, ?_⟩
    rw [hcls1, hcls]
    exact (by change 0 = (r : Coeff p) • (compatibleLinearEquiv p Θ hΘ) 0; simp)
  by_cases hc : (c : K) = 0
  · have hfclass : cls p f = cls p x := by
      have heq : f = (d : K) * x := by simpa [hc] using hcd.symm
      rw [heq, cls_mul p _ _ hd hx0,
        cls_eq_zero_of_mem_powSubfield p hp hK d.property hd, zero_add]
    refine ⟨R x ^ n, hxP, pow_ne_zero _ (hR x).1, ?_⟩
    rw [hfclass, lineRecovery_corrected_class p Θ r hr R hR x]
  · let a : K := (c : K) / (d : K)
    have ha : a ∈ powSubfield p K := (powSubfield p K).div_mem c.property d.property
    have ha0 : a ≠ 0 := div_ne_zero hc hd
    have hxa := lineRecovery_shift_ne_zero p hx ha
    have heq : f = (d : K) * (x + a) := by
      dsimp [a]
      field_simp
      linear_combination hcd.symm
    have hfclass : cls p f = cls p (x + a) := by
      rw [heq, cls_mul p _ _ hd hxa,
        cls_eq_zero_of_mem_powSubfield p hp hK d.property hd, zero_add]
    obtain ⟨A, hA, B, hB, heqpow⟩ := haff x hx a ha ha0
    have hpowP : R (x + a) ^ n ∈ P := by
      rw [heqpow]
      have hAP := P.smul_mem (⟨A, hA⟩ : C) h1P
      have hBP := P.smul_mem (⟨B, hB⟩ : C) hxP
      change A * 1 ∈ P at hAP
      change B * R x ^ n ∈ P at hBP
      exact P.add_mem (by simpa only [mul_one] using hAP) hBP
    refine ⟨R (x + a) ^ n, hpowP, pow_ne_zero _ (hR (x + a)).1, ?_⟩
    rw [hfclass, lineRecovery_corrected_class p Θ r hr R hR (x + a)]

/-- If [Θ is a compatible Milnor isomorphism](hyp:hΘ) and [its multiple by r sends
every source projective line through zero into a target projective line](hyp:hzero),
then [its multiple by r sends every source projective line into a target
projective line](goal). -/
-- @node: lineRecovery_all_line_containment
lemma lineRecovery_all_line_containment
    (Θ : MilnorOne K p → MilnorOne L p) (hΘ : IsCompatibleIso p Θ) (r : (Coeff p)ˣ)
    (hzero : ∀ S, IsProjLine p K S → 0 ∈ S →
      ∃ T, IsProjLine p L T ∧ scalarAct p r Θ '' S ⊆ T) :
    ∀ S, IsProjLine p K S → ∃ T, IsProjLine p L T ∧ scalarAct p r Θ '' S ⊆ T := by
  intro S hS
  obtain ⟨W, hW, hSdef⟩ := hS
  have hS : IsProjLine p K S := ⟨W, hW, hSdef⟩
  have hWne : W ≠ ⊥ := by
    intro hz
    rw [hz, finrank_bot] at hW
    omega
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWne
  have hv : cls p f ∈ S := hSdef ▸ ⟨f, hf, hf0, rfl⟩
  let S₀ := (fun z => -cls p f + z) '' S
  have hS₀ := lineRecovery_translate_line p (-cls p f) hS
  have h0 : 0 ∈ S₀ := ⟨cls p f, hv, neg_add_cancel _⟩
  obtain ⟨T, hT, hmap⟩ := hzero S₀ hS₀ h0
  refine ⟨(fun z => scalarAct p r Θ (cls p f) + z) '' T,
    lineRecovery_translate_line p (scalarAct p r Θ (cls p f)) hT, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  refine ⟨scalarAct p r Θ (-cls p f + z), hmap ⟨_, ⟨z, hz, rfl⟩, rfl⟩, ?_⟩
  let e := compatibleLinearEquiv p Θ hΘ
  change (r : Coeff p) • e (cls p f) + (r : Coeff p) • e (-cls p f + z) =
    (r : Coeff p) • e z
  rw [← smul_add, ← map_add]
  congr 1
  abel_nf

/-- If [p is prime](hyp:hp), [L is geometric over κL](hyp:hL), and [its
transcendence degree over κL is at least two](hyp:hdim), then [the dimension of
L over its power subfield is strictly greater than p](goal). -/
-- @node: lineRecovery_finrank_gt_prime
lemma lineRecovery_finrank_gt_prime
    (κL : Type*) [Field κL] [Algebra κL L]
    (hp : PrimeChar p) (hL : GeometricField p κL L) (hdim : 2 ≤ Algebra.trdeg κL L) :
    p < Module.finrank ↥(powSubfield p L) L := by
  let : Algebra.EssFiniteType κL L := IntermediateField.fg_top_iff.mp hL.2.2
  have hd : 2 ≤ (Algebra.trdeg κL L).toNat := by
    simpa only [Cardinal.toNat_ofNat] using
      Cardinal.toNat_le_toNat hdim (trdeg_lt_aleph0 κL L)
  have hdegree := (finrank_powSubfield_eq_pow_trdeg p κL L hp hL).2
  change Module.finrank ↥(powSubfield p L) L = p ^ (Algebra.trdeg κL L).toNat at hdegree
  rw [hdegree]
  calc
    p < p ^ 2 := by nlinarith [hp.two_le]
    _ ≤ p ^ (Algebra.trdeg κL L).toNat := pow_le_pow_right' hp.one_lt.le hd

/-- Suppose [p is prime](hyp:hp), [K is geometric over κ](hyp:hK), [L is geometric
over κL](hyp:hL), and [L has transcendence degree at least two over κL](hyp:hdim).
If [Θ is a compatible Milnor isomorphism](hyp:hΘ), then [there is an invertible
coefficient modulo p whose multiple of Θ sends every source projective line
into a target projective line](goal). -/
-- @node: lineRecovery_forward_containment
lemma lineRecovery_forward_containment
    (κ : Type*) [Field κ] [Algebra κ K]
    (κL : Type*) [Field κL] [Algebra κL L]
    (hp : PrimeChar p) (hK : GeometricField p κ K) (hL : GeometricField p κL L)
    (hdim : 2 ≤ Algebra.trdeg κL L)
    (Θ : MilnorOne K p → MilnorOne L p) (hΘ : IsCompatibleIso p Θ) :
    ∃ r : (Coeff p)ˣ, ∀ S, IsProjLine p K S →
      ∃ T, IsProjLine p L T ∧ scalarAct p r Θ '' S ⊆ T := by
  have hfinite := geometricField_finiteDimensional_powSubfield p κL L hp hL
  have hdegree := lineRecovery_finrank_gt_prime p κL hp hL hdim
  have himperfect : powSubfield p L ≠ ⊤ :=
    powSubfield_ne_top_of_finrank p (le_trans hp.two_le hdegree.le)
  obtain ⟨R, hR⟩ := lineRecovery_image_representatives p Θ
  obtain ⟨x₀, y₀, hx₀, hy₀, hpair⟩ :=
    lineRecovery_representative_anchors p hp hK.2.1 hL.2.1 hfinite himperfect hdegree Θ hΘ R hR
  obtain ⟨n, hn, hnp, haff⟩ :=
    lineRecovery_global_affine_exponent p κ κL hp hK hL Θ hΘ R hR hx₀ hy₀ hpair
  obtain ⟨r, hr⟩ := lineRecovery_exponent_unit p hp hn hnp
  exact ⟨r, lineRecovery_all_line_containment p Θ hΘ r (fun S hS hzero =>
    lineRecovery_zero_line_containment p hp hK.2.1 hL.2.1 Θ hΘ R hR hn hnp r hr haff hS hzero)⟩

end Papers.OaiReconstructionMilnorTheory

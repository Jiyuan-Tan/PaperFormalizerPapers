module

public import Papers.OaiReconstructionMilnorTheory.Helpers.Intersection
public import Papers.OaiReconstructionMilnorTheory.Helpers.ScalarLine
public import Papers.OaiReconstructionMilnorTheory.Helpers.CompatibleOperations

/-! # The affine configuration for local line correction

The shifted points are outside the prime-field spans of their original classes.
Compatibility transports the four vanishing symbols used by the intersection
configuration.
-/

public section

namespace Papers.OaiReconstructionMilnorTheory

open scoped TensorProduct

variable (p : ℕ) {K L : Type*} [Field K] [Field L]

/-- If [x lies outside the power subfield](hyp:hx) and [a belongs to that
subfield](hyp:ha), then [x + a is nonzero](goal). -/
-- @node: lineRecovery_shift_ne_zero
lemma lineRecovery_shift_ne_zero {x a : K} (hx : x ∉ powSubfield p K)
    (ha : a ∈ powSubfield p K) : x + a ≠ 0 := by
  intro hz
  exact hx ((eq_neg_of_add_eq_zero_left hz) ▸ (powSubfield p K).neg_mem ha)

/-- Suppose [p is prime](hyp:hp) and [K has characteristic p](hyp:hK). If [x lies
outside the power subfield](hyp:hx) and [a belongs to that subfield](hyp:ha) with
[a nonzero](hyp:ha0), then [the class of x + a is outside the prime-field span of
the class of x](goal). -/
-- @node: lineRecovery_shift_not_pin
lemma lineRecovery_shift_not_pin (hp : PrimeChar p) (hK : CharP K p)
    {x a : K} (hx : x ∉ powSubfield p K) (ha : a ∈ powSubfield p K)
    (ha0 : a ≠ 0) : ¬ FpMultiplesPin p x (cls p (x + a)) := by
  let : Fact p.Prime := ⟨hp⟩
  have hx0 : x ≠ 0 := fun hz => hx (hz ▸ (powSubfield p K).zero_mem)
  have hxa := lineRecovery_shift_ne_zero p hx ha
  intro hpin
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hpin
  let n := c.val
  have hn : n < p := ZMod.val_lt c
  have hpow : cls p (x ^ n) = c • cls p x := by
    rw [← ZMod.natCast_zmod_val c]
    simpa only [zpow_natCast, natCast_zsmul, Nat.cast_smul_eq_nsmul] using
      cls_zpow p x hx0 (n : ℤ)
  have hratio := cls_eq_ratio_mem_powSubfield p K hxa (pow_ne_zero n hx0)
    (hc.symm.trans hpow.symm)
  let C := powSubfield p K
  let h : C := ⟨(x + a) / x ^ n, hratio⟩
  let a' : C := ⟨a, ha⟩
  let q : Polynomial C := Polynomial.X + Polynomial.C a' -
    Polynomial.C h * Polynomial.X ^ n
  have hdeg : q.natDegree < p := by
    apply lt_of_le_of_lt (b := max 1 n) ?_ (max_lt hp.one_lt hn)
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le_max
    · exact (Polynomial.natDegree_add_le _ _).trans (by simp)
    · exact Polynomial.natDegree_mul_le.trans (by simp)
  have hq : q ≠ 0 := by
    intro hz
    by_cases hn0 : n = 0
    · have hcoeff := congrArg (fun f : Polynomial C => f.coeff 1) hz
      simp [q, hn0] at hcoeff
    · have hcoeff := congrArg (fun f : Polynomial C => f.coeff 0) hz
      have ha' : a' = 0 := by
        simpa [q, Polynomial.coeff_C_mul, hn0, Ne.symm hn0] using hcoeff
      exact ha0 (congrArg (fun z : C => (z : K)) ha')
  apply powSubfield_aeval_ne_zero p K hp hK hx hq hdeg
  simp only [q, map_sub, map_add, map_mul, map_pow, Polynomial.aeval_X,
    Polynomial.aeval_C]
  change x + a - ((x + a) / x ^ n) * x ^ n = 0
  rw [div_mul_cancel₀ _ (pow_ne_zero n hx0), sub_self]

/-- Suppose [Θ is a compatible Milnor isomorphism](hyp:hΘ), [s and t are
nonzero](hyp:hs,ht), and [S and T are nonzero](hyp:hS,hT). If [Θ sends the class of
s to that of S](hyp:hclsS) and [the class of t to that of T](hyp:hclsT), and
[the Milnor symbol of s and t vanishes](hyp:hzero), then [the Milnor symbol of S
and T vanishes](goal). -/
-- @node: lineRecovery_transport_zero_symbol
lemma lineRecovery_transport_zero_symbol
    (Θ : MilnorOne K p → MilnorOne L p) (hΘ : IsCompatibleIso p Θ)
    {s t : K} {S T : L} (hs : s ≠ 0) (ht : t ≠ 0)
    (hS : S ≠ 0) (hT : T ≠ 0)
    (hclsS : Θ (cls p s) = cls p S) (hclsT : Θ (cls p t) = cls p T)
    (hzero : milnorSymbol p s t hs ht = 0) :
    milnorSymbol p S T hS hT = 0 := by
  let e := compatibleLinearEquiv p Θ hΘ
  have hmem : cls p s ⊗ₜ[Coeff p] cls p t ∈ steinbergRel p K :=
    (Submodule.Quotient.mk_eq_zero _).mp hzero
  have himage : TensorProduct.map e.toLinearMap e.toLinearMap
      (cls p s ⊗ₜ[Coeff p] cls p t) ∈ steinbergRel p L := by
    rw [← compatibleLinearEquiv_relations p Θ hΘ]
    exact Submodule.mem_map_of_mem hmem
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  simpa only [TensorProduct.map_tmul, LinearEquiv.coe_coe, e,
    compatibleLinearEquiv_apply, hclsS, hclsT] using himage

/-- Suppose [p is prime](hyp:hp) and [Θ is a compatible Milnor isomorphism](hyp:hΘ)
that [sends the class of x to that of X](hyp:hX) and [the class of u to that of
U](hyp:hU). If [the class of u is outside the prime-field span of the class of
x](hyp:hoff), then [the class of U is outside the prime-field span of the class
of X](goal). -/
-- @node: lineRecovery_transport_not_pin
lemma lineRecovery_transport_not_pin (hp : PrimeChar p)
    (Θ : MilnorOne K p → MilnorOne L p) (hΘ : IsCompatibleIso p Θ)
    {x u : K} {X U : L} (hX : Θ (cls p x) = cls p X)
    (hU : Θ (cls p u) = cls p U)
    (hoff : ¬ FpMultiplesPin p x (cls p u)) :
    ¬ FpMultiplesPin p X (cls p U) := by
  let : Fact p.Prime := ⟨hp⟩
  intro hpin
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hpin
  apply hoff
  apply Submodule.mem_span_singleton.mpr
  refine ⟨c, hΘ.linear.2.1 ?_⟩
  rw [hΘ.linear.1.map_smul, hX, hU]
  exact hc

/-- If [x is nonzero](hyp:hx) and [y is nonzero](hyp:hy), then [the class of x / y
is the class of x minus the class of y](goal). -/
-- @node: lineRecovery_cls_div
lemma lineRecovery_cls_div {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    cls p (x / y) = cls p x - cls p y := by
  have hinv : cls p y⁻¹ = -cls p y := by
    simpa using cls_zpow p y hy (-1 : ℤ)
  rw [div_eq_mul_inv, cls_mul p x y⁻¹ hx (inv_ne_zero hy), hinv, sub_eq_add_neg]

/-- Suppose [p is prime](hyp:hp), [K is geometric over κ](hyp:hK), [x and y lie
outside the power subfield](hyp:hx,hy), [a and b belong to that subfield](hyp:ha,hb),
[a and b are nonzero](hyp:ha0,hb0), [x and y are nonzero](hyp:hx0,hy0), and
[b x − a y is nonzero](hyp:hz). Then [the four Milnor symbols for the pairs
(x, x + a), (y, y + b), (y / x, (b x − a y) / x), and
((y + b) / (x + a), (b x − a y) / (x + a)) all vanish](goal). -/
-- @node: lineRecovery_configuration_zero_symbols
lemma lineRecovery_configuration_zero_symbols
    (κ : Type*) [Field κ] [Algebra κ K]
    (hp : PrimeChar p) (hK : GeometricField p κ K)
    {x y a b : K} (hx : x ∉ powSubfield p K) (hy : y ∉ powSubfield p K)
    (ha : a ∈ powSubfield p K) (hb : b ∈ powSubfield p K)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hx0 : x ≠ 0) (hy0 : y ≠ 0)
    (hz : b * x - a * y ≠ 0) :
    milnorSymbol p x (x + a) hx0 (lineRecovery_shift_ne_zero p hx ha) = 0 ∧
    milnorSymbol p y (y + b) hy0 (lineRecovery_shift_ne_zero p hy hb) = 0 ∧
    milnorSymbol p (y / x) ((b * x - a * y) / x)
      (div_ne_zero hy0 hx0) (div_ne_zero hz hx0) = 0 ∧
    milnorSymbol p ((y + b) / (x + a)) ((b * x - a * y) / (x + a))
      (div_ne_zero (lineRecovery_shift_ne_zero p hy hb)
        (lineRecovery_shift_ne_zero p hx ha))
      (div_ne_zero hz (lineRecovery_shift_ne_zero p hx ha)) = 0 := by
  have hu := lineRecovery_shift_ne_zero p hx ha
  have hv := lineRecovery_shift_ne_zero p hy hb
  have hneg : -a ∈ powSubfield p K := (powSubfield p K).neg_mem ha
  have hrel : (b * x - a * y) / x = b + -a * (y / x) := by
    field_simp
    ring
  have hrel' : (b * x - a * y) / (x + a) = b + -a * ((y + b) / (x + a)) := by
    field_simp
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hs : a + 1 * x ≠ 0 := by simpa [add_comm] using hu
    simpa only [one_mul, add_comm a x] using
      milnorSymbol_affine_eq_zero p κ a 1 x hp hK
        ⟨⟨ha, ha0⟩, ⟨(powSubfield p K).one_mem, one_ne_zero⟩, hx0, hs⟩
  · have hs : b + 1 * y ≠ 0 := by simpa [add_comm] using hv
    simpa only [one_mul, add_comm b y] using
      milnorSymbol_affine_eq_zero p κ b 1 y hp hK
        ⟨⟨hb, hb0⟩, ⟨(powSubfield p K).one_mem, one_ne_zero⟩, hy0, hs⟩
  · have hs : b + -a * (y / x) ≠ 0 := hrel ▸ div_ne_zero hz hx0
    simpa only [← hrel] using
      milnorSymbol_affine_eq_zero p κ b (-a) (y / x) hp hK
        ⟨⟨hb, hb0⟩, ⟨hneg, neg_ne_zero.mpr ha0⟩, div_ne_zero hy0 hx0, hs⟩
  · have hs : b + -a * ((y + b) / (x + a)) ≠ 0 := hrel' ▸ div_ne_zero hz hu
    simpa only [← hrel'] using
      milnorSymbol_affine_eq_zero p κ b (-a) ((y + b) / (x + a)) hp hK
        ⟨⟨hb, hb0⟩, ⟨hneg, neg_ne_zero.mpr ha0⟩, div_ne_zero hv hu, hs⟩

/-- Suppose [p is prime](hyp:hp), [L has characteristic p](hyp:hL), and [L is
finite dimensional over its power subfield](hyp:hfinite). If [X and Y are
nonzero](hyp:hX,hY) and [form a p-independent pair](hyp:hpair), then [Y / X lies
outside the power subfield](goal). -/
-- @node: lineRecovery_independent_ratio_not_mem
lemma lineRecovery_independent_ratio_not_mem (hp : PrimeChar p) (hL : CharP L p)
    (hfinite : FiniteDimensional ↥(powSubfield p L) L)
    {X Y : L} (hX : X ≠ 0) (hY : Y ≠ 0)
    (hpair : IsPIndependent p L ![X, Y]) : Y / X ∉ powSubfield p L := by
  let : CharP L p := hL
  obtain ⟨DX, DY, hXX, hYY, hXY, hYX⟩ := symbol_pair_derivations p hp hfinite hpair
  intro hmem
  have hzero : DY (Y / X) = 0 := DY.map_algebraMap (⟨Y / X, hmem⟩ : powSubfield p L)
  rw [Derivation.leibniz_div, hYY, hYX, smul_eq_mul, smul_zero, sub_zero] at hzero
  exact (mul_ne_zero (pow_ne_zero 2 (inv_ne_zero hX)) (mul_ne_zero hX hY)) hzero

/-- Suppose [p is prime](hyp:hp), [L has characteristic p](hyp:hL), [L is finite
dimensional over its power subfield](hyp:hfinite), and [X and Y form a
p-independent pair](hyp:hpair). If [U belongs to the field generated by X over
the power subfield](hyp:hUm), [V belongs to the field generated by Y over that
subfield](hyp:hVm), [U and V are nonzero](hyp:hU,hV), and [U lies outside the
power subfield](hyp:hUC), then [V / U lies outside the power subfield](goal). -/
-- @node: lineRecovery_simple_ratio_not_mem
lemma lineRecovery_simple_ratio_not_mem (hp : PrimeChar p) (hL : CharP L p)
    (hfinite : FiniteDimensional ↥(powSubfield p L) L)
    {X Y U V : L} (hpair : IsPIndependent p L ![X, Y])
    (hUm : U ∈ IntermediateField.adjoin ↥(powSubfield p L) {X})
    (hVm : V ∈ IntermediateField.adjoin ↥(powSubfield p L) {Y})
    (hU : U ≠ 0) (hV : V ≠ 0) (hUC : U ∉ powSubfield p L) :
    V / U ∉ powSubfield p L := by
  intro hratio
  let MY := IntermediateField.adjoin ↥(powSubfield p L) {Y}
  have hc : V / U ∈ MY := MY.algebraMap_mem (⟨V / U, hratio⟩ : powSubfield p L)
  have hUY : U ∈ MY := by
    have heq : V / (V / U) = U := by field_simp
    exact heq ▸ MY.div_mem hVm hc
  have hinter : U ∈ IntermediateField.adjoin ↥(powSubfield p L) {X} ⊓ MY := ⟨hUm, hUY⟩
  rw [intersection_independent_simple_inf p hp hL hfinite hpair] at hinter
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hinter
  exact hUC (hc ▸ c.property)

/-- Suppose [p is prime](hyp:hp), [L has characteristic p](hyp:hL), and [L is
finite dimensional over its power subfield](hyp:hfinite). If [X and Y are
nonzero](hyp:hX,hY) and [form a p-independent pair](hyp:hpair), then [both X and Y
lie outside the power subfield](goal). -/
-- @node: lineRecovery_independent_nonconstant
lemma lineRecovery_independent_nonconstant (hp : PrimeChar p) (hL : CharP L p)
    (hfinite : FiniteDimensional ↥(powSubfield p L) L)
    {X Y : L} (hX : X ≠ 0) (hY : Y ≠ 0)
    (hpair : IsPIndependent p L ![X, Y]) :
    X ∉ powSubfield p L ∧ Y ∉ powSubfield p L := by
  let : CharP L p := hL
  obtain ⟨DX, DY, hXX, hYY, _, _⟩ := symbol_pair_derivations p hp hfinite hpair
  constructor
  · intro hmem
    have hz : DX X = 0 := DX.map_algebraMap (⟨X, hmem⟩ : powSubfield p L)
    exact hX (hXX.symm.trans hz)
  · intro hmem
    have hz : DY Y = 0 := DY.map_algebraMap (⟨Y, hmem⟩ : powSubfield p L)
    exact hY (hYY.symm.trans hz)

/-- Suppose [p is prime](hyp:hp) and [L has characteristic p](hyp:hL). If [U is
nonzero](hyp:hU) and [its class lies outside the prime-field span of the class of
X](hyp:hoff), then [U lies outside the power subfield](goal). -/
-- @node: lineRecovery_not_pin_nonconstant
lemma lineRecovery_not_pin_nonconstant (hp : PrimeChar p) (hL : CharP L p)
    {X U : L} (hU : U ≠ 0) (hoff : ¬ FpMultiplesPin p X (cls p U)) :
    U ∉ powSubfield p L := by
  intro hmem
  apply hoff
  rw [cls_eq_zero_of_mem_powSubfield p hp hL hmem hU]
  exact Submodule.zero_mem _

/-- Suppose [Θ is a compatible Milnor isomorphism](hyp:hΘ), [s and t are
nonzero](hyp:hs,ht), and [S and T are nonzero](hyp:hS,hT). If [Θ sends the class of
s to that of S](hyp:hclsS) and [the class of t to that of T](hyp:hclsT), then
[Θ sends the class of s / t to that of S / T](goal). -/
-- @node: lineRecovery_transport_quotient
lemma lineRecovery_transport_quotient
    (Θ : MilnorOne K p → MilnorOne L p) (hΘ : IsCompatibleIso p Θ)
    {s t : K} {S T : L} (hs : s ≠ 0) (ht : t ≠ 0)
    (hS : S ≠ 0) (hT : T ≠ 0)
    (hclsS : Θ (cls p s) = cls p S) (hclsT : Θ (cls p t) = cls p T) :
    Θ (cls p (s / t)) = cls p (S / T) := by
  let e := compatibleLinearEquiv p Θ hΘ
  change e (cls p (s / t)) = _
  rw [lineRecovery_cls_div p hs ht, map_sub, compatibleLinearEquiv_apply,
    compatibleLinearEquiv_apply, hclsS, hclsT, lineRecovery_cls_div p hS hT]

/-- Suppose [p is prime](hyp:hp), [K is geometric over κ](hyp:hK), [L is geometric
over κL](hyp:hL), and [Θ is a compatible Milnor isomorphism](hyp:hΘ). Assume
[x and y lie outside the source power subfield](hyp:hx,hy), [a and b belong to
that subfield](hyp:ha,hb), [a and b are nonzero](hyp:ha0,hb0), [x and y are
nonzero](hyp:hx0,hy0), and [b x − a y is nonzero](hyp:hz). If [X, Y, U, V, and Z
are nonzero](hyp:hX,hY,hU,hV,hZ), [X and Y form a p-independent pair](hyp:hpair),
and Θ sends [the class of x to that of X](hyp:hclsX), [the class of y to that of
Y](hyp:hclsY), [the class of x + a to that of U](hyp:hclsU), [the class of y + b
to that of V](hyp:hclsV), and [the class of b x − a y to that of Z](hyp:hclsZ),
then [there is an integer n between one and p − 1 such that, among exponents in
that range, U to the m-th power is an affine combination of one and X to the
m-th power exactly when m equals n, and the same equivalence holds for V and
Y, with coefficients in the target power subfield](goal). -/
-- @node: lineRecovery_local_affine_correction
lemma lineRecovery_local_affine_correction
    (κ : Type*) [Field κ] [Algebra κ K]
    (κL : Type*) [Field κL] [Algebra κL L]
    (hp : PrimeChar p) (hK : GeometricField p κ K) (hL : GeometricField p κL L)
    (Θ : MilnorOne K p → MilnorOne L p) (hΘ : IsCompatibleIso p Θ)
    {x y a b : K} {X Y U V Z : L}
    (hx : x ∉ powSubfield p K) (hy : y ∉ powSubfield p K)
    (ha : a ∈ powSubfield p K) (hb : b ∈ powSubfield p K)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hx0 : x ≠ 0) (hy0 : y ≠ 0)
    (hz : b * x - a * y ≠ 0)
    (hX : X ≠ 0) (hY : Y ≠ 0) (hU : U ≠ 0) (hV : V ≠ 0) (hZ : Z ≠ 0)
    (hpair : IsPIndependent p L ![X, Y])
    (hclsX : Θ (cls p x) = cls p X) (hclsY : Θ (cls p y) = cls p Y)
    (hclsU : Θ (cls p (x + a)) = cls p U)
    (hclsV : Θ (cls p (y + b)) = cls p V)
    (hclsZ : Θ (cls p (b * x - a * y)) = cls p Z) :
    ∃ n : ℕ, 1 ≤ n ∧ n < p ∧
      (∀ m, 1 ≤ m → m < p → (AffPow (powSubfield p L) X U m ↔ m = n)) ∧
      (∀ m, 1 ≤ m → m < p → (AffPow (powSubfield p L) Y V m ↔ m = n)) := by
  have hu := lineRecovery_shift_ne_zero p hx ha
  have hv := lineRecovery_shift_ne_zero p hy hb
  have hfinite := geometricField_finiteDimensional_powSubfield p κL L hp hL
  obtain ⟨hXC, hYC⟩ := lineRecovery_independent_nonconstant p hp hL.2.1 hfinite hX hY hpair
  obtain ⟨hsX, hsY, hsXY, hsUV⟩ :=
    lineRecovery_configuration_zero_symbols p κ hp hK hx hy ha hb ha0 hb0 hx0 hy0 hz
  have hUm : U ∈ IntermediateField.adjoin ↥(powSubfield p L) {X} :=
    mem_adjoin_of_milnorSymbol_eq_zero p κL X U hp hL ⟨hX, hU⟩
      ⟨hXC, lineRecovery_transport_zero_symbol p Θ hΘ hx0 hu hX hU hclsX hclsU hsX⟩
  have hVm : V ∈ IntermediateField.adjoin ↥(powSubfield p L) {Y} :=
    mem_adjoin_of_milnorSymbol_eq_zero p κL Y V hp hL ⟨hY, hV⟩
      ⟨hYC, lineRecovery_transport_zero_symbol p Θ hΘ hy0 hv hY hV hclsY hclsV hsY⟩
  have hoffU : ¬ FpMultiplesPin p X (cls p U) :=
    lineRecovery_transport_not_pin p hp Θ hΘ hclsX hclsU
      (lineRecovery_shift_not_pin p hp hK.2.1 hx ha ha0)
  have hoffV : ¬ FpMultiplesPin p Y (cls p V) :=
    lineRecovery_transport_not_pin p hp Θ hΘ hclsY hclsV
      (lineRecovery_shift_not_pin p hp hK.2.1 hy hb hb0)
  have hYX := lineRecovery_independent_ratio_not_mem p hp hL.2.1 hfinite hX hY hpair
  have hVU := lineRecovery_simple_ratio_not_mem p hp hL.2.1 hfinite hpair hUm hVm hU hV
    (lineRecovery_not_pin_nonconstant p hp hL.2.1 hU hoffU)
  have hZY : Z / X ∈ IntermediateField.adjoin ↥(powSubfield p L) {Y / X} :=
    mem_adjoin_of_milnorSymbol_eq_zero p κL (Y / X) (Z / X) hp hL
      ⟨div_ne_zero hY hX, div_ne_zero hZ hX⟩ ⟨hYX,
        lineRecovery_transport_zero_symbol p Θ hΘ (div_ne_zero hy0 hx0)
          (div_ne_zero hz hx0) (div_ne_zero hY hX) (div_ne_zero hZ hX)
          (lineRecovery_transport_quotient p Θ hΘ hy0 hx0 hY hX hclsY hclsX)
          (lineRecovery_transport_quotient p Θ hΘ hz hx0 hZ hX hclsZ hclsX) hsXY⟩
  have hZV : Z / U ∈ IntermediateField.adjoin ↥(powSubfield p L) {V / U} :=
    mem_adjoin_of_milnorSymbol_eq_zero p κL (V / U) (Z / U) hp hL
      ⟨div_ne_zero hV hU, div_ne_zero hZ hU⟩ ⟨hVU,
        lineRecovery_transport_zero_symbol p Θ hΘ (div_ne_zero hv hu)
          (div_ne_zero hz hu) (div_ne_zero hV hU) (div_ne_zero hZ hU)
          (lineRecovery_transport_quotient p Θ hΘ hv hu hV hU hclsV hclsU)
          (lineRecovery_transport_quotient p Θ hΘ hz hu hZ hU hclsZ hclsU) hsUV⟩
  have hwitness : IntersectionWitness p X Y U V := by
    refine ⟨Z / X, Z / U, hZY, div_ne_zero hZ hX, hZV, div_ne_zero hZ hU, ?_⟩
    rw [mul_div_cancel₀ _ hX, mul_div_cancel₀ _ hU]
  obtain ⟨n, hn, hnp, hnX, hnY, _, _⟩ :=
    intersection_unique_power p X Y U V hp hL.2.1 hfinite
      ⟨hX, hY, hpair⟩ ⟨⟨hUm, hU⟩, ⟨hVm, hV⟩, hoffU, hoffV⟩ hwitness
  exact ⟨n, hn, hnp, hnX, hnY⟩

/-- Suppose [p is prime](hyp:hp) and [K has characteristic p](hyp:hK). For
[nonzero x](hyp:hx), [its Milnor class is zero if and only if x belongs to the
power subfield](goal). -/
-- @node: lineRecovery_cls_eq_zero_iff
lemma lineRecovery_cls_eq_zero_iff (hp : PrimeChar p) (hK : CharP K p)
    {x : K} (hx : x ≠ 0) : cls p x = 0 ↔ x ∈ powSubfield p K := by
  constructor
  · intro hz
    have h1 : cls p (1 : K) = 0 :=
      cls_eq_zero_of_mem_powSubfield p hp hK (powSubfield p K).one_mem one_ne_zero
    simpa only [div_one] using cls_eq_ratio_mem_powSubfield p K hx one_ne_zero (hz.trans h1.symm)
  · exact fun hmem => cls_eq_zero_of_mem_powSubfield p hp hK hmem hx

/-- Suppose [p is prime](hyp:hp), [K has characteristic p](hyp:hK), [L has
characteristic p](hyp:hL), and [Θ is a compatible Milnor isomorphism](hyp:hΘ).
If [x is nonzero](hyp:hx), [X is nonzero](hyp:hX), [Θ sends the class of x to that
of X](hyp:hclsX), and [X lies outside the target power subfield](hyp:hXC), then
[x lies outside the source power subfield](goal). -/
-- @node: lineRecovery_source_nonconstant
lemma lineRecovery_source_nonconstant (hp : PrimeChar p)
    (hK : CharP K p) (hL : CharP L p)
    (Θ : MilnorOne K p → MilnorOne L p) (hΘ : IsCompatibleIso p Θ)
    {x : K} {X : L} (hx : x ≠ 0) (hX : X ≠ 0)
    (hclsX : Θ (cls p x) = cls p X) (hXC : X ∉ powSubfield p L) :
    x ∉ powSubfield p K := by
  intro hmem
  have hz := (lineRecovery_cls_eq_zero_iff p hp hK hx).mpr hmem
  have hzX : cls p X = 0 := by
    rw [← hclsX, hz]
    exact (compatibleLinearEquiv p Θ hΘ).map_zero
  exact hXC ((lineRecovery_cls_eq_zero_iff p hp hL hX).mp hzX)

/-- Suppose [p is prime](hyp:hp), [K has characteristic p](hyp:hK), [L has
characteristic p](hyp:hL), [L is finite dimensional over its power
subfield](hyp:hfinite), and [Θ is a compatible Milnor isomorphism](hyp:hΘ).
If [x and y are nonzero](hyp:hx,hy), [a and b belong to the source power
subfield](hyp:ha,hb), [a is nonzero](hyp:ha0), [X and Y are nonzero](hyp:hX,hY),
[X and Y form a p-independent pair](hyp:hpair), and Θ sends [the class of x to
that of X](hyp:hclsX) and [the class of y to that of Y](hyp:hclsY), then
[b x − a y is nonzero](goal). -/
-- @node: lineRecovery_edge_configuration_ne_zero
lemma lineRecovery_edge_configuration_ne_zero (hp : PrimeChar p)
    (hK : CharP K p) (hL : CharP L p)
    (hfinite : FiniteDimensional ↥(powSubfield p L) L)
    (Θ : MilnorOne K p → MilnorOne L p) (hΘ : IsCompatibleIso p Θ)
    {x y a b : K} {X Y : L} (hx : x ≠ 0) (hy : y ≠ 0)
    (ha : a ∈ powSubfield p K) (hb : b ∈ powSubfield p K) (ha0 : a ≠ 0)
    (hX : X ≠ 0) (hY : Y ≠ 0) (hpair : IsPIndependent p L ![X, Y])
    (hclsX : Θ (cls p x) = cls p X) (hclsY : Θ (cls p y) = cls p Y) :
    b * x - a * y ≠ 0 := by
  intro hz
  have hrel : y / x = b / a := by
    apply (div_eq_div_iff hx ha0).mpr
    linear_combination -hz
  have hratio : y / x ∈ powSubfield p K := hrel ▸ (powSubfield p K).div_mem hb ha
  have heq : cls p y = cls p x := by
    apply sub_eq_zero.mp
    rw [← lineRecovery_cls_div p hy hx]
    exact cls_eq_zero_of_mem_powSubfield p hp hK hratio (div_ne_zero hy hx)
  have heqXY : cls p Y = cls p X := by rw [← hclsY, ← hclsX, heq]
  exact lineRecovery_independent_ratio_not_mem p hp hL hfinite hX hY hpair
    (cls_eq_ratio_mem_powSubfield p L hY hX heqXY)

/-- Suppose [p is prime](hyp:hp), [K is geometric over κ](hyp:hK), [L is geometric
over κL](hyp:hL), and [Θ is a compatible Milnor isomorphism](hyp:hΘ). Assume
[a and b belong to the source power subfield](hyp:ha,hb), [a and b are
nonzero](hyp:ha0,hb0), and [x and y are nonzero](hyp:hx,hy). If [X, Y, U, V, and Z
are nonzero](hyp:hX,hY,hU,hV,hZ), [X and Y form a p-independent pair](hyp:hpair),
and Θ sends [the class of x to that of X](hyp:hclsX), [the class of y to that of
Y](hyp:hclsY), [the class of x + a to that of U](hyp:hclsU), [the class of y + b
to that of V](hyp:hclsV), and [the class of b x − a y to that of Z](hyp:hclsZ),
then [there is an integer n between one and p − 1 such that, among exponents in
that range, U to the m-th power is an affine combination of one and X to the
m-th power exactly when m equals n, and the same equivalence holds for V and
Y, with coefficients in the target power subfield](goal). -/
-- @node: lineRecovery_edge_affine_correction
lemma lineRecovery_edge_affine_correction
    (κ : Type*) [Field κ] [Algebra κ K]
    (κL : Type*) [Field κL] [Algebra κL L]
    (hp : PrimeChar p) (hK : GeometricField p κ K) (hL : GeometricField p κL L)
    (Θ : MilnorOne K p → MilnorOne L p) (hΘ : IsCompatibleIso p Θ)
    {x y a b : K} {X Y U V Z : L}
    (ha : a ∈ powSubfield p K) (hb : b ∈ powSubfield p K)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0)
    (hX : X ≠ 0) (hY : Y ≠ 0) (hU : U ≠ 0) (hV : V ≠ 0) (hZ : Z ≠ 0)
    (hpair : IsPIndependent p L ![X, Y])
    (hclsX : Θ (cls p x) = cls p X) (hclsY : Θ (cls p y) = cls p Y)
    (hclsU : Θ (cls p (x + a)) = cls p U)
    (hclsV : Θ (cls p (y + b)) = cls p V)
    (hclsZ : Θ (cls p (b * x - a * y)) = cls p Z) :
    ∃ n : ℕ, 1 ≤ n ∧ n < p ∧
      (∀ m, 1 ≤ m → m < p → (AffPow (powSubfield p L) X U m ↔ m = n)) ∧
      (∀ m, 1 ≤ m → m < p → (AffPow (powSubfield p L) Y V m ↔ m = n)) := by
  have hfinite := geometricField_finiteDimensional_powSubfield p κL L hp hL
  obtain ⟨hXC, hYC⟩ := lineRecovery_independent_nonconstant p hp hL.2.1 hfinite hX hY hpair
  exact lineRecovery_local_affine_correction p κ κL hp hK hL Θ hΘ
    (lineRecovery_source_nonconstant p hp hK.2.1 hL.2.1 Θ hΘ hx hX hclsX hXC)
    (lineRecovery_source_nonconstant p hp hK.2.1 hL.2.1 Θ hΘ hy hY hclsY hYC)
    ha hb ha0 hb0 hx hy
    (lineRecovery_edge_configuration_ne_zero p hp hK.2.1 hL.2.1 hfinite Θ hΘ
      hx hy ha hb ha0 hX hY hpair hclsX hclsY)
    hX hY hU hV hZ hpair hclsX hclsY hclsU hclsV hclsZ

end Papers.OaiReconstructionMilnorTheory

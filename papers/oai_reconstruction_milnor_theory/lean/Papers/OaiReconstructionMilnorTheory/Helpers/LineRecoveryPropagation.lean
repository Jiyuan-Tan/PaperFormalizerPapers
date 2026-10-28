module

public import Papers.OaiReconstructionMilnorTheory.Helpers.InducedMaps
public import Papers.OaiReconstructionMilnorTheory.Helpers.LineRecoveryAffine

/-! # Propagation of the local affine exponent

Fix representatives of image classes. Two independent anchor vertices suffice:
every nonconstant image lies outside at least one of their simple fields, since
the intersection of those fields consists of constants. Uniqueness at the fixed
shift of that anchor propagates its exponent to every vertex and every shift.
-/

public section

namespace Papers.OaiReconstructionMilnorTheory

variable (p : ℕ) {K L : Type*} [Field K] [Field L]

/-- For any map Θ between the Milnor class spaces, [there is a function R
assigning each source element a nonzero target element whose class equals the
image of its source class](goal). -/
-- @node: lineRecovery_image_representatives
lemma lineRecovery_image_representatives (Θ : MilnorOne K p → MilnorOne L p) :
    ∃ R : K → L, ∀ x, R x ≠ 0 ∧ Θ (cls p x) = cls p (R x) := by
  classical
  have hex (x : K) : ∃ X : L, X ≠ 0 ∧ Θ (cls p x) = cls p X := by
    obtain ⟨X, hX, heq⟩ := cls_surjective_nonzero p (Θ (cls p x))
    exact ⟨X, hX, heq.symm⟩
  choose R hR using hex
  exact ⟨R, hR⟩

/-- Suppose [p is prime](hyp:hp), [K has characteristic p](hyp:hK), [L has
characteristic p](hyp:hL), and [Θ is a compatible Milnor isomorphism](hyp:hΘ).
If [x lies outside the source power subfield](hyp:hx), [X is nonzero](hyp:hX),
and [Θ sends the class of x to that of X](hyp:hcls), then [X lies outside the
target power subfield](goal). -/
-- @node: lineRecovery_image_nonconstant
lemma lineRecovery_image_nonconstant (hp : PrimeChar p)
    (hK : CharP K p) (hL : CharP L p)
    (Θ : MilnorOne K p → MilnorOne L p) (hΘ : IsCompatibleIso p Θ)
    {x : K} {X : L} (hx : x ∉ powSubfield p K) (hX : X ≠ 0)
    (hcls : Θ (cls p x) = cls p X) : X ∉ powSubfield p L := by
  intro hmem
  have hzX := (lineRecovery_cls_eq_zero_iff p hp hL hX).mpr hmem
  let e := compatibleLinearEquiv p Θ hΘ
  have hz : cls p x = 0 := e.injective (by
    change Θ (cls p x) = e 0
    rw [hcls, hzX, map_zero])
  have hx0 : x ≠ 0 := fun hz => hx (hz ▸ (powSubfield p K).zero_mem)
  exact hx ((lineRecovery_cls_eq_zero_iff p hp hK hx0).mp hz)

/-- Suppose [p is prime](hyp:hp), [K is geometric over κ](hyp:hK), [L is geometric
over κL](hyp:hL), [Θ is a compatible Milnor isomorphism](hyp:hΘ), and [R assigns
each source element a nonzero representative of its image class](hyp:hR). If
[x and y are nonzero](hyp:hx,hy), [a and b belong to the source power
subfield](hyp:ha,hb), [a and b are nonzero](hyp:ha0,hb0), and [R(x) and R(y) form
a p-independent pair](hyp:hpair), then [there is an integer n between one and
p − 1 such that, among exponents in that range, R(x + a) to the m-th power is
an affine combination of one and R(x) to the m-th power exactly when m equals
n, and the same equivalence holds for R(y + b) and R(y), with coefficients in
the target power subfield](goal). -/
-- @node: lineRecovery_representative_local_correction
lemma lineRecovery_representative_local_correction
    (κ : Type*) [Field κ] [Algebra κ K]
    (κL : Type*) [Field κL] [Algebra κL L]
    (hp : PrimeChar p) (hK : GeometricField p κ K) (hL : GeometricField p κL L)
    (Θ : MilnorOne K p → MilnorOne L p) (hΘ : IsCompatibleIso p Θ)
    (R : K → L) (hR : ∀ x, R x ≠ 0 ∧ Θ (cls p x) = cls p (R x))
    {x y a b : K} (hx : x ≠ 0) (hy : y ≠ 0)
    (ha : a ∈ powSubfield p K) (hb : b ∈ powSubfield p K)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hpair : IsPIndependent p L ![R x, R y]) :
    ∃ n : ℕ, 1 ≤ n ∧ n < p ∧
      (∀ m, 1 ≤ m → m < p →
        (AffPow (powSubfield p L) (R x) (R (x + a)) m ↔ m = n)) ∧
      (∀ m, 1 ≤ m → m < p →
        (AffPow (powSubfield p L) (R y) (R (y + b)) m ↔ m = n)) := by
  exact lineRecovery_edge_affine_correction p κ κL hp hK hL Θ hΘ
    ha hb ha0 hb0 hx hy (hR x).1 (hR y).1 (hR (x + a)).1
    (hR (y + b)).1 (hR (b * x - a * y)).1 hpair
    (hR x).2 (hR y).2 (hR (x + a)).2 (hR (y + b)).2 (hR (b * x - a * y)).2

/-- Suppose [p is prime](hyp:hp), [K is geometric over κ](hyp:hK), [L is geometric
over κL](hyp:hL), [Θ is a compatible Milnor isomorphism](hyp:hΘ), and [R assigns
each source element a nonzero representative of its image class](hyp:hR). If
[x₀ and y₀ are nonzero](hyp:hx₀,hy₀) and [R(x₀) and R(y₀) form a p-independent
pair](hyp:hpair), then [there is one integer n between one and p − 1 such that
for every x outside the source power subfield and every nonzero a in that
subfield, R(x + a) to the n-th power is an affine combination of one and R(x)
to the n-th power over the target power subfield](goal). -/
-- @node: lineRecovery_global_affine_exponent
lemma lineRecovery_global_affine_exponent
    (κ : Type*) [Field κ] [Algebra κ K]
    (κL : Type*) [Field κL] [Algebra κL L]
    (hp : PrimeChar p) (hK : GeometricField p κ K) (hL : GeometricField p κL L)
    (Θ : MilnorOne K p → MilnorOne L p) (hΘ : IsCompatibleIso p Θ)
    (R : K → L) (hR : ∀ x, R x ≠ 0 ∧ Θ (cls p x) = cls p (R x))
    {x₀ y₀ : K} (hx₀ : x₀ ≠ 0) (hy₀ : y₀ ≠ 0)
    (hpair : IsPIndependent p L ![R x₀, R y₀]) :
    ∃ n : ℕ, 1 ≤ n ∧ n < p ∧
      ∀ x, x ∉ powSubfield p K → ∀ a, a ∈ powSubfield p K → a ≠ 0 →
        AffPow (powSubfield p L) (R x) (R (x + a)) n := by
  let : CharP L p := hL.2.1
  have hfinite := geometricField_finiteDimensional_powSubfield p κL L hp hL
  obtain ⟨hXC, hYC⟩ := lineRecovery_independent_nonconstant p hp hL.2.1 hfinite
    (hR x₀).1 (hR y₀).1 hpair
  obtain ⟨n, hn, hnp, hnX, hnY⟩ :=
    lineRecovery_representative_local_correction p κ κL hp hK hL Θ hΘ R hR hx₀ hy₀
      (powSubfield p K).one_mem (powSubfield p K).one_mem one_ne_zero one_ne_zero hpair
  refine ⟨n, hn, hnp, ?_⟩
  intro x hx a ha ha0
  have hx0 : x ≠ 0 := fun hz => hx (hz ▸ (powSubfield p K).zero_mem)
  have hRxC : R x ∉ powSubfield p L :=
    lineRecovery_image_nonconstant p hp hK.2.1 hL.2.1 Θ hΘ hx (hR x).1 (hR x).2
  have hstep (z : K) (hz : z ≠ 0) (hZC : R z ∉ powSubfield p L)
      (hanchor : ∀ m, 1 ≤ m → m < p →
        (AffPow (powSubfield p L) (R z) (R (z + 1)) m ↔ m = n))
      (hoff : R x ∉ IntermediateField.adjoin ↥(powSubfield p L) {R z}) :
      AffPow (powSubfield p L) (R x) (R (x + a)) n := by
    have hpZX := symbol_pair_independent p hp hZC hoff
    obtain ⟨r, hr, hrp, hrZ, hrX⟩ :=
      lineRecovery_representative_local_correction p κ κL hp hK hL Θ hΘ R hR hz hx0
        (powSubfield p K).one_mem ha one_ne_zero ha0 hpZX
    have hrn : r = n := (hanchor r hr hrp).mp ((hrZ r hr hrp).mpr rfl)
    exact hrn ▸ (hrX r hr hrp).mpr rfl
  by_cases hmem : R x ∈ IntermediateField.adjoin ↥(powSubfield p L) {R x₀}
  · apply hstep y₀ hy₀ hYC hnY
    intro hmemY
    have hinter : R x ∈ IntermediateField.adjoin ↥(powSubfield p L) {R x₀} ⊓
        IntermediateField.adjoin ↥(powSubfield p L) {R y₀} := ⟨hmem, hmemY⟩
    rw [intersection_independent_simple_inf p hp hL.2.1 hfinite hpair] at hinter
    obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hinter
    exact hRxC (hc ▸ c.property)
  · exact hstep x₀ hx₀ hXC hnX hmem

/-- If [p is prime](hyp:hp), [L has characteristic p](hyp:hL), and [X lies outside
the power subfield](hyp:hX), then [the field generated by X over the power
subfield has dimension p over that subfield](goal). -/
-- @node: lineRecovery_simple_finrank
lemma lineRecovery_simple_finrank (hp : PrimeChar p) (hL : CharP L p)
    {X : L} (hX : X ∉ powSubfield p L) :
    Module.finrank ↥(powSubfield p L)
      ↥(IntermediateField.adjoin ↥(powSubfield p L) {X}) = p := by
  have hempty : IsPIndependent p L (Fin.elim0 : Fin 0 → L) := by
    constructor
    simp [PIndependentDegree]
  have hX' : X ∉ IntermediateField.adjoin ↥(powSubfield p L)
      (Set.range (Fin.elim0 : Fin 0 → L)) := by
    rw [Set.range_eq_empty, IntermediateField.adjoin_empty, IntermediateField.mem_bot]
    rintro ⟨c, rfl⟩
    exact hX c.property
  have hsingle := pIndependent_snoc p hp hL (Fin.elim0 : Fin 0 → L) hempty X hX'
  have hrange : Set.range (Fin.snoc (Fin.elim0 : Fin 0 → L) X) = {X} := by
    rw [Fin.range_snoc, Set.range_eq_empty]
    simp
  have hd := hsingle.degree
  change Module.finrank ↥(powSubfield p L)
    ↥(IntermediateField.adjoin ↥(powSubfield p L)
      (Set.range (Fin.snoc (Fin.elim0 : Fin 0 → L) X))) = p ^ 1 at hd
  rw [hrange, pow_one] at hd
  exact hd

/-- Suppose [p is prime](hyp:hp), [L has characteristic p](hyp:hL), [its power
subfield is proper](hyp:himperfect), and [its dimension over that subfield is
greater than p](hyp:hdegree). Then [L contains two nonzero elements forming a
p-independent pair](goal). -/
-- @node: lineRecovery_independent_pair_exists
lemma lineRecovery_independent_pair_exists (hp : PrimeChar p) (hL : CharP L p)
    (himperfect : powSubfield p L ≠ ⊤)
    (hdegree : p < Module.finrank ↥(powSubfield p L) L) :
    ∃ X Y : L, X ≠ 0 ∧ Y ≠ 0 ∧ IsPIndependent p L ![X, Y] := by
  let : CharP L p := hL
  obtain ⟨X, hX⟩ : ∃ X : L, X ∉ powSubfield p L := by
    by_contra! h
    exact himperfect (top_unique (fun X _ => h X))
  have hproper : IntermediateField.adjoin ↥(powSubfield p L) {X} ≠ ⊤ := by
    intro heq
    have hd := lineRecovery_simple_finrank p hp hL hX
    rw [heq, IntermediateField.finrank_top'] at hd
    exact (ne_of_gt hdegree) hd
  obtain ⟨Y, hY⟩ : ∃ Y : L, Y ∉ IntermediateField.adjoin ↥(powSubfield p L) {X} := by
    by_contra! h
    exact hproper (top_unique (fun Y _ => h Y))
  exact ⟨X, Y, (fun hz => hX (hz ▸ (powSubfield p L).zero_mem)),
    (fun hz => hY (hz ▸ (IntermediateField.adjoin ↥(powSubfield p L) {X}).zero_mem)),
    symbol_pair_independent p hp hX hY⟩

/-- If [X is nonzero](hyp:hX), [Y is nonzero](hyp:hY), and [their Milnor classes
are equal](hyp:heq), then [X and Y generate the same intermediate field over the
power subfield](goal). -/
-- @node: lineRecovery_adjoin_eq_of_cls_eq
lemma lineRecovery_adjoin_eq_of_cls_eq {X Y : L} (hX : X ≠ 0) (hY : Y ≠ 0)
    (heq : cls p X = cls p Y) :
    IntermediateField.adjoin ↥(powSubfield p L) {X} =
      IntermediateField.adjoin ↥(powSubfield p L) {Y} := by
  have hmem {S T : L} (hS : S ≠ 0) (hT : T ≠ 0) (h : cls p S = cls p T) :
      S ∈ IntermediateField.adjoin ↥(powSubfield p L) {T} := by
    let M := IntermediateField.adjoin ↥(powSubfield p L) {T}
    have hc : S / T ∈ M := M.algebraMap_mem
      (⟨S / T, cls_eq_ratio_mem_powSubfield p L hS hT h⟩ : powSubfield p L)
    have hTmem : T ∈ M := IntermediateField.subset_adjoin _ _ (Set.mem_singleton T)
    exact (div_mul_cancel₀ S hT) ▸ M.mul_mem hc hTmem
  apply le_antisymm
  · exact IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr (hmem hX hY heq))
  · exact IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr (hmem hY hX heq.symm))

/-- Suppose [p is prime](hyp:hp), [K has characteristic p](hyp:hK), [L has
characteristic p](hyp:hL), [L is finite dimensional over its power
subfield](hyp:hfinite), [that subfield is proper](hyp:himperfect), and [the
dimension is greater than p](hyp:hdegree). If [Θ is a compatible Milnor
isomorphism](hyp:hΘ) and [R assigns each source element a nonzero representative
of its image class](hyp:hR), then [there are nonzero source elements x and y
such that R(x) and R(y) form a p-independent pair](goal). -/
-- @node: lineRecovery_representative_anchors
lemma lineRecovery_representative_anchors (hp : PrimeChar p)
    (hK : CharP K p) (hL : CharP L p)
    (hfinite : FiniteDimensional ↥(powSubfield p L) L)
    (himperfect : powSubfield p L ≠ ⊤)
    (hdegree : p < Module.finrank ↥(powSubfield p L) L)
    (Θ : MilnorOne K p → MilnorOne L p) (hΘ : IsCompatibleIso p Θ)
    (R : K → L) (hR : ∀ x, R x ≠ 0 ∧ Θ (cls p x) = cls p (R x)) :
    ∃ x y : K, x ≠ 0 ∧ y ≠ 0 ∧ IsPIndependent p L ![R x, R y] := by
  let : CharP L p := hL
  obtain ⟨X, Y, hX, hY, hpair⟩ :=
    lineRecovery_independent_pair_exists p hp hL himperfect hdegree
  obtain ⟨hXC, hYC⟩ := lineRecovery_independent_nonconstant p hp hL hfinite hX hY hpair
  obtain ⟨v, hv⟩ := hΘ.linear.2.2 (cls p X)
  obtain ⟨w, hw⟩ := hΘ.linear.2.2 (cls p Y)
  obtain ⟨x, hx, hcx⟩ := cls_surjective_nonzero p v
  obtain ⟨y, hy, hcy⟩ := cls_surjective_nonzero p w
  have heqX : cls p (R x) = cls p X := by rw [← (hR x).2, hcx, hv]
  have heqY : cls p (R y) = cls p Y := by rw [← (hR y).2, hcy, hw]
  have hRx : R x ∉ powSubfield p L := by
    intro hmem
    apply hXC
    apply (lineRecovery_cls_eq_zero_iff p hp hL hX).mp
    rw [← heqX]
    exact cls_eq_zero_of_mem_powSubfield p hp hL hmem (hR x).1
  have hYnot : Y ∉ IntermediateField.adjoin ↥(powSubfield p L) {X} := by
    obtain ⟨DX, DY, _, hYY, _, hYX⟩ := symbol_pair_derivations p hp hfinite hpair
    intro hmem
    exact hY (hYY.symm.trans (intersection_derivation_zero_on_adjoin p DY hYX hmem))
  have hRy : R y ∉ IntermediateField.adjoin ↥(powSubfield p L) {R x} := by
    intro hmem
    rw [lineRecovery_adjoin_eq_of_cls_eq p (hR x).1 hX heqX] at hmem
    have hle : IntermediateField.adjoin ↥(powSubfield p L) {R y} ≤
        IntermediateField.adjoin ↥(powSubfield p L) {X} :=
      IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hmem)
    rw [lineRecovery_adjoin_eq_of_cls_eq p (hR y).1 hY heqY] at hle
    exact hYnot (hle (IntermediateField.subset_adjoin _ _ (Set.mem_singleton Y)))
  exact ⟨x, y, hx, hy, symbol_pair_independent p hp hRx hRy⟩

end Papers.OaiReconstructionMilnorTheory

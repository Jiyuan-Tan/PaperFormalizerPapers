module

public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Papers.OaiNearInclusionsVon.Helpers.NearConstruction

/-! Absolute summability and the moment bound for the near-inclusion constant. -/

public section

namespace Papers.OaiNearInclusionsVon

/-- If [the operator U has norm at most one](hyp:hU), then [the norm of the
commutator of its n-th power with X is at most n times the norm of the
commutator of U with X](goal). -/
-- @node: near_nat_power_commutator_le
lemma near_nat_power_commutator_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [Nontrivial E]
    (U X : E →L[ℂ] E) (hU : ‖U‖ ≤ 1) (n : ℕ) :
    ‖U ^ n * X - X * U ^ n‖ ≤ (n : ℝ) * ‖U * X - X * U‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp : ‖U ^ n‖ ≤ 1 := (norm_pow_le _ _).trans
      (pow_le_one₀ (norm_nonneg _) hU)
    calc
      ‖U ^ (n + 1) * X - X * U ^ (n + 1)‖ =
          ‖U ^ n * (U * X - X * U) + (U ^ n * X - X * U ^ n) * U‖ := by
        congr 1
        rw [pow_succ]
        noncomm_ring
      _ ≤ ‖U ^ n * (U * X - X * U)‖ + ‖(U ^ n * X - X * U ^ n) * U‖ :=
        norm_add_le _ _
      _ ≤ 1 * ‖U * X - X * U‖ + ((n : ℝ) * ‖U * X - X * U‖) * 1 := by
        exact add_le_add
          ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hp (norm_nonneg _)))
          ((norm_mul_le _ _).trans (mul_le_mul ih hU (norm_nonneg _) (by positivity)))
      _ = ((n + 1 : ℕ) : ℝ) * ‖U * X - X * U‖ := by push_cast; ring

/-- If [U is unitary](hyp:hU), then [the commutator of its adjoint with X has
the same norm as the commutator of U with X](goal). -/
-- @node: near_star_commutator_norm
lemma near_star_commutator_norm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (U X : E →L[ℂ] E) (hU : U ∈ unitary _) :
    ‖star U * X - X * star U‖ = ‖U * X - X * U‖ := by
  have hid : star U * X - X * star U =
      -(star U * (U * X - X * U) * star U) := by
    rw [mul_sub, sub_mul]
    simp only [← mul_assoc, Unitary.star_mul_self_of_mem hU, one_mul]
    simp only [mul_assoc, Unitary.mul_star_self_of_mem hU, mul_one]
    abel
  rw [hid, norm_neg, CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem hU),
    CStarRing.norm_mem_unitary_mul _ (Unitary.star_mem hU)]

/-- If [U is unitary](hyp:hU), then [the norm of the commutator of its
integer power with exponent a and X is at most the absolute value of a times
the norm of the commutator of U with X](goal). -/
-- @node: near_int_power_commutator_le
lemma near_int_power_commutator_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (U X : E →L[ℂ] E) (hU : U ∈ unitary _) (a : ℤ) :
    ‖unitaryIntPow U a * X - X * unitaryIntPow U a‖ ≤
      (a.natAbs : ℝ) * ‖U * X - X * U‖ := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · have hz : U * X - X * U = 0 := Subsingleton.elim _ _
    have hz' : unitaryIntPow U a * X - X * unitaryIntPow U a = 0 :=
      Subsingleton.elim _ _
    simp [hz, hz']
  · have hnorm : ‖U‖ ≤ 1 := (CStarRing.norm_of_mem_unitary hU).le
    unfold unitaryIntPow
    split_ifs with ha
    · have habs : a.toNat = a.natAbs := by
        cases a <;> simp_all
      simpa only [habs] using near_nat_power_commutator_le U X hnorm a.toNat
    · simpa only [near_star_commutator_norm U X hU] using
        near_nat_power_commutator_le (star U) X
          (CStarRing.norm_of_mem_unitary (Unitary.star_mem hU)).le a.natAbs

/-- If [U is unitary](hyp:hU) and [V is unitary](hyp:hV), then [the
commutator of their integer powers with exponents a and b has norm at most
the product of the absolute values of a and b times the norm of the
commutator of U and V](goal). -/
-- @node: near_power_commutator_le
lemma near_power_commutator_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (U V : E →L[ℂ] E) (hU : U ∈ unitary _) (hV : V ∈ unitary _) (a b : ℤ) :
    ‖unitaryIntPow U a * unitaryIntPow V b - unitaryIntPow V b * unitaryIntPow U a‖ ≤
      (a.natAbs : ℝ) * (b.natAbs : ℝ) * ‖U * V - V * U‖ := by
  have hb : ‖U * unitaryIntPow V b - unitaryIntPow V b * U‖ ≤
      (b.natAbs : ℝ) * ‖U * V - V * U‖ := by
    simpa only [norm_sub_rev] using near_int_power_commutator_le V U hV b
  exact (near_int_power_commutator_le U (unitaryIntPow V b) hU a).trans
    (by simpa only [mul_assoc] using (mul_le_mul_of_nonneg_left hb
      (Nat.cast_nonneg a.natAbs)))

/-- If [U is unitary](hyp:hU), then [its integer power defined using
adjoints for negative exponents equals its integer power in the group of
unitary operators](goal). -/
-- @node: near_unitaryIntPow_eq_zpow
lemma near_unitaryIntPow_eq_zpow
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (U : E →L[ℂ] E) (hU : U ∈ unitary _) (a : ℤ) :
    unitaryIntPow U a = ((⟨U, hU⟩ : unitary (E →L[ℂ] E)) ^ a : unitary _) := by
  cases a with
  | ofNat n => simp [unitaryIntPow]
  | negSucc n =>
    simp [unitaryIntPow, zpow_negSucc, ← Unitary.star_eq_inv]

/-- If [U is unitary](hyp:hU), then [its integer power with exponent a + b
equals the product of its powers with exponents a and b](goal). -/
-- @node: near_unitaryIntPow_add
lemma near_unitaryIntPow_add
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (U : E →L[ℂ] E) (hU : U ∈ unitary _) (a b : ℤ) :
    unitaryIntPow U (a + b) = unitaryIntPow U a * unitaryIntPow U b := by
  simp only [near_unitaryIntPow_eq_zpow U hU, zpow_add, Submonoid.coe_mul]

/-- If [U is unitary](hyp:hU) and [V is unitary](hyp:hV), then [reordering
the product of U to the power k, V to the power m − p, and U to the power
−h into U to the power k − h followed by V to the power m − p changes it
in norm by at most |m − p| times |h| times the norm of the commutator of
U and V](goal). -/
-- @node: near_laurent_reordering_le
lemma near_laurent_reordering_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (U V : E →L[ℂ] E) (hU : U ∈ unitary _) (hV : V ∈ unitary _)
    (k m p h : ℤ) :
    ‖unitaryIntPow U k * unitaryIntPow V (m - p) * unitaryIntPow U (-h) -
      unitaryIntPow U (k - h) * unitaryIntPow V (m - p)‖ ≤
      ((m - p).natAbs : ℝ) * (h.natAbs : ℝ) * ‖U * V - V * U‖ := by
  have hcomm : ‖unitaryIntPow V (m - p) * unitaryIntPow U (-h) -
      unitaryIntPow U (-h) * unitaryIntPow V (m - p)‖ ≤
      ((m - p).natAbs : ℝ) * (h.natAbs : ℝ) * ‖U * V - V * U‖ := by
    simpa only [norm_sub_rev, Int.natAbs_neg, mul_comm (h.natAbs : ℝ)] using
      near_power_commutator_le U V hU hV (-h) (m - p)
  calc
    _ = ‖unitaryIntPow U k * (unitaryIntPow V (m - p) * unitaryIntPow U (-h) -
        unitaryIntPow U (-h) * unitaryIntPow V (m - p))‖ := by
      rw [sub_eq_add_neg k h, near_unitaryIntPow_add U hU]
      congr 1
      noncomm_ring
    _ ≤ ‖unitaryIntPow U k‖ * ‖unitaryIntPow V (m - p) * unitaryIntPow U (-h) -
        unitaryIntPow U (-h) * unitaryIntPow V (m - p)‖ := norm_mul_le _ _
    _ ≤ 1 * (((m - p).natAbs : ℝ) * (h.natAbs : ℝ) * ‖U * V - V * U‖) :=
      mul_le_mul (unitaryIntPow_norm_le U hU k) hcomm (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

/-- If [f is summable](hyp:hf), [g is summable](hyp:hg),
[h is summable](hyp:hh), and [l is summable](hyp:hl), and
[f is everywhere nonnegative](hyp:hf0), [g is everywhere nonnegative](hyp:hg0),
[h is everywhere nonnegative](hyp:hh0), and [l is everywhere nonnegative](hyp:hl0),
then [the product of their values at four independent integer indices is
summable over all integer quadruples](goal). -/
-- @node: near_fourfold_summable
lemma near_fourfold_summable (f g h l : ℤ → ℝ)
    (hf : Summable f) (hg : Summable g) (hh : Summable h) (hl : Summable l)
    (hf0 : ∀ k, 0 ≤ f k) (hg0 : ∀ k, 0 ≤ g k)
    (hh0 : ∀ k, 0 ≤ h k) (hl0 : ∀ k, 0 ≤ l k) :
    Summable (fun q : ℤ × ℤ × ℤ × ℤ => f q.1 * (g q.2.1 * (h q.2.2.1 * l q.2.2.2))) := by
  have hhl := hh.mul_of_nonneg hl hh0 hl0
  have hghl := hg.mul_of_nonneg hhl hg0 (fun q => mul_nonneg (hh0 q.1) (hl0 q.2))
  exact hf.mul_of_nonneg hghl hf0
    (fun q => mul_nonneg (hg0 q.1) (mul_nonneg (hh0 q.2.1) (hl0 q.2.2)))

/-- If [f is summable](hyp:hf), [g is summable](hyp:hg),
[h is summable](hyp:hh), and [l is summable](hyp:hl), and
[f is everywhere nonnegative](hyp:hf0), [g is everywhere nonnegative](hyp:hg0),
[h is everywhere nonnegative](hyp:hh0), and [l is everywhere nonnegative](hyp:hl0),
then [the sum of their product over four independent integer indices equals
the product of their four individual sums](goal). -/
-- @node: near_fourfold_tsum
lemma near_fourfold_tsum (f g h l : ℤ → ℝ)
    (hf : Summable f) (hg : Summable g) (hh : Summable h) (hl : Summable l)
    (hf0 : ∀ k, 0 ≤ f k) (hg0 : ∀ k, 0 ≤ g k)
    (hh0 : ∀ k, 0 ≤ h k) (hl0 : ∀ k, 0 ≤ l k) :
    (∑' q : ℤ × ℤ × ℤ × ℤ, f q.1 * (g q.2.1 * (h q.2.2.1 * l q.2.2.2))) =
      (∑' k, f k) * ((∑' k, g k) * ((∑' k, h k) * ∑' k, l k)) := by
  have hhl := hh.mul_of_nonneg hl hh0 hl0
  have hghl := hg.mul_of_nonneg hhl hg0 (fun q => mul_nonneg (hh0 q.1) (hl0 q.2))
  rw [← hf.tsum_mul_tsum hghl (near_fourfold_summable f g h l hf hg hh hl hf0 hg0 hh0 hl0)]
  rw [← hg.tsum_mul_tsum hhl hghl, ← hh.tsum_mul_tsum hl hhl]

/-- [The near-inclusion weight at every integer quadruple is nonnegative](goal). -/
-- @node: nearWeight_nonneg
lemma nearWeight_nonneg (q : ℤ × ℤ × ℤ × ℤ) : 0 ≤ nearWeight q := by
  unfold nearWeight
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
    (cWeight_nonneg _) (cWeight_nonneg _)) (cWeight_nonneg _))
    (cWeight_nonneg _)) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)

/-- [For every integer quadruple (k, m, p, h), its near-inclusion weight is
at most the product of the four coefficient weights multiplied by
(|m| + |p|)|h|, expressed as the sum of the terms with factors |m||h|
and |p||h|](goal). -/
-- @node: nearWeight_le_moment_majorant
lemma nearWeight_le_moment_majorant (q : ℤ × ℤ × ℤ × ℤ) :
    nearWeight q ≤
      cWeight q.1 * ((q.2.1.natAbs : ℝ) * cWeight q.2.1 *
        (cWeight q.2.2.1 * ((q.2.2.2.natAbs : ℝ) * cWeight q.2.2.2))) +
      cWeight q.1 * (cWeight q.2.1 * ((q.2.2.1.natAbs : ℝ) * cWeight q.2.2.1 *
        ((q.2.2.2.natAbs : ℝ) * cWeight q.2.2.2))) := by
  have habs : ((q.2.1 - q.2.2.1).natAbs : ℝ) ≤
      (q.2.1.natAbs : ℝ) + (q.2.2.1.natAbs : ℝ) := by
    exact_mod_cast Int.natAbs_sub_le q.2.1 q.2.2.1
  calc
    nearWeight q ≤ cWeight q.1 * cWeight q.2.1 * cWeight q.2.2.1 * cWeight q.2.2.2 *
        ((q.2.1.natAbs : ℝ) + (q.2.2.1.natAbs : ℝ)) * (q.2.2.2.natAbs : ℝ) := by
      unfold nearWeight
      have hprod0 := mul_nonneg (mul_nonneg (mul_nonneg
        (cWeight_nonneg q.1) (cWeight_nonneg q.2.1)) (cWeight_nonneg q.2.2.1))
        (cWeight_nonneg q.2.2.2)
      gcongr <;> first | fun_prop | assumption | positivity
    _ = _ := by ring

/-- [The near-inclusion weights are summable over all integer quadruples](goal). -/
-- @node: nearWeight_summable
lemma nearWeight_summable : Summable nearWeight := by
  have hm0 : ∀ k : ℤ, 0 ≤ (k.natAbs : ℝ) * cWeight k :=
    fun k => mul_nonneg (Nat.cast_nonneg _) (cWeight_nonneg k)
  have hleft := near_fourfold_summable _ _ _ _
    cWeight_summable cWeight_moment_summable cWeight_summable cWeight_moment_summable
    cWeight_nonneg hm0 cWeight_nonneg hm0
  have hright := near_fourfold_summable _ _ _ _
    cWeight_summable cWeight_summable cWeight_moment_summable cWeight_moment_summable
    cWeight_nonneg cWeight_nonneg hm0 hm0
  exact Summable.of_nonneg_of_le nearWeight_nonneg nearWeight_le_moment_majorant
    (hleft.add hright)

/-- [The universal near-inclusion constant is nonnegative](goal). -/
-- @node: nearC_nonneg
lemma nearC_nonneg : 0 ≤ nearC := tsum_nonneg nearWeight_nonneg

/-- [The universal near-inclusion constant is at most twice the square of
the total coefficient weight times the square of its first absolute moment](goal). -/
-- @node: nearC_le_moments
lemma nearC_le_moments : nearC ≤ 2 * S0 ^ 2 * S1 ^ 2 := by
  have hm0 : ∀ k : ℤ, 0 ≤ (k.natAbs : ℝ) * cWeight k :=
    fun k => mul_nonneg (Nat.cast_nonneg _) (cWeight_nonneg k)
  have hleft := near_fourfold_summable _ _ _ _
    cWeight_summable cWeight_moment_summable cWeight_summable cWeight_moment_summable
    cWeight_nonneg hm0 cWeight_nonneg hm0
  have hright := near_fourfold_summable _ _ _ _
    cWeight_summable cWeight_summable cWeight_moment_summable cWeight_moment_summable
    cWeight_nonneg cWeight_nonneg hm0 hm0
  have hsumleft := near_fourfold_tsum _ _ _ _
    cWeight_summable cWeight_moment_summable cWeight_summable cWeight_moment_summable
    cWeight_nonneg hm0 cWeight_nonneg hm0
  have hsumright := near_fourfold_tsum _ _ _ _
    cWeight_summable cWeight_summable cWeight_moment_summable cWeight_moment_summable
    cWeight_nonneg cWeight_nonneg hm0 hm0
  calc
    nearC ≤ _ := nearWeight_summable.tsum_le_tsum nearWeight_le_moment_majorant
      (hleft.add hright)
    _ = S0 * (S1 * (S0 * S1)) + S0 * (S0 * (S1 * S1)) := by
      rw [hleft.tsum_add hright, hsumleft, hsumright]
      rfl
    _ = 2 * S0 ^ 2 * S1 ^ 2 := by ring

end Papers.OaiNearInclusionsVon

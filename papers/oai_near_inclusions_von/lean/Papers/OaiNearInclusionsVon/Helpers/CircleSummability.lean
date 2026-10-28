module

public import Papers.OaiNearInclusionsVon.Helpers.FreeGroupSpace
public import Mathlib.Analysis.SpecificLimits.Normed

/-! Summable Laurent majorants and uniform absolute tails for the circle family. -/

public section

namespace Papers.OaiNearInclusionsVon

open Filter
open scoped Topology

-- @node: cWeight_nonneg
/-- [The Laurent coefficient weight is nonnegative at every integer index](goal). -/
lemma cWeight_nonneg (k : ℤ) : 0 ≤ cWeight k := by
  unfold cWeight tParam
  positivity

-- @node: circle_geometric_summable
/-- [The powers of one half indexed by the absolute value of an integer have a
finite sum over all integers](goal). -/
lemma circle_geometric_summable : Summable (fun k : ℤ => tParam ^ k.natAbs) := by
  have h : Summable (fun n : ℕ => tParam ^ n) :=
    summable_geometric_of_lt_one (by norm_num [tParam]) (by norm_num [tParam])
  apply summable_int_iff_summable_nat_and_neg.mpr
  simpa using And.intro h h

-- @node: circle_geometric_moment_summable
/-- [The absolute integer index times one half raised to that absolute index has
a finite sum over all integers](goal). -/
lemma circle_geometric_moment_summable :
    Summable (fun k : ℤ => (k.natAbs : ℝ) * tParam ^ k.natAbs) := by
  have h : Summable (fun n : ℕ => (n : ℝ) * tParam ^ n) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1
      (r := tParam) (by norm_num [tParam])
  apply summable_int_iff_summable_nat_and_neg.mpr
  simpa using And.intro h h

-- @node: cWeight_summable
/-- [The Laurent coefficient weights have a finite sum over all integer indices](goal). -/
lemma cWeight_summable : Summable cWeight := by
  have h₀ : Summable (fun k : ℤ => if k = 0 then (1 : ℝ) else 0) := by
    apply summable_of_ne_finset_zero (s := {0})
    intro k hk
    simp_all
  unfold cWeight
  simpa only [div_eq_mul_inv, mul_assoc] using
    h₀.add ((circle_geometric_summable.mul_left 2).mul_right (1 - tParam)⁻¹)

-- @node: cWeight_moment_summable
/-- [The Laurent coefficient weights multiplied by their absolute integer indices
have a finite sum](goal). -/
lemma cWeight_moment_summable :
    Summable (fun k : ℤ => (k.natAbs : ℝ) * cWeight k) := by
  have h := (circle_geometric_moment_summable.mul_left 2).mul_right (1 - tParam)⁻¹
  apply h.congr
  intro k
  by_cases hk : k = 0
  · subst k; simp [cWeight]
  · simp only [cWeight, hk, ite_false, zero_add, div_eq_mul_inv]
    ring

-- @node: circle_laurent_norm
/-- [Multiplying a Laurent coefficient by any integer power of a unit-circle
parameter leaves its operator norm unchanged](goal). -/
lemma circle_laurent_norm (A : LaurentData) (z : Circle) (g : FreeGrp) (k : ℤ) :
    ‖((z : ℂ) ^ k) • A k g‖ = ‖A k g‖ := by
  rw [norm_smul, norm_zpow, Circle.norm_coe, one_zpow, one_mul]

-- @node: circle_laurent_norm_summable
/-- If [each Laurent coefficient's operator norm is bounded by its index's
weight, uniformly over group elements](hyp:hA), then [the norms of the Laurent
terms have a finite sum at every circle parameter and group element](goal). -/
lemma circle_laurent_norm_summable (A : LaurentData)
    (hA : ∀ k g, ‖A k g‖ ≤ cWeight k) (z : Circle) (g : FreeGrp) :
    Summable (fun k : ℤ => ‖((z : ℂ) ^ k) • A k g‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ cWeight_summable
  intro k
  rw [circle_laurent_norm]
  exact hA k g

/-- If [each Laurent coefficient's operator norm is bounded by its index's weight,
uniformly over group elements](hyp:hA), then [for every positive tolerance there
is a finite set of integer indices such that the sum of Laurent term norms outside
that set is below the tolerance for every circle parameter and group element](goal). -/
-- @node: circle_laurent_uniform_tails
lemma circle_laurent_uniform_tails (A : LaurentData)
    (hA : ∀ k g, ‖A k g‖ ≤ cWeight k) :
    ∀ ε : ℝ, 0 < ε → ∃ s : Finset ℤ, ∀ (z : Circle) (g : FreeGrp),
      ∑' k : {k : ℤ // k ∉ s}, ‖((z : ℂ) ^ (k : ℤ)) • A k g‖ < ε := by
  intro ε hε
  obtain ⟨s, hs⟩ := ((tendsto_tsum_compl_atTop_zero cWeight).eventually_lt_const hε).exists
  refine ⟨s, fun z g => lt_of_le_of_lt ?_ hs⟩
  apply Summable.tsum_le_tsum
  · intro k
    rw [circle_laurent_norm]
    exact hA k g
  · exact (circle_laurent_norm_summable A hA z g).subtype (fun k => k ∉ s)
  · exact cWeight_summable.subtype (fun k => k ∉ s)

/-- If [the Laurent series sums to the given representation at every circle parameter
and group element](hyp:hsum), [all coefficient norms are bounded by their index's
weight](hyp:hA), and [the representations of successive free generators converge
in every matrix coefficient to one half times the circle parameter times the
projection onto the identity basis vector](hyp:hwot), then [the representation
and coefficients form a circle family, with summable weights and first absolute
moment, absolutely convergent Laurent series, and tails uniformly small in the
circle parameter and group element](goal). -/
-- @node: circle_family_of_coefficients
lemma circle_family_of_coefficients (π : CircleRep) (A : LaurentData)
    (hsum : ∀ (z : Circle) (g : FreeGrp),
      HasSum (fun k : ℤ => ((z : ℂ) ^ k) • A k g) (π z g : TreeSpace →L[ℂ] TreeSpace))
    (hA : ∀ k g, ‖A k g‖ ≤ cWeight k)
    (hwot : ∀ (z : Circle) (ξ η : TreeSpace),
      Tendsto (fun j => inner ℂ ξ ((π z (gen j) : TreeSpace →L[ℂ] TreeSpace) η))
        atTop (𝓝 (inner ℂ ξ ((((tParam : ℂ) * (z : ℂ)) • projE) η)))) :
    IsCircleFamily π A := by
  exact ⟨hsum, hA, hwot, cWeight_summable, cWeight_moment_summable,
    circle_laurent_norm_summable A hA, circle_laurent_uniform_tails A hA⟩

end Papers.OaiNearInclusionsVon

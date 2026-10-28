module

public import Papers.OaiNearInclusionsVon.Helpers.Amplification
public import Mathlib.GroupTheory.FreeGroup.Reduce
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Complex.Circle

/-! The free group, its regular Hilbert space, and the circle-family coefficients. -/

@[expose] public section

set_option linter.style.longLine false

namespace Papers.OaiNearInclusionsVon


open Filter
open scoped Topology ComplexConjugate

-- @env: S2
variable (j : ℕ)

-- @node: def:free-group
/-- The [free group on countably many generators](goal) has one generator for each
natural number. -/
noncomputable abbrev FreeGrp := FreeGroup ℕ -- @realizes F(countably generated free group)

/-- For [a natural-number index j](hyp:j), the [j-th free generator](goal) is the
corresponding distinguished element of the countably generated free group. -/
noncomputable def gen (j : ℕ) : FreeGrp := FreeGroup.of j -- @realizes s_j(generators, relabelled from one)
/-- The [identity element of the countably generated free group](goal) is its neutral
element for multiplication. -/
noncomputable def freeIdentity : FreeGrp := 1 -- @realizes e(group identity)

-- @node: def:regular-space
/-- The [regular Hilbert space of the free group](goal) consists of square-summable
complex-valued functions on the group. -/
noncomputable abbrev TreeSpace := lp (fun _ : FreeGrp => ℂ) 2 -- @realizes K(ℓ² of F)

-- @node: def:tree-basis
/-- For [a free-group element x](hyp:x), the [standard basis vector at x](goal) is the
square-summable function equal to one at x and zero elsewhere. -/
noncomputable def treeBasis (x : FreeGrp) : TreeSpace :=
  lp.single 2 x 1 -- @realizes \delta_x(standard basis in K)

-- @node: def:identity-projection
/-- The [identity-vector projection](goal) is the orthogonal projection onto the
one-dimensional span of the standard basis vector at the group identity. -/
noncomputable def projE : TreeSpace →L[ℂ] TreeSpace :=
  (ℂ ∙ treeBasis 1).starProjection -- @realizes p_e(projection onto the identity vector)

-- @node: def:left-regular
/-- For [a free-group element g](hyp:g), the [left regular operator associated with
g](goal) sends a function to the function whose value at x is its original value at
the product of the inverse of g with x. -/
noncomputable def leftReg (g : FreeGrp) : TreeSpace →L[ℂ] TreeSpace :=
  lpReindex (Equiv.mulLeft g⁻¹) -- @realizes l(left regular action)

/-- The [fixed real parameter t](goal) equals one half. -/
noncomputable def tParam : ℝ := 1 / 2 -- @realizes t(fixed scalar one half)

/-- The [real parameter r](goal) is the nonnegative square root of one minus the
square of t. -/
noncomputable def rParam : ℝ := Real.sqrt (1 - tParam ^ 2) -- @realizes r(positive square root)
/-- The [circle parameter space](goal) is the complex unit circle, consisting of
complex numbers of modulus one. -/
noncomputable abbrev CircleParam := Circle -- @realizes \mathbb T(complex unit circle)

-- @node: def:circle-parameters
/-- The [triple of circle-family parameters](goal) consists of t equal to one half,
r equal to the nonnegative square root of one minus t squared, and the set of complex
numbers of modulus one. -/
noncomputable def circleParameters : ℝ × ℝ × Set ℂ :=
  (tParam, rParam, {z : ℂ | ‖z‖ = 1}) -- @realizes \mathbb T(complex numbers of norm one)

/-- For [an integer Laurent index k](hyp:k), the [coefficient weight at k](goal) is
the indicator that k is zero plus twice t raised to the absolute value of k divided
by one minus t. -/
noncomputable def cWeight (k : ℤ) : ℝ :=
  (if k = 0 then 1 else 0) + 2 * tParam ^ k.natAbs / (1 - tParam) -- @realizes c_k(Laurent coefficient bound)

-- @node: s0
/-- The [zeroth moment of the coefficient weights](goal) is their sum over all integer
Laurent indices. -/
noncomputable def S0 : ℝ := ∑' k : ℤ, cWeight k -- @realizes S_0(zeroth moment)
-- @node: s1
/-- The [first absolute moment of the coefficient weights](goal) is the sum, over all
integer Laurent indices, of each weight multiplied by the absolute value of its index. -/
noncomputable def S1 : ℝ := ∑' k : ℤ, (k.natAbs : ℝ) * cWeight k -- @realizes S_1(first absolute moment)

/-- A [circle-indexed family of unitary representations](goal) assigns to each point
of the complex unit circle a group homomorphism from the free group to the unitary
operators on its regular Hilbert space. -/
noncomputable abbrev CircleRep := Circle → FreeGrp →* unitary (TreeSpace →L[ℂ] TreeSpace)
/-- An [array of operator-valued Laurent data](goal) assigns a bounded operator on
the regular Hilbert space to each integer Laurent index and each free-group element. -/
noncomputable abbrev LaurentData := ℤ → FreeGrp → (TreeSpace →L[ℂ] TreeSpace)

/-- For [a circle-indexed family of unitary representations π](hyp:π) and
[operator-valued Laurent coefficients A indexed by integers and free-group elements](hyp:A),
the [circle-family condition](goal) requires that
[the Laurent series sums in operator norm to π at each circle point and group element](step:1),
[each coefficient norm is bounded by the corresponding coefficient weight](step:2),
[the generator operators converge weakly to t times the circle parameter times the
identity-vector projection](step:3),
[the coefficient weights are summable](step:4),
[their first absolute moments are summable](step:5),
[the Laurent series is absolutely summable at every circle point and group element](step:6),
and [for every positive tolerance a finite set of Laurent indices makes the sum of
norms outside that set smaller than the tolerance uniformly over circle points and
group elements](step:7). -/
noncomputable def IsCircleFamily (π : CircleRep) (A : LaurentData) : Prop :=
  (∀ (z : Circle) (g : FreeGrp),
    HasSum (fun k : ℤ => ((z : ℂ) ^ k) • A k g) (π z g : TreeSpace →L[ℂ] TreeSpace)) ∧ -- @realizes A_k(g)(operator-valued Laurent coefficients)
  (∀ k g, ‖A k g‖ ≤ cWeight k) ∧
  (∀ (z : Circle) (ξ η : TreeSpace),
    Tendsto (fun j => inner ℂ ξ ((π z (gen j) : TreeSpace →L[ℂ] TreeSpace) η))
      atTop (𝓝 (inner ℂ ξ ((((tParam : ℂ) * (z : ℂ)) • projE) η)))) ∧ -- @realizes \pi_z(unitary representations with the stated WOT limit)
  Summable cWeight ∧ Summable (fun k : ℤ => (k.natAbs : ℝ) * cWeight k) ∧
  (∀ (z : Circle) (g : FreeGrp), Summable (fun k : ℤ => ‖((z : ℂ) ^ k) • A k g‖)) ∧ -- @realizes z(unit circle parameter)
  (∀ ε : ℝ, 0 < ε → ∃ s : Finset ℤ, ∀ (z : Circle) (g : FreeGrp),
    ∑' k : {k : ℤ // k ∉ s}, ‖((z : ℂ) ^ (k : ℤ)) • A k g‖ < ε)

end Papers.OaiNearInclusionsVon

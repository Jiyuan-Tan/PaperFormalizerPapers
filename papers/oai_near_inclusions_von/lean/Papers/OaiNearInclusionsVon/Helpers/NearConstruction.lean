module

public import Papers.OaiNearInclusionsVon.Helpers.AmplificationAlgebra
public import Papers.OaiNearInclusionsVon.Helpers.FreeGroupSpace
public import Papers.OaiNearInclusionsVon.Helpers.Gap
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Papers.OaiNearInclusionsVon.Helpers.CircleSummability

/-! Laurent substitution, product representations, and the near-inclusion algebras. -/

@[expose] public section

set_option linter.style.longLine false

namespace Papers.OaiNearInclusionsVon


open Filter
open scoped Topology

-- @env: S3
variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℂ D] [CompleteSpace D] -- @realizes D(input complex Hilbert space; dimension and nonzeroness in NearUnitaryPair)

-- @node: ass:near-unitary-pair
/-- For [a complex Hilbert space D](hyp:D) and [operators U](hyp:U) and [V on D](hyp:V),
the [near-unitary-pair condition](goal) requires that [D is nonzero](step:1),
[D is finite-dimensional](step:2), [U is unitary](step:3), and [V is unitary](step:4). -/
noncomputable def NearUnitaryPair (U V : D →L[ℂ] D) : Prop := -- @realizes U(operator on D) @realizes V(operator on D)
  Nontrivial D ∧ FiniteDimensional ℂ D ∧ -- @realizes D(nonzero finite-dimensional input space)
  U ∈ unitary (D →L[ℂ] D) ∧ -- @realizes U(first input unitary)
  V ∈ unitary (D →L[ℂ] D) -- @realizes V(second input unitary)

/-- For [a normed additive group D](hyp:D), the [space L](goal) consists of
square-summable sequences, indexed by the free group, of square-summable
free-group-indexed sequences with values in D. -/
noncomputable abbrev Lsp (D : Type*) [NormedAddCommGroup D] :=
  lp (fun _ : FreeGrp => lp (fun _ : FreeGrp => D) 2) 2 -- @realizes L(K tensor K tensor D)

/-- The [identity operator on the free group's regular Hilbert space](goal) leaves every vector unchanged. -/
noncomputable def treeIdentity : TreeSpace →L[ℂ] TreeSpace := 1 -- @realizes I_K(identity on K)
/-- For [a complex Hilbert space D](hyp:D) and [a bounded operator X on the free
group's regular Hilbert space](hyp:X), the [first-factor amplification of X](goal)
acts on the first regular factor of L and leaves the other two factors unchanged. -/
noncomputable def ampFst (X : TreeSpace →L[ℂ] TreeSpace) : Lsp D →L[ℂ] Lsp D :=
  amplify X
/-- For [a complex Hilbert space D](hyp:D) and [a bounded operator X on the free
group's regular Hilbert space](hyp:X), the [second-factor amplification of X](goal)
acts on the second regular factor of L and leaves the other two factors unchanged. -/
noncomputable def ampSnd (X : TreeSpace →L[ℂ] TreeSpace) : Lsp D →L[ℂ] Lsp D :=
  lp.mapCLM 2 (fun _ : FreeGrp => amplify (E := D) X)
    (norm_nonneg X) (fun _ => (amplify_spec X).2)
/-- For [a complex Hilbert space D](hyp:D) and [a bounded operator Y on D](hyp:Y),
the [D-factor amplification of Y](goal) applies Y to each D-valued coordinate of L. -/
noncomputable def ampD (Y : D →L[ℂ] D) : Lsp D →L[ℂ] Lsp D :=
  lp.mapCLM 2 (fun _ : FreeGrp =>
    lp.mapCLM 2 (fun _ : FreeGrp => Y) (norm_nonneg Y) (fun _ => le_rfl))
    (norm_nonneg Y) (fun _ => lp.norm_mapCLM_le 2 _ (norm_nonneg Y) (fun _ => le_rfl))

/-- For [a complex Hilbert space D](hyp:D), [a bounded operator U on D](hyp:U),
and [an integer exponent k](hyp:k), the [adjoint-based integer power of U](goal)
is the usual k-th power when k is nonnegative and the absolute-k-th power of the
adjoint when k is negative. -/
noncomputable def unitaryIntPow (U : D →L[ℂ] D) (k : ℤ) : D →L[ℂ] D :=
  if 0 ≤ k then U ^ k.toNat else (star U) ^ k.natAbs

/-- For [a complex Hilbert space D](hyp:D), [operator-valued Laurent coefficients A](hyp:A),
[an operator U on D](hyp:U), [an integer index k](hyp:k), and [a free-group element g](hyp:g),
the [first substitution term](goal) is the product of the first-factor amplification
of the coefficient at k and g with the D-factor amplification of U's adjoint-based integer power k. -/
noncomputable def aTerm (A : LaurentData) (U : D →L[ℂ] D) (k : ℤ) (g : FreeGrp) :
    Lsp D →L[ℂ] Lsp D := ampFst (A k g) * ampD (unitaryIntPow U k)
/-- For [a complex Hilbert space D](hyp:D), [operator-valued Laurent coefficients A](hyp:A),
[an operator V on D](hyp:V), [an integer index k](hyp:k), and [a free-group element g](hyp:g),
the [second substitution term](goal) is the product of the second-factor amplification
of the coefficient at k and g with the D-factor amplification of V's adjoint-based integer power k. -/
noncomputable def bTerm (A : LaurentData) (V : D →L[ℂ] D) (k : ℤ) (g : FreeGrp) :
    Lsp D →L[ℂ] Lsp D := ampSnd (A k g) * ampD (unitaryIntPow V k)

-- @node: ass:pin-1
/-- For [a complex Hilbert space D](hyp:D), [operator-valued Laurent coefficients A](hyp:A),
and [operators U](hyp:U) and [V on D](hyp:V), the [absolute-convergence condition
for both matrix substitutions](goal) requires, at every free-group element,
[summability over integer indices of the norms of the first substitution terms](step:1)
and [summability of the norms of the second substitution terms](step:2). -/
noncomputable def MatrixRepsAbsConv (A : LaurentData) (U V : D →L[ℂ] D) : Prop :=
  ∀ g : FreeGrp, Summable (fun k : ℤ => ‖aTerm A U k g‖) ∧
    Summable (fun k : ℤ => ‖bTerm A V k g‖)

-- @node: def:matrix-reps
/-- For [a complex Hilbert space D](hyp:D), [operator-valued Laurent coefficients A](hyp:A),
[an operator U on D](hyp:U), and [a free-group element g](hyp:g), the
[first matrix substitution at g](goal) is the sum over all integer indices of the
first substitution terms formed from A and U. -/
noncomputable def matrixRepA (A : LaurentData) (U : D →L[ℂ] D) (g : FreeGrp) :
    Lsp D →L[ℂ] Lsp D := ∑' k : ℤ, aTerm A U k g -- @realizes a(Laurent substitution in first factor)
/-- For [a complex Hilbert space D](hyp:D), [operator-valued Laurent coefficients A](hyp:A),
[an operator V on D](hyp:V), and [a free-group element g](hyp:g), the
[second matrix substitution at g](goal) is the sum over all integer indices of the
second substitution terms formed from A and V. -/
noncomputable def matrixRepB (A : LaurentData) (V : D →L[ℂ] D) (g : FreeGrp) :
    Lsp D →L[ℂ] Lsp D := ∑' k : ℤ, bTerm A V k g -- @realizes b(Laurent substitution in second factor)

/-- For [a complex Hilbert space D](hyp:D) and [an operator U on D](hyp:U), the
[first matrix limit operator](goal) is one half times the product of the first-factor
amplification of the projection onto the identity basis vector and the D-factor amplification of U. -/
noncomputable def matrixLimitA (U : D →L[ℂ] D) : Lsp D →L[ℂ] Lsp D :=
  tParam • (ampFst projE * ampD U)
/-- For [a complex Hilbert space D](hyp:D) and [an operator V on D](hyp:V), the
[second matrix limit operator](goal) is one half times the product of the second-factor
amplification of the projection onto the identity basis vector and the D-factor amplification of V. -/
noncomputable def matrixLimitB (V : D →L[ℂ] D) : Lsp D →L[ℂ] Lsp D :=
  tParam • (ampSnd projE * ampD V)

-- @node: def:product-spaces
/-- The [product group](goal) is the direct product of two copies of the free group. -/
noncomputable abbrev ProdGrp := FreeGrp × FreeGrp -- @realizes G(product group)
/-- The [regular Hilbert space of the product group](goal) consists of square-summable
complex-valued functions on the product group. -/
noncomputable abbrev Ssp := lp (fun _ : ProdGrp => ℂ) 2 -- @realizes S(regular product-group Hilbert space)
/-- For [a normed additive group D](hyp:D), the [space H](goal) consists of
square-summable functions on the product group with values in L, the space of
square-summable D-valued arrays indexed by two free-group elements. -/
noncomputable abbrev Hsp (D : Type*) [NormedAddCommGroup D] :=
  lp (fun _ : ProdGrp => Lsp D) 2 -- @realizes H(S tensor L)

/-- For [a product-group element x](hyp:x), the [standard basis vector at x](goal)
equals one at x and zero at every other product-group element. -/
noncomputable def prodBasis (x : ProdGrp) : Ssp := lp.single 2 x 1 -- @realizes \delta_x(standard basis in S)
/-- For [a complex Hilbert space D](hyp:D), the [identity operator on L](goal)
leaves every square-summable D-valued array unchanged. -/
noncomputable def tensorIdentity : Lsp D →L[ℂ] Lsp D := 1 -- @realizes I_L(identity on L)

-- @node: def:product-regular
/-- For [a product-group element g](hyp:g), the [left regular operator at g](goal)
sends a scalar-valued function to the function whose value at x is its original value at g inverse times x. -/
noncomputable def lamReg (g : ProdGrp) : Ssp →L[ℂ] Ssp :=
  lpReindex (Equiv.mulLeft g⁻¹) -- @realizes \lambda(left regular representation)
/-- For [a product-group element g](hyp:g), the [right regular operator at g](goal)
sends a scalar-valued function to the function whose value at x is its original value at x times g. -/
noncomputable def rhoReg (g : ProdGrp) : Ssp →L[ℂ] Ssp :=
  lpReindex (Equiv.mulRight g) -- @realizes \rho(right regular representation)
/-- For [a complex Hilbert space D](hyp:D) and [a product-group element g](hyp:g),
the [amplified left regular operator at g](goal) sends an L-valued function to the
function whose value at x is its original value at g inverse times x. -/
noncomputable def lamAmp (g : ProdGrp) : Hsp D →L[ℂ] Hsp D :=
  lpReindex (Equiv.mulLeft g⁻¹)
/-- For [a complex Hilbert space D](hyp:D) and [a product-group element g](hyp:g),
the [amplified right regular operator at g](goal) sends an L-valued function to the
function whose value at x is its original value at x times g. -/
noncomputable def rhoAmp (g : ProdGrp) : Hsp D →L[ℂ] Hsp D :=
  lpReindex (Equiv.mulRight g)

-- @node: def:product-map
/-- For [a complex Hilbert space D](hyp:D), [operator-valued Laurent coefficients A](hyp:A),
[operators U](hyp:U) and [V on D](hyp:V), and [a pair x of free-group elements](hyp:x),
the [product map at x](goal) is the first matrix substitution at the first element
multiplied, in that order, by the second matrix substitution at the second element. -/
noncomputable def prodMap (A : LaurentData) (U V : D →L[ℂ] D) (x : ProdGrp) :
    Lsp D →L[ℂ] Lsp D := matrixRepA A U x.1 * matrixRepB A V x.2 -- @realizes f(ordered product)

-- @node: ampFst_mem_unitary
/-- If [X is unitary on the free group's regular Hilbert space](hyp:hX), then
[its first-factor amplification on L is unitary](goal). -/
lemma ampFst_mem_unitary (X : TreeSpace →L[ℂ] TreeSpace) (hX : X ∈ unitary _) :
    ampFst (D := D) X ∈ unitary (Lsp D →L[ℂ] Lsp D) :=
  amplify_mem_unitary X hX

-- @node: ampSnd_mem_unitary
/-- If [X is unitary on the free group's regular Hilbert space](hyp:hX), then
[its second-factor amplification on L is unitary](goal). -/
lemma ampSnd_mem_unitary (X : TreeSpace →L[ℂ] TreeSpace) (hX : X ∈ unitary _) :
    ampSnd (D := D) X ∈ unitary (Lsp D →L[ℂ] Lsp D) := by
  exact lpMap_mem_unitary _ (norm_nonneg X) _ (fun _ => amplify_mem_unitary X hX)

-- @node: ampD_mem_unitary
/-- If [Y is a unitary operator on D](hyp:hY), then
[its D-factor amplification on L is unitary](goal). -/
lemma ampD_mem_unitary (Y : D →L[ℂ] D) (hY : Y ∈ unitary _) :
    ampD Y ∈ unitary (Lsp D →L[ℂ] Lsp D) := by
  apply lpMap_mem_unitary
  intro _
  exact lpMap_mem_unitary _ (norm_nonneg Y) _ (fun _ => hY)

-- @node: ampD_mul
/-- For bounded operators X and Y on D, [the D-factor amplification of their
product equals the product of their D-factor amplifications in the same order](goal). -/
lemma ampD_mul (X Y : D →L[ℂ] D) : ampD (X * Y) = ampD X * ampD Y := by
  ext ξ x y
  rfl

-- @node: ampD_star
/-- For a bounded operator Y on D, [amplifying its adjoint on the D factor gives
the adjoint of its D-factor amplification](goal). -/
lemma ampD_star (Y : D →L[ℂ] D) : ampD (star Y) = star (ampD Y) := by
  symm
  unfold ampD
  rw [lpMap_star]
  congr 1
  · funext x
    exact lpMap_star _ (norm_nonneg Y) _
  · simp

-- @node: ampFst_commute_ampD
/-- For a bounded operator X on the free group's regular Hilbert space and a
bounded operator Y on D, [the first-factor amplification of X commutes with the
D-factor amplification of Y](goal). -/
lemma ampFst_commute_ampD (X : TreeSpace →L[ℂ] TreeSpace) (Y : D →L[ℂ] D) :
    Commute (ampFst (D := D) X) (ampD Y) := by
  have h := amplify_commute_lpMap X
    (lp.mapCLM 2 (fun _ : FreeGrp => Y) (norm_nonneg Y) (fun _ => le_rfl))
  convert h using 1 <;> rfl

-- @node: ampSnd_commute_ampD
/-- For a bounded operator X on the free group's regular Hilbert space and a
bounded operator Y on D, [the second-factor amplification of X commutes with the
D-factor amplification of Y](goal). -/
lemma ampSnd_commute_ampD (X : TreeSpace →L[ℂ] TreeSpace) (Y : D →L[ℂ] D) :
    Commute (ampSnd (D := D) X) (ampD Y) := by
  have h := amplify_commute_lpMap X Y
  change ampSnd X * ampD Y = ampD Y * ampSnd X
  ext ξ x y
  exact congrArg (fun T : lp (fun _ : FreeGrp => D) 2 →L[ℂ]
    lp (fun _ : FreeGrp => D) 2 => T (ξ x) y) h.eq

-- @node: unitaryIntPow_mem_unitary
/-- If [U is unitary on D](hyp:hU), then [every adjoint-based integer power of U
is unitary](goal). -/
lemma unitaryIntPow_mem_unitary (U : D →L[ℂ] D) (hU : U ∈ unitary _) (k : ℤ) :
    unitaryIntPow U k ∈ unitary (D →L[ℂ] D) := by
  unfold unitaryIntPow
  split
  · exact (unitary _).pow_mem hU _
  · exact (unitary _).pow_mem (Unitary.star_mem hU) _

-- @node: unitaryIntPow_norm_le
/-- If [U is unitary on D](hyp:hU), then [the operator norm of every adjoint-based
integer power of U is at most one](goal). -/
lemma unitaryIntPow_norm_le (U : D →L[ℂ] D) (hU : U ∈ unitary _) (k : ℤ) :
    ‖unitaryIntPow U k‖ ≤ 1 := by
  rcases subsingleton_or_nontrivial D with hD | hD
  · have hzero : unitaryIntPow U k = 0 := Subsingleton.elim _ _
    simp [hzero]
  · have hnorm : ‖U‖ ≤ 1 := (CStarRing.norm_of_mem_unitary hU).le
    unfold unitaryIntPow
    split
    · exact (norm_pow_le _ _).trans (pow_le_one₀ (norm_nonneg _) hnorm)
    · exact (norm_pow_le _ _).trans (pow_le_one₀ (norm_nonneg _) (by simpa using hnorm))

-- @node: ampD_norm_le
/-- For a bounded operator Y on D, [the operator norm of its D-factor amplification
is at most the operator norm of Y](goal). -/
lemma ampD_norm_le (Y : D →L[ℂ] D) : ‖ampD Y‖ ≤ ‖Y‖ := by
  exact lp.norm_mapCLM_le 2 _ (norm_nonneg Y) _

-- @node: aTerm_norm_le
/-- If [U is unitary on D](hyp:hU), then, for any operator-valued Laurent data A,
integer index k, and free-group element g, [the norm of the first substitution term
at k and g is at most the norm of the corresponding Laurent coefficient](goal). -/
lemma aTerm_norm_le (A : LaurentData) (U : D →L[ℂ] D)
    (hU : U ∈ unitary _) (k : ℤ) (g : FreeGrp) : ‖aTerm A U k g‖ ≤ ‖A k g‖ := by
  calc
    ‖aTerm A U k g‖ ≤ ‖ampFst (D := D) (A k g)‖ * ‖ampD (unitaryIntPow U k)‖ := norm_mul_le _ _
    _ ≤ ‖A k g‖ * 1 := mul_le_mul (amplify_spec (A k g)).2
      ((ampD_norm_le _).trans (unitaryIntPow_norm_le U hU k))
      (norm_nonneg _) (norm_nonneg _)
    _ = ‖A k g‖ := mul_one _

-- @node: bTerm_norm_le
/-- If [V is unitary on D](hyp:hV), then, for any operator-valued Laurent data A,
integer index k, and free-group element g, [the norm of the second substitution term
at k and g is at most the norm of the corresponding Laurent coefficient](goal). -/
lemma bTerm_norm_le (A : LaurentData) (V : D →L[ℂ] D)
    (hV : V ∈ unitary _) (k : ℤ) (g : FreeGrp) : ‖bTerm A V k g‖ ≤ ‖A k g‖ := by
  calc
    ‖bTerm A V k g‖ ≤ ‖ampSnd (D := D) (A k g)‖ * ‖ampD (unitaryIntPow V k)‖ := norm_mul_le _ _
    _ ≤ ‖A k g‖ * 1 := mul_le_mul
      (lp.norm_mapCLM_le 2 _ (norm_nonneg _) _)
      ((ampD_norm_le _).trans (unitaryIntPow_norm_le V hV k))
      (norm_nonneg _) (norm_nonneg _)
    _ = ‖A k g‖ := mul_one _

-- @node: matrixRepA_norm_le
/-- If [A and the circle-indexed representations π satisfy the circle-family
condition](hyp:hπ) and [U is unitary on D](hyp:hU), then [the norm of the first
matrix substitution at any free-group element is at most S₀, the sum of the
coefficient weights](goal). -/
lemma matrixRepA_norm_le (π : CircleRep) (A : LaurentData) (hπ : IsCircleFamily π A)
    (U : D →L[ℂ] D) (hU : U ∈ unitary _) (g : FreeGrp) :
    ‖matrixRepA A U g‖ ≤ S0 := by
  exact tsum_of_norm_bounded cWeight_summable.hasSum
    (fun k => (aTerm_norm_le A U hU k g).trans (hπ.2.1 k g))

-- @node: matrixRepB_norm_le
/-- If [A and the circle-indexed representations π satisfy the circle-family
condition](hyp:hπ) and [V is unitary on D](hyp:hV), then [the norm of the second
matrix substitution at any free-group element is at most S₀, the sum of the
coefficient weights](goal). -/
lemma matrixRepB_norm_le (π : CircleRep) (A : LaurentData) (hπ : IsCircleFamily π A)
    (V : D →L[ℂ] D) (hV : V ∈ unitary _) (g : FreeGrp) :
    ‖matrixRepB A V g‖ ≤ S0 := by
  exact tsum_of_norm_bounded cWeight_summable.hasSum
    (fun k => (bTerm_norm_le A V hV k g).trans (hπ.2.1 k g))

-- @node: matrixRepsAbsConv_of_circleFamily
/-- If [A and the circle-indexed representations π satisfy the circle-family
condition](hyp:hπ), [U is unitary on D](hyp:hU), and [V is unitary on D](hyp:hV),
then [both matrix substitutions converge absolutely in operator norm at every
free-group element](goal). -/
lemma matrixRepsAbsConv_of_circleFamily (π : CircleRep) (A : LaurentData)
    (hπ : IsCircleFamily π A) (U V : D →L[ℂ] D)
    (hU : U ∈ unitary _) (hV : V ∈ unitary _) : MatrixRepsAbsConv A U V := by
  intro g
  constructor
  · exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun k => (aTerm_norm_le A U hU k g).trans (hπ.2.1 k g)) cWeight_summable
  · exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun k => (bTerm_norm_le A V hV k g).trans (hπ.2.1 k g)) cWeight_summable

-- @node: prodMap_norm_bound
/-- If [A and the circle-indexed representations π satisfy the circle-family
condition](hyp:hπ) and [U and V are both unitary on D](hyp:hUV), then [at every
product-group element the product map has operator norm at most the square of S₀,
the sum of the coefficient weights](goal). -/
lemma prodMap_norm_bound (π : CircleRep) (A : LaurentData) (hπ : IsCircleFamily π A)
    (U V : D →L[ℂ] D) (hUV : U ∈ unitary _ ∧ V ∈ unitary _) :
    ∀ x : ProdGrp, ‖prodMap A U V x‖ ≤ S0 ^ 2 := by
  intro x
  have hS0 : 0 ≤ S0 := tsum_nonneg cWeight_nonneg
  calc
    ‖prodMap A U V x‖ ≤ ‖matrixRepA A U x.1‖ * ‖matrixRepB A V x.2‖ := norm_mul_le _ _
    _ ≤ S0 * S0 := mul_le_mul (matrixRepA_norm_le π A hπ U hUV.1 x.1)
      (matrixRepB_norm_le π A hπ V hUV.2 x.2) (norm_nonneg _) hS0
    _ = S0 ^ 2 := (pow_two _).symm

-- @node: def:diagonal-unitary
/-- For [a complex Hilbert space D](hyp:D), [operator-valued Laurent coefficients A](hyp:A),
[operators U and V on D](hyp:U,V), and [a uniform bound of S₀ squared on the norms
of their product-map operators](hyp:hb), the [diagonal operator on H](goal) applies
the product-map operator at each product-group element to the vector's coordinate there. -/
noncomputable def diagUnitary (A : LaurentData) (U V : D →L[ℂ] D)
    (hb : ∀ x : ProdGrp, ‖prodMap A U V x‖ ≤ S0 ^ 2) : Hsp D →L[ℂ] Hsp D :=
  lp.mapCLM 2 (prodMap A U V) (sq_nonneg S0) hb -- @realizes W(diagonal operator with blocks f(x))

-- @node: diagUnitary_star_apply
/-- If [every product-map operator formed from A, U, and V has norm at most S₀
squared](hyp:hb), then [the coordinate at x of the adjoint diagonal operator applied
to a vector ξ equals the adjoint of the product-map operator at x applied to the
coordinate of ξ at x](goal). -/
lemma diagUnitary_star_apply (A : LaurentData) (U V : D →L[ℂ] D)
    (hb : ∀ x : ProdGrp, ‖prodMap A U V x‖ ≤ S0 ^ 2) (ξ : Hsp D) (x : ProdGrp) :
    star (diagUnitary A U V hb) ξ x = star (prodMap A U V x) (ξ x) := by
  unfold diagUnitary
  rw [lpMap_star]
  rfl

-- @node: diagUnitary_star_single
/-- If [every product-map operator formed from A, U, and V has norm at most S₀
squared](hyp:hb), then [the adjoint diagonal operator sends a vector supported only
at y, with value v, to a vector supported only at y whose value is the adjoint
product-map operator at y applied to v](goal). -/
lemma diagUnitary_star_single (A : LaurentData) (U V : D →L[ℂ] D)
    (hb : ∀ x : ProdGrp, ‖prodMap A U V x‖ ≤ S0 ^ 2) (y : ProdGrp) (v : Lsp D) :
    star (diagUnitary A U V hb) (lp.single 2 y v) =
      lp.single 2 y (star (prodMap A U V y) v) := by
  ext x
  by_cases h : y = x <;> simp [diagUnitary_star_apply, lp.single_apply, h]

-- @node: hspBlock
/-- For [a complex Hilbert space D](hyp:D), [a bounded operator T on H](hyp:T),
and [product-group indices x and y](hyp:x,y), the [operator-valued matrix block
of T in row x and column y](goal) sends a vector in L to the coordinate at x
obtained by applying T to that vector placed only at y. -/
noncomputable def hspBlock (T : Hsp D →L[ℂ] Hsp D) (x y : ProdGrp) :
    Lsp D →L[ℂ] Lsp D :=
  lp.evalCLM ℂ (fun _ : ProdGrp => Lsp D) 2 x ∘L T ∘L
    lp.singleContinuousLinearMap ℂ (fun _ : ProdGrp => Lsp D) 2 y

-- @node: hspBlock_apply
/-- For a bounded operator T on H, product-group indices x and y, and a vector v
in L, [the row-x, column-y block of T applied to v equals the coordinate at x of
T applied to the vector supported only at y with value v](goal). -/
lemma hspBlock_apply (T : Hsp D →L[ℂ] Hsp D) (x y : ProdGrp) (v : Lsp D) :
    hspBlock T x y v = T (lp.single 2 y v) x := rfl

-- @node: hspBlock_ext
/-- If [two bounded operators T and R on H have equal operator-valued blocks
at every pair of product-group indices](hyp:h), then [T and R are equal](goal). -/
lemma hspBlock_ext (T R : Hsp D →L[ℂ] Hsp D)
    (h : ∀ x y, hspBlock T x y = hspBlock R x y) : T = R := by
  apply lp.ext_continuousLinearMap (by norm_num)
  intro y
  apply ContinuousLinearMap.ext
  intro v
  apply lp.ext
  funext x
  exact DFunLike.congr_fun (h x y) v

-- @node: diagUnitary_conjugate_block
/-- If [every product-map operator formed from A, U, and V has norm at most S₀
squared](hyp:hb), then, for a bounded operator X on the scalar product-group
Hilbert space, [the row-x, column-y block of its amplification multiplied on the
left by the diagonal operator and on the right by its adjoint equals the scalar
matrix entry of X at x and y times the product-map operator at x multiplied by
the adjoint product-map operator at y](goal). -/
lemma diagUnitary_conjugate_block (A : LaurentData) (U V : D →L[ℂ] D)
    (hb : ∀ x : ProdGrp, ‖prodMap A U V x‖ ≤ S0 ^ 2)
    (X : Ssp →L[ℂ] Ssp) (x y : ProdGrp) :
    hspBlock (diagUnitary A U V hb * amplify X * star (diagUnitary A U V hb)) x y =
      (X (prodBasis y) x) • (prodMap A U V x * star (prodMap A U V y)) := by
  apply ContinuousLinearMap.ext
  intro v
  rw [hspBlock_apply]
  simp only [mul_apply_eq_comp, diagUnitary_star_single]
  change prodMap A U V x (amplify X
    (lp.single 2 y (star (prodMap A U V y) v)) x) = _
  rw [(amplify_spec X).1, map_smul]
  rfl

-- @node: def:algebras
/-- For [a complex Hilbert space D](hyp:D), [operator-valued Laurent coefficients A](hyp:A),
[operators U and V on D](hyp:U,V), and [a uniform bound of S₀ squared on the norms
of their product-map operators](hyp:hb), the [source von Neumann algebra](goal)
is the double commutant of the amplified left regular operators multiplied on
the left by the diagonal operator and on the right by its adjoint.

The theorem sourceAlg_carrier identifies this with the full amplified source algebra in the paper. -/
noncomputable def sourceAlg (A : LaurentData) (U V : D →L[ℂ] D)
    (hb : ∀ x : ProdGrp, ‖prodMap A U V x‖ ≤ S0 ^ 2) : VonNeumannAlgebra (Hsp D) :=
  (commutantVN (Set.range (fun g : ProdGrp =>
    diagUnitary A U V hb * lamAmp g * star (diagUnitary A U V hb)))).commutant -- @realizes M(conjugated amplified group algebra)
/-- For [a complex Hilbert space D](hyp:D), the [target von Neumann algebra](goal)
is the commutant of the amplified right regular representation of the product group on H. -/
noncomputable def targetAlg : VonNeumannAlgebra (Hsp D) :=
  commutantVN (Set.range (rhoAmp (D := D))) -- @realizes N(commutant of amplified right regular representation)

-- @node: rhoAmp_star
/-- For any product-group element g, [the adjoint of the amplified right regular
operator at g is the amplified right regular operator at the inverse of g](goal). -/
lemma rhoAmp_star (g : ProdGrp) :
    star (rhoAmp (D := D) g) = rhoAmp (D := D) g⁻¹ := by
  unfold rhoAmp
  rw [lpReindex_star]
  congr 1
  ext x <;> simp

-- @node: rhoAmp_range_star
/-- [Taking adjoints leaves the set of amplified right regular operators
unchanged](goal). -/
lemma rhoAmp_range_star :
    star (Set.range (rhoAmp (D := D))) = Set.range (rhoAmp (D := D)) := by
  ext T
  change star T ∈ Set.range (rhoAmp (D := D)) ↔ T ∈ Set.range (rhoAmp (D := D))
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g⁻¹, ?_⟩
    rw [← rhoAmp_star, hg, star_star]
  · rintro ⟨g, hg⟩
    exact ⟨g⁻¹, by rw [← rhoAmp_star, hg]⟩

-- @node: targetAlg_carrier
/-- [The operators belonging to the target von Neumann algebra are exactly those
that commute with every amplified right regular operator](goal). -/
lemma targetAlg_carrier :
    (targetAlg (D := D) : Set (Hsp D →L[ℂ] Hsp D)) =
      commutant (Set.range (rhoAmp (D := D))) := by
  change (StarSubalgebra.centralizer ℂ (Set.range (rhoAmp (D := D))) : Set (Hsp D →L[ℂ] Hsp D)) = _
  rw [StarSubalgebra.coe_centralizer, rhoAmp_range_star, Set.union_self]

/-- For [an ordered quadruple q of integers](hyp:q), the [near-inclusion weight
of q](goal) is the product of the four coefficient weights, multiplied by the
absolute difference between the second and third integers and by the absolute
value of the fourth integer. -/
noncomputable def nearWeight (q : ℤ × ℤ × ℤ × ℤ) : ℝ :=
  cWeight q.1 * cWeight q.2.1 * cWeight q.2.2.1 * cWeight q.2.2.2 *
    ((q.2.1 - q.2.2.1).natAbs : ℝ) * (q.2.2.2.natAbs : ℝ)
/-- The [universal near-inclusion constant C](goal) is the sum of the
near-inclusion weights over all ordered quadruples of integers. -/
noncomputable def nearC : ℝ := ∑' q : ℤ × ℤ × ℤ × ℤ, nearWeight q -- @realizes C(universal fourfold sum)


end Papers.OaiNearInclusionsVon

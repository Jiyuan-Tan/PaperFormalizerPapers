module

public import Papers.OaiNearInclusionsVon.ReusedTree.Helpers.OperatorMaps
public import Mathlib.Algebra.Star.Subalgebra
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Topology.Algebra.StarSubalgebra
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.GroupTheory.FreeGroup.Reduce
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Close separable C*-algebras: definitions and standing conventions

All algebras are concrete unital star subalgebras of bounded operators; norm closure is
recorded separately. Hilbert direct sums are ℓ² spaces. Tensor operator norms are computed
on the dense algebraic Hilbert tensor product, with its canonical inner product.
-/

@[expose] public section

noncomputable section

open Filter Topology
open scoped BigOperators InnerProductSpace TensorProduct

namespace Papers.OaiNearInclusionsVon.ReusedTree
variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

/-- For [a complex normed space V](hyp:V), [the bounded operators on V](goal) are
the continuous complex-linear maps from V to itself. -/
abbrev Op (V : Type*) [NormedAddCommGroup V] [NormedSpace ℂ V] := V →L[ℂ] V

/-- For [a normed additive space L](hyp:L), [its countable square-summable sum](goal)
consists of sequences in L whose squared norms have finite sum. -/
abbrev SumSpace (L : Type*) [NormedAddCommGroup L] := lp (fun _ : ℕ => L) 2
/-- For [a complex inner product space V](hyp:V), [the Hilbert space convention](goal)
requires V to be complete. -/
def ComplexHilbertConvention (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] : Prop := CompleteSpace V
/-- For [a unital star subalgebra A](hyp:A) of bounded operators on
[the complex Hilbert space L](hyp:L), [the identity convention](goal) says that A contains
the identity operator.
@realizes \id_L(the ambient identity belongs to each unital star subalgebra)
@realizes \id_H(the same convention on the direct-sum space) -/
def UnitalIdentityConvention (A : StarSubalgebra ℂ (Op L)) : Prop := (1 : Op L) ∈ A
/-- For [a unital star subalgebra A](hyp:A) acting on [the complex Hilbert space L](hyp:L),
[its unit ball](goal) consists of the operators in A with norm at most one.
@realizes A_1(closed operator-norm unit ball of A)
@realizes B_1(the same construction applied to B) -/
def unitBall (A : StarSubalgebra ℂ (Op L)) : Set (Op L) := {a | a ∈ A ∧ ‖a‖ ≤ 1}
/-- For [a unital star subalgebra A](hyp:A) and [a unital star subalgebra B](hyp:B)
acting on [the complex Hilbert space L](hyp:L), [their Kadison–Kastler distance](goal)
is the Hausdorff distance between their operator-norm unit balls.
@realizes \KK(Hausdorff distance of the nonempty bounded closed unit balls) -/
def kkDist (A B : StarSubalgebra ℂ (Op L)) : ℝ :=
  Metric.hausdorffDist (unitBall A) (unitBall B)
/-- For [a set D of bounded operators](hyp:D) on [the complex Hilbert space L](hyp:L),
[its commutant](goal) consists of all bounded operators commuting with every member of D.
@realizes D'(all bounded operators commuting with the given set) -/
def commutant (D : Set (Op L)) : Set (Op L) := Set.centralizer D

/-- For [a bounded operator U](hyp:U) and [a set X of bounded operators](hyp:X) on
[the complex Hilbert space L](hyp:L), [the conjugated set](goal) consists of all products
U x U* with x in X. -/
def conjSet (U : Op L) (X : Set (Op L)) : Set (Op L) :=
  (fun x => U * x * star U) '' X
/-- For [a unitary operator U](hyp:U) and [a unital star subalgebra P](hyp:P) on
[the complex Hilbert space L](hyp:L), [the conjugated algebra](goal) consists of all
operators U p U* with p in P. -/
def conjAlg (U : unitary (Op L)) (P : StarSubalgebra ℂ (Op L)) :
    StarSubalgebra ℂ (Op L) where
  carrier := conjSet (U : Op L) P
  zero_mem' := by
    exact ⟨0, P.zero_mem, by simp⟩
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x + y, P.add_mem hx hy, by simp [mul_add, add_mul]⟩
  one_mem' := by
    exact ⟨1, P.one_mem, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    refine ⟨x * y, P.mul_mem hx hy, ?_⟩
    simp only [mul_assoc, ← mul_assoc (star (U : Op L)) (U : Op L),
      Unitary.star_mul_self_of_mem U.prop, one_mul]
  algebraMap_mem' := by
    intro c
    refine ⟨algebraMap ℂ (Op L) c, P.algebraMap_mem c, ?_⟩
    change (U : Op L) * algebraMap ℂ (Op L) c * star (U : Op L) = _
    rw [(Algebra.commutes c (U : Op L)).symm, mul_assoc,
      Unitary.mul_star_self_of_mem U.prop, mul_one]
  star_mem' := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨star x, star_mem hx, by simp [star_mul, mul_assoc]⟩
/-- For [a complex inner product space L](hyp:L), [the sequence-space assumptions](goal)
require [L to be nonzero](step:1) and [L to be separable](step:2). -/
def SequencesL (L : Type*) [NormedAddCommGroup L] [InnerProductSpace ℂ L] : Prop :=
  Nontrivial L ∧
  TopologicalSpace.SeparableSpace L
/-- For [a unital star subalgebra D](hyp:D) acting on [the complex Hilbert space L](hyp:L),
[the ambient-algebra assumptions](goal) require [D to be closed in operator norm](step:1)
and [D to be separable in operator norm](step:2). -/
def SequencesD
    (D : StarSubalgebra ℂ (Op L)) : Prop :=
  IsClosed (D : Set (Op L)) ∧
  TopologicalSpace.IsSeparable (D : Set (Op L))
/-- For [a unital star subalgebra D](hyp:D) on [the complex Hilbert space L](hyp:L),
[the scalar-center condition](goal) says that every element of D commuting with all of D
is a scalar multiple of the identity.
@realizes Z(D)(relative center equals the scalar identities) -/
def SequencesCenter (D : StarSubalgebra ℂ (Op L)) : Prop :=
  ∀ x ∈ D, (∀ y ∈ D, x * y = y * x) → ∃ c : ℂ, x = c • (1 : Op L)
/-- For [unital star subalgebras D](hyp:D), [P](hyp:P), and [Q](hyp:Q) on
[the complex Hilbert space L](hyp:L), [the subalgebra assumptions](goal) require
[P to be contained in D](step:1), [Q to be contained in D](step:2),
[P to be closed in operator norm](step:3), and [Q to be closed in operator norm](step:4). -/
def SequencesSubalgebras (D : StarSubalgebra ℂ (Op L))
    (P : StarSubalgebra ℂ (Op L))
    (Q : StarSubalgebra ℂ (Op L)) : Prop :=
  P ≤ D ∧
  Q ≤ D ∧
  IsClosed (P : Set (Op L)) ∧
  IsClosed (Q : Set (Op L))
/-- For [a unital star subalgebra D](hyp:D) and [a unital star subalgebra P](hyp:P) on
[the complex Hilbert space L](hyp:L), [the sequence algebra](goal) consists of diagonal
operators on the countable square-summable sum of L whose diagonal entries lie in D
and converge in operator norm to an element of P.
@realizes \E_D(P)(diagonal sequences in D converging in norm to a point of P)
@realizes \E_D(Q)(the same construction with limit algebra Q) -/
def seqAlg (D P : StarSubalgebra ℂ (Op L)) : StarSubalgebra ℂ (Op (SumSpace L)) where
  carrier := {T | ∃ x : ℕ → Op L, (∀ n, x n ∈ D) ∧
    (∃ p ∈ P, Tendsto x atTop (𝓝 p)) ∧ ∀ v n, (T v) n = x n (v n)}
  zero_mem' := by
    refine ⟨fun _ => 0, fun _ => D.zero_mem, ⟨0, P.zero_mem, tendsto_const_nhds⟩, ?_⟩
    intro v n
    rfl
  add_mem' := by
    rintro T S ⟨x, hx, ⟨p, hp, hxp⟩, hT⟩ ⟨y, hy, ⟨q, hq, hyq⟩, hS⟩
    refine ⟨fun n => x n + y n, fun n => D.add_mem (hx n) (hy n),
      ⟨p + q, P.add_mem hp hq, hxp.add hyq⟩, ?_⟩
    intro v n
    change (T v + S v) n = _
    simp only [lp.coeFn_add, Pi.add_apply, hT, hS, ContinuousLinearMap.add_apply]
  one_mem' := by
    refine ⟨fun _ => 1, fun _ => D.one_mem, ⟨1, P.one_mem, tendsto_const_nhds⟩, ?_⟩
    intro v n
    rfl
  mul_mem' := by
    rintro T S ⟨x, hx, ⟨p, hp, hxp⟩, hT⟩ ⟨y, hy, ⟨q, hq, hyq⟩, hS⟩
    refine ⟨fun n => x n * y n, fun n => D.mul_mem (hx n) (hy n),
      ⟨p * q, P.mul_mem hp hq, hxp.mul hyq⟩, ?_⟩
    intro v n
    change (T (S v)) n = x n (y n (v n))
    rw [hT, hS]
  algebraMap_mem' := by
    intro c
    refine ⟨fun _ => algebraMap ℂ (Op L) c, fun _ => D.algebraMap_mem c,
      ⟨algebraMap ℂ (Op L) c, P.algebraMap_mem c, tendsto_const_nhds⟩, ?_⟩
    intro v n
    rfl
  star_mem' := by
    rintro T ⟨x, hx, ⟨p, hp, hxp⟩, hT⟩
    exact ⟨fun n => star (x n), fun n => star_mem (hx n),
      ⟨star p, star_mem hp, hxp.star⟩, diagonal_star_apply T x hT⟩
/-- For [unital star subalgebras D](hyp:D), [P](hyp:P), and [Q](hyp:Q) on
[the complex Hilbert space L](hyp:L), [the sequence-conjugacy condition](goal) says
that a unitary on the countable square-summable sum of L conjugates the sequence algebra
with entries in D and limits in P onto the one with entries in D and limits in Q. -/
def SequencesConjugacy (D P Q : StarSubalgebra ℂ (Op L)) : Prop :=
  ∃ S ∈ unitary (Op (SumSpace L)), conjSet S (seqAlg D P) = (seqAlg D Q : Set _)
/-- For [a bounded operator b](hyp:b), [a sequence U of unitary operators](hyp:U), and
[a fixed bounded operator p](hyp:p) on [the complex Hilbert space L](hyp:L),
[pointwise approximation](goal) means that the norm of b minus Uₙ p Uₙ* tends to zero. -/
def PointwiseNormalizerApprox
    (b : Op L)
    (U : ℕ → unitary (Op L))
    (p : Op L) : Prop :=
  Tendsto (fun n => ‖b - (U n : Op L) * p * star (U n : Op L)‖) atTop (𝓝 0)
/-- For [unital star subalgebras D](hyp:D), [P](hyp:P), and [Q](hyp:Q) on
[the complex Hilbert space L](hyp:L), [the invariant-algebra assumptions](goal) require
[D to be norm closed](step:1), [P to be norm closed](step:2), [Q to be norm closed](step:3),
[P to be contained in D](step:4), and [Q to be contained in D](step:5). -/
def InvariantUnital (D P Q : StarSubalgebra ℂ (Op L)) : Prop :=
  IsClosed (D : Set (Op L)) ∧ IsClosed (P : Set (Op L)) ∧
    IsClosed (Q : Set (Op L)) ∧ P ≤ D ∧ Q ≤ D
/-- For [unital star subalgebras D](hyp:D), [P](hyp:P), and [Q](hyp:Q), and
[a sequence U of unitary operators](hyp:U) on [the complex Hilbert space L](hyp:L),
[the invariant approximation condition](goal) requires [every Uₙ to conjugate D onto itself](step:1)
and [each b in Q to admit a fixed p in P such that Uₙ p Uₙ* converges in norm to b](step:2). -/
def InvariantApproximation (D P Q : StarSubalgebra ℂ (Op L))
    (U : ℕ → unitary (Op L)) : Prop :=
  (∀ n, conjSet (U n : Op L) D = (D : Set _)) ∧
  ∀ b ∈ Q, ∃ p ∈ P, PointwiseNormalizerApprox b U p

/-- For [a finite family p of bounded operators](hyp:p) and [an equally indexed family z](hyp:z)
on [the complex Hilbert space L](hyp:L), [the spatial norm of their tensor sum](goal)
is the supremum of the norms of its values on vectors of norm at most one in the
algebraic Hilbert tensor product of L with itself. -/
def tensorSumNorm {m : ℕ} (p z : Fin m → Op L) : ℝ :=
  sSup ((fun x : TensorProduct ℂ L L =>
    ‖(∑ i, TensorProduct.map (p i).toLinearMap (z i).toLinearMap) x‖) ''
      {x | ‖x‖ ≤ 1})
/-- For [a complex inner product space L](hyp:L), [the spatial tensor convention](goal)
requires every finite sum of tensor products of bounded operators on L to admit a continuous
linear operator on the algebraic Hilbert tensor product that [agrees with the tensor sum
on every vector](step:1) and [has operator norm equal to the supremum computed on its
unit ball](step:2). -/
def SpatialTensorConvention (L : Type*) [NormedAddCommGroup L]
    [InnerProductSpace ℂ L] : Prop :=
  ∀ (m : ℕ) (p z : Fin m → Op L),
    ∃ T : TensorProduct ℂ L L →L[ℂ] TensorProduct ℂ L L,
      (∀ x, T x = (∑ i, TensorProduct.map (p i).toLinearMap (z i).toLinearMap) x) ∧
        ‖T‖ = tensorSumNorm p z
/-- For [a unital star subalgebra D](hyp:D) and [a unital star subalgebra P](hyp:P)
on [the complex Hilbert space L](hyp:L), [the spatial tensor identity](goal) says that,
for every nonempty finite family of operators from P and equally indexed family from
the commutant of D, the norm of the sum of their products equals the spatial norm
of the corresponding tensor sum. -/
def HasSpatialTensorIdentity (D P : StarSubalgebra ℂ (Op L)) : Prop :=
  ∀ m : ℕ, 0 < m → ∀ p z : Fin m → Op L,
    (∀ i, p i ∈ P) → (∀ i, z i ∈ commutant D) →
      ‖∑ i, p i * z i‖ = tensorSumNorm p z
/-- For [unital star subalgebras D](hyp:D), [P](hyp:P), and [Q](hyp:Q) on
[the complex Hilbert space L](hyp:L), [the tensor distinction condition](goal) requires
[P to satisfy the spatial tensor identity relative to D](step:1) and
[Q to fail that identity relative to D](step:2). -/
def ObstructionTensorDistinction (D P Q : StarSubalgebra ℂ (Op L)) : Prop :=
  HasSpatialTensorIdentity D P ∧ ¬ HasSpatialTensorIdentity D Q
/-- For [unital star subalgebras P](hyp:P) and [Q](hyp:Q), and [a bounded operator W](hyp:W)
on [the complex Hilbert space L](hyp:L), [the conjugating-unitary condition](goal)
requires [W to be unitary](step:1) and [conjugation by W to map P onto Q](step:2). -/
def ObstructionUnitary (P Q : StarSubalgebra ℂ (Op L))
    (W : Op L) : Prop :=
  W ∈ unitary (Op L) ∧
  conjSet W P = (Q : Set _)
/-- [The group G](goal) is the free group on countably many generators indexed by
the natural numbers.
@realizes G(free group on countably many generators) -/
abbrev FG := FreeGroup ℕ

/-- For [a natural-number index i](hyp:i), [the corresponding free generator](goal)
is the generator of G indexed by i, starting with index zero.
@realizes s_i(free generators, reindexed from zero) -/
abbrev gen (i : ℕ) : FG := FreeGroup.of i

/-- [The group identity](goal) is the identity element of the countably generated free group G.
@realizes e(identity of the free group) -/
abbrev groupIdentity : FG := 1

/-- [The Hilbert space K](goal) consists of square-summable complex-valued functions
on the countably generated free group G.
@realizes K(complex square-summable functions on G) -/
abbrev KSp := lp (fun _ : FG => ℂ) 2

/-- For [a group element x](hyp:x), [the coordinate vector at x](goal) is the
square-summable function on G equal to one at x and zero elsewhere.
@realizes \delta_x(usual coordinate orthonormal basis vector) -/
def delta (x : FG) : KSp := lp.single 2 x 1

/-- [The identity operator on K](goal) leaves every square-summable complex-valued
function on G unchanged.
@realizes \id_K(identity bounded operator on K) -/
def idK : Op KSp := 1
variable {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]
/-- For [a complex inner product space J](hyp:J), [the representation-space condition](goal)
requires J to be nonzero.
@realizes J(nonzero representation space) -/
def AbsorptionRepresentation (J : Type*) [NormedAddCommGroup J]
    [InnerProductSpace ℂ J] : Prop := Nontrivial J

/-- On [the complex Hilbert space J](hyp:J), [the identity operator](goal) leaves
every vector unchanged.
@realizes \id_J(identity bounded operator on J) -/
def idJ : Op J := 1
/-- For [a real deformation parameter t](hyp:t), [the deformation range condition](goal)
requires [t to be strictly positive](step:1) and [t to be strictly less than one](step:2). -/
def DeformationRange (t : ℝ) : Prop :=
  0 < t ∧ t < 1
/-- For [a group element g](hyp:g) and [a complex Hilbert space J](hyp:J),
[the left-shift operator](goal) on square-summable J-valued functions on G sends
a function f to the function whose value at x is f evaluated at g⁻¹x. -/
def shiftOp (g : FG) : Op (lp (fun _ : FG => J) 2) :=
  reindexOp { toFun := fun x => g⁻¹ * x
              invFun := fun x => g * x
              left_inv := by intro x; simp
              right_inv := by intro x; simp }
/-- [The left regular unitary representation](goal) of G on K sends each group element g
to the operator taking a function f to the function whose value at x is f evaluated at g⁻¹x.
@realizes \lambda(left regular unitary representation, f(x) ↦ f(g⁻¹x)) -/
def leftReg : FG →* unitary (Op KSp) where
  toFun g := ⟨shiftOp g, reindexOp_mem_unitary _⟩
  map_one' := by
    apply Subtype.ext
    ext v x
    change v (1⁻¹ * x) = v x
    simp
  map_mul' g h := by
    apply Subtype.ext
    ext v x
    change v ((g * h)⁻¹ * x) = v (h⁻¹ * (g⁻¹ * x))
    simp [mul_assoc]
/-- [The right regular unitary representation](goal) of G on K sends each group element g
to the operator taking a function f to the function whose value at x is f evaluated at xg.
@realizes \rho(right regular unitary representation, f(x) ↦ f(xg)) -/
def rightReg : FG →* unitary (Op KSp) where
  toFun g := ⟨reindexOp
    { toFun := fun x => x * g
      invFun := fun x => x * g⁻¹
      left_inv := by intro x; simp [mul_assoc]
      right_inv := by intro x; simp [mul_assoc] }, reindexOp_mem_unitary _⟩
  map_one' := by
    apply Subtype.ext
    ext v x
    change v (x * 1) = v x
    simp
  map_mul' g h := by
    apply Subtype.ext
    ext v x
    change v (x * (g * h)) = v ((x * g) * h)
    rw [mul_assoc]
/-- [The zero-parameter representation](goal) is the left regular unitary representation
of G on K.
@realizes \pi_0(the zero-parameter representation is λ) -/
abbrev piZero : FG →* unitary (Op KSp) := leftReg

/-- For [a real parameter t](hyp:t) [strictly between zero and one](hyp:_ht),
[the scalar r](goal) is the nonnegative square root of one minus t squared.
@realizes r(the scalar √(1-t²); lies in (0,1) under DeformationRange) -/
def rValue (t : ℝ) (_ht : DeformationRange t) : ℝ := Real.sqrt (1 - t ^ 2)

/-- For [a real parameter t](hyp:t) [strictly between zero and one](hyp:ht),
[the perturbation bound](goal) is twice one minus the square root of one minus t squared,
plus t divided by one minus t, plus t.
@realizes c(t)(the uniform perturbation bound; positive for 0<t<1) -/
def cBound (t : ℝ) (ht : DeformationRange t) : ℝ :=
  2 * (1 - rValue t ht) + t / (1 - t) + t

/-- For [a real parameter t](hyp:t) [strictly between zero and one](hyp:ht) and
[a unitary representation π of G on K](hyp:π), [the tree representation condition](goal)
requires [the matrix coefficient of every free generator at the identity coordinate vector
to equal t](step:1) and [the operator-norm distance between π and the left regular
representation at every group element to be at most the perturbation bound at t](step:2). -/
def IsTreeRep (t : ℝ) (ht : DeformationRange t)
    (π : FG →* unitary (Op KSp)) : Prop :=
  (∀ i : ℕ, ⟪(π (gen i) : Op KSp) (delta 1), delta 1⟫_ℂ = (t : ℂ)) ∧
  ∀ g : FG, ‖(π g : Op KSp) - (leftReg g : Op KSp)‖ ≤ cBound t ht

/-- For [a unitary representation σ of G](hyp:σ) on [the complex Hilbert space J](hyp:J),
[the absorption operator](goal) acts on square-summable J-valued functions on G by applying
the representing unitary for x to the function's value at each coordinate x.
@realizes W_\sigma(diagonal action δ_x⊗v ↦ δ_x⊗σ(x)v) -/
def absorptionOp
    (σ : FG →* unitary (Op J)) : Op (lp (fun _ : FG => J) 2) :=
  diagUnitaryOp (fun x => σ x)

/-- [The Hilbert space L](goal) consists of square-summable K-valued functions on G,
realizing the tensor product of K with itself.
@realizes L(the concrete tensor product K⊗K realized as ℓ²(G;K)) -/
abbrev LSp := lp (fun _ : FG => KSp) 2

/-- [The flip operator on L](goal) exchanges the two K factors in the tensor product. -/
def flipOp : Op LSp := swapOp FG

/-- For [a unitary representation π of G on K](hyp:π) and [a group element g](hyp:g),
[the tensor-product operator at g](goal) applies the left regular action of g to the
first K factor and the action of π at g to the second K factor. -/
def Qop (π : FG →* unitary (Op KSp)) (g : FG) : Op LSp :=
  (shiftOp g).comp (diagUnitaryOp (fun _ : FG => π g))
/-- For [a unitary representation π of G on K](hyp:π),
[the tensor-product unitary representation on L](goal) sends each group element to
the tensor product of its left regular operator and its operator under π. -/
def tensorRep (π : FG →* unitary (Op KSp)) : FG →* unitary (Op LSp) where
  toFun g := ⟨Qop π g, by
    change shiftOp g * diagUnitaryOp (fun _ : FG => π g) ∈ unitary (Op LSp)
    exact mul_mem (reindexOp_mem_unitary _) (diagUnitaryOp_mem_unitary _)⟩
  map_one' := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro v
    apply lp.ext
    funext x
    change (π 1 : Op KSp) (v (1⁻¹ * x)) = v x
    simp
  map_mul' g h := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro v
    apply lp.ext
    funext x
    change (π (g * h) : Op KSp) (v ((g * h)⁻¹ * x)) =
      (π g : Op KSp) ((π h : Op KSp) (v (h⁻¹ * (g⁻¹ * x))))
    simp [mul_assoc]

/-- For [a real parameter t](hyp:t), [a unitary representation π of G on K](hyp:π),
and [a real index a equal to zero or t](hyp:a), [the indexed representation](goal)
is [the left regular representation when a is zero](step:1) and
[π otherwise](step:2). -/
def indexedRep (t : ℝ) (π : FG →* unitary (Op KSp))
    (a : {a : ℝ // a = 0 ∨ a = t})
    : FG →* unitary (Op KSp) :=
  if a.val = 0 then piZero else π

/-- For [a real parameter t](hyp:t), [a unitary representation π of G on K](hyp:π),
and [a real index a equal to zero or t](hyp:a), [the indexed tensor representation](goal)
is the tensor product of the left regular representation with the indexed representation
that equals the left regular representation at zero and π otherwise.
@realizes Q_a(unitary representation λ⊗π_a on L for a∈{0,t}) -/
def Qindexed (t : ℝ) (π : FG →* unitary (Op KSp))
    (a : {a : ℝ // a = 0 ∨ a = t}) : FG →* unitary (Op LSp) :=
  tensorRep (indexedRep t π a)
/-- For [a unitary representation π of G on K](hyp:π), [the generated algebra P](goal)
is the norm-closed unital star algebra on L generated by the tensor products of the
left regular operator at g with the operator of π at g, over all group elements g.
@realizes P_0(Palg piZero)
@realizes P_t(Palg π for the representation π supplied by the tree lemma) -/
def Palg (π : FG →* unitary (Op KSp)) : StarSubalgebra ℂ (Op LSp) :=
  (StarAlgebra.adjoin ℂ (Set.range (Qop π))).topologicalClosure

/-- For [a real parameter t](hyp:t), [a unitary representation π of G on K](hyp:π),
and [a real index a equal to zero or t](hyp:a), [the indexed algebra P](goal) is the
norm-closed unital star algebra generated by the indexed tensor representation at a,
using the left regular representation at zero and π otherwise.
@realizes P_a(norm-closed unital star algebras generated by Q_a for a∈{0,t}, with π₀=λ) -/
def Pindexed (t : ℝ) (π : FG →* unitary (Op KSp))
    (a : {a : ℝ // a = 0 ∨ a = t}) : StarSubalgebra ℂ (Op LSp) :=
  Palg (indexedRep t π a)
/-- For [an output coordinate x in G](hyp:x) and [an input coordinate y in G](hyp:y),
[the coordinate matrix unit](goal) maps a function on G to its value at y times the
coordinate vector at x.
@realizes E_{xy}(rank-one coordinate operator f ↦ f(y)δ_x) -/
def matUnit (x y : FG) : Op KSp :=
  (lp.evalCLM ℂ (fun _ : FG => ℂ) 2 y).smulRight (delta x)
/-- For [a unitary representation π of G on K](hyp:π), [the algebra D](goal) is the
norm-closed unital star algebra on L generated by all left shifts of the outer G
coordinate and by the operators acting identically at every outer coordinate as a
left regular operator, an operator of π, or a coordinate matrix unit on K.
@realizes D(the norm-closed unital star algebra generated by the four stated families) -/
def Dalg (π : FG →* unitary (Op KSp)) : StarSubalgebra ℂ (Op LSp) :=
  (StarAlgebra.adjoin ℂ
    (Set.range (fun g : FG => (shiftOp g : Op LSp)) ∪
      Set.range (fun g => (constantDiagOp (piZero g : Op KSp) : Op LSp)) ∪
      Set.range (fun g => (constantDiagOp (π g : Op KSp) : Op LSp)) ∪
      Set.range (fun xy : FG × FG =>
        (constantDiagOp (matUnit xy.1 xy.2) : Op LSp)))).topologicalClosure

end Papers.OaiNearInclusionsVon.ReusedTree

module

public import Papers.OaiNearInclusionsVon.Helpers.Corner
public import Mathlib.Algebra.Star.UnitaryStarAlgAut

/-! Commutation across adjoints survives identification and restriction of a finite corner. -/

public section

namespace Papers.OaiNearInclusionsVon

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- If [E is self-adjoint](hyp:hE), [P is self-adjoint](hyp:hP), and
[J intertwines E with P](hyp:hJE), then [pulling the compression of T by P back
through J equals compressing the pullback of T by E](goal). -/
-- @node: corner_conjugate_compression
lemma corner_conjugate_compression (E P J T : K →L[ℂ] K)
    (hE : IsSelfAdjoint E) (hP : IsSelfAdjoint P)
    (hJE : J * E = P * J) :
    star J * (P * T * P) * J = E * (star J * T * J) * E := by
  have hEJ : E * star J = star J * P := by
    simpa only [star_mul, hE.star_eq, hP.star_eq] using congrArg star hJE
  calc
    star J * (P * T * P) * J = (star J * P) * T * (P * J) := by
      simp only [mul_assoc]
    _ = (E * star J) * T * (J * E) := by rw [← hEJ, ← hJE]
    _ = E * (star J * T * J) * E := by simp only [mul_assoc]

/-- If [J is unitary](hyp:hJ) and [A and B commute](hyp:hAB), then
[their conjugates by the adjoint of J commute](goal). -/
-- @node: corner_unitary_conjugate_commute
lemma corner_unitary_conjugate_commute (J A B : K →L[ℂ] K)
    (hJ : J ∈ unitary _) (hAB : Commute A B) :
    Commute (star J * A * J) (star J * B * J) := by
  simpa only [Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_star] using
    hAB.map (Unitary.conjStarAlgAut ℂ _ ⟨star J, Unitary.star_mem hJ⟩)

/-- Suppose [the two algebras commute element by element](hyp:hA),
[Q₁ and Q₂ are orthogonal projections](hyp:hQ₁,hQ₂),
[Q₁ belongs to the first algebra](hyp:hQ₁A), [Q₂ belongs to the second](hyp:hQ₂A),
[T₁ belongs to the first](hyp:hT₁A), and [T₂ belongs to the second](hyp:hT₂A).
If [E is an orthogonal projection](hyp:hE), [J is unitary](hyp:hJ), and
[J intertwines E with the product of Q₁ and Q₂](hyp:hJE), then
[the conjugates of T₁ and T₂ compressed by E commute, and the first also
commutes with the adjoint of the second](goal). -/
-- @node: corner_transferred_compressions_commute
lemma corner_transferred_compressions_commute
    (A₁ A₂ : VonNeumannAlgebra K)
    (hA : ∀ x ∈ A₁, ∀ y ∈ A₂, Commute x y)
    (Q₁ Q₂ T₁ T₂ E J : K →L[ℂ] K)
    (hQ₁ : IsStarProjection Q₁) (hQ₂ : IsStarProjection Q₂)
    (hQ₁A : Q₁ ∈ A₁) (hQ₂A : Q₂ ∈ A₂)
    (hT₁A : T₁ ∈ A₁) (hT₂A : T₂ ∈ A₂)
    (hE : IsStarProjection E) (hJ : J ∈ unitary _)
    (hJE : J * E = (Q₁ * Q₂) * J) :
    Commute (E * (star J * T₁ * J) * E) (E * (star J * T₂ * J) * E) ∧
    Commute (E * (star J * T₁ * J) * E) (star (E * (star J * T₂ * J) * E)) := by
  have hP := hQ₁.mul hQ₂ (hA Q₁ hQ₁A Q₂ hQ₂A)
  have hc := corner_algebra_compressions_commute A₁ A₂ hA Q₁ Q₂ T₁ T₂
    hQ₁ hQ₂ hQ₁A hQ₂A hT₁A hT₂A
  have hs := corner_algebra_compressions_star_commute A₁ A₂ hA Q₁ Q₂ T₁ T₂
    hQ₁ hQ₂ hQ₁A hQ₂A hT₁A hT₂A
  have ht (T : K →L[ℂ] K) :=
    corner_conjugate_compression E (Q₁ * Q₂) J T hE.isSelfAdjoint hP.isSelfAdjoint hJE
  constructor
  · simpa only [ht] using corner_unitary_conjugate_commute J _ _ hJ hc
  · have hh := corner_unitary_conjugate_commute J _ _ hJ hs
    have hstar (X : K →L[ℂ] K) : star J * star X * J = star (star J * X * J) := by
      simp only [star_mul, star_star, mul_assoc]
    simpa only [hstar, ht] using hh

variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℂ (H n)] [∀ n, CompleteSpace (H n)]

/-- For [operator sequences E₁ and E₂](hyp:E₁,E₂), if
[E₁ and E₂ are commuting orthogonal projections at every index](hyp:hE),
[their product fixes every vector in its range](goal). -/
-- @node: cornerProj_apply_range
lemma cornerProj_apply_range (E₁ E₂ : ∀ n, H n →L[ℂ] H n)
    (hE : CornerProjections E₁ E₂) (n : ℕ) (x : cornerRange E₁ E₂ n) :
    cornerProj E₁ E₂ n x = x := by
  obtain ⟨y, hy⟩ := x.property
  change cornerProj E₁ E₂ n y = (x : H n) at hy
  rw [← hy]
  exact congrArg (fun T : H n →L[ℂ] H n => T y)
    ((hE n).1.mul (hE n).2.1 (hE n).2.2).isIdempotentElem.eq

/-- For [operator sequences E₁ and E₂ defining a product range](hyp:E₁,E₂)
and [operator sequences T and S](hyp:T,S), [the product of their compressed
restrictions equals the compressed restriction of the operator obtained by
applying S, then the product of E₁ and E₂, then T](goal). -/
-- @node: cornerRestrict_mul_compressed
lemma cornerRestrict_mul_compressed (E₁ E₂ T S : ∀ n, H n →L[ℂ] H n)
    (n : ℕ) :
    cornerRestrict E₁ E₂ T n * cornerRestrict E₁ E₂ S n =
      cornerRestrict E₁ E₂
        (fun m => T m * cornerProj E₁ E₂ m * S m) n := by
  ext x
  rfl

/-- For [operator sequences E₁ and E₂](hyp:E₁,E₂) and
[operator sequences T and S](hyp:T,S), suppose [E₁ and E₂ are commuting
orthogonal projections at every index](hyp:hE). If [the ambient compressions
of T and S by their product commute at the chosen index](hyp:hc), then
[their compressed restrictions to the common range commute](goal). -/
-- @node: cornerRestrict_commute_of_compressions
lemma cornerRestrict_commute_of_compressions (E₁ E₂ T S : ∀ n, H n →L[ℂ] H n)
    (hE : CornerProjections E₁ E₂) (n : ℕ)
    (hc : Commute (cornerProj E₁ E₂ n * T n * cornerProj E₁ E₂ n)
      (cornerProj E₁ E₂ n * S n * cornerProj E₁ E₂ n)) :
    Commute (cornerRestrict E₁ E₂ T n) (cornerRestrict E₁ E₂ S n) := by
  let P := cornerProj E₁ E₂ n
  have hP : P * P = P := ((hE n).1.mul (hE n).2.1 (hE n).2.2).isIdempotentElem.eq
  have heq : P * T n * P * S n * P = P * S n * P * T n * P := by
    have hh := hc.eq
    change (P * T n * P) * (P * S n * P) =
      (P * S n * P) * (P * T n * P) at hh
    simpa only [mul_assoc, ← mul_assoc P P, hP] using hh
  change cornerRestrict E₁ E₂ T n * cornerRestrict E₁ E₂ S n =
    cornerRestrict E₁ E₂ S n * cornerRestrict E₁ E₂ T n
  ext x
  have hx : P (x : H n) = x := cornerProj_apply_range E₁ E₂ hE n x
  have hh := congrArg (fun A : H n →L[ℂ] H n => A (x : H n)) heq
  change P (T n (P (S n (x : H n)))) = P (S n (P (T n (x : H n))))
  simpa only [mul_apply_eq_comp, hx] using hh

/-- For [operator sequences E₁ and E₂](hyp:E₁,E₂) and
[an operator sequence T](hyp:T), if [E₁ and E₂ are commuting orthogonal
projections at every index](hyp:hE), then [on a complete common range,
the adjoint of the compressed restriction of T equals the compressed
restriction of its adjoint](goal). -/
-- @node: cornerRestrict_star
lemma cornerRestrict_star (E₁ E₂ T : ∀ n, H n →L[ℂ] H n)
    (hE : CornerProjections E₁ E₂) (n : ℕ)
    [CompleteSpace (cornerRange E₁ E₂ n)] :
    star (cornerRestrict E₁ E₂ T n) =
      cornerRestrict E₁ E₂ (fun m => star (T m)) n := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  change inner ℂ (x : H n) (cornerProj E₁ E₂ n (T n y)) =
    inner ℂ (cornerProj E₁ E₂ n (star (T n) x)) (y : H n)
  have hs (a b : H n) :
      inner ℂ (cornerProj E₁ E₂ n a) b = inner ℂ a (cornerProj E₁ E₂ n b) :=
    ((hE n).1.mul (hE n).2.1 (hE n).2.2).isSelfAdjoint.isSymmetric a b
  rw [← hs, cornerProj_apply_range E₁ E₂ hE n x,
    hs, cornerProj_apply_range E₁ E₂ hE n y,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]

/-- For [corner operators E₁ and E₂](hyp:E₁,E₂), [projection candidates Q₁ and Q₂](hyp:Q₁,Q₂),
[operators T₁ and T₂](hyp:T₁,T₂), [identifying operators J](hyp:J), and
[two sequences of von Neumann algebras](hyp:A₁,A₂), suppose
[E₁ and E₂ are commuting orthogonal projections](hyp:hE) and
[the two algebras commute element by element](hyp:hA).
At an index with complete common range, assume [Q₁ is an orthogonal projection](hyp:hQ₁),
[Q₂ is an orthogonal projection](hyp:hQ₂), [Q₁ belongs to the first algebra](hyp:hQ₁A),
[Q₂ belongs to the second](hyp:hQ₂A), [T₁ belongs to the first](hyp:hT₁A),
[T₂ belongs to the second](hyp:hT₂A), [J is unitary](hyp:hJ), and
[J intertwines the common projection with the product of Q₁ and Q₂](hyp:hJE).
Then [the conjugated operators restricted to the common range commute,
and the first also commutes with the adjoint of the second](goal). -/
-- @node: cornerRestrict_transferred_commute
lemma cornerRestrict_transferred_commute
    (E₁ E₂ Q₁ Q₂ T₁ T₂ J : ∀ n, H n →L[ℂ] H n)
    (A₁ A₂ : ∀ n, VonNeumannAlgebra (H n))
    (hE : CornerProjections E₁ E₂) (hA : CornerAlgebras A₁ A₂)
    (n : ℕ) [CompleteSpace (cornerRange E₁ E₂ n)]
    (hQ₁ : IsStarProjection (Q₁ n)) (hQ₂ : IsStarProjection (Q₂ n))
    (hQ₁A : Q₁ n ∈ A₁ n) (hQ₂A : Q₂ n ∈ A₂ n)
    (hT₁A : T₁ n ∈ A₁ n) (hT₂A : T₂ n ∈ A₂ n)
    (hJ : J n ∈ unitary _)
    (hJE : J n * cornerProj E₁ E₂ n = (Q₁ n * Q₂ n) * J n) :
    let C₁ := cornerRestrict E₁ E₂ (fun m => star (J m) * T₁ m * J m) n
    let C₂ := cornerRestrict E₁ E₂ (fun m => star (J m) * T₂ m * J m) n
    Commute C₁ C₂ ∧ Commute C₁ (star C₂) := by
  have hP : IsStarProjection (cornerProj E₁ E₂ n) :=
    (hE n).1.mul (hE n).2.1 (hE n).2.2
  have hc := corner_transferred_compressions_commute (A₁ n) (A₂ n) (hA n)
    (Q₁ n) (Q₂ n) (T₁ n) (T₂ n) (cornerProj E₁ E₂ n) (J n)
    hQ₁ hQ₂ hQ₁A hQ₂A hT₁A hT₂A hP hJ hJE
  constructor
  · exact cornerRestrict_commute_of_compressions E₁ E₂ _ _ hE n hc.1
  · rw [cornerRestrict_star E₁ E₂ _ hE n]
    apply cornerRestrict_commute_of_compressions E₁ E₂ _ _ hE n
    simpa only [star_mul, hP.isSelfAdjoint.star_eq, star_star, mul_assoc] using hc.2

end Papers.OaiNearInclusionsVon

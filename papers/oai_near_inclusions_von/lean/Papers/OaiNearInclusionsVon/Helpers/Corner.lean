module

public import Papers.OaiNearInclusionsVon.Helpers.Gap
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-! Finite common corners of commuting projections and their unitary approximants. -/

@[expose] public section

set_option linter.style.longLine false

namespace Papers.OaiNearInclusionsVon


open Filter
open scoped Topology

-- @env: S5
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℂ (H n)] [∀ n, CompleteSpace (H n)] -- @realizes H_n(arbitrary complex Hilbert spaces; no separability restriction)

-- @node: ass:corner-projections
/-- For [a sequence of complex Hilbert spaces](hyp:H) and [operator sequences E₁ and E₂](hyp:E₁,E₂), [the common-corner projection condition](goal) requires, at each index, [E₁ to be an orthogonal projection](step:1), [E₂ to be an orthogonal projection](step:2), and [the two projections to commute](step:3). -/
noncomputable def CornerProjections (E₁ E₂ : ∀ n, H n →L[ℂ] H n) : Prop :=
  ∀ n, IsStarProjection (E₁ n) ∧ -- @realizes E_{1n}(first orthogonal projection)
    IsStarProjection (E₂ n) ∧ Commute (E₁ n) (E₂ n) -- @realizes E_{2n}(second commuting orthogonal projection)

/-- On [a sequence of complex Hilbert spaces](hyp:H), for [operator sequences E₁ and E₂](hyp:E₁,E₂) and [an index n](hyp:n), [the corner operator](goal) is the product of E₁ and E₂ at n. -/
noncomputable def cornerProj (E₁ E₂ : ∀ n, H n →L[ℂ] H n) (n : ℕ) : H n →L[ℂ] H n :=
  E₁ n * E₂ n -- @realizes E_n(product of the two projections)

-- @node: def:corner-range
/-- On [a sequence of complex Hilbert spaces](hyp:H), given [operator sequences E₁ and E₂](hyp:E₁,E₂) and [an index n](hyp:n), [the corner subspace](goal) is the range of their product at n. -/
noncomputable def cornerRange (E₁ E₂ : ∀ n, H n →L[ℂ] H n) (n : ℕ) : Submodule ℂ (H n) :=
  LinearMap.range (cornerProj E₁ E₂ n).toLinearMap -- @realizes D_n(range of the common projection)

-- @node: ass:corner-dimension
/-- For [a sequence of complex Hilbert spaces](hyp:H) and [operator sequences E₁ and E₂](hyp:E₁,E₂), [the corner dimension condition](goal) requires their product's range at every index to be [nonzero](step:1) and [finite dimensional over the complex numbers](step:2). -/
noncomputable def CornerDimension (E₁ E₂ : ∀ n, H n →L[ℂ] H n) : Prop :=
  ∀ n, cornerRange E₁ E₂ n ≠ ⊥ ∧ FiniteDimensional ℂ (cornerRange E₁ E₂ n) -- @realizes D_n(nonzero finite-dimensional range)

-- @node: ass:corner-unitaries
/-- For [a sequence of complex Hilbert spaces](hyp:H), [operator sequences E₁ and E₂](hyp:E₁,E₂), and [operator sequences R₁ and R₂](hyp:R₁,R₂), [the corner unitary condition](goal) requires at every index that [R₁ be unitary](step:1), [R₂ be unitary](step:2), [R₁ commute with E₁](step:3), [R₁ commute with E₂](step:4), [R₂ commute with E₁](step:5), and [R₂ commute with E₂](step:6). -/
noncomputable def CornerUnitaries (E₁ E₂ R₁ R₂ : ∀ n, H n →L[ℂ] H n) : Prop :=
  ∀ n, R₁ n ∈ unitary _ ∧ -- @realizes \widetilde R_{1n}(first lifted unitary)
    R₂ n ∈ unitary _ ∧ -- @realizes \widetilde R_{2n}(second lifted unitary)
    Commute (R₁ n) (E₁ n) ∧ Commute (R₁ n) (E₂ n) ∧
    Commute (R₂ n) (E₁ n) ∧ Commute (R₂ n) (E₂ n)

-- @node: ass:corner-algebras
/-- On [a sequence of complex Hilbert spaces](hyp:H), for [two sequences of von Neumann algebras A₁ and A₂](hyp:A₁,A₂), [the corner algebra condition](goal) says that, at each index, every element of the first algebra commutes with every element of the second. -/
noncomputable def CornerAlgebras (A₁ A₂ : ∀ n, VonNeumannAlgebra (H n)) : Prop :=
  ∀ n, ∀ x ∈ A₁ n, ∀ y ∈ A₂ n, Commute x y -- @realizes \mathcal A_{1n}(first unital von Neumann algebra) @realizes \mathcal A_{2n}(second commuting unital von Neumann algebra)

-- @node: ass:corner-approximation
/-- On [a sequence of complex Hilbert spaces](hyp:H), given [von Neumann algebra sequences A₁ and A₂](hyp:A₁,A₂), [operator sequences T₁ and T₂](hyp:T₁,T₂), [operator sequences E₁ and E₂](hyp:E₁,E₂), and [operator sequences R₁ and R₂](hyp:R₁,R₂), [the corner approximation condition](goal) requires [T₁ and T₂ to belong to their respective algebras at every index](step:1), [the norm distance from T₁ to E₁R₁ to tend to zero](step:2), and [the norm distance from T₂ to E₂R₂ to tend to zero](step:3). -/
noncomputable def CornerApproximation (A₁ A₂ : ∀ n, VonNeumannAlgebra (H n))
    (T₁ T₂ E₁ E₂ R₁ R₂ : ∀ n, H n →L[ℂ] H n) : Prop :=
  (∀ n, T₁ n ∈ A₁ n ∧ T₂ n ∈ A₂ n) ∧ -- @realizes T_{in}(operators belonging to their respective algebras)
  Tendsto (fun n => ‖T₁ n - E₁ n * R₁ n‖) atTop (𝓝 0) ∧ -- @realizes T_{in}(first approximation in operator norm)
  Tendsto (fun n => ‖T₂ n - E₂ n * R₂ n‖) atTop (𝓝 0) -- @realizes T_{in}(second approximation in operator norm)

-- @node: cornerProj_mem_range
/-- For [operator sequences E₁ and E₂](hyp:E₁,E₂), [an index n](hyp:n), and [a vector x in the corresponding Hilbert space](hyp:x), [the product E₁E₂ applied to x belongs to the corner subspace at n](goal). -/
lemma cornerProj_mem_range (E₁ E₂ : ∀ n, H n →L[ℂ] H n) (n : ℕ) (x : H n) :
    cornerProj E₁ E₂ n x ∈ cornerRange E₁ E₂ n := by
  exact LinearMap.mem_range_self (cornerProj E₁ E₂ n).toLinearMap x

-- @node: def:corner-restrictions
/-- On [a sequence of complex Hilbert spaces](hyp:H), given [operator sequences E₁ and E₂](hyp:E₁,E₂), [an operator sequence R](hyp:R), and [an index n](hyp:n), [the corner compression of R](goal) sends a vector in the range of E₁E₂ to E₁E₂ applied after R, all at n, with the result viewed in that same range. -/
noncomputable def cornerRestrict (E₁ E₂ R : ∀ n, H n →L[ℂ] H n) (n : ℕ) :
    cornerRange E₁ E₂ n →L[ℂ] cornerRange E₁ E₂ n :=
  ((cornerProj E₁ E₂ n).codRestrict (cornerRange E₁ E₂ n)
    (cornerProj_mem_range E₁ E₂ n)).comp
      ((R n).comp (cornerRange E₁ E₂ n).subtypeL) -- @realizes R_{in}(restriction on the common invariant range)

-- @node: cornerRestrict_apply
/-- For [operator sequences E₁, E₂, R₁, and R₂](hyp:E₁,E₂,R₁,R₂), suppose [E₁ and E₂ are commuting orthogonal projections at every index](hyp:hE) and [R₁ and R₂ are unitaries commuting with both projections at every index](hyp:hR). At [an index n](hyp:n), for [a vector x in the common corner](hyp:x), [both corner compressions act on x exactly as their respective ambient operators R₁ and R₂](goal). -/
lemma cornerRestrict_apply (E₁ E₂ R₁ R₂ : ∀ n, H n →L[ℂ] H n)
    (hE : CornerProjections E₁ E₂) (hR : CornerUnitaries E₁ E₂ R₁ R₂)
    (n : ℕ) (x : cornerRange E₁ E₂ n) :
    (cornerRestrict E₁ E₂ R₁ n x : H n) = R₁ n x ∧
    (cornerRestrict E₁ E₂ R₂ n x : H n) = R₂ n x := by
  have hP : IsIdempotentElem (cornerProj E₁ E₂ n) :=
    ((hE n).1.mul (hE n).2.1 (hE n).2.2).isIdempotentElem
  have hx : cornerProj E₁ E₂ n x = x := by
    obtain ⟨y, hy⟩ := x.property
    change cornerProj E₁ E₂ n y = (x : H n) at hy
    rw [← hy]
    exact congrArg (fun T : H n →L[ℂ] H n => T y) hP
  have h₁ : Commute (R₁ n) (cornerProj E₁ E₂ n) :=
    (hR n).2.2.1.mul_right (hR n).2.2.2.1
  have h₂ : Commute (R₂ n) (cornerProj E₁ E₂ n) :=
    (hR n).2.2.2.2.1.mul_right (hR n).2.2.2.2.2
  constructor
  · change cornerProj E₁ E₂ n (R₁ n x) = R₁ n x
    calc
      cornerProj E₁ E₂ n (R₁ n x) = R₁ n (cornerProj E₁ E₂ n x) :=
        congrArg (fun T : H n →L[ℂ] H n => T x) h₁.eq.symm
      _ = R₁ n x := congrArg (R₁ n) hx
  · change cornerProj E₁ E₂ n (R₂ n x) = R₂ n x
    calc
      cornerProj E₁ E₂ n (R₂ n x) = R₂ n (cornerProj E₁ E₂ n x) :=
        congrArg (fun T : H n →L[ℂ] H n => T x) h₂.eq.symm
      _ = R₂ n x := congrArg (R₂ n) hx

-- @node: cornerModel_star_mul_self
/-- For [operators E and R](hyp:E,R), if [E is an orthogonal projection](hyp:hE), [R is unitary](hyp:hR), and [R commutes with E](hyp:hRE), then [the adjoint of ER multiplied by ER equals E](goal). -/
lemma cornerModel_star_mul_self {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K]
    (E R : K →L[ℂ] K) (hE : IsStarProjection E)
    (hR : R ∈ unitary _) (hRE : Commute R E) :
    star (E * R) * (E * R) = E := by
  rw [star_mul, hE.isSelfAdjoint.star_eq]
  calc
    star R * E * (E * R) = star R * (E * E) * R := by noncomm_ring
    _ = star R * E * R := by rw [hE.isIdempotentElem.eq]
    _ = star R * (R * E) := by rw [mul_assoc, hRE.eq]
    _ = E := by rw [← mul_assoc, Unitary.star_mul_self_of_mem hR, one_mul]

-- @node: corner_star_mul_error_bound
/-- For [operators T, E, and R](hyp:T,E,R), if [E is an orthogonal projection](hyp:hE), [R is unitary](hyp:hR), and [R commutes with E](hyp:hRE), then [the norm distance from T's adjoint times T to E is at most the norm distance from T to ER multiplied by two plus that same distance](goal). -/
lemma corner_star_mul_error_bound {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K]
    (T E R : K →L[ℂ] K) (hE : IsStarProjection E)
    (hR : R ∈ unitary _) (hRE : Commute R E) :
    ‖star T * T - E‖ ≤ ‖T - E * R‖ * (2 + ‖T - E * R‖) := by
  let X := E * R
  have hX : ‖X‖ ≤ 1 := by
    simpa only [X, CStarRing.norm_mul_mem_unitary E hR] using hE.norm_le E
  have hT : ‖T‖ ≤ ‖T - X‖ + 1 := by
    calc
      ‖T‖ = ‖(T - X) + X‖ := by rw [sub_add_cancel]
      _ ≤ ‖T - X‖ + ‖X‖ := norm_add_le _ _
      _ ≤ ‖T - X‖ + 1 := add_le_add le_rfl hX
  have hId : star T * T - E = star (T - X) * T + star X * (T - X) := by
    rw [star_sub]
    have h := cornerModel_star_mul_self E R hE hR hRE
    change star X * X = E at h
    rw [← h]
    noncomm_ring
  calc
    ‖star T * T - E‖ = ‖star (T - X) * T + star X * (T - X)‖ := congrArg norm hId
    _ ≤ ‖star (T - X) * T‖ + ‖star X * (T - X)‖ := norm_add_le _ _
    _ ≤ ‖T - X‖ * ‖T‖ + ‖X‖ * ‖T - X‖ := by
      simpa only [norm_star] using add_le_add (norm_mul_le (star (T - X)) T)
        (norm_mul_le (star X) (T - X))
    _ ≤ ‖T - X‖ * (‖T - X‖ + 1) + 1 * ‖T - X‖ := by
      exact add_le_add (mul_le_mul_of_nonneg_left hT (norm_nonneg _))
        (mul_le_mul_of_nonneg_right hX (norm_nonneg _))
    _ = ‖T - E * R‖ * (2 + ‖T - E * R‖) := by dsimp [X]; ring

-- @node: corner_star_mul_error_tendsto
/-- For [operator sequences E, R, and T](hyp:E,R,T), suppose [each E is an orthogonal projection](hyp:hE), [each R is unitary](hyp:hR), [R commutes with E at every index](hyp:hRE), and [the norm distance from T to ER tends to zero](hyp:hT). Then [the norm distance from T's adjoint times T to E tends to zero](goal). -/
lemma corner_star_mul_error_tendsto
    (E R T : ∀ n, H n →L[ℂ] H n)
    (hE : ∀ n, IsStarProjection (E n))
    (hR : ∀ n, R n ∈ unitary _)
    (hRE : ∀ n, Commute (R n) (E n))
    (hT : Tendsto (fun n => ‖T n - E n * R n‖) atTop (𝓝 0)) :
    Tendsto (fun n => ‖star (T n) * T n - E n‖) atTop (𝓝 0) := by
  have hbound := hT.mul ((tendsto_const_nhds (x := (2 : ℝ))).add hT)
  have hzero : Tendsto (fun n => ‖T n - E n * R n‖ * (2 + ‖T n - E n * R n‖))
      atTop (𝓝 0) := by simpa using hbound
  exact squeeze_zero (fun n => norm_nonneg _)
    (fun n => corner_star_mul_error_bound (T n) (E n) (R n) (hE n) (hR n) (hRE n)) hzero

-- @node: corner_compression_factor
/-- For [elements Q₁, Q₂, and T of a monoid](hyp:Q₁,Q₂,T), if [Q₂ is idempotent](hyp:hQ₂), [Q₁ commutes with Q₂](hyp:hQQ), and [T commutes with Q₂](hyp:hTQ), then [multiplying T on both sides by Q₁Q₂ gives Q₁TQ₁ multiplied by Q₂](goal). -/
lemma corner_compression_factor {M : Type*} [Monoid M]
    (Q₁ Q₂ T : M) (hQ₂ : IsIdempotentElem Q₂)
    (hQQ : Commute Q₁ Q₂) (hTQ : Commute T Q₂) :
    (Q₁ * Q₂) * T * (Q₁ * Q₂) = (Q₁ * T * Q₁) * Q₂ := by
  calc
    (Q₁ * Q₂) * T * (Q₁ * Q₂) = Q₁ * (Q₂ * (T * Q₁)) * Q₂ := by
      simp only [mul_assoc]
    _ = Q₁ * ((T * Q₁) * Q₂) * Q₂ := by
      rw [(hTQ.symm.mul_right hQQ.symm).eq]
    _ = (Q₁ * T * Q₁) * (Q₂ * Q₂) := by simp only [mul_assoc]
    _ = (Q₁ * T * Q₁) * Q₂ := by rw [hQ₂.eq]

-- @node: corner_supported_compressions_commute
/-- For [monoid elements Q₁, Q₂, A, and B](hyp:Q₁,Q₂,A,B), assume [Q₁ and Q₂ commute](hyp:hQQ), [A and B commute](hyp:hAB), [left multiplication of A by Q₁ leaves A unchanged](hyp:hAl), [right multiplication of A by Q₁ leaves A unchanged](hyp:hAr), [left multiplication of B by Q₂ leaves B unchanged](hyp:hBl), and [right multiplication of B by Q₂ leaves B unchanged](hyp:hBr). Then [AQ₂ and Q₁B commute](goal). -/
lemma corner_supported_compressions_commute {M : Type*} [Monoid M]
    (Q₁ Q₂ A B : M) (hQQ : Commute Q₁ Q₂) (hAB : Commute A B)
    (hAl : Q₁ * A = A) (hAr : A * Q₁ = A)
    (hBl : Q₂ * B = B) (hBr : B * Q₂ = B) :
    Commute (A * Q₂) (Q₁ * B) := by
  have hl : (A * Q₂) * (Q₁ * B) = A * B := by
    calc
      (A * Q₂) * (Q₁ * B) = A * (Q₂ * Q₁) * B := by simp only [mul_assoc]
      _ = A * (Q₁ * Q₂) * B := by rw [hQQ.eq]
      _ = (A * Q₁) * (Q₂ * B) := by simp only [mul_assoc]
      _ = A * B := by rw [hAr, hBl]
  have hr : (Q₁ * B) * (A * Q₂) = A * B := by
    calc
      (Q₁ * B) * (A * Q₂) = Q₁ * (B * A) * Q₂ := by simp only [mul_assoc]
      _ = Q₁ * (A * B) * Q₂ := by rw [hAB.eq]
      _ = (Q₁ * A) * (B * Q₂) := by simp only [mul_assoc]
      _ = A * B := by rw [hAl, hBr]
  exact hl.trans hr.symm

-- @node: corner_algebra_compressions_commute
/-- Given [von Neumann algebras A₁ and A₂](hyp:A₁,A₂) whose [elements commute across the two algebras](hyp:hA), consider [operators Q₁, Q₂, T₁, and T₂](hyp:Q₁,Q₂,T₁,T₂), where [Q₁ is an orthogonal projection](hyp:hQ₁), [Q₂ is an orthogonal projection](hyp:hQ₂), [Q₁ belongs to A₁](hyp:hQ₁A), [Q₂ belongs to A₂](hyp:hQ₂A), [T₁ belongs to A₁](hyp:hT₁A), and [T₂ belongs to A₂](hyp:hT₂A). Then [the compressions of T₁ and T₂ by Q₁Q₂ commute](goal). -/
lemma corner_algebra_compressions_commute {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K]
    (A₁ A₂ : VonNeumannAlgebra K)
    (hA : ∀ x ∈ A₁, ∀ y ∈ A₂, Commute x y)
    (Q₁ Q₂ T₁ T₂ : K →L[ℂ] K)
    (hQ₁ : IsStarProjection Q₁) (hQ₂ : IsStarProjection Q₂)
    (hQ₁A : Q₁ ∈ A₁) (hQ₂A : Q₂ ∈ A₂)
    (hT₁A : T₁ ∈ A₁) (hT₂A : T₂ ∈ A₂) :
    Commute ((Q₁ * Q₂) * T₁ * (Q₁ * Q₂))
      ((Q₁ * Q₂) * T₂ * (Q₁ * Q₂)) := by
  let A := Q₁ * T₁ * Q₁
  let B := Q₂ * T₂ * Q₂
  have hAmem : A ∈ A₁ := A₁.mul_mem (A₁.mul_mem hQ₁A hT₁A) hQ₁A
  have hBmem : B ∈ A₂ := A₂.mul_mem (A₂.mul_mem hQ₂A hT₂A) hQ₂A
  have hQQ := hA Q₁ hQ₁A Q₂ hQ₂A
  have hf₁ := corner_compression_factor Q₁ Q₂ T₁ hQ₂.isIdempotentElem hQQ
    (hA T₁ hT₁A Q₂ hQ₂A)
  have hf₂ : (Q₁ * Q₂) * T₂ * (Q₁ * Q₂) = Q₁ * B := by
    rw [hQQ.eq, corner_compression_factor Q₂ Q₁ T₂ hQ₁.isIdempotentElem hQQ.symm
      (hA Q₁ hQ₁A T₂ hT₂A).symm]
    exact (hA Q₁ hQ₁A B hBmem).eq.symm
  rw [hf₁, hf₂]
  apply corner_supported_compressions_commute Q₁ Q₂ A B hQQ (hA A hAmem B hBmem)
  · dsimp [A]; rw [← mul_assoc, ← mul_assoc, hQ₁.isIdempotentElem.eq]
  · dsimp [A]; rw [mul_assoc, hQ₁.isIdempotentElem.eq]
  · dsimp [B]; rw [← mul_assoc, ← mul_assoc, hQ₂.isIdempotentElem.eq]
  · dsimp [B]; rw [mul_assoc, hQ₂.isIdempotentElem.eq]

-- @node: corner_algebra_compressions_star_commute
/-- Given [von Neumann algebras A₁ and A₂](hyp:A₁,A₂) whose [elements commute across the two algebras](hyp:hA), consider [operators Q₁, Q₂, T₁, and T₂](hyp:Q₁,Q₂,T₁,T₂), where [Q₁ is an orthogonal projection](hyp:hQ₁), [Q₂ is an orthogonal projection](hyp:hQ₂), [Q₁ belongs to A₁](hyp:hQ₁A), [Q₂ belongs to A₂](hyp:hQ₂A), [T₁ belongs to A₁](hyp:hT₁A), and [T₂ belongs to A₂](hyp:hT₂A). Then [the compression of T₁ by Q₁Q₂ commutes with the adjoint of the compression of T₂ by Q₁Q₂](goal). -/
lemma corner_algebra_compressions_star_commute {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K]
    (A₁ A₂ : VonNeumannAlgebra K)
    (hA : ∀ x ∈ A₁, ∀ y ∈ A₂, Commute x y)
    (Q₁ Q₂ T₁ T₂ : K →L[ℂ] K)
    (hQ₁ : IsStarProjection Q₁) (hQ₂ : IsStarProjection Q₂)
    (hQ₁A : Q₁ ∈ A₁) (hQ₂A : Q₂ ∈ A₂)
    (hT₁A : T₁ ∈ A₁) (hT₂A : T₂ ∈ A₂) :
    Commute ((Q₁ * Q₂) * T₁ * (Q₁ * Q₂))
      (star ((Q₁ * Q₂) * T₂ * (Q₁ * Q₂))) := by
  have hP := hQ₁.mul hQ₂ (hA Q₁ hQ₁A Q₂ hQ₂A)
  have hstar (P : K →L[ℂ] K) (hP : IsSelfAdjoint P) :
      star (P * T₂ * P) = P * star T₂ * P := by
    simp only [star_mul, hP.star_eq, mul_assoc]
  rw [hstar (Q₁ * Q₂) hP.isSelfAdjoint]
  exact corner_algebra_compressions_commute A₁ A₂ hA Q₁ Q₂ T₁ (star T₂)
      hQ₁ hQ₂ hQ₁A hQ₂A hT₁A (star_mem hT₂A)

-- @node: corner_product_projection_error_bound
/-- For [operators Q₁, Q₂, E₁, and E₂](hyp:Q₁,Q₂,E₁,E₂), if [Q₁ is an orthogonal projection](hyp:hQ₁) and [E₂ is an orthogonal projection](hyp:hE₂), then [the norm distance between Q₁Q₂ and E₁E₂ is at most the sum of the norm distances between Q₁ and E₁ and between Q₂ and E₂](goal). -/
lemma corner_product_projection_error_bound {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K]
    (Q₁ Q₂ E₁ E₂ : K →L[ℂ] K)
    (hQ₁ : IsStarProjection Q₁) (hE₂ : IsStarProjection E₂) :
    ‖Q₁ * Q₂ - E₁ * E₂‖ ≤ ‖Q₁ - E₁‖ + ‖Q₂ - E₂‖ := by
  have hid : Q₁ * Q₂ - E₁ * E₂ = (Q₁ - E₁) * E₂ + Q₁ * (Q₂ - E₂) := by
    noncomm_ring
  rw [hid]
  calc
    ‖(Q₁ - E₁) * E₂ + Q₁ * (Q₂ - E₂)‖ ≤
        ‖(Q₁ - E₁) * E₂‖ + ‖Q₁ * (Q₂ - E₂)‖ := norm_add_le _ _
    _ ≤ ‖Q₁ - E₁‖ * ‖E₂‖ + ‖Q₁‖ * ‖Q₂ - E₂‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ ‖Q₁ - E₁‖ * 1 + 1 * ‖Q₂ - E₂‖ :=
      add_le_add (mul_le_mul_of_nonneg_left (hE₂.norm_le E₂) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (hQ₁.norm_le Q₁) (norm_nonneg _))
    _ = ‖Q₁ - E₁‖ + ‖Q₂ - E₂‖ := by ring

-- @node: corner_product_projection_error_tendsto
/-- For [operator sequences Q₁, Q₂, E₁, and E₂](hyp:Q₁,Q₂,E₁,E₂), suppose [each Q₁ is an orthogonal projection](hyp:hQ₁), [each E₂ is an orthogonal projection](hyp:hE₂), [the norm distance between Q₁ and E₁ tends to zero](hyp:h₁), and [the norm distance between Q₂ and E₂ tends to zero](hyp:h₂). Then [the norm distance between their products Q₁Q₂ and E₁E₂ tends to zero](goal). -/
lemma corner_product_projection_error_tendsto
    (Q₁ Q₂ E₁ E₂ : ∀ n, H n →L[ℂ] H n)
    (hQ₁ : ∀ n, IsStarProjection (Q₁ n)) (hE₂ : ∀ n, IsStarProjection (E₂ n))
    (h₁ : Tendsto (fun n => ‖Q₁ n - E₁ n‖) atTop (𝓝 0))
    (h₂ : Tendsto (fun n => ‖Q₂ n - E₂ n‖) atTop (𝓝 0)) :
    Tendsto (fun n => ‖Q₁ n * Q₂ n - E₁ n * E₂ n‖) atTop (𝓝 0) := by
  exact squeeze_zero (fun n => norm_nonneg _)
    (fun n => corner_product_projection_error_bound (Q₁ n) (Q₂ n) (E₁ n) (E₂ n)
      (hQ₁ n) (hE₂ n)) (by simpa using h₁.add h₂)

-- @node: cornerIntertwiner
/-- For [elements P and E of a ring](hyp:P,E), [the intertwining element](goal) is PE plus the product of one minus P and one minus E. -/
noncomputable def cornerIntertwiner {M : Type*} [Ring M] (P E : M) : M :=
  P * E + (1 - P) * (1 - E)

-- @node: cornerIntertwiner_eq_one_add
/-- For [ring elements P and E](hyp:P,E), if [E is idempotent](hyp:hE), then [their intertwining element equals one plus the product of P minus E and twice E minus one](goal). -/
lemma cornerIntertwiner_eq_one_add {M : Type*} [Ring M] (P E : M)
    (hE : IsIdempotentElem E) :
    cornerIntertwiner P E = 1 + (P - E) * (2 * E - 1) := by
  dsimp [cornerIntertwiner]
  have hEE := hE.eq
  noncomm_ring [hEE]

-- @node: cornerIntertwiner_mul_projection
/-- For [ring elements P and E](hyp:P,E), if [P is idempotent](hyp:hP) and [E is idempotent](hyp:hE), then [the intertwining element multiplied on the right by E equals P multiplied by the intertwining element](goal). -/
lemma cornerIntertwiner_mul_projection {M : Type*} [Ring M] (P E : M)
    (hP : IsIdempotentElem P) (hE : IsIdempotentElem E) :
    cornerIntertwiner P E * E = P * cornerIntertwiner P E := by
  dsimp [cornerIntertwiner]
  have hPP := hP.eq
  have hEE := hE.eq
  noncomm_ring [hPP, hEE]
  simp [← mul_assoc, hPP]
  noncomm_ring

-- @node: cornerIntertwiner_star_mul_commute
/-- For [elements P and E of a ring with an adjoint operation](hyp:P,E), if [P is a self-adjoint idempotent](hyp:hP) and [E is a self-adjoint idempotent](hyp:hE), then [the adjoint of their intertwining element multiplied by that element commutes with E](goal). -/
lemma cornerIntertwiner_star_mul_commute {M : Type*} [Ring M] [StarRing M]
    (P E : M) (hP : IsStarProjection P) (hE : IsStarProjection E) :
    Commute (star (cornerIntertwiner P E) * cornerIntertwiner P E) E := by
  let S := cornerIntertwiner P E
  have hSE : S * E = P * S :=
    cornerIntertwiner_mul_projection P E hP.isIdempotentElem hE.isIdempotentElem
  have hES : E * star S = star S * P := by
    simpa only [star_mul, hP.isSelfAdjoint.star_eq, hE.isSelfAdjoint.star_eq] using
      congrArg star hSE
  change (star S * S) * E = E * (star S * S)
  calc
    (star S * S) * E = star S * (P * S) := by rw [mul_assoc, hSE]
    _ = (E * star S) * S := by rw [← mul_assoc, ← hES]
    _ = E * (star S * S) := mul_assoc _ _ _

-- @node: cornerIntertwiner_norm_sub_one
/-- For [operators P and E](hyp:P,E), if [E is an orthogonal projection](hyp:hE), then [the norm distance of their intertwining operator from the identity equals the norm distance between P and E](goal). -/
lemma cornerIntertwiner_norm_sub_one {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K]
    (P E : K →L[ℂ] K) (hE : IsStarProjection E) :
    ‖cornerIntertwiner P E - 1‖ = ‖P - E‖ := by
  rw [cornerIntertwiner_eq_one_add P E hE.isIdempotentElem, add_sub_cancel_left]
  exact CStarRing.norm_mul_mem_unitary (P - E) hE.two_mul_sub_one_mem_unitary

-- @node: cornerIntertwiner_error_tendsto
/-- For [operator sequences P and E](hyp:P,E), if [each E is an orthogonal projection](hyp:hE) and [the norm distance between P and E tends to zero](hyp:hPE), then [the norm distance of their intertwining operators from the identity tends to zero](goal). -/
lemma cornerIntertwiner_error_tendsto (P E : ∀ n, H n →L[ℂ] H n)
    (hE : ∀ n, IsStarProjection (E n))
    (hPE : Tendsto (fun n => ‖P n - E n‖) atTop (𝓝 0)) :
    Tendsto (fun n => ‖cornerIntertwiner (P n) (E n) - 1‖) atTop (𝓝 0) := by
  simpa only [cornerIntertwiner_norm_sub_one _ _ (hE _)] using hPE

-- @node: cornerIntertwiner_eventually_isUnit
/-- For [operator sequences P and E](hyp:P,E), if [each E is an orthogonal projection](hyp:hE) and [the norm distance between P and E tends to zero](hyp:hPE), then [their intertwining operators are invertible at all sufficiently large indices](goal). -/
lemma cornerIntertwiner_eventually_isUnit (P E : ∀ n, H n →L[ℂ] H n)
    (hE : ∀ n, IsStarProjection (E n))
    (hPE : Tendsto (fun n => ‖P n - E n‖) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, IsUnit (cornerIntertwiner (P n) (E n)) := by
  have hsmall : ∀ᶠ n in atTop, ‖P n - E n‖ < 1 :=
    hPE.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [hsmall] with n hn
  have hnorm : ‖1 - cornerIntertwiner (P n) (E n)‖ < 1 := by
    rw [norm_sub_rev, cornerIntertwiner_norm_sub_one _ _ (hE n)]
    exact hn
  simpa only [sub_sub_cancel] using isUnit_one_sub_of_norm_lt_one hnorm

-- @node: corner_unitary_conjugation_error_bound
/-- For [operators J and X](hyp:J,X), if [J is unitary](hyp:hJ) and [X has norm at most one](hyp:hX), then [the norm distance between J's adjoint times X times J and X is at most twice the norm distance of J from the identity](goal). -/
lemma corner_unitary_conjugation_error_bound {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K]
    (J X : K →L[ℂ] K) (hJ : J ∈ unitary _) (hX : ‖X‖ ≤ 1) :
    ‖star J * X * J - X‖ ≤ 2 * ‖J - 1‖ := by
  have hstar : ‖star J - 1‖ = ‖J - 1‖ := by
    simpa only [star_sub, star_one] using norm_star (J - 1)
  have hid : star J * X * J - X = (star J - 1) * X * J + X * (J - 1) := by
    noncomm_ring
  rw [hid]
  calc
    ‖(star J - 1) * X * J + X * (J - 1)‖ ≤
        ‖(star J - 1) * X * J‖ + ‖X * (J - 1)‖ := norm_add_le _ _
    _ = ‖(star J - 1) * X‖ + ‖X * (J - 1)‖ := by
      rw [CStarRing.norm_mul_mem_unitary _ hJ]
    _ ≤ ‖J - 1‖ * ‖X‖ + ‖X‖ * ‖J - 1‖ := by
      simpa only [hstar] using add_le_add (norm_mul_le (star J - 1) X)
        (norm_mul_le X (J - 1))
    _ ≤ ‖J - 1‖ * 1 + 1 * ‖J - 1‖ :=
      add_le_add (mul_le_mul_of_nonneg_left hX (norm_nonneg _))
        (mul_le_mul_of_nonneg_right hX (norm_nonneg _))
    _ = 2 * ‖J - 1‖ := by ring

-- @node: corner_transported_error_bound
/-- For [operators J, T, and X](hyp:J,T,X), if [J is unitary](hyp:hJ) and [X has norm at most one](hyp:hX), then [the norm distance from J's adjoint times T times J to X is at most the norm distance from T to X plus twice the norm distance of J from the identity](goal). -/
lemma corner_transported_error_bound {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K]
    (J T X : K →L[ℂ] K) (hJ : J ∈ unitary _) (hX : ‖X‖ ≤ 1) :
    ‖star J * T * J - X‖ ≤ ‖T - X‖ + 2 * ‖J - 1‖ := by
  have hid : star J * T * J - X =
      star J * (T - X) * J + (star J * X * J - X) := by noncomm_ring
  rw [hid]
  calc
    ‖star J * (T - X) * J + (star J * X * J - X)‖ ≤
        ‖star J * (T - X) * J‖ + ‖star J * X * J - X‖ := norm_add_le _ _
    _ = ‖T - X‖ + ‖star J * X * J - X‖ := by
      rw [CStarRing.norm_mul_mem_unitary _ hJ,
        CStarRing.norm_mem_unitary_mul _ (Unitary.star_mem hJ)]
    _ ≤ ‖T - X‖ + 2 * ‖J - 1‖ :=
      add_le_add le_rfl (corner_unitary_conjugation_error_bound J X hJ hX)

-- @node: corner_compression_norm_le
/-- For [operators E and X](hyp:E,X), if [E is an orthogonal projection](hyp:hE), then [the norm of EXE is at most the norm of X](goal). -/
lemma corner_compression_norm_le {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K]
    (E X : K →L[ℂ] K) (hE : IsStarProjection E) :
    ‖E * X * E‖ ≤ ‖X‖ := by
  calc
    ‖E * X * E‖ ≤ ‖E * X‖ * ‖E‖ := norm_mul_le _ _
    _ ≤ (‖E‖ * ‖X‖) * ‖E‖ :=
      mul_le_mul_of_nonneg_right (norm_mul_le E X) (norm_nonneg _)
    _ ≤ (1 * ‖X‖) * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_right (hE.norm_le E) (norm_nonneg _))
        (hE.norm_le E) (norm_nonneg _) (by positivity)
    _ = ‖X‖ := by ring

-- @node: corner_compressed_transport_error_bound
/-- For [operators E, Q, R, J, and T](hyp:E,Q,R,J,T), suppose [E is an orthogonal projection](hyp:hE), [Q is an orthogonal projection](hyp:hQ), [R is unitary](hyp:hR), [J is unitary](hyp:hJ), and [EQ equals E](hyp:hEQ). Then [the norm of the compression by E of the difference between J's adjoint times T times J and R is at most the norm distance from T to QR plus twice the norm distance of J from the identity](goal). -/
lemma corner_compressed_transport_error_bound {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K]
    (E Q R J T : K →L[ℂ] K) (hE : IsStarProjection E)
    (hQ : IsStarProjection Q) (hR : R ∈ unitary _) (hJ : J ∈ unitary _)
    (hEQ : E * Q = E) :
    ‖E * (star J * T * J - R) * E‖ ≤ ‖T - Q * R‖ + 2 * ‖J - 1‖ := by
  have hid : E * (star J * T * J - R) * E =
      E * (star J * T * J - Q * R) * E := by
    simp only [mul_sub, sub_mul, ← mul_assoc, hEQ]
  rw [hid]
  exact (corner_compression_norm_le E _ hE).trans
    (corner_transported_error_bound J T (Q * R) hJ (by
      simpa only [CStarRing.norm_mul_mem_unitary Q hR] using hQ.norm_le Q))

-- @node: cornerRestrict_norm_sub_le
/-- For [operator sequences E₁, E₂, T, and R](hyp:E₁,E₂,T,R), assume [E₁ and E₂ are commuting orthogonal projections at every index](hyp:hE). At [any index n](hyp:n), [the norm distance between the corner compressions of T and R is at most the norm of their ambient difference multiplied on both sides by E₁E₂](goal). -/
lemma cornerRestrict_norm_sub_le (E₁ E₂ T R : ∀ n, H n →L[ℂ] H n)
    (hE : CornerProjections E₁ E₂) (n : ℕ) :
    ‖cornerRestrict E₁ E₂ T n - cornerRestrict E₁ E₂ R n‖ ≤
      ‖cornerProj E₁ E₂ n * (T n - R n) * cornerProj E₁ E₂ n‖ := by
  let P := cornerProj E₁ E₂ n
  have hP : IsIdempotentElem P :=
    ((hE n).1.mul (hE n).2.1 (hE n).2.2).isIdempotentElem
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  have hx : P (x : H n) = x := by
    obtain ⟨y, hy⟩ := x.property
    change P y = (x : H n) at hy
    rw [← hy]
    exact congrArg (fun A : H n →L[ℂ] H n => A y) hP.eq
  change ‖P (T n x) - P (R n x)‖ ≤ ‖P * (T n - R n) * P‖ * ‖(x : H n)‖
  simpa only [mul_apply_eq_comp, sub_apply, hx, map_sub]
    using (P * (T n - R n) * P).le_opNorm (x : H n)

-- @node: cornerRestrict_transport_error_bound
/-- For [operator sequences E₁, E₂, R₁, R₂, T, and J](hyp:E₁,E₂,R₁,R₂,T,J), assume [E₁ and E₂ are commuting orthogonal projections at every index](hyp:hE) and [R₁ and R₂ are unitaries commuting with both projections at every index](hyp:hR). At [an index n](hyp:n) where [J is unitary](hyp:hJ), [the norm distance on the common corner between the compression of J's adjoint times T times J and the compression of R₁ is at most the norm distance from T to E₁R₁ plus twice the norm distance of J from the identity](goal). -/
lemma cornerRestrict_transport_error_bound
    (E₁ E₂ R₁ R₂ T J : ∀ n, H n →L[ℂ] H n)
    (hE : CornerProjections E₁ E₂) (hR : CornerUnitaries E₁ E₂ R₁ R₂)
    (n : ℕ) (hJ : J n ∈ unitary _) :
    ‖cornerRestrict E₁ E₂ (fun m => star (J m) * T m * J m) n -
        cornerRestrict E₁ E₂ R₁ n‖ ≤
      ‖T n - E₁ n * R₁ n‖ + 2 * ‖J n - 1‖ := by
  have hP : IsStarProjection (cornerProj E₁ E₂ n) :=
    (hE n).1.mul (hE n).2.1 (hE n).2.2
  have hPE : cornerProj E₁ E₂ n * E₁ n = cornerProj E₁ E₂ n := by
    change (E₁ n * E₂ n) * E₁ n = E₁ n * E₂ n
    calc
      (E₁ n * E₂ n) * E₁ n = E₁ n * (E₂ n * E₁ n) := mul_assoc _ _ _
      _ = E₁ n * (E₁ n * E₂ n) := by rw [← (hE n).2.2.eq]
      _ = E₁ n * E₂ n := by rw [← mul_assoc, (hE n).1.isIdempotentElem.eq]
  exact (cornerRestrict_norm_sub_le E₁ E₂ _ R₁ hE n).trans
    (corner_compressed_transport_error_bound (cornerProj E₁ E₂ n) (E₁ n) (R₁ n)
      (J n) (T n) hP (hE n).1 (hR n).1 hJ hPE)

-- @node: cornerRestrict_transport_error_tendsto
/-- For [operator sequences E₁, E₂, R₁, R₂, T, and J](hyp:E₁,E₂,R₁,R₂,T,J), suppose [E₁ and E₂ are commuting orthogonal projections at every index](hyp:hE), [R₁ and R₂ are unitaries commuting with both projections at every index](hyp:hR), [J is unitary at all sufficiently large indices](hyp:hJ), [the norm distance from T to E₁R₁ tends to zero](hyp:hT), and [the norm distance of J from the identity tends to zero](hyp:hJI). Then [the norm distance on the common corner between the compression of J's adjoint times T times J and the compression of R₁ tends to zero](goal). -/
lemma cornerRestrict_transport_error_tendsto
    (E₁ E₂ R₁ R₂ T J : ∀ n, H n →L[ℂ] H n)
    (hE : CornerProjections E₁ E₂) (hR : CornerUnitaries E₁ E₂ R₁ R₂)
    (hJ : ∀ᶠ n in atTop, J n ∈ unitary _)
    (hT : Tendsto (fun n => ‖T n - E₁ n * R₁ n‖) atTop (𝓝 0))
    (hJI : Tendsto (fun n => ‖J n - 1‖) atTop (𝓝 0)) :
    Tendsto (fun n =>
      ‖cornerRestrict E₁ E₂ (fun m => star (J m) * T m * J m) n -
        cornerRestrict E₁ E₂ R₁ n‖) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun n => norm_nonneg _))
  · filter_upwards [hJ] with n hn
    exact cornerRestrict_transport_error_bound E₁ E₂ R₁ R₂ T J hE hR n hn
  · simpa using hT.add (tendsto_const_nhds.mul hJI)

-- @node: cornerRestrict_transport_errors_tendsto
/-- For [operator sequences E₁, E₂, R₁, R₂, T₁, T₂, and J](hyp:E₁,E₂,R₁,R₂,T₁,T₂,J), suppose [E₁ and E₂ are commuting orthogonal projections at every index](hyp:hE), [R₁ and R₂ are unitaries commuting with both projections at every index](hyp:hR), [J is unitary at all sufficiently large indices](hyp:hJ), [the norm distance from T₁ to E₁R₁ tends to zero](hyp:hT₁), [the norm distance from T₂ to E₂R₂ tends to zero](hyp:hT₂), and [the norm distance of J from the identity tends to zero](hyp:hJI). Then [on the common corner, the norm distances from the compressions of J's adjoint times T₁ times J and J's adjoint times T₂ times J to the respective compressions of R₁ and R₂ both tend to zero](goal). -/
lemma cornerRestrict_transport_errors_tendsto
    (E₁ E₂ R₁ R₂ T₁ T₂ J : ∀ n, H n →L[ℂ] H n)
    (hE : CornerProjections E₁ E₂) (hR : CornerUnitaries E₁ E₂ R₁ R₂)
    (hJ : ∀ᶠ n in atTop, J n ∈ unitary _)
    (hT₁ : Tendsto (fun n => ‖T₁ n - E₁ n * R₁ n‖) atTop (𝓝 0))
    (hT₂ : Tendsto (fun n => ‖T₂ n - E₂ n * R₂ n‖) atTop (𝓝 0))
    (hJI : Tendsto (fun n => ‖J n - 1‖) atTop (𝓝 0)) :
    Tendsto (fun n =>
      ‖cornerRestrict E₁ E₂ (fun m => star (J m) * T₁ m * J m) n -
        cornerRestrict E₁ E₂ R₁ n‖) atTop (𝓝 0) ∧
    Tendsto (fun n =>
      ‖cornerRestrict E₁ E₂ (fun m => star (J m) * T₂ m * J m) n -
        cornerRestrict E₁ E₂ R₂ n‖) atTop (𝓝 0) := by
  refine ⟨cornerRestrict_transport_error_tendsto E₁ E₂ R₁ R₂ T₁ J hE hR hJ hT₁ hJI, ?_⟩
  apply squeeze_zero' (Eventually.of_forall (fun n => norm_nonneg _))
  · filter_upwards [hJ] with n hn
    have hP : IsStarProjection (cornerProj E₁ E₂ n) :=
      (hE n).1.mul (hE n).2.1 (hE n).2.2
    have hPE : cornerProj E₁ E₂ n * E₂ n = cornerProj E₁ E₂ n := by
      change (E₁ n * E₂ n) * E₂ n = E₁ n * E₂ n
      rw [mul_assoc, (hE n).2.1.isIdempotentElem.eq]
    exact (cornerRestrict_norm_sub_le E₁ E₂ _ R₂ hE n).trans
      (corner_compressed_transport_error_bound (cornerProj E₁ E₂ n) (E₂ n) (R₂ n)
        (J n) (T₂ n) hP (hE n).2.1 (hR n).2.1 hn hPE)
  · simpa using hT₂.add (tendsto_const_nhds.mul hJI)

end Papers.OaiNearInclusionsVon

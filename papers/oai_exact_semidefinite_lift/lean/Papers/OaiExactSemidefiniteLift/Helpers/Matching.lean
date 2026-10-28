module

public import Papers.OaiExactSemidefiniteLift.Helpers.MatchingRotation

/-!
# Degree-two matching for arbitrary symmetric weights

The constructed matrix depends on the symmetric weight and the nondegenerate
vector. No positivity hypothesis is imposed on the weight.
-/

public section

namespace Papers.OaiExactSemidefiniteLift

open Matrix

-- @node: weightedPairing_complex_trace
/-- [The weighted pairing of two three-by-two complex factors equals the real
part of the trace of the first factor's conjugate transpose times the real
symmetric weight matrix, viewed over the complex numbers, times the second
factor](goal). -/
lemma weightedPairing_complex_trace (S : Sym3) (F H : Matrix (Fin 3) (Fin 2) ℂ) :
    weightedPairing S F H =
      (F.conjTranspose * (S : Mat 3).map (fun r => (r : ℂ)) * H).trace.re := by
  simp [weightedPairing, realify, Matrix.trace, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_succ, Complex.mul_re]
  ring

-- @node: Qpol_diagonal
/-- [Evaluating the polarized quadratic matrix on two copies of the same real
three-vector gives the quadratic matrix at that vector](goal). -/
lemma Qpol_diagonal (y : Fin 3 → ℝ) : Qpol y y = Qmat y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Qpol, QuadraticMap.polar, Qmat] <;> ring

set_option maxHeartbeats 0 in
-- Expand the finite trace and reduce powers by the two unit-circle identities.
set_option maxRecDepth 10000 in
-- @node: matchingR0_pairing_expansion
/-- [The weighted pairing of an angular factor with the reference Gram factor
equals the trace of the weight matrix times the polarized quadratic matrix of
their angular-plane vectors, plus square root of two times the sum of p times
the real part and q times the imaginary part of the matching coefficient h](goal),
where u and v are the cosine and sine of the reference angle, c and d are the
cosine and sine of the varying angle, p is minus the varying planar coefficient
times $c(d^2+v^2-2v^4)-2du^3v$, and q is the varying planar coefficient times
$2cuv^3+d^3-dv^2(2u^2+1)$. -/
lemma matchingR0_pairing_expansion (S : Sym3) (α τ ρ θ η ξ : ℝ) :
    let u := Real.cos α
    let v := Real.sin α
    let c := Real.cos θ
    let d := Real.sin θ
    let p := -η * (c * (d^2 + v^2 - 2*v^4) - 2*d*u^3*v)
    let q := η * (2*c*u*v^3 + d^3 - d*v^2*(2*u^2+1))
    weightedPairing S (Fθ θ η ξ) (matchingR0 α τ ρ) =
      ((S : Mat 3) * Qpol (Yplane θ η ξ) (Yplane α τ ρ)).trace +
      Real.sqrt 2 * (p * (matchingH S α τ ρ).re + q * (matchingH S α τ ρ).im) := by
  dsimp only
  have hs := S.property
  have hs01 : (S : Mat 3) 1 0 = (S : Mat 3) 0 1 := congrFun (congrFun hs 0) 1
  have hs02 : (S : Mat 3) 2 0 = (S : Mat 3) 0 2 := congrFun (congrFun hs 0) 2
  have hs12 : (S : Mat 3) 2 1 = (S : Mat 3) 1 2 := congrFun (congrFun hs 1) 2
  have hcα (n : ℕ) : Real.cos α ^ (n+2) = Real.cos α ^ n * (1-Real.sin α ^ 2) := by
    rw [pow_add, Real.cos_sq']
  have hcθ (n : ℕ) : Real.cos θ ^ (n+2) = Real.cos θ ^ n * (1-Real.sin θ ^ 2) := by
    rw [pow_add, Real.cos_sq']
  have hsq (n : ℕ) : Real.sqrt 2 ^ (n+2) = Real.sqrt 2 ^ n * 2 := by
    rw [pow_add, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  rw [weightedPairing_complex_trace]
  simp only [matchingH, matchingV, matchingN, matchingR0,
    Fθ, Umat, V0, wPhase_inv_trig]
  simp [wPhase, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Qpol, QuadraticMap.polar, Qmat, Yplane, dVec, kVec,
    Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fin.sum_univ_succ, pow_two, Complex.mul_re, Complex.mul_im, hs01, hs02, hs12]
  generalize (S : Mat 3) 0 0 = a, (S : Mat 3) 0 1 = b, (S : Mat 3) 0 2 = c,
    (S : Mat 3) 1 1 = d, (S : Mat 3) 1 2 = e, (S : Mat 3) 2 2 = f
  ring_nf
  simp only [(show Real.cos α ^ 2 = Real.cos α ^ 0 * (1 - Real.sin α ^ 2) from hcα 0),
    (show Real.cos α ^ 3 = Real.cos α ^ 1 * (1 - Real.sin α ^ 2) from hcα 1),
    (show Real.cos α ^ 4 = Real.cos α ^ 2 * (1 - Real.sin α ^ 2) from hcα 2),
    (show Real.cos α ^ 6 = Real.cos α ^ 4 * (1 - Real.sin α ^ 2) from hcα 4),
    (show Real.cos θ ^ 2 = Real.cos θ ^ 0 * (1 - Real.sin θ ^ 2) from hcθ 0),
    (show Real.cos θ ^ 3 = Real.cos θ ^ 1 * (1 - Real.sin θ ^ 2) from hcθ 1),
    (show Real.sqrt 2 ^ 2 = Real.sqrt 2 ^ 0 * 2 from hsq 0), pow_zero]
  ring

-- @node: matchingRotation_numerator
/-- For [complex coefficients g and h](hyp:g,h), if [the sum of their squared
moduli is nonzero](hyp:hd), then
[multiplying the matching rotation by that sum gives the matrix whose diagonal
entries are the squared modulus of g plus the squared modulus of h times,
respectively, the matching phase and its conjugate, and whose upper and lower
off-diagonal entries are, respectively, the conjugate of g times h times one
minus the matching phase and the negative of that product](goal). -/
lemma matchingRotation_numerator (g h : ℂ) (α θ : ℝ) (hd : matchingDelta g h ≠ 0) :
    !![(Complex.normSq g : ℂ) + (Complex.normSq h : ℂ) * matchingKappa α θ,
       star (g * h * (1 - matchingKappa α θ));
       -(g * h * (1 - matchingKappa α θ)),
       (Complex.normSq g : ℂ) + (Complex.normSq h : ℂ) * star (matchingKappa α θ)] =
      (matchingDelta g h : ℂ) • matchingRotation g h α θ := by
  have hd' : (matchingDelta g h : ℂ) ≠ 0 := by exact_mod_cast hd
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matchingRotation, rotationA, rotationB, hd, star_div₀, star_add, star_mul,
      Complex.star_def] <;> field_simp <;> ring
-- @node: weightedPairing_ofReal_smul
/-- [Scaling the second complex factor by a real number scales its weighted
pairing with the first factor by the same real number](goal). -/
lemma weightedPairing_ofReal_smul (S : Sym3) (F H : Matrix (Fin 3) (Fin 2) ℂ) (r : ℝ) :
    weightedPairing S F ((r : ℂ) • H) = r * weightedPairing S F H := by
  simp [weightedPairing, realify, Matrix.trace, Matrix.mul_apply,
    Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im]
  ring

set_option maxHeartbeats 0 in
-- Reduce the finite row expressions using the unit-circle identity.
-- @node: matchingGH_explicit
/-- [The matching coefficient g equals square root of two times the difference
between the vertical coefficient times the sum of the second and third diagonal
weights and the planar coefficient times the inverse reference phase times the
sum of the first-to-third weight and the imaginary unit times the
second-to-third weight. The matching coefficient h equals square root of two
times the planar coefficient times the inverse reference phase times a sum:
the imaginary unit times the first-to-second weight, plus the inverse reference
phase times the difference between the third diagonal weight times cosine of
the reference angle and the imaginary unit times the second diagonal weight
times sine of that angle](goal). -/
lemma matchingGH_explicit (S : Sym3) (α τ ρ : ℝ) :
    matchingG S α τ ρ = (Real.sqrt 2 : ℂ) *
      ((ρ : ℂ) * ((S : Mat 3) 1 1 + (S : Mat 3) 2 2) -
        τ * (wPhase α)⁻¹ * ((S : Mat 3) 0 2 + Complex.I * (S : Mat 3) 1 2)) ∧
    matchingH S α τ ρ = (Real.sqrt 2 : ℂ) * τ * (wPhase α)⁻¹ *
      (Complex.I * (S : Mat 3) 0 1 + (wPhase α)⁻¹ *
        ((S : Mat 3) 2 2 * Real.cos α - Complex.I * (S : Mat 3) 1 1 * Real.sin α)) := by
  have hs := S.property
  have hs01 : (S : Mat 3) 1 0 = (S : Mat 3) 0 1 := congrFun (congrFun hs 0) 1
  have hs02 : (S : Mat 3) 2 0 = (S : Mat 3) 0 2 := congrFun (congrFun hs 0) 2
  have hs12 : (S : Mat 3) 2 1 = (S : Mat 3) 1 2 := congrFun (congrFun hs 1) 2
  have hc2 := Real.cos_sq' α
  have hc3 : Real.cos α ^ 3 = Real.cos α * (1 - Real.sin α ^ 2) := by
    rw [pow_succ, hc2]; ring
  simp only [matchingG, matchingH, matchingV, matchingN, matchingR0,
    Fθ, Umat, V0, wPhase_inv_trig]
  constructor <;> apply Complex.ext <;>
    simp [wPhase, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Matrix.mul_apply, Fin.sum_univ_succ, pow_two, Complex.mul_re,
      Complex.mul_im, hs01, hs02, hs12] <;>
    (generalize (S : Mat 3) 0 1 = b, (S : Mat 3) 0 2 = c,
      (S : Mat 3) 1 1 = d, (S : Mat 3) 1 2 = e, (S : Mat 3) 2 2 = f) <;>
    ring_nf <;> simp only [hc2, hc3] <;> ring

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 0 in
-- The numerator is a finite polynomial identity in the symmetric entries and phases.
set_option maxRecDepth 10000 in
-- @node: matchingR0_pairing_numerator
/-- [Pairing an angular factor with the reference factor multiplied by the
unnormalized matching rotation gives the sum of the squared moduli of g and h
times the trace of the weight matrix times the polarized quadratic matrix of
the varying and reference angular-plane vectors](goal). Here g and h are the
reference matching coefficients, k is the matching phase, and the unnormalized
rotation has diagonal entries $|g|^2+|h|^2k$ and $|g|^2+|h|^2\overline{k}$,
upper off-diagonal entry the conjugate of $gh(1-k)$, and lower off-diagonal
entry $-gh(1-k)$. -/
lemma matchingR0_pairing_numerator (S : Sym3) (α τ ρ θ η ξ : ℝ) :
    let g := matchingG S α τ ρ
    let h := matchingH S α τ ρ
    let k := matchingKappa α θ
    let M : Matrix (Fin 2) (Fin 2) ℂ :=
      !![(Complex.normSq g : ℂ) + (Complex.normSq h : ℂ) * k,
         star (g * h * (1 - k));
         -(g * h * (1 - k)),
         (Complex.normSq g : ℂ) + (Complex.normSq h : ℂ) * star k]
    weightedPairing S (Fθ θ η ξ) (matchingR0 α τ ρ * M) =
      matchingDelta g h *
        ((S : Mat 3) * Qpol (Yplane θ η ξ) (Yplane α τ ρ)).trace := by
  dsimp only
  have hs := S.property
  have hs01 : (S : Mat 3) 1 0 = (S : Mat 3) 0 1 := congrFun (congrFun hs 0) 1
  have hs02 : (S : Mat 3) 2 0 = (S : Mat 3) 0 2 := congrFun (congrFun hs 0) 2
  have hs12 : (S : Mat 3) 2 1 = (S : Mat 3) 1 2 := congrFun (congrFun hs 1) 2
  have hcα (n : ℕ) : Real.cos α ^ (n+2) = Real.cos α ^ n * (1-Real.sin α ^ 2) := by
    rw [pow_add, Real.cos_sq']
  have hcθ (n : ℕ) : Real.cos θ ^ (n+2) = Real.cos θ ^ n * (1-Real.sin θ ^ 2) := by
    rw [pow_add, Real.cos_sq']
  have hsq (n : ℕ) : Real.sqrt 2 ^ (n+2) = Real.sqrt 2 ^ n * 2 := by
    rw [pow_add, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  rw [weightedPairing_complex_trace]
  simp only [matchingDelta, (matchingGH_explicit S α τ ρ).1,
    (matchingGH_explicit S α τ ρ).2, matchingR0,
    Fθ, Umat, V0, matchingKappa, matchingW0, div_eq_mul_inv, wPhase_inv_trig]
  simp [wPhase, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Qpol, QuadraticMap.polar, Qmat, Yplane, dVec, kVec,
    Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fin.sum_univ_succ, pow_two, Complex.mul_re, Complex.mul_im,
    Complex.normSq_apply, hs01, hs02, hs12]
  generalize (S : Mat 3) 0 0 = a, (S : Mat 3) 0 1 = b, (S : Mat 3) 0 2 = c,
    (S : Mat 3) 1 1 = d, (S : Mat 3) 1 2 = e, (S : Mat 3) 2 2 = f
  ring_nf
  simp only [(show Real.cos α ^ 2 = Real.cos α ^ 0 * (1 - Real.sin α ^ 2) from hcα 0),
    (show Real.cos α ^ 3 = Real.cos α ^ 1 * (1 - Real.sin α ^ 2) from hcα 1),
    (show Real.cos α ^ 4 = Real.cos α ^ 2 * (1 - Real.sin α ^ 2) from hcα 2),
    (show Real.cos α ^ 5 = Real.cos α ^ 3 * (1 - Real.sin α ^ 2) from hcα 3),
    (show Real.cos α ^ 6 = Real.cos α ^ 4 * (1 - Real.sin α ^ 2) from hcα 4),
    (show Real.cos α ^ 7 = Real.cos α ^ 5 * (1 - Real.sin α ^ 2) from hcα 5),
    (show Real.cos α ^ 8 = Real.cos α ^ 6 * (1 - Real.sin α ^ 2) from hcα 6),
    (show Real.cos α ^ 9 = Real.cos α ^ 7 * (1 - Real.sin α ^ 2) from hcα 7),
    (show Real.cos α ^ 10 = Real.cos α ^ 8 * (1 - Real.sin α ^ 2) from hcα 8),
    (show Real.cos α ^ 11 = Real.cos α ^ 9 * (1 - Real.sin α ^ 2) from hcα 9),
    (show Real.cos α ^ 12 = Real.cos α ^ 10 * (1 - Real.sin α ^ 2) from hcα 10),
    (show Real.cos α ^ 13 = Real.cos α ^ 11 * (1 - Real.sin α ^ 2) from hcα 11),
    (show Real.cos θ ^ 2 = Real.cos θ ^ 0 * (1 - Real.sin θ ^ 2) from hcθ 0),
    (show Real.cos θ ^ 3 = Real.cos θ ^ 1 * (1 - Real.sin θ ^ 2) from hcθ 1),
    (show Real.cos θ ^ 4 = Real.cos θ ^ 2 * (1 - Real.sin θ ^ 2) from hcθ 2),
    (show Real.cos θ ^ 5 = Real.cos θ ^ 3 * (1 - Real.sin θ ^ 2) from hcθ 3),
    (show Real.cos θ ^ 6 = Real.cos θ ^ 4 * (1 - Real.sin θ ^ 2) from hcθ 4),
    (show Real.cos θ ^ 7 = Real.cos θ ^ 5 * (1 - Real.sin θ ^ 2) from hcθ 5),
    (show Real.cos θ ^ 8 = Real.cos θ ^ 6 * (1 - Real.sin θ ^ 2) from hcθ 6),
    (show Real.cos θ ^ 9 = Real.cos θ ^ 7 * (1 - Real.sin θ ^ 2) from hcθ 7),
    (show Real.cos θ ^ 10 = Real.cos θ ^ 8 * (1 - Real.sin θ ^ 2) from hcθ 8),
    (show Real.cos θ ^ 11 = Real.cos θ ^ 9 * (1 - Real.sin θ ^ 2) from hcθ 9),
    (show Real.cos θ ^ 12 = Real.cos θ ^ 10 * (1 - Real.sin θ ^ 2) from hcθ 10),
    (show Real.cos θ ^ 13 = Real.cos θ ^ 11 * (1 - Real.sin θ ^ 2) from hcθ 11),
    (show Real.sqrt 2 ^ 2 = Real.sqrt 2 ^ 0 * 2 from hsq 0),
    (show Real.sqrt 2 ^ 3 = Real.sqrt 2 ^ 1 * 2 from hsq 1),
    (show Real.sqrt 2 ^ 4 = Real.sqrt 2 ^ 2 * 2 from hsq 2),
    (show Real.sqrt 2 ^ 5 = Real.sqrt 2 ^ 3 * 2 from hsq 3),
    (show Real.sqrt 2 ^ 6 = Real.sqrt 2 ^ 4 * 2 from hsq 4),
    (show Real.sqrt 2 ^ 7 = Real.sqrt 2 ^ 5 * 2 from hsq 5),
    (show Real.sqrt 2 ^ 8 = Real.sqrt 2 ^ 6 * 2 from hsq 6),
    (show Real.sqrt 2 ^ 9 = Real.sqrt 2 ^ 7 * 2 from hsq 7),
    (show Real.sqrt 2 ^ 10 = Real.sqrt 2 ^ 8 * 2 from hsq 8),
    (show Real.sqrt 2 ^ 11 = Real.sqrt 2 ^ 9 * 2 from hsq 9),
    (show Real.sqrt 2 ^ 12 = Real.sqrt 2 ^ 10 * 2 from hsq 10),
    (show Real.sqrt 2 ^ 13 = Real.sqrt 2 ^ 11 * 2 from hsq 11), pow_zero]
  ring

-- @node: matchingCandidate_pairing
/-- If [the reference planar coefficient is strictly positive](hyp:hτ), then
[the weighted pairing of the angular factor with the candidate matching factor
equals the trace of the symmetric weight matrix times the polarized quadratic
matrix of the varying and reference angular-plane vectors, for every varying
angle and every pair of varying planar and vertical coefficients](goal). -/
lemma matchingCandidate_pairing (S : Sym3) (α τ ρ : ℝ) (hτ : 0 < τ)
    (θ η ξ : ℝ) :
    weightedPairing S (Fθ θ η ξ) (matchingCandidate S α τ ρ θ) =
      ((S : Mat 3) * Qpol (Yplane θ η ξ) (Yplane α τ ρ)).trace := by
  by_cases hd : matchingDelta (matchingG S α τ ρ) (matchingH S α τ ρ) = 0
  · have hh : matchingH S α τ ρ = 0 := Complex.normSq_eq_zero.mp (by
      have hg := Complex.normSq_nonneg (matchingG S α τ ρ)
      have hh := Complex.normSq_nonneg (matchingH S α τ ρ)
      unfold matchingDelta at hd
      linarith)
    have hrot : matchingRotation (matchingG S α τ ρ) (matchingH S α τ ρ) α θ = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [matchingRotation, rotationA, rotationB, hd]
    rw [matchingCandidate, hrot, Matrix.mul_one]
    simpa only [hh, Complex.zero_re, Complex.zero_im, mul_zero, add_zero] using
      matchingR0_pairing_expansion S α τ ρ θ η ξ
  · have hn := matchingR0_pairing_numerator S α τ ρ θ η ξ
    dsimp only at hn
    rw [matchingRotation_numerator _ _ α θ hd, Matrix.mul_smul,
      weightedPairing_ofReal_smul] at hn
    exact mul_left_cancel₀ hd hn

-- @node: lem:matching
/-- For an arbitrary real symmetric weight matrix, if [the first two coordinates
of the target three-vector are not both zero](hyp:hz), then [there exists a
three-by-two complex matrix function of the angle whose entries are complex
trigonometric polynomials of degree at most two, whose realified row Gram
matrix is the quadratic matrix at the target vector, and whose weighted pairing
with every angular factor equals the trace of the weight matrix times the
polarized quadratic matrix of the corresponding angular-plane vector and the
target vector](goal). -/
lemma matching_exists (S : Sym3) (z : Fin 3 → ℝ)
-- @realizes S(arbitrary symmetric real weight, with no PSD restriction)
    (hz : MatchingNondegenerate z) :
    ∃ C : ℝ → Matrix (Fin 3) (Fin 2) ℂ, -- @realizes C(\theta)(chosen matrix function for S and z)
      (∀ i j, IsComplexTrigPolyLE 2 (fun θ => C θ i j)) ∧
      ∀ θ η ξ : ℝ,
        realify (C θ) * (realify (C θ))ᵀ = Qmat z ∧
        weightedPairing S (Fθ θ η ξ) (C θ) =
          ((S : Mat 3) * Qpol (Yplane θ η ξ) z).trace := by
  obtain ⟨α, τ, ρ, hτ, rfl⟩ := matching_polar_decomposition z hz
  refine ⟨matchingCandidate S α τ ρ, matchingCandidate_degree S α τ ρ, ?_⟩
  intro θ η ξ
  exact ⟨matchingCandidate_gram S α τ ρ θ,
    matchingCandidate_pairing S α τ ρ hτ θ η ξ⟩

end Papers.OaiExactSemidefiniteLift

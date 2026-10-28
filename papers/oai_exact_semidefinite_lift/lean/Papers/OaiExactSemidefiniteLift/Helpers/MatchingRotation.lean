module

public import Papers.OaiExactSemidefiniteLift.Helpers.Gram

/-!
# The explicit degree-two matching rotation

All weights are arbitrary real symmetric matrices. The vanishing-denominator
case is built into the coefficients, exactly as in the paper.
-/

@[expose] public section

noncomputable section

namespace Papers.OaiExactSemidefiniteLift

open Matrix

/-- For [a reference angle](hyp:α), [a planar coefficient](hyp:τ), and
[a vertical coefficient](hyp:ρ), the [reference Gram factor](goal) is the
angular Gram factor at these three values. -/
def matchingR0 (α τ ρ : ℝ) : Matrix (Fin 3) (Fin 2) ℂ := -- @realizes R_0(fixed Gram factor)
  Fθ α τ ρ

/-- For [a real symmetric weight matrix](hyp:S), [a reference angle](hyp:α),
[a planar coefficient](hyp:τ), and [a vertical coefficient](hyp:ρ), the
[weighted reference factor](goal) is the weight matrix, viewed over the complex
numbers, multiplied by the reference Gram factor. -/
def matchingN (S : Sym3) (α τ ρ : ℝ) : Matrix (Fin 3) (Fin 2) ℂ :=
  -- @realizes N(complex product S R_0)
  ((S : Mat 3).map (fun r => (r : ℂ))) * matchingR0 α τ ρ

/-- For [a symmetric weight matrix](hyp:S), [a reference angle](hyp:α),
[a planar coefficient](hyp:τ), [a vertical coefficient](hyp:ρ), and
[a row index](hyp:j), the [selected weighted row](goal) is that row of the
weighted reference factor. -/
def matchingRow (S : Sym3) (α τ ρ : ℝ) (j : Fin 3) : Fin 2 → ℂ := -- @realizes N_j(rows of S R_0)
  matchingN S α τ ρ j

/-- For [a symmetric weight matrix](hyp:S), [a reference angle](hyp:α),
[a planar coefficient](hyp:τ), and [a vertical coefficient](hyp:ρ), the
[difference row](goal) is the third weighted reference row minus the imaginary
unit times the second weighted reference row. -/
def matchingV (S : Sym3) (α τ ρ : ℝ) : Fin 2 → ℂ := -- @realizes v(complex row N_3 - i N_2)
  fun j => matchingN S α τ ρ 2 j - Complex.I * matchingN S α τ ρ 1 j

/-- For [a symmetric weight matrix](hyp:S), [a reference angle](hyp:α),
[a planar coefficient](hyp:τ), and [a vertical coefficient](hyp:ρ), the
[sum row](goal) is the third weighted reference row plus the imaginary unit
times the second weighted reference row. -/
def matchingMRow (S : Sym3) (α τ ρ : ℝ) : Fin 2 → ℂ := -- @realizes m(complex row N_3 + i N_2)
  fun j => matchingN S α τ ρ 2 j + Complex.I * matchingN S α τ ρ 1 j

/-- For [a symmetric weight matrix](hyp:S), [a reference angle](hyp:α),
[a planar coefficient](hyp:τ), and [a vertical coefficient](hyp:ρ), the
[first weighted row](goal) is the first row of the weighted reference factor. -/
def matchingNRow (S : Sym3) (α τ ρ : ℝ) : Fin 2 → ℂ := -- @realizes n(first complex row)
  matchingN S α τ ρ 0

/-- For [a symmetric weight matrix](hyp:S), [a reference angle](hyp:α),
[a planar coefficient](hyp:τ), and [a vertical coefficient](hyp:ρ), the
[complex matching coefficient g](goal) is the first entry of the difference row
plus the complex conjugate of its second entry. -/
def matchingG (S : Sym3) (α τ ρ : ℝ) : ℂ := -- @realizes g(v_+ plus conjugate v_-)
  matchingV S α τ ρ 0 + star (matchingV S α τ ρ 1)

/-- For [a symmetric weight matrix](hyp:S), [a reference angle](hyp:α),
[a planar coefficient](hyp:τ), and [a vertical coefficient](hyp:ρ), the
[complex matching coefficient h](goal) is the first entry of the difference row
minus the complex conjugate of its second entry. -/
def matchingH (S : Sym3) (α τ ρ : ℝ) : ℂ := -- @realizes h(v_+ minus conjugate v_-)
  matchingV S α τ ρ 0 - star (matchingV S α τ ρ 1)

/-- For [a reference angle](hyp:α), the [reference unit phase](goal) is the
complex exponential of the imaginary unit times that angle. -/
def matchingW0 (α : ℝ) : ℂ := wPhase α -- @realizes w_0(fixed unit phase)

/-- For [a reference angle](hyp:α) and [a varying angle](hyp:θ), the
[matching phase](goal) is the square of the ratio of the reference unit phase
to the unit phase at the varying angle. -/
def matchingKappa (α θ : ℝ) : ℂ := -- @realizes \kappa(unit rotation phase)
  (matchingW0 α / wPhase θ)^2

/-- For [a complex coefficient g](hyp:g) and [a complex coefficient h](hyp:h),
the [normalizing denominator](goal) is the sum of their squared moduli. -/
def matchingDelta (g h : ℂ) : ℝ := Complex.normSq g + Complex.normSq h
-- @realizes \delta(nonnegative squared norm sum)

/-- For [a complex coefficient g](hyp:g), [a complex coefficient h](hyp:h),
[a reference angle](hyp:α), and [a varying angle](hyp:θ), the
[first rotation coefficient](goal) is [one when the normalizing denominator is
zero](step:1); [otherwise it is the squared modulus of g plus the squared
modulus of h times the matching phase, divided by that denominator](step:2). -/
def rotationA (g h : ℂ) (α θ : ℝ) : ℂ := -- @realizes a(prescribed complex rotation coefficient)
  if matchingDelta g h = 0 then 1 else
    ((Complex.normSq g : ℂ) + (Complex.normSq h : ℂ) * matchingKappa α θ) /
      (matchingDelta g h : ℂ)

/-- For [a complex coefficient g](hyp:g), [a complex coefficient h](hyp:h),
[a reference angle](hyp:α), and [a varying angle](hyp:θ), the
[second rotation coefficient](goal) is [zero when the normalizing denominator
is zero](step:1); [otherwise it is the complex conjugate of the product of g,
h, and one minus the matching phase, divided by that denominator](step:2). -/
def rotationB (g h : ℂ) (α θ : ℝ) : ℂ := -- @realizes b(prescribed conjugate rotation coefficient)
  if matchingDelta g h = 0 then 0 else
    star (g * h * (1 - matchingKappa α θ) / (matchingDelta g h : ℂ))

/-- For [a complex coefficient g](hyp:g), [a complex coefficient h](hyp:h),
[a reference angle](hyp:α), and [a varying angle](hyp:θ), the
[matching rotation matrix](goal) has the first and second rotation coefficients
in its first row, and minus the conjugate of the second and the conjugate of
the first in its second row. -/
def matchingRotation (g h : ℂ) (α θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  -- @realizes M(explicit two-by-two rotation)
  !![rotationA g h α θ, rotationB g h α θ;
     -star (rotationB g h α θ), star (rotationA g h α θ)]

/-- For [a symmetric weight matrix](hyp:S), [a reference angle](hyp:α),
[a planar coefficient](hyp:τ), [a vertical coefficient](hyp:ρ), and
[a varying angle](hyp:θ), the [candidate matching factor](goal) is the reference
Gram factor multiplied by the matching rotation using the weight-dependent
coefficients g and h. -/
def matchingCandidate (S : Sym3) (α τ ρ θ : ℝ) : Matrix (Fin 3) (Fin 2) ℂ :=
  matchingR0 α τ ρ * matchingRotation (matchingG S α τ ρ) (matchingH S α τ ρ) α θ

-- @node: matching_polar_decomposition
/-- If [a real three-vector has nonzero first two coordinates as a pair](hyp:hz),
then [it admits an angular-plane representation with a strictly positive planar
coefficient and a real vertical coefficient](goal). -/
lemma matching_polar_decomposition (z : Fin 3 → ℝ) (hz : MatchingNondegenerate z) :
    ∃ (α : ℝ) (τ : ℝ) (ρ : ℝ),
    -- @realizes \alpha(real polar angle)
    -- @realizes \tau(planar coefficient)
    -- @realizes \rho(real vertical coefficient)
      0 < τ ∧ z = Yplane α τ ρ := by
  let q : ℂ := ⟨z 0, z 1⟩
  have hq : q ≠ 0 := by
    intro h
    apply hz
    exact Prod.ext (congrArg Complex.re h) (congrArg Complex.im h)
  refine ⟨q.arg, ‖q‖, z 2, norm_pos_iff.mpr hq, ?_⟩
  ext i
  fin_cases i
  · simpa [Yplane, dVec, kVec, q] using (Complex.norm_mul_cos_arg q).symm
  · simpa [Yplane, dVec, kVec, q] using (Complex.norm_mul_sin_arg q).symm
  · simp [Yplane, dVec, kVec]
      -- @realizes \tau(strict positivity of the planar coefficient)

-- @node: matching_phase_norms
/-- [The reference phase and the matching phase both have modulus one at every
pair of real angles](goal). -/
lemma matching_phase_norms (α θ : ℝ) :
    ‖matchingW0 α‖ = 1 ∧ -- @realizes w_0(unit modulus)
    ‖matchingKappa α θ‖ = 1 := by
  have hα := (angular_bounds α).2.2
  have hθ := (angular_bounds θ).2.2
  constructor
  · exact hα
  · simp [matchingKappa, matchingW0, norm_pow, norm_div, hα, hθ] -- @realizes \kappa(unit modulus)

-- @node: matchingDelta_nonneg
/-- For [any two complex coefficients g and h](hyp:g,h), [the sum of their
squared moduli is nonnegative](goal). -/
lemma matchingDelta_nonneg (g h : ℂ) : 0 ≤ matchingDelta g h := by
  exact add_nonneg (Complex.normSq_nonneg g) (Complex.normSq_nonneg h)

-- @node: matchingRotation_coefficients_normalized
/-- For [any two complex coefficients g and h](hyp:g,h), [at any reference and
varying angles, the sum of each rotation coefficient times its complex
conjugate is one](goal). -/
lemma matchingRotation_coefficients_normalized (g h : ℂ) (α θ : ℝ) :
    rotationA g h α θ * star (rotationA g h α θ) +
      rotationB g h α θ * star (rotationB g h α θ) = 1 := by
  by_cases hd : matchingDelta g h = 0
  · simp [rotationA, rotationB, hd]
  · have hd' : (matchingDelta g h : ℂ) ≠ 0 := by exact_mod_cast hd
    have hk : matchingKappa α θ * star (matchingKappa α θ) = 1 := by
      rw [show star (matchingKappa α θ) = starRingEnd ℂ (matchingKappa α θ) from rfl,
        Complex.mul_conj, Complex.normSq_eq_norm_sq, (matching_phase_norms α θ).2]
      norm_num
    have hg : g * star g = (Complex.normSq g : ℂ) := Complex.mul_conj g
    have hh : h * star h = (Complex.normSq h : ℂ) := Complex.mul_conj h
    simp only [rotationA, rotationB, hd, if_false, star_star, star_div₀,
      star_add, star_mul, star_sub, star_one, Complex.star_def, Complex.conj_ofReal]
    field_simp
    simp only [matchingDelta, Complex.ofReal_add, starRingEnd_apply, star_star]
    linear_combination
      (Complex.normSq h : ℂ)^2 * hk +
      (Complex.normSq g : ℂ) * (Complex.normSq h : ℂ) * hk +
      (1 - matchingKappa α θ) * (1 - star (matchingKappa α θ)) *
        (h * star h * hg + (Complex.normSq g : ℂ) * hh)

-- @node: matchingRotation_unitary
/-- For [any two complex coefficients g and h](hyp:g,h), [the matching rotation
is unitary: multiplying it by its conjugate transpose in either order gives the
identity matrix](goal). -/
lemma matchingRotation_unitary (g h : ℂ) (α θ : ℝ) :
    matchingRotation g h α θ * (matchingRotation g h α θ).conjTranspose = 1 ∧
    (matchingRotation g h α θ).conjTranspose * matchingRotation g h α θ = 1 := by
  have hn := matchingRotation_coefficients_normalized g h α θ
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [matchingRotation, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.conjTranspose_apply] <;>
    (try simp only [starRingEnd_apply, star_star]) <;>
    first | linear_combination hn | ring

-- @node: matchingRotation_at_angle
/-- For [any two complex coefficients g and h](hyp:g,h), [at the reference
angle, the matching rotation equals the identity matrix](goal). -/
lemma matchingRotation_at_angle (g h : ℂ) (α : ℝ) :
    matchingRotation g h α α = 1 := by
  have hw : wPhase α ≠ 0 := Complex.exp_ne_zero _
  have hk : matchingKappa α α = 1 := by
    simp [matchingKappa, matchingW0, hw]
  have ha : rotationA g h α α = 1 := by
    by_cases hd : matchingDelta g h = 0
    · simp [rotationA, hd]
    · have hd' : (matchingDelta g h : ℂ) ≠ 0 := by exact_mod_cast hd
      simp [rotationA, hd, hk, matchingDelta, ← Complex.ofReal_add] at *
  have hb : rotationB g h α α = 0 := by simp [rotationB, hk]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matchingRotation, ha, hb]

-- @node: complexTrig_two_modes
/-- [A complex constant plus arbitrary complex multiples of the exponential
modes with frequencies minus two and two is a complex trigonometric polynomial
of degree at most two](goal). -/
lemma complexTrig_two_modes (a b c : ℂ) :
    IsComplexTrigPolyLE 2 (fun θ => a + b * Complex.exp (-2 * θ * Complex.I) +
      c * Complex.exp (2 * θ * Complex.I)) := by
  refine ⟨fun l => if l = -2 then b else if l = 0 then a else if l = 2 then c else 0, ?_⟩
  intro θ
  have hi : Finset.Icc (-2 : ℤ) 2 = {-2, -1, 0, 1, 2} := by decide
  norm_num [hi]
  ring

-- @node: matchingKappa_fourier
/-- [The matching phase equals the square of the reference phase times the
complex exponential of minus twice the varying angle times the imaginary
unit](goal). -/
lemma matchingKappa_fourier (α θ : ℝ) :
    matchingKappa α θ = matchingW0 α ^ 2 * Complex.exp (-2 * θ * Complex.I) := by
  rw [matchingKappa, div_pow, div_eq_mul_inv, wPhase, ← Complex.exp_nat_mul,
    ← Complex.exp_neg]
  congr 1
  congr 1
  ring

-- @node: matchingKappa_star_fourier
/-- [The complex conjugate of the matching phase equals the conjugate of the
squared reference phase times the complex exponential of twice the varying
angle times the imaginary unit](goal). -/
lemma matchingKappa_star_fourier (α θ : ℝ) :
    star (matchingKappa α θ) = star (matchingW0 α ^ 2) *
      Complex.exp (2 * θ * Complex.I) := by
  rw [matchingKappa_fourier, star_mul]
  have he : star (Complex.exp (-2 * (θ : ℂ) * Complex.I)) =
      Complex.exp (2 * θ * Complex.I) := by
    rw [Complex.star_def, ← Complex.exp_conj]
    congr 1
    simp only [map_mul, map_neg, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [he]
  simp [star_pow, mul_comm]

-- @node: complexTrig_matching_modes
/-- [For any fixed reference angle, a complex constant plus arbitrary complex
multiples of the matching phase and its conjugate is a complex trigonometric
polynomial of degree at most two in the varying angle](goal). -/
lemma complexTrig_matching_modes (α : ℝ) (a b c : ℂ) :
    IsComplexTrigPolyLE 2 (fun θ => a + b * matchingKappa α θ +
      c * star (matchingKappa α θ)) := by
  convert complexTrig_two_modes a (b * matchingW0 α ^ 2)
    (c * star (matchingW0 α ^ 2)) using 1
  ext θ
  rw [matchingKappa_star_fourier, matchingKappa_fourier]
  ring

-- @node: matchingCandidate_degree
/-- [For every symmetric weight matrix and fixed reference angle, planar
coefficient, and vertical coefficient, each entry of the candidate matching
factor is a complex trigonometric polynomial of degree at most two in the
varying angle](goal). -/
lemma matchingCandidate_degree (S : Sym3) (α τ ρ : ℝ) (i : Fin 3) (j : Fin 2) :
    IsComplexTrigPolyLE 2 (fun θ => matchingCandidate S α τ ρ θ i j) := by
  let g := matchingG S α τ ρ
  let h := matchingH S α τ ρ
  let r := matchingR0 α τ ρ i 0
  let s := matchingR0 α τ ρ i 1
  by_cases hd : matchingDelta g h = 0
  · simp only [g, h] at hd
    convert complexTrig_matching_modes α (matchingR0 α τ ρ i j) 0 0 using 1
    ext θ
    fin_cases j <;>
      simp [matchingCandidate, matchingRotation, rotationA, rotationB, g, h, hd,
        Matrix.mul_apply, Fin.sum_univ_succ]
  · simp only [g, h] at hd
    fin_cases j
    · convert complexTrig_matching_modes α
        ((r * (Complex.normSq g : ℂ) - s * g * h) / (matchingDelta g h : ℂ))
        ((r * (Complex.normSq h : ℂ) + s * g * h) / (matchingDelta g h : ℂ)) 0 using 1
      ext θ
      simp [matchingCandidate, matchingRotation, rotationA, rotationB, g, h, hd,
        Matrix.mul_apply, Fin.sum_univ_succ, star_star, r, s]
      <;> ring
    · convert complexTrig_matching_modes α
        ((r * star g * star h + s * (Complex.normSq g : ℂ)) / (matchingDelta g h : ℂ))
        0 ((-r * star g * star h + s * (Complex.normSq h : ℂ)) /
          (matchingDelta g h : ℂ)) using 1
      ext θ
      simp [matchingCandidate, matchingRotation, rotationA, rotationB, g, h, hd,
        Matrix.mul_apply, Fin.sum_univ_succ, star_div₀, star_sub, star_mul, star_add,
        Complex.star_def, r, s]
      <;> ring

-- @node: realify_gram_eq_re
/-- [For any three-by-two complex matrix, the row Gram matrix obtained by
separating its real and imaginary parts equals the entrywise real part of its
complex row Gram matrix](goal). -/
lemma realify_gram_eq_re (F : Matrix (Fin 3) (Fin 2) ℂ) :
    realify F * (realify F)ᵀ = (F * F.conjTranspose).map Complex.re := by
  ext i j
  simp [realify, Matrix.mul_apply, Fin.sum_univ_succ,
    Matrix.conjTranspose_apply, Complex.mul_re]
  <;> ring

-- @node: matchingCandidate_gram
/-- [The realified candidate matching factor has row Gram matrix equal to the
quadratic matrix at the reference angular-plane vector, for every symmetric
weight matrix and every varying angle](goal). -/
lemma matchingCandidate_gram (S : Sym3) (α τ ρ θ : ℝ) :
    realify (matchingCandidate S α τ ρ θ) * (realify (matchingCandidate S α τ ρ θ))ᵀ =
      Qmat (Yplane α τ ρ) := by
  rw [realify_gram_eq_re, matchingCandidate, Matrix.conjTranspose_mul]
  have hu := (matchingRotation_unitary
    (matchingG S α τ ρ) (matchingH S α τ ρ) α θ).1
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc
    (matchingRotation (matchingG S α τ ρ) (matchingH S α τ ρ) α θ), hu,
    Matrix.one_mul, ← realify_gram_eq_re]
  exact gram_identity.1 α τ ρ

end Papers.OaiExactSemidefiniteLift

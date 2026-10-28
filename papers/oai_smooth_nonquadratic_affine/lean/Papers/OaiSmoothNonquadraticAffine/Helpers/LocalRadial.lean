module

public import Papers.OaiSmoothNonquadraticAffine.Helpers.LocalEstimates

/-! # Radial profiles and the integrated local equations

The substitution ρ = rv converts the normalized averages into radial
integrals. These identities use only the continuous fixed point.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace OaiSmoothNonquadraticAffine

-- @node: localRadialProfiles
/-- For [a positive cutoff δ](hyp:hδ), [a trial pair](hyp:fp) [belonging to the
admissible trial set](hyp:hfp), and [a real radius r](hyp:r), the [local radial
profiles](goal) are the pair of integral primitives evaluated at r²/2. -/
def localRadialProfiles {δ : ℝ} (hδ : 0 < δ) (fp : LocalTrialPair δ)
    (hfp : fp ∈ localTrialSet δ) (r : ℝ) : ℝ × ℝ :=
  localIntegralPrimitives hδ fp hfp (r ^ 2 / 2)

-- @node: localRadialProfiles_hasDerivAt
/-- With [δ positive](hyp:hδ) and [an admissible trial pair](hyp:hfp), [at every
real radius r the first radial profile has derivative rQ(r²/2), and the second
has derivative $-KrJ(r^2/2)Q(r^2/2)^{1-d}$](goal).

Here Q and J are the normalized factors, K is the radial constant, and d is
the radial dimension. -/
lemma localRadialProfiles_hasDerivAt {δ : ℝ} (hδ : 0 < δ)
    {fp : LocalTrialPair δ} (hfp : fp ∈ localTrialSet δ) (r : ℝ) :
    HasDerivAt (fun t => (localRadialProfiles hδ fp hfp t).1)
      (r * localQ δ hδ fp hfp (r ^ 2 / 2)) r ∧
    HasDerivAt (fun t => (localRadialProfiles hδ fp hfp t).2)
      (-radialK * r * localJ δ hδ fp hfp (r ^ 2 / 2) *
        localQ δ hδ fp hfp (r ^ 2 / 2) ^ (1 - (radialDim : ℝ))) r := by
  have hs : HasDerivAt (fun t : ℝ => t ^ 2 / 2) r r := by
    convert ((hasDerivAt_id r).pow 2).div_const 2 using 1 <;> first | rfl | norm_num
  have hd := localIntegralPrimitives_hasDerivAt hδ hfp (r ^ 2 / 2)
  constructor
  · convert hd.1.comp r hs using 1 <;> first | rfl | (dsimp [localDifferentialValues]; ring)
  · convert hd.2.comp r hs using 1 <;> first | rfl | (dsimp [localDifferentialValues]; ring)

-- @node: localRadialProfiles_zero
/-- If [δ is positive](hyp:hδ) and [the trial pair is admissible](hyp:hfp),
[both local radial profiles equal one at radius zero](goal). -/
lemma localRadialProfiles_zero {δ : ℝ} (hδ : 0 < δ)
    {fp : LocalTrialPair δ} (hfp : fp ∈ localTrialSet δ) :
    localRadialProfiles hδ fp hfp 0 = (1, 1) := by
  simp [localRadialProfiles, localIntegralPrimitives]

-- @node: localRadialProfiles_eq_extension
/-- If [δ is positive](hyp:hδ), [the trial pair is admissible](hyp:hfp) and
[is a fixed point of the local transform](hyp:hfix), and [r²/2 is at most
δ](hyp:hr), then [the radial profiles at r equal the two extended trial
profiles evaluated at r²/2](goal). -/
lemma localRadialProfiles_eq_extension {δ : ℝ} (hδ : 0 < δ)
    {fp : LocalTrialPair δ} (hfp : fp ∈ localTrialSet δ)
    (hfix : ∀ s, (fp.1 s, fp.2 s) = localTransformValues δ hδ fp hfp s)
    {r : ℝ} (hr : r ^ 2 / 2 ≤ δ) :
    localRadialProfiles hδ fp hfp r =
      (localTrialExtension δ hδ fp.1 (r ^ 2 / 2),
       localTrialExtension δ hδ fp.2 (r ^ 2 / 2)) := by
  exact (localFixedPoint_extension_eq hδ hfp hfix
    ⟨r ^ 2 / 2, by constructor <;> nlinarith [sq_nonneg r]⟩).symm

-- @node: localRadialProfiles_pos
/-- If [δ is positive](hyp:hδ), [the trial pair is admissible](hyp:hfp) and
[is a fixed point of the local transform](hyp:hfix), and [r²/2 is at most
δ](hyp:hr), then [both local radial profiles are strictly positive at r](goal). -/
lemma localRadialProfiles_pos {δ : ℝ} (hδ : 0 < δ)
    {fp : LocalTrialPair δ} (hfp : fp ∈ localTrialSet δ)
    (hfix : ∀ s, (fp.1 s, fp.2 s) = localTransformValues δ hδ fp hfp s)
    {r : ℝ} (hr : r ^ 2 / 2 ≤ δ) :
    0 < (localRadialProfiles hδ fp hfp r).1 ∧
      0 < (localRadialProfiles hδ fp hfp r).2 := by
  rw [localRadialProfiles_eq_extension hδ hfp hfix hr]
  have hb := localTrialExtension_mem hδ hfp (r ^ 2 / 2)
  constructor <;> dsimp <;> linarith [hb.1.1, hb.2.1]

-- @node: localRadialProfiles_derivative_signs
/-- For [positive δ](hyp:hδ), [an admissible trial pair](hyp:hfp), and [a
strictly positive radius](hyp:hr), [the first radial profile has strictly
positive derivative and the second has strictly negative derivative](goal). -/
lemma localRadialProfiles_derivative_signs {δ : ℝ} (hδ : 0 < δ)
    {fp : LocalTrialPair δ} (hfp : fp ∈ localTrialSet δ)
    {r : ℝ} (hr : 0 < r) :
    0 < deriv (fun t => (localRadialProfiles hδ fp hfp t).1) r ∧
      deriv (fun t => (localRadialProfiles hδ fp hfp t).2) r < 0 := by
  have hd := localRadialProfiles_hasDerivAt hδ hfp r
  rw [hd.1.deriv, hd.2.deriv]
  have hq := localQ_pos hδ hfp (r ^ 2 / 2)
  have hj := localJ_pos hδ hfp (r ^ 2 / 2)
  exact ⟨mul_pos hr hq, mul_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num [radialK]) hr) hj)
    (Real.rpow_pos_of_pos hq _)⟩

-- @node: localRadial_integral_rescale
/-- For any real function g and real radius r, [the integral from zero to r of
ρ⁸g(ρ²/2) equals r⁹ times the integral from zero to one of v⁸g(v²r²/2)](goal). -/
lemma localRadial_integral_rescale (g : ℝ → ℝ) (r : ℝ) :
    (∫ ρ : ℝ in 0..r, ρ ^ 8 * g (ρ ^ 2 / 2)) =
      r ^ 9 * ∫ v : ℝ in 0..1, v ^ 8 * g (v ^ 2 * (r ^ 2 / 2)) := by
  have hs := intervalIntegral.smul_integral_comp_mul_left
    (fun ρ : ℝ => ρ ^ 8 * g (ρ ^ 2 / 2)) (a := 0) (b := 1) r
  simp only [smul_eq_mul, mul_zero, mul_one] at hs
  rw [← hs]
  have hi : (∫ v : ℝ in 0..1, (r * v) ^ 8 * g ((r * v) ^ 2 / 2)) =
      r ^ 8 * ∫ v : ℝ in 0..1, v ^ 8 * g (v ^ 2 * (r ^ 2 / 2)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro v _
    dsimp only
    rw [mul_pow]
    have he : (r * v) ^ 2 / 2 = v ^ 2 * (r ^ 2 / 2) := by ring
    rw [he]
    ring
  rw [hi]
  ring

-- @node: localQ_pow_nine
/-- For [positive δ](hyp:hδ) and [an admissible trial pair](hyp:hfp), [the ninth
power of the normalized factor Q at s equals nine times the integral from zero
to one of $v^8 f(v^2s)p(v^2s)^{-\gamma}$](goal).

Here f and p are the extended trial profiles, and the power applies only to p. -/
lemma localQ_pow_nine {δ : ℝ} (hδ : 0 < δ)
    {fp : LocalTrialPair δ} (hfp : fp ∈ localTrialSet δ) (s : ℝ) :
    localQ δ hδ fp hfp s ^ 9 =
      9 * ∫ v : ℝ in 0..1, v ^ 8 * localTrialExtension δ hδ fp.1 (v ^ 2 * s) *
        localTrialExtension δ hδ fp.2 (v ^ 2 * s) ^ (-radialGamma) := by
  unfold localQ
  rw [← Real.rpow_natCast, ← Real.rpow_mul
    (mul_nonneg (by norm_num) (localAverage_pos hδ hfp (-radialGamma) s).le)]
  norm_num

-- @node: localRadial_normalized_integrals
/-- For [positive δ](hyp:hδ) and [an admissible trial pair](hyp:hfp), [the ninth
power of rQ(r²/2) equals nine times the integral of ρ⁸f(ρ²/2)p(ρ²/2)⁻ᵞ from
zero to r, and r⁹J(r²/2) equals the integral of
$\rho^8 p(\rho^2/2)^{1-\gamma}$ from zero to r](goal).

Here f and p are the extended trial profiles, Q and J are the normalized factors,
and the power in the second integrand applies only to p. -/
lemma localRadial_normalized_integrals {δ : ℝ} (hδ : 0 < δ)
    {fp : LocalTrialPair δ} (hfp : fp ∈ localTrialSet δ) (r : ℝ) :
    (r * localQ δ hδ fp hfp (r ^ 2 / 2)) ^ 9 =
      9 * ∫ ρ : ℝ in 0..r, ρ ^ 8 * localTrialExtension δ hδ fp.1 (ρ ^ 2 / 2) *
        localTrialExtension δ hδ fp.2 (ρ ^ 2 / 2) ^ (-radialGamma) ∧
    r ^ 9 * localJ δ hδ fp hfp (r ^ 2 / 2) =
      ∫ ρ : ℝ in 0..r, ρ ^ 8 *
        localTrialExtension δ hδ fp.2 (ρ ^ 2 / 2) ^ (1 - radialGamma) := by
  constructor
  · rw [mul_pow, localQ_pow_nine]
    simp_rw [mul_assoc]
    rw [localRadial_integral_rescale (fun s =>
      localTrialExtension δ hδ fp.1 s * localTrialExtension δ hδ fp.2 s ^ (-radialGamma))]
    ring
  · exact (localRadial_integral_rescale
      (fun s => localTrialExtension δ hδ fp.2 s ^ (1 - radialGamma)) r).symm

-- @node: localRadial_weight_continuous
/-- For [positive δ](hyp:hδ) and [an admissible trial pair](hyp:hfp), [the
function r⁸f(r²/2)p(r²/2)ᵅ is continuous on the real line for every real
exponent α](goal), where f and p are the extended trial profiles. -/
@[fun_prop] lemma localRadial_weight_continuous {δ : ℝ} (hδ : 0 < δ)
    {fp : LocalTrialPair δ} (hfp : fp ∈ localTrialSet δ) (α : ℝ) :
    Continuous (fun r : ℝ => r ^ 8 * localTrialExtension δ hδ fp.1 (r ^ 2 / 2) *
      localTrialExtension δ hδ fp.2 (r ^ 2 / 2) ^ α) := by
  have hp : Continuous (fun r : ℝ => localTrialExtension δ hδ fp.2 (r ^ 2 / 2) ^ α) :=
    (show Continuous (fun r : ℝ => localTrialExtension δ hδ fp.2 (r ^ 2 / 2)) by
      fun_prop).rpow_const (fun r => Or.inl (ne_of_gt (lt_of_lt_of_le
        (by norm_num : (0 : ℝ) < 1 / 2) (localTrialExtension_mem hδ hfp _).2.1)))
  fun_prop

-- @node: localRadialSlope_power_hasDerivAt
/-- For [positive δ](hyp:hδ) and [an admissible trial pair](hyp:hfp), [the ninth
power of the radial slope tQ(t²/2) has derivative
9r⁸f(r²/2)p(r²/2)⁻ᵞ at every real r](goal), where f and p are the extended
trial profiles and Q is the normalized slope factor. -/
lemma localRadialSlope_power_hasDerivAt {δ : ℝ} (hδ : 0 < δ)
    {fp : LocalTrialPair δ} (hfp : fp ∈ localTrialSet δ) (r : ℝ) :
    HasDerivAt (fun t => (t * localQ δ hδ fp hfp (t ^ 2 / 2)) ^ 9)
      (9 * (r ^ 8 * localTrialExtension δ hδ fp.1 (r ^ 2 / 2) *
        localTrialExtension δ hδ fp.2 (r ^ 2 / 2) ^ (-radialGamma))) r := by
  have hd := ((localRadial_weight_continuous hδ hfp (-radialGamma)).integral_hasStrictDerivAt
    0 r).hasDerivAt.const_mul 9
  have he : (fun t => (t * localQ δ hδ fp hfp (t ^ 2 / 2)) ^ 9) =
      (fun t => 9 * ∫ ρ : ℝ in 0..t, ρ ^ 8 * localTrialExtension δ hδ fp.1 (ρ ^ 2 / 2) *
        localTrialExtension δ hδ fp.2 (ρ ^ 2 / 2) ^ (-radialGamma)) :=
    funext (fun t => (localRadial_normalized_integrals hδ hfp t).1)
  rw [he]
  exact hd

-- @node: localRadialSlope_differentiableAt
/-- For [positive δ](hyp:hδ) and [an admissible trial pair](hyp:hfp), [at a
strictly positive radius r](hyp:hr) [the radial slope tQ(t²/2) is
differentiable](goal), where Q is the normalized slope factor. -/
lemma localRadialSlope_differentiableAt {δ : ℝ} (hδ : 0 < δ)
    {fp : LocalTrialPair δ} (hfp : fp ∈ localTrialSet δ) {r : ℝ} (hr : 0 < r) :
    DifferentiableAt ℝ (fun t => t * localQ δ hδ fp hfp (t ^ 2 / 2)) r := by
  have hp := mul_pos hr (localQ_pos hδ hfp (r ^ 2 / 2))
  have hd := (localRadialSlope_power_hasDerivAt hδ hfp r).differentiableAt.rpow_const
    (p := (1 / 9 : ℝ)) (Or.inl (pow_ne_zero 9 hp.ne'))
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds hr] with t ht
  simpa only [Nat.cast_ofNat, one_div] using (Real.pow_rpow_inv_natCast
    (mul_pos ht (localQ_pos hδ hfp (t ^ 2 / 2))).le (by norm_num : (9 : ℕ) ≠ 0)).symm

-- @node: localRadialProfiles_first_equation
/-- For [positive δ](hyp:hδ), [an admissible trial pair](hyp:hfp), and [r
strictly positive](hyp:hr), [the eighth power of the first radial profile's
derivative times its second derivative equals r⁸f(r²/2)p(r²/2)⁻ᵞ, and that
second derivative is strictly positive](goal), where f and p are the extended
trial profiles. -/
lemma localRadialProfiles_first_equation {δ : ℝ} (hδ : 0 < δ)
    {fp : LocalTrialPair δ} (hfp : fp ∈ localTrialSet δ) {r : ℝ} (hr : 0 < r) :
    deriv (fun t => (localRadialProfiles hδ fp hfp t).1) r ^ 8 *
      deriv (deriv (fun t => (localRadialProfiles hδ fp hfp t).1)) r =
        r ^ 8 * localTrialExtension δ hδ fp.1 (r ^ 2 / 2) *
          localTrialExtension δ hδ fp.2 (r ^ 2 / 2) ^ (-radialGamma) ∧
    0 < deriv (deriv (fun t => (localRadialProfiles hδ fp hfp t).1)) r := by
  have he : deriv (fun t => (localRadialProfiles hδ fp hfp t).1) =
      fun t => t * localQ δ hδ fp hfp (t ^ 2 / 2) :=
    funext (fun t => (localRadialProfiles_hasDerivAt hδ hfp t).1.deriv)
  rw [he]
  have hd := (localRadialSlope_differentiableAt hδ hfp hr).hasDerivAt.pow 9
  have hid := hd.unique (localRadialSlope_power_hasDerivAt hδ hfp r)
  have heq : (r * localQ δ hδ fp hfp (r ^ 2 / 2)) ^ 8 *
      deriv (fun t => t * localQ δ hδ fp hfp (t ^ 2 / 2)) r =
        r ^ 8 * localTrialExtension δ hδ fp.1 (r ^ 2 / 2) *
          localTrialExtension δ hδ fp.2 (r ^ 2 / 2) ^ (-radialGamma) := by
    norm_num only [Nat.cast_ofNat, Nat.reduceSub] at hid
    nlinarith [hid]
  refine ⟨heq, ?_⟩
  have hpos : 0 < r ^ 8 * localTrialExtension δ hδ fp.1 (r ^ 2 / 2) *
      localTrialExtension δ hδ fp.2 (r ^ 2 / 2) ^ (-radialGamma) := by
    apply mul_pos
    · apply mul_pos (pow_pos hr _)
      linarith [(localTrialExtension_mem hδ hfp (r ^ 2 / 2)).1.1]
    · apply Real.rpow_pos_of_pos
      linarith [(localTrialExtension_mem hδ hfp (r ^ 2 / 2)).2.1]
  exact (mul_pos_iff.mp (heq ▸ hpos)).resolve_right
    (fun h => (not_lt_of_ge (pow_nonneg (mul_pos hr (localQ_pos hδ hfp _)).le 8)) h.1) |>.2

-- @node: localRadialFlux_eq_integral
/-- For [positive δ](hyp:hδ) and [an admissible trial pair](hyp:hfp), [the
eighth power of the first radial profile's derivative times the second
profile's derivative at r equals −K times the integral of
$\rho^8 p(\rho^2/2)^{1-\gamma}$ from zero to r](goal).

Here p is the extended second trial profile, K is the radial constant, and
the power in the integrand applies only to p. -/
lemma localRadialFlux_eq_integral {δ : ℝ} (hδ : 0 < δ)
    {fp : LocalTrialPair δ} (hfp : fp ∈ localTrialSet δ) (r : ℝ) :
    deriv (fun t => (localRadialProfiles hδ fp hfp t).1) r ^ 8 *
      deriv (fun t => (localRadialProfiles hδ fp hfp t).2) r =
      -radialK * ∫ ρ : ℝ in 0..r, ρ ^ 8 *
        localTrialExtension δ hδ fp.2 (ρ ^ 2 / 2) ^ (1 - radialGamma) := by
  have hd := localRadialProfiles_hasDerivAt hδ hfp r
  rw [hd.1.deriv, hd.2.deriv]
  have hq := (localQ_pos hδ hfp (r ^ 2 / 2)).ne'
  have hcancel : localQ δ hδ fp hfp (r ^ 2 / 2) ^ 8 *
      localQ δ hδ fp hfp (r ^ 2 / 2) ^ (1 - (radialDim : ℝ)) = 1 := by
    norm_num only [radialDim, Nat.cast_ofNat, show (1 : ℝ) - 9 = -8 by norm_num]
    rw [Real.rpow_neg (localQ_pos hδ hfp _).le, Real.rpow_ofNat]
    exact mul_inv_cancel₀ (pow_ne_zero _ hq)
  have halg : (r * localQ δ hδ fp hfp (r ^ 2 / 2)) ^ 8 *
      (-radialK * r * localJ δ hδ fp hfp (r ^ 2 / 2) *
        localQ δ hδ fp hfp (r ^ 2 / 2) ^ (1 - (radialDim : ℝ))) =
      -radialK * (r ^ 9 * localJ δ hδ fp hfp (r ^ 2 / 2)) := by
    calc
      _ = -radialK * (r ^ 9 * localJ δ hδ fp hfp (r ^ 2 / 2)) *
          (localQ δ hδ fp hfp (r ^ 2 / 2) ^ 8 *
            localQ δ hδ fp hfp (r ^ 2 / 2) ^ (1 - (radialDim : ℝ))) := by ring
      _ = _ := by rw [hcancel, mul_one]
  rw [halg, (localRadial_normalized_integrals hδ hfp r).2]

-- @node: localRadialFlux_hasDerivAt
/-- For [positive δ](hyp:hδ) and [an admissible trial pair](hyp:hfp), [the flux
formed by multiplying the eighth power of the first radial profile's derivative
by the second profile's derivative has derivative $-Kr^8 p(r^2/2)^{1-\gamma}$
at every real r](goal).

Here p is the extended second trial profile, K is the radial constant, and
the power in the derivative formula applies only to p. -/
lemma localRadialFlux_hasDerivAt {δ : ℝ} (hδ : 0 < δ)
    {fp : LocalTrialPair δ} (hfp : fp ∈ localTrialSet δ) (r : ℝ) :
    HasDerivAt (fun t => deriv (fun u => (localRadialProfiles hδ fp hfp u).1) t ^ 8 *
      deriv (fun u => (localRadialProfiles hδ fp hfp u).2) t)
      (-radialK * r ^ 8 * localTrialExtension δ hδ fp.2 (r ^ 2 / 2) ^ (1 - radialGamma)) r := by
  have hc : Continuous (fun ρ : ℝ => ρ ^ 8 *
      localTrialExtension δ hδ fp.2 (ρ ^ 2 / 2) ^ (1 - radialGamma)) := by
    have hp : Continuous (fun ρ : ℝ =>
        localTrialExtension δ hδ fp.2 (ρ ^ 2 / 2) ^ (1 - radialGamma)) :=
      (show Continuous (fun ρ : ℝ => localTrialExtension δ hδ fp.2 (ρ ^ 2 / 2)) by
        fun_prop).rpow_const (fun ρ => Or.inl (ne_of_gt (lt_of_lt_of_le
          (by norm_num : (0 : ℝ) < 1 / 2) (localTrialExtension_mem hδ hfp _).2.1)))
    fun_prop
  have hd := (hc.integral_hasStrictDerivAt 0 r).hasDerivAt.const_mul (-radialK)
  have he := funext (localRadialFlux_eq_integral hδ hfp)
  rw [he]
  convert hd using 1 <;> first | rfl | ring

-- @node: localRadialProfiles_equations
/-- If [δ is positive](hyp:hδ), [the trial pair is admissible](hyp:hfp) and
[is a fixed point of the local transform](hyp:hfix), and [r is strictly
positive](hyp:hr) with [r²/2 at most δ](hyp:hrδ), then [the radial profiles
F and P satisfy (F′)⁸F″ = r⁸FP⁻ᵞ and the derivative of (F′)⁸P′ equals
$-Kr^8P^{1-\gamma}$; moreover F, P, F′, and F″ are strictly positive
and P′ is strictly negative at r](goal).

Here K is the radial constant, and the power on the second right-hand side
applies only to P. -/
lemma localRadialProfiles_equations {δ : ℝ} (hδ : 0 < δ)
    {fp : LocalTrialPair δ} (hfp : fp ∈ localTrialSet δ)
    (hfix : ∀ s, (fp.1 s, fp.2 s) = localTransformValues δ hδ fp hfp s)
    {r : ℝ} (hr : 0 < r) (hrδ : r ^ 2 / 2 ≤ δ) :
    deriv (fun t => (localRadialProfiles hδ fp hfp t).1) r ^ 8 *
      deriv (deriv (fun t => (localRadialProfiles hδ fp hfp t).1)) r =
        r ^ 8 * (localRadialProfiles hδ fp hfp r).1 *
          (localRadialProfiles hδ fp hfp r).2 ^ (-radialGamma) ∧
    deriv (fun t => deriv (fun u => (localRadialProfiles hδ fp hfp u).1) t ^ 8 *
      deriv (fun u => (localRadialProfiles hδ fp hfp u).2) t) r =
        -radialK * r ^ 8 * (localRadialProfiles hδ fp hfp r).2 ^ (1 - radialGamma) ∧
    0 < (localRadialProfiles hδ fp hfp r).1 ∧
    0 < (localRadialProfiles hδ fp hfp r).2 ∧
    0 < deriv (fun t => (localRadialProfiles hδ fp hfp t).1) r ∧
    0 < deriv (deriv (fun t => (localRadialProfiles hδ fp hfp t).1)) r ∧
    deriv (fun t => (localRadialProfiles hδ fp hfp t).2) r < 0 := by
  have he := localRadialProfiles_eq_extension hδ hfp hfix hrδ
  have hd := localRadialProfiles_first_equation hδ hfp hr
  have hp := localRadialProfiles_pos hδ hfp hfix hrδ
  have hs := localRadialProfiles_derivative_signs hδ hfp hr
  refine ⟨?_, ?_, hp.1, hp.2, hs.1, hd.2, hs.2⟩
  · simpa only [he] using hd.1
  · simpa only [he] using (localRadialFlux_hasDerivAt hδ hfp r).deriv

-- @node: localRadialProfiles_contDiff_one
/-- For [positive δ](hyp:hδ) and [an admissible trial pair](hyp:hfp), [both
local radial profiles are continuously differentiable on the real line](goal). -/
lemma localRadialProfiles_contDiff_one {δ : ℝ} (hδ : 0 < δ)
    {fp : LocalTrialPair δ} (hfp : fp ∈ localTrialSet δ) :
    ContDiff ℝ 1 (fun t => (localRadialProfiles hδ fp hfp t).1) ∧
    ContDiff ℝ 1 (fun t => (localRadialProfiles hδ fp hfp t).2) := by
  have hq := localQ_continuous hδ hfp
  have hj := localJ_continuous hδ hfp
  have hpower : Continuous (fun r : ℝ =>
      localQ δ hδ fp hfp (r ^ 2 / 2) ^ (1 - (radialDim : ℝ))) :=
    (show Continuous (fun r : ℝ => localQ δ hδ fp hfp (r ^ 2 / 2)) by fun_prop).rpow_const
      (fun r => Or.inl (localQ_pos hδ hfp _).ne')
  constructor
  · apply contDiff_one_iff_deriv.mpr
    refine ⟨fun r => (localRadialProfiles_hasDerivAt hδ hfp r).1.differentiableAt, ?_⟩
    have he : deriv (fun t => (localRadialProfiles hδ fp hfp t).1) =
        fun t => t * localQ δ hδ fp hfp (t ^ 2 / 2) :=
      funext (fun t => (localRadialProfiles_hasDerivAt hδ hfp t).1.deriv)
    rw [he]
    fun_prop
  · apply contDiff_one_iff_deriv.mpr
    refine ⟨fun r => (localRadialProfiles_hasDerivAt hδ hfp r).2.differentiableAt, ?_⟩
    have he : deriv (fun t => (localRadialProfiles hδ fp hfp t).2) =
        fun t => -radialK * t * localJ δ hδ fp hfp (t ^ 2 / 2) *
          localQ δ hδ fp hfp (t ^ 2 / 2) ^ (1 - (radialDim : ℝ)) :=
      funext (fun t => (localRadialProfiles_hasDerivAt hδ hfp t).2.deriv)
    rw [he]
    fun_prop

-- @node: localRadialSlope_contDiffOn_one
/-- For [positive δ](hyp:hδ) and [an admissible trial pair](hyp:hfp), [the
radial slope rQ(r²/2) is continuously differentiable on the positive real
axis](goal), where Q is the normalized slope factor. -/
lemma localRadialSlope_contDiffOn_one {δ : ℝ} (hδ : 0 < δ)
    {fp : LocalTrialPair δ} (hfp : fp ∈ localTrialSet δ) :
    ContDiffOn ℝ 1 (fun t => t * localQ δ hδ fp hfp (t ^ 2 / 2)) (Ioi 0) := by
  have hq := localQ_continuous hδ hfp
  have hc : Continuous (fun t : ℝ => t * localQ δ hδ fp hfp (t ^ 2 / 2)) := by fun_prop
  have he : EqOn (deriv (fun t => t * localQ δ hδ fp hfp (t ^ 2 / 2)))
      (fun r => (r ^ 8 * localTrialExtension δ hδ fp.1 (r ^ 2 / 2) *
        localTrialExtension δ hδ fp.2 (r ^ 2 / 2) ^ (-radialGamma)) /
          (r * localQ δ hδ fp hfp (r ^ 2 / 2)) ^ 8) (Ioi 0) := by
    intro r hr
    apply (eq_div_iff (pow_ne_zero 8 (mul_pos hr (localQ_pos hδ hfp _)).ne')).mpr
    have h := (localRadialProfiles_first_equation hδ hfp hr).1
    have heF : deriv (fun t => (localRadialProfiles hδ fp hfp t).1) =
        fun t => t * localQ δ hδ fp hfp (t ^ 2 / 2) :=
      funext (fun t => (localRadialProfiles_hasDerivAt hδ hfp t).1.deriv)
    rw [heF] at h
    simpa only [mul_comm] using h
  rw [show (1 : ℕ∞ω) = 0 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨fun r hr => (localRadialSlope_differentiableAt hδ hfp hr).differentiableWithinAt,
    by simp, ?_⟩
  rw [contDiffOn_zero]
  apply ContinuousOn.congr _ he
  exact (localRadial_weight_continuous hδ hfp (-radialGamma)).continuousOn.div
    (hc.pow 8).continuousOn (fun r hr => pow_ne_zero 8 (mul_pos hr (localQ_pos hδ hfp _)).ne')

-- @node: localRadialFlux_contDiff_one
/-- For [positive δ](hyp:hδ) and [an admissible trial pair](hyp:hfp), [the flux
formed by multiplying the eighth power of the first radial profile's derivative
by the second profile's derivative is continuously differentiable on the real
line](goal). -/
lemma localRadialFlux_contDiff_one {δ : ℝ} (hδ : 0 < δ)
    {fp : LocalTrialPair δ} (hfp : fp ∈ localTrialSet δ) :
    ContDiff ℝ 1 (fun t => deriv (fun u => (localRadialProfiles hδ fp hfp u).1) t ^ 8 *
      deriv (fun u => (localRadialProfiles hδ fp hfp u).2) t) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun r => (localRadialFlux_hasDerivAt hδ hfp r).differentiableAt, ?_⟩
  have he := funext (fun r => (localRadialFlux_hasDerivAt hδ hfp r).deriv)
  rw [he]
  have hp : Continuous (fun r : ℝ =>
      localTrialExtension δ hδ fp.2 (r ^ 2 / 2) ^ (1 - radialGamma)) :=
    (show Continuous (fun r : ℝ => localTrialExtension δ hδ fp.2 (r ^ 2 / 2)) by
      fun_prop).rpow_const (fun r => Or.inl (ne_of_gt (lt_of_lt_of_le
        (by norm_num : (0 : ℝ) < 1 / 2) (localTrialExtension_mem hδ hfp _).2.1)))
  fun_prop

-- @node: localRadialProfiles_contDiffOn_two
/-- For [positive δ](hyp:hδ) and [an admissible trial pair](hyp:hfp), [both
local radial profiles are twice continuously differentiable on the positive
real axis](goal). -/
lemma localRadialProfiles_contDiffOn_two {δ : ℝ} (hδ : 0 < δ)
    {fp : LocalTrialPair δ} (hfp : fp ∈ localTrialSet δ) :
    ContDiffOn ℝ 2 (fun t => (localRadialProfiles hδ fp hfp t).1) (Ioi 0) ∧
    ContDiffOn ℝ 2 (fun t => (localRadialProfiles hδ fp hfp t).2) (Ioi 0) := by
  have heF : deriv (fun t => (localRadialProfiles hδ fp hfp t).1) =
      fun t => t * localQ δ hδ fp hfp (t ^ 2 / 2) :=
    funext (fun t => (localRadialProfiles_hasDerivAt hδ hfp t).1.deriv)
  have hF' : ContDiffOn ℝ 1 (deriv (fun t => (localRadialProfiles hδ fp hfp t).1)) (Ioi 0) := by
    rw [heF]
    exact localRadialSlope_contDiffOn_one hδ hfp
  have hP' : ContDiffOn ℝ 1 (deriv (fun t => (localRadialProfiles hδ fp hfp t).2)) (Ioi 0) := by
    have hquot := (localRadialFlux_contDiff_one hδ hfp).contDiffOn.div (hF'.pow 8)
      (fun r hr => pow_ne_zero 8 (localRadialProfiles_derivative_signs hδ hfp hr).1.ne')
    apply hquot.congr
    intro r hr
    exact (mul_div_cancel_left₀ _ (pow_ne_zero 8
      (localRadialProfiles_derivative_signs hδ hfp hr).1.ne')).symm
  constructor
  · rw [show (2 : ℕ∞ω) = 1 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
    exact ⟨(localRadialProfiles_contDiff_one hδ hfp).1.differentiable (by norm_num)
        |>.differentiableOn,
      by simp, hF'⟩
  · rw [show (2 : ℕ∞ω) = 1 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
    exact ⟨(localRadialProfiles_contDiff_one hδ hfp).2.differentiable (by norm_num)
        |>.differentiableOn,
      by simp, hP'⟩

-- @node: localRadialProfiles_integrated
/-- If [δ is positive](hyp:hδ), [the trial pair is admissible](hyp:hfp) and
[is a fixed point of the local transform](hyp:hfix), and [r is strictly
positive](hyp:hr) with [r²/2 at most δ](hyp:hrδ), then [the radial profiles
F and P satisfy F′(r)⁹ = 9 times the integral of ρ⁸F(ρ)P(ρ)⁻ᵞ from zero
to r, and F′(r)⁸P′(r) = −K times the integral of $\rho^8P(\rho)^{1-\gamma}$
over the same interval](goal).

Here K is the radial constant, and the power in the second integrand applies
only to P. -/
lemma localRadialProfiles_integrated {δ : ℝ} (hδ : 0 < δ)
    {fp : LocalTrialPair δ} (hfp : fp ∈ localTrialSet δ)
    (hfix : ∀ s, (fp.1 s, fp.2 s) = localTransformValues δ hδ fp hfp s)
    {r : ℝ} (hr : 0 < r) (hrδ : r ^ 2 / 2 ≤ δ) :
    deriv (fun t => (localRadialProfiles hδ fp hfp t).1) r ^ 9 =
      9 * ∫ ρ : ℝ in 0..r, ρ ^ 8 * (localRadialProfiles hδ fp hfp ρ).1 *
        (localRadialProfiles hδ fp hfp ρ).2 ^ (-radialGamma) ∧
    deriv (fun t => (localRadialProfiles hδ fp hfp t).1) r ^ 8 *
      deriv (fun t => (localRadialProfiles hδ fp hfp t).2) r =
      -radialK * ∫ ρ : ℝ in 0..r, ρ ^ 8 *
        (localRadialProfiles hδ fp hfp ρ).2 ^ (1 - radialGamma) := by
  have he (ρ : ℝ) (hρ : ρ ∈ uIcc 0 r) :
      localRadialProfiles hδ fp hfp ρ =
        (localTrialExtension δ hδ fp.1 (ρ ^ 2 / 2),
         localTrialExtension δ hδ fp.2 (ρ ^ 2 / 2)) := by
    rw [uIcc_of_le hr.le] at hρ
    apply localRadialProfiles_eq_extension hδ hfp hfix
    nlinarith [mul_nonneg (sub_nonneg.mpr hρ.2) (add_nonneg hr.le hρ.1)]
  have hi := localRadial_normalized_integrals hδ hfp r
  have hd := localRadialProfiles_hasDerivAt hδ hfp r
  rw [hd.1.deriv, hd.2.deriv]
  constructor
  · rw [hi.1]
    congr 1
    apply intervalIntegral.integral_congr
    intro ρ hρ
    dsimp only
    rw [he ρ hρ]
  · rw [← hd.1.deriv, ← hd.2.deriv, localRadialFlux_eq_integral hδ hfp r]
    congr 1
    apply intervalIntegral.integral_congr
    intro ρ hρ
    dsimp only
    rw [he ρ hρ]

-- @node: localRadialProfiles_system
/-- For [positive δ](hyp:hδ), [an admissible trial pair](hyp:hfp) that [is a
fixed point of the local transform](hyp:hfix) yields [radial profiles solving
the radial system with dimension nine and the prescribed constants K and γ
on the open interval from zero to the smaller of δ and one; throughout this
interval both profiles, the first profile's first derivative, and its second
derivative are strictly positive, while the second profile's derivative is
strictly negative](goal). -/
lemma localRadialProfiles_system {δ : ℝ} (hδ : 0 < δ)
    {fp : LocalTrialPair δ} (hfp : fp ∈ localTrialSet δ)
    (hfix : ∀ s, (fp.1 s, fp.2 s) = localTransformValues δ hδ fp hfp s) :
    RadialSystem radialDim radialK radialGamma
      (fun r => (localRadialProfiles hδ fp hfp r).1)
      (fun r => (localRadialProfiles hδ fp hfp r).2) (Ioo 0 (min δ 1)) ∧
    ∀ r ∈ Ioo 0 (min δ 1),
      0 < (localRadialProfiles hδ fp hfp r).1 ∧
      0 < (localRadialProfiles hδ fp hfp r).2 ∧
      0 < deriv (fun t => (localRadialProfiles hδ fp hfp t).1) r ∧
      0 < deriv (deriv (fun t => (localRadialProfiles hδ fp hfp t).1)) r ∧
      deriv (fun t => (localRadialProfiles hδ fp hfp t).2) r < 0 := by
  have hcoord (r : ℝ) (hr : r ∈ Ioo 0 (min δ 1)) : r ^ 2 / 2 ≤ δ := by
    have hrδ := hr.2.trans_le (min_le_left δ 1)
    have hr1 := hr.2.trans_le (min_le_right δ 1)
    nlinarith [mul_nonneg hr.1.le (sub_nonneg.mpr hr1.le)]
  constructor
  · intro r hr
    have hc := localRadialProfiles_contDiffOn_two hδ hfp
    have hd := localRadialProfiles_equations hδ hfp hfix hr.1 (hcoord r hr)
    exact ⟨hc.1.contDiffAt (isOpen_Ioi.mem_nhds hr.1),
      hc.2.contDiffAt (isOpen_Ioi.mem_nhds hr.1), hd.1, hd.2.1⟩
  · intro r hr
    exact (localRadialProfiles_equations hδ hfp hfix hr.1 (hcoord r hr)).2.2

end OaiSmoothNonquadraticAffine

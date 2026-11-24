module

public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Papers.HawkesD75660b.Helpers.GeneratingFunction

/-! Euler harmonic integration and the continuous duration-integrand endpoint. -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology

namespace Papers.HawkesD75660b

/-- For [a nonnegative branching parameter ρ](hyp:ρ) and [a real integration coordinate u](hyp:u),
[the duration integrand](goal) is [1/(1 − ρ) when u equals ρ](step:1), and otherwise
[the ratio of exp(−u) − exp(−ρ) to ρ exp(−ρ) − u exp(−u)](step:2).
@realizes u(real integration coordinate restricted to [0,rho] by the integral bounds) -/
def durationIntegrand (ρ : ℝ≥0) (u : ℝ) : ℝ :=
  if u = (ρ : ℝ) then 1 / (1 - (ρ : ℝ)) else
    (Real.exp (-u) - Real.exp (-(ρ : ℝ))) /
      ((ρ : ℝ) * Real.exp (-(ρ : ℝ)) - u * Real.exp (-u))

-- @node: ass:pin-1
/-- For [a nonnegative branching parameter ρ](hyp:ρ), [the continuous endpoint convention](goal)
requires [the duration integrand to equal its exponential quotient for 0 ≤ u < ρ](step:1),
[to be continuous on the closed interval from zero to ρ](step:2), and
[to equal 1/(1 − ρ) at ρ](step:3). -/
def continuousEndpointConvention (ρ : ℝ≥0) : Prop :=
  (∀ u ∈ Set.Ico (0 : ℝ) (ρ : ℝ),
    durationIntegrand ρ u =
      (Real.exp (-u) - Real.exp (-(ρ : ℝ))) /
        ((ρ : ℝ) * Real.exp (-(ρ : ℝ)) - u * Real.exp (-u))) ∧
  ContinuousOn (durationIntegrand ρ) (Set.Icc 0 (ρ : ℝ)) ∧
  durationIntegrand ρ (ρ : ℝ) = 1 / (1 - (ρ : ℝ))

/-- For [a nonnegative integer j](hyp:j) and [a real coordinate x](hyp:x),
[the harmonic integrand is the sum of the powers of x from exponent zero through j − 1, with an empty sum when j is zero](goal). -/
def harmonicIntegrand (j : ℕ) (x : ℝ) : ℝ := ∑ i ∈ Finset.range j, x ^ i

-- @node: harmonic_euler_integral
/-- [The j-th harmonic number equals the integral, from zero to one, of the sum of the first j nonnegative powers of the integration coordinate](goal). -/
lemma harmonic_euler_integral (j : ℕ) :
    harmonicNumber j = ∫ x in (0 : ℝ)..1, harmonicIntegrand j x := by
  unfold harmonicIntegrand
  rw [intervalIntegral.integral_finsetSum]
  · simp [harmonicNumber, harmonic, integral_pow, div_eq_mul_inv]
  · intro i hi
    exact (continuous_id.pow i).intervalIntegrable 0 1

-- @node: harmonicIntegrand_nonneg
/-- If [x is nonnegative](hyp:hx), [the harmonic integrand of any order j at x is nonnegative](goal). -/
lemma harmonicIntegrand_nonneg (j : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ harmonicIntegrand j x := by
  unfold harmonicIntegrand
  exact Finset.sum_nonneg (fun i _ => pow_nonneg hx i)

-- @node: harmonicIntegrand_mul_one_sub
/-- [The harmonic integrand of order j at any real x, multiplied by 1 − x, equals 1 − x to the power j](goal). -/
lemma harmonicIntegrand_mul_one_sub (j : ℕ) (x : ℝ) :
    harmonicIntegrand j x * (1 - x) = 1 - x ^ j := by
  exact geom_sum_mul_neg x j

-- @node: harmonicIntegrand_continuous
/-- [The harmonic integrand of every nonnegative integer order is continuous on the real line](goal). -/
@[fun_prop] lemma harmonicIntegrand_continuous (j : ℕ) :
    Continuous (harmonicIntegrand j) := by
  unfold harmonicIntegrand
  fun_prop

-- @node: harmonicIntegrand_le_nat
/-- If [x lies in the closed unit interval](hyp:hx), [the harmonic integrand of order j at x is at most j](goal). -/
lemma harmonicIntegrand_le_nat (j : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    harmonicIntegrand j x ≤ j := by
  unfold harmonicIntegrand
  calc
    _ ≤ ∑ _i ∈ Finset.range j, (1 : ℝ) := by
      exact Finset.sum_le_sum (fun i _ => pow_le_one₀ hx.1 hx.2)
    _ = _ := by simp

-- @node: borelHarmonicKernel
/-- For [a nonnegative branching parameter ρ](hyp:ρ) and [a real coordinate x](hyp:x),
[the Borel harmonic kernel is the infinite sum, over nonnegative integers j, of the Borel mass at j times j times the harmonic integrand of order j at x](goal). -/
def borelHarmonicKernel (ρ : ℝ≥0) (x : ℝ) : ℝ :=
  ∑' j : ℕ, borelMass ρ j * (j : ℝ) * harmonicIntegrand j x

-- @node: borelHarmonicKernel_term_bound
/-- For [a nonnegative branching parameter ρ](hyp:ρ), if [x lies in the closed unit interval](hyp:hx), [the absolute value of the j-th term of the Borel harmonic kernel is bounded by the Borel mass at j times j squared](goal). -/
lemma borelHarmonicKernel_term_bound (ρ : ℝ≥0) (j : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ‖borelMass ρ j * (j : ℝ) * harmonicIntegrand j x‖ ≤
      borelMass ρ j * (j : ℝ)^2 := by
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (mul_nonneg (borelMass_nonneg ρ j) (Nat.cast_nonneg j))
      (harmonicIntegrand_nonneg j hx.1))]
  calc
    _ ≤ borelMass ρ j * (j : ℝ) * j :=
      mul_le_mul_of_nonneg_left (harmonicIntegrand_le_nat j hx)
        (mul_nonneg (borelMass_nonneg ρ j) (Nat.cast_nonneg j))
    _ = _ := by ring

-- @node: borelHarmonicKernel_summable
/-- If [the nonnegative branching parameter ρ is below one](hyp:ρ,hρ) and [x lies in the closed unit interval](hyp:hx),
[the series defining the Borel harmonic kernel at x is summable](goal). -/
lemma borelHarmonicKernel_summable (ρ : ℝ≥0) (hρ : subcritical ρ) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    Summable (fun j : ℕ => borelMass ρ j * (j : ℝ) * harmonicIntegrand j x) := by
  exact (borel_second_moment_summable ρ hρ).of_norm_bounded
    (fun j => borelHarmonicKernel_term_bound ρ j hx)

-- @node: borelHarmonicKernel_continuousOn
/-- If [the nonnegative branching parameter ρ is below one](hyp:ρ,hρ), [the Borel harmonic kernel is continuous on the closed unit interval](goal). -/
@[fun_prop] lemma borelHarmonicKernel_continuousOn (ρ : ℝ≥0) (hρ : subcritical ρ) :
    ContinuousOn (borelHarmonicKernel ρ) (Set.Icc (0 : ℝ) 1) := by
  unfold borelHarmonicKernel
  apply continuousOn_tsum (u := fun j => borelMass ρ j * (j : ℝ)^2)
  · intro j
    fun_prop
  · exact borel_second_moment_summable ρ hρ
  · intro j x hx
    exact borelHarmonicKernel_term_bound ρ j hx

-- @node: harmonic_borel_euler_integral
/-- If [the nonnegative branching parameter ρ is below one](hyp:ρ,hρ), [the Borel expectation of j times its harmonic number equals the integral of the Borel harmonic kernel from zero to one](goal). -/
lemma harmonic_borel_euler_integral (ρ : ℝ≥0) (hρ : subcritical ρ) :
    (∫ j : ℕ, (j : ℝ) * harmonicNumber j ∂borelMeasure ρ) =
      ∫ x in (0 : ℝ)..1, borelHarmonicKernel ρ x := by
  let F : ℕ → ℝ → ℝ := fun j x =>
    borelMass ρ j * (j : ℝ) * harmonicIntegrand j x
  have hi (j : ℕ) : IntervalIntegrable (F j) volume 0 1 := by
    apply Continuous.intervalIntegrable
    dsimp [F]
    fun_prop
  have hnorm (j : ℕ) :
      (∫ x in Set.Ioc (0 : ℝ) 1, ‖F j x‖) =
        borelMass ρ j * (j : ℝ) * harmonicNumber j := by
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    calc
      _ = ∫ x in (0 : ℝ)..1, F j x := by
        apply intervalIntegral.integral_congr
        intro x hx
        change ‖F j x‖ = F j x
        rw [Real.norm_eq_abs, abs_of_nonneg]
        · dsimp [F]
          exact mul_nonneg (mul_nonneg (borelMass_nonneg ρ j) (Nat.cast_nonneg j))
            (harmonicIntegrand_nonneg j (by simpa using hx.1))
      _ = _ := by
        dsimp [F]
        rw [intervalIntegral.integral_const_mul, ← harmonic_euler_integral]
  have hswap := integral_tsum_of_summable_integral_norm
    (μ := volume.restrict (Set.Ioc (0 : ℝ) 1)) (fun j => (hi j).1)
    (by simpa only [hnorm] using borel_harmonic_moment_summable ρ hρ)
  unfold borelMeasure
  rw [integral_sum_dirac (fun j => ENNReal.ofReal_ne_top)]
  simp only [ENNReal.toReal_ofReal (borelMass_nonneg ρ _), smul_eq_mul, ← mul_assoc]
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  change _ = ∫ x in Set.Ioc (0 : ℝ) 1, ∑' j, F j x
  rw [← hswap]
  apply tsum_congr
  intro j
  rw [← hnorm]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg]
  dsimp [F]
  exact mul_nonneg (mul_nonneg (borelMass_nonneg ρ j) (Nat.cast_nonneg j))
    (harmonicIntegrand_nonneg j hx.1.le)

-- @node: borel_centered_euler_integral
/-- If [the nonnegative branching parameter ρ is below one](hyp:ρ,hρ), [multiplying the Borel expectation of j times its harmonic number by 1 − ρ and subtracting one gives the integral, from zero to one, of (1 − ρ) times the Borel harmonic kernel minus one](goal). -/
lemma borel_centered_euler_integral (ρ : ℝ≥0) (hρ : subcritical ρ) :
    (1 - (ρ : ℝ)) * (∫ j : ℕ, (j : ℝ) * harmonicNumber j ∂borelMeasure ρ) - 1 =
      ∫ x in (0 : ℝ)..1, (1 - (ρ : ℝ)) * borelHarmonicKernel ρ x - 1 := by
  have hi : IntervalIntegrable (borelHarmonicKernel ρ) volume 0 1 :=
    ContinuousOn.intervalIntegrable (by
      simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
        borelHarmonicKernel_continuousOn ρ hρ)
  rw [intervalIntegral.integral_sub (hi.const_mul _) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, ← harmonic_borel_euler_integral ρ hρ]
  norm_num

-- @node: borelHarmonicKernel_geometric_identity
/-- If [the nonnegative branching parameter ρ is below one](hyp:ρ,hρ) and [x lies in the closed unit interval](hyp:hx),
[the Borel harmonic kernel at x times 1 − x equals 1/(1 − ρ) minus the sum of the Borel mass at j times j times x to the power j](goal). -/
lemma borelHarmonicKernel_geometric_identity (ρ : ℝ≥0) (hρ : subcritical ρ)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    borelHarmonicKernel ρ x * (1 - x) =
      1 / (1 - (ρ : ℝ)) - ∑' j : ℕ, borelMass ρ j * (j : ℝ) * x ^ j := by
  have hs : Summable (fun j : ℕ => borelMass ρ j * (j : ℝ)) := by
    simpa only [pow_one] using borelMass_polynomial_summable ρ hρ 1
  have hxsum : Summable (fun j : ℕ => borelMass ρ j * (j : ℝ) * x ^ j) := by
    apply Summable.of_nonneg_of_le
      (fun j => mul_nonneg (mul_nonneg (borelMass_nonneg ρ j) (Nat.cast_nonneg j))
        (pow_nonneg hx.1 j)) (fun j => ?_) hs
    exact mul_le_of_le_one_right
      (mul_nonneg (borelMass_nonneg ρ j) (Nat.cast_nonneg j)) (pow_le_one₀ hx.1 hx.2)
  have hm : (∑' j : ℕ, borelMass ρ j * (j : ℝ)) = 1 / (1 - (ρ : ℝ)) := by
    have he := borel_first_moment ρ hρ
    unfold borelMeasure at he
    rw [integral_sum_dirac (fun j => ENNReal.ofReal_ne_top)] at he
    simpa only [ENNReal.toReal_ofReal (borelMass_nonneg ρ _), smul_eq_mul] using he
  rw [borelHarmonicKernel, ← tsum_mul_right, ← hm, ← hs.tsum_sub hxsum]
  apply tsum_congr
  intro j
  calc
    _ = borelMass ρ j * (j : ℝ) * (harmonicIntegrand j x * (1 - x)) := by ring
    _ = _ := by rw [harmonicIntegrand_mul_one_sub]; ring

-- @node: durationIntegrand_denominator_pos
/-- If [the nonnegative branching parameter ρ is below one](hyp:ρ,hρ) and [u is strictly below ρ](hyp:hu),
[the duration-integrand denominator ρ exp(−ρ) − u exp(−u) is strictly positive](goal). -/
lemma durationIntegrand_denominator_pos (ρ : ℝ≥0) (hρ : subcritical ρ)
    {u : ℝ} (hu : u < (ρ : ℝ)) :
    0 < (ρ : ℝ) * Real.exp (-(ρ : ℝ)) - u * Real.exp (-u) := by
  have hρ' : (ρ : ℝ) < 1 := by exact_mod_cast hρ
  have hmono := mul_exp_strictMonoOn
    (show -(ρ : ℝ) ∈ Set.Ici (-1) by simp only [Set.mem_Ici]; linarith)
    (show -u ∈ Set.Ici (-1) by simp only [Set.mem_Ici]; linarith)
    (show -(ρ : ℝ) < -u by linarith)
  simp only [neg_mul] at hmono
  linarith

-- @node: durationIntegrand_continuousAt_endpoint
/-- If [the nonnegative branching parameter ρ is below one](hyp:ρ,hρ), [the duration integrand is continuous at u = ρ](goal). -/
@[fun_prop] lemma durationIntegrand_continuousAt_endpoint (ρ : ℝ≥0)
    (hρ : subcritical ρ) : ContinuousAt (durationIntegrand ρ) (ρ : ℝ) := by
  have hρ' : (ρ : ℝ) < 1 := by exact_mod_cast hρ
  have hf : HasDerivAt (fun u : ℝ => Real.exp (-u))
      (-Real.exp (-(ρ : ℝ))) (ρ : ℝ) := by
    convert (hasDerivAt_id (ρ : ℝ)).neg.exp using 1 <;> simp
  have hg : HasDerivAt (fun u : ℝ => u * Real.exp (-u))
      (Real.exp (-(ρ : ℝ)) * (1 - (ρ : ℝ))) (ρ : ℝ) := by
    convert (hasDerivAt_id (ρ : ℝ)).mul hf using 1 <;> first | rfl | (dsimp; ring)
  have hden : Real.exp (-(ρ : ℝ)) * (1 - (ρ : ℝ)) ≠ 0 :=
    ne_of_gt (mul_pos (Real.exp_pos _) (by linarith))
  have hc := hf.continuousAt_div.neg.div hg.continuousAt_div
    (by simpa only [Function.update_self] using hden)
  have heq : (fun u : ℝ =>
      -(Function.update (fun u : ℝ =>
        (Real.exp (-u) - Real.exp (-(ρ : ℝ))) / (u - (ρ : ℝ)))
          (ρ : ℝ) (-Real.exp (-(ρ : ℝ))) u) /
      Function.update (fun u : ℝ =>
        (u * Real.exp (-u) - (ρ : ℝ) * Real.exp (-(ρ : ℝ))) / (u - (ρ : ℝ)))
          (ρ : ℝ) (Real.exp (-(ρ : ℝ)) * (1 - (ρ : ℝ))) u) =
      durationIntegrand ρ := by
    funext u
    by_cases hu : u = (ρ : ℝ)
    · subst u
      simp only [Function.update_self, neg_neg, durationIntegrand, ↓reduceIte]
      field_simp
    · simp only [Function.update_of_ne hu, durationIntegrand, if_neg hu]
      rw [neg_div, div_div_div_cancel_right₀ (sub_ne_zero.mpr hu), ← div_neg, neg_sub]
  rw [← heq]
  exact hc

-- @node: durationIntegrand_continuous
/-- If [the nonnegative branching parameter ρ is below one](hyp:ρ,hρ), [the duration integrand is continuous on the closed interval from zero to ρ](goal). -/
@[fun_prop] lemma durationIntegrand_continuous (ρ : ℝ≥0) (hρ : subcritical ρ) :
    ContinuousOn (durationIntegrand ρ) (Set.Icc 0 (ρ : ℝ)) := by
  intro u hu
  by_cases he : u = (ρ : ℝ)
  · subst u
    exact (durationIntegrand_continuousAt_endpoint ρ hρ).continuousWithinAt
  · have hden := ne_of_gt (durationIntegrand_denominator_pos ρ hρ
        (lt_of_le_of_ne hu.2 he))
    have hc : ContinuousAt (fun u : ℝ =>
        (Real.exp (-u) - Real.exp (-(ρ : ℝ))) /
          ((ρ : ℝ) * Real.exp (-(ρ : ℝ)) - u * Real.exp (-u))) u := by
      fun_prop
    apply (hc.congr ?_).continuousWithinAt
    filter_upwards [eventually_ne_nhds he] with x hx
    simp [durationIntegrand, hx]


-- @node: borel_weighted_forwardSubstitution
/-- If [the nonnegative branching parameter ρ is below one](hyp:ρ,hρ), [ρ is positive](hyp:hpos), and [u lies between zero and ρ, inclusive](hyp:hu),
[the sum of the Borel mass at j times j times the forward substitution at u raised to j equals u divided by ρ(1 − u)](goal). -/
lemma borel_weighted_forwardSubstitution (ρ : ℝ≥0) (hρ : subcritical ρ)
    (hpos : 0 < ρ) {u : ℝ} (hu : u ∈ Set.Icc 0 (ρ : ℝ)) :
    (∑' j : ℕ, borelMass ρ j * (j : ℝ) * (forwardSubstitution ρ u) ^ j) =
      u / ((ρ : ℝ) * (1 - u)) := by
  have hr : 0 < (ρ : ℝ) := by exact_mod_cast hpos
  have hs : (ρ : ℝ) < 1 := by exact_mod_cast hρ
  have hw := borelPGF_weighted_identity ρ hρ (forwardSubstitution_range ρ hρ hpos hu)
  rw [borelPGF_forwardSubstitution ρ hρ hpos hu] at hw
  have he : (ρ : ℝ) * (u / (ρ : ℝ)) = u := mul_div_cancel₀ u hr.ne'
  rw [he] at hw
  apply (eq_div_iff (mul_ne_zero hr.ne' (by linarith [hu.2] : 1 - u ≠ 0))).mpr
  calc
    _ = (ρ : ℝ) *
        ((∑' j : ℕ, borelMass ρ j * (j : ℝ) * (forwardSubstitution ρ u) ^ j) *
          (1 - u)) := by ring
    _ = u := by rw [hw, he]

-- @node: forwardSubstitution_lt_one
/-- If [the nonnegative branching parameter ρ is below one](hyp:ρ,hρ), [ρ is positive](hyp:hpos), and [u is strictly below ρ](hyp:hu),
[the forward substitution u exp(−u)/(ρ exp(−ρ)) is strictly below one](goal). -/
lemma forwardSubstitution_lt_one (ρ : ℝ≥0) (hρ : subcritical ρ)
    (hpos : 0 < ρ) {u : ℝ} (hu : u < (ρ : ℝ)) :
    forwardSubstitution ρ u < 1 := by
  have hr : 0 < (ρ : ℝ) := by exact_mod_cast hpos
  rw [forwardSubstitution, div_lt_one (mul_pos hr (Real.exp_pos _))]
  linarith [durationIntegrand_denominator_pos ρ hρ hu]

-- @node: borelHarmonicKernel_substitution
/-- If [the nonnegative branching parameter ρ is below one](hyp:ρ,hρ), [ρ is positive](hyp:hpos), and [0 ≤ u < ρ](hyp:hu),
[the centered kernel, (1 − ρ) times the Borel harmonic kernel at the forward substitution minus one, multiplied by exp(−u)(1 − u)/(ρ exp(−ρ)), equals the duration integrand plus 1/ρ minus that same multiplier](goal). -/
lemma borelHarmonicKernel_substitution (ρ : ℝ≥0) (hρ : subcritical ρ)
    (hpos : 0 < ρ) {u : ℝ} (hu : u ∈ Set.Ico 0 (ρ : ℝ)) :
    ((1 - (ρ : ℝ)) * borelHarmonicKernel ρ (forwardSubstitution ρ u) - 1) *
      (Real.exp (-u) * (1 - u) / ((ρ : ℝ) * Real.exp (-(ρ : ℝ)))) =
      durationIntegrand ρ u + 1 / (ρ : ℝ) -
        Real.exp (-u) * (1 - u) / ((ρ : ℝ) * Real.exp (-(ρ : ℝ))) := by
  have hr : 0 < (ρ : ℝ) := by exact_mod_cast hpos
  have hs : (ρ : ℝ) < 1 := by exact_mod_cast hρ
  have hx := forwardSubstitution_range ρ hρ hpos ⟨hu.1, hu.2.le⟩
  have hk := borelHarmonicKernel_geometric_identity ρ hρ hx
  rw [borel_weighted_forwardSubstitution ρ hρ hpos ⟨hu.1, hu.2.le⟩] at hk
  have h1 : 1 - forwardSubstitution ρ u ≠ 0 := by
    linarith [forwardSubstitution_lt_one ρ hρ hpos hu.2]
  have h2 : 1 - (ρ : ℝ) ≠ 0 := by linarith
  have h3 : 1 - u ≠ 0 := by linarith [hu.2]
  have h4 := ne_of_gt (durationIntegrand_denominator_pos ρ hρ hu.2)
  have h5 := Real.exp_ne_zero (-(ρ : ℝ))
  have hk' : borelHarmonicKernel ρ (forwardSubstitution ρ u) =
      (1 / (1 - (ρ : ℝ)) - u / ((ρ : ℝ) * (1 - u))) /
        (1 - forwardSubstitution ρ u) := (eq_div_iff h1).mpr hk
  rw [hk', durationIntegrand, if_neg (ne_of_lt hu.2)]
  dsimp only [forwardSubstitution]
  field_simp
  <;> ring

-- @node: harmonic_borel_integral
/-- If [the nonnegative branching parameter ρ is below one](hyp:ρ,hρ) and [the duration integrand agrees with its quotient below ρ, is continuous on the closed interval from zero to ρ, and has endpoint value 1/(1 − ρ)](hyp:hendpoint),
[the Borel expectation of j times its harmonic number, multiplied by 1 − ρ and reduced by one, equals the integral of the duration integrand from zero to ρ](goal). -/
lemma harmonic_borel_integral (ρ : ℝ≥0) (hρ : subcritical ρ)
    (hendpoint : continuousEndpointConvention ρ) :
    (1 - (ρ : ℝ)) * (∫ j : ℕ, (j : ℝ) * harmonicNumber j ∂borelMeasure ρ) - 1 =
      ∫ u in (0 : ℝ)..(ρ : ℝ), durationIntegrand ρ u := by
  by_cases hzero : ρ = 0
  · subst ρ
    rw [borelMeasure_zero_parameter]
    norm_num [harmonicNumber, harmonic]
  have hpos : 0 < ρ := bot_lt_iff_ne_bot.mpr hzero
  rw [borel_centered_euler_integral ρ hρ]
  have hr : 0 < (ρ : ℝ) := by exact_mod_cast hpos
  let d : ℝ → ℝ := fun u =>
    Real.exp (-u) * (1 - u) / ((ρ : ℝ) * Real.exp (-(ρ : ℝ)))
  let g : ℝ → ℝ := fun x => (1 - (ρ : ℝ)) * borelHarmonicKernel ρ x - 1
  have hd (u : ℝ) : HasDerivAt (forwardSubstitution ρ) (d u) u :=
    forwardSubstitution_derivative ρ hpos u
  have hdc : Continuous d := by dsimp [d]; fun_prop
  have hgc : ContinuousOn g (Set.Icc (0 : ℝ) 1) :=
    ((borelHarmonicKernel_continuousOn ρ hρ).const_mul _).sub continuousOn_const
  have hbounds : Set.uIcc (0 : ℝ) (ρ : ℝ) = Set.Icc 0 (ρ : ℝ) :=
    Set.uIcc_of_le ρ.coe_nonneg
  have hsub := intervalIntegral.integral_comp_mul_deriv'
    (a := (0 : ℝ)) (b := (ρ : ℝ)) (fun u _ => hd u) hdc.continuousOn
    (hgc.mono (by
      rintro x ⟨u, hu, rfl⟩
      exact forwardSubstitution_range ρ hρ hpos (hbounds ▸ hu)))
  have hden : (ρ : ℝ) * Real.exp (-(ρ : ℝ)) ≠ 0 := by positivity
  have hfzero : forwardSubstitution ρ 0 = 0 := by simp [forwardSubstitution]
  have hfone : forwardSubstitution ρ (ρ : ℝ) = 1 := by
    exact div_self hden
  rw [hfzero, hfone] at hsub
  change (∫ x in (0 : ℝ)..1, g x) = _
  rw [← hsub]
  have heq : (∫ u in (0 : ℝ)..(ρ : ℝ), (g ∘ forwardSubstitution ρ) u * d u) =
      ∫ u in (0 : ℝ)..(ρ : ℝ), durationIntegrand ρ u + 1 / (ρ : ℝ) - d u := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [volume.ae_ne (ρ : ℝ)] with u hune hu
    have hu' : u ∈ Set.Ioc (0 : ℝ) (ρ : ℝ) := by
      simpa only [Set.uIoc_of_le ρ.coe_nonneg] using hu
    exact borelHarmonicKernel_substitution ρ hρ hpos
      ⟨hu'.1.le, lt_of_le_of_ne hu'.2 hune⟩
  rw [heq]
  have hi : IntervalIntegrable (durationIntegrand ρ) volume 0 (ρ : ℝ) :=
    ContinuousOn.intervalIntegrable (hbounds.symm ▸ durationIntegrand_continuous ρ hρ)
  have hid : IntervalIntegrable d volume 0 (ρ : ℝ) := hdc.intervalIntegrable 0 (ρ : ℝ)
  have hdi : (∫ u in (0 : ℝ)..(ρ : ℝ), d u) = 1 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u) hid,
      hfone, hfzero, sub_zero]
  rw [intervalIntegral.integral_sub (hi.add intervalIntegrable_const) hid,
    intervalIntegral.integral_add hi intervalIntegrable_const, hdi,
    intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]
  rw [mul_one_div_cancel hr.ne']
  ring

end Papers.HawkesD75660b

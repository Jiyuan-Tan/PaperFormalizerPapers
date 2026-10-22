module
public import Papers.TbsExtremeEffects.Helpers.Hill.ExponentialLaw
public import Toolkit.Foundations.Probability.Conditioning.ConditionalIntegrability

/-! Integrability of finite exponential spacing sums from their exact conditional
increment moments, using bounded truncations of the adapted multiplier. -/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
variable {Z : Type*} [mZ : MeasurableSpace Z]

/-- If [the process is strongly adapted](hyp:hB), [starts at zero](hyp:hzero), [the exponential-moment constant is nonzero](hyp:hc), and [each increment has the stated conditional exponential moment before time `n`](hyp:hMoment), then [all exponential partial sums through `n` are integrable](goal).

No independence beyond these conditional identities is needed for this step. -/
-- @node: hill_partial_exponential_integrable
lemma hill_partial_exponential_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℕ → Ω → ℝ)
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (hB : StronglyAdapted ℱ B)
    (hzero : ∀ w, B 0 w = 0) (n : ℕ) (lam c : ℝ) (hc : c ≠ 0)
    (hMoment : ∀ i < n,
      P[(fun w => Real.exp (lam * (B (i + 1) w - B i w))) | ℱ i]
        =ᵐ[P] fun _ => c) :
    ∀ i ≤ n, Integrable (fun w => Real.exp (lam * B i w)) P := by
  intro i hi
  induction i with
  | zero => simpa only [hzero, mul_zero, Real.exp_zero] using
      (integrable_const (1 : ℝ) : Integrable (fun _ : Ω => (1 : ℝ)) P)
  | succ i ih =>
    have hstep := hMoment i (by omega)
    have hInc := hill_integrable_of_nonzero_conditional_moment P (ℱ i) _ hc hstep
    have hPrev := ih (by omega)
    have hMeas : StronglyMeasurable[ℱ i] (fun w => Real.exp (lam * B i w)) := by
      apply Measurable.stronglyMeasurable
      have hb := (hB i).measurable
      fun_prop
    have hWeighted : Integrable (fun w =>
        P[(fun w => Real.exp (lam * (B (i + 1) w - B i w))) | ℱ i] w *
          Real.exp (lam * B i w)) P := by
      apply (hPrev.const_mul c).congr
      filter_upwards [hstep] with w hw
      rw [hw]
    have hProd := Toolkit.Foundations.Probability.Conditioning.integrable_mul_of_integrable_condExp_mul P hInc
      (fun w => (Real.exp_pos _).le) (ℱ.le i) hMeas
      (fun w => (Real.exp_pos _).le) hWeighted
    convert hProd using 1
    funext w
    rw [← Real.exp_add]
    congr 1
    ring

/-- If [the process is strongly adapted](hyp:hB), [starts at zero](hyp:hzero), [the exponential tilt is positive](hyp:hlam) and [less than one](hyp:hlamone), and [both signed increments have the stated exact conditional moments](hyp:hMoment), then [both compensated exponential processes are integrable through time `n`](goal). -/
-- @node: hill_compensated_integrable_of_exact_moments
lemma hill_compensated_integrable_of_exact_moments
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℕ → Ω → ℝ)
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (hB : StronglyAdapted ℱ B)
    (hzero : ∀ w, B 0 w = 0) (n : ℕ) {lam : ℝ}
    (hlam : 0 < lam) (hlamone : lam < 1)
    (hMoment : ∀ i < n,
      P[(fun w => Real.exp (lam * (B (i + 1) w - B i w))) | ℱ i]
        =ᵐ[P] (fun _ => Real.exp (-lam) / (1 - lam)) ∧
      P[(fun w => Real.exp (-lam * (B (i + 1) w - B i w))) | ℱ i]
        =ᵐ[P] (fun _ => Real.exp lam / (1 + lam))) :
    ∀ i ≤ n,
      Integrable (fun w => Real.exp
        (lam * B i w - (i : ℝ) * (lam ^ 2 / (2 * (1 - lam))))) P ∧
      Integrable (fun w => Real.exp
        (lam * (-B i w) - (i : ℝ) * (lam ^ 2 / (2 * (1 - lam))))) P := by
  have hplus := hill_partial_exponential_integrable P B ℱ hB hzero n lam
    (Real.exp (-lam) / (1 - lam)) (ne_of_gt (by positivity))
    (fun i hi => (hMoment i hi).1)
  have hminus := hill_partial_exponential_integrable P B ℱ hB hzero n (-lam)
    (Real.exp lam / (1 + lam)) (ne_of_gt (by positivity))
    (fun i hi => (hMoment i hi).2)
  intro i hi
  constructor
  · convert (hplus i hi).const_mul
      (Real.exp (-(i : ℝ) * (lam ^ 2 / (2 * (1 - lam))))) using 1
    funext w
    rw [← Real.exp_add]
    congr 1
    ring
  · convert (hminus i hi).const_mul
      (Real.exp (-(i : ℝ) * (lam ^ 2 / (2 * (1 - lam))))) using 1
    funext w
    rw [← Real.exp_add]
    congr 1
    ring

end Papers.TbsExtremeEffects

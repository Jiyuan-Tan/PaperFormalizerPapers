module
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVSetup
public import Papers.TsAdaptiveEstimationInference.Helpers.IterBias
/-! Empirical center changes and deterministic recursive RDIV stability.

These lemmas implement the algebra and induction in the stability roadmap.
They do not supply the simultaneous fitting and calibration event.
-/
@[expose] public section
set_option linter.style.longLine false
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory

variable {𝒲 X Z Ω : Type*} [MeasurableSpace 𝒲] [MeasurableSpace X]
  [MeasurableSpace Z] [MeasurableSpace Ω]
  (V : IVWorld 𝒲 X Z) (P : Measure Ω)
  (sample : AnalysisSample V P) (split : SampleSplit)

/-- [The difference between the empirical squared-distance contrasts for two
centers equals twice the fitting-block average of the product of the candidate
difference and the center difference](goal). -/
-- @node: iter_rdiv_empirical_center_identity
lemma iter_rdiv_empirical_center_identity (n : ℕ) (ω : Ω)
    (h a center previous : V.Hbar.toSubmodule) :
    primalEmpDistanceSq V P sample split n ω h center -
      primalEmpDistanceSq V P sample split n ω a center -
      primalEmpDistanceSq V P sample split n ω h previous +
      primalEmpDistanceSq V P sample split n ω a previous =
      2 * blockAverage V P sample (split.fit n)
        (fun w => (primalVersion V h (V.xOf w) - primalVersion V a (V.xOf w)) *
          (primalVersion V previous (V.xOf w) - primalVersion V center (V.xOf w))) ω := by
  unfold primalEmpDistanceSq blockAverage
  simp only [← mul_sub, ← mul_add, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  conv_rhs => rw [mul_left_comm, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- If [the fitted candidate has no larger penalized empirical loss than the
comparator when centered at the previous fitted iterate](hyp:hOpt), then
[its penalized loss contrast around the fixed center is at most twice the
penalty times the empirical product of the candidate and center differences](goal). -/
-- @node: iter_rdiv_fixed_center_optimality
lemma iter_rdiv_fixed_center_optimality (n : ℕ) (ω : Ω) (lam : ℝ)
    (loss : V.Hbar.toSubmodule → ℝ) (h a center previous : V.Hbar.toSubmodule)
    (hOpt : loss h + lam * primalEmpDistanceSq V P sample split n ω h previous ≤
      loss a + lam * primalEmpDistanceSq V P sample split n ω a previous) :
    (loss h + lam * primalEmpDistanceSq V P sample split n ω h center) -
      (loss a + lam * primalEmpDistanceSq V P sample split n ω a center) ≤
      2 * lam * blockAverage V P sample (split.fit n)
        (fun w => (primalVersion V h (V.xOf w) - primalVersion V a (V.xOf w)) *
          (primalVersion V previous (V.xOf w) - primalVersion V center (V.xOf w))) ω := by
  have hid := iter_rdiv_empirical_center_identity V P sample split n ω h a center previous
  have hm := congrArg (fun x : ℝ => lam * x) hid
  nlinarith only [hOpt, hm]

/-- [The fitting-block average of the product of the candidate difference and
the center difference is at most the product of their empirical root mean
squared distances](goal). -/
-- @node: iter_rdiv_empirical_cross_le
lemma iter_rdiv_empirical_cross_le (n : ℕ) (ω : Ω)
    (h a previous center : V.Hbar.toSubmodule) :
    blockAverage V P sample (split.fit n)
      (fun w => (primalVersion V h (V.xOf w) - primalVersion V a (V.xOf w)) *
        (primalVersion V previous (V.xOf w) - primalVersion V center (V.xOf w))) ω ≤
      Real.sqrt (primalEmpDistanceSq V P sample split n ω h a) *
        Real.sqrt (primalEmpDistanceSq V P sample split n ω previous center) := by
  let c : ℝ := ((split.fit n).card : ℝ)⁻¹
  let f : ℕ → ℝ := fun i =>
    primalVersion V h (V.xOf (sample.Z i ω)) - primalVersion V a (V.xOf (sample.Z i ω))
  let g : ℕ → ℝ := fun i => primalVersion V previous (V.xOf (sample.Z i ω)) -
    primalVersion V center (V.xOf (sample.Z i ω))
  have hc : 0 ≤ c := by dsimp [c]; positivity
  change c * ∑ i ∈ split.fit n, f i * g i ≤
    Real.sqrt (c * ∑ i ∈ split.fit n, f i ^ 2) *
      Real.sqrt (c * ∑ i ∈ split.fit n, g i ^ 2)
  calc
    _ ≤ c * (Real.sqrt (∑ i ∈ split.fit n, f i ^ 2) *
        Real.sqrt (∑ i ∈ split.fit n, g i ^ 2)) :=
      mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt (split.fit n) f g) hc
    _ = _ := by
      rw [Real.sqrt_mul hc, Real.sqrt_mul hc]
      conv_lhs => rw [← Real.sq_sqrt hc]
      ring

/-- Suppose [K is at least one](hyp:hK), [the accuracy is nonnegative](hyp:hδ),
[the current error magnitude is nonnegative](hyp:hu), [the previous error
magnitude is nonnegative](hyp:hp), and [the penalty lies in $(0,2]$](hyp:hlam).
If [the current penalized squared error plus squared weak error is bounded by
twice the penalty times K squared times the product of current and previous
errors each augmented by accuracy, plus K times accuracy times current error
and K times accuracy squared](hyp:henergy),
then [it is at most the sum of accuracy squared divided by the penalty and
the penalty times previous error squared, multiplied by
64 K⁴ + 24 K² + 4 K + 1](goal). -/
-- @node: iter_rdiv_young_absorption
lemma iter_rdiv_young_absorption (K δ lam u previous weak : ℝ)
    (hK : 1 ≤ K) (hδ : 0 ≤ δ) (hu : 0 ≤ u) (hp : 0 ≤ previous)
    (hlam : lam ∈ Set.Ioc (0 : ℝ) 2)
    (henergy : lam * u ^ 2 + weak ^ 2 ≤
      2 * lam * K ^ 2 * (u + δ) * (previous + δ) + K * (δ * u + δ ^ 2)) :
    lam * u ^ 2 + weak ^ 2 ≤
      (64 * K ^ 4 + 24 * K ^ 2 + 4 * K + 1) * δ ^ 2 / lam +
      (64 * K ^ 4 + 24 * K ^ 2 + 4 * K + 1) * lam * previous ^ 2 := by
  have hK0 : 0 ≤ K := by linarith
  have hlam0 : 0 ≤ lam := hlam.1.le
  let U := lam * u
  let Q := lam * previous
  have hU : 0 ≤ U := mul_nonneg hlam.1.le hu
  have hQ : 0 ≤ Q := mul_nonneg hlam.1.le hp
  have hld : lam * δ ≤ 2 * δ := mul_le_mul_of_nonneg_right hlam.2 hδ
  have hprod : (U + lam * δ) * (Q + lam * δ) ≤ (U + 2 * δ) * (Q + 2 * δ) :=
    mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
  have hmul := mul_le_mul_of_nonneg_left henergy hlam.1.le
  have hinflate := mul_le_mul_of_nonneg_left hprod (by positivity : 0 ≤ 2 * K ^ 2)
  have hsmall := mul_le_mul_of_nonneg_left hlam.2 (by positivity : 0 ≤ K * δ ^ 2)
  have hscaled : U ^ 2 + lam * weak ^ 2 ≤
      2 * K ^ 2 * (U + 2 * δ) * (Q + 2 * δ) + K * δ * U + 2 * K * δ ^ 2 := by
    dsimp [U, Q] at *
    nlinarith only [hmul, hinflate, hsmall]
  have hy1 := sq_nonneg (U - 8 * K ^ 2 * Q)
  have hy2 := sq_nonneg (U - 16 * K ^ 2 * δ)
  have hy3 := sq_nonneg (U - 4 * K * δ)
  have hy4 := mul_nonneg (sq_nonneg K) (sq_nonneg (Q - δ))
  have hw : 0 ≤ lam * weak ^ 2 := by positivity
  have habsorb : U ^ 2 + lam * weak ^ 2 ≤
      (64 * K ^ 4 + 24 * K ^ 2 + 4 * K) * δ ^ 2 +
        (16 * K ^ 4 + 4 * K ^ 2) * Q ^ 2 := by
    nlinarith only [hscaled, hy1, hy2, hy3, hy4, hw]
  have hcoeff : 16 * K ^ 4 + 4 * K ^ 2 ≤
      64 * K ^ 4 + 24 * K ^ 2 + 4 * K + 1 := by
    nlinarith [sq_nonneg K, pow_nonneg hK0 4]
  have hfinal : U ^ 2 + lam * weak ^ 2 ≤
      (64 * K ^ 4 + 24 * K ^ 2 + 4 * K + 1) * δ ^ 2 +
        (64 * K ^ 4 + 24 * K ^ 2 + 4 * K + 1) * Q ^ 2 := by
    nlinarith only [habsorb, mul_le_mul_of_nonneg_right hcoeff (sq_nonneg Q), sq_nonneg δ]
  apply (mul_le_mul_iff_right₀ hlam.1).mp
  conv_rhs => rw [mul_add, mul_div_cancel₀ _ (ne_of_gt hlam.1)]
  dsimp [U, Q] at hfinal
  nlinarith only [hfinal]

/-- For [a propagation constant C](hyp:C), [the stability coefficient sequence](goal)
[starts at zero](step:1) and [sets each next coefficient to C times one plus
the preceding coefficient](step:2). -/
-- @node: iterRdivStabilityCoefficients
def iterRdivStabilityCoefficients (C : ℝ) : ℕ → ℝ
  | 0 => 0
  | j + 1 => C * (1 + iterRdivStabilityCoefficients C j)

/-- If [the propagation constant is at least one](hyp:hC), then [the initial
stability coefficient is zero, every coefficient is nonnegative, and every
coefficient at a positive stage is at least one](goal). -/
-- @node: iterRdivStabilityCoefficients_bounds
lemma iterRdivStabilityCoefficients_bounds (C : ℝ) (hC : 1 ≤ C) :
    iterRdivStabilityCoefficients C 0 = 0 ∧
      (∀ j, 0 ≤ iterRdivStabilityCoefficients C j) ∧
      ∀ j, 1 ≤ j → 1 ≤ iterRdivStabilityCoefficients C j := by
  have hnonneg : ∀ j, 0 ≤ iterRdivStabilityCoefficients C j := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      exact mul_nonneg (by linarith) (by linarith)
  refine ⟨rfl, hnonneg, ?_⟩
  rintro (_ | j) hj
  · omega
  · change 1 ≤ C * (1 + iterRdivStabilityCoefficients C j)
    nlinarith [mul_nonneg (by linarith : 0 ≤ C) (hnonneg j)]

/-- Suppose [C is at least one](hyp:hC), [the penalty is positive](hyp:hlam),
[the initial strong error is zero](hyp:hzero), and [all projected errors are
nonnegative](hyp:hprojected). If [each next energy is at most C times accuracy
squared divided by the penalty plus C times the penalty times the previous
strong error](hyp:hstep), then [at every positive stage through the horizon,
the energy is bounded by its stability coefficient times accuracy squared
divided by the penalty, and the strong error by the same numerator divided
by penalty squared](goal). -/
-- @node: iter_rdiv_recursive_energy_bound
lemma iter_rdiv_recursive_energy_bound (C δ lam : ℝ) (t : ℕ)
    (strong projected : ℕ → ℝ) (hC : 1 ≤ C) (hlam : 0 < lam)
    (hzero : strong 0 = 0) (hprojected : ∀ j, 0 ≤ projected j)
    (hstep : ∀ j, j < t →
      lam * strong (j + 1) + projected (j + 1) ≤
        C * δ ^ 2 / lam + C * lam * strong j) :
    ∀ j, 1 ≤ j → j ≤ t →
      lam * strong j + projected j ≤ iterRdivStabilityCoefficients C j * δ ^ 2 / lam ∧
      strong j ≤ iterRdivStabilityCoefficients C j * δ ^ 2 / lam ^ 2 := by
  have hC0 : 0 ≤ C := by linarith
  have hbound : ∀ j, j ≤ t →
      lam * strong j ≤ iterRdivStabilityCoefficients C j * δ ^ 2 / lam := by
    intro j
    induction j with
    | zero => simp [hzero, iterRdivStabilityCoefficients]
    | succ j ih =>
      intro hj
      have hprev := ih (by omega)
      have hm := mul_le_mul_of_nonneg_left hprev hC0
      have he := hstep j (by omega)
      have hid : C * δ ^ 2 / lam +
          C * (iterRdivStabilityCoefficients C j * δ ^ 2 / lam) =
          iterRdivStabilityCoefficients C (j + 1) * δ ^ 2 / lam := by
        simp only [iterRdivStabilityCoefficients]
        ring
      rw [← hid]
      nlinarith only [he, hm, hprojected (j + 1)]
  intro j hj hjt
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  have hm := mul_le_mul_of_nonneg_left (hbound k (by omega)) hC0
  have he := hstep k (by omega)
  have henergy : lam * strong (k + 1) + projected (k + 1) ≤
      iterRdivStabilityCoefficients C (k + 1) * δ ^ 2 / lam := by
    have hid : iterRdivStabilityCoefficients C (k + 1) * δ ^ 2 / lam =
        C * δ ^ 2 / lam + C * (iterRdivStabilityCoefficients C k * δ ^ 2 / lam) := by
      simp only [iterRdivStabilityCoefficients]
      ring
    rw [hid]
    nlinarith only [he, hm]
  refine ⟨henergy, ?_⟩
  apply (le_div_iff₀ (sq_pos_of_pos hlam)).2
  have hstrong := hbound (k + 1) hjt
  have hm' := mul_le_mul_of_nonneg_right hstrong hlam.le
  rw [div_mul_cancel₀ _ (ne_of_gt hlam)] at hm'
  nlinarith only [hm']

/-- Suppose [K is at least one](hyp:hK), [the accuracy is nonnegative](hyp:hδ),
[the penalty lies in $(0,2]$](hyp:hlam), and [the initial error is zero](hyp:hzero).
If [each step's energy is bounded by twice the penalty times K squared times
the product of current and previous error norms augmented by the accuracy,
plus K times the accuracy-error and squared-accuracy terms](hyp:henergy), then
[with C = 64 K⁴ + 24 K² + 4 K + 1, every positive stage through the horizon
has energy at most its stability coefficient times accuracy squared divided
by the penalty, and squared error norm at most that numerator divided by
penalty squared](goal). -/
-- @node: iter_rdiv_stability_from_energy
lemma iter_rdiv_stability_from_energy (K δ lam : ℝ) (t : ℕ)
    (errors : ℕ → V.Hbar.toSubmodule) (hK : 1 ≤ K) (hδ : 0 ≤ δ)
    (hlam : lam ∈ Set.Ioc (0 : ℝ) 2) (hzero : errors 0 = 0)
    (henergy : ∀ j, j < t →
      lam * ‖errors (j + 1)‖ ^ 2 + ‖projCondExpOp V (errors (j + 1))‖ ^ 2 ≤
        2 * lam * K ^ 2 * (‖errors (j + 1)‖ + δ) * (‖errors j‖ + δ) +
          K * (δ * ‖errors (j + 1)‖ + δ ^ 2)) :
    let C := 64 * K ^ 4 + 24 * K ^ 2 + 4 * K + 1
    ∀ j, 1 ≤ j → j ≤ t →
      lam * ‖errors j‖ ^ 2 + ‖projCondExpOp V (errors j)‖ ^ 2 ≤
        iterRdivStabilityCoefficients C j * δ ^ 2 / lam ∧
      ‖errors j‖ ^ 2 ≤ iterRdivStabilityCoefficients C j * δ ^ 2 / lam ^ 2 := by
  dsimp only
  apply iter_rdiv_recursive_energy_bound _ δ lam t
    (fun j => ‖errors j‖ ^ 2) (fun j => ‖projCondExpOp V (errors j)‖ ^ 2)
  · have hK0 : 0 ≤ K := by linarith
    nlinarith [pow_nonneg hK0 4, sq_nonneg K]
  · exact hlam.1
  · simp [hzero]
  · intro j; positivity
  · intro j hj
    exact iter_rdiv_young_absorption K δ lam _ _ _ hK hδ
      (norm_nonneg _) (norm_nonneg _) hlam (henergy j hj)

end Papers.TsAdaptiveEstimationInference

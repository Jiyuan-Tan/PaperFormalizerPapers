module
public import Papers.TsAdaptiveEstimationInference.Helpers.IterRDIVRecursion
/-! Fixed-population curvature and empirical-center assembly for iterative RDIV.

These deterministic lemmas retain the observed representatives and zero-initialized
empirical iterates. The fixed-center and norm comparisons must still be proved on
the common concentration event; no such event is supplied here.
-/
public section
set_option linter.style.longLine false
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory
variable {𝒲 X Z Ω : Type*} [MeasurableSpace 𝒲] [MeasurableSpace X]
  [MeasurableSpace Z] [MeasurableSpace Ω]
  (V : IVWorld 𝒲 X Z) (P : Measure Ω)
  (sample : AnalysisSample V P) (split : SampleSplit)

/-- For [a positive penalty](hyp:hlam), [the population objective's excess over the
next population iterate equals the penalty-weighted squared distance to that
iterate plus the squared norm of its projected conditional-mean error](goal). -/
-- @node: iter_rdiv_population_curvature
lemma iter_rdiv_population_curvature (lam : ℝ) (hlam : 0 < lam) (j : ℕ)
    (h : V.Hbar.toSubmodule) :
    (‖projCondExpOp V h - momentRepresenter V‖ ^ 2 +
        lam * ‖h - populationIterate V lam j‖ ^ 2) -
      (‖projCondExpOp V (populationIterate V lam (j + 1)) - momentRepresenter V‖ ^ 2 +
        lam * ‖populationIterate V lam (j + 1) - populationIterate V lam j‖ ^ 2) =
      lam * ‖h - populationIterate V lam (j + 1)‖ ^ 2 +
        ‖projCondExpOp V (h - populationIterate V lam (j + 1))‖ ^ 2 := by
  let a := populationIterate V lam (j + 1)
  let c := populationIterate V lam j
  have hnormal : normalOp V a + lam • a =
      adjointOp V (momentRepresenter V) + lam • c :=
    resolvent_normalEquation V lam hlam _
  have hcross : inner ℝ (projCondExpOp V a - momentRepresenter V)
      (projCondExpOp V (h - a)) + lam * inner ℝ (a - c) (h - a) = 0 := by
    have hi := congrArg (fun x => inner ℝ x (h - a)) hnormal
    have hia : inner ℝ (lam • a) (h - a) = lam * inner ℝ a (h - a) := by
      exact real_inner_smul_left a (h - a) lam
    have hic : inner ℝ (lam • c) (h - a) = lam * inner ℝ c (h - a) := by
      exact real_inner_smul_left c (h - a) lam
    simp only [inner_add_left, hia, hic] at hi
    simp only [normalOp,
      ContinuousLinearMap.comp_apply, adjointOp, ContinuousLinearMap.adjoint_inner_left,
      inner_sub_left] at hi ⊢
    linarith
  have hT : projCondExpOp V h - momentRepresenter V =
      (projCondExpOp V a - momentRepresenter V) + projCondExpOp V (h - a) := by
    rw [map_sub]
    abel
  have hc : h - c = (a - c) + (h - a) := by abel
  change (‖projCondExpOp V h - momentRepresenter V‖ ^ 2 + lam * ‖h - c‖ ^ 2) -
    (‖projCondExpOp V a - momentRepresenter V‖ ^ 2 + lam * ‖a - c‖ ^ 2) =
      lam * ‖h - a‖ ^ 2 + ‖projCondExpOp V (h - a)‖ ^ 2
  rw [hT, hc, norm_add_sq_real, norm_add_sq_real]
  nlinarith only [hcross]

/-- If [the comparison constant is nonnegative](hyp:hD), [the radius is
nonnegative](hyp:hδ), and [the empirical squared distance differs from the
population squared distance by at most the constant times the radius-distance
product plus the squared radius](hyp:hComparison), then [the empirical distance
is at most one plus the constant times the sum of population distance and radius](goal). -/
-- @node: iter_rdiv_empirical_norm_of_comparison
lemma iter_rdiv_empirical_norm_of_comparison (n : ℕ) (ω : Ω) (D δ : ℝ)
    (h a : V.Hbar.toSubmodule) (hD : 0 ≤ D) (hδ : 0 ≤ δ)
    (hComparison : |primalEmpDistanceSq V P sample split n ω h a - ‖h - a‖ ^ 2| ≤
      D * (δ * ‖h - a‖ + δ ^ 2)) :
    Real.sqrt (primalEmpDistanceSq V P sample split n ω h a) ≤
      (D + 1) * (‖h - a‖ + δ) := by
  apply (Real.sqrt_le_iff).2
  refine ⟨by positivity, ?_⟩
  have hupper := (abs_le.mp hComparison).2
  have hcross : δ * ‖h - a‖ ≤ (‖h - a‖ + δ) ^ 2 := by
    nlinarith [norm_nonneg (h - a)]
  have hdelta : δ ^ 2 ≤ (‖h - a‖ + δ) ^ 2 := by
    nlinarith [norm_nonneg (h - a)]
  have hnorm : ‖h - a‖ ^ 2 ≤ (‖h - a‖ + δ) ^ 2 := by
    nlinarith [norm_nonneg (h - a)]
  have hscaled := mul_le_mul_of_nonneg_left (add_le_add hcross hdelta) hD
  have hrest : 0 ≤ D ^ 2 * (‖h - a‖ + δ) ^ 2 := by positivity
  nlinarith only [hupper, hscaled, hnorm, hrest]

/-- With [a positive penalty](hyp:hlam), if [the population objective difference
is bounded by the empirical objective difference with the previous population
center plus the localized remainder](hyp:hComparison), then [the penalty-weighted
squared error plus projected squared error is bounded by that same empirical
objective difference and remainder](goal). -/
-- @node: iter_rdiv_fixed_center_of_objective_comparison
lemma iter_rdiv_fixed_center_of_objective_comparison (n j : ℕ) (ω : Ω)
    (K δ lam : ℝ) (loss : V.Hbar.toSubmodule → ℝ) (h : V.Hbar.toSubmodule)
    (hlam : 0 < lam)
    (hComparison :
      (‖projCondExpOp V h - momentRepresenter V‖ ^ 2 -
        ‖projCondExpOp V (populationIterate V lam (j + 1)) - momentRepresenter V‖ ^ 2) +
        lam * (‖h - populationIterate V lam j‖ ^ 2 -
          ‖populationIterate V lam (j + 1) - populationIterate V lam j‖ ^ 2) ≤
      (loss h - loss (populationIterate V lam (j + 1))) +
        lam * (primalEmpDistanceSq V P sample split n ω h (populationIterate V lam j) -
          primalEmpDistanceSq V P sample split n ω
            (populationIterate V lam (j + 1)) (populationIterate V lam j)) +
        K * (δ * ‖h - populationIterate V lam (j + 1)‖ + δ ^ 2)) :
    lam * ‖h - populationIterate V lam (j + 1)‖ ^ 2 +
        ‖projCondExpOp V (h - populationIterate V lam (j + 1))‖ ^ 2 ≤
      (loss h + lam * primalEmpDistanceSq V P sample split n ω h (populationIterate V lam j)) -
        (loss (populationIterate V lam (j + 1)) + lam * primalEmpDistanceSq V P sample split n ω
          (populationIterate V lam (j + 1)) (populationIterate V lam j)) +
        K * (δ * ‖h - populationIterate V lam (j + 1)‖ + δ ^ 2) := by
  have hcurvature := iter_rdiv_population_curvature V lam hlam j h
  linarith only [hComparison, hcurvature]

/-- If [the comparison constant is at least one](hyp:hK), [the radius is
nonnegative](hyp:hδ), [the penalty is positive](hyp:hlam), [the candidate has no
larger empirical objective than the comparator when centered at the previous
estimate](hyp:hOpt), [the fixed-center energy comparison holds](hyp:hFixed), and
[the current and previous empirical distances obey their population-distance
envelopes](hyp:hCurrent,hPrevious), then [the candidate's energy is bounded by
twice the penalty times the squared comparison constant times the two
distance-plus-radius factors, plus the localized remainder](goal). -/
-- @node: iter_rdiv_one_step_of_fixed_center
lemma iter_rdiv_one_step_of_fixed_center (n : ℕ) (ω : Ω) (K δ lam : ℝ)
    (loss : V.Hbar.toSubmodule → ℝ) (h a center previous : V.Hbar.toSubmodule)
    (hK : 1 ≤ K) (hδ : 0 ≤ δ) (hlam : 0 < lam)
    (hOpt : loss h + lam * primalEmpDistanceSq V P sample split n ω h previous ≤
      loss a + lam * primalEmpDistanceSq V P sample split n ω a previous)
    (hFixed : lam * ‖h - a‖ ^ 2 + ‖projCondExpOp V (h - a)‖ ^ 2 ≤
      (loss h + lam * primalEmpDistanceSq V P sample split n ω h center) -
        (loss a + lam * primalEmpDistanceSq V P sample split n ω a center) +
          K * (δ * ‖h - a‖ + δ ^ 2))
    (hCurrent : Real.sqrt (primalEmpDistanceSq V P sample split n ω h a) ≤
      K * (‖h - a‖ + δ))
    (hPrevious : Real.sqrt (primalEmpDistanceSq V P sample split n ω previous center) ≤
      K * (‖previous - center‖ + δ)) :
    lam * ‖h - a‖ ^ 2 + ‖projCondExpOp V (h - a)‖ ^ 2 ≤
      2 * lam * K ^ 2 * (‖h - a‖ + δ) * (‖previous - center‖ + δ) +
        K * (δ * ‖h - a‖ + δ ^ 2) := by
  have hcenter := iter_rdiv_fixed_center_optimality V P sample split n ω lam
    loss h a center previous hOpt
  have hcross := iter_rdiv_empirical_cross_le V P sample split n ω h a previous center
  have hprod := mul_le_mul hCurrent hPrevious (Real.sqrt_nonneg _)
    (by positivity : 0 ≤ K * (‖h - a‖ + δ))
  have hscaled := mul_le_mul_of_nonneg_left (hcross.trans hprod)
    (by positivity : 0 ≤ 2 * lam)
  calc
    _ ≤ _ := hFixed
    _ ≤ 2 * lam * blockAverage V P sample (split.fit n)
        (fun w => (primalVersion V h (V.xOf w) - primalVersion V a (V.xOf w)) *
          (primalVersion V previous (V.xOf w) - primalVersion V center (V.xOf w))) ω +
          K * (δ * ‖h - a‖ + δ ^ 2) := add_le_add hcenter le_rfl
    _ ≤ _ := by nlinarith only [hscaled]

/-- Suppose [the comparison constant is at least one](hyp:hK), [the radius is
nonnegative](hyp:hδ), [the penalty lies in $(0,2]$](hyp:hlam), [the candidates are
zero-initialized empirical iterates](hyp:hEst), [the positive population iterates
belong to the hypothesis class](hyp:hStar), [each fixed-center energy comparison
holds](hyp:hFixed), and [the empirical-distance envelope holds through the
horizon, including zero](hyp:hNorm). Then [every positive iterate has energy at
most the recursive stability coefficient times the squared radius divided by
the penalty, and squared estimation error at most the same numerator divided
by the squared penalty, with base constant 64 K⁴ + 24 K² + 4 K + 1](goal). -/
-- @node: iter_rdiv_stability_of_fixed_center
lemma iter_rdiv_stability_of_fixed_center (n t : ℕ) (ω : Ω) (K δ lam : ℝ)
    (loss : Ω → V.Hbar.toSubmodule → ℝ)
    (candidate : ℕ → Ω → V.Hbar.toSubmodule)
    (hK : 1 ≤ K) (hδ : 0 ≤ δ) (hlam : lam ∈ Set.Ioc (0 : ℝ) 2)
    (hEst : IsEmpiricalIterate V loss (primalEmpDistanceSq V P sample split n)
      candidate t lam)
    (hStar : ∀ j, 1 ≤ j → j ≤ t → populationIterate V lam j ∈ V.H)
    (hFixed : ∀ j, j < t →
      lam * ‖candidate (j + 1) ω - populationIterate V lam (j + 1)‖ ^ 2 +
        ‖projCondExpOp V (candidate (j + 1) ω - populationIterate V lam (j + 1))‖ ^ 2 ≤
      (loss ω (candidate (j + 1) ω) + lam * primalEmpDistanceSq V P sample split n ω
          (candidate (j + 1) ω) (populationIterate V lam j)) -
        (loss ω (populationIterate V lam (j + 1)) + lam * primalEmpDistanceSq V P sample split n ω
          (populationIterate V lam (j + 1)) (populationIterate V lam j)) +
        K * (δ * ‖candidate (j + 1) ω - populationIterate V lam (j + 1)‖ + δ ^ 2))
    (hNorm : ∀ j, j ≤ t →
      Real.sqrt (primalEmpDistanceSq V P sample split n ω (candidate j ω)
        (populationIterate V lam j)) ≤ K * (‖candidate j ω - populationIterate V lam j‖ + δ)) :
    let C := 64 * K ^ 4 + 24 * K ^ 2 + 4 * K + 1
    ∀ j, 1 ≤ j → j ≤ t →
      lam * ‖candidate j ω - populationIterate V lam j‖ ^ 2 +
          ‖projCondExpOp V (candidate j ω - populationIterate V lam j)‖ ^ 2 ≤
        iterRdivStabilityCoefficients C j * δ ^ 2 / lam ∧
      ‖candidate j ω - populationIterate V lam j‖ ^ 2 ≤
        iterRdivStabilityCoefficients C j * δ ^ 2 / lam ^ 2 := by
  apply iter_rdiv_stability_from_energy V K δ lam t
    (fun j => candidate j ω - populationIterate V lam j) hK hδ hlam
  · simp only [hEst.1 ω, populationIterate, sub_self]
  · intro j hj
    have hOpt := (hEst.2 (j + 1) (by omega) (by omega) ω).2
      _ (hStar (j + 1) (by omega) (by omega))
    simp only [Nat.add_sub_cancel] at hOpt
    exact iter_rdiv_one_step_of_fixed_center V P sample split n ω K δ lam
      (loss ω) _ _ _ _ hK hδ hlam.1 hOpt (hFixed j hj)
        (hNorm (j + 1) (by omega)) (hNorm j (by omega))

end Papers.TsAdaptiveEstimationInference

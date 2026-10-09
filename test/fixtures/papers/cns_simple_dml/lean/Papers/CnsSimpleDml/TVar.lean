module
public import Papers.CnsSimpleDml.Helpers.Variance

/-!
Finite-sample variance-estimator bound including every fold’s conditional learning errors.
-/

public section


set_option linter.style.longLine false

-- Retain the existing proof scripts while keeping scaffold diagnostics focused.
set_option linter.deprecated false
set_option linter.unusedVariables false

noncomputable section

namespace Papers.CnsSimpleDml

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal Topology
attribute [local instance] Classical.propDecidable

variable (P : DMLPopulation) (n L : ℕ) (fold : FoldAssignment n L)
  (gHat : GammaFits P n L) (aHat : AlphaFits P n L)
  (Qbar q sigmabar alphabar alphabarP eps sigma : ℝ)
  (nu : Measure (Sample P n)) (Rreading Preading : Fin L → Sample P n → ℝ)

/-- For [the first sequence](hyp:x) and [the second sequence](hyp:y), [the absolute average of their products
is bounded by the product of their root-mean-square averages](goal).
@node: fullAverage_cauchy_schwarz -/
lemma fullAverage_cauchy_schwarz (x y : Fin n → ℝ) :
    |fullAverage n (fun i => x i * y i)| ≤
      Real.sqrt (fullAverage n (fun i => x i ^ 2)) *
        Real.sqrt (fullAverage n (fun i => y i ^ 2)) := by
  have hx : 0 ≤ fullAverage n (fun i => x i ^ 2) := by
    unfold fullAverage
    positivity
  have hy : 0 ≤ fullAverage n (fun i => y i ^ 2) := by
    unfold fullAverage
    positivity
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x y
  have hscaled := mul_le_mul_of_nonneg_left hcs
    (sq_nonneg ((n : ℝ)⁻¹))
  have hsq : (fullAverage n (fun i => x i * y i)) ^ 2 ≤
      fullAverage n (fun i => x i ^ 2) * fullAverage n (fun i => y i ^ 2) := by
    simpa only [fullAverage, mul_pow, pow_two, Finset.sum_filter, mul_assoc,
      mul_left_comm, mul_comm] using hscaled
  have hxroot := Real.sq_sqrt hx
  have hyroot := Real.sq_sqrt hy
  have hprod : (Real.sqrt (fullAverage n (fun i => x i ^ 2)) *
      Real.sqrt (fullAverage n (fun i => y i ^ 2))) ^ 2 =
      fullAverage n (fun i => x i ^ 2) * fullAverage n (fun i => y i ^ 2) := by
    rw [mul_pow, hxroot, hyroot]
  have habs := sq_abs (fullAverage n (fun i => x i * y i))
  nlinarith [Real.sqrt_nonneg (fullAverage n (fun i => x i ^ 2)),
    Real.sqrt_nonneg (fullAverage n (fun i => y i ^ 2)),
    mul_nonneg (Real.sqrt_nonneg (fullAverage n (fun i => x i ^ 2)))
      (Real.sqrt_nonneg (fullAverage n (fun i => y i ^ 2))),
    abs_nonneg (fullAverage n (fun i => x i * y i))]

/-- If [the reference scale is nonnegative](hyp:hs), [the average squared discrepancy is at most its allowance](hyp:hd),
and [the reference empirical second moment is close to that scale squared](hyp:hf), then [the empirical second moment
of the first sequence obeys the stated perturbation bound](goal).
@node: empirical_variance_perturbation -/
lemma empirical_variance_perturbation (x y : Fin n → ℝ) (s d f : ℝ)
    (hs : 0 ≤ s)
    (hd : fullAverage n (fun i => (x i - y i) ^ 2) ≤ d)
    (hf : |fullAverage n (fun i => y i ^ 2) - s ^ 2| ≤ f) :
    |fullAverage n (fun i => x i ^ 2) - s ^ 2| ≤
      d + 2 * Real.sqrt d * (Real.sqrt f + s) + f := by
  let D := fullAverage n (fun i => (x i - y i) ^ 2)
  let B := fullAverage n (fun i => y i ^ 2)
  let C := fullAverage n (fun i => (x i - y i) * y i)
  have hD : 0 ≤ D := by dsimp [D, fullAverage]; positivity
  have hB : 0 ≤ B := by dsimp [B, fullAverage]; positivity
  have hd0 : 0 ≤ d := hD.trans hd
  have hf0 : 0 ≤ f := (abs_nonneg _).trans hf
  have hexpand : fullAverage n (fun i => x i ^ 2) - s ^ 2 =
      D + 2 * C + (B - s ^ 2) := by
    have hpoint : (fun i => x i ^ 2) =
        (fun i => (x i - y i) ^ 2 + 2 * ((x i - y i) * y i) + y i ^ 2) := by
      funext i
      ring
    rw [hpoint]
    simp only [D, B, C, fullAverage, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  have hC : |C| ≤ Real.sqrt D * Real.sqrt B :=
    fullAverage_cauchy_schwarz n (fun i => x i - y i) y
  have hBbound : B ≤ f + s ^ 2 := by
    have := (abs_le.mp hf).2
    dsimp [B]
    linarith
  have hrootB : Real.sqrt B ≤ Real.sqrt f + s := by
    have hr := Real.sq_sqrt hB
    have hfr := Real.sq_sqrt hf0
    nlinarith [Real.sqrt_nonneg B, Real.sqrt_nonneg f]
  have hrootD : Real.sqrt D ≤ Real.sqrt d := Real.sqrt_le_sqrt hd
  have hcross : |C| ≤ Real.sqrt d * (Real.sqrt f + s) :=
    hC.trans (mul_le_mul hrootD hrootB (Real.sqrt_nonneg B) (Real.sqrt_nonneg d))
  rw [hexpand]
  calc
    |D + 2 * C + (B - s ^ 2)| ≤ |D| + |2 * C| + |B - s ^ 2| :=
      by
        have h1 := abs_add_le (D + 2 * C) (B - s ^ 2)
        have h2 := abs_add_le D (2 * C)
        linarith
    _ ≤ d + 2 * (Real.sqrt d * (Real.sqrt f + s)) + f := by
      rw [abs_of_nonneg hD, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact add_le_add (add_le_add hd (mul_le_mul_of_nonneg_left hcross (by norm_num))) hf
    _ = _ := by ring

/-- For [the sample](hyp:s), [the DML variance estimator equals the average squared fitted score](goal).
@node: dmlVarianceEstimator_eq_fullAverage -/
lemma dmlVarianceEstimator_eq_fullAverage (s : Sample P n) :
    dmlVarianceEstimator P n L fold gHat aHat s =
      fullAverage n (fun i => scoreHat P n L fold gHat aHat s i ^ 2) := by
  unfold dmlVarianceEstimator fullAverage scoreHat
  congr 1
  have hsum := Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ) (t := Finset.univ) (g := fold)
    (fun i _ => Finset.mem_univ (fold i))
    (fun i => (fittedSummand P n L gHat aHat (fold i) s i -
      empiricalDmlFormula P n L fold gHat aHat s) ^ 2)
  dsimp [foldIndices]
  convert hsum using 1
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro i hi
  rw [(Finset.mem_filter.mp hi).2]

/-- If [the confidence-interval reading](hyp:h_interval_reading), [the population model](hyp:hmodel), [training-only fits](hyp:htraining),
[functional linearity](hyp:h_cont_linearity), [mean-square continuity](hyp:h_cont_mean_square), [the estimated-representer bound](hyp:h_var_estimated_representer_bound),
[the noise bound](hyp:h_var_noise), [a finite fourth oracle-score moment](hyp:h_other_half_zeta), [the oracle-score reading](hyp:h_oracle_reading),
[pointwise linearity](hyp:h_pointwise_linearity), [foldwise conditional independence](hyp:h_resid_fold_iid), [training-measurable nuisances](hyp:h_resid_training_fixed),
[exact identification](hyp:h_inverse_exact_identification), [the exact-identification reading](hyp:h_pin_11), [the noise-bound reading](hyp:h_pin_15),
[the IID reading](hyp:h_pin_32), [the training-measurability reading](hyp:h_pin_33), [the inverse-MSE reading](hyp:h_pin_48),
[reference-nuisance membership](hyp:hgamma0), [equal folds](hyp:hequal), and [an admissible error probability](hyp:heps) hold,
[the variance estimator stays within the displayed finite-sample error bound with probability at least `1 - eps`](goal).
-/
-- @node: thm:var
theorem variance_estimator_bound
    (h_interval_reading : ConfidenceIntervalClosedReading P n L fold gHat aHat)
    (hmodel : PopulationModelDomain P)
    (htraining : TrainingOnlyFits P n L fold gHat aHat)
    (h_cont_linearity : FunctionalLinear P)
    (h_cont_mean_square : MeanSquareContinuous P Qbar q)
    (h_var_estimated_representer_bound : VarEstRepresenterBound P n L aHat alphabarP)
    (h_var_noise : VarNoiseBound P sigmabar)
    (h_other_half_zeta : OracleFourthMomentFinite P)
    (h_oracle_reading : OracleScoreOutcomeReading P)
    (h_pointwise_linearity : PointwiseLinear P)
    (h_resid_fold_iid : FoldwiseIIDGivenTraining P n L fold)
    (h_resid_training_fixed : TrainingMeasurableNuisances P n L fold gHat aHat)
    (h_inverse_exact_identification : ExactIdentification P)
    (h_pin_11 : ExactIdentificationReading P)
    (h_pin_15 : VarNoiseBound P sigmabar)
    (h_pin_32 : FoldwiseIIDGivenTraining P n L fold)
    (h_pin_33 : TrainingMeasurableNuisancesReading P n L fold gHat aHat)
    (h_pin_48 : InverseMSEReading P n L aHat Preading)
    (hgamma0 : GammaZeroMem P)
    (hequal : EqualFolds n L fold) (heps : EpsilonPrimeInUnit eps) :
  1 - eps ≤ ((sampleLaw P n) {s |
  |dmlVarianceEstimator P n L fold gHat aHat s - oracleSigma P ^ 2| ≤
    deltaPrime P n L fold gHat aHat Qbar q sigmabar alphabarP eps s +
    2 * Real.sqrt (deltaPrime P n L fold gHat aHat Qbar q sigmabar alphabarP eps s) *
      (Real.sqrt (deltaDoublePrime P n eps) + oracleSigma P) + deltaDoublePrime P n eps}).toReal := by
  let A : Set (Sample P n) := {s |
    fullAverage n (fun i => (scoreHat P n L fold gHat aHat s i - scoreOracle P n s i) ^ 2) ≤
      deltaPrime P n L fold gHat aHat Qbar q sigmabar alphabarP eps s}
  let B : Set (Sample P n) := {s |
    |fullAverage n (fun i => scoreOracle P n s i ^ 2) - oracleSigma P ^ 2| ≤
      deltaDoublePrime P n eps}
  have hA : 1 - eps / 2 ≤ ((sampleLaw P n) A).toReal :=
    score_sq_error_bound P n L fold gHat aHat Qbar q sigmabar alphabarP eps
      hmodel htraining h_cont_linearity h_cont_mean_square
      (resid2_mean_bound_of_second_moment P sigmabar hgamma0 h_var_noise)
      h_var_estimated_representer_bound h_pointwise_linearity h_resid_fold_iid
      h_resid_training_fixed h_inverse_exact_identification h_var_noise h_pin_11 h_pin_32 h_pin_33
      (resid2_mean_bound_of_second_moment P sigmabar hgamma0 h_pin_15) hgamma0 hequal heps
  have hB : 1 - eps / 2 ≤ ((sampleLaw P n) B).toReal :=
    oracle_second_moment_concentration P n eps (sampleLaw P n)
      h_other_half_zeta h_oracle_reading rfl hequal.1 heps.1
  have hmB : NullMeasurableSet B (sampleLaw P n) := by
    have hcoord (i : Fin n) : AEStronglyMeasurable
        (fun s : Sample P n => scoreOracle P n s i) (sampleLaw P n) := by
      first
      | fun_prop
      | exact h_other_half_zeta.1.comp_quasiMeasurePreserving
          (measurePreserving_eval (fun _ : Fin n => P.pr) i).quasiMeasurePreserving
    have havg : AEStronglyMeasurable
        (fun s : Sample P n => fullAverage n (fun i => scoreOracle P n s i ^ 2))
        (sampleLaw P n) := by
      unfold fullAverage
      fun_prop
    simpa only [Real.norm_eq_abs, Pi.sub_apply, B] using
      (havg.sub (aestronglyMeasurable_const (b := oracleSigma P ^ 2))).norm.nullMeasurableSet_le
        (aestronglyMeasurable_const (b := deltaDoublePrime P n eps))
  have hinter : 1 - eps ≤ ((sampleLaw P n) (A ∩ B)).toReal := by
    have hid := measure_union_add_inter₀ A hmB
    have hidR := congrArg ENNReal.toReal hid
    simp only [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at hidR
    have hu : ((sampleLaw P n) (A ∪ B)).toReal ≤ 1 := by
      simpa only [ENNReal.toReal_one] using
        ENNReal.toReal_mono (by norm_num : (1 : ℝ≥0∞) ≠ ⊤)
          (prob_le_one (μ := sampleLaw P n) (s := A ∪ B))
    linarith
  have hsub : A ∩ B ⊆ {s |
      |dmlVarianceEstimator P n L fold gHat aHat s - oracleSigma P ^ 2| ≤
        deltaPrime P n L fold gHat aHat Qbar q sigmabar alphabarP eps s +
        2 * Real.sqrt (deltaPrime P n L fold gHat aHat Qbar q sigmabar alphabarP eps s) *
          (Real.sqrt (deltaDoublePrime P n eps) + oracleSigma P) + deltaDoublePrime P n eps} := by
    intro s hs
    rw [Set.mem_setOf_eq, dmlVarianceEstimator_eq_fullAverage P n L fold gHat aHat]
    exact empirical_variance_perturbation n
      (scoreHat P n L fold gHat aHat s) (scoreOracle P n s) (oracleSigma P)
      (deltaPrime P n L fold gHat aHat Qbar q sigmabar alphabarP eps s)
      (deltaDoublePrime P n eps) (Real.sqrt_nonneg _) hs.1 hs.2
  exact hinter.trans (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub))

end Papers.CnsSimpleDml

module
public import Papers.TsAdaptiveEstimationInference.Helpers.IterTRAEProcessTransfer
/-! Finite-sample extension of the fixed-center clipped scalar concentration step.
The first two sample sizes use only the deterministic envelope and calibrated floor.
-/
public section
set_option linter.style.longLine false
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory
variable {W X Z : Type*} [MeasurableSpace W] [MeasurableSpace X]
  [MeasurableSpace Z]

/-- If [the first function takes values between zero and one](hyp:hf),
[the second does too](hyp:hg), and [the sample size is positive](hyp:hn),
[the absolute difference between the sample average and population mean of their
difference is at most two](goal). -/
-- @node: iter_trae_bounded_increment_deviation
lemma iter_trae_bounded_increment_deviation (law : Measure W) [IsProbabilityMeasure law]
    (f g : W → ℝ) (hf : ∀ w, f w ∈ Set.Icc (0 : ℝ) 1)
    (hg : ∀ w, g w ∈ Set.Icc (0 : ℝ) 1)
    (n : ℕ) (hn : 0 < n) (x : Fin n → W) :
    |(n : ℝ)⁻¹ * (∑ i, (f (x i) - g (x i))) - ∫ w, f w - g w ∂law| ≤ 2 := by
  have hb (w : W) : |f w - g w| ≤ 1 := by
    obtain ⟨hf0, hf1⟩ := hf w
    obtain ⟨hg0, hg1⟩ := hg w
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hemp : |(n : ℝ)⁻¹ * (∑ i, (f (x i) - g (x i)))| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ)⁻¹)]
    calc
      _ ≤ (n : ℝ)⁻¹ * ∑ i : Fin n, |f (x i) - g (x i)| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
      _ ≤ (n : ℝ)⁻¹ * ∑ _i : Fin n, (1 : ℝ) := by
        gcongr with i
        exact hb (x i)
      _ = 1 := by simp [ne_of_gt hn]
  have hint : |∫ w, f w - g w ∂law| ≤ 1 := by
    simpa [Real.norm_eq_abs] using
      norm_integral_le_of_norm_le_const (μ := law) (f := fun w => f w - g w)
        (C := 1) (Filter.Eventually.of_forall
          (fun w => by simpa only [Real.norm_eq_abs] using hb w))
  exact (abs_sub _ _).trans (by linarith)

/-- If [the sample size is positive](hyp:hn), [it is less than three](hyp:hsmall),
and [the radius is at least the inverse square root of the sample size](hyp:hfloor),
then [four times the squared radius is at least two](goal). -/
-- @node: iter_trae_small_sample_floor
lemma iter_trae_small_sample_floor (n : ℕ) (hn : 0 < n) (hsmall : n < 3)
    (r : ℝ) (hfloor : (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ r) :
    2 ≤ 4 * r ^ 2 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hinv : ((n : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = (n : ℝ)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
    norm_num [Real.rpow_neg_one]
  have hsquare := pow_le_pow_left₀ (Real.rpow_nonneg hnpos.le _) hfloor 2
  rw [hinv] at hsquare
  have hn2 : (n : ℝ) ≤ 2 := by exact_mod_cast (show n ≤ 2 by omega)
  have hinv2 : (1 / 2 : ℝ) ≤ (n : ℝ)⁻¹ := by
    rw [inv_eq_one_div]
    exact (div_le_div_iff₀ (by norm_num) hnpos).mpr (by linarith)
  linarith

/-- For [a positive sample size](hyp:hn), [the square root of the sum of the
log-log sample-size term and the log inverse-confidence term, divided by sample
size, is bounded by the paper's confidence floor](goal). -/
-- @node: iter_trae_scalar_source_floor_le
lemma iter_trae_scalar_source_floor_le (n : ℕ) (hn : 0 < n) (ζ : ℝ) :
    Real.sqrt ((Real.log (Real.log n) + Real.log (1 / ζ)) / n) ≤
      confidenceFloor n ζ := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : Real.log (Real.log n) ≤ Real.log (Real.log (Real.exp 1 * n)) := by
    by_cases hn1 : n = 1
    · subst n
      simp
    · have hn1' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
      have hexp : 1 ≤ Real.exp 1 := by
        simp
      exact Real.log_le_log (Real.log_pos hn1')
        (Real.log_le_log hnpos (by nlinarith))
  exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (by linarith only [hlog]) hnpos.le)

variable (V : IVWorld W X Z)

/-- Given [a positive multiplier for the scalar confidence floor](hyp:hcfloor)
and [a complexity curve bounding the required critical radii](hyp:hComplexity),
[there is a multiplier at least one such that every calibrated accuracy curve,
at every positive sample size with allocation between zero and one, simultaneously
dominates the scalar floor at half allocation and the inverse-square-root floor,
and bounds the primal critical radius](goal). -/
-- @node: iter_trae_scalar_radius_at_allocation
lemma iter_trae_scalar_radius_at_allocation
    (cfloor : ℝ) (hcfloor : 0 < cfloor) (tildeδ : ℕ → ℝ → ℝ)
    (hComplexity : TRAECriticalRadiusBound V tildeδ) :
    ∃ K ≥ (1 : ℝ), ∀ (δ allocation : ℕ → ℝ),
      TRAEScaleCalibration δ tildeδ allocation →
      ∀ n : ℕ, 0 < n → allocation n ∈ Set.Ioo (0 : ℝ) 1 →
      cfloor * Real.sqrt
        ((Real.log (Real.log n) + Real.log (1 / (allocation n / 2))) / n) ≤ K * δ n ∧
      (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ K * δ n ∧
      IsCriticalRadiusBound V.law (starClass (primalObservationClass V)) n (K * δ n) := by
  obtain ⟨L, hL, hradius⟩ := trae_radius_uniform_at_allocation V tildeδ hComplexity
  let K := max 1 (cfloor * L)
  have hK : 1 ≤ K := le_max_left _ _
  refine ⟨K, hK, ?_⟩
  intro δ allocation hScale n hn halloc
  obtain ⟨_, _, _, _, hprimal, _⟩ := hComplexity.choose_spec.2 n hn (allocation n) halloc
  have htilde : tildeδ n (allocation n) ≤ δ n :=
    (le_max_left _ _).trans (hScale.1 n hn)
  have hd : 0 ≤ δ n := hprimal.1.le.trans htilde
  have hdK : δ n ≤ K * δ n := by nlinarith only [hK, hd]
  have hf := (hradius δ allocation hScale n hn halloc).1
  refine ⟨?_, ((le_max_right _ _).trans (hScale.1 n hn)).trans hdK,
    criticalRadiusBound_mono _ _ _ _ _ hprimal (htilde.trans hdK)⟩
  calc
    _ ≤ cfloor * confidenceFloor n (allocation n / 2) :=
      mul_le_mul_of_nonneg_left (iter_trae_scalar_source_floor_le n hn _) hcfloor.le
    _ ≤ cfloor * (L * δ n) := mul_le_mul_of_nonneg_left hf hcfloor.le
    _ ≤ K * δ n := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) hd

/-- Assuming [fixed-center squared-loss concentration](hyp:hSource),
[for every bounded model with a common null-set envelope and positive floor
coefficient, one positive constant controls clipped squared-loss increments at
all positive sample sizes: whenever the radius dominates both confidence and
inverse-square-root floors and bounds the primal critical radius, each admissible
population iterate and adjacent population center with measurable localized
processes admits a measurable event of probability at least one minus the
confidence allocation on which every candidate's deviation is bounded by the
constant times radius times its population L2 distance from the iterate plus
the squared radius](goal). -/
-- @node: iter_trae_fixed_center_concentration_all_sizes
lemma iter_trae_fixed_center_concentration_all_sizes
    (hSource : IterTRAEFixedCenterSquaredLossConcentration V) :
  ∀ B cfloor : ℝ, TRAEBoundedness V B → TRAECommonNullSetBoundedness V B → 0 < cfloor →
  ∃ C > 0, ∀ n : ℕ, 0 < n → ∀ ζ ∈ Set.Ioo (0 : ℝ) 1,
  ∀ r : ℝ, cfloor * Real.sqrt
    ((Real.log (Real.log n) + Real.log (1 / ζ)) / n) ≤ r →
  0 < r → (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ r →
  IsCriticalRadiusBound V.law (starClass (primalObservationClass V)) n r →
  ∀ (ρ c b β : ℝ) (δ : ℕ → ℝ) (t j : ℕ),
  GridDomain ρ → 0 < c → 2 ≤ b → 0 < β → 1 ≤ j → j ≤ t →
  let radius := c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1))
  (∃ k ≤ terminalIndex ρ n, gridValue ρ k ≤ radius) →
  ∀ lam ∈ regGrid ρ n, oraclePoint ρ n radius ≤ lam → lam ≤ 2 → 0 < lam →
  populationIterate V lam j ∈ V.H →
  ∀ center : V.Hbar.toSubmodule,
  (center = populationIterate V lam (j - 1) ∨ center = populationIterate V lam j) →
  (∀ᵐ w ∂V.law, |primalVersion V center (V.xOf w)| ≤ B) →
  LocalizedSupremaMeasurableAt V.law
    (iterTraeScalarClass (primalObservationClass V))
    (fun w => fun _ : Fin 1 => primalVersion V (populationIterate V lam j) (V.xOf w))
    (fun w v => (v 0 - primalVersion V center (V.xOf w)) ^ 2) n →
  ∃ E : Set (Fin n → W), MeasurableSet E ∧
    1 - ζ ≤ (Measure.pi (fun _ : Fin n => V.law)).real E ∧
    ∀ x ∈ E, ∀ h ∈ V.H,
      |(n : ℝ)⁻¹ * (∑ i,
          (iterTraeSourceSquare B (fun w => primalVersion V center (V.xOf w))
            (x i) (fun _ => primalVersion V h (V.xOf (x i))) -
          iterTraeSourceSquare B (fun w => primalVersion V center (V.xOf w))
            (x i) (fun _ => primalVersion V (populationIterate V lam j) (V.xOf (x i))))) -
        ∫ w, (iterTraeSourceSquare B (fun w => primalVersion V center (V.xOf w))
          w (fun _ => primalVersion V h (V.xOf w)) -
          iterTraeSourceSquare B (fun w => primalVersion V center (V.xOf w))
            w (fun _ => primalVersion V (populationIterate V lam j) (V.xOf w))) ∂V.law| ≤
      C * (r * inputL2Norm V.law (fun w =>
        primalVersion V h (V.xOf w) -
          primalVersion V (populationIterate V lam j) (V.xOf w)) + r ^ 2) := by
  intro B cfloor hBound hCommon hcfloor
  obtain ⟨C, hC, hSource⟩ :=
    iter_trae_fixed_center_concentration_of_raw_processes V hSource B cfloor hBound hCommon hcfloor
  refine ⟨C + 4, by linarith, ?_⟩
  intro n hn ζ hζ r hfloor hr hsmallfloor hcritical ρ c b β δ t j hρ hc hb hβ hj hjt
  dsimp only
  intro hDefined lam hlam hlow hu hp hmem center hcenter hEnvelope hMeas
  by_cases hlarge : 3 ≤ n
  · obtain ⟨E, hE, hpE, hgood⟩ := hSource n hlarge ζ hζ r hfloor hr hcritical
      ρ c b β δ t j hρ hc hb hβ hj hjt hDefined lam hlam hlow hu hp hmem center
      hcenter hEnvelope hMeas
    refine ⟨E, hE, hpE, ?_⟩
    intro x hx h hh
    exact (hgood x hx h hh).trans
      (mul_le_mul_of_nonneg_right (by linarith : C ≤ C + 4) (by unfold inputL2Norm; positivity))
  · refine ⟨Set.univ, MeasurableSet.univ, by simp; linarith [hζ.1], ?_⟩
    intro x hx h hh
    have hclip (h : V.Hbar.toSubmodule) (w : W) :
        iterTraeSourceSquare B (fun w => primalVersion V center (V.xOf w))
          w (fun _ => primalVersion V h (V.xOf w)) ∈ Set.Icc (0 : ℝ) 1 :=
      iter_trae_clipped_distance_mem_Icc V (2 * max 1 B) h center w
    have hdet := iter_trae_bounded_increment_deviation V.law
      (fun w => iterTraeSourceSquare B (fun w => primalVersion V center (V.xOf w))
        w (fun _ => primalVersion V h (V.xOf w)))
      (fun w => iterTraeSourceSquare B (fun w => primalVersion V center (V.xOf w))
        w (fun _ => primalVersion V (populationIterate V lam j) (V.xOf w)))
      (hclip h) (hclip (populationIterate V lam j)) n hn x
    apply hdet.trans
    have hfinite := iter_trae_small_sample_floor n hn (by omega) r hsmallfloor
    have hnorm : 0 ≤ inputL2Norm V.law (fun w =>
        primalVersion V h (V.xOf w) -
          primalVersion V (populationIterate V lam j) (V.xOf w)) := by
      unfold inputL2Norm
      positivity
    nlinarith [mul_nonneg hr.le hnorm, mul_nonneg hC.le (sq_nonneg r)]

/-- Under [fixed-center squared-loss concentration](hyp:hSource),
[model boundedness](hyp:hBound), [a common null-set envelope](hyp:hCommon), and
[the critical-radius complexity bound](hyp:hComplexity), [one positive constant
works for every calibrated accuracy and allocation curve: at every positive
sample size with valid allocation, each admissible grid penalty, population
iterate, and adjacent bounded population center with measurable localized
processes admits an event of probability at least one minus half the allocation,
uniformly bounding clipped squared-loss increment deviations by the constant
times accuracy times the candidate's distance from the iterate plus squared
accuracy](goal). -/
-- @node: iter_trae_fixed_center_calibrated_at_allocation
lemma iter_trae_fixed_center_calibrated_at_allocation
    (hSource : IterTRAEFixedCenterSquaredLossConcentration V)
    (B : ℝ) (tildeδ : ℕ → ℝ → ℝ)
    (hBound : TRAEBoundedness V B) (hCommon : TRAECommonNullSetBoundedness V B)
    (hComplexity : TRAECriticalRadiusBound V tildeδ) :
    ∃ C > 0, ∀ (accuracy allocation : ℕ → ℝ),
      TRAEScaleCalibration accuracy tildeδ allocation →
      ∀ n : ℕ, 0 < n → allocation n ∈ Set.Ioo (0 : ℝ) 1 →
  ∀ (ρ c b β : ℝ) (δ : ℕ → ℝ) (t j : ℕ),
  GridDomain ρ → 0 < c → 2 ≤ b → 0 < β → 1 ≤ j → j ≤ t →
  let radius := c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1))
  (∃ k ≤ terminalIndex ρ n, gridValue ρ k ≤ radius) →
  ∀ lam ∈ regGrid ρ n, oraclePoint ρ n radius ≤ lam → lam ≤ 2 → 0 < lam →
  populationIterate V lam j ∈ V.H →
  ∀ center : V.Hbar.toSubmodule,
  (center = populationIterate V lam (j - 1) ∨ center = populationIterate V lam j) →
  (∀ᵐ w ∂V.law, |primalVersion V center (V.xOf w)| ≤ B) →
  LocalizedSupremaMeasurableAt V.law
    (iterTraeScalarClass (primalObservationClass V))
    (fun w => fun _ : Fin 1 => primalVersion V (populationIterate V lam j) (V.xOf w))
    (fun w v => (v 0 - primalVersion V center (V.xOf w)) ^ 2) n →
  ∃ E : Set (Fin n → W), MeasurableSet E ∧
    1 - allocation n / 2 ≤ (Measure.pi (fun _ : Fin n => V.law)).real E ∧
    ∀ x ∈ E, ∀ h ∈ V.H,
      |(n : ℝ)⁻¹ * (∑ i,
          (iterTraeSourceSquare B (fun w => primalVersion V center (V.xOf w))
            (x i) (fun _ => primalVersion V h (V.xOf (x i))) -
          iterTraeSourceSquare B (fun w => primalVersion V center (V.xOf w))
            (x i) (fun _ => primalVersion V (populationIterate V lam j) (V.xOf (x i))))) -
        ∫ w, (iterTraeSourceSquare B (fun w => primalVersion V center (V.xOf w))
          w (fun _ => primalVersion V h (V.xOf w)) -
          iterTraeSourceSquare B (fun w => primalVersion V center (V.xOf w))
            w (fun _ => primalVersion V (populationIterate V lam j) (V.xOf w))) ∂V.law| ≤
      C * (accuracy n * ‖h - populationIterate V lam j‖ + accuracy n ^ 2) := by
  obtain ⟨cfloor, hcfloor, hcritical⟩ := hComplexity
  have hComplexity : TRAECriticalRadiusBound V tildeδ := ⟨cfloor, hcfloor, hcritical⟩
  obtain ⟨K, hK, hradius⟩ :=
    iter_trae_scalar_radius_at_allocation V cfloor hcfloor tildeδ hComplexity
  obtain ⟨Cs, hCs, hsource⟩ :=
    iter_trae_fixed_center_concentration_all_sizes V hSource B cfloor hBound hCommon hcfloor
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  refine ⟨Cs * (K ^ 2 + K), by positivity, ?_⟩
  intro accuracy allocation hScale n hn halloc ρ c b β δ t j hρ hc hb hβ hj hjt
  dsimp only
  intro hDefined lam hlam hlow hu hp hmem center hcenter hEnvelope hMeas
  obtain ⟨hfloor, hsmall, hcrit⟩ := hradius accuracy allocation hScale n hn halloc
  have hα : 0 < accuracy n := by
    have hi : 0 < (n : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos (by positivity) _
    exact hi.trans_le ((le_max_right _ _).trans (hScale.1 n hn))
  have hhalf : allocation n / 2 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [halloc.1, halloc.2]
  obtain ⟨E, hE, hpE, hgood⟩ := hsource n hn (allocation n / 2) hhalf
    (K * accuracy n) hfloor (mul_pos hKpos hα) hsmall hcrit
    ρ c b β δ t j hρ hc hb hβ hj hjt hDefined lam hlam hlow hu hp hmem center
    hcenter hEnvelope hMeas
  refine ⟨E, hE, hpE, ?_⟩
  intro x hx h hh
  have he := hgood x hx h hh
  have hnorm : inputL2Norm V.law (fun w => primalVersion V h (V.xOf w) -
      primalVersion V (populationIterate V lam j) (V.xOf w)) =
      ‖h - populationIterate V lam j‖ := by
    rw [inputL2Norm, trae_primal_difference_energy, Real.sqrt_sq (norm_nonneg _)]
  rw [hnorm] at he
  apply he.trans
  have hk : K ≤ K ^ 2 + K := by nlinarith only [sq_nonneg K]
  have hk2 : K ^ 2 ≤ K ^ 2 + K := by linarith only [hKpos]
  calc
    _ = Cs * (K * (accuracy n * ‖h - populationIterate V lam j‖) +
        K ^ 2 * accuracy n ^ 2) := by ring
    _ ≤ Cs * ((K ^ 2 + K) * (accuracy n * ‖h - populationIterate V lam j‖) +
        (K ^ 2 + K) * accuracy n ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hCs.le
      exact add_le_add (mul_le_mul_of_nonneg_right hk (by positivity))
        (mul_le_mul_of_nonneg_right hk2 (sq_nonneg _))
    _ = _ := by ring

end Papers.TsAdaptiveEstimationInference

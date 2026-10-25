module
public import Papers.TsAdaptiveEstimationInference.Helpers.IterRDIVFitting
/-! Joint fixed-center fitting and empirical-norm events for iterative RDIV.
The two source applications retain their individual radius and confidence checks.
Their intersection spends half the confidence budget, leaving the remaining
budget for the preliminary and calibration events in the stability proof. -/
public section
set_option linter.style.longLine false
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory
variable {𝒲 X Z Ω : Type*} [MeasurableSpace 𝒲] [MeasurableSpace X]
  [MeasurableSpace Z] [MeasurableSpace Ω]
  (V : IVWorld 𝒲 X Z)

/-- Under [fixed-center concentration](hyp:hFix), [squared-loss
concentration](hyp:hSq), [the RDIV model](hyp:hIV), [density
realizability](hyp:hDensity), [density bounds](hyp:hBounds), [bounded
outcomes](hyp:hY), and [bounded hypotheses](hyp:hHyp), [one comparison constant
at least one and four positive tail constants can be fixed before sampling so
that admissible selections, versions, grid scope, population centers, critical
radii, and both logarithmic tail conditions yield a measurable event of
probability at least one minus half the failure probability, uniformly
controlling centered fitting deviations by K times radius times population
distance plus K times squared radius, and empirical distances by K times
the sum of population distance and radius, over the entire iteration-grid segment](goal).

Both recursive fitting comparisons hold on one measurable event. All five
constants are chosen before the sampling experiment, horizon and source data.
The probability estimate adds the two quarter budgets without independence. -/
-- @node: iter_rdiv_joint_fitting_iteration_grid_event
lemma iter_rdiv_joint_fitting_iteration_grid_event
    (hFix : IterRDIVFixedCenterLocalizedConcentration (Ω := Ω) V)
    (hSq : IterRDIVSquaredLossLocalizedConcentration (Ω := Ω) V)
    (mu : Measure X) (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (support : Set (X × Z)) (B c₀ CG : ℝ)
    (hIV : RDIVSetting V mu g₀) (hDensity : DensityRealizable V mu G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hY : OutcomeBounded V B) (hHyp : HypothesisClassBounded V support B) :
    ∃ K, 1 ≤ K ∧ ∃ cf₁ > 0, ∃ cf₂ > 0, ∃ cs₁ > 0, ∃ cs₂ > 0,
    ∀ (P : Measure Ω) (_hProbability : IsProbabilityMeasure P)
      (sample : AnalysisSample V P) (split : SampleSplit)
      (gHat : ℕ → Ω → X → Z → ℝ) (ρ ξ : ℝ),
    MLEMaximizerSelected V P sample split G gHat →
    RDIVClassesMeasurable V P sample split mu G g₀ gHat →
    IterRDIVFixedCenterSupremumVersion V P sample split mu gHat ρ →
    ∀ (n t : ℕ) (r : ℝ) (segment : Set ℝ) (sourceRadius : ℝ)
      (_hSourceScope : gridValue ρ (terminalIndex ρ n) ≤ sourceRadius ∧
        ∀ lam ∈ regGrid ρ n, lam ∈ segment → oraclePoint ρ n sourceRadius ≤ lam), 0 < n → 1 ≤ t →
    ξ ∈ Set.Ioo (0 : ℝ) 1 → 0 < r →
    1 < 2 * cf₂ * n →
    8 * Real.log (41 * Real.log (2 * cf₂ * n)) / (cf₂ * n) ≤ r ^ 2 →
    Real.log (8 * cf₁ / iterGridConfidence ρ ξ n t) ≤ cf₂ * n * r ^ 2 / 8 →
    1 < 2 * cs₂ * n →
    4 * Real.log (41 * Real.log (2 * cs₂ * n)) / (cs₂ * n) ≤ r ^ 2 →
    Real.log (8 * cs₁ / iterGridConfidence ρ ξ n t) ≤ cs₂ * n * r ^ 2 / 4 →
    IsCriticalRadiusBound (V.law.map V.xOf) (primalVersion V '' V.H) n r →
    (∀ g ∈ G, IsCriticalRadiusBound (V.law.map V.zOf)
      (densityOperator mu g '' (primalVersion V '' V.H)) n r) →
    (∀ lam ∈ regGrid ρ n, lam ∈ segment → lam ∈ Set.Ioc (0 : ℝ) 2) →
    (∀ lam ∈ regGrid ρ n, lam ∈ segment → ∀ j, 1 ≤ j → j ≤ t →
      populationIterate V lam j ∈ V.H) →
    ∃ E : Set Ω, MeasurableSet E ∧ 1 - ξ / 2 ≤ P.real E ∧
      ∀ ω ∈ E, ∀ lam ∈ regGrid ρ n, lam ∈ segment → ∀ j, 1 ≤ j → j ≤ t →
        ∀ h ∈ V.H,
        |blockAverage V P sample (split.fit n)
            (fun w => iterRdivFixedCenterLoss V mu (gHat n ω) lam j h w -
              iterRdivFixedCenterLoss V mu (gHat n ω) lam j
                (populationIterate V lam j) w) ω -
          ∫ w, iterRdivFixedCenterLoss V mu (gHat n ω) lam j h w -
            iterRdivFixedCenterLoss V mu (gHat n ω) lam j
              (populationIterate V lam j) w ∂V.law| ≤
          K * (r * ‖h - populationIterate V lam j‖ + r ^ 2) ∧
        Real.sqrt (primalEmpDistanceSq V P sample split n ω h
          (populationIterate V lam j)) ≤ K * (‖h - populationIterate V lam j‖ + r) := by
  obtain ⟨Cf, hCf, cf₁, hcf₁, cf₂, hcf₂, hf⟩ :=
    iter_rdiv_fixed_center_iteration_grid_event V hFix mu G g₀ support B c₀ CG
      hIV hDensity hBounds hY hHyp
  obtain ⟨Cs, hCs, cs₁, hcs₁, cs₂, hcs₂, hs⟩ :=
    iter_rdiv_squared_loss_iteration_grid_event V hSq mu G g₀ support B c₀ CG
      hIV hDensity hBounds hHyp
  let K := max Cf (Cs + 1)
  have hK : 1 ≤ K := le_trans (by linarith) (le_max_right _ _)
  refine ⟨K, hK, cf₁, hcf₁, cf₂, hcf₂, cs₁, hcs₁, cs₂, hcs₂, ?_⟩
  intro P hProbability sample split gHat ρ ξ hMLE hMeas hVersion n t r segment sourceRadius hSourceScope
    hn ht hξ hr hflarge hffloor hflog hslarge hsfloor hslog hradX hradZ hdom hstar
  let : IsProbabilityMeasure P := hProbability
  obtain ⟨Ef, hEf, hpEf, hgoodf⟩ := hf P hProbability sample split gHat ρ ξ
    hMLE hMeas hVersion n t r segment sourceRadius hSourceScope hn ht hξ hr hflarge hffloor hflog
    hradX hradZ hdom hstar
  obtain ⟨Es, hEs, hpEs, hgoods⟩ := hs P hProbability sample split gHat ρ ξ
    hMeas hVersion n t r segment sourceRadius hSourceScope hn ht hξ.1 hr hslarge hsfloor hslog hradX hdom hstar
  refine ⟨Ef ∩ Es, hEf.inter hEs, ?_, ?_⟩
  · have hbad : P.real (Ef ∩ Es)ᶜ ≤ P.real Efᶜ + P.real Esᶜ := by
      rw [Set.compl_inter]
      exact measureReal_union_le _ _
    linarith only [hbad, hpEf, hpEs, probReal_add_probReal_compl (μ := P) hEf,
      probReal_add_probReal_compl (μ := P) hEs,
      probReal_add_probReal_compl (μ := P) (hEf.inter hEs)]
  · intro ω hω lam hl hseg j hj hjt h hh
    constructor
    · exact (hgoodf ω hω.1 lam hl hseg j hj hjt h hh).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    · exact (hgoods ω hω.2 lam hl hseg j hj hjt h hh).2.trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))

/-- If [K is nonnegative](hyp:hK), [the radius is nonnegative](hyp:hr), [the
candidates form zero-initialized empirical iterates](hyp:hEst), and [every
hypothesis satisfies the empirical-distance envelope at every positive
iteration through the horizon](hyp:hNorm), then [the empirical-distance
envelope holds for every candidate iterate through the horizon, including
iteration zero](goal).

The norm comparison applies to every positive fitted iterate by empirical
minimizer membership. At index zero the empirical error is identically zero,
so no concentration process or class membership for zero is required. -/
-- @node: iter_rdiv_iterate_empirical_norms
lemma iter_rdiv_iterate_empirical_norms
    (P : Measure Ω) (sample : AnalysisSample V P) (split : SampleSplit)
    (n t : ℕ) (ω : Ω) (K r lam : ℝ)
    (loss : Ω → V.Hbar.toSubmodule → ℝ)
    (candidate : ℕ → Ω → V.Hbar.toSubmodule)
    (hK : 0 ≤ K) (hr : 0 ≤ r)
    (hEst : IsEmpiricalIterate V loss (primalEmpDistanceSq V P sample split n)
      candidate t lam)
    (hNorm : ∀ j, 1 ≤ j → j ≤ t → ∀ h ∈ V.H,
      Real.sqrt (primalEmpDistanceSq V P sample split n ω h
        (populationIterate V lam j)) ≤ K * (‖h - populationIterate V lam j‖ + r)) :
    ∀ j, j ≤ t →
      Real.sqrt (primalEmpDistanceSq V P sample split n ω (candidate j ω)
        (populationIterate V lam j)) ≤
        K * (‖candidate j ω - populationIterate V lam j‖ + r) := by
  intro j hjt
  by_cases hj : j = 0
  · subst j
    simp only [hEst.1 ω, populationIterate, primalEmpDistanceSq, blockAverage, sub_self,
      zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, mul_zero,
      Real.sqrt_zero, norm_zero, zero_add]
    exact mul_nonneg hK hr
  · exact hNorm j (by omega) hjt _ (hEst.2 j (by omega) hjt ω).1

/-- Assume [the RDIV model](hyp:hIV), [the range condition](hyp:hRange),
[density realizability](hyp:hDensity), [density bounds](hyp:hBounds), [bounded
hypotheses](hyp:hHyp), [bounded outcomes](hyp:hY), [a class-valued selected
density](hyp:hg), [nonnegative rate constant](hyp:hC), [nonnegative
radius](hyp:hr), and [positive penalty](hyp:hlam). If [integrated squared
Hellinger error is at most C times squared radius](hyp:hRate), [the candidate
belongs to the hypothesis class](hyp:hh), [the next population iterate belongs
to that class](hyp:hstar), and [their centered fitting loss deviation is at
most K times radius times distance plus K times squared radius](hyp:hDeviation),
then [the penalty-weighted squared error plus projected squared error is at
most the empirical objective difference centered at the previous population
iterate plus the same localized remainder with constant D + K, where D equals
4 B √(2(CG/c₀ + 1)) √C + 4 B √C](goal).

The density comparison and the actual fitting increment yield the
fixed-center energy inequality. Population curvature and the noise cancellation
are proved locally; neither is part of a source concentration interface. -/
-- @node: iter_rdiv_fixed_center_energy_of_deviation
lemma iter_rdiv_fixed_center_energy_of_deviation
    (P : Measure Ω) (sample : AnalysisSample V P) (split : SampleSplit)
    (mu : Measure X) (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (gHat : ℕ → Ω → X → Z → ℝ) (support : Set (X × Z))
    (B c₀ CG C K r lam : ℝ) (n j : ℕ) (ω : Ω)
    (hIV : RDIVSetting V mu g₀) (hRange : RangeCondition V)
    (hDensity : DensityRealizable V mu G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hHyp : HypothesisClassBounded V support B) (hY : OutcomeBounded V B)
    (hg : gHat n ω ∈ G) (hC : 0 ≤ C) (hr : 0 ≤ r) (hlam : 0 < lam)
    (hRate : (∫ z, hellingerSqDensity mu (fun x => gHat n ω x z) (fun x => g₀ x z)
      ∂V.law.map V.zOf) ≤ C * r ^ 2)
    (h : V.Hbar.toSubmodule) (hh : h ∈ V.H)
    (hstar : populationIterate V lam (j + 1) ∈ V.H)
    (hDeviation :
      |blockAverage V P sample (split.fit n)
          (fun w => iterRdivFixedCenterLoss V mu (gHat n ω) lam (j + 1) h w -
            iterRdivFixedCenterLoss V mu (gHat n ω) lam (j + 1)
              (populationIterate V lam (j + 1)) w) ω -
        ∫ w, iterRdivFixedCenterLoss V mu (gHat n ω) lam (j + 1) h w -
          iterRdivFixedCenterLoss V mu (gHat n ω) lam (j + 1)
            (populationIterate V lam (j + 1)) w ∂V.law| ≤
        K * (r * ‖h - populationIterate V lam (j + 1)‖ + r ^ 2)) :
    let D := 4 * B * (Real.sqrt (2 * (CG / c₀ + 1)) * Real.sqrt C) +
      2 * (2 * B * Real.sqrt C)
    lam * ‖h - populationIterate V lam (j + 1)‖ ^ 2 +
        ‖projCondExpOp V (h - populationIterate V lam (j + 1))‖ ^ 2 ≤
      (rdivEmpiricalLoss V P sample split mu gHat n ω h +
        lam * primalEmpDistanceSq V P sample split n ω h (populationIterate V lam j)) -
      (rdivEmpiricalLoss V P sample split mu gHat n ω (populationIterate V lam (j + 1)) +
        lam * primalEmpDistanceSq V P sample split n ω
          (populationIterate V lam (j + 1)) (populationIterate V lam j)) +
      (D + K) * (r * ‖h - populationIterate V lam (j + 1)‖ + r ^ 2) := by
  dsimp only
  let D := 4 * B * (Real.sqrt (2 * (CG / c₀ + 1)) * Real.sqrt C) +
    2 * (2 * B * Real.sqrt C)
  have hD : 0 ≤ D := by dsimp [D]; positivity [hY.1]
  have hp := (abs_le.mp (rdiv_conditional_population_loss_rate V mu G g₀ gHat
    support B c₀ CG C r n ω hIV hDensity hBounds hHyp hY hg hC hr hRate
    h hh _ hstar)).1
  rw [iter_rdiv_fixed_center_deviation_eq_risks V P sample split mu G g₀ gHat
    support B c₀ CG n (j + 1) ω ω lam hIV hDensity hBounds hHyp hY hg
    h (populationIterate V lam (j + 1)) hh hstar] at hDeviation
  have hf := (abs_le.mp hDeviation).2
  simp only [Nat.add_sub_cancel] at hf
  have hpop (v : V.Hbar.toSubmodule) : rdivPopulationLoss V v =
      outcomeNoise V + ‖projCondExpOp V v - momentRepresenter V‖ ^ 2 := by
    rw [rdivPopulationLoss_eq V mu g₀ hIV hRange B hY,
      map_sub, (minNormSolution_spec V hRange).1]
  rw [hpop h, hpop (populationIterate V lam (j + 1))] at hp
  have hcurv := iter_rdiv_population_curvature V lam hlam j h
  have hrest : 0 ≤ D * r ^ 2 := mul_nonneg hD (sq_nonneg r)
  change - (D * r * ‖h - populationIterate V lam (j + 1)‖) ≤ _ at hp
  simp only [rdivEmpiricalLoss, estimatedOperator] at hf ⊢
  dsimp only [D] at hp hrest
  nlinarith only [hp, hf, hcurv, hrest]

/-- Under [the RDIV model](hyp:hIV), [the range condition](hyp:hRange),
[density realizability](hyp:hDensity), [density bounds](hyp:hBounds), [bounded
hypotheses](hyp:hHyp), and [bounded outcomes](hyp:hY), assume [the selected
density belongs to its class](hyp:hg), [C is nonnegative](hyp:hC), [K is at
least one](hyp:hK), [the radius is nonnegative](hyp:hr), [the penalty lies in
$(0,2]$](hyp:hlam), and [integrated squared Hellinger error is at most C times
squared radius](hyp:hRate). If [the candidates are empirical iterates](hyp:hEst),
[the positive population iterates belong to the class](hyp:hStar), and [the
centered fitting-deviation and empirical-distance comparisons hold uniformly
through the horizon](hyp:hComparisons), then [each positive iterate has energy
and squared-error bounds equal to its recursive stability coefficient times
squared radius divided by the penalty and squared penalty, respectively, with
base constant 64 L⁴ + 24 L² + 4 L + 1, where L is the larger of K and
K + 4 B √(2(CG/c₀ + 1)) √C + 4 B √C](goal).

Assemble recursive stability for the supplied empirical iterates from the
actual fixed-center fitting deviations and density error. The norm comparison
includes the zero iterate locally; no recursive energy bound is assumed.
The coefficient depends only on the fixed density and concentration constants. -/
-- @node: iter_rdiv_stability_of_density_and_deviations
lemma iter_rdiv_stability_of_density_and_deviations
    (P : Measure Ω) (sample : AnalysisSample V P) (split : SampleSplit)
    (mu : Measure X) (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (gHat : ℕ → Ω → X → Z → ℝ) (support : Set (X × Z))
    (B c₀ CG C K r lam : ℝ) (n t : ℕ) (ω : Ω)
    (candidate : ℕ → Ω → V.Hbar.toSubmodule)
    (hIV : RDIVSetting V mu g₀) (hRange : RangeCondition V)
    (hDensity : DensityRealizable V mu G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hHyp : HypothesisClassBounded V support B) (hY : OutcomeBounded V B)
    (hg : gHat n ω ∈ G) (hC : 0 ≤ C) (hK : 1 ≤ K) (hr : 0 ≤ r)
    (hlam : lam ∈ Set.Ioc (0 : ℝ) 2)
    (hRate : (∫ z, hellingerSqDensity mu (fun x => gHat n ω x z) (fun x => g₀ x z)
      ∂V.law.map V.zOf) ≤ C * r ^ 2)
    (hEst : IsEmpiricalIterate V (rdivEmpiricalLoss V P sample split mu gHat n)
      (primalEmpDistanceSq V P sample split n) candidate t lam)
    (hStar : ∀ j, 1 ≤ j → j ≤ t → populationIterate V lam j ∈ V.H)
    (hComparisons : ∀ j, 1 ≤ j → j ≤ t → ∀ h ∈ V.H,
      |blockAverage V P sample (split.fit n)
          (fun w => iterRdivFixedCenterLoss V mu (gHat n ω) lam j h w -
            iterRdivFixedCenterLoss V mu (gHat n ω) lam j
              (populationIterate V lam j) w) ω -
        ∫ w, iterRdivFixedCenterLoss V mu (gHat n ω) lam j h w -
          iterRdivFixedCenterLoss V mu (gHat n ω) lam j
            (populationIterate V lam j) w ∂V.law| ≤
        K * (r * ‖h - populationIterate V lam j‖ + r ^ 2) ∧
      Real.sqrt (primalEmpDistanceSq V P sample split n ω h
        (populationIterate V lam j)) ≤ K * (‖h - populationIterate V lam j‖ + r)) :
    let D := 4 * B * (Real.sqrt (2 * (CG / c₀ + 1)) * Real.sqrt C) +
      2 * (2 * B * Real.sqrt C)
    let L := max K (D + K)
    let A := 64 * L ^ 4 + 24 * L ^ 2 + 4 * L + 1
    ∀ j, 1 ≤ j → j ≤ t →
      lam * ‖candidate j ω - populationIterate V lam j‖ ^ 2 +
          ‖projCondExpOp V (candidate j ω - populationIterate V lam j)‖ ^ 2 ≤
        iterRdivStabilityCoefficients A j * r ^ 2 / lam ∧
      ‖candidate j ω - populationIterate V lam j‖ ^ 2 ≤
        iterRdivStabilityCoefficients A j * r ^ 2 / lam ^ 2 := by
  let D := 4 * B * (Real.sqrt (2 * (CG / c₀ + 1)) * Real.sqrt C) +
    2 * (2 * B * Real.sqrt C)
  let L := max K (D + K)
  have hKL : K ≤ L := le_max_left _ _
  have hL : 1 ≤ L := hK.trans hKL
  apply iter_rdiv_stability_of_fixed_center V P sample split n t ω L r lam
    (rdivEmpiricalLoss V P sample split mu gHat n) candidate hL hr hlam hEst hStar
  · intro j hj
    have hmem := (hEst.2 (j + 1) (by omega) (by omega) ω).1
    have hdev := (hComparisons (j + 1) (by omega) (by omega) _ hmem).1
    have henergy := iter_rdiv_fixed_center_energy_of_deviation V P sample split
      mu G g₀ gHat support B c₀ CG C K r lam n j ω hIV hRange hDensity hBounds
      hHyp hY hg hC hr hlam.1 hRate _ hmem (hStar _ (by omega) (by omega)) hdev
    apply henergy.trans
    apply add_le_add le_rfl
    exact mul_le_mul_of_nonneg_right (le_max_right K (D + K)) (by positivity)
  · apply iter_rdiv_iterate_empirical_norms V P sample split n t ω L r lam
      (rdivEmpiricalLoss V P sample split mu gHat n) candidate (by linarith) hr hEst
    intro j hj hjt h hh
    exact ((hComparisons j hj hjt h hh).2).trans
      (mul_le_mul_of_nonneg_right hKL (by positivity))

end Papers.TsAdaptiveEstimationInference

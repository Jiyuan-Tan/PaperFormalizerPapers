module
public import Papers.TsAdaptiveEstimationInference.Helpers.TRAEVectorCoordinates
/-! Uniform TRAE deviations and confidence-radius conversions. -/
public section
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.style.longLine false
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory Filter
open scoped Topology
variable {𝒲 𝒳 𝒵 Ω : Type*} [MeasurableSpace 𝒲] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒵] [MeasurableSpace Ω]
  (V : IVWorld 𝒲 𝒳 𝒵) (P : Measure Ω) [IsProbabilityMeasure P]
  (sample : AnalysisSample V P) (split : SampleSplit)
variable (ρ ξ B β : ℝ) (w₀ : V.Hbar.toSubmodule)
  (δ ν baseδ baseν : ℕ → ℝ) (δG δH δr tildeδ : ℕ → ℝ → ℝ)
  (κδ κν required c₀ CG Cm : ℝ) (κ₀ : ℝ → ℝ → ℝ → ℝ → ℝ × ℝ)
  (mu : Measure 𝒳) (G : Set (𝒳 → 𝒵 → ℝ)) (g₀ : 𝒳 → 𝒵 → ℝ)
  (gHat : ℕ → Ω → 𝒳 → 𝒵 → ℝ) (rHat : ℕ → Ω → 𝒵 → ℝ)
  (support : Set (𝒳 × 𝒵)) (candidate : ℕ → ℝ → Ω → V.Hbar.toSubmodule)
  (iter : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule)
  (a b c : ℝ) (t : ℕ)
-- @node: confidenceFloor_half_le
/-- For [a positive sample size](hyp:hn) and [a confidence level strictly
between zero and one](hyp:hζ), [halving the confidence level increases the
confidence floor by at most the reciprocal square root of sample size](goal). -/
lemma confidenceFloor_half_le (n : ℕ) (ζ : ℝ) (hn : 0 < n)
    (hζ : ζ ∈ Set.Ioo (0 : ℝ) 1) :
    confidenceFloor n (ζ / 2) ≤ confidenceFloor n ζ + (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hζpos := hζ.1
  let d := (n : ℝ) ^ (-(1 / 2 : ℝ))
  have hd : 0 ≤ d := Real.rpow_nonneg hnpos.le _
  have hd2 : d ^ 2 = 1 / (n : ℝ) := by
    dsimp [d]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
    norm_num [Real.rpow_neg_one]
  have hlog : Real.log (1 / (ζ / 2)) = Real.log (1 / ζ) + Real.log 2 := by
    rw [show 1 / (ζ / 2) = (1 / ζ) * 2 by ring,
      Real.log_mul (by positivity) (by norm_num)]
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hf : (Real.log (Real.log (Real.exp 1 * n)) + Real.log (1 / ζ)) / n ≤
      confidenceFloor n ζ ^ 2 := by
    unfold confidenceFloor
    rw [Real.sq_sqrt']
    exact le_max_left _ _
  have ht : Real.log 2 / (n : ℝ) ≤ d ^ 2 := by
    rw [hd2]
    exact div_le_div_of_nonneg_right hlog2 hnpos.le
  change Real.sqrt _ ≤ confidenceFloor n ζ + d
  apply Real.sqrt_le_iff.mpr
  constructor
  · exact add_nonneg (Real.sqrt_nonneg _) hd
  · rw [hlog, ← add_assoc, add_div]
    have hnonneg : 0 ≤ confidenceFloor n ζ := Real.sqrt_nonneg _
    nlinarith [mul_nonneg hnonneg hd]

/-- Given [critical-radius bounds supplied by the radius curve](hyp:hComplexity),
[one positive inflation factor, fixed before the accuracy curve and confidence
allocation, makes the inflated calibrated accuracy dominate the half-allocation
confidence floor and serve as a critical-radius bound for the star-shaped
product, moment-image and critic observation classes at every positive sample
size with valid allocated confidence](goal). -/
-- @node: trae_radius_uniform_at_allocation
lemma trae_radius_uniform_at_allocation
    (tildeδ : ℕ → ℝ → ℝ)
    (hComplexity : TRAECriticalRadiusBound V tildeδ) :
    ∃ K > 0, ∀ (δ allocation : ℕ → ℝ),
      TRAEScaleCalibration δ tildeδ allocation →
      ∀ n : ℕ, 0 < n → allocation n ∈ Set.Ioo (0 : ℝ) 1 →
      confidenceFloor n (allocation n / 2) ≤ K * δ n ∧
      IsCriticalRadiusBound V.law (starClass (productObservationClass V)) n (K * δ n) ∧
      IsCriticalRadiusBound V.law (starClass (momentImageClass V)) n (K * δ n) ∧
      IsCriticalRadiusBound V.law (starClass (criticObservationClass V)) n (K * δ n) := by
  obtain ⟨c, hc, hcomplex⟩ := hComplexity
  let K := max 1 (c⁻¹ + 1)
  have hK1 : 1 ≤ K := le_max_left _ _
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one hK1
  refine ⟨K, hK, ?_⟩
  intro δ allocation hScale n hn hValid
  obtain ⟨hf, hp, hm, hq, _⟩ := hcomplex n hn (allocation n) hValid
  have htilde : tildeδ n (allocation n) ≤ δ n :=
    (le_max_left _ _).trans (hScale.1 n hn)
  have hd : 0 ≤ δ n := hp.1.le.trans htilde
  have hdK : δ n ≤ K * δ n := by nlinarith only [hK1, hd]
  have hr : tildeδ n (allocation n) ≤ K * δ n := htilde.trans hdK
  refine ⟨?_, criticalRadiusBound_mono _ _ _ _ _ hp hr,
    criticalRadiusBound_mono _ _ _ _ _ hm hr,
    criticalRadiusBound_mono _ _ _ _ _ hq hr⟩
  have hfloor : confidenceFloor n (allocation n) ≤ c⁻¹ * δ n := by
    apply (mul_le_mul_iff_right₀ hc).mp
    have hmul : c * (c⁻¹ * δ n) = δ n := by field_simp
    rw [hmul]
    exact hf.trans htilde
  have hinv : (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ δ n :=
    (le_max_right _ _).trans (hScale.1 n hn)
  calc
    confidenceFloor n (allocation n / 2) ≤
        confidenceFloor n (allocation n) + (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
      confidenceFloor_half_le n (allocation n) hn hValid
    _ ≤ (c⁻¹ + 1) * δ n := by linarith
    _ ≤ K * δ n := mul_le_mul_of_nonneg_right (le_max_right _ _) hd

-- @node: trae_radius_at_allocation
/-- If [the radius curve supplies the critical-radius bounds](hyp:hComplexity)
and [the accuracy curve is scale-calibrated to that radius curve and confidence
allocation](hyp:hScale), then [one positive inflation factor makes the inflated
accuracy dominate the half-allocation confidence floor and bound the critical
radii of the star-shaped product, moment-image and critic observation classes
at every positive sample size with valid allocated confidence](goal). -/
lemma trae_radius_at_allocation
    (δ : ℕ → ℝ) (tildeδ : ℕ → ℝ → ℝ)
    (allocation : ℕ → ℝ)
    (hComplexity : TRAECriticalRadiusBound V tildeδ)
    (hScale : TRAEScaleCalibration δ tildeδ allocation) :
    ∃ K > 0, ∀ n : ℕ, 0 < n → allocation n ∈ Set.Ioo (0 : ℝ) 1 →
      confidenceFloor n (allocation n / 2) ≤ K * δ n ∧
      IsCriticalRadiusBound V.law (starClass (productObservationClass V)) n (K * δ n) ∧
      IsCriticalRadiusBound V.law (starClass (momentImageClass V)) n (K * δ n) ∧
      IsCriticalRadiusBound V.law (starClass (criticObservationClass V)) n (K * δ n) := by
  obtain ⟨K, hK, hRadius⟩ := trae_radius_uniform_at_allocation V tildeδ hComplexity
  exact ⟨K, hK, hRadius δ allocation hScale⟩

open ProbabilityTheory

/-- Assume [localized concentration for the adversarial loss](hyp:hBennett),
[the range condition](hyp:hRange), [admissibility of projected residuals as
critics](hyp:hClose), [mean-square continuity](hyp:hMSC), [bounded model classes
with envelope B](hyp:hBound), [boundedness outside one common null set](hyp:hCommon),
and [the critical-radius bounds](hyp:hComplexity). Then [one positive constant,
fixed before the accuracy and allocation curves, ensures that scale calibration
gives, at each positive sample size with valid allocated confidence, a measurable
event for independent observations of probability at least one minus half the
allocation, on which every clipped adversarial loss has absolute empirical
deviation at most that constant times three times squared accuracy plus three
times accuracy times the sum of its three population coordinate norms](goal).

The source
carrier gives the absolute clipped-coordinate comparison, with constants before
all accuracy and allocation sequences. The fixed subdivision is proved by
critical-radius/floor inflation and the recorded calibration,
including its n^(-1/2) floor at n=1. It assumes no comparison of an arbitrary
curve at different confidence levels, and supplies no variational conclusion.
The sum-of-three-coordinates normalization is also a local instantiation step.
A forward confidence evaluation suffices: on (0,1/2), use the original radius
curve at twice the new confidence and adjoin the n^(-1/2) floor; on [1/2,1),
use its original valid-confidence value, and set irrelevant invalid-confidence
values to zero. For a supplied allocation, halve its valid entries and send
invalid entries to an invalid sentinel. The resulting calibration follows by
fixed inflation of delta, without a global validity premise or any comparison
between arbitrary values of the original curve. All of these reductions are
proved locally, without additional assumed source content. -/
-- @node: trae_clipped_calibrated_at_allocation
lemma trae_clipped_calibrated_at_allocation
    (hBennett : TRAELocalizedConcentration V)
    (B : ℝ) (tildeδ : ℕ → ℝ → ℝ)
    (hRange : RangeCondition V) (hClose : ClosenessCondition V)
    (hMSC : MeanSquareContinuity V) (hBound : TRAEBoundedness V B) (hCommon : TRAECommonNullSetBoundedness V B)
    (hComplexity : TRAECriticalRadiusBound V tildeδ) :
    ∃ C > 0, ∀ (δ allocation : ℕ → ℝ),
      TRAEScaleCalibration δ tildeδ allocation →
      ∀ n : ℕ, 0 < n → allocation n ∈ Set.Ioo (0 : ℝ) 1 →
      ∃ E : Set (Fin n → 𝒲), MeasurableSet E ∧
        1 - allocation n / 2 ≤ (Measure.pi (fun _ : Fin n => V.law)).real E ∧
        ∀ x ∈ E, ∀ h ∈ V.H, ∀ f ∈ V.F,
          |(n : ℝ)⁻¹ * (∑ i, traeClippedLoss B (x i)
              ![V.m f (x i), primalVersion V h (V.xOf (x i)) *
                dualVersion V f (V.zOf (x i)), dualVersion V f (V.zOf (x i))]) -
            (∫ w, traeClippedLoss B w ![V.m f w,
              primalVersion V h (V.xOf w) * dualVersion V f (V.zOf w),
              dualVersion V f (V.zOf w)] ∂V.law)| ≤
            C * (3 * δ n ^ 2 + 3 * δ n *
              (inputL2Norm V.law (V.m f) +
                inputL2Norm V.law (fun w => primalVersion V h (V.xOf w) *
                  dualVersion V f (V.zOf w)) +
                inputL2Norm V.law (fun w => dualVersion V f (V.zOf w)))) := by
  classical
  -- Reindex valid small confidence levels forward, so halving an allocation
  -- evaluates the original complexity curve at exactly its original argument.
  let forward : ℝ → ℝ := fun ζ => if ζ < 1 / 2 then 2 * ζ else ζ
  let radius : ℕ → ℝ → ℝ := fun n ζ =>
    if ζ ∈ Set.Ioo (0 : ℝ) 1 then
      max (tildeδ n (forward ζ)) (confidenceFloor n ζ) else 0
  have hforward (ζ : ℝ) (hζ : ζ ∈ Set.Ioo (0 : ℝ) 1) :
      forward ζ ∈ Set.Ioo (0 : ℝ) 1 := by
    dsimp [forward]
    split <;> constructor <;> linarith [hζ.1, hζ.2]
  have hcomplex : TRAECriticalRadiusBound V radius := by
    refine ⟨1, zero_lt_one, ?_⟩
    intro n hn ζ hζ
    obtain ⟨_, hp, hm, hf, hh, hdiff⟩ := hComplexity.choose_spec.2 n hn
      (forward ζ) (hforward ζ hζ)
    have hmono : tildeδ n (forward ζ) ≤ radius n ζ := by
      dsimp [radius]
      rw [if_pos hζ]
      exact le_max_left _ _
    refine ⟨?_, criticalRadiusBound_mono _ _ _ _ _ hp hmono,
      criticalRadiusBound_mono _ _ _ _ _ hm hmono,
      criticalRadiusBound_mono _ _ _ _ _ hf hmono,
      criticalRadiusBound_mono _ _ _ _ _ hh hmono,
      criticalRadiusBound_mono _ _ _ _ _ hdiff hmono⟩
    simpa only [radius, if_pos hζ, one_mul] using
      (le_max_right (tildeδ n (forward ζ)) (confidenceFloor n ζ))
  obtain ⟨K, hK, hfloor⟩ := trae_radius_uniform_at_allocation V tildeδ hComplexity
  let M := K + 1
  have hM : 1 ≤ M := by dsimp [M]; linarith
  obtain ⟨D, hD, hdev⟩ := hBennett B radius hRange hClose hMSC hBound hCommon hcomplex
  refine ⟨D * (M ^ 2 + M), by positivity [show 0 < M by linarith], ?_⟩
  intro δ allocation hScale
  let allocated : ℕ → ℝ := fun n =>
    if allocation n ∈ Set.Ioo (0 : ℝ) 1 then allocation n / 2 else 1
  have hd (n : ℕ) (hn : 0 < n) : 0 ≤ δ n :=
    (Real.rpow_nonneg (by positivity) _).trans
      ((le_max_right _ _).trans (hScale.1 n hn))
  have hdM (n : ℕ) (hn : 0 < n) : δ n ≤ M * δ n := by
    nlinarith only [hd n hn, hM]
  have hcal : TRAEScaleCalibration (fun n => M * δ n) radius allocated := by
    constructor
    · intro n hn
      apply max_le
      · by_cases hv : allocation n ∈ Set.Ioo (0 : ℝ) 1
        · have hvhalf : allocation n / 2 ∈ Set.Ioo (0 : ℝ) 1 := by
            constructor <;> linarith [hv.1, hv.2]
          have hfwd : forward (allocation n / 2) = allocation n := by
            dsimp only [forward]
            rw [if_pos (by linarith [hv.2])]
            ring
          simp only [allocated, if_pos hv, radius, if_pos hvhalf, hfwd]
          apply max_le
          · exact ((le_max_left _ _).trans (hScale.1 n hn)).trans (hdM n hn)
          · exact ((hfloor δ allocation hScale n hn hv).1).trans
              (by dsimp [M]; nlinarith only [hd n hn])
        · simpa only [allocated, if_neg hv, radius,
            show ¬ (1 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 by simp, if_false] using
              (show 0 ≤ M * δ n by positivity [hd n hn, show 0 < M by linarith])
      · exact ((le_max_right _ _).trans (hScale.1 n hn)).trans (hdM n hn)
    · simpa using hScale.2.const_mul M
  intro n hn hv
  have hvhalf : allocated n ∈ Set.Ioo (0 : ℝ) 1 := by
    dsimp [allocated]
    rw [if_pos hv]
    constructor <;> linarith [hv.1, hv.2]
  obtain ⟨E, hE, hprob, he⟩ := hdev (fun n => M * δ n) allocated hcal n hn hvhalf
  refine ⟨E, hE, ?_, ?_⟩
  · simpa only [allocated, if_pos hv] using hprob
  · intro x hx h hh f hf
    have hbound := he x hx h hh f hf
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
      Matrix.cons_val_succ, add_zero, ← add_assoc] at hbound
    apply hbound.trans
    have hs : 0 ≤ inputL2Norm V.law (V.m f) +
        inputL2Norm V.law (fun w => primalVersion V h (V.xOf w) *
          dualVersion V f (V.zOf w)) +
        inputL2Norm V.law (fun w => dualVersion V f (V.zOf w)) := by
      unfold inputL2Norm
      positivity
    have hterm : 0 ≤ δ n * (inputL2Norm V.law (V.m f) +
        inputL2Norm V.law (fun w => primalVersion V h (V.xOf w) *
          dualVersion V f (V.zOf w)) +
        inputL2Norm V.law (fun w => dualVersion V f (V.zOf w))) := mul_nonneg (hd n hn) hs
    conv_rhs => rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hD.le
    have hM0 : 0 ≤ M := by linarith
    nlinarith only [mul_nonneg (sq_nonneg M) (sq_nonneg (δ n)),
      mul_nonneg hM0 (sq_nonneg (δ n)), mul_nonneg (sq_nonneg M) hterm,
      mul_nonneg hM0 hterm]

/-- Given [localized concentration for the adversarial loss](hyp:hBennett),
[bounded model classes with envelope B](hyp:hBound), [boundedness outside one
common null set](hyp:hCommon), [mean-square continuity](hyp:hMSC), and
[the critical-radius bounds](hyp:hComplexity), [one positive constant works
for every accuracy curve and confidence allocation satisfying the range,
closeness and scale calibration conditions: at every positive sample size with
valid allocated confidence, there is a measurable event of probability at least
one minus half the allocation on which the absolute difference between empirical
and population adversarial integrands is bounded by that constant times squared
accuracy plus accuracy times the critic norm, uniformly over hypotheses and
critics](goal).

Calibrated actual-integrand concentration uses the proved confidence
subdivision `trae_clipped_calibrated_at_allocation`. The common null hull,
iid transport, unclipping and critic-norm conversion below retain the same
paper function representatives and the same event. No arbitrary-radius
concentration theorem occurs in this dependency path. -/
lemma trae_calibrated_deviation_at_allocation
    (hBennett : TRAELocalizedConcentration V)
    (B : ℝ) (tildeδ : ℕ → ℝ → ℝ)
    (hBound : TRAEBoundedness V B) (hCommon : TRAECommonNullSetBoundedness V B) (hMSC : MeanSquareContinuity V)
    (hComplexity : TRAECriticalRadiusBound V tildeδ) :
    ∃ C > 0, ∀ (δ allocation : ℕ → ℝ),
      RangeCondition V → ClosenessCondition V →
      TRAEScaleCalibration δ tildeδ allocation →
      ∀ n : ℕ, 0 < n → allocation n ∈ Set.Ioo (0 : ℝ) 1 →
      ∃ E : Set Ω, MeasurableSet E ∧ 1 - allocation n / 2 ≤ P.real E ∧
        ∀ ω ∈ E, ∀ h ∈ V.H, ∀ f ∈ V.F,
          |blockAverage V P sample (split.fit n) (traeIntegrand V h f) ω -
            (∫ w, traeIntegrand V h f w ∂V.law)| ≤
              C * (δ n ^ 2 + δ n * ‖f‖) := by
  classical
  by_cases hSetup : RangeCondition V ∧ ClosenessCondition V
  · obtain ⟨D, hD, hevent⟩ := trae_clipped_calibrated_at_allocation V hBennett
      B tildeδ hSetup.1 hSetup.2 hMSC hBound hCommon hComplexity
    obtain ⟨K, hK, hnorms⟩ := trae_vector_input_norms V B hBound hCommon hMSC
    refine ⟨3 * D * (K + 1), by positivity, ?_⟩
    intro δ allocation hRange hClose hScale n hn hValid
    obtain ⟨E, hE, hprob, hdev⟩ := hevent δ allocation hScale n hn hValid
    let Q : Measure (Fin n → 𝒲) := Measure.pi (fun _ => V.law)
    let S : Set (Fin n → 𝒲) := {x | ∀ i, ∀ f ∈ V.F,
      |dualVersion V f (V.zOf (x i))| ≤ B}
    have hS : ∀ᵐ x ∂Q, x ∈ S := by
      apply ae_all_iff.mpr
      intro i
      exact (measurePreserving_eval (fun _ : Fin n => V.law) i).quasiMeasurePreserving.ae
        (hCommon.mono (fun _ hw => hw.2.1))
    obtain ⟨N, hSN, hN, hQN⟩ := exists_measurable_superset_of_null (ae_iff.mp hS)
    let F := E \ N
    have hFmeas : MeasurableSet F := hE.diff hN
    have hFprob : 1 - allocation n / 2 ≤ Q.real F := by
      have heq : Q F = Q E := measure_sdiff_null' (measure_mono_null Set.inter_subset_right hQN)
      change 1 - allocation n / 2 ≤ (Q F).toReal
      rw [heq]
      exact hprob
    let tuple : Ω → Fin n → 𝒲 := fun ω i =>
      sample.Z ((Finset.equivFinOfCardEq (split.card_fit n)).symm i) ω
    have htuple : Measurable tuple := by
      fun_prop
    have hlaw : P.map tuple = Q := by
      have hinj : Function.Injective (fun i : Fin n =>
          ((Finset.equivFinOfCardEq (split.card_fit n)).symm i : ℕ)) :=
        Subtype.val_injective.comp (Equiv.injective _)
      have hiid := sample.indep.precomp hinj
      have he := (iIndepFun_iff_map_fun_eq_pi_map
        (fun i : Fin n => (sample.meas _).aemeasurable)).mp hiid
      change P.map tuple = _ at he
      rw [he]
      simp_rw [sample.map_eq]
      rfl
    refine ⟨tuple ⁻¹' F, hFmeas.preimage htuple, ?_, ?_⟩
    · change 1 - allocation n / 2 ≤ (P (tuple ⁻¹' F)).toReal
      rw [← Measure.map_apply htuple hFmeas, hlaw]
      exact hFprob
    · intro ω hω h hh f hff
      have hx : tuple ω ∈ E := hω.1
      have hs : tuple ω ∈ S := by
        by_contra hnS
        exact hω.2 (hSN hnS)
      have he := hdev (tuple ω) hx h hh f hff
      have hmean : (∫ w, traeClippedLoss B w ![V.m f w,
          primalVersion V h (V.xOf w) * dualVersion V f (V.zOf w),
          dualVersion V f (V.zOf w)] ∂V.law) = ∫ w, traeIntegrand V h f w ∂V.law := by
        apply integral_congr_ae
        filter_upwards [(hCommon.mono (fun _ hw => hw.2.1))] with w hw
        exact trae_clipped_loss_eq_integrand V B w h f (hw f hff)
      have hsum : (∑ i, traeClippedLoss B (tuple ω i) ![V.m f (tuple ω i),
          primalVersion V h (V.xOf (tuple ω i)) * dualVersion V f (V.zOf (tuple ω i)),
          dualVersion V f (V.zOf (tuple ω i))]) =
          ∑ i, traeIntegrand V h f (tuple ω i) := by
        apply Finset.sum_congr rfl
        intro i _
        exact trae_clipped_loss_eq_integrand V B _ h f (hs i f hff)
      rw [hmean, hsum] at he
      have havg : (n : ℝ)⁻¹ * ∑ i, traeIntegrand V h f (tuple ω i) =
          blockAverage V P sample (split.fit n) (traeIntegrand V h f) ω := by
        unfold blockAverage
        rw [split.card_fit]
        congr 1
        rw [← Finset.sum_coe_sort (split.fit n)]
        exact Equiv.sum_comp (Finset.equivFinOfCardEq (split.card_fit n)).symm
          (fun i : split.fit n => traeIntegrand V h f (sample.Z i ω))
      rw [havg] at he
      have hr : 0 ≤ δ n :=
        (show 0 ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) by positivity).trans
          ((le_max_right _ _).trans (hScale.1 n hn))
      have hb := mul_le_mul_of_nonneg_left (hnorms h hh f hff)
        (show 0 ≤ 3 * δ n by positivity)
      have hrr : 0 ≤ 3 * D * K * δ n ^ 2 := by positivity
      have hrf : 0 ≤ 3 * D * δ n * ‖f‖ := by positivity
      exact he.trans (by nlinarith only [mul_le_mul_of_nonneg_left hb hD.le, hrr, hrf])
  · refine ⟨1, zero_lt_one, ?_⟩
    intro δ allocation hRange hClose
    exact False.elim (hSetup ⟨hRange, hClose⟩)

/-- Given [localized concentration for the adversarial loss](hyp:hBennett),
[bounded model classes with envelope B](hyp:hBound), [boundedness outside one
common null set](hyp:hCommon), [mean-square continuity](hyp:hMSC), and
[the critical-radius bounds](hyp:hComplexity), [one positive constant works
for every accuracy curve and confidence allocation satisfying the range,
closeness and scale calibration conditions: at every positive sample size with
valid allocated confidence, a measurable event of probability at least one
minus one third of the allocation bounds the absolute empirical deviation of
every adversarial integrand by that constant times squared accuracy plus
accuracy times the critic norm](goal).

A quarter-budget specialization suffices for each of the three iterative
comparison families. The accuracy is inflated by a fixed constant; the original
complexity curve is evaluated forward only on its valid confidence domain.
Constants precede the requested accuracy and allocation. -/
lemma trae_calibrated_deviation_at_third_allocation
    (hBennett : TRAELocalizedConcentration V)
    (B : ℝ) (tildeδ : ℕ → ℝ → ℝ)
    (hBound : TRAEBoundedness V B) (hCommon : TRAECommonNullSetBoundedness V B) (hMSC : MeanSquareContinuity V)
    (hComplexity : TRAECriticalRadiusBound V tildeδ) :
    ∃ C > 0, ∀ (δ allocation : ℕ → ℝ),
      RangeCondition V → ClosenessCondition V →
      TRAEScaleCalibration δ tildeδ allocation →
      ∀ n : ℕ, 0 < n → allocation n ∈ Set.Ioo (0 : ℝ) 1 →
      ∃ E : Set Ω, MeasurableSet E ∧ 1 - allocation n / 3 ≤ P.real E ∧
        ∀ ω ∈ E, ∀ h ∈ V.H, ∀ f ∈ V.F,
          |blockAverage V P sample (split.fit n) (traeIntegrand V h f) ω -
            (∫ w, traeIntegrand V h f w ∂V.law)| ≤
              C * (δ n ^ 2 + δ n * ‖f‖) := by
  classical
  -- Reindex valid small confidence levels forward, so halving an allocation
  -- evaluates the original complexity curve at exactly its original argument.
  let forward : ℝ → ℝ := fun ζ => if ζ < 1 / 2 then 2 * ζ else ζ
  let radius : ℕ → ℝ → ℝ := fun n ζ =>
    if ζ ∈ Set.Ioo (0 : ℝ) 1 then
      max (tildeδ n (forward ζ)) (confidenceFloor n ζ) else 0
  have hforward (ζ : ℝ) (hζ : ζ ∈ Set.Ioo (0 : ℝ) 1) :
      forward ζ ∈ Set.Ioo (0 : ℝ) 1 := by
    dsimp [forward]
    split <;> constructor <;> linarith [hζ.1, hζ.2]
  have hcomplex : TRAECriticalRadiusBound V radius := by
    refine ⟨1, zero_lt_one, ?_⟩
    intro n hn ζ hζ
    obtain ⟨_, hp, hm, hf, hh, hdiff⟩ := hComplexity.choose_spec.2 n hn
      (forward ζ) (hforward ζ hζ)
    have hmono : tildeδ n (forward ζ) ≤ radius n ζ := by
      dsimp [radius]
      rw [if_pos hζ]
      exact le_max_left _ _
    refine ⟨?_, criticalRadiusBound_mono _ _ _ _ _ hp hmono,
      criticalRadiusBound_mono _ _ _ _ _ hm hmono,
      criticalRadiusBound_mono _ _ _ _ _ hf hmono,
      criticalRadiusBound_mono _ _ _ _ _ hh hmono,
      criticalRadiusBound_mono _ _ _ _ _ hdiff hmono⟩
    simpa only [radius, if_pos hζ, one_mul] using
      (le_max_right (tildeδ n (forward ζ)) (confidenceFloor n ζ))
  obtain ⟨K, hK, hfloor⟩ := trae_radius_uniform_at_allocation V tildeδ hComplexity
  let M := K + 1
  have hM : 1 ≤ M := by dsimp [M]; linarith
  obtain ⟨D, hD, hdev⟩ := trae_calibrated_deviation_at_allocation
    V P sample split hBennett B radius hBound hCommon hMSC hcomplex
  refine ⟨D * (M ^ 2 + M), by positivity [show 0 < M by linarith], ?_⟩
  intro δ allocation hRange hClose hScale
  let allocated : ℕ → ℝ := fun n =>
    if allocation n ∈ Set.Ioo (0 : ℝ) 1 then allocation n / 2 else 1
  have hd (n : ℕ) (hn : 0 < n) : 0 ≤ δ n :=
    (Real.rpow_nonneg (by positivity) _).trans
      ((le_max_right _ _).trans (hScale.1 n hn))
  have hdM (n : ℕ) (hn : 0 < n) : δ n ≤ M * δ n := by
    nlinarith only [hd n hn, hM]
  have hcal : TRAEScaleCalibration (fun n => M * δ n) radius allocated := by
    constructor
    · intro n hn
      apply max_le
      · by_cases hv : allocation n ∈ Set.Ioo (0 : ℝ) 1
        · have hvhalf : allocation n / 2 ∈ Set.Ioo (0 : ℝ) 1 := by
            constructor <;> linarith [hv.1, hv.2]
          have hfwd : forward (allocation n / 2) = allocation n := by
            dsimp only [forward]
            rw [if_pos (by linarith [hv.2])]
            ring
          simp only [allocated, if_pos hv, radius, if_pos hvhalf, hfwd]
          apply max_le
          · exact ((le_max_left _ _).trans (hScale.1 n hn)).trans (hdM n hn)
          · exact ((hfloor δ allocation hScale n hn hv).1).trans
              (by dsimp [M]; nlinarith only [hd n hn])
        · simpa only [allocated, if_neg hv, radius,
            show ¬ (1 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 by simp, if_false] using
              (show 0 ≤ M * δ n by positivity [hd n hn, show 0 < M by linarith])
      · exact ((le_max_right _ _).trans (hScale.1 n hn)).trans (hdM n hn)
    · simpa using hScale.2.const_mul M
  intro n hn hv
  have hvhalf : allocated n ∈ Set.Ioo (0 : ℝ) 1 := by
    dsimp [allocated]
    rw [if_pos hv]
    constructor <;> linarith [hv.1, hv.2]
  obtain ⟨E, hE, hprob, he⟩ :=
    hdev (fun n => M * δ n) allocated hRange hClose hcal n hn hvhalf
  refine ⟨E, hE, ?_, ?_⟩
  · simp only [allocated, if_pos hv] at hprob
    linarith [hv.1]
  · intro ω hω h hh f hf
    apply (he ω hω h hh f hf).trans
    conv_rhs => rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hD.le
    have hM0 : 0 ≤ M := by linarith
    nlinarith only [mul_nonneg (sq_nonneg M) (sq_nonneg (δ n)),
      mul_nonneg hM0 (sq_nonneg (δ n)),
      mul_nonneg (sq_nonneg M) (mul_nonneg (hd n hn) (norm_nonneg f)),
      mul_nonneg hM0 (mul_nonneg (hd n hn) (norm_nonneg f))]

end Papers.TsAdaptiveEstimationInference

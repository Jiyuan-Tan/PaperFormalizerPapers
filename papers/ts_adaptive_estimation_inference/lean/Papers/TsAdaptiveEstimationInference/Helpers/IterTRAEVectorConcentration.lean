module
public import Papers.TsAdaptiveEstimationInference.Helpers.IterTRAEFiniteConcentration
/-! Fixed-anchor vector concentration at all positive sample sizes.
The two initial sample sizes use the common coordinate envelope, without a
pointwise envelope or a measurable intersection over the hypothesis class.
-/
public section
set_option linter.style.longLine false
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory
variable {W X Z : Type*} [MeasurableSpace W] [MeasurableSpace X]
  [MeasurableSpace Z] (V : IVWorld W X Z)

/-- Under [boundedness by the envelope constant](hyp:hBound) and
[a common almost-sure envelope](hyp:hCommon), [almost every population observation
simultaneously bounds the absolute clipped loss of every vector loss-class member
by four times the envelope constant plus five times its square](goal). -/
-- @node: iter_trae_clipped_vector_envelope
lemma iter_trae_clipped_vector_envelope (B : ℝ) (hBound : TRAEBoundedness V B) (hCommon : TRAECommonNullSetBoundedness V B) :
    ∀ᵐ w ∂V.law, ∀ u ∈ traeLossClass V,
      |traeClippedLoss B w (u w)| ≤ 4 * (B + B ^ 2) + B ^ 2 := by
  filter_upwards [trae_vector_coordinate_envelope V B hBound hCommon] with w hw
  intro u hu
  have hc := (Set.ext_iff.mp (trae_loss_class_coordinates V) u).mpr hu
  have h0 := hw 0 (fun w => u w 0) (hc 0)
  have h1 := hw 1 (fun w => u w 1) (hc 1)
  have hclip : |max (-B) (min (u w 2) B)| ≤ B := by
    exact abs_le.mpr ⟨le_max_left _ _, max_le (by linarith [hBound.1]) (min_le_right _ _)⟩
  have hsq : (max (-B) (min (u w 2) B)) ^ 2 ≤ B ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hclip 2
  unfold traeClippedLoss
  have ht := abs_sub (2 * u w 0 - 2 * u w 1)
    ((max (-B) (min (u w 2) B)) ^ 2)
  have hs := abs_sub (2 * u w 0) (2 * u w 1)
  norm_num only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_sq] at ht hs
  linarith

/-- Given [boundedness](hyp:hBound) and [a common almost-sure envelope](hyp:hCommon),
[there is a measurable event of probability one for an independent sample of any
specified size on which every observation simultaneously bounds every absolute
clipped vector loss by four times the envelope constant plus five times its square](goal). -/
-- @node: iter_trae_clipped_vector_envelope_event
lemma iter_trae_clipped_vector_envelope_event (B : ℝ) (hBound : TRAEBoundedness V B) (hCommon : TRAECommonNullSetBoundedness V B)
    (n : ℕ) :
    ∃ E : Set (Fin n → W), MeasurableSet E ∧
      (Measure.pi (fun _ : Fin n => V.law)).real E = 1 ∧
      ∀ x ∈ E, ∀ i, ∀ u ∈ traeLossClass V,
        |traeClippedLoss B (x i) (u (x i))| ≤ 4 * (B + B ^ 2) + B ^ 2 := by
  let Q := Measure.pi (fun _ : Fin n => V.law)
  let S : Set (Fin n → W) := {x | ∀ i, ∀ u ∈ traeLossClass V,
    |traeClippedLoss B (x i) (u (x i))| ≤ 4 * (B + B ^ 2) + B ^ 2}
  have hS : ∀ᵐ x ∂Q, x ∈ S := by
    apply ae_all_iff.mpr
    intro i
    exact (measurePreserving_eval (fun _ : Fin n => V.law) i).quasiMeasurePreserving.ae
      (iter_trae_clipped_vector_envelope V B hBound hCommon)
  obtain ⟨N, hSN, hN, hQN⟩ := exists_measurable_superset_of_null (ae_iff.mp hS)
  refine ⟨Nᶜ, hN.compl, ?_, ?_⟩
  · have heq : Q Nᶜ = Q Set.univ := by
      simpa only [Set.compl_eq_univ_sdiff] using
        (measure_sdiff_null (s := Set.univ) hQN)
    change (Q Nᶜ).toReal = 1
    rw [heq]
    simp [Q]
  · intro x hx
    have hxS : x ∈ S := by by_contra hn; exact hx (hSN hn)
    exact hxS

/-- Assuming [anchored localized concentration](hyp:hSource), [for each bounded
class with a common envelope and positive logarithmic-floor coefficient, one positive
constant controls centered clipped-loss increments at every positive sample size:
any positive radius dominating the logarithmic and inverse-square-root floors and
all three critical radii gives a measurable event of probability at least one minus
the failure budget, with error bounded by radius times the sum of coordinate distances
plus squared radius, for each admissible population anchor with measurable suprema](goal). -/
-- @node: iter_trae_anchored_concentration_all_sizes
lemma iter_trae_anchored_concentration_all_sizes
    (hSource : IterTRAEAnchoredLocalizedConcentration V) :
∀ B cfloor : ℝ, TRAEBoundedness V B → TRAECommonNullSetBoundedness V B → 0 < cfloor →
  ∃ C > 0, ∀ n : ℕ, 0 < n → ∀ ζ ∈ Set.Ioo (0 : ℝ) 1,
  ∀ r : ℝ, cfloor * Real.sqrt
    ((3 * Real.log (Real.log n) + Real.log (1 / ζ)) / n) ≤ r →
  0 < r → (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ r →
  (∀ F ∈ ({starClass (momentImageClass V),
      starClass (productObservationClass V), starClass (criticObservationClass V)} :
        Set (Set (W → ℝ))),
    IsCriticalRadiusBound V.law F n r) →
  ∀ (ρ c b β : ℝ) (δ : ℕ → ℝ) (t : ℕ),
  GridDomain ρ → 0 < c → 2 ≤ b → 0 < β → 1 ≤ t →
  let radius := c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1))
  ∀ anchor : W → Fin 3 → ℝ,
  (anchor = 0 ∨ ∃ j : ℕ, 1 ≤ j ∧ j ≤ t ∧
    ∃ lam ∈ regGrid ρ n,
      (∃ k ≤ terminalIndex ρ n, gridValue ρ k ≤ radius) ∧
      oraclePoint ρ n radius ≤ lam ∧ lam ≤ 2 ∧ 0 < lam ∧
      populationIterate V lam j ∈ V.H ∧
      projCondExpOp V (minNormSolution V - populationIterate V lam j) ∈ V.F ∧
      anchor = iterTraePopulationAnchor V j lam) →
  anchor ∈ traeLossClass V →
  AELocalizedSupremaMeasurableAt V.law (traeLossClass V) anchor (traeClippedLoss B) n →
  ∃ E : Set (Fin n → W), MeasurableSet E ∧
    1 - ζ ≤ (Measure.pi (fun _ : Fin n => V.law)).real E ∧
    ∀ x ∈ E, ∀ u ∈ traeLossClass V,
      |(n : ℝ)⁻¹ * (∑ i, (traeClippedLoss B (x i) (u (x i)) -
          traeClippedLoss B (x i) (anchor (x i)))) -
        ∫ w, (traeClippedLoss B w (u w) - traeClippedLoss B w (anchor w)) ∂V.law| ≤
      C * (r * (∑ i : Fin 3, inputL2Norm V.law (fun w => u w i - anchor w i)) + r ^ 2) := by
  intro B cfloor hBound hCommon hcfloor
  obtain ⟨C, hC, hSource⟩ := hSource B cfloor hBound hCommon hcfloor
  let M := 4 * (B + B ^ 2) + B ^ 2
  have hM : 0 ≤ M := by dsimp [M]; positivity [hBound.1]
  refine ⟨C + 8 * M, by positivity, ?_⟩
  intro n hn ζ hζ r hfloor hr hsmall hcritical ρ c b β δ t hρ hc hb hβ ht
  dsimp only
  intro anchor hanchor hmem hMeas
  by_cases hlarge : 3 ≤ n
  · obtain ⟨E, hE, hpE, hgood⟩ := hSource n hlarge ζ hζ r hfloor hr hcritical
      ρ c b β δ t hρ hc hb hβ ht anchor hanchor hmem hMeas
    refine ⟨E, hE, hpE, ?_⟩
    intro x hx u hu
    exact (hgood x hx u hu).trans (mul_le_mul_of_nonneg_right
      (by linarith : C ≤ C + 8 * M) (by unfold inputL2Norm; positivity))
  · obtain ⟨E, hE, hpE, hgood⟩ := iter_trae_clipped_vector_envelope_event V B hBound hCommon n
    refine ⟨E, hE, by rw [hpE]; linarith [hζ.1], ?_⟩
    intro x hx u hu
    have hemp : |(n : ℝ)⁻¹ * (∑ i,
        (traeClippedLoss B (x i) (u (x i)) -
          traeClippedLoss B (x i) (anchor (x i))))| ≤ 2 * M := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ)⁻¹)]
      calc
        _ ≤ (n : ℝ)⁻¹ * ∑ i, |traeClippedLoss B (x i) (u (x i)) -
            traeClippedLoss B (x i) (anchor (x i))| :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
        _ ≤ (n : ℝ)⁻¹ * ∑ _i : Fin n, 2 * M := by
          gcongr with i
          apply (abs_sub _ _).trans
          dsimp [M]
          linarith [hgood x hx i u hu, hgood x hx i anchor hmem]
        _ = 2 * M := by simp [ne_of_gt hn]
    have hint : |∫ w, (traeClippedLoss B w (u w) - traeClippedLoss B w (anchor w))
        ∂V.law| ≤ 2 * M := by
      apply (show |∫ w, (traeClippedLoss B w (u w) - traeClippedLoss B w (anchor w))
          ∂V.law| ≤ (2 * M) * V.law.real Set.univ from ?_).trans_eq (by simp)
      rw [← Real.norm_eq_abs]
      apply norm_integral_le_of_norm_le_const
      filter_upwards [iter_trae_clipped_vector_envelope V B hBound hCommon] with w hw
      rw [Real.norm_eq_abs]
      apply (abs_sub _ _).trans
      dsimp [M]
      linarith [hw u hu, hw anchor hmem]
    have hdet := (abs_sub _ _).trans (add_le_add hemp hint)
    have hf := iter_trae_small_sample_floor n hn (by omega) r hsmall
    have hnorm : 0 ≤ ∑ i : Fin 3, inputL2Norm V.law (fun w => u w i - anchor w i) := by
      unfold inputL2Norm
      positivity
    apply hdet.trans
    nlinarith [mul_le_mul_of_nonneg_left hf (show 0 ≤ 2 * M by positivity),
      mul_nonneg hr.le hnorm, mul_nonneg hC.le (sq_nonneg r),
      mul_nonneg hC.le (mul_nonneg hr.le hnorm),
      mul_nonneg (show 0 ≤ 8 * M by positivity) (mul_nonneg hr.le hnorm)]

/-- For [a positive sample size](hyp:hn) and [a failure budget strictly between zero
and one](hyp:hζ), [the square root of three times the log-log sample size plus the
log inverse budget, divided by sample size, is at most twice the confidence floor](goal). -/
-- @node: iter_trae_vector_source_floor_le
lemma iter_trae_vector_source_floor_le (n : ℕ) (hn : 0 < n)
    (ζ : ℝ) (hζ : ζ ∈ Set.Ioo (0 : ℝ) 1) :
    Real.sqrt ((3 * Real.log (Real.log n) + Real.log (1 / ζ)) / n) ≤
      2 * confidenceFloor n ζ := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : Real.log (Real.log n) ≤ Real.log (Real.log (Real.exp 1 * n)) := by
    by_cases hn1 : n = 1
    · subst n
      simp
    · have hn1' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
      have hexp : 1 ≤ Real.exp 1 := by simp
      exact Real.log_le_log (Real.log_pos hn1')
        (Real.log_le_log hnpos (by nlinarith))
  have hζlog : 0 ≤ Real.log (1 / ζ) :=
    Real.log_nonneg ((one_le_div hζ.1).mpr hζ.2.le)
  have hf : (Real.log (Real.log (Real.exp 1 * n)) + Real.log (1 / ζ)) / n ≤
      confidenceFloor n ζ ^ 2 := by
    unfold confidenceFloor
    rw [Real.sq_sqrt']
    exact le_max_left _ _
  apply Real.sqrt_le_iff.mpr
  refine ⟨by unfold confidenceFloor; positivity, ?_⟩
  have hraw : (3 * Real.log (Real.log n) + Real.log (1 / ζ)) / n ≤
      3 * ((Real.log (Real.log (Real.exp 1 * n)) + Real.log (1 / ζ)) / n) := by
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ hnpos.le
    linarith
  nlinarith [sq_nonneg (confidenceFloor n ζ)]

/-- Given [a positive logarithmic-floor coefficient](hyp:hcfloor) and
[critical-radius control](hyp:hComplexity), [one multiplier at least one, chosen
before the accuracy and allocation curves, makes every calibrated accuracy dominate
the raw logarithmic floor at half allocation, the inverse-square-root sample-size
floor, and all three coordinate critical radii, at every positive sample size with
an allocation strictly between zero and one](goal). -/
-- @node: iter_trae_vector_radius_at_allocation
lemma iter_trae_vector_radius_at_allocation
    (cfloor : ℝ) (hcfloor : 0 < cfloor) (tildeδ : ℕ → ℝ → ℝ)
    (hComplexity : TRAECriticalRadiusBound V tildeδ) :
    ∃ K ≥ (1 : ℝ), ∀ (δ allocation : ℕ → ℝ),
      TRAEScaleCalibration δ tildeδ allocation →
      ∀ n : ℕ, 0 < n → allocation n ∈ Set.Ioo (0 : ℝ) 1 →
      cfloor * Real.sqrt
        ((3 * Real.log (Real.log n) + Real.log (1 / (allocation n / 2))) / n) ≤ K * δ n ∧
      (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ K * δ n ∧
      (∀ F ∈ ({starClass (momentImageClass V), starClass (productObservationClass V),
          starClass (criticObservationClass V)} : Set (Set (W → ℝ))),
        IsCriticalRadiusBound V.law F n (K * δ n)) := by
  obtain ⟨L, hL, hradius⟩ := trae_radius_uniform_at_allocation V tildeδ hComplexity
  let K := max 1 (max L (2 * cfloor * L))
  have hK : 1 ≤ K := le_max_left _ _
  have hLK : L ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hcK : 2 * cfloor * L ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨K, hK, ?_⟩
  intro δ allocation hScale n hn halloc
  obtain ⟨hf, hp, hm, hq⟩ := hradius δ allocation hScale n hn halloc
  have hd : 0 ≤ δ n := (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ n) _).trans
    ((le_max_right _ _).trans (hScale.1 n hn))
  have hdK : δ n ≤ K * δ n := by nlinarith only [hK, hd]
  have hhalf : allocation n / 2 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [halloc.1, halloc.2]
  refine ⟨?_, ((le_max_right _ _).trans (hScale.1 n hn)).trans hdK, ?_⟩
  · calc
      _ ≤ cfloor * (2 * confidenceFloor n (allocation n / 2)) :=
        mul_le_mul_of_nonneg_left (iter_trae_vector_source_floor_le n hn _ hhalf) hcfloor.le
      _ ≤ cfloor * (2 * (L * δ n)) := by gcongr
      _ ≤ K * δ n := by
        nlinarith only [mul_le_mul_of_nonneg_right hcK hd]
  · intro F hF
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hF
    have hr := mul_le_mul_of_nonneg_right hLK hd
    rcases hF with rfl | rfl | rfl
    · exact criticalRadiusBound_mono _ _ _ _ _ hm hr
    · exact criticalRadiusBound_mono _ _ _ _ _ hp hr
    · exact criticalRadiusBound_mono _ _ _ _ _ hq hr

/-- Under [anchored localized concentration](hyp:hSource), [boundedness](hyp:hBound),
[a common almost-sure envelope](hyp:hCommon), and [critical-radius control](hyp:hComplexity),
[one positive constant uniform in calibrated accuracy and allocation curves gives,
for each admissible population anchor with measurable localized suprema, a measurable
independent-sample event of probability at least one minus half the allocation on
which every centered clipped-loss increment is bounded by accuracy times the sum
of its three coordinate distances from the anchor plus squared accuracy](goal). -/
-- @node: iter_trae_anchored_calibrated_at_allocation
lemma iter_trae_anchored_calibrated_at_allocation
    (hSource : IterTRAEAnchoredLocalizedConcentration V)
    (B : ℝ) (tildeδ : ℕ → ℝ → ℝ)
    (hBound : TRAEBoundedness V B) (hCommon : TRAECommonNullSetBoundedness V B)
    (hComplexity : TRAECriticalRadiusBound V tildeδ) :
    ∃ C > 0, ∀ (accuracy allocation : ℕ → ℝ),
      TRAEScaleCalibration accuracy tildeδ allocation →
      ∀ n : ℕ, 0 < n → allocation n ∈ Set.Ioo (0 : ℝ) 1 →
  ∀ (ρ c b β : ℝ) (δ : ℕ → ℝ) (t : ℕ),
  GridDomain ρ → 0 < c → 2 ≤ b → 0 < β → 1 ≤ t →
  let radius := c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1))
  ∀ anchor : W → Fin 3 → ℝ,
  (anchor = 0 ∨ ∃ j : ℕ, 1 ≤ j ∧ j ≤ t ∧
    ∃ lam ∈ regGrid ρ n,
      (∃ k ≤ terminalIndex ρ n, gridValue ρ k ≤ radius) ∧
      oraclePoint ρ n radius ≤ lam ∧ lam ≤ 2 ∧ 0 < lam ∧
      populationIterate V lam j ∈ V.H ∧
      projCondExpOp V (minNormSolution V - populationIterate V lam j) ∈ V.F ∧
      anchor = iterTraePopulationAnchor V j lam) →
  anchor ∈ traeLossClass V →
  AELocalizedSupremaMeasurableAt V.law (traeLossClass V) anchor (traeClippedLoss B) n →
  ∃ E : Set (Fin n → W), MeasurableSet E ∧
    1 - allocation n / 2 ≤ (Measure.pi (fun _ : Fin n => V.law)).real E ∧
    ∀ x ∈ E, ∀ u ∈ traeLossClass V,
      |(n : ℝ)⁻¹ * (∑ i, (traeClippedLoss B (x i) (u (x i)) -
          traeClippedLoss B (x i) (anchor (x i)))) -
        ∫ w, (traeClippedLoss B w (u w) - traeClippedLoss B w (anchor w)) ∂V.law| ≤
      C * (accuracy n * (∑ i : Fin 3, inputL2Norm V.law (fun w => u w i - anchor w i)) + accuracy n ^ 2) := by
  obtain ⟨cfloor, hcfloor, hcritical⟩ := hComplexity
  have hComplexity : TRAECriticalRadiusBound V tildeδ := ⟨cfloor, hcfloor, hcritical⟩
  obtain ⟨K, hK, hradius⟩ :=
    iter_trae_vector_radius_at_allocation V cfloor hcfloor tildeδ hComplexity
  obtain ⟨Cs, hCs, hsource⟩ :=
    iter_trae_anchored_concentration_all_sizes V hSource B cfloor hBound hCommon hcfloor
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  refine ⟨Cs * (K ^ 2 + K), by positivity, ?_⟩
  intro accuracy allocation hScale n hn halloc ρ c b β δ t hρ hc hb hβ ht
  dsimp only
  intro anchor hanchor hmem hMeas
  obtain ⟨hfloor, hsmall, hcrit⟩ := hradius accuracy allocation hScale n hn halloc
  have hα : 0 < accuracy n := by
    have hi : 0 < (n : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos (by positivity) _
    exact hi.trans_le ((le_max_right _ _).trans (hScale.1 n hn))
  have hhalf : allocation n / 2 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [halloc.1, halloc.2]
  obtain ⟨E, hE, hpE, hgood⟩ := hsource n hn (allocation n / 2) hhalf
    (K * accuracy n) hfloor (mul_pos hKpos hα) hsmall hcrit
    ρ c b β δ t hρ hc hb hβ ht anchor hanchor hmem hMeas
  refine ⟨E, hE, hpE, ?_⟩
  intro x hx u hu
  apply (hgood x hx u hu).trans
  have hnorm : 0 ≤ ∑ i : Fin 3, inputL2Norm V.law (fun w => u w i - anchor w i) := by
    unfold inputL2Norm
    positivity
  have hk : K ≤ K ^ 2 + K := by nlinarith only [sq_nonneg K]
  have hk2 : K ^ 2 ≤ K ^ 2 + K := by linarith only [hKpos]
  calc
    _ = Cs * (K * (accuracy n * ∑ i : Fin 3,
        inputL2Norm V.law (fun w => u w i - anchor w i)) +
        K ^ 2 * accuracy n ^ 2) := by ring
    _ ≤ Cs * ((K ^ 2 + K) * (accuracy n * ∑ i : Fin 3,
        inputL2Norm V.law (fun w => u w i - anchor w i)) +
        (K ^ 2 + K) * accuracy n ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hCs.le
      exact add_le_add (mul_le_mul_of_nonneg_right hk (mul_nonneg hα.le hnorm))
        (mul_le_mul_of_nonneg_right hk2 (sq_nonneg _))
    _ = _ := by ring

end Papers.TsAdaptiveEstimationInference

module
public import Papers.TsAdaptiveEstimationInference.Helpers.TRAESetup
/-! Normalized scalar squared-loss concentration for the TRAE norm comparison. -/
public section
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory Filter
open scoped Topology ENNReal
variable {𝒲 𝒳 𝒵 Ω : Type*} [MeasurableSpace 𝒲] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒵] [MeasurableSpace Ω]
  (V : IVWorld 𝒲 𝒳 𝒵) (P : Measure Ω) [IsProbabilityMeasure P]
  (sample : AnalysisSample V P) (split : SampleSplit)

/-- If [one function class is contained in another](hyp:hFG), then [its expected
Rademacher complexity is no larger, under the same measure and sample size](goal). -/
-- @node: trae_expectedRademacher_mono
lemma trae_expectedRademacher_mono {A : Type*} [MeasurableSpace A]
    (μ : Measure A) {F G : Set (A → ℝ)} (hFG : F ⊆ G) (n : ℕ) :
    expectedRademacher μ F n ≤ expectedRademacher μ G n := by
  apply lintegral_mono
  intro x
  apply mul_le_mul_of_nonneg_left _ zero_le
  apply Finset.sum_le_sum
  intro ε _
  apply iSup_le
  intro f
  exact le_iSup_of_le (⟨f.1, hFG f.2⟩ : G) le_rfl

/-- [The absolute difference between two squared magnitudes clipped at one is
at most twice the absolute difference between the original real numbers](goal). -/
-- @node: trae_clipped_square_lipschitz
lemma trae_clipped_square_lipschitz (u v : ℝ) :
    |(min |u| 1) ^ 2 - (min |v| 1) ^ 2| ≤ 2 * |u - v| := by
  have hu : |min |u| 1| ≤ 1 := by
    rw [abs_of_nonneg (le_min (abs_nonneg _) zero_le_one)]
    exact min_le_right _ _
  have hv : |min |v| 1| ≤ 1 := by
    rw [abs_of_nonneg (le_min (abs_nonneg _) zero_le_one)]
    exact min_le_right _ _
  have hl : LipschitzWith 1 (fun x : ℝ => min |x| 1) :=
    (show LipschitzWith 1 (fun x : ℝ => |x|) from by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using abs_abs_sub_abs_le_abs_sub x y).min_const 1
  have hd : |min |u| 1 - min |v| 1| ≤ |u - v| := by
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using hl.dist_le_mul u v
  exact (localizedSquaredLossLipschitz 1 _ _ zero_le_one hu hv).trans (by linarith)

/-- [The population mean of the squared difference between the observation
representatives of two hypotheses equals the squared Hilbert-space norm of
their difference](goal). -/
-- @node: trae_primal_difference_energy
lemma trae_primal_difference_energy (h h' : V.Hbar.toSubmodule) :
    (∫ w, (primalVersion V h (V.xOf w) - primalVersion V h' (V.xOf w)) ^ 2
      ∂V.law) = ‖h - h'‖ ^ 2 := by
  have he : (fun w => primalVersion V h (V.xOf w) - primalVersion V h' (V.xOf w))
      =ᵐ[V.law] (fun w => ((h - h' : V.Hbar.toSubmodule) : Lp ℝ 2 V.law) w) :=
    ((V.primal_coherent h).sub (V.primal_coherent h')).trans (Lp.coeFn_sub _ _).symm
  calc
    _ = ∫ w, (((h - h' : V.Hbar.toSubmodule) : Lp ℝ 2 V.law) w) ^ 2 ∂V.law := by
      apply integral_congr_ae
      filter_upwards [he] with w hw
      exact congrArg (fun x : ℝ => x ^ 2) hw
    _ = _ := by
      simpa only [L2.inner_def, RCLike.inner_apply, conj_trivial, ← pow_two,
        Submodule.norm_coe] using
        (real_inner_self_eq_norm_sq ((h - h' : V.Hbar.toSubmodule) : Lp ℝ 2 V.law))

omit [IsProbabilityMeasure P] in
/-- Under [the TRAE boundedness and process-measurability assumptions](hyp:hBound)
and [simultaneous bounds outside a common null set](hyp:hCommon), [there is a
measurable event of full measure on which sample representatives respect zero
and every hypothesis observation in the fitting block is bounded in absolute
value by B](goal).

The null hull avoids requiring measurability of an arbitrary class intersection. -/
-- @node: trae_fitting_bounded_event
lemma trae_fitting_bounded_event (B : ℝ) (hBound : TRAEBoundedness V B) (hCommon : TRAECommonNullSetBoundedness V B) (n : ℕ) :
    ∃ E : Set Ω, MeasurableSet E ∧ (∀ᵐ ω ∂P, ω ∈ E) ∧
      ∀ ω ∈ E, ω ∈ sampleZeroEvent V P sample ∧ ∀ i ∈ split.fit n, ∀ h ∈ V.H,
        |primalVersion V h (V.xOf (sample.Z i ω))| ≤ B := by
  have ha : ∀ᵐ ω ∂P, ∀ i : ℕ, ∀ h ∈ V.H,
      |primalVersion V h (V.xOf (sample.Z i ω))| ≤ B := by
    apply ae_all_iff.mpr
    intro i
    have h : ∀ᵐ w ∂P.map (sample.Z i), ∀ h ∈ V.H,
        |primalVersion V h (V.xOf w)| ≤ B := by
      simpa only [sample.map_eq i] using hCommon.mono (fun _ hw => hw.1)
    exact ae_of_ae_map (sample.meas i).aemeasurable h
  let S := {ω | ∀ i : ℕ, ∀ h ∈ V.H,
    |primalVersion V h (V.xOf (sample.Z i ω))| ≤ B}
  have hnull : P Sᶜ = 0 := by exact (ae_iff.mp ha)
  obtain ⟨N, hSN, hN, hPN⟩ := exists_measurable_superset_of_null hnull
  refine ⟨Nᶜ ∩ sampleZeroEvent V P sample,
    hN.compl.inter (sampleZeroEvent_measurable V P sample), ?_, ?_⟩
  · have hNa : ∀ᵐ ω ∂P, ω ∈ Nᶜ := compl_mem_ae_iff.mpr hPN
    exact hNa.and (sampleZeroEvent_ae V P sample)
  · intro ω hω
    refine ⟨hω.2, ?_⟩
    intro i _ h hh
    have hωS : ω ∈ S := by by_contra hn; exact hω.1 (hSN hn)
    exact hωS i h hh

/-- If [the normalization scale is at least one](hyp:hs), [the minimum-norm
solution belongs to the hypothesis class](hyp:hRealizable), and [r is a critical
radius bound for the primal observation star class at sample size n](hyp:hr),
then [the expected Rademacher complexity of the star hull of normalized
hypothesis differences from the minimum-norm solution, restricted to L² norm
at most r, is at most r squared](goal). -/
-- @node: trae_anchored_rademacher_bound
lemma trae_anchored_rademacher_bound (s r : ℝ) (hs : 1 ≤ s)
    (hRealizable : H0MemHypothesisClass V) (n : ℕ)
    (hr : IsCriticalRadiusBound V.law (starClass (primalObservationClass V)) n r) :
    expectedRademacher V.law
      {g ∈ starClass {g | ∃ h ∈ V.H, g = fun w =>
        primalVersion V h (V.xOf w) / s -
          primalVersion V (minNormSolution V) (V.xOf w) / s} |
        eLpNorm g 2 V.law ≤ ENNReal.ofReal r} n ≤ ENNReal.ofReal (r ^ 2) := by
  apply (trae_expectedRademacher_mono V.law (n := n) ?_).trans hr.2
  intro g hg
  refine ⟨?_, hg.2⟩
  obtain ⟨a, ha, f, ⟨h, hh, rfl⟩, rfl⟩ := hg.1
  refine ⟨a / s, ⟨div_nonneg ha.1 (by linarith),
    (div_le_one (by linarith)).2 (ha.2.trans hs)⟩,
    (fun w => primalVersion V h (V.xOf w)) -
      (fun w => primalVersion V (minNormSolution V) (V.xOf w)), ?_, ?_⟩
  · refine ⟨_, ?_, _, ?_, rfl⟩
    · exact ⟨1, ⟨zero_le_one, le_rfl⟩, (fun w => primalVersion V h (V.xOf w)),
        ⟨h, hh, rfl⟩, by simp⟩
    · exact ⟨1, ⟨zero_le_one, le_rfl⟩,
        (fun w => primalVersion V (minNormSolution V) (V.xOf w)),
        ⟨minNormSolution V, hRealizable, rfl⟩, by simp⟩
  · ext w
    simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
    ring

/-- For [a positive normalization scale](hyp:hs), [the population L² norm of
the difference between two normalized hypothesis representatives equals their
Hilbert-space distance divided by that scale](goal). -/
-- @node: trae_normalized_difference_norm
lemma trae_normalized_difference_norm (s : ℝ) (hs : 0 < s)
    (h h' : V.Hbar.toSubmodule) :
    inputL2Norm V.law (fun w => primalVersion V h (V.xOf w) / s -
      primalVersion V h' (V.xOf w) / s) = ‖h - h'‖ / s := by
  unfold inputL2Norm
  simp_rw [← sub_div, div_pow]
  rw [integral_div, trae_primal_difference_energy, Real.sqrt_div (sq_nonneg _),
    Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hs.le]

omit [IsProbabilityMeasure P] in
/-- Suppose [the normalization scale is positive](hyp:hs), [B does not exceed
that scale](hyp:hBs), [the TRAE boundedness and process-measurability assumptions
hold](hyp:hBound), [the common-null-set bounds hold](hyp:hCommon), and [the
minimum-norm solution is admissible](hyp:hRealizable). If [every admissible
hypothesis is bounded by B at every fitting observation of this sample](hyp:hω)
and [the hypothesis under comparison is admissible](hyp:hh), then [its empirical
squared-norm increment relative to the minimum-norm solution, minus the
population increment, equals the scale squared times the centered fitting
average of their normalized, clipped squared-loss difference](goal). -/
-- @node: trae_clipped_square_transfer
lemma trae_clipped_square_transfer (s B : ℝ) (hs : 0 < s) (hBs : B ≤ s)
    (hBound : TRAEBoundedness V B) (hCommon : TRAECommonNullSetBoundedness V B) (hRealizable : H0MemHypothesisClass V)
    (n : ℕ) (ω : Ω)
    (hω : ∀ i ∈ split.fit n, ∀ h ∈ V.H,
      |primalVersion V h (V.xOf (sample.Z i ω))| ≤ B)
    (h : V.Hbar.toSubmodule) (hh : h ∈ V.H) :
    let f := fun w => (min |primalVersion V h (V.xOf w) / s| 1) ^ 2 -
      (min |primalVersion V (minNormSolution V) (V.xOf w) / s| 1) ^ 2
    (primalEmpSq V P sample split n ω h -
        primalEmpSq V P sample split n ω (minNormSolution V)) -
      (‖h‖ ^ 2 - ‖minNormSolution V‖ ^ 2) =
        s ^ 2 * (blockAverage V P sample (split.fit n) f ω - ∫ w, f w ∂V.law) := by
  dsimp only
  have hc (u : ℝ) (hu : |u| ≤ B) : (min |u / s| 1) ^ 2 = u ^ 2 / s ^ 2 := by
    rw [min_eq_left (by rw [abs_div, abs_of_pos hs]; exact (div_le_one hs).2 (hu.trans hBs)),
      sq_abs, div_pow]
  have hi (u : V.Hbar.toSubmodule) :
      Integrable (fun w => primalVersion V u (V.xOf w) ^ 2) V.law :=
    ((memLp_congr_ae (V.primal_coherent u)).2
      (Lp.memLp (u : Lp ℝ 2 V.law))).integrable_sq
  have he (u : V.Hbar.toSubmodule) :
      (∫ w, primalVersion V u (V.xOf w) ^ 2 ∂V.law) = ‖u‖ ^ 2 := by
    calc
      _ = ∫ w, (primalVersion V u (V.xOf w) - primalVersion V 0 (V.xOf w)) ^ 2 ∂V.law := by
        apply integral_congr_ae
        filter_upwards [primalVersion_zero_ae V] with w hw
        simp only [hw, algorithmicZero, Pi.zero_apply, sub_zero]
      _ = ‖u‖ ^ 2 := by simpa only [sub_zero] using trae_primal_difference_energy V u 0
  have hpop : (∫ w, (min |primalVersion V h (V.xOf w) / s| 1) ^ 2 -
      (min |primalVersion V (minNormSolution V) (V.xOf w) / s| 1) ^ 2 ∂V.law) =
        (‖h‖ ^ 2 - ‖minNormSolution V‖ ^ 2) / s ^ 2 := by
    calc
      _ = ∫ w, (primalVersion V h (V.xOf w) ^ 2 -
          primalVersion V (minNormSolution V) (V.xOf w) ^ 2) / s ^ 2 ∂V.law := by
        apply integral_congr_ae
        filter_upwards [hBound.2.2.1] with w hw
        rw [hc _ (hw h hh), hc _ (hw _ hRealizable), sub_div]
      _ = _ := by rw [integral_div, integral_sub (hi h) (hi _), he, he]
  have hemp : blockAverage V P sample (split.fit n)
      (fun w => (min |primalVersion V h (V.xOf w) / s| 1) ^ 2 -
        (min |primalVersion V (minNormSolution V) (V.xOf w) / s| 1) ^ 2) ω =
      (primalEmpSq V P sample split n ω h -
        primalEmpSq V P sample split n ω (minNormSolution V)) / s ^ 2 := by
    simp only [blockAverage, primalEmpSq]
    rw [← mul_sub, ← Finset.sum_sub_distrib, mul_div_assoc, Finset.sum_div]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [hc _ (hω i hi h hh), hc _ (hω i hi _ hRealizable), sub_div]
  rw [hpop, hemp]
  field_simp

/-- If [the normalization scale is positive](hyp:hs), [B does not exceed that
scale](hyp:hBs), [the TRAE boundedness and process-measurability assumptions
hold](hyp:hBound), [the common-null-set bounds hold](hyp:hCommon), and [the
minimum-norm solution is admissible](hyp:hRealizable), then [the localized
normalized scalar loss obtained by squaring magnitudes clipped at one has
measurable centered and signed processes](goal). -/
-- @node: trae_clipped_square_processes_measurable
lemma trae_clipped_square_processes_measurable (s B : ℝ) (hs : 0 < s)
    (hBs : B ≤ s) (hBound : TRAEBoundedness V B) (hCommon : TRAECommonNullSetBoundedness V B)
    (hRealizable : H0MemHypothesisClass V) :
    MeasurableLocalizedScalarLoss V s (fun u => (min |u| 1) ^ 2) := by
  classical
  intro n hn r hr
  have hloc : {h ∈ V.H | inputL2Norm V.law (fun w =>
      primalVersion V h (V.xOf w) / s -
        primalVersion V (minNormSolution V) (V.xOf w) / s) ≤ r} =
      {h ∈ V.H | ‖h - minNormSolution V‖ ≤ s * r} := by
    ext h
    simp only [Set.mem_setOf_eq, trae_normalized_difference_norm V s hs,
      div_le_iff₀ hs, mul_comm r s]
  dsimp only
  rw [hloc]
  let raw := fun (h : V.Hbar.toSubmodule) w =>
    primalVersion V h (V.xOf w) ^ 2 -
      primalVersion V (minNormSolution V) (V.xOf w) ^ 2
  let inc := fun (h : V.Hbar.toSubmodule) w =>
    (min |primalVersion V h (V.xOf w) / s| 1) ^ 2 -
      (min |primalVersion V (minNormSolution V) (V.xOf w) / s| 1) ^ 2
  have hc (u : ℝ) (hu : |u| ≤ B) : (min |u / s| 1) ^ 2 = u ^ 2 / s ^ 2 := by
    have hu1 : |u / s| ≤ 1 := by
      rw [abs_div, abs_of_pos hs]
      exact (div_le_one hs).2 (hu.trans hBs)
    rw [min_eq_left hu1, sq_abs, div_pow]
  have he (w : 𝒲) (hw : ∀ h ∈ V.H, |primalVersion V h (V.xOf w)| ≤ B)
      (h : V.Hbar.toSubmodule) (hh : h ∈ V.H) : inc h w = raw h w / s ^ 2 := by
    dsimp [inc, raw]
    rw [hc _ (hw h hh), hc _ (hw _ hRealizable), sub_div]
  have hi (h : V.Hbar.toSubmodule) (hh : h ∈ V.H) :
      (∫ w, inc h w ∂V.law) = (∫ w, raw h w ∂V.law) / s ^ 2 := by
    rw [← integral_div]
    apply integral_congr_ae
    filter_upwards [hBound.2.2.1] with w hw
    exact he w hw h hh
  have htuple : ∀ᵐ x : Fin n → 𝒲 ∂Measure.pi (fun _ => V.law),
      ∀ i, ∀ h ∈ V.H, |primalVersion V h (V.xOf (x i))| ≤ B := by
    apply ae_all_iff.mpr
    intro i
    exact (measurePreserving_eval (fun _ : Fin n => V.law) i).quasiMeasurePreserving.ae
      hBound.2.2.1
  obtain ⟨hm, hsign⟩ := hBound.2.2.2.2.1 n hn (s * r) (mul_pos hs hr)
  constructor
  · apply (hm.aemeasurable.div_const (ENNReal.ofReal (s ^ 2))).congr
    filter_upwards [htuple] with x hx
    rw [ENNReal.iSup_div]
    apply iSup_congr
    intro h
    have havg : (n : ℝ)⁻¹ * ∑ i, inc h.1 (x i) =
        ((n : ℝ)⁻¹ * ∑ i, raw h.1 (x i)) / s ^ 2 := by
      simp_rw [he _ (hx _) h.1 h.2.1]
      rw [← Finset.sum_div, mul_div_assoc]
    change ENNReal.ofReal |(n : ℝ)⁻¹ * ∑ i, raw h.1 (x i) -
      ∫ w, raw h.1 w ∂V.law| / ENNReal.ofReal (s ^ 2) =
      ENNReal.ofReal |(n : ℝ)⁻¹ * ∑ i, inc h.1 (x i) - ∫ w, inc h.1 w ∂V.law|
    rw [havg, hi h.1 h.2.1, ← sub_div, abs_div, abs_of_pos (sq_pos_of_pos hs),
      ENNReal.ofReal_div_of_pos (sq_pos_of_pos hs)]
  · apply (hsign.aemeasurable.div_const (ENNReal.ofReal (s ^ 2))).congr
    have ht : ∀ᵐ p : (Fin n → 𝒲) × (Fin n → Bool)
        ∂(Measure.pi (fun _ => V.law)).prod
          ((2 ^ n : ℝ≥0∞)⁻¹ • (Measure.count : Measure (Fin n → Bool))),
        ∀ i, ∀ h ∈ V.H, |primalVersion V h (V.xOf (p.1 i))| ≤ B :=
      Measure.quasiMeasurePreserving_fst.ae htuple
    filter_upwards [ht] with p hp
    rw [ENNReal.iSup_div]
    apply iSup_congr
    intro h
    have havg : (n : ℝ)⁻¹ * ∑ i, (if p.2 i then (1 : ℝ) else -1) * inc h.1 (p.1 i) =
        ((n : ℝ)⁻¹ * ∑ i, (if p.2 i then (1 : ℝ) else -1) * raw h.1 (p.1 i)) / s ^ 2 := by
      simp_rw [he _ (hp _) h.1 h.2.1, ← mul_div_assoc]
      rw [← Finset.sum_div, mul_div_assoc]
    change ENNReal.ofReal |(n : ℝ)⁻¹ * ∑ i, (if p.2 i then (1 : ℝ) else -1) *
      raw h.1 (p.1 i)| / ENNReal.ofReal (s ^ 2) =
      ENNReal.ofReal |(n : ℝ)⁻¹ * ∑ i, (if p.2 i then (1 : ℝ) else -1) * inc h.1 (p.1 i)|
    rw [havg, abs_div, abs_of_pos (sq_pos_of_pos hs),
      ENNReal.ofReal_div_of_pos (sq_pos_of_pos hs)]

/-- Given [localized concentration for scalar Lipschitz losses](hyp:hNorm),
[for every bounded, realizable TRAE model with common-null-set bounds, critical
radius bounds, and calibrated scales, a positive constant bounds all empirical
squared-norm increments relative to the minimum-norm solution by their population
increments plus the constant times the sum of accuracy times hypothesis distance
and accuracy squared, on a measurable event of probability at least one minus
the allocation for each positive sample size with allocation between zero and
one; sample representatives also respect zero on this event](goal). -/
-- @node: trae_squared_norm_at_allocation
lemma trae_squared_norm_at_allocation
    (hNorm : ScalarLipschitzLocalizedConcentration V P sample split) :
  ∀ (B : ℝ) (tildeδ : ℕ → ℝ → ℝ) (δ allocation : ℕ → ℝ),
  TRAEBoundedness V B → TRAECommonNullSetBoundedness V B → H0MemHypothesisClass V →
  TRAECriticalRadiusBound V tildeδ → TRAEScaleCalibration δ tildeδ allocation →
  ∃ C > 0, ∀ n : ℕ, 0 < n → allocation n ∈ Set.Ioo (0 : ℝ) 1 →
    ∃ E : Set Ω, MeasurableSet E ∧ 1 - allocation n ≤ P.real E ∧
      ∀ ω ∈ E, ω ∈ sampleZeroEvent V P sample ∧ ∀ h ∈ V.H,
        |(primalEmpSq V P sample split n ω h -
            primalEmpSq V P sample split n ω (minNormSolution V)) -
          (‖h‖ ^ 2 - ‖minNormSolution V‖ ^ 2)| ≤
            C * (δ n * ‖h - minNormSolution V‖ + δ n ^ 2) := by
  intro B tildeδ δ allocation hBound hCommon hRealizable hComplexity hScale
  obtain ⟨C, hC, hUniform⟩ := hNorm inferInstance B tildeδ hBound hCommon hComplexity
  refine ⟨C, hC, ?_⟩
  intro n hn halloc
  obtain ⟨E, hE, hp, hgood⟩ := hUniform δ allocation hRealizable hScale n hn halloc
  refine ⟨E ∩ sampleZeroEvent V P sample,
    hE.inter (sampleZeroEvent_measurable V P sample), ?_, ?_⟩
  · have heq : (E ∩ sampleZeroEvent V P sample : Set Ω) =ᵐ[P] E := by
      filter_upwards [sampleZeroEvent_ae V P sample] with ω hω
      exact propext ⟨fun h => h.1, fun h => ⟨h, hω⟩⟩
    rwa [measureReal_congr heq]
  · intro ω hω
    exact ⟨hω.2, hgood ω hω.1⟩

/-! PRIOR PROOF (carry-over of the generic scalar-loss instantiation).
The registered carrier now states only the frozen squared-norm specialization.
The normalization and anchored-complexity helpers above remain local.
  intro B tildeδ δ allocation hBound hCommon hRealizable hComplexity hScale
  obtain ⟨c2, hc2, c5, hc5, c6, hc6, hlocal⟩ := hNorm
  obtain ⟨c, hc, hcomplex⟩ := hComplexity
  obtain ⟨Kp, hKp, hpeel⟩ := localizedPeelingRadiusWithFloor c2 c 1 hc2 hc (by omega)
  obtain ⟨Kt, hKt, htail⟩ := decayingTailConfidence c5 c6 c hc5 hc6 hc
  let s := max 1 B
  let K := max 1 (max Kp Kt)
  let C := 36 * s ^ 2 * (K ^ 2 + K) + 2 * s ^ 2 / c2 + 1
  have hs1 : 1 ≤ s := le_max_left _ _
  have hs : 0 < s := zero_lt_one.trans_le hs1
  have hBs : B ≤ s := le_max_right _ _
  have hK1 : 1 ≤ K := le_max_left _ _
  have hK : 0 < K := zero_lt_one.trans_le hK1
  have hC : 0 < C := by dsimp [C]; positivity
  have hnormalized : ∀ᵐ w ∂V.law, ∀ h ∈ V.H,
      |primalVersion V h (V.xOf w) / s| ≤ 1 := by
    filter_upwards [hBound.2.2.1] with w hw
    intro h hh
    rw [abs_div, abs_of_pos hs]
    exact (div_le_one hs).2 ((hw h hh).trans hBs)
  refine ⟨C, hC, ?_⟩
  intro n hn halloc
  obtain ⟨hfloor, _, _, _, hprimal, _⟩ := hcomplex n hn (allocation n) halloc
  have htilde : tildeδ n (allocation n) ≤ δ n :=
    (le_max_left _ _).trans (hScale.1 n hn)
  have hsmall : (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ δ n :=
    (le_max_right _ _).trans (hScale.1 n hn)
  have hδ : 0 < δ n := hprimal.1.trans_le htilde
  have hdK : δ n ≤ K * δ n := by nlinarith only [hK1, hδ]
  have hfl : c * confidenceFloor n (allocation n) ≤ δ n := hfloor.trans htilde
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨S, hS, hSae, hSgood⟩ := trae_fitting_bounded_event V P sample split B hBound hCommon n
  let loss : ℝ → ℝ := fun u => (min |u| 1) ^ 2
  have hMeas : MeasurableLocalizedScalarLoss V s loss :=
    trae_clipped_square_processes_measurable V s B hs hBs hBound hCommon hRealizable
  by_cases hlarge : 1 < 2 * c2 * (n : ℝ)
  · have hpeeling := hpeel n (allocation n) (δ n) hn halloc hfl hsmall
    have hKpK : Kp ≤ K := (le_max_left _ _).trans (le_max_right _ _)
    have hKtK : Kt ≤ K := (le_max_right _ _).trans (le_max_right _ _)
    have hrad := criticalRadiusBound_mono _ _ n _ _ hprimal (htilde.trans hdK)
    have hthreshold : 4 * Real.log (41 * Real.log (2 * c2 * n)) / (c2 * n) ≤
        (K * δ n) ^ 2 := by
      norm_num only [Nat.cast_one, mul_one] at hpeeling
      exact hpeeling.trans (pow_le_pow_left₀ (by positivity)
        (mul_le_mul_of_nonneg_right hKpK hδ.le) 2)
    obtain ⟨E, hE, hpE, hcomp⟩ := hlocal s hs hRealizable hnormalized 2 (by norm_num)
      loss (fun u v => trae_clipped_square_lipschitz u v) hMeas n (K * δ n) hn
      (mul_pos hK hδ) hlarge hthreshold
      (trae_anchored_rademacher_bound V s _ hs1 hRealizable n hrad)
    have htail' : c5 * Real.exp (-c6 * n * (K * δ n) ^ 2) ≤ allocation n := by
      apply le_trans _ (htail n (allocation n) (δ n) hn halloc hfl hsmall)
      apply mul_le_mul_of_nonneg_left _ hc5.le
      apply Real.exp_le_exp.mpr
      have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ Kt * δ n)
        (mul_le_mul_of_nonneg_right hKtK hδ.le) 2
      nlinarith only [mul_le_mul_of_nonneg_left hsq (mul_pos hc6 hnpos).le]
    refine ⟨E ∩ S, hE.inter hS, ?_, ?_⟩
    · have heq : (E ∩ S : Set Ω) =ᵐ[P] E := by
        filter_upwards [hSae] with ω hω
        exact propext ⟨fun h => h.1, fun h => ⟨h, hω⟩⟩
      rw [measureReal_congr heq]
      linarith only [hpE, htail']
    · intro ω hω h hh
      rw [trae_clipped_square_transfer V P sample split s B hs hBs hBound hCommon hRealizable
        n ω (hSgood ω hω.2) h hh, abs_mul, abs_of_nonneg (sq_nonneg s)]
      have hb := hcomp ω hω.1 h hh
      dsimp only at hb
      rw [trae_normalized_difference_norm V s hs] at hb
      apply (mul_le_mul_of_nonneg_left hb (sq_nonneg s)).trans
      have hdiv : ‖h - minNormSolution V‖ / s ≤ ‖h - minNormSolution V‖ :=
        (div_le_iff₀ hs).2 (by nlinarith only [hs1, norm_nonneg (h - minNormSolution V)])
      have hmain : s ^ 2 * (18 * 2 * (K * δ n) *
          (‖h - minNormSolution V‖ / s + K * δ n)) ≤
          (36 * s ^ 2 * (K ^ 2 + K)) *
            (δ n * ‖h - minNormSolution V‖ + δ n ^ 2) := by
        have hh := mul_le_mul_of_nonneg_left hdiv
          (show 0 ≤ 36 * s ^ 2 * K * δ n by positivity)
        have hx : 0 ≤ K ^ 2 * (δ n * ‖h - minNormSolution V‖) := by positivity
        have hy : 0 ≤ K * δ n ^ 2 := by positivity
        nlinarith only [hh, mul_nonneg (sq_nonneg s) hx, mul_nonneg (sq_nonneg s) hy]
      exact hmain.trans (mul_le_mul_of_nonneg_right
        (by
          have hsmallC : 0 ≤ 2 * s ^ 2 / c2 := by positivity
          dsimp [C]
          linarith only [hsmallC] : 36 * s ^ 2 * (K ^ 2 + K) ≤ C)
        (by positivity))
  · -- The finite initial segment 2*c2*n <= 1 is handled by the common
    -- bounded fitting event S and the n^(-1/2) floor. The added 2*s^2/c2
    -- in C dominates the deterministic squared-loss deviation there.
    sorry

-/

end Papers.TsAdaptiveEstimationInference

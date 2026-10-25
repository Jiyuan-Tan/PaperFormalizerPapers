module
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVSetup
public import Papers.TsAdaptiveEstimationInference.Helpers.IterRDIVJointFitting
public import Papers.TsAdaptiveEstimationInference.Helpers.IterRDIVBounded
public import Papers.TsAdaptiveEstimationInference.Helpers.IterRDIVBoundedFitting
/-! Exact iteration-grid radius specialization for recursive RDIV concentration.
The raw curves are evaluated at their prescribed quarter budgets. Radius
inflation never compares values at different confidence arguments. -/
public section
set_option linter.style.longLine false
set_option linter.style.haveILetI false
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory
variable {W X Z : Type*} [MeasurableSpace W] [MeasurableSpace X] [MeasurableSpace Z]

/-- If [the confidence level lies strictly between zero and one](hyp:hξ) and [the iteration
horizon is at least one](hyp:ht), then [dividing confidence by four times the horizon
still gives a number strictly between zero and one, and its ordinary grid confidence
equals one quarter of the iteration-grid confidence](goal). -/
-- @node: iter_rdiv_quarter_budget
lemma iter_rdiv_quarter_budget (ρ ξ : ℝ) (n t : ℕ)
    (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1) (ht : 1 ≤ t) :
    ξ / (4 * t) ∈ Set.Ioo (0 : ℝ) 1 ∧
      gridConfidence ρ (ξ / (4 * t)) n = iterGridConfidence ρ ξ n t / 4 := by
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  constructor
  · constructor
    · exact div_pos hξ.1 (by positivity)
    · apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 4 * t)).2
      linarith only [hξ.2, htR]
  · unfold gridConfidence iterGridConfidence
    simp only [Nat.cast_mul, div_eq_mul_inv, mul_inv_rev]
    ring

/-- Suppose [the raw density curve bounds density critical radii](hyp:hG), [the raw hypothesis
curve bounds primal and density-transformed critical radii](hyp:hH), and [the raw curves
dominate their confidence floors](hyp:hFloor). Then [a population multiplier of at least
one makes every valid calibrated inflated fitting accuracy positive, at least the raw
hypothesis radius, large enough to dominate the confidence floor up to that multiplier,
and a critical-radius bound for both the primal class and every density-transformed class
at each positive sample size](goal). -/
-- @node: iter_rdiv_calibrated_radii
lemma iter_rdiv_calibrated_radii (V : IVWorld W X Z)
    (mu : Measure X) (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (ρ : ℝ) (rawG rawH rawR : ℕ → ℝ → ℝ)
    (hG : DensityCriticalRadiusBound V G g₀ rawG)
    (hH : HypothesisCriticalRadiusBound V mu G rawH ρ)
    (hFloor : RDIVRadiusFloor rawG rawH ρ) :
    ∃ K ≥ (1 : ℝ), ∀ (ξ : ℝ) (t : ℕ) (δ ν baseδ baseν : ℕ → ℝ)
      (κδ κν required : ℝ), ξ ∈ Set.Ioo (0 : ℝ) 1 →
      RDIVScaleCalibration ρ ξ baseδ baseν rawG rawH rawR t →
      CalibratedValidBounds δ ν baseδ baseν κδ κν required →
      ∀ n, 0 < n →
      0 < δ n ∧ rawH n (iterGridConfidence ρ ξ n t / 4) ≤ δ n ∧
      confidenceFloor n (iterGridConfidence ρ ξ n t / 4) ≤ K * δ n ∧
      IsCriticalRadiusBound (V.law.map V.xOf) (primalVersion V '' V.H) n (δ n) ∧
      (∀ g ∈ G, IsCriticalRadiusBound (V.law.map V.zOf)
        (densityOperator mu g '' (primalVersion V '' V.H)) n (δ n)) := by
  obtain ⟨c, hc, hfloor⟩ := hFloor
  let K := max 1 c⁻¹
  refine ⟨K, le_max_left _ _, ?_⟩
  intro ξ t δ ν baseδ baseν κδ κν required hξ hScale hInflate n hn
  obtain ⟨hbudget, heq⟩ := iter_rdiv_quarter_budget ρ ξ n t hξ hScale.1
  have hquarter : ξ / 4 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith only [hξ.1, hξ.2]
  obtain ⟨hx, hz⟩ := hH n hn _ hbudget
  rw [heq] at hx hz
  have hg := (hG n hn _ hquarter).1.le
  have hs := (hScale.2.1 n hn).1
  change rawG n (ξ / 4) + rawH n (iterGridConfidence ρ ξ n t / 4) +
    rdivPublicLogScale ρ ξ n ≤ baseδ n at hs
  have hh : rawH n (iterGridConfidence ρ ξ n t / 4) ≤ baseδ n := by
    have hl : 0 ≤ rdivPublicLogScale ρ ξ n := Real.sqrt_nonneg _
    linarith only [hs, hg, hl]
  have hb : 0 ≤ baseδ n := hx.1.le.trans hh
  have hd : baseδ n ≤ δ n := by
    rw [hInflate.2.2.2.2.1 n]
    nlinarith only [hInflate.1, hb]
  have hr := hh.trans hd
  have hp : 0 < δ n := hx.1.trans_le hr
  refine ⟨hp, hr, ?_, criticalRadiusBound_mono _ _ _ _ _ hx hr,
    fun g hg => criticalRadiusBound_mono _ _ _ _ _ (hz g hg) hr⟩
  have hf := (hfloor n hn _ hbudget).2
  rw [heq] at hf
  have hcf : c * confidenceFloor n (iterGridConfidence ρ ξ n t / 4) ≤ δ n :=
    hf.trans hr
  have hf' : confidenceFloor n (iterGridConfidence ρ ξ n t / 4) ≤ c⁻¹ * δ n := by
    apply (mul_le_mul_iff_right₀ hc).mp
    have he : c * (c⁻¹ * δ n) = δ n := by field_simp
    rw [he]
    simpa only [mul_comm] using hcf
  exact hf'.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hp.le)

/-- For [a positive concentration prefactor](hyp:hc₁), [a positive concentration decay
constant](hyp:hc₂), and [a positive confidence-floor multiplier](hyp:hA), [a positive
radius inflation exists such that, at every positive sample size and failure probability
in $(0,1/4]$, a nonnegative radius whose multiple dominates the confidence floor satisfies
the logarithmic tail requirement: the logarithm of twice the prefactor divided by failure
probability is at most the decay constant times sample size times squared inflated radius
divided by eight](goal). -/
-- @node: iter_rdiv_source_log_inflation
lemma iter_rdiv_source_log_inflation (c₁ c₂ A : ℝ)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hA : 0 < A) :
    ∃ K > 0, ∀ (n : ℕ) (η d : ℝ), 0 < n →
      η ∈ Set.Ioc (0 : ℝ) (1 / 4) → 0 ≤ d →
      confidenceFloor n η ≤ A * d →
      Real.log (2 * c₁ / η) ≤ c₂ * n * (K * d) ^ 2 / 8 := by
  let D := max (Real.log (2 * c₁)) 0
  let L := 1 + D / Real.log 4
  let K := Real.sqrt (8 * L * A ^ 2 / c₂)
  have hfour : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hD : 0 ≤ D := le_max_right _ _
  have hL : 0 < L := by dsimp [L]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  have hKsq : c₂ * K ^ 2 = 8 * L * A ^ 2 := by
    dsimp [K]
    rw [Real.sq_sqrt (by positivity), mul_div_cancel₀ _ hc₂.ne']
  refine ⟨K, hK, ?_⟩
  intro n η d hn hη hd hf
  have hvalid : η ∈ Set.Ioo (0 : ℝ) 1 := ⟨hη.1, by linarith only [hη.2]⟩
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hlog := confidenceFloor_log_le n η hn hvalid
  have hsq : confidenceFloor n η ^ 2 ≤ A ^ 2 * d ^ 2 := by
    have hnonneg : 0 ≤ confidenceFloor n η := Real.sqrt_nonneg _
    have hs := pow_le_pow_left₀ hnonneg hf 2
    rw [mul_pow] at hs
    exact hs
  have hbound : Real.log (1 / η) ≤ (n : ℝ) * (A ^ 2 * d ^ 2) :=
    hlog.trans (mul_le_mul_of_nonneg_left hsq hnR)
  have hinv : (4 : ℝ) ≤ 1 / η := (le_div_iff₀ hη.1).2 (by linarith only [hη.2])
  have hlogfour : Real.log 4 ≤ Real.log (1 / η) :=
    Real.log_le_log (by norm_num) hinv
  have hconst : D ≤ (D / Real.log 4) * Real.log (1 / η) := by
    have hm := mul_le_mul_of_nonneg_left hlogfour (div_nonneg hD hfour.le)
    simpa only [div_mul_cancel₀ _ hfour.ne'] using hm
  have htotal : Real.log (2 * c₁ / η) ≤ L * ((n : ℝ) * (A ^ 2 * d ^ 2)) := by
    rw [show 2 * c₁ / η = (2 * c₁) * (1 / η) by ring,
      Real.log_mul (by positivity) (by positivity)]
    have hc := le_max_left (Real.log (2 * c₁)) 0
    have hm := mul_le_mul_of_nonneg_left hbound (div_nonneg hD hfour.le)
    dsimp [L]
    nlinarith only [hc, hconst, hbound, hm]
  calc
    _ ≤ L * ((n : ℝ) * (A ^ 2 * d ^ 2)) := htotal
    _ = c₂ * n * (K * d) ^ 2 / 8 := by
      calc
        _ = (c₂ * K ^ 2) * n * d ^ 2 / 8 := by rw [hKsq]; ring
        _ = _ := by ring

/-- For [a positive concentration prefactor](hyp:hc₁), [a positive decay constant](hyp:hc₂),
and [a positive confidence-floor multiplier](hyp:hA), [one inflation factor of at least
one makes every nonnegative radius dominating the confidence floor up to that multiplier
satisfy both the iterated-logarithm peeling lower bound on squared radius and the
logarithmic tail requirement, for sample sizes at least two and failure probabilities
in $(0,1/4]$](goal). -/
-- @node: iter_rdiv_source_radius_conditions
lemma iter_rdiv_source_radius_conditions (c₁ c₂ A : ℝ)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hA : 0 < A) :
    ∃ K ≥ (1 : ℝ), ∀ (n : ℕ) (η d : ℝ), 2 ≤ n →
      η ∈ Set.Ioc (0 : ℝ) (1 / 4) → 0 ≤ d →
      confidenceFloor n η ≤ A * d →
      8 * Real.log (41 * Real.log (2 * c₂ * n)) / (c₂ * n) ≤ (K * d) ^ 2 ∧
      Real.log (2 * c₁ / η) ≤ c₂ * n * (K * d) ^ 2 / 8 := by
  obtain ⟨Kp, hKp, hp⟩ := localizedPeelingRadius c₂ A⁻¹ 2 hc₂
    (inv_pos.mpr hA) (by norm_num)
  obtain ⟨Kt, hKt, ht⟩ := iter_rdiv_source_log_inflation c₁ c₂ A hc₁ hc₂ hA
  let K := max Kp Kt
  refine ⟨K, hKp.trans (le_max_left _ _), ?_⟩
  intro n η d hn hη hd hf
  have hvalid : η ∈ Set.Ioo (0 : ℝ) 1 := ⟨hη.1, by linarith only [hη.2]⟩
  have hfloor : A⁻¹ * confidenceFloor n η ≤ d := by
    have hm := mul_le_mul_of_nonneg_left hf (inv_nonneg.mpr hA.le)
    simpa only [← mul_assoc, inv_mul_cancel₀ hA.ne', one_mul] using hm
  have hpsq : (Kp * d) ^ 2 ≤ (K * d) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right (le_max_left _ _) hd) 2
  have htsq : (Kt * d) ^ 2 ≤ (K * d) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hKt.le hd)
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hd) 2
  constructor
  · have hb := (hp n η d hn hvalid hfloor).trans hpsq
    norm_num only [Nat.cast_ofNat] at hb
    linarith only [hb]
  · exact (ht n η d (by omega) hη hd hf).trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left htsq (by positivity)) (by norm_num))

/-- For [a positive concentration decay constant](hyp:hc₂), [there is an integer sample
threshold of at least two beyond which twice the decay constant times sample size
is greater than one](goal). -/
-- @node: iter_rdiv_source_sample_threshold
lemma iter_rdiv_source_sample_threshold (c₂ : ℝ) (hc₂ : 0 < c₂) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → 1 < 2 * c₂ * n := by
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / (2 * c₂))
  refine ⟨max 2 m, le_max_left _ _, ?_⟩
  intro n hn
  have hmn : m ≤ n := (le_max_right 2 m).trans hn
  have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hdiv : 1 / (2 * c₂) < (n : ℝ) := hm.trans_le hmnR
  have hmul := (div_lt_iff₀ (by positivity : 0 < 2 * c₂)).mp hdiv
  nlinarith only [hmul]

variable {Ω : Type*} [MeasurableSpace Ω] (V : IVWorld W X Z)

/-- Assume [fixed-center loss concentration](hyp:hFix), [squared-loss concentration](hyp:hSq),
[a positive confidence-floor multiplier](hyp:hA), [the instrumental-variable model](hyp:hIV),
[density realizability](hyp:hDensity), [the density bounds](hyp:hBounds), [the outcome
bound](hyp:hY), and [the hypothesis-class bound](hyp:hHyp). Then [a population constant
and sample threshold give a measurable event of probability at least one minus half
the confidence level on which fixed-center loss-difference deviations are bounded by
the constant times radius times Hilbert distance plus squared radius, and empirical
distances by the constant times Hilbert distance plus radius, uniformly over admissible
grid penalties, iterations and class members, whenever density selection, measurability,
coherent versions, source scope, critical radii, confidence floors, and population-iterate
membership satisfy the indicated requirements](goal). -/
-- @node: iter_rdiv_calibrated_joint_fitting_event
lemma iter_rdiv_calibrated_joint_fitting_event
    (hFix : IterRDIVFixedCenterLocalizedConcentration (Ω := Ω) V)
    (hSq : IterRDIVSquaredLossLocalizedConcentration (Ω := Ω) V)
    (mu : Measure X) (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (support : Set (X × Z)) (B c₀ CG A : ℝ) (hA : 0 < A)
    (hIV : RDIVSetting V mu g₀) (hDensity : DensityRealizable V mu G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hY : OutcomeBounded V B) (hHyp : HypothesisClassBounded V support B) :
    ∃ K, 1 ≤ K ∧ ∃ N : ℕ, 2 ≤ N ∧
    ∀ (P : Measure Ω) (_hProbability : IsProbabilityMeasure P)
      (sample : AnalysisSample V P) (split : SampleSplit)
      (gHat : ℕ → Ω → X → Z → ℝ) (ρ ξ : ℝ),
    MLEMaximizerSelected V P sample split G gHat →
    RDIVClassesMeasurable V P sample split mu G g₀ gHat →
    IterRDIVFixedCenterSupremumVersion V P sample split mu gHat ρ →
    ∀ (n t : ℕ) (r : ℝ) (segment : Set ℝ) (sourceRadius : ℝ)
      (_hSourceScope : gridValue ρ (terminalIndex ρ n) ≤ sourceRadius ∧
        ∀ lam ∈ regGrid ρ n, lam ∈ segment → oraclePoint ρ n sourceRadius ≤ lam), N ≤ n → 1 ≤ t →
    ξ ∈ Set.Ioo (0 : ℝ) 1 → 0 < r →
    confidenceFloor n (iterGridConfidence ρ ξ n t / 4) ≤ A * r →
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
  obtain ⟨C, hC, cf₁, hcf₁, cf₂, hcf₂, cs₁, hcs₁, cs₂, hcs₂, hsource⟩ :=
    iter_rdiv_joint_fitting_iteration_grid_event V hFix hSq mu G g₀ support B c₀ CG
      hIV hDensity hBounds hY hHyp
  obtain ⟨Kf, hKf, hf⟩ := iter_rdiv_source_radius_conditions cf₁ cf₂ A hcf₁
      (by exact_mod_cast hcf₂) hA
  obtain ⟨Ks, hKs, hs⟩ := iter_rdiv_source_radius_conditions cs₁ cs₂ A hcs₁
      (by exact_mod_cast hcs₂) hA
  obtain ⟨Nf, hNf, hnf⟩ := iter_rdiv_source_sample_threshold cf₂ (by exact_mod_cast hcf₂)
  obtain ⟨Ns, hNs, hns⟩ := iter_rdiv_source_sample_threshold cs₂ (by exact_mod_cast hcs₂)
  let M := max Kf Ks
  have hM : 1 ≤ M := hKf.trans (le_max_left _ _)
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  let K := C * M ^ 2
  have hM2 : 1 ≤ M ^ 2 := by nlinarith only [hM]
  have hK : 1 ≤ K := one_le_mul_of_one_le_of_one_le hC hM2
  refine ⟨K, hK, max Nf Ns, hNf.trans (le_max_left _ _), ?_⟩
  intro P hProbability sample split gHat ρ ξ hMLE hMeas hVersion n t r segment sourceRadius hSourceScope
    hn ht hξ hr hfloor hradX hradZ hdom hstar
  have hn₂ : 2 ≤ n := hNf.trans ((le_max_left Nf Ns).trans hn)
  have hn₀ : 0 < n := by omega
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hkR : (1 : ℝ) ≤ (terminalIndex ρ n + 1 : ℕ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  have hden : 1 ≤ (t : ℝ) * (terminalIndex ρ n + 1 : ℕ) := by nlinarith
  have hη : iterGridConfidence ρ ξ n t ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · unfold iterGridConfidence
      positivity [hξ.1]
    · unfold iterGridConfidence
      rw [Nat.cast_mul]
      apply (div_lt_iff₀ (by positivity)).2
      simpa only [one_mul] using hξ.2.trans_le hden
  have hquarter : iterGridConfidence ρ ξ n t / 4 ∈ Set.Ioc (0 : ℝ) (1 / 4) := by
    constructor <;> linarith only [hη.1, hη.2]
  obtain ⟨hffloor, hflog⟩ := hf n _ r hn₂ hquarter hr.le hfloor
  obtain ⟨hsfloor, hslog⟩ := hs n _ r hn₂ hquarter hr.le hfloor
  have heq (c : ℝ) : 2 * c / (iterGridConfidence ρ ξ n t / 4) =
      8 * c / iterGridConfidence ρ ξ n t := by ring
  rw [heq] at hflog hslog
  have hfsq : (Kf * r) ^ 2 ≤ (M * r) ^ 2 :=
    pow_le_pow_left₀ (by positivity)
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hr.le) 2
  have hssq : (Ks * r) ^ 2 ≤ (M * r) ^ 2 :=
    pow_le_pow_left₀ (by positivity)
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hr.le) 2
  have hrM : r ≤ M * r := by nlinarith only [hM, hr.le]
  have hscalarfloor :
      4 * Real.log (41 * Real.log (2 * cs₂ * n)) / (cs₂ * n) ≤ (M * r) ^ 2 := by
    have hb := hsfloor.trans hssq
    have hsq := sq_nonneg (M * r)
    have he : 4 * Real.log (41 * Real.log (2 * cs₂ * n)) / (cs₂ * n) =
        (8 * Real.log (41 * Real.log (2 * cs₂ * n)) / (cs₂ * n)) / 2 := by ring
    rw [he]
    linarith only [hb, hsq]
  have hscalartail : Real.log (8 * cs₁ / iterGridConfidence ρ ξ n t) ≤
      cs₂ * n * (M * r) ^ 2 / 4 := by
    have hm := mul_le_mul_of_nonneg_left hssq
      (show (0 : ℝ) ≤ (cs₂ : ℝ) * n by positivity)
    have hnonneg : 0 ≤ cs₂ * n * (M * r) ^ 2 := by positivity
    linarith only [hslog, hm, hnonneg]
  obtain ⟨E, hE, hpE, hgood⟩ := hsource P hProbability sample split gHat ρ ξ
    hMLE hMeas hVersion n t (M * r) segment sourceRadius hSourceScope hn₀ ht hξ (by positivity)
    (by exact_mod_cast hnf n ((le_max_left _ _).trans hn)) (hffloor.trans hfsq)
    (hflog.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hfsq (by positivity)) (by norm_num)))
    (by exact_mod_cast hns n ((le_max_right _ _).trans hn)) hscalarfloor hscalartail
    (criticalRadiusBound_mono _ _ _ _ _ hradX hrM)
    (fun g hg => criticalRadiusBound_mono _ _ _ _ _ (hradZ g hg) hrM) hdom hstar
  refine ⟨E, hE, hpE, ?_⟩
  intro ω hω lam hl hseg j hj hjt h hh
  obtain ⟨hdev, hnorm⟩ := hgood ω hω lam hl hseg j hj hjt h hh
  have hMle : M ≤ M ^ 2 := by nlinarith only [hM]
  have hnorm0 : 0 ≤ ‖h - populationIterate V lam j‖ := norm_nonneg _
  have hCr : 0 ≤ C := by linarith only [hC]
  constructor
  · apply hdev.trans
    dsimp only [K]
    have hm := mul_le_mul_of_nonneg_left hMle
      (mul_nonneg hr.le hnorm0)
    have hc := mul_le_mul_of_nonneg_left hm hCr
    nlinarith only [hc]
  · apply hnorm.trans
    dsimp only [K]
    have hm := mul_le_mul_of_nonneg_left hMle hr.le
    have hu := mul_le_mul_of_nonneg_right hM2 hnorm0
    have hc := mul_le_mul_of_nonneg_left (add_le_add hu hm) hCr
    nlinarith only [hc]


/-- If [the smaller recursion constant is at least one](hyp:hC) and [does not exceed the
larger recursion constant](hyp:hCD), then [every stability coefficient computed with
the smaller constant is at most its counterpart computed with the larger constant](goal). -/
-- @node: iterRdivStabilityCoefficients_mono
lemma iterRdivStabilityCoefficients_mono (C D : ℝ) (hC : 1 ≤ C) (hCD : C ≤ D)
    (j : ℕ) : iterRdivStabilityCoefficients C j ≤ iterRdivStabilityCoefficients D j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change C * (1 + iterRdivStabilityCoefficients C j) ≤
      D * (1 + iterRdivStabilityCoefficients D j)
    exact mul_le_mul hCD (add_le_add_right ih 1)
      (by linarith only [(iterRdivStabilityCoefficients_bounds C hC).2.1 j])
      (by linarith only [hC, hCD])

/-- Assume [fixed-center loss concentration](hyp:hFix), [squared-loss concentration](hyp:hSq),
[a positive confidence-floor multiplier](hyp:hA), [a nonnegative density-error coefficient](hyp:hC),
[the instrumental-variable model](hyp:hIV), [the range condition](hyp:hRange), [density
realizability](hyp:hDensity), [the density bounds](hyp:hBounds), [the outcome bound](hyp:hY),
and [the hypothesis-class bound](hyp:hHyp). Then [population recursion and deviation
constants give a measurable event of probability at least one minus half the confidence
level, retaining loss-difference bounds at the critical radius and recursive weighted and
Hilbert fitting-error bounds at any larger radius whenever the selected density's
Hellinger error is at most the density-error coefficient times that larger radius squared,
under the selection, measurability, version, source-scope, confidence-floor, critical-radius,
penalty, population-membership and empirical-minimization requirements](goal). -/
-- @node: iter_rdiv_uniform_fitting_stability_two_radii_event
lemma iter_rdiv_uniform_fitting_stability_two_radii_event
    (hFix : IterRDIVFixedCenterLocalizedConcentration (Ω := Ω) V)
    (hSq : IterRDIVSquaredLossLocalizedConcentration (Ω := Ω) V)
    (mu : Measure X) (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (support : Set (X × Z)) (B c₀ CG A C : ℝ) (hA : 0 < A) (hC : 0 ≤ C)
    (hIV : RDIVSetting V mu g₀) (hRange : RangeCondition V)
    (hDensity : DensityRealizable V mu G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hY : OutcomeBounded V B) (hHyp : HypothesisClassBounded V support B) :
    ∃ D ≥ (1 : ℝ), ∃ Kret ≥ (1 : ℝ),
    ∀ (P : Measure Ω) (_hProbability : IsProbabilityMeasure P)
      (sample : AnalysisSample V P) (split : SampleSplit)
      (gHat : ℕ → Ω → X → Z → ℝ) (ρ ξ : ℝ),
    MLEMaximizerSelected V P sample split G gHat →
    RDIVClassesMeasurable V P sample split mu G g₀ gHat →
    IterRDIVFixedCenterSupremumVersion V P sample split mu gHat ρ →
    ∀ (n t : ℕ) (r d : ℝ) (segment : Set ℝ) (sourceRadius : ℝ)
      (_hSourceScope : gridValue ρ (terminalIndex ρ n) ≤ sourceRadius ∧
        ∀ lam ∈ regGrid ρ n, lam ∈ segment → oraclePoint ρ n sourceRadius ≤ lam)
      (iter : ℕ → ℝ → Ω → V.Hbar.toSubmodule),
    0 < n → 1 ≤ t → ξ ∈ Set.Ioo (0 : ℝ) 1 → 0 < r → r ≤ d →
    1 / (n : ℝ) ≤ r ^ 2 →
    confidenceFloor n (iterGridConfidence ρ ξ n t / 4) ≤ A * r →
    IsCriticalRadiusBound (V.law.map V.xOf) (primalVersion V '' V.H) n r →
    (∀ g ∈ G, IsCriticalRadiusBound (V.law.map V.zOf)
      (densityOperator mu g '' (primalVersion V '' V.H)) n r) →
    (∀ lam ∈ regGrid ρ n, lam ∈ segment → lam ∈ Set.Ioc (0 : ℝ) 2) →
    (∀ lam ∈ regGrid ρ n, lam ∈ segment → ∀ j, 1 ≤ j → j ≤ t →
      populationIterate V lam j ∈ V.H) →
    (∀ lam ∈ regGrid ρ n, lam ∈ segment →
      IsEmpiricalIterate V (rdivEmpiricalLoss V P sample split mu gHat n)
        (primalEmpDistanceSq V P sample split n) (fun j => iter j lam) t lam) →
    ∃ E : Set Ω, MeasurableSet E ∧ 1 - ξ / 2 ≤ P.real E ∧
      (∀ ω ∈ E, gHat n ω ∈ G →
      (∫ z, hellingerSqDensity mu (fun x => gHat n ω x z) (fun x => g₀ x z)
        ∂V.law.map V.zOf) ≤ C * d ^ 2 →
      ∀ lam ∈ regGrid ρ n, lam ∈ segment → ∀ j, 1 ≤ j → j ≤ t →
        lam * ‖iter j lam ω - populationIterate V lam j‖ ^ 2 +
            ‖projCondExpOp V (iter j lam ω - populationIterate V lam j)‖ ^ 2 ≤
          iterRdivStabilityCoefficients D j * d ^ 2 / lam ∧
        ‖iter j lam ω - populationIterate V lam j‖ ^ 2 ≤
          iterRdivStabilityCoefficients D j * d ^ 2 / lam ^ 2) ∧
      ∀ ω ∈ E, ∀ lam ∈ regGrid ρ n, lam ∈ segment → ∀ j, 1 ≤ j → j ≤ t →
        ∀ h ∈ V.H,
        |blockAverage V P sample (split.fit n)
            (fun w => iterRdivFixedCenterLoss V mu (gHat n ω) lam j h w -
              iterRdivFixedCenterLoss V mu (gHat n ω) lam j
                (populationIterate V lam j) w) ω -
          ∫ w, iterRdivFixedCenterLoss V mu (gHat n ω) lam j h w -
            iterRdivFixedCenterLoss V mu (gHat n ω) lam j
              (populationIterate V lam j) w ∂V.law| ≤
          Kret * (r * ‖h - populationIterate V lam j‖ + r ^ 2) := by
  obtain ⟨K, hK, N, hN, hfit⟩ := iter_rdiv_calibrated_joint_fitting_event V
    hFix hSq mu G g₀ support B c₀ CG A hA hIV hDensity hBounds hY hHyp
  let L := max K (4 * B * (Real.sqrt (2 * (CG / c₀ + 1)) * Real.sqrt C) +
    2 * (2 * B * Real.sqrt C) + K)
  let Q := 64 * L ^ 4 + 24 * L ^ 2 + 4 * L + 1
  let D := max Q (24 * B ^ 2 * N)
  have hL : 1 ≤ L := hK.trans (le_max_left _ _)
  have hQ : 1 ≤ Q := by
    dsimp [Q]
    nlinarith only [sq_nonneg (L ^ 2), sq_nonneg L, hL]
  have hD : 1 ≤ D := hQ.trans (le_max_left _ _)
  let Kret := max K (24 * B ^ 2 * N)
  have hKret : 1 ≤ Kret := hK.trans (le_max_left _ _)
  refine ⟨D, hD, Kret, hKret, ?_⟩
  intro P hProbability sample split gHat ρ ξ hMLE hMeas hVersion n t r d segment sourceRadius hSourceScope iter
    hn ht hξ hr hrd hfloor hconfidence hradX hradZ hdom hstar hEst
  letI : IsProbabilityMeasure P := hProbability
  have hd : 0 < d := hr.trans_le hrd
  have hsquares : r ^ 2 ≤ d ^ 2 := pow_le_pow_left₀ hr.le hrd 2
  by_cases hnN : N ≤ n
  · obtain ⟨E, hE, hpE, hgood⟩ := hfit P hProbability sample split gHat ρ ξ
      hMLE hMeas hVersion n t r segment sourceRadius hSourceScope hnN ht hξ hr hconfidence hradX hradZ hdom hstar
    refine ⟨E, hE, hpE, ?_, ?_⟩
    · intro ω hω hg hrate lam hl hs j hj hjt
      have hb := iter_rdiv_stability_of_density_and_deviations V P sample split
        mu G g₀ gHat support B c₀ CG C K d lam n t ω (fun j => iter j lam)
        hIV hRange hDensity hBounds hHyp hY hg hC hK hd.le (hdom lam hl hs)
        hrate (hEst lam hl hs) (hstar lam hl hs)
        (fun j hj hjt h hh => by
          obtain ⟨hdev, hnorm⟩ := hgood ω hω lam hl hs j hj hjt h hh
          constructor
          · exact hdev.trans (mul_le_mul_of_nonneg_left
              (add_le_add (mul_le_mul_of_nonneg_right hrd (norm_nonneg _)) hsquares)
              (by linarith only [hK]))
          · exact hnorm.trans (mul_le_mul_of_nonneg_left
              (add_le_add le_rfl hrd) (by linarith only [hK]))) j hj hjt
      change _ ≤ iterRdivStabilityCoefficients Q j * d ^ 2 / lam ∧
        _ ≤ iterRdivStabilityCoefficients Q j * d ^ 2 / lam ^ 2 at hb
      have hm := mul_le_mul_of_nonneg_right
        (iterRdivStabilityCoefficients_mono Q D hQ (le_max_left _ _) j) (sq_nonneg d)
      exact ⟨hb.1.trans (div_le_div_of_nonneg_right hm (hdom lam hl hs).1.le),
        hb.2.trans (div_le_div_of_nonneg_right hm (sq_nonneg lam))⟩
    · intro ω hω lam hl hs j hj hjt h hh
      exact (hgood ω hω lam hl hs j hj hjt h hh).1.trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · obtain ⟨E, hE, hpE, hgood⟩ := iter_rdiv_bounded_fixed_center_iteration_grid_event
      V P sample split mu G g₀ gHat support B c₀ CG ρ ξ r n N t segment
      hIV hDensity hBounds hHyp hY hMLE hVersion hn (by omega) ht hξ hfloor hdom hstar
    refine ⟨E, hE, by linarith only [hpE, hξ.1], ?_, ?_⟩
    · intro ω hω hg hrate lam hl hs j hj hjt
      exact iter_rdiv_bounded_iterate_stability V P sample split mu G g₀ gHat support
        B c₀ CG d D n N t iter (regGrid ρ n ∩ segment) hIV hDensity hBounds hHyp
        hY.1 hn (by omega) (hfloor.trans hsquares) hD (le_max_right _ _)
        (fun lam hl => hdom lam hl.1 hl.2)
        (fun lam hl => hEst lam hl.1 hl.2)
        (fun lam hl => hstar lam hl.1 hl.2) ω lam ⟨hl, hs⟩ j hj hjt
    · intro ω hω lam hl hs j hj hjt h hh
      apply (hgood ω hω lam hl hs j hj hjt h hh).trans
      calc
        _ ≤ Kret * r ^ 2 := mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg r)
        _ ≤ Kret * (r * ‖h - populationIterate V lam j‖ + r ^ 2) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) (by linarith)

/-- Assume [fixed-center loss concentration](hyp:hFix), [squared-loss concentration](hyp:hSq),
[a positive confidence-floor multiplier](hyp:hA), [a nonnegative density-error coefficient](hyp:hC),
[the instrumental-variable model](hyp:hIV), [the range condition](hyp:hRange), [density
realizability](hyp:hDensity), [the density bounds](hyp:hBounds), [the outcome bound](hyp:hY),
and [the hypothesis-class bound](hyp:hHyp). Then [population constants give one measurable
event of probability at least one minus half the confidence level retaining all fixed-center
loss-difference deviation bounds and recursive weighted and Hilbert fitting-error bounds
at the same radius, the latter conditional on density membership and the Hellinger error
bound, whenever the selection, measurability, version, source-scope, radius, penalty,
population-membership and empirical-minimization requirements hold](goal). -/
-- @node: iter_rdiv_uniform_fitting_stability_retained_event
lemma iter_rdiv_uniform_fitting_stability_retained_event
    (hFix : IterRDIVFixedCenterLocalizedConcentration (Ω := Ω) V)
    (hSq : IterRDIVSquaredLossLocalizedConcentration (Ω := Ω) V)
    (mu : Measure X) (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (support : Set (X × Z)) (B c₀ CG A C : ℝ) (hA : 0 < A) (hC : 0 ≤ C)
    (hIV : RDIVSetting V mu g₀) (hRange : RangeCondition V)
    (hDensity : DensityRealizable V mu G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hY : OutcomeBounded V B) (hHyp : HypothesisClassBounded V support B) :
    ∃ D ≥ (1 : ℝ), ∃ Kret ≥ (1 : ℝ),
    ∀ (P : Measure Ω) (_hProbability : IsProbabilityMeasure P)
      (sample : AnalysisSample V P) (split : SampleSplit)
      (gHat : ℕ → Ω → X → Z → ℝ) (ρ ξ : ℝ),
    MLEMaximizerSelected V P sample split G gHat →
    RDIVClassesMeasurable V P sample split mu G g₀ gHat →
    IterRDIVFixedCenterSupremumVersion V P sample split mu gHat ρ →
    ∀ (n t : ℕ) (r : ℝ) (segment : Set ℝ) (sourceRadius : ℝ)
      (_hSourceScope : gridValue ρ (terminalIndex ρ n) ≤ sourceRadius ∧
        ∀ lam ∈ regGrid ρ n, lam ∈ segment → oraclePoint ρ n sourceRadius ≤ lam)
      (iter : ℕ → ℝ → Ω → V.Hbar.toSubmodule),
    0 < n → 1 ≤ t → ξ ∈ Set.Ioo (0 : ℝ) 1 → 0 < r →
    1 / (n : ℝ) ≤ r ^ 2 →
    confidenceFloor n (iterGridConfidence ρ ξ n t / 4) ≤ A * r →
    IsCriticalRadiusBound (V.law.map V.xOf) (primalVersion V '' V.H) n r →
    (∀ g ∈ G, IsCriticalRadiusBound (V.law.map V.zOf)
      (densityOperator mu g '' (primalVersion V '' V.H)) n r) →
    (∀ lam ∈ regGrid ρ n, lam ∈ segment → lam ∈ Set.Ioc (0 : ℝ) 2) →
    (∀ lam ∈ regGrid ρ n, lam ∈ segment → ∀ j, 1 ≤ j → j ≤ t →
      populationIterate V lam j ∈ V.H) →
    (∀ lam ∈ regGrid ρ n, lam ∈ segment →
      IsEmpiricalIterate V (rdivEmpiricalLoss V P sample split mu gHat n)
        (primalEmpDistanceSq V P sample split n) (fun j => iter j lam) t lam) →
    ∃ E : Set Ω, MeasurableSet E ∧ 1 - ξ / 2 ≤ P.real E ∧
      (∀ ω ∈ E, gHat n ω ∈ G →
      (∫ z, hellingerSqDensity mu (fun x => gHat n ω x z) (fun x => g₀ x z)
        ∂V.law.map V.zOf) ≤ C * r ^ 2 →
      ∀ lam ∈ regGrid ρ n, lam ∈ segment → ∀ j, 1 ≤ j → j ≤ t →
        lam * ‖iter j lam ω - populationIterate V lam j‖ ^ 2 +
            ‖projCondExpOp V (iter j lam ω - populationIterate V lam j)‖ ^ 2 ≤
          iterRdivStabilityCoefficients D j * r ^ 2 / lam ∧
        ‖iter j lam ω - populationIterate V lam j‖ ^ 2 ≤
          iterRdivStabilityCoefficients D j * r ^ 2 / lam ^ 2) ∧
      ∀ ω ∈ E, ∀ lam ∈ regGrid ρ n, lam ∈ segment → ∀ j, 1 ≤ j → j ≤ t →
        ∀ h ∈ V.H,
        |blockAverage V P sample (split.fit n)
            (fun w => iterRdivFixedCenterLoss V mu (gHat n ω) lam j h w -
              iterRdivFixedCenterLoss V mu (gHat n ω) lam j
                (populationIterate V lam j) w) ω -
          ∫ w, iterRdivFixedCenterLoss V mu (gHat n ω) lam j h w -
            iterRdivFixedCenterLoss V mu (gHat n ω) lam j
              (populationIterate V lam j) w ∂V.law| ≤
          Kret * (r * ‖h - populationIterate V lam j‖ + r ^ 2) := by
  obtain ⟨D, hD, K, hK, hevent⟩ := iter_rdiv_uniform_fitting_stability_two_radii_event V
    hFix hSq mu G g₀ support B c₀ CG A C hA hC hIV hRange hDensity hBounds hY hHyp
  refine ⟨D, hD, K, hK, ?_⟩
  intro P hProbability sample split gHat ρ ξ hMLE hMeas hVersion n t r segment sourceRadius hSourceScope iter
    hn ht hξ hr hfloor hconfidence hx hz hdom hstar hEst
  exact hevent P hProbability sample split gHat ρ ξ hMLE hMeas hVersion n t r r
    segment sourceRadius hSourceScope iter hn ht hξ hr le_rfl hfloor hconfidence hx hz hdom hstar hEst

/-- Assume [fixed-center loss concentration](hyp:hFix), [squared-loss concentration](hyp:hSq),
[a positive confidence-floor multiplier](hyp:hA), [a nonnegative density-error coefficient](hyp:hC),
[the instrumental-variable model](hyp:hIV), [the range condition](hyp:hRange), [density
realizability](hyp:hDensity), [the density bounds](hyp:hBounds), [the outcome bound](hyp:hY),
and [the hypothesis-class bound](hyp:hHyp). Then [one population recursion constant gives,
under the selection, measurability, version, source-scope, radius, penalty,
population-membership and empirical-minimization requirements, a measurable event of
probability at least one minus half the confidence level on which density membership
and a Hellinger error bound imply weighted fitting error at most the iteration coefficient
times squared radius divided by penalty and Hilbert squared fitting error at most that
coefficient times squared radius divided by squared penalty, uniformly over the segment
and iteration horizon](goal). -/
-- @node: iter_rdiv_uniform_fitting_stability_event
lemma iter_rdiv_uniform_fitting_stability_event
    (hFix : IterRDIVFixedCenterLocalizedConcentration (Ω := Ω) V)
    (hSq : IterRDIVSquaredLossLocalizedConcentration (Ω := Ω) V)
    (mu : Measure X) (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (support : Set (X × Z)) (B c₀ CG A C : ℝ) (hA : 0 < A) (hC : 0 ≤ C)
    (hIV : RDIVSetting V mu g₀) (hRange : RangeCondition V)
    (hDensity : DensityRealizable V mu G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hY : OutcomeBounded V B) (hHyp : HypothesisClassBounded V support B) :
    ∃ D ≥ (1 : ℝ),
    ∀ (P : Measure Ω) (_hProbability : IsProbabilityMeasure P)
      (sample : AnalysisSample V P) (split : SampleSplit)
      (gHat : ℕ → Ω → X → Z → ℝ) (ρ ξ : ℝ),
    MLEMaximizerSelected V P sample split G gHat →
    RDIVClassesMeasurable V P sample split mu G g₀ gHat →
    IterRDIVFixedCenterSupremumVersion V P sample split mu gHat ρ →
    ∀ (n t : ℕ) (r : ℝ) (segment : Set ℝ) (sourceRadius : ℝ)
      (_hSourceScope : gridValue ρ (terminalIndex ρ n) ≤ sourceRadius ∧
        ∀ lam ∈ regGrid ρ n, lam ∈ segment → oraclePoint ρ n sourceRadius ≤ lam)
      (iter : ℕ → ℝ → Ω → V.Hbar.toSubmodule),
    0 < n → 1 ≤ t → ξ ∈ Set.Ioo (0 : ℝ) 1 → 0 < r →
    1 / (n : ℝ) ≤ r ^ 2 →
    confidenceFloor n (iterGridConfidence ρ ξ n t / 4) ≤ A * r →
    IsCriticalRadiusBound (V.law.map V.xOf) (primalVersion V '' V.H) n r →
    (∀ g ∈ G, IsCriticalRadiusBound (V.law.map V.zOf)
      (densityOperator mu g '' (primalVersion V '' V.H)) n r) →
    (∀ lam ∈ regGrid ρ n, lam ∈ segment → lam ∈ Set.Ioc (0 : ℝ) 2) →
    (∀ lam ∈ regGrid ρ n, lam ∈ segment → ∀ j, 1 ≤ j → j ≤ t →
      populationIterate V lam j ∈ V.H) →
    (∀ lam ∈ regGrid ρ n, lam ∈ segment →
      IsEmpiricalIterate V (rdivEmpiricalLoss V P sample split mu gHat n)
        (primalEmpDistanceSq V P sample split n) (fun j => iter j lam) t lam) →
    ∃ E : Set Ω, MeasurableSet E ∧ 1 - ξ / 2 ≤ P.real E ∧
      ∀ ω ∈ E, gHat n ω ∈ G →
      (∫ z, hellingerSqDensity mu (fun x => gHat n ω x z) (fun x => g₀ x z)
        ∂V.law.map V.zOf) ≤ C * r ^ 2 →
      ∀ lam ∈ regGrid ρ n, lam ∈ segment → ∀ j, 1 ≤ j → j ≤ t →
        lam * ‖iter j lam ω - populationIterate V lam j‖ ^ 2 +
            ‖projCondExpOp V (iter j lam ω - populationIterate V lam j)‖ ^ 2 ≤
          iterRdivStabilityCoefficients D j * r ^ 2 / lam ∧
        ‖iter j lam ω - populationIterate V lam j‖ ^ 2 ≤
          iterRdivStabilityCoefficients D j * r ^ 2 / lam ^ 2 := by
  obtain ⟨D, hD, Kret, hKret, hretained⟩ :=
    iter_rdiv_uniform_fitting_stability_retained_event V hFix hSq mu G g₀ support
      B c₀ CG A C hA hC hIV hRange hDensity hBounds hY hHyp
  refine ⟨D, hD, ?_⟩
  intro P hProbability sample split gHat ρ ξ hMLE hMeas hVersion n t r segment sourceRadius hSourceScope iter
    hn ht hξ hr hfloor hconfidence hradX hradZ hdom hstar hEst
  obtain ⟨E, hE, hpE, hgood, _hraw⟩ := hretained P hProbability sample split gHat ρ ξ
    hMLE hMeas hVersion n t r segment sourceRadius hSourceScope iter hn ht hξ hr hfloor hconfidence
    hradX hradZ hdom hstar hEst
  exact ⟨E, hE, hpE, hgood⟩

end Papers.TsAdaptiveEstimationInference

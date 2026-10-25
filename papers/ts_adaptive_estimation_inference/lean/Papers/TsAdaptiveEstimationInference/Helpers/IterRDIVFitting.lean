module
public import Papers.TsAdaptiveEstimationInference.Helpers.IterRDIVLoss
/-! Actual-sample fixed-center fitting events for iterative RDIV. The source
increment is reduced by conditional Jensen, transported using the recorded
coherent versions, and allocated over the finite iteration grid locally. -/
public section
set_option linter.style.longLine false
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory
open scoped ENNReal
variable {𝒲 X Z Ω : Type*} [MeasurableSpace 𝒲] [MeasurableSpace X]
  [MeasurableSpace Z] [MeasurableSpace Ω]
  (V : IVWorld 𝒲 X Z)

/-- Given [fixed-center localized concentration](hyp:hFix), [the RDIV
model](hyp:hIV), [density realizability](hyp:hDensity), [density
bounds](hyp:hBounds), [outcomes bounded by B](hyp:hY), and [hypotheses bounded
by B](hyp:hHyp), [positive constants can be chosen before sampling so that
likelihood selection, measurability, coherent versions, admissible grid and
population centers, critical-radius bounds, and logarithmic radius and tail
conditions yield a measurable fitting event of probability at least one minus
a quarter of the confidence allocation; uniformly over hypotheses, the centered
loss deviation is at most K times radius times population distance plus K times
squared radius](goal).

Conditional Jensen removes the fitted-operator coordinate from the cited
increment. Independence and actual-block coherence then yield a measurable event
for the original representatives. Source constants precede the experiment. -/
-- @node: iter_rdiv_fixed_center_fitting_event
lemma iter_rdiv_fixed_center_fitting_event
    (hFix : IterRDIVFixedCenterLocalizedConcentration (Ω := Ω) V)
    (mu : Measure X) (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (support : Set (X × Z)) (B c₀ CG : ℝ)
    (hIV : RDIVSetting V mu g₀) (hDensity : DensityRealizable V mu G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hY : OutcomeBounded V B) (hHyp : HypothesisClassBounded V support B) :
    ∃ K > 0, ∃ c₁ > 0, ∃ c₂ > 0,
    ∀ (P : Measure Ω) (_hProbability : IsProbabilityMeasure P)
      (sample : AnalysisSample V P) (split : SampleSplit)
      (gHat : ℕ → Ω → X → Z → ℝ) (ρ : ℝ),
    MLEMaximizerSelected V P sample split G gHat →
    RDIVClassesMeasurable V P sample split mu G g₀ gHat →
    IterRDIVFixedCenterSupremumVersion V P sample split mu gHat ρ →
    ∀ (n t j : ℕ) (lam r sourceRadius : ℝ)
      (_hSourceScope : gridValue ρ (terminalIndex ρ n) ≤ sourceRadius ∧
        oraclePoint ρ n sourceRadius ≤ lam) (η : ℝ), 0 < n → 1 ≤ t → 1 ≤ j → j ≤ t →
    lam ∈ regGrid ρ n → lam ∈ Set.Ioc (0 : ℝ) 2 →
    populationIterate V lam j ∈ V.H →
    (populationIterate V lam (j - 1) ∈ V.H ∨ j = 1) →
    0 < r → η ∈ Set.Ioo (0 : ℝ) 1 → 1 < 2 * c₂ * n →
    8 * Real.log (41 * Real.log (2 * c₂ * n)) / (c₂ * n) ≤ r ^ 2 →
    Real.log (8 * c₁ / η) ≤ c₂ * n * r ^ 2 / 8 →
    IsCriticalRadiusBound (V.law.map V.xOf) (primalVersion V '' V.H) n r →
    (∀ g ∈ G, IsCriticalRadiusBound (V.law.map V.zOf)
      (densityOperator mu g '' (primalVersion V '' V.H)) n r) →
    ∃ E : Set Ω, MeasurableSet E ∧ 1 - η / 4 ≤ P.real E ∧
      ∀ ω ∈ E, ∀ h ∈ V.H,
        |blockAverage V P sample (split.fit n)
            (fun w => iterRdivFixedCenterLoss V mu (gHat n ω) lam j h w -
              iterRdivFixedCenterLoss V mu (gHat n ω) lam j
                (populationIterate V lam j) w) ω -
          ∫ w, iterRdivFixedCenterLoss V mu (gHat n ω) lam j h w -
            iterRdivFixedCenterLoss V mu (gHat n ω) lam j
              (populationIterate V lam j) w ∂V.law| ≤
          K * (r * ‖h - populationIterate V lam j‖ + r ^ 2) := by
  obtain ⟨C, hC, c₁, hc₁, c₂, hc₂, hsource⟩ :=
    iter_rdiv_fixed_center_frozen_fitting_event V hFix mu G g₀ support B c₀ CG
      hIV hDensity hBounds hY hHyp
  let K := C * (Real.sqrt (CG / c₀) + 1)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, c₁, hc₁, c₂, hc₂, ?_⟩
  intro P hProbability sample split gHat ρ hMLE hMeas hVersion n t j lam r sourceRadius hSourceScope η
    hn ht hj hjt hlam hdom hstar hcenter hr hη hlarge hfloor hlog hradX hradZ
  let : IsProbabilityMeasure P := hProbability
  have htail : 2 * c₁ * Real.exp (-c₂ * n * r ^ 2 / 8) ≤ η / 4 := by
    have hb := iter_rdiv_source_tail_at_allocation c₁ (c₂ * n * r ^ 2 / 8)
      η hc₁ hη.1 hlog
    simpa only [neg_div, neg_mul] using hb
  have hfrozen := hsource P hProbability sample split gHat ρ hMLE hMeas hVersion
    n t j lam r sourceRadius hSourceScope hn hj hjt hlam hdom hstar hcenter hr hlarge hfloor hradX hradZ
  have hlocal : ∀ᵐ pre ∂P, 1 - η / 4 ≤ P.real {fit | ∀ h ∈ V.H,
      |blockAverage V P sample (split.fit n)
          (fun w => iterRdivFixedCenterLoss V mu (gHat n pre) lam j h w -
            iterRdivFixedCenterLoss V mu (gHat n pre) lam j
              (populationIterate V lam j) w) fit -
        ∫ w, iterRdivFixedCenterLoss V mu (gHat n pre) lam j h w -
          iterRdivFixedCenterLoss V mu (gHat n pre) lam j
            (populationIterate V lam j) w ∂V.law| ≤
        (K * r) * ‖h - populationIterate V lam j‖ + K * r ^ 2} := by
    filter_upwards [hfrozen, (hMLE n hn).1] with pre hp hg
    obtain ⟨E, hE, hpE, hgood⟩ := hp
    apply (show 1 - η / 4 ≤ P.real E by linarith only [hpE, htail]).trans
    apply measureReal_mono (h₂ := measure_ne_top P _)
    intro fit hfit h hh
    have hb := hgood fit hfit h hh
    dsimp only at hb
    rw [← iter_rdiv_fixed_center_deviation_eq_risks V P sample split mu G g₀ gHat
      support B c₀ CG n j pre fit lam hIV hDensity hBounds hHyp hY hg.1
      h (populationIterate V lam j) hh hstar] at hb
    have hcoord := rdiv_fitting_coordinate_bound V mu G g₀ (gHat n pre)
      support c₀ CG hIV hDensity hBounds hg.1 h (populationIterate V lam j)
    have hb' := hb.trans (mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add hcoord le_rfl) le_rfl)
      (mul_nonneg hC.le hr.le))
    dsimp only [K]
    nlinarith only [hb', mul_nonneg (mul_nonneg hC.le (Real.sqrt_nonneg (CG / c₀)))
      (sq_nonneg r)]
  obtain ⟨E, hE, hpE, hgood⟩ := iter_rdiv_thaw_fixed_center_deviations V P sample split
    mu gHat ρ n t j lam (K * r) (K * r ^ 2) (η / 4) hn ht hj hjt hlam
    (by positivity) (by positivity) (by constructor <;> linarith [hη.1, hη.2])
    hVersion hlocal
  refine ⟨E, hE, hpE, ?_⟩
  intro ω hω h hh
  have hb := hgood ω hω h hh
  nlinarith only [hb]

/-- Assume [fixed-center localized concentration](hyp:hFix), [the RDIV
model](hyp:hIV), [density realizability](hyp:hDensity), [density
bounds](hyp:hBounds), [the outcome envelope B](hyp:hY), and [the hypothesis
envelope B](hyp:hHyp). Then [positive constants chosen before sampling give,
under likelihood selection, measurability, coherent versions, critical-radius
and logarithmic floor conditions at the iteration-grid allocation, a measurable
event of probability at least one minus a quarter of the failure probability
on which all positive iterations through the horizon, all admissible penalties
in the grid segment, and all hypotheses satisfy the centered loss-deviation
bound K times radius times population distance plus K times squared radius](goal).

One actual-sample event controls the fixed-center increments on the entire
iteration--grid segment. The confidence curve is evaluated at its prescribed
allocation and the union consumes exactly the fitting quarter budget. -/
-- @node: iter_rdiv_fixed_center_iteration_grid_event
lemma iter_rdiv_fixed_center_iteration_grid_event
    (hFix : IterRDIVFixedCenterLocalizedConcentration (Ω := Ω) V)
    (mu : Measure X) (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (support : Set (X × Z)) (B c₀ CG : ℝ)
    (hIV : RDIVSetting V mu g₀) (hDensity : DensityRealizable V mu G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hY : OutcomeBounded V B) (hHyp : HypothesisClassBounded V support B) :
    ∃ K > 0, ∃ c₁ > 0, ∃ c₂ > 0,
    ∀ (P : Measure Ω) (_hProbability : IsProbabilityMeasure P)
      (sample : AnalysisSample V P) (split : SampleSplit)
      (gHat : ℕ → Ω → X → Z → ℝ) (ρ ξ : ℝ),
    MLEMaximizerSelected V P sample split G gHat →
    RDIVClassesMeasurable V P sample split mu G g₀ gHat →
    IterRDIVFixedCenterSupremumVersion V P sample split mu gHat ρ →
    ∀ (n t : ℕ) (r : ℝ) (segment : Set ℝ) (sourceRadius : ℝ)
      (_hSourceScope : gridValue ρ (terminalIndex ρ n) ≤ sourceRadius ∧
        ∀ lam ∈ regGrid ρ n, lam ∈ segment → oraclePoint ρ n sourceRadius ≤ lam), 0 < n → 1 ≤ t →
    ξ ∈ Set.Ioo (0 : ℝ) 1 → 0 < r → 1 < 2 * c₂ * n →
    8 * Real.log (41 * Real.log (2 * c₂ * n)) / (c₂ * n) ≤ r ^ 2 →
    Real.log (8 * c₁ / iterGridConfidence ρ ξ n t) ≤ c₂ * n * r ^ 2 / 8 →
    IsCriticalRadiusBound (V.law.map V.xOf) (primalVersion V '' V.H) n r →
    (∀ g ∈ G, IsCriticalRadiusBound (V.law.map V.zOf)
      (densityOperator mu g '' (primalVersion V '' V.H)) n r) →
    (∀ lam ∈ regGrid ρ n, lam ∈ segment → lam ∈ Set.Ioc (0 : ℝ) 2) →
    (∀ lam ∈ regGrid ρ n, lam ∈ segment → ∀ j, 1 ≤ j → j ≤ t →
      populationIterate V lam j ∈ V.H) →
    ∃ E : Set Ω, MeasurableSet E ∧ 1 - ξ / 4 ≤ P.real E ∧
      ∀ ω ∈ E, ∀ lam ∈ regGrid ρ n, lam ∈ segment → ∀ j, 1 ≤ j → j ≤ t →
        ∀ h ∈ V.H,
        |blockAverage V P sample (split.fit n)
            (fun w => iterRdivFixedCenterLoss V mu (gHat n ω) lam j h w -
              iterRdivFixedCenterLoss V mu (gHat n ω) lam j
                (populationIterate V lam j) w) ω -
          ∫ w, iterRdivFixedCenterLoss V mu (gHat n ω) lam j h w -
            iterRdivFixedCenterLoss V mu (gHat n ω) lam j
              (populationIterate V lam j) w ∂V.law| ≤
          K * (r * ‖h - populationIterate V lam j‖ + r ^ 2) := by
  obtain ⟨K, hK, c₁, hc₁, c₂, hc₂, hsource⟩ :=
    iter_rdiv_fixed_center_fitting_event V hFix mu G g₀ support B c₀ CG
      hIV hDensity hBounds hY hHyp
  refine ⟨K, hK, c₁, hc₁, c₂, hc₂, ?_⟩
  intro P hProbability sample split gHat ρ ξ hMLE hMeas hVersion n t r segment sourceRadius hSourceScope
    hn ht hξ hr hlarge hfloor hlog hradX hradZ hdom hstar
  let : IsProbabilityMeasure P := hProbability
  have hη : iterGridConfidence ρ ξ n t ∈ Set.Ioo (0 : ℝ) 1 := by
    have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
    have hkR : (1 : ℝ) ≤ (terminalIndex ρ n + 1 : ℕ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
    have hden : 1 ≤ (t : ℝ) * (terminalIndex ρ n + 1 : ℕ) := by nlinarith
    constructor
    · unfold iterGridConfidence
      positivity [hξ.1]
    · unfold iterGridConfidence
      rw [Nat.cast_mul]
      apply (div_lt_iff₀ (by positivity)).2
      simpa only [one_mul] using hξ.2.trans_le hden
  classical
  let good : ℕ → ℝ → Ω → Prop := fun j lam ω =>
    lam ∈ segment → ∀ h ∈ V.H,
      |blockAverage V P sample (split.fit n)
          (fun w => iterRdivFixedCenterLoss V mu (gHat n ω) lam j h w -
            iterRdivFixedCenterLoss V mu (gHat n ω) lam j
              (populationIterate V lam j) w) ω -
        ∫ w, iterRdivFixedCenterLoss V mu (gHat n ω) lam j h w -
          iterRdivFixedCenterLoss V mu (gHat n ω) lam j
            (populationIterate V lam j) w ∂V.law| ≤
        K * (r * ‖h - populationIterate V lam j‖ + r ^ 2)
  have hlocal : ∀ j ∈ Finset.Icc 1 t, ∀ lam ∈ regGrid ρ n,
      ∃ E : Set Ω, MeasurableSet E ∧
        1 - iterGridConfidence ρ ξ n t / 4 ≤ P.real E ∧
        ∀ ω ∈ E, good j lam ω := by
    intro j hj lam hl
    obtain ⟨hj₁, hjt⟩ := Finset.mem_Icc.mp hj
    by_cases hs : lam ∈ segment
    · have hcenter : populationIterate V lam (j - 1) ∈ V.H ∨ j = 1 := by
        by_cases hjone : j = 1
        · exact Or.inr hjone
        · exact Or.inl (hstar lam hl hs (j - 1) (by omega) (by omega))
      obtain ⟨E, hE, hpE, hgood⟩ := hsource P hProbability sample split gHat ρ
        hMLE hMeas hVersion n t j lam r sourceRadius ⟨hSourceScope.1, hSourceScope.2 lam hl hs⟩ (iterGridConfidence ρ ξ n t) hn ht hj₁ hjt
        hl (hdom lam hl hs) (hstar lam hl hs j hj₁ hjt) hcenter hr hη
        hlarge hfloor hlog hradX hradZ
      exact ⟨E, hE, hpE, fun ω hω _ => hgood ω hω⟩
    · refine ⟨Set.univ, MeasurableSet.univ, ?_, ?_⟩
      · simp only [measureReal_def, measure_univ, ENNReal.toReal_one]
        linarith [hη.1]
      · intro ω hω hs'
        exact (hs hs').elim
  choose F hF hpF hgood using hlocal
  let E : ℕ → ℝ → Set Ω := fun j lam =>
    if hj : j ∈ Finset.Icc 1 t then
      if hl : lam ∈ regGrid ρ n then F j hj lam hl else Set.univ
    else Set.univ
  have hEm : ∀ j ∈ Finset.Icc 1 t, ∀ lam ∈ regGrid ρ n, MeasurableSet (E j lam) := by
    intro j hj lam hl
    simpa only [E, dif_pos hj, dif_pos hl] using hF j hj lam hl
  have hEp : ∀ j ∈ Finset.Icc 1 t, ∀ lam ∈ regGrid ρ n,
      1 - iterGridConfidence ρ ξ n t / 4 ≤ P.real (E j lam) := by
    intro j hj lam hl
    simpa only [E, dif_pos hj, dif_pos hl] using hpF j hj lam hl
  obtain ⟨hm, hp⟩ := iter_rdiv_iteration_grid_event_budget P ρ ξ n t hξ.1.le ht E hEm hEp
  refine ⟨⋂ j ∈ Finset.Icc 1 t, ⋂ lam ∈ regGrid ρ n, E j lam, hm, hp, ?_⟩
  intro ω hω lam hl hs j hj hjt h hh
  have hj' : j ∈ Finset.Icc 1 t := Finset.mem_Icc.mpr ⟨hj, hjt⟩
  have hmem := Set.mem_iInter₂.mp (Set.mem_iInter₂.mp hω j hj') lam hl
  simp only [E, dif_pos hj', dif_pos hl] at hmem
  exact hgood j hj' lam hl ω hmem hs h hh

end Papers.TsAdaptiveEstimationInference

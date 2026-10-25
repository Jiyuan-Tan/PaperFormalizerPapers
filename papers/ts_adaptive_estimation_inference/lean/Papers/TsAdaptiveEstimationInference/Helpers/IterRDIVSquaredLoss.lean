module
public import Papers.TsAdaptiveEstimationInference.Helpers.IterRDIVConcentration
public import Papers.TsAdaptiveEstimationInference.Helpers.IterRDIVFixedCenter
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVFittingTransfer
/-! Fixed-comparator radius reduction and transport of the iterative squared-loss
source event to the actual fitting block. Confidence and radius inflation, finite
iteration-grid allocation, and the fitting-loss event remain separate obligations. -/
public section
set_option linter.style.longLine false
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- If [the fixed anchor belongs to the function class](hyp:hfstar) and [the
radius bounds the localized complexity of the difference class](hyp:hr), [the
same radius bounds the star hull of differences from that anchor](goal). -/
-- @node: iter_rdiv_anchored_radius_of_critical_radius
lemma iter_rdiv_anchored_radius_of_critical_radius {A : Type*} [MeasurableSpace A]
    (law : Measure A) (F : Set (A → ℝ)) (fstar : A → ℝ) (hfstar : fstar ∈ F)
    (n : ℕ) (r : ℝ) (hr : IsCriticalRadiusBound law F n r) :
    iterRdivAnchoredRadius law F fstar n r := by
  have hsub : {f ∈ starClass ((fun g => g - fstar) '' F) |
      eLpNorm f 2 law ≤ ENNReal.ofReal r} ⊆
      {f ∈ starClass (differenceClass F) |
        eLpNorm f 2 law ≤ ENNReal.ofReal r} := by
    intro f hf
    obtain ⟨a, ha, g, ⟨u, hu, rfl⟩, heq⟩ := hf.1
    exact ⟨⟨a, ha, u - fstar, ⟨u, hu, fstar, hfstar, rfl⟩, heq⟩, hf.2⟩
  apply le_trans (b := expectedRademacher law
    {f ∈ starClass (differenceClass F) | eLpNorm f 2 law ≤ ENNReal.ofReal r} n)
    ?_ hr.2
  apply lintegral_mono
  intro ws
  apply mul_le_mul_of_nonneg_left _ zero_le
  apply Finset.sum_le_sum
  intro ε _
  apply iSup_le
  intro f
  exact le_iSup_of_le (⟨f.1, hsub f.2⟩ :
    {f ∈ starClass (differenceClass F) | eLpNorm f 2 law ≤ ENNReal.ofReal r}) le_rfl

/-- If [the failure budget is nonnegative](hyp:hξ), [the iteration horizon is at
least one](hyp:ht), [each iteration-grid event is measurable](hyp:hE), and [each
has failure probability at most one quarter of its allocated grid
budget](hyp:hp), [their intersection is measurable and has failure probability
at most one quarter of the total budget](goal). -/
-- @node: iter_rdiv_iteration_grid_event_budget
lemma iter_rdiv_iteration_grid_event_budget {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ρ ξ : ℝ) (n t : ℕ)
    (hξ : 0 ≤ ξ) (ht : 1 ≤ t) (E : ℕ → ℝ → Set Ω)
    (hE : ∀ j ∈ Finset.Icc 1 t, ∀ lam ∈ regGrid ρ n, MeasurableSet (E j lam))
    (hp : ∀ j ∈ Finset.Icc 1 t, ∀ lam ∈ regGrid ρ n,
      1 - iterGridConfidence ρ ξ n t / 4 ≤ P.real (E j lam)) :
    MeasurableSet (⋂ j ∈ Finset.Icc 1 t, ⋂ lam ∈ regGrid ρ n, E j lam) ∧
      1 - ξ / 4 ≤ P.real (⋂ j ∈ Finset.Icc 1 t, ⋂ lam ∈ regGrid ρ n, E j lam) := by
  classical
  have hm : MeasurableSet (⋂ j ∈ Finset.Icc 1 t, ⋂ lam ∈ regGrid ρ n, E j lam) :=
    MeasurableSet.biInter (Finset.Icc 1 t).countable_toSet fun j hj =>
      MeasurableSet.biInter (regGrid ρ n).countable_toSet (hE j hj)
  refine ⟨hm, ?_⟩
  have hcard : (regGrid ρ n).card ≤ terminalIndex ρ n + 1 :=
    (Finset.card_image_le).trans_eq (Finset.card_range _)
  have hη : 0 ≤ iterGridConfidence ρ ξ n t / 4 := by
    unfold iterGridConfidence
    positivity
  have hbad : P.real (⋂ j ∈ Finset.Icc 1 t, ⋂ lam ∈ regGrid ρ n, E j lam)ᶜ ≤ ξ / 4 := by
    simp only [Set.compl_iInter]
    calc
      _ ≤ ∑ j ∈ Finset.Icc 1 t, P.real (⋃ lam ∈ regGrid ρ n, (E j lam)ᶜ) :=
        measureReal_biUnion_finset_le _ _
      _ ≤ ∑ j ∈ Finset.Icc 1 t, ∑ lam ∈ regGrid ρ n, P.real (E j lam)ᶜ := by
        apply Finset.sum_le_sum
        intro j hj
        exact measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _j ∈ Finset.Icc 1 t, ∑ _lam ∈ regGrid ρ n,
          iterGridConfidence ρ ξ n t / 4 := by
        apply Finset.sum_le_sum
        intro j hj
        apply Finset.sum_le_sum
        intro lam hlam
        linarith only [probReal_add_probReal_compl (μ := P) (hE j hj lam hlam),
          hp j hj lam hlam]
      _ = (t : ℝ) * ((regGrid ρ n).card * (iterGridConfidence ρ ξ n t / 4)) := by
        simp
      _ ≤ (t : ℝ) * ((terminalIndex ρ n + 1 : ℕ) *
          (iterGridConfidence ρ ξ n t / 4)) := by
        gcongr
      _ = ξ / 4 := by
        have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast (by omega : t ≠ 0)
        have hk0 : (terminalIndex ρ n + 1 : ℝ) ≠ 0 := by positivity
        unfold iterGridConfidence
        push_cast
        field_simp
  linarith only [probReal_add_probReal_compl (μ := P) hm, hbad]

variable {𝒲 X Z Ω : Type*} [MeasurableSpace 𝒲] [MeasurableSpace X]
  [MeasurableSpace Z] [MeasurableSpace Ω]
  (V : IVWorld 𝒲 X Z)

/-- Under [localized squared-loss concentration](hyp:hSq), [the RDIV model
assumptions](hyp:hIV), [density realizability](hyp:hDensity), [the density
bounds](hyp:hBounds), and [boundedness of the hypothesis class](hyp:hHyp),
[there are positive population constants such that every admissible measurable
sampling experiment, fixed population iterate, and critical radius satisfying
the source-scope, positivity, and logarithmic floor conditions admit a measurable
fitting event with the exponential source probability bound; on it every class
member's squared-distance deviation is at most the constant times the radius
times its distance plus the radius, and its empirical distance obeys the
corresponding norm envelope](goal). -/
-- @node: iter_rdiv_squared_loss_fitting_event
lemma iter_rdiv_squared_loss_fitting_event
    (hSq : IterRDIVSquaredLossLocalizedConcentration (Ω := Ω) V)
    (mu : Measure X) (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (support : Set (X × Z)) (B c₀ CG : ℝ)
    (hIV : RDIVSetting V mu g₀) (hDensity : DensityRealizable V mu G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hHyp : HypothesisClassBounded V support B) :
    ∃ C > 0, ∃ c₁ > 0, ∃ c₂ > 0,
    ∀ (P : Measure Ω) (_hProbability : IsProbabilityMeasure P)
      (sample : AnalysisSample V P) (split : SampleSplit)
      (gHat : ℕ → Ω → X → Z → ℝ) (ρ : ℝ),
    RDIVClassesMeasurable V P sample split mu G g₀ gHat →
    IterRDIVFixedCenterSupremumVersion V P sample split mu gHat ρ →
    ∀ (n t k : ℕ) (lam r : ℝ) (sourceRadius : ℝ)
      (_hSourceScope : gridValue ρ (terminalIndex ρ n) ≤ sourceRadius ∧
        oraclePoint ρ n sourceRadius ≤ lam), 0 < n → 1 ≤ k → k ≤ t →
    lam ∈ regGrid ρ n → lam ∈ Set.Ioc (0 : ℝ) 2 →
    populationIterate V lam k ∈ V.H →
    0 < r → 1 < 2 * c₂ * n →
    4 * Real.log (41 * Real.log (2 * c₂ * n)) / (c₂ * n) ≤ r ^ 2 →
    IsCriticalRadiusBound (V.law.map V.xOf) (primalVersion V '' V.H) n r →
    ∃ E : Set Ω, MeasurableSet E ∧
      1 - 2 * c₁ * Real.exp (-c₂ * n * r ^ 2 / 4) ≤ P.real E ∧
      ∀ ω ∈ E, ∀ h ∈ V.H,
        |primalEmpDistanceSq V P sample split n ω h (populationIterate V lam k) -
          ‖h - populationIterate V lam k‖ ^ 2| ≤
          C * r * (‖h - populationIterate V lam k‖ + r) ∧
        Real.sqrt (primalEmpDistanceSq V P sample split n ω h
          (populationIterate V lam k)) ≤
          (C + 1) * (‖h - populationIterate V lam k‖ + r) := by
  obtain ⟨C, hC, c₁, hc₁, c₂, hc₂, hsource⟩ :=
    hSq mu G g₀ support B c₀ CG hIV hDensity hBounds hHyp
  refine ⟨C, hC, c₁, hc₁, c₂, hc₂, ?_⟩
  intro P hProbability sample split gHat ρ hMeas hVersion n t k lam r sourceRadius hSourceScope hn hk hkt
    hlam hdom hstar hr hlarge hfloor hrad
  let : IsProbabilityMeasure P := hProbability
  have hanchored := iter_rdiv_anchored_radius_of_critical_radius
    (V.law.map V.xOf) (primalVersion V '' V.H)
    (primalVersion V (populationIterate V lam k)) ⟨_, hstar, rfl⟩ n r hrad
  obtain ⟨_, E, hE, hpE, hgood⟩ := (hsource P hProbability sample split gHat ρ
    hMeas hVersion n t k lam r sourceRadius hSourceScope hn hk hkt hlam hdom hstar hr hlarge hfloor hanchored).exists
  let tuple : Ω → Fin n → 𝒲 := fun ω i =>
    sample.Z ((Finset.equivFinOfCardEq (split.card_fit n)).symm i) ω
  have htuple : Measurable tuple := by fun_prop
  have hlaw : P.map tuple = Measure.pi (fun _ : Fin n => V.law) := by
    have hinj : Function.Injective (fun i : Fin n =>
        ((Finset.equivFinOfCardEq (split.card_fit n)).symm i : ℕ)) :=
      Subtype.val_injective.comp (Equiv.injective _)
    have hi := sample.indep.precomp hinj
    have hm := (iIndepFun_iff_map_fun_eq_pi_map
      (fun i : Fin n => (sample.meas _).aemeasurable)).mp hi
    change P.map tuple = _ at hm
    rw [hm]
    simp_rw [sample.map_eq]
  refine ⟨tuple ⁻¹' E, hE.preimage htuple, ?_, ?_⟩
  · have heq : P (tuple ⁻¹' E) = (Measure.pi (fun _ : Fin n => V.law)) E := by
      rw [← Measure.map_apply htuple hE, hlaw]
    simpa only [measureReal_def, heq] using hpE
  intro ω hω h hh
  have hb := hgood (tuple ω) hω h hh
  dsimp only [tuple] at hb
  rw [rdiv_fitting_tuple_average V P sample split n
    (fun w => (primalVersion V h (V.xOf w) -
      primalVersion V (populationIterate V lam k) (V.xOf w)) ^ 2) ω] at hb
  change |primalEmpDistanceSq V P sample split n ω h (populationIterate V lam k) -
    ‖h - populationIterate V lam k‖ ^ 2| ≤ _ at hb
  refine ⟨hb, ?_⟩
  apply iter_rdiv_empirical_norm_of_comparison V P sample split n ω C r
    h (populationIterate V lam k) hC.le hr.le
  nlinarith only [hb]

/-- If [the tail prefactor is positive](hyp:hc₁), [the allocated budget is
positive](hyp:hη), and [the exponent is at least the logarithm of eight times
the prefactor divided by that budget](hyp:hlog), [twice the prefactor times the
negative exponential of the exponent is at most one quarter of the
budget](goal). -/
-- @node: iter_rdiv_source_tail_at_allocation
lemma iter_rdiv_source_tail_at_allocation (c₁ x η : ℝ)
    (hc₁ : 0 < c₁) (hη : 0 < η)
    (hlog : Real.log (8 * c₁ / η) ≤ x) :
    2 * c₁ * Real.exp (-x) ≤ η / 4 := by
  calc
    _ ≤ 2 * c₁ * Real.exp (-Real.log (8 * c₁ / η)) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hlog))
      positivity
    _ = η / 4 := by
      rw [Real.exp_neg, Real.exp_log (by positivity)]
      field_simp
      ring

/-- Under [localized squared-loss concentration](hyp:hSq), [the RDIV model
assumptions](hyp:hIV), [density realizability](hyp:hDensity), [the density
bounds](hyp:hBounds), and [boundedness of the hypothesis class](hyp:hHyp),
[positive population constants can be chosen so that every admissible measurable
sampling experiment, grid segment, and radius satisfying the source-scope,
critical-radius, floor, tail, and iterate-membership requirements has a
measurable event of probability at least one minus a quarter of the failure
budget, on which the squared-distance deviation and empirical norm bounds hold
simultaneously for every positive iteration up to the horizon, every grid point
in the segment, and every class member](goal). -/
-- @node: iter_rdiv_squared_loss_iteration_grid_event
lemma iter_rdiv_squared_loss_iteration_grid_event
    (hSq : IterRDIVSquaredLossLocalizedConcentration (Ω := Ω) V)
    (mu : Measure X) (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (support : Set (X × Z)) (B c₀ CG : ℝ)
    (hIV : RDIVSetting V mu g₀) (hDensity : DensityRealizable V mu G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hHyp : HypothesisClassBounded V support B) :
    ∃ C > 0, ∃ c₁ > 0, ∃ c₂ > 0,
    ∀ (P : Measure Ω) (_hProbability : IsProbabilityMeasure P)
      (sample : AnalysisSample V P) (split : SampleSplit)
      (gHat : ℕ → Ω → X → Z → ℝ) (ρ ξ : ℝ),
    RDIVClassesMeasurable V P sample split mu G g₀ gHat →
    IterRDIVFixedCenterSupremumVersion V P sample split mu gHat ρ →
    ∀ (n t : ℕ) (r : ℝ) (segment : Set ℝ) (sourceRadius : ℝ)
      (_hSourceScope : gridValue ρ (terminalIndex ρ n) ≤ sourceRadius ∧
        ∀ lam ∈ regGrid ρ n, lam ∈ segment → oraclePoint ρ n sourceRadius ≤ lam), 0 < n → 1 ≤ t → 0 < ξ → 0 < r →
    1 < 2 * c₂ * n →
    4 * Real.log (41 * Real.log (2 * c₂ * n)) / (c₂ * n) ≤ r ^ 2 →
    Real.log (8 * c₁ / iterGridConfidence ρ ξ n t) ≤ c₂ * n * r ^ 2 / 4 →
    IsCriticalRadiusBound (V.law.map V.xOf) (primalVersion V '' V.H) n r →
    (∀ lam ∈ regGrid ρ n, lam ∈ segment → lam ∈ Set.Ioc (0 : ℝ) 2) →
    (∀ lam ∈ regGrid ρ n, lam ∈ segment → ∀ k, 1 ≤ k → k ≤ t →
      populationIterate V lam k ∈ V.H) →
    ∃ E : Set Ω, MeasurableSet E ∧ 1 - ξ / 4 ≤ P.real E ∧
      ∀ ω ∈ E, ∀ lam ∈ regGrid ρ n, lam ∈ segment → ∀ k, 1 ≤ k → k ≤ t → ∀ h ∈ V.H,
        |primalEmpDistanceSq V P sample split n ω h (populationIterate V lam k) -
          ‖h - populationIterate V lam k‖ ^ 2| ≤ C * r * (‖h - populationIterate V lam k‖ + r) ∧
        Real.sqrt (primalEmpDistanceSq V P sample split n ω h
          (populationIterate V lam k)) ≤ (C + 1) * (‖h - populationIterate V lam k‖ + r) := by
  obtain ⟨C, hC, c₁, hc₁, c₂, hc₂, hsource⟩ :=
    iter_rdiv_squared_loss_fitting_event V hSq mu G g₀ support B c₀ CG
      hIV hDensity hBounds hHyp
  refine ⟨C, hC, c₁, hc₁, c₂, hc₂, ?_⟩
  intro P hProbability sample split gHat ρ ξ hMeas hVersion n t r segment sourceRadius hSourceScope hn ht hξ hr
    hlarge hfloor hlog hrad hdom hstar
  let : IsProbabilityMeasure P := hProbability
  have hη : 0 < iterGridConfidence ρ ξ n t := by
    unfold iterGridConfidence
    positivity
  have htail : 2 * c₁ * Real.exp (-c₂ * n * r ^ 2 / 4) ≤
      iterGridConfidence ρ ξ n t / 4 := by
    have hb := iter_rdiv_source_tail_at_allocation c₁ (c₂ * n * r ^ 2 / 4)
      (iterGridConfidence ρ ξ n t) hc₁ hη hlog
    simpa only [neg_div, neg_mul] using hb
  classical
  have hlocal : ∀ k ∈ Finset.Icc 1 t, ∀ lam ∈ regGrid ρ n,
      ∃ E : Set Ω, MeasurableSet E ∧
        1 - iterGridConfidence ρ ξ n t / 4 ≤ P.real E ∧
        ∀ ω ∈ E, lam ∈ segment → ∀ h ∈ V.H,
          |primalEmpDistanceSq V P sample split n ω h (populationIterate V lam k) -
            ‖h - populationIterate V lam k‖ ^ 2| ≤
            C * r * (‖h - populationIterate V lam k‖ + r) ∧
          Real.sqrt (primalEmpDistanceSq V P sample split n ω h
            (populationIterate V lam k)) ≤ (C + 1) * (‖h - populationIterate V lam k‖ + r) := by
    intro k hk lam hlam
    obtain ⟨hk₁, hkt⟩ := Finset.mem_Icc.mp hk
    by_cases hs : lam ∈ segment
    · obtain ⟨E, hE, hpE, hgood⟩ := hsource P hProbability sample split gHat ρ
        hMeas hVersion n t k lam r sourceRadius ⟨hSourceScope.1, hSourceScope.2 lam hlam hs⟩ hn hk₁ hkt hlam (hdom lam hlam hs)
        (hstar lam hlam hs k hk₁ hkt) hr hlarge hfloor hrad
      refine ⟨E, hE, ?_, ?_⟩
      · linarith only [hpE, htail]
      · intro ω hω _ h hh
        have hb := hgood ω hω h hh
        simpa only [mul_add, mul_assoc] using hb
    · refine ⟨Set.univ, MeasurableSet.univ, ?_, ?_⟩
      · simp only [measureReal_def, measure_univ, ENNReal.toReal_one]
        linarith [hη]
      · intro ω hω hs'
        exact (hs hs').elim
  choose F hF hpF hgood using hlocal
  let E : ℕ → ℝ → Set Ω := fun k lam =>
    if hk : k ∈ Finset.Icc 1 t then
      if hl : lam ∈ regGrid ρ n then F k hk lam hl else Set.univ
    else Set.univ
  have hEm : ∀ k ∈ Finset.Icc 1 t, ∀ lam ∈ regGrid ρ n, MeasurableSet (E k lam) := by
    intro k hk lam hl
    simpa only [E, dif_pos hk, dif_pos hl] using hF k hk lam hl
  have hEp : ∀ k ∈ Finset.Icc 1 t, ∀ lam ∈ regGrid ρ n,
      1 - iterGridConfidence ρ ξ n t / 4 ≤ P.real (E k lam) := by
    intro k hk lam hl
    simpa only [E, dif_pos hk, dif_pos hl] using hpF k hk lam hl
  obtain ⟨hm, hp⟩ := iter_rdiv_iteration_grid_event_budget P ρ ξ n t hξ.le ht E hEm hEp
  refine ⟨⋂ k ∈ Finset.Icc 1 t, ⋂ lam ∈ regGrid ρ n, E k lam, hm, hp, ?_⟩
  intro ω hω lam hl hs k hk hkt h hh
  have hk' : k ∈ Finset.Icc 1 t := Finset.mem_Icc.mpr ⟨hk, hkt⟩
  have hmem := Set.mem_iInter₂.mp (Set.mem_iInter₂.mp hω k hk') lam hl
  simp only [E, dif_pos hk', dif_pos hl] at hmem
  exact hgood k hk' lam hl ω hmem hs h hh

end Papers.TsAdaptiveEstimationInference

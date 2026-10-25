module
public import Papers.TsAdaptiveEstimationInference.Helpers.IterRDIVSquaredLoss
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVFittingTransfer
/-! Integral and empirical identities for the fixed-population-center RDIV loss.
These identities keep the supplied representatives and empirical objective. They
connect the concentration increment to the objective used in the stability proof;
they do not assert a concentration event or a stability bound. -/
public section
set_option linter.style.longLine false
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory
open scoped ENNReal
variable {𝒲 X Z Ω : Type*} [MeasurableSpace 𝒲] [MeasurableSpace X]
  [MeasurableSpace Z] [MeasurableSpace Ω]
  (V : IVWorld 𝒲 X Z)

/-- For [a candidate function in the population Hilbert space](hyp:h) and any center in that space,
[the squared difference of their selected realizations is integrable, and its population
integral equals their squared Hilbert-space distance](goal). -/
-- @node: iter_rdiv_centered_penalty_integral
lemma iter_rdiv_centered_penalty_integral (h center : V.Hbar.toSubmodule) :
    Integrable (fun w => (primalVersion V h (V.xOf w) -
      primalVersion V center (V.xOf w)) ^ 2) V.law ∧
    (∫ w, (primalVersion V h (V.xOf w) -
      primalVersion V center (V.xOf w)) ^ 2 ∂V.law) = ‖h - center‖ ^ 2 := by
  have hhp : MemLp (fun w => primalVersion V h (V.xOf w)) 2 V.law :=
    (memLp_congr_ae (V.primal_coherent h)).2 (Lp.memLp (h : Lp ℝ 2 V.law))
  have hcp : MemLp (fun w => primalVersion V center (V.xOf w)) 2 V.law :=
    (memLp_congr_ae (V.primal_coherent center)).2
      (Lp.memLp (center : Lp ℝ 2 V.law))
  refine ⟨(hhp.sub hcp).integrable_sq, ?_⟩
  calc
    _ = ∫ w, ((h - center : V.Hbar.toSubmodule) : Lp ℝ 2 V.law) w ^ 2 ∂V.law := by
      apply integral_congr_ae
      filter_upwards [V.primal_coherent h, V.primal_coherent center,
        Lp.coeFn_sub (h : Lp ℝ 2 V.law) (center : Lp ℝ 2 V.law)] with w hh hc he
      change (V.primalRealization h (V.xOf w) -
        V.primalRealization center (V.xOf w)) ^ 2 = _
      rw [hh, hc]
      exact congrArg (fun x : ℝ => x ^ 2) he.symm
    _ = _ := by
      simpa only [L2.inner_def, RCLike.inner_apply, conj_trivial, ← pow_two,
        Submodule.norm_coe] using
        real_inner_self_eq_norm_sq ((h - center : V.Hbar.toSubmodule) : Lp ℝ 2 V.law)

/-- Assume [the instrumental-variable model holds](hyp:hIV), [the true density is realizable
in the density class](hyp:hDensity), [the class satisfies the specified density bounds](hyp:hBounds),
[the hypothesis class is bounded by B on the support](hyp:hHyp), and [the outcome is bounded
by B](hyp:hY). For [a density in the class](hyp:hg) and [a candidate in the population Hilbert
space](hyp:h) that [belongs to the hypothesis class](hyp:hh), [the fixed-center loss is
integrable and its expectation equals the population squared residual loss plus the penalty
weight times squared distance to the preceding population iterate](goal). -/
-- @node: iter_rdiv_fixed_center_loss_integral
lemma iter_rdiv_fixed_center_loss_integral
    (mu : Measure X) (G : Set (X → Z → ℝ)) (g₀ g : X → Z → ℝ)
    (support : Set (X × Z)) (B c₀ CG lam : ℝ) (j : ℕ)
    (hIV : RDIVSetting V mu g₀) (hDensity : DensityRealizable V mu G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hHyp : HypothesisClassBounded V support B) (hY : OutcomeBounded V B)
    (hg : g ∈ G) (h : V.Hbar.toSubmodule) (hh : h ∈ V.H) :
    Integrable (iterRdivFixedCenterLoss V mu g lam j h) V.law ∧
    (∫ w, iterRdivFixedCenterLoss V mu g lam j h w ∂V.law) =
      (∫ w, (V.Y w - densityOperator mu g (primalVersion V h) (V.zOf w)) ^ 2 ∂V.law) +
        lam * ‖h - populationIterate V lam (j - 1)‖ ^ 2 := by
  obtain ⟨hi, _⟩ := rdiv_fitting_loss_integral V mu G g₀ g support B c₀ CG 0
    hIV hDensity hBounds hHyp hY hg h hh
  change Integrable (fun w =>
    (V.Y w - densityOperator mu g (primalVersion V h) (V.zOf w)) ^ 2 +
      0 * primalVersion V h (V.xOf w) ^ 2) V.law at hi
  simp only [zero_mul, add_zero] at hi
  obtain ⟨hpen, heq⟩ :=
    iter_rdiv_centered_penalty_integral V h (populationIterate V lam (j - 1))
  refine ⟨hi.add (hpen.const_mul lam), ?_⟩
  unfold iterRdivFixedCenterLoss
  rw [integral_add hi (hpen.const_mul lam), integral_const_mul, heq]

variable (P : Measure Ω) (sample : AnalysisSample V P) (split : SampleSplit)

/-- For [a candidate function in the population Hilbert space](hyp:h), a comparison function,
and a center, [the difference between their uncentered empirical squared-norm contrast and
their centered empirical squared-distance contrast equals twice the fitting-block average
of their realization difference multiplied by the center realization](goal). -/
-- @node: iter_rdiv_empirical_penalty_center_change
lemma iter_rdiv_empirical_penalty_center_change (n : ℕ) (ω : Ω)
    (h k center : V.Hbar.toSubmodule) :
    (primalEmpSq V P sample split n ω h - primalEmpSq V P sample split n ω k) -
      (primalEmpDistanceSq V P sample split n ω h center -
        primalEmpDistanceSq V P sample split n ω k center) =
      2 * blockAverage V P sample (split.fit n)
        (fun w => (primalVersion V h (V.xOf w) - primalVersion V k (V.xOf w)) *
          primalVersion V center (V.xOf w)) ω := by
  unfold primalEmpSq primalEmpDistanceSq blockAverage
  rw [← mul_sub, ← mul_sub, ← mul_sub, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  have heq : (∑ i ∈ split.fit n,
      ((primalVersion V h (V.xOf (sample.Z i ω)) ^ 2 -
        primalVersion V k (V.xOf (sample.Z i ω)) ^ 2) -
      ((primalVersion V h (V.xOf (sample.Z i ω)) -
          primalVersion V center (V.xOf (sample.Z i ω))) ^ 2 -
        (primalVersion V k (V.xOf (sample.Z i ω)) -
          primalVersion V center (V.xOf (sample.Z i ω))) ^ 2))) =
      2 * ∑ i ∈ split.fit n,
        (primalVersion V h (V.xOf (sample.Z i ω)) -
          primalVersion V k (V.xOf (sample.Z i ω))) *
            primalVersion V center (V.xOf (sample.Z i ω)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [heq]
  ring

/-- For [a candidate function in the population Hilbert space](hyp:h), a comparison function,
and a center, [the zero-centered population-minus-empirical risk contrast minus its
fixed-center counterpart equals twice the penalty weight times the difference between
the population inner product of the candidate contrast with the center and its fitting-block
average product](goal). -/
-- @node: iter_rdiv_risk_deviation_center_change
lemma iter_rdiv_risk_deviation_center_change (mu : Measure X)
    (gHat : ℕ → Ω → X → Z → ℝ) (n : ℕ) (ω : Ω) (lam : ℝ)
    (h k center : V.Hbar.toSubmodule) :
    ((conditionalRisk V mu gHat n ω lam h - conditionalRisk V mu gHat n ω lam k) -
      (empiricalRisk V P sample split mu gHat n ω lam h -
        empiricalRisk V P sample split mu gHat n ω lam k)) -
    (((conditionalPopulationLoss V mu gHat n ω h + lam * ‖h - center‖ ^ 2) -
        (conditionalPopulationLoss V mu gHat n ω k + lam * ‖k - center‖ ^ 2)) -
      ((rdivEmpiricalLoss V P sample split mu gHat n ω h +
          lam * primalEmpDistanceSq V P sample split n ω h center) -
        (rdivEmpiricalLoss V P sample split mu gHat n ω k +
          lam * primalEmpDistanceSq V P sample split n ω k center))) =
    2 * lam * (inner ℝ (h - k) center -
      blockAverage V P sample (split.fit n)
        (fun w => (primalVersion V h (V.xOf w) - primalVersion V k (V.xOf w)) *
          primalVersion V center (V.xOf w)) ω) := by
  have hemp := iter_rdiv_empirical_penalty_center_change V P sample split n ω h k center
  simp only [conditionalRisk, empiricalRisk, norm_sub_sq_real, inner_sub_left]
  linear_combination -lam * hemp

/-- For [a candidate function in the population Hilbert space](hyp:h), [averaging its
fixed-center loss over the fitting block with the preliminary density frozen equals
its observed squared residual loss plus the penalty weight times its empirical squared
distance to the preceding population iterate](goal). -/
-- @node: iter_rdiv_fixed_center_loss_average
lemma iter_rdiv_fixed_center_loss_average (mu : Measure X)
    (gHat : ℕ → Ω → X → Z → ℝ) (n j : ℕ) (preliminary ω : Ω)
    (lam : ℝ) (h : V.Hbar.toSubmodule) :
    blockAverage V P sample (split.fit n)
      (iterRdivFixedCenterLoss V mu (gHat n preliminary) lam j h) ω =
      rdivEmpiricalLoss V P sample split mu (fun _ _ => gHat n preliminary) n ω h +
        lam * primalEmpDistanceSq V P sample split n ω h
          (populationIterate V lam (j - 1)) := by
  simp only [blockAverage, iterRdivFixedCenterLoss, rdivEmpiricalLoss,
    estimatedOperator, primalEmpDistanceSq, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- Assume [the instrumental-variable model holds](hyp:hIV), [the true density is realizable](hyp:hDensity),
[the density bounds hold on the support](hyp:hBounds), [the hypothesis class is bounded
by B](hyp:hHyp), [the outcome is bounded by B](hyp:hY), and [the frozen density estimate
belongs to the density class](hyp:hg). For [two population Hilbert-space functions](hyp:h,hstar)
that [both belong to the hypothesis class](hyp:hh,hstarH), [the absolute empirical-minus-population
deviation of their fixed-center loss difference equals the absolute difference between
their population and empirical fixed-center objective contrasts](goal). -/
-- @node: iter_rdiv_fixed_center_deviation_eq_risks
lemma iter_rdiv_fixed_center_deviation_eq_risks
    (mu : Measure X) (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (gHat : ℕ → Ω → X → Z → ℝ) (support : Set (X × Z))
    (B c₀ CG : ℝ) (n j : ℕ) (preliminary ω : Ω) (lam : ℝ)
    (hIV : RDIVSetting V mu g₀) (hDensity : DensityRealizable V mu G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hHyp : HypothesisClassBounded V support B) (hY : OutcomeBounded V B)
    (hg : gHat n preliminary ∈ G)
    (h hstar : V.Hbar.toSubmodule) (hh : h ∈ V.H) (hstarH : hstar ∈ V.H) :
    |blockAverage V P sample (split.fit n)
        (fun w => iterRdivFixedCenterLoss V mu (gHat n preliminary) lam j h w -
          iterRdivFixedCenterLoss V mu (gHat n preliminary) lam j hstar w) ω -
      ∫ w, iterRdivFixedCenterLoss V mu (gHat n preliminary) lam j h w -
        iterRdivFixedCenterLoss V mu (gHat n preliminary) lam j hstar w ∂V.law| =
    |((conditionalPopulationLoss V mu gHat n preliminary h +
          lam * ‖h - populationIterate V lam (j - 1)‖ ^ 2) -
        (conditionalPopulationLoss V mu gHat n preliminary hstar +
          lam * ‖hstar - populationIterate V lam (j - 1)‖ ^ 2)) -
      ((rdivEmpiricalLoss V P sample split mu (fun _ _ => gHat n preliminary) n ω h +
          lam * primalEmpDistanceSq V P sample split n ω h
            (populationIterate V lam (j - 1))) -
        (rdivEmpiricalLoss V P sample split mu (fun _ _ => gHat n preliminary) n ω hstar +
          lam * primalEmpDistanceSq V P sample split n ω hstar
            (populationIterate V lam (j - 1))))| := by
  obtain ⟨hi, he⟩ := iter_rdiv_fixed_center_loss_integral V mu G g₀ _ support B c₀ CG lam j
    hIV hDensity hBounds hHyp hY hg h hh
  obtain ⟨hsi, hse⟩ := iter_rdiv_fixed_center_loss_integral V mu G g₀ _ support B c₀ CG lam j
    hIV hDensity hBounds hHyp hY hg hstar hstarH
  rw [integral_sub hi hsi, he, hse]
  have havg : blockAverage V P sample (split.fit n)
      (fun w => iterRdivFixedCenterLoss V mu (gHat n preliminary) lam j h w -
        iterRdivFixedCenterLoss V mu (gHat n preliminary) lam j hstar w) ω =
      blockAverage V P sample (split.fit n)
        (iterRdivFixedCenterLoss V mu (gHat n preliminary) lam j h) ω -
      blockAverage V P sample (split.fit n)
        (iterRdivFixedCenterLoss V mu (gHat n preliminary) lam j hstar) ω := by
    simp only [blockAverage, Finset.sum_sub_distrib, mul_sub]
  rw [havg, iter_rdiv_fixed_center_loss_average V P sample split mu gHat,
    iter_rdiv_fixed_center_loss_average V P sample split mu gHat]
  exact abs_sub_comm _ _

/-- Assume [localized concentration for fixed-center losses](hyp:hFix), [the instrumental-variable
model](hyp:hIV), [density realizability](hyp:hDensity), [the specified density bounds](hyp:hBounds),
[an outcome bounded by B](hyp:hY), and [a hypothesis class bounded by B](hyp:hHyp).
Then [positive population constants give, for almost every frozen preliminary sample,
a measurable fitting event with probability at least one minus twice the concentration
prefactor times the exponential of minus the decay constant times sample size times squared
radius divided by eight; on this event every fixed-center objective contrast is controlled
by the radius times the sum of its estimated-operator distance, Hilbert distance, and radius,
whenever density selection, measurability, coherent versions, grid and source scope,
iterate membership, and critical-radius and confidence-floor conditions hold](goal). -/
-- @node: iter_rdiv_fixed_center_frozen_fitting_event
lemma iter_rdiv_fixed_center_frozen_fitting_event
    (hFix : IterRDIVFixedCenterLocalizedConcentration (Ω := Ω) V)
    (mu : Measure X) (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (support : Set (X × Z)) (B c₀ CG : ℝ)
    (hIV : RDIVSetting V mu g₀) (hDensity : DensityRealizable V mu G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hY : OutcomeBounded V B) (hHyp : HypothesisClassBounded V support B) :
    ∃ C > 0, ∃ c₁ > 0, ∃ c₂ > 0,
    ∀ (P : Measure Ω) (_hProbability : IsProbabilityMeasure P)
      (sample : AnalysisSample V P) (split : SampleSplit)
      (gHat : ℕ → Ω → X → Z → ℝ) (ρ : ℝ),
    MLEMaximizerSelected V P sample split G gHat →
    RDIVClassesMeasurable V P sample split mu G g₀ gHat →
    IterRDIVFixedCenterSupremumVersion V P sample split mu gHat ρ →
    ∀ (n t j : ℕ) (lam r : ℝ) (sourceRadius : ℝ)
      (_hSourceScope : gridValue ρ (terminalIndex ρ n) ≤ sourceRadius ∧
        oraclePoint ρ n sourceRadius ≤ lam), 0 < n → 1 ≤ j → j ≤ t →
    lam ∈ regGrid ρ n → lam ∈ Set.Ioc (0 : ℝ) 2 →
    populationIterate V lam j ∈ V.H →
    (populationIterate V lam (j - 1) ∈ V.H ∨ j = 1) →
    0 < r → 1 < 2 * c₂ * n →
    8 * Real.log (41 * Real.log (2 * c₂ * n)) / (c₂ * n) ≤ r ^ 2 →
    IsCriticalRadiusBound (V.law.map V.xOf) (primalVersion V '' V.H) n r →
    (∀ g ∈ G, IsCriticalRadiusBound (V.law.map V.zOf)
      (densityOperator mu g '' (primalVersion V '' V.H)) n r) →
    ∀ᵐ preliminary ∂P, ∃ E : Set Ω, MeasurableSet E ∧
      1 - 2 * c₁ * Real.exp (-c₂ * n * r ^ 2 / 8) ≤ P.real E ∧
      ∀ ω ∈ E, ∀ h ∈ V.H,
        let center := populationIterate V lam (j - 1)
        let star := populationIterate V lam j
        let pop := fun u => conditionalPopulationLoss V mu gHat n preliminary u +
          lam * ‖u - center‖ ^ 2
        let emp := fun u => rdivEmpiricalLoss V P sample split mu
          (fun _ _ => gHat n preliminary) n ω u +
            lam * primalEmpDistanceSq V P sample split n ω u center
        |(pop h - pop star) - (emp h - emp star)| ≤
          C * r * (inputL2Norm (V.law.map V.zOf)
            (densityOperator mu (gHat n preliminary) (primalVersion V h -
              primalVersion V star)) + ‖h - star‖ + r) := by
  obtain ⟨C, hC, c₁, hc₁, c₂, hc₂, hsource⟩ :=
    hFix mu G g₀ support B c₀ CG hIV hDensity hBounds hY hHyp
  refine ⟨C, hC, c₁, hc₁, c₂, hc₂, ?_⟩
  intro P hProbability sample split gHat ρ hMLE hMeas hVersion n t j lam r sourceRadius hSourceScope hn hj hjt
    hlam hdom hstar hcenter hr hlarge hfloor hradX hradZ
  let : IsProbabilityMeasure P := hProbability
  have hanchoredX := iter_rdiv_anchored_radius_of_critical_radius
    (V.law.map V.xOf) (primalVersion V '' V.H)
    (primalVersion V (populationIterate V lam j)) ⟨_, hstar, rfl⟩ n r hradX
  have hanchoredZ : ∀ g ∈ G, iterRdivAnchoredRadius (V.law.map V.zOf)
      (densityOperator mu g '' (primalVersion V '' V.H))
      (densityOperator mu g (primalVersion V (populationIterate V lam j))) n r := by
    intro g hg
    exact iter_rdiv_anchored_radius_of_critical_radius (V.law.map V.zOf)
      (densityOperator mu g '' (primalVersion V '' V.H))
      (densityOperator mu g (primalVersion V (populationIterate V lam j)))
      ⟨_, ⟨_, hstar, rfl⟩, rfl⟩ n r (hradZ g hg)
  have hs := hsource P hProbability sample split gHat ρ hMLE hMeas hVersion
    n t j lam r sourceRadius hSourceScope hn hj hjt hlam hdom hstar hcenter hr hlarge hfloor hanchoredX hanchoredZ
  let tuple : Ω → Fin n → 𝒲 := fun ω i =>
    sample.Z ((Finset.equivFinOfCardEq (split.card_fit n)).symm i) ω
  have htuple : Measurable tuple := by fun_prop
  have hlaw : P.map tuple = Measure.pi (fun _ : Fin n => V.law) := by
    have hinj : Function.Injective (fun i : Fin n =>
        ((Finset.equivFinOfCardEq (split.card_fit n)).symm i : ℕ)) :=
      Subtype.val_injective.comp (Equiv.injective _)
    have hi := sample.indep.precomp hinj
    have hm := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
      (fun i : Fin n => (sample.meas _).aemeasurable)).mp hi
    change P.map tuple = _ at hm
    rw [hm]
    simp_rw [sample.map_eq]
  filter_upwards [hs, (hMLE n hn).1] with preliminary hpre hg
  obtain ⟨E, hE, hpE, hgood⟩ := hpre
  refine ⟨tuple ⁻¹' E, hE.preimage htuple, ?_, ?_⟩
  · have heq : P (tuple ⁻¹' E) = (Measure.pi (fun _ : Fin n => V.law)) E := by
      rw [← Measure.map_apply htuple hE, hlaw]
    simpa only [measureReal_def, heq] using hpE
  intro ω hω h hh
  dsimp only
  rw [← iter_rdiv_fixed_center_deviation_eq_risks V P sample split mu G g₀ gHat
    support B c₀ CG n j preliminary ω lam hIV hDensity hBounds hHyp hY hg.1
    h (populationIterate V lam j) hh hstar]
  have hb := hgood (tuple ω) hω h hh
  dsimp only at hb
  rw [rdiv_fitting_tuple_average V P sample split n _ ω] at hb
  exact hb

/-- For [loss classes indexed by positive rational radii and preliminary samples](hyp:lossClass)
and [an extended nonnegative bound for each radius](hyp:bound), suppose [the failure
probability lies strictly between zero and one](hyp:hη), [each empirical supremum has
a coherent measurable version](hyp:hVersion), and [for almost every frozen preliminary
sample all the supremum bounds hold with probability at least one minus the failure
probability](hyp:hFrozen). Then [a measurable event with that same probability lower
bound satisfies all radius bounds with preliminary and fitting data evaluated at the
actual sample](goal). -/
-- @node: iter_rdiv_coherent_localizations_event
lemma iter_rdiv_coherent_localizations_event [IsProbabilityMeasure P]
    (n : ℕ) (lossClass : {q : ℚ // 0 < q} → Ω → Set (𝒲 → ℝ))
    (bound : {q : ℚ // 0 < q} → ℝ≥0∞) (η : ℝ)
    (hη : η ∈ Set.Ioo (0 : ℝ) 1)
    (hVersion : ∀ q, iterRdivCoherentSupremum V P sample split n (lossClass q))
    (hFrozen : ∀ᵐ pre ∂P, 1 - η ≤ P.real {fit | ∀ q,
      empiricalSupremum V.law (lossClass q pre) n
        (fun i => sample.Z ((Finset.equivFinOfCardEq (split.card_fit n)).symm i) fit) ≤
          bound q}) :
    ∃ E : Set Ω, MeasurableSet E ∧ 1 - η ≤ P.real E ∧
      ∀ ω ∈ E, ∀ q, empiricalSupremum V.law (lossClass q ω) n
        (fun i => sample.Z ((Finset.equivFinOfCardEq (split.card_fit n)).symm i) ω) ≤
          bound q := by
  classical
  let Q := {q : ℚ // 0 < q}
  choose S hSm hSsec hScoh using hVersion
  let tuple : Ω → Fin n → 𝒲 := fun ω i =>
    sample.Z ((Finset.equivFinOfCardEq (split.card_fit n)).symm i) ω
  have htuple : Measurable tuple := by fun_prop
  have htupleLaw : P.map tuple = Measure.pi (fun _ : Fin n => V.law) := by
    have hinj : Function.Injective (fun i : Fin n =>
        ((Finset.equivFinOfCardEq (split.card_fit n)).symm i : ℕ)) :=
      Subtype.val_injective.comp (Equiv.injective _)
    have hi := sample.indep.precomp hinj
    have hm := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
      (fun i : Fin n => (sample.meas _).aemeasurable)).mp hi
    change P.map tuple = _ at hm
    rw [hm]
    simp_rw [sample.map_eq]
  let R : Ω → Ω → Prop := fun pre fit => ∀ q : Q, S q (pre, tuple fit) ≤ bound q
  have htfit : @Measurable Ω (Fin n → 𝒲)
      (⨆ i ∈ split.fit n, MeasurableSpace.comap (sample.Z i) inferInstance)
      inferInstance tuple := by
    let : MeasurableSpace Ω :=
      ⨆ i ∈ split.fit n, MeasurableSpace.comap (sample.Z i) inferInstance
    apply measurable_pi_lambda
    intro i
    apply measurable_iff_comap_le.2
    exact le_iSup_of_le _ (le_iSup_of_le
      ((Finset.equivFinOfCardEq (split.card_fit n)).symm i).2 le_rfl)
  have hR : MeasurableSet[(preliminarySigma V P sample split n).prod
      (⨆ i ∈ split.fit n, MeasurableSpace.comap (sample.Z i) inferInstance)]
      {p : Ω × Ω | R p.1 p.2} := by
    let : MeasurableSpace (Ω × Ω) := (preliminarySigma V P sample split n).prod
      (⨆ i ∈ split.fit n, MeasurableSpace.comap (sample.Z i) inferInstance)
    simp only [R, Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro q
    exact measurableSet_le ((hSm q).comp
      (measurable_fst.prodMk (htfit.comp measurable_snd))) measurable_const
  have hsections : ∀ᵐ pre ∂P, 1 - η ≤ P.real {fit | R pre fit} := by
    filter_upwards [ae_all_iff.2 hSsec, hFrozen] with pre hsec hprob
    have hident : ∀ᵐ fit ∂P, ∀ q : Q,
        S q (pre, tuple fit) =
          empiricalSupremum V.law (lossClass q pre) n (tuple fit) := by
      apply ae_all_iff.2
      intro q
      have hs : ∀ᵐ ws ∂P.map tuple, S q (pre, ws) =
          empiricalSupremum V.law (lossClass q pre) n ws := by
        rw [htupleLaw]
        exact hsec q
      exact ae_of_ae_map htuple.aemeasurable hs
    apply hprob.trans
    apply ENNReal.toReal_mono (measure_ne_top P _)
    apply measure_mono_ae
    filter_upwards [hident] with fit hid hgood
    intro q
    rw [hid q]
    exact hgood q
  obtain ⟨hE, hpE⟩ := rdiv_fitting_event_of_frozen_sections V P sample split
    n R hR η hη hsections
  have hcoh : ∀ᵐ ω ∂P, ∀ q : Q, S q (ω, tuple ω) =
      empiricalSupremum V.law (lossClass q ω) n (tuple ω) := ae_all_iff.2 hScoh
  obtain ⟨N, hsub, hN, hN0⟩ := exists_measurable_superset_of_null
    (show P {ω | ¬ ∀ q : Q, S q (ω, tuple ω) =
      empiricalSupremum V.law (lossClass q ω) n (tuple ω)} = 0 from ae_iff.mp hcoh)
  refine ⟨{ω | R ω ω} \ N, hE.diff hN, ?_, ?_⟩
  · simpa only [measureReal_def, measure_sdiff_null hN0] using hpE
  intro ω hω q
  have hid : ∀ q : Q, S q (ω, tuple ω) =
      empiricalSupremum V.law (lossClass q ω) n (tuple ω) := by
    by_contra hbad
    exact hω.2 (hsub hbad)
  rw [← hid q]
  exact hω.1 q

/-- Suppose [the sample size is positive](hyp:hn), [the horizon is at least one](hyp:ht),
[the iteration is at least one](hyp:hj) and [does not exceed the horizon](hyp:hjt),
[the penalty lies on the regularization grid](hyp:hlam), [the distance coefficient](hyp:hA)
and [the additive bound](hyp:hD) are nonnegative, and [the failure probability lies strictly
between zero and one](hyp:hη). If [the fixed-center suprema have coherent versions](hyp:hVersion)
and [almost every frozen preliminary sample gives a fitting event of probability at least
one minus the failure probability on which every loss-difference deviation is bounded by
the distance coefficient times distance to the current population iterate plus the additive
bound](hyp:hFrozen), then [a measurable event with the same probability lower bound gives
this inequality uniformly over the hypothesis class using the actual preliminary and
fitting data](goal). -/
-- @node: iter_rdiv_thaw_fixed_center_deviations
lemma iter_rdiv_thaw_fixed_center_deviations [IsProbabilityMeasure P]
    (mu : Measure X) (gHat : ℕ → Ω → X → Z → ℝ) (ρ : ℝ)
    (n t j : ℕ) (lam A D η : ℝ) (hn : 0 < n) (ht : 1 ≤ t)
    (hj : 1 ≤ j) (hjt : j ≤ t) (hlam : lam ∈ regGrid ρ n)
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hη : η ∈ Set.Ioo (0 : ℝ) 1)
    (hVersion : IterRDIVFixedCenterSupremumVersion V P sample split mu gHat ρ)
    (hFrozen : ∀ᵐ pre ∂P, 1 - η ≤ P.real {fit | ∀ h ∈ V.H,
      |blockAverage V P sample (split.fit n)
          (fun w => iterRdivFixedCenterLoss V mu (gHat n pre) lam j h w -
            iterRdivFixedCenterLoss V mu (gHat n pre) lam j
              (populationIterate V lam j) w) fit -
        ∫ w, iterRdivFixedCenterLoss V mu (gHat n pre) lam j h w -
          iterRdivFixedCenterLoss V mu (gHat n pre) lam j
            (populationIterate V lam j) w ∂V.law| ≤
        A * ‖h - populationIterate V lam j‖ + D}) :
    ∃ E : Set Ω, MeasurableSet E ∧ 1 - η ≤ P.real E ∧
      ∀ ω ∈ E, ∀ h ∈ V.H,
        |blockAverage V P sample (split.fit n)
            (fun w => iterRdivFixedCenterLoss V mu (gHat n ω) lam j h w -
              iterRdivFixedCenterLoss V mu (gHat n ω) lam j
                (populationIterate V lam j) w) ω -
          ∫ w, iterRdivFixedCenterLoss V mu (gHat n ω) lam j h w -
            iterRdivFixedCenterLoss V mu (gHat n ω) lam j
              (populationIterate V lam j) w ∂V.law| ≤
          A * ‖h - populationIterate V lam j‖ + D := by
  let value : Ω → Ω → V.Hbar.toSubmodule → ℝ := fun pre fit h =>
    |blockAverage V P sample (split.fit n)
        (fun w => iterRdivFixedCenterLoss V mu (gHat n pre) lam j h w -
          iterRdivFixedCenterLoss V mu (gHat n pre) lam j
            (populationIterate V lam j) w) fit -
      ∫ w, iterRdivFixedCenterLoss V mu (gHat n pre) lam j h w -
        iterRdivFixedCenterLoss V mu (gHat n pre) lam j
          (populationIterate V lam j) w ∂V.law|
  have hsup (pre fit : Ω) (q : ℝ) :
      empiricalSupremum V.law (iterRdivFixedCenterLossClass V mu (gHat n pre) lam q j) n
        (fun i => sample.Z ((Finset.equivFinOfCardEq (split.card_fit n)).symm i) fit) =
      ⨆ h : {h : V.H // ‖h.1 - populationIterate V lam j‖ ≤ q},
        ENNReal.ofReal (value pre fit h.1.1) := by
    have heq (h : V.Hbar.toSubmodule) :
        ENNReal.ofReal |(n : ℝ)⁻¹ * ∑ i : Fin n,
          (iterRdivFixedCenterLoss V mu (gHat n pre) lam j h -
            iterRdivFixedCenterLoss V mu (gHat n pre) lam j (populationIterate V lam j))
              (sample.Z ((Finset.equivFinOfCardEq (split.card_fit n)).symm i) fit) -
          ∫ w, (iterRdivFixedCenterLoss V mu (gHat n pre) lam j h -
            iterRdivFixedCenterLoss V mu (gHat n pre) lam j
              (populationIterate V lam j)) w ∂V.law| =
        ENNReal.ofReal (value pre fit h) := by
      rw [rdiv_fitting_tuple_average V P sample split]
      rfl
    unfold empiricalSupremum
    apply le_antisymm
    · apply iSup_le
      intro f
      obtain ⟨h, hh, hr, hf⟩ := f.2
      apply le_iSup_of_le ⟨⟨h, hh⟩, hr⟩
      simpa only [hf] using (heq h).le
    · apply iSup_le
      intro h
      apply le_iSup_of_le ⟨_, ⟨h.1.1, h.1.2, h.2, rfl⟩⟩
      exact (heq h.1.1).ge
  have hversions (q : {q : ℚ // 0 < q}) :=
    (hVersion n hn t ht lam hlam q.1 q.2).1 j hj hjt
  have hfrozenLocal : ∀ᵐ pre ∂P, 1 - η ≤ P.real {fit | ∀ q : {q : ℚ // 0 < q},
      empiricalSupremum V.law
        (iterRdivFixedCenterLossClass V mu (gHat n pre) lam (q.1 : ℝ) j) n
        (fun i => sample.Z ((Finset.equivFinOfCardEq (split.card_fit n)).symm i) fit) ≤
        ENNReal.ofReal (A * (q.1 : ℝ) + D)} := by
    filter_upwards [hFrozen] with pre hp
    apply hp.trans
    apply ENNReal.toReal_mono (measure_ne_top P _)
    apply measure_mono
    intro fit hfit q
    rw [hsup]
    apply iSup_le
    intro h
    exact ENNReal.ofReal_le_ofReal ((hfit h.1.1 h.1.2).trans
      (add_le_add (mul_le_mul_of_nonneg_left h.2 hA) le_rfl))
  obtain ⟨E, hE, hpE, hgood⟩ := iter_rdiv_coherent_localizations_event V P sample split n
    (fun q pre => iterRdivFixedCenterLossClass V mu (gHat n pre) lam (q.1 : ℝ) j)
    (fun q => ENNReal.ofReal (A * (q.1 : ℝ) + D)) η hη hversions hfrozenLocal
  refine ⟨E, hE, hpE, ?_⟩
  intro ω hω h hh
  have hb := (rdiv_uniform_bound_iff_rational_localizations
    (fun h : V.H => ‖h.1 - populationIterate V lam j‖)
    (fun h : V.H => value ω ω h.1) A D (fun _ => norm_nonneg _) hA hD).2 (by
      intro q hq
      have hq' : 0 < q := by exact_mod_cast hq
      have hb := hgood ω hω ⟨q, hq'⟩
      rwa [hsup] at hb)
  exact hb ⟨h, hh⟩

end Papers.TsAdaptiveEstimationInference

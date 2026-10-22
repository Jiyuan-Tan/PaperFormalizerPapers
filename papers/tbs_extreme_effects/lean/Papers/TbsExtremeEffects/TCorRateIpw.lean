module
public import Papers.TbsExtremeEffects.TRate
public import Papers.TbsExtremeEffects.Helpers.AdaptiveAngularRates
public import Papers.TbsExtremeEffects.Helpers.AdaptiveProduct
public import Papers.TbsExtremeEffects.Helpers.ThresholdSampling
public import Papers.TbsExtremeEffects.Helpers.AdaptiveEvents
public import Papers.TbsExtremeEffects.Helpers.AdaptiveTailCounts
public import Papers.TbsExtremeEffects.Helpers.AdaptiveTailRates
public import Papers.TbsExtremeEffects.Helpers.AdaptiveExponent
public import Papers.TbsExtremeEffects.Helpers.AdaptiveMean
public import Papers.TbsExtremeEffects.Helpers.AdaptiveScoreMean
public import Papers.TbsExtremeEffects.Helpers.ThresholdMaximalEvents
public import Papers.TbsExtremeEffects.Helpers.ThresholdSignedMoments
public import Papers.TbsExtremeEffects.Helpers.ScoreEnergy
public import Papers.TbsExtremeEffects.Helpers.LocalizedThresholdEnvelope

public import Papers.TbsExtremeEffects.Helpers.AdaptiveIPWMean

/-! The two IPW adaptive-threshold regimes with deterministic order constants. -/

public section
set_option linter.style.longLine false
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
variable {q d m : ℕ}

-- @node: thm:cor-rate-ipw
/-- [The extreme model $M$](hyp:M), [experiment $E$](hyp:E), [representation matrix $A$](hyp:A), [tail parameters](hyp:tp), [overlap level $c$](hyp:c), [nuisance-rate functions](hyp:Rp,Rg,Ralpha), [consistency](hyp:hConsistency), [exogeneity](hyp:hExogeneity), [estimated overlap](hyp:hOverlap), [noise regular variation](hyp:hRV), [noise independence](hyp:hNoise), [bounded covariates](hyp:hX), [asymptotic homogeneity](hyp:hHomogeneity), [the varying-density condition](hyp:hDensity), [the varying-matrix condition](hyp:hMatrix), [the parameter-range conditions](hyp:hConstants), [an outcome exponent below the tail index](hyp:hAlpha), [nuisance error bounds](hyp:hNuisance), [exponent training](hyp:hExponentTraining), [a conditional-mean version](hyp:hMean), [identification side conditions](hyp:hSide), [positive nuisance-rate constant $c_\alpha$](hyp:cAlpha,hcAlpha), [inverse-probability-weighted rates for the nuisance estimators](hyp:hRp,hRg,hRalpha), [threshold-band constants and confidence level](hyp:cminus,cplus,V,delta,hdelta,hdeltaHalf), [the selected threshold rule](hyp:tn), and [the angular rate bound](hyp:CW,k,tW,hAngular) imply [in each specified tail-exponent range, that the corresponding threshold-order and band guarantees yield a Hill constant and an eventual high-probability bound for the inverse-probability-weighted estimation error at the displayed angular rate](goal). -/
theorem nete_ipw_rate_adaptive_threshold
    (M : ExtremeModel q d) (E : NeteExperiment M)
    (A : Matrix (Fin d) (Fin m) ℝ) (tp : TailParams)
    (c : ℝ) (Rp Rg Ralpha : ℕ → ℝ → ℝ)
    (hConsistency : Consistency M) (hExogeneity : Exogeneity M)
    (hOverlap : EstimatedOverlap E c)
    (hRV : NoiseRegularlyVarying M) (hNoise : NoiseIndependent M)
    (hX : CovariateBounded M) (hHomogeneity : AsymptoticHomogeneity M)
    (hDensity : MvaryDensity M A tp) (hMatrix : MvaryMatrix A tp)
    (hConstants : MvaryConstants d m tp) (hAlpha : AlphaLtBeta M)
    (hNuisance : ∀ n, EvenSampleSize n → NuisanceErrorBounds E n Rp Rg Ralpha)
    (hExponentTraining : ∀ n, EvenSampleSize n → ExponentTraining E n)
    (hMean : ConditionalMeanVersion M)
    (hSide : IdentificationSideConditions M)
    (cAlpha : ℝ) (hcAlpha : 0 < cAlpha)
    (hRp : RateThetaIpw Rp (1 / 2)) (hRg : RateThetaIpw Rg (1 / 2))
    (hRalpha : RateThetaIpw Ralpha cAlpha)
    (cminus cplus V delta : ℝ) (hdelta : 0 < delta) (hdeltaHalf : delta < 1 / 2)
    (tn : ℕ → E.Om → ℝ)
    (CW k tW : ℝ) (hAngular : AngularRateBound M tp CW k tW) :
    (0 < tp.s ∧ tp.s < 1 / (2 + max 1 M.beta) →
      SelectedThresholdOrderIpw cminus cplus (lowRegimeExponent tp.s)
        (fun n => hillAdaptive E n (delta / 6)) tn →
      (∀ n, EvenSampleSize n → BandGuarantee E .ipw cminus cplus V delta
        (lowRegimeExponent tp.s) Rp Rg Ralpha n) →
      ∃ Cg : ℝ, ∃ n0 : ℕ, HillConstantAt E (delta / 6) n0 Cg ∧
        EventualBigOBoundIpw E.P delta (IIDSampling E) (corError E .ipw tn delta)
          (corRateAngular E .ipw tn k V Cg delta cAlpha tp.s)) ∧
    (1 / (2 + max 1 M.beta) ≤ tp.s ∧ tp.s < 1 / 2 →
      SelectedThresholdOrderIpw cminus cplus highRegimeExponent
        (fun n => hillAdaptive E n (delta / 6)) tn →
      (∀ n, EvenSampleSize n → BandGuarantee E .ipw cminus cplus V delta
        highRegimeExponent Rp Rg Ralpha n) →
      ∃ Cg : ℝ, ∃ n0 : ℕ, HillConstantAt E (delta / 6) n0 Cg ∧
        EventualBigOBoundIpw E.P delta (IIDSampling E) (corError E .ipw tn delta)
          (corRateAngular E .ipw tn k V Cg delta cAlpha (corRateExponent M.beta))) := by
  have hTail : Nonempty (ParetoTailModel M m tp) :=
    ⟨⟨A, hDensity, hMatrix, hConstants⟩⟩
  have hd6 : ConfidenceDomain (delta / 6) := ⟨by positivity, by linarith⟩
  let Cg := sourceHillConstant M E tp hRV hNoise hTail (delta / 6)
  obtain ⟨nHill, hHill⟩ := sourceHillConstant_spec M E tp hRV hNoise hTail
    (delta / 6) hd6
  have hg : 0 < gamma M := one_div_pos.mpr hRV.1
  have hTarget : thetaNETE M = etaTarget M * (1 / radialH M) := by
    have hId := nete_identification M hRV hConsistency hExogeneity hRV hNoise hX
      hHomogeneity hMean hAlpha hSide
    have hValue := hId.2.2.1.limUnder_eq
    change thetaNETE M = _ at hValue
    rw [hValue, radial_target_eq_inv_h hRV.1 hAlpha]
  suffices hRemaining : ∀ (kappa : ℝ → ℝ) (r : ℝ),
      0 < kappa (gamma M) → 0 < r →
      (1 - M.beta * kappa (gamma M)) / 2 = r →
      r ≤ min 1 M.beta * kappa (gamma M) →
      r ≤ (M.beta * tp.s / (1 - 2 * tp.s)) * kappa (gamma M) →
      SelectedThresholdOrder cminus cplus kappa
        (fun n => hillAdaptive E n (delta / 6)) tn →
      (∀ᶠ n : ℕ in atTop, EvenSampleSize n → IIDSampling E n →
        1 - delta / 6 ≤ E.P.real {w |
          |gamma M - hillAdaptive E n (delta / 6) w| ≤ hillErrorBound M Cg delta n ∧
          tn n w ∈ thresholdBand M cminus cplus kappa n}) →
      (∀ n, EvenSampleSize n → BandGuarantee E .ipw cminus cplus V delta
        kappa Rp Rg Ralpha n) →
      EventualBigOBound E.P delta (IIDSampling E) (corError E .ipw tn delta)
        (corRateAngular E .ipw tn k V Cg delta cAlpha r) by
    constructor
    · intro hs hOrder hGuarantee
      have hden : 0 < 2 + max 1 M.beta := by
        have := le_max_left (1 : ℝ) M.beta
        linarith
      have hcut : 1 / (2 + max 1 M.beta) ≤ (1 / 2 : ℝ) := by
        apply (div_le_iff₀ hden).mpr
        have := le_max_left (1 : ℝ) M.beta
        linarith
      have hsHalf : tp.s < 1 / 2 := hs.2.trans_le hcut
      have hLip : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
          |lowRegimeExponent tp.s x - lowRegimeExponent tp.s y| ≤ |x - y| := by
        intro x y _ _
        exact lowRegimeExponent_sub_le hs.1.le hsHalf.le
      have hBand := hill_selected_threshold_band_probability E hRV.1 hdelta
        hHill hOrder hLip
      refine ⟨Cg, nHill, hHill, ?_⟩
      exact hRemaining (lowRegimeExponent tp.s) tp.s
        (mul_pos (by linarith : 0 < 1 - 2 * tp.s) hg) hs.1
        (lowRegime_count_exponent hRV.1)
        (lowRegime_angular_exponents hRV.1 hs.1 hs.2).1
        (lowRegime_angular_exponents hRV.1 hs.1 hs.2).2 hOrder hBand hGuarantee
    · intro hs hOrder hGuarantee
      have hLip : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
          |highRegimeExponent x - highRegimeExponent y| ≤ |x - y| := by
        intro x y hx hy
        exact highRegimeExponent_sub_le hx hy
      have hBand := hill_selected_threshold_band_probability E hRV.1 hdelta
        hHill hOrder hLip
      have hk : 0 < highRegimeExponent (gamma M) := by
        unfold highRegimeExponent
        positivity
      have hr : 0 < corRateExponent M.beta := by
        unfold corRateExponent
        have := le_max_right M.beta (1 : ℝ)
        positivity
      refine ⟨Cg, nHill, hHill, ?_⟩
      exact hRemaining highRegimeExponent (corRateExponent M.beta) hk hr
        (highRegime_count_exponent hRV.1)
        (highRegime_angular_exponents hRV.1 hs.1 hs.2).1
        (highRegime_angular_exponents hRV.1 hs.1 hs.2).2 hOrder hBand hGuarantee
  intro kappa r hk hr hCountExponent hrAngular hrTailAngular hOrder hBand hGuarantee
  obtain ⟨D, hD, hRadialRate⟩ := adaptiveRadialQ_rate_bound
    (M := M) (Cg := Cg) hRV.1 hd6 hRalpha
  have hMu := adaptive_muHat_bounds_eventually E (Cg := Cg)
    hRV.1 hAlpha hd6 hcAlpha hRalpha
  have hh : 0 < radialH M := radialH_pos hRV.1 hAlpha
  let K := 2 / radialH M + |etaTarget M| * (2 / radialH M ^ 2) * D + 1
  have hK : 0 < K := by dsimp [K]; positivity
  suffices hFirstFactor : ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      EvenSampleSize n → IIDSampling E n →
      1 - delta ≤ E.P.real {w |
        |E.alphaHat n w - M.alpha| ≤ Ralpha n (delta / 6) ∧
        |gamma M - hillAdaptive E n (delta / 6) w| ≤ hillErrorBound M Cg delta n ∧
        ∃ e : ℝ, |etaEstimate E .ipw n (tn n w) w - etaTarget M| ≤ e ∧
          e + adaptiveRadialScale M Cg delta cAlpha n ≤
            C * corRateAngular E .ipw tn k V Cg delta cAlpha r n w} by
    obtain ⟨C, hC, hEvent⟩ := hFirstFactor
    refine ⟨K * C, mul_pos hK hC, ?_⟩
    have hFinal : ∀ᶠ n : ℕ in atTop, Even n → IIDSampling E n →
        1 - delta ≤ E.P.real {w | corError E .ipw tn delta n w ≤
          (K * C) * corRateAngular E .ipw tn k V Cg delta cAlpha r n w} := by
      filter_upwards [hEvent, hMu, hRadialRate, eventually_ge_atTop 1] with
        n hnEvent hnMu hnRate hn
      intro heven hiid
      apply (hnEvent ⟨by omega, heven⟩ hiid).trans
      apply measureReal_mono (h₂ := measure_ne_top E.P _)
      rintro w ⟨ha, hHillGood, e, hEta, hRateGood⟩
      have hbnd : 0 ≤ hillErrorBound M Cg delta n := (abs_nonneg _).trans hHillGood
      obtain ⟨hScale, hQ⟩ := hnRate hbnd
      have he : 0 ≤ e := (abs_nonneg _).trans hEta
      have hProduct := adaptive_product_error_bound E .ipw hTarget
        (hnMu w ha hHillGood) hEta
      have hA : 2 / radialH M ≤ K := by
        have hNonneg : 0 ≤ |etaTarget M| * (2 / radialH M ^ 2) * D := by positivity
        dsimp [K]
        linarith
      have hB : |etaTarget M| * (2 / radialH M ^ 2) * D ≤ K := by
        have hNonneg : 0 ≤ 2 / radialH M := by positivity
        dsimp [K]
        linarith
      change |neteEstimator E .ipw n (tn n w) (delta / 6) w - thetaNETE M| ≤ _
      calc
        _ ≤ (2 / radialH M) * e + |etaTarget M| *
            (2 * adaptiveRadialQ M Cg delta Ralpha n / radialH M ^ 2) := hProduct
        _ = (2 / radialH M) * e + (|etaTarget M| * (2 / radialH M ^ 2)) *
            adaptiveRadialQ M Cg delta Ralpha n := by ring
        _ ≤ (2 / radialH M) * e + (|etaTarget M| * (2 / radialH M ^ 2)) *
            (D * adaptiveRadialScale M Cg delta cAlpha n) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hQ (by positivity))
        _ = (2 / radialH M) * e + (|etaTarget M| * (2 / radialH M ^ 2) * D) *
            adaptiveRadialScale M Cg delta cAlpha n := by ring
        _ ≤ K * e + K * adaptiveRadialScale M Cg delta cAlpha n :=
          add_le_add (mul_le_mul_of_nonneg_right hA he)
            (mul_le_mul_of_nonneg_right hB hScale)
        _ = K * (e + adaptiveRadialScale M Cg delta cAlpha n) := by ring
        _ ≤ K * (C * corRateAngular E .ipw tn k V Cg delta cAlpha r n w) :=
          mul_le_mul_of_nonneg_left hRateGood hK.le
        _ = _ := by ring
    obtain ⟨n0, hn0⟩ := eventually_atTop.mp hFinal
    exact ⟨n0, hn0⟩
  suffices hProcesses : ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      EvenSampleSize n → IIDSampling E n →
      1 - delta ≤ E.P.real {w |
        |E.alphaHat n w - M.alpha| ≤ Ralpha n (delta / 6) ∧
        |gamma M - hillAdaptive E n (delta / 6) w| ≤ hillErrorBound M Cg delta n ∧
        tn n w ∈ thresholdBand M cminus cplus kappa n ∧
        ∃ N A B e : ℝ, 0 < N ∧
          N ≤ (evalCount E n (2 * cplus * (n : ℝ) ^ kappa (gamma M)) w : ℝ) ∧
          (∀ t ∈ thresholdBand M cminus cplus kappa n,
            |thresholdCenteredScore E .ipw n t w| ≤ A ∧
            |thresholdCenteredCount E n t w| ≤ B ∧
            MemLp (score E .ipw n w) 2 (obsTailLaw M t) ∧
            scoreSecondMoment E .ipw n t w ≤ V) ∧
          |thresholdScoreMean E .ipw n (tn n w) w - etaTarget M| ≤ e ∧
          (A + Real.sqrt V * B) / N + e + adaptiveRadialScale M Cg delta cAlpha n ≤
            C * corRateAngular E .ipw tn k V Cg delta cAlpha r n w} by
    obtain ⟨C, hC, hEvent⟩ := hProcesses
    refine ⟨C, hC, ?_⟩
    filter_upwards [hEvent] with n hn
    intro heven hiid
    apply (hn heven hiid).trans
    apply measureReal_mono (h₂ := measure_ne_top E.P _)
    rintro w ⟨ha, hHillGood, ht, N, A, B, e, hN, hCount, hBounds, hMeanGood, hRate⟩
    have hBandBounds : ∀ t ∈ thresholdBand M cminus cplus kappa n,
        |thresholdCenteredScore E .ipw n t w| ≤ A ∧
        |thresholdCenteredCount E n t w| ≤ B ∧
        |thresholdScoreMean E .ipw n t w| ≤ Real.sqrt V := by
      intro t ht
      obtain ⟨hA, hB, hLp, hV⟩ := hBounds t ht
      exact ⟨hA, hB, thresholdScoreMean_le_sqrt E .ipw hRV n t w hLp hV⟩
    exact ⟨ha, hHillGood, (A + Real.sqrt V * B) / N + e,
      selected_threshold_error_of_selected_mean E .ipw n w ht hN hCount hBandBounds
        hMeanGood, hRate⟩
  have hCountGrowth := adaptive_band_count_tendsto_atTop M tp hRV hTail
    (mul_pos (by norm_num : (0 : ℝ) < 2) (hOrder.1.trans_le hOrder.2.1))
    hk hr hCountExponent
  have hCountBudget : ∀ᶠ n : ℕ in atTop, 16 * Real.log (6 / delta) ≤
      (n : ℝ) * tailProb M (2 * cplus * (n : ℝ) ^ kappa (gamma M)) :=
    hCountGrowth.eventually (eventually_ge_atTop _)
  let countFloor : ℕ → ℝ := fun n =>
    (n : ℝ) * tailProb M (2 * cplus * (n : ℝ) ^ kappa (gamma M)) / 4
  suffices hCertificates : ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      EvenSampleSize n → IIDSampling E n →
      ∀ (reg : ℝ → ((Fin q → ℝ) × Bool × (Fin d → ℝ)) → ℝ) (G : Set E.Om),
      (∀ t ∈ thresholdBand M cminus cplus kappa n,
        IsTailRegressionVersion M t (reg t)) →
      MeasurableSet[trainSigma E n] G →
      (∀ t ∈ thresholdBand M cminus cplus kappa n,
        FittedPseudoOutcomeIntegrable E n t G) →
      (∀ w ∈ G, ∀ t ∈ thresholdBand M cminus cplus kappa n,
        |E.alphaHat n w - M.alpha| ≤ Ralpha n (delta / 6) ∧
        (∀ᵐ x ∂(M.mu.map M.X), |M.p x - E.pHat n w x| ≤ Rp (n / 2) (delta / 6)) ∧
        (∀ a : Bool, ∀ᵐ z ∂(covariateDirectionLaw M t),
          |reg t (z.1, a, z.2) - E.gHat n w z.1 a z.2| ≤
            Rg (trainCount E n t w) (delta / 6)) ∧
        MemLp (score E .ipw n w) 2 (obsTailLaw M t) ∧
        scoreSecondMoment E .ipw n t w ≤ V) →
      ∃ S : Fin 2 → Set E.Om,
        (∀ i, MeasurableSet (S i)) ∧
        E.P.real (G \ S 0) ≤ delta / 6 ∧ E.P.real (G \ S 1) ≤ delta / 6 ∧
        ∀ w ∈ G,
          (|gamma M - hillAdaptive E n (delta / 6) w| ≤ hillErrorBound M Cg delta n ∧
            tn n w ∈ thresholdBand M cminus cplus kappa n) →
          (n : ℝ) * tailProb M (2 * cplus * (n : ℝ) ^ kappa (gamma M)) / 4 ≤
            (trainCount E n (2 * cplus * (n : ℝ) ^ kappa (gamma M)) w : ℝ) →
          (n : ℝ) * tailProb M (2 * cplus * (n : ℝ) ^ kappa (gamma M)) / 4 ≤
            (evalCount E n (2 * cplus * (n : ℝ) ^ kappa (gamma M)) w : ℝ) →
          (∀ i, w ∈ S i) →
          ∃ A B e : ℝ,
            (∀ t ∈ thresholdBand M cminus cplus kappa n,
              |thresholdCenteredScore E .ipw n t w| ≤ A ∧
              |thresholdCenteredCount E n t w| ≤ B) ∧
            |thresholdScoreMean E .ipw n (tn n w) w - etaTarget M| ≤ e ∧
            (A + Real.sqrt V * B) / countFloor n + e + adaptiveRadialScale M Cg delta cAlpha n ≤
              C * corRateAngular E .ipw tn k V Cg delta cAlpha r n w by
    obtain ⟨C, hC, hData⟩ := hCertificates
    refine ⟨C, hC, ?_⟩
    filter_upwards [hData, hBand, hCountBudget] with n hn hHillBand hBudget
    intro heven hiid
    obtain ⟨reg, hreg, G, hGtraining, hGprob, hPseudo, hGood⟩ := hGuarantee n heven
    obtain ⟨S, hS, hScoreFailure, hCountFailure, hCertificate⟩ :=
      hn heven hiid reg G hreg hGtraining hPseudo hGood
    obtain ⟨hTrain, hEval⟩ := adaptive_endpoint_count_events E n
      (2 * cplus * (n : ℝ) ^ kappa (gamma M)) heven hiid hdelta hBudget
    let J : Fin 4 → Set E.Om := ![
      {w | (n : ℝ) * tailProb M (2 * cplus * (n : ℝ) ^ kappa (gamma M)) / 4 ≤
        (trainCount E n (2 * cplus * (n : ℝ) ^ kappa (gamma M)) w : ℝ)},
      {w | (n : ℝ) * tailProb M (2 * cplus * (n : ℝ) ^ kappa (gamma M)) / 4 ≤
        (evalCount E n (2 * cplus * (n : ℝ) ^ kappa (gamma M)) w : ℝ)}, S 0, S 1]
    have hJ : ∀ i, MeasurableSet (J i) := by
      intro i
      fin_cases i
      · exact hTrain.1
      · exact hEval.1
      · exact hS 0
      · exact hS 1
    have hCounts : ∀ i : Fin 2, 1 - delta / 6 ≤ E.P.real (J i.castSucc.castSucc) := by
      intro i
      fin_cases i
      · exact hTrain.2
      · exact hEval.2
    apply adaptive_six_events_imp E.P G
      {w | |gamma M - hillAdaptive E n (delta / 6) w| ≤ hillErrorBound M Cg delta n ∧
        tn n w ∈ thresholdBand M cminus cplus kappa n}
      J ((trainSigma_le E n) _ hGtraining) hJ hGprob (hHillBand heven hiid)
      hCounts hScoreFailure hCountFailure
    intro w hw hHillGood hAll
    have hFloor : 0 < countFloor n := by
      dsimp [countFloor]
      apply div_pos (mul_pos ?_ (tailProb_pos_of_regularVariation M hRV _)) (by norm_num)
      exact_mod_cast (show 0 < n by have := heven.1; omega)
    have hProcesses : ∀ i, w ∈ S i := by
      intro i
      fin_cases i
      · exact hAll 2
      · exact hAll 3
    obtain ⟨A, B, e, hBounds, hMeanGood, hRate⟩ :=
      hCertificate w hw hHillGood (hAll 0) (hAll 1) hProcesses
    refine ⟨(hGood w hw (tn n w) hHillGood.2).1, hHillGood.1, hHillGood.2,
      countFloor n, A, B, e, hFloor, hAll 1, ?_, hMeanGood, hRate⟩
    intro t ht
    obtain ⟨hA, hB⟩ := hBounds t ht
    have hMoments := (hGood w hw t ht).2.2.2
    exact ⟨hA, hB, hMoments.1, hMoments.2⟩
  obtain ⟨Ltail, Utail, hLtail, hUtail, hTailRates⟩ :=
    adaptive_band_tail_envelopes M tp hRV hTail hOrder.1
      (hOrder.1.trans_le hOrder.2.1) hk hCountExponent
  obtain ⟨Cgb, hGBound⟩ := homogeneous_regression_has_bound M hHomogeneity
  obtain ⟨nuisanceConstant, hNuisanceConstant, hBiasRates⟩ :=
    adaptive_band_ipw_bias_rate E hRV hX hHomogeneity hOverlap hGBound hRp hd6
      hOrder.1 hk
  let samplingConstant := 4 * Real.sqrt (192 * Utail / Ltail ^ 2)
  obtain ⟨exponentConstant, hExponentConstant, hExponentMoments⟩ :=
    adaptive_band_radial_moment_rate M hRV hRalpha hcAlpha hd6 hOrder.1
      (hOrder.1.trans_le hOrder.2.1) hk
      (half_pos hRV.1) (by linarith [hRV.1] : M.beta / 2 < M.beta)
  have htol : 1 / (delta / 6) = 6 / delta := by ring
  suffices hMaximalAndMean : ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      EvenSampleSize n → IIDSampling E n →
      (∀ t ∈ thresholdBand M cminus cplus kappa n,
        1 ≤ t ∧ 0 ≤ Ralpha n (delta / 6) ∧ Ralpha n (delta / 6) ≤ M.beta / 2 ∧
        Integrable (fun w => radius M w ^ (Ralpha n (delta / 6)) - 1) (tailLaw M t) ∧
        (∫ w, radius M w ^ (Ralpha n (delta / 6)) - 1 ∂tailLaw M t) ≤
          exponentConstant * ((n : ℝ) ^ (-cAlpha) * Real.log n * Real.log (6 / delta))) →
      ∀ (reg : ℝ → ((Fin q → ℝ) × Bool × (Fin d → ℝ)) → ℝ) (G : Set E.Om),
      (∀ t ∈ thresholdBand M cminus cplus kappa n,
        IsTailRegressionVersion M t (reg t)) →
      MeasurableSet[trainSigma E n] G →
      (∀ t ∈ thresholdBand M cminus cplus kappa n,
        FittedPseudoOutcomeIntegrable E n t G) →
      (∀ w ∈ G, ∀ t ∈ thresholdBand M cminus cplus kappa n,
        |E.alphaHat n w - M.alpha| ≤ Ralpha n (delta / 6) ∧
        (∀ᵐ x ∂(M.mu.map M.X), |M.p x - E.pHat n w x| ≤ Rp (n / 2) (delta / 6)) ∧
        (∀ a : Bool, ∀ᵐ z ∂(covariateDirectionLaw M t),
          |reg t (z.1, a, z.2) - E.gHat n w z.1 a z.2| ≤
            Rg (trainCount E n t w) (delta / 6)) ∧
        MemLp (score E .ipw n w) 2 (obsTailLaw M t) ∧
        scoreSecondMoment E .ipw n t w ≤ V) →
      (∀ w ∈ G,
        (n : ℝ) * tailProb M (2 * cplus * (n : ℝ) ^ kappa (gamma M)) / 4 ≤
          (trainCount E n (2 * cplus * (n : ℝ) ^ kappa (gamma M)) w : ℝ) →
        ∀ t ∈ thresholdBand M cminus cplus kappa n,
          |∫ v, ipwBiasIntegrand E n w v ∂tailLaw M t| ≤
            nuisanceConstant * Real.log (6 / delta) *
              (n : ℝ) ^ (-(1 / 2 : ℝ))) →
      ∃ S : Fin 2 → Set E.Om,
        (∀ i, MeasurableSet (S i)) ∧
        E.P.real (G \ S 0) ≤ delta / 6 ∧ E.P.real (G \ S 1) ≤ delta / 6 ∧
        ∀ w ∈ G,
          (|gamma M - hillAdaptive E n (delta / 6) w| ≤ hillErrorBound M Cg delta n ∧
            tn n w ∈ thresholdBand M cminus cplus kappa n) →
          (n : ℝ) * tailProb M (2 * cplus * (n : ℝ) ^ kappa (gamma M)) / 4 ≤
            (trainCount E n (2 * cplus * (n : ℝ) ^ kappa (gamma M)) w : ℝ) →
          (n : ℝ) * tailProb M (2 * cplus * (n : ℝ) ^ kappa (gamma M)) / 4 ≤
            (evalCount E n (2 * cplus * (n : ℝ) ^ kappa (gamma M)) w : ℝ) →
          (∀ i, w ∈ S i) →
          ∃ e : ℝ,
            (∀ t ∈ thresholdBand M cminus cplus kappa n,
              |thresholdCenteredScore E .ipw n t w| ≤
                Real.sqrt (48 * (n : ℝ) * V *
                  tailProb M ((cminus / 2) * (n : ℝ) ^ kappa (gamma M)) / delta) ∧
              |thresholdCenteredCount E n t w| ≤
                Real.sqrt (48 * (n : ℝ) *
                  tailProb M ((cminus / 2) * (n : ℝ) ^ kappa (gamma M)) / delta)) ∧
            |thresholdScoreMean E .ipw n (tn n w) w - etaTarget M| ≤ e ∧
            samplingConstant * Real.sqrt (V / delta) * (n : ℝ) ^ (-r) + e +
              adaptiveRadialScale M Cg delta cAlpha n ≤
                C * corRateAngular E .ipw tn k V Cg delta cAlpha r n w by
    obtain ⟨C, hC, hData⟩ := hMaximalAndMean
    refine ⟨C, hC, ?_⟩
    filter_upwards [hData, hTailRates, hExponentMoments, hBiasRates]
      with n hn hTails hMoments hBias
    intro heven hiid reg G hreg hGtraining hPseudo hGood
    obtain ⟨S, hS, hScoreFailure, hCountFailure, hCertificate⟩ :=
      hn heven hiid (by simpa only [thresholdBand, htol] using hMoments)
        reg G hreg hGtraining hPseudo hGood (by
          intro w hw hCount t ht
          exact hBias heven w t ht (hGood w hw t ht).2.1)
    refine ⟨S, hS, hScoreFailure, hCountFailure, ?_⟩
    intro w hw hHillGood hTrain hEval hProcesses
    obtain ⟨e, hBounds, hMeanGood, hRate⟩ := hCertificate w hw hHillGood hTrain hEval hProcesses
    let ell := tailProb M ((cminus / 2) * (n : ℝ) ^ kappa (gamma M))
    let u := tailProb M (2 * cplus * (n : ℝ) ^ kappa (gamma M))
    let A := Real.sqrt (48 * (n : ℝ) * V * ell / delta)
    let B := Real.sqrt (48 * (n : ℝ) * ell / delta)
    have hV0 : 0 ≤ V := by
      have hNonneg : 0 ≤ scoreSecondMoment E .ipw n (tn n w) w :=
        integral_nonneg (fun z => sq_nonneg _)
      exact hNonneg.trans (hGood w hw (tn n w) hHillGood.2).2.2.2.2
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by have := heven.1; omega)
    have hSampling := threshold_process_radius_rate_bound hn0 hLtail hUtail
      (tailProb_nonneg M _) hV0 hdelta hTails.2 hTails.1
    refine ⟨A, B, e, hBounds, hMeanGood, ?_⟩
    calc
      _ ≤ samplingConstant * Real.sqrt (V / delta) * (n : ℝ) ^ (-r) + e +
          adaptiveRadialScale M Cg delta cAlpha n := by
        exact add_le_add (add_le_add hSampling le_rfl) le_rfl
      _ ≤ _ := hRate
  let exponentMeanConstant := (2 * (Cgb + 1) / c) * exponentConstant
  obtain ⟨angularConstant, hAngularConstant, hAngularCompare⟩ :=
    adaptive_corRate_angular_comparison E .ipw tp hRV hHomogeneity
      hConstants.2.2.2.2.1 hConstants.2.2.2.2.2.1 CW k tW cminus cplus V Cg delta
      cAlpha r kappa tn hAngular hOrder.1 hOrder.2.1 hdelta hdeltaHalf hk hrAngular hrTailAngular
  let C := samplingConstant + nuisanceConstant + exponentMeanConstant + 4
  have hSamplingConstant : 0 ≤ samplingConstant := by dsimp [samplingConstant]; positivity
  have hExponentMeanConstant : 0 ≤ exponentMeanConstant := by
    dsimp [exponentMeanConstant]
    positivity [hGBound.1, hOverlap.1]
  have hC : 0 < C := by dsimp [C]; linarith
  have hCs : samplingConstant ≤ C := by dsimp [C]; linarith
  have hCn : nuisanceConstant ≤ C := by dsimp [C]; linarith
  have hCe : 2 ≤ C := by dsimp [C]; linarith
  have hCz : exponentMeanConstant + 1 ≤ C := by dsimp [C]; linarith
  suffices hMaximal : ∀ᶠ n : ℕ in atTop,
      EvenSampleSize n → IIDSampling E n →
      (∀ t ∈ thresholdBand M cminus cplus kappa n,
        1 ≤ t ∧ 0 ≤ Ralpha n (delta / 6) ∧ Ralpha n (delta / 6) ≤ M.beta / 2 ∧
        Integrable (fun w => radius M w ^ (Ralpha n (delta / 6)) - 1) (tailLaw M t) ∧
        (∫ w, radius M w ^ (Ralpha n (delta / 6)) - 1 ∂tailLaw M t) ≤
          exponentConstant * ((n : ℝ) ^ (-cAlpha) * Real.log n * Real.log (6 / delta))) →
      ∀ (reg : ℝ → ((Fin q → ℝ) × Bool × (Fin d → ℝ)) → ℝ) (G : Set E.Om),
      (∀ t ∈ thresholdBand M cminus cplus kappa n,
        IsTailRegressionVersion M t (reg t)) →
      MeasurableSet[trainSigma E n] G →
      (∀ t ∈ thresholdBand M cminus cplus kappa n,
        FittedPseudoOutcomeIntegrable E n t G) →
      (∀ w ∈ G, ∀ t ∈ thresholdBand M cminus cplus kappa n,
        |E.alphaHat n w - M.alpha| ≤ Ralpha n (delta / 6) ∧
        (∀ᵐ x ∂(M.mu.map M.X), |M.p x - E.pHat n w x| ≤ Rp (n / 2) (delta / 6)) ∧
        (∀ a : Bool, ∀ᵐ z ∂(covariateDirectionLaw M t),
          |reg t (z.1, a, z.2) - E.gHat n w z.1 a z.2| ≤
            Rg (trainCount E n t w) (delta / 6)) ∧
        MemLp (score E .ipw n w) 2 (obsTailLaw M t) ∧
        scoreSecondMoment E .ipw n t w ≤ V) →
      (∀ w ∈ G,
        (n : ℝ) * tailProb M (2 * cplus * (n : ℝ) ^ kappa (gamma M)) / 4 ≤
          (trainCount E n (2 * cplus * (n : ℝ) ^ kappa (gamma M)) w : ℝ) →
        ∀ t ∈ thresholdBand M cminus cplus kappa n,
          |∫ v, ipwBiasIntegrand E n w v ∂tailLaw M t| ≤
            nuisanceConstant * Real.log (6 / delta) *
              (n : ℝ) ^ (-(1 / 2 : ℝ))) →
      ∃ S : Fin 2 → Set E.Om,
        (∀ i, MeasurableSet (S i)) ∧
        E.P.real (G \ S 0) ≤ delta / 6 ∧ E.P.real (G \ S 1) ≤ delta / 6 ∧
        ∀ w ∈ G,
          (|gamma M - hillAdaptive E n (delta / 6) w| ≤ hillErrorBound M Cg delta n ∧
            tn n w ∈ thresholdBand M cminus cplus kappa n) →
          (n : ℝ) * tailProb M (2 * cplus * (n : ℝ) ^ kappa (gamma M)) / 4 ≤
            (trainCount E n (2 * cplus * (n : ℝ) ^ kappa (gamma M)) w : ℝ) →
          (n : ℝ) * tailProb M (2 * cplus * (n : ℝ) ^ kappa (gamma M)) / 4 ≤
            (evalCount E n (2 * cplus * (n : ℝ) ^ kappa (gamma M)) w : ℝ) →
          (∀ i, w ∈ S i) →
          (∀ t ∈ thresholdBand M cminus cplus kappa n,
              |thresholdCenteredScore E .ipw n t w| ≤
                Real.sqrt (48 * (n : ℝ) * V *
                  tailProb M ((cminus / 2) * (n : ℝ) ^ kappa (gamma M)) / delta) ∧
              |thresholdCenteredCount E n t w| ≤
                Real.sqrt (48 * (n : ℝ) *
                  tailProb M ((cminus / 2) * (n : ℝ) ^ kappa (gamma M)) / delta)) by
    refine ⟨C * angularConstant, mul_pos hC hAngularConstant, ?_⟩
    have hEnvelope := adaptive_band_homogeneity_envelope M hHomogeneity
      (cplus := cplus) hOrder.1 hk
    filter_upwards [hMaximal, hEnvelope, hAngularCompare, eventually_ge_atTop (1 : ℕ)]
      with n hn hEnvelope hAngularCompare hn1
    intro heven hiid hMoments reg G hreg hGtraining hPseudo hGood hBias
    obtain ⟨S, hS, hScoreFailure, hCountFailure, hCertificate⟩ :=
      hn heven hiid hMoments reg G hreg hGtraining hPseudo hGood hBias
    refine ⟨S, hS, hScoreFailure, hCountFailure, ?_⟩
    intro w hw hHillGood hTrain hEval hProcesses
    have hBounds := hCertificate w hw hHillGood hTrain hEval hProcesses
    have ht := hHillGood.2
    obtain ⟨ht1, hb, he0, he1⟩ := hEnvelope (tn n w) ht
    obtain ⟨_, ha, ha0, hRad, hMoment⟩ := hMoments (tn n w) ht
    let P : ℕ → ℝ → ℝ := fun _ _ => Rp (n / 2) (delta / 6)
    let Gfit : ℕ → ℝ → ℝ := fun k _ => Rg k (delta / 6)
    let Afit : ℕ → ℝ → ℝ := fun _ _ => Ralpha n (delta / 6)
    have hNuisanceAt : NuisanceAt E n (tn n w) (delta / 6) P Gfit Afit
        (reg (tn n w)) w := by
      exact ⟨(hGood w hw (tn n w) ht).1, (hGood w hw (tn n w) ht).2.1,
        (hGood w hw (tn n w) ht).2.2.1⟩
    have hIdentity := ipw_mean_decomposition_of_score_moment E hRV hNoise hX
      hHomogeneity hMean heven hOverlap hGBound ht1 hb P Gfit Afit
      (by intro i j hij; exact le_rfl) (reg (tn n w)) w
      hNuisanceAt
      (by simpa only [abs_sub_comm] using (hGood w hw (tn n w) ht).1)
      hRad (hGood w hw (tn n w) ht).2.2.2.1
    let N := Real.log (6 / delta) * (n : ℝ) ^ (-(1 / 2 : ℝ))
    let Z := (n : ℝ) ^ (-cAlpha) * Real.log n * Real.log (6 / delta)
    let H := |M.alpha| * hillErrorBound M Cg delta n
    let e := nuisanceConstant * N + exponentMeanConstant * Z +
      (2 * eBar M (tn n w) + 2 * M.L * angularW1 M (tn n w))
    have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
    have hlogd : 0 ≤ Real.log (6 / delta) := by
      apply Real.log_nonneg
      apply (one_le_div hdelta).mpr
      linarith
    have hN0 : 0 ≤ N := by dsimp [N]; positivity
    have hZ0 : 0 ≤ Z := by dsimp [Z]; positivity
    have hH0 : 0 ≤ H := mul_nonneg (abs_nonneg _) ((abs_nonneg _).trans hHillGood.1)
    have hAngular : 0 ≤ 2 * M.L * angularW1 M (tn n w) :=
      mul_nonneg (mul_nonneg (by norm_num) hHomogeneity.2.2.2.1)
        (angularW1_nonneg M _)
    have hMeanBound := adaptive_ipw_mean_error_bound E hRV hNoise hX hHomogeneity
      hMean heven hOverlap hGBound ht1 hb w hIdentity
      (hBias w hw hTrain (tn n w) ht)
      (by simpa only [abs_sub_comm] using (hGood w hw (tn n w) ht).1)
      hRad hMoment
    have hcoef : 2 * (Cgb + eBar M (tn n w)) / c ≤ 2 * (Cgb + 1) / c := by
      apply div_le_div_of_nonneg_right _ hOverlap.1.le
      linarith
    have hMeanGood : |thresholdScoreMean E .ipw n (tn n w) w - etaTarget M| ≤ e := by
      apply hMeanBound.trans
      have hExpBound : (2 * (Cgb + eBar M (tn n w)) / c) *
          (exponentConstant * Z) ≤ exponentMeanConstant * Z := by
        calc
          _ ≤ (2 * (Cgb + 1) / c) * (exponentConstant * Z) :=
            mul_le_mul_of_nonneg_right hcoef (mul_nonneg hExponentConstant.le hZ0)
          _ = _ := by dsimp [exponentMeanConstant]; ring
      simpa only [e, N, Z, mul_assoc] using
        add_le_add (add_le_add (le_refl (nuisanceConstant * N)) hExpBound)
          (le_refl (2 * eBar M (tn n w) + 2 * M.L * angularW1 M (tn n w)))
    refine ⟨e, hBounds, hMeanGood, ?_⟩
    have hMain := rate_weighted_sum_bound
      (S := Real.sqrt (V / delta) * (n : ℝ) ^ (-r))
      (N := N) (E := eBar M (tn n w)) (A := 2 * M.L * angularW1 M (tn n w))
      (Z := Z) (B := 0) (cs := samplingConstant) (cn := nuisanceConstant)
      (cz := exponentMeanConstant + 1) (D := C)
      (by positivity) hN0 he0 hAngular hZ0 (by norm_num) hCs hCn hCe
      (by linarith : 1 ≤ C) hCz
    have hHillTerm : H ≤ C * H := le_mul_of_one_le_left hH0 (by linarith)
    have hSum := add_le_add hMain hHillTerm
    have hOld : samplingConstant * Real.sqrt (V / delta) * (n : ℝ) ^ (-r) + e +
        adaptiveRadialScale M Cg delta cAlpha n ≤ C * corRate E .ipw tn V Cg delta cAlpha r n w := by
      convert hSum using 1 <;> first
        | rfl
        | (try dsimp only [e, N, Z, H, adaptiveRadialScale, corRate]); ring
    calc
      _ ≤ C * corRate E .ipw tn V Cg delta cAlpha r n w := hOld
      _ ≤ C * (angularConstant * corRateAngular E .ipw tn k V Cg delta cAlpha r n w) :=
        mul_le_mul_of_nonneg_left
          (hAngularCompare w ht ((abs_nonneg _).trans hHillGood.1)) hC.le
      _ = _ := by ring
  filter_upwards [] with n
  intro heven hiid hMoments reg G hreg hGtraining hPseudo hGood hBias
  by_cases hEmpty : G = ∅
  · refine ⟨fun _ => Set.univ, fun _ => MeasurableSet.univ, ?_, ?_, ?_⟩
    · simp only [hEmpty, Set.empty_sdiff, measureReal_empty]
      positivity
    · simp only [hEmpty, Set.empty_sdiff, measureReal_empty]
      positivity
    · intro w hw
      simp [hEmpty] at hw
  -- Localized envelopes give both uniform sampling events without conditioning
  -- on the selected threshold; the exceptional domination set is null.
  suffices hEnvelopes : ∃ H : Fin 2 → E.Om → ℝ,
      (∀ i, Measurable (H i)) ∧ (∀ i, Integrable (H i) E.P) ∧
      (∀ i, ∀ᵐ w ∂E.P, 0 ≤ H i w) ∧
      (∫ w, H 0 w ∂E.P) ≤ 8 * (n : ℝ) * V *
        tailProb M ((cminus / 2) * (n : ℝ) ^ kappa (gamma M)) ∧
      (∫ w, H 1 w ∂E.P) ≤ 8 * (n : ℝ) *
        tailProb M ((cminus / 2) * (n : ℝ) ^ kappa (gamma M)) ∧
      ∀ᵐ w ∂E.P, w ∈ G → ∀ t ∈ thresholdBand M cminus cplus kappa n,
        thresholdCenteredScore E .ipw n t w ^ 2 ≤ H 0 w ∧
        thresholdCenteredCount E n t w ^ 2 ≤ H 1 w by
    obtain ⟨H, hMeas, hInt, hNonneg, hScore, hCount, hDom⟩ := hEnvelopes
    obtain ⟨S, hS, hScoreFailure, hCountFailure, hBounds⟩ :=
      threshold_maximal_events_of_ae_square_envelopes E .ipw n
        (thresholdBand M cminus cplus kappa n) G H
        hMeas hInt hNonneg hdelta hScore hCount hDom
    refine ⟨S, hS, hScoreFailure, hCountFailure, ?_⟩
    intro w hw hHillGood hTrain hEval hProcesses
    exact hBounds w hw hProcesses
  classical
  let ell := (cminus / 2) * (n : ℝ) ^ kappa (gamma M)
  have hEllBand : ell ∈ thresholdBand M cminus cplus kappa n := by
    change ell ∈ Set.Icc ell (2 * cplus * (n : ℝ) ^ kappa (gamma M))
    refine ⟨le_rfl, ?_⟩
    dsimp only [ell]
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    linarith [hOrder.1, hOrder.2.1]
  obtain ⟨w0, hw0⟩ := Set.nonempty_iff_ne_empty.mpr hEmpty
  have hV0 : 0 ≤ V :=
    (integral_nonneg (fun z => sq_nonneg (score E .ipw n w0 z))).trans
      (hGood w0 hw0 ell hEllBand).2.2.2.2
  obtain ⟨Hs, hHs, hIs, hNs, hBs, hDs⟩ :=
    evaluation_localized_score_square_envelope E .ipw n heven hiid
      (hExponentTraining n heven) hRV G hGtraining
      (thresholdBand M cminus cplus kappa n) ell hEllBand
      (fun t ht => ht.1) hV0
      (fun w hw t ht => (hGood w hw t ht).2.2.2.1)
      (fun w hw => (hGood w hw ell hEllBand).2.2.2.2)
  obtain ⟨Hc, hHc, hIc, hNc, hBc, hDc⟩ :=
    evaluation_localized_count_square_envelope E n heven hiid G hGtraining ell
  refine ⟨![Hs, Hc], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · simpa using hHs
    · simpa using hHc
  · intro i
    fin_cases i
    · simpa using hIs
    · simpa using hIc
  · intro i
    fin_cases i
    · exact Filter.Eventually.of_forall hNs
    · exact Filter.Eventually.of_forall hNc
  · simpa only [Matrix.cons_val_zero, ell] using hBs
  · simpa only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons, ell] using hBc
  · filter_upwards [hDs, hDc] with w hs hc
    intro hw t ht
    exact ⟨hs hw t ht, hc hw t ht.1⟩

end Papers.TbsExtremeEffects

module
public import Papers.TbsExtremeEffects.Helpers.TruncatedJointLimit
public import Papers.TbsExtremeEffects.Helpers.TailConditionalMean
public import Papers.TbsExtremeEffects.Helpers.ParetoRadial
public import Papers.TbsExtremeEffects.Helpers.JointWeakLimit
public import Papers.TbsExtremeEffects.Helpers.RegressionPositivity

/-! Population identification and convergence of both factors. -/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
variable {q d m : ℕ}

-- @node: prop:id
/-- [The extreme model $M$](hyp:M), [proportional identification regular variation](hyp:hPropRV), [consistency](hyp:hConsistency), [exogeneity](hyp:hExogeneity), [noise regular variation](hyp:hRV), [noise independence](hyp:hNoise), [bounded covariates](hyp:hX), [asymptotic homogeneity](hyp:hHomogeneity), [a conditional-mean version](hyp:hMean), [an outcome exponent below the tail index](hyp:hAlpha), and [the identification side conditions](hyp:hSide) imply [that the angular and radial factors, and their product NETE estimator, converge to the stated targets and identify the NETE parameter](goal). -/
theorem nete_identification (M : ExtremeModel q d)
    (hPropRV : PropIdRegularVariation M)
    (hConsistency : Consistency M) (hExogeneity : Exogeneity M)
    (hRV : NoiseRegularlyVarying M) (hNoise : NoiseIndependent M)
    (hX : CovariateBounded M) (hHomogeneity : AsymptoticHomogeneity M)
    (hMean : ConditionalMeanVersion M) (hAlpha : M.alpha < M.beta)
    (hSide : IdentificationSideConditions M) :
    Tendsto (angularFactor M) atTop (𝓝 (etaTarget M)) ∧
    Tendsto (radialFactor M) atTop (𝓝 (M.beta / (M.beta - M.alpha))) ∧
    Tendsto (neteAt M) atTop (𝓝 (etaTarget M * (M.beta / (M.beta - M.alpha)))) ∧
    Tendsto (neteAt M) atTop (𝓝 (thetaNETE M)) ∧
    thetaNETE M = limUnder atTop (angularFactor M) * limUnder atTop (radialFactor M) := by
  have hRadial := radial_moment_limit M hRV hAlpha
  have hAngular := angularFactor_tendsto_etaTarget M hRV hNoise hX hHomogeneity
  suffices hNete : Tendsto (neteAt M) atTop
      (𝓝 (etaTarget M * (M.beta / (M.beta - M.alpha)))) by
    have hTheta : thetaNETE M = etaTarget M * (M.beta / (M.beta - M.alpha)) :=
      hNete.limUnder_eq
    refine ⟨hAngular, hRadial, hNete, ?_, ?_⟩
    · rw [hTheta]
      exact hNete
    · rw [hAngular.limUnder_eq, hRadial.limUnder_eq, hTheta]
  obtain ⟨H, hH⟩ := angular_contrast_bounded_extension M hHomogeneity
  let : IsProbabilityMeasure M.S := hRV.2.2.spectral_probability
  let : IsProbabilityMeasure (paretoMeasure 1 M.beta) :=
    isProbabilityMeasure_paretoMeasure (by norm_num) hRV.1
  let ρ : ProbabilityMeasure ℝ := ⟨paretoMeasure 1 M.beta, inferInstance⟩
  have hRad : Integrable (fun r => (max 1 r) ^ M.alpha) (ρ : Measure ℝ) :=
    pareto_clamped_power_integrable hRV.1 hAlpha
  have hMoment : (∫ r, (max 1 r) ^ M.alpha ∂(ρ : Measure ℝ)) =
      M.beta / (M.beta - M.alpha) := pareto_clamped_power_moment hRV.1 hAlpha
  suffices hRemaining :
      ∀ a : Bool, ∀ᵐ w ∂M.mu, M.D w ≠ a →
        M.f (M.X w) a (M.U w) = conditionalPotentialMean M a (sigmaXU M) w by
    have hWeighted : Tendsto (fun t => ∫ w, weightedAngularContrast M t w ∂tailLaw M t)
        atTop (𝓝 (etaTarget M * (M.beta / (M.beta - M.alpha)))) := by
      by_cases hz : M.alpha = 0
      · exact weightedAngularContrast_tendsto_of_alpha_zero M hRV hNoise hX hHomogeneity hz
      · have hweak := radialAngularLaw_weak_limit M hRV
        have hClipped := clippedJointContrast_product_limit M hRV hX H hH
          (ρ : Measure ℝ) hRad hMoment
        exact weightedAngularContrast_tendsto_of_truncated_joint_limit M hRV hNoise hX
          hHomogeneity hAlpha H hH ⟨(ρ : Measure ℝ).prod M.S, inferInstance⟩ hweak hClipped
    have hRegression (a : Bool) : (fun w => M.f (M.X w) a (M.U w)) =ᵐ[M.mu]
        conditionalPotentialMean M a (sigmaXU M) := by
      filter_upwards [regression_eq_potentialMean_on_treatment M hConsistency hMean hSide a,
        hRemaining a] with w hon hoff
      by_cases hwa : M.D w = a
      · exact hon hwa
      · exact hoff hwa
    apply (regression_integral_tendsto_of_weighted M hRV hX hHomogeneity hMean hAlpha
      hWeighted).congr'
    filter_upwards [neteAt_eq_conditionalPotentialMean_eventually M hRV hSide] with t ht
    rw [ht]
    apply integral_congr_ae
    filter_upwards [cond_absolutelyContinuous.ae_le (hRegression true),
      cond_absolutelyContinuous.ae_le (hRegression false)] with w h1 h0
    simp only [regressionContrast, h1, h0]
  intro a
  filter_upwards [regression_eq_potentialMean M hConsistency hMean hNoise hSide a]
    with w hw _
  exact hw

end Papers.TbsExtremeEffects

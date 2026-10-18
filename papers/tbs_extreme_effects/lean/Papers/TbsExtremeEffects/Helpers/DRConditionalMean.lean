module
public import Papers.TbsExtremeEffects.Helpers.IPWMean

/-! DR treatment-averaged score algebra and integration of its mean decomposition.
The conditional treatment/outcome identities remain explicit proof obligations. -/

@[expose] public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
variable {q d : ℕ} {M : ExtremeModel q d}

/-- For [an experiment](hyp:E), [a sample size](hyp:n), [a regression function](hyp:reg), [a realized training outcome](hyp:w), and [a latent population observation](hyp:v), [the fitted-regression doubly robust mean integrand](goal) combines the fitted treatment contrast, propensity-weighted regression corrections, and the exponent mean integrand.

@node: drFittedRegressionMean
-/
noncomputable def drFittedRegressionMean (E : NeteExperiment M) (n : ℕ)
    (reg : ((Fin q → ℝ) × Bool × (Fin d → ℝ)) → ℝ) (w : E.Om) (v : M.Om) : ℝ :=
  E.gHat n w (M.X v) true (direction M v) -
    E.gHat n w (M.X v) false (direction M v) +
    M.p (M.X v) / E.pHat n w (M.X v) *
      (reg (M.X v, true, direction M v) - E.gHat n w (M.X v) true (direction M v)) -
    (1 - M.p (M.X v)) / (1 - E.pHat n w (M.X v)) *
      (reg (M.X v, false, direction M v) - E.gHat n w (M.X v) false (direction M v)) +
    exponentMeanIntegrand E n w v

/-- For [an experiment](hyp:E), [a sample size](hyp:n), [a tail threshold](hyp:t), [a regression function](hyp:reg), and [a realized training outcome](hyp:w), [the doubly robust conditional-score mean condition](goal) requires: [the score-tail mean to equal the fitted-regression mean](step:1), [integrability of the regression contrast](step:2), and [agreement of that contrast's mean with the normalized regression contrast](step:3).

@node: DrConditionalScoreMean
-/
def DrConditionalScoreMean (E : NeteExperiment M) (n : ℕ) (t : ℝ)
    (reg : ((Fin q → ℝ) × Bool × (Fin d → ℝ)) → ℝ) (w : E.Om) : Prop :=
  (∫ z, score E .dr n w z ∂obsTailLaw M t) =
    (∫ v, drFittedRegressionMean E n reg w v ∂tailLaw M t) ∧
  Integrable (fun v => reg (M.X v, true, direction M v) -
    reg (M.X v, false, direction M v)) (tailLaw M t) ∧
  (∫ v, reg (M.X v, true, direction M v) - reg (M.X v, false, direction M v)
      ∂tailLaw M t) = ∫ v, normalizedRegressionContrast M v ∂tailLaw M t

/-- Given [an even sample size](hyp:hn) and [estimated overlap](hyp:hOverlap), [the fitted-regression doubly robust mean integrand decomposes into nuisance-product bias, exponent mean, and the regression treatment contrast](goal).

@node: dr_fitted_regression_mean_decomposition
-/
lemma dr_fitted_regression_mean_decomposition (E : NeteExperiment M)
    {n : ℕ} (hn : EvenSampleSize n) {c : ℝ} (hOverlap : EstimatedOverlap E c)
    (reg : ((Fin q → ℝ) × Bool × (Fin d → ℝ)) → ℝ) (w : E.Om) (v : M.Om) :
    drFittedRegressionMean E n reg w v = drBiasIntegrand E n reg w v +
      exponentMeanIntegrand E n w v +
      (reg (M.X v, true, direction M v) - reg (M.X v, false, direction M v)) := by
  have hp := hOverlap.2.2 n hn w (M.X v) (M.X_mem_domain v)
  have hp0 := (hOverlap.1.trans_le hp.1).ne'
  have hp1 : 1 - E.pHat n w (M.X v) ≠ 0 := by
    have : c ≤ 1 - E.pHat n w (M.X v) := by linarith [hp.2]
    exact (hOverlap.1.trans_le this).ne'
  have hBias := dr_conditional_bias_identity
    (p := M.p (M.X v))
    (m1 := reg (M.X v, true, direction M v))
    (m0 := reg (M.X v, false, direction M v))
    (g1 := E.gHat n w (M.X v) true (direction M v))
    (g0 := E.gHat n w (M.X v) false (direction M v)) hp0 hp1
  unfold drFittedRegressionMean drBiasIntegrand
  linarith only [hBias]

/-- If [the noise is regularly varying](hyp:hRV), [covariates are bounded](hyp:hX), [the model is asymptotically homogeneous](hyp:hHom), [the required conditional-mean version holds](hyp:hMean), [the sample size is even](hyp:hn), [estimated overlap holds](hyp:hOverlap), [the fitted regression is uniformly bounded](hyp:hG), [the tail threshold is at least one](hyp:ht), [the tail exponent set is bounded above](hyp:hb), [the first nuisance rate is antitone in sample size](hyp:hRp), [the regression is measurable](hyp:hreg), [the nuisance condition holds at the realized outcome](hyp:hNuisance), [the exponent estimation error is bounded](hyp:hErr), [the required radial moment is integrable](hyp:hRad), and [the doubly robust conditional-score mean condition holds](hyp:hIdentity), then [the doubly robust mean decomposition holds](goal).

@node: dr_mean_decomposition_of_conditional_score_mean
-/
lemma dr_mean_decomposition_of_conditional_score_mean (E : NeteExperiment M)
    (hRV : NoiseRegularlyVarying M) (hX : CovariateBounded M)
    (hHom : AsymptoticHomogeneity M) (hMean : ConditionalMeanVersion M)
    {n : ℕ} (hn : EvenSampleSize n) {c C t eps a : ℝ}
    (hOverlap : EstimatedOverlap E c) (hG : GBound M C) (ht : 1 ≤ t)
    (hb : BddAbove (M.e '' Set.Ici t)) (Rp Rg Ralpha : ℕ → ℝ → ℝ)
    (hRp : Antitone (fun k => Rp k eps))
    (reg : ((Fin q → ℝ) × Bool × (Fin d → ℝ)) → ℝ) (hreg : Measurable reg)
    (w : E.Om) (hNuisance : NuisanceAt E n t eps Rp Rg Ralpha reg w)
    (hErr : |M.alpha - E.alphaHat n w| ≤ a)
    (hRad : Integrable (fun v => radius M v ^ a - 1) (tailLaw M t))
    (hIdentity : DrConditionalScoreMean E n t reg w) :
    DrMeanDecomposition E n t reg w := by
  obtain ⟨hScore, hRegInt, hRegMean⟩ := hIdentity
  have hBias := dr_nuisance_bias_integrable E hRV hn hOverlap Rp Rg Ralpha hRp
    reg hreg w hNuisance
  have hExp := exponentMeanIntegrand_integrable E hX hHom hMean hn hOverlap hG
    ht hb w hErr hRad
  unfold DrMeanDecomposition
  rw [hScore]
  have hDecomp : (∫ v, drFittedRegressionMean E n reg w v ∂tailLaw M t) =
      (∫ v, drBiasIntegrand E n reg w v ∂tailLaw M t) +
      (∫ v, exponentMeanIntegrand E n w v ∂tailLaw M t) +
      ∫ v, reg (M.X v, true, direction M v) - reg (M.X v, false, direction M v)
        ∂tailLaw M t := by
    calc
      _ = ∫ v, drBiasIntegrand E n reg w v + exponentMeanIntegrand E n w v +
          (reg (M.X v, true, direction M v) - reg (M.X v, false, direction M v))
          ∂tailLaw M t := integral_congr_ae (Eventually.of_forall
            (dr_fitted_regression_mean_decomposition E hn hOverlap reg w))
      _ = _ := by rw [integral_add (show Integrable (fun v => drBiasIntegrand E n reg w v +
          exponentMeanIntegrand E n w v) (tailLaw M t) from hBias.add hExp) hRegInt,
          integral_add hBias hExp]
  rw [hDecomp, hRegMean]
  ring

end Papers.TbsExtremeEffects

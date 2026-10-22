module
public import Papers.TbsExtremeEffects.Basic
public import Papers.TbsExtremeEffects.Helpers.Potter
public import Papers.TbsExtremeEffects.Helpers.TailIntegrals
public import Papers.TbsExtremeEffects.Helpers.ConditionalMoments
public import Papers.TbsExtremeEffects.Helpers.AngularConvergence

/-! Consequences of the pinned regular-variation convergence. -/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
variable {q d m : ℕ}

-- @node: radial_moment_limit
/-- If [the noise is regularly varying](hyp:hRV) and [the tail index is below the moment exponent](hyp:hAlpha), then [the radial normalization factor converges to the stated ratio of exponents](goal). -/
lemma radial_moment_limit (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (hAlpha : AlphaLtBeta M) :
    Tendsto (radialFactor M) atTop (𝓝 (M.beta / (M.beta - M.alpha))) := by
  by_cases hzero : M.alpha = 0
  · have heq : radialFactor M = fun _ => (1 : ℝ) :=
      funext (radialFactor_eq_one_of_alpha_zero M hRV hzero)
    rw [heq, hzero, sub_zero, div_self hRV.1.ne']
    exact tendsto_const_nhds
  · apply (tail_integral_limit M hRV (a := M.alpha) hAlpha).congr'
    filter_upwards [conditional_radial_power_layercake M hRV hAlpha hzero] with t ht
    exact ht.symm

-- @node: spectral_test_limit
/-- If [the noise is regularly varying](hyp:hRV) and [the test function is continuous](hyp:hphi), then [its expectation under the angular tail law converges to its expectation under the spectral law](goal). -/
lemma spectral_test_limit (M : ExtremeModel q d) (hRV : NoiseRegularlyVarying M)
    (phi : (Fin d → ℝ) → ℝ) (hphi : Continuous phi) :
    Tendsto (fun t => ∫ u, phi u ∂((tailLaw M t).map (direction M)))
      atTop (𝓝 (∫ u, phi u ∂M.S)) := by
  obtain ⟨C₀, hC₀⟩ := isCompact_positiveSphere_l1.exists_bound_of_continuousOn hphi.continuousOn
  let C := max C₀ 0
  have hC : 0 ≤ C := le_max_right _ _
  let clipped : (Fin d → ℝ) → ℝ := fun u => max (-C) (min C (phi u))
  have hclip (u : Fin d → ℝ) : -C ≤ clipped u ∧ clipped u ≤ C := by
    refine ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  let test : BoundedContinuousFunction (Fin d → ℝ) ℝ :=
    BoundedContinuousFunction.mkOfBound ⟨clipped, by fun_prop⟩ (2 * C) (by
      intro u v
      change dist (clipped u) (clipped v) ≤ 2 * C
      rw [Real.dist_eq]
      exact abs_le.2 ⟨by linarith [(hclip u).1, (hclip v).2],
        by linarith [(hclip u).2, (hclip v).1]⟩)
  have heq (u : Fin d → ℝ) (hu : u ∈ positiveSphere l1Norm) : test u = phi u := by
    have hb : |phi u| ≤ C := (hC₀ u hu).trans (le_max_left _ _)
    have hrange := abs_le.1 hb
    change max (-C) (min C (phi u)) = phi u
    rw [min_eq_right hrange.2, max_eq_right hrange.1]
  have hlim := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1
    (angular_law_weak_limit M hRV)) test
  have hspec : (∫ u, test u ∂M.S) = ∫ u, phi u ∂M.S := by
    apply integral_congr_ae
    filter_upwards [spectral_ae_sphere M hRV] with u hu
    exact heq u hu
  change Tendsto (fun t => ∫ u, test u ∂((tailLaw M t).map (direction M)))
    atTop (𝓝 (∫ u, test u ∂M.S)) at hlim
  rw [hspec] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  apply integral_congr_ae
  filter_upwards [angular_law_ae_sphere M ht] with u hu
  exact heq u hu

end Papers.TbsExtremeEffects

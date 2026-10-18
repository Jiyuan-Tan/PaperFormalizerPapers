module
public import Papers.TbsPrteOptimalTransport.Helpers.QuantileGridTransfer
public import Papers.TbsPrteOptimalTransport.Helpers.PluginPopulation
/-! Triangle and expectation assembly for selected boundary quantile errors. -/
public section
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

-- @node: supported_interior_quantile_integrable
/-- If [the absolute quantile is bounded by C at every rank strictly between zero and one](hyp:hb), [the quantile function is integrable over the closed unit rank interval](goal). -/
lemma supported_interior_quantile_integrable (ν : Measure ℝ) (C : ℝ)
    (hb : ∀ t ∈ Ioo (0 : ℝ) 1, |Causalean.Stat.quantile ν t| ≤ C) :
    IntegrableOn (Causalean.Stat.quantile ν) (Icc (0 : ℝ) 1) := by
  rw [IntegrableOn, ← restrict_Ioo_eq_restrict_Icc]
  apply Integrable.of_bound
    (Causalean.Stat.aemeasurable_quantile_unifOI ν).aestronglyMeasurable C
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact hb t ht

-- @node: fitted_selected_boundary_triangle
/-- If [the fitted rank function is nondecreasing on the open unit interval](hyp:hmono), [it is integrable on the closed unit interval](hyp:hQ), and [the quantiles of the intermediate law](hyp:hν) and [the target law](hyp:hξ) are integrable there, [the integrated absolute quantile distance from the fitted distribution to the target is at most the fitted function's integrated absolute error against the intermediate quantile plus the quantile distance from the intermediate law to the target](goal). -/
lemma fitted_selected_boundary_triangle (Q : ℝ → ℝ) (ν ξ : Measure ℝ)
    (hmono : MonotoneOn Q (Ioo (0 : ℝ) 1))
    (hQ : IntegrableOn Q (Icc (0 : ℝ) 1))
    (hν : IntegrableOn (Causalean.Stat.quantile ν) (Icc (0 : ℝ) 1))
    (hξ : IntegrableOn (Causalean.Stat.quantile ξ) (Icc (0 : ℝ) 1)) :
    quantileDistanceIntegral (Causalean.Stat.unifOI.map Q) ξ ≤
      (∫ t in Ioo (0 : ℝ) 1, |Q t - Causalean.Stat.quantile ν t|) +
        quantileDistanceIntegral ν ξ := by
  rw [quantile_distance_uniform_map Q ξ hmono, quantileDistanceIntegral,
    restrict_Ioo_eq_restrict_Icc]
  calc
    _ ≤ ∫ t in Icc (0 : ℝ) 1,
        |Q t - Causalean.Stat.quantile ν t| +
          |Causalean.Stat.quantile ν t - Causalean.Stat.quantile ξ t| := by
      apply integral_mono ((hQ.sub hξ).abs)
        (((hQ.sub hν).abs).add ((hν.sub hξ).abs))
      intro t
      exact abs_sub_le _ _ _
    _ = _ := by
      simpa only [Pi.sub_apply] using
        integral_add ((hQ.sub hν).abs) ((hν.sub hξ).abs)

universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]

-- @node: selected_boundary_rank_integrable
/-- Given [fallback outcome distributions supported on the outcome set](hyp:zeroLaw), [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he), and [joint measurability of each fitted propensity in the sample, instrument, and covariates](hyp:hp), [for almost every covariate value both the selected-law quantile and the boundary-law quantile are integrable over the closed unit rank interval](goal). -/
lemma selected_boundary_rank_integrable (M : LatentIVModel Ω X Z)
    (zeroLaw : X → {ν : ProbabilityMeasure ℝ // ν.toMeasure M.Ysetᶜ = 0})
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (pHat : ℕ → A → Z → X → ℝ) (delta : ℕ → ℝ)
    (hp : ∀ n, Measurable (fun ax : A × Z × X => pHat n ax.1 ax.2.1 ax.2.2))
    (n : ℕ) (a : A) :
    ∀ᵐ x ∂xLaw M,
      IntegrableOn (selQuantile M zeroLaw pHat delta n a x) (Icc (0 : ℝ) 1) ∧
      IntegrableOn (Causalean.Stat.quantile (boundaryLaw M zeroLaw x))
        (Icc (0 : ℝ) 1) := by
  filter_upwards [selected_quantile_supported M zeroLaw h he pHat delta hp n a,
    boundary_quantile_supported M zeroLaw h he] with x hs hb
  constructor
  · exact supported_interior_quantile_integrable _ (outcomeMagnitude M)
      (fun t ht => outcome_norm_le_magnitude M he (hs t ht))
  · apply supported_interior_quantile_integrable _ (outcomeMagnitude M)
    intro t ht
    rw [← boundaryQuantile_eq_quantile_of_mem_Ioo M zeroLaw x ht]
    exact outcome_norm_le_magnitude M he (hb t ht)

-- @node: interpolated_boundary_error_via_selected
/-- Suppose [supported fallback outcome distributions are chosen](hyp:zeroLaw), [the structural assumptions hold](hyp:h), [outcome endpoints are known](hyp:he), [each fitted propensity is jointly measurable](hyp:hp), [each grid size is positive](hyp:hMQ), [trimming levels are nonnegative](hyp:heps), and [grids have at least two cells when endpoints are not imposed](hyp:hInterior). If [the interpolated fitted quantile is nondecreasing at every covariate value](hyp:hm), [its lower-endpoint-weighted quantile distance from the boundary law is almost surely bounded by the weighted trimmed grid error, twice the outcome range times trimming, four times the outcome range divided by grid size, and the weighted distance from the selected law to the boundary law](goal). -/
lemma interpolated_boundary_error_via_selected (M : LatentIVModel Ω X Z)
    (zeroLaw : X → {ν : ProbabilityMeasure ℝ // ν.toMeasure M.Ysetᶜ = 0})
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (pHat : ℕ → A → Z → X → ℝ) (delta : ℕ → ℝ)
    (hp : ∀ n, Measurable (fun ax : A × Z × X => pHat n ax.1 ax.2.1 ax.2.2))
    (raw : ℕ → A → ℕ → X → ℝ) (MQ : ℕ → ℕ) (hMQ : ∀ n, 0 < MQ n)
    (eps : ℕ → ℝ) (heps : ∀ n, 0 ≤ eps n) (knownEndpoints : Bool)
    (hInterior : knownEndpoints = false → ∀ n, 2 ≤ MQ n)
    (n : ℕ) (a : A)
    (hm : ∀ x, MonotoneOn
      (interpolatedQuantile M raw (MQ n) (hMQ n) knownEndpoints
        (fun hk => hInterior hk n) n a x) (Ioo (0 : ℝ) 1)) :
    ∀ᵐ x ∂xLaw M,
      pLow M.prop x * quantileDistanceIntegral
        (boundaryLawHat (fun n a x => interpolatedQuantile M raw (MQ n) (hMQ n)
          knownEndpoints (fun hk => hInterior hk n) n a x) n a x)
        (boundaryLaw M zeroLaw x) ≤
      pLow M.prop x * (MQ n : ℝ)⁻¹ *
        (∑ m ∈ interiorIdx MQ hMQ eps n, |clippedGrid M raw n a m x -
          selQuantile M zeroLaw pHat delta n a x (gridLevel (MQ n) (hMQ n) m)|) +
        2 * (M.yMax - M.yMin) * eps n +
        4 * (M.yMax - M.yMin) * (MQ n : ℝ)⁻¹ +
        pLow M.prop x * quantileDistanceIntegral
          (selLaw M zeroLaw pHat delta n a x) (boundaryLaw M zeroLaw x) := by
  filter_upwards [selected_boundary_rank_integrable M zeroLaw h he pHat delta hp n a,
    interpolated_selected_trimmed_error_integral M zeroLaw h he pHat delta hp
      raw MQ hMQ eps heps knownEndpoints hInterior n a] with x hi hg
  let Q := interpolatedQuantile M raw (MQ n) (hMQ n) knownEndpoints
    (fun hk => hInterior hk n) n a x
  have hQi : IntegrableOn Q (Icc (0 : ℝ) 1) :=
    bounded_monotone_rank_integrable Q (hm x)
      (fitted_quantile_magnitude M (fun _ t _ =>
        interpolated_quantile_range M he raw (MQ n) (hMQ n) knownEndpoints
          (fun hk => hInterior hk n) n a x t) x)
  have ht := mul_le_mul_of_nonneg_left
    (fitted_selected_boundary_triangle Q (selLaw M zeroLaw pHat delta n a x)
      (boundaryLaw M zeroLaw x) (hm x) hQi hi.1 hi.2)
    (population_support_endpoints M x).1.1
  rw [mul_add] at ht
  exact ht.trans (add_le_add hg le_rfl)

-- @node: boundary_grid_envelope_integral
/-- If [the target function is nonnegative everywhere](hyp:hf), [each error function indexed by the finite grid is integrable](hyp:hg), and [the target is almost surely bounded by the mesh factor times the sum of grid errors plus localization, trimming, and discretization constants](hyp:hbound), [its integral is at most the mesh factor times the sum of integrated grid errors plus those same constants](goal). -/
lemma boundary_grid_envelope_integral {T ι : Type*} [MeasurableSpace T]
    (μ : Measure T) [IsProbabilityMeasure μ] (s : Finset ι)
    (f : T → ℝ) (g : ι → T → ℝ) (mesh loc trim disc : ℝ)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ i ∈ s, Integrable (g i) μ)
    (hbound : ∀ᵐ x ∂μ, f x ≤ mesh * (∑ i ∈ s, g i x) + loc + trim + disc) :
    (∫ x, f x ∂μ) ≤ mesh * (∑ i ∈ s, ∫ x, g i x ∂μ) + loc + trim + disc := by
  have hs : Integrable (fun x => ∑ i ∈ s, g i x) μ := integrable_finsetSum s hg
  calc
    _ ≤ ∫ x, mesh * (∑ i ∈ s, g i x) + loc + trim + disc ∂μ :=
      integral_mono_of_nonneg (Eventually.of_forall hf)
        ((((hs.const_mul mesh).add (integrable_const loc)).add
          (integrable_const trim)).add (integrable_const disc)) hbound
    _ = _ := by
      rw [integral_add (f := fun x => mesh * (∑ i ∈ s, g i x) + loc + trim)
          (((hs.const_mul mesh).add (integrable_const loc)).add
          (integrable_const trim)) (integrable_const disc),
        integral_add (f := fun x => mesh * (∑ i ∈ s, g i x) + loc)
          ((hs.const_mul mesh).add (integrable_const loc))
          (integrable_const trim),
        integral_add (hs.const_mul mesh) (integrable_const loc),
        integral_const_mul, integral_finsetSum s hg]
      simp

end Papers.TbsPrteOptimalTransport

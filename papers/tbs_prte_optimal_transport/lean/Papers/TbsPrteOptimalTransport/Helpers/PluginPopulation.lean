module
public import Papers.TbsPrteOptimalTransport.Helpers.PluginStability
public import Papers.TbsPrteOptimalTransport.Helpers.PluginRateAlgebra
public import Causalean.Tactic.IntegralLinearity
/-!
# Population perturbation of the continuous lower score

The quantile endpoints are null for the rank integral. The population
boundary law therefore needs support only at interior ranks; no lower bound
on the propensity endpoint is used.
-/
@[expose] public section
set_option linter.style.openClassical false
set_option linter.unusedSectionVars false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v
variable {Ω : Type u} {X Z : Type v}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]
variable (M : LatentIVModel Ω X Z)
  (zeroLaw : X → {ν : ProbabilityMeasure ℝ // ν.toMeasure M.Ysetᶜ = 0})

-- @node: boundary_quantile_rank_integrable
/-- Under [the model's structural assumptions](hyp:h) and [known outcome bounds](hyp:he),
[the boundary quantile is integrable over the unit rank interval for almost every covariate value](goal). -/
lemma boundary_quantile_rank_integrable
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M) :
    ∀ᵐ x ∂xLaw M, IntegrableOn (boundaryQuantile M zeroLaw x) (Icc (0 : ℝ) 1) := by
  filter_upwards [boundary_quantile_supported M zeroLaw h he] with x hx
  rw [IntegrableOn, ← restrict_Ioo_eq_restrict_Icc]
  apply Integrable.of_bound
    ((Causalean.Stat.aemeasurable_quantile_unifOI (boundaryLaw M zeroLaw x)).congr
      (boundaryQuantile_ae_quantile M zeroLaw x).symm).aestronglyMeasurable
    (outcomeMagnitude M)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact outcome_norm_le_magnitude M he (hx t ht)

-- @node: fitted_quantile_magnitude
/-- If [every fitted quantile on the unit rank interval lies between the model's outcome bounds](hyp:hQ),
[its absolute value is at most the larger absolute outcome bound, at every covariate and unit rank](goal). -/
lemma fitted_quantile_magnitude {Q : X → ℝ → ℝ}
    (hQ : ∀ x t, t ∈ Icc (0 : ℝ) 1 → Q x t ∈ Icc M.yMin M.yMax) :
    ∀ x t, t ∈ Icc (0 : ℝ) 1 → |Q x t| ≤ outcomeMagnitude M := by
  intro x t ht
  have hr := hQ x t ht
  have hlo : |M.yMin| ≤ outcomeMagnitude M := le_max_left _ _
  have hhi : |M.yMax| ≤ outcomeMagnitude M := le_max_right _ _
  apply abs_le.mpr
  constructor
  · linarith [neg_abs_le M.yMin, hr.1]
  · exact hr.2.trans ((le_abs_self M.yMax).trans hhi)

-- @node: fitted_lower_population_error_pointwise
/-- Under [the structural assumptions](hyp:h) and [known outcome bounds](hyp:he), suppose
[the policy map is admissible](hyp:hphi), [the fitted propensity lies in the unit interval](hyp:hp),
[the fitted quantile is nondecreasing on interior ranks](hyp:hm), and
[its values on all unit ranks lie between the outcome bounds](hyp:hQ).
Then [for almost every covariate value and every instrument, treatment, and outcome, the absolute difference between the fitted and population lower scores is bounded by the outcome-magnitude-weighted endpoint errors, the lower-propensity-weighted quantile distance, the two regression errors, and the absolute lower-outcome-bound-weighted excess-policy endpoint error](goal). -/
lemma fitted_lower_population_error_pointwise
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (p : Z → X → ℝ) (g : ℝ → X → ℝ) (Q : X → ℝ → ℝ)
    (hp : ∀ z x, p z x ∈ Icc (0 : ℝ) 1)
    (hm : ∀ x, MonotoneOn (Q x) (Ioo (0 : ℝ) 1))
    (hQ : ∀ x t, t ∈ Icc (0 : ℝ) 1 → Q x t ∈ Icc M.yMin M.yMax) :
    ∀ᵐ x ∂xLaw M, ∀ z w y,
      |fittedInt M false phi p g (fun x => quantilePrimitive (Q x)) (x,z,w,y) -
        fittedInt M false phi M.prop (g1 M)
          (fun x => quantilePrimitive (boundaryQuantile M zeroLaw x)) (x,z,w,y)| ≤
      outcomeMagnitude M *
        (2 * |endpointMap p (policyProp phi p) 0 (z,x) -
          endpointMap M.prop (policyProp phi M.prop) 0 (z,x)| +
          |endpointMap p (policyProp phi p) 1 (z,x) -
            endpointMap M.prop (policyProp phi M.prop) 1 (z,x)|) +
      pLow M.prop x * quantileDistanceIntegral
        (Causalean.Stat.unifOI.map (Q x)) (boundaryLaw M zeroLaw x) +
      (|g (clampPolicy p (policyProp phi p) z x) x -
          g1 M (clampPolicy M.prop (policyProp phi M.prop) z x) x| +
        |g (p z x) x - g1 M (M.prop z x) x|) +
      |M.yMin| * |endpointMap p (policyProp phi p) 2 (z,x) -
        endpointMap M.prop (policyProp phi M.prop) 2 (z,x)| := by
  have hb := fitted_quantile_magnitude M hQ
  have hC : 0 ≤ outcomeMagnitude M := (abs_nonneg M.yMin).trans (le_max_left _ _)
  filter_upwards [boundary_quantile_rank_integrable M zeroLaw h he] with x hx
  intro z w y
  have hi := bounded_monotone_rank_integrable (Q x) (hm x) (hb x)
  have herr := fittedInt_lower_error M phi hphi M.prop p (g1 M) g
    (boundaryQuantile M zeroLaw) Q M.rangeProp hp (x,z,w,y) hC hx hi (hb x)
  have hdist : (∫ t in Icc (0 : ℝ) 1, |Q x t - boundaryQuantile M zeroLaw x t|) =
      ∫ t in Icc (0 : ℝ) 1, |Q x t - Causalean.Stat.quantile (boundaryLaw M zeroLaw x) t| := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    apply integral_congr_ae
    filter_upwards [boundaryQuantile_ae_quantile M zeroLaw x] with t ht
    rw [ht]
  simpa only [endpointMap, Fin.reduceEq, if_true, if_false, hdist,
    quantile_distance_uniform_map (Q x) (boundaryLaw M zeroLaw x) (hm x)] using herr

-- @node: quantile_primitive_rescaled_tail
/-- If [the rank function is integrable on the unit interval](hyp:hQ),
[the scale is positive](hyp:hb), and [the cutoff is nonnegative](hyp:hq),
[its integral after dividing ranks by the scale, from the smaller of scale and cutoff to the scale, equals the scale times its primitive's increment from the smaller of one and cutoff divided by scale to one](goal). -/
lemma quantile_primitive_rescaled_tail (Q : ℝ → ℝ)
    (hQ : IntegrableOn Q (Icc (0 : ℝ) 1)) {b q : ℝ}
    (hb : 0 < b) (hq : 0 ≤ q) :
    (∫ v in Ioc (min b q) b, Q (v / b)) =
      b * (quantilePrimitive Q 1 - quantilePrimitive Q (min 1 (q / b))) := by
  have hmin : min b q / b = min 1 (q / b) := by
    rw [← min_div_div_right hb.le, div_self hb.ne']
  have ht : min 1 (q / b) ∈ Icc (0 : ℝ) 1 :=
    ⟨le_min zero_le_one (div_nonneg hq hb.le), min_le_left _ _⟩
  rw [← intervalIntegral.integral_of_le (min_le_left b q),
    intervalIntegral.integral_comp_div Q hb.ne', div_self hb.ne', hmin,
    quantile_tail_primitive Q hQ ht, smul_eq_mul]

-- @node: population_fitted_lower_eq_connected
/-- Under [the structural assumptions](hyp:h), [known outcome bounds](hyp:he), and
[an admissible policy map](hyp:hphi), [the lower score evaluated at the population propensity, regression, and boundary-quantile primitive equals the connected lower integrand for almost every covariate value and all instruments, treatments, and outcomes](goal). -/
lemma population_fitted_lower_eq_connected
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi) :
    ∀ᵐ x ∂xLaw M, ∀ z w y,
      fittedInt M false phi M.prop (g1 M)
        (fun x => quantilePrimitive (boundaryQuantile M zeroLaw x)) (x,z,w,y) =
      connectedInt M zeroLaw false (policyProp phi M.prop) (z,x) := by
  filter_upwards [boundary_quantile_rank_integrable M zeroLaw h he] with x hx
  intro z w y
  have hq := (hphi.2 z x (M.prop z x) (M.rangeProp z x)).1
  dsimp only [fittedInt, connectedInt]
  simp only [Bool.false_eq_true, if_false]
  by_cases hl : 0 < pLow M.prop x
  · simp only [if_pos hl]
    dsimp only [policyProp]
    rw [quantile_primitive_rescaled_tail (boundaryQuantile M zeroLaw x) hx hl hq]
    ring
  · simp only [if_neg hl, policyProp]

-- @node: lowerPopulationEnvelope
/-- For [the latent instrumental-variable model](hyp:M), [a fallback outcome law supported within its outcome bounds at each covariate](hyp:zeroLaw),
[a policy map](hyp:phi), [a fitted propensity](hyp:p), [a fitted regression](hyp:g),
[a fitted rank function](hyp:Q), and [an instrument–covariate pair](hyp:zx),
the [population lower-score error envelope](goal) adds the outcome magnitude times twice the lower-support endpoint error plus the truncated-policy endpoint error, the lower population propensity times the quantile distance to the boundary law, the regression errors at the clamped policy and original propensity, and the absolute lower outcome bound times the excess-policy endpoint error. -/
noncomputable def lowerPopulationEnvelope
    (phi : Z → X → ℝ → ℝ) (p : Z → X → ℝ)
    (g : ℝ → X → ℝ) (Q : X → ℝ → ℝ) (zx : Z × X) : ℝ :=
  outcomeMagnitude M *
    (2 * |endpointMap p (policyProp phi p) 0 zx -
      endpointMap M.prop (policyProp phi M.prop) 0 zx| +
      |endpointMap p (policyProp phi p) 1 zx -
        endpointMap M.prop (policyProp phi M.prop) 1 zx|) +
  pLow M.prop zx.2 * quantileDistanceIntegral
    (Causalean.Stat.unifOI.map (Q zx.2)) (boundaryLaw M zeroLaw zx.2) +
  (|g (clampPolicy p (policyProp phi p) zx.1 zx.2) zx.2 -
      g1 M (clampPolicy M.prop (policyProp phi M.prop) zx.1 zx.2) zx.2| +
    |g (p zx.1 zx.2) zx.2 - g1 M (M.prop zx.1 zx.2) zx.2|) +
  |M.yMin| * |endpointMap p (policyProp phi p) 2 zx -
    endpointMap M.prop (policyProp phi M.prop) 2 zx|

-- @node: fitted_lower_connected_error_ae
/-- Under [the structural assumptions](hyp:h), [known outcome bounds](hyp:he), and
[an admissible policy map](hyp:hphi), suppose [the fitted propensity lies in the unit interval](hyp:hp),
[the fitted quantiles are nondecreasing on interior ranks](hyp:hm), and
[all fitted unit-rank quantiles lie within the outcome bounds](hyp:hQ).
Then [the absolute difference between the fitted lower score and the population connected lower integrand is bounded by the population error envelope for almost every observation](goal). -/
lemma fitted_lower_connected_error_ae
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (p : Z → X → ℝ) (g : ℝ → X → ℝ) (Q : X → ℝ → ℝ)
    (hp : ∀ z x, p z x ∈ Icc (0 : ℝ) 1)
    (hm : ∀ x, MonotoneOn (Q x) (Ioo (0 : ℝ) 1))
    (hQ : ∀ x t, t ∈ Icc (0 : ℝ) 1 → Q x t ∈ Icc M.yMin M.yMax) :
    ∀ᵐ o ∂observationLaw M,
      |fittedInt M false phi p g (fun x => quantilePrimitive (Q x)) o -
        connectedInt M zeroLaw false (policyProp phi M.prop) (o.2.1,o.1)| ≤
      lowerPopulationEnvelope M zeroLaw phi p g Q (o.2.1,o.1) := by
  have hmap : (observationLaw M).map Prod.fst = xLaw M := by
    rw [observationLaw, Measure.map_map measurable_fst
      (M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY)))]
    rfl
  have hx := (fitted_lower_population_error_pointwise M zeroLaw h he phi hphi p g Q
    hp hm hQ).and (population_fitted_lower_eq_connected M zeroLaw h he phi hphi)
  rw [← hmap] at hx
  filter_upwards [ae_of_ae_map measurable_fst.aemeasurable hx] with o ho
  have hb := ho.1 o.2.1 o.2.2.1 o.2.2.2
  rw [ho.2 o.2.1 o.2.2.1 o.2.2.2] at hb
  exact hb

-- @node: fitted_lower_integral_error_le_envelope
/-- Under [the structural assumptions](hyp:h), [known outcome bounds](hyp:he), and
[an admissible policy map](hyp:hphi), assume [the fitted propensity is in the unit interval](hyp:hp),
[the fitted quantiles are nondecreasing on interior ranks](hyp:hm), and
[the fitted unit-rank quantiles satisfy the outcome bounds](hyp:hQ).
If [the fitted lower score is integrable under the observation law](hyp:hf),
[the connected lower integrand is integrable under the instrument–covariate law](hyp:hc), and
[the population error envelope is integrable under the instrument–covariate law](hyp:hE),
[the absolute difference between the expected fitted score and the connected lower value is bounded by the expected population error envelope](goal). -/
lemma fitted_lower_integral_error_le_envelope
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (p : Z → X → ℝ) (g : ℝ → X → ℝ) (Q : X → ℝ → ℝ)
    (hp : ∀ z x, p z x ∈ Icc (0 : ℝ) 1)
    (hm : ∀ x, MonotoneOn (Q x) (Ioo (0 : ℝ) 1))
    (hQ : ∀ x t, t ∈ Icc (0 : ℝ) 1 → Q x t ∈ Icc M.yMin M.yMax)
    (hf : Integrable (fittedInt M false phi p g (fun x => quantilePrimitive (Q x)))
      (observationLaw M))
    (hc : Integrable (connectedInt M zeroLaw false (policyProp phi M.prop)) (zxLaw M))
    (hE : Integrable (lowerPopulationEnvelope M zeroLaw phi p g Q) (zxLaw M)) :
    |(∫ o, fittedInt M false phi p g (fun x => quantilePrimitive (Q x)) o
        ∂observationLaw M) - connectedValue M zeroLaw false (policyProp phi M.prop)| ≤
      ∫ zx, lowerPopulationEnvelope M zeroLaw phi p g Q zx ∂zxLaw M := by
  let r : Obs X Z → Z × X := fun o => (o.2.1,o.1)
  have hr : Measurable r := by fun_prop
  have hmap : (observationLaw M).map r = zxLaw M := by
    rw [observationLaw, Measure.map_map hr
      (M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY)))]
    rfl
  have hcp : Integrable (fun o => connectedInt M zeroLaw false (policyProp phi M.prop)
      (r o)) (observationLaw M) := by
    rw [← hmap] at hc
    exact hc.comp_measurable hr
  have hEp : Integrable (fun o => lowerPopulationEnvelope M zeroLaw phi p g Q (r o))
      (observationLaw M) := by
    rw [← hmap] at hE
    exact hE.comp_measurable hr
  have hci : (∫ o, connectedInt M zeroLaw false (policyProp phi M.prop) (r o)
      ∂observationLaw M) = connectedValue M zeroLaw false (policyProp phi M.prop) := by
    rw [connectedValue, ← hmap]
    exact (integral_map hr.aemeasurable (by simpa only [hmap] using hc.aestronglyMeasurable)).symm
  have hEi : (∫ o, lowerPopulationEnvelope M zeroLaw phi p g Q (r o)
      ∂observationLaw M) = ∫ zx, lowerPopulationEnvelope M zeroLaw phi p g Q zx ∂zxLaw M := by
    rw [← hmap]
    exact (integral_map hr.aemeasurable (by simpa only [hmap] using hE.aestronglyMeasurable)).symm
  rw [← hci, ← integral_sub hf hcp]
  calc
    _ ≤ ∫ o, |fittedInt M false phi p g (fun x => quantilePrimitive (Q x)) o -
        connectedInt M zeroLaw false (policyProp phi M.prop) (r o)| ∂observationLaw M :=
      abs_integral_le_integral_abs
    _ ≤ ∫ o, lowerPopulationEnvelope M zeroLaw phi p g Q (r o) ∂observationLaw M :=
      integral_mono_ae (hf.sub hcp).abs hEp
        (fitted_lower_connected_error_ae M zeroLaw h he phi hphi p g Q hp hm hQ)
    _ = _ := hEi

-- @node: lowerPopulationEnvelope_integral
/-- If [each of the three absolute endpoint errors is integrable](hyp:he),
[the sum of regression errors at the clamped policy and original propensity is integrable](hyp:hg), and
[the lower-propensity-weighted boundary quantile distance is integrable](hyp:hm),
[the population lower-score error envelope is integrable and its expectation equals the same weighted sum of the individual error expectations, with the boundary-distance term integrated over the covariate law](goal). -/
lemma lowerPopulationEnvelope_integral
    (phi : Z → X → ℝ → ℝ) (p : Z → X → ℝ)
    (g : ℝ → X → ℝ) (Q : X → ℝ → ℝ)
    (he : ∀ j : Fin 3, Integrable (fun zx =>
      |endpointMap p (policyProp phi p) j zx -
        endpointMap M.prop (policyProp phi M.prop) j zx|) (zxLaw M))
    (hg : Integrable (fun zx =>
      |g (clampPolicy p (policyProp phi p) zx.1 zx.2) zx.2 -
          g1 M (clampPolicy M.prop (policyProp phi M.prop) zx.1 zx.2) zx.2| +
        |g (p zx.1 zx.2) zx.2 - g1 M (M.prop zx.1 zx.2) zx.2|) (zxLaw M))
    (hm : Integrable (fun x => pLow M.prop x * quantileDistanceIntegral
      (Causalean.Stat.unifOI.map (Q x)) (boundaryLaw M zeroLaw x)) (xLaw M)) :
    Integrable (lowerPopulationEnvelope M zeroLaw phi p g Q) (zxLaw M) ∧
    (∫ zx, lowerPopulationEnvelope M zeroLaw phi p g Q zx ∂zxLaw M) =
      outcomeMagnitude M *
        (2 * (∫ zx, |endpointMap p (policyProp phi p) 0 zx -
          endpointMap M.prop (policyProp phi M.prop) 0 zx| ∂zxLaw M) +
          ∫ zx, |endpointMap p (policyProp phi p) 1 zx -
            endpointMap M.prop (policyProp phi M.prop) 1 zx| ∂zxLaw M) +
      (∫ x, pLow M.prop x * quantileDistanceIntegral
        (Causalean.Stat.unifOI.map (Q x)) (boundaryLaw M zeroLaw x) ∂xLaw M) +
      (∫ zx, |g (clampPolicy p (policyProp phi p) zx.1 zx.2) zx.2 -
          g1 M (clampPolicy M.prop (policyProp phi M.prop) zx.1 zx.2) zx.2| +
        |g (p zx.1 zx.2) zx.2 - g1 M (M.prop zx.1 zx.2) zx.2| ∂zxLaw M) +
      |M.yMin| * (∫ zx, |endpointMap p (policyProp phi p) 2 zx -
        endpointMap M.prop (policyProp phi M.prop) 2 zx| ∂zxLaw M) := by
  have hmap : (zxLaw M).map Prod.snd = xLaw M := by
    rw [zxLaw, Measure.map_map measurable_snd (M.measZ.prodMk M.measX)]
    rfl
  have hmp : Integrable (fun zx : Z × X => pLow M.prop zx.2 * quantileDistanceIntegral
      (Causalean.Stat.unifOI.map (Q zx.2)) (boundaryLaw M zeroLaw zx.2)) (zxLaw M) := by
    rw [← hmap] at hm
    exact hm.comp_measurable measurable_snd
  have hmi : (∫ zx : Z × X, pLow M.prop zx.2 * quantileDistanceIntegral
      (Causalean.Stat.unifOI.map (Q zx.2)) (boundaryLaw M zeroLaw zx.2) ∂zxLaw M) =
      ∫ x, pLow M.prop x * quantileDistanceIntegral
        (Causalean.Stat.unifOI.map (Q x)) (boundaryLaw M zeroLaw x) ∂xLaw M := by
    rw [← hmap]
    exact (integral_map (μ := zxLaw M) measurable_snd.aemeasurable
      (by simpa only [hmap] using hm.aestronglyMeasurable)).symm
  have hfirst := ((he 0).const_mul 2 |>.add (he 1)).const_mul (outcomeMagnitude M)
  dsimp only [Pi.add_apply] at hfirst
  constructor
  · exact ((hfirst.add hmp).add hg).add ((he 2).const_mul |M.yMin|)
  · unfold lowerPopulationEnvelope
    have he0 := he 0
    have he1 := he 1
    have he2 := he 2
    integral_linearity
    rw [hmi]

end Papers.TbsPrteOptimalTransport

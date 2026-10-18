module
public import Papers.TbsPrteOptimalTransport.Helpers.GapAttainment
/-! Endpoint optimizers and integrability of the unrestricted treated tail. -/
public section
set_option linter.style.longLine false
set_option linter.unusedVariables false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z]
variable (M : LatentIVModel Ω X Z)

-- @node: tail_endpoint_cost
/-- [The weighted mean of the point mass at the endpoint selected by the weight's sign
equals the selected upper or lower endpoint times the positive part of the weight,
plus the opposite endpoint times its negative part](goal). -/
lemma tail_endpoint_cost (upper : Bool) (w : ℝ) :
    (∫ y : ℝ, y ∂Measure.dirac
      (if 0 ≤ w then (if upper then M.yMax else M.yMin)
        else (if upper then M.yMin else M.yMax))) * w =
    (if upper then M.yMax else M.yMin) * max 0 w +
      (if upper then M.yMin else M.yMax) * min 0 w := by
  rw [integral_dirac]
  by_cases hw : 0 ≤ w
  · rw [if_pos hw, max_eq_right hw, min_eq_left hw, mul_zero, add_zero]
  · have hw' := le_of_lt (lt_of_not_ge hw)
    rw [if_neg hw, max_eq_left hw', min_eq_right hw', mul_zero, zero_add]

-- @node: tail_endpoint_extremal
/-- If [the outcome endpoints are known](hyp:he) and [the outcome lies in the feasible
outcome set](hyp:hy), [its weighted value lies between the lower and upper endpoint
expressions, with endpoint roles reversed for negative weights](goal). -/
lemma tail_endpoint_extremal (he : OutcomeEndpointsKnown M) {y : ℝ}
    (hy : y ∈ M.Yset) (w : ℝ) :
    M.yMin * max 0 w + M.yMax * min 0 w ≤ y * w ∧
      y * w ≤ M.yMax * max 0 w + M.yMin * min 0 w := by
  by_cases hw : 0 ≤ w
  · rw [max_eq_right hw, min_eq_left hw, mul_zero, mul_zero, add_zero, add_zero]
    exact ⟨mul_le_mul_of_nonneg_right (he.1.2 hy) hw,
      mul_le_mul_of_nonneg_right (he.2.2 hy) hw⟩
  · have hw' := le_of_lt (lt_of_not_ge hw)
    rw [max_eq_left hw', min_eq_right hw', mul_zero, mul_zero, zero_add, zero_add]
    exact ⟨mul_le_mul_of_nonpos_right (he.2.2 hy) hw',
      mul_le_mul_of_nonpos_right (he.1.2 hy) hw'⟩

-- @node: tail_endpoint_supported
/-- If [the outcome endpoints are known](hyp:he), [the point mass at the endpoint
selected by the optimization direction and the weight's sign assigns zero mass
outside the feasible outcome set](goal). -/
lemma tail_endpoint_supported (he : OutcomeEndpointsKnown M) (upper : Bool) (w : ℝ) :
    (Measure.dirac (if 0 ≤ w then (if upper then M.yMax else M.yMin)
      else (if upper then M.yMin else M.yMax))) M.Ysetᶜ = 0 := by
  have hy : (if 0 ≤ w then (if upper then M.yMax else M.yMin)
      else (if upper then M.yMin else M.yMax)) ∈ M.Yset := by
    split <;> cases upper <;> first | exact he.1.1 | exact he.2.1
  simp [Measure.dirac_apply, hy]

-- @node: tail_cost_integrable
/-- If [the outcome endpoints are known](hyp:he) and [the weight is integrable under
the given measure](hyp:hi), [the endpoint cost formed from its positive and negative
parts is integrable under that measure](goal). -/
lemma tail_cost_integrable (he : OutcomeEndpointsKnown M) (upper : Bool)
    (mu : Measure ℝ) (w : ℝ → ℝ) (hi : Integrable w mu) :
    Integrable (fun u => (if upper then M.yMax else M.yMin) * max 0 (w u) +
      (if upper then M.yMin else M.yMax) * min 0 (w u)) mu := by
  have hp : Integrable (fun u => max 0 (w u)) mu := by
    simpa only [max_comm] using hi.pos_part
  have hn : Integrable (fun u => min 0 (w u)) mu := by
    have hn := hi.neg.pos_part.neg
    convert hn using 1
    funext u
    change min 0 (w u) = -(max (-(w u)) 0)
    by_cases hw : 0 ≤ w u
    · rw [min_eq_left hw, max_eq_right (neg_nonpos.mpr hw), neg_zero]
    · have hw' := le_of_lt (lt_of_not_ge hw)
      rw [min_eq_right hw', max_eq_left (neg_nonneg.mpr hw'), neg_neg]
  exact (hp.const_mul _).add (hn.const_mul _)

-- @node: tail_region_integrable
/-- If [the outcome endpoints are known](hyp:he) and [the target weight is
integrable](hyp:hi), [for almost every covariate value the sign-dependent endpoint
cost is integrable over the unrestricted tail of the conditional propensity range](goal). -/
lemma tail_region_integrable (he : OutcomeEndpointsKnown M) (upper : Bool)
    (om : X → ℝ → ℝ) (hi : TargetWeightIntegrable M om) :
    ∀ᵐ x ∂xLaw M, Integrable (fun u =>
      (if upper then M.yMax else M.yMin) * max 0 (om x u) +
      (if upper then M.yMin else M.yMax) * min 0 (om x u))
      (volume.restrict (CondRangeDecomposition M x).tail) := by
  haveI : IsProbabilityMeasure (xLaw M) := Measure.isProbabilityMeasure_map M.measX.aemeasurable
  filter_upwards [Integrable.prod_right_ae hi] with x hx
  have hs : (CondRangeDecomposition M x).tail ⊆ Icc (0 : ℝ) 1 := by
    intro u hu
    have hlo : 0 ≤ (CondRangeDecomposition M x).tailLo := by
      rcases rangeDecomposition_valid_or_empty (range (fun z => M.prop z x)) with hv | hz
      · unfold RangeData.tailLo
        split
        · exact le_rfl
        · have hn : (CondRangeDecomposition M x).count ≠ 0 := by assumption
          have hk : (CondRangeDecomposition M x).count - 1 < (CondRangeDecomposition M x).count := by omega
          change (CondRangeDecomposition M x).Valid _ at hv
          change (CondRangeDecomposition M x).count - 1 < (CondRangeDecomposition M x).1 at hk
          have hh := hv.1 ⟨_, hk⟩
          simpa only [RangeData.high, dif_pos hk] using hh.1.trans hh.2.1
      · change 0 ≤ (RangeDecomposition (range (fun z => M.prop z x))).tailLo
        simp only [RangeData.tailLo, hz, ↓reduceIte, le_refl]
    exact ⟨hlo.trans hu.1.le, hu.2⟩
  exact tail_cost_integrable M he upper _ _ (hx.mono_measure (Measure.restrict_mono_set volume hs))

-- @node: supported_mean_endpoint_bounds
/-- Under [the structural assumptions](hyp:h), if [the outcome endpoints are
known](hyp:he) and [the probability distribution assigns zero mass outside the
feasible outcome set](hyp:hs), [its mean lies between the minimum and maximum
outcome endpoints](goal). -/
lemma supported_mean_endpoint_bounds (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hs : mu M.Ysetᶜ = 0) :
    M.yMin ≤ (∫ y, y ∂mu) ∧ (∫ y, y ∂mu) ≤ M.yMax := by
  have hy : ∀ᵐ y ∂mu, y ∈ M.Yset := by
    exact ae_iff.mpr hs
  have hi : Integrable (fun y : ℝ => y) mu :=
    Integrable.of_bound (by fun_prop) (outcomeMagnitude M)
      (supported_outcome_norm_bound M h he mu hs)
  constructor
  · simpa only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] using
      integral_mono_ae (integrable_const M.yMin) hi (hy.mono fun y hy => he.1.2 hy)
  · simpa only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] using
      integral_mono_ae hi (integrable_const M.yMax) (hy.mono fun y hy => he.2.2 hy)

-- @node: tail_mean_extremal
/-- Under [the structural assumptions](hyp:h), if [the outcome endpoints are
known](hyp:he) and [the probability distribution is supported on feasible
outcomes](hyp:hs), [its mean times any weight lies between the endpoint expressions
that interchange the endpoints when the weight is negative](goal). -/
lemma tail_mean_extremal (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hs : mu M.Ysetᶜ = 0) (w : ℝ) :
    M.yMin * max 0 w + M.yMax * min 0 w ≤ (∫ y, y ∂mu) * w ∧
      (∫ y, y ∂mu) * w ≤ M.yMax * max 0 w + M.yMin * min 0 w := by
  have hb := supported_mean_endpoint_bounds M h he mu hs
  by_cases hw : 0 ≤ w
  · rw [max_eq_right hw, min_eq_left hw, mul_zero, mul_zero, add_zero, add_zero]
    exact ⟨mul_le_mul_of_nonneg_right hb.1 hw, mul_le_mul_of_nonneg_right hb.2 hw⟩
  · have hw' := le_of_lt (lt_of_not_ge hw)
    rw [max_eq_left hw', min_eq_right hw', mul_zero, mul_zero, zero_add, zero_add]
    exact ⟨mul_le_mul_of_nonpos_right hb.2 hw', mul_le_mul_of_nonpos_right hb.1 hw'⟩

-- @node: tail_region_cost
/-- [Integrating the weighted means of the sign-selected endpoint point masses over
the conditional tail equals integrating the corresponding endpoint coefficients
times the positive and negative parts of the target weight](goal). -/
lemma tail_region_cost (upper : Bool) (om : X → ℝ → ℝ) (x : X) :
    (∫ u in (CondRangeDecomposition M x).tail,
      (∫ y : ℝ, y ∂Measure.dirac
        (if 0 ≤ om x u then (if upper then M.yMax else M.yMin)
          else (if upper then M.yMin else M.yMax))) * om x u) =
    ∫ u in (CondRangeDecomposition M x).tail,
      (if upper then M.yMax else M.yMin) * max 0 (om x u) +
        (if upper then M.yMin else M.yMax) * min 0 (om x u) := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun u => tail_endpoint_cost M upper (om x u))

-- @node: tail_kernel_objective_bounds
/-- Under [the structural assumptions](hyp:h), if [the outcome endpoints are
known](hyp:he), [the probability kernel is supported on feasible outcomes almost
everywhere](hyp:hs), and [the weight is integrable](hyp:hi), [the integrated weighted
kernel mean lies between the integrated lower and upper sign-dependent endpoint
costs](goal). -/
lemma tail_kernel_objective_bounds (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) (mu : Measure ℝ) (K : Kernel ℝ ℝ)
    [IsMarkovKernel K] (hs : ∀ᵐ u ∂mu, K u M.Ysetᶜ = 0)
    (w : ℝ → ℝ) (hi : Integrable w mu) :
    (∫ u, M.yMin * max 0 (w u) + M.yMax * min 0 (w u) ∂mu) ≤
      (∫ u, (∫ y, y ∂K u) * w u ∂mu) ∧
    (∫ u, (∫ y, y ∂K u) * w u ∂mu) ≤
      (∫ u, M.yMax * max 0 (w u) + M.yMin * min 0 (w u) ∂mu) := by
  have hm : AEStronglyMeasurable (fun u => ∫ y, y ∂K u) mu := by
    exact (stronglyMeasurable_id.integral_kernel (κ := K)).aestronglyMeasurable
  have hb : ∀ᵐ u ∂mu, ‖∫ y, y ∂K u‖ ≤ outcomeMagnitude M := by
    filter_upwards [hs] with u hu
    simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using
      norm_integral_le_of_norm_le_const (supported_outcome_norm_bound M h he (K u) hu)
  have hc := hi.bdd_mul hm hb
  have hl := tail_cost_integrable M he false mu w hi
  have hh := tail_cost_integrable M he true mu w hi
  constructor
  · apply integral_mono_ae hl hc
    filter_upwards [hs] with u hu
    exact (tail_mean_extremal M h he (K u) hu (w u)).1
  · apply integral_mono_ae hc hh
    filter_upwards [hs] with u hu
    exact (tail_mean_extremal M h he (K u) hu (w u)).2

end Papers.TbsPrteOptimalTransport

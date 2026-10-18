module
public import Papers.TbsPrteOptimalTransport.T1dOt
public import Papers.TbsPrteOptimalTransport.Helpers.ObservationalCompatibility
/-! Product-cost comparison for arbitrary couplings on a conditional gap. -/
public section
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.style.openClassical false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

-- @node: weighted_coupling_map_measurable
/-- If [a joint probability law couples the two given marginal measures](hyp:hp) and
[a transformation is almost everywhere measurable under the second marginal](hyp:hf), then
[keeping the first coordinate and transforming the second is almost everywhere measurable under the joint law](goal). -/
@[fun_prop] lemma weighted_coupling_map_measurable
    (mu nu : Measure ℝ) (pi : Measure (ℝ × ℝ)) (hp : IsCoupling pi mu nu)
    (f : ℝ → ℝ) (hf : AEMeasurable f nu) :
    AEMeasurable (fun a : ℝ × ℝ => (a.1, f a.2)) pi := by
  have hs : AEMeasurable f (pi.map Prod.snd) := by rwa [hp.map_snd]
  exact measurable_fst.aemeasurable.prodMk
    (hs.comp_aemeasurable measurable_snd.aemeasurable)

-- @node: weighted_coupling_pushforward
/-- If [a joint probability law couples the two given marginals](hyp:hp) and
[a transformation is almost everywhere measurable under the second marginal](hyp:hf), then
[the law obtained by keeping the first coordinate and transforming the second couples the first marginal
with the transformed second marginal](goal). -/
lemma weighted_coupling_pushforward
    (mu nu : Measure ℝ) (pi : Measure (ℝ × ℝ)) (hp : IsCoupling pi mu nu)
    (f : ℝ → ℝ) (hf : AEMeasurable f nu) :
    IsCoupling (pi.map (fun a => (a.1, f a.2))) mu (nu.map f) := by
  letI := hp.isProbabilityMeasure
  have hm := weighted_coupling_map_measurable mu nu pi hp f hf
  refine ⟨Measure.isProbabilityMeasure_map hm, ?_, ?_⟩
  · rw [AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable hm]
    exact hp.map_fst
  · rw [AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable hm]
    have hs : AEMeasurable f (pi.map Prod.snd) := by rwa [hp.map_snd]
    change pi.map (f ∘ Prod.snd) = nu.map f
    rw [← AEMeasurable.map_map_of_aemeasurable hs measurable_snd.aemeasurable, hp.map_snd]

-- @node: weighted_coupling_cost
/-- If [a joint probability law couples the two given marginals](hyp:hp) and
[a transformation is almost everywhere measurable under the second marginal](hyp:hf), then
[the expected coordinate product under the transformed joint law equals the expected first coordinate
times the transformation of the second coordinate under the original law](goal). -/
lemma weighted_coupling_cost
    (mu nu : Measure ℝ) (pi : Measure (ℝ × ℝ)) (hp : IsCoupling pi mu nu)
    (f : ℝ → ℝ) (hf : AEMeasurable f nu) :
    (∫ a, a.1 * a.2 ∂pi.map (fun a => (a.1, f a.2))) =
      ∫ a, a.1 * f a.2 ∂pi := by
  apply integral_map (weighted_coupling_map_measurable mu nu pi hp f hf)
  fun_prop

-- @node: weighted_coupling_quantile_bounds
/-- For two probability marginals, suppose [the proposed quantile function agrees with the first marginal's quantile
on the open unit interval](hyp:hQ), [the first marginal has bounded support](hyp:hb),
[the transformation of the second coordinate is integrable under its marginal](hyp:hi), and
[the joint law couples these marginals](hyp:hp). Then [the first coordinate times the transformed second coordinate is integrable,
and its expectation lies between the integrals pairing the first marginal's quantile with the transformed second marginal's quantile
in opposite orders and in the same order, respectively](goal). -/
lemma weighted_coupling_quantile_bounds
    (mu nu : Measure ℝ) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (Q : ℝ → ℝ) (hQ : ∀ t ∈ Ioo (0 : ℝ) 1, Q t = Causalean.Stat.quantile mu t)
    (hb : ∃ B : ℝ, mu (Icc (-B) B)ᶜ = 0)
    (f : ℝ → ℝ) (hi : Integrable f nu)
    (pi : Measure (ℝ × ℝ)) (hp : IsCoupling pi mu nu) :
    Integrable (fun a : ℝ × ℝ => a.1 * f a.2) pi ∧
    (∫ t in Ioo (0 : ℝ) 1, Q t * Causalean.Stat.quantile (nu.map f) (1 - t)) ≤
      (∫ a, a.1 * f a.2 ∂pi) ∧
    (∫ a, a.1 * f a.2 ∂pi) ≤
      (∫ t in Ioo (0 : ℝ) 1, Q t * Causalean.Stat.quantile (nu.map f) t) := by
  have hf := hi.aemeasurable
  have hm := weighted_coupling_map_measurable mu nu pi hp f hf
  have hp' := weighted_coupling_pushforward mu nu pi hp f hf
  haveI : IsProbabilityMeasure (nu.map f) := Measure.isProbabilityMeasure_map hf
  have hid : Integrable id (nu.map f) := by
    exact (integrable_map_measure (by fun_prop) hf).mpr hi
  have hot := productCost_transport_extrema mu (nu.map f) Q
    (Causalean.Stat.quantile (nu.map f)) (fun y v => y * v)
    ⟨inferInstance, inferInstance, hQ, fun _ _ => rfl⟩ (Or.inl ⟨hb, hid⟩)
    (fun _ _ => rfl)
  have hc := hot.1 _ hp'
  have heq := weighted_coupling_cost mu nu pi hp f hf
  refine ⟨hc.comp_aemeasurable hm, ?_, ?_⟩
  · rw [← heq]
    exact hot.2.1.2 ⟨_, hp', rfl⟩
  · rw [← heq]
    exact hot.2.2.1.2 ⟨_, hp', rfl⟩

-- @node: kernel_swapped_coupling
/-- For a probability distribution of ranks and a probability kernel giving outcomes conditional on rank,
[swapping the rank and outcome coordinates of their joint law gives a coupling of the mixture outcome law and the rank distribution](goal). -/
lemma kernel_swapped_coupling (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (K : Kernel ℝ ℝ) [IsMarkovKernel K] :
    IsCoupling ((nu ⊗ₘ K).map Prod.swap) (nu.bind K) nu := by
  refine ⟨Measure.isProbabilityMeasure_map measurable_swap.aemeasurable, ?_, ?_⟩
  · change ((nu ⊗ₘ K).map Prod.swap).fst = _
    rw [Measure.fst_map_swap, Measure.snd_compProd]
  · change ((nu ⊗ₘ K).map Prod.swap).snd = _
    rw [Measure.snd_map_swap, Measure.fst_compProd]

-- @node: kernel_swapped_cost_disintegration
/-- If [the outcome times a function of rank is integrable under the joint law ordered as outcome then rank](hyp:hi),
then [its integral equals the rank-distribution integral of the kernel's conditional outcome mean times that function](goal).

The rank measure and the conditional kernel are assumed to be countable sums of finite measures and kernels, respectively. -/
lemma kernel_swapped_cost_disintegration (nu : Measure ℝ) [SFinite nu]
    (K : Kernel ℝ ℝ) [IsSFiniteKernel K] (f : ℝ → ℝ)
    (hi : Integrable (fun a : ℝ × ℝ => a.1 * f a.2) ((nu ⊗ₘ K).map Prod.swap)) :
    (∫ a, a.1 * f a.2 ∂(nu ⊗ₘ K).map Prod.swap) =
      ∫ u, (∫ y, y ∂K u) * f u ∂nu := by
  have hprod : Integrable (fun a : ℝ × ℝ => a.2 * f a.1) (nu ⊗ₘ K) :=
    hi.comp_measurable measurable_swap
  rw [integral_map measurable_swap.aemeasurable hi.aestronglyMeasurable]
  change (∫ a, a.2 * f a.1 ∂nu ⊗ₘ K) = _
  rw [Measure.integral_compProd hprod]
  simp only [integral_mul_const]

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z]
variable (M : LatentIVModel Ω X Z)

-- @node: conditional_feasible_cumulative_law
/-- If [the conditional treated-outcome kernel is feasible at the given covariate value](hyp:hK) and
[the cutoff is zero or an attainable propensity at that covariate value](hyp:hp), then
[mixing the kernel against Lebesgue measure over ranks above zero and at most the cutoff gives the canonical
treated-outcome submeasure at that cutoff](goal). -/
lemma conditional_feasible_cumulative_law (x : X) (K : Kernel ℝ ℝ)
    (hK : ConditionalTreatedFeasible M x K) (p : ℝ)
    (hp : p = 0 ∨ p ∈ range (fun z => M.prop z x)) :
    (volume.restrict (Ioc 0 p)).bind K = canonSubmeasure M true x p := by
  rcases hp with rfl | hp
  · simp [canonSubmeasure, selRegion]
  letI := hK.1
  letI := outcomeKernel_isMarkov (latentMarginal M true)
  let K0 := (outcomeKernel (latentMarginal M true)).comap
    (fun u : ℝ => (u, x)) (by fun_prop)
  haveI : IsFiniteMeasure ((volume.restrict (Ioc 0 p)).bind K) :=
    ⟨(interval_kernel_finite K 0 p).lt_top⟩
  haveI : IsFiniteMeasure (canonSubmeasure M true x p) :=
    ⟨(interval_kernel_finite K0 0 p).lt_top⟩
  ext B hB
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  rw [← markov_bind_evaluation_integral _ K B hB]
  exact hK.2.2 p hp B hB

-- @node: range_endpoint_mem
/-- If [the finite interval decomposition is valid for a set of real numbers](hyp:hD) and
[the component index is below its component count](hyp:hk), then
[both endpoints of that component belong to the set](goal). -/
lemma range_endpoint_mem (D : RangeData) (R : Set ℝ) (hD : D.Valid R)
    {k : ℕ} (hk : k < D.count) : D.low k ∈ R ∧ D.high k ∈ R := by
  have hk' : k < D.1 := hk
  have hle := (hD.1 ⟨k, hk'⟩).2.1
  rw [hD.2.2]
  constructor
  · apply mem_iUnion.mpr
    refine ⟨⟨k, hk'⟩, ?_⟩
    simp only [RangeData.low, dif_pos hk', mem_Icc]
    exact ⟨le_rfl, hle⟩
  · apply mem_iUnion.mpr
    refine ⟨⟨k, hk'⟩, ?_⟩
    simp only [RangeData.high, dif_pos hk', mem_Icc]
    exact ⟨hle, le_rfl⟩

-- @node: conditional_feasible_gap_law
/-- If [the conditional treated-outcome kernel is feasible](hyp:hK),
[the conditional range decomposition is valid for the attainable propensities](hyp:hv),
[the gap index is within that decomposition](hyp:hk), and [the gap has positive length](hyp:hab), then
[mixing the kernel over the uniform rank distribution on that gap gives the prescribed gap outcome law](goal). -/
lemma conditional_feasible_gap_law (x : X) (K : Kernel ℝ ℝ)
    (hK : ConditionalTreatedFeasible M x K)
    (hv : (CondRangeDecomposition M x).Valid (range (fun z => M.prop z x)))
    (k : ℕ) (hk : k < (CondRangeDecomposition M x).count)
    (hab : (CondRangeDecomposition M x).gapLo k < (CondRangeDecomposition M x).gapHi k) :
    (gapUnif M x k).bind K = gapLaw M x k := by
  letI := hK.1
  let D := CondRangeDecomposition M x
  have hlo := (conditional_gap_endpoints M x k hk).1.1
  have hmemLo : D.gapLo k = 0 ∨ D.gapLo k ∈ range (fun z => M.prop z x) := by
    by_cases hz : k = 0
    · exact Or.inl (by simp [D, RangeData.gapLo, hz])
    · apply Or.inr
      have hk' : k - 1 < D.count := by change k < D.count at hk; omega
      simpa only [RangeData.gapLo, if_neg hz] using
        (range_endpoint_mem D _ hv hk').2
  have hmemHi : D.gapHi k ∈ range (fun z => M.prop z x) :=
    (range_endpoint_mem D _ hv hk).1
  have ha := conditional_feasible_cumulative_law M x K hK _ hmemLo
  have hb := conditional_feasible_cumulative_law M x K hK _ (Or.inr hmemHi)
  haveI : IsFiniteMeasure ((volume.restrict (Ioc 0 (D.gapLo k))).bind K) :=
    ⟨(interval_kernel_finite K 0 (D.gapLo k)).lt_top⟩
  rw [gapLaw, if_pos hab, gapUnif, uniformInterval, Measure.bind_smul]
  congr 1
  rw [restrict_Ioo_eq_restrict_Ioc, ← ha, ← hb,
    interval_kernel_add K 0 _ _ hlo hab.le, add_comm, Measure.add_sub_cancel]

-- @node: gap_coupling_objective_bounds
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
[continuity of propensity on instrument components](hyp:hc), and [finitely many instrument components](hyp:hfin),
suppose [the target weight is integrable over covariates and unit-interval ranks](hyp:hi).
Then [for almost every covariate value and every gap of positive length, every coupling of the prescribed gap outcome law
and uniform gap ranks has an integrable outcome-weight product, whose expectation lies between the integrals of the outcome
and weight quantiles paired in opposite orders and in the same order, respectively](goal). -/
lemma gap_coupling_objective_bounds (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) (hc : PropensityContinuousOnComponents M)
    (hfin : FiniteInstrumentComponents Z) (om : X → ℝ → ℝ)
    (hi : TargetWeightIntegrable M om) :
    ∀ᵐ x ∂xLaw M, ∀ k < (CondRangeDecomposition M x).count,
      (CondRangeDecomposition M x).gapLo k < (CondRangeDecomposition M x).gapHi k →
      ∀ pi : Measure (ℝ × ℝ), IsCoupling pi (gapLaw M x k) (gapUnif M x k) →
        Integrable (fun a : ℝ × ℝ => a.1 * om x a.2) pi ∧
        (∫ t in Ioo (0 : ℝ) 1, (gapQuantiles M om x k).1 t *
          (gapQuantiles M om x k).2 (1 - t)) ≤ (∫ a, a.1 * om x a.2 ∂pi) ∧
        (∫ a, a.1 * om x a.2 ∂pi) ≤
          (∫ t in Ioo (0 : ℝ) 1, (gapQuantiles M om x k).1 t *
            (gapQuantiles M om x k).2 t) := by
  filter_upwards [gap_law_isProbability M h hc hfin, gap_law_supported M h,
    gap_weight_integrable M om hi] with x hprob hs hw
  intro k hk hab pi hp
  letI := hprob k hk hab
  haveI : IsProbabilityMeasure (gapUnif M x k) := by
    change IsProbabilityMeasure (uniformInterval _ _)
    exact uniformInterval_isProbability _ _ hab
  have hb : ∃ B : ℝ, gapLaw M x k (Icc (-B) B)ᶜ = 0 := by
    refine ⟨outcomeMagnitude M, ?_⟩
    apply ae_iff.mp
    filter_upwards [supported_outcome_norm_bound M h he _ (hs k hk hab)] with y hy
    simpa only [Real.norm_eq_abs, abs_le, mem_Icc] using hy
  exact weighted_coupling_quantile_bounds _ _ (endpointGapQuantile M x k)
    (fun t ht => by
      simp only [endpointGapQuantile, if_neg (ne_of_gt ht.1), if_neg (ne_of_lt ht.2)])
    hb (om x) (hw k hk hab) pi hp

-- @node: gap_kernel_region_objective_bounds
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
[continuity of propensity on instrument components](hyp:hc), and [finitely many instrument components](hyp:hfin),
with [a target weight integrable over covariates and unit-interval ranks](hyp:hi),
[for almost every covariate value and every gap of positive length, any probability kernel whose uniform-gap mixture
is the prescribed outcome law has an integrable weighted conditional mean on the gap, and its Lebesgue integral lies between
the gap length times the oppositely ordered and equally ordered quantile-product integrals](goal). -/
lemma gap_kernel_region_objective_bounds (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) (hc : PropensityContinuousOnComponents M)
    (hfin : FiniteInstrumentComponents Z) (om : X → ℝ → ℝ)
    (hi : TargetWeightIntegrable M om) :
    ∀ᵐ x ∂xLaw M, ∀ k < (CondRangeDecomposition M x).count,
      (CondRangeDecomposition M x).gapLo k < (CondRangeDecomposition M x).gapHi k →
      ∀ K : Kernel ℝ ℝ, IsMarkovKernel K →
      (gapUnif M x k).bind K = gapLaw M x k →
      Integrable (fun u => (∫ y, y ∂K u) * om x u)
        (volume.restrict (RangeDecomposition.gap (CondRangeDecomposition M x) k)) ∧
      max 0 ((CondRangeDecomposition M x).gapHi k - (CondRangeDecomposition M x).gapLo k) *
        (∫ t in Ioo (0 : ℝ) 1, (gapQuantiles M om x k).1 t *
          (gapQuantiles M om x k).2 (1 - t)) ≤
        (∫ u in RangeDecomposition.gap (CondRangeDecomposition M x) k,
          (∫ y, y ∂K u) * om x u) ∧
      (∫ u in RangeDecomposition.gap (CondRangeDecomposition M x) k,
        (∫ y, y ∂K u) * om x u) ≤
        max 0 ((CondRangeDecomposition M x).gapHi k - (CondRangeDecomposition M x).gapLo k) *
          (∫ t in Ioo (0 : ℝ) 1, (gapQuantiles M om x k).1 t *
            (gapQuantiles M om x k).2 t) := by
  filter_upwards [gap_coupling_objective_bounds M h he hc hfin om hi] with x hx
  intro k hk hab K hK hgap
  letI := hK
  haveI : IsProbabilityMeasure (gapUnif M x k) := uniformInterval_isProbability _ _ hab
  have hp := kernel_swapped_coupling (gapUnif M x k) K
  rw [hgap] at hp
  obtain ⟨hint, hlo, hhi⟩ := hx k hk hab _ hp
  have hcost := kernel_swapped_cost_disintegration (gapUnif M x k) K (om x) hint
  rw [hcost] at hlo hhi
  have hmean := (hint.comp_measurable measurable_swap).integral_compProd
  simp only [Function.comp_def, Prod.swap_prod_mk, Kernel.prodMkLeft_apply,
    Kernel.const_apply, integral_mul_const] at hmean
  let d := (CondRangeDecomposition M x).gapHi k - (CondRangeDecomposition M x).gapLo k
  have hd : 0 ≤ d := sub_nonneg.mpr hab.le
  have hscale : ENNReal.ofReal d • gapUnif M x k =
      volume.restrict (RangeDecomposition.gap (CondRangeDecomposition M x) k) :=
    by
      rw [conditional_gap_eq_Ioo M x k hk]
      exact uniformInterval_scaled _ _ hab
  have hregion := hmean.smul_measure (c := ENNReal.ofReal d) ENNReal.ofReal_ne_top
  rw [hscale] at hregion
  have heq : (∫ u in RangeDecomposition.gap (CondRangeDecomposition M x) k,
      (∫ y, y ∂K u) * om x u) = d *
        (∫ u, (∫ y, y ∂K u) * om x u ∂gapUnif M x k) := by
    rw [← hscale, integral_smul_measure, ENNReal.toReal_ofReal hd]
    rfl
  refine ⟨hregion, ?_, ?_⟩
  · rw [max_eq_right hd, heq]
    exact mul_le_mul_of_nonneg_left hlo hd
  · rw [max_eq_right hd, heq]
    exact mul_le_mul_of_nonneg_left hhi hd

-- @node: conditional_feasible_mean_primitive
/-- Under [the structural assumptions](hyp:h) and [known outcome endpoints](hyp:he), if
[the conditional treated-outcome kernel is feasible at the given covariate value](hyp:hK) and
[the cutoff is an attainable propensity there](hyp:hp), then
[the canonical treated-outcome mean primitive at that cutoff equals the integral of the kernel's conditional outcome mean
over ranks above zero and at most the cutoff](goal). -/
lemma conditional_feasible_mean_primitive (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) (x : X) (K : Kernel ℝ ℝ)
    (hK : ConditionalTreatedFeasible M x K) (p : ℝ)
    (hp : p ∈ range (fun z => M.prop z x)) :
    g1Canon M p x = ∫ u in Ioc 0 p, (∫ y, y ∂K u) := by
  letI := hK.1
  have hpu : p ∈ Icc (0 : ℝ) 1 := by
    obtain ⟨z, rfl⟩ := hp
    exact M.rangeProp z x
  let mu := volume.restrict (Ioc (0 : ℝ) p)
  have hs : ∀ᵐ u ∂mu, K u M.Ysetᶜ = 0 := by
    apply hK.2.1.filter_mono
    apply ae_mono (Measure.restrict_mono_set volume _)
    intro u hu
    exact ⟨hu.1.le, hu.2.trans hpu.2⟩
  have hb : ∀ᵐ a ∂mu ⊗ₘ K, ‖a.2‖ ≤ outcomeMagnitude M := by
    apply Measure.ae_compProd_of_ae_ae
    · exact measurableSet_le measurable_snd.norm measurable_const
    · filter_upwards [hs] with u hu
      exact supported_outcome_norm_bound M h he (K u) hu
  have hi : Integrable (fun a : ℝ × ℝ => a.2) (mu ⊗ₘ K) :=
    Integrable.of_bound (by fun_prop) (outcomeMagnitude M) hb
  rw [g1Canon, ← conditional_feasible_cumulative_law M x K hK p (Or.inr hp)]
  change (∫ y, y ∂mu.bind K) = _
  rw [← Measure.snd_compProd mu K, Measure.snd,
    integral_map measurable_snd.aemeasurable (by fun_prop)]
  exact Measure.integral_compProd hi

-- @node: conditional_feasible_liv_deriv
/-- Under [the structural assumptions](hyp:h) and [known outcome endpoints](hyp:he), suppose
[the conditional treated-outcome kernel is feasible](hyp:hK),
[the conditional range decomposition is valid for the attainable propensities](hyp:hv), and
[the component index is within the decomposition](hyp:hk). Then
[at Lebesgue-almost every rank in that identified propensity component, the derivative of the canonical
treated-outcome mean primitive equals the kernel's conditional outcome mean](goal). -/
lemma conditional_feasible_liv_deriv (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) (x : X) (K : Kernel ℝ ℝ)
    (hK : ConditionalTreatedFeasible M x K)
    (hv : (CondRangeDecomposition M x).Valid (range (fun z => M.prop z x)))
    (k : ℕ) (hk : k < (CondRangeDecomposition M x).count) :
    ∀ᵐ u ∂volume.restrict ((CondRangeDecomposition M x).liv k),
      deriv (fun p => g1Canon M p x) u = ∫ y, y ∂K u := by
  letI := hK.1
  let D := CondRangeDecomposition M x
  let f : ℝ → ℝ := fun u => ∫ y, y ∂K u
  have hi : IntegrableOn f (Icc (0 : ℝ) 1) := by
    simpa only [f, mul_one, IntegrableOn] using
      supported_kernel_weighted_integrable M h he _ K hK.2.1
        (fun _ => 1) (integrable_const 1)
  have hii : IntervalIntegrable f volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr hi
  have hd := hii.ae_hasDerivAt_integral
  have hu : ∀ᵐ u ∂volume.restrict (D.liv k), u ∈ Ioo (D.low k) (D.high k) := by
    change ∀ᵐ u ∂volume.restrict (Icc _ _), _
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  have hb := range_endpoint_bounds D _ hv hk
  filter_upwards [hd.filter_mono (ae_mono Measure.restrict_le_self), hu] with u hdu hu
  have hunit : u ∈ Icc (0 : ℝ) 1 :=
    ⟨hb.1.trans hu.1.le, hu.2.le.trans hb.2.2⟩
  have hd' := hdu (by simpa using hunit) 0 (by simp)
  have heq : (fun p => g1Canon M p x) =ᶠ[𝓝 u] (fun p => ∫ v in 0..p, f v) := by
    filter_upwards [Ioo_mem_nhds hu.1 hu.2] with p hp
    have hpr : p ∈ range (fun z => M.prop z x) := by
      rw [hv.2.2]
      refine mem_iUnion.mpr ⟨⟨k, hk⟩, ?_⟩
      have hk' : k < D.1 := hk
      simpa only [D, RangeData.low, RangeData.high, dif_pos hk', mem_Icc] using
        And.intro hp.1.le hp.2.le
    rw [conditional_feasible_mean_primitive M h he x K hK p hpr,
      intervalIntegral.integral_of_le (hb.1.trans hp.1.le)]
  exact (hd'.congr_of_eventuallyEq heq).deriv

-- @node: conditional_feasible_liv_cost
/-- Under [the structural assumptions](hyp:h) and [known outcome endpoints](hyp:he), suppose
[the conditional treated-outcome kernel is feasible](hyp:hK),
[the conditional range decomposition is valid for the attainable propensities](hyp:hv), and
[the component index is within the decomposition](hyp:hk). Then [for any real-valued weight, its integral times the kernel's
conditional outcome mean over that identified propensity component equals its integral times the derivative
of the canonical treated-outcome mean primitive over the same component](goal). -/
lemma conditional_feasible_liv_cost (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) (x : X) (K : Kernel ℝ ℝ)
    (hK : ConditionalTreatedFeasible M x K)
    (hv : (CondRangeDecomposition M x).Valid (range (fun z => M.prop z x)))
    (k : ℕ) (hk : k < (CondRangeDecomposition M x).count) (w : ℝ → ℝ) :
    (∫ u in (CondRangeDecomposition M x).liv k, (∫ y, y ∂K u) * w u) =
      ∫ u in (CondRangeDecomposition M x).liv k,
        deriv (fun p => g1Canon M p x) u * w u := by
  apply integral_congr_ae
  filter_upwards [conditional_feasible_liv_deriv M h he x K hK hv k hk] with u hu
  rw [hu]

-- @node: conditional_feasible_gap_cost_bounds
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
[continuity of propensity on instrument components](hyp:hc), and [finitely many instrument components](hyp:hfin),
with [a target weight integrable over covariates and unit-interval ranks](hyp:hi),
[for almost every covariate value, every feasible conditional treated-outcome kernel and every gap in the decomposition
have a weighted conditional-mean integral bounded below by the nonnegative gap length times the oppositely ordered
quantile-product integral and above by that length times the equally ordered quantile-product integral](goal). -/
lemma conditional_feasible_gap_cost_bounds (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) (hc : PropensityContinuousOnComponents M)
    (hfin : FiniteInstrumentComponents Z) (om : X → ℝ → ℝ)
    (hi : TargetWeightIntegrable M om) :
    ∀ᵐ x ∂xLaw M, ∀ K : Kernel ℝ ℝ, ConditionalTreatedFeasible M x K →
      ∀ k < (CondRangeDecomposition M x).count,
      max 0 ((CondRangeDecomposition M x).gapHi k - (CondRangeDecomposition M x).gapLo k) *
        (∫ t in Ioo (0 : ℝ) 1, (gapQuantiles M om x k).1 t *
          (gapQuantiles M om x k).2 (1 - t)) ≤
        (∫ u in RangeDecomposition.gap (CondRangeDecomposition M x) k,
          (∫ y, y ∂K u) * om x u) ∧
      (∫ u in RangeDecomposition.gap (CondRangeDecomposition M x) k,
        (∫ y, y ∂K u) * om x u) ≤
        max 0 ((CondRangeDecomposition M x).gapHi k - (CondRangeDecomposition M x).gapLo k) *
          (∫ t in Ioo (0 : ℝ) 1, (gapQuantiles M om x k).1 t *
            (gapQuantiles M om x k).2 t) := by
  filter_upwards [gap_kernel_region_objective_bounds M h he hc hfin om hi,
    range_decomposition_valid M h hfin hc] with x hx hv
  intro K hK k hk
  by_cases hab : (CondRangeDecomposition M x).gapLo k < (CondRangeDecomposition M x).gapHi k
  · exact (hx k hk hab K hK.1
      (conditional_feasible_gap_law M x K hK hv k hk hab)).2
  · have hle := le_of_not_gt hab
    have hz : RangeDecomposition.gap (CondRangeDecomposition M x) k = ∅ :=
      by
        rw [conditional_gap_eq_Ioo M x k hk]
        exact Ioo_eq_empty_of_le hle
    rw [max_eq_left (sub_nonpos.mpr hle), hz]
    simp only [zero_mul, Measure.restrict_empty, integral_zero_measure, le_refl, and_self]

-- @node: conditional_feasible_objective_bounds
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
[continuity of propensity on instrument components](hyp:hc), and [finitely many instrument components](hyp:hfin),
suppose [the target weight is integrable over covariates and unit-interval ranks](hyp:hi).
Then [for almost every covariate value, every feasible conditional treated-outcome kernel has an integrable weighted
conditional mean on the unit interval, and its integral lies between the conditional lower and upper bound integrands](goal). -/
lemma conditional_feasible_objective_bounds (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) (hc : PropensityContinuousOnComponents M)
    (hfin : FiniteInstrumentComponents Z) (om : X → ℝ → ℝ)
    (hi : TargetWeightIntegrable M om) :
    ∀ᵐ x ∂xLaw M, ∀ K : Kernel ℝ ℝ, ConditionalTreatedFeasible M x K →
      IntegrableOn (fun u => (∫ y, y ∂K u) * om x u) (Icc (0 : ℝ) 1) ∧
      conditionalBoundIntegrand M false om x ≤
        (∫ u in Icc (0 : ℝ) 1, (∫ y, y ∂K u) * om x u) ∧
      (∫ u in Icc (0 : ℝ) 1, (∫ y, y ∂K u) * om x u) ≤
        conditionalBoundIntegrand M true om x := by
  haveI : IsProbabilityMeasure (xLaw M) := Measure.isProbabilityMeasure_map M.measX.aemeasurable
  filter_upwards [conditional_feasible_gap_cost_bounds M h he hc hfin om hi,
    range_decomposition_valid M h hfin hc, Integrable.prod_right_ae hi] with x hg hv hw
  intro K hK
  letI := hK.1
  let D := CondRangeDecomposition M x
  let f : ℝ → ℝ := fun u => (∫ y, y ∂K u) * om x u
  have hint : IntegrableOn f (Icc (0 : ℝ) 1) :=
    supported_kernel_weighted_integrable M h he _ K hK.2.1 (om x) hw
  have hdec := range_regions_integral D _ hv f hint
  have hliv : (∑ k ∈ Finset.range D.count, ∫ u in D.liv k, f u) =
      ∑ k ∈ Finset.range D.count, ∫ u in D.liv k,
        deriv (fun p => g1Canon M p x) u * om x u := by
    apply Finset.sum_congr rfl
    intro k hk
    exact conditional_feasible_liv_cost M h he x K hK hv k (Finset.mem_range.mp hk) (om x)
  have hsTail : ∀ᵐ u ∂volume.restrict D.tail, K u M.Ysetᶜ = 0 :=
    hK.2.1.filter_mono (ae_mono (Measure.restrict_mono_set volume (range_tail_subset_unit D _ hv)))
  have hwTail := hw.mono_measure (Measure.restrict_mono_set volume (range_tail_subset_unit D _ hv))
  have ht := tail_kernel_objective_bounds M h he _ K hsTail (om x) hwTail
  have hlGap : (∑ k ∈ Finset.range D.count,
      max 0 (D.gapHi k - D.gapLo k) * ∫ t in Ioo (0 : ℝ) 1,
        (gapQuantiles M om x k).1 t * (gapQuantiles M om x k).2 (1 - t)) ≤
      ∑ k ∈ Finset.range D.count, ∫ u in RangeDecomposition.gap D k, f u := by
    exact Finset.sum_le_sum fun k hk => (hg K hK k (Finset.mem_range.mp hk)).1
  have huGap : (∑ k ∈ Finset.range D.count, ∫ u in RangeDecomposition.gap D k, f u) ≤
      ∑ k ∈ Finset.range D.count,
        max 0 (D.gapHi k - D.gapLo k) * ∫ t in Ioo (0 : ℝ) 1,
          (gapQuantiles M om x k).1 t * (gapQuantiles M om x k).2 t := by
    exact Finset.sum_le_sum fun k hk => (hg K hK k (Finset.mem_range.mp hk)).2
  refine ⟨hint, ?_, ?_⟩
  · change conditionalBoundIntegrand M false om x ≤ ∫ u in Icc (0 : ℝ) 1, f u
    rw [hdec, hliv]
    simp only [conditionalBoundIntegrand, Bool.false_eq_true, ↓reduceIte]
    exact add_le_add (add_le_add hlGap le_rfl) ht.1
  · change (∫ u in Icc (0 : ℝ) 1, f u) ≤ conditionalBoundIntegrand M true om x
    rw [hdec, hliv]
    simp only [conditionalBoundIntegrand, ↓reduceIte]
    exact add_le_add (add_le_add huGap le_rfl) ht.2

end Papers.TbsPrteOptimalTransport

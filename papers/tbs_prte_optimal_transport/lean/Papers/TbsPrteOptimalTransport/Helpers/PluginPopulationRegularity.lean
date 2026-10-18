module
public import Papers.TbsPrteOptimalTransport.Helpers.FeasibleDisintegration
public import Papers.TbsPrteOptimalTransport.Helpers.ConnectedBoundary
public import Papers.TbsPrteOptimalTransport.Helpers.PluginPopulation
public import Papers.TbsPrteOptimalTransport.Helpers.PluginScoreMeasurability
/-! Measurable canonical population kernels for the continuous plug-in proof. -/
@[expose] public section
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set
open scoped Classical Topology

universe u v
variable {Ω : Type u} {X Z : Type v}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]
variable (M : LatentIVModel Ω X Z)

-- @node: canonical_treated_kernel
/-- For [the latent instrumental-variable model](hyp:M), [a covariate map from a parameter space](hyp:x),
[a rank cutoff on that space](hyp:b), [measurability of the covariate map](hyp:hx), and
[measurability of the cutoff](hyp:hb), the [canonical treated-outcome kernel](goal)
integrates the treated latent outcome law over ranks strictly above zero and at most the cutoff. -/
noncomputable def canonical_treated_kernel {T : Type*} [MeasurableSpace T]
    (x : T → X) (b : T → ℝ) (hx : Measurable x) (hb : Measurable b) : Kernel T ℝ where
  toFun t := canonSubmeasure M true (x t) (b t)
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro B hB
    have hm : Measurable (fun tu : T × ℝ =>
        if 0 < tu.2 ∧ tu.2 ≤ b tu.1 then
          outcomeKernel (latentMarginal M true) (tu.2, x tu.1) B else 0) := by
      apply Measurable.ite
      · exact (measurableSet_lt measurable_const measurable_snd).inter
          (measurableSet_le measurable_snd (hb.comp measurable_fst))
      · exact ((outcomeKernel (latentMarginal M true)).measurable_coe hB).comp
          (measurable_snd.prodMk (hx.comp measurable_fst))
      · fun_prop
    convert hm.lintegral_prod_right' (ν := volume) using 1
    funext t
    rw [canonSubmeasure, Measure.bind_apply hB (by fun_prop)]
    simp only [selRegion, if_true]
    rw [← lintegral_indicator measurableSet_Ioc]
    apply lintegral_congr
    intro u
    simp only [indicator_apply, mem_Ioc]

-- @node: measurable_canonical_regression
/-- [The canonical treated regression is jointly measurable in the propensity threshold and covariates](goal). -/
@[fun_prop] lemma measurable_canonical_regression :
    Measurable (fun tx : ℝ × X => g1 M tx.1 tx.2) := by
  have hm := (show StronglyMeasurable (fun y : ℝ => y) by fun_prop).integral_kernel
    (κ := canonical_treated_kernel M Prod.snd Prod.fst measurable_snd measurable_fst)
  exact hm.measurable

-- @node: measurable_markov_quantile_interior
/-- For a probability-valued measurable kernel, [its quantile is jointly measurable in the kernel's parameter and ranks strictly between zero and one](goal). -/
@[fun_prop] lemma measurable_markov_quantile_interior
    {T : Type*} [MeasurableSpace T] (K : Kernel T ℝ) [IsMarkovKernel K] :
    Measurable (fun tr : T × Ioo (0 : ℝ) 1 =>
      Causalean.Stat.quantile (K tr.1) tr.2.val) := by
  apply measurable_of_Iic
  intro c
  have hm : Measurable (fun tr : T × Ioo (0 : ℝ) 1 =>
      ((K tr.1) (Iic c)).toReal) :=
    ((K.measurable_coe measurableSet_Iic).comp measurable_fst).ennreal_toReal
  convert measurableSet_le (measurable_subtype_coe.comp measurable_snd) hm using 1
  ext tr
  simp only [mem_preimage, mem_Iic, mem_setOf_eq,
    Causalean.Stat.quantile_le_iff tr.2.property.1 tr.2.property.2,
    cdf_eq_real, measureReal_def, Function.comp_apply]

-- @node: canonical_boundary_kernel
/-- For [the latent instrumental-variable model](hyp:M), [a covariate-dependent rank cutoff](hyp:b), and
[measurability of that cutoff](hyp:hb), the [canonical boundary kernel](goal)
uses the treated canonical submeasure divided by the cutoff when the cutoff is positive, and a point mass at the lower outcome bound otherwise. -/
noncomputable def canonical_boundary_kernel (b : X → ℝ) (hb : Measurable b) : Kernel X ℝ where
  toFun x := if 0 < b x then
    (ENNReal.ofReal (b x))⁻¹ • canonSubmeasure M true x (b x) else Measure.dirac M.yMin
  measurable' := by
    classical
    apply Measure.measurable_of_measurable_coe
    intro B hB
    have hm : Measurable (fun x => if 0 < b x then
        (ENNReal.ofReal (b x))⁻¹ * canonSubmeasure M true x (b x) B
        else Measure.dirac M.yMin B) := Measurable.ite (measurableSet_lt (measurable_const (a := (0 : ℝ))) hb)
      ((hb.ennreal_ofReal.inv).mul
        ((canonical_treated_kernel M id b measurable_id hb).measurable_coe hB))
      (measurable_const (a := Measure.dirac M.yMin B))
    convert hm using 1
    funext x
    split_ifs <;> simp only [Measure.smul_apply, smul_eq_mul]

-- @node: canonical_boundary_kernel_markov
/-- If [the covariate-dependent rank cutoff is measurable](hyp:hb),
[the canonical boundary kernel assigns a probability measure to every covariate value](goal). -/
lemma canonical_boundary_kernel_markov (b : X → ℝ) (hb : Measurable b) :
    IsMarkovKernel (canonical_boundary_kernel M b hb) := by
  letI := outcomeKernel_isMarkov (latentMarginal M true)
  constructor
  intro x
  constructor
  change (if 0 < b x then (ENNReal.ofReal (b x))⁻¹ •
    canonSubmeasure M true x (b x) else Measure.dirac M.yMin) univ = 1
  split_ifs with h
  · rw [Measure.smul_apply]
    have hmass : canonSubmeasure M true x (b x) univ = ENNReal.ofReal (b x) := by
      rw [canonSubmeasure, Measure.bind_apply MeasurableSet.univ (by fun_prop)]
      simp [selRegion, Real.volume_Ioc]
    rw [hmass]
    exact ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr h) ENNReal.ofReal_ne_top
  · simp

-- @node: population_regression_magnitude
/-- Under [the structural assumptions](hyp:h) and [known outcome bounds](hyp:he),
[the absolute canonical treated regression is bounded by the outcome magnitude at every unit-interval threshold for almost every covariate value](goal). -/
lemma population_regression_magnitude (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) :
    ∀ᵐ x ∂xLaw M, ∀ t ∈ Icc (0 : ℝ) 1, |g1 M t x| ≤ outcomeMagnitude M := by
  have hC : 0 ≤ outcomeMagnitude M := (abs_nonneg M.yMin).trans (le_max_left _ _)
  filter_upwards [canonical_regression_lipschitz M h he] with x hx
  intro t ht
  have hb := hx t ht 0 ⟨le_rfl, zero_le_one⟩
  have hz : g1Canon M 0 x = 0 := by
    simp [g1Canon, canonSubmeasure, selRegion]
  simp only [hz, sub_zero, abs_of_nonneg ht.1] at hb
  exact hb.trans (mul_le_of_le_one_right hC ht.2)

-- @node: exists_population_boundary_rank_version
/-- For [a covariate-indexed fallback probability law supported on the outcome range](hyp:zeroLaw), under [the structural assumptions](hyp:h) and [known outcome bounds](hyp:he),
[there exists a rank function that is jointly measurable on covariates and unit ranks, bounded in absolute value by the outcome magnitude at all covariates and real ranks, and equal to the boundary quantile at almost every unit rank for almost every covariate with positive lower propensity](goal). -/
lemma exists_population_boundary_rank_version
    (zeroLaw : X → {ν : ProbabilityMeasure ℝ // ν.toMeasure M.Ysetᶜ = 0})
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M) :
    ∃ Q : X → ℝ → ℝ,
      Measurable (fun xt : X × Icc (0 : ℝ) 1 => Q xt.1 xt.2.val) ∧
      (∀ x t, |Q x t| ≤ outcomeMagnitude M) ∧
      (∀ᵐ x ∂xLaw M, 0 < pLow M.prop x →
        Q x =ᵐ[volume.restrict (Icc (0 : ℝ) 1)] boundaryQuantile M zeroLaw x) := by
  haveI : IsProbabilityMeasure (xLaw M) := Measure.isProbabilityMeasure_map M.measX.aemeasurable
  have hm : Measurable (fun xz : X × Z => M.prop xz.2 xz.1) :=
    h.2.2.2.1.2.1.comp measurable_swap
  have hl := aemeasurable_bounded_parameter_infimum (xLaw M) _ hm
    (fun x z => (M.rangeProp z x).1)
  change AEMeasurable (pLow M.prop) (xLaw M) at hl
  let b := hl.mk (pLow M.prop)
  let K := canonical_boundary_kernel M b hl.measurable_mk
  letI : IsMarkovKernel K := canonical_boundary_kernel_markov M b hl.measurable_mk
  let q : X → ℝ → ℝ := fun x t =>
    if ht : t ∈ Ioo (0 : ℝ) 1 then Causalean.Stat.quantile (K x) t else M.yMin
  have hq : Measurable (fun xt : X × ℝ => q xt.1 xt.2) := by
    dsimp only [q]
    convert Measurable.dite
      (f := fun xt : {xt : X × ℝ // xt.2 ∈ Ioo (0 : ℝ) 1} =>
        Causalean.Stat.quantile (K xt.val.1) xt.val.2)
      (g := fun _ => M.yMin) ?_ ?_ ((show MeasurableSet (Ioo (0 : ℝ) 1) from measurableSet_Ioo).preimage measurable_snd) using 1
    · funext xt
      split_ifs with h1 h2
      · rfl
      · exact False.elim (h2 h1)
      · rename_i h2; exact False.elim (h1 h2)
      · rfl
    · exact (measurable_markov_quantile_interior K).comp
        (measurable_subtype_coe.fst.prodMk (measurable_subtype_coe.snd.subtype_mk (h := fun xt => xt.property)))
    · fun_prop
  let C := outcomeMagnitude M
  let Q : X → ℝ → ℝ := fun x t => max (-C) (min C (q x t))
  have hC : 0 ≤ C := (abs_nonneg M.yMin).trans (le_max_left _ _)
  refine ⟨Q, ?_, ?_, ?_⟩
  · exact (measurable_const.max (measurable_const.min hq)).comp
      (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd))
  · intro x t
    exact abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  · filter_upwards [hl.ae_eq_mk, boundary_quantile_supported M zeroLaw h he] with x hx hs
    intro hp
    have hK : K x = boundaryLaw M zeroLaw x := by
      change (if 0 < b x then (ENNReal.ofReal (b x))⁻¹ • canonSubmeasure M true x (b x)
        else Measure.dirac M.yMin) = boundaryLaw M zeroLaw x
      dsimp only [b]
      simp only [← hx, boundaryLaw, if_pos hp]
    rw [← restrict_Ioo_eq_restrict_Icc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have hb := outcome_norm_le_magnitude M he (hs t ht)
    rw [Real.norm_eq_abs] at hb
    dsimp only [Q, q]
    rw [dif_pos ht, hK, ← boundaryQuantile_eq_quantile_of_mem_Ioo M zeroLaw x ht]
    change max (-outcomeMagnitude M) (min (outcomeMagnitude M) (boundaryQuantile M zeroLaw x t)) = _
    rw [min_eq_right (abs_le.mp hb).2, max_eq_right (abs_le.mp hb).1]

-- @node: propensity_endpoints_aemeasurable
/-- For a finite measure on a standard Borel parameter space, if [the covariate map is measurable](hyp:hx),
[the propensity is jointly measurable in instrument and covariates](hyp:hp), and
[all propensity values lie in the unit interval](hyp:hb),
[both the infimum and supremum propensities across instruments, evaluated along the covariate map, are almost everywhere measurable](goal). -/
lemma propensity_endpoints_aemeasurable
    {T : Type*} [MeasurableSpace T] [StandardBorelSpace T]
    (ν : Measure T) [IsFiniteMeasure ν] (x : T → X) (hx : Measurable x)
    (p : Z → X → ℝ) (hp : Measurable (Function.uncurry p))
    (hb : ∀ z x, p z x ∈ Icc (0 : ℝ) 1) :
    AEMeasurable (fun t => pLow p (x t)) ν ∧
      AEMeasurable (fun t => pHigh p (x t)) ν := by
  have hm : Measurable (fun tz : T × Z => p tz.2 (x tz.1)) := by
    first | fun_prop | exact hp.comp (measurable_snd.prodMk (hx.comp measurable_fst))
  exact ⟨aemeasurable_bounded_parameter_infimum ν _ hm (fun t z => (hb z (x t)).1),
    aemeasurable_bounded_parameter_supremum ν _ hm (fun t z => (hb z (x t)).2)⟩

-- @node: endpoint_map_aemeasurable
/-- If [the original propensity is jointly measurable](hyp:hp) and [the policy propensity is jointly measurable](hyp:hq),
and [the original propensity lies in the unit interval everywhere](hyp:hb),
[each of the three endpoint maps is almost everywhere measurable under the joint instrument–covariate law](goal). -/
@[fun_prop] lemma endpoint_map_aemeasurable
    (p q : Z → X → ℝ) (hp : Measurable (Function.uncurry p))
    (hq : Measurable (Function.uncurry q)) (hb : ∀ z x, p z x ∈ Icc (0 : ℝ) 1)
    (j : Fin 3) : AEMeasurable (endpointMap p q j) (zxLaw M) := by
  haveI : IsProbabilityMeasure (zxLaw M) := Measure.isProbabilityMeasure_map
    (M.measZ.prodMk M.measX).aemeasurable
  have he := propensity_endpoints_aemeasurable (zxLaw M) Prod.snd measurable_snd p hp hb
  unfold endpointMap
  split_ifs
  · exact he.1
  · exact he.1.min hq.aemeasurable
  · exact aemeasurable_const.max (hq.aemeasurable.sub he.2)

-- @node: endpoint_error_integrable
/-- Under [an admissible policy map](hyp:hphi) and [the threshold-crossing assumptions](hyp:ht),
if [the fitted propensity is jointly measurable](hyp:hp) and [lies in the unit interval everywhere](hyp:hb),
[the absolute difference between each fitted endpoint map and its population counterpart is integrable under the instrument–covariate law](goal). -/
lemma endpoint_error_integrable
    (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (ht : ThresholdCrossing M) (p : Z → X → ℝ)
    (hp : Measurable (Function.uncurry p)) (hb : ∀ z x, p z x ∈ Icc (0 : ℝ) 1)
    (j : Fin 3) : Integrable (fun zx =>
      |endpointMap p (policyProp phi p) j zx -
        endpointMap M.prop (policyProp phi M.prop) j zx|) (zxLaw M) := by
  haveI : IsProbabilityMeasure (zxLaw M) := Measure.isProbabilityMeasure_map
    (M.measZ.prodMk M.measX).aemeasurable
  have hq : Measurable (Function.uncurry (policyProp phi p)) :=
    hphi.1.comp (measurable_fst.prodMk (measurable_snd.prodMk (hp.subtype_mk (h := fun zx => hb zx.1 zx.2))))
  have hm := (endpoint_map_aemeasurable M p (policyProp phi p) hp hq hb j).sub
    (endpoint_map_aemeasurable M M.prop (policyProp phi M.prop) ht.2.1
      (policy_propensity_jointly_measurable M ht phi hphi) M.rangeProp j)
  apply Integrable.of_bound (by simpa only [Real.norm_eq_abs, Pi.sub_apply, Pi.add_apply, Function.comp_apply, Function.uncurry, Set.codRestrict, Pi.add_def] using hm.aestronglyMeasurable.norm) 1
  filter_upwards [] with zx
  have hf := endpoint_maps_range p (policyProp phi p) hb (fun z x => hphi.2 z x _ (hb z x)) j zx
  have hr := population_endpoint_maps_range M phi hphi j zx
  change endpointMap M.prop (policyProp phi M.prop) j zx ∈ Icc (0 : ℝ) 1 at hr
  rw [Real.norm_eq_abs, abs_abs]
  apply abs_le.mpr
  constructor <;> linarith [hf.1, hf.2, hr.1, hr.2]

-- @node: regression_error_integrable
/-- Under [the structural assumptions](hyp:h), [known outcome bounds](hyp:he), and
[an admissible policy map](hyp:hphi), assume [the fitted propensity is jointly measurable](hyp:hp),
[the fitted regression is jointly measurable at unit-interval thresholds](hyp:hg),
[the fitted propensity lies in the unit interval](hyp:hb), and
[the fitted regression is bounded in absolute value by the outcome magnitude on that interval](hyp:hgb).
Then [the sum of absolute fitted-versus-population regression errors at the respective clamped policies and original propensities is integrable under the instrument–covariate law](goal). -/
lemma regression_error_integrable
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (p : Z → X → ℝ) (g : ℝ → X → ℝ)
    (hp : Measurable (Function.uncurry p))
    (hg : Measurable (fun tx : Icc (0 : ℝ) 1 × X => g tx.1.val tx.2))
    (hb : ∀ z x, p z x ∈ Icc (0 : ℝ) 1)
    (hgb : ∀ t x, t ∈ Icc (0 : ℝ) 1 → |g t x| ≤ outcomeMagnitude M) :
    Integrable (fun zx =>
      |g (clampPolicy p (policyProp phi p) zx.1 zx.2) zx.2 -
        g1 M (clampPolicy M.prop (policyProp phi M.prop) zx.1 zx.2) zx.2| +
      |g (p zx.1 zx.2) zx.2 - g1 M (M.prop zx.1 zx.2) zx.2|) (zxLaw M) := by
  haveI : IsProbabilityMeasure (zxLaw M) := Measure.isProbabilityMeasure_map
    (M.measZ.prodMk M.measX).aemeasurable
  have hcl (p : Z → X → ℝ) (hp : Measurable (Function.uncurry p))
      (hb : ∀ z x, p z x ∈ Icc (0 : ℝ) 1) :
      AEMeasurable (Function.uncurry (clampPolicy p (policyProp phi p))) (zxLaw M) := by
    have hq : Measurable (Function.uncurry (policyProp phi p)) :=
      hphi.1.comp (measurable_fst.prodMk (measurable_snd.prodMk (hp.subtype_mk (h := fun zx => hb zx.1 zx.2))))
    have he := propensity_endpoints_aemeasurable (zxLaw M) Prod.snd measurable_snd p hp hb
    exact he.2.min (he.1.max hq.aemeasurable)
  have hcr (p : Z → X → ℝ) (hb : ∀ z x, p z x ∈ Icc (0 : ℝ) 1) (zx : Z × X) :
      clampPolicy p (policyProp phi p) zx.1 zx.2 ∈ Icc (0 : ℝ) 1 := by
    have he := propensity_support_endpoints p hb zx.2
    exact ⟨le_min he.2.1.1 (le_max_of_le_left he.1.1), (min_le_left _ _).trans he.2.1.2⟩
  have hm1 := hg.comp_aemeasurable
    ((AEMeasurable.subtype_mk (hcl p hp hb) (hfs := fun zx => hcr p hb zx)).prodMk measurable_snd.aemeasurable)
  have hm2 := (measurable_canonical_regression M).comp_aemeasurable
    ((hcl M.prop h.2.2.2.1.2.1 M.rangeProp).prodMk measurable_snd.aemeasurable)
  have hm3 := hg.comp ((hp.subtype_mk (h := fun zx => hb zx.1 zx.2)).prodMk measurable_snd)
  have hm4 := (measurable_canonical_regression M).comp
    (h.2.2.2.1.2.1.prodMk measurable_snd)
  apply Integrable.of_bound (by simpa only [Real.norm_eq_abs, Pi.sub_apply, Pi.add_apply, Function.comp_apply, Function.uncurry, Set.codRestrict, Pi.add_def] using
    (hm1.sub hm2).aestronglyMeasurable.norm.add (hm3.sub hm4).aestronglyMeasurable.norm)
    (4 * outcomeMagnitude M)
  have hmap : (zxLaw M).map Prod.snd = xLaw M := by
    rw [zxLaw, Measure.map_map measurable_snd (M.measZ.prodMk M.measX)]
    rfl
  have hx := population_regression_magnitude M h he
  rw [← hmap] at hx
  filter_upwards [ae_of_ae_map measurable_snd.aemeasurable hx] with zx hx
  rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))]
  have h1 := abs_sub (g (clampPolicy p (policyProp phi p) zx.1 zx.2) zx.2)
    (g1 M (clampPolicy M.prop (policyProp phi M.prop) zx.1 zx.2) zx.2)
  have h2 := abs_sub (g (p zx.1 zx.2) zx.2) (g1 M (M.prop zx.1 zx.2) zx.2)
  linarith [hgb _ zx.2 (hcr p hb zx), hgb _ zx.2 (hb zx.1 zx.2),
    hx _ (hcr M.prop M.rangeProp zx), hx _ (M.rangeProp zx.1 zx.2)]

-- @node: weighted_boundary_distance_integrable
/-- For [a covariate-indexed fallback probability law supported on the outcome range](hyp:zeroLaw), under [the structural assumptions](hyp:h) and [known outcome bounds](hyp:he), suppose
[the fitted rank function is jointly measurable on covariates and unit ranks](hyp:hQ),
[nondecreasing on interior ranks](hyp:hm), and [bounded in absolute value by the outcome magnitude on unit ranks](hyp:hb).
Then [the quantile distance between its induced law and the population boundary law, weighted by the lower population propensity, is integrable under the covariate law](goal). -/
lemma weighted_boundary_distance_integrable
    (zeroLaw : X → {ν : ProbabilityMeasure ℝ // ν.toMeasure M.Ysetᶜ = 0})
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (Q : X → ℝ → ℝ)
    (hQ : Measurable (fun xt : X × Icc (0 : ℝ) 1 => Q xt.1 xt.2.val))
    (hm : ∀ x, MonotoneOn (Q x) (Ioo (0 : ℝ) 1))
    (hb : ∀ x t, t ∈ Icc (0 : ℝ) 1 → |Q x t| ≤ outcomeMagnitude M) :
    Integrable (fun x => pLow M.prop x * quantileDistanceIntegral
      (Causalean.Stat.unifOI.map (Q x)) (boundaryLaw M zeroLaw x)) (xLaw M) := by
  haveI : IsProbabilityMeasure (xLaw M) := Measure.isProbabilityMeasure_map M.measX.aemeasurable
  obtain ⟨R, hR, hRb, hReq⟩ := exists_population_boundary_rank_version M zeroLaw h he
  let f : X × ℝ → ℝ := fun xt => |Q xt.1 (unitRankClamp xt.2) - R xt.1 (unitRankClamp xt.2)|
  have hf : Measurable f := by
    first | fun_prop | exact ((hQ.comp (measurable_fst.prodMk (measurable_unitRankClamp.comp measurable_snd))).sub
      (hR.comp (measurable_fst.prodMk (measurable_unitRankClamp.comp measurable_snd)))).norm
  have hi : Measurable (fun x => ∫ t in Icc (0 : ℝ) 1, f (x,t)) :=
    (hf.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Icc (0 : ℝ) 1))).measurable
  have hl := (propensity_endpoints_aemeasurable (xLaw M) id measurable_id M.prop
    h.2.2.2.1.2.1 M.rangeProp).1
  have hInt : Integrable (fun x => pLow M.prop x * ∫ t in Icc (0 : ℝ) 1, f (x,t)) (xLaw M) := by
    apply Integrable.of_bound (hl.mul hi.aemeasurable).aestronglyMeasurable (2 * outcomeMagnitude M)
    filter_upwards [] with x
    have hb' : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1), ‖f (x,t)‖ ≤ 2 * outcomeMagnitude M := by
      filter_upwards [] with t
      have ht := (unitRankClamp t).property
      dsimp only [f]
      rw [Real.norm_eq_abs, abs_abs]
      exact (abs_sub _ _).trans (by linarith [hb x _ ht, hRb x (unitRankClamp t)])
    have hbI := norm_integral_le_of_norm_le_const hb'
    simp only [measureReal_def, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero, ENNReal.ofReal_one, ENNReal.toReal_one, one_mul, mul_one] at hbI
    have he := (propensity_support_endpoints M.prop M.rangeProp x).1
    simp only [Pi.mul_apply, id_eq]
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg he.1]
    exact (mul_le_mul_of_nonneg_left hbI he.1).trans
      (mul_le_of_le_one_left (mul_nonneg (by norm_num) ((abs_nonneg M.yMin).trans (le_max_left _ _))) he.2)
  apply hInt.congr
  filter_upwards [hReq] with x hx
  rw [quantile_distance_uniform_map _ _ (hm x)]
  by_cases hp : 0 < pLow M.prop x
  · congr 1
    apply integral_congr_ae
    have hraw : R x =ᵐ[volume.restrict (Icc (0 : ℝ) 1)]
        Causalean.Stat.quantile (boundaryLaw M zeroLaw x) :=
      (hx hp).trans (by
        simpa only [Causalean.Stat.unifOI, restrict_Ioo_eq_restrict_Icc] using
          boundaryQuantile_ae_quantile M zeroLaw x)
    filter_upwards [hraw, ae_restrict_mem measurableSet_Icc] with t ht hmem
    dsimp only [f]
    rw [unitRankClamp_of_mem t hmem, ht]
  · have hz : pLow M.prop x = 0 := le_antisymm (le_of_not_gt hp)
      (propensity_support_endpoints M.prop M.rangeProp x).1.1
    rw [hz, zero_mul, zero_mul]

set_option maxHeartbeats 1000000 in
-- @node: connected_lower_integrable
/-- For [a covariate-indexed fallback probability law supported on the outcome range](hyp:zeroLaw), under [the structural assumptions](hyp:h), [known outcome bounds](hyp:he), and
[an admissible policy map](hyp:hphi), [the connected lower integrand for the policy-transformed population propensity is integrable under the instrument–covariate law](goal). -/
lemma connected_lower_integrable
    (zeroLaw : X → {ν : ProbabilityMeasure ℝ // ν.toMeasure M.Ysetᶜ = 0})
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi) :
    Integrable (connectedInt M zeroLaw false (policyProp phi M.prop)) (zxLaw M) := by
  haveI : IsProbabilityMeasure (zxLaw M) := Measure.isProbabilityMeasure_map
    (M.measZ.prodMk M.measX).aemeasurable
  obtain ⟨R, hR, hRb, hReq⟩ := exists_population_boundary_rank_version M zeroLaw h he
  let C := outcomeMagnitude M
  have hC : 0 ≤ C := (abs_nonneg M.yMin).trans (le_max_left _ _)
  let G : ℝ → X → ℝ := fun t x => max (-C) (min C (g1 M t x))
  have hGb (t : ℝ) (x : X) : |G t x| ≤ C :=
    abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hGm : Measurable (fun tx : ℝ × X => G tx.1 tx.2) := by
    first | fun_prop | exact measurable_const.max (measurable_const.min (measurable_canonical_regression M))
  let d : Z × X → Unit × Obs X Z := fun zx => ((), (zx.2,zx.1,0,0))
  have hd : Measurable d := by fun_prop
  have hp : Measurable (fun tzx : Unit × Z × X => M.prop tzx.2.1 tzx.2.2) :=
    h.2.2.2.1.2.1.comp measurable_snd
  have hg : Measurable (fun tpx : Unit × Icc (0 : ℝ) 1 × X => G tpx.2.1.val tpx.2.2) :=
    by
      simpa only [Function.comp_def] using hGm.comp (show Measurable (fun tpx : Unit × Icc (0 : ℝ) 1 × X =>
      (tpx.2.1.val, tpx.2.2)) by fun_prop)
  have hq : Measurable (fun txr : Unit × X × Icc (0 : ℝ) 1 => R txr.2.1 txr.2.2.val) :=
    hR.comp measurable_snd
  have hfm := aemeasurable_fittedInt_lower_training_block M ((zxLaw M).map d) phi hphi
    (fun _ => M.prop) (fun _ => G) (fun _ => R) hp hg hq (fun _ => M.rangeProp)
  have hm := hfm.comp_measurable hd
  have hRi (x : X) : IntegrableOn (R x) (Icc (0 : ℝ) 1) := by
    refine Integrable.of_bound ?_ C ?_
    · have hm : AEStronglyMeasurable (fun t => R x (unitRankClamp t))
          (volume.restrict (Icc (0 : ℝ) 1)) :=
        (hR.comp ((measurable_const (a := x)).prodMk measurable_unitRankClamp)).aestronglyMeasurable
      apply hm.congr
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      rw [unitRankClamp_of_mem t ht]
    · filter_upwards [] with t
      simpa only [Real.norm_eq_abs] using hRb x t
  have hi : Integrable (fun zx => fittedInt M false phi M.prop G
      (fun x => quantilePrimitive (R x)) (zx.2,zx.1,0,0)) (zxLaw M) := by
    apply Integrable.of_bound hm.aestronglyMeasurable (4 * C)
    filter_upwards [] with zx
    rw [Real.norm_eq_abs]
    exact fittedInt_lower_bounded M phi hphi M.prop G R M.rangeProp hC
      (le_max_left _ _) (fun t x _ => hGb t x) hRi (fun x t _ => hRb x t) _
  apply hi.congr
  have hmap : (zxLaw M).map Prod.snd = xLaw M := by
    rw [zxLaw, Measure.map_map measurable_snd (M.measZ.prodMk M.measX)]
    rfl
  have hx := hReq.and ((population_regression_magnitude M h he).and
    (population_fitted_lower_eq_connected M zeroLaw h he phi hphi))
  rw [← hmap] at hx
  filter_upwards [ae_of_ae_map measurable_snd.aemeasurable hx] with zx hx
  have hprim (hp : 0 < pLow M.prop zx.2) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      quantilePrimitive (R zx.2) t = quantilePrimitive (boundaryQuantile M zeroLaw zx.2) t := by
    apply integral_congr_ae
    exact (hx.1 hp).filter_mono (ae_mono (Measure.restrict_mono_set volume
      (fun u hu => ⟨hu.1.le, hu.2.trans ht.2⟩)))
  have hcl : clampPolicy M.prop (policyProp phi M.prop) zx.1 zx.2 ∈ Icc (0 : ℝ) 1 := by
    have he := propensity_support_endpoints M.prop M.rangeProp zx.2
    exact ⟨le_min he.2.1.1 (le_max_of_le_left he.1.1), (min_le_left _ _).trans he.2.1.2⟩
  have hGeq (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : G t zx.2 = g1 M t zx.2 := by
    have hb := abs_le.mp (hx.2.1 t ht)
    dsimp only [G, C]
    rw [min_eq_right hb.2, max_eq_right hb.1]
  rw [← hx.2.2 zx.1 0 0]
  dsimp only [fittedInt]
  simp only [Bool.false_eq_true, if_false, hGeq _ hcl, hGeq _ (M.rangeProp zx.1 zx.2)]
  by_cases hp : 0 < pLow M.prop zx.2
  · have ht : min 1 (phi zx.1 zx.2 (M.prop zx.1 zx.2) / pLow M.prop zx.2) ∈ Icc (0 : ℝ) 1 :=
      ⟨le_min zero_le_one (div_nonneg (hphi.2 _ _ _ (M.rangeProp _ _)).1 hp.le), min_le_left _ _⟩
    rw [if_pos hp, if_pos hp, hprim hp 1 ⟨zero_le_one, le_rfl⟩, hprim hp _ ht]
  · rw [if_neg hp, if_neg hp]

-- @node: connected_lower_target_identity
/-- For [a covariate-indexed fallback probability law supported on the outcome range](hyp:zeroLaw), under [the structural assumptions](hyp:h), [known outcome bounds](hyp:he),
[continuity of the propensity on instrument components](hyp:hc),
[finitely many instrument components](hyp:hfin), [a connected instrument space](hyp:hconn), and
[an admissible policy map](hyp:hphi), [the sharp lower treated-outcome transport target with policy weights equals the connected lower value for the policy-transformed population propensity](goal). -/
lemma connected_lower_target_identity
    (zeroLaw : X → {ν : ProbabilityMeasure ℝ // ν.toMeasure M.Ysetᶜ = 0})
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (hc : PropensityContinuousOnComponents M) (hfin : FiniteInstrumentComponents Z)
    (hconn : InstrumentConnected Z)
    (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi) :
    thetaLower1 (transportData M) (policyWeight M (policyProp phi M.prop)) =
      connectedValue M zeroLaw false (policyProp phi M.prop) := by
  have hRegular := policyWeight_target_regular M h.2.2.2.1 (policyProp phi M.prop)
    (policy_propensity_jointly_measurable M h.2.2.2.1 phi hphi)
  have hSharp := conditional_sharp_bounds_assembly M h he
    (policyWeight M (policyProp phi M.prop)) hRegular.1 hRegular.2 hc hfin
  apply hSharp.2.2.2.2.1.trans
  calc
    _ = ∫ x, (∫ z, connectedInt M zeroLaw false (policyProp phi M.prop) (z,x)
        ∂M.instKernel x) ∂xLaw M :=
      integral_congr_ae (connected_conditional_formula M zeroLaw h he hc hfin hconn phi hphi false)
    _ = _ := instrument_kernel_outer_integral M _ (connected_lower_integrable M zeroLaw h he phi hphi)

end Papers.TbsPrteOptimalTransport

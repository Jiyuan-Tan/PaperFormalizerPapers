module
public import Papers.TbsPrteOptimalTransport.Helpers.Attainment
public import Mathlib.MeasureTheory.Integral.Prod
/-! The prescribed outcome marginal of the randomized gap optimizer. -/
public section
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.style.openClassical false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z]
variable (M : LatentIVModel Ω X Z)

-- @node: gap_weight_aemeasurable
/-- If [the target weight is measurable on covariates and unit-interval ranks](hyp:hm) and
[the gap index is within the conditional decomposition](hyp:hk), then
[the weight at the given covariate value is almost everywhere measurable under the uniform law on that gap](goal). -/
lemma gap_weight_aemeasurable (om : X → ℝ → ℝ) (hm : TargetWeightMeasurable om)
    (x : X) (k : ℕ) (hk : k < (CondRangeDecomposition M x).count) :
    AEMeasurable (om x) (gapUnif M x k) := by
  have he := conditional_gap_endpoints M x k hk
  have hs : Measurable (fun u : Icc (0 : ℝ) 1 => om x u.val) := by
    exact hm.comp (measurable_const.prodMk measurable_id)
  have hu : AEMeasurable (om x) (volume.restrict (Icc (0 : ℝ) 1)) :=
    aemeasurable_restrict_of_measurable_subtype measurableSet_Icc hs
  change AEMeasurable (om x) (_ • volume.restrict (Ioo _ _))
  apply AEMeasurable.smul_measure
  apply hu.mono_measure
  apply Measure.restrict_mono_set
  intro u hu
  exact ⟨he.1.1.trans hu.1.le, hu.2.le.trans he.2.2⟩

-- @node: gap_rank_aemeasurable
/-- If [the target weight is measurable](hyp:hm), [the gap index is within the conditional decomposition](hyp:hk),
and [the gap has positive length](hyp:hab), then [the randomized weight rank is almost everywhere measurable
under independent uniform draws from the gap and the unit interval](goal). -/
@[fun_prop] lemma gap_rank_aemeasurable (om : X → ℝ → ℝ) (hm : TargetWeightMeasurable om)
    (x : X) (k : ℕ) (hk : k < (CondRangeDecomposition M x).count)
    (hab : (CondRangeDecomposition M x).gapLo k < (CondRangeDecomposition M x).gapHi k) :
    AEMeasurable (fun a : ℝ × ℝ => randomizedRank M om x k a.1 a.2)
      ((gapUnif M x k).prod Causalean.Stat.unifOI) := by
  have hf := gap_weight_aemeasurable M om hm x k hk
  haveI : IsProbabilityMeasure (gapUnif M x k) := uniformInterval_isProbability _ _ hab
  haveI : IsProbabilityMeasure ((gapUnif M x k).map (om x)) := Measure.isProbabilityMeasure_map hf
  have hg : AEMeasurable (fun a : ℝ × ℝ => (om x a.1, a.2))
      ((gapUnif M x k).prod Causalean.Stat.unifOI) := by
    fun_prop
  have hr := (DistributionalTransform.measurable_rank ((gapUnif M x k).map (om x))).comp_aemeasurable hg
  simpa only [DistributionalTransform.rank, DistributionalTransform.leftCDF,
    cdf_eq_real, measureReal_def, randomizedRank, weightCDF, weightCDFLeft,
    weightLaw, Function.comp_def] using hr

-- @node: gap_map_product_eq_bind
/-- If [a function of two real variables is almost everywhere measurable under the product of two measures](hyp:hf),
then [its distribution under that product equals the mixture, over the first variable, of its distributions under the second measure](goal).

Both measures are assumed to be countable sums of finite measures. -/
lemma gap_map_product_eq_bind (mu nu : Measure ℝ) [SFinite mu] [SFinite nu]
    (f : ℝ × ℝ → ℝ) (hf : AEMeasurable f (mu.prod nu)) :
    (mu.prod nu).map f = mu.bind (fun u => nu.map (fun s => f (u, s))) := by
  let g := hf.mk f
  have hg : Measurable g := hf.measurable_mk
  have hgm : Measurable (fun u => nu.map (fun s => g (u, s))) := by
    have hmap := (Measure.measurable_map g hg).comp
      (Measurable.map_prodMk_left (ν := nu) (α := ℝ))
    simpa only [Measure.map_map hg measurable_prodMk_left, Function.comp_def] using hmap
  have heq : (fun u => nu.map (fun s => f (u, s))) =ᵐ[mu]
      (fun u => nu.map (fun s => g (u, s))) := by
    filter_upwards [Measure.ae_ae_of_ae_prod hf.ae_eq_mk] with u hu
    exact Measure.map_congr hu
  rw [Measure.map_congr hf.ae_eq_mk, Measure.bind_congr_right heq]
  ext A hA
  rw [Measure.map_apply hg hA, Measure.prod_apply (hg hA),
    Measure.bind_apply hA hgm.aemeasurable]
  apply lintegral_congr
  intro u
  have hgu : Measurable (fun s => g (u, s)) := by fun_prop
  rw [Measure.map_apply hgu hA]
  rfl

-- @node: gap_attaining_product_marginal
/-- Under [the structural assumptions](hyp:h), [continuity of propensity on instrument components](hyp:hc),
and [finitely many instrument components](hyp:hfin), suppose [the target weight is measurable](hyp:hm)
and [the measurable outcome quantile extension agrees with the gap quantiles and stays in the outcome set](hyp:hQ).
Then [for almost every covariate value and every gap of positive length, applying that extension to one minus the randomized weight rank,
using independent uniform draws from the gap and the unit interval, produces the prescribed gap outcome law](goal). -/
lemma gap_attaining_product_marginal (h : StructuralAssumptions M)
    (hc : PropensityContinuousOnComponents M) (hfin : FiniteInstrumentComponents Z)
    (om : X → ℝ → ℝ) (hm : TargetWeightMeasurable om)
    (Q : X → ℕ → ℝ → ℝ) (hQ : RankKernelExtensionReading M Q) :
    ∀ᵐ x ∂xLaw M, ∀ k < (CondRangeDecomposition M x).count,
      (CondRangeDecomposition M x).gapLo k < (CondRangeDecomposition M x).gapHi k →
      ((gapUnif M x k).prod Causalean.Stat.unifOI).map
        (fun a => Q x k (1 - randomizedRank M om x k a.1 a.2)) = gapLaw M x k := by
  filter_upwards [randomized_rank_uniform M h om hm,
    gap_law_isProbability M h hc hfin, hQ.2] with x hr hp hq
  intro k hk hab
  haveI : IsProbabilityMeasure (gapLaw M x k) := hp k hk hab
  have hR := gap_rank_aemeasurable M om hm x k hk hab
  have hRef : Measurable (fun t : ℝ => 1 - t) := by fun_prop
  have hU : ((gapUnif M x k).prod Causalean.Stat.unifOI).map
      (fun a => 1 - randomizedRank M om x k a.1 a.2) = Causalean.Stat.unifOI := by
    change ((gapUnif M x k).prod Causalean.Stat.unifOI).map
      ((fun t : ℝ => 1 - t) ∘ (fun a => randomizedRank M om x k a.1 a.2)) = _
    rw [← AEMeasurable.map_map_of_aemeasurable hRef.aemeasurable hR,
      (hr k hk hab).1, Causalean.Stat.map_one_sub_unifOI]
  have hQx : Measurable (Q x k) := by
    exact hQ.1.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have heq : Q x k =ᵐ[Causalean.Stat.unifOI] Causalean.Stat.quantile (gapLaw M x k) := by
    filter_upwards [(ae_restrict_mem measurableSet_Ioo : ∀ᵐ t ∂Causalean.Stat.unifOI, t ∈ Ioo (0 : ℝ) 1)] with t ht
    exact (hq k hk hab).2 t ht
  calc
    ((gapUnif M x k).prod Causalean.Stat.unifOI).map
        (fun a => Q x k (1 - randomizedRank M om x k a.1 a.2)) =
      (((gapUnif M x k).prod Causalean.Stat.unifOI).map
        (fun a => 1 - randomizedRank M om x k a.1 a.2)).map (Q x k) := by
          simpa only [Function.comp_def] using
            (AEMeasurable.map_map_of_aemeasurable hQx.aemeasurable
              (hRef.comp_aemeasurable hR)).symm
    _ = Causalean.Stat.unifOI.map (Q x k) := by rw [hU]
    _ = Causalean.Stat.unifOI.map (Causalean.Stat.quantile (gapLaw M x k)) :=
      Measure.map_congr heq
    _ = gapLaw M x k := Causalean.Stat.quantile_map_uniform _

-- @node: gap_attaining_marginal
/-- Under [the structural assumptions](hyp:h), [continuity of propensity on instrument components](hyp:hc),
and [finitely many instrument components](hyp:hfin), suppose [the target weight is measurable](hyp:hm)
and [the measurable outcome quantile extension agrees with the gap quantiles and takes values in the outcome set](hyp:hQ).
Then [for almost every covariate value and every gap of positive length, mixing the attaining conditional outcome laws
over the uniform distribution on the gap gives the prescribed gap outcome law](goal). -/
lemma gap_attaining_marginal (h : StructuralAssumptions M)
    (hc : PropensityContinuousOnComponents M) (hfin : FiniteInstrumentComponents Z)
    (om : X → ℝ → ℝ) (hm : TargetWeightMeasurable om)
    (Q : X → ℕ → ℝ → ℝ) (hQ : RankKernelExtensionReading M Q) :
    ∀ᵐ x ∂xLaw M, ∀ k < (CondRangeDecomposition M x).count,
      (CondRangeDecomposition M x).gapLo k < (CondRangeDecomposition M x).gapHi k →
      (gapUnif M x k).bind (gapAttainingLaw M om Q x k) = gapLaw M x k := by
  filter_upwards [gap_attaining_product_marginal M h hc hfin om hm Q hQ] with x hx
  intro k hk hab
  haveI : IsProbabilityMeasure (gapUnif M x k) := uniformInterval_isProbability _ _ hab
  have hR := gap_rank_aemeasurable M om hm x k hk hab
  have hQx : Measurable (Q x k) :=
    hQ.1.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have hf : AEMeasurable (fun a : ℝ × ℝ => Q x k (1 - randomizedRank M om x k a.1 a.2))
      ((gapUnif M x k).prod Causalean.Stat.unifOI) := by
    fun_prop
  rw [← hx k hk hab]
  exact (gap_map_product_eq_bind _ _ _ hf).symm

-- @node: gap_attaining_product_cost
/-- Under [the structural assumptions](hyp:h), with [a measurable target weight](hyp:hm)
and [a measurable outcome quantile extension that agrees with gap quantiles and stays in the outcome set](hyp:hQ),
[for almost every covariate value and every gap of positive length, the expected product of the weight and the outcome
assigned by the reflected randomized rank equals the integral of the outcome quantile times the oppositely ranked weight quantile](goal). -/
lemma gap_attaining_product_cost (h : StructuralAssumptions M)
    (om : X → ℝ → ℝ) (hm : TargetWeightMeasurable om)
    (Q : X → ℕ → ℝ → ℝ) (hQ : RankKernelExtensionReading M Q) :
    ∀ᵐ x ∂xLaw M, ∀ k < (CondRangeDecomposition M x).count,
      (CondRangeDecomposition M x).gapLo k < (CondRangeDecomposition M x).gapHi k →
      (∫ a, Q x k (1 - randomizedRank M om x k a.1 a.2) * om x a.1
        ∂(gapUnif M x k).prod Causalean.Stat.unifOI) =
      ∫ t in Ioo (0 : ℝ) 1, (gapQuantiles M om x k).1 t *
        (gapQuantiles M om x k).2 (1 - t) := by
  filter_upwards [randomized_rank_uniform M h om hm, hQ.2] with x hr hq
  intro k hk hab
  let R := fun a : ℝ × ℝ => randomizedRank M om x k a.1 a.2
  let rho := (gapUnif M x k).prod Causalean.Stat.unifOI
  have hR : AEMeasurable R rho := gap_rank_aemeasurable M om hm x k hk hab
  have hmap : rho.map R = Causalean.Stat.unifOI := (hr k hk hab).1
  have hQx : Measurable (Q x k) :=
    hQ.1.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  let f := fun t : ℝ => Q x k (1 - t) * Causalean.Stat.quantile (weightLaw M om x k) t
  have hf : AEMeasurable f Causalean.Stat.unifOI := by
    exact (hQx.comp (measurable_const.sub measurable_id)).aemeasurable.mul
      (Causalean.Stat.aemeasurable_quantile_unifOI _)
  have hfmap : AEStronglyMeasurable f (rho.map R) := by
    rw [hmap]
    exact hf.aestronglyMeasurable
  have hcost : (∫ a, Q x k (1 - R a) * om x a.1 ∂rho) =
      ∫ t, f t ∂Causalean.Stat.unifOI := by
    calc
      _ = ∫ a, f (R a) ∂rho := by
        apply integral_congr_ae
        filter_upwards [(hr k hk hab).2] with a ha
        exact congrArg (fun v => Q x k (1 - R a) * v) ha
      _ = ∫ t, f t ∂rho.map R := (integral_map hR hfmap).symm
      _ = _ := by rw [hmap]
  have hRef : Measurable (fun t : ℝ => 1 - t) := by fun_prop
  have hfref : AEStronglyMeasurable f
      (Causalean.Stat.unifOI.map (fun t : ℝ => 1 - t)) := by
    rw [Causalean.Stat.map_one_sub_unifOI]
    exact hf.aestronglyMeasurable
  change (∫ a, Q x k (1 - R a) * om x a.1 ∂rho) = _
  rw [hcost]
  calc
    _ = ∫ t, f t ∂Causalean.Stat.unifOI.map (fun t : ℝ => 1 - t) := by
      rw [Causalean.Stat.map_one_sub_unifOI]
    _ = ∫ t, Q x k t * Causalean.Stat.quantile (weightLaw M om x k) (1 - t)
        ∂Causalean.Stat.unifOI := by
      rw [integral_map hRef.aemeasurable hfref]
      simp only [f, sub_sub_cancel]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [(ae_restrict_mem measurableSet_Ioo :
        ∀ᵐ t ∂Causalean.Stat.unifOI, t ∈ Ioo (0 : ℝ) 1)] with t ht
      have ht0 : t ≠ 0 := ne_of_gt ht.1
      have ht1 : t ≠ 1 := ne_of_lt ht.2
      simp only [gapQuantiles, endpointGapQuantile, if_neg ht0, if_neg ht1]
      rw [(hq k hk hab).2 t ht]

-- @node: gap_attaining_quantile_joint_law
/-- Under [the structural assumptions](hyp:h), with [a measurable target weight](hyp:hm)
and [a measurable outcome quantile extension agreeing with gap quantiles and taking values in the outcome set](hyp:hQ),
[for almost every covariate value and every gap of positive length, the joint law of the assigned outcome and weight equals
the law obtained from a uniform quantile index, pairing outcome and weight quantiles in the same order for the upper choice
and in opposite orders for the lower choice](goal). -/
lemma gap_attaining_quantile_joint_law (h : StructuralAssumptions M)
    (om : X → ℝ → ℝ) (hm : TargetWeightMeasurable om)
    (Q : X → ℕ → ℝ → ℝ) (hQ : RankKernelExtensionReading M Q) (upper : Bool) :
    ∀ᵐ x ∂xLaw M, ∀ k < (CondRangeDecomposition M x).count,
      (CondRangeDecomposition M x).gapLo k < (CondRangeDecomposition M x).gapHi k →
      ((gapUnif M x k).prod Causalean.Stat.unifOI).map
        (fun a => (Q x k (if upper then randomizedRank M om x k a.1 a.2
          else 1 - randomizedRank M om x k a.1 a.2), om x a.1)) =
      Causalean.Stat.unifOI.map (fun t =>
        (Causalean.Stat.quantile (gapLaw M x k) t,
          Causalean.Stat.quantile (weightLaw M om x k) (if upper then t else 1 - t))) := by
  filter_upwards [randomized_rank_uniform M h om hm, hQ.2] with x hr hq
  intro k hk hab
  let rho := (gapUnif M x k).prod Causalean.Stat.unifOI
  let R := fun a : ℝ × ℝ => randomizedRank M om x k a.1 a.2
  let T := fun a => if upper then R a else 1 - R a
  have hR : AEMeasurable R rho := gap_rank_aemeasurable M om hm x k hk hab
  have hRef : Measurable (fun t : ℝ => 1 - t) := by fun_prop
  have hT : AEMeasurable T rho := by
    cases upper <;> dsimp [T] <;> fun_prop
  have hTmap : rho.map T = Causalean.Stat.unifOI := by
    cases upper with
    | false =>
      change rho.map ((fun t : ℝ => 1 - t) ∘ R) = _
      rw [← AEMeasurable.map_map_of_aemeasurable hRef.aemeasurable hR,
        (hr k hk hab).1, Causalean.Stat.map_one_sub_unifOI]
    | true => exact (hr k hk hab).1
  haveI : IsProbabilityMeasure (gapUnif M x k) := uniformInterval_isProbability _ _ hab
  haveI : IsProbabilityMeasure (weightLaw M om x k) :=
    Measure.isProbabilityMeasure_map (gap_weight_aemeasurable M om hm x k hk)
  have hv := Causalean.Stat.aemeasurable_quantile_unifOI (weightLaw M om x k)
  have hvref : AEMeasurable (fun t : ℝ =>
      Causalean.Stat.quantile (weightLaw M om x k) (1 - t)) Causalean.Stat.unifOI := by
    have hvmap : AEMeasurable (Causalean.Stat.quantile (weightLaw M om x k))
        (Causalean.Stat.unifOI.map (fun t : ℝ => 1 - t)) := by
      rwa [Causalean.Stat.map_one_sub_unifOI]
    exact hvmap.comp_aemeasurable hRef.aemeasurable
  have hQx : Measurable (Q x k) :=
    hQ.1.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  let f := fun t : ℝ => (Q x k t,
    Causalean.Stat.quantile (weightLaw M om x k) (if upper then t else 1 - t))
  have hf : AEMeasurable f Causalean.Stat.unifOI := by
    cases upper
    · exact hQx.aemeasurable.prodMk hvref
    · exact hQx.aemeasurable.prodMk hv
  have hfmap : AEMeasurable f (rho.map T) := by rwa [hTmap]
  calc
    _ = rho.map (f ∘ T) := by
      apply Measure.map_congr
      filter_upwards [(hr k hk hab).2] with a ha
      dsimp [f, T, R, Function.comp_def]
      cases upper <;> simp only [Bool.false_eq_true, ↓reduceIte, sub_sub_cancel]
      · exact Prod.ext rfl ha
      · exact Prod.ext rfl ha
    _ = (rho.map T).map f :=
      (AEMeasurable.map_map_of_aemeasurable hfmap hT).symm
    _ = Causalean.Stat.unifOI.map f := by rw [hTmap]
    _ = _ := by
      apply Measure.map_congr
      filter_upwards [(ae_restrict_mem measurableSet_Ioo :
        ∀ᵐ t ∂Causalean.Stat.unifOI, t ∈ Ioo (0 : ℝ) 1)] with t ht
      exact Prod.ext ((hq k hk hab).2 t ht) rfl

-- @node: gap_attaining_product_coupling
/-- Under [the structural assumptions](hyp:h), [continuity of propensity on instrument components](hyp:hc),
and [finitely many instrument components](hyp:hfin), with [a measurable target weight](hyp:hm)
and [a measurable outcome quantile extension agreeing with gap quantiles and staying in the outcome set](hyp:hQ),
[for almost every covariate value and every gap of positive length, the randomized assignment of outcome and weight
is a probability coupling of the prescribed gap outcome law and the gap weight law, for either the upper or lower rank choice](goal). -/
lemma gap_attaining_product_coupling (h : StructuralAssumptions M)
    (hc : PropensityContinuousOnComponents M) (hfin : FiniteInstrumentComponents Z)
    (om : X → ℝ → ℝ) (hm : TargetWeightMeasurable om)
    (Q : X → ℕ → ℝ → ℝ) (hQ : RankKernelExtensionReading M Q) (upper : Bool) :
    ∀ᵐ x ∂xLaw M, ∀ k < (CondRangeDecomposition M x).count,
      (CondRangeDecomposition M x).gapLo k < (CondRangeDecomposition M x).gapHi k →
      IsCoupling (((gapUnif M x k).prod Causalean.Stat.unifOI).map
        (fun a => (Q x k (if upper then randomizedRank M om x k a.1 a.2
          else 1 - randomizedRank M om x k a.1 a.2), om x a.1)))
        (gapLaw M x k) (weightLaw M om x k) := by
  filter_upwards [gap_attaining_quantile_joint_law M h om hm Q hQ upper,
    gap_law_isProbability M h hc hfin] with x hj hp
  intro k hk hab
  haveI : IsProbabilityMeasure (gapLaw M x k) := hp k hk hab
  haveI : IsProbabilityMeasure (gapUnif M x k) := uniformInterval_isProbability _ _ hab
  haveI : IsProbabilityMeasure (weightLaw M om x k) :=
    Measure.isProbabilityMeasure_map (gap_weight_aemeasurable M om hm x k hk)
  rw [hj k hk hab]
  cases upper with
  | false => exact Causalean.Stat.isCoupling_countermonotoneCoupling _ _
  | true => exact Causalean.Stat.isCoupling_comonotoneCoupling _ _

-- @node: gap_attaining_upper_product_marginal
/-- Under [the structural assumptions](hyp:h), [continuity of propensity on instrument components](hyp:hc),
and [finitely many instrument components](hyp:hfin), suppose [the target weight is measurable](hyp:hm)
and [the measurable outcome quantile extension agrees with gap quantiles and stays in the outcome set](hyp:hQ).
Then [for almost every covariate value and every gap of positive length, applying that extension directly to the randomized
weight rank under independent uniform gap and unit-interval draws produces the prescribed gap outcome law](goal). -/
lemma gap_attaining_upper_product_marginal (h : StructuralAssumptions M)
    (hc : PropensityContinuousOnComponents M) (hfin : FiniteInstrumentComponents Z)
    (om : X → ℝ → ℝ) (hm : TargetWeightMeasurable om)
    (Q : X → ℕ → ℝ → ℝ) (hQ : RankKernelExtensionReading M Q) :
    ∀ᵐ x ∂xLaw M, ∀ k < (CondRangeDecomposition M x).count,
      (CondRangeDecomposition M x).gapLo k < (CondRangeDecomposition M x).gapHi k →
      ((gapUnif M x k).prod Causalean.Stat.unifOI).map
        (fun a => Q x k (randomizedRank M om x k a.1 a.2)) = gapLaw M x k := by
  filter_upwards [randomized_rank_uniform M h om hm,
    gap_law_isProbability M h hc hfin, hQ.2] with x hr hp hq
  intro k hk hab
  haveI : IsProbabilityMeasure (gapLaw M x k) := hp k hk hab
  have hR := gap_rank_aemeasurable M om hm x k hk hab
  have hQx : Measurable (Q x k) :=
    hQ.1.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have heq : Q x k =ᵐ[Causalean.Stat.unifOI] Causalean.Stat.quantile (gapLaw M x k) := by
    filter_upwards [(ae_restrict_mem measurableSet_Ioo :
      ∀ᵐ t ∂Causalean.Stat.unifOI, t ∈ Ioo (0 : ℝ) 1)] with t ht
    exact (hq k hk hab).2 t ht
  change ((gapUnif M x k).prod Causalean.Stat.unifOI).map
    ((Q x k) ∘ (fun a => randomizedRank M om x k a.1 a.2)) = _
  rw [← AEMeasurable.map_map_of_aemeasurable hQx.aemeasurable hR,
    (hr k hk hab).1, Measure.map_congr heq]
  exact Causalean.Stat.quantile_map_uniform _

-- @node: gap_attaining_upper_product_cost
/-- Under [the structural assumptions](hyp:h), with [a measurable target weight](hyp:hm)
and [a measurable outcome quantile extension agreeing with gap quantiles and staying in the outcome set](hyp:hQ),
[for almost every covariate value and every gap of positive length, the expected product of the weight and the outcome
assigned directly by its randomized rank equals the integral of the outcome and weight quantiles paired in the same order](goal). -/
lemma gap_attaining_upper_product_cost (h : StructuralAssumptions M)
    (om : X → ℝ → ℝ) (hm : TargetWeightMeasurable om)
    (Q : X → ℕ → ℝ → ℝ) (hQ : RankKernelExtensionReading M Q) :
    ∀ᵐ x ∂xLaw M, ∀ k < (CondRangeDecomposition M x).count,
      (CondRangeDecomposition M x).gapLo k < (CondRangeDecomposition M x).gapHi k →
      (∫ a, Q x k (randomizedRank M om x k a.1 a.2) * om x a.1
        ∂(gapUnif M x k).prod Causalean.Stat.unifOI) =
      ∫ t in Ioo (0 : ℝ) 1, (gapQuantiles M om x k).1 t * (gapQuantiles M om x k).2 t := by
  filter_upwards [randomized_rank_uniform M h om hm, hQ.2] with x hr hq
  intro k hk hab
  let R := fun a : ℝ × ℝ => randomizedRank M om x k a.1 a.2
  let rho := (gapUnif M x k).prod Causalean.Stat.unifOI
  have hR : AEMeasurable R rho := gap_rank_aemeasurable M om hm x k hk hab
  have hmap : rho.map R = Causalean.Stat.unifOI := (hr k hk hab).1
  have hQx : Measurable (Q x k) :=
    hQ.1.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  let f := fun t : ℝ => Q x k t * Causalean.Stat.quantile (weightLaw M om x k) t
  have hf : AEMeasurable f Causalean.Stat.unifOI :=
    hQx.aemeasurable.mul (Causalean.Stat.aemeasurable_quantile_unifOI _)
  have hfmap : AEStronglyMeasurable f (rho.map R) := by
    rw [hmap]
    exact hf.aestronglyMeasurable
  calc
    _ = ∫ a, f (R a) ∂rho := by
      apply integral_congr_ae
      filter_upwards [(hr k hk hab).2] with a ha
      exact congrArg (fun v => Q x k (R a) * v) ha
    _ = ∫ t, f t ∂rho.map R := (integral_map hR hfmap).symm
    _ = ∫ t, f t ∂Causalean.Stat.unifOI := by rw [hmap]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [(ae_restrict_mem measurableSet_Ioo :
        ∀ᵐ t ∂Causalean.Stat.unifOI, t ∈ Ioo (0 : ℝ) 1)] with t ht
      have ht0 : t ≠ 0 := ne_of_gt ht.1
      have ht1 : t ≠ 1 := ne_of_lt ht.2
      simp only [f, gapQuantiles, endpointGapQuantile, if_neg ht0, if_neg ht1]
      rw [(hq k hk hab).2 t ht]

-- @node: gap_weight_integrable
/-- If [the target weight is integrable over the covariate distribution and unit-interval ranks](hyp:hi),
then [for almost every covariate value, it is integrable under the uniform law on every gap of positive length in the conditional decomposition](goal). -/
lemma gap_weight_integrable (om : X → ℝ → ℝ) (hi : TargetWeightIntegrable M om) :
    ∀ᵐ x ∂xLaw M, ∀ k < (CondRangeDecomposition M x).count,
      (CondRangeDecomposition M x).gapLo k < (CondRangeDecomposition M x).gapHi k →
      Integrable (om x) (gapUnif M x k) := by
  haveI : IsProbabilityMeasure (xLaw M) := Measure.isProbabilityMeasure_map M.measX.aemeasurable
  filter_upwards [Integrable.prod_right_ae hi] with x hx
  intro k hk hab
  have he := conditional_gap_endpoints M x k hk
  have hs : Ioo ((CondRangeDecomposition M x).gapLo k)
      ((CondRangeDecomposition M x).gapHi k) ⊆ Icc (0 : ℝ) 1 := by
    intro u hu
    exact ⟨he.1.1.trans hu.1.le, hu.2.le.trans he.2.2⟩
  have hg : Integrable (om x) (volume.restrict
      (Ioo ((CondRangeDecomposition M x).gapLo k) ((CondRangeDecomposition M x).gapHi k))) :=
    Integrable.mono_measure hx (Measure.restrict_mono_set volume hs)
  apply hg.smul_measure
  exact ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr (sub_pos.mpr hab))

-- @node: gap_attaining_product_integrable
/-- Under [the structural assumptions](hyp:h) and [known outcome endpoints](hyp:he), suppose
[the target weight is measurable](hyp:hm), [it is integrable over covariates and unit-interval ranks](hyp:hi),
and [the measurable outcome quantile extension agrees with gap quantiles and stays in the outcome set](hyp:hQ).
Then [for almost every covariate value and every gap of positive length, the product of the assigned outcome and weight
is integrable under independent uniform gap and unit-interval draws, for either the direct or reflected rank assignment](goal). -/
lemma gap_attaining_product_integrable (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) (om : X → ℝ → ℝ)
    (hm : TargetWeightMeasurable om) (hi : TargetWeightIntegrable M om)
    (Q : X → ℕ → ℝ → ℝ) (hQ : RankKernelExtensionReading M Q) (upper : Bool) :
    ∀ᵐ x ∂xLaw M, ∀ k < (CondRangeDecomposition M x).count,
      (CondRangeDecomposition M x).gapLo k < (CondRangeDecomposition M x).gapHi k →
      Integrable (fun a => Q x k (if upper then randomizedRank M om x k a.1 a.2
        else 1 - randomizedRank M om x k a.1 a.2) * om x a.1)
        ((gapUnif M x k).prod Causalean.Stat.unifOI) := by
  filter_upwards [gap_weight_integrable M om hi, randomized_rank_uniform M h om hm,
    hQ.2] with x hw hr hq
  intro k hk hab
  let rho := (gapUnif M x k).prod Causalean.Stat.unifOI
  let R := fun a : ℝ × ℝ => randomizedRank M om x k a.1 a.2
  let T := fun a => if upper then R a else 1 - R a
  haveI : IsProbabilityMeasure (gapUnif M x k) := uniformInterval_isProbability _ _ hab
  have hR : AEMeasurable R rho := gap_rank_aemeasurable M om hm x k hk hab
  have hT : AEMeasurable T rho := by
    cases upper <;> dsimp [T] <;> fun_prop
  have hQx : Measurable (Q x k) :=
    hQ.1.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have hmem : ∀ᵐ a ∂rho, R a ∈ Ioo (0 : ℝ) 1 := by
    apply ae_of_ae_map hR
    rw [(hr k hk hab).1]
    exact ae_restrict_mem measurableSet_Ioo
  have hb : ∀ᵐ a ∂rho, ‖Q x k (T a)‖ ≤ outcomeMagnitude M := by
    filter_upwards [hmem] with a ha
    apply outcome_norm_le_magnitude M he
    apply (hq k hk hab).1
    cases upper <;> dsimp [T] <;> constructor <;> linarith [ha.1, ha.2]
  exact (Integrable.comp_fst (hw k hk hab) Causalean.Stat.unifOI).bdd_mul
    (hQx.comp_aemeasurable hT).aestronglyMeasurable hb

-- @node: gap_attaining_mean
/-- Given [a measurable outcome quantile extension that agrees with gap quantiles and stays in the outcome set](hyp:hQ),
[the mean of the attaining outcome law at any covariate value, gap index, and rank equals the average of the extension
evaluated at one minus the randomized weight rank over a uniform unit-interval randomizer](goal). -/
lemma gap_attaining_mean (om : X → ℝ → ℝ)
    (Q : X → ℕ → ℝ → ℝ) (hQ : RankKernelExtensionReading M Q)
    (x : X) (k : ℕ) (u : ℝ) :
    (∫ y, y ∂gapAttainingLaw M om Q x k u) =
      ∫ s, Q x k (1 - randomizedRank M om x k u s) ∂Causalean.Stat.unifOI := by
  have hQx : Measurable (Q x k) :=
    hQ.1.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have hR : Measurable (fun s => randomizedRank M om x k u s) := by
    unfold randomizedRank
    fun_prop
  have hf : Measurable (fun s => Q x k (1 - randomizedRank M om x k u s)) := by
    fun_prop
  exact integral_map hf.aemeasurable measurable_id.aestronglyMeasurable

-- @node: gap_attaining_mean_integrable
/-- Under [the structural assumptions](hyp:h) and [known outcome endpoints](hyp:he), with
[a measurable target weight](hyp:hm), [integrability of that weight over covariates and unit-interval ranks](hyp:hi),
and [a measurable outcome quantile extension agreeing with gap quantiles and staying in the outcome set](hyp:hQ),
[for almost every covariate value and every gap of positive length, the attaining conditional mean times the weight
is integrable under the uniform law on the gap](goal). -/
lemma gap_attaining_mean_integrable (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) (om : X → ℝ → ℝ)
    (hm : TargetWeightMeasurable om) (hi : TargetWeightIntegrable M om)
    (Q : X → ℕ → ℝ → ℝ) (hQ : RankKernelExtensionReading M Q) :
    ∀ᵐ x ∂xLaw M, ∀ k < (CondRangeDecomposition M x).count,
      (CondRangeDecomposition M x).gapLo k < (CondRangeDecomposition M x).gapHi k →
      Integrable (fun u => (∫ y, y ∂gapAttainingLaw M om Q x k u) * om x u)
        (gapUnif M x k) := by
  filter_upwards [gap_attaining_product_integrable M h he om hm hi Q hQ false] with x hx
  intro k hk hab
  have hp := (hx k hk hab).integral_prod_left
  simpa only [Bool.false_eq_true, ↓reduceIte, integral_mul_const,
    gap_attaining_mean M om Q hQ] using hp

-- @node: gap_attaining_cost
/-- Under [the structural assumptions](hyp:h) and [known outcome endpoints](hyp:he), suppose
[the target weight is measurable](hyp:hm), [it is integrable over covariates and unit-interval ranks](hyp:hi),
and [the measurable outcome quantile extension agrees with gap quantiles and stays in the outcome set](hyp:hQ).
Then [for almost every covariate value and every gap of positive length, the uniform-gap average of the attaining
conditional mean times the weight equals the integral of outcome and weight quantiles paired in opposite orders](goal). -/
lemma gap_attaining_cost (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) (om : X → ℝ → ℝ)
    (hm : TargetWeightMeasurable om) (hi : TargetWeightIntegrable M om)
    (Q : X → ℕ → ℝ → ℝ) (hQ : RankKernelExtensionReading M Q) :
    ∀ᵐ x ∂xLaw M, ∀ k < (CondRangeDecomposition M x).count,
      (CondRangeDecomposition M x).gapLo k < (CondRangeDecomposition M x).gapHi k →
      (∫ u, (∫ y, y ∂gapAttainingLaw M om Q x k u) * om x u ∂gapUnif M x k) =
      ∫ t in Ioo (0 : ℝ) 1, (gapQuantiles M om x k).1 t *
        (gapQuantiles M om x k).2 (1 - t) := by
  filter_upwards [gap_attaining_product_integrable M h he om hm hi Q hQ false,
    gap_attaining_product_cost M h om hm Q hQ] with x hi hc
  intro k hk hab
  haveI : IsProbabilityMeasure (gapUnif M x k) := uniformInterval_isProbability _ _ hab
  have hp := integral_prod _ (hi k hk hab)
  simp only [Bool.false_eq_true, ↓reduceIte, integral_mul_const,
    ← gap_attaining_mean M om Q hQ] at hp
  exact hp.symm.trans (hc k hk hab)


-- @node: uniformInterval_scaled
/-- If [the lower endpoint is strictly below the upper endpoint](hyp:hab), then
[multiplying the uniform probability measure on the open interval by its length gives Lebesgue measure restricted to that interval](goal). -/
lemma uniformInterval_scaled (a b : ℝ) (hab : a < b) :
    ENNReal.ofReal (b - a) • uniformInterval a b = volume.restrict (Ioo a b) := by
  unfold uniformInterval
  rw [smul_smul, ENNReal.mul_inv_cancel
    (ENNReal.ofReal_ne_zero_iff.mpr (sub_pos.mpr hab)) ENNReal.ofReal_ne_top, one_smul]

-- @node: gap_attaining_canonical_increment
/-- Under [the structural assumptions](hyp:h), [continuity of propensity on instrument components](hyp:hc),
and [finitely many instrument components](hyp:hfin), with [a measurable target weight](hyp:hm)
and [a measurable outcome quantile extension agreeing with gap quantiles and staying in the outcome set](hyp:hQ),
[for almost every covariate value and every gap of positive length, integrating the attaining outcome law against Lebesgue
measure on the gap gives the difference between the canonical treated-outcome submeasures at the upper and lower gap endpoints](goal). -/
lemma gap_attaining_canonical_increment (h : StructuralAssumptions M)
    (hc : PropensityContinuousOnComponents M) (hfin : FiniteInstrumentComponents Z)
    (om : X → ℝ → ℝ) (hm : TargetWeightMeasurable om)
    (Q : X → ℕ → ℝ → ℝ) (hQ : RankKernelExtensionReading M Q) :
    ∀ᵐ x ∂xLaw M, ∀ k < (CondRangeDecomposition M x).count,
      (CondRangeDecomposition M x).gapLo k < (CondRangeDecomposition M x).gapHi k →
      (volume.restrict (RangeDecomposition.gap (CondRangeDecomposition M x) k)).bind
        (gapAttainingLaw M om Q x k) =
      canonSubmeasure M true x ((CondRangeDecomposition M x).gapHi k) -
        canonSubmeasure M true x ((CondRangeDecomposition M x).gapLo k) := by
  filter_upwards [gap_attaining_marginal M h hc hfin om hm Q hQ] with x hx
  intro k hk hab
  have hscale := uniformInterval_scaled
    ((CondRangeDecomposition M x).gapLo k) ((CondRangeDecomposition M x).gapHi k) hab
  change ENNReal.ofReal (_ - _) • gapUnif M x k = _ at hscale
  rw [conditional_gap_eq_Ioo M x k hk]
  change (volume.restrict (Ioo _ _)).bind _ = _
  rw [← hscale, Measure.bind_smul, hx k hk hab, gapLaw, if_pos hab,
    smul_smul, ENNReal.mul_inv_cancel
      (ENNReal.ofReal_ne_zero_iff.mpr (sub_pos.mpr hab)) ENNReal.ofReal_ne_top, one_smul]

-- @node: gap_attaining_region_integrable
/-- Under [the structural assumptions](hyp:h) and [known outcome endpoints](hyp:he), suppose
[the target weight is measurable](hyp:hm), [it is integrable over covariates and unit-interval ranks](hyp:hi),
and [the measurable outcome quantile extension agrees with gap quantiles and stays in the outcome set](hyp:hQ).
Then [for almost every covariate value and every gap of positive length, the attaining conditional mean times the weight
is integrable with respect to Lebesgue measure on the gap region](goal). -/
lemma gap_attaining_region_integrable (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) (om : X → ℝ → ℝ)
    (hm : TargetWeightMeasurable om) (hi : TargetWeightIntegrable M om)
    (Q : X → ℕ → ℝ → ℝ) (hQ : RankKernelExtensionReading M Q) :
    ∀ᵐ x ∂xLaw M, ∀ k < (CondRangeDecomposition M x).count,
      (CondRangeDecomposition M x).gapLo k < (CondRangeDecomposition M x).gapHi k →
      Integrable (fun u => (∫ y, y ∂gapAttainingLaw M om Q x k u) * om x u)
        (volume.restrict (RangeDecomposition.gap (CondRangeDecomposition M x) k)) := by
  filter_upwards [gap_attaining_mean_integrable M h he om hm hi Q hQ] with x hx
  intro k hk hab
  have hscale := uniformInterval_scaled
    ((CondRangeDecomposition M x).gapLo k) ((CondRangeDecomposition M x).gapHi k) hab
  change ENNReal.ofReal (_ - _) • gapUnif M x k = _ at hscale
  rw [conditional_gap_eq_Ioo M x k hk]
  change Integrable _ (volume.restrict (Ioo _ _))
  rw [← hscale]
  exact (hx k hk hab).smul_measure ENNReal.ofReal_ne_top

-- @node: gap_attaining_region_cost
/-- Under [the structural assumptions](hyp:h) and [known outcome endpoints](hyp:he), with
[a measurable target weight](hyp:hm), [integrability of that weight over covariates and unit-interval ranks](hyp:hi),
and [a measurable outcome quantile extension agreeing with gap quantiles and staying in the outcome set](hyp:hQ),
[for almost every covariate value and every gap of positive length, the Lebesgue integral of the attaining conditional mean
times the weight on the gap equals its nonnegative length times the integral of outcome and weight quantiles paired in opposite orders](goal). -/
lemma gap_attaining_region_cost (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) (om : X → ℝ → ℝ)
    (hm : TargetWeightMeasurable om) (hi : TargetWeightIntegrable M om)
    (Q : X → ℕ → ℝ → ℝ) (hQ : RankKernelExtensionReading M Q) :
    ∀ᵐ x ∂xLaw M, ∀ k < (CondRangeDecomposition M x).count,
      (CondRangeDecomposition M x).gapLo k < (CondRangeDecomposition M x).gapHi k →
      (∫ u in RangeDecomposition.gap (CondRangeDecomposition M x) k,
        (∫ y, y ∂gapAttainingLaw M om Q x k u) * om x u) =
      max 0 ((CondRangeDecomposition M x).gapHi k - (CondRangeDecomposition M x).gapLo k) *
        ∫ t in Ioo (0 : ℝ) 1, (gapQuantiles M om x k).1 t *
          (gapQuantiles M om x k).2 (1 - t) := by
  filter_upwards [gap_attaining_cost M h he om hm hi Q hQ] with x hx
  intro k hk hab
  have hscale := uniformInterval_scaled
    ((CondRangeDecomposition M x).gapLo k) ((CondRangeDecomposition M x).gapHi k) hab
  change ENNReal.ofReal (_ - _) • gapUnif M x k = _ at hscale
  rw [conditional_gap_eq_Ioo M x k hk]
  change (∫ u, _ ∂volume.restrict (Ioo _ _)) = _
  rw [← hscale, integral_smul_measure, ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le),
    smul_eq_mul, hx k hk hab, max_eq_right (sub_nonneg.mpr hab.le)]


-- @node: gap_attaining_law_isProbability
/-- Given [a measurable outcome quantile extension agreeing with gap quantiles and staying in the outcome set](hyp:hQ),
[the attaining outcome law is a probability measure at every covariate value, gap index, and rank](goal). -/
lemma gap_attaining_law_isProbability (om : X → ℝ → ℝ)
    (Q : X → ℕ → ℝ → ℝ) (hQ : RankKernelExtensionReading M Q)
    (x : X) (k : ℕ) (u : ℝ) : IsProbabilityMeasure (gapAttainingLaw M om Q x k u) := by
  have hQx : Measurable (Q x k) :=
    hQ.1.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have hR : Measurable (fun s => randomizedRank M om x k u s) := by
    unfold randomizedRank
    fun_prop
  have hf : Measurable (fun s => Q x k (1 - randomizedRank M om x k u s)) := by
    fun_prop
  exact Measure.isProbabilityMeasure_map hf.aemeasurable

-- @node: gap_attaining_law_supported
/-- Under [the structural assumptions](hyp:h), with [a measurable target weight](hyp:hm)
and [a measurable outcome quantile extension agreeing with gap quantiles and taking values in the outcome set](hyp:hQ),
[for almost every covariate value and every gap of positive length, the attaining outcome law assigns zero mass
outside the model's outcome set at every rank](goal). -/
lemma gap_attaining_law_supported (h : StructuralAssumptions M)
    (om : X → ℝ → ℝ) (hm : TargetWeightMeasurable om)
    (Q : X → ℕ → ℝ → ℝ) (hQ : RankKernelExtensionReading M Q) :
    ∀ᵐ x ∂xLaw M, ∀ k < (CondRangeDecomposition M x).count,
      (CondRangeDecomposition M x).gapLo k < (CondRangeDecomposition M x).gapHi k →
      ∀ u, gapAttainingLaw M om Q x k u M.Ysetᶜ = 0 := by
  filter_upwards [hQ.2] with x hq
  intro k hk hab u
  haveI : IsProbabilityMeasure (gapUnif M x k) := uniformInterval_isProbability _ _ hab
  haveI : IsProbabilityMeasure (weightLaw M om x k) :=
    Measure.isProbabilityMeasure_map (gap_weight_aemeasurable M om hm x k hk)
  have hQx : Measurable (Q x k) :=
    hQ.1.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have hR : Measurable (fun s => randomizedRank M om x k u s) := by
    unfold randomizedRank
    fun_prop
  have hf : Measurable (fun s => Q x k (1 - randomizedRank M om x k u s)) := by
    fun_prop
  rw [gapAttainingLaw, Measure.map_apply hf h.2.2.2.2.2.2.1.measurableSet.compl,
    measure_eq_zero_iff_ae_notMem]
  filter_upwards [(ae_restrict_mem measurableSet_Ioo :
    ∀ᵐ s ∂Causalean.Stat.unifOI, s ∈ Ioo (0 : ℝ) 1)] with s hs
  have hb := DistributionalTransform.rank_bounds (weightLaw M om x k) (om x u) s
    ⟨hs.1.le, hs.2.le⟩
  have hlo : 0 ≤ DistributionalTransform.leftCDF (weightLaw M om x k) (om x u) :=
    measureReal_nonneg
  have hhi := cdf_le_one (weightLaw M om x k) (om x u)
  have hr : randomizedRank M om x k u s ∈ Icc (0 : ℝ) 1 := by
    simpa only [DistributionalTransform.rank, DistributionalTransform.leftCDF,
      cdf_eq_real, measureReal_def, randomizedRank, weightCDF, weightCDFLeft, mem_Icc] using
      And.intro (hlo.trans hb.1) (hb.2.trans hhi)
  have hy := (hq k hk hab).1 (1 - randomizedRank M om x k u s)
    ⟨by linarith [hr.2], by linarith [hr.1]⟩
  exact fun hn => hn hy

end Papers.TbsPrteOptimalTransport

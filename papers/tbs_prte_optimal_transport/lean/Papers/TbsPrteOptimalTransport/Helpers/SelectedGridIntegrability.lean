module
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousLearners
public import Papers.TbsPrteOptimalTransport.Helpers.PluginPopulationRegularity
/-! Measurable selected-law versions and integrable weighted grid errors. -/
@[expose] public section
set_option linter.mathlibStandardSet false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set
open scoped Classical ENNReal

/-- Given [a probability kernel for the original observations](hyp:K), [a fallback
probability kernel on outcomes](hyp:B), [a parameter-dependent selection set](hyp:E)
that [is measurable](hyp:hE), and [an outcome map](hyp:f) that [is measurable](hyp:hf),
the [normalized selection kernel](goal) first [restricts the original law to
selected observations at each parameter](step:1), then [uses the fallback law
when the selected mass is zero and otherwise maps the selected law to outcomes
and divides by its mass](step:2). -/
-- @node: normalized_selection_kernel
noncomputable def normalized_selection_kernel {T V : Type*}
    [MeasurableSpace T] [MeasurableSpace V]
    (K : Kernel T V) [IsMarkovKernel K] (B : Kernel T ℝ) [IsMarkovKernel B]
    (E : Set (T × V)) (hE : MeasurableSet E) (f : V → ℝ) (hf : Measurable f) :
    Kernel T ℝ where
  toFun t :=
    let ν := (K t).restrict {v | (t, v) ∈ E}
    if ν univ = 0 then B t else (ν univ)⁻¹ • ν.map f
  measurable' := by
    classical
    apply Measure.measurable_of_measurable_coe
    intro D hD
    have hm (D : Set ℝ) (hD : MeasurableSet D) :
        Measurable (fun t => ((K t).restrict {v | (t, v) ∈ E}).map f D) := by
      have hi : Measurable (fun tv : T × V =>
          if tv ∈ E ∧ f tv.2 ∈ D then (1 : ℝ≥0∞) else 0) := by
        apply Measurable.ite
        · exact hE.inter (hD.preimage (hf.comp measurable_snd))
        · fun_prop
        · fun_prop
      convert hi.lintegral_kernel_prod_right' (κ := K) using 1
      funext t
      rw [Measure.map_apply hf hD, Measure.restrict_apply (hD.preimage hf)]
      rw [← lintegral_indicator_one ((hD.preimage hf).inter
        (show MeasurableSet {v | (t, v) ∈ E} from
          hE.preimage (measurable_const.prodMk measurable_id)))]
      apply lintegral_congr
      intro v
      simp only [indicator_apply, mem_inter_iff, mem_preimage, mem_setOf_eq]
      split_ifs <;> simp_all
    have hmass : Measurable (fun t => (K t).restrict {v | (t, v) ∈ E} univ) := by
      simpa only [Measure.map_apply hf MeasurableSet.univ, preimage_univ] using
        hm univ MeasurableSet.univ
    convert Measurable.ite (hmass (measurableSet_singleton 0))
      (B.measurable_coe hD) (hmass.inv.mul (hm D hD)) using 1
    funext t
    simp only [mem_singleton_iff, Pi.mul_apply, Pi.inv_apply]
    split_ifs <;> simp only [Measure.smul_apply, smul_eq_mul]
    all_goals infer_instance

-- @node: normalized_selection_kernel_markov
/-- Given probability kernels for observations and fallback outcomes, [a measurable
parameter-dependent selection set](hyp:hE), and [a measurable outcome map](hyp:hf),
[normalizing the selected outcome law, with the fallback used at zero selected
mass, yields a probability kernel](goal). -/
lemma normalized_selection_kernel_markov {T V : Type*}
    [MeasurableSpace T] [MeasurableSpace V]
    (K : Kernel T V) [IsMarkovKernel K] (B : Kernel T ℝ) [IsMarkovKernel B]
    (E : Set (T × V)) (hE : MeasurableSet E) (f : V → ℝ) (hf : Measurable f) :
    IsMarkovKernel (normalized_selection_kernel K B E hE f hf) := by
  classical
  constructor
  intro t
  constructor
  change (if ((K t).restrict {v | (t, v) ∈ E}) univ = 0 then B t
    else (((K t).restrict {v | (t, v) ∈ E}) univ)⁻¹ •
      ((K t).restrict {v | (t, v) ∈ E}).map f) univ = 1
  split_ifs with hz
  · simp
  · rw [Measure.smul_apply, Measure.map_apply hf MeasurableSet.univ,
      preimage_univ, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hz (measure_ne_top _ _)

universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]

/-- Given [fallback probability laws supported on the outcome domain at each
covariate value](hyp:zeroLaw), [the model's structural assumptions](hyp:h),
[joint measurability in instrument and covariates of every fitted propensity](hyp:hp),
and [fitted propensities in the unit interval everywhere](hyp:hb), [for any
bandwidth sequence, sample index, and learner parameter, there exists a probability
kernel agreeing with the selected outcome law for almost every covariate value
at which the minimum true propensity is positive](goal). -/
-- @node: selected_law_markov_version
lemma selected_law_markov_version (M : LatentIVModel Ω X Z)
    (zeroLaw : X → {ν : ProbabilityMeasure ℝ // ν.toMeasure M.Ysetᶜ = 0})
    (h : StructuralAssumptions M)
    (pHat : ℕ → A → Z → X → ℝ)
    (hp : ∀ n a, Measurable (Function.uncurry (pHat n a)))
    (hb : ∀ n a z x, pHat n a z x ∈ Icc (0 : ℝ) 1)
    (delta : ℕ → ℝ) (n : ℕ) (a : A) :
    ∃ K : Kernel X ℝ, IsMarkovKernel K ∧
      ∀ᵐ x ∂xLaw M, 0 < pLow M.prop x →
        K x = selLaw M zeroLaw pHat delta n a x := by
  haveI : IsProbabilityMeasure (xLaw M) :=
    Measure.isProbabilityMeasure_map M.measX.aemeasurable
  have hl := (propensity_endpoints_aemeasurable (xLaw M) id measurable_id
    M.prop h.2.2.2.1.2.1 M.rangeProp).1
  have hf := (propensity_endpoints_aemeasurable (xLaw M) id measurable_id
    (pHat n a) (hp n a) (hb n a)).1
  change AEMeasurable (pLow M.prop) (xLaw M) at hl
  change AEMeasurable (pLow (pHat n a)) (xLaw M) at hf
  let b := hl.mk (pLow M.prop)
  let c := hf.mk (pLow (pHat n a))
  let B := canonical_boundary_kernel M b hl.measurable_mk
  letI : IsMarkovKernel B := canonical_boundary_kernel_markov M b hl.measurable_mk
  let J := condDistrib (fun s => (M.Y s, M.W s, M.Zv s)) M.Xv M.law.toMeasure
  let E : Set (X × (ℝ × ℝ × Z)) :=
    {xo | xo.2.2.1 = 1 ∧ pHat n a xo.2.2.2 xo.1 ≤ c xo.1 + delta n}
  have hE : MeasurableSet E := by
    change MeasurableSet ({xo : X × (ℝ × ℝ × Z) | xo.2.2.1 = 1} ∩
      {xo | pHat n a xo.2.2.2 xo.1 ≤ c xo.1 + delta n})
    apply MeasurableSet.inter
    · exact measurableSet_eq_fun (show Measurable (fun xo : X × (ℝ × ℝ × Z) => xo.2.2.1) by fun_prop) measurable_const
    · exact measurableSet_le ((hp n a).comp (show Measurable (fun xo : X × (ℝ × ℝ × Z) => (xo.2.2.2, xo.1)) by fun_prop))
        ((hf.measurable_mk.comp measurable_fst).add_const _)
  let K := normalized_selection_kernel J B E hE Prod.fst measurable_fst
  refine ⟨K, normalized_selection_kernel_markov J B E hE Prod.fst measurable_fst, ?_⟩
  filter_upwards [hl.ae_eq_mk, hf.ae_eq_mk] with x hx hc
  intro hpos
  have hB : B x = boundaryLaw M zeroLaw x := by
    change (if 0 < b x then _ else _) = _
    dsimp only [b]
    simp only [← hx, if_pos hpos, boundaryLaw]
  change (if ((J x).restrict {o | (x, o) ∈ E}) univ = 0 then B x
    else (((J x).restrict {o | (x, o) ∈ E}) univ)⁻¹ •
      ((J x).restrict {o | (x, o) ∈ E}).map Prod.fst) = _
  have hset : {o | (x, o) ∈ E} =
      {o | o.2.1 = 1 ∧ pHat n a o.2.2 x ≤ pLow (pHat n a) x + delta n} := by
    ext o
    change (o.2.1 = 1 ∧ pHat n a o.2.2 x ≤ c x + delta n) ↔ _
    dsimp only [c]
    rw [← hc]
    rfl
  rw [hset, hB]
  rfl

/-- Given [fallback probability laws supported on the outcome domain at each
covariate value](hyp:zeroLaw), [the model's structural assumptions](hyp:h),
[known lower and upper endpoints of the outcome domain](hyp:he), [fitted
propensities jointly measurable in learner parameter, instrument, and covariates
at every sample index](hyp:hp), [fitted propensities in the unit interval
everywhere](hyp:hb), [a quantile index strictly between zero and one](hyp:ht), and
[an almost everywhere measurable clipped grid value](hyp:hr), [the absolute
error between that clipped grid value and the selected outcome quantile,
multiplied by the minimum true propensity, is integrable under the covariate law](goal). -/
-- @node: selected_grid_error_integrable
lemma selected_grid_error_integrable (M : LatentIVModel Ω X Z)
    (zeroLaw : X → {ν : ProbabilityMeasure ℝ // ν.toMeasure M.Ysetᶜ = 0})
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (pHat : ℕ → A → Z → X → ℝ)
    (hp : ∀ n, Measurable (fun ax : A × Z × X => pHat n ax.1 ax.2.1 ax.2.2))
    (hb : ∀ n a z x, pHat n a z x ∈ Icc (0 : ℝ) 1)
    (delta : ℕ → ℝ) (raw : ℕ → A → ℕ → X → ℝ)
    (n : ℕ) (a : A) (m : ℕ) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hr : AEMeasurable (clippedGrid M raw n a m) (xLaw M)) :
    Integrable (fun x => pLow M.prop x *
      |clippedGrid M raw n a m x - selQuantile M zeroLaw pHat delta n a x t|)
      (xLaw M) := by
  haveI : IsProbabilityMeasure (xLaw M) :=
    Measure.isProbabilityMeasure_map M.measX.aemeasurable
  have hp' (n : ℕ) (a : A) : Measurable (Function.uncurry (pHat n a)) := by
    change Measurable (fun zx : Z × X => pHat n a zx.1 zx.2)
    simpa only [Function.comp_def, id_eq] using
      (hp n).comp (measurable_const.prodMk measurable_id)
  obtain ⟨K, hK, heq⟩ := selected_law_markov_version M zeroLaw h pHat hp' hb delta n a
  letI : IsMarkovKernel K := hK
  have hq : Measurable (fun x => Causalean.Stat.quantile (K x) t) := by
    first
    | fun_prop
    | exact (measurable_markov_quantile_interior K).comp
        (measurable_id.prodMk (measurable_const (a := (⟨t, ht⟩ : Ioo (0 : ℝ) 1))))
  have hl := (propensity_endpoints_aemeasurable (xLaw M) id measurable_id
    M.prop h.2.2.2.1.2.1 M.rangeProp).1
  have hm : AEMeasurable (fun x => pLow M.prop x *
      |clippedGrid M raw n a m x - Causalean.Stat.quantile (K x) t|) (xLaw M) := by
    first
    | fun_prop
    | exact hl.mul (hr.sub hq.aemeasurable).norm
  have htrue : (fun x => pLow M.prop x *
      |clippedGrid M raw n a m x - Causalean.Stat.quantile (K x) t|) =ᵐ[xLaw M]
      (fun x => pLow M.prop x *
      |clippedGrid M raw n a m x - selQuantile M zeroLaw pHat delta n a x t|) := by
    filter_upwards [heq] with x hx
    by_cases hpos : 0 < pLow M.prop x
    · rw [hx hpos]; rfl
    · have hz : pLow M.prop x = 0 := le_antisymm (le_of_not_gt hpos)
        (population_support_endpoints M x).1.1
      rw [hz, zero_mul, zero_mul]
  apply Integrable.of_bound (hm.congr htrue).aestronglyMeasurable (M.yMax - M.yMin)
  filter_upwards [selected_quantile_supported M zeroLaw h he pHat delta hp n a] with x hx
  have hs := hx t ht
  have hc : clippedGrid M raw n a m x ∈ Icc M.yMin M.yMax :=
    ⟨le_min (he.1.2 he.2.1) (le_max_left _ _), min_le_left _ _⟩
  have hd : |clippedGrid M raw n a m x - selQuantile M zeroLaw pHat delta n a x t| ≤
      M.yMax - M.yMin := by
    apply abs_le.mpr
    constructor <;> linarith [he.1.2 hs, he.2.2 hs, hc.1, hc.2]
  have hw := (population_support_endpoints M x).1
  rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg hw.1]
  exact (mul_le_mul_of_nonneg_left hd hw.1).trans
    (mul_le_of_le_one_left (sub_nonneg.mpr (he.1.2 he.2.1)) hw.2)

end Papers.TbsPrteOptimalTransport

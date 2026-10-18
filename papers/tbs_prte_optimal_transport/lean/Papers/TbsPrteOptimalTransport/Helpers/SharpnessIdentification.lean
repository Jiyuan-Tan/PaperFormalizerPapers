module
public import Papers.TbsPrteOptimalTransport.Helpers.Canonical
public import Papers.TbsPrteOptimalTransport.Helpers.SharpnessExogeneity
/-! Identification of observable response laws from the two selection constraints. -/
public section
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.unusedVariables false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z]
variable (M : LatentIVModel Ω X Z)

-- @node: sharpness_exogenous_latent_given_instrument
/-- Under [instrument exogeneity](hyp:h), [the conditional joint law of resistance
and both potential outcomes given instrument and covariates equals their
conditional law given covariates alone, almost everywhere under the
instrument–covariate law](goal). -/
lemma sharpness_exogenous_latent_given_instrument (h : InstrumentExogeneity M)
    :
    condDistrib (fun s => (M.U s, M.Y0 s, M.Y1 s))
      (fun s => (M.Zv s, M.Xv s)) M.law.toMeasure
      =ᵐ[M.law.toMeasure.map (fun s => (M.Zv s, M.Xv s))]
        fun px : Z × X =>
          condDistrib (fun s => (M.U s, M.Y0 s, M.Y1 s)) M.Xv M.law.toMeasure px.2 := by
  let V := fun s => (M.U s, M.Y0 s, M.Y1 s)
  have hV : Measurable V := by
    first | fun_prop | exact M.measU.prodMk (M.measY0.prodMk M.measY1)
  have hZX : Measurable (fun s => (M.Zv s, M.Xv s)) := by
    first | fun_prop | exact M.measZ.prodMk M.measX
  have hPX : Measurable (fun s => (M.Zv s, M.Xv s)) := by
    first | fun_prop | exact M.measZ.prodMk M.measX
  haveI := M.instKernel_markov
  change _ =ᵐ[_] ((condDistrib V M.Xv M.law.toMeasure).comap
    (mγ := inferInstance) (Prod.snd : Z × X → X) measurable_snd)
  apply condDistrib_ae_eq_of_measure_eq_compProd _ hV.aemeasurable
  have hj : M.law.toMeasure.map (fun s => (M.Xv s, (M.Zv s, V s))) =
      (xLaw M) ⊗ₘ (M.instKernel.prod (condDistrib V M.Xv M.law.toMeasure)) := by
    rw [← compProd_map_condDistrib (M.measZ.prodMk hV).aemeasurable]
    apply Measure.compProd_congr
    filter_upwards [h] with x hx
    exact hx.trans (Kernel.prod_apply _ _ x).symm
  have hi : (xLaw M) ⊗ₘ M.instKernel =
      M.law.toMeasure.map (fun s => (M.Xv s, M.Zv s)) := by
    change (M.law.toMeasure.map M.Xv) ⊗ₘ M.instKernel = _
    rw [Measure.compProd_congr M.instKernel_version, compProd_map_condDistrib M.measZ.aemeasurable]
  haveI : IsFiniteMeasure (xLaw M) := inferInstanceAs
    (IsFiniteMeasure (M.law.toMeasure.map M.Xv))
  haveI := M.instKernel_markov
  have he := factorized_kernel_statistic_joint (xLaw M) M.instKernel
    (condDistrib V M.Xv M.law.toMeasure) (fun z (_x : X) => z) (by fun_prop)
  rw [← hj, hi, Measure.map_map (by fun_prop) (M.measX.prodMk (M.measZ.prodMk hV)),
    Measure.map_map (by fun_prop) (M.measX.prodMk M.measZ)] at he
  exact he
-- @node: sharpness_threshold_instrument_response
/-- Under [consistency](hyp:hcon), [instrument exogeneity](hyp:hex), [a measurable
propensity](hyp:hp), and [treatment determined almost surely by whether resistance
is at most propensity](hyp:hsel), [the conditional law of observed outcome and
treatment given instrument and covariates is obtained from the conditional latent
law given covariates by selecting the treated outcome and treatment one below
the propensity threshold, and the untreated outcome and treatment zero above it,
almost everywhere under the instrument–covariate law](goal). -/
lemma sharpness_threshold_instrument_response (hcon : Consistency M) (hex : InstrumentExogeneity M)
    (hp : Measurable (Function.uncurry M.prop))
    (hsel : ∀ᵐ s ∂M.law.toMeasure,
      M.W s = if M.U s ≤ M.prop (M.Zv s) (M.Xv s) then 1 else 0) :
    condDistrib (fun s => (M.Y s, M.W s))
      (fun s => (M.Zv s, M.Xv s)) M.law.toMeasure
      =ᵐ[M.law.toMeasure.map (fun s => (M.Zv s, M.Xv s))]
        fun px => (condDistrib (fun s => (M.U s, M.Y0 s, M.Y1 s))
          M.Xv M.law.toMeasure px.2).map
          (fun v => (if v.1 ≤ M.prop px.1 px.2 then v.2.2 else v.2.1,
            if v.1 ≤ M.prop px.1 px.2 then (1 : ℝ) else 0)) := by
  let V := fun s => (M.U s, M.Y0 s, M.Y1 s)
  let P := M.Zv
  let F := fun (z : Z) (x : X) (v : ℝ × ℝ × ℝ) =>
    (if v.1 ≤ M.prop z x then v.2.2 else v.2.1, if v.1 ≤ M.prop z x then (1 : ℝ) else 0)
  have hV : Measurable V := by
    first | fun_prop | exact M.measU.prodMk (M.measY0.prodMk M.measY1)
  have hP : Measurable P := M.measZ
  have hF : Measurable (fun a : (Z × X) × (ℝ × ℝ × ℝ) =>
      F a.1.1 a.1.2 a.2) := by
    first | fun_prop | exact (
      (measurable_snd.snd.snd.ite
        (measurableSet_le measurable_snd.fst (hp.comp measurable_fst))
        measurable_snd.snd.fst).prodMk
      (measurable_const.ite (measurableSet_le measurable_snd.fst (hp.comp measurable_fst))
        measurable_const))
  have hCI := sharpness_exogenous_latent_given_instrument M hex
  have hresponse := condDistrib_map_of_condDistrib_fst_eq M.law.toMeasure
    (X := P) (Z := M.Xv) (C := V) (h := F) hP M.measX hV hF hCI
  have he : (fun s => (M.Y s, M.W s)) =ᵐ[M.law.toMeasure]
      (fun s => F (P s) (M.Xv s) (V s)) := by
    filter_upwards [hcon, hsel] with s hs ht
    dsimp only [F, P, V]
    rw [hs, ht]
    split_ifs <;> simp
  rw [condDistrib_congr_left he]
  exact hresponse

-- @node: sharpness_canonical_instrument_slice
/-- Under [consistency](hyp:hcon), [instrument exogeneity](hyp:hex), [uniform
resistance conditional on covariates](hyp:hu), [a measurable propensity](hyp:hpmeas),
and [the threshold treatment rule almost surely](hyp:hsel), [for either treatment
state the canonical outcome submeasure at the propensity threshold equals the
outcome marginal of the conditional response law restricted to that treatment
state, almost everywhere under the instrument–covariate law](goal). -/
lemma sharpness_canonical_instrument_slice (hcon : Consistency M) (hex : InstrumentExogeneity M)
    (hu : UniformResistance M) (hpmeas : Measurable (Function.uncurry M.prop))
    (hsel : ∀ᵐ s ∂M.law.toMeasure,
      M.W s = if M.U s ≤ M.prop (M.Zv s) (M.Xv s) then 1 else 0) (w : Bool) :
    ∀ᵐ px ∂M.law.toMeasure.map (fun s => (M.Zv s, M.Xv s)),
      canonSubmeasure M w px.2 (M.prop px.1 px.2) =
        ((condDistrib (fun s => (M.Y s, M.W s))
          (fun s => (M.Zv s, M.Xv s)) M.law.toMeasure px).restrict
          {a | a.2 = if w then 1 else 0}).map Prod.fst := by
  let V := fun s => (M.U s, M.Y0 s, M.Y1 s)
  let proj := fun v : ℝ × ℝ × ℝ => (v.1, if w then v.2.2 else v.2.1)
  have hV : Measurable V := by
    first | fun_prop | exact M.measU.prodMk (M.measY0.prodMk M.measY1)
  have hproj : Measurable proj := by
    first | fun_prop | cases w <;> simp only [proj, Bool.false_eq_true, ↓reduceIte] <;> fun_prop
  have hcomp := condDistrib_comp (μ := M.law.toMeasure) (mβ := inferInstance) M.Xv hV.aemeasurable hproj
  have hlatent := latent_conditional_uniform_disintegration M hu w
  have hjoint : ∀ᵐ x ∂xLaw M,
      (condDistrib V M.Xv M.law.toMeasure x).map proj =
        ((Kernel.const X Causalean.Stat.unifOI) ⊗ₖ
          ((outcomeKernel (latentMarginal M w)).comap
            (Prod.swap : X × ℝ → ℝ × X) measurable_swap)) x := by
    filter_upwards [hcomp, hlatent] with x hx hl
    have heproj : proj ∘ V = fun s => (M.U s, potential M w s) := by
      funext s
      cases w <;> rfl
    rw [heproj] at hx
    rw [Kernel.map_apply _ hproj] at hx
    exact hx.symm.trans hl
  have hPX : Measurable (fun s => (M.Zv s, M.Xv s)) := by
    exact M.measZ.prodMk M.measX
  have hmarg : (M.law.toMeasure.map
      (fun s => (M.Zv s, M.Xv s))).map Prod.snd = xLaw M := by
    rw [Measure.map_map measurable_snd hPX]
    rfl
  rw [← hmarg] at hjoint
  have hpull := ae_of_ae_map measurable_snd.aemeasurable hjoint
  have hprange : ∀ᵐ px ∂M.law.toMeasure.map
      (fun s => (M.Zv s, M.Xv s)), M.prop px.1 px.2 ∈ Icc (0 : ℝ) 1 := by
    apply (ae_map_iff hPX.aemeasurable (measurableSet_Icc.preimage hpmeas)).mpr
    exact Filter.Eventually.of_forall fun s => M.rangeProp _ _
  filter_upwards [sharpness_threshold_instrument_response M hcon hex hpmeas hsel, hpull, hprange]
    with px hobs hx hp
  haveI := outcomeKernel_isMarkov (latentMarginal M w)
  let K := outcomeKernel (latentMarginal M w)
  let F := fun v : ℝ × ℝ × ℝ =>
    (if v.1 ≤ (M.prop px.1 px.2) then v.2.2 else v.2.1, if v.1 ≤ (M.prop px.1 px.2) then (1 : ℝ) else 0)
  let E := fun (B : Set ℝ) => {uy : ℝ × ℝ |
    uy.2 ∈ B ∧ (if uy.1 ≤ (M.prop px.1 px.2) then (1 : ℝ) else 0) = (if w then 1 else 0)}
  have hF : Measurable F := by
    first | fun_prop | exact (
      (measurable_snd.snd.ite (measurableSet_le measurable_fst measurable_const)
        measurable_snd.fst).prodMk
      (measurable_const.ite (measurableSet_le measurable_fst measurable_const)
        measurable_const))
  ext B hB
  have hE : MeasurableSet (E B) := by
    exact (hB.preimage measurable_snd).inter
      (measurableSet_eq_fun
        (measurable_const.ite (measurableSet_le measurable_fst measurable_const)
          measurable_const) measurable_const)
  have heval : (((condDistrib (fun s => (M.Y s, M.W s))
      (fun s => (M.Zv s, M.Xv s)) M.law.toMeasure px).restrict
      {a | a.2 = if w then 1 else 0}).map Prod.fst) B =
      ((Kernel.const X Causalean.Stat.unifOI) ⊗ₖ
        (K.comap (Prod.swap : X × ℝ → ℝ × X) measurable_swap)) px.2 (E B) := by
    change ((condDistrib (fun s => (M.Y s, M.W s))
      (fun s => (M.Zv s, M.Xv s)) M.law.toMeasure px).restrict
      {a | a.2 = if w then 1 else 0}).map Prod.fst B = _
    rw [hobs, Measure.map_apply measurable_fst hB,
      Measure.restrict_apply (hB.preimage measurable_fst),
      Measure.map_apply hF ((hB.preimage measurable_fst).inter
        (measurableSet_eq_fun measurable_snd measurable_const)), ← hx,
      Measure.map_apply hproj hE]
    congr 1
    ext v
    cases w <;> by_cases hv : v.1 ≤ (M.prop px.1 px.2) <;>
      simp [F, proj, E, hv, and_comm]
  symm
  rw [heval, Kernel.compProd_apply hE]
  change (∫⁻ u, K (u, px.2) {y | (u, y) ∈ E B} ∂Causalean.Stat.unifOI) =
    canonSubmeasure M w px.2 (M.prop px.1 px.2) B
  have hsel : MeasurableSet (selRegion w (M.prop px.1 px.2)) := by
    cases w <;> simp only [selRegion, Bool.false_eq_true, ↓reduceIte] <;>
      exact measurableSet_Ioc
  have hrestrict : Causalean.Stat.unifOI.restrict (selRegion w (M.prop px.1 px.2)) =
      volume.restrict (selRegion w (M.prop px.1 px.2)) := by
    rw [Causalean.Stat.unifOI, Measure.restrict_restrict hsel]
    apply Measure.restrict_congr_set
    filter_upwards [volume.ae_ne (1 : ℝ)] with u hu
    apply propext
    cases w <;> simp only [selRegion, Bool.false_eq_true, ↓reduceIte,
      mem_inter_iff, mem_Ioc, mem_Ioo]
    · constructor
      · exact fun h => h.1
      · intro h
        exact ⟨h, hp.1.trans_lt h.1, lt_of_le_of_ne h.2 hu⟩
    · constructor
      · exact fun h => h.1
      · intro h
        exact ⟨h, h.1, lt_of_le_of_ne (h.2.trans hp.2) hu⟩
  calc
    _ = ∫⁻ u, (selRegion w (M.prop px.1 px.2)).indicator (fun u => K (u, px.2) B) u
        ∂Causalean.Stat.unifOI := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
      have hset : {y | (u, y) ∈ E B} =
          if u ∈ selRegion w (M.prop px.1 px.2) then B else ∅ := by
        ext y
        cases w <;> by_cases ht : u ≤ (M.prop px.1 px.2) <;>
          simp [E, selRegion, ht, hu.1, hu.2.le, not_lt, not_le, and_comm]
      rw [hset]
      by_cases ht : u ∈ selRegion w (M.prop px.1 px.2) <;> simp [ht]
    _ = ∫⁻ u, K (u, px.2) B ∂volume.restrict (selRegion w (M.prop px.1 px.2)) := by
      rw [lintegral_indicator hsel, hrestrict]
    _ = _ := by
      rw [canonSubmeasure, Measure.bind_apply hB (by fun_prop)]
-- @node: sharpness_response_slice_reconstruction
/-- For a joint measure of outcome and treatment and a fixed treatment value,
[restricting to that treatment value, taking the outcome marginal, and restoring
the fixed treatment coordinate recovers the restricted joint measure](goal). -/
lemma sharpness_response_slice_reconstruction (ν : Measure (ℝ × ℝ)) (w : ℝ) :
    ((ν.restrict {a | a.2 = w}).map Prod.fst).map (fun y => (y, w)) =
      ν.restrict {a | a.2 = w} := by
  rw [Measure.map_map (by fun_prop) measurable_fst]
  calc
    _ = (ν.restrict {a | a.2 = w}).map id := by
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem (measurableSet_eq_fun measurable_snd measurable_const)]
        with a ha
      exact Prod.ext rfl ha.symm
    _ = _ := Measure.map_id

-- @node: sharpness_binary_response_eq
/-- If [the first response measure is concentrated on treatment zero or one](hyp:hν),
[the second response measure is concentrated on treatment zero or one](hyp:hη),
and [their outcome submeasures agree separately for both treatment states](hyp:hs),
[the two joint response measures are equal](goal). -/
lemma sharpness_binary_response_eq (ν η : Measure (ℝ × ℝ))
    (hν : ∀ᵐ a ∂ν, a.2 = 0 ∨ a.2 = 1)
    (hη : ∀ᵐ a ∂η, a.2 = 0 ∨ a.2 = 1)
    (hs : ∀ w : Bool, (ν.restrict {a | a.2 = if w then 1 else 0}).map Prod.fst =
      (η.restrict {a | a.2 = if w then 1 else 0}).map Prod.fst) : ν = η := by
  have h0 : ν.restrict {a | a.2 = 0} = η.restrict {a | a.2 = 0} := by
    rw [← sharpness_response_slice_reconstruction ν 0,
      ← sharpness_response_slice_reconstruction η 0]
    exact congrArg (fun μ : Measure ℝ => μ.map (fun y => (y, (0 : ℝ)))) (hs false)
  have h1 : ν.restrict {a | a.2 = 1} = η.restrict {a | a.2 = 1} := by
    rw [← sharpness_response_slice_reconstruction ν 1,
      ← sharpness_response_slice_reconstruction η 1]
    exact congrArg (fun μ : Measure ℝ => μ.map (fun y => (y, (1 : ℝ)))) (hs true)
  have hdis : Disjoint {a : ℝ × ℝ | a.2 = 0} {a | a.2 = 1} := by
    rw [Set.disjoint_left]
    intro a ha hb
    exact zero_ne_one (ha.symm.trans hb)
  have hsplit (μ : Measure (ℝ × ℝ)) (hμ : ∀ᵐ a ∂μ, a.2 = 0 ∨ a.2 = 1) :
      μ = μ.restrict {a | a.2 = 0} + μ.restrict {a | a.2 = 1} := by
    rw [← Measure.restrict_union hdis (measurableSet_eq_fun measurable_snd measurable_const)]
    exact (Measure.restrict_eq_self_of_ae_mem hμ).symm
  rw [hsplit ν hν, hsplit η hη, h0, h1]

-- @node: sharpness_conditional_response_binary
/-- [For almost every instrument–covariate pair, the conditional law of observed
outcome and treatment assigns probability one to treatment being zero or one](goal). -/
lemma sharpness_conditional_response_binary :
    ∀ᵐ zx ∂zxLaw M, ∀ᵐ yw ∂condDistrib (fun s => (M.Y s, M.W s))
      (fun s => (M.Zv s, M.Xv s)) M.law.toMeasure zx,
      yw.2 = 0 ∨ yw.2 = 1 := by
  have hj : ∀ᵐ a ∂M.law.toMeasure.map
      (fun s => ((M.Zv s, M.Xv s), (M.Y s, M.W s))),
      a.2.2 = 0 ∨ a.2.2 = 1 := by
    apply (ae_map_iff ((M.measZ.prodMk M.measX).prodMk
      (M.measY.prodMk M.measW)).aemeasurable ?_).mpr
    · exact Eventually.of_forall M.rangeW
    · exact (measurableSet_eq_fun measurable_snd.snd measurable_const).union
        (measurableSet_eq_fun measurable_snd.snd measurable_const)
  rw [← compProd_map_condDistrib (M.measY.prodMk M.measW).aemeasurable] at hj
  exact Measure.ae_ae_of_ae_compProd hj

/-- If [a second model has the original propensity](hyp:hp) and [its two latent
outcome marginals form a feasible pair for the original transport problem](hyp:hf),
[the two models' canonical outcome submeasures at their propensity thresholds
agree for both treatment states, almost everywhere under the original
instrument–covariate law](goal). -/
-- @node: sharpness_feasible_canonical_response
lemma sharpness_feasible_canonical_response
    {B : Type*} [MeasurableSpace B] (N : LatentIVModel B X Z)
    (hp : N.prop = M.prop)
    (hf : IsFeasiblePair (transportData M) (latentMarginal N false) (latentMarginal N true)) :
    ∀ᵐ zx ∂zxLaw M, ∀ w : Bool,
      canonSubmeasure N w zx.2 (N.prop zx.1 zx.2) =
        canonSubmeasure M w zx.2 (M.prop zx.1 zx.2) := by
  filter_upwards [hf.treated, hf.untreated] with zx ht hu
  intro w
  ext A hA
  rw [canonSubmeasure, hp, Measure.bind_apply hA (by
    first | fun_prop | exact ((outcomeKernel (latentMarginal N w)).measurable.comp
      (measurable_id.prodMk measurable_const)).aemeasurable)]
  cases w
  · exact hu A hA
  · exact ht A hA

/-- Suppose [the original model satisfies the structural assumptions](hyp:h).
If a second model satisfies [consistency](hyp:hcon), [instrument exogeneity](hyp:hex),
[uniform resistance conditional on covariates](hyp:hu), [measurability of its
propensity](hyp:hmeas), and [the threshold treatment rule almost surely](hyp:hsel),
has [the original propensity](hyp:hp) and [instrument–covariate law](hyp:hzx), and
[its latent outcome marginals are feasible for the original transport problem](hyp:hf),
[its joint observed law of outcome, treatment, instrument and covariates equals
the original observed law](goal). -/
-- @node: sharpness_identification_direct
lemma sharpness_identification_direct (h : StructuralAssumptions M)
    {B : Type*} [MeasurableSpace B] (N : LatentIVModel B X Z)
    (hcon : Consistency N) (hex : InstrumentExogeneity N) (hu : UniformResistance N)
    (hmeas : Measurable (Function.uncurry N.prop))
    (hsel : ∀ᵐ a ∂N.law.toMeasure,
      N.W a = if N.U a ≤ N.prop (N.Zv a) (N.Xv a) then 1 else 0)
    (hp : N.prop = M.prop) (hzx : zxLaw N = zxLaw M)
    (hf : IsFeasiblePair (transportData M) (latentMarginal N false) (latentMarginal N true)) :
    observedLaw N = observedLaw M := by
  have hN0 := sharpness_canonical_instrument_slice N hcon hex hu hmeas hsel false
  have hN1 := sharpness_canonical_instrument_slice N hcon hex hu hmeas hsel true
  have hNb := sharpness_conditional_response_binary N
  change ∀ᵐ zx ∂zxLaw N, _ at hN0 hN1
  rw [hzx] at hN0 hN1 hNb
  have hcond : condDistrib (fun a => (N.Y a, N.W a))
      (fun a => (N.Zv a, N.Xv a)) N.law.toMeasure =ᵐ[zxLaw M]
        condDistrib (fun a => (M.Y a, M.W a))
          (fun a => (M.Zv a, M.Xv a)) M.law.toMeasure := by
    filter_upwards [hN0, hN1, hNb, sharpness_conditional_response_binary M,
      sharpness_canonical_instrument_slice M h.2.1 h.2.2.1 h.2.2.2.2.1
        h.2.2.2.1.2.1 h.2.2.2.1.1 false,
      sharpness_canonical_instrument_slice M h.2.1 h.2.2.1 h.2.2.2.2.1
        h.2.2.2.1.2.1 h.2.2.2.1.1 true,
      sharpness_feasible_canonical_response M N hp hf] with zx hn0 hn1 hnb hmb hm0 hm1 hcanon
    apply sharpness_binary_response_eq _ _ hnb hmb
    intro w
    cases w
    · exact hn0.symm.trans ((hcanon false).trans hm0)
    · exact hn1.symm.trans ((hcanon true).trans hm1)
  have hj : N.law.toMeasure.map (fun a => ((N.Zv a, N.Xv a), (N.Y a, N.W a))) =
      M.law.toMeasure.map (fun a => ((M.Zv a, M.Xv a), (M.Y a, M.W a))) := by
    rw [← compProd_map_condDistrib (N.measY.prodMk N.measW).aemeasurable,
      ← compProd_map_condDistrib (M.measY.prodMk M.measW).aemeasurable]
    change (zxLaw N) ⊗ₘ _ = (zxLaw M) ⊗ₘ _
    rw [hzx]
    exact Measure.compProd_congr hcond
  have he := congrArg (fun μ : Measure ((Z × X) × (ℝ × ℝ)) =>
    μ.map (fun a => (a.2.1, a.2.2, a.1.1, a.1.2))) hj
  rw [Measure.map_map (by fun_prop) ((N.measZ.prodMk N.measX).prodMk
      (N.measY.prodMk N.measW)),
    Measure.map_map (by fun_prop) ((M.measZ.prodMk M.measX).prodMk
      (M.measY.prodMk M.measW))] at he
  exact he

-- @node: sharpness_observed_zx_marginal
/-- If [two models have the same joint observed law](hyp:hobs), [their joint
instrument–covariate laws coincide](goal). -/
lemma sharpness_observed_zx_marginal
    {B : Type*} [MeasurableSpace B] (N : LatentIVModel B X Z)
    (hobs : observedLaw N = observedLaw M) : zxLaw N = zxLaw M := by
  have he := congrArg (fun μ : Measure (ℝ × ℝ × Z × X) => μ.map (fun a => a.2.2)) hobs
  rw [observedLaw, observedLaw,
    Measure.map_map (by fun_prop) (N.measY.prodMk (N.measW.prodMk (N.measZ.prodMk N.measX))),
    Measure.map_map (by fun_prop) (M.measY.prodMk (M.measW.prodMk (M.measZ.prodMk M.measX)))] at he
  exact he

-- @node: sharpness_observed_x_marginal
/-- If [two models have the same joint observed law](hyp:hobs), [their covariate
laws coincide](goal). -/
lemma sharpness_observed_x_marginal
    {B : Type*} [MeasurableSpace B] (N : LatentIVModel B X Z)
    (hobs : observedLaw N = observedLaw M) : xLaw N = xLaw M := by
  have he := congrArg (fun μ : Measure (Z × X) => μ.map Prod.snd)
    (sharpness_observed_zx_marginal M N hobs)
  rw [zxLaw, zxLaw, Measure.map_map measurable_snd (N.measZ.prodMk N.measX),
    Measure.map_map measurable_snd (M.measZ.prodMk M.measX)] at he
  exact he

-- @node: sharpness_observed_response_unique
/-- If [two models have the same joint observed law](hyp:hobs), [their conditional
joint laws of outcome and treatment given instrument and covariates coincide
almost everywhere under the original instrument–covariate law](goal). -/
lemma sharpness_observed_response_unique
    {B : Type*} [MeasurableSpace B] (N : LatentIVModel B X Z)
    (hobs : observedLaw N = observedLaw M) :
    condDistrib (fun a => (N.Y a, N.W a)) (fun a => (N.Zv a, N.Xv a)) N.law.toMeasure
      =ᵐ[zxLaw M]
        condDistrib (fun a => (M.Y a, M.W a)) (fun a => (M.Zv a, M.Xv a)) M.law.toMeasure := by
  have hj : N.law.toMeasure.map (fun a => ((N.Zv a, N.Xv a), (N.Y a, N.W a))) =
      M.law.toMeasure.map (fun a => ((M.Zv a, M.Xv a), (M.Y a, M.W a))) := by
    have he := congrArg (fun μ : Measure (ℝ × ℝ × Z × X) =>
      μ.map (fun a => (a.2.2, (a.1, a.2.1)))) hobs
    rw [observedLaw, observedLaw,
      Measure.map_map (by fun_prop) (N.measY.prodMk (N.measW.prodMk (N.measZ.prodMk N.measX))),
      Measure.map_map (by fun_prop) (M.measY.prodMk (M.measW.prodMk (M.measZ.prodMk M.measX)))] at he
    exact he
  have hc := sharpness_conditional_law_unique N.law.toMeasure M.law.toMeasure
    (fun a => (N.Zv a, N.Xv a)) (fun a => (N.Y a, N.W a))
    (fun a => (M.Zv a, M.Xv a)) (fun a => (M.Y a, M.W a))
    (N.measZ.prodMk N.measX) (N.measY.prodMk N.measW)
    (M.measZ.prodMk M.measX) (M.measY.prodMk M.measW) hj
  change _ =ᵐ[zxLaw N] _ at hc
  rwa [sharpness_observed_zx_marginal M N hobs] at hc

/-- If [the original model satisfies threshold crossing](hyp:ht), [a second model
also satisfies threshold crossing](hyp:hnt), and [their joint observed laws
coincide](hyp:hobs), [their propensity functions agree almost everywhere under
the original instrument–covariate law](goal). -/
-- @node: sharpness_observed_propensity_unique
lemma sharpness_observed_propensity_unique (ht : ThresholdCrossing M)
    {B : Type*} [MeasurableSpace B] (N : LatentIVModel B X Z)
    (hnt : ThresholdCrossing N) (hobs : observedLaw N = observedLaw M) :
    ∀ᵐ zx ∂zxLaw M, N.prop zx.1 zx.2 = M.prop zx.1 zx.2 := by
  have hj : N.law.toMeasure.map (fun a => ((N.Zv a, N.Xv a), N.W a)) =
      M.law.toMeasure.map (fun a => ((M.Zv a, M.Xv a), M.W a)) := by
    have he := congrArg (fun μ : Measure (ℝ × ℝ × Z × X) =>
      μ.map (fun a => (a.2.2, a.2.1))) hobs
    rw [observedLaw, observedLaw,
      Measure.map_map (by fun_prop) (N.measY.prodMk (N.measW.prodMk (N.measZ.prodMk N.measX))),
      Measure.map_map (by fun_prop) (M.measY.prodMk (M.measW.prodMk (M.measZ.prodMk M.measX)))] at he
    exact he
  have hc := sharpness_conditional_law_unique N.law.toMeasure M.law.toMeasure
    (fun a => (N.Zv a, N.Xv a)) N.W (fun a => (M.Zv a, M.Xv a)) M.W
    (N.measZ.prodMk N.measX) N.measW (M.measZ.prodMk M.measX) M.measW hj
  change _ =ᵐ[zxLaw N] _ at hc
  have hnmean := hnt.2.2.2
  rw [sharpness_observed_zx_marginal M N hobs] at hc hnmean
  filter_upwards [hc, hnmean, ht.2.2.2] with zx hκ hn hm
  rw [hκ] at hn
  exact hn.symm.trans hm

/-- If [the original model satisfies the structural assumptions](hyp:h), [a second
model satisfies those assumptions as well](hyp:hn), [the two outcome domains
coincide](hyp:hy), and [their joint observed laws coincide](hyp:hobs), [the second
model's two latent outcome marginals form a feasible pair for the original
transport problem, satisfying support, both selection constraints and the
uniform resistance–covariate marginal restriction](goal). -/
-- @node: sharpness_identification_converse
lemma sharpness_identification_converse (h : StructuralAssumptions M)
    {B : Type*} [MeasurableSpace B] (N : LatentIVModel B X Z)
    (hn : StructuralAssumptions N) (hy : N.Yset = M.Yset)
    (hobs : observedLaw N = observedLaw M) :
    IsFeasiblePair (transportData M) (latentMarginal N false) (latentMarginal N true) := by
  have hz := sharpness_observed_zx_marginal M N hobs
  have hx := sharpness_observed_x_marginal M N hobs
  have hcanon : ∀ᵐ zx ∂zxLaw M, ∀ w : Bool,
      canonSubmeasure N w zx.2 (M.prop zx.1 zx.2) =
        canonSubmeasure M w zx.2 (M.prop zx.1 zx.2) := by
    have hns (w : Bool) := sharpness_canonical_instrument_slice N hn.2.1 hn.2.2.1
      hn.2.2.2.2.1 hn.2.2.2.1.2.1 hn.2.2.2.1.1 w
    change ∀ w : Bool, ∀ᵐ zx ∂zxLaw N, _ at hns
    simp only [hz] at hns
    filter_upwards [hns false, hns true,
      sharpness_canonical_instrument_slice M h.2.1 h.2.2.1 h.2.2.2.2.1
        h.2.2.2.1.2.1 h.2.2.2.1.1 false,
      sharpness_canonical_instrument_slice M h.2.1 h.2.2.1 h.2.2.2.2.1
        h.2.2.2.1.2.1 h.2.2.2.1.1 true,
      sharpness_observed_response_unique M N hobs,
      sharpness_observed_propensity_unique M h.2.2.2.1 N hn.2.2.2.1 hobs]
      with zx hn0 hn1 hm0 hm1 hresp hp
    rw [hp, hresp] at hn0 hn1
    intro w
    cases w
    · exact hn0.trans hm0.symm
    · exact hn1.trans hm1.symm
  have hs (w : Bool) : IsProbabilityMeasure (latentMarginal N w) ∧
      (latentMarginal N w) {a | a.1.1 ∈ Icc (0 : ℝ) 1 ∧ a.2 ∈ M.Yset}ᶜ = 0 := by
    have hm : Measurable (potential N w) := by
      first | fun_prop | cases w <;> first | exact N.measY0 | exact N.measY1
    have hjm := (N.measU.prodMk N.measX).prodMk hm
    refine ⟨Measure.isProbabilityMeasure_map hjm.aemeasurable, ae_iff.mp ?_⟩
    apply (ae_map_iff hjm.aemeasurable ?_).mpr
    · have hp : ∀ᵐ a ∂N.law.toMeasure, potential N w a ∈ N.Yset := by
        cases w
        · exact hn.1.1
        · exact hn.1.2
      filter_upwards [hp] with a ha
      exact ⟨N.rangeU a, hy ▸ ha⟩
    · exact (measurableSet_Icc.preimage measurable_fst.fst).inter
        (h.2.2.2.2.2.2.1.measurableSet.preimage measurable_snd)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro pi hpi
    rcases hpi with hpi | hpi
    · rw [hpi]
      exact hs false
    · rw [Set.mem_singleton_iff.mp hpi]
      exact hs true
  · filter_upwards [hcanon] with zx hc
    intro A hA
    have he := congrArg (fun μ : Measure ℝ => μ A) (hc true)
    rw [canonSubmeasure, Measure.bind_apply hA (by fun_prop)] at he
    exact he
  · filter_upwards [hcanon] with zx hc
    intro A hA
    have he := congrArg (fun μ : Measure ℝ => μ A) (hc false)
    rw [canonSubmeasure, Measure.bind_apply hA (by fun_prop)] at he
    exact he
  · constructor <;> rw [latentMarginal_uniform_fst N hn.2.2.2.2.1, hx] <;> rfl

end Papers.TbsPrteOptimalTransport

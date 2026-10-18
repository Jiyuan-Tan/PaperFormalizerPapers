module
public import Papers.TbsPrteOptimalTransport.Helpers.Ranges
public import Causalean.Mathlib.Probability.Kernel.CondDistribWitness
/-! Shared Canonical proof obligations. -/
public section
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set
open scoped Classical ENNReal
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z]
variable (M : LatentIVModel Ω X Z)

-- @node: factorized_kernel_statistic_joint
/-- If [the statistic f of a draw and its conditioning value is jointly measurable](hyp:hf), [drawing two conditionally independent variables and retaining the statistic together with the conditioning value leaves the other variable's conditional kernel unchanged: the transformed joint measure factors into the statistic-and-conditioning marginal and that same kernel](goal). -/
lemma factorized_kernel_statistic_joint
    {C T V D : Type*} [MeasurableSpace C] [MeasurableSpace T]
    [MeasurableSpace V] [MeasurableSpace D]
    (ν : Measure C) [IsFiniteMeasure ν]
    (J : Kernel C T) (K : Kernel C V) [IsMarkovKernel J] [IsMarkovKernel K]
    (f : T → C → D) (hf : Measurable (fun tc : T × C => f tc.1 tc.2)) :
    (ν ⊗ₘ (J.prod K)).map (fun a => ((f a.2.1 a.1, a.1), a.2.2)) =
      ((ν ⊗ₘ J).map (fun a => (f a.2 a.1, a.1))) ⊗ₘ
        (K.comap (Prod.snd : D × C → C) measurable_snd) := by
  have hF : Measurable (fun a : C × T => (f a.2 a.1, a.1)) := by fun_prop
  have hG : Measurable (fun a : C × (T × V) => ((f a.2.1 a.1, a.1), a.2.2)) := by
    fun_prop
  refine Measure.ext_prod fun {A B} hA hB => ?_
  rw [Measure.map_apply hG (hA.prod hB), Measure.compProd_apply_prod hA hB,
    ← lintegral_indicator hA]
  have hm := (((K.comap (Prod.snd : D × C → C)
    measurable_snd).measurable_coe hB).indicator hA).comp hF
  simp only [Function.comp_def] at hm
  rw [lintegral_map (((K.comap (Prod.snd : D × C → C)
    measurable_snd).measurable_coe hB).indicator hA) hF,
    Measure.lintegral_compProd hm]
  rw [Measure.compProd_apply ((hA.prod hB).preimage hG)]
  apply lintegral_congr
  intro c
  have hAc : MeasurableSet {t : T | (f t c, c) ∈ A} := by
    first | fun_prop | exact hA.preimage (hF.comp (measurable_const.prodMk measurable_id))
  have he : (Prod.mk c ⁻¹' ((fun a : C × (T × V) =>
      ((f a.2.1 a.1, a.1), a.2.2)) ⁻¹' (A ×ˢ B))) =
      {t : T | (f t c, c) ∈ A} ×ˢ B := rfl
  rw [he, Kernel.prod_apply, Measure.prod_prod]
  change J c {t | (f t c, c) ∈ A} * K c B =
    ∫⁻ t, A.indicator (fun dc => K dc.2 B) (f t c, c) ∂J c
  rw [show (fun t => A.indicator (fun dc => K dc.2 B) (f t c, c)) =
      {t : T | (f t c, c) ∈ A}.indicator (fun _ => K c B) by
    funext t; by_cases ht : (f t c, c) ∈ A <;> simp [ht]]
  rw [lintegral_indicator hAc, lintegral_const, mul_comm]
  simp only [Measure.restrict_apply_univ]

-- @node: exogenous_latent_given_propensity
/-- Under [conditional exogeneity of the instrument](hyp:h) and [joint measurability of the propensity in instruments and covariates](hyp:hp), [the conditional distribution of resistance and both potential outcomes given propensity and covariates equals their conditional distribution given covariates alone, for almost every observed propensity-covariate pair](goal). -/
lemma exogenous_latent_given_propensity (h : InstrumentExogeneity M)
    (hp : Measurable (Function.uncurry M.prop)) :
    condDistrib (fun s => (M.U s, M.Y0 s, M.Y1 s))
      (fun s => (M.prop (M.Zv s) (M.Xv s), M.Xv s)) M.law.toMeasure
      =ᵐ[M.law.toMeasure.map (fun s => (M.prop (M.Zv s) (M.Xv s), M.Xv s))]
        fun px : ℝ × X =>
          condDistrib (fun s => (M.U s, M.Y0 s, M.Y1 s)) M.Xv M.law.toMeasure px.2 := by
  let V := fun s => (M.U s, M.Y0 s, M.Y1 s)
  have hV : Measurable V := by
    first | fun_prop | exact M.measU.prodMk (M.measY0.prodMk M.measY1)
  have hZX : Measurable (fun s => (M.Zv s, M.Xv s)) := by
    first | fun_prop | exact M.measZ.prodMk M.measX
  have hPX : Measurable (fun s => (M.prop (M.Zv s) (M.Xv s), M.Xv s)) := by
    first | fun_prop | exact (hp.comp hZX).prodMk M.measX
  haveI := M.instKernel_markov
  change _ =ᵐ[_] ((condDistrib V M.Xv M.law.toMeasure).comap
    (mγ := inferInstance) (Prod.snd : ℝ × X → X) measurable_snd)
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
    (condDistrib V M.Xv M.law.toMeasure) M.prop hp
  rw [← hj, hi, Measure.map_map (by fun_prop) (M.measX.prodMk (M.measZ.prodMk hV)),
    Measure.map_map (by fun_prop) (M.measX.prodMk M.measZ)] at he
  exact he
-- @node: latent_conditional_uniform_disintegration
/-- Under [uniform resistance conditional on covariates](hyp:hu), [the conditional joint law of resistance and the potential outcome for either treatment state can almost surely be obtained by drawing resistance uniformly between zero and one and then drawing the outcome from the latent outcome kernel at that resistance and covariate value](goal). -/
lemma latent_conditional_uniform_disintegration (hu : UniformResistance M) (w : Bool) :
    condDistrib (fun s => (M.U s, potential M w s)) M.Xv M.law.toMeasure
      =ᵐ[xLaw M]
        (Kernel.const X Causalean.Stat.unifOI) ⊗ₖ
          ((outcomeKernel (latentMarginal M w)).comap
            (Prod.swap : X × ℝ → ℝ × X) measurable_swap) := by
  have hY : Measurable (potential M w) := by
    first | fun_prop | cases w <;> first | exact M.measY0 | exact M.measY1
  have hUY := M.measU.prodMk hY
  haveI := outcomeKernel_isMarkov (latentMarginal M w)
  haveI : IsProbabilityMeasure (latentMarginal M w) :=
    Measure.isProbabilityMeasure_map ((M.measU.prodMk M.measX).prodMk hY).aemeasurable
  haveI : IsProbabilityMeasure (xLaw M) :=
    Measure.isProbabilityMeasure_map M.measX.aemeasurable
  let K := outcomeKernel (latentMarginal M w)
  let L := (Kernel.const X Causalean.Stat.unifOI) ⊗ₖ
    (K.comap (Prod.swap : X × ℝ → ℝ × X) measurable_swap)
  apply condDistrib_ae_eq_of_measure_eq_compProd _ hUY.aemeasurable (κ := L)
  have hd : (Causalean.Stat.unifOI.prod (xLaw M)) ⊗ₘ K = latentMarginal M w := by
    rw [← latentMarginal_uniform_fst M hu w]
    dsimp only [K, outcomeKernel]
    rw [dif_pos (inferInstance : IsFiniteMeasure (latentMarginal M w))]
    exact Measure.disintegrate _ _
  have he : M.law.toMeasure.map (fun s => (M.Xv s, M.U s, potential M w s)) =
      (latentMarginal M w).map (fun a => (a.1.2, a.1.1, a.2)) := by
    rw [latentMarginal, Measure.map_map (by fun_prop)
      ((M.measU.prodMk M.measX).prodMk hY)]
    rfl
  rw [he, ← hd]
  ext B hB
  rw [Measure.map_apply (by fun_prop) hB,
    Measure.compProd_apply (hB.preimage (by fun_prop)), Measure.compProd_apply hB]
  change (∫⁻ ux : ℝ × X, K ux {y | (ux.2, ux.1, y) ∈ B}
      ∂Causalean.Stat.unifOI.prod (xLaw M)) = ∫⁻ x, L x (Prod.mk x ⁻¹' B) ∂xLaw M
  have hm : Measurable (fun xu : X × ℝ => K (xu.2, xu.1) {y | (xu.1, xu.2, y) ∈ B}) := by
    first | fun_prop | exact (Kernel.measurable_kernel_prodMk_left
      (κ := K.comap (Prod.swap : X × ℝ → ℝ × X) measurable_swap)
      (hB.preimage MeasurableEquiv.prodAssoc.measurable))
  rw [← Measure.prod_swap (μ := xLaw M) (ν := Causalean.Stat.unifOI),
    lintegral_map (by simpa only [Function.comp_def, Prod.swap, Prod.mk.eta] using (hm.comp measurable_swap)) measurable_swap]
  change (∫⁻ xu : X × ℝ, K (xu.2, xu.1) {y | (xu.1, xu.2, y) ∈ B}
    ∂(xLaw M).prod Causalean.Stat.unifOI) = _
  rw [lintegral_prod _ hm.aemeasurable]
  apply lintegral_congr
  intro x
  rw [show L = _ from rfl, Kernel.compProd_apply (hB.preimage (by fun_prop))]
  rfl

-- @node: interval_kernel_mass
/-- [Integrating a probability kernel over the interval open at a and closed at b gives a measure whose total mass is the greater of zero and the difference b − a](goal). -/
lemma interval_kernel_mass (K : Kernel ℝ ℝ) [IsMarkovKernel K] (a b : ℝ) :
    ((volume.restrict (Ioc a b)).bind K) univ = ENNReal.ofReal (b - a) := by
  have hK : Measurable K := by fun_prop
  rw [Measure.bind_apply MeasurableSet.univ hK.aemeasurable]
  simp [Real.volume_Ioc]

-- @node: interval_kernel_add
/-- If [a does not exceed b](hyp:hab) and [b does not exceed c](hyp:hbc), [integrating a kernel from a to c equals the sum of its integrals from a to b and from b to c, with each interval open on the left and closed on the right](goal). -/
lemma interval_kernel_add (K : Kernel ℝ ℝ) (a b c : ℝ)
    (hab : a ≤ b) (hbc : b ≤ c) :
    (volume.restrict (Ioc a c)).bind K =
      (volume.restrict (Ioc a b)).bind K + (volume.restrict (Ioc b c)).bind K := by
  have hK : Measurable K := by fun_prop
  rw [← Ioc_union_Ioc_eq_Ioc hab hbc,
    Measure.restrict_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc]
  ext A hA
  simp only [Measure.add_apply, Measure.bind_apply hA hK.aemeasurable,
    lintegral_add_measure]

-- @node: measure_add_increment_bound
/-- If [the original measure has finite total mass](hyp:hmu), [d is nonnegative](hyp:hd), and [the added measure has total mass d](hyp:hnu), [adding that measure changes the real-valued mass of any event by at most d in absolute value](goal). -/
lemma measure_add_increment_bound (mu nu : Measure ℝ)
    (hmu : mu univ ≠ ∞) (d : ℝ) (hd : 0 ≤ d)
    (hnu : nu univ = ENNReal.ofReal d) (A : Set ℝ) :
    |((mu + nu) A).toReal - (mu A).toReal| ≤ d := by
  have hmuA : mu A ≠ ∞ := ne_top_of_le_ne_top hmu (measure_mono (subset_univ A))
  have hnuA_le : nu A ≤ ENNReal.ofReal d := by
    rw [← hnu]
    exact measure_mono (subset_univ A)
  have hnuA : nu A ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hnuA_le
  have hbound : (nu A).toReal ≤ d := by
    simpa only [ENNReal.toReal_ofReal hd] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hnuA_le
  rw [Measure.add_apply, ENNReal.toReal_add hmuA hnuA]
  simpa only [add_sub_cancel_left, abs_of_nonneg ENNReal.toReal_nonneg] using hbound

-- @node: interval_kernel_finite
/-- [Integrating a probability kernel over any bounded interval open on the left and closed on the right gives a measure of finite total mass](goal). -/
lemma interval_kernel_finite (K : Kernel ℝ ℝ) [IsMarkovKernel K] (a b : ℝ) :
    ((volume.restrict (Ioc a b)).bind K) univ ≠ ∞ := by
  rw [interval_kernel_mass]
  exact ENNReal.ofReal_ne_top

-- @node: interval_kernel_upper_increment
/-- If [a does not exceed b](hyp:hab) and [b does not exceed c](hyp:hbc), [extending the upper endpoint of a probability-kernel integration interval from b to c changes the real-valued mass of any event by at most c minus b](goal). -/
lemma interval_kernel_upper_increment (K : Kernel ℝ ℝ) [IsMarkovKernel K]
    (a b c : ℝ) (hab : a ≤ b) (hbc : b ≤ c) (A : Set ℝ) :
    |(((volume.restrict (Ioc a c)).bind K) A).toReal -
      (((volume.restrict (Ioc a b)).bind K) A).toReal| ≤ c - b := by
  rw [interval_kernel_add K a b c hab hbc]
  exact measure_add_increment_bound _ _ (interval_kernel_finite K a b)
    (c - b) (sub_nonneg.mpr hbc) (interval_kernel_mass K b c) A

-- @node: interval_kernel_lower_increment
/-- If [a does not exceed b](hyp:hab) and [b does not exceed c](hyp:hbc), [extending a probability-kernel integration interval's lower endpoint from b down to a changes the real-valued mass of any event by at most b minus a](goal). -/
lemma interval_kernel_lower_increment (K : Kernel ℝ ℝ) [IsMarkovKernel K]
    (a b c : ℝ) (hab : a ≤ b) (hbc : b ≤ c) (A : Set ℝ) :
    |(((volume.restrict (Ioc a c)).bind K) A).toReal -
      (((volume.restrict (Ioc b c)).bind K) A).toReal| ≤ b - a := by
  rw [interval_kernel_add K a b c hab hbc, add_comm]
  exact measure_add_increment_bound _ _ (interval_kernel_finite K b c)
    (b - a) (sub_nonneg.mpr hab) (interval_kernel_mass K a b) A

-- @node: selected_kernel_lipschitz
/-- If [p lies between zero and one](hyp:hp) and [p′ lies between zero and one](hyp:hp'), [changing the selection threshold from p to p′ changes any event's real-valued mass under the integrated probability kernel by at most the absolute threshold difference, for either the treated or untreated selection region](goal). -/
lemma selected_kernel_lipschitz (K : Kernel ℝ ℝ) [IsMarkovKernel K]
    (w : Bool) (p p' : ℝ) (hp : p ∈ Icc (0 : ℝ) 1)
    (hp' : p' ∈ Icc (0 : ℝ) 1) (A : Set ℝ) :
    |(((volume.restrict (selRegion w p)).bind K) A).toReal -
      (((volume.restrict (selRegion w p')).bind K) A).toReal| ≤ |p - p'| := by
  cases w with
  | false =>
    change |(((volume.restrict (Ioc p 1)).bind K) A).toReal -
      (((volume.restrict (Ioc p' 1)).bind K) A).toReal| ≤ |p - p'|
    rcases le_total p p' with hpp | hpp
    · rw [abs_sub_comm p p', abs_of_nonneg (sub_nonneg.mpr hpp)]
      exact interval_kernel_lower_increment K p p' 1 hpp hp'.2 A
    · rw [abs_sub_comm (((volume.restrict (Ioc p 1)).bind K) A).toReal,
        abs_of_nonneg (sub_nonneg.mpr hpp)]
      exact interval_kernel_lower_increment K p' p 1 hpp hp.2 A
  | true =>
    change |(((volume.restrict (Ioc 0 p)).bind K) A).toReal -
      (((volume.restrict (Ioc 0 p')).bind K) A).toReal| ≤ |p - p'|
    rcases le_total p p' with hpp | hpp
    · rw [abs_sub_comm (((volume.restrict (Ioc 0 p)).bind K) A).toReal,
        abs_sub_comm p p', abs_of_nonneg (sub_nonneg.mpr hpp)]
      exact interval_kernel_upper_increment K 0 p p' hp.1 hpp A
    · rw [abs_of_nonneg (sub_nonneg.mpr hpp)]
      exact interval_kernel_upper_increment K 0 p' p hp'.1 hpp A

-- @node: canonical_submeasure_mass
/-- Under [the structural assumptions](hyp:h), [for almost every covariate value and every propensity between zero and one, the canonical outcome submeasure has total mass equal to the propensity for the treated state and one minus the propensity for the untreated state](goal). -/
lemma canonical_submeasure_mass (h : StructuralAssumptions M) (w : Bool) :
    ∀ᵐ x ∂xLaw M, ∀ p ∈ Icc (0 : ℝ) 1,
      canonSubmeasure M w x p univ = ENNReal.ofReal (if w then p else 1-p) := by
  have := outcomeKernel_isMarkov (latentMarginal M w)
  refine Filter.Eventually.of_forall fun x p hp => ?_
  have hK : Measurable (fun u : ℝ => outcomeKernel (latentMarginal M w) (u, x)) := by
    fun_prop
  rw [canonSubmeasure, Measure.bind_apply MeasurableSet.univ hK.aemeasurable]
  cases w <;> simp [selRegion, Real.volume_Ioc]
-- @node: canonical_submeasure_tv
/-- Under [the structural assumptions](hyp:h), [for almost every covariate value, changing a propensity within the unit interval changes the canonical outcome submeasure's real-valued mass on any event by at most the absolute propensity difference, for either treatment state](goal). -/
lemma canonical_submeasure_tv (h : StructuralAssumptions M) (w : Bool) :
    ∀ᵐ x ∂xLaw M, ∀ p ∈ Icc (0 : ℝ) 1, ∀ p' ∈ Icc (0 : ℝ) 1, ∀ A,
      |(canonSubmeasure M w x p A).toReal - (canonSubmeasure M w x p' A).toReal| ≤ |p-p'| := by
  have := outcomeKernel_isMarkov (latentMarginal M w)
  refine Filter.Eventually.of_forall fun x p hp p' hp' A => ?_
  let K := (outcomeKernel (latentMarginal M w)).comap
    (fun u : ℝ => (u, x)) (by fun_prop)
  exact selected_kernel_lipschitz K w p p' hp hp' A
-- @node: threshold_observed_conditional_law
/-- Under [the structural assumptions](hyp:h), [for almost every observed propensity-covariate pair, the conditional law of observed outcome and treatment equals the law obtained from resistance and potential outcomes conditional on covariates by assigning treatment when resistance does not exceed the propensity and selecting the corresponding potential outcome](goal). -/
lemma threshold_observed_conditional_law (h : StructuralAssumptions M) :
    condDistrib (fun s => (M.Y s, M.W s))
      (fun s => (M.prop (M.Zv s) (M.Xv s), M.Xv s)) M.law.toMeasure
      =ᵐ[M.law.toMeasure.map (fun s => (M.prop (M.Zv s) (M.Xv s), M.Xv s))]
        fun px => (condDistrib (fun s => (M.U s, M.Y0 s, M.Y1 s))
          M.Xv M.law.toMeasure px.2).map
          (fun v => (if v.1 ≤ px.1 then v.2.2 else v.2.1,
            if v.1 ≤ px.1 then (1 : ℝ) else 0)) := by
  let V := fun s => (M.U s, M.Y0 s, M.Y1 s)
  let P := fun s => M.prop (M.Zv s) (M.Xv s)
  let F := fun (p : ℝ) (_x : X) (v : ℝ × ℝ × ℝ) =>
    (if v.1 ≤ p then v.2.2 else v.2.1, if v.1 ≤ p then (1 : ℝ) else 0)
  have hV : Measurable V := by
    first | fun_prop | exact M.measU.prodMk (M.measY0.prodMk M.measY1)
  have hP : Measurable P := by
    first | fun_prop | exact h.2.2.2.1.2.1.comp (M.measZ.prodMk M.measX)
  have hF : Measurable (fun a : (ℝ × X) × (ℝ × ℝ × ℝ) =>
      F a.1.1 a.1.2 a.2) := by
    first | fun_prop | exact (
      (measurable_snd.snd.snd.ite
        (measurableSet_le measurable_snd.fst measurable_fst.fst)
        measurable_snd.snd.fst).prodMk
      (measurable_const.ite (measurableSet_le measurable_snd.fst measurable_fst.fst)
        measurable_const))
  have hCI := exogenous_latent_given_propensity M h.2.2.1 h.2.2.2.1.2.1
  have hresponse := condDistrib_map_of_condDistrib_fst_eq M.law.toMeasure
    (X := P) (Z := M.Xv) (C := V) (h := F) hP M.measX hV hF hCI
  have he : (fun s => (M.Y s, M.W s)) =ᵐ[M.law.toMeasure]
      (fun s => F (P s) (M.Xv s) (V s)) := by
    filter_upwards [h.2.1, h.2.2.2.1.1] with s hs ht
    dsimp only [F, P, V]
    rw [hs, ht]
    split_ifs <;> simp
  rw [condDistrib_congr_left he]
  exact hresponse

-- @node: canonical_submeasure_observed
/-- Under [the structural assumptions](hyp:h), [the canonical outcome submeasure for either treatment state equals the corresponding observed conditional outcome submeasure for almost every observed propensity-covariate pair](goal). -/
lemma canonical_submeasure_observed (h : StructuralAssumptions M) (w : Bool) :
    ∀ᵐ px ∂M.law.toMeasure.map (fun s => (M.prop (M.Zv s) (M.Xv s), M.Xv s)),
      canonSubmeasure M w px.2 px.1 = obsSubmeasure M w px.2 px.1 := by
  let V := fun s => (M.U s, M.Y0 s, M.Y1 s)
  let proj := fun v : ℝ × ℝ × ℝ => (v.1, if w then v.2.2 else v.2.1)
  have hV : Measurable V := by
    first | fun_prop | exact M.measU.prodMk (M.measY0.prodMk M.measY1)
  have hproj : Measurable proj := by
    first | fun_prop | cases w <;> simp only [proj, Bool.false_eq_true, ↓reduceIte] <;> fun_prop
  have hcomp := condDistrib_comp (μ := M.law.toMeasure) (mβ := inferInstance) M.Xv hV.aemeasurable hproj
  have hlatent := latent_conditional_uniform_disintegration M h.2.2.2.2.1 w
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
  have hPX : Measurable (fun s => (M.prop (M.Zv s) (M.Xv s), M.Xv s)) := by
    first | fun_prop | exact
      (h.2.2.2.1.2.1.comp (M.measZ.prodMk M.measX)).prodMk M.measX
  have hmarg : (M.law.toMeasure.map
      (fun s => (M.prop (M.Zv s) (M.Xv s), M.Xv s))).map Prod.snd = xLaw M := by
    rw [Measure.map_map measurable_snd hPX]
    rfl
  rw [← hmarg] at hjoint
  have hpull := ae_of_ae_map measurable_snd.aemeasurable hjoint
  have hprange : ∀ᵐ px ∂M.law.toMeasure.map
      (fun s => (M.prop (M.Zv s) (M.Xv s), M.Xv s)), px.1 ∈ Icc (0 : ℝ) 1 := by
    apply (ae_map_iff hPX.aemeasurable (measurableSet_Icc.preimage measurable_fst)).mpr
    exact Filter.Eventually.of_forall fun s => M.rangeProp _ _
  filter_upwards [threshold_observed_conditional_law M h, hpull, hprange]
    with px hobs hx hp
  haveI := outcomeKernel_isMarkov (latentMarginal M w)
  let K := outcomeKernel (latentMarginal M w)
  let F := fun v : ℝ × ℝ × ℝ =>
    (if v.1 ≤ px.1 then v.2.2 else v.2.1, if v.1 ≤ px.1 then (1 : ℝ) else 0)
  let E := fun (B : Set ℝ) => {uy : ℝ × ℝ |
    uy.2 ∈ B ∧ (if uy.1 ≤ px.1 then (1 : ℝ) else 0) = (if w then 1 else 0)}
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
  have heval : obsSubmeasure M w px.2 px.1 B =
      ((Kernel.const X Causalean.Stat.unifOI) ⊗ₖ
        (K.comap (Prod.swap : X × ℝ → ℝ × X) measurable_swap)) px.2 (E B) := by
    change ((condDistrib (fun s => (M.Y s, M.W s))
      (fun s => (M.prop (M.Zv s) (M.Xv s), M.Xv s)) M.law.toMeasure px).restrict
      {a | a.2 = if w then 1 else 0}).map Prod.fst B = _
    rw [hobs, Measure.map_apply measurable_fst hB,
      Measure.restrict_apply (hB.preimage measurable_fst),
      Measure.map_apply hF ((hB.preimage measurable_fst).inter
        (measurableSet_eq_fun measurable_snd measurable_const)), ← hx,
      Measure.map_apply hproj hE]
    congr 1
    ext v
    cases w <;> by_cases hv : v.1 ≤ px.1 <;>
      simp [F, proj, E, hv, and_comm]
  symm
  rw [heval, Kernel.compProd_apply hE]
  change (∫⁻ u, K (u, px.2) {y | (u, y) ∈ E B} ∂Causalean.Stat.unifOI) =
    canonSubmeasure M w px.2 px.1 B
  have hsel : MeasurableSet (selRegion w px.1) := by
    cases w <;> simp only [selRegion, Bool.false_eq_true, ↓reduceIte] <;>
      exact measurableSet_Ioc
  have hrestrict : Causalean.Stat.unifOI.restrict (selRegion w px.1) =
      volume.restrict (selRegion w px.1) := by
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
    _ = ∫⁻ u, (selRegion w px.1).indicator (fun u => K (u, px.2) B) u
        ∂Causalean.Stat.unifOI := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
      have hset : {y | (u, y) ∈ E B} =
          if u ∈ selRegion w px.1 then B else ∅ := by
        ext y
        cases w <;> by_cases ht : u ≤ px.1 <;>
          simp [E, selRegion, ht, hu.1, hu.2.le, not_lt, not_le, and_comm]
      rw [hset]
      by_cases ht : u ∈ selRegion w px.1 <;> simp [ht]
    _ = ∫⁻ u, K (u, px.2) B ∂volume.restrict (selRegion w px.1) := by
      rw [lintegral_indicator hsel, hrestrict]
    _ = _ := by
      rw [canonSubmeasure, Measure.bind_apply hB (by fun_prop)]
end Papers.TbsPrteOptimalTransport

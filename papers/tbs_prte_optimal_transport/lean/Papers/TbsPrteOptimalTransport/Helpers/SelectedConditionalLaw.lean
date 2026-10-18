module
public import Papers.TbsPrteOptimalTransport.Helpers.Canonical
/-! Structural factorization of the conditional joint law used by boundary selection. -/
public section
set_option linter.style.openClassical false
set_option linter.unusedSectionVars false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z]

/-- Under [the structural assumptions on the latent instrument model](hyp:h),
[for almost every covariate value, the conditional joint law of observed outcome,
treatment, and instrument equals the product of the conditional instrument law
and the conditional joint law of resistance and both potential outcomes, transformed
by assigning treatment when resistance does not exceed propensity and choosing
the corresponding potential outcome while retaining the instrument](goal). -/
-- @node: conditional_observed_joint_factorization
lemma conditional_observed_joint_factorization (M : LatentIVModel Ω X Z)
    (h : StructuralAssumptions M) :
    ∀ᵐ x ∂xLaw M,
      condDistrib (fun s => (M.Y s, M.W s, M.Zv s)) M.Xv M.law.toMeasure x =
        ((M.instKernel x).prod
          (condDistrib (fun s => (M.U s, M.Y0 s, M.Y1 s)) M.Xv M.law.toMeasure x)).map
          (fun zv => (if zv.2.1 ≤ M.prop zv.1 x then zv.2.2.2 else zv.2.2.1,
            if zv.2.1 ≤ M.prop zv.1 x then (1 : ℝ) else 0, zv.1)) := by
  let V := fun s => (M.U s, M.Y0 s, M.Y1 s)
  let H := fun (x : X) (zv : Z × (ℝ × ℝ × ℝ)) =>
    (if zv.2.1 ≤ M.prop zv.1 x then zv.2.2.2 else zv.2.2.1,
      if zv.2.1 ≤ M.prop zv.1 x then (1 : ℝ) else 0, zv.1)
  have hV : Measurable V := by
    first | fun_prop | exact M.measU.prodMk (M.measY0.prodMk M.measY1)
  have hp : Measurable (fun p : X × (Z × (ℝ × ℝ × ℝ)) => M.prop p.2.1 p.1) := by
    exact h.2.2.2.1.2.1.comp (measurable_snd.fst.prodMk measurable_fst)
  have hH : Measurable (fun p : X × (Z × (ℝ × ℝ × ℝ)) => H p.1 p.2) := by
    first | fun_prop | exact (
      (measurable_snd.snd.snd.snd.ite
        (measurableSet_le measurable_snd.snd.fst hp)
        measurable_snd.snd.snd.fst).prodMk
      ((measurable_const.ite (measurableSet_le measurable_snd.snd.fst hp)
        measurable_const).prodMk measurable_snd.fst))
  have hresponse := condDistrib_map_of_funext M.law.toMeasure M.measX
    (M.measZ.prodMk hV) hH
  have he : (fun s => (M.Y s, M.W s, M.Zv s)) =ᵐ[M.law.toMeasure]
      (fun s => H (M.Xv s) (M.Zv s, V s)) := by
    filter_upwards [h.2.1, h.2.2.2.1.1] with s hs ht
    dsimp only [H, V]
    rw [hs, ht]
    split_ifs <;> simp
  rw [condDistrib_congr_left he]
  filter_upwards [hresponse, h.2.2.1] with x hx hi
  exact hx.trans (congrArg (fun ν => ν.map (H x)) hi)

/-- If [resistance is conditionally uniform on the unit interval](hyp:hu), then
[for almost every covariate value, simultaneously for every threshold in the
unit interval and every measurable outcome set, the conditional probability
that the treated potential outcome belongs to that set and resistance does not
exceed the threshold equals the canonical treated submeasure of that set at
that threshold](goal). -/
-- @node: conditional_latent_treated_slice
lemma conditional_latent_treated_slice (M : LatentIVModel Ω X Z)
    (hu : UniformResistance M) :
    ∀ᵐ x ∂xLaw M, ∀ p ∈ Icc (0 : ℝ) 1, ∀ B : Set ℝ, MeasurableSet B →
      condDistrib (fun s => (M.U s, M.Y0 s, M.Y1 s)) M.Xv M.law.toMeasure x
        {v : ℝ × ℝ × ℝ | v.2.2 ∈ B ∧ v.1 ≤ p} =
          canonSubmeasure M true x p B := by
  let V := fun s => (M.U s, M.Y0 s, M.Y1 s)
  let proj := fun v : ℝ × ℝ × ℝ => (v.1, v.2.2)
  have hV : Measurable V := by
    first | fun_prop | exact M.measU.prodMk (M.measY0.prodMk M.measY1)
  have hproj : Measurable proj := by fun_prop
  have hcomp := condDistrib_comp (μ := M.law.toMeasure) (mβ := inferInstance)
    M.Xv hV.aemeasurable hproj
  let K := outcomeKernel (latentMarginal M true)
  let := outcomeKernel_isMarkov (latentMarginal M true)
  filter_upwards [hcomp, latent_conditional_uniform_disintegration M hu true]
    with x hx hl
  have he : (condDistrib V M.Xv M.law.toMeasure x).map proj =
      ((Kernel.const X Causalean.Stat.unifOI) ⊗ₖ
        (K.comap (Prod.swap : X × ℝ → ℝ × X) measurable_swap)) x := by
    rw [Kernel.map_apply _ hproj] at hx
    exact hx.symm.trans hl
  intro p hp B hB
  let E := {uy : ℝ × ℝ | uy.2 ∈ B ∧ uy.1 ≤ p}
  have hE : MeasurableSet E :=
    (hB.preimage measurable_snd).inter (measurableSet_le measurable_fst measurable_const)
  have hrestrict : Causalean.Stat.unifOI.restrict (Iic p) =
      volume.restrict (Ioc 0 p) := by
    rw [Causalean.Stat.unifOI, Measure.restrict_restrict measurableSet_Iic]
    apply Measure.restrict_congr_set
    filter_upwards [volume.ae_ne (1 : ℝ)] with u hu
    apply propext
    change (u ≤ p ∧ 0 < u ∧ u < 1) ↔ (0 < u ∧ u ≤ p)
    constructor
    · rintro ⟨hup, h0, h1⟩
      exact ⟨h0, hup⟩
    · rintro ⟨h0, hup⟩
      exact ⟨hup, h0, lt_of_le_of_ne (hup.trans hp.2) hu⟩
  calc
    _ = ((condDistrib V M.Xv M.law.toMeasure x).map proj) E := by
      rw [Measure.map_apply hproj hE]
      rfl
    _ = ∫⁻ u, K (u, x) {y | (u, y) ∈ E} ∂Causalean.Stat.unifOI := by
      rw [he, Kernel.compProd_apply hE]
      rfl
    _ = ∫⁻ u in Iic p, K (u, x) B ∂Causalean.Stat.unifOI := by
      rw [← lintegral_indicator measurableSet_Iic]
      apply lintegral_congr
      intro u
      by_cases ht : u ≤ p <;> simp [E, ht]
    _ = canonSubmeasure M true x p B := by
      rw [hrestrict, canonSubmeasure, Measure.bind_apply hB (by fun_prop)]
      rfl

/-- For [a measurable propensity function](hyp:hp), [a measurable instrument
window](hyp:hD), and [a measurable outcome set](hyp:hB), [the outcome mass in that
set obtained from the product of an instrument measure and a sigma-finite joint
measure of resistance and potential outcomes, after threshold assignment and
restriction to treated observations in the window, equals the integral over the
window of the latent mass with treated potential outcome in the set and
resistance below or equal to the instrument-specific propensity](goal). -/
-- @node: threshold_selection_product_evaluation
lemma threshold_selection_product_evaluation
    (μz : Measure Z) (ν : Measure (ℝ × ℝ × ℝ)) [SFinite ν]
    (p : Z → ℝ) (hp : Measurable p) (D : Set Z) (hD : MeasurableSet D)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (((μz.prod ν).map
      (fun zv => (if zv.2.1 ≤ p zv.1 then zv.2.2.2 else zv.2.2.1,
        if zv.2.1 ≤ p zv.1 then (1 : ℝ) else 0, zv.1))).restrict
        {o : ℝ × ℝ × Z | o.2.1 = 1 ∧ o.2.2 ∈ D}).map Prod.fst B =
      ∫⁻ z in D, ν {v : ℝ × ℝ × ℝ | v.2.2 ∈ B ∧ v.1 ≤ p z} ∂μz := by
  let F := fun zv : Z × (ℝ × ℝ × ℝ) =>
    (if zv.2.1 ≤ p zv.1 then zv.2.2.2 else zv.2.2.1,
      if zv.2.1 ≤ p zv.1 then (1 : ℝ) else 0, zv.1)
  have hF : Measurable F := by
    first | fun_prop | exact (
      (measurable_snd.snd.snd.ite
        (measurableSet_le measurable_snd.fst (hp.comp measurable_fst))
        measurable_snd.snd.fst).prodMk
      ((measurable_const.ite
        (measurableSet_le measurable_snd.fst (hp.comp measurable_fst))
        measurable_const).prodMk measurable_fst))
  have hE : MeasurableSet {o : ℝ × ℝ × Z | o.2.1 = 1 ∧ o.2.2 ∈ D} := by
    first | fun_prop | exact (
      (measurableSet_eq_fun measurable_snd.fst measurable_const).inter
        (hD.preimage measurable_snd.snd))
  change (((μz.prod ν).map F).restrict _).map Prod.fst B = _
  rw [Measure.map_apply measurable_fst hB,
    Measure.restrict_apply (hB.preimage measurable_fst),
    Measure.map_apply hF ((hB.preimage measurable_fst).inter hE),
    Measure.prod_apply (((hB.preimage measurable_fst).inter hE).preimage hF),
    ← lintegral_indicator hD]
  apply lintegral_congr
  intro z
  by_cases hz : z ∈ D
  · rw [indicator_of_mem hz]
    congr 1
    ext v
    by_cases ht : v.1 ≤ p z <;> simp [F, ht, hz]
  · rw [indicator_of_notMem hz]
    have he : Prod.mk z ⁻¹' (F ⁻¹'
        ((Prod.fst ⁻¹' B) ∩ {o : ℝ × ℝ × Z | o.2.1 = 1 ∧ o.2.2 ∈ D})) = ∅ := by
      ext v
      simp [F, hz]
    rw [he, measure_empty]

/-- Under [the structural assumptions on the latent instrument model](hyp:h),
[for almost every covariate value, every measurable instrument window, and every
measurable outcome set, the conditional outcome mass in that set among treated
observations in the window equals the integral over the window of the canonical
treated submeasure evaluated at each instrument's true propensity, against the
conditional instrument law](goal). -/
-- @node: conditional_selected_submeasure_evaluation
lemma conditional_selected_submeasure_evaluation (M : LatentIVModel Ω X Z)
    (h : StructuralAssumptions M) :
    ∀ᵐ x ∂xLaw M, ∀ D : Set Z, MeasurableSet D →
      ∀ B : Set ℝ, MeasurableSet B →
      (((condDistrib (fun s => (M.Y s, M.W s, M.Zv s)) M.Xv M.law.toMeasure x).restrict
        {o : ℝ × ℝ × Z | o.2.1 = 1 ∧ o.2.2 ∈ D}).map Prod.fst) B =
          ∫⁻ z in D, canonSubmeasure M true x (M.prop z x) B ∂M.instKernel x := by
  filter_upwards [conditional_observed_joint_factorization M h,
    conditional_latent_treated_slice M h.2.2.2.2.1] with x hx hs
  intro D hD B hB
  rw [hx]
  have hp : Measurable (fun z => M.prop z x) := by
    first | fun_prop | exact h.2.2.2.1.2.1.comp (measurable_id.prodMk measurable_const)
  rw [threshold_selection_product_evaluation _ _ _ hp D hD B hB]
  exact lintegral_congr fun z => hs _ (M.rangeProp z x) B hB

-- @node: conditional_selected_submeasure_mass
/-- Under [the structural assumptions on the latent instrument model](hyp:h),
[for almost every covariate value and every measurable instrument window, the
conditional mass of treated observations with instrument in that window equals
the integral of the true propensity over the window against the conditional
instrument law](goal). -/
lemma conditional_selected_submeasure_mass (M : LatentIVModel Ω X Z)
    (h : StructuralAssumptions M) :
    ∀ᵐ x ∂xLaw M, ∀ D : Set Z, MeasurableSet D →
      (condDistrib (fun s => (M.Y s, M.W s, M.Zv s)) M.Xv M.law.toMeasure x).restrict
        {o : ℝ × ℝ × Z | o.2.1 = 1 ∧ o.2.2 ∈ D} univ =
          ∫⁻ z in D, ENNReal.ofReal (M.prop z x) ∂M.instKernel x := by
  filter_upwards [conditional_selected_submeasure_evaluation M h,
    canonical_submeasure_mass M h true] with x hx hm
  intro D hD
  have he := hx D hD univ MeasurableSet.univ
  rw [Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ] at he
  rw [he]
  apply lintegral_congr
  intro z
  simpa only [Bool.true_eq, ite_true] using hm _ (M.rangeProp z x)

end Papers.TbsPrteOptimalTransport

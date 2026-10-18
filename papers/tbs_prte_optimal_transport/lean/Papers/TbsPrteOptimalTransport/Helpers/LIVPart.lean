module
public import Papers.TbsPrteOptimalTransport.Helpers.RangeRegularity
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
/-! LIVPart shared proof obligations. -/
public section
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.whitespace false
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

-- @node: outcome_norm_le_magnitude
/-- If [the designated outcome endpoints are the minimum and maximum of the outcome domain](hyp:he)
and [an outcome belongs to that domain](hyp:hy), then [its absolute value is at most the larger
absolute value of the two endpoints](goal). -/
lemma outcome_norm_le_magnitude (he : OutcomeEndpointsKnown M) {y : ℝ}
    (hy : y ∈ M.Yset) : ‖y‖ ≤ outcomeMagnitude M := by
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · have hlo := he.1.2 hy
    have hb : |M.yMin| ≤ outcomeMagnitude M := le_max_left _ _
    linarith [neg_abs_le M.yMin]
  · have hhi := he.2.2 hy
    have hb : |M.yMax| ≤ outcomeMagnitude M := le_max_right _ _
    linarith [le_abs_self M.yMax]

-- @node: supported_outcome_norm_bound
/-- Under [the structural model assumptions](hyp:h), if [the outcome endpoints are known](hyp:he)
and [a measure assigns zero mass outside the outcome domain](hyp:hs), then [almost every outcome
under that measure has absolute value at most the larger absolute outcome endpoint](goal). -/
lemma supported_outcome_norm_bound (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) (mu : Measure ℝ) (hs : mu M.Ysetᶜ = 0) :
    ∀ᵐ y ∂mu, ‖y‖ ≤ outcomeMagnitude M := by
  have hy : ∀ᵐ y ∂mu, y ∈ M.Yset :=
    (ae_iff.mpr (by
      rw [show {y | y ∉ M.Yset} = M.Ysetᶜ from Set.ext fun _ => Iff.rfl]
      exact hs))
  exact hy.mono fun y hy => outcome_norm_le_magnitude M he hy

-- @node: canonical_regression_increment_bound
/-- Under [the structural model assumptions](hyp:h) and [known outcome endpoints](hyp:he), suppose
[the lower propensity lies in the unit interval](hyp:ha), [the upper propensity does too](hyp:hb),
[the lower does not exceed the upper](hyp:hab), and [the canonical treated submeasures at the lower](hyp:hsa)
and [upper propensities are supported on the outcome domain](hyp:hsb). Then [the absolute change in
the canonical treated regression is at most the larger absolute outcome endpoint times the propensity increase](goal). -/
lemma canonical_regression_increment_bound (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) (x : X) (a b : ℝ)
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) (hab : a ≤ b)
    (hsa : canonSubmeasure M true x a M.Ysetᶜ = 0)
    (hsb : canonSubmeasure M true x b M.Ysetᶜ = 0) :
    |g1Canon M b x - g1Canon M a x| ≤ outcomeMagnitude M * (b-a) := by
  let K := (outcomeKernel (latentMarginal M true)).comap
    (fun u : ℝ => (u,x)) (by fun_prop)
  letI := outcomeKernel_isMarkov (latentMarginal M true)
  let mu := (volume.restrict (Ioc 0 a)).bind K
  let nu := (volume.restrict (Ioc a b)).bind K
  letI : IsFiniteMeasure mu := ⟨(interval_kernel_finite K 0 a).lt_top⟩
  letI : IsFiniteMeasure nu := ⟨(interval_kernel_finite K a b).lt_top⟩
  have hadd : canonSubmeasure M true x b = mu + nu :=
    interval_kernel_add K 0 a b ha.1 hab
  have hnu : nu M.Ysetᶜ = 0 := by
    apply le_zero_iff.mp
    calc
      nu M.Ysetᶜ ≤ (mu + nu) M.Ysetᶜ := Measure.le_add_left le_rfl _
      _ = 0 := by rw [← hadd]; exact hsb
  have hmuBound := supported_outcome_norm_bound M h he mu hsa
  have hnuBound := supported_outcome_norm_bound M h he nu hnu
  have hmuInt : Integrable (fun y : ℝ => y) mu := by
    apply Integrable.of_bound (by fun_prop) (outcomeMagnitude M) hmuBound
  have hnuInt : Integrable (fun y : ℝ => y) nu := by
    apply Integrable.of_bound (by fun_prop) (outcomeMagnitude M) hnuBound
  change |(∫ y, y ∂canonSubmeasure M true x b) - (∫ y, y ∂mu)| ≤ _
  rw [hadd, integral_add_measure hmuInt hnuInt, add_sub_cancel_left]
  have hmass : nu.real univ = b-a := by
    rw [measureReal_def, interval_kernel_mass K a b, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
  simpa only [Real.norm_eq_abs, hmass] using norm_integral_le_of_norm_le_const hnuBound

-- @node: canonical_regression_lipschitz
/-- Under [the structural model assumptions](hyp:h) and [known outcome endpoints](hyp:he),
[for almost every covariate value, the absolute difference in canonical treated regressions at any
two propensities in the unit interval is at most their distance times the larger absolute outcome endpoint](goal). -/
lemma canonical_regression_lipschitz (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M) :
    ∀ᵐ x ∂xLaw M, ∀ p ∈ Icc (0:ℝ) 1, ∀ p' ∈ Icc (0:ℝ) 1,
      |g1Canon M p x - g1Canon M p' x| ≤ outcomeMagnitude M * |p-p'| := by
  filter_upwards [canonical_submeasure_supported M h true] with x hx
  intro p hp p' hp'
  rcases le_total p p' with hpp | hpp
  · rw [abs_sub_comm (g1Canon M p x), abs_sub_comm p p',
      abs_of_nonneg (sub_nonneg.mpr hpp)]
    exact canonical_regression_increment_bound M h he x p p' hp hp' hpp (hx p hp) (hx p' hp')
  · rw [abs_of_nonneg (sub_nonneg.mpr hpp)]
    exact canonical_regression_increment_bound M h he x p' p hp' hp hpp (hx p' hp') (hx p hp)

-- @node: canonical_regression_ac
/-- Under [the structural model assumptions](hyp:h) and [known outcome endpoints](hyp:he), with
[propensity continuous on each instrument component for almost every covariate value](hyp:hc)
and [finitely many connected instrument components](hyp:hfin), [the canonical treated regression
is absolutely continuous on every interval in the conditional propensity-range decomposition,
for almost every covariate value](goal). -/
lemma canonical_regression_ac (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (hc : PropensityContinuousOnComponents M) (hfin : FiniteInstrumentComponents Z) :
    ∀ᵐ x ∂xLaw M, ∀ k < (CondRangeDecomposition M x).count,
      AbsolutelyContinuousOnInterval (fun p => g1Canon M p x)
        ((CondRangeDecomposition M x).low k) ((CondRangeDecomposition M x).high k) := by
  filter_upwards [canonical_regression_lipschitz M h he] with x hx
  intro k hk
  let D := CondRangeDecomposition M x
  have hD : D.Valid (range (fun z => M.prop z x)) := by
    change (RangeDecomposition (range (fun z => M.prop z x))).Valid _
    unfold RangeDecomposition
    split
    · exact Classical.choose_spec _
    · change k < (CondRangeDecomposition M x).count at hk
      simp only [CondRangeDecomposition, RangeDecomposition, dif_neg ‹_›,
        RangeData.count] at hk
      omega
  have hk' : k < D.1 := hk
  have heD := hD.1 ⟨k, hk'⟩
  have hlohi : D.low k ≤ D.high k := by
    simpa only [RangeData.low, RangeData.high, dif_pos hk'] using heD.2.1
  have hsubset : uIcc (D.low k) (D.high k) ⊆ Icc (0 : ℝ) 1 := by
    rw [uIcc_of_le hlohi]
    exact liv_interval_range D _ hD ⟨k, hk⟩
  let B : NNReal := NNReal.mk (outcomeMagnitude M)
    (le_trans (abs_nonneg _) (le_max_left _ _))
  have hLip : LipschitzOnWith B (fun p => g1Canon M p x) (uIcc (D.low k) (D.high k)) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro p hp p' hp'
    simpa only [Real.dist_eq, B, NNReal.coe_mk] using hx p (hsubset hp) p' (hsubset hp')
  exact hLip.absolutelyContinuousOnInterval

-- @node: bounded_weighted_disintegration
/-- For a finite measure, suppose [the conditioning variable is measurable](hyp:hV),
[the real outcome is measurable](hyp:hY), [the weight is integrable under the conditioning variable's
distribution](hyp:hw), and [the outcome's absolute value is almost everywhere bounded by a constant](hyp:hB).
Then [the weighted outcome is integrable under the joint distribution, its weighted conditional mean
is integrable under the conditioning distribution, and their integrals are equal](goal). -/
lemma bounded_weighted_disintegration {S A : Type*} [MeasurableSpace S]
    [MeasurableSpace A] (mu : Measure S) [IsFiniteMeasure mu]
    (V : S → A) (Y : S → ℝ) (hV : Measurable V) (hY : Measurable Y)
    (w : A → ℝ) (hw : Integrable w (mu.map V)) (B : ℝ)
    (hB : ∀ᵐ s ∂mu, ‖Y s‖ ≤ B) :
    Integrable (fun a : A × ℝ => a.2 * w a.1) (mu.map (fun s => (V s, Y s))) ∧
    Integrable (fun a => (∫ y, y ∂condDistrib Y V mu a) * w a) (mu.map V) ∧
    (∫ a, a.2 * w a.1 ∂mu.map (fun s => (V s, Y s))) =
      ∫ a, (∫ y, y ∂condDistrib Y V mu a) * w a ∂mu.map V := by
  let joint := mu.map (fun s => (V s, Y s))
  have hfst : joint.map Prod.fst = mu.map V := by
    rw [Measure.map_map measurable_fst (hV.prodMk hY)]
    rfl
  have hwj : Integrable (fun a : A × ℝ => w a.1) joint := by
    have hw' : Integrable w (joint.map Prod.fst) := by rwa [hfst]
    exact hw'.comp_measurable measurable_fst
  have hBj : ∀ᵐ a ∂joint, ‖a.2‖ ≤ B := by
    exact (ae_map_iff (hV.prodMk hY).aemeasurable
      (measurableSet_le measurable_snd.norm measurable_const)).mpr hB
  have hf := hwj.bdd_mul (measurable_snd.aestronglyMeasurable) hBj
  have hi := hf.integral_condDistrib_map hY.aemeasurable
  simp only [integral_mul_const] at hi
  refine ⟨hf, hi, ?_⟩
  have hf' : Integrable (fun a : A × ℝ => a.2 * w a.1)
      ((mu.map V) ⊗ₘ condDistrib Y V mu) := by
    rw [compProd_map_condDistrib hY.aemeasurable]
    exact hf
  rw [← compProd_map_condDistrib hY.aemeasurable,
    Measure.integral_compProd hf']
  simp only [integral_mul_const]

-- @node: mte_component_decomposition
/-- Under [the structural model assumptions](hyp:h) and [known outcome endpoints](hyp:he), if
[the target weight is jointly measurable on covariates and unit-interval resistance](hyp:hm)
and [integrable under their product distribution](hyp:hi), then [the weighted marginal-treatment-effect
target equals the treated weighted-outcome component minus the untreated component under their respective latent laws](goal). -/
lemma mte_component_decomposition (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (om : X → ℝ → ℝ) (hm : TargetWeightMeasurable om) (hi : TargetWeightIntegrable M om) :
    thetaTarget M om = thetaComp om (latentMarginal M true) - thetaComp om (latentMarginal M false) := by
  letI : IsProbabilityMeasure (xLaw M) := Measure.isProbabilityMeasure_map M.measX.aemeasurable
  let V := fun s => (M.U s, M.Xv s)
  let w := fun ux : ℝ × X => om ux.2 ux.1
  have hV : Measurable V := M.measU.prodMk M.measX
  have hlaw : M.law.toMeasure.map V = Causalean.Stat.unifOI.prod (xLaw M) :=
    uniform_resistance_joint_law M h.2.2.2.2.1
  have hi' : Integrable (Function.uncurry om) ((xLaw M).prod Causalean.Stat.unifOI) := by
    simpa only [TargetWeightIntegrable, Causalean.Stat.unifOI,
      restrict_Ioo_eq_restrict_Icc] using hi
  have hw : Integrable w (M.law.toMeasure.map V) := by
    rw [hlaw]
    exact hi'.swap
  have hb0 : ∀ᵐ s ∂M.law.toMeasure, ‖M.Y0 s‖ ≤ outcomeMagnitude M :=
    h.1.1.mono fun s hs => outcome_norm_le_magnitude M he hs
  have hb1 : ∀ᵐ s ∂M.law.toMeasure, ‖M.Y1 s‖ ≤ outcomeMagnitude M :=
    h.1.2.mono fun s hs => outcome_norm_le_magnitude M he hs
  have hbd : ∀ᵐ s ∂M.law.toMeasure, ‖M.Y1 s - M.Y0 s‖ ≤
      outcomeMagnitude M + outcomeMagnitude M := by
    filter_upwards [hb0, hb1] with s h0 h1
    exact (norm_sub_le _ _).trans (add_le_add h1 h0)
  have hd := bounded_weighted_disintegration M.law.toMeasure V
    (fun s => M.Y1 s - M.Y0 s) hV (M.measY1.sub M.measY0) w hw _ hbd
  have h0 := bounded_weighted_disintegration M.law.toMeasure V M.Y0 hV M.measY0 w hw _ hb0
  have h1 := bounded_weighted_disintegration M.law.toMeasure V M.Y1 hV M.measY1 w hw _ hb1
  have hmean : Integrable (fun ux : ℝ × X => mte M ux.2 ux.1 * w ux)
      (Causalean.Stat.unifOI.prod (xLaw M)) := by
    rw [← hlaw]
    exact hd.2.1
  have htarget : thetaTarget M om =
      ∫ ux, mte M ux.2 ux.1 * w ux ∂Causalean.Stat.unifOI.prod (xLaw M) := by
    rw [thetaTarget, integral_prod_symm _ hmean]
    simp only [w, Causalean.Stat.unifOI, restrict_Ioo_eq_restrict_Icc]
  have hraw0 : Integrable (fun s => M.Y0 s * w (V s)) M.law.toMeasure :=
    h0.1.comp_measurable (hV.prodMk M.measY0)
  have hraw1 : Integrable (fun s => M.Y1 s * w (V s)) M.law.toMeasure :=
    h1.1.comp_measurable (hV.prodMk M.measY1)
  have hcomp0 : thetaComp om (latentMarginal M false) =
      ∫ s, M.Y0 s * w (V s) ∂M.law.toMeasure := by
    exact integral_map (hV.prodMk M.measY0).aemeasurable h0.1.aestronglyMeasurable
  have hcomp1 : thetaComp om (latentMarginal M true) =
      ∫ s, M.Y1 s * w (V s) ∂M.law.toMeasure := by
    exact integral_map (hV.prodMk M.measY1).aemeasurable h1.1.aestronglyMeasurable
  rw [htarget, ← hlaw]
  change (∫ ux, (∫ y, y ∂condDistrib (fun s => M.Y1 s - M.Y0 s) V M.law.toMeasure ux) * w ux
    ∂M.law.toMeasure.map V) = _
  rw [← hd.2.2, integral_map (hV.prodMk
    (show Measurable (fun s => M.Y1 s - M.Y0 s) from M.measY1.sub M.measY0)).aemeasurable
    hd.1.aestronglyMeasurable, hcomp1, hcomp0]
  simp only [sub_mul]
  exact integral_sub hraw1 hraw0

-- @node: canonical_regression_primitive
/-- Under [the structural model assumptions](hyp:h) and [known outcome endpoints](hyp:he),
[for almost every covariate value and every propensity in the unit interval, the canonical treated
regression equals the integral from zero to that propensity of the conditional treated-outcome mean
given resistance and covariates](goal). -/
lemma canonical_regression_primitive (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) :
    ∀ᵐ x ∂xLaw M, ∀ p ∈ Icc (0 : ℝ) 1,
      g1Canon M p x = ∫ u in Ioc 0 p,
        (∫ y, y ∂outcomeKernel (latentMarginal M true) (u, x)) := by
  filter_upwards [canonical_submeasure_supported M h true] with x hx
  intro p hp
  let K := (outcomeKernel (latentMarginal M true)).comap
    (fun u : ℝ => (u, x)) (by fun_prop)
  letI := outcomeKernel_isMarkov (latentMarginal M true)
  let μ := volume.restrict (Ioc (0 : ℝ) p)
  haveI : IsFiniteMeasure (K ∘ₘ μ) := ⟨(interval_kernel_finite K 0 p).lt_top⟩
  have hi : Integrable (fun y : ℝ => y) (K ∘ₘ μ) := by
    apply Integrable.of_bound (by fun_prop) (outcomeMagnitude M)
    exact supported_outcome_norm_bound M h he _ (hx p hp)
  have hi' : Integrable (fun a : ℝ × ℝ => a.2) (μ ⊗ₘ K) :=
    (Measure.integrable_compProd_snd_iff (by fun_prop)).mpr hi
  change (∫ y, y ∂K ∘ₘ μ) = ∫ u, (∫ y, y ∂K u) ∂μ
  rw [← Measure.snd_compProd μ K, Measure.snd,
    integral_map measurable_snd.aemeasurable (by fun_prop)]
  exact Measure.integral_compProd hi'

-- @node: canonical_regression_deriv
/-- Under [the structural model assumptions](hyp:h) and [known outcome endpoints](hyp:he),
[for almost every covariate value and almost every resistance in the unit interval, the derivative
of the canonical treated regression with respect to propensity equals the conditional treated-outcome
mean at that resistance and covariate value](goal). -/
lemma canonical_regression_deriv (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) :
    ∀ᵐ x ∂xLaw M, ∀ᵐ u ∂volume.restrict (Icc (0 : ℝ) 1),
      deriv (fun p => g1Canon M p x) u =
        ∫ y, y ∂outcomeKernel (latentMarginal M true) (u, x) := by
  haveI : IsProbabilityMeasure (xLaw M) :=
    Measure.isProbabilityMeasure_map M.measX.aemeasurable
  have hs := latentOutcomeKernel_supported M h true
  have hswap : ∀ᵐ xu ∂(xLaw M).prod Causalean.Stat.unifOI,
      outcomeKernel (latentMarginal M true) (xu.2, xu.1) M.Ysetᶜ = 0 := by
    have hh : ∀ᵐ ux ∂((xLaw M).prod Causalean.Stat.unifOI).map Prod.swap,
        outcomeKernel (latentMarginal M true) ux M.Ysetᶜ = 0 := by
      rw [Measure.prod_swap]
      exact hs.mono fun _ ha => ha.2
    exact ae_of_ae_map measurable_swap.aemeasurable hh
  filter_upwards [canonical_regression_primitive M h he,
    Measure.ae_ae_of_ae_prod hswap] with x hx hsx
  let K := (outcomeKernel (latentMarginal M true)).comap
    (fun u : ℝ => (u, x)) (by fun_prop)
  letI := outcomeKernel_isMarkov (latentMarginal M true)
  let f : ℝ → ℝ := fun u => ∫ y, y ∂K u
  have hsx' : ∀ᵐ u ∂volume.restrict (Icc (0 : ℝ) 1), K u M.Ysetᶜ = 0 := by
    simpa only [K, Kernel.comap_apply, Causalean.Stat.unifOI,
      restrict_Ioo_eq_restrict_Icc] using hsx
  have hb : ∀ᵐ u ∂volume.restrict (Icc (0 : ℝ) 1), ‖f u‖ ≤ outcomeMagnitude M := by
    filter_upwards [hsx'] with u hu
    simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using
      norm_integral_le_of_norm_le_const (supported_outcome_norm_bound M h he (K u) hu)
  have hi : IntegrableOn f (Icc (0 : ℝ) 1) := by
    apply Integrable.of_bound _ (outcomeMagnitude M) hb
    exact (stronglyMeasurable_id.integral_kernel (κ := K)).aestronglyMeasurable
  have hii : IntervalIntegrable f volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr hi
  have hd := hii.ae_hasDerivAt_integral
  have hu : ∀ᵐ u ∂volume.restrict (Icc (0 : ℝ) 1), u ∈ Ioo (0 : ℝ) 1 := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [hd.filter_mono (ae_mono Measure.restrict_le_self), hu] with u hdu hu
  have hd' := hdu (by simpa using ⟨hu.1.le, hu.2.le⟩) 0 (by simp)
  have heq : (fun p => g1Canon M p x) =ᶠ[𝓝 u] (fun p => ∫ v in 0..p, f v) := by
    filter_upwards [Ioo_mem_nhds hu.1 hu.2] with p hp
    rw [hx p ⟨hp.1.le, hp.2.le⟩, intervalIntegral.integral_of_le hp.1.le]
    rfl
  exact (hd'.congr_of_eventuallyEq heq).deriv

end Papers.TbsPrteOptimalTransport

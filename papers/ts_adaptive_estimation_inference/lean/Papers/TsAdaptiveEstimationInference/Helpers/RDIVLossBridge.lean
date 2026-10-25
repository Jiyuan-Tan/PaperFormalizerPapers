module
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVOperatorBridge
/-! The uniform first-stage loss comparison from the density operator rates. -/
public section
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory Filter
variable {𝒲 X Z : Type*} [MeasurableSpace 𝒲] [MeasurableSpace X]
  [MeasurableSpace Z] (V : IVWorld 𝒲 X Z)

/-- Under [the conditional-density IV setting](hyp:hIV), [density-class
realizability](hyp:hDensity), [common-support density bounds](hyp:hBounds), and
[a hypothesis envelope of size B](hyp:hHyp) with [B nonnegative](hyp:hB), if
[the fitted density belongs to the density class](hyp:hg) and [the primal
element](hyp:h) [belongs to the hypothesis class](hyp:hh), [its fitted
conditional regression has finite second moment under the instrument law](goal). -/
-- @node: rdiv_density_operator_memLp
lemma rdiv_density_operator_memLp
    (μ : Measure X) (G : Set (X → Z → ℝ)) (g₀ g : X → Z → ℝ)
    (support : Set (X × Z)) (B c₀ CG : ℝ)
    (hIV : RDIVSetting V μ g₀) (hDensity : DensityRealizable V μ G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hHyp : HypothesisClassBounded V support B) (hB : 0 ≤ B)
    (hg : g ∈ G) (h : V.Hbar.toSubmodule) (hh : h ∈ V.H) :
    MemLp (densityOperator μ g (primalVersion V h)) 2 (V.law.map V.zOf) := by
  have hzero (x : X) (z : Z) (hx : g₀ x z = 0) : g x z = 0 := by
    have hd := rdiv_density_ratio_of_bounds G g₀ g support c₀ CG hBounds hDensity.1 hg x z
    rw [hx, mul_zero] at hd
    exact le_antisymm hd ((hDensity.2 g hg).2.1 x z)
  have hm : AEStronglyMeasurable (densityOperator μ g (primalVersion V h))
      (V.law.map V.zOf) := by
    exact rdiv_density_supported_integral_aestronglyMeasurable V μ G g₀ hIV hDensity
      (fun p => primalVersion V h p.1 * g p.1 p.2)
      (((V.primal_measurable h).comp measurable_fst).mul (hDensity.2 g hg).1)
      (by intro x z hx; simp [hzero x z hx])
  have hb := rdiv_hypothesis_density_operator_bounded V μ G g₀ g support B c₀ CG
    hDensity hBounds hHyp hB hg
  have : IsProbabilityMeasure (V.law.map V.zOf) :=
    Measure.isProbabilityMeasure_map V.measurable_z.aemeasurable
  exact MemLp.of_bound hm B (by
    filter_upwards [hb] with z hz
    simpa only [Real.norm_eq_abs] using hz h hh)

/-- For [two primal Hilbert-space elements](hyp:h,h'), [the input L2 norm of
the difference of their chosen realizations equals the Hilbert norm of their
difference](goal). -/
-- @node: rdiv_primal_difference_input_norm
lemma rdiv_primal_difference_input_norm (h h' : V.Hbar.toSubmodule) :
    inputL2Norm (V.law.map V.xOf) (primalVersion V h - primalVersion V h') = ‖h - h'‖ := by
  have he : (fun w => primalVersion V h (V.xOf w) - primalVersion V h' (V.xOf w))
      =ᵐ[V.law] (fun w => ((h - h' : V.Hbar.toSubmodule) : Lp ℝ 2 V.law) w) :=
    ((V.primal_coherent h).sub (V.primal_coherent h')).trans (Lp.coeFn_sub _ _).symm
  unfold inputL2Norm
  have hmap : (∫ x, (primalVersion V h x - primalVersion V h' x) ^ 2 ∂V.law.map V.xOf) =
      ∫ w, (primalVersion V h (V.xOf w) - primalVersion V h' (V.xOf w)) ^ 2 ∂V.law :=
    integral_map V.measurable_x.aemeasurable
      (((V.primal_measurable h).sub (V.primal_measurable h')).pow_const 2).aestronglyMeasurable
  simp only [Pi.sub_apply]
  rw [hmap]
  have hi : (∫ w, (primalVersion V h (V.xOf w) - primalVersion V h' (V.xOf w)) ^ 2
      ∂V.law) = ‖h - h'‖ ^ 2 := by
    calc
      _ = ∫ w, (((h - h' : V.Hbar.toSubmodule) : Lp ℝ 2 V.law) w) ^ 2 ∂V.law := by
        apply integral_congr_ae
        filter_upwards [he] with w hw
        rw [hw]
      _ = _ := by
        simpa only [L2.inner_def, RCLike.inner_apply, conj_trivial, ← pow_two,
          Submodule.norm_coe] using
          real_inner_self_eq_norm_sq ((h - h' : V.Hbar.toSubmodule) : Lp ℝ 2 V.law)
  exact (congrArg Real.sqrt hi).trans (Real.sqrt_sq (norm_nonneg _))

/-- If [an instrument function is almost everywhere strongly measurable under
the instrument law](hyp:hf), [both its L1 and L2 input norms equal the
corresponding norms after evaluating it on observations under the observation
law](goal). -/
-- @node: rdiv_input_norms_comp_z
lemma rdiv_input_norms_comp_z (f : Z → ℝ)
    (hf : AEStronglyMeasurable f (V.law.map V.zOf)) :
    inputL1Norm V.law (fun w => f (V.zOf w)) = inputL1Norm (V.law.map V.zOf) f ∧
    inputL2Norm V.law (fun w => f (V.zOf w)) = inputL2Norm (V.law.map V.zOf) f := by
  constructor
  · exact (integral_map V.measurable_z.aemeasurable hf.norm).symm
  · unfold inputL2Norm
    exact congrArg Real.sqrt (show (∫ w, f (V.zOf w) ^ 2 ∂V.law) =
      ∫ z, f z ^ 2 ∂V.law.map V.zOf from
        (integral_map V.measurable_z.aemeasurable (hf.pow 2)).symm)

/-- Under [the conditional-density IV setting](hyp:hIV), [density-class
realizability](hyp:hDensity), [common-support density bounds](hyp:hBounds),
[a hypothesis envelope of size B](hyp:hHyp), and [an outcome bound of size B](hyp:hY),
suppose [the selected density lies in the density class](hyp:hg), [the rate
constant is nonnegative](hyp:hC), [the radius is nonnegative](hyp:hδ), and
[mean squared Hellinger error is bounded by the rate constant times the
squared radius](hyp:hRate). Then [for every pair of hypotheses, the absolute
error in their population squared-loss difference is bounded by their Hilbert
distance times the radius times the sum of four B times the square root of
twice the rate constant times one plus the density-bound ratio, and four B
times the square root of the rate constant](goal). -/
-- @node: rdiv_conditional_population_loss_rate
lemma rdiv_conditional_population_loss_rate
    {Ω : Type*} (μ : Measure X) (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (gHat : ℕ → Ω → X → Z → ℝ) (support : Set (X × Z))
    (B c₀ CG C δ : ℝ) (n : ℕ) (ω : Ω)
    (hIV : RDIVSetting V μ g₀) (hDensity : DensityRealizable V μ G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hHyp : HypothesisClassBounded V support B) (hY : OutcomeBounded V B)
    (hg : gHat n ω ∈ G) (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hRate : (∫ z, hellingerSqDensity μ (fun x => gHat n ω x z) (fun x => g₀ x z)
      ∂V.law.map V.zOf) ≤ C * δ ^ 2) :
    ∀ h ∈ V.H, ∀ h' ∈ V.H,
      |(conditionalPopulationLoss V μ gHat n ω h - conditionalPopulationLoss V μ gHat n ω h') -
        (rdivPopulationLoss V h - rdivPopulationLoss V h')| ≤
      (4 * B * (Real.sqrt (2 * (CG / c₀ + 1)) * Real.sqrt C) +
        2 * (2 * B * Real.sqrt C)) * δ * ‖h - h'‖ := by
  intro h hh h' hh'
  have hB := hY.1
  let a := densityOperator μ (gHat n ω) (primalVersion V h)
  let a' := densityOperator μ (gHat n ω) (primalVersion V h')
  let b := densityOperator μ g₀ (primalVersion V h)
  let b' := densityOperator μ g₀ (primalVersion V h')
  let u := primalVersion V h - primalVersion V h'
  have ha := rdiv_density_operator_memLp V μ G g₀ _ support B c₀ CG
    hIV hDensity hBounds hHyp hY.1 hg h hh
  have ha' := rdiv_density_operator_memLp V μ G g₀ _ support B c₀ CG
    hIV hDensity hBounds hHyp hY.1 hg h' hh'
  have hb := rdiv_density_operator_memLp V μ G g₀ g₀ support B c₀ CG
    hIV hDensity hBounds hHyp hY.1 hDensity.1 h hh
  have hb' := rdiv_density_operator_memLp V μ G g₀ g₀ support B c₀ CG
    hIV hDensity hBounds hHyp hY.1 hDensity.1 h' hh'
  have hab := rdiv_hypothesis_density_operator_bounded V μ G g₀ _ support B c₀ CG
    hDensity hBounds hHyp hY.1 hg
  have htrue := rdiv_true_density_operator_ae_eq V μ G g₀ hIV hDensity h
  have htrue' := rdiv_true_density_operator_ae_eq V μ G g₀ hIV hDensity h'
  have hglobal := rdiv_estimated_operator_global_rate V μ G g₀ gHat support B c₀ CG C δ n ω
    hIV hDensity hBounds hHyp hY.1 hg hC hδ hRate
  have hea : inputL2Norm (V.law.map V.zOf) (a - b) ≤ (2 * B * Real.sqrt C) * δ := by
    convert hglobal h hh using 1
    unfold inputL2Norm
    congr 1
    apply integral_congr_ae
    filter_upwards [htrue] with z hz
    simp [a, b, estimatedOperator, hz]
  have hea' : inputL2Norm (V.law.map V.zOf) (a' - b') ≤ (2 * B * Real.sqrt C) * δ := by
    convert hglobal h' hh' using 1
    unfold inputL2Norm
    congr 1
    apply integral_congr_ae
    filter_upwards [htrue'] with z hz
    simp [a', b', estimatedOperator, hz]
  have hsub (g : X → Z → ℝ) (hg : g ∈ G) :
      densityOperator μ g u =ᵐ[V.law.map V.zOf]
        densityOperator μ g (primalVersion V h) - densityOperator μ g (primalVersion V h') := by
    filter_upwards [rdiv_density_integrable_of_realizable V μ G g₀ g hDensity hg] with z hzi
    exact rdiv_density_operator_sub_support μ g _ _ B support z
      (V.primal_measurable h).aestronglyMeasurable (V.primal_measurable h').aestronglyMeasurable
      hzi (fun x => (hDensity.2 g hg).2.1 x z) (hHyp h hh) (hHyp h' hh')
      (hBounds.2.2.2.2 g hg)
  have hrel := rdiv_density_operator_relative_input_rate V μ G g₀ (gHat n ω) support
    c₀ CG C δ hIV hDensity hBounds hg u
    ((V.primal_measurable h).sub (V.primal_measurable h'))
    ((rdiv_primal_input_memLp_norm V h).1.sub (rdiv_primal_input_memLp_norm V h').1)
    hC hδ hRate
  have hre : inputL1Norm (V.law.map V.zOf) ((a - b) - (a' - b')) ≤
      (Real.sqrt (2 * (CG / c₀ + 1)) * Real.sqrt C) * δ * ‖h - h'‖ := by
    rw [rdiv_primal_difference_input_norm V h h'] at hrel
    convert hrel using 1
    apply integral_congr_ae
    filter_upwards [hsub _ hg, hsub _ hDensity.1] with z hz hz'
    dsimp [a, a', b, b']
    rw [hz, hz']
    simp only [Pi.sub_apply]
    congr 1
    ring
  have hbnorm : inputL2Norm (V.law.map V.zOf) (b - b') ≤ ‖h - h'‖ := by
    have he : (fun w => (b - b') (V.zOf w)) =ᵐ[V.law]
        (fun w => ((projCondExpOp V (h - h') : V.Qbar.toSubmodule) : Lp ℝ 2 V.law) w) := by
      have he₁ : (fun w => b (V.zOf w)) =ᵐ[V.law]
          (fun w => ((projCondExpOp V h : V.Qbar.toSubmodule) : Lp ℝ 2 V.law) w) := by
        filter_upwards [ae_of_ae_map V.measurable_z.aemeasurable htrue,
          V.dual_coherent (projCondExpOp V h)] with w hw hc
        exact hw.trans hc
      have he₂ : (fun w => b' (V.zOf w)) =ᵐ[V.law]
          (fun w => ((projCondExpOp V h' : V.Qbar.toSubmodule) : Lp ℝ 2 V.law) w) := by
        filter_upwards [ae_of_ae_map V.measurable_z.aemeasurable htrue',
          V.dual_coherent (projCondExpOp V h')] with w hw hc
        exact hw.trans hc
      rw [map_sub]
      exact (he₁.sub he₂).trans (Lp.coeFn_sub _ _).symm
    have hnorm : inputL2Norm V.law (fun w => (b - b') (V.zOf w)) =
        ‖projCondExpOp V (h - h')‖ := by
      unfold inputL2Norm
      have hi := integral_congr_ae (he.fun_comp (fun x : ℝ => x ^ 2))
      dsimp only [Function.comp_def] at hi
      rw [hi]
      have hs : (∫ w, (((projCondExpOp V (h - h') : V.Qbar.toSubmodule) : Lp ℝ 2 V.law) w) ^ 2
          ∂V.law) = ‖projCondExpOp V (h - h')‖ ^ 2 := by
        simpa only [L2.inner_def, RCLike.inner_apply, conj_trivial, ← pow_two,
          Submodule.norm_coe] using real_inner_self_eq_norm_sq
          ((projCondExpOp V (h - h') : V.Qbar.toSubmodule) : Lp ℝ 2 V.law)
      rw [hs, Real.sqrt_sq (norm_nonneg _)]
    rw [← (rdiv_input_norms_comp_z V (b - b') (hb.sub hb').1).2, hnorm]
    simpa only [one_mul] using
      (projCondExpOp V).le_of_opNorm_le (projCondExpOp_norm_le_one V) (h - h')
  have hpull (f : Z → ℝ) (hf : MemLp f 2 (V.law.map V.zOf)) :
      MemLp (fun w => f (V.zOf w)) 2 V.law :=
    (memLp_map_measure_iff hf.1 V.measurable_z.aemeasurable).1 hf
  have hY2 : MemLp V.Y 2 V.law := MemLp.of_bound V.measurable_Y.aestronglyMeasurable B
    (by simpa only [Real.norm_eq_abs] using hY.2)
  have hloss := rdiv_loss_perturbation_bound V.law V.Y
    (fun w => a (V.zOf w)) (fun w => a' (V.zOf w))
    (fun w => b (V.zOf w)) (fun w => b' (V.zOf w)) B
    hY2 (hpull a ha) (hpull a' ha') (hpull b hb) (hpull b' hb') hY.2
    (ae_of_ae_map V.measurable_z.aemeasurable (hab.mono fun z hz => hz h hh))
    (ae_of_ae_map V.measurable_z.aemeasurable (hab.mono fun z hz => hz h' hh'))
  have hpop (v : V.Hbar.toSubmodule) :
      rdivPopulationLoss V v = ∫ w,
        (V.Y w - densityOperator μ g₀ (primalVersion V v) (V.zOf w)) ^ 2 ∂V.law := by
    apply integral_congr_ae
    filter_upwards [ae_of_ae_map V.measurable_z.aemeasurable
      (rdiv_true_density_operator_ae_eq V μ G g₀ hIV hDensity v)] with w hw
    rw [hw]
  rw [hpop h, hpop h']
  change |((∫ w, (V.Y w - a (V.zOf w)) ^ 2 ∂V.law) -
      ∫ w, (V.Y w - a' (V.zOf w)) ^ 2 ∂V.law) -
      ((∫ w, (V.Y w - b (V.zOf w)) ^ 2 ∂V.law) -
      ∫ w, (V.Y w - b' (V.zOf w)) ^ 2 ∂V.law)| ≤ _
  have ht₁ := (rdiv_input_norms_comp_z V ((a - b) - (a' - b'))
    (((ha.sub hb).sub (ha'.sub hb')).1)).1
  have ht₂ := (rdiv_input_norms_comp_z V (b - b') (hb.sub hb').1).2
  have ht₃ := (rdiv_input_norms_comp_z V (a - b) (ha.sub hb).1).2
  have ht₄ := (rdiv_input_norms_comp_z V (a' - b') (ha'.sub hb').1).2
  change _ ≤ 4 * B * inputL1Norm V.law (fun w => ((a - b) - (a' - b')) (V.zOf w)) +
    inputL2Norm V.law (fun w => (b - b') (V.zOf w)) *
      (inputL2Norm V.law (fun w => (a - b) (V.zOf w)) +
        inputL2Norm V.law (fun w => (a' - b') (V.zOf w))) at hloss
  rw [ht₁, ht₂, ht₃, ht₄] at hloss
  apply hloss.trans
  calc
    _ ≤ 4 * B * ((Real.sqrt (2 * (CG / c₀ + 1)) * Real.sqrt C) * δ * ‖h - h'‖) +
        ‖h - h'‖ * ((2 * B * Real.sqrt C) * δ + (2 * B * Real.sqrt C) * δ) := by
      gcongr <;> first | fun_prop | assumption | (unfold inputL2Norm; positivity)
    _ = _ := by ring

end Papers.TsAdaptiveEstimationInference

module
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVMoments
/-! Identification of the true conditional density operator and its Hilbert realization. -/
public section

namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory Filter

variable {𝒲 X Z : Type*} [MeasurableSpace 𝒲] [MeasurableSpace X]
  [MeasurableSpace Z] (V : IVWorld 𝒲 X Z)

/-- Under [the conditional-density IV setting](hyp:hIV), for [a primal
Hilbert-space element](hyp:h), [the projected conditional-expectation operator
equals ordinary L2 conditional expectation given the instruments](goal). -/
-- @node: rdiv_projCondExpOp_eq_condExpL2
lemma rdiv_projCondExpOp_eq_condExpL2 (μ : Measure X) (g₀ : X → Z → ℝ)
    (hIV : RDIVSetting V μ g₀) (h : V.Hbar.toSubmodule) :
    ((projCondExpOp V h : V.Qbar.toSubmodule) : Lp ℝ 2 V.law) =
      (condExpL2 ℝ ℝ V.measurable_z.comap_le (h : Lp ℝ 2 V.law) : Lp ℝ 2 V.law) := by
  let q := condExpL2 ℝ ℝ V.measurable_z.comap_le (h : Lp ℝ 2 V.law)
  have hq : (q : Lp ℝ 2 V.law) ∈ V.Qbar.toSubmodule := by
    rw [hIV.1]
    exact q.property
  exact congrArg Subtype.val
    (V.Qbar.toSubmodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨q, hq⟩)

/-- For any dual Hilbert-space element, [its chosen instrument realization has
finite second moment and its instrument L2 norm equals its Hilbert norm](goal). -/
-- @node: rdiv_dual_input_memLp_norm
lemma rdiv_dual_input_memLp_norm (q : V.Qbar.toSubmodule) :
    MemLp (dualVersion V q) 2 (V.law.map V.zOf) ∧
      inputL2Norm (V.law.map V.zOf) (dualVersion V q) = ‖q‖ := by
  have hm : Measurable (dualVersion V q) := V.dual_measurable q
  have hp : MemLp (fun w => dualVersion V q (V.zOf w)) 2 V.law :=
    (memLp_congr_ae (V.dual_coherent q)).2 (Lp.memLp (q : Lp ℝ 2 V.law))
  refine ⟨(memLp_map_measure_iff hm.aestronglyMeasurable V.measurable_z.aemeasurable).2 hp, ?_⟩
  have he : (∫ z, dualVersion V q z ^ 2 ∂V.law.map V.zOf) = ‖q‖ ^ 2 := by
    rw [integral_map V.measurable_z.aemeasurable (hm.pow_const 2).aestronglyMeasurable]
    calc
      _ = ∫ w, ((q : Lp ℝ 2 V.law) w) ^ 2 ∂V.law := by
        apply integral_congr_ae
        filter_upwards [V.dual_coherent q] with w hw
        exact congrArg (fun x : ℝ => x ^ 2) hw
      _ = _ := by
        simpa only [L2.inner_def, RCLike.inner_apply, conj_trivial, ← pow_two,
          Submodule.norm_coe] using (real_inner_self_eq_norm_sq (q : Lp ℝ 2 V.law))
  unfold inputL2Norm
  rw [he, Real.sqrt_sq (norm_nonneg q)]

/-- Under [the conditional-density IV setting](hyp:hIV) and [density-class
realizability](hyp:hDensity), for [a measurable input function](hyp:hu) with
[finite second moment](hyp:hu2), [the true-density regression is integrable,
and its integral over any measurable instrument set equals the input's
expectation over observations whose instruments lie in that set](goal). -/
-- @node: rdiv_true_density_setIntegral
lemma rdiv_true_density_setIntegral (μ : Measure X)
    (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (hIV : RDIVSetting V μ g₀) (hDensity : DensityRealizable V μ G g₀)
    (u : X → ℝ) (hu : Measurable u) (hu2 : MemLp u 2 (V.law.map V.xOf)) :
    Integrable (densityOperator μ g₀ u) (V.law.map V.zOf) ∧
      ∀ s : Set Z, MeasurableSet s →
        (∫ z in s, densityOperator μ g₀ u z ∂V.law.map V.zOf) =
          ∫ w in V.zOf ⁻¹' s, u (V.xOf w) ∂V.law := by
  have : IsProbabilityMeasure (V.law.map V.xOf) :=
    Measure.isProbabilityMeasure_map V.measurable_x.aemeasurable
  have hf : Measurable (fun p : X × Z => u p.1) := hu.comp measurable_fst
  have hi : Integrable (fun p : X × Z => u p.1)
      (V.law.map (fun w => (V.xOf w, V.zOf w))) := by
    apply (integrable_map_measure hf.aestronglyMeasurable
      (V.measurable_x.prodMk V.measurable_z).aemeasurable).2
    exact (integrable_map_measure hu.aestronglyMeasurable
      V.measurable_x.aemeasurable).1 (hu2.integrable (by norm_num))
  refine ⟨(rdiv_density_integral_disintegration V μ G g₀ hIV hDensity _ hf hi).2.1, ?_⟩
  intro s hs
  let f : X × Z → ℝ := (Prod.snd ⁻¹' s).indicator (fun p => u p.1)
  have hfm : Measurable f := hf.indicator (measurable_snd hs)
  have hfi : Integrable f (V.law.map (fun w => (V.xOf w, V.zOf w))) :=
    hi.indicator (measurable_snd hs)
  have he := (rdiv_density_integral_disintegration V μ G g₀ hIV hDensity f hfm hfi).2.2
  have hinner (z : Z) : (∫ x, f (x, z) * g₀ x z ∂μ) =
      s.indicator (densityOperator μ g₀ u) z := by
    by_cases hz : z ∈ s <;> simp [f, hz, densityOperator]
  simp_rw [hinner] at he
  rw [integral_indicator hs] at he
  rw [← integral_indicator (V.measurable_z hs)]
  exact he

/-- Under [the conditional-density IV setting](hyp:hIV), for [a primal
Hilbert-space element](hyp:h), [the instrument realization of its projected
operator equals, almost surely, the conditional expectation of its input
realization given the instruments](goal). -/
-- @node: rdiv_dual_operator_ae_condExp
lemma rdiv_dual_operator_ae_condExp (μ : Measure X) (g₀ : X → Z → ℝ)
    (hIV : RDIVSetting V μ g₀) (h : V.Hbar.toSubmodule) :
    (fun w => dualVersion V (projCondExpOp V h) (V.zOf w)) =ᵐ[V.law]
      V.law[(fun w => primalVersion V h (V.xOf w)) |
        MeasurableSpace.comap V.zOf inferInstance] := by
  have he := (Lp.memLp (h : Lp ℝ 2 V.law)).condExpL2_ae_eq_condExp
    (𝕜 := ℝ) V.measurable_z.comap_le
  simp only [Lp.toLp_coeFn] at he
  have hq := V.dual_coherent (projCondExpOp V h)
  rw [rdiv_projCondExpOp_eq_condExpL2 V μ g₀ hIV h] at hq
  exact hq.trans (he.trans (condExp_congr_ae (V.primal_coherent h).symm))

/-- Under [the conditional-density IV setting](hyp:hIV) and [density-class
realizability](hyp:hDensity), for [a primal Hilbert-space element](hyp:h),
[integration of its input realization against the true conditional density
equals the instrument realization of its projected operator almost everywhere
under the instrument law](goal). -/
-- @node: rdiv_true_density_operator_ae_eq
lemma rdiv_true_density_operator_ae_eq (μ : Measure X)
    (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (hIV : RDIVSetting V μ g₀) (hDensity : DensityRealizable V μ G g₀)
    (h : V.Hbar.toSubmodule) :
    densityOperator μ g₀ (primalVersion V h) =ᵐ[V.law.map V.zOf]
      dualVersion V (projCondExpOp V h) := by
  have : IsProbabilityMeasure (V.law.map V.zOf) :=
    Measure.isProbabilityMeasure_map V.measurable_z.aemeasurable
  obtain ⟨hi, hsets⟩ := rdiv_true_density_setIntegral V μ G g₀ hIV hDensity
    (primalVersion V h) (V.primal_measurable h) (rdiv_primal_input_memLp_norm V h).1
  have hqi := (rdiv_dual_input_memLp_norm V (projCondExpOp V h)).1.integrable (by norm_num)
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _ hi hqi
  intro s hs _
  rw [hsets s hs, setIntegral_map hs (show AEStronglyMeasurable (dualVersion V (projCondExpOp V h))
      (V.law.map V.zOf) from (V.dual_measurable _).aestronglyMeasurable)
    V.measurable_z.aemeasurable]
  have hce := rdiv_dual_operator_ae_condExp V μ g₀ hIV h
  calc
    _ = ∫ w in V.zOf ⁻¹' s,
        V.law[(fun w => primalVersion V h (V.xOf w)) |
          MeasurableSpace.comap V.zOf inferInstance] w ∂V.law := by
      exact (setIntegral_condExp V.measurable_z.comap_le
        (((memLp_congr_ae (V.primal_coherent h)).2 (Lp.memLp (h : Lp ℝ 2 V.law))).integrable
          (by norm_num)) ⟨s, hs, rfl⟩).symm
    _ = _ := integral_congr_ae (hce.symm.filter_mono ae_restrict_le)

/-- Under [the conditional-density IV setting](hyp:hIV), [density-class
realizability](hyp:hDensity), [common-support density bounds](hyp:hBounds), and
[a hypothesis envelope of size B](hyp:hHyp) with [B nonnegative](hyp:hB), suppose
[the selected density belongs to the density class](hyp:hg), [the rate constant
is nonnegative](hyp:hC), [the radius is nonnegative](hyp:hδ), and [mean squared
Hellinger error is at most the rate constant times the squared radius](hyp:hRate).
Then [uniformly over the hypothesis class, the instrument L2 error of the
estimated operator relative to the projected true operator is at most twice
B times the square root of the rate constant times the radius](goal). -/
-- @node: rdiv_estimated_operator_global_rate
lemma rdiv_estimated_operator_global_rate
    {Ω : Type*} (μ : Measure X) (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (gHat : ℕ → Ω → X → Z → ℝ) (support : Set (X × Z))
    (B c₀ CG C δ : ℝ) (n : ℕ) (ω : Ω)
    (hIV : RDIVSetting V μ g₀) (hDensity : DensityRealizable V μ G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hHyp : HypothesisClassBounded V support B) (hB : 0 ≤ B)
    (hg : gHat n ω ∈ G) (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hRate : (∫ z, hellingerSqDensity μ (fun x => gHat n ω x z) (fun x => g₀ x z)
      ∂V.law.map V.zOf) ≤ C * δ ^ 2) :
    ∀ h ∈ V.H, inputL2Norm (V.law.map V.zOf)
      (estimatedOperator V μ gHat n ω h - dualVersion V (projCondExpOp V h)) ≤
        (2 * B * Real.sqrt C) * δ := by
  have hgz (x : X) (z : Z) (hx : g₀ x z = 0) : gHat n ω x z = 0 := by
    have hb := rdiv_density_ratio_of_bounds G g₀ (gHat n ω) support c₀ CG
      hBounds hDensity.1 hg x z
    rw [hx, mul_zero] at hb
    exact le_antisymm hb ((hDensity.2 _ hg).2.1 x z)
  have hHm : AEStronglyMeasurable
      (fun z => hellingerSqDensity μ (fun x => gHat n ω x z) (fun x => g₀ x z))
      (V.law.map V.zOf) := by
    apply rdiv_density_supported_integral_aestronglyMeasurable V μ G g₀ hIV hDensity
      (fun p => (Real.sqrt (gHat n ω p.1 p.2) - Real.sqrt (g₀ p.1 p.2)) ^ 2)
    · exact (((hDensity.2 _ hg).1.sqrt).sub (hDensity.2 _ hDensity.1).1.sqrt).pow_const 2
    · intro x z hx
      simp [hx, hgz x z hx]
  have hm (g : X → Z → ℝ) (hg : g ∈ G)
      (hz : ∀ x z, g₀ x z = 0 → g x z = 0) (h : V.Hbar.toSubmodule) :
      AEStronglyMeasurable (densityOperator μ g (primalVersion V h)) (V.law.map V.zOf) := by
    apply rdiv_density_supported_integral_aestronglyMeasurable V μ G g₀ hIV hDensity
      (fun p => primalVersion V h p.1 * g p.1 p.2)
    · exact ((V.primal_measurable h).comp measurable_fst).mul (hDensity.2 _ hg).1
    · intro x z hx
      simp [hz x z hx]
  have hb := rdiv_hypothesis_operator_global_rate V μ G g₀ (gHat n ω) support
    B c₀ CG C δ hDensity hBounds hHyp hB hg hC hδ hHm hRate
    (fun h _ => (hm _ hg hgz h).sub (hm _ hDensity.1 (fun _ _ hx => hx) h))
  intro h hh
  have he : inputL2Norm (V.law.map V.zOf)
      (estimatedOperator V μ gHat n ω h - dualVersion V (projCondExpOp V h)) =
      inputL2Norm (V.law.map V.zOf)
        (densityOperator μ (gHat n ω) (primalVersion V h) -
          densityOperator μ g₀ (primalVersion V h)) := by
    unfold inputL2Norm
    congr 1
    apply integral_congr_ae
    filter_upwards [rdiv_true_density_operator_ae_eq V μ G g₀ hIV hDensity h] with z hz
    simp only [Pi.sub_apply, estimatedOperator, hz]
  rw [he]
  exact hb h hh

/-- Under [the conditional-density IV setting](hyp:hIV), [density-class
realizability](hyp:hDensity), and [common-support density bounds](hyp:hBounds),
take [a selected density in the class](hyp:hg) and [a primal Hilbert-space
element](hyp:h). If [the rate constant is nonnegative](hyp:hC), [the radius is
nonnegative](hyp:hδ), and [mean squared Hellinger error is at most the rate
constant times the squared radius](hyp:hRate), [the instrument L1 error of
the estimated operator relative to the projected true operator is at most the
element's norm times the radius times the square root of twice the rate
constant times one plus the density-bound ratio](goal). -/
-- @node: rdiv_estimated_operator_relative_rate
lemma rdiv_estimated_operator_relative_rate
    {Ω : Type*} (μ : Measure X) (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (gHat : ℕ → Ω → X → Z → ℝ) (support : Set (X × Z))
    (c₀ CG C δ : ℝ) (n : ℕ) (ω : Ω)
    (hIV : RDIVSetting V μ g₀) (hDensity : DensityRealizable V μ G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hg : gHat n ω ∈ G) (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hRate : (∫ z, hellingerSqDensity μ (fun x => gHat n ω x z) (fun x => g₀ x z)
      ∂V.law.map V.zOf) ≤ C * δ ^ 2) (h : V.Hbar.toSubmodule) :
    inputL1Norm (V.law.map V.zOf)
      (estimatedOperator V μ gHat n ω h - dualVersion V (projCondExpOp V h)) ≤
        (Real.sqrt (2 * (CG / c₀ + 1)) * Real.sqrt C) * δ * ‖h‖ := by
  have he : inputL1Norm (V.law.map V.zOf)
      (estimatedOperator V μ gHat n ω h - dualVersion V (projCondExpOp V h)) =
      inputL1Norm (V.law.map V.zOf)
        (densityOperator μ (gHat n ω) (primalVersion V h) -
          densityOperator μ g₀ (primalVersion V h)) := by
    apply integral_congr_ae
    filter_upwards [rdiv_true_density_operator_ae_eq V μ G g₀ hIV hDensity h] with z hz
    simp only [Pi.sub_apply, estimatedOperator, hz]
  rw [he]
  exact rdiv_hypothesis_operator_relative_rate V μ G g₀ (gHat n ω) support c₀ CG C δ
    hIV hDensity hBounds hg hC hδ hRate h

end Papers.TsAdaptiveEstimationInference

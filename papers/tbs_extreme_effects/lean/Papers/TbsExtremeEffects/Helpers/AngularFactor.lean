module
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Papers.TbsExtremeEffects.Helpers.RegularVariation
public import Toolkit.Foundations.Probability.Independence.Conditioning

/-! Averaging the angular contrast over the independent covariate marginal. -/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
variable {q d : ℕ}

-- @node: l1Norm_le_card_mul_norm
/-- The [l1 norm of a finite-dimensional vector](goal) is at most its dimension times its supremum norm. -/
lemma l1Norm_le_card_mul_norm {k : ℕ} (x : Fin k → ℝ) :
    l1Norm x ≤ (k : ℝ) * ‖x‖ := by
  unfold l1Norm
  calc
    ∑ i, |x i| ≤ ∑ _ : Fin k, ‖x‖ := Finset.sum_le_sum fun i _ => by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
    _ = _ := by simp

-- @node: angular_contrast_lipschitzOn
/-- Under [asymptotic homogeneity](hyp:hHom), the [treatment contrast is Lipschitz on bounded covariates and positive unit-l1 directions](goal), with the stated dimension-adjusted constant. -/
lemma angular_contrast_lipschitzOn (M : ExtremeModel q d)
    (hHom : AsymptoticHomogeneity M) :
    LipschitzOnWith ⟨2 * M.L * (q + d), by positivity [hHom.2.2.2.1]⟩
      (fun z : (Fin q → ℝ) × (Fin d → ℝ) => M.g z.1 true z.2 - M.g z.1 false z.2)
      ({x | l1Norm x ≤ M.R} ×ˢ positiveSphere l1Norm) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro z hz z' hz'
  have h1 := hHom.2.2.2.2 z.1 z'.1 hz.1 hz'.1 true z.2 hz.2 z'.2 hz'.2
  have h0 := hHom.2.2.2.2 z.1 z'.1 hz.1 hz'.1 false z.2 hz.2 z'.2 hz'.2
  have hq := l1Norm_le_card_mul_norm (z.1 - z'.1)
  have hd := l1Norm_le_card_mul_norm (z.2 - z'.2)
  have hx : ‖z.1 - z'.1‖ ≤ dist z z' := by
    simpa [dist_eq_norm] using norm_fst_le (z - z')
  have hs : ‖z.2 - z'.2‖ ≤ dist z z' := by
    simpa [dist_eq_norm] using norm_snd_le (z - z')
  have hsum : l1Norm (z.1 - z'.1) + l1Norm (z.2 - z'.2) ≤
      ((q : ℝ) + d) * dist z z' := by
    nlinarith [mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg q),
      mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg d)]
  rw [Real.dist_eq]
  change |(M.g z.1 true z.2 - M.g z.1 false z.2) -
    (M.g z'.1 true z'.2 - M.g z'.1 false z'.2)| ≤ _
  calc
    _ = |(M.g z.1 true z.2 - M.g z'.1 true z'.2) -
        (M.g z.1 false z.2 - M.g z'.1 false z'.2)| := by congr 1; ring
    _ ≤ _ := abs_sub _ _
    _ ≤ 2 * M.L * (l1Norm (z.1 - z'.1) + l1Norm (z.2 - z'.2)) := by linarith
    _ ≤ _ := by
      change 2 * M.L * _ ≤ (2 * M.L * ((q : ℝ) + d)) * dist z z'
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hsum (by positivity [hHom.2.2.2.1] : 0 ≤ 2 * M.L)

-- @node: isCompact_covariate_l1Ball
/-- The [covariate l1 ball of radius `R`](goal) is compact. -/
lemma isCompact_covariate_l1Ball (R : ℝ) :
    IsCompact {x : Fin q → ℝ | l1Norm x ≤ R} := by
  have hc : Continuous (l1Norm (k := q)) := by unfold l1Norm; fun_prop
  have hclosed : IsClosed {x : Fin q → ℝ | l1Norm x ≤ R} :=
    isClosed_le hc continuous_const
  apply (isCompact_Icc : IsCompact
    (Set.Icc (fun _ : Fin q => -R) (fun _ => R))).of_isClosed_subset hclosed
  intro x hx
  constructor <;> intro i
  · have hi : |x i| ≤ l1Norm x := Finset.single_le_sum (fun j _ => abs_nonneg (x j))
      (Finset.mem_univ i)
    exact (abs_le.mp (hi.trans hx)).1
  · have hi : |x i| ≤ l1Norm x := Finset.single_le_sum (fun j _ => abs_nonneg (x j))
      (Finset.mem_univ i)
    exact (abs_le.mp (hi.trans hx)).2

-- @node: angular_contrast_bounded_extension
/-- Under [asymptotic homogeneity](hyp:hHom), there [exists a bounded continuous function agreeing with the treatment contrast](goal) for covariates in the model's l1 ball and directions on the positive unit l1 sphere. -/
lemma angular_contrast_bounded_extension (M : ExtremeModel q d)
    (hHom : AsymptoticHomogeneity M) :
    ∃ H : BoundedContinuousFunction ((Fin q → ℝ) × (Fin d → ℝ)) ℝ,
      ∀ x, l1Norm x ≤ M.R → ∀ s ∈ positiveSphere l1Norm,
        H (x, s) = M.g x true s - M.g x false s := by
  obtain ⟨f, hf, heq⟩ := (angular_contrast_lipschitzOn M hHom).extend_real
  obtain ⟨C₀, hC₀⟩ := ((isCompact_covariate_l1Ball M.R).prod
    isCompact_positiveSphere_l1).exists_bound_of_continuousOn hf.continuous.continuousOn
  let C := max C₀ 0
  have hC : 0 ≤ C := le_max_right _ _
  let clipped := fun z => max (-C) (min C (f z))
  have hclip z : -C ≤ clipped z ∧ clipped z ≤ C :=
    ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  let H : BoundedContinuousFunction ((Fin q → ℝ) × (Fin d → ℝ)) ℝ :=
    BoundedContinuousFunction.mkOfBound ⟨clipped, by
      have hfc := hf.continuous
      fun_prop⟩ (2 * C) (by
      intro z z'
      change dist (clipped z) (clipped z') ≤ 2 * C
      rw [Real.dist_eq]
      exact abs_le.mpr ⟨by linarith [(hclip z).1, (hclip z').2],
        by linarith [(hclip z).2, (hclip z').1]⟩)
  refine ⟨H, ?_⟩
  intro x hx s hs
  have hbound : |f (x, s)| ≤ C := (hC₀ (x, s) ⟨hx, hs⟩).trans (le_max_left _ _)
  change max (-C) (min C (f (x, s))) = _
  rw [min_eq_right (abs_le.mp hbound).2, max_eq_right (abs_le.mp hbound).1]
  exact (heq (x := (x, s)) ⟨hx, hs⟩).symm

-- @node: continuous_covariate_average
/-- The [covariate average](goal) of a [bounded continuous contrast extension](hyp:H) varies continuously with the angular direction. -/
@[fun_prop] lemma continuous_covariate_average (M : ExtremeModel q d)
    (H : BoundedContinuousFunction ((Fin q → ℝ) × (Fin d → ℝ)) ℝ) :
    Continuous (fun s => ∫ x, H (x, s) ∂M.mu.map M.X) := by
  let : IsProbabilityMeasure (M.mu.map M.X) :=
    Measure.isProbabilityMeasure_map M.measurable_X.aemeasurable
  apply continuous_of_dominated (bound := fun _ => ‖H‖)
  · intro s
    apply Continuous.aestronglyMeasurable
    fun_prop
  · intro s
    exact Eventually.of_forall fun x => H.norm_coe_le_norm (x, s)
  · exact integrable_const _
  · apply Eventually.of_forall
    intro x
    fun_prop

-- @node: covariate_noise_independent
/-- Under [independence of the model noise](hyp:hNoise), the [covariates and noise are independent](goal). -/
lemma covariate_noise_independent (M : ExtremeModel q d) (hNoise : NoiseIndependent M) :
    IndepFun M.X M.U M.mu := by
  have h : IndepFun M.U (fun w => (M.X w, M.D w)) M.mu := hNoise
  exact (h.comp measurable_id measurable_fst).symm

-- @node: covariate_direction_tail_pair_law
/-- With [regularly varying noise](hyp:hRV) that is [independent of covariates and treatment](hyp:hNoise), the [tail-conditioned joint law of covariates and direction factors into their marginal laws](goal). -/
lemma covariate_direction_tail_pair_law (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (hNoise : NoiseIndependent M) (t : ℝ) :
    (tailLaw M t).map (fun w => (M.X w, direction M w)) =
      (M.mu.map M.X).prod ((tailLaw M t).map (direction M)) := by
  have hpos : M.mu (M.U ⁻¹' {u | t < l1Norm u}) ≠ 0 := by
    intro h
    change M.mu {w | t < radius M w} = 0 at h
    exact (tailProb_pos_of_regularVariation M hRV t).ne'
      (by simp only [tailProb, h, ENNReal.toReal_zero])
  have hset : MeasurableSet {u : Fin d → ℝ | t < l1Norm u} := by
    exact measurableSet_lt measurable_const measurable_l1Norm
  have hlaw := Toolkit.Foundations.Probability.Independence.map_prodMk_cond_preimage_eq_prod M.mu M.X M.U M.measurable_X M.measurable_U
    (covariate_noise_independent M hNoise) _ hset hpos
  let D : (Fin d → ℝ) → Fin d → ℝ := fun u i => u i / l1Norm u
  have hD : Measurable D := by fun_prop
  have hmap := congrArg (fun ν => ν.map (Prod.map id D)) hlaw
  rw [Measure.map_map (measurable_id.prodMap hD) (M.measurable_X.prodMk M.measurable_U),
    ← Measure.map_prod_map _ _ measurable_id hD, Measure.map_id,
    Measure.map_map hD M.measurable_U] at hmap
  exact hmap

-- @node: angularFactor_eq_covariate_average
/-- For [regularly varying noise](hyp:hRV), [noise independent of covariates and treatment](hyp:hNoise), [bounded covariates](hyp:hX), a [bounded continuous contrast extension](hyp:H), and its [agreement with the treatment contrast on the required domain](hyp:hH), at a [positive threshold](hyp:ht), the [angular factor equals the covariate average of that extension under the tail direction law](goal). -/
lemma angularFactor_eq_covariate_average (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (hNoise : NoiseIndependent M)
    (hX : CovariateBounded M)
    (H : BoundedContinuousFunction ((Fin q → ℝ) × (Fin d → ℝ)) ℝ)
    (hH : ∀ x, l1Norm x ≤ M.R → ∀ s ∈ positiveSphere l1Norm,
      H (x, s) = M.g x true s - M.g x false s)
    {t : ℝ} (ht : 0 < t) :
    angularFactor M t = ∫ s, (∫ x, H (x, s) ∂M.mu.map M.X)
      ∂((tailLaw M t).map (direction M)) := by
  have hxe : ∀ᵐ w ∂tailLaw M t, l1Norm (M.X w) ≤ M.R :=
    cond_absolutelyContinuous.ae_le hX.2
  have heq : angularFactor M t = ∫ w, H (M.X w, direction M w) ∂tailLaw M t := by
    apply integral_congr_ae
    filter_upwards [hxe, ae_cond_mem (μ := M.mu)
      (measurableSet_lt measurable_const (measurable_radius M))] with w hwX hw
    exact (hH _ hwX _ (direction_mem_positiveSphere M (ht.trans hw))).symm
  rw [heq, ← integral_map (M.measurable_X.prodMk (measurable_direction M)).aemeasurable
    H.continuous.aestronglyMeasurable, covariate_direction_tail_pair_law M hRV hNoise]
  let : IsProbabilityMeasure (M.mu.map M.X) :=
    Measure.isProbabilityMeasure_map M.measurable_X.aemeasurable
  let : IsProbabilityMeasure ((tailLaw M t).map (direction M)) := angular_law_probability M hRV t
  apply integral_prod_symm
  apply Integrable.mono' (integrable_const ‖H‖) H.continuous.aestronglyMeasurable
  exact Eventually.of_forall H.norm_coe_le_norm

-- @node: angularFactor_tendsto_etaTarget
/-- If the noise is [regularly varying](hyp:hRV) and [independent of covariates and treatment](hyp:hNoise), covariates are [bounded](hyp:hX), and outcomes are [asymptotically homogeneous](hyp:hHom), then the [angular factor converges to its target](goal) as the threshold grows. -/
lemma angularFactor_tendsto_etaTarget (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (hNoise : NoiseIndependent M)
    (hX : CovariateBounded M) (hHom : AsymptoticHomogeneity M) :
    Tendsto (angularFactor M) atTop (𝓝 (etaTarget M)) := by
  obtain ⟨H, hH⟩ := angular_contrast_bounded_extension M hHom
  have hlim := spectral_test_limit M hRV _ (continuous_covariate_average M H)
  have hxe : ∀ᵐ x ∂M.mu.map M.X, l1Norm x ≤ M.R := by
    apply (ae_map_iff M.measurable_X.aemeasurable ?_).mpr hX.2
    exact measurableSet_le measurable_l1Norm measurable_const
  have htarget : (∫ s, (∫ x, H (x, s) ∂M.mu.map M.X) ∂M.S) = etaTarget M := by
    apply integral_congr_ae
    filter_upwards [spectral_ae_sphere M hRV] with s hs
    apply integral_congr_ae
    filter_upwards [hxe] with x hx
    exact hH x hx s hs
  rw [htarget] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  exact (angularFactor_eq_covariate_average M hRV hNoise hX H hH ht).symm

end Papers.TbsExtremeEffects

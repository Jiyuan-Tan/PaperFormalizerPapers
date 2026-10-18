module
public import Papers.TbsPrteOptimalTransport.Helpers.FirstStageTransfer
public import Papers.TbsPrteOptimalTransport.Helpers.PluginPopulationRegularity
/-! Projected learner errors transfer to the two population regression targets. -/
public section
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

-- @node: boundedAtRate_of_three_term_bound
/-- If [D is nonnegative](hyp:hD), [the first error is bounded in probability at rate r](hyp:h₀),
[the second error has the same rate](hyp:h₁), [the third error has rate s](hyp:he), and
[the target's absolute value is bounded pointwise by the first two absolute errors plus
D times the third](hyp:hb), [the target is bounded in probability at rate r plus s](goal). -/
lemma boundedAtRate_of_three_term_bound
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (f₀ f₁ e target : ℕ → A → ℝ) (r s : ℕ → ℝ) (D : ℝ) (hD : 0 ≤ D)
    (h₀ : BoundedAtRate μ f₀ r) (h₁ : BoundedAtRate μ f₁ r)
    (he : BoundedAtRate μ e s)
    (hb : ∀ n a, |target n a| ≤ |f₀ n a| + |f₁ n a| + D * |e n a|) :
    BoundedAtRate μ target (fun n => r n + s n) := by
  refine ⟨fun n => add_nonneg (h₀.1 n) (he.1 n), ?_⟩
  intro ε hε
  obtain ⟨C₀, hC₀, hn₀⟩ := h₀.2 (ε / 3) (by positivity)
  obtain ⟨C₁, hC₁, hn₁⟩ := h₁.2 (ε / 3) (by positivity)
  obtain ⟨Cₑ, hCₑ, hnₑ⟩ := he.2 (ε / 3) (by positivity)
  let C := C₀ + C₁ + D * Cₑ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  filter_upwards [hn₀, hn₁, hnₑ] with n hn₀ hn₁ hnₑ
  have hsub : {a | C * (r n + s n) < |target n a|} ⊆
      ({a | C₀ * r n < |f₀ n a|} ∪ {a | C₁ * r n < |f₁ n a|}) ∪
        {a | Cₑ * s n < |e n a|} := by
    intro a ha
    by_contra hnot
    have hbounds := not_or.mp hnot
    have hfirst := not_or.mp hbounds.1
    have b₀ : |f₀ n a| ≤ C₀ * r n := le_of_not_gt hfirst.1
    have b₁ : |f₁ n a| ≤ C₁ * r n := le_of_not_gt hfirst.2
    have bₑ : |e n a| ≤ Cₑ * s n := le_of_not_gt hbounds.2
    have b := (hb n a).trans (add_le_add (add_le_add b₀ b₁)
      (mul_le_mul_of_nonneg_left bₑ hD))
    have hr := h₀.1 n
    have hs := he.1 n
    have hCr : C₀ + C₁ ≤ C := by dsimp [C]; linarith [mul_nonneg hD hCₑ.le]
    have hCs : D * Cₑ ≤ C := by dsimp [C]; linarith
    have b' := add_le_add (mul_le_mul_of_nonneg_right hCr hr)
      (mul_le_mul_of_nonneg_right hCs hs)
    simp only [Set.mem_setOf_eq] at ha
    nlinarith
  calc
    _ ≤ μ (({a | C₀ * r n < |f₀ n a|} ∪ {a | C₁ * r n < |f₁ n a|}) ∪
        {a | Cₑ * s n < |e n a|}) := measure_mono hsub
    _ ≤ (μ {a | C₀ * r n < |f₀ n a|} + μ {a | C₁ * r n < |f₁ n a|}) +
        μ {a | Cₑ * s n < |e n a|} :=
      (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ (ENNReal.ofReal (ε / 3) + ENNReal.ofReal (ε / 3)) +
        ENNReal.ofReal (ε / 3) := add_le_add (add_le_add hn₀ hn₁) hnₑ
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]

-- @node: projected_learner_error_integrable
/-- Under [the structural model assumptions](hyp:h) and [known outcome endpoints](hyp:hend),
if [the policy is admissible](hyp:hphi), [the fitted propensity is measurable](hyp:hp),
[the outcome learner is measurable on the unit interval and covariate space](hyp:hg),
[the fitted propensity lies in the unit interval](hyp:hpr), and [the learner is bounded
by the outcome magnitude there](hyp:hgb), [the absolute difference between the learner
at either evaluation index and the true regression at its support projection is integrable
under the joint instrument and covariate law](goal). -/
lemma projected_learner_error_integrable (M : LatentIVModel Ω X Z)
    (h : StructuralAssumptions M) (hend : OutcomeEndpointsKnown M)
    (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (p : Z → X → ℝ) (g : ℝ → X → ℝ)
    (hp : Measurable (Function.uncurry p))
    (hg : Measurable (fun tx : Icc (0 : ℝ) 1 × X => g tx.1.val tx.2))
    (hpr : ∀ z x, p z x ∈ Icc (0 : ℝ) 1)
    (hgb : ∀ t x, t ∈ Icc (0 : ℝ) 1 → |g t x| ≤ outcomeMagnitude M)
    (ell : Fin 2) :
    Integrable (fun zx => |g (evalIndex phi p ell zx.1 zx.2) zx.2 -
      g1 M (supportProjection M zx.2 (evalIndex phi p ell zx.1 zx.2)) zx.2|)
      (zxLaw M) := by
  haveI : IsProbabilityMeasure (zxLaw M) := Measure.isProbabilityMeasure_map
    (M.measZ.prodMk M.measX).aemeasurable
  have hq : Measurable (Function.uncurry (policyProp phi p)) := by
    first | fun_prop | exact hphi.1.comp (measurable_fst.prodMk
      (measurable_snd.prodMk (hp.subtype_mk (h := fun zx => hpr zx.1 zx.2))))
  have hep := propensity_endpoints_aemeasurable (zxLaw M) Prod.snd measurable_snd p hp hpr
  have hi : AEMeasurable (fun zx : Z × X => evalIndex phi p ell zx.1 zx.2)
      (zxLaw M) := by
    unfold evalIndex
    split_ifs
    · exact hep.2.min (hep.1.max hq.aemeasurable)
    · exact hp.aemeasurable
  have hir (zx : Z × X) := evaluation_indices_range phi p hpr hphi ell zx.1 zx.2
  have hpop := propensity_endpoints_aemeasurable (zxLaw M) Prod.snd measurable_snd
    M.prop h.2.2.2.1.2.1 M.rangeProp
  have hproj : AEMeasurable (fun zx : Z × X =>
      supportProjection M zx.2 (evalIndex phi p ell zx.1 zx.2)) (zxLaw M) := by
    first | fun_prop | exact hpop.2.min (hpop.1.max hi)
  have hm₁ := hg.comp_aemeasurable
    ((hi.subtype_mk (hfs := hir)).prodMk measurable_snd.aemeasurable)
  have hm₂ := (measurable_canonical_regression M).comp_aemeasurable
    (hproj.prodMk measurable_snd.aemeasurable)
  apply Integrable.of_bound (by
    simpa only [Real.norm_eq_abs, Function.comp_apply, Function.uncurry, Set.codRestrict,
      Pi.sub_apply] using (hm₁.sub hm₂).aestronglyMeasurable.norm)
    (2 * outcomeMagnitude M)
  have hmap : (zxLaw M).map Prod.snd = xLaw M := by
    rw [zxLaw, Measure.map_map measurable_snd (M.measZ.prodMk M.measX)]
    rfl
  have hx := population_regression_magnitude M h hend
  rw [← hmap] at hx
  filter_upwards [ae_of_ae_map measurable_snd.aemeasurable hx] with zx hx
  rw [Real.norm_eq_abs, abs_abs]
  have hr := support_projection_range M zx.2 (evalIndex phi p ell zx.1 zx.2)
  exact (abs_sub _ _).trans (by
    linarith [hgb _ zx.2 (hir zx), hx _ (hr.1 hr.2)])

-- @node: projected_regression_integral_error_bound
/-- Under [the structural assumptions](hyp:h) and [known outcome endpoints](hyp:hend),
for [an admissible policy](hyp:hphi) that [is Lipschitz with constant L](hyp:hL), suppose
[the fitted propensity is measurable](hyp:hp), [the outcome learner is measurable on
the unit interval and covariate space](hyp:hg), [the propensity stays in the unit interval](hyp:hpr),
and [the learner is bounded by the outcome magnitude](hyp:hgb). If [e is nonnegative](hyp:he0)
and [uniformly bounds the propensity error](hyp:he), [the integrated sum of policy and
baseline regression errors is bounded by the two integrated projected learner errors
plus twice the outcome magnitude times one plus L times e](goal). -/
lemma projected_regression_integral_error_bound (M : LatentIVModel Ω X Z)
    (h : StructuralAssumptions M) (hend : OutcomeEndpointsKnown M)
    (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (L : ℝ) (hL : PolicyLipschitz phi L)
    (p : Z → X → ℝ) (g : ℝ → X → ℝ)
    (hp : Measurable (Function.uncurry p))
    (hg : Measurable (fun tx : Icc (0 : ℝ) 1 × X => g tx.1.val tx.2))
    (hpr : ∀ z x, p z x ∈ Icc (0 : ℝ) 1)
    (hgb : ∀ t x, t ∈ Icc (0 : ℝ) 1 → |g t x| ≤ outcomeMagnitude M)
    (e : ℝ) (he0 : 0 ≤ e) (he : ∀ z x, |p z x - M.prop z x| ≤ e) :
    (∫ zx, (|g (clampPolicy p (policyProp phi p) zx.1 zx.2) zx.2 -
      g1 M (clampPolicy M.prop (policyProp phi M.prop) zx.1 zx.2) zx.2| +
      |g (p zx.1 zx.2) zx.2 - g1 M (M.prop zx.1 zx.2) zx.2|) ∂zxLaw M) ≤
    (∫ zx, |g (evalIndex phi p 0 zx.1 zx.2) zx.2 -
      g1 M (supportProjection M zx.2 (evalIndex phi p 0 zx.1 zx.2)) zx.2| ∂zxLaw M) +
    (∫ zx, |g (evalIndex phi p 1 zx.1 zx.2) zx.2 -
      g1 M (supportProjection M zx.2 (evalIndex phi p 1 zx.1 zx.2)) zx.2| ∂zxLaw M) +
      (2 * outcomeMagnitude M * (1 + L)) * e := by
  haveI : IsProbabilityMeasure (zxLaw M) := Measure.isProbabilityMeasure_map
    (M.measZ.prodMk M.measX).aemeasurable
  let F := fun (ell : Fin 2) (zx : Z × X) =>
    |g (evalIndex phi p ell zx.1 zx.2) zx.2 -
      g1 M (supportProjection M zx.2 (evalIndex phi p ell zx.1 zx.2)) zx.2|
  have hF (ell) : Integrable (F ell) (zxLaw M) :=
    projected_learner_error_integrable M h hend phi hphi p g hp hg hpr hgb ell
  have hmap : (zxLaw M).map Prod.snd = xLaw M := by
    rw [zxLaw, Measure.map_map measurable_snd (M.measZ.prodMk M.measX)]
    rfl
  have hx := projected_regression_error_bound M h hend phi L hL p hpr g e he0 he
  rw [← hmap] at hx
  have hb := ae_of_ae_map measurable_snd.aemeasurable hx
  calc
    _ ≤ ∫ zx, (F 0 zx + F 1 zx + (2 * outcomeMagnitude M * (1 + L)) * e)
        ∂zxLaw M := by
      apply integral_mono_ae
        (regression_error_integrable M h hend phi hphi p g hp hg hpr hgb)
        (((hF 0).add (hF 1)).add (integrable_const _))
      filter_upwards [hb] with zx hx
      have h₀ := hx (0 : Fin 2) zx.1
      have h₁ := hx (1 : Fin 2) zx.1
      simp only [evalIndex, Fin.zero_eta, Fin.isValue, ↓reduceIte, one_ne_zero] at h₀ h₁
      dsimp only [F]
      simp only [evalIndex, Fin.zero_eta, Fin.isValue, ↓reduceIte, one_ne_zero]
      simp only [Pi.add_apply]
      linarith
    _ = _ := by
      change (∫ zx, (F 0 + F 1) zx + (2 * outcomeMagnitude M * (1 + L)) * e
        ∂zxLaw M) = (∫ zx, F 0 zx ∂zxLaw M) + (∫ zx, F 1 zx ∂zxLaw M) + _
      rw [integral_add ((hF 0).add (hF 1)) (integrable_const _)]
      simp only [Pi.add_apply]
      rw [integral_add (hF 0) (hF 1)]
      simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]

-- @node: first_stage_regression_target_rates
/-- Under [the structural assumptions](hyp:h) and [known outcome endpoints](hyp:hend),
for [an admissible policy](hyp:hphi) with [Lipschitz constant L](hyp:hL), suppose
[every propensity estimate is measurable](hyp:hp), [every outcome learner is measurable
on the unit interval and covariate space](hyp:hg), [the propensity estimates lie in the
unit interval](hyp:hpr), and [the outcome learners lie between the outcome endpoints
enlarged to include zero](hyp:hgr). If [the uniform propensity error has rate rp](hyp:hrp)
and [the local projected outcome learner errors have rate rgloc](hyp:hloc), [the population
regression targets have rate rgloc plus rp](goal). -/
lemma first_stage_regression_target_rates (M : LatentIVModel Ω X Z)
    (μ : Measure A) (h : StructuralAssumptions M) (hend : OutcomeEndpointsKnown M)
    (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (L : ℝ) (hL : PolicyLipschitz phi L)
    (pHat : ℕ → A → Z → X → ℝ) (gHat : ℕ → A → ℝ → X → ℝ)
    (hp : ∀ n a, Measurable (Function.uncurry (pHat n a)))
    (hg : ∀ n a, Measurable (fun tx : Icc (0 : ℝ) 1 × X => gHat n a tx.1.val tx.2))
    (hpr : ∀ n a z x, pHat n a z x ∈ Icc (0 : ℝ) 1)
    (hgr : ∀ n a t x, t ∈ Icc (0 : ℝ) 1 →
      gHat n a t x ∈ Icc (min 0 M.yMin) (max 0 M.yMax))
    (rp rgloc : ℕ → ℝ) (hrp : FirstStageUniformRate M μ pHat rp)
    (hloc : OutcomeLearnerRate M μ phi pHat gHat rgloc) :
    RegressionTargetRate M μ phi pHat gHat (fun n => rgloc n + rp n) := by
  refine ⟨hgr, ?_⟩
  apply boundedAtRate_of_three_term_bound μ _ _ (uniformFirstStageError M pHat)
    _ rgloc rp (2 * outcomeMagnitude M * (1 + L))
    (by have hC := (abs_nonneg M.yMin).trans (le_max_left (|M.yMin|) (|M.yMax|));
        have hL0 := hL.1; positivity)
    (hloc 0) (hloc 1) hrp
  intro n a
  have hgb (t : ℝ) (x : X) (ht : t ∈ Icc (0 : ℝ) 1) :
      |gHat n a t x| ≤ outcomeMagnitude M := by
    have hr := hgr n a t x ht
    have hC : 0 ≤ outcomeMagnitude M := (abs_nonneg M.yMin).trans (le_max_left _ _)
    have hlo : -outcomeMagnitude M ≤ M.yMin := by
      have hm : |M.yMin| ≤ outcomeMagnitude M := le_max_left _ _
      linarith [neg_abs_le M.yMin]
    have hhi : M.yMax ≤ outcomeMagnitude M := (le_abs_self _).trans (le_max_right _ _)
    exact abs_le.mpr ⟨(le_min (by linarith) hlo).trans hr.1,
      hr.2.trans (max_le hC hhi)⟩
  have he := uniform_first_stage_error_bounds M pHat hpr n a
  have hb := projected_regression_integral_error_bound M h hend phi hphi L hL
    (pHat n a) (gHat n a) (hp n a) (hg n a) (hpr n a) hgb _ he.1 he.2
  rw [abs_of_nonneg (integral_nonneg (fun zx => add_nonneg (abs_nonneg _) (abs_nonneg _)))]
  exact hb.trans (add_le_add (add_le_add (le_abs_self _) (le_abs_self _))
    (mul_le_mul_of_nonneg_left (le_abs_self _) (by
      have hC := (abs_nonneg M.yMin).trans (le_max_left (|M.yMin|) (|M.yMax|))
      have hL0 := hL.1
      positivity)))

end Papers.TbsPrteOptimalTransport

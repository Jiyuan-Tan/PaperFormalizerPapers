module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLTailBaselineConvergence
public import Papers.TbsPrteOptimalTransport.Helpers.DMLFiniteFullScoreConvergence
public import Papers.TbsPrteOptimalTransport.Helpers.DMLPooledPolicyConvergence
/-! Second moments and L2 convergence of the complete terminal binary score.
The policy residual correction is Lipschitz on the clipped propensity domain.
Its component rates combine with the terminal baseline convergence. -/
public section
set_option linter.style.haveILetI false
set_option linter.style.openClassical false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

-- @node: policy_corrected_value_difference_bound
/-- Suppose [the value-error bound is nonnegative](hyp:hB), [the derivative-error bound is nonnegative](hyp:hD), [the reference propensity lies between zero and one](hyp:hp), and [treatment lies between zero and one](hyp:hw). If [the policy-value error is at most the value-error bound times the propensity error](hyp:hq), [the fitted derivative is bounded in absolute value by the value-error bound](hyp:hdh), and [the derivative error is at most the derivative-error bound times the propensity error](hyp:hd), [the error in the derivative-corrected policy value is at most twice the value-error bound plus the derivative-error bound, multiplied by the absolute propensity error](goal). -/
lemma policy_corrected_value_difference_bound {p ph w B D : ℝ}
    {q qh d dh : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hp : p ∈ Icc (0 : ℝ) 1) (hw : w ∈ Icc (0 : ℝ) 1)
    (hq : |qh - q| ≤ B * |ph - p|) (hdh : |dh| ≤ B)
    (hd : |dh - d| ≤ D * |ph - p|) :
    |(qh + dh * (w - ph)) - (q + d * (w - p))| ≤
      (2 * B + D) * |ph - p| := by
  have hwp : |w - p| ≤ 1 := abs_le.mpr
    ⟨by linarith [hw.1, hp.2], by linarith [hw.2, hp.1]⟩
  calc
    _ = |(qh - q) + dh * (p - ph) + (dh - d) * (w - p)| := by congr 1; ring
    _ ≤ |qh - q| + |dh| * |p - ph| + |dh - d| * |w - p| := by
      simpa only [abs_mul] using
        (abs_add_le ((qh-q) + dh*(p-ph)) ((dh-d)*(w-p))).trans
          (add_le_add (abs_add_le (qh-q) (dh*(p-ph))) le_rfl)
    _ ≤ B * |ph-p| + B * |ph-p| + (D * |ph-p|) * 1 := by
      rw [abs_sub_comm p ph]
      gcongr
    _ = _ := by ring

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- The clipping is a measurable version only: the conclusion uses the fitted
-- propensity itself, whose range is guaranteed almost everywhere.
-- @node: fitted_policy_correction_memLp
/-- If [the policy is a measurable probability-valued map](hyp:hphi), [its proposed derivative differentiates it](hyp:hd), [that derivative is uniformly bounded and Lipschitz in the propensity](hyp:hDerivative), and [the fitted binary nuisances are admissible](hyp:he), [the derivative-corrected fitted policy value restricted to any finite instrument set has a finite second moment under the observation law](goal). -/
lemma fitted_policy_correction_memLp (phi dphi : Z → X → ℝ → ℝ)
    (hphi : IsPolicyMap phi) (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e : NuisanceBin L) (he : BinAdmissible M L e)
    (G : Finset Z) :
    MemLp (fun o : Obs X Z => indicator (o.2.1 ∈ G) *
      (phi o.2.1 o.1 (e.prop o.2.1 o.1) +
        dphi o.2.1 o.1 (e.prop o.2.1 o.1) * (o.2.2.1 - e.prop o.2.1 o.1)))
      2 (observationLaw M) := by
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  obtain ⟨B, D, hB, hD, hb⟩ := hDerivative
  let pc : Z → X → ℝ := fun z x => max 0 (min 1 (e.prop z x))
  have hpc : Measurable (fun zx : Z × X => pc zx.1 zx.2) := by
    apply measurable_from_prod_countable_right
    intro z
    have hm := he.2.1 z
    dsimp only [pc]
    fun_prop
  have hpcR : ∀ z x, pc z x ∈ Icc (0 : ℝ) 1 := fun z x =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hq : Measurable (fun zx : Z × X => phi zx.1 zx.2 (pc zx.1 zx.2)) := by
    first | fun_prop | exact hphi.1.comp (measurable_fst.prodMk
      (measurable_snd.prodMk (hpc.subtype_mk (h := fun zx => hpcR zx.1 zx.2))))
  have hdq := policy_derivative_graph_measurable phi dphi hphi hd pc hpc hpcR
  have hpco : Measurable (fun o : Obs X Z => pc o.2.1 o.1) :=
    hpc.comp (measurable_snd.fst.prodMk measurable_fst)
  have hqo : Measurable (fun o : Obs X Z => phi o.2.1 o.1 (pc o.2.1 o.1)) :=
    hq.comp (measurable_snd.fst.prodMk measurable_fst)
  have hdqo : Measurable (fun o : Obs X Z => dphi o.2.1 o.1 (pc o.2.1 o.1)) :=
    hdq.comp (measurable_snd.fst.prodMk measurable_fst)
  have hev : Measurable (fun o : Obs X Z => indicator (o.2.1 ∈ G)) := by
    unfold indicator
    exact Measurable.ite (G.finite_toSet.measurableSet.preimage measurable_snd.fst)
      measurable_const measurable_const
  have hmem : MemLp (fun o : Obs X Z => indicator (o.2.1 ∈ G) *
      (phi o.2.1 o.1 (pc o.2.1 o.1) +
        dphi o.2.1 o.1 (pc o.2.1 o.1) * (o.2.2.1 - pc o.2.1 o.1)))
      2 (observationLaw M) := by
    apply MemLp.of_bound (by
      first | fun_prop | exact (hev.mul (hqo.add (hdqo.mul
        (measurable_snd.snd.fst.sub hpco)))).aestronglyMeasurable) (1 + B)
    filter_upwards [observationLaw_treatment_range M] with o ho
    have hp := hpcR o.2.1 o.1
    have hr := hphi.2 o.2.1 o.1 _ hp
    have hdb := (hb o.2.1 o.1 _ _ hp hp).1
    have hw : |o.2.2.1 - pc o.2.1 o.1| ≤ 1 :=
      abs_le.mpr ⟨by linarith [ho.1, hp.2], by linarith [ho.2, hp.1]⟩
    have hi : |indicator (o.2.1 ∈ G)| ≤ 1 := by
      unfold indicator
      split_ifs <;> norm_num
    rw [Real.norm_eq_abs, abs_mul]
    calc
      _ ≤ 1 * (|phi o.2.1 o.1 (pc o.2.1 o.1)| +
          |dphi o.2.1 o.1 (pc o.2.1 o.1)| * |o.2.2.1 - pc o.2.1 o.1|) := by
        apply mul_le_mul hi _ (abs_nonneg _) zero_le_one
        simpa only [abs_mul] using abs_add_le
          (phi o.2.1 o.1 (pc o.2.1 o.1))
          (dphi o.2.1 o.1 (pc o.2.1 o.1) * (o.2.2.1 - pc o.2.1 o.1))
      _ ≤ 1 * (1 + B * 1) := by
        gcongr
        exact (abs_of_nonneg hr.1).trans_le hr.2
      _ = _ := by ring
  apply hmem.ae_eq
  have heq : ∀ᵐ x ∂xLaw M, ∀ z, pc z x = e.prop z x := by
    filter_upwards [ae_all_iff.mpr he.1] with x hx
    intro z
    simp only [pc, min_eq_right (hx z).2, max_eq_right (hx z).1]
  filter_upwards [observationLaw_covariate_ae M _ heq] with o ho
  rw [ho o.2.1]

-- Finite instrument-specific L2 rates bound the random observed instrument
-- error, without assuming a rate for the policy correction itself.
-- @node: nuisanceRates_policy_correction_sq_tendsto_probability_zero
/-- Suppose [the policy is a measurable probability-valued map](hyp:hphi), [the proposed derivative differentiates it](hyp:hd), [the derivative is uniformly bounded and Lipschitz in the propensity](hyp:hDerivative), [the reference nuisances are admissible](hyp:he0), and [every fitted nuisance vector is admissible](hyp:heh). If [the instrument-specific propensity estimates satisfy the finite nuisance rate conditions](hyp:hrp), [the integrated squared error of the derivative-corrected policy value restricted to any finite instrument set, at even sample sizes, converges to zero in probability](goal). -/
lemma nuisanceRates_policy_correction_sq_tendsto_probability_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e0 : NuisanceBin L) (eh : ℕ → A → NuisanceBin L)
    (he0 : BinAdmissible M L e0) (heh : ∀ n a, BinAdmissible M L (eh n a))
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) e0.prop)
    (G : Finset Z) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o : Obs X Z,
        (indicator (o.2.1 ∈ G) *
          ((phi o.2.1 o.1 ((eh (2*(n+1)) a).prop o.2.1 o.1) +
              dphi o.2.1 o.1 ((eh (2*(n+1)) a).prop o.2.1 o.1) *
                (o.2.2.1 - (eh (2*(n+1)) a).prop o.2.1 o.1)) -
            (phi o.2.1 o.1 (e0.prop o.2.1 o.1) +
              dphi o.2.1 o.1 (e0.prop o.2.1 o.1) * (o.2.2.1 - e0.prop o.2.1 o.1))))^2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  obtain ⟨B, D, hB, hD, hb⟩ := hDerivative
  have hDerivative : PolicyDerivativeBoundedLipschitz dphi := ⟨B, D, hB, hD, hb⟩
  have hlip := policy_lipschitz_of_derivative_bound phi dphi hd B
    (fun z x p hp => (hb z x p p hp hp).1)
  let f := fun (z : Z) n a (o : Obs X Z) =>
    |(eh (2*(n+1)) a).prop z o.1 - e0.prop z o.1|
  have hf (z : Z) (n : ℕ) (a : A) : MemLp (f z n a) 2 (observationLaw M) := by
    simpa only [f, Real.norm_eq_abs, Function.comp_apply, Pi.sub_apply] using
      ((((fitted_prop_gammaTail_memLp M L _ (heh _ a)).1 z).sub
        ((fitted_prop_gammaTail_memLp M L e0 he0).1 z)).comp_measurePreserving
          (observationLaw_fst_measurePreserving M)).norm
  have hrs := dml_finset_sum_sq_tendsto_probability_zero μ (observationLaw M)
    Finset.univ f (fun z _ => hf z) (fun z _ => by
      simpa only [f, sq_abs] using nuisanceRates_covariate_sq_tendsto_probability_zero M μ
        e0.prop (fun n a => (eh n a).prop) (fun z => he0.2.1 z)
        (fun n a z => (heh n a).2.1 z) hrp z)
  have hc : Continuous (fun t : ℝ => (2*B+D)^2 * t) := by fun_prop
  have hrsC := Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt
    hc.continuousAt hrs
  simp only [mul_zero] at hrsC
  apply probability_zero_of_nonneg_le μ _ _ hrsC
  intro n
  apply Eventually.of_forall
  intro a
  refine ⟨integral_nonneg (fun _ => sq_nonneg _), ?_⟩
  have hmem := (fitted_policy_correction_memLp M phi dphi hphi hd hDerivative
    L _ (heh (2*(n+1)) a) G).sub
      (fitted_policy_correction_memLp M phi dphi hphi hd hDerivative L e0 he0 G)
  have hs : MemLp (fun o => ∑ z : Z, f z n a o) 2 (observationLaw M) :=
    memLp_finsetSum Finset.univ (fun z _ => hf z n a)
  have hi : Integrable (fun o : Obs X Z =>
      (indicator (o.2.1 ∈ G) *
        ((phi o.2.1 o.1 ((eh (2*(n+1)) a).prop o.2.1 o.1) +
            dphi o.2.1 o.1 ((eh (2*(n+1)) a).prop o.2.1 o.1) *
              (o.2.2.1 - (eh (2*(n+1)) a).prop o.2.1 o.1)) -
          (phi o.2.1 o.1 (e0.prop o.2.1 o.1) +
            dphi o.2.1 o.1 (e0.prop o.2.1 o.1) * (o.2.2.1 - e0.prop o.2.1 o.1))))^2)
      (observationLaw M) := by
    convert hmem.integrable_sq using 1
    funext o
    simp only [Pi.sub_apply]
    ring
  rw [← integral_const_mul]
  apply integral_mono_ae hi (hs.integrable_sq.const_mul _)
  filter_upwards [observationLaw_treatment_range M,
    observationLaw_covariate_ae M _ (ae_all_iff.mpr he0.1),
    observationLaw_covariate_ae M _ (ae_all_iff.mpr (heh (2*(n+1)) a).1)] with o hw hp hph
  have ht := policy_corrected_value_difference_bound hB hD (hp o.2.1) hw
    (hlip o.2.1 o.1 _ _ (hph o.2.1) (hp o.2.1))
    (hb o.2.1 o.1 _ _ (hph o.2.1) (hp o.2.1)).1
    (hb o.2.1 o.1 _ _ (hph o.2.1) (hp o.2.1)).2
  have hsum : |(eh (2*(n+1)) a).prop o.2.1 o.1 - e0.prop o.2.1 o.1| ≤
      ∑ z : Z, f z n a o := by
    change f o.2.1 n a o ≤ ∑ z : Z, f z n a o
    exact Finset.single_le_sum (f := fun z => f z n a o)
      (fun z _ => abs_nonneg _) (Finset.mem_univ o.2.1)
  have htotal := ht.trans (mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 2*B+D))
  dsimp only [indicator]
  split_ifs
  · simpa only [one_mul, sq_abs, mul_pow] using
      pow_le_pow_left₀ (abs_nonneg _) htotal 2
  · simp only [zero_mul, zero_pow (by norm_num : 2 ≠ 0)]
    positivity

-- @node: fitted_commonTailScore_memLp
/-- If [the policy is a measurable probability-valued map](hyp:hphi), [its proposed derivative differentiates it](hyp:hd), [the derivative is uniformly bounded and Lipschitz in the propensity](hyp:hDerivative), [the fitted nuisances are admissible](hyp:he), [the clipping constant is positive](hyp:hc), and [positive-level fitted assignment probabilities are bounded below by it almost everywhere](hyp:hclip), [the complete fitted terminal binary score has a finite second moment](goal). -/
lemma fitted_commonTailScore_memLp (phi dphi : Z → X → ℝ → ℝ)
    (hphi : IsPolicyMap phi) (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e : NuisanceBin L) (he : BinAdmissible M L e)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x) :
    MemLp (commonTailScore M phi dphi L e.prop e.pLev e.piLev e.gammaTail)
      2 (observationLaw M) := by
  have hp := fitted_policy_correction_memLp M phi dphi hphi hd hDerivative
    L e he (policyUnion L L.K 1)
  have hb := fitted_tail_baseline_memLp M L e he c hc hclip
  convert (hp.sub hb).const_mul M.yMin using 1
  funext o
  exact commonTailScore_binary_residual_split M phi dphi L e o

-- The actual policy correction and IPW baseline are assembled before taking
-- the squared error. Both inputs were derived from the component nuisances.
-- @node: nuisanceRates_commonTailScore_sq_tendsto_probability_zero
/-- Suppose [the policy is a measurable probability-valued map](hyp:hphi), [its proposed derivative differentiates it](hyp:hd), [the derivative is uniformly bounded and Lipschitz in the propensity](hyp:hDerivative), [the reference nuisances are admissible](hyp:he0), [all fitted nuisance vectors are admissible](hyp:heh), [the clipping constant is positive](hyp:hc), and [reference and fitted positive-level assignment probabilities are uniformly bounded below by it almost everywhere](hyp:hclip). If [instrument-specific propensities satisfy the finite nuisance rate conditions](hyp:hrp), [level treatment regressions satisfy those rate conditions](hyp:hrlev), [assignment probabilities satisfy those rate conditions](hyp:hrpi), and [terminal weights satisfy those rate conditions](hyp:hrg), [the integrated squared error of the complete terminal binary score at even sample sizes converges to zero in probability](goal). -/
lemma nuisanceRates_commonTailScore_sq_tendsto_probability_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e0 : NuisanceBin L) (eh : ℕ → A → NuisanceBin L)
    (he0 : BinAdmissible M L e0) (heh : ∀ n a, BinAdmissible M L (eh n a))
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a (i : PositiveIndex L.K), ∀ᵐ x ∂xLaw M,
      c ≤ e0.piLev i x ∧ c ≤ (eh n a).piLev i x)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) e0.prop)
    (hrlev : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) e0.piLev)
    (hrg : FiniteNuisanceRates M μ (fun n a (_ : Unit) => (eh n a).gammaTail)
      (fun _ => e0.gammaTail)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o,
        (commonTailScore M phi dphi L (eh (2*(n+1)) a).prop
            (eh (2*(n+1)) a).pLev (eh (2*(n+1)) a).piLev
            (eh (2*(n+1)) a).gammaTail o -
          commonTailScore M phi dphi L e0.prop e0.pLev e0.piLev e0.gammaTail o)^2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  let pol := fun (e : NuisanceBin L) (o : Obs X Z) =>
    indicator (o.2.1 ∈ policyUnion L L.K 1) *
      (phi o.2.1 o.1 (e.prop o.2.1 o.1) +
        dphi o.2.1 o.1 (e.prop o.2.1 o.1) * (o.2.2.1 - e.prop o.2.1 o.1))
  let base := fun (e : NuisanceBin L) (o : Obs X Z) =>
    indicator (o.2.1 ∈ policyUnion L L.K 1) * positiveValue e.pLev L.K o.1 +
      e.gammaTail o.1 * Rp L e L.K o
  let f := fun n a o => pol (eh (2*(n+1)) a) o - pol e0 o
  let g := fun n a o => base (eh (2*(n+1)) a) o - base e0 o
  have hf (n : ℕ) (a : A) : MemLp (f n a) 2 (observationLaw M) :=
    (fitted_policy_correction_memLp M phi dphi hphi hd hDerivative L _ (heh _ a) _).sub
      (fitted_policy_correction_memLp M phi dphi hphi hd hDerivative L e0 he0 _)
  have hg (n : ℕ) (a : A) : MemLp (g n a) 2 (observationLaw M) :=
    (fitted_tail_baseline_memLp M L _ (heh _ a) c hc
      (fun i => (hclip _ a i).mono (fun _ hx => hx.2))).sub
      (fitted_tail_baseline_memLp M L e0 he0 c hc
        (fun i => (hclip (2*(n+1)) a i).mono (fun _ hx => hx.1)))
  have hrf : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o, (f n a o)^2 ∂observationLaw M) atTop (fun _ _ => 0) := by
    simpa only [f, pol, mul_sub] using
      nuisanceRates_policy_correction_sq_tendsto_probability_zero M μ phi dphi hphi hd
        hDerivative L e0 eh he0 heh hrp (policyUnion L L.K 1)
  have hrg' := nuisanceRates_tail_baseline_sq_tendsto_probability_zero M μ L e0 eh
    he0 heh c hc hclip hrlev hrpi hrg
  have hz : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun (_ : ℕ) (_ : A) => (0 : ℝ)) atTop (fun _ _ => 0) := by
    rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm]
    intro eps heps
    simpa only [sub_self, norm_zero, not_le.mpr heps, Set.ofPred_false,
      measure_empty] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (𝓝 0))
  have hs := dml_three_term_sq_tendsto_probability_zero μ (observationLaw M)
    (fun _ _ _ => 0) f g (fun _ _ => MemLp.zero') hf hg
    (by simpa using hz) hrf hrg'
  have hm : Continuous (fun t : ℝ => M.yMin^2 * t) := by fun_prop
  have ht := Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt
    hm.continuousAt hs
  simp only [mul_zero, zero_add] at ht
  convert ht using 1
  funext n a
  rw [← integral_const_mul]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro o
  dsimp only
  rw [commonTailScore_binary_residual_split M phi dphi L (eh (2*(n+1)) a) o,
    commonTailScore_binary_residual_split M phi dphi L e0 o]
  dsimp only [f, g, pol, base]
  ring

-- @node: nuisanceRates_commonTailScore_l2_tendsto_probability_zero
/-- Suppose [the policy is a measurable probability-valued map](hyp:hphi), [its proposed derivative differentiates it](hyp:hd), [the derivative is uniformly bounded and Lipschitz in the propensity](hyp:hDerivative), [the reference nuisances are admissible](hyp:he0), [all fitted nuisance vectors are admissible](hyp:heh), [the clipping constant is positive](hyp:hc), and [reference and fitted positive-level assignment probabilities are uniformly bounded below by it almost everywhere](hyp:hclip). If [instrument-specific propensities satisfy the finite nuisance rate conditions](hyp:hrp), [level treatment regressions satisfy those rate conditions](hyp:hrlev), [assignment probabilities satisfy those rate conditions](hyp:hrpi), and [terminal weights satisfy those rate conditions](hyp:hrg), [the population L2 error of the complete terminal binary score at even sample sizes converges to zero in probability](goal). -/
lemma nuisanceRates_commonTailScore_l2_tendsto_probability_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e0 : NuisanceBin L) (eh : ℕ → A → NuisanceBin L)
    (he0 : BinAdmissible M L e0) (heh : ∀ n a, BinAdmissible M L (eh n a))
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a (i : PositiveIndex L.K), ∀ᵐ x ∂xLaw M,
      c ≤ e0.piLev i x ∧ c ≤ (eh n a).piLev i x)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) e0.prop)
    (hrlev : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) e0.piLev)
    (hrg : FiniteNuisanceRates M μ (fun n a (_ : Unit) => (eh n a).gammaTail)
      (fun _ => e0.gammaTail)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt (∫ o,
        (commonTailScore M phi dphi L (eh (2*(n+1)) a).prop
            (eh (2*(n+1)) a).pLev (eh (2*(n+1)) a).piLev
            (eh (2*(n+1)) a).gammaTail o -
          commonTailScore M phi dphi L e0.prop e0.pLev e0.piLev e0.gammaTail o)^2
        ∂observationLaw M)) atTop (fun _ _ => 0) := by
  have hs := nuisanceRates_commonTailScore_sq_tendsto_probability_zero M μ phi dphi
    hphi hd hDerivative L e0 eh he0 heh c hc hclip hrp hrlev hrpi hrg
  have hm : Continuous (fun t : ℝ => Real.sqrt t) := by fun_prop
  simpa only [Real.sqrt_zero] using
    Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt hm.continuousAt hs

end Papers.TbsPrteOptimalTransport

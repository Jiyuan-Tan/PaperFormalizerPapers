module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLTailScoreConvergence
public import Papers.TbsPrteOptimalTransport.Helpers.DMLFractionalResidualConvergence
/-! Second moments and convergence of the derivative-weighted policy residual.
Finite instrument-specific propensity rates control the numerator of RqBin;
no convergence assumption on that residual is introduced. -/
public section
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.whitespace false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

-- The derivative and treatment residual each vary with the fitted propensity.
-- @node: policy_derivative_residual_difference_bound
/-- If [B is nonnegative](hyp:hB), [D is nonnegative](hyp:hD), [the true propensity
lies between zero and one](hyp:hp), [the treatment value lies between zero and
one](hyp:hw), [the fitted derivative
has absolute value at most B](hyp:hdh), and [the derivative error is at most D
times the propensity error](hyp:hd), then [the derivative-weighted treatment
residual changes by at most B plus D times the absolute propensity error](goal). -/
lemma policy_derivative_residual_difference_bound {p ph w d dh B D : ℝ}
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hp : p ∈ Icc (0 : ℝ) 1)
    (hw : w ∈ Icc (0 : ℝ) 1) (hdh : |dh| ≤ B)
    (hd : |dh - d| ≤ D * |ph - p|) :
    |dh * (w - ph) - d * (w - p)| ≤ (B + D) * |ph - p| := by
  have hwp : |w - p| ≤ 1 := abs_le.mpr
    ⟨by linarith [hw.1, hp.2], by linarith [hw.2, hp.1]⟩
  calc
    _ = |dh * (p - ph) + (dh - d) * (w - p)| := by congr 1; ring
    _ ≤ |dh| * |p - ph| + |dh - d| * |w - p| := by
      simpa only [abs_mul] using abs_add_le (dh * (p - ph)) ((dh - d) * (w - p))
    _ ≤ B * |ph - p| + (D * |ph - p|) * 1 := by
      rw [abs_sub_comm p ph]
      gcongr
    _ = _ := by ring

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- A clipped measurable representative makes the derivative evaluable on its
-- documented domain; the conclusion is about the original fitted residual.
-- @node: fitted_policy_derivative_residual_memLp
/-- For [a valid policy map](hyp:hphi) with [the specified derivative](hyp:hd)
that is [uniformly bounded and Lipschitz in propensity](hyp:hDerivative), and
[an admissible binary nuisance fit](hyp:he), [the derivative-weighted treatment
residual restricted to any one instrument has a finite second moment under
the observation law](goal). -/
lemma fitted_policy_derivative_residual_memLp (phi dphi : Z → X → ℝ → ℝ)
    (hphi : IsPolicyMap phi) (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e : NuisanceBin L) (he : BinAdmissible M L e) (z : Z) :
    MemLp (fun o : Obs X Z => dphi z o.1 (e.prop z o.1) *
      indicator (o.2.1 = z) * (o.2.2.1 - e.prop z o.1)) 2 (observationLaw M) := by
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
  have hdq := policy_derivative_graph_measurable phi dphi hphi hd pc hpc hpcR
  have hdz : Measurable (fun o : Obs X Z => dphi z o.1 (pc z o.1)) :=
    hdq.comp (measurable_const.prodMk measurable_fst)
  have hpz : Measurable (fun o : Obs X Z => pc z o.1) :=
    hpc.comp (measurable_const.prodMk measurable_fst)
  have hi : Measurable (fun o : Obs X Z => indicator (o.2.1 = z)) := by fun_prop
  have hm : MemLp (fun o : Obs X Z => dphi z o.1 (pc z o.1) *
      indicator (o.2.1 = z) * (o.2.2.1 - pc z o.1)) 2 (observationLaw M) := by
    apply MemLp.of_bound (by
      first | fun_prop | exact ((hdz.mul hi).mul (measurable_snd.snd.fst.sub hpz)).aestronglyMeasurable) B
    filter_upwards [observationLaw_treatment_range M] with o ho
    have hr := hpcR z o.1
    have hdB := (hb z o.1 _ _ hr hr).1
    have hw : |o.2.2.1 - pc z o.1| ≤ 1 := abs_le.mpr
      ⟨by linarith [ho.1, hr.2], by linarith [ho.2, hr.1]⟩
    have hiB : |indicator (o.2.1 = z)| ≤ 1 := by
      unfold indicator
      split_ifs <;> norm_num
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    calc
      _ ≤ B * 1 * 1 := by gcongr
      _ = B := by ring
  apply hm.ae_eq
  filter_upwards [observationLaw_covariate_ae M _ (he.1 z)] with o ho
  have heq : pc z o.1 = e.prop z o.1 := by
    simp only [pc, min_eq_right ho.2, max_eq_right ho.1]
  rw [heq]

-- Each observed-instrument indicator is a contraction. The derivative's
-- uniform Lipschitz bound therefore converts the propensity energy directly.
-- @node: nuisanceRates_policy_derivative_residual_sq_tendsto_probability_zero
/-- For [a valid policy](hyp:hphi) with [the specified derivative](hyp:hd)
that is [uniformly bounded and Lipschitz](hyp:hDerivative), suppose [the reference
nuisances](hyp:he0) and [all fitted nuisances](hyp:heh) are admissible and
[instrument-specific propensity errors have the required quarter rate](hyp:hrp).
Then [the integrated squared error of each instrument's derivative-weighted
treatment residual, evaluated at sample sizes twice n plus two, converges to
zero in probability](goal). -/
lemma nuisanceRates_policy_derivative_residual_sq_tendsto_probability_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e0 : NuisanceBin L) (eh : ℕ → A → NuisanceBin L)
    (he0 : BinAdmissible M L e0) (heh : ∀ n a, BinAdmissible M L (eh n a))
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) e0.prop) (z : Z) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o : Obs X Z,
        (dphi z o.1 ((eh (2*(n+1)) a).prop z o.1) * indicator (o.2.1 = z) *
            (o.2.2.1 - (eh (2*(n+1)) a).prop z o.1) -
          dphi z o.1 (e0.prop z o.1) * indicator (o.2.1 = z) *
            (o.2.2.1 - e0.prop z o.1))^2 ∂observationLaw M)
      atTop (fun _ _ => 0) := by
  obtain ⟨B, D, hB, hD, hb⟩ := hDerivative
  have hDerivative : PolicyDerivativeBoundedLipschitz dphi := ⟨B, D, hB, hD, hb⟩
  have hr := nuisanceRates_covariate_sq_tendsto_probability_zero M μ e0.prop
    (fun n a => (eh n a).prop) (fun z => he0.2.1 z)
    (fun n a z => (heh n a).2.1 z) hrp z
  have hc : Continuous (fun t : ℝ => (B+D)^2*t) := by fun_prop
  have hs := Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt hc.continuousAt hr
  simp only [mul_zero] at hs
  apply probability_zero_of_nonneg_le μ _ _ hs
  intro n
  apply Eventually.of_forall
  intro a
  refine ⟨integral_nonneg (fun o => sq_nonneg _), ?_⟩
  have hi := ((fitted_policy_derivative_residual_memLp M phi dphi hphi hd hDerivative
    L _ (heh (2*(n+1)) a) z).sub
    (fitted_policy_derivative_residual_memLp M phi dphi hphi hd hDerivative L e0 he0 z)).integrable_sq
  have hp := (((fitted_prop_gammaTail_memLp M L _ (heh (2*(n+1)) a)).1 z).sub
    ((fitted_prop_gammaTail_memLp M L e0 he0).1 z)).comp_measurePreserving
      (observationLaw_fst_measurePreserving M)
  rw [← integral_const_mul]
  apply integral_mono_ae hi (hp.integrable_sq.const_mul _)
  filter_upwards [observationLaw_treatment_range M,
    observationLaw_covariate_ae M _ (he0.1 z),
    observationLaw_covariate_ae M _ ((heh (2*(n+1)) a).1 z)] with o hw hp hph
  have hbnd := policy_derivative_residual_difference_bound hB hD hp hw
    (hb z o.1 _ _ hph hp).1 (hb z o.1 _ _ hph hp).2
  dsimp only [Pi.sub_apply, Function.comp_apply]
  unfold indicator
  split_ifs
  · simpa only [mul_one, sq_abs, mul_pow] using
      pow_le_pow_left₀ (abs_nonneg _) hbnd 2
  · simp only [mul_zero, zero_mul, sub_self, zero_pow (by norm_num : 2 ≠ 0)]
    positivity

-- This is precisely the finite numerator in RqBin, with its treatment
-- centering retained rather than replaced by a policy plug-in error.
-- @node: fitted_RqBin_numerator_memLp
/-- Given [a valid policy](hyp:hphi), [its specified derivative](hyp:hd),
[a uniform boundedness and Lipschitz bound on that derivative](hyp:hDerivative),
and [admissible binary nuisances](hyp:he), [the sum of derivative-weighted
treatment residuals over the instruments in any policy level has a finite
second moment under the observation law](goal). -/
lemma fitted_RqBin_numerator_memLp (phi dphi : Z → X → ℝ → ℝ)
    (hphi : IsPolicyMap phi) (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e : NuisanceBin L) (he : BinAdmissible M L e) (k j : ℕ) :
    MemLp (fun o : Obs X Z => ∑ z ∈ L.T k j,
      dphi z o.1 (e.prop z o.1) * indicator (o.2.1 = z) *
        (o.2.2.1 - e.prop z o.1)) 2 (observationLaw M) := by
  exact memLp_finsetSum _ (fun z _ =>
    fitted_policy_derivative_residual_memLp M phi dphi hphi hd hDerivative L e he z)

-- @node: nuisanceRates_RqBin_numerator_sq_tendsto_probability_zero
/-- If [the policy is valid](hyp:hphi), [its derivative is as specified](hyp:hd)
and [uniformly bounded and Lipschitz](hyp:hDerivative), [the reference](hyp:he0)
and [every fit](hyp:heh) are admissible, and [propensities satisfy the finite
componentwise quarter-rate condition](hyp:hrp), then [the integrated squared
error of the level-specific sum of derivative-weighted treatment residuals
converges to zero in probability along sample sizes twice n plus two](goal). -/
lemma nuisanceRates_RqBin_numerator_sq_tendsto_probability_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e0 : NuisanceBin L) (eh : ℕ → A → NuisanceBin L)
    (he0 : BinAdmissible M L e0) (heh : ∀ n a, BinAdmissible M L (eh n a))
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) e0.prop) (k j : ℕ) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o : Obs X Z,
        ((∑ z ∈ L.T k j, dphi z o.1 ((eh (2*(n+1)) a).prop z o.1) *
            indicator (o.2.1 = z) * (o.2.2.1 - (eh (2*(n+1)) a).prop z o.1)) -
          ∑ z ∈ L.T k j, dphi z o.1 (e0.prop z o.1) * indicator (o.2.1 = z) *
            (o.2.2.1 - e0.prop z o.1))^2 ∂observationLaw M)
      atTop (fun _ _ => 0) := by
  have hs := dml_finset_sum_sq_tendsto_probability_zero μ (observationLaw M)
    (L.T k j) (fun z n a o =>
      dphi z o.1 ((eh (2*(n+1)) a).prop z o.1) * indicator (o.2.1 = z) *
        (o.2.2.1 - (eh (2*(n+1)) a).prop z o.1) -
      dphi z o.1 (e0.prop z o.1) * indicator (o.2.1 = z) * (o.2.2.1 - e0.prop z o.1))
    (fun z _ n a =>
      (fitted_policy_derivative_residual_memLp M phi dphi hphi hd hDerivative L _ (heh _ a) z).sub
        (fitted_policy_derivative_residual_memLp M phi dphi hphi hd hDerivative L e0 he0 z))
    (fun z _ => nuisanceRates_policy_derivative_residual_sq_tendsto_probability_zero
      M μ phi dphi hphi hd hDerivative L e0 eh he0 heh hrp z)
  simpa only [Finset.sum_sub_distrib] using hs

-- @node: fitted_RqBin_numerator_abs_bound
/-- If [B is nonnegative](hyp:hB), [the absolute policy derivative is at most B
for every propensity between zero and one](hyp:hb), and [the binary nuisances
are admissible](hyp:he), then [almost surely the absolute level-specific sum
of derivative-weighted treatment residuals is at most the number of instruments
in that level times B](goal). -/
lemma fitted_RqBin_numerator_abs_bound (dphi : Z → X → ℝ → ℝ)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ z x p, p ∈ Icc (0 : ℝ) 1 → |dphi z x p| ≤ B)
    (L : LevelData Z X) (e : NuisanceBin L) (he : BinAdmissible M L e) (k j : ℕ) :
    ∀ᵐ o ∂observationLaw M, |∑ z ∈ L.T k j,
      dphi z o.1 (e.prop z o.1) * indicator (o.2.1 = z) *
        (o.2.2.1 - e.prop z o.1)| ≤ (L.T k j).card * B := by
  filter_upwards [observationLaw_treatment_range M,
    observationLaw_covariate_ae M _ (ae_all_iff.mpr he.1)] with o hw hp
  calc
    _ ≤ ∑ z ∈ L.T k j, |dphi z o.1 (e.prop z o.1) * indicator (o.2.1 = z) *
        (o.2.2.1 - e.prop z o.1)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ z ∈ L.T k j, B := by
      apply Finset.sum_le_sum
      intro z hz
      have hr : |o.2.2.1 - e.prop z o.1| ≤ 1 := abs_le.mpr
        ⟨by linarith [hw.1, (hp z).2], by linarith [hw.2, (hp z).1]⟩
      have hi : |indicator (o.2.1 = z)| ≤ 1 := by
        unfold indicator
        split_ifs <;> norm_num
      rw [abs_mul, abs_mul]
      calc
        _ ≤ B * 1 * 1 := by gcongr; exact hb z o.1 _ (hp z)
        _ = B := by ring
    _ = _ := by simp

-- @node: dml_clipped_reciprocal_memLp
/-- For a finite measure, if [the denominator is measurable](hyp:hp) and
[almost surely bounded below by c](hyp:hclip), where [c is positive](hyp:hc),
then [its reciprocal has a finite second moment](goal). -/
lemma dml_clipped_reciprocal_memLp {B : Type*} [MeasurableSpace B]
    (ν : Measure B) [IsFiniteMeasure ν] (p : B → ℝ) (hp : Measurable p)
    (c : ℝ) (hc : 0 < c) (hclip : ∀ᵐ x ∂ν, c ≤ p x) :
    MemLp (fun x => (p x)⁻¹) 2 ν := by
  apply MemLp.of_bound (by fun_prop) (1/c)
  filter_upwards [hclip] with x hx
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hc.trans_le hx)), one_div]
  exact inv_le_inv₀ (hc.trans_le hx) hc |>.mpr hx

-- Reciprocal errors inherit squared-energy convergence from the original
-- denominator through the proved overlap Lipschitz inequality.
-- @node: dml_clipped_reciprocal_sq_tendsto_probability_zero
/-- Suppose [the reference denominator](hyp:hp) and [each fitted denominator](hyp:hph)
are measurable, [c is positive](hyp:hc), [both denominators are almost surely
at least c for every fit](hyp:hclip), [their differences have finite second
moments](hyp:hep), and [their integrated squared errors converge to zero in
probability](hyp:hr). Then [the integrated squared errors of their reciprocals
also converge to zero in probability](goal). -/
lemma dml_clipped_reciprocal_sq_tendsto_probability_zero {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B] (μ : Measure A) (ν : Measure B)
    [IsFiniteMeasure ν] (p : B → ℝ) (ph : ℕ → A → B → ℝ)
    (hp : Measurable p) (hph : ∀ n a, Measurable (ph n a))
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a, ∀ᵐ x ∂ν, c ≤ p x ∧ c ≤ ph n a x)
    (hep : ∀ n a, MemLp (fun x => ph n a x - p x) 2 ν)
    (hr : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ x, (ph n a x - p x)^2 ∂ν) atTop (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ x, ((ph n a x)⁻¹ - (p x)⁻¹)^2 ∂ν) atTop (fun _ _ => 0) := by
  have hct : Continuous (fun t : ℝ => (1 / c^2)^2*t) := by fun_prop
  have hs := Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt hct.continuousAt hr
  simp only [mul_zero] at hs
  apply probability_zero_of_nonneg_le μ _ _ hs
  intro n
  apply Eventually.of_forall
  intro a
  refine ⟨integral_nonneg (fun _ => sq_nonneg _), ?_⟩
  have hi := ((dml_clipped_reciprocal_memLp ν (ph n a) (hph n a) c hc
    ((hclip n a).mono (fun _ hx => hx.2))).sub
    (dml_clipped_reciprocal_memLp ν p hp c hc
      ((hclip n a).mono (fun _ hx => hx.1)))).integrable_sq
  rw [← integral_const_mul]
  apply integral_mono_ae hi ((hep n a).integrable_sq.const_mul _)
  filter_upwards [hclip n a] with x hx
  have hb := clipped_reciprocal_error_bound hc hx.2 hx.1
  simpa only [Pi.sub_apply, sq_abs, div_eq_mul_inv, mul_pow, one_mul, one_pow, mul_one, mul_comm] using
    pow_le_pow_left₀ (abs_nonneg _) hb 2

-- The zero-boundary convention in RqBin is preserved exactly.
-- @node: fitted_RqBin_memLp
/-- For [a valid policy](hyp:hphi) with [the specified derivative](hyp:hd)
that is [uniformly bounded and Lipschitz](hyp:hDerivative), suppose [the binary
nuisances are admissible](hyp:he), [c is positive](hyp:hc), and [all fitted
regular-level policy masses are almost surely at least c](hyp:hclip).
If [the treatment level does not exceed the maximum level](hyp:hk), then
[the binary policy residual correction has a finite second moment](goal). -/
lemma fitted_RqBin_memLp (phi dphi : Z → X → ℝ → ℝ)
    (hphi : IsPolicyMap phi) (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e : NuisanceBin L) (he : BinAdmissible M L e)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ r : RegularIndex L, ∀ᵐ x ∂xLaw M, c ≤ e.tauLev r x)
    (k j : ℕ) (hk : k ≤ L.K) :
    MemLp (RqBin dphi L e k j) 2 (observationLaw M) := by
  unfold RqBin
  split_ifs with hi
  · exact MemLp.zero'
  · have hr : k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k := ⟨hk, by omega, by omega⟩
    let r : RegularIndex L := ⟨(k,j), hr⟩
    have ht : Measurable (fun o : Obs X Z => (e.tauLev r o.1)⁻¹) := by
      first | fun_prop | have hm := (he.2.2.2.2.2.1 r).1; fun_prop
    have hn := fitted_RqBin_numerator_memLp M phi dphi hphi hd hDerivative L e he k j
    simp only [regularValue, dif_pos hr]
    apply (hn.norm.const_mul (1/c)).mono' (by
      first | fun_prop | exact ht.aestronglyMeasurable.mul hn.1)
    filter_upwards [observationLaw_covariate_ae M _ (hclip r)] with o ho
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hc.trans_le ho))]
    exact mul_le_mul_of_nonneg_right
      (by simpa only [one_div] using (inv_le_inv₀ (hc.trans_le ho) hc).mpr ho) (norm_nonneg _)

-- @node: nuisanceRates_RqBin_sq_tendsto_probability_zero
/-- For [a valid policy](hyp:hphi) with [the specified derivative](hyp:hd)
that is [uniformly bounded and Lipschitz](hyp:hDerivative), assume [reference](hyp:he0)
and [fitted](hyp:heh) nuisances are admissible, [c is positive](hyp:hc),
[reference and fitted regular policy masses are almost surely at least c](hyp:hclip),
and [propensity](hyp:hrp) and [policy-mass](hyp:hrt) errors satisfy the finite
quarter-rate conditions. For [a treatment level at most the maximum](hyp:hk),
[the integrated squared error of the binary policy residual correction tends
to zero in probability along sample sizes twice n plus two](goal). -/
lemma nuisanceRates_RqBin_sq_tendsto_probability_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e0 : NuisanceBin L) (eh : ℕ → A → NuisanceBin L)
    (he0 : BinAdmissible M L e0) (heh : ∀ n a, BinAdmissible M L (eh n a))
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a (r : RegularIndex L), ∀ᵐ x ∂xLaw M,
      c ≤ e0.tauLev r x ∧ c ≤ (eh n a).tauLev r x)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) e0.prop)
    (hrt : FiniteNuisanceRates M μ (fun n a => (eh n a).tauLev) e0.tauLev)
    (k j : ℕ) (hk : k ≤ L.K) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o, (RqBin dphi L (eh (2*(n+1)) a) k j o -
        RqBin dphi L e0 k j o)^2 ∂observationLaw M) atTop (fun _ _ => 0) := by
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  by_cases hi : j = 0 ∨ L.l k < j
  · simp only [RqBin, if_pos hi, sub_self, zero_pow (by norm_num : 2 ≠ 0), integral_zero]
    rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm]
    intro eps heps
    simpa only [sub_self, norm_zero, not_le.mpr heps, Set.ofPred_false, measure_empty] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (𝓝 0))
  have hr : k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k := ⟨hk, by omega, by omega⟩
  let r : RegularIndex L := ⟨(k,j), hr⟩
  obtain ⟨B, D, hB, hD, hb⟩ := hDerivative
  have hDerivative : PolicyDerivativeBoundedLipschitz dphi := ⟨B, D, hB, hD, hb⟩
  let N := fun (e : NuisanceBin L) (o : Obs X Z) => ∑ z ∈ L.T k j,
    dphi z o.1 (e.prop z o.1) * indicator (o.2.1 = z) * (o.2.2.1 - e.prop z o.1)
  let t := fun (e : NuisanceBin L) (o : Obs X Z) => (e.tauLev r o.1)⁻¹
  have hN (e : NuisanceBin L) (he : BinAdmissible M L e) : MemLp (N e) 2 (observationLaw M) :=
    fitted_RqBin_numerator_memLp M phi dphi hphi hd hDerivative L e he k j
  have ht (e : NuisanceBin L) (he : BinAdmissible M L e)
      (hcl : ∀ᵐ x ∂xLaw M, c ≤ e.tauLev r x) : MemLp (t e) 2 (observationLaw M) := by
    apply dml_clipped_reciprocal_memLp (observationLaw M)
      (fun o => e.tauLev r o.1) (by
        first | fun_prop | have hm := (he.2.2.2.2.2.1 r).1; fun_prop) c hc
    exact observationLaw_covariate_ae M _ hcl
  have hs := dml_ae_weighted_residual_sq_tendsto_probability_zero μ (observationLaw M)
    (N e0) (t e0) (fun n a => N (eh (2*(n+1)) a)) (fun n a => t (eh (2*(n+1)) a))
    ((L.T k j).card * B) (1/c)
    (hN e0 he0).1
    (by
      first | fun_prop | skip
      exact ((he0.2.2.2.2.2.1 r).1.comp measurable_fst).inv.aestronglyMeasurable)
    (fun n a => (hN _ (heh _ a)).1)
    (fun n a => (ht _ (heh _ a) ((hclip (2*(n+1)) a r).mono (fun _ hx => hx.2))).1)
    (fun n a => (hN _ (heh _ a)).sub (hN e0 he0))
    (fun n a => (ht _ (heh _ a) ((hclip (2*(n+1)) a r).mono (fun _ hx => hx.2))).sub
      (ht e0 he0 ((hclip (2*(n+1)) a r).mono (fun _ hx => hx.1))))
    (fun n a => fitted_RqBin_numerator_abs_bound M dphi B hB
      (fun z x p hp => (hb z x p p hp hp).1) L _ (heh _ a) k j)
    (by
      intro n a
      filter_upwards [observationLaw_covariate_ae M _ (hclip n a r)] with o ho
      dsimp only [t]
      rw [abs_of_pos (inv_pos.mpr (hc.trans_le ho.1)), one_div]
      exact (inv_le_inv₀ (hc.trans_le ho.1) hc).mpr ho.1)
    (nuisanceRates_RqBin_numerator_sq_tendsto_probability_zero M μ phi dphi hphi hd
      hDerivative L e0 eh he0 heh hrp k j)
    (by
      apply dml_clipped_reciprocal_sq_tendsto_probability_zero μ (observationLaw M)
        (fun o => e0.tauLev r o.1) (fun n a o => (eh (2*(n+1)) a).tauLev r o.1)
        (by first | fun_prop | have hm := (he0.2.2.2.2.2.1 r).1; fun_prop)
        (by
          intro n a
          first | fun_prop | skip
          exact ((heh (2*(n+1)) a).2.2.2.2.2.1 r).1.comp measurable_fst)
        c hc (fun n a => observationLaw_covariate_ae M _ (hclip (2*(n+1)) a r))
      · intro n a
        haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
        have hm (e : NuisanceBin L) (he : BinAdmissible M L e) : MemLp (e.tauLev r) 2 (xLaw M) := by
          apply MemLp.of_bound (he.2.2.2.2.2.1 r).1.aestronglyMeasurable 1
          filter_upwards [he.2.2.2.2.1 r] with x hx
          rw [Real.norm_eq_abs, abs_of_nonneg hx.1.1]
          exact hx.1.2
        exact ((hm _ (heh _ a)).sub (hm e0 he0)).comp_measurePreserving
          (observationLaw_fst_measurePreserving M)
      · exact nuisanceRates_covariate_sq_tendsto_probability_zero M μ _ _
          (fun r => (he0.2.2.2.2.2.1 r).1)
          (fun n a r => ((heh n a).2.2.2.2.2.1 r).1) hrt r)
  have hid (e : NuisanceBin L) (o : Obs X Z) : RqBin dphi L e k j o = N e o * t e o := by
    simp only [RqBin, if_neg hi, regularValue, dif_pos hr, N, t, r]
    ring
  simpa only [hid] using hs

end Papers.TbsPrteOptimalTransport

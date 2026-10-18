module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLObservedRampBandBias
public import Papers.TbsPrteOptimalTransport.Helpers.CrossedBandBoundary
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationContinuousBandSeparation
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousBandReferenceMean
/-! Quadratic control and stochastic negligibility of crossed fitted band endpoints.
Clipped endpoints bound the crossing outcome even off the outcome support. The
selected-treatment tower keeps the fitted product coefficient and denominator. -/
public section
set_option linter.style.openClassical false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: crossed_band_clipped_quadratic_bound
/-- If [the separation margin is positive](hyp:hd), [the true upper endpoint
exceeds the true lower endpoint by at least that margin](hyp:hg), [the clipping
bound is nonnegative](hyp:hB), and [the fitted lower](hyp:ha) and [upper](hyp:hb)
endpoints have absolute values at most that bound, then [the absolute outcome
on the interval created by crossed fitted endpoints is at most twice the clipping
bound divided by the squared separation margin, times the sum of squared endpoint
errors](goal). -/
lemma crossed_band_clipped_quadratic_bound (a b ah bh y delta B : ℝ)
    (hd : 0 < delta) (hg : delta ≤ b - a) (hB : 0 ≤ B)
    (ha : |ah| ≤ B) (hb : |bh| ≤ B) :
    |y * indicator (bh < y ∧ y ≤ ah)| ≤
      (2 * B / delta ^ 2) * ((ah - a) ^ 2 + (bh - b) ^ 2) := by
  by_cases hy : bh < y ∧ y ≤ ah
  · apply crossed_band_quadratic_correction_bound a b ah bh y delta B hd hg hB
    exact abs_le.mpr ⟨(abs_le.mp hb).1.trans hy.1.le, hy.2.trans (abs_le.mp ha).2⟩
  · simp only [indicator, if_neg hy, mul_zero, abs_zero]
    positivity

-- @node: population_observed_crossed_band_bias_bound
/-- Suppose [the true lower endpoint](hyp:ha), [true upper endpoint](hyp:hb),
[fitted lower endpoint](hyp:hah), [fitted upper endpoint](hyp:hbh), [weight](hyp:hw),
and [denominator](hyp:hc) are measurable, and [both endpoint errors are
square-integrable](hyp:hea,heb). If [the separation margin is positive](hyp:hd),
[the endpoint and weight bounds are nonnegative](hyp:hB,hD), [the denominator
floor is positive](hyp:hc0), [the true endpoints are separated by the margin
almost surely](hyp:hgap), [both fitted endpoints satisfy the absolute clipping
bound almost surely](hyp:hahB,hbhB), [the weight satisfies its absolute bound
almost surely](hyp:hwB), and [the denominator exceeds its floor almost surely](hyp:hclip),
then [the weighted selected-treatment outcome on the crossed fitted interval is
integrable, and its absolute mean is bounded by the weight bound divided by the
denominator floor, times twice the endpoint bound divided by the squared margin,
times the sum of the squared population L² endpoint errors](goal). -/
lemma population_observed_crossed_band_bias_bound
    (L : LevelData Z X) (i : ℕ) (a b ah bh w c : X → ℝ)
    (ha : Measurable a) (hb : Measurable b)
    (hah : Measurable ah) (hbh : Measurable bh)
    (hw : Measurable w) (hc : Measurable c)
    (hea : MemLp (fun x => ah x - a x) 2 (xLaw M))
    (heb : MemLp (fun x => bh x - b x) 2 (xLaw M))
    (delta B D c0 : ℝ) (hd : 0 < delta) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hc0 : 0 < c0)
    (hgap : ∀ᵐ x ∂xLaw M, delta ≤ b x - a x)
    (hahB : ∀ᵐ x ∂xLaw M, |ah x| ≤ B)
    (hbhB : ∀ᵐ x ∂xLaw M, |bh x| ≤ B)
    (hwB : ∀ᵐ x ∂xLaw M, |w x| ≤ D)
    (hclip : ∀ᵐ x ∂xLaw M, c0 ≤ c x) :
    Integrable (fun o : Obs X Z => w o.1 *
      (indicator (o.2.1 ∈ L.S i) * o.2.2.1 / c o.1 *
        (o.2.2.2 * indicator (bh o.1 < o.2.2.2 ∧ o.2.2.2 ≤ ah o.1))))
      (observationLaw M) ∧
    |∫ o : Obs X Z, w o.1 *
      (indicator (o.2.1 ∈ L.S i) * o.2.2.1 / c o.1 *
        (o.2.2.2 * indicator (bh o.1 < o.2.2.2 ∧ o.2.2.2 ≤ ah o.1)))
      ∂observationLaw M| ≤
      (D / c0) * (2 * B / delta ^ 2) *
        (finiteL2Error M ah a ^ 2 + finiteL2Error M bh b ^ 2) := by
  let C := 2 * B / delta ^ 2
  let H := fun x => C * ((ah x - a x) ^ 2 + (bh x - b x) ^ 2)
  let g := fun x y => y * indicator (bh x < y ∧ y ≤ ah x)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hHi : Integrable H (xLaw M) :=
    (hea.integrable_sq.fun_add heb.integrable_sq).const_mul C
  have hHm : Measurable H := by fun_prop
  have hgm : Measurable (Function.uncurry g) := by fun_prop
  have hbound : ∀ᵐ x ∂xLaw M, ∀ y, ‖g x y‖ ≤ H x := by
    filter_upwards [hgap, hahB, hbhB] with x hx hax hbx
    intro y
    exact crossed_band_clipped_quadratic_bound _ _ _ _ _ delta B hd hx hB hax hbx
  have hi := population_selected_integrand_integrable_of_envelope M L i g hgm H
    hHm hHi hbound w c hw hc D c0 hD hc0 hwB hclip
  refine ⟨hi, ?_⟩
  rw [population_selected_treatment_integral_transfer M L i g hgm w c hw hc hi]
  let v := fun x => w x * (selectedTreatmentMass M L i x / c x)
  have hv := clipped_selected_treatment_weight_bound M L i w c hw hc D c0 hD hc0 hwB hclip
  have hmean : ∀ᵐ x ∂xLaw M, |∫ y, g x y ∂treatedLaw M L i x| ≤ H x := by
    filter_upwards [hbound] with x hx
    have hn : 0 ≤ H x := by dsimp only [H]; positivity
    let := treatedLaw_isFiniteMeasure M L i x
    have hi' := norm_integral_le_of_norm_le_const
      (μ := treatedLaw M L i x) (Eventually.of_forall hx)
    have hm := treatedLaw_mass_le_one M L i x
    exact hi'.trans (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hm hn)
  have hvm : Measurable (fun x => v x * ∫ y, g x y ∂treatedLaw M L i x) := by fun_prop
  have hdom : ∀ᵐ x ∂xLaw M, |v x * ∫ y, g x y ∂treatedLaw M L i x| ≤ (D/c0) * H x := by
    filter_upwards [hv.2, hmean] with x hx hy
    rw [abs_mul]
    exact mul_le_mul hx hy (abs_nonneg _) (div_nonneg hD hc0.le)
  have hiv := (hHi.const_mul (D/c0)).mono' hvm.aestronglyMeasurable hdom
  calc
    _ ≤ ∫ x, |v x * ∫ y, g x y ∂treatedLaw M L i x| ∂xLaw M :=
      abs_integral_le_integral_abs
    _ ≤ ∫ x, (D/c0) * H x ∂xLaw M :=
      integral_mono_ae hiv.abs (hHi.const_mul _) hdom
    _ = _ := by
      rw [integral_const_mul, integral_const_mul,
        integral_add hea.integrable_sq heb.integrable_sq]
      simp only [finiteL2Error, Real.sq_sqrt (integral_nonneg fun x => sq_nonneg _)]
      ring

-- @node: encoded_continuous_observed_crossed_band_bias_root_n_negligible
/-- If [the true continuous nuisance is admissible](hyp:he0), [every fitted nuisance
is admissible](hyp:heh), and [their encoded components satisfy the finite nuisance
convergence rates](hyp:hrates), then, provided [the boundary separation margin is
positive](hyp:hd), [the denominator floor is positive](hyp:hc), [the true upper
boundary exceeds the true lower boundary by at least the margin almost surely](hyp:hgap),
and [the fitted selected-level denominators exceed that floor almost surely at
every sample size and realization](hyp:hclip), [the population mean of the fitted
regression-weighted, inverse-denominator selected-treatment outcome on the crossed
fitted interval, multiplied by the square root of the half-sample size, converges
to zero in probability](goal). -/
lemma encoded_continuous_observed_crossed_band_bias_root_n_negligible
    {A : Type*} [MeasurableSpace A] (μ : Measure A) (L : LevelData Z X)
    (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hrates : FiniteNuisanceRates M μ (fun n a => contComponent M L (eh n a))
      (contComponent M L (trueNuisance M L)))
    (b₁ b₂ : BoundaryIndex L) (g : RegularIndex L) (i : PositiveIndex L.K)
    (delta c : ℝ) (hd : 0 < delta) (hc : 0 < c)
    (hgap : ∀ᵐ x ∂xLaw M,
      delta ≤ (trueNuisance M L).nu b₂ x - (trueNuisance M L).nu b₁ x)
    (hclip : ∀ n a, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).piLev i x) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) * ∫ o : Obs X Z,
        (eh (2*(n+1)) a).gamma g o.1 *
          (indicator (o.2.1 ∈ L.S i.val) * o.2.2.1 / (eh (2*(n+1)) a).piLev i o.1 *
            (o.2.2.2 * indicator ((eh (2*(n+1)) a).nu b₂ o.1 < o.2.2.2 ∧
              o.2.2.2 ≤ (eh (2*(n+1)) a).nu b₁ o.1))) ∂observationLaw M)
      atTop (fun _ _ => 0) := by
  have : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  let B := max |M.yMin| |M.yMax|
  have hB : 0 ≤ B := (abs_nonneg _).trans (le_max_left _ _)
  have hcoords (e : NuisanceCont L) (he : ContAdmissible M L e) :
      (∀ b, Measurable (e.nu b) ∧ MemLp (e.nu b) 2 (xLaw M) ∧
        ∀ᵐ x ∂xLaw M, |e.nu b x| ≤ B) ∧
      Measurable (e.gamma g) ∧ Measurable (e.piLev i) ∧
        ∀ᵐ x ∂xLaw M, |e.gamma g x| ≤ 1 := by
    rcases he with ⟨_, _, _, _, _, hpim, _, _, _, _, _, _, hgb, hgm,
      _, _, hnb, hnm, _⟩
    refine ⟨?_, by fun_prop, by fun_prop, ?_⟩
    · intro b
      refine ⟨by fun_prop, ?_, ?_⟩
      · apply memLp_of_bounded (hnb b)
        fun_prop
      · filter_upwards [hnb b] with x hx
        apply abs_le.mpr
        constructor
        · have hl : -B ≤ M.yMin := by
            have hh := neg_le_abs M.yMin
            dsimp only [B]
            linarith [le_max_left |M.yMin| |M.yMax|]
          exact hl.trans hx.1
        · exact hx.2.trans ((le_abs_self _).trans (le_max_right _ _))
    · filter_upwards [hgb g] with x hx
      simpa only [abs_of_nonneg hx.1] using hx.2
  obtain ⟨_, _, _, _, _, _, _, _, hrnu, _⟩ :=
    continuous_component_rates_to_oracle_rates M μ L eh (trueNuisance M L) hrates
  let r := fun b n a => finiteL2Error M ((eh (2*(n+1)) a).nu b) ((trueNuisance M L).nu b)
  have hs b := dml_quarter_rate_product μ (r b) (r b) (hrnu b) (hrnu b)
  have hsum := (hs b₁).add_eventually_nonneg_rate
    (Eventually.of_forall fun _ => Real.rpow_nonneg (by positivity) _) (hs b₂)
  let C := max 1 ((1/c) * (2*B/delta^2))
  have hC : 0 < C := one_pos.trans_le (le_max_left _ _)
  apply dml_root_n_bias_tendsto_probability
  apply Causalean.Stat.IsLittleOp.of_abs_le_const_mul hC hsum
  intro n a
  have ht := hcoords _ he0
  have hf := hcoords _ (heh (2*(n+1)) a)
  have hb := (population_observed_crossed_band_bias_bound M L i.val
    ((trueNuisance M L).nu b₁) ((trueNuisance M L).nu b₂)
    ((eh (2*(n+1)) a).nu b₁) ((eh (2*(n+1)) a).nu b₂)
    ((eh (2*(n+1)) a).gamma g) ((eh (2*(n+1)) a).piLev i)
    (ht.1 b₁).1 (ht.1 b₂).1 (hf.1 b₁).1 (hf.1 b₂).1 hf.2.1 hf.2.2.1
    ((hf.1 b₁).2.1.sub (ht.1 b₁).2.1) ((hf.1 b₂).2.1.sub (ht.1 b₂).2.1)
    delta B 1 c hd hB zero_le_one hc hgap (hf.1 b₁).2.2 (hf.1 b₂).2.2
    hf.2.2.2 (hclip _ a)).2
  calc
    _ ≤ (1/c) * (2*B/delta^2) * (r b₁ n a ^ 2 + r b₂ n a ^ 2) := hb
    _ ≤ C * (r b₁ n a ^ 2 + r b₂ n a ^ 2) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    _ = C * |r b₁ n a * r b₁ n a + r b₂ n a * r b₂ n a| := by
      rw [← sq, ← sq, abs_of_nonneg (by positivity)]

-- Integrability needs only clipping, including when the population band has
-- no positive uniform separation. Separation is used solely for the rate.
-- @node: fitted_continuous_observed_crossed_band_integrable
/-- If [the fitted continuous nuisance is admissible](hyp:he), [the denominator
floor is positive](hyp:hc), and [the fitted selected-level denominator exceeds
that floor almost surely](hyp:hclip), then [the fitted regression-weighted,
inverse-denominator selected-treatment outcome on the crossed fitted interval
is integrable under the observation law](goal). -/
lemma fitted_continuous_observed_crossed_band_integrable
    (L : LevelData Z X) (e : NuisanceCont L) (he : ContAdmissible M L e)
    (b₁ b₂ : BoundaryIndex L) (g : RegularIndex L) (i : PositiveIndex L.K)
    (c : ℝ) (hc : 0 < c) (hclip : ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x) :
    Integrable (fun o : Obs X Z => e.gamma g o.1 *
      (indicator (o.2.1 ∈ L.S i.val) * o.2.2.1 / e.piLev i o.1 *
        (o.2.2.2 * indicator (e.nu b₂ o.1 < o.2.2.2 ∧ o.2.2.2 ≤ e.nu b₁ o.1))))
      (observationLaw M) := by
  have : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  rcases he with ⟨_, _, _, _, _, hpim, _, _, _, _, _, _, hgb, hgm,
    _, _, hnb, hnm, _⟩
  let B := max |M.yMin| |M.yMax|
  apply population_selected_integrand_integrable_of_envelope M L i.val
    (fun x y => y * indicator (e.nu b₂ x < y ∧ y ≤ e.nu b₁ x))
    (by fun_prop) (fun _ => B) (by fun_prop) (integrable_const B) _
    (e.gamma g) (e.piLev i) (by fun_prop) (by fun_prop) 1 c zero_le_one hc _ hclip
  · filter_upwards [hnb b₁, hnb b₂] with x hx₁ hx₂
    intro y
    by_cases hy : e.nu b₂ x < y ∧ y ≤ e.nu b₁ x
    · simp only [indicator, if_pos hy, mul_one, Real.norm_eq_abs]
      apply abs_le.mpr
      have hl : -B ≤ M.yMin := by
        dsimp only [B]
        linarith [neg_le_abs M.yMin, le_max_left |M.yMin| |M.yMax|]
      exact ⟨hl.trans (hx₂.1.trans hy.1.le),
        (hy.2.trans hx₁.2).trans ((le_abs_self _).trans (le_max_right _ _))⟩
    · simp only [indicator, if_neg hy, mul_zero, norm_zero]
      exact (abs_nonneg _).trans (le_max_left _ _)
  · filter_upwards [hgb g] with x hx
    simpa only [abs_of_nonneg hx.1] using hx.2

-- Both endpoints can move and cross. Each endpoint is controlled by its
-- local density bound; the crossing is controlled by the population gap.
-- @node: encoded_continuous_observed_unordered_band_bias_root_n_negligible
/-- Suppose [the true continuous nuisance is admissible](hyp:he0), [all fitted
nuisances are admissible](hyp:heh), [boundary densities are bounded](hyp:hdensity),
and [encoded nuisance components satisfy the finite convergence rates](hyp:hrates).
If [the selected level is adjacent to the lower boundary](hyp:hi₁) and [to the
upper boundary](hyp:hi₂), [the separation margin](hyp:hd) and [denominator floor](hyp:hc)
are positive, [the true boundaries are separated by at least that margin almost
surely](hyp:hgap), and [all fitted level denominators exceed the floor almost
surely](hyp:hclip), then [the population mean of the fitted regression-weighted,
inverse-denominator selected-treatment debiased band-boundary remainder, allowing
fitted endpoints to cross, multiplied by the square root of the half-sample size,
converges to zero in probability](goal). -/
lemma encoded_continuous_observed_unordered_band_bias_root_n_negligible
    {A : Type*} [MeasurableSpace A] (μ : Measure A) (L : LevelData Z X)
    (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hdensity : BoundaryDensitiesBounded M L)
    (hrates : FiniteNuisanceRates M μ (fun n a => contComponent M L (eh n a))
      (contComponent M L (trueNuisance M L)))
    (b₁ b₂ : BoundaryIndex L) (g : RegularIndex L) (i : PositiveIndex L.K)
    (hi₁ : i.val = b₁.val.1 + 1 ∨ (1 ≤ b₁.val.1 ∧ i.val = b₁.val.1))
    (hi₂ : i.val = b₂.val.1 + 1 ∨ (1 ≤ b₂.val.1 ∧ i.val = b₂.val.1))
    (delta c : ℝ) (hd : 0 < delta) (hc : 0 < c)
    (hgap : ∀ᵐ x ∂xLaw M,
      delta ≤ (trueNuisance M L).nu b₂ x - (trueNuisance M L).nu b₁ x)
    (hclip : ∀ n a i, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).piLev i x) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) * ∫ o : Obs X Z,
        (eh (2*(n+1)) a).gamma g o.1 *
          (indicator (o.2.1 ∈ L.S i.val) * o.2.2.1 / (eh (2*(n+1)) a).piLev i o.1 *
            continuousDebiasedBandBoundary ((trueNuisance M L).nu b₁ o.1)
              ((trueNuisance M L).nu b₂ o.1)
              ((eh (2*(n+1)) a).nu b₁ o.1) ((eh (2*(n+1)) a).nu b₂ o.1) o.2.2.2)
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  let R := fun n a b (o : Obs X Z) => (eh n a).gamma g o.1 *
    (indicator (o.2.1 ∈ L.S i.val) * o.2.2.1 / (eh n a).piLev i o.1 *
      (((eh n a).nu b o.1 - o.2.2.2) * indicator (o.2.2.2 ≤ (eh n a).nu b o.1) -
        ((trueNuisance M L).nu b o.1 - o.2.2.2) *
          indicator (o.2.2.2 ≤ (trueNuisance M L).nu b o.1) -
        ((eh n a).nu b o.1 - (trueNuisance M L).nu b o.1) *
          indicator (o.2.2.2 ≤ (trueNuisance M L).nu b o.1)))
  let Q := fun n a (o : Obs X Z) => (eh n a).gamma g o.1 *
    (indicator (o.2.1 ∈ L.S i.val) * o.2.2.1 / (eh n a).piLev i o.1 *
      (o.2.2.2 * indicator ((eh n a).nu b₂ o.1 < o.2.2.2 ∧
        o.2.2.2 ≤ (eh n a).nu b₁ o.1)))
  have hr := encoded_continuous_observed_ramp_pair_bias_root_n_negligible M μ L eh
    he0 heh hdensity hrates b₁ b₂ g i i hi₁ hi₂ c hc hclip
  have hq := encoded_continuous_observed_crossed_band_bias_root_n_negligible M μ L eh
    he0 heh hrates b₁ b₂ g i delta c hd hc hgap (fun n a => hclip n a i)
  have hs := (show TendstoInMeasure μ _ atTop (fun _ => (0 : ℝ)) from hr).add_zero
    (show TendstoInMeasure μ _ atTop (fun _ => (0 : ℝ)) from hq)
  change TendstoInMeasure μ _ atTop (fun _ => (0 : ℝ))
  convert hs using 1
  funext n a
  have hiR b : Integrable (R (2*(n+1)) a b) (observationLaw M) :=
    fitted_continuous_observed_quantile_remainder_integrable M L _ _
      (heh (2*(n+1)) a) he0 b g i c hc (hclip _ a i)
  have hiQ : Integrable (Q (2*(n+1)) a) (observationLaw M) :=
    fitted_continuous_observed_crossed_band_integrable M L _ (heh (2*(n+1)) a)
      b₁ b₂ g i c hc (hclip _ a i)
  have heq : (fun o : Obs X Z => (eh (2*(n+1)) a).gamma g o.1 *
      (indicator (o.2.1 ∈ L.S i.val) * o.2.2.1 / (eh (2*(n+1)) a).piLev i o.1 *
        continuousDebiasedBandBoundary ((trueNuisance M L).nu b₁ o.1)
          ((trueNuisance M L).nu b₂ o.1)
          ((eh (2*(n+1)) a).nu b₁ o.1) ((eh (2*(n+1)) a).nu b₂ o.1) o.2.2.2)) =ᵐ[observationLaw M]
      (fun o => (R (2*(n+1)) a b₁ o - R (2*(n+1)) a b₂ o) + Q (2*(n+1)) a o) := by
    filter_upwards [observationLaw_covariate_ae M _ hgap] with o ho
    rw [continuous_debiased_band_boundary_crossing_decomposition]
    · dsimp only [R, Q]
      ring
    · linarith
  rw [integral_congr_ae heq,
    integral_add (f := fun o => R (2*(n+1)) a b₁ o - R (2*(n+1)) a b₂ o)
      (g := Q (2*(n+1)) a) ((hiR b₁).sub (hiR b₂)) hiQ]
  dsimp only [R, Q]
  ring

-- The population separation used above follows from the theorem's existing
-- density and propensity-gap assumptions for any two interior boundaries.
-- @node: encoded_continuous_observed_interior_band_bias_root_n_negligible
/-- Under [the structural model assumptions](hyp:h), [known outcome endpoints](hyp:hend),
[invariant level ordering](hyp:hL), [baseline overlap](hyp:hov), and [the specified
propensity-gap separation](hyp:hg), suppose [the true continuous nuisance is
admissible](hyp:he0), [all fitted nuisances are admissible](hyp:heh), [boundary
densities are bounded](hyp:hdensity), [there is no atom at the lower endpoint](hyp:h0),
and [encoded nuisance components satisfy the finite convergence rates](hyp:hrates).
For [two boundaries in the same level](hyp:hband) [listed in increasing sublevel
order](hyp:horder), if [the selected level is adjacent to their level](hyp:hi),
[the denominator floor is positive](hyp:hc), and [all fitted level denominators
exceed that floor almost surely](hyp:hclip), then [the population mean of their
fitted regression-weighted, inverse-denominator selected-treatment debiased
band-boundary remainder, multiplied by the square root of the half-sample size,
converges to zero in probability](goal). -/
lemma encoded_continuous_observed_interior_band_bias_root_n_negligible
    (h : StructuralAssumptions M) (hend : OutcomeEndpointsKnown M)
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (cpi gap : ℝ)
    (hov : BaselineOverlapWitness M L cpi)
    (hg : PropensityGapSeparationWitness M.prop q gap)
    (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hdensity : BoundaryDensitiesBounded M L) (h0 : NoAtomAtLowerEndpoint M L)
    (hrates : FiniteNuisanceRates M μ (fun n a => contComponent M L (eh n a))
      (contComponent M L (trueNuisance M L)))
    (b₁ b₂ : BoundaryIndex L) (g : RegularIndex L) (i : PositiveIndex L.K)
    (hband : b₁.val.1 = b₂.val.1) (horder : b₁.val.2 < b₂.val.2)
    (hi : i.val = b₁.val.1 + 1 ∨ (1 ≤ b₁.val.1 ∧ i.val = b₁.val.1))
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a i, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).piLev i x) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) * ∫ o : Obs X Z,
        (eh (2*(n+1)) a).gamma g o.1 *
          (indicator (o.2.1 ∈ L.S i.val) * o.2.2.1 / (eh (2*(n+1)) a).piLev i o.1 *
            continuousDebiasedBandBoundary ((trueNuisance M L).nu b₁ o.1)
              ((trueNuisance M L).nu b₂ o.1)
              ((eh (2*(n+1)) a).nu b₁ o.1) ((eh (2*(n+1)) a).nu b₂ o.1) o.2.2.2)
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  obtain ⟨delta, hd, hsep⟩ := population_continuous_interior_boundaries_uniformly_separated
    M h hend q L hL cpi gap hov hg hdensity h0
  have hgap : ∀ᵐ x ∂xLaw M,
      delta ≤ (trueNuisance M L).nu b₂ x - (trueNuisance M L).nu b₁ x := by
    have hs := hsep b₁.val.1 b₁.property.1 b₁.val.2 b₂.val.2
      b₁.property.2.1 horder (hband.symm ▸ b₂.property.2.2)
    simpa only [trueNuisance, hband] using hs
  exact encoded_continuous_observed_unordered_band_bias_root_n_negligible M μ L eh
    he0 heh hdensity hrates b₁ b₂ g i hi (hband ▸ hi) delta c hd hc hgap hclip

-- @node: fitted_continuous_observed_debiased_band_integrable
/-- If [the fitted continuous nuisance](hyp:he) and [the true continuous nuisance](hyp:he0)
are admissible, [the true lower boundary is at most the true upper boundary almost
surely](hyp:horder), [the denominator floor is positive](hyp:hc), and [the fitted
selected-level denominator exceeds that floor almost surely](hyp:hclip), then
[the fitted regression-weighted, inverse-denominator selected-treatment debiased
band-boundary remainder is integrable under the observation law](goal). -/
lemma fitted_continuous_observed_debiased_band_integrable
    (L : LevelData Z X) (e : NuisanceCont L)
    (he : ContAdmissible M L e) (he0 : ContAdmissible M L (trueNuisance M L))
    (b₁ b₂ : BoundaryIndex L) (g : RegularIndex L) (i : PositiveIndex L.K)
    (horder : ∀ᵐ x ∂xLaw M, (trueNuisance M L).nu b₁ x ≤ (trueNuisance M L).nu b₂ x)
    (c : ℝ) (hc : 0 < c) (hclip : ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x) :
    Integrable (fun o : Obs X Z => e.gamma g o.1 *
      (indicator (o.2.1 ∈ L.S i.val) * o.2.2.1 / e.piLev i o.1 *
        continuousDebiasedBandBoundary ((trueNuisance M L).nu b₁ o.1)
          ((trueNuisance M L).nu b₂ o.1) (e.nu b₁ o.1) (e.nu b₂ o.1) o.2.2.2))
      (observationLaw M) := by
  let R := fun b (o : Obs X Z) => e.gamma g o.1 *
    (indicator (o.2.1 ∈ L.S i.val) * o.2.2.1 / e.piLev i o.1 *
      ((e.nu b o.1 - o.2.2.2) * indicator (o.2.2.2 ≤ e.nu b o.1) -
        ((trueNuisance M L).nu b o.1 - o.2.2.2) *
          indicator (o.2.2.2 ≤ (trueNuisance M L).nu b o.1) -
        (e.nu b o.1 - (trueNuisance M L).nu b o.1) *
          indicator (o.2.2.2 ≤ (trueNuisance M L).nu b o.1)))
  let Q := fun o : Obs X Z => e.gamma g o.1 *
    (indicator (o.2.1 ∈ L.S i.val) * o.2.2.1 / e.piLev i o.1 *
      (o.2.2.2 * indicator (e.nu b₂ o.1 < o.2.2.2 ∧ o.2.2.2 ≤ e.nu b₁ o.1)))
  have hiR b : Integrable (R b) (observationLaw M) :=
    fitted_continuous_observed_quantile_remainder_integrable M L e _
      he he0 b g i c hc hclip
  have hiQ : Integrable Q (observationLaw M) :=
    fitted_continuous_observed_crossed_band_integrable M L e he b₁ b₂ g i c hc hclip
  apply ((hiR b₁).sub (hiR b₂)).fun_add hiQ |>.congr
  filter_upwards [observationLaw_covariate_ae M _ horder] with o ho
  rw [continuous_debiased_band_boundary_crossing_decomposition _ _ _ _ _ ho]
  dsimp only [R, Q, Pi.sub_apply]
  ring

-- @node: encoded_continuous_restored_interior_band_regression_correction_root_n_negligible
/-- Under [the structural model assumptions](hyp:hStruct), [known outcome endpoints](hyp:hend),
[invariant level ordering](hyp:hL), [baseline overlap](hyp:hov), and [the specified
propensity-gap separation](hyp:hg), suppose [the true continuous nuisance is
admissible](hyp:he0), [all fitted nuisances are admissible](hyp:heh), [boundary
densities are bounded](hyp:hdensity), [there is no atom at the lower endpoint](hyp:h0),
and [encoded nuisance components satisfy the finite convergence rates](hyp:hrates).
For [a level below the final level](hyp:hk) and [a positive sublevel index](hyp:hj0)
[below that level's final sublevel](hyp:hj), if [the denominator floor is positive](hyp:hc)
and [all fitted level denominators exceed it almost surely](hyp:hclip), then
[the population mean of the fitted regression coefficient times the band regression
correction formed by restoring the true regression components, multiplied by
the square root of the half-sample size, converges to zero in probability](goal). -/
lemma encoded_continuous_restored_interior_band_regression_correction_root_n_negligible
    (hStruct : StructuralAssumptions M) (hend : OutcomeEndpointsKnown M)
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (cpi gap : ℝ)
    (hov : BaselineOverlapWitness M L cpi)
    (hg : PropensityGapSeparationWitness M.prop q gap)
    (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hdensity : BoundaryDensitiesBounded M L) (h0 : NoAtomAtLowerEndpoint M L)
    (hrates : FiniteNuisanceRates M μ (fun n a => contComponent M L (eh n a))
      (contComponent M L (trueNuisance M L)))
    (k j : ℕ) (hk : k < L.K) (hj0 : 1 ≤ j) (hj : j < L.l k)
    (g : RegularIndex L) (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a i, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).piLev i x) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) * ∫ o : Obs X Z,
        (eh (2*(n+1)) a).gamma g o.1 * continuousBandRegressionCorrection M L
          (continuousBandRegressionHybrid (eh (2*(n+1)) a) (trueNuisance M L)) k j o
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  let b₁ : BoundaryIndex L := ⟨(k,j), hk, hj0, hj.le⟩
  let b₂ : BoundaryIndex L := ⟨(k,j+1), hk, by omega, Nat.succ_le_of_lt hj⟩
  let h := fun n a => continuousBandRegressionHybrid (eh n a) (trueNuisance M L)
  let R := fun n a plus (o : Obs X Z) => (eh n a).gamma g o.1 *
    ((if !plus && k == 0 then 0 else
      indicator (o.2.1 ∈ L.S (if plus then k+1 else k)) * o.2.2.1 /
        positiveValue (eh n a).piLev (if plus then k+1 else k) o.1) *
      continuousDebiasedBandBoundary
        (bandBoundary M L k j o.1) (bandBoundary M L k (j+1) o.1)
        (nuValue M (h n a) k j o.1) (nuValue M (h n a) k (j+1) o.1) o.2.2.2)
  have hp : TendstoInMeasure μ (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
      ∫ o, R (2*(n+1)) a true o ∂observationLaw M) atTop (fun _ => (0 : ℝ)) := by
    have ht := encoded_continuous_observed_interior_band_bias_root_n_negligible
      M hStruct hend μ q L hL cpi gap hov hg eh he0 heh hdensity h0 hrates
      b₁ b₂ g ⟨k+1, by omega⟩ rfl (by dsimp only [b₁, b₂]; omega)
      (Or.inl rfl) c hc hclip
    change TendstoInMeasure μ _ atTop (fun _ => (0 : ℝ)) at ht
    simpa only [R, Bool.not_true, Bool.false_and, Bool.false_eq_true, if_false,
      if_true, positiveValue, dif_pos (show 1 ≤ k+1 ∧ k+1 ≤ L.K by omega),
      nuValue, if_neg (show j ≠ 0 by omega), if_neg (show j+1 ≠ 0 by omega),
      dif_pos (show k < L.K ∧ 1 ≤ j ∧ j ≤ L.l k from ⟨hk, hj0, hj.le⟩),
      dif_pos (show k < L.K ∧ 1 ≤ j+1 ∧ j+1 ≤ L.l k by omega),
      h, continuousBandRegressionHybrid, trueNuisance, b₁, b₂] using ht
  have hm : TendstoInMeasure μ (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
      ∫ o, R (2*(n+1)) a false o ∂observationLaw M) atTop (fun _ => (0 : ℝ)) := by
    by_cases hk0 : k = 0
    · subst k
      simp only [R, Bool.not_false, beq_self_eq_true, Bool.and_self, if_true,
        zero_mul, mul_zero, integral_zero]
      intro eps heps
      simpa only [edist_self, not_le.mpr heps, Set.ofPred_false, measure_empty]
        using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (𝓝 0))
    · have ht := encoded_continuous_observed_interior_band_bias_root_n_negligible
        M hStruct hend μ q L hL cpi gap hov hg eh he0 heh hdensity h0 hrates
        b₁ b₂ g ⟨k, by omega⟩ rfl (by dsimp only [b₁, b₂]; omega)
        (Or.inr ⟨by dsimp only [b₁]; omega, rfl⟩) c hc hclip
      change TendstoInMeasure μ _ atTop (fun _ => (0 : ℝ)) at ht
      simpa only [R, Bool.not_false, Bool.true_and, Bool.false_eq_true, beq_iff_eq, hk0, if_false,
        positiveValue, dif_pos (show 1 ≤ k ∧ k ≤ L.K by omega),
        nuValue, if_neg (show j ≠ 0 by omega), if_neg (show j+1 ≠ 0 by omega),
        dif_pos (show k < L.K ∧ 1 ≤ j ∧ j ≤ L.l k from ⟨hk, hj0, hj.le⟩),
        dif_pos (show k < L.K ∧ 1 ≤ j+1 ∧ j+1 ≤ L.l k by omega),
        h, continuousBandRegressionHybrid, trueNuisance, b₁, b₂] using ht
  have hs := hp.sub_zero hm
  change TendstoInMeasure μ _ atTop (fun _ => (0 : ℝ))
  convert hs using 1
  funext n a
  obtain ⟨iR, hmean⟩ := continuous_restored_band_regression_correction_nonlinear_mean
    M hStruct hend L (eh (2*(n+1)) a) (heh _ a) he0 c hc (hclip _ a) g k j hk hj
  have iD := fitted_continuous_weighted_band_regression_correction_integrable
    M L (h (2*(n+1)) a)
    (continuous_band_regression_hybrid_admissible M L _ _ (heh _ a) he0)
    c hc (hclip _ a) g k j hk
  obtain ⟨delta, hd, hsep⟩ := population_continuous_interior_boundaries_uniformly_separated
    M hStruct hend q L hL cpi gap hov hg hdensity h0
  have ho : ∀ᵐ x ∂xLaw M,
      (trueNuisance M L).nu b₁ x ≤ (trueNuisance M L).nu b₂ x := by
    filter_upwards [hsep k hk j (j+1) hj0 (by omega) (by omega)] with x hx
    change bandBoundary M L k j x ≤ bandBoundary M L k (j+1) x
    linarith
  have hi plus : Integrable (R (2*(n+1)) a plus) (observationLaw M) := by
    cases plus
    · by_cases hk0 : k = 0
      · subst k
        simp only [R, Bool.not_false, beq_self_eq_true, Bool.and_self, if_true,
          zero_mul, mul_zero]
        exact integrable_zero _ _ _
      · have ht := fitted_continuous_observed_debiased_band_integrable M L
          (eh (2*(n+1)) a) (heh _ a) he0 b₁ b₂ g ⟨k, by omega⟩ ho c hc
          (hclip _ a _)
        simpa only [R, Bool.not_false, Bool.true_and, Bool.false_eq_true, beq_iff_eq, hk0, if_false,
          positiveValue, dif_pos (show 1 ≤ k ∧ k ≤ L.K by omega),
          nuValue, if_neg (show j ≠ 0 by omega), if_neg (show j+1 ≠ 0 by omega),
          dif_pos (show k < L.K ∧ 1 ≤ j ∧ j ≤ L.l k from ⟨hk, hj0, hj.le⟩),
          dif_pos (show k < L.K ∧ 1 ≤ j+1 ∧ j+1 ≤ L.l k by omega),
          h, continuousBandRegressionHybrid, trueNuisance, b₁, b₂] using ht
    · have ht := fitted_continuous_observed_debiased_band_integrable M L
        (eh (2*(n+1)) a) (heh _ a) he0 b₁ b₂ g ⟨k+1, by omega⟩ ho c hc
        (hclip _ a _)
      simpa only [R, Bool.not_true, Bool.false_and, Bool.false_eq_true, if_false,
        if_true, positiveValue, dif_pos (show 1 ≤ k+1 ∧ k+1 ≤ L.K by omega),
        nuValue, if_neg (show j ≠ 0 by omega), if_neg (show j+1 ≠ 0 by omega),
        dif_pos (show k < L.K ∧ 1 ≤ j ∧ j ≤ L.l k from ⟨hk, hj0, hj.le⟩),
        dif_pos (show k < L.K ∧ 1 ≤ j+1 ∧ j+1 ≤ L.l k by omega),
        h, continuousBandRegressionHybrid, trueNuisance, b₁, b₂] using ht
  rw [← mul_sub, ← integral_sub (hi true) (hi false)]
  rw [hmean]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with o
  dsimp only [R]
  ring

-- @node: encoded_continuous_restored_band_regression_correction_root_n_negligible
/-- Under [the structural model assumptions](hyp:hStruct), [known outcome endpoints](hyp:hend),
[invariant level ordering](hyp:hL), [baseline overlap](hyp:hov), and [the specified
propensity-gap separation](hyp:hg), suppose [the true continuous nuisance is
admissible](hyp:he0), [all fitted nuisances are admissible](hyp:heh), [boundary
densities are bounded](hyp:hdensity), [there is no atom at the lower endpoint](hyp:h0),
and [encoded nuisance components satisfy the finite convergence rates](hyp:hrates).
For [a level below the final level](hyp:hk) and [a sublevel below its final
sublevel](hyp:hj), if [the denominator floor is positive](hyp:hc) and [all fitted
level denominators exceed it almost surely](hyp:hclip), then [the population mean
of the fitted regression coefficient times the band regression correction formed
by restoring the true regression components, multiplied by the square root of
the half-sample size, converges to zero in probability, including for the first band](goal). -/
lemma encoded_continuous_restored_band_regression_correction_root_n_negligible
    (hStruct : StructuralAssumptions M) (hend : OutcomeEndpointsKnown M)
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (cpi gap : ℝ)
    (hov : BaselineOverlapWitness M L cpi)
    (hg : PropensityGapSeparationWitness M.prop q gap)
    (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hdensity : BoundaryDensitiesBounded M L) (h0 : NoAtomAtLowerEndpoint M L)
    (hrates : FiniteNuisanceRates M μ (fun n a => contComponent M L (eh n a))
      (contComponent M L (trueNuisance M L)))
    (k j : ℕ) (hk : k < L.K) (hj : j < L.l k)
    (g : RegularIndex L) (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a i, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).piLev i x) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) * ∫ o : Obs X Z,
        (eh (2*(n+1)) a).gamma g o.1 * continuousBandRegressionCorrection M L
          (continuousBandRegressionHybrid (eh (2*(n+1)) a) (trueNuisance M L)) k j o
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  by_cases hj0 : j = 0
  · subst j
    exact encoded_continuous_restored_first_band_regression_correction_root_n_negligible
      M μ hStruct hend L eh he0 heh hdensity hrates k hk (by omega) g c hc hclip
  · exact encoded_continuous_restored_interior_band_regression_correction_root_n_negligible
      M hStruct hend μ q L hL cpi gap hov hg eh he0 heh hdensity h0 hrates
      k j hk (by omega) hj g c hc hclip

-- @node: encoded_continuous_restored_all_band_regression_block_root_n_negligible
/-- Under [the structural model assumptions](hyp:hStruct), [known outcome endpoints](hyp:hend),
[invariant level ordering](hyp:hL), [baseline overlap](hyp:hov), and [the specified
propensity-gap separation](hyp:hg), suppose [the true continuous nuisance is
admissible](hyp:he0), [all fitted nuisances are admissible](hyp:heh), [boundary
densities are bounded](hyp:hdensity), [there is no atom at the lower endpoint](hyp:h0),
and [encoded nuisance components satisfy the finite convergence rates](hyp:hrates).
If [the denominator floor is positive](hyp:hc), [all fitted level denominators
exceed it almost surely](hyp:hclip), and [every band in the finite collection has
a level and sublevel below their respective final indices](hyp:ht), then [the
population mean of the sum of fitted regression-weighted band corrections formed
by restoring the true regression components, multiplied by the square root of
the half-sample size, converges to zero in probability](goal). -/
lemma encoded_continuous_restored_all_band_regression_block_root_n_negligible
    (hStruct : StructuralAssumptions M) (hend : OutcomeEndpointsKnown M)
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (cpi gap : ℝ)
    (hov : BaselineOverlapWitness M L cpi)
    (hg : PropensityGapSeparationWitness M.prop q gap)
    (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hdensity : BoundaryDensitiesBounded M L) (h0 : NoAtomAtLowerEndpoint M L)
    (hrates : FiniteNuisanceRates M μ (fun n a => contComponent M L (eh n a))
      (contComponent M L (trueNuisance M L)))
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a i, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).piLev i x)
    (t : Finset ((ℕ × ℕ) × RegularIndex L))
    (ht : ∀ b ∈ t, b.1.1 < L.K ∧ b.1.2 < L.l b.1.1) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) * ∫ o : Obs X Z, ∑ b ∈ t,
        (eh (2*(n+1)) a).gamma b.2 o.1 * continuousBandRegressionCorrection M L
          (continuousBandRegressionHybrid (eh (2*(n+1)) a) (trueNuisance M L))
          b.1.1 b.1.2 o ∂observationLaw M) atTop (fun _ _ => 0) := by
  let R := fun n a (b : (ℕ × ℕ) × RegularIndex L) (o : Obs X Z) =>
    (eh n a).gamma b.2 o.1 * continuousBandRegressionCorrection M L
      (continuousBandRegressionHybrid (eh n a) (trueNuisance M L)) b.1.1 b.1.2 o
  let F := fun b n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
    ∫ o, R (2*(n+1)) a b o ∂observationLaw M
  have hF b (hb : b ∈ t) : TendstoInMeasure μ (F b) atTop (fun _ => (0 : ℝ)) :=
    encoded_continuous_restored_band_regression_correction_root_n_negligible M
      hStruct hend μ q L hL cpi gap hov hg eh he0 heh hdensity h0 hrates
      b.1.1 b.1.2 (ht b hb).1 (ht b hb).2 b.2 c hc hclip
  have hs : TendstoInMeasure μ (fun n a => ∑ b ∈ t, F b n a)
      atTop (fun _ => (0 : ℝ)) := by
    induction t using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      intro eps heps
      simpa only [edist_self, not_le.mpr heps, Set.ofPred_false, measure_empty]
        using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (𝓝 0))
    | @insert b t hb ih =>
      have hsingle := hF b (Finset.mem_insert_self b t)
      have hrest := ih (fun d hd => ht d (Finset.mem_insert_of_mem hd))
        (fun d hd => hF d (Finset.mem_insert_of_mem hd))
      simpa only [Finset.sum_insert hb] using hsingle.add_zero hrest
  change TendstoInMeasure μ _ atTop (fun _ => (0 : ℝ))
  convert hs using 1
  funext n a
  have hi b (hb : b ∈ t) : Integrable (R (2*(n+1)) a b) (observationLaw M) :=
    fitted_continuous_weighted_band_regression_correction_integrable M L _
      (continuous_band_regression_hybrid_admissible M L _ _ (heh _ a) he0)
      c hc (hclip _ a) b.2 b.1.1 b.1.2 (ht b hb).1
  rw [integral_finsetSum t hi]
  exact Finset.mul_sum t _ _

end Papers.TbsPrteOptimalTransport

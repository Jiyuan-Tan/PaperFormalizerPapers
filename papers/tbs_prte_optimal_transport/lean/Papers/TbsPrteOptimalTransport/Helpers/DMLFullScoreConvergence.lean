module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLObservedResidualConvergence
public import Papers.TbsPrteOptimalTransport.Helpers.DMLBranchWeightedConvergence
/-! Observation-law convergence of the full-interval binary product corrections.
Clipping supplies moments, and component nuisance rates control both the fitted
regression residual and its fitted signed weight. -/
public section
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.whitespace false
set_option linter.unreachableTactic false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedTactic false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: fitted_RP_measurable
/-- If [the binary nuisance vector is admissible](hyp:he), then
[its success residual at any level index is measurable as a function of the observation](goal). -/
@[fun_prop] lemma fitted_RP_measurable (L : LevelData Z X) (e : NuisanceBin L)
    (he : BinAdmissible M L e) (i : ℕ) : Measurable (RP L e i) := by
  first | fun_prop | skip
  have hp := fitted_positive_success_measurable M L e he i
  have hpi := fitted_positive_assignment_measurable M L e he i
  unfold RP
  split_ifs <;> fun_prop

-- The fixed zero boundary has no denominator and contributes no residual.
-- @node: fitted_RP_abs_bound
/-- If [the binary nuisance vector is admissible](hyp:he), [the outcome is binary almost surely](hyp:hy),
[the clipping constant c is positive](hyp:hc),
[positive-level assignment probabilities are bounded below by c almost everywhere](hyp:hclip), and
[the residual index is no larger than the number of levels](hyp:hi), then
[the success residual has absolute value at most 1/c almost surely under the observation law](goal). -/
lemma fitted_RP_abs_bound (L : LevelData Z X) (e : NuisanceBin L)
    (he : BinAdmissible M L e) (hy : OutcomeBinaryAE M)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (i : ℕ) (hi : i ≤ L.K) :
    ∀ᵐ o ∂observationLaw M, |RP L e i o| ≤ 1 / c := by
  by_cases hi0 : i = 0
  · subst i
    exact Eventually.of_forall (fun o => by simp only [RP, ↓reduceIte, abs_zero]; positivity)
  have hip : 1 ≤ i ∧ i ≤ L.K := ⟨by omega, hi⟩
  have hcl : ∀ᵐ x ∂xLaw M, c ≤ positiveValue e.piLev i x := by
    simpa only [positiveValue, dif_pos hip] using hclip ⟨i, hip⟩
  filter_upwards [observationLaw_binary_numerator_range M hy,
    observationLaw_covariate_ae M _ (fitted_positive_success_range M L e he i),
    observationLaw_covariate_ae M _ hcl] with o ho hj hp
  have hr : |o.2.2.2 * o.2.2.1 - positiveValue e.P1 i o.1| ≤ 1 :=
    abs_le.mpr ⟨by linarith [ho.2.1, hj.2], by linarith [ho.2.2, hj.1]⟩
  have ha : |indicator (o.2.1 ∈ L.S i)| ≤ 1 := by
    unfold indicator
    split_ifs <;> norm_num
  rw [RP, if_neg hi0, abs_mul, abs_div, abs_of_pos (hc.trans_le hp)]
  calc
    _ ≤ (1 / positiveValue e.piLev i o.1) * 1 := by
      have hp0 := hc.trans_le hp
      gcongr
    _ ≤ 1 / c := by
      rw [mul_one]
      exact div_le_div_of_nonneg_left zero_le_one hc hp

-- @node: fitted_RP_memLp
/-- If [the binary nuisance vector is admissible](hyp:he), [the outcome is binary almost surely](hyp:hy),
[the clipping constant is positive](hyp:hc),
[positive-level assignment probabilities are bounded below by that constant almost everywhere](hyp:hclip), and
[the residual index is no larger than the number of levels](hyp:hi), then
[the success residual is square-integrable under the observation law](goal). -/
lemma fitted_RP_memLp (L : LevelData Z X) (e : NuisanceBin L)
    (he : BinAdmissible M L e) (hy : OutcomeBinaryAE M)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (i : ℕ) (hi : i ≤ L.K) : MemLp (RP L e i) 2 (observationLaw M) := by
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  apply MemLp.of_bound (by fun_prop) (1 / c)
  simpa only [Real.norm_eq_abs] using fitted_RP_abs_bound M L e he hy c hc hclip i hi

-- The square of the covariate L2 norm is exactly the observation-law energy.
-- @node: nuisanceRates_covariate_sq_tendsto_probability_zero
/-- If [every reference covariate function is measurable](hyp:hf),
[every fitted covariate function is measurable](hyp:hfh), and
[the fitted functions satisfy the finite nuisance rates relative to their reference functions](hyp:hr), then
[for any coordinate the integrated squared error evaluated at the observed covariate, using fits at sample sizes twice n plus two, converges in probability to zero](goal). -/
lemma nuisanceRates_covariate_sq_tendsto_probability_zero
    {A ι : Type*} [MeasurableSpace A] (μ : Measure A)
    (f : ι → X → ℝ) (fh : ℕ → A → ι → X → ℝ)
    (hf : ∀ i, Measurable (f i)) (hfh : ∀ n a i, Measurable (fh n a i))
    (hr : FiniteNuisanceRates M μ fh f) (i : ι) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o, (fh (2*(n+1)) a i o.1 - f i o.1)^2 ∂observationLaw M)
      atTop (fun _ _ => 0) := by
  have hsq : Continuous (fun t : ℝ => t^2) := by fun_prop
  have h := Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt
    hsq.continuousAt (dml_quarter_rate_tendsto_probability_zero μ _ (hr i))
  simp only [finiteL2Error, Real.sq_sqrt (integral_nonneg fun x => sq_nonneg _),
    zero_pow (by norm_num : 2 ≠ 0)] at h
  have hi (n : ℕ) (a : A) := observationLaw_covariate_integral M
    (fun x => (fh (2*(n+1)) a i x - f i x)^2) (by fun_prop)
  simpa only [hi] using h

-- Both energies are derived from component rates. The weight is signed but
-- bounded by one, while overlap bounds the population regression residual.
-- @node: nuisanceRates_gammaFull_RP_sq_tendsto_probability_zero
/-- Suppose [the reference binary nuisance vector is admissible](hyp:he0),
[all fitted nuisance vectors are admissible](hyp:heh), [the outcome is binary almost surely](hyp:hy),
[the clipping constant is positive](hyp:hc), and
[reference and fitted positive-level assignment probabilities are bounded below by that constant almost everywhere](hyp:hclip).
If [success probabilities, assignment probabilities, and full-interval weights satisfy the finite nuisance rates](hyp:hrP,hrpi,hrg), and
[the residual index is no larger than the number of levels](hyp:hi), then
[the observation-law integrated squared error of the full-interval weight times the success residual converges in probability to zero along sample sizes twice n plus two](goal). -/
lemma nuisanceRates_gammaFull_RP_sq_tendsto_probability_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (L : LevelData Z X) (e0 : NuisanceBin L) (eh : ℕ → A → NuisanceBin L)
    (he0 : BinAdmissible M L e0) (heh : ∀ n a, BinAdmissible M L (eh n a))
    (hy : OutcomeBinaryAE M) (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a (i : PositiveIndex L.K), ∀ᵐ x ∂xLaw M,
      c ≤ e0.piLev i x ∧ c ≤ (eh n a).piLev i x)
    (hrP : FiniteNuisanceRates M μ (fun n a => (eh n a).P1) e0.P1)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) e0.piLev)
    (hrg : FiniteNuisanceRates M μ (fun n a => (eh n a).gammaFull) e0.gammaFull)
    (k : Fin L.K) (i : ℕ) (hi : i ≤ L.K) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o,
        ((eh (2*(n+1)) a).gammaFull k o.1 * RP L (eh (2*(n+1)) a) i o -
          e0.gammaFull k o.1 * RP L e0 i o)^2 ∂observationLaw M)
      atTop (fun _ _ => 0) := by
  have hg0 : Measurable (e0.gammaFull k) := he0.2.2.2.2.2.2.2.2.2.2.1 k
  have hgh (n : ℕ) (a : A) : Measurable ((eh n a).gammaFull k) :=
    (heh n a).2.2.2.2.2.2.2.2.2.2.1 k
  apply dml_weighted_residual_sq_tendsto_probability_zero μ (observationLaw M)
    (fun o => e0.gammaFull k o.1) (RP L e0 i)
    (fun n a o => (eh (2*(n+1)) a).gammaFull k o.1)
    (fun n a => RP L (eh (2*(n+1)) a) i) 1 (1 / c)
    (by fun_prop) (by fun_prop) (by intro n a; fun_prop)
    (by intro n a; first | fun_prop | exact fitted_RP_measurable M L _ (heh _ a) i)
  · intro n a
    exact ((fitted_gammaFull_memLp M L _ (heh _ a) k).sub
      (fitted_gammaFull_memLp M L e0 he0 k)).comp_measurePreserving
      (observationLaw_fst_measurePreserving M)
  · intro n a
    exact (fitted_RP_memLp M L _ (heh _ a) hy c hc
      (fun j => (hclip _ a j).mono (fun _ hx => hx.2)) i hi).sub
        (fitted_RP_memLp M L e0 he0 hy c hc
          (fun j => (hclip (2*(n+1)) a j).mono (fun _ hx => hx.1)) i hi)
  · intro n a
    apply observationLaw_covariate_ae M (fun x => |(eh (2*(n+1)) a).gammaFull k x| ≤ 1)
    filter_upwards [(heh (2*(n+1)) a).2.2.2.2.2.2.2.2.2.1 k] with x hx
    exact abs_le.mpr hx
  · exact fun n a => fitted_RP_abs_bound M L e0 he0 hy c hc
      (fun j => (hclip n a j).mono (fun _ hx => hx.1)) i hi
  · exact nuisanceRates_covariate_sq_tendsto_probability_zero M μ _ _
      (fun k => he0.2.2.2.2.2.2.2.2.2.2.1 k)
      (fun n a k => (heh n a).2.2.2.2.2.2.2.2.2.2.1 k) hrg k
  · exact nuisanceRates_RP_sq_tendsto_probability_zero M μ L e0 eh he0 heh
      hy c hc hclip hrP hrpi i hi

-- Finite score assembly uses actual squared errors, with no uniform rate.
-- @node: dml_three_term_sq_tendsto_probability_zero
/-- For [a first array of random functions](hyp:f), [a second array of random functions](hyp:g), and
[a third array of random functions](hyp:h), suppose
[every function in the first array is square-integrable](hyp:hf),
[every function in the second array is square-integrable](hyp:hg), and
[every function in the third array is square-integrable](hyp:hh).
If [the first array's integrated squares converge in probability to zero](hyp:hrf),
[the second array's integrated squares converge in probability to zero](hyp:hrg), and
[the third array's integrated squares converge in probability to zero](hyp:hrh), then
[the integrated square of the first function plus the second minus the third converges in probability to zero](goal). -/
lemma dml_three_term_sq_tendsto_probability_zero {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B] (μ : Measure A) (ν : Measure B)
    (f g h : ℕ → A → B → ℝ)
    (hf : ∀ n a, MemLp (f n a) 2 ν)
    (hg : ∀ n a, MemLp (g n a) 2 ν)
    (hh : ∀ n a, MemLp (h n a) 2 ν)
    (hrf : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ x, (f n a x)^2 ∂ν) atTop (fun _ _ => 0))
    (hrg : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ x, (g n a x)^2 ∂ν) atTop (fun _ _ => 0))
    (hrh : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ x, (h n a x)^2 ∂ν) atTop (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ x, (f n a x + g n a x - h n a x)^2 ∂ν)
      atTop (fun _ _ => 0) := by
  have hn : Continuous (fun t : ℝ => -t) := by fun_prop
  have hng := Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt
    hn.continuousAt hrg
  have hnh := Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt
    hn.continuousAt hrh
  simp only [neg_zero] at hng hnh
  have hs := (hrf.sub hng).sub hnh
  simp only [sub_neg_eq_add, sub_zero] at hs
  have hc : Continuous (fun t : ℝ => 3*t) := by fun_prop
  have hb := Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt hc.continuousAt hs
  simp only [mul_zero] at hb
  apply probability_zero_of_nonneg_le μ _ _ hb
  intro n
  apply Eventually.of_forall
  intro a
  refine ⟨integral_nonneg (fun x => sq_nonneg _), ?_⟩
  obtain ⟨he, hbound⟩ := integral_sq_abs_sum_three_le ν _ _ _ (hf n a) (hg n a) (hh n a)
  apply le_trans _ hbound
  apply integral_mono ((hf n a).add (hg n a) |>.sub (hh n a)).integrable_sq he.integrable_sq
  intro x
  change (f n a x + g n a x - h n a x)^2 ≤ (|f n a x| + |g n a x| + |h n a x|)^2
  have ha : |f n a x + g n a x - h n a x| ≤
      |f n a x| + |g n a x| + |h n a x| :=
    (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) ha 2

-- @node: fitted_gammaFull_RP_memLp
/-- If [the binary nuisance vector is admissible](hyp:he), [the outcome is binary almost surely](hyp:hy),
[the clipping constant is positive](hyp:hc),
[positive-level assignment probabilities are bounded below by that constant almost everywhere](hyp:hclip), and
[the residual index is no larger than the number of levels](hyp:hi), then
[the full-interval weight times the success residual is square-integrable under the observation law](goal). -/
lemma fitted_gammaFull_RP_memLp (L : LevelData Z X) (e : NuisanceBin L)
    (he : BinAdmissible M L e) (hy : OutcomeBinaryAE M)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (k : Fin L.K) (i : ℕ) (hi : i ≤ L.K) :
    MemLp (fun o => e.gammaFull k o.1 * RP L e i o) 2 (observationLaw M) := by
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  have hg : Measurable (e.gammaFull k) := he.2.2.2.2.2.2.2.2.2.2.1 k
  apply MemLp.of_bound (by fun_prop) (1/c)
  filter_upwards [fitted_RP_abs_bound M L e he hy c hc hclip i hi,
    observationLaw_covariate_ae M _ (he.2.2.2.2.2.2.2.2.2.1 k)] with o hr hg
  rw [Real.norm_eq_abs, abs_mul]
  calc
    _ ≤ 1 * (1/c) := mul_le_mul (abs_le.mpr hg) hr (abs_nonneg _) zero_le_one
    _ = _ := one_mul _

-- Cancellation of the plug-in weight terms leaves a bounded event contrast
-- and two weighted residuals. All three energies follow from nuisance rates.
-- @node: nuisanceRates_full_product_sq_tendsto_probability_zero
/-- Suppose [the reference binary nuisance vector is admissible](hyp:he0),
[all fitted nuisance vectors are admissible](hyp:heh), [the outcome is binary almost surely](hyp:hy),
[the clipping constant is positive](hyp:hc), and
[reference and fitted positive-level assignment probabilities are bounded below by that constant almost everywhere](hyp:hclip).
If [success probabilities, assignment probabilities, and full-interval weights satisfy the finite nuisance rates](hyp:hrP,hrpi,hrg), then
[the observation-law integrated squared error of each full-interval product score converges in probability to zero along sample sizes twice n plus two](goal). -/
lemma nuisanceRates_full_product_sq_tendsto_probability_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (L : LevelData Z X) (e0 : NuisanceBin L) (eh : ℕ → A → NuisanceBin L)
    (he0 : BinAdmissible M L e0) (heh : ∀ n a, BinAdmissible M L (eh n a))
    (hy : OutcomeBinaryAE M) (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a (i : PositiveIndex L.K), ∀ᵐ x ∂xLaw M,
      c ≤ e0.piLev i x ∧ c ≤ (eh n a).piLev i x)
    (hrP : FiniteNuisanceRates M μ (fun n a => (eh n a).P1) e0.P1)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) e0.piLev)
    (hrg : FiniteNuisanceRates M μ (fun n a => (eh n a).gammaFull) e0.gammaFull)
    (k : Fin L.K) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o, (psiFullProdBin L (eh (2*(n+1)) a) k o -
        psiFullProdBin L e0 k o)^2 ∂observationLaw M) atTop (fun _ _ => 0) := by
  let ev := fun o : Obs X Z => indicator (o.2.1 ∈ higherPolicy L k) -
    indicator (o.2.1 ∈ higherBaseline L k)
  have hev : Measurable ev := by dsimp only [ev]; fun_prop
  have hevb (o : Obs X Z) : |ev o| ≤ 1 := by
    dsimp only [ev, indicator]
    split_ifs <;> norm_num
  let f := fun n a o => ev o * (binFullJ L (eh (2*(n+1)) a) k o.1 - binFullJ L e0 k o.1)
  let r := fun n a i o => (eh (2*(n+1)) a).gammaFull k o.1 * RP L (eh (2*(n+1)) a) i o -
    e0.gammaFull k o.1 * RP L e0 i o
  have hJ0 : MemLp (binFullJ L e0 k) 2 (xLaw M) := by
    haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
    exact MemLp.of_bound (by fun_prop) 1 (fitted_binFullJ_norm_bound M L e0 he0 k)
  have hJh (n : ℕ) (a : A) : MemLp (binFullJ L (eh (2*(n+1)) a) k) 2 (xLaw M) := by
    haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
    have he := heh (2*(n+1)) a
    exact MemLp.of_bound (by fun_prop) 1 (fitted_binFullJ_norm_bound M L _ he k)
  have hf (n : ℕ) (a : A) : MemLp (f n a) 2 (observationLaw M) := by
    have hd := ((hJh n a).sub hJ0).comp_measurePreserving (observationLaw_fst_measurePreserving M)
    have hj0 := fitted_binFullJ_measurable M L e0 he0 k
    have hjh := fitted_binFullJ_measurable M L _ (heh (2*(n+1)) a) k
    apply hd.norm.mono' (by
      first | fun_prop | exact (hev.mul ((hjh.comp measurable_fst).sub
        (hj0.comp measurable_fst))).aestronglyMeasurable)
    apply Eventually.of_forall
    intro o
    change ‖ev o * (binFullJ L (eh (2*(n+1)) a) k o.1 - binFullJ L e0 k o.1)‖ ≤
      ‖binFullJ L (eh (2*(n+1)) a) k o.1 - binFullJ L e0 k o.1‖
    rw [norm_mul, Real.norm_eq_abs (ev o)]
    exact mul_le_of_le_one_left (norm_nonneg _) (hevb o)
  have hr (n : ℕ) (a : A) (i : ℕ) (hi : i ≤ L.K) : MemLp (r n a i) 2 (observationLaw M) := by
    exact (fitted_gammaFull_RP_memLp M L _ (heh _ a) hy c hc
      (fun j => (hclip _ a j).mono (fun _ hx => hx.2)) k i hi).sub
      (fitted_gammaFull_RP_memLp M L e0 he0 hy c hc
        (fun j => (hclip (2*(n+1)) a j).mono (fun _ hx => hx.1)) k i hi)
  have hJr := nuisanceRates_covariate_sq_tendsto_probability_zero M μ
    (fun i => binFullJ L e0 i) (fun n a i => binFullJ L (eh n a) i)
    (fun i => fitted_binFullJ_measurable M L e0 he0 i)
    (fun n a i => fitted_binFullJ_measurable M L _ (heh n a) i)
    (nuisanceRates_binFullJ_quarter_rate M μ L e0 eh he0 heh hrP) k
  have hfr : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o, (f n a o)^2 ∂observationLaw M) atTop (fun _ _ => 0) := by
    apply probability_zero_of_nonneg_le μ _ _ hJr
    intro n
    apply Eventually.of_forall
    intro a
    refine ⟨integral_nonneg (fun o => sq_nonneg _), ?_⟩
    apply integral_mono (hf n a).integrable_sq
      (((hJh n a).sub hJ0).comp_measurePreserving (observationLaw_fst_measurePreserving M)).integrable_sq
    intro o
    dsimp only [f]
    rw [mul_pow]
    have hb : (ev o)^2 ≤ 1 := by
      simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (abs_nonneg _) (hevb o) 2
    exact mul_le_of_le_one_left (sq_nonneg _) hb
  have hrr (i : ℕ) (hi : i ≤ L.K) := nuisanceRates_gammaFull_RP_sq_tendsto_probability_zero
    M μ L e0 eh he0 heh hy c hc hclip hrP hrpi hrg k i hi
  have hs := dml_three_term_sq_tendsto_probability_zero μ (observationLaw M)
    f (fun n a => r n a (k+1)) (fun n a => r n a k) hf
    (fun n a => hr n a (k+1) (by omega)) (fun n a => hr n a k k.isLt.le)
    hfr (hrr (k+1) (by omega)) (hrr k k.isLt.le)
  have hid (n : ℕ) (a : A) (o : Obs X Z) :
      psiFullProdBin L (eh (2*(n+1)) a) k o - psiFullProdBin L e0 k o =
        f n a o + r n a (k+1) o - r n a k o := by
    simp only [psiFullProdBin, fullValue, dif_pos k.isLt, f, r, ev]
    ring
  simpa only [← hid] using hs

end Papers.TbsPrteOptimalTransport

module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLFullBlockRates
public import Papers.TbsPrteOptimalTransport.Helpers.DMLIPWConvergence
/-! Convergence of the actual binary regression residuals under the observation law.
Covariate nuisance rates are transported to observations, including the fixed zero boundary. -/
public section
set_option linter.style.openClassical false
set_option linter.unnecessarySimpa false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false
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

-- @node: observationLaw_fst_measurePreserving
/-- [Extracting the covariates from an observation preserves their population distribution](goal). -/
lemma observationLaw_fst_measurePreserving :
    MeasurePreserving (Prod.fst : Obs X Z → X) (observationLaw M) (xLaw M) := by
  refine ⟨measurable_fst, ?_⟩
  have hm : Measurable (fun s => (M.Xv s, M.Zv s, M.W s, M.Y s)) := by
    first | fun_prop | exact M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY))
  simpa only [observationLaw, xLaw, Function.comp_def] using
    Measure.map_map measurable_fst hm

-- @node: observationLaw_covariate_integral
/-- If [a real-valued covariate function is measurable](hyp:hf), [its integral under the observation distribution equals its integral under the covariate distribution](goal). -/
lemma observationLaw_covariate_integral (f : X → ℝ) (hf : Measurable f) :
    (∫ o : Obs X Z, f o.1 ∂observationLaw M) = ∫ x, f x ∂xLaw M := by
  have hmp := observationLaw_fst_measurePreserving M
  rw [← hmp.map_eq]
  exact (integral_map hmp.aemeasurable (by fun_prop)).symm

-- Only binary treatment is needed for Rp; the binary outcome regime also
-- bounds the observed treated-success numerator used by RP.
-- @node: observationLaw_binary_numerator_range
/-- If [the outcome is binary almost surely](hyp:hy), [both treatment and the product of outcome and treatment lie between zero and one almost surely under the observation distribution](goal). -/
lemma observationLaw_binary_numerator_range (hy : OutcomeBinaryAE M) :
    ∀ᵐ o : Obs X Z ∂observationLaw M,
      o.2.2.1 ∈ Icc (0 : ℝ) 1 ∧ o.2.2.2 * o.2.2.1 ∈ Icc (0 : ℝ) 1 := by
  have hm : Measurable (fun s => (M.Xv s, M.Zv s, M.W s, M.Y s)) := by
    first | fun_prop | exact M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY))
  have hs : MeasurableSet {o : Obs X Z |
      o.2.2.1 ∈ Icc (0 : ℝ) 1 ∧ o.2.2.2 * o.2.2.1 ∈ Icc (0 : ℝ) 1} := by
    exact (measurableSet_Icc.preimage (by fun_prop)).inter
      (measurableSet_Icc.preimage (by fun_prop))
  apply (ae_map_iff hm.aemeasurable hs).2
  filter_upwards [hy] with s hs
  rcases hs with hs | hs <;> rcases M.rangeW s with hw | hw <;> simp [hs, hw]

-- The IPW discrepancy's energy is derived from covariate regression and
-- denominator errors. No convergence premise for a score is used.
-- @node: dml_observation_ipw_residual_sq_tendsto_probability_zero
/-- Suppose [the common denominator lower bound is positive](hyp:hc), [the population denominator and regression are measurable](hyp:hp,hj), [the observed response and assignment weight are measurable](hyp:hy,ha), and [all fitted denominators and regressions are measurable](hyp:hph,hjh). If [both fitted errors are square-integrable over covariates](hyp:heJ,heP), [population and fitted denominators exceed the common lower bound almost everywhere](hyp:hclip), [the assignment weight has absolute value at most one](hyp:hassign), [the population response residual is bounded in absolute value by the residual bound](hyp:hres), and [both covariate L2 errors are little-o in probability of the inverse fourth root of the even sample size](hyp:hrJ,hrP), then [the integrated squared difference between fitted and population inverse-probability-weighted residuals converges in probability to zero](goal). -/
lemma dml_observation_ipw_residual_sq_tendsto_probability_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (p j : X → ℝ) (y a : Obs X Z → ℝ) (ph jh : ℕ → A → X → ℝ)
    (c R : ℝ) (hc : 0 < c) (hp : Measurable p) (hj : Measurable j)
    (hy : Measurable y) (ha : Measurable a)
    (hph : ∀ n t, Measurable (ph n t)) (hjh : ∀ n t, Measurable (jh n t))
    (heJ : ∀ n t, MemLp (fun x => jh n t x - j x) 2 (xLaw M))
    (heP : ∀ n t, MemLp (fun x => ph n t x - p x) 2 (xLaw M))
    (hclip : ∀ n t, ∀ᵐ x ∂xLaw M, c ≤ p x ∧ c ≤ ph n t x)
    (hassign : ∀ᵐ o ∂observationLaw M, |a o| ≤ 1)
    (hres : ∀ᵐ o ∂observationLaw M, |y o - j o.1| ≤ R)
    (hrJ : Causalean.Stat.IsLittleOp
      (fun n t => finiteL2Error M (jh n t) j)
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ)) μ)
    (hrP : Causalean.Stat.IsLittleOp
      (fun n t => finiteL2Error M (ph n t) p)
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ)) μ) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ o, (a o / ph n t o.1 * (y o - jh n t o.1) -
        a o / p o.1 * (y o - j o.1)) ^ 2 ∂observationLaw M)
      atTop (fun _ _ => 0) := by
  have hmp := observationLaw_fst_measurePreserving M
  apply dml_clipped_ipw_residual_sq_tendsto_probability_zero μ (observationLaw M)
    (fun o => p o.1) (fun o => j o.1) y a
    (fun n t o => ph n t o.1) (fun n t o => jh n t o.1) c R
    hc (by fun_prop) (by fun_prop) hy ha
    (by intro n t; fun_prop) (by intro n t; fun_prop)
  · intro n t
    exact (heJ n t).comp_measurePreserving hmp
  · intro n t
    exact (heP n t).comp_measurePreserving hmp
  · exact fun n t => observationLaw_covariate_ae M _ (hclip n t)
  · exact hassign
  · exact hres
  · have hi (n : ℕ) (t : A) := observationLaw_covariate_integral M
      (fun x => (jh n t x - j x) ^ 2) (by fun_prop)
    simpa only [hi, finiteL2Error] using hrJ
  · have hi (n : ℕ) (t : A) := observationLaw_covariate_integral M
      (fun x => (ph n t x - p x) ^ 2) (by fun_prop)
    simpa only [hi, finiteL2Error] using hrP

-- The two nuisance coordinates already carry their measurable versions.
-- @node: fitted_positive_assignment_measurable
/-- If [the binary nuisance functions are admissible](hyp:he), [the assignment probability at any level, extended by zero outside the positive levels, is measurable in covariates](goal). -/
@[fun_prop] lemma fitted_positive_assignment_measurable (L : LevelData Z X)
    (e : NuisanceBin L) (he : BinAdmissible M L e) (k : ℕ) :
    Measurable (positiveValue e.piLev k) := by
  first | fun_prop | skip
  unfold positiveValue
  split_ifs with hk
  · exact (he.2.2.2.1 ⟨k, hk⟩).2.2
  · fun_prop

-- @node: fitted_positive_treatment_measurable
/-- If [the binary nuisance functions are admissible](hyp:he), [the treatment probability at any level, extended by zero outside the positive levels, is measurable in covariates](goal). -/
@[fun_prop] lemma fitted_positive_treatment_measurable (L : LevelData Z X)
    (e : NuisanceBin L) (he : BinAdmissible M L e) (k : ℕ) :
    Measurable (positiveValue e.pLev k) := by
  first | fun_prop | skip
  unfold positiveValue
  split_ifs with hk
  · exact (he.2.2.2.1 ⟨k, hk⟩).1
  · fun_prop

-- @node: nuisanceRates_RP_sq_tendsto_probability_zero
/-- Suppose [the population binary nuisance is admissible](hyp:he0), [every fitted binary nuisance is admissible](hyp:heh), [outcomes are binary almost surely](hyp:hy), [the assignment lower bound is positive](hyp:hc), and [population and fitted positive-level assignment probabilities exceed that bound almost everywhere](hyp:hclip). If [the treated-success regressions satisfy the finite nuisance rates](hyp:hrP), [the assignment probabilities satisfy those rates](hyp:hrpi), and [the selected level does not exceed the number of levels](hyp:hk), then [the observation-distribution squared error of the treated-success residual at that level, evaluated at even sample sizes, converges in probability to zero](goal). -/
lemma nuisanceRates_RP_sq_tendsto_probability_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (L : LevelData Z X) (e0 : NuisanceBin L) (eh : ℕ → A → NuisanceBin L)
    (he0 : BinAdmissible M L e0) (heh : ∀ n a, BinAdmissible M L (eh n a))
    (hy : OutcomeBinaryAE M) (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a (i : PositiveIndex L.K), ∀ᵐ x ∂xLaw M,
      c ≤ e0.piLev i x ∧ c ≤ (eh n a).piLev i x)
    (hrP : FiniteNuisanceRates M μ (fun n a => (eh n a).P1) e0.P1)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) e0.piLev)
    (k : ℕ) (hk : k ≤ L.K) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o, (RP L (eh (2*(n+1)) a) k o - RP L e0 k o) ^ 2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  by_cases hk0 : k = 0
  · subst k
    rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm]
    intro eps heps
    simpa [RP, not_le_of_gt heps] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (𝓝 0))
  have hk : 1 ≤ k ∧ k ≤ L.K := ⟨by omega, hk⟩
  have hp := fitted_positive_assignment_measurable M L e0 he0 k
  have hj := fitted_positive_success_measurable M L e0 he0 k
  have hph (n : ℕ) (a : A) :=
    fitted_positive_assignment_measurable M L (eh (2*(n+1)) a) (heh _ a) k
  have hjh (n : ℕ) (a : A) :=
    fitted_positive_success_measurable M L (eh (2*(n+1)) a) (heh _ a) k
  have hsel : Measurable (fun o : Obs X Z => indicator (o.2.1 ∈ L.S k)) := by fun_prop
  have hres : ∀ᵐ o : Obs X Z ∂observationLaw M,
      |o.2.2.2 * o.2.2.1 - positiveValue e0.P1 k o.1| ≤ 1 := by
    filter_upwards [observationLaw_binary_numerator_range M hy,
      observationLaw_covariate_ae M _ (fitted_positive_success_range M L e0 he0 k)]
      with o ho hj
    exact abs_le.mpr ⟨by linarith [ho.2.1, hj.2], by linarith [ho.2.2, hj.1]⟩
  have hr := dml_observation_ipw_residual_sq_tendsto_probability_zero M μ
    (positiveValue e0.piLev k) (positiveValue e0.P1 k)
    (fun o => o.2.2.2 * o.2.2.1) (fun o => indicator (o.2.1 ∈ L.S k))
    (fun n a => positiveValue (eh (2*(n+1)) a).piLev k)
    (fun n a => positiveValue (eh (2*(n+1)) a).P1 k) c 1 hc hp hj
    (by fun_prop) hsel hph hjh
    (fun n a => (fitted_positive_success_memLp M L _ (heh _ a) k).sub
      (fitted_positive_success_memLp M L e0 he0 k))
    (fun n a => (fitted_positive_treatment_assignment_memLp M L _ (heh _ a) k).2.sub
      (fitted_positive_treatment_assignment_memLp M L e0 he0 k).2)
    (fun n a => by simpa only [positiveValue, dif_pos hk] using hclip _ a ⟨k, hk⟩)
    (Eventually.of_forall (fun o => by unfold indicator; split_ifs <;> norm_num)) hres
    (nuisanceRates_positiveValue M μ L.K _ _ hrP k)
    (nuisanceRates_positiveValue M μ L.K _ _ hrpi k)
  simpa only [RP, if_neg (show k ≠ 0 by omega)] using hr

-- @node: nuisanceRates_Rp_sq_tendsto_probability_zero
/-- Suppose [the population binary nuisance is admissible](hyp:he0), [every fitted binary nuisance is admissible](hyp:heh), [the assignment lower bound is positive](hyp:hc), and [population and fitted positive-level assignment probabilities exceed that bound almost everywhere](hyp:hclip). If [the treatment regressions satisfy the finite nuisance rates](hyp:hrp), [the assignment probabilities satisfy those rates](hyp:hrpi), and [the selected level does not exceed the number of levels](hyp:hk), then [the observation-distribution squared error of the treatment residual at that level, evaluated at even sample sizes, converges in probability to zero](goal). -/
lemma nuisanceRates_Rp_sq_tendsto_probability_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (L : LevelData Z X) (e0 : NuisanceBin L) (eh : ℕ → A → NuisanceBin L)
    (he0 : BinAdmissible M L e0) (heh : ∀ n a, BinAdmissible M L (eh n a))
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a (i : PositiveIndex L.K), ∀ᵐ x ∂xLaw M,
      c ≤ e0.piLev i x ∧ c ≤ (eh n a).piLev i x)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) e0.piLev)
    (k : ℕ) (hk : k ≤ L.K) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o, (Rp L (eh (2*(n+1)) a) k o - Rp L e0 k o) ^ 2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  by_cases hk0 : k = 0
  · subst k
    rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm]
    intro eps heps
    simpa [Rp, not_le_of_gt heps] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (𝓝 0))
  have hk : 1 ≤ k ∧ k ≤ L.K := ⟨by omega, hk⟩
  have hp := fitted_positive_assignment_measurable M L e0 he0 k
  have hj := fitted_positive_treatment_measurable M L e0 he0 k
  have hph (n : ℕ) (a : A) :=
    fitted_positive_assignment_measurable M L (eh (2*(n+1)) a) (heh _ a) k
  have hjh (n : ℕ) (a : A) :=
    fitted_positive_treatment_measurable M L (eh (2*(n+1)) a) (heh _ a) k
  have hsel : Measurable (fun o : Obs X Z => indicator (o.2.1 ∈ L.S k)) := by fun_prop
  have hW : ∀ᵐ o : Obs X Z ∂observationLaw M, o.2.2.1 ∈ Icc (0 : ℝ) 1 := by
    have hm : Measurable (fun s => (M.Xv s, M.Zv s, M.W s, M.Y s)) := by
      first | fun_prop | exact M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY))
    apply (ae_map_iff hm.aemeasurable (measurableSet_Icc.preimage (by fun_prop))).2
    exact Eventually.of_forall (fun s => by rcases M.rangeW s with h | h <;> simp [h])
  have hres : ∀ᵐ o : Obs X Z ∂observationLaw M,
      |o.2.2.1 - positiveValue e0.pLev k o.1| ≤ 1 := by
    have hr : ∀ᵐ x ∂xLaw M, positiveValue e0.pLev k x ∈ Icc (0 : ℝ) 1 := by
      simpa only [positiveValue, dif_pos hk] using
        (he0.2.2.1 ⟨k, hk⟩).mono (fun _ hx => hx.1)
    filter_upwards [hW, observationLaw_covariate_ae M _ hr] with o ho hj
    exact abs_le.mpr ⟨by linarith [ho.1, hj.2], by linarith [ho.2, hj.1]⟩
  have hr := dml_observation_ipw_residual_sq_tendsto_probability_zero M μ
    (positiveValue e0.piLev k) (positiveValue e0.pLev k)
    (fun o => o.2.2.1) (fun o => indicator (o.2.1 ∈ L.S k))
    (fun n a => positiveValue (eh (2*(n+1)) a).piLev k)
    (fun n a => positiveValue (eh (2*(n+1)) a).pLev k) c 1 hc hp hj
    (by fun_prop) hsel hph hjh
    (fun n a => (fitted_positive_treatment_assignment_memLp M L _ (heh _ a) k).1.sub
      (fitted_positive_treatment_assignment_memLp M L e0 he0 k).1)
    (fun n a => (fitted_positive_treatment_assignment_memLp M L _ (heh _ a) k).2.sub
      (fitted_positive_treatment_assignment_memLp M L e0 he0 k).2)
    (fun n a => by simpa only [positiveValue, dif_pos hk] using hclip _ a ⟨k, hk⟩)
    (Eventually.of_forall (fun o => by unfold indicator; split_ifs <;> norm_num)) hres
    (nuisanceRates_positiveValue M μ L.K _ _ hrp k)
    (nuisanceRates_positiveValue M μ L.K _ _ hrpi k)
  simpa only [Rp, if_neg (show k ≠ 0 by omega)] using hr

end Papers.TbsPrteOptimalTransport

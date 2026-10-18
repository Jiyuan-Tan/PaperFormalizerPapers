module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLFullScoreConvergence
public import Papers.TbsPrteOptimalTransport.Helpers.DMLTailAssembly
/-! Second moments and L2 convergence of the terminal baseline correction.
The fitted terminal weight multiplies the actual IPW treatment residual;
its convergence follows from the three component nuisance rates. -/
public section
set_option linter.style.haveILetI false
set_option linter.style.openClassical false
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

-- @node: observationLaw_treatment_range
/-- [Observed treatment lies between zero and one almost surely under the observation law](goal). -/
lemma observationLaw_treatment_range :
    ∀ᵐ o : Obs X Z ∂observationLaw M, o.2.2.1 ∈ Icc (0 : ℝ) 1 := by
  have hm : Measurable (fun s => (M.Xv s, M.Zv s, M.W s, M.Y s)) := by
    first | fun_prop | exact M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY))
  apply (ae_map_iff hm.aemeasurable (measurableSet_Icc.preimage (by fun_prop))).2
  exact Eventually.of_forall (fun s => by rcases M.rangeW s with h | h <;> simp [h])

-- @node: fitted_positive_treatment_range
/-- If [the fitted binary nuisances are admissible](hyp:he), [the fitted treatment probability at any level, with zero used outside the positive levels, lies between zero and one almost everywhere](goal). -/
lemma fitted_positive_treatment_range (L : LevelData Z X) (e : NuisanceBin L)
    (he : BinAdmissible M L e) (i : ℕ) :
    ∀ᵐ x ∂xLaw M, positiveValue e.pLev i x ∈ Icc (0 : ℝ) 1 := by
  by_cases hi : 1 ≤ i ∧ i ≤ L.K
  · simpa only [positiveValue, dif_pos hi] using
      (he.2.2.1 ⟨i, hi⟩).mono (fun _ hx => hx.1)
  · simp only [positiveValue, dif_neg hi]
    exact Eventually.of_forall (fun _ => ⟨le_rfl, zero_le_one⟩)

-- @node: fitted_Rp_measurable
/-- If [the fitted binary nuisances are admissible](hyp:he), [the inverse-assignment-weighted treatment residual at any level is measurable](goal). -/
@[fun_prop] lemma fitted_Rp_measurable (L : LevelData Z X) (e : NuisanceBin L)
    (he : BinAdmissible M L e) (i : ℕ) : Measurable (Rp L e i) := by
  first | fun_prop | skip
  have hp := fitted_positive_treatment_measurable M L e he i
  have hpi := fitted_positive_assignment_measurable M L e he i
  unfold Rp
  split_ifs <;> fun_prop

-- The treatment bound does not require the binary-outcome alternative.
-- @node: fitted_Rp_abs_bound
/-- If [the fitted nuisances are admissible](hyp:he), [the clipping constant is positive](hyp:hc), [every positive-level fitted assignment probability is at least that constant almost everywhere](hyp:hclip), and [the level does not exceed the level count](hyp:hi), [the absolute inverse-assignment-weighted treatment residual is almost surely at most the reciprocal clipping constant](goal). -/
lemma fitted_Rp_abs_bound (L : LevelData Z X) (e : NuisanceBin L)
    (he : BinAdmissible M L e) (c : ℝ) (hc : 0 < c)
    (hclip : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (i : ℕ) (hi : i ≤ L.K) :
    ∀ᵐ o ∂observationLaw M, |Rp L e i o| ≤ 1 / c := by
  by_cases hi0 : i = 0
  · subst i
    exact Eventually.of_forall (fun o => by simp only [Rp, ↓reduceIte, abs_zero]; positivity)
  have hip : 1 ≤ i ∧ i ≤ L.K := ⟨by omega, hi⟩
  have hcl : ∀ᵐ x ∂xLaw M, c ≤ positiveValue e.piLev i x := by
    simpa only [positiveValue, dif_pos hip] using hclip ⟨i, hip⟩
  filter_upwards [observationLaw_treatment_range M,
    observationLaw_covariate_ae M _ (fitted_positive_treatment_range M L e he i),
    observationLaw_covariate_ae M _ hcl] with o ho hj hp
  have hr : |o.2.2.1 - positiveValue e.pLev i o.1| ≤ 1 :=
    abs_le.mpr ⟨by linarith [ho.1, hj.2], by linarith [ho.2, hj.1]⟩
  have ha : |indicator (o.2.1 ∈ L.S i)| ≤ 1 := by
    unfold indicator
    split_ifs <;> norm_num
  rw [Rp, if_neg hi0, abs_mul, abs_div, abs_of_pos (hc.trans_le hp)]
  calc
    _ ≤ (1 / positiveValue e.piLev i o.1) * 1 := by
      have hp0 := hc.trans_le hp
      gcongr
    _ ≤ 1 / c := by
      rw [mul_one]
      exact div_le_div_of_nonneg_left zero_le_one hc hp

-- @node: fitted_Rp_memLp
/-- If [the fitted nuisances are admissible](hyp:he), [the clipping constant is positive](hyp:hc), [all positive-level fitted assignment probabilities are bounded below by it almost everywhere](hyp:hclip), and [the index is no larger than the level count](hyp:hi), [the inverse-assignment-weighted treatment residual has a finite second moment under the observation law](goal). -/
lemma fitted_Rp_memLp (L : LevelData Z X) (e : NuisanceBin L)
    (he : BinAdmissible M L e) (c : ℝ) (hc : 0 < c)
    (hclip : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (i : ℕ) (hi : i ≤ L.K) : MemLp (Rp L e i) 2 (observationLaw M) := by
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  apply MemLp.of_bound (by fun_prop) (1 / c)
  simpa only [Real.norm_eq_abs] using fitted_Rp_abs_bound M L e he c hc hclip i hi

-- @node: fitted_gammaTail_Rp_memLp
/-- If [the fitted nuisances are admissible](hyp:he), [the clipping constant is positive](hyp:hc), [all positive-level fitted assignment probabilities are at least this lower bound almost everywhere](hyp:hclip), and [the level is within the level count](hyp:hi), [the terminal weight times the inverse-assignment-weighted treatment residual has a finite second moment](goal). -/
lemma fitted_gammaTail_Rp_memLp (L : LevelData Z X) (e : NuisanceBin L)
    (he : BinAdmissible M L e) (c : ℝ) (hc : 0 < c)
    (hclip : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (i : ℕ) (hi : i ≤ L.K) :
    MemLp (fun o => e.gammaTail o.1 * Rp L e i o) 2 (observationLaw M) := by
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  have hg : Measurable e.gammaTail := he.2.2.2.2.2.2.2.2.2.2.2.2
  apply MemLp.of_bound (by fun_prop) (1/c)
  filter_upwards [fitted_Rp_abs_bound M L e he c hc hclip i hi,
    observationLaw_covariate_ae M _ he.2.2.2.2.2.2.2.2.2.2.2.1] with o hr hg
  have hb : |e.gammaTail o.1| ≤ 1 := by
    rw [abs_of_nonneg hg.1]
    exact hg.2
  rw [Real.norm_eq_abs, abs_mul]
  exact (mul_le_mul hb hr (abs_nonneg _) zero_le_one).trans_eq (one_mul _)

-- Weight, treatment regression and denominator errors each converge from
-- the stated component rates, including the fixed zero boundary.
-- @node: nuisanceRates_gammaTail_Rp_sq_tendsto_probability_zero
/-- Suppose [the reference nuisances are admissible](hyp:he0), [every fitted nuisance vector is admissible](hyp:heh), [the clipping constant is positive](hyp:hc), and [reference and fitted positive-level assignment probabilities are uniformly bounded below by it almost everywhere](hyp:hclip). If [the treatment regressions satisfy the finite nuisance rate conditions](hyp:hrp), [the assignment probabilities satisfy those rate conditions](hyp:hrpi), [the terminal weights satisfy those rate conditions](hyp:hrg), and [the level is no larger than the level count](hyp:hi), [the integrated squared error of the terminal-weighted treatment residual, along even sample sizes, converges to zero in probability](goal). -/
lemma nuisanceRates_gammaTail_Rp_sq_tendsto_probability_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (L : LevelData Z X) (e0 : NuisanceBin L) (eh : ℕ → A → NuisanceBin L)
    (he0 : BinAdmissible M L e0) (heh : ∀ n a, BinAdmissible M L (eh n a))
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a (i : PositiveIndex L.K), ∀ᵐ x ∂xLaw M,
      c ≤ e0.piLev i x ∧ c ≤ (eh n a).piLev i x)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) e0.piLev)
    (hrg : FiniteNuisanceRates M μ (fun n a (_ : Unit) => (eh n a).gammaTail)
      (fun _ => e0.gammaTail))
    (i : ℕ) (hi : i ≤ L.K) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o,
        ((eh (2*(n+1)) a).gammaTail o.1 * Rp L (eh (2*(n+1)) a) i o -
          e0.gammaTail o.1 * Rp L e0 i o)^2 ∂observationLaw M)
      atTop (fun _ _ => 0) := by
  have hg0 : Measurable e0.gammaTail := he0.2.2.2.2.2.2.2.2.2.2.2.2
  have hgh (n : ℕ) (a : A) : Measurable (eh n a).gammaTail :=
    (heh n a).2.2.2.2.2.2.2.2.2.2.2.2
  apply dml_weighted_residual_sq_tendsto_probability_zero μ (observationLaw M)
    (fun o => e0.gammaTail o.1) (Rp L e0 i)
    (fun n a o => (eh (2*(n+1)) a).gammaTail o.1)
    (fun n a => Rp L (eh (2*(n+1)) a) i) 1 (1 / c)
    (by fun_prop) (by fun_prop) (by intro n a; fun_prop)
    (by intro n a; first | fun_prop | exact fitted_Rp_measurable M L _ (heh _ a) i)
  · intro n a
    exact ((fitted_prop_gammaTail_memLp M L _ (heh _ a)).2.sub
      (fitted_prop_gammaTail_memLp M L e0 he0).2).comp_measurePreserving
      (observationLaw_fst_measurePreserving M)
  · intro n a
    exact (fitted_Rp_memLp M L _ (heh _ a) c hc
      (fun j => (hclip _ a j).mono (fun _ hx => hx.2)) i hi).sub
        (fitted_Rp_memLp M L e0 he0 c hc
          (fun j => (hclip (2*(n+1)) a j).mono (fun _ hx => hx.1)) i hi)
  · intro n a
    apply observationLaw_covariate_ae M (fun x => |(eh (2*(n+1)) a).gammaTail x| ≤ 1)
    filter_upwards [(heh (2*(n+1)) a).2.2.2.2.2.2.2.2.2.2.2.1] with x hx
    rw [abs_of_nonneg hx.1]
    exact hx.2
  · exact fun n a => fitted_Rp_abs_bound M L e0 he0 c hc
      (fun j => (hclip n a j).mono (fun _ hx => hx.1)) i hi
  · exact nuisanceRates_covariate_sq_tendsto_probability_zero M μ _ _
      (fun _ => hg0) (fun n a _ => hgh n a) hrg ()
  · exact nuisanceRates_Rp_sq_tendsto_probability_zero M μ L e0 eh he0 heh
      c hc hclip hrp hrpi i hi

-- @node: commonTailScore_binary_residual_split
/-- [The terminal binary score equals the lower outcome endpoint times the difference between the policy value with its derivative-based treatment correction and the terminal baseline, which is the policy-region treatment regression plus the terminal-weighted inverse-assignment treatment residual](goal). -/
lemma commonTailScore_binary_residual_split (phi dphi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (e : NuisanceBin L) (o : Obs X Z) :
    commonTailScore M phi dphi L e.prop e.pLev e.piLev e.gammaTail o =
      M.yMin * (indicator (o.2.1 ∈ policyUnion L L.K 1) *
        (phi o.2.1 o.1 (e.prop o.2.1 o.1) +
          dphi o.2.1 o.1 (e.prop o.2.1 o.1) * (o.2.2.1 - e.prop o.2.1 o.1)) -
        (indicator (o.2.1 ∈ policyUnion L L.K 1) * positiveValue e.pLev L.K o.1 +
          e.gammaTail o.1 * Rp L e L.K o)) := by
  by_cases hk : L.K = 0
  · simp only [commonTailScore, Rp, hk, ↓reduceIte]
    ring
  · simp only [commonTailScore, Rp, if_neg hk, div_eq_mul_inv]
    ring

-- @node: fitted_tail_baseline_memLp
/-- If [the fitted nuisances are admissible](hyp:he), [the clipping constant is positive](hyp:hc), and [positive-level fitted assignment probabilities are bounded below by it almost everywhere](hyp:hclip), [the terminal baseline, consisting of the policy-region treatment regression plus the terminal-weighted treatment residual, has a finite second moment](goal). -/
lemma fitted_tail_baseline_memLp (L : LevelData Z X) (e : NuisanceBin L)
    (he : BinAdmissible M L e) (c : ℝ) (hc : 0 < c)
    (hclip : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x) :
    MemLp (fun o : Obs X Z =>
      indicator (o.2.1 ∈ policyUnion L L.K 1) * positiveValue e.pLev L.K o.1 +
        e.gammaTail o.1 * Rp L e L.K o) 2 (observationLaw M) := by
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  have hm := fitted_positive_treatment_measurable M L e he L.K
  have hev : Measurable (fun o : Obs X Z =>
      indicator (o.2.1 ∈ policyUnion L L.K 1)) := by fun_prop
  have hp : MemLp (fun o : Obs X Z =>
      indicator (o.2.1 ∈ policyUnion L L.K 1) * positiveValue e.pLev L.K o.1)
      2 (observationLaw M) := by
    apply MemLp.of_bound (by fun_prop) 1
    filter_upwards [observationLaw_covariate_ae M _
      (fitted_positive_treatment_range M L e he L.K)] with o ho
    have hb : |indicator (o.2.1 ∈ policyUnion L L.K 1)| ≤ 1 := by
      unfold indicator
      split_ifs <;> norm_num
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ho.1]
    exact (mul_le_mul hb ho.2 ho.1 zero_le_one).trans_eq (one_mul _)
  exact hp.add (fitted_gammaTail_Rp_memLp M L e he c hc hclip L.K le_rfl)

-- Both terms are the baseline part in commonTailScore_binary_residual_split.
-- The event indicator has magnitude at most one, so its squared error is
-- bounded by the covariate regression energy.
-- @node: nuisanceRates_tail_baseline_sq_tendsto_probability_zero
/-- Suppose [the reference nuisances are admissible](hyp:he0), [all fitted nuisances are admissible](hyp:heh), [the clipping constant is positive](hyp:hc), and [reference and fitted assignment probabilities at positive levels are uniformly bounded below by it almost everywhere](hyp:hclip). If [the treatment regressions satisfy the finite nuisance rate conditions](hyp:hrp), [the assignment probabilities satisfy those rate conditions](hyp:hrpi), and [the terminal weights satisfy those rate conditions](hyp:hrg), [the integrated squared error of the terminal baseline at even sample sizes converges to zero in probability](goal). -/
lemma nuisanceRates_tail_baseline_sq_tendsto_probability_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (L : LevelData Z X) (e0 : NuisanceBin L) (eh : ℕ → A → NuisanceBin L)
    (he0 : BinAdmissible M L e0) (heh : ∀ n a, BinAdmissible M L (eh n a))
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a (i : PositiveIndex L.K), ∀ᵐ x ∂xLaw M,
      c ≤ e0.piLev i x ∧ c ≤ (eh n a).piLev i x)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) e0.piLev)
    (hrg : FiniteNuisanceRates M μ (fun n a (_ : Unit) => (eh n a).gammaTail)
      (fun _ => e0.gammaTail)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o : Obs X Z,
        ((indicator (o.2.1 ∈ policyUnion L L.K 1) *
            positiveValue (eh (2*(n+1)) a).pLev L.K o.1 +
          (eh (2*(n+1)) a).gammaTail o.1 * Rp L (eh (2*(n+1)) a) L.K o) -
        (indicator (o.2.1 ∈ policyUnion L L.K 1) * positiveValue e0.pLev L.K o.1 +
          e0.gammaTail o.1 * Rp L e0 L.K o)) ^ 2 ∂observationLaw M)
      atTop (fun _ _ => 0) := by
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  let ev := fun o : Obs X Z => indicator (o.2.1 ∈ policyUnion L L.K 1)
  let f := fun n a (o : Obs X Z) => ev o *
    (positiveValue (eh (2*(n+1)) a).pLev L.K o.1 - positiveValue e0.pLev L.K o.1)
  let g := fun n a (o : Obs X Z) =>
    (eh (2*(n+1)) a).gammaTail o.1 * Rp L (eh (2*(n+1)) a) L.K o -
      e0.gammaTail o.1 * Rp L e0 L.K o
  have hm0 := fitted_positive_treatment_measurable M L e0 he0 L.K
  have hmh (n : ℕ) (a : A) := fitted_positive_treatment_measurable M L (eh n a) (heh n a) L.K
  have hfm (n : ℕ) (a : A) : Measurable (f n a) := by dsimp only [f, ev]; fun_prop
  have hmem (n : ℕ) (a : A) : MemLp
      (fun o : Obs X Z => positiveValue (eh (2*(n+1)) a).pLev L.K o.1 -
        positiveValue e0.pLev L.K o.1) 2 (observationLaw M) :=
    ((fitted_positive_treatment_assignment_memLp M L _ (heh _ a) L.K).1.sub
      (fitted_positive_treatment_assignment_memLp M L e0 he0 L.K).1).comp_measurePreserving
        (observationLaw_fst_measurePreserving M)
  have hbound (n : ℕ) (a : A) (o : Obs X Z) :
      (f n a o)^2 ≤ (positiveValue (eh (2*(n+1)) a).pLev L.K o.1 -
        positiveValue e0.pLev L.K o.1)^2 := by
    dsimp only [f, ev, indicator]
    split_ifs <;> simp [sq_nonneg]
  have hfi (n : ℕ) (a : A) : Integrable (fun o => (f n a o)^2) (observationLaw M) :=
    (hmem n a).integrable_sq.mono' (by fun_prop) (by
      exact Eventually.of_forall (fun o => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (f n a o))]
          using hbound n a o))
  have hf (n : ℕ) (a : A) : MemLp (f n a) 2 (observationLaw M) :=
    (memLp_two_iff_integrable_sq (hfm n a).aestronglyMeasurable).mpr (hfi n a)
  have hr := nuisanceRates_covariate_sq_tendsto_probability_zero M μ _ _
    (fun i => fitted_positive_treatment_measurable M L e0 he0 i)
    (fun n a i => fitted_positive_treatment_measurable M L _ (heh n a) i)
    (nuisanceRates_positiveValue M μ L.K _ _ hrp) L.K
  have hrf : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o, (f n a o)^2 ∂observationLaw M) atTop (fun _ _ => 0) := by
    apply probability_zero_of_nonneg_le μ _ _ hr
    intro n
    apply Eventually.of_forall
    intro a
    exact ⟨integral_nonneg (fun _ => sq_nonneg _),
      integral_mono (hfi n a) (hmem n a).integrable_sq (hbound n a)⟩
  have hg (n : ℕ) (a : A) : MemLp (g n a) 2 (observationLaw M) :=
    (fitted_gammaTail_Rp_memLp M L _ (heh _ a) c hc
      (fun i => (hclip _ a i).mono (fun _ hx => hx.2)) L.K le_rfl).sub
    (fitted_gammaTail_Rp_memLp M L e0 he0 c hc
      (fun i => (hclip (2*(n+1)) a i).mono (fun _ hx => hx.1)) L.K le_rfl)
  have hz : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun (_ : ℕ) (_ : A) => (0 : ℝ)) atTop (fun _ _ => 0) := by
    rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm]
    intro eps heps
    simpa only [sub_self, norm_zero, not_le.mpr heps, Set.ofPred_false,
      measure_empty] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (𝓝 0))
  have hs := dml_three_term_sq_tendsto_probability_zero μ (observationLaw M)
    f g (fun _ _ _ => 0) hf hg (fun _ _ => MemLp.zero') hrf
    (nuisanceRates_gammaTail_Rp_sq_tendsto_probability_zero M μ L e0 eh he0 heh
      c hc hclip hrp hrpi hrg L.K le_rfl) (by simpa using hz)
  convert hs using 1
  funext n a
  congr 1
  funext o
  dsimp only [f, g, ev]
  ring

-- @node: nuisanceRates_tail_baseline_l2_tendsto_probability_zero
/-- Suppose [the reference nuisances are admissible](hyp:he0), [every fitted nuisance vector is admissible](hyp:heh), [the clipping constant is positive](hyp:hc), and [reference and fitted positive-level assignment probabilities are uniformly bounded below by it almost everywhere](hyp:hclip). If [the treatment regressions satisfy the finite nuisance rate conditions](hyp:hrp), [the assignment probabilities satisfy those rate conditions](hyp:hrpi), and [the terminal weights satisfy those rate conditions](hyp:hrg), [the population L2 error of the terminal baseline at even sample sizes converges to zero in probability](goal). -/
lemma nuisanceRates_tail_baseline_l2_tendsto_probability_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (L : LevelData Z X) (e0 : NuisanceBin L) (eh : ℕ → A → NuisanceBin L)
    (he0 : BinAdmissible M L e0) (heh : ∀ n a, BinAdmissible M L (eh n a))
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a (i : PositiveIndex L.K), ∀ᵐ x ∂xLaw M,
      c ≤ e0.piLev i x ∧ c ≤ (eh n a).piLev i x)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) e0.piLev)
    (hrg : FiniteNuisanceRates M μ (fun n a (_ : Unit) => (eh n a).gammaTail)
      (fun _ => e0.gammaTail)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt (∫ o : Obs X Z,
        ((indicator (o.2.1 ∈ policyUnion L L.K 1) *
            positiveValue (eh (2*(n+1)) a).pLev L.K o.1 +
          (eh (2*(n+1)) a).gammaTail o.1 * Rp L (eh (2*(n+1)) a) L.K o) -
        (indicator (o.2.1 ∈ policyUnion L L.K 1) * positiveValue e0.pLev L.K o.1 +
          e0.gammaTail o.1 * Rp L e0 L.K o)) ^ 2 ∂observationLaw M))
      atTop (fun _ _ => 0) := by
  have hs := nuisanceRates_tail_baseline_sq_tendsto_probability_zero M μ L e0 eh
    he0 heh c hc hclip hrp hrpi hrg
  have hcont : Continuous (fun t : ℝ => Real.sqrt t) := by fun_prop
  simpa only [Real.sqrt_zero] using
    Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt hcont.continuousAt hs

end Papers.TbsPrteOptimalTransport

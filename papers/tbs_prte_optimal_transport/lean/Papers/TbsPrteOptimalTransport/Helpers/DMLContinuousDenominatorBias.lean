module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousFullRates
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousTreatmentResidual
/-! Continuous full-interval denominator remainders.
The true treatment probability and fitted signed product weight are bounded by
one. Clipped assignment reciprocals leave a product of the assignment and
outcome-regression errors, which is negligible after root-n scaling. -/
public section
set_option linter.style.openClassical false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: nuisanceRates_continuous_full_mean_quarter_rate
/-- If [the plus full-interval mean regressions satisfy the finite nuisance rates](hyp:hrplus) and
[the minus full-interval mean regressions satisfy those rates](hyp:hrminus), then
[the L² error of either selected full-interval mean regression, evaluated at sample size twice a positive integer, is of smaller order in probability than that sample size to the power minus one quarter](goal). -/
lemma nuisanceRates_continuous_full_mean_quarter_rate
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (L : LevelData Z X) (e0 : NuisanceCont L) (eh : ℕ → A → NuisanceCont L)
    (hrplus : FiniteNuisanceRates M μ (fun n a => (eh n a).JfullPlus) e0.JfullPlus)
    (hrminus : FiniteNuisanceRates M μ (fun n a => (eh n a).JfullMinus) e0.JfullMinus)
    (plus : Bool) (k : Fin L.K) :
    Causalean.Stat.IsLittleOp
      (fun n a => finiteL2Error M
        (fun x => if plus then fullValue (eh (2*(n+1)) a).JfullPlus k x
          else minusFullValue (eh (2*(n+1)) a) k x)
        (fun x => if plus then fullValue e0.JfullPlus k x else minusFullValue e0 k x))
      (fun n => ((2*(n+1) : ℕ) : ℝ)^(-1/4 : ℝ)) μ := by
  cases plus
  · by_cases hk : 1 ≤ k.val ∧ k.val < L.K
    · simpa only [Bool.false_eq_true, if_false, minusFullValue, dif_pos hk] using
        hrminus ⟨k, hk⟩
    · have hz := maxErrors_isLittleOp μ ([] : List Unit) (fun _ _ _ => (0 : ℝ))
        (fun n => ((2*(n+1) : ℕ) : ℝ)^(-1/4 : ℝ))
        (fun n => Real.rpow_pos_of_pos (by positivity) _) (by simp)
      simpa only [Bool.false_eq_true, if_false, minusFullValue, dif_neg hk, finiteL2Error,
        sub_self, zero_pow (by norm_num : 2 ≠ 0), integral_zero, Real.sqrt_zero,
        List.map_nil, maxErrors, List.foldr_nil] using hz
  · simpa only [Bool.true_eq, if_true, fullValue, dif_pos k.isLt] using hrplus k

-- This is the regression-times-denominator remainder in the conditional
-- mean expansion, including the structural-zero minus correction.
-- @node: fitted_continuous_full_denominator_bias_bound
/-- If [the reference nuisance record is admissible](hyp:he0), [the fitted record is admissible](hyp:he),
[the clipping constant is positive](hyp:hc), and [every fitted positive-level assignment probability is almost surely at least that constant](hyp:hclip), then
[the selected full-interval regression-times-denominator remainder is integrable, and its absolute population mean is bounded by the product of the assignment-probability and mean-regression L² errors divided by the clipping constant](goal). -/
lemma fitted_continuous_full_denominator_bias_bound (L : LevelData Z X)
    (e0 e : NuisanceCont L) (he0 : ContAdmissible M L e0)
    (he : ContAdmissible M L e) (c : ℝ) (hc : 0 < c)
    (hclip : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (plus : Bool) (k : Fin L.K) :
    let i := if plus then k.val+1 else k.val
    let J := fun (e' : NuisanceCont L) x =>
      if plus then fullValue e'.JfullPlus k x else minusFullValue e' k x
    Integrable (fun x => (e.gammaFull k x * positiveValue e0.pLev i x) *
      (1 - positiveValue e0.piLev i x / positiveValue e.piLev i x) *
        (J e x - J e0 x)) (xLaw M) ∧
    |∫ x, (e.gammaFull k x * positiveValue e0.pLev i x) *
      (1 - positiveValue e0.piLev i x / positiveValue e.piLev i x) *
        (J e x - J e0 x) ∂xLaw M| ≤
      finiteL2Error M (positiveValue e.piLev i) (positiveValue e0.piLev i) *
        finiteL2Error M (J e) (J e0) / c := by
  dsimp only
  let i : ℕ := if plus then k.val+1 else k.val
  let J := fun (e' : NuisanceCont L) x =>
    if plus then fullValue e'.JfullPlus k x else minusFullValue e' k x
  by_cases hi0 : i = 0
  · have hplus : plus = false := by cases plus <;> simp_all [i]
    have hk0 : k.val = 0 := by simpa [i, hplus] using hi0
    simp [hplus, minusFullValue, hk0, finiteL2Error]
  have hi : 1 ≤ i ∧ i ≤ L.K := by
    dsimp only [i] at *
    cases plus <;> simp_all <;> omega
  have hJ (e' : NuisanceCont L) (he' : ContAdmissible M L e') :
      MemLp (J e') 2 (xLaw M) := by
    cases plus
    · exact (fitted_continuous_full_coordinate_memLp M L e' he' k).2.2
    · exact (fitted_continuous_full_coordinate_memLp M L e' he' k).2.1
  have hpi := (fitted_continuous_treatment_assignment_memLp M L e he i).2.sub
    (fitted_continuous_treatment_assignment_memLp M L e0 he0 i).2
  have hj := (hJ e he).sub (hJ e0 he0)
  rw [l2Error_eq_eLpNorm M _ _ hpi, l2Error_eq_eLpNorm M _ _ hj]
  have hgm := (fitted_continuous_gammaFull_coordinates M L e he k).1
  have hpm := (fitted_continuous_full_coordinates M L e0 he0 i).1.1
  simpa only [one_mul] using
    (weighted_clipped_assignment_regression_L2_bound (xLaw M)
      (fun x => e.gammaFull k x * positiveValue e0.pLev i x)
      (positiveValue e0.piLev i) (positiveValue e.piLev i)
      (fun x => J e x - J e0 x) c 1 hc zero_le_one
      (by fun_prop)
      (fitted_continuous_assignment_coordinates M L e0 he0 i).1
      (fitted_continuous_assignment_coordinates M L e he i).1
      (by simpa only [positiveValue, dif_pos hi] using hclip ⟨i, hi⟩)
      (by
        filter_upwards [(fitted_continuous_gammaFull_coordinates M L e he k).2,
          (fitted_continuous_full_coordinates M L e0 he0 i).1.2] with x hg hp
        rw [Real.norm_eq_abs, abs_mul]
        exact (mul_le_mul hg hp (abs_nonneg _) zero_le_one).trans_eq (one_mul _))
      hpi hj)

-- @node: nuisanceRates_continuous_full_denominator_bias_root_n_negligible
/-- Suppose [the reference record is admissible](hyp:he0), [every fitted record is admissible](hyp:heh),
[the clipping constant is positive](hyp:hc), and [all fitted positive-level assignment probabilities exceed that constant almost surely](hyp:hclip).
If [assignment probabilities](hyp:hrpi), [plus full-interval means](hyp:hrplus), and [minus full-interval means](hyp:hrminus) satisfy the finite nuisance rates, then
[the selected full-interval regression-times-denominator population remainder, evaluated at sample size twice a positive integer and scaled by the square root of that integer, converges in probability to zero](goal). -/
lemma nuisanceRates_continuous_full_denominator_bias_root_n_negligible
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (L : LevelData Z X) (e0 : NuisanceCont L) (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L e0) (heh : ∀ n a, ContAdmissible M L (eh n a))
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a (i : PositiveIndex L.K), ∀ᵐ x ∂xLaw M, c ≤ (eh n a).piLev i x)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) e0.piLev)
    (hrplus : FiniteNuisanceRates M μ (fun n a => (eh n a).JfullPlus) e0.JfullPlus)
    (hrminus : FiniteNuisanceRates M μ (fun n a => (eh n a).JfullMinus) e0.JfullMinus)
    (plus : Bool) (k : Fin L.K) :
    let i := if plus then k.val+1 else k.val
    let J := fun (e' : NuisanceCont L) x =>
      if plus then fullValue e'.JfullPlus k x else minusFullValue e' k x
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
        (∫ x, ((eh (2*(n+1)) a).gammaFull k x * positiveValue e0.pLev i x) *
          (1 - positiveValue e0.piLev i x / positiveValue (eh (2*(n+1)) a).piLev i x) *
            (J (eh (2*(n+1)) a) x - J e0 x) ∂xLaw M))
      atTop (fun _ _ => 0) := by
  dsimp only
  have hpi := nuisanceRates_positiveValue M μ L.K _ _ hrpi
    (if plus then k.val+1 else k.val)
  have hj := nuisanceRates_continuous_full_mean_quarter_rate M μ L e0 eh
    hrplus hrminus plus k
  have hp := dml_quarter_rate_product μ _ _ hpi hj
  apply dml_root_n_bias_tendsto_probability μ
  apply Causalean.Stat.IsLittleOp.of_abs_le_const_mul (by positivity : 0 < 1 / c) hp
  intro n a
  have hb := (fitted_continuous_full_denominator_bias_bound M L e0
    (eh (2*(n+1)) a) he0 (heh _ a) c hc (hclip _ a) plus k).2
  apply hb.trans
  rw [div_eq_mul_inv, one_div, mul_comm]
  exact mul_le_mul_of_nonneg_left (le_abs_self _) (inv_nonneg.mpr hc.le)


-- The two signed corrections are aggregated only after each denominator
-- remainder has been bounded, so no cancellation is needed for the rate.
-- @node: fitted_continuous_full_denominator_block_bias_bound
/-- Suppose [the reference record is admissible](hyp:he0), [the fitted record is admissible](hyp:he),
[the clipping constant is positive](hyp:hc), and [fitted positive-level assignment probabilities are almost surely bounded below by that constant](hyp:hclip).
If [the assignment-error bound is nonnegative](hyp:hwt), [every signed full-interval mean-regression L² error is at most the regression-error bound](hyp:hj), and
[every corresponding assignment-probability L² error is at most the assignment-error bound](hyp:hpi), then
[the sum across levels of plus-minus regression-times-denominator remainders is integrable, with absolute population mean at most twice the level count divided by the clipping constant times the two error bounds](goal). -/
lemma fitted_continuous_full_denominator_block_bias_bound (L : LevelData Z X)
    (e0 e : NuisanceCont L) (he0 : ContAdmissible M L e0)
    (he : ContAdmissible M L e) (c : ℝ) (hc : 0 < c)
    (hclip : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (reg wt : ℝ) (hwt : 0 ≤ wt)
    (hj : ∀ (plus : Bool) (k : Fin L.K), finiteL2Error M
      (fun x => if plus then fullValue e.JfullPlus k x else minusFullValue e k x)
      (fun x => if plus then fullValue e0.JfullPlus k x else minusFullValue e0 k x) ≤ reg)
    (hpi : ∀ (plus : Bool) (k : Fin L.K), finiteL2Error M
      (positiveValue e.piLev (if plus then k.val+1 else k.val))
      (positiveValue e0.piLev (if plus then k.val+1 else k.val)) ≤ wt) :
    let B := fun (plus : Bool) (k : Fin L.K) x =>
      (e.gammaFull k x * positiveValue e0.pLev (if plus then k.val+1 else k.val) x) *
        (1 - positiveValue e0.piLev (if plus then k.val+1 else k.val) x /
          positiveValue e.piLev (if plus then k.val+1 else k.val) x) *
        ((if plus then fullValue e.JfullPlus k x else minusFullValue e k x) -
          (if plus then fullValue e0.JfullPlus k x else minusFullValue e0 k x))
    Integrable (fun x => ∑ k : Fin L.K, (B true k x - B false k x)) (xLaw M) ∧
      |∫ x, ∑ k : Fin L.K, (B true k x - B false k x) ∂xLaw M| ≤
        (2 * (L.K : ℝ) / c) * (reg * wt) := by
  dsimp only
  let B := fun (plus : Bool) (k : Fin L.K) x =>
    (e.gammaFull k x * positiveValue e0.pLev (if plus then k.val+1 else k.val) x) *
      (1 - positiveValue e0.piLev (if plus then k.val+1 else k.val) x /
        positiveValue e.piLev (if plus then k.val+1 else k.val) x) *
      ((if plus then fullValue e.JfullPlus k x else minusFullValue e k x) -
        (if plus then fullValue e0.JfullPlus k x else minusFullValue e0 k x))
  have hb (plus : Bool) (k : Fin L.K) :=
    fitted_continuous_full_denominator_bias_bound M L e0 e he0 he c hc hclip plus k
  have hi (k : Fin L.K) : Integrable (fun x => B true k x - B false k x) (xLaw M) :=
    (hb true k).1.sub (hb false k).1
  have hbound (plus : Bool) (k : Fin L.K) :
      |∫ x, B plus k x ∂xLaw M| ≤ wt * reg / c := by
    apply (hb plus k).2.trans
    exact div_le_div_of_nonneg_right
      (mul_le_mul (hpi plus k) (hj plus k) (Real.sqrt_nonneg _) hwt) hc.le
  refine ⟨integrable_finsetSum _ (fun k _ => hi k), ?_⟩
  rw [integral_finsetSum _ (fun k _ => hi k)]
  calc
    _ ≤ ∑ k : Fin L.K, |∫ x, B true k x - B false k x ∂xLaw M| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin L.K, (wt * reg / c + wt * reg / c) := by
      apply Finset.sum_le_sum
      intro k _
      rw [integral_sub (hb true k).1 (hb false k).1]
      exact (abs_sub _ _).trans (add_le_add (hbound true k) (hbound false k))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

-- @node: nuisanceRates_continuous_full_denominator_block_bias_root_n_negligible
/-- If [the reference record is admissible](hyp:he0), [all fitted records are admissible](hyp:heh),
[the clipping constant is positive](hyp:hc), [all fitted positive-level assignment probabilities are almost surely at least that constant](hyp:hclip), and
[assignment probabilities](hyp:hrpi), [plus full-interval means](hyp:hrplus), and [minus full-interval means](hyp:hrminus) satisfy the finite nuisance rates, then
[the population mean of the full sum of plus-minus regression-times-denominator remainders, evaluated at sample size twice a positive integer and scaled by the square root of that integer, converges in probability to zero](goal). -/
lemma nuisanceRates_continuous_full_denominator_block_bias_root_n_negligible
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (L : LevelData Z X) (e0 : NuisanceCont L) (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L e0) (heh : ∀ n a, ContAdmissible M L (eh n a))
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a (i : PositiveIndex L.K), ∀ᵐ x ∂xLaw M, c ≤ (eh n a).piLev i x)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) e0.piLev)
    (hrplus : FiniteNuisanceRates M μ (fun n a => (eh n a).JfullPlus) e0.JfullPlus)
    (hrminus : FiniteNuisanceRates M μ (fun n a => (eh n a).JfullMinus) e0.JfullMinus) :
    let B := fun n a (plus : Bool) (k : Fin L.K) x =>
      ((eh (2*(n+1)) a).gammaFull k x *
        positiveValue e0.pLev (if plus then k.val+1 else k.val) x) *
        (1 - positiveValue e0.piLev (if plus then k.val+1 else k.val) x /
          positiveValue (eh (2*(n+1)) a).piLev (if plus then k.val+1 else k.val) x) *
        ((if plus then fullValue (eh (2*(n+1)) a).JfullPlus k x
          else minusFullValue (eh (2*(n+1)) a) k x) -
          (if plus then fullValue e0.JfullPlus k x else minusFullValue e0 k x))
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
        (∫ x, ∑ k : Fin L.K, (B n a true k x - B n a false k x) ∂xLaw M))
      atTop (fun _ _ => 0) := by
  dsimp only
  let ks := (Finset.univ : Finset (Bool × Fin L.K)).toList
  let J := fun (e : NuisanceCont L) (i : Bool × Fin L.K) x =>
    if i.1 then fullValue e.JfullPlus i.2 x else minusFullValue e i.2 x
  let pi := fun (e : NuisanceCont L) (i : Bool × Fin L.K) =>
    positiveValue e.piLev (if i.1 then i.2.val+1 else i.2.val)
  let reg := fun n a => maxErrors (ks.map (fun i =>
    finiteL2Error M (J (eh (2*(n+1)) a) i) (J e0 i)))
  let wt := fun n a => maxErrors (ks.map (fun i =>
    finiteL2Error M (pi (eh (2*(n+1)) a) i) (pi e0 i)))
  have hr := nuisanceRates_finite_maxErrors M μ
    (fun n a => J (eh n a)) (J e0) ks (fun i =>
      nuisanceRates_continuous_full_mean_quarter_rate M μ L e0 eh hrplus hrminus i.1 i.2)
  have hw := nuisanceRates_finite_maxErrors M μ
    (fun n a => pi (eh n a)) (pi e0) ks (fun i =>
      nuisanceRates_positiveValue M μ L.K _ _ hrpi (if i.1 then i.2.val+1 else i.2.val))
  have hp := dml_quarter_rate_product μ reg wt hr hw
  apply dml_root_n_bias_tendsto_probability μ
  apply Causalean.Stat.IsLittleOp.of_abs_le_const_mul
    (by positivity : 0 < 2 * (L.K : ℝ) / c + 1) hp
  intro n a
  have hb := (fitted_continuous_full_denominator_block_bias_bound M L e0
    (eh (2*(n+1)) a) he0 (heh _ a) c hc (hclip _ a)
    (reg n a) (wt n a) (maxErrors_nonneg _)
    (fun plus k => le_maxErrors_of_mem
      (List.mem_map.mpr ⟨(plus, k), by simp [ks], rfl⟩))
    (fun plus k => le_maxErrors_of_mem
      (List.mem_map.mpr ⟨(plus, k), by simp [ks], rfl⟩))).2
  rw [abs_of_nonneg (mul_nonneg (maxErrors_nonneg _) (maxErrors_nonneg _))]
  exact hb.trans (mul_le_mul_of_nonneg_right (by linarith)
    (mul_nonneg (maxErrors_nonneg _) (maxErrors_nonneg _)))

-- The coefficient is the full propensity times outcome-mean product.
-- @node: fitted_continuous_full_coefficient_l2Error_bound
/-- If [the reference nuisance record is admissible](hyp:he0) and [the fitted record is admissible](hyp:he), then
[the L² error of the selected treatment-probability times full-interval mean coefficient is at most the largest absolute outcome endpoint times the treatment-probability L² error, plus the full-interval mean L² error](goal). -/
lemma fitted_continuous_full_coefficient_l2Error_bound (L : LevelData Z X)
    (e0 e : NuisanceCont L) (he0 : ContAdmissible M L e0)
    (he : ContAdmissible M L e) (b : Bool) (k : ℕ) :
    let P := fun (e' : NuisanceCont L) => positiveValue e'.pLev (if b then k+1 else k)
    let J := fun (e' : NuisanceCont L) x =>
      if b then fullValue e'.JfullPlus k x else minusFullValue e' k x
    finiteL2Error M (fun x => P e x * J e x) (fun x => P e0 x * J e0 x) ≤
      max |M.yMin| |M.yMax| * finiteL2Error M (P e) (P e0) + finiteL2Error M (J e) (J e0) := by
  dsimp only
  let P := fun (e' : NuisanceCont L) (b : Bool) =>
    positiveValue e'.pLev (if b then k+1 else k)
  let J := fun (e' : NuisanceCont L) (b : Bool) x =>
    if b then fullValue e'.JfullPlus k x else minusFullValue e' k x
  have hp0 := (fitted_continuous_full_coordinate_memLp M L e0 he0 (if b then k+1 else k)).1
  have hp := (fitted_continuous_full_coordinate_memLp M L e he (if b then k+1 else k)).1
  have hj0 : MemLp (J e0 b) 2 (xLaw M) := by
    cases b
    · exact (fitted_continuous_full_coordinate_memLp M L e0 he0 k).2.2
    · exact (fitted_continuous_full_coordinate_memLp M L e0 he0 k).2.1
  have hj : MemLp (J e b) 2 (xLaw M) := by
    cases b
    · exact (fitted_continuous_full_coordinate_memLp M L e he k).2.2
    · exact (fitted_continuous_full_coordinate_memLp M L e he k).2.1
  apply dml_l2Error_bounded_product_le M _ _ _ _ hp0 hp hj0 hj _
    ((abs_nonneg _).trans (le_max_left _ _))
    (fitted_continuous_full_coordinates M L e he (if b then k+1 else k)).1.2
  cases b
  · exact (fitted_continuous_full_coordinates M L e0 he0 k).2.2.2
  · exact (fitted_continuous_full_coordinates M L e0 he0 k).2.1.2

-- @node: nuisanceRates_continuous_full_coefficient_quarter_rate
/-- If [the reference record is admissible](hyp:he0), [all fitted records are admissible](hyp:heh), and
[treatment probabilities](hyp:hrp), [plus full-interval means](hyp:hrplus), and [minus full-interval means](hyp:hrminus) satisfy the finite nuisance rates, then
[the L² error of the selected treatment-probability times full-interval mean coefficient, evaluated at sample size twice a positive integer, is of smaller order in probability than that sample size to the power minus one quarter](goal). -/
lemma nuisanceRates_continuous_full_coefficient_quarter_rate
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (L : LevelData Z X) (e0 : NuisanceCont L) (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L e0) (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrplus : FiniteNuisanceRates M μ (fun n a => (eh n a).JfullPlus) e0.JfullPlus)
    (hrminus : FiniteNuisanceRates M μ (fun n a => (eh n a).JfullMinus) e0.JfullMinus)
    (b : Bool) (k : ℕ) :
    let C := fun (e : NuisanceCont L) x =>
      positiveValue e.pLev (if b then k+1 else k) x *
        (if b then fullValue e.JfullPlus k x else minusFullValue e k x)
    Causalean.Stat.IsLittleOp
      (fun n a => finiteL2Error M (C (eh (2*(n+1)) a)) (C e0))
      (fun n => ((2*(n+1) : ℕ) : ℝ)^(-1/4 : ℝ)) μ := by
  dsimp only
  obtain ⟨hp, hjp, hjm⟩ := nuisanceRates_continuous_full_values M μ L e0 eh hrp hrplus hrminus
  have hj : Causalean.Stat.IsLittleOp
      (fun n a => finiteL2Error M
        (fun x => if b then fullValue (eh (2*(n+1)) a).JfullPlus k x
          else minusFullValue (eh (2*(n+1)) a) k x)
        (fun x => if b then fullValue e0.JfullPlus k x else minusFullValue e0 k x))
      (fun n => ((2*(n+1) : ℕ) : ℝ)^(-1/4 : ℝ)) μ := by
    cases b
    · simpa only [Bool.false_eq_true, if_false] using hjm k
    · simpa only [Bool.true_eq, if_true] using hjp k
  have hn : ∀ᶠ n : ℕ in atTop, 0 ≤ ((2*(n+1) : ℕ) : ℝ)^(-1/4 : ℝ) :=
    Eventually.of_forall (fun n => Real.rpow_nonneg (by positivity) _)
  have hs := (hp (if b then k+1 else k)).add_eventually_nonneg_rate hn hj
  let B := max |M.yMin| |M.yMax|
  have hB : 0 ≤ B := (abs_nonneg _).trans (le_max_left _ _)
  apply Causalean.Stat.IsLittleOp.of_abs_le_const_mul (by positivity : 0 < B + 1) hs
  intro n a
  dsimp only [finiteL2Error]
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  have hb := fitted_continuous_full_coefficient_l2Error_bound M L e0
    (eh (2*(n+1)) a) he0 (heh _ a) b k
  apply hb.trans
  rw [abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  have hP := Real.sqrt_nonneg (∫ x,
    (positiveValue (eh (2*(n+1)) a).pLev (if b then k+1 else k) x -
      positiveValue e0.pLev (if b then k+1 else k) x)^2 ∂xLaw M)
  have hJ := Real.sqrt_nonneg (∫ x,
    ((if b then fullValue (eh (2*(n+1)) a).JfullPlus k x
      else minusFullValue (eh (2*(n+1)) a) k x) -
      (if b then fullValue e0.JfullPlus k x else minusFullValue e0 k x))^2 ∂xLaw M)
  dsimp only [finiteL2Error, B] at *
  nlinarith [mul_nonneg hB hJ]

-- Both fitted regressions enter this remainder through their product.
-- @node: fitted_continuous_full_joint_denominator_bias_bound
/-- If [the reference nuisance record is admissible](hyp:he0), [the fitted record is admissible](hyp:he),
[the clipping constant is positive](hyp:hc), and [fitted positive-level assignment probabilities are almost surely bounded below by that constant](hyp:hclip), then
[the selected full-interval remainder formed from the fitted product weight, the relative assignment-probability error, and the error in the treatment-probability times mean coefficient is integrable, with absolute mean at most the product of the assignment and coefficient L² errors divided by the clipping constant](goal). -/
lemma fitted_continuous_full_joint_denominator_bias_bound (L : LevelData Z X)
    (e0 e : NuisanceCont L) (he0 : ContAdmissible M L e0)
    (he : ContAdmissible M L e) (c : ℝ) (hc : 0 < c)
    (hclip : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (plus : Bool) (k : Fin L.K) :
    let i := if plus then k.val+1 else k.val
    let C := fun (e' : NuisanceCont L) x =>
      positiveValue e'.pLev i x *
        (if plus then fullValue e'.JfullPlus k x else minusFullValue e' k x)
    Integrable (fun x => e.gammaFull k x *
      (1 - positiveValue e0.piLev i x / positiveValue e.piLev i x) *
        (C e x - C e0 x)) (xLaw M) ∧
    |∫ x, e.gammaFull k x *
      (1 - positiveValue e0.piLev i x / positiveValue e.piLev i x) *
        (C e x - C e0 x) ∂xLaw M| ≤
      finiteL2Error M (positiveValue e.piLev i) (positiveValue e0.piLev i) *
        finiteL2Error M (C e) (C e0) / c := by
  dsimp only
  let i : ℕ := if plus then k.val+1 else k.val
  let C := fun (e' : NuisanceCont L) x =>
    positiveValue e'.pLev i x *
      (if plus then fullValue e'.JfullPlus k x else minusFullValue e' k x)
  by_cases hi0 : i = 0
  · have hplus : plus = false := by cases plus <;> simp_all [i]
    have hk0 : k.val = 0 := by simpa [i, hplus] using hi0
    simp [hplus, hk0, positiveValue, finiteL2Error]
  have hi : 1 ≤ i ∧ i ≤ L.K := by
    dsimp only [i] at *
    cases plus <;> simp_all <;> omega
  have hpi := (fitted_continuous_treatment_assignment_memLp M L e he i).2.sub
    (fitted_continuous_treatment_assignment_memLp M L e0 he0 i).2
  have hC : MemLp (fun x => C e x - C e0 x) 2 (xLaw M) :=
    (fitted_continuous_full_product_memLp M L e he plus k).sub
      (fitted_continuous_full_product_memLp M L e0 he0 plus k)
  rw [l2Error_eq_eLpNorm M _ _ hpi, l2Error_eq_eLpNorm M _ _ hC]
  simpa only [one_mul] using
    (weighted_clipped_assignment_regression_L2_bound (xLaw M)
      (e.gammaFull k) (positiveValue e0.piLev i) (positiveValue e.piLev i)
      (fun x => C e x - C e0 x) c 1 hc zero_le_one
      (by first | fun_prop | exact (fitted_continuous_gammaFull_coordinates M L e he k).1)
      (fitted_continuous_assignment_coordinates M L e0 he0 i).1
      (fitted_continuous_assignment_coordinates M L e he i).1
      (by simpa only [positiveValue, dif_pos hi] using hclip ⟨i, hi⟩)
      (by simpa only [Real.norm_eq_abs] using
        (fitted_continuous_gammaFull_coordinates M L e he k).2)
      hpi hC)

-- @node: nuisanceRates_continuous_full_joint_denominator_bias_root_n_negligible
/-- If [the reference record is admissible](hyp:he0), [all fitted records are admissible](hyp:heh),
[the clipping constant is positive](hyp:hc), [all fitted positive-level assignment probabilities are almost surely at least that constant](hyp:hclip), and
[assignment probabilities](hyp:hrpi), [treatment probabilities](hyp:hrp), [plus full-interval means](hyp:hrplus), and [minus full-interval means](hyp:hrminus) satisfy the finite nuisance rates, then
[the selected full-interval population remainder involving relative assignment error and treatment-probability times mean-coefficient error, evaluated at sample size twice a positive integer and scaled by the square root of that integer, converges in probability to zero](goal). -/
lemma nuisanceRates_continuous_full_joint_denominator_bias_root_n_negligible
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (L : LevelData Z X) (e0 : NuisanceCont L) (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L e0) (heh : ∀ n a, ContAdmissible M L (eh n a))
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a (i : PositiveIndex L.K), ∀ᵐ x ∂xLaw M, c ≤ (eh n a).piLev i x)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) e0.piLev)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrplus : FiniteNuisanceRates M μ (fun n a => (eh n a).JfullPlus) e0.JfullPlus)
    (hrminus : FiniteNuisanceRates M μ (fun n a => (eh n a).JfullMinus) e0.JfullMinus)
    (plus : Bool) (k : Fin L.K) :
    let i := if plus then k.val+1 else k.val
    let C := fun (e' : NuisanceCont L) x =>
      positiveValue e'.pLev i x *
        (if plus then fullValue e'.JfullPlus k x else minusFullValue e' k x)
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
        (∫ x, (eh (2*(n+1)) a).gammaFull k x *
          (1 - positiveValue e0.piLev i x / positiveValue (eh (2*(n+1)) a).piLev i x) *
            (C (eh (2*(n+1)) a) x - C e0 x) ∂xLaw M))
      atTop (fun _ _ => 0) := by
  dsimp only
  have hpi := nuisanceRates_positiveValue M μ L.K _ _ hrpi
    (if plus then k.val+1 else k.val)
  have hC := nuisanceRates_continuous_full_coefficient_quarter_rate M μ L e0 eh
    he0 heh hrp hrplus hrminus plus k
  have hp := dml_quarter_rate_product μ _ _ hpi hC
  apply dml_root_n_bias_tendsto_probability μ
  apply Causalean.Stat.IsLittleOp.of_abs_le_const_mul (by positivity : 0 < 1 / c) hp
  intro n a
  have hb := (fitted_continuous_full_joint_denominator_bias_bound M L e0
    (eh (2*(n+1)) a) he0 (heh _ a) c hc (hclip _ a) plus k).2
  apply hb.trans
  rw [div_eq_mul_inv, one_div, mul_comm]
  exact mul_le_mul_of_nonneg_left (le_abs_self _) (inv_nonneg.mpr hc.le)

-- Aggregate the joint regression products, including the propensity/outcome
-- cross term, before assembling the full-score conditional bias.
-- @node: fitted_continuous_full_joint_denominator_block_bias_bound
/-- Suppose [the reference record is admissible](hyp:he0), [the fitted record is admissible](hyp:he),
[the clipping constant is positive](hyp:hc), and [fitted positive-level assignment probabilities are almost surely at least that constant](hyp:hclip).
If [the assignment-error bound is nonnegative](hyp:hwt), [all signed treatment-probability times full-interval mean coefficients have L² error at most the coefficient-error bound](hyp:hC), and
[all corresponding assignment probabilities have L² error at most the assignment-error bound](hyp:hpi), then
[the sum of the plus-minus joint coefficient-and-denominator remainders is integrable, and its absolute population mean is at most twice the level count divided by the clipping constant times the two error bounds](goal). -/
lemma fitted_continuous_full_joint_denominator_block_bias_bound (L : LevelData Z X)
    (e0 e : NuisanceCont L) (he0 : ContAdmissible M L e0)
    (he : ContAdmissible M L e) (c : ℝ) (hc : 0 < c)
    (hclip : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (reg wt : ℝ) (hwt : 0 ≤ wt)
    (hC : ∀ (plus : Bool) (k : Fin L.K), finiteL2Error M
      (fun x => positiveValue e.pLev (if plus then k.val+1 else k.val) x *
        (if plus then fullValue e.JfullPlus k x else minusFullValue e k x))
      (fun x => positiveValue e0.pLev (if plus then k.val+1 else k.val) x *
        (if plus then fullValue e0.JfullPlus k x else minusFullValue e0 k x)) ≤ reg)
    (hpi : ∀ (plus : Bool) (k : Fin L.K), finiteL2Error M
      (positiveValue e.piLev (if plus then k.val+1 else k.val))
      (positiveValue e0.piLev (if plus then k.val+1 else k.val)) ≤ wt) :
    let C := fun (e' : NuisanceCont L) (plus : Bool) (k : Fin L.K) x =>
      positiveValue e'.pLev (if plus then k.val+1 else k.val) x *
        (if plus then fullValue e'.JfullPlus k x else minusFullValue e' k x)
    let B := fun (plus : Bool) (k : Fin L.K) x => e.gammaFull k x *
      (1 - positiveValue e0.piLev (if plus then k.val+1 else k.val) x /
        positiveValue e.piLev (if plus then k.val+1 else k.val) x) *
      (C e plus k x - C e0 plus k x)
    Integrable (fun x => ∑ k : Fin L.K, (B true k x - B false k x)) (xLaw M) ∧
      |∫ x, ∑ k : Fin L.K, (B true k x - B false k x) ∂xLaw M| ≤
        (2 * (L.K : ℝ) / c) * (reg * wt) := by
  dsimp only
  let C := fun (e' : NuisanceCont L) (plus : Bool) (k : Fin L.K) x =>
    positiveValue e'.pLev (if plus then k.val+1 else k.val) x *
      (if plus then fullValue e'.JfullPlus k x else minusFullValue e' k x)
  let B := fun (plus : Bool) (k : Fin L.K) x => e.gammaFull k x *
    (1 - positiveValue e0.piLev (if plus then k.val+1 else k.val) x /
      positiveValue e.piLev (if plus then k.val+1 else k.val) x) *
    (C e plus k x - C e0 plus k x)
  have hb (plus : Bool) (k : Fin L.K) :=
    fitted_continuous_full_joint_denominator_bias_bound M L e0 e he0 he c hc hclip plus k
  have hi (k : Fin L.K) : Integrable (fun x => B true k x - B false k x) (xLaw M) :=
    (hb true k).1.sub (hb false k).1
  have hbound (plus : Bool) (k : Fin L.K) :
      |∫ x, B plus k x ∂xLaw M| ≤ wt * reg / c := by
    apply (hb plus k).2.trans
    exact div_le_div_of_nonneg_right
      (mul_le_mul (hpi plus k) (hC plus k) (Real.sqrt_nonneg _) hwt) hc.le
  refine ⟨integrable_finsetSum _ (fun k _ => hi k), ?_⟩
  rw [integral_finsetSum _ (fun k _ => hi k)]
  calc
    _ ≤ ∑ k : Fin L.K, |∫ x, B true k x - B false k x ∂xLaw M| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin L.K, (wt * reg / c + wt * reg / c) := by
      apply Finset.sum_le_sum
      intro k _
      rw [integral_sub (hb true k).1 (hb false k).1]
      exact (abs_sub _ _).trans (add_le_add (hbound true k) (hbound false k))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

-- @node: nuisanceRates_continuous_full_joint_denominator_block_bias_root_n_negligible
/-- If [the reference record is admissible](hyp:he0), [all fitted records are admissible](hyp:heh),
[the clipping constant is positive](hyp:hc), [all fitted positive-level assignment probabilities are almost surely at least that constant](hyp:hclip), and
[assignment probabilities](hyp:hrpi), [treatment probabilities](hyp:hrp), [plus full-interval means](hyp:hrplus), and [minus full-interval means](hyp:hrminus) satisfy the finite nuisance rates, then
[the population mean of the sum of plus-minus joint coefficient-and-denominator remainders, evaluated at sample size twice a positive integer and scaled by the square root of that integer, converges in probability to zero](goal). -/
lemma nuisanceRates_continuous_full_joint_denominator_block_bias_root_n_negligible
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (L : LevelData Z X) (e0 : NuisanceCont L) (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L e0) (heh : ∀ n a, ContAdmissible M L (eh n a))
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a (i : PositiveIndex L.K), ∀ᵐ x ∂xLaw M, c ≤ (eh n a).piLev i x)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) e0.piLev)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrplus : FiniteNuisanceRates M μ (fun n a => (eh n a).JfullPlus) e0.JfullPlus)
    (hrminus : FiniteNuisanceRates M μ (fun n a => (eh n a).JfullMinus) e0.JfullMinus) :
    let C := fun (e : NuisanceCont L) (plus : Bool) (k : Fin L.K) x =>
      positiveValue e.pLev (if plus then k.val+1 else k.val) x *
        (if plus then fullValue e.JfullPlus k x else minusFullValue e k x)
    let B := fun n a (plus : Bool) (k : Fin L.K) x =>
      (eh (2*(n+1)) a).gammaFull k x *
        (1 - positiveValue e0.piLev (if plus then k.val+1 else k.val) x /
          positiveValue (eh (2*(n+1)) a).piLev (if plus then k.val+1 else k.val) x) *
        (C (eh (2*(n+1)) a) plus k x - C e0 plus k x)
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
        (∫ x, ∑ k : Fin L.K, (B n a true k x - B n a false k x) ∂xLaw M))
      atTop (fun _ _ => 0) := by
  dsimp only
  let ks := (Finset.univ : Finset (Bool × Fin L.K)).toList
  let C := fun (e : NuisanceCont L) (i : Bool × Fin L.K) x =>
    positiveValue e.pLev (if i.1 then i.2.val+1 else i.2.val) x *
      (if i.1 then fullValue e.JfullPlus i.2 x else minusFullValue e i.2 x)
  let pi := fun (e : NuisanceCont L) (i : Bool × Fin L.K) =>
    positiveValue e.piLev (if i.1 then i.2.val+1 else i.2.val)
  let reg := fun n a => maxErrors (ks.map (fun i =>
    finiteL2Error M (C (eh (2*(n+1)) a) i) (C e0 i)))
  let wt := fun n a => maxErrors (ks.map (fun i =>
    finiteL2Error M (pi (eh (2*(n+1)) a) i) (pi e0 i)))
  have hr := nuisanceRates_finite_maxErrors M μ
    (fun n a => C (eh n a)) (C e0) ks (fun i =>
      nuisanceRates_continuous_full_coefficient_quarter_rate M μ L e0 eh
        he0 heh hrp hrplus hrminus i.1 i.2)
  have hw := nuisanceRates_finite_maxErrors M μ
    (fun n a => pi (eh n a)) (pi e0) ks (fun i =>
      nuisanceRates_positiveValue M μ L.K _ _ hrpi (if i.1 then i.2.val+1 else i.2.val))
  have hp := dml_quarter_rate_product μ reg wt hr hw
  apply dml_root_n_bias_tendsto_probability μ
  apply Causalean.Stat.IsLittleOp.of_abs_le_const_mul
    (by positivity : 0 < 2 * (L.K : ℝ) / c + 1) hp
  intro n a
  have hb := (fitted_continuous_full_joint_denominator_block_bias_bound M L e0
    (eh (2*(n+1)) a) he0 (heh _ a) c hc (hclip _ a)
    (reg n a) (wt n a) (maxErrors_nonneg _)
    (fun plus k => le_maxErrors_of_mem
      (List.mem_map.mpr ⟨(plus, k), by simp [ks], rfl⟩))
    (fun plus k => le_maxErrors_of_mem
      (List.mem_map.mpr ⟨(plus, k), by simp [ks], rfl⟩))).2
  rw [abs_of_nonneg (mul_nonneg (maxErrors_nonneg _) (maxErrors_nonneg _))]
  exact hb.trans (mul_le_mul_of_nonneg_right (by linarith)
    (mul_nonneg (maxErrors_nonneg _) (maxErrors_nonneg _)))

end Papers.TbsPrteOptimalTransport

module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLWeightedBoundaryResidual
/-! Cancellation of the fitted fractional binary regression correction.
Almost-everywhere measurable fitted branch weights preserve the baseline
product-of-errors bound, including the structural zero at level zero. -/
public section
set_option linter.style.haveILetI false
set_option linter.style.openClassical false
set_option linter.unreachableTactic false
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

-- @node: fitted_positive_treatment_centering_ae_weighted_L2_bound
/-- Suppose [the reference nuisances are admissible](hyp:he0), [the fitted nuisances are admissible](hyp:he), [the assignment clipping constant is positive](hyp:hc), [the weight bound is nonnegative](hyp:hW), [all fitted positive-level assignment probabilities are at least the clipping constant almost everywhere](hyp:hclip), [the covariate weight is almost everywhere strongly measurable](hyp:hw), and [its absolute value is almost everywhere at most the weight bound](hyp:hwb). [The weighted sum of the reference-assignment-to-fitted-assignment ratio times the reference-minus-fitted treatment regression and the fitted-minus-reference treatment regression is integrable, and its absolute mean is at most the weight bound divided by the clipping constant times the product of the assignment and treatment-regression L2 errors](goal). -/
lemma fitted_positive_treatment_centering_ae_weighted_L2_bound
    (L : LevelData Z X) (e0 e : NuisanceBin L)
    (he0 : BinAdmissible M L e0) (he : BinAdmissible M L e)
    (i : ℕ) (c W : ℝ) (hc : 0 < c) (hW : 0 ≤ W)
    (hclip : ∀ a, ∀ᵐ x ∂xLaw M, c ≤ e.piLev a x)
    (w : X → ℝ) (hw : AEStronglyMeasurable w (xLaw M))
    (hwb : ∀ᵐ x ∂xLaw M, ‖w x‖ ≤ W) :
    let R := fun x => positiveValue e0.piLev i x *
      (positiveValue e0.pLev i x - positiveValue e.pLev i x) /
        positiveValue e.piLev i x +
      (positiveValue e.pLev i x - positiveValue e0.pLev i x)
    Integrable (fun x => w x * R x) (xLaw M) ∧
      |∫ x, w x * R x ∂xLaw M| ≤
        (W / c) * (finiteL2Error M (positiveValue e.piLev i) (positiveValue e0.piLev i) *
          finiteL2Error M (positiveValue e.pLev i) (positiveValue e0.pLev i)) := by
  let w' := hw.mk w
  have hw' : Measurable w' := by first | fun_prop | exact hw.stronglyMeasurable_mk.measurable
  have heq : w =ᵐ[xLaw M] w' := hw.ae_eq_mk
  have hb' : ∀ᵐ x ∂xLaw M, ‖w' x‖ ≤ W := by
    filter_upwards [hwb, heq] with x hx he
    simpa only [← he] using hx
  obtain ⟨hi, hb⟩ := fitted_positive_treatment_centering_weighted_L2_bound
    M L e0 e he0 he i c W hc hW hclip w' hw' hb'
  dsimp only at hi hb ⊢
  have heR : (fun x => w x *
      (positiveValue e0.piLev i x *
        (positiveValue e0.pLev i x - positiveValue e.pLev i x) /
          positiveValue e.piLev i x +
        (positiveValue e.pLev i x - positiveValue e0.pLev i x))) =ᵐ[xLaw M]
      (fun x => w' x *
      (positiveValue e0.piLev i x *
        (positiveValue e0.pLev i x - positiveValue e.pLev i x) /
          positiveValue e.piLev i x +
        (positiveValue e.pLev i x - positiveValue e0.pLev i x))) := by
    filter_upwards [heq] with x hx
    rw [hx]
  exact ⟨hi.congr heR.symm, by rw [integral_congr_ae heR]; exact hb⟩

-- @node: nuisanceRates_positive_treatment_centering_ae_weighted_root_n_negligible
/-- Suppose [the reference nuisances are admissible](hyp:he0), [every fitted nuisance vector is admissible](hyp:heh), [the clipping constant is positive](hyp:hc), [the weight bound is nonnegative](hyp:hW), and [fitted positive-level assignment probabilities are uniformly bounded below by the clipping constant almost everywhere](hyp:hclip). If [each fitted covariate weight is almost everywhere strongly measurable](hyp:hw), [these weights are uniformly bounded in absolute value almost everywhere](hyp:hwb), [the treatment regressions satisfy the finite nuisance rate conditions](hyp:hrp), and [the assignment probabilities satisfy those rate conditions](hyp:hrpi), [the weighted treatment-centering mean at even sample sizes, multiplied by the square root of the half-sample size, converges to zero in probability](goal). -/
lemma nuisanceRates_positive_treatment_centering_ae_weighted_root_n_negligible
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (L : LevelData Z X) (e0 : NuisanceBin L) (eh : ℕ → A → NuisanceBin L)
    (he0 : BinAdmissible M L e0) (heh : ∀ n a, BinAdmissible M L (eh n a))
    (i : ℕ) (c W : ℝ) (hc : 0 < c) (hW : 0 ≤ W)
    (hclip : ∀ n a b, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).piLev b x)
    (w : ℕ → A → X → ℝ) (hw : ∀ n a, AEStronglyMeasurable (w n a) (xLaw M))
    (hwb : ∀ n a, ∀ᵐ x ∂xLaw M, ‖w n a x‖ ≤ W)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) e0.piLev) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
        ∫ x, w (2*(n+1)) a x *
          (positiveValue e0.piLev i x *
            (positiveValue e0.pLev i x - positiveValue (eh (2*(n+1)) a).pLev i x) /
              positiveValue (eh (2*(n+1)) a).piLev i x +
            (positiveValue (eh (2*(n+1)) a).pLev i x - positiveValue e0.pLev i x))
          ∂xLaw M) atTop (fun _ _ => 0) := by
  let reg := fun n a => finiteL2Error M (positiveValue (eh (2*(n+1)) a).pLev i)
    (positiveValue e0.pLev i)
  let wt := fun n a => finiteL2Error M (positiveValue (eh (2*(n+1)) a).piLev i)
    (positiveValue e0.piLev i)
  have hr := nuisanceRates_positiveValue M μ L.K _ _ hrp i
  have ht := nuisanceRates_positiveValue M μ L.K _ _ hrpi i
  apply dml_quadratic_bias_root_n_negligible μ _ reg wt (W / c + 1)
    (by positivity) hr ht
  intro n a
  have hb := (fitted_positive_treatment_centering_ae_weighted_L2_bound
    M L e0 (eh (2*(n+1)) a) he0 (heh _ a) i c W hc hW
    (hclip _ a) (w (2*(n+1)) a) (hw _ a) (hwb _ a)).2
  dsimp only at hb
  apply hb.trans
  have hn : 0 ≤ reg n a * wt n a := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc
    _ = (W / c) * (reg n a * wt n a) := by dsimp only [reg, wt]; ring
    _ ≤ (W / c + 1) * (reg n a * wt n a) :=
      mul_le_mul_of_nonneg_right (by linarith) hn
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (sq_nonneg _))
      (by positivity)

-- Both fitted indicators are kept, so no branch-recovery premise is needed.
-- @node: fitted_fractional_lower_weight_memLp_bound
/-- If [the policy is a measurable probability-valued map](hyp:hphi) and [the fitted binary nuisances are admissible](hyp:he), [the product of the fitted regular weight, dominance indicator, and active indicator has a finite covariate second moment and absolute value at most one almost everywhere](goal). -/
lemma fitted_fractional_lower_weight_memLp_bound
    (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (L : LevelData Z X) (e : NuisanceBin L) (he : BinAdmissible M L e) (k j : ℕ) :
    MemLp (fun x => regularValue e.gamma k j x * Edom phi L e k j x *
      Iact phi L e k j x) 2 (xLaw M) ∧
    (∀ᵐ x ∂xLaw M, ‖regularValue e.gamma k j x * Edom phi L e k j x *
      Iact phi L e k j x‖ ≤ 1) := by
  have hg := fitted_regular_gamma_memLp M L e he k j
  obtain ⟨hi, hd, hedom⟩ := fitted_fractional_branches_memLp M phi hphi L e he k j
  have hm : AEStronglyMeasurable (fun x => regularValue e.gamma k j x *
      Edom phi L e k j x * Iact phi L e k j x) (xLaw M) := by
    first | fun_prop | exact (hg.1.mul hedom.1).mul hi.1
  have hb : ∀ x, ‖Edom phi L e k j x‖ ≤ 1 ∧ ‖Iact phi L e k j x‖ ≤ 1 := by
    intro x
    unfold Edom Iact indicator
    split_ifs <;> norm_num
  have hgb : ∀ᵐ x ∂xLaw M, ‖regularValue e.gamma k j x‖ ≤ 1 := by
    unfold regularValue
    split_ifs with hidx
    · filter_upwards [he.2.2.2.2.1 ⟨(k,j), hidx⟩] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg hx.2.1]
      exact hx.2.2
    · simp
  have hwb : ∀ᵐ x ∂xLaw M, ‖regularValue e.gamma k j x * Edom phi L e k j x *
      Iact phi L e k j x‖ ≤ 1 := by
    filter_upwards [hgb] with x hx
    rw [norm_mul, norm_mul]
    exact (mul_le_mul
      ((mul_le_mul hx (hb x).1 (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
      (hb x).2 (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  exact ⟨MemLp.of_bound hm 1 hwb, hwb⟩

-- @node: nuisanceRates_fractional_baseline_correction_root_n_negligible
/-- Suppose [the policy is a measurable probability-valued map](hyp:hphi), [the reference nuisances are admissible](hyp:he0), [all fitted nuisance vectors are admissible](hyp:heh), [the clipping constant is positive](hyp:hc), and [fitted positive-level assignment probabilities are uniformly bounded below by it almost everywhere](hyp:hclip). If [treatment regressions satisfy the finite nuisance rate conditions](hyp:hrp) and [assignment probabilities satisfy those rate conditions](hyp:hrpi), [the fractional baseline correction mean at even sample sizes, multiplied by the square root of the half-sample size, converges to zero in probability; the correction uses the fitted regular, dominance, and active weights on the first branch and is zero on other branches](goal). -/
lemma nuisanceRates_fractional_baseline_correction_root_n_negligible
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (L : LevelData Z X) (e0 : NuisanceBin L) (eh : ℕ → A → NuisanceBin L)
    (he0 : BinAdmissible M L e0) (heh : ∀ n a, BinAdmissible M L (eh n a))
    (c : ℝ) (hc : 0 < c) (k j : ℕ)
    (hclip : ∀ n a i, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).piLev i x)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) e0.piLev) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) * ∫ x,
        (if j = 1 then regularValue (eh (2*(n+1)) a).gamma k j x *
          Edom phi L (eh (2*(n+1)) a) k j x * Iact phi L (eh (2*(n+1)) a) k j x *
          (positiveValue e0.piLev k x *
            (positiveValue e0.pLev k x - positiveValue (eh (2*(n+1)) a).pLev k x) /
              positiveValue (eh (2*(n+1)) a).piLev k x +
            (positiveValue (eh (2*(n+1)) a).pLev k x - positiveValue e0.pLev k x))
        else 0) ∂xLaw M) atTop (fun _ _ => 0) := by
  by_cases hj : j = 1
  · simp only [if_pos hj]
    apply nuisanceRates_positive_treatment_centering_ae_weighted_root_n_negligible
      M μ L e0 eh he0 heh k c 1 hc zero_le_one hclip
      (fun n a x => regularValue (eh n a).gamma k j x * Edom phi L (eh n a) k j x *
        Iact phi L (eh n a) k j x)
    · intro n a
      first | fun_prop | exact (fitted_fractional_lower_weight_memLp_bound M phi hphi L
        (eh n a) (heh n a) k j).1.1
    · exact fun n a => (fitted_fractional_lower_weight_memLp_bound M phi hphi L
        (eh n a) (heh n a) k j).2
    · exact hrp
    · exact hrpi
  · simp only [if_neg hj, integral_zero, mul_zero]
    rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm]
    intro eps heps
    simpa only [sub_self, norm_zero, not_le.mpr heps, Set.ofPred_false,
      measure_empty] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (𝓝 0))

-- The regression residual cancels the two affine regression arguments of the hinge.
-- @node: fitted_fractional_regression_centering_identity
/-- [Subtracting the fitted boundary-indicator-weighted change in the upper treatment-minus-success-increment regression and the first-branch dominance-and-activity-weighted change in the lower treatment regression from the binary regular regression mean gives the boundary-indicator-weighted centered boundary residual minus the first-branch dominance-and-activity-weighted treatment-centering residual](goal). -/
lemma fitted_fractional_regression_centering_identity
    (phi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (e0 e : NuisanceBin L) (k j : ℕ) (x : X) :
    binaryRegularRegressionMean phi L e0 e k j x -
      Dbd phi L e k j x *
        ((positiveValue e.pLev (k+1) x - binFullJ L e k x) -
          (positiveValue e0.pLev (k+1) x - binFullJ L e0 k x)) -
      (if j = 1 then Edom phi L e k j x * Iact phi L e k j x *
        (positiveValue e.pLev k x - positiveValue e0.pLev k x) else 0) =
    Dbd phi L e k j x * binaryBoundaryCenteredResidual L e0 e k x -
      (if j = 1 then Edom phi L e k j x * Iact phi L e k j x *
        (positiveValue e0.piLev k x *
          (positiveValue e0.pLev k x - positiveValue e.pLev k x) /
            positiveValue e.piLev k x +
          (positiveValue e.pLev k x - positiveValue e0.pLev k x)) else 0) := by
  dsimp only [binaryRegularRegressionMean, binaryBoundaryCenteredResidual]
  by_cases hj : j = 1
  · simp only [if_pos hj]; ring
  · simp only [if_neg hj]; ring

-- Original rates imply cancellation of the entire fitted regression-mean block.
-- @node: nuisanceRates_fractional_regression_centering_root_n_negligible
/-- Suppose [the policy is a measurable probability-valued map](hyp:hphi), [the reference nuisances are admissible](hyp:he0), [all fitted nuisance vectors are admissible](hyp:heh), [the clipping constant is positive](hyp:hc), and [fitted positive-level assignment probabilities are uniformly bounded below by it almost everywhere](hyp:hclip). If [success regressions satisfy the finite nuisance rate conditions](hyp:hrP), [treatment regressions satisfy those rate conditions](hyp:hrp), and [assignment probabilities satisfy those rate conditions](hyp:hrpi), [the population mean of the fitted regular weight times the binary regular regression mean after subtracting its boundary and first-branch affine regression changes, evaluated at even sample sizes and multiplied by the square root of the half-sample size, converges to zero in probability](goal). -/
lemma nuisanceRates_fractional_regression_centering_root_n_negligible
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (L : LevelData Z X) (e0 : NuisanceBin L) (eh : ℕ → A → NuisanceBin L)
    (he0 : BinAdmissible M L e0) (heh : ∀ n a, BinAdmissible M L (eh n a))
    (c : ℝ) (hc : 0 < c) (k j : ℕ)
    (hclip : ∀ n a i, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).piLev i x)
    (hrP : FiniteNuisanceRates M μ (fun n a => (eh n a).P1) e0.P1)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) e0.piLev) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) * ∫ x,
        regularValue (eh (2*(n+1)) a).gamma k j x *
          (binaryRegularRegressionMean phi L e0 (eh (2*(n+1)) a) k j x -
            Dbd phi L (eh (2*(n+1)) a) k j x *
              ((positiveValue (eh (2*(n+1)) a).pLev (k+1) x -
                  binFullJ L (eh (2*(n+1)) a) k x) -
                (positiveValue e0.pLev (k+1) x - binFullJ L e0 k x)) -
            (if j = 1 then Edom phi L (eh (2*(n+1)) a) k j x *
              Iact phi L (eh (2*(n+1)) a) k j x *
              (positiveValue (eh (2*(n+1)) a).pLev k x - positiveValue e0.pLev k x)
            else 0)) ∂xLaw M) atTop (fun _ _ => 0) := by
  let B := fun n a x => regularValue (eh n a).gamma k j x *
    Dbd phi L (eh n a) k j x * binaryBoundaryCenteredResidual L e0 (eh n a) k x
  let T := fun n a x => if j = 1 then regularValue (eh n a).gamma k j x *
    Edom phi L (eh n a) k j x * Iact phi L (eh n a) k j x *
    (positiveValue e0.piLev k x *
      (positiveValue e0.pLev k x - positiveValue (eh n a).pLev k x) /
        positiveValue (eh n a).piLev k x +
      (positiveValue (eh n a).pLev k x - positiveValue e0.pLev k x)) else 0
  have hB := nuisanceRates_fractional_boundary_correction_root_n_negligible
    M μ phi hphi L e0 eh he0 heh c hc k j hclip hrP hrp hrpi
  have hT := nuisanceRates_fractional_baseline_correction_root_n_negligible
    M μ phi hphi L e0 eh he0 heh c hc k j hclip hrp hrpi
  have hs := hB.sub hT
  simp only [sub_zero] at hs
  have iB (n : ℕ) (a : A) : Integrable (B n a) (xLaw M) := by
    have hgam := fitted_regular_gamma_memLp M L (eh n a) (heh n a) k j
    have hD := (fitted_fractional_branches_memLp M phi hphi L (eh n a) (heh n a) k j).2.1
    have hw : AEStronglyMeasurable (fun x => regularValue (eh n a).gamma k j x *
        Dbd phi L (eh n a) k j x) (xLaw M) := by
      first | fun_prop | exact hgam.1.mul hD.1
    have hb : ∀ᵐ x ∂xLaw M, ‖regularValue (eh n a).gamma k j x *
        Dbd phi L (eh n a) k j x‖ ≤ 1 := by
      unfold regularValue
      split_ifs with hi
      · filter_upwards [(heh n a).2.2.2.2.1 ⟨(k,j), hi⟩] with x hx
        have hg : ‖(eh n a).gamma ⟨(k,j), hi⟩ x‖ ≤ 1 := by
          rw [Real.norm_eq_abs, abs_of_nonneg hx.2.1]; exact hx.2.2
        have hd : ‖Dbd phi L (eh n a) k j x‖ ≤ 1 := by
          unfold Dbd indicator; split_ifs <;> norm_num
        rw [norm_mul]
        exact (mul_le_mul hg hd (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
      · simp
    exact (fitted_boundary_centered_residual_weighted_integral_bound M L e0 (eh n a)
      he0 (heh n a) c 1 hc zero_le_one k (hclip n a) _ hw hb).1
  have iT (n : ℕ) (a : A) : Integrable (T n a) (xLaw M) := by
    dsimp only [T]
    by_cases hj : j = 1
    · simp only [if_pos hj]
      have hw := fitted_fractional_lower_weight_memLp_bound M phi hphi L (eh n a) (heh n a) k j
      exact (fitted_positive_treatment_centering_ae_weighted_L2_bound M L e0 (eh n a)
        he0 (heh n a) k c 1 hc zero_le_one (hclip n a) _ hw.1.1 hw.2).1
    · simp only [if_neg hj]
      exact integrable_zero _ _ _
  convert hs using 1
  funext n a
  simp_rw [fitted_fractional_regression_centering_identity]
  have hid : (fun x => regularValue (eh (2*(n+1)) a).gamma k j x *
      (Dbd phi L (eh (2*(n+1)) a) k j x *
        binaryBoundaryCenteredResidual L e0 (eh (2*(n+1)) a) k x -
        (if j = 1 then Edom phi L (eh (2*(n+1)) a) k j x *
          Iact phi L (eh (2*(n+1)) a) k j x *
          (positiveValue e0.piLev k x *
            (positiveValue e0.pLev k x - positiveValue (eh (2*(n+1)) a).pLev k x) /
              positiveValue (eh (2*(n+1)) a).piLev k x +
            (positiveValue (eh (2*(n+1)) a).pLev k x - positiveValue e0.pLev k x)) else 0))) =
      (fun x => B (2*(n+1)) a x - T (2*(n+1)) a x) := by
    funext x
    dsimp only [B, T]
    by_cases hj : j = 1
    · simp only [if_pos hj]; ring
    · simp only [if_neg hj]; ring
  rw [hid, integral_sub (iB _ a) (iT _ a), mul_sub]

end Papers.TbsPrteOptimalTransport

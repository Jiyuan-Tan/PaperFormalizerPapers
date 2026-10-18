module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLBaselineResidualRates
public import Papers.TbsPrteOptimalTransport.Helpers.DMLFractionalHingeBias
public import Papers.TbsPrteOptimalTransport.Helpers.DMLFractionalResidualConvergence
/-! Fitted branch weights preserve the quadratic boundary regression cancellation.
The rate is derived from the original success, treatment and assignment nuisances,
including the structural zero, without a rate assumption on the residual itself. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.unreachableTactic false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: binaryBoundaryCenteredResidual
/-- For [a level structure](hyp:L), [reference binary nuisances](hyp:e0), [fitted binary nuisances](hyp:e), [a boundary level](hyp:k), and [a covariate value](hyp:x), the [centered binary boundary residual](goal) is the reference-to-fitted assignment ratio times the reference-minus-fitted success regression at the next level, minus the corresponding quantity at the current level, minus the next-level ratio times the reference-minus-fitted treatment regression, minus the fitted-minus-reference change in the next-level treatment regression less the success-regression increment. -/
noncomputable def binaryBoundaryCenteredResidual (L : LevelData Z X)
    (e0 e : NuisanceBin L) (k : ℕ) (x : X) : ℝ :=
  positiveValue e0.piLev (k+1) x *
      (positiveValue e0.P1 (k+1) x - positiveValue e.P1 (k+1) x) /
        positiveValue e.piLev (k+1) x -
  positiveValue e0.piLev k x * (positiveValue e0.P1 k x - positiveValue e.P1 k x) /
      positiveValue e.piLev k x -
  positiveValue e0.piLev (k+1) x *
      (positiveValue e0.pLev (k+1) x - positiveValue e.pLev (k+1) x) /
        positiveValue e.piLev (k+1) x -
  ((positiveValue e.pLev (k+1) x - binFullJ L e k x) -
    (positiveValue e0.pLev (k+1) x - binFullJ L e0 k x))

-- @node: binary_boundary_centered_residual_aestronglyMeasurable
/-- If [the reference binary nuisances are admissible](hyp:he0) and [the fitted binary nuisances are admissible](hyp:he), [the centered binary boundary residual at any level is almost everywhere strongly measurable under the covariate law](goal). -/
@[fun_prop] lemma binary_boundary_centered_residual_aestronglyMeasurable
    (L : LevelData Z X) (e0 e : NuisanceBin L)
    (he0 : BinAdmissible M L e0) (he : BinAdmissible M L e) (k : ℕ) :
    AEStronglyMeasurable (binaryBoundaryCenteredResidual L e0 e k) (xLaw M) := by
  first | fun_prop | skip
  have hP (i : ℕ) := (fitted_positive_success_memLp M L e he i).1.aemeasurable
  have hP0 (i : ℕ) := (fitted_positive_success_memLp M L e0 he0 i).1.aemeasurable
  have hp (i : ℕ) := (fitted_positive_treatment_assignment_memLp M L e he i).1.1.aemeasurable
  have hp0 (i : ℕ) := (fitted_positive_treatment_assignment_memLp M L e0 he0 i).1.1.aemeasurable
  have ht (i : ℕ) := (fitted_positive_treatment_assignment_memLp M L e he i).2.1.aemeasurable
  have ht0 (i : ℕ) := (fitted_positive_treatment_assignment_memLp M L e0 he0 i).2.1.aemeasurable
  unfold binaryBoundaryCenteredResidual binFullJ
  apply AEMeasurable.aestronglyMeasurable
  exact (((((ht0 (k+1)).mul ((hP0 (k+1)).sub (hP (k+1)))).div (ht (k+1))).sub
    (((ht0 k).mul ((hP0 k).sub (hP k))).div (ht k))).sub
      (((ht0 (k+1)).mul ((hp0 (k+1)).sub (hp (k+1)))).div (ht (k+1)))).sub
        (((hp (k+1)).sub ((hP (k+1)).sub (hP k))).sub
          ((hp0 (k+1)).sub ((hP0 (k+1)).sub (hP0 k))))

-- @node: binary_boundary_residual_envelope_integrable
/-- If [the reference nuisances are admissible](hyp:he0), [the fitted nuisances are admissible](hyp:he), and [the envelope scaling constant is positive](hyp:hc), [the binary boundary residual envelope is integrable under the covariate law at every level](goal). -/
lemma binary_boundary_residual_envelope_integrable (L : LevelData Z X)
    (e0 e : NuisanceBin L) (he0 : BinAdmissible M L e0) (he : BinAdmissible M L e)
    (c : ℝ) (hc : 0 < c) (k : ℕ) :
    Integrable (binaryBoundaryResidualEnvelope L e0 e c k) (xLaw M) := by
  have hpi (i : ℕ) := ((fitted_positive_treatment_assignment_memLp M L e he i).2).sub
    (fitted_positive_treatment_assignment_memLp M L e0 he0 i).2
  have hP (i : ℕ) := (fitted_positive_success_memLp M L e he i).sub
    (fitted_positive_success_memLp M L e0 he0 i)
  have hp (i : ℕ) := ((fitted_positive_treatment_assignment_memLp M L e he i).1).sub
    (fitted_positive_treatment_assignment_memLp M L e0 he0 i).1
  have hS (i : ℕ) := ((hpi i).norm.integrable_mul (hP i).norm).div_const c
  have hT (i : ℕ) := ((hpi i).norm.integrable_mul (hp i).norm).div_const c
  have hi := ((hS (k+1)).fun_add (hT (k+1))).fun_add (hS k)
  apply hi.congr
  exact Eventually.of_forall (fun x => by
    simp only [Pi.mul_apply, Pi.sub_apply, Real.norm_eq_abs]
    dsimp only [binaryBoundaryResidualEnvelope]
    ring)

-- @node: fitted_boundary_centered_residual_weighted_integral_bound
/-- Suppose [the reference nuisances are admissible](hyp:he0), [the fitted nuisances are admissible](hyp:he), [the clipping constant is positive](hyp:hc), [the weight bound is nonnegative](hyp:hW), and [all fitted positive-level assignment probabilities are at least the clipping constant almost everywhere](hyp:hclip). If [the weight is almost everywhere strongly measurable](hyp:hw) and [its absolute value is almost everywhere at most the weight bound](hyp:hwb), [the weighted centered boundary residual is integrable, and its absolute population mean is bounded by the weight bound times the population mean of the boundary residual envelope](goal). -/
lemma fitted_boundary_centered_residual_weighted_integral_bound
    (L : LevelData Z X) (e0 e : NuisanceBin L)
    (he0 : BinAdmissible M L e0) (he : BinAdmissible M L e)
    (c W : ℝ) (hc : 0 < c) (hW : 0 ≤ W) (k : ℕ)
    (hclip : ∀ i, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (w : X → ℝ) (hw : AEStronglyMeasurable w (xLaw M))
    (hwb : ∀ᵐ x ∂xLaw M, ‖w x‖ ≤ W) :
    Integrable (fun x => w x * binaryBoundaryCenteredResidual L e0 e k x) (xLaw M) ∧
    |∫ x, w x * binaryBoundaryCenteredResidual L e0 e k x ∂xLaw M| ≤
      W * ∫ x, binaryBoundaryResidualEnvelope L e0 e c k x ∂xLaw M := by
  have hi := binary_boundary_residual_envelope_integrable M L e0 e he0 he c hc k
  have hb : ∀ᵐ x ∂xLaw M, |binaryBoundaryCenteredResidual L e0 e k x| ≤
      binaryBoundaryResidualEnvelope L e0 e c k x :=
    binary_boundary_residual_envelope_ae M L e0 e c hc k hclip
  have hR : Integrable (binaryBoundaryCenteredResidual L e0 e k) (xLaw M) :=
    hi.mono' (by first | fun_prop | exact binary_boundary_centered_residual_aestronglyMeasurable M L e0 e he0 he k) (by simpa only [Real.norm_eq_abs] using hb)
  have hiw := hR.bdd_mul hw hwb
  refine ⟨hiw, ?_⟩
  calc
    _ ≤ ∫ x, |w x * binaryBoundaryCenteredResidual L e0 e k x| ∂xLaw M := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun x => w x * binaryBoundaryCenteredResidual L e0 e k x)
    _ ≤ ∫ x, W * binaryBoundaryResidualEnvelope L e0 e c k x ∂xLaw M := by
      apply integral_mono_ae hiw.abs (hi.const_mul W)
      filter_upwards [hwb, hb] with x hwx hx
      rw [abs_mul]
      exact mul_le_mul (by simpa only [Real.norm_eq_abs] using hwx) hx (abs_nonneg _) hW
    _ = _ := integral_const_mul _ _

-- Original nuisance rates control a random fitted branch weight.
-- @node: nuisanceRates_boundary_centered_residual_weighted_root_n_negligible
/-- Suppose [the reference nuisances are admissible](hyp:he0), [all fitted nuisance vectors are admissible](hyp:heh), [the clipping constant is positive](hyp:hc), [the weight bound is nonnegative](hyp:hW), and [all fitted positive-level assignment probabilities are uniformly bounded below by the clipping constant almost everywhere](hyp:hclip). If [each fitted weight is almost everywhere strongly measurable](hyp:hw), [the weights obey the uniform absolute bound almost everywhere](hyp:hwb), [success regressions satisfy the finite nuisance rate conditions](hyp:hrP), [treatment regressions satisfy those rate conditions](hyp:hrp), and [assignment probabilities satisfy those rate conditions](hyp:hrpi), [the weighted centered boundary residual mean at even sample sizes, multiplied by the square root of the half-sample size, converges to zero in probability](goal). -/
lemma nuisanceRates_boundary_centered_residual_weighted_root_n_negligible
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (L : LevelData Z X) (e0 : NuisanceBin L) (eh : ℕ → A → NuisanceBin L)
    (he0 : BinAdmissible M L e0) (heh : ∀ n a, BinAdmissible M L (eh n a))
    (c W : ℝ) (hc : 0 < c) (hW : 0 ≤ W) (k : ℕ)
    (hclip : ∀ n a i, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).piLev i x)
    (w : ℕ → A → X → ℝ) (hw : ∀ n a, AEStronglyMeasurable (w n a) (xLaw M))
    (hwb : ∀ n a, ∀ᵐ x ∂xLaw M, ‖w n a x‖ ≤ W)
    (hrP : FiniteNuisanceRates M μ (fun n a => (eh n a).P1) e0.P1)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) e0.piLev) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) * ∫ x,
        w (2*(n+1)) a x * binaryBoundaryCenteredResidual L e0 (eh (2*(n+1)) a) k x
        ∂xLaw M) atTop (fun _ _ => 0) := by
  have hE := binary_boundary_residual_envelope_root_n_negligible M μ L e0 eh he0 heh
    c hc k hrP hrp hrpi
  rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm] at hE ⊢
  intro eps heps
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hE (eps / (W+1)) (by positivity))
    (fun _ => zero_le)
  intro n
  apply measure_mono
  intro a ha
  have hb := (fitted_boundary_centered_residual_weighted_integral_bound M L e0
    (eh (2*(n+1)) a) he0 (heh _ a) c W hc hW k (hclip _ a)
    (w (2*(n+1)) a) (hw _ a) (hwb _ a)).2
  have hn : 0 ≤ ∫ x, binaryBoundaryResidualEnvelope L e0 (eh (2*(n+1)) a) c k x
      ∂xLaw M := by
    apply integral_nonneg
    intro x
    dsimp only [binaryBoundaryResidualEnvelope]
    positivity
  change eps ≤ ‖_ - 0‖ at ha
  change eps / (W+1) ≤ ‖_ - 0‖
  simp only [sub_zero, norm_mul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg hW, abs_of_nonneg hn] at ha ⊢
  rw [div_le_iff₀ (by positivity : 0 < W+1)]
  have hs := mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg ((n+1 : ℕ) : ℝ))
  have hprod := mul_nonneg (Real.sqrt_nonneg ((n+1 : ℕ) : ℝ)) hn
  nlinarith

-- The branch is fitted, not replaced by its population value. Its unit bound
-- and measurability follow from the clipped construction.
-- @node: nuisanceRates_fractional_boundary_correction_root_n_negligible
/-- Suppose [the policy is a measurable probability-valued map](hyp:hphi), [the reference nuisances are admissible](hyp:he0), [all fitted nuisance vectors are admissible](hyp:heh), [the clipping constant is positive](hyp:hc), and [all fitted positive-level assignment probabilities are uniformly bounded below by it almost everywhere](hyp:hclip). If [success regressions satisfy the finite nuisance rate conditions](hyp:hrP), [treatment regressions satisfy those rate conditions](hyp:hrp), and [assignment probabilities satisfy those rate conditions](hyp:hrpi), [the mean of the centered boundary residual multiplied by the fitted regular weight and fitted boundary indicator, at even sample sizes and scaled by the square root of the half-sample size, converges to zero in probability](goal). -/
lemma nuisanceRates_fractional_boundary_correction_root_n_negligible
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
        regularValue (eh (2*(n+1)) a).gamma k j x * Dbd phi L (eh (2*(n+1)) a) k j x *
          binaryBoundaryCenteredResidual L e0 (eh (2*(n+1)) a) k x ∂xLaw M)
      atTop (fun _ _ => 0) := by
  apply nuisanceRates_boundary_centered_residual_weighted_root_n_negligible
    M μ L e0 eh he0 heh c 1 hc zero_le_one k hclip
    (fun n a x => regularValue (eh n a).gamma k j x * Dbd phi L (eh n a) k j x)
  · intro n a
    first | fun_prop | skip
    exact (fitted_regular_gamma_memLp M L (eh n a) (heh n a) k j).1.mul
      (fitted_fractional_branches_memLp M phi hphi L (eh n a) (heh n a) k j).2.1.1
  · intro n a
    have hg : ∀ᵐ x ∂xLaw M, ‖regularValue (eh n a).gamma k j x‖ ≤ 1 := by
      unfold regularValue
      split_ifs with hi
      · filter_upwards [(heh n a).2.2.2.2.1 ⟨(k,j), hi⟩] with x hx
        rw [Real.norm_eq_abs, abs_of_nonneg hx.2.1]
        exact hx.2.2
      · simp
    filter_upwards [hg] with x hx
    have hb : ‖Dbd phi L (eh n a) k j x‖ ≤ 1 := by
      unfold Dbd indicator
      split_ifs <;> norm_num
    rw [norm_mul]
    exact (mul_le_mul hx hb (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  · exact hrP
  · exact hrp
  · exact hrpi

end Papers.TbsPrteOptimalTransport

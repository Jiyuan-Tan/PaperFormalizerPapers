module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLFractionalResidualConvergence
public import Papers.TbsPrteOptimalTransport.Helpers.DMLFiniteFullScoreConvergence
public import Papers.TbsPrteOptimalTransport.Helpers.RegularRegressionMean
/-! Second moments and convergence of the fractional binary treatment corrections.
The interior and dominance coefficients are controlled by the separated branches,
and the treatment residuals by component nuisance rates and clipped denominators. -/
public section
set_option linter.style.longLine false
set_option linter.style.openClassical false
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

-- @node: fitted_fractional_treatment_coefficient_memLp
/-- If [the policy satisfies the policy restrictions](hyp:hphi) and [the binary nuisance vector is admissible](hyp:he),
then [the fractional treatment coefficient is square-integrable under the observation law, whether one selects the interior indicator or the product of the dominance and active indicators](goal). -/
lemma fitted_fractional_treatment_coefficient_memLp
    (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (L : LevelData Z X) (e : NuisanceBin L) (he : BinAdmissible M L e)
    (k j : ℕ) (b : Bool) :
    MemLp (fun o : Obs X Z => if b then Dbd phi L e k j o.1 else
      Edom phi L e k j o.1 * Iact phi L e k j o.1) 2 (observationLaw M) := by
  have hmp := observationLaw_fst_measurePreserving M
  obtain ⟨hI, hD, hE⟩ := fitted_fractional_branches_memLp M phi hphi L e he k j
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hi := hI.comp_measurePreserving hmp
    have he := hE.comp_measurePreserving hmp
    apply hi.norm.mono' (by first | fun_prop | exact he.1.mul hi.1)
    exact Eventually.of_forall (fun o => by
      rw [norm_mul]
      have hb : ‖Edom phi L e k j o.1‖ ≤ 1 := by
        unfold Edom indicator
        split_ifs <;> norm_num
      exact mul_le_of_le_one_left (norm_nonneg _) hb)
  · simpa only [↓reduceIte, Function.comp_def] using hD.comp_measurePreserving hmp

-- Both choices are actual coefficients in the regular regression correction.
-- @node: nuisanceRates_fractional_treatment_coefficient_sq_tendsto_probability_zero
/-- Suppose [the policy satisfies the policy restrictions](hyp:hphi), [the specified derivative differentiates it](hyp:hd),
[the derivative is bounded and Lipschitz](hyp:hDerivative), [the reference nuisance vector is admissible](hyp:he0),
and [every fitted nuisance vector is admissible](hyp:heh). If
[instrument propensities, treatment-level probabilities, and success probabilities satisfy the finite nuisance rates](hyp:hrp,hrlev,hrP),
[every regular share satisfies those rates](hyp:hrs), [the separation constant is positive](hyp:hsep), and
[the reference pooled policy endpoints are separated by that constant and the branch threshold stays at least that far from both endpoints almost everywhere](hyp:hgap), then
[the integrated squared error of either fractional treatment coefficient, the interior indicator or the dominance-times-active indicator, converges in probability to zero along sample sizes twice n plus two](goal). -/
lemma nuisanceRates_fractional_treatment_coefficient_sq_tendsto_probability_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e0 : NuisanceBin L) (eh : ℕ → A → NuisanceBin L)
    (he0 : BinAdmissible M L e0) (heh : ∀ n a, BinAdmissible M L (eh n a))
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) e0.prop)
    (hrlev : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrP : FiniteNuisanceRates M μ (fun n a => (eh n a).P1) e0.P1)
    (hrs : ∀ a : RegularIndex L,
      FiniteNuisanceRates M μ (fun n t => (eh n t).share a) (e0.share a))
    (k j : ℕ) (b : Bool)
    (sep : ℝ) (hsep : 0 < sep)
    (hgap : ∀ᵐ x ∂xLaw M,
      sep ≤ pooledQBin phi L e0 k j x - pooledQBin phi L e0 k (j-1) x ∧
      sep ≤ |positiveValue e0.pLev (k+1) x - binFullJ L e0 k x -
        pooledQBin phi L e0 k (j-1) x| ∧
      sep ≤ |positiveValue e0.pLev (k+1) x - binFullJ L e0 k x -
        pooledQBin phi L e0 k j x|) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o : Obs X Z,
        ((if b then Dbd phi L (eh (2*(n+1)) a) k j o.1 else
            Edom phi L (eh (2*(n+1)) a) k j o.1 * Iact phi L (eh (2*(n+1)) a) k j o.1) -
          (if b then Dbd phi L e0 k j o.1 else
            Edom phi L e0 k j o.1 * Iact phi L e0 k j o.1))^2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  have hr := nuisanceRates_fractional_branch_observation_sq_tendsto_probability_zero
    M μ phi dphi hphi hd hDerivative L e0 eh he0 heh hrp hrlev hrP hrs k j sep hsep hgap
  have hc : Continuous (fun t : ℝ => 2*t) := by fun_prop
  have hr2 := Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt hc.continuousAt hr
  simp only [mul_zero] at hr2
  apply probability_zero_of_nonneg_le μ _ _ hr2
  intro n
  apply Eventually.of_forall
  intro a
  refine ⟨integral_nonneg (fun _ => sq_nonneg _), ?_⟩
  have hmp := observationLaw_fst_measurePreserving M
  obtain ⟨hI, hD, hE⟩ := fitted_fractional_branches_memLp M phi hphi L e0 he0 k j
  obtain ⟨hIh, hDh, hEh⟩ := fitted_fractional_branches_memLp M phi hphi L _ (heh (2*(n+1)) a) k j
  have hi := ((hIh.sub hI).comp_measurePreserving hmp).integrable_sq
  have hdi := ((hDh.sub hD).comp_measurePreserving hmp).integrable_sq
  have he := ((hEh.sub hE).comp_measurePreserving hmp).integrable_sq
  have hm := ((fitted_fractional_treatment_coefficient_memLp M phi hphi L _ (heh (2*(n+1)) a) k j b).sub
    (fitted_fractional_treatment_coefficient_memLp M phi hphi L e0 he0 k j b)).integrable_sq
  rw [← integral_const_mul]
  apply integral_mono hm (((hi.add hdi).add he).const_mul 2)
  intro o
  dsimp only [Pi.sub_apply, Pi.add_apply, Function.comp_apply]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hbE : |Edom phi L (eh (2*(n+1)) a) k j o.1| ≤ 1 := by
      unfold Edom indicator
      split_ifs <;> norm_num
    have hbI : |Iact phi L e0 k j o.1| ≤ 1 := by
      unfold Iact indicator
      split_ifs <;> norm_num
    have hb := clipped_weighted_residual_sq_difference_bound
      (w := Edom phi L e0 k j o.1)
      (fh := Iact phi L (eh (2*(n+1)) a) k j o.1) hbE hbI
    norm_num only [one_pow, mul_one] at hb
    nlinarith [sq_nonneg (Dbd phi L (eh (2*(n+1)) a) k j o.1 - Dbd phi L e0 k j o.1)]
  · simp only [↓reduceIte]
    nlinarith [sq_nonneg (Iact phi L (eh (2*(n+1)) a) k j o.1 - Iact phi L e0 k j o.1),
      sq_nonneg (Dbd phi L (eh (2*(n+1)) a) k j o.1 - Dbd phi L e0 k j o.1),
      sq_nonneg (Edom phi L (eh (2*(n+1)) a) k j o.1 - Edom phi L e0 k j o.1)]

-- @node: fitted_fractional_treatment_residual_memLp
/-- If [the policy satisfies the policy restrictions](hyp:hphi), [the binary nuisance vector is admissible](hyp:he),
[the clipping constant is positive](hyp:hc), [positive-level assignment probabilities are bounded below by that constant almost everywhere](hyp:hclip),
and [the residual index is no larger than the number of levels](hyp:hi), then
[either fractional treatment coefficient multiplied by the treatment residual is square-integrable under the observation law](goal). -/
lemma fitted_fractional_treatment_residual_memLp
    (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (L : LevelData Z X) (e : NuisanceBin L) (he : BinAdmissible M L e)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (k j i : ℕ) (hi : i ≤ L.K) (b : Bool) :
    MemLp (fun o : Obs X Z =>
      (if b then Dbd phi L e k j o.1 else Edom phi L e k j o.1 * Iact phi L e k j o.1) *
        Rp L e i o) 2 (observationLaw M) := by
  have hw := fitted_fractional_treatment_coefficient_memLp M phi hphi L e he k j b
  have hr := fitted_Rp_memLp M L e he c hc hclip i hi
  apply hr.norm.mono' (by first | fun_prop | exact hw.1.mul hr.1)
  exact Eventually.of_forall (fun o => by
    rw [norm_mul]
    have hb : ‖(if b then Dbd phi L e k j o.1 else
        Edom phi L e k j o.1 * Iact phi L e k j o.1)‖ ≤ 1 := by
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · unfold Edom Iact indicator
        split_ifs <;> norm_num
      · unfold Dbd indicator
        split_ifs <;> norm_num
    exact mul_le_of_le_one_left (norm_nonneg _) hb)

-- Branch and treatment-residual energies are derived separately before multiplication.
-- @node: nuisanceRates_fractional_treatment_residual_sq_tendsto_probability_zero
/-- Suppose [the policy satisfies the policy restrictions](hyp:hphi), [the given derivative differentiates it](hyp:hd),
[the derivative is bounded and Lipschitz](hyp:hDerivative), [the reference nuisance vector is admissible](hyp:he0),
and [all fitted nuisance vectors are admissible](hyp:heh). Assume [a positive clipping constant](hyp:hc),
[reference and fitted positive-level assignment probabilities bounded below by that constant almost everywhere](hyp:hclip),
[finite nuisance rates for instrument propensities, treatment-level probabilities, success probabilities, and assignment probabilities](hyp:hrp,hrlev,hrP,hrpi),
[finite nuisance rates for every regular share](hyp:hrs), [a residual index no larger than the number of levels](hyp:hi),
[a positive separation constant](hyp:hsep), and
[reference pooled policy endpoints separated by that constant and a branch threshold at least that far from both endpoints almost everywhere](hyp:hgap).
Then [the integrated squared error of either fractional treatment coefficient times the treatment residual converges in probability to zero along sample sizes twice n plus two](goal). -/
lemma nuisanceRates_fractional_treatment_residual_sq_tendsto_probability_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e0 : NuisanceBin L) (eh : ℕ → A → NuisanceBin L)
    (he0 : BinAdmissible M L e0) (heh : ∀ n a, BinAdmissible M L (eh n a))
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a (i : PositiveIndex L.K), ∀ᵐ x ∂xLaw M,
      c ≤ e0.piLev i x ∧ c ≤ (eh n a).piLev i x)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) e0.prop)
    (hrlev : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrP : FiniteNuisanceRates M μ (fun n a => (eh n a).P1) e0.P1)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) e0.piLev)
    (hrs : ∀ a : RegularIndex L,
      FiniteNuisanceRates M μ (fun n t => (eh n t).share a) (e0.share a))
    (k j i : ℕ) (hi : i ≤ L.K) (b : Bool)
    (sep : ℝ) (hsep : 0 < sep)
    (hgap : ∀ᵐ x ∂xLaw M,
      sep ≤ pooledQBin phi L e0 k j x - pooledQBin phi L e0 k (j-1) x ∧
      sep ≤ |positiveValue e0.pLev (k+1) x - binFullJ L e0 k x -
        pooledQBin phi L e0 k (j-1) x| ∧
      sep ≤ |positiveValue e0.pLev (k+1) x - binFullJ L e0 k x -
        pooledQBin phi L e0 k j x|) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o : Obs X Z,
        ((if b then Dbd phi L (eh (2*(n+1)) a) k j o.1 else
            Edom phi L (eh (2*(n+1)) a) k j o.1 * Iact phi L (eh (2*(n+1)) a) k j o.1) *
            Rp L (eh (2*(n+1)) a) i o -
          (if b then Dbd phi L e0 k j o.1 else
            Edom phi L e0 k j o.1 * Iact phi L e0 k j o.1) * Rp L e0 i o)^2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  let w := fun (e : NuisanceBin L) (o : Obs X Z) => if b then Dbd phi L e k j o.1 else
    Edom phi L e k j o.1 * Iact phi L e k j o.1
  have hw (e : NuisanceBin L) (he : BinAdmissible M L e) :=
    fitted_fractional_treatment_coefficient_memLp M phi hphi L e he k j b
  apply dml_ae_weighted_residual_sq_tendsto_probability_zero μ (observationLaw M)
    (w e0) (Rp L e0 i) (fun n a => w (eh (2*(n+1)) a))
    (fun n a => Rp L (eh (2*(n+1)) a) i) 1 (1/c)
    (hw e0 he0).1 (by fun_prop) (fun n a => (hw _ (heh (2*(n+1)) a)).1)
    (by
      intro n a
      first | fun_prop | exact (fitted_Rp_memLp M L _ (heh (2*(n+1)) a) c hc
        (fun t => (hclip (2*(n+1)) a t).mono (fun _ hx => hx.2)) i hi).1)
  · exact fun n a => (hw _ (heh (2*(n+1)) a)).sub (hw e0 he0)
  · intro n a
    exact (fitted_Rp_memLp M L _ (heh (2*(n+1)) a) c hc
      (fun t => (hclip _ a t).mono (fun _ hx => hx.2)) i hi).sub
      (fitted_Rp_memLp M L e0 he0 c hc
        (fun t => (hclip (2*(n+1)) a t).mono (fun _ hx => hx.1)) i hi)
  · intro n a
    exact Eventually.of_forall (fun o => by
      dsimp only [w]
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · unfold Edom Iact indicator
        split_ifs <;> norm_num
      · unfold Dbd indicator
        split_ifs <;> norm_num)
  · exact fun n a => fitted_Rp_abs_bound M L e0 he0 c hc
      (fun t => (hclip n a t).mono (fun _ hx => hx.1)) i hi
  · exact nuisanceRates_fractional_treatment_coefficient_sq_tendsto_probability_zero
      M μ phi dphi hphi hd hDerivative L e0 eh he0 heh hrp hrlev hrP hrs k j b sep hsep hgap
  · exact nuisanceRates_Rp_sq_tendsto_probability_zero M μ L e0 eh he0 heh
      c hc hclip hrlev hrpi i hi

-- All four corrections are retained, including the dominance term at j=1.
-- @node: fitted_regular_regression_correction_memLp
/-- If [the policy satisfies the policy restrictions](hyp:hphi), [the binary nuisance vector is admissible](hyp:he),
[the outcome is binary almost surely](hyp:hy), [the clipping constant is positive](hyp:hc),
[positive-level assignment probabilities are bounded below by that constant almost everywhere](hyp:hclip), and
[the interval index is smaller than the number of levels](hyp:hk), then
[the complete regular regression correction, including its first-band dominance term, is square-integrable under the observation law](goal). -/
lemma fitted_regular_regression_correction_memLp
    (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (L : LevelData Z X) (e : NuisanceBin L) (he : BinAdmissible M L e)
    (hy : OutcomeBinaryAE M) (c : ℝ) (hc : 0 < c)
    (hclip : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (k j : ℕ) (hk : k < L.K) :
    MemLp (binaryRegularRegressionCorrection phi L e k j) 2 (observationLaw M) := by
  have hp := fitted_Dbd_RP_memLp M phi hphi L e he hy c hc hclip k j (k+1) (by omega)
  have hm := fitted_Dbd_RP_memLp M phi hphi L e he hy c hc hclip k j k hk.le
  have ht := fitted_fractional_treatment_residual_memLp M phi hphi L e he c hc
    hclip k j (k+1) (by omega) true
  have hb := fitted_fractional_treatment_residual_memLp M phi hphi L e he c hc
    hclip k j k hk.le false
  have hi : MemLp (fun o => if j = 1 then
      Edom phi L e k j o.1 * Iact phi L e k j o.1 * Rp L e k o else 0)
      2 (observationLaw M) := by
    by_cases hj : j = 1
    · simpa only [hj, Bool.false_eq_true, ↓reduceIte] using hb
    · simpa only [hj, Bool.false_eq_true, ↓reduceIte] using (MemLp.zero' : MemLp (0 : Obs X Z → ℝ) 2 (observationLaw M))
  convert ((hp.sub hm).sub ht).sub hi using 1
  funext o
  simp only [binaryRegularRegressionCorrection, Pi.sub_apply, ↓reduceIte]
  ring

-- @node: nuisanceRates_regular_regression_correction_sq_tendsto_probability_zero
/-- Suppose [the policy satisfies the policy restrictions](hyp:hphi), [the given derivative differentiates it](hyp:hd),
[the derivative is bounded and Lipschitz](hyp:hDerivative), [the reference nuisance vector is admissible](hyp:he0),
[all fitted nuisance vectors are admissible](hyp:heh), and [the outcome is binary almost surely](hyp:hy).
Assume [a positive clipping constant](hyp:hc),
[reference and fitted positive-level assignment probabilities bounded below by that constant almost everywhere](hyp:hclip),
[finite nuisance rates for instrument propensities, treatment-level probabilities, success probabilities, and assignment probabilities](hyp:hrp,hrlev,hrP,hrpi),
[finite nuisance rates for every regular share](hyp:hrs), [an interval index smaller than the number of levels](hyp:hk),
[a positive separation constant](hyp:hsep), and
[reference pooled policy endpoints separated by that constant and a branch threshold at least that far from both endpoints almost everywhere](hyp:hgap).
Then [the integrated squared error of the complete regular regression correction converges in probability to zero along sample sizes twice n plus two](goal). -/
lemma nuisanceRates_regular_regression_correction_sq_tendsto_probability_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e0 : NuisanceBin L) (eh : ℕ → A → NuisanceBin L)
    (he0 : BinAdmissible M L e0) (heh : ∀ n a, BinAdmissible M L (eh n a))
    (hy : OutcomeBinaryAE M) (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a (i : PositiveIndex L.K), ∀ᵐ x ∂xLaw M,
      c ≤ e0.piLev i x ∧ c ≤ (eh n a).piLev i x)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) e0.prop)
    (hrlev : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrP : FiniteNuisanceRates M μ (fun n a => (eh n a).P1) e0.P1)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) e0.piLev)
    (hrs : ∀ a : RegularIndex L,
      FiniteNuisanceRates M μ (fun n t => (eh n t).share a) (e0.share a))
    (k j : ℕ) (hk : k < L.K)
    (sep : ℝ) (hsep : 0 < sep)
    (hgap : ∀ᵐ x ∂xLaw M,
      sep ≤ pooledQBin phi L e0 k j x - pooledQBin phi L e0 k (j-1) x ∧
      sep ≤ |positiveValue e0.pLev (k+1) x - binFullJ L e0 k x -
        pooledQBin phi L e0 k (j-1) x| ∧
      sep ≤ |positiveValue e0.pLev (k+1) x - binFullJ L e0 k x -
        pooledQBin phi L e0 k j x|) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o,
        (binaryRegularRegressionCorrection phi L (eh (2*(n+1)) a) k j o -
          binaryRegularRegressionCorrection phi L e0 k j o)^2 ∂observationLaw M)
      atTop (fun _ _ => 0) := by
  let P := fun (e : NuisanceBin L) i (o : Obs X Z) => Dbd phi L e k j o.1 * RP L e i o
  let T := fun (e : NuisanceBin L) (o : Obs X Z) => Dbd phi L e k j o.1 * Rp L e (k+1) o
  let B := fun (e : NuisanceBin L) (o : Obs X Z) =>
    if j = 1 then Edom phi L e k j o.1 * Iact phi L e k j o.1 * Rp L e k o else 0
  have hP (e : NuisanceBin L) (he : BinAdmissible M L e)
      (hpi : ∀ i, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x) (i : ℕ) (hi : i ≤ L.K) :
      MemLp (P e i) 2 (observationLaw M) :=
    fitted_Dbd_RP_memLp M phi hphi L e he hy c hc hpi k j i hi
  have hT (e : NuisanceBin L) (he : BinAdmissible M L e)
      (hpi : ∀ i, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x) :
      MemLp (T e) 2 (observationLaw M) := by
    simpa only [T, ↓reduceIte] using fitted_fractional_treatment_residual_memLp M
      phi hphi L e he c hc hpi k j (k+1) (by omega) true
  have hB (e : NuisanceBin L) (he : BinAdmissible M L e)
      (hpi : ∀ i, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x) :
      MemLp (B e) 2 (observationLaw M) := by
    by_cases hj : j = 1
    · simpa only [B, hj, Bool.false_eq_true, ↓reduceIte] using fitted_fractional_treatment_residual_memLp M
        phi hphi L e he c hc hpi k j k hk.le false
    · simpa only [B, hj, Bool.false_eq_true, ↓reduceIte] using
        (MemLp.zero' : MemLp (0 : Obs X Z → ℝ) 2 (observationLaw M))
  have h0 (n : ℕ) (a : A) : ∀ i, ∀ᵐ x ∂xLaw M, c ≤ e0.piLev i x :=
    fun i => (hclip (2*(n+1)) a i).mono (fun _ hx => hx.1)
  have hH (n : ℕ) (a : A) : ∀ i, ∀ᵐ x ∂xLaw M, c ≤ (eh (2*(n+1)) a).piLev i x :=
    fun i => (hclip _ a i).mono (fun _ hx => hx.2)
  have hz : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun (_ : ℕ) (_ : A) => (0 : ℝ)) atTop (fun _ _ => 0) := by
    rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm]
    intro eps heps
    simpa only [sub_self, norm_zero, not_le.mpr heps, Set.ofPred_false,
      measure_empty] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (𝓝 0))
  have hrP' (i : ℕ) (hi : i ≤ L.K) :=
    nuisanceRates_Dbd_RP_sq_tendsto_probability_zero M μ phi dphi hphi hd hDerivative
      L e0 eh he0 heh hy c hc hclip hrp hrlev hrP hrpi hrs k j i hi sep hsep hgap
  have hrT := nuisanceRates_fractional_treatment_residual_sq_tendsto_probability_zero
    M μ phi dphi hphi hd hDerivative L e0 eh he0 heh c hc hclip hrp hrlev hrP hrpi hrs
      k j (k+1) (by omega) true sep hsep hgap
  have hrB : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o, (B (eh (2*(n+1)) a) o - B e0 o)^2 ∂observationLaw M)
      atTop (fun _ _ => 0) := by
    by_cases hj : j = 1
    · simpa only [B, hj, Bool.false_eq_true, ↓reduceIte] using
        nuisanceRates_fractional_treatment_residual_sq_tendsto_probability_zero
          M μ phi dphi hphi hd hDerivative L e0 eh he0 heh c hc hclip hrp hrlev hrP hrpi hrs
            k j k hk.le false sep hsep hgap
    · simpa only [B, hj, ↓reduceIte, sub_self, zero_pow (by norm_num : 2 ≠ 0),
        integral_zero] using hz
  have hpair := dml_three_term_sq_tendsto_probability_zero μ (observationLaw M)
    (fun n a o => P (eh (2*(n+1)) a) (k+1) o - P e0 (k+1) o)
    (fun _ _ _ => 0) (fun n a o => P (eh (2*(n+1)) a) k o - P e0 k o)
    (fun n a => (hP _ (heh (2*(n+1)) a) (hH n a) (k+1) (by omega)).sub
      (hP e0 he0 (h0 n a) (k+1) (by omega)))
    (fun _ _ => MemLp.zero')
    (fun n a => (hP _ (heh (2*(n+1)) a) (hH n a) k hk.le).sub (hP e0 he0 (h0 n a) k hk.le))
    (hrP' (k+1) (by omega)) (by simpa using hz) (hrP' k hk.le)
  have ht := dml_three_term_sq_tendsto_probability_zero μ (observationLaw M)
    (fun n a o => (P (eh (2*(n+1)) a) (k+1) o - P e0 (k+1) o) + 0 -
      (P (eh (2*(n+1)) a) k o - P e0 k o))
    (fun n a o => -(T (eh (2*(n+1)) a) o - T e0 o))
    (fun n a o => B (eh (2*(n+1)) a) o - B e0 o)
    (fun n a => (((hP _ (heh (2*(n+1)) a) (hH n a) (k+1) (by omega)).sub
      (hP e0 he0 (h0 n a) (k+1) (by omega))).add MemLp.zero').sub
      ((hP _ (heh (2*(n+1)) a) (hH n a) k hk.le).sub (hP e0 he0 (h0 n a) k hk.le)))
    (fun n a => ((hT _ (heh (2*(n+1)) a) (hH n a)).sub (hT e0 he0 (h0 n a))).neg)
    (fun n a => (hB _ (heh (2*(n+1)) a) (hH n a)).sub (hB e0 he0 (h0 n a)))
    hpair (by simpa only [T, ↓reduceIte, neg_sq] using hrT) hrB
  convert ht using 1
  funext n a
  apply integral_congr_ae
  exact Eventually.of_forall (fun o => by
    dsimp only [P, T, B, binaryRegularRegressionCorrection]
    ring)

end Papers.TbsPrteOptimalTransport

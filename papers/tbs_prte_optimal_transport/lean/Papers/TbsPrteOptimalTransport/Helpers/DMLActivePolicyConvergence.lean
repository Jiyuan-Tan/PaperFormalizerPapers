module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLPolicyResidualConvergence
/-! Convergence of the active-branch policy residual corrections in the binary score.
The branch gap controls fitted indicators and clipped denominator rates control
RqBin; their product is assembled from these two derived convergence results. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.openClassical false
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

-- @node: fitted_fractional_policy_coefficient_memLp
/-- For [a valid policy map](hyp:hphi) and [an admissible binary nuisance specification](hyp:he), [both the active-branch indicator and its product with the lower-boundary dominance indicator are square integrable under the observation law, as selected by the Boolean flag](goal). -/
lemma fitted_fractional_policy_coefficient_memLp
    (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (L : LevelData Z X) (e : NuisanceBin L) (he : BinAdmissible M L e)
    (k j : ℕ) (b : Bool) :
    MemLp (fun o : Obs X Z => if b then Iact phi L e k j o.1 else
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
  · simpa only [↓reduceIte, Function.comp_def] using hI.comp_measurePreserving hmp

-- Both choices are the active coefficients multiplying policy residuals.
-- @node: nuisanceRates_fractional_policy_coefficient_sq_tendsto_probability_zero
/-- Assume [a valid policy map](hyp:hphi), [its differentiability](hyp:hd), [a bounded Lipschitz derivative](hyp:hDerivative), [an admissible reference nuisance](hyp:he0), and [admissible fitted nuisances at every sample size and training outcome](hyp:heh). If the fitted [propensities](hyp:hrp), [treatment levels](hyp:hrlev), [treated-outcome probabilities](hyp:hrP), and [within-band shares](hyp:hrs) satisfy the finite componentwise nuisance rates, [the separation constant is positive](hyp:hsep), and [the reference band width and the distances from the full-interval threshold to both band endpoints are almost surely at least that constant](hyp:hgap), then [the observation-integrated squared difference between fitted and reference active policy coefficients converges to zero in probability along sample sizes twice the iteration index plus two, for either Boolean choice of coefficient](goal). -/
lemma nuisanceRates_fractional_policy_coefficient_sq_tendsto_probability_zero
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
        ((if b then Iact phi L (eh (2*(n+1)) a) k j o.1 else
            Edom phi L (eh (2*(n+1)) a) k j o.1 * Iact phi L (eh (2*(n+1)) a) k j o.1) -
          (if b then Iact phi L e0 k j o.1 else
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
  have hm := ((fitted_fractional_policy_coefficient_memLp M phi hphi L _ (heh (2*(n+1)) a) k j b).sub
    (fitted_fractional_policy_coefficient_memLp M phi hphi L e0 he0 k j b)).integrable_sq
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

-- The same bound includes the structurally zero policy boundary.
-- @node: fitted_RqBin_abs_bound
/-- If [the derivative bound is nonnegative](hyp:hB), [the policy derivative is bounded in absolute value by it on the unit interval](hyp:hb), [the nuisance specification is admissible](hyp:he), [the clipping constant is positive](hyp:hc), [every regular policy denominator is almost surely at least that constant](hyp:hclip), and [the level index is at most the number of levels](hyp:hk), [the absolute binary policy residual is almost surely at most the number of instruments in the selected band times the derivative bound divided by the clipping constant](goal). -/
lemma fitted_RqBin_abs_bound (dphi : Z → X → ℝ → ℝ)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ z x p, p ∈ Icc (0 : ℝ) 1 → |dphi z x p| ≤ B)
    (L : LevelData Z X) (e : NuisanceBin L) (he : BinAdmissible M L e)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ r : RegularIndex L, ∀ᵐ x ∂xLaw M, c ≤ e.tauLev r x)
    (k j : ℕ) (hk : k ≤ L.K) :
    ∀ᵐ o ∂observationLaw M, |RqBin dphi L e k j o| ≤ (L.T k j).card * B / c := by
  by_cases hi : j = 0 ∨ L.l k < j
  · simp only [RqBin, if_pos hi, abs_zero]
    exact Eventually.of_forall (fun _ => by positivity)
  have hr : k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k := ⟨hk, by omega, by omega⟩
  let r : RegularIndex L := ⟨(k,j), hr⟩
  filter_upwards [observationLaw_covariate_ae M _ (hclip r),
    fitted_RqBin_numerator_abs_bound M dphi B hB hb L e he k j] with o ht hn
  simp only [RqBin, if_neg hi, regularValue, dif_pos hr, abs_mul]
  have hp := hc.trans_le ht
  rw [abs_of_pos (inv_pos.mpr hp)]
  calc
    _ ≤ c⁻¹ * ((L.T k j).card * B) :=
      mul_le_mul ((inv_le_inv₀ hp hc).mpr ht) hn (abs_nonneg _) (inv_nonneg.mpr hc.le)
    _ = _ := by ring

-- @node: fitted_fractional_policy_residual_memLp
/-- Under [a valid policy map](hyp:hphi), [policy differentiability](hyp:hd), [a bounded Lipschitz policy derivative](hyp:hDerivative), and [an admissible nuisance specification](hyp:he), suppose [the clipping constant is positive](hyp:hc), [all regular policy denominators are almost surely bounded below by it](hyp:hclip), and [the level index is at most the number of levels](hyp:hk). Then [the policy residual at the selected residual index, multiplied by either the active indicator or its product with the lower-boundary dominance indicator at the selected band, is square integrable under the observation law](goal). -/
lemma fitted_fractional_policy_residual_memLp
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e : NuisanceBin L) (he : BinAdmissible M L e)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ i : RegularIndex L, ∀ᵐ x ∂xLaw M, c ≤ e.tauLev i x)
    (k j i : ℕ) (hk : k ≤ L.K) (b : Bool) :
    MemLp (fun o : Obs X Z =>
      (if b then Iact phi L e k j o.1 else Edom phi L e k j o.1 * Iact phi L e k j o.1) *
        RqBin dphi L e k i o) 2 (observationLaw M) := by
  have hw := fitted_fractional_policy_coefficient_memLp M phi hphi L e he k j b
  have hr := fitted_RqBin_memLp M phi dphi hphi hd hDerivative L e he c hc hclip k i hk
  apply hr.norm.mono' (by first | fun_prop | exact hw.1.mul hr.1)
  exact Eventually.of_forall (fun o => by
    rw [norm_mul]
    have hb : ‖(if b then Iact phi L e k j o.1 else
        Edom phi L e k j o.1 * Iact phi L e k j o.1)‖ ≤ 1 := by
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · unfold Edom Iact indicator
        split_ifs <;> norm_num
      · unfold Iact indicator
        split_ifs <;> norm_num
    exact mul_le_of_le_one_left (norm_nonneg _) hb)

-- Branch and policy-residual energies are derived separately before multiplication.
-- @node: nuisanceRates_fractional_policy_residual_sq_tendsto_probability_zero
/-- Assume [a valid policy map](hyp:hphi), [policy differentiability](hyp:hd), [a bounded Lipschitz derivative](hyp:hDerivative), [an admissible reference nuisance](hyp:he0), [admissible fitted nuisances](hyp:heh), [a positive clipping constant](hyp:hc), and [reference and fitted regular policy denominators almost surely bounded below by that constant](hyp:hclip). If the fitted [propensities](hyp:hrp), [treatment levels](hyp:hrlev), [treated-outcome probabilities](hyp:hrP), [policy denominators](hyp:hrt), and [within-band shares](hyp:hrs) satisfy the finite componentwise nuisance rates, [the level index is at most the number of levels](hyp:hk), [the separation constant is positive](hyp:hsep), and [the reference band width and distances from the full-interval threshold to its two endpoints are almost surely at least that separation](hyp:hgap), then [the integrated squared error of either active-coefficient-weighted policy residual converges to zero in probability along sample sizes twice the iteration index plus two](goal). -/
lemma nuisanceRates_fractional_policy_residual_sq_tendsto_probability_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e0 : NuisanceBin L) (eh : ℕ → A → NuisanceBin L)
    (he0 : BinAdmissible M L e0) (heh : ∀ n a, BinAdmissible M L (eh n a))
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a (i : RegularIndex L), ∀ᵐ x ∂xLaw M,
      c ≤ e0.tauLev i x ∧ c ≤ (eh n a).tauLev i x)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) e0.prop)
    (hrlev : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrP : FiniteNuisanceRates M μ (fun n a => (eh n a).P1) e0.P1)
    (hrt : FiniteNuisanceRates M μ (fun n a => (eh n a).tauLev) e0.tauLev)
    (hrs : ∀ a : RegularIndex L,
      FiniteNuisanceRates M μ (fun n t => (eh n t).share a) (e0.share a))
    (k j i : ℕ) (hk : k ≤ L.K) (b : Bool)
    (sep : ℝ) (hsep : 0 < sep)
    (hgap : ∀ᵐ x ∂xLaw M,
      sep ≤ pooledQBin phi L e0 k j x - pooledQBin phi L e0 k (j-1) x ∧
      sep ≤ |positiveValue e0.pLev (k+1) x - binFullJ L e0 k x -
        pooledQBin phi L e0 k (j-1) x| ∧
      sep ≤ |positiveValue e0.pLev (k+1) x - binFullJ L e0 k x -
        pooledQBin phi L e0 k j x|) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o : Obs X Z,
        ((if b then Iact phi L (eh (2*(n+1)) a) k j o.1 else
            Edom phi L (eh (2*(n+1)) a) k j o.1 * Iact phi L (eh (2*(n+1)) a) k j o.1) *
            RqBin dphi L (eh (2*(n+1)) a) k i o -
          (if b then Iact phi L e0 k j o.1 else
            Edom phi L e0 k j o.1 * Iact phi L e0 k j o.1) * RqBin dphi L e0 k i o)^2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  obtain ⟨B, D, hB, hD, hb⟩ := hDerivative
  have hDerivative : PolicyDerivativeBoundedLipschitz dphi := ⟨B, D, hB, hD, hb⟩
  let w := fun (e : NuisanceBin L) (o : Obs X Z) => if b then Iact phi L e k j o.1 else
    Edom phi L e k j o.1 * Iact phi L e k j o.1
  have hw (e : NuisanceBin L) (he : BinAdmissible M L e) :=
    fitted_fractional_policy_coefficient_memLp M phi hphi L e he k j b
  apply dml_ae_weighted_residual_sq_tendsto_probability_zero μ (observationLaw M)
    (w e0) (RqBin dphi L e0 k i) (fun n a => w (eh (2*(n+1)) a))
    (fun n a => RqBin dphi L (eh (2*(n+1)) a) k i) 1 ((L.T k i).card * B / c)
    (hw e0 he0).1 (by
      first | fun_prop | skip
      unfold RqBin
      split_ifs with hz
      · fun_prop
      · have hr : k ≤ L.K ∧ 1 ≤ i ∧ i ≤ L.l k := ⟨hk, by omega, by omega⟩
        simp only [regularValue, dif_pos hr]
        have hm : AEStronglyMeasurable (fun o : Obs X Z => (e0.tauLev ⟨(k,i), hr⟩ o.1)⁻¹)
            (observationLaw M) := ((he0.2.2.2.2.2.1 ⟨(k,i), hr⟩).1.comp measurable_fst).inv.aestronglyMeasurable
        exact hm.mul (fitted_RqBin_numerator_memLp M phi dphi hphi hd hDerivative L e0 he0 k i).1) (fun n a => (hw _ (heh (2*(n+1)) a)).1)
    (by
      intro n a
      first | fun_prop | exact (fitted_RqBin_memLp M phi dphi hphi hd hDerivative L _ (heh (2*(n+1)) a) c hc
        (fun t => (hclip (2*(n+1)) a t).mono (fun _ hx => hx.2)) k i hk).1)
  · exact fun n a => (hw _ (heh (2*(n+1)) a)).sub (hw e0 he0)
  · intro n a
    exact (fitted_RqBin_memLp M phi dphi hphi hd hDerivative L _ (heh (2*(n+1)) a) c hc
      (fun t => (hclip _ a t).mono (fun _ hx => hx.2)) k i hk).sub
      (fitted_RqBin_memLp M phi dphi hphi hd hDerivative L e0 he0 c hc
        (fun t => (hclip (2*(n+1)) a t).mono (fun _ hx => hx.1)) k i hk)
  · intro n a
    exact Eventually.of_forall (fun o => by
      dsimp only [w]
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · unfold Edom Iact indicator
        split_ifs <;> norm_num
      · unfold Iact indicator
        split_ifs <;> norm_num)
  · exact fun n a => fitted_RqBin_abs_bound M dphi B hB
      (fun z x p hp => (hb z x p p hp hp).1) L e0 he0 c hc
      (fun t => (hclip n a t).mono (fun _ hx => hx.1)) k i hk
  · exact nuisanceRates_fractional_policy_coefficient_sq_tendsto_probability_zero
      M μ phi dphi hphi hd hDerivative L e0 eh he0 heh hrp hrlev hrP hrs k j b sep hsep hgap
  · exact nuisanceRates_RqBin_sq_tendsto_probability_zero M μ phi dphi hphi hd hDerivative
      L e0 eh he0 heh c hc hclip hrp hrt k i hk

-- Exactly the last two residual terms of binScoreComponents.
-- @node: binaryRegularPolicyCorrection
/-- For [a policy transformation](hyp:phi), [its derivative function](hyp:dphi), [a level and band configuration](hyp:L), [a binary nuisance specification](hyp:e), [a level index](hyp:k), [a band index](hyp:j), and [an observation](hyp:o), [the regular binary policy correction](goal) is the active indicator times the policy residual at the upper band index, minus the lower-boundary dominance indicator times the active indicator times the policy residual at the preceding index. -/
noncomputable def binaryRegularPolicyCorrection (phi dphi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (e : NuisanceBin L) (k j : ℕ) (o : Obs X Z) : ℝ :=
  Iact phi L e k j o.1 * RqBin dphi L e k j o -
    Edom phi L e k j o.1 * Iact phi L e k j o.1 * RqBin dphi L e k (j-1) o

-- @node: fitted_regular_policy_correction_memLp
/-- Under [a valid policy map](hyp:hphi), [policy differentiability](hyp:hd), [a bounded Lipschitz derivative](hyp:hDerivative), and [an admissible nuisance specification](hyp:he), if [the clipping constant is positive](hyp:hc), [all regular policy denominators are almost surely at least that constant](hyp:hclip), and [the level index is at most the number of levels](hyp:hk), [the complete regular binary policy correction at the selected band is square integrable under the observation law](goal). -/
lemma fitted_regular_policy_correction_memLp
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e : NuisanceBin L) (he : BinAdmissible M L e)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ r : RegularIndex L, ∀ᵐ x ∂xLaw M, c ≤ e.tauLev r x)
    (k j : ℕ) (hk : k ≤ L.K) :
    MemLp (binaryRegularPolicyCorrection phi dphi L e k j) 2 (observationLaw M) := by
  have ht := fitted_fractional_policy_residual_memLp M phi dphi hphi hd hDerivative
    L e he c hc hclip k j j hk true
  have hb := fitted_fractional_policy_residual_memLp M phi dphi hphi hd hDerivative
    L e he c hc hclip k j (j-1) hk false
  change MemLp (fun o : Obs X Z => Iact phi L e k j o.1 * RqBin dphi L e k j o -
    Edom phi L e k j o.1 * Iact phi L e k j o.1 * RqBin dphi L e k (j-1) o) 2 _
  simp only [Bool.false_eq_true, ↓reduceIte] at ht hb
  exact ht.sub hb

-- @node: nuisanceRates_regular_policy_correction_sq_tendsto_probability_zero
/-- Assume [a valid policy map](hyp:hphi), [policy differentiability](hyp:hd), [a bounded Lipschitz derivative](hyp:hDerivative), [an admissible reference nuisance](hyp:he0), [admissible fitted nuisances](hyp:heh), [a positive clipping constant](hyp:hc), and [reference and fitted regular policy denominators almost surely at least that constant](hyp:hclip). If the fitted [propensities](hyp:hrp), [treatment levels](hyp:hrlev), [treated-outcome probabilities](hyp:hrP), [policy denominators](hyp:hrt), and [within-band shares](hyp:hrs) satisfy the finite componentwise nuisance rates, [the level index is at most the number of levels](hyp:hk), [the separation constant is positive](hyp:hsep), and [the reference band width and distances from the full-interval threshold to both endpoints are almost surely at least that separation](hyp:hgap), then [the observation-integrated squared error of the complete regular policy correction converges to zero in probability along sample sizes twice the iteration index plus two](goal). -/
lemma nuisanceRates_regular_policy_correction_sq_tendsto_probability_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e0 : NuisanceBin L) (eh : ℕ → A → NuisanceBin L)
    (he0 : BinAdmissible M L e0) (heh : ∀ n a, BinAdmissible M L (eh n a))
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a (r : RegularIndex L), ∀ᵐ x ∂xLaw M,
      c ≤ e0.tauLev r x ∧ c ≤ (eh n a).tauLev r x)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) e0.prop)
    (hrlev : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrP : FiniteNuisanceRates M μ (fun n a => (eh n a).P1) e0.P1)
    (hrt : FiniteNuisanceRates M μ (fun n a => (eh n a).tauLev) e0.tauLev)
    (hrs : ∀ r : RegularIndex L,
      FiniteNuisanceRates M μ (fun n a => (eh n a).share r) (e0.share r))
    (k j : ℕ) (hk : k ≤ L.K) (sep : ℝ) (hsep : 0 < sep)
    (hgap : ∀ᵐ x ∂xLaw M,
      sep ≤ pooledQBin phi L e0 k j x - pooledQBin phi L e0 k (j-1) x ∧
      sep ≤ |positiveValue e0.pLev (k+1) x - binFullJ L e0 k x -
        pooledQBin phi L e0 k (j-1) x| ∧
      sep ≤ |positiveValue e0.pLev (k+1) x - binFullJ L e0 k x -
        pooledQBin phi L e0 k j x|) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o,
        (binaryRegularPolicyCorrection phi dphi L (eh (2*(n+1)) a) k j o -
          binaryRegularPolicyCorrection phi dphi L e0 k j o)^2 ∂observationLaw M)
      atTop (fun _ _ => 0) := by
  let F := fun (e : NuisanceBin L) (o : Obs X Z) =>
    Iact phi L e k j o.1 * RqBin dphi L e k j o
  let G := fun (e : NuisanceBin L) (o : Obs X Z) =>
    Edom phi L e k j o.1 * Iact phi L e k j o.1 * RqBin dphi L e k (j-1) o
  have hF (e : NuisanceBin L) (he : BinAdmissible M L e)
      (hcl : ∀ r, ∀ᵐ x ∂xLaw M, c ≤ e.tauLev r x) :
      MemLp (F e) 2 (observationLaw M) := by
    simpa only [F, ↓reduceIte] using fitted_fractional_policy_residual_memLp
      M phi dphi hphi hd hDerivative L e he c hc hcl k j j hk true
  have hG (e : NuisanceBin L) (he : BinAdmissible M L e)
      (hcl : ∀ r, ∀ᵐ x ∂xLaw M, c ≤ e.tauLev r x) :
      MemLp (G e) 2 (observationLaw M) := by
    simpa only [G, Bool.false_eq_true, ↓reduceIte] using fitted_fractional_policy_residual_memLp
      M phi dphi hphi hd hDerivative L e he c hc hcl k j (j-1) hk false
  have h0 (n : ℕ) (a : A) : ∀ r, ∀ᵐ x ∂xLaw M, c ≤ e0.tauLev r x :=
    fun r => (hclip (2*(n+1)) a r).mono (fun _ hx => hx.1)
  have hH (n : ℕ) (a : A) : ∀ r, ∀ᵐ x ∂xLaw M, c ≤ (eh (2*(n+1)) a).tauLev r x :=
    fun r => (hclip (2*(n+1)) a r).mono (fun _ hx => hx.2)
  have hrF := nuisanceRates_fractional_policy_residual_sq_tendsto_probability_zero
    M μ phi dphi hphi hd hDerivative L e0 eh he0 heh c hc hclip
    hrp hrlev hrP hrt hrs k j j hk true sep hsep hgap
  have hrG := nuisanceRates_fractional_policy_residual_sq_tendsto_probability_zero
    M μ phi dphi hphi hd hDerivative L e0 eh he0 heh c hc hclip
    hrp hrlev hrP hrt hrs k j (j-1) hk false sep hsep hgap
  have hz : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun (_ : ℕ) (_ : A) => (0 : ℝ)) atTop (fun _ _ => 0) := by
    rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm]
    intro eps heps
    simpa only [sub_self, norm_zero, not_le.mpr heps, Set.ofPred_false,
      measure_empty] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (𝓝 0))
  have hs := dml_three_term_sq_tendsto_probability_zero μ (observationLaw M)
    (fun n a o => F (eh (2*(n+1)) a) o - F e0 o)
    (fun _ _ _ => (0 : ℝ))
    (fun n a o => G (eh (2*(n+1)) a) o - G e0 o)
    (fun n a => (hF _ (heh _ a) (hH n a)).sub (hF e0 he0 (h0 n a)))
    (fun _ _ => MemLp.zero')
    (fun n a => (hG _ (heh _ a) (hH n a)).sub (hG e0 he0 (h0 n a)))
    (by simpa only [F, ↓reduceIte] using hrF)
    (by simpa only [zero_pow (by norm_num : 2 ≠ 0), integral_zero] using hz)
    (by simpa only [G, Bool.false_eq_true, ↓reduceIte] using hrG)
  have hid (n : ℕ) (a : A) (o : Obs X Z) :
      binaryRegularPolicyCorrection phi dphi L (eh (2*(n+1)) a) k j o -
        binaryRegularPolicyCorrection phi dphi L e0 k j o =
      F (eh (2*(n+1)) a) o - F e0 o + 0 - (G (eh (2*(n+1)) a) o - G e0 o) := by
    dsimp only [binaryRegularPolicyCorrection, F, G]
    ring
  simpa only [hid] using hs
-- All finite policy-correction terms are retained, including j=1.
-- @node: nuisanceRates_regular_policy_block_sq_tendsto_probability_zero
/-- Assume [a valid policy map](hyp:hphi), [policy differentiability](hyp:hd), [a bounded Lipschitz derivative](hyp:hDerivative), [an admissible reference nuisance](hyp:he0), [admissible fitted nuisances](hyp:heh), [a positive clipping constant](hyp:hc), and [reference and fitted policy denominators almost surely bounded below by it](hyp:hclip). If the fitted [propensities](hyp:hrp), [treatment levels](hyp:hrlev), [treated-outcome probabilities](hyp:hrP), [policy denominators](hyp:hrt), and [within-band shares](hyp:hrs) satisfy the finite componentwise nuisance rates, [the separation constant is positive](hyp:hsep), and [every regular reference band has width and distances from the full-interval threshold to both endpoints almost surely at least that separation](hyp:hgap), then [the integrated squared error of the sum of all regular policy corrections converges to zero in probability along sample sizes twice the iteration index plus two](goal). -/
lemma nuisanceRates_regular_policy_block_sq_tendsto_probability_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e0 : NuisanceBin L) (eh : ℕ → A → NuisanceBin L)
    (he0 : BinAdmissible M L e0) (heh : ∀ n a, BinAdmissible M L (eh n a))
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a (r : RegularIndex L), ∀ᵐ x ∂xLaw M,
      c ≤ e0.tauLev r x ∧ c ≤ (eh n a).tauLev r x)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) e0.prop)
    (hrlev : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrP : FiniteNuisanceRates M μ (fun n a => (eh n a).P1) e0.P1)
    (hrt : FiniteNuisanceRates M μ (fun n a => (eh n a).tauLev) e0.tauLev)
    (hrs : ∀ r : RegularIndex L,
      FiniteNuisanceRates M μ (fun n a => (eh n a).share r) (e0.share r))
    (sep : ℝ) (hsep : 0 < sep)
    (hgap : ∀ k, k < L.K → ∀ j, 1 ≤ j ∧ j ≤ L.l k → ∀ᵐ x ∂xLaw M,
      sep ≤ pooledQBin phi L e0 k j x - pooledQBin phi L e0 k (j-1) x ∧
      sep ≤ |positiveValue e0.pLev (k+1) x - binFullJ L e0 k x -
        pooledQBin phi L e0 k (j-1) x| ∧
      sep ≤ |positiveValue e0.pLev (k+1) x - binFullJ L e0 k x -
        pooledQBin phi L e0 k j x|) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o : Obs X Z,
        ((∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
          binaryRegularPolicyCorrection phi dphi L (eh (2*(n+1)) a) k j o) -
          ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
          binaryRegularPolicyCorrection phi dphi L e0 k j o)^2 ∂observationLaw M)
      atTop (fun _ _ => 0) := by
  let F := fun (k j n : ℕ) (a : A) (o : Obs X Z) =>
    binaryRegularPolicyCorrection phi dphi L (eh (2*(n+1)) a) k j o -
      binaryRegularPolicyCorrection phi dphi L e0 k j o
  have hF (k j n : ℕ) (a : A) (hk : k < L.K) :
      MemLp (F k j n a) 2 (observationLaw M) :=
    (fitted_regular_policy_correction_memLp M phi dphi hphi hd hDerivative L _ (heh _ a)
      c hc (fun r => (hclip _ a r).mono (fun _ hx => hx.2)) k j hk.le).sub
      (fitted_regular_policy_correction_memLp M phi dphi hphi hd hDerivative L e0 he0
        c hc (fun r => (hclip (2*(n+1)) a r).mono (fun _ hx => hx.1)) k j hk.le)
  have hs := dml_finset_sum_sq_tendsto_probability_zero μ (observationLaw M)
    (Finset.range L.K) (fun k n a o => ∑ j ∈ Finset.Icc 1 (L.l k), F k j n a o)
    (fun k hk n a => memLp_finsetSum _
      (fun j _ => hF k j n a (Finset.mem_range.mp hk))) (by
      intro k hk
      apply dml_finset_sum_sq_tendsto_probability_zero μ (observationLaw M)
        (Finset.Icc 1 (L.l k)) (F k)
        (fun j _ n a => hF k j n a (Finset.mem_range.mp hk))
      intro j hj
      exact nuisanceRates_regular_policy_correction_sq_tendsto_probability_zero M μ
        phi dphi hphi hd hDerivative L e0 eh he0 heh c hc hclip
        hrp hrlev hrP hrt hrs k j (Finset.mem_range.mp hk).le sep hsep
        (hgap k (Finset.mem_range.mp hk) j (Finset.mem_Icc.mp hj)))
  simpa only [F, Finset.sum_sub_distrib] using hs

end Papers.TbsPrteOptimalTransport

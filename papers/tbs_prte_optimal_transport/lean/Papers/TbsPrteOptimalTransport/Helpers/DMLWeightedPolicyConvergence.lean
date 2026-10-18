module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLActivePolicyConvergence
public import Papers.TbsPrteOptimalTransport.Helpers.DMLWeightedRegularRegressionConvergence
/-! Convergence of the gamma-weighted active policy corrections. The derivative
and overlap bounds control the residual, and the original gamma nuisance rate
controls the fitted product weight. -/
public section
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

-- @node: fitted_regular_policy_correction_aestronglyMeasurable
/-- If [the policy is a policy map](hyp:hphi), [its derivative is
dphi](hyp:hd), [that derivative is bounded and Lipschitz on the unit
interval](hyp:hDerivative), [the fitted binary nuisance specification is
admissible](hyp:he), and [k is at most the highest level](hyp:hk), then [the
fitted regular policy correction at k and j is strongly measurable up to an
observation-law null set](goal). -/
@[fun_prop] lemma fitted_regular_policy_correction_aestronglyMeasurable
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e : NuisanceBin L) (he : BinAdmissible M L e)
    (k j : ℕ) (hk : k ≤ L.K) :
    AEStronglyMeasurable (binaryRegularPolicyCorrection phi dphi L e k j)
      (observationLaw M) := by
  first | fun_prop | skip
  have hq (i : ℕ) : AEStronglyMeasurable (RqBin dphi L e k i) (observationLaw M) := by
    first | fun_prop | skip
    unfold RqBin
    split_ifs with hi
    · fun_prop
    · have hr : k ≤ L.K ∧ 1 ≤ i ∧ i ≤ L.l k := ⟨hk, by omega, by omega⟩
      simp only [regularValue, dif_pos hr]
      have hm : Measurable (fun o : Obs X Z => (e.tauLev ⟨(k,i), hr⟩ o.1)⁻¹) := by
        have ht := (he.2.2.2.2.2.1 ⟨(k,i), hr⟩).1
        fun_prop
      exact hm.aestronglyMeasurable.mul
        (fitted_RqBin_numerator_memLp M phi dphi hphi hd hDerivative L e he k i).1
  obtain ⟨hI, hD, hE⟩ := fitted_fractional_branches_memLp M phi hphi L e he k j
  have hmp := observationLaw_fst_measurePreserving M
  have hi := (hI.comp_measurePreserving hmp).1
  have he := (hE.comp_measurePreserving hmp).1
  exact (hi.mul (hq j)).sub ((he.mul hi).mul (hq (j-1)))

-- @node: fitted_regular_policy_correction_abs_bound
/-- If [B is nonnegative](hyp:hB), [the policy derivative is bounded in absolute
value by B on the unit interval](hyp:hb), [the fitted binary nuisance
specification is admissible](hyp:he), [c is positive](hyp:hc), [every fitted
regular treatment mass is at least c almost everywhere](hyp:hclip), and [k is at
most the highest level](hyp:hk), then [the fitted regular policy correction has
absolute value at most B/c times the sum of the instrument-set cardinalities at
boundaries j and j minus one, almost surely under the observation law](goal). -/
lemma fitted_regular_policy_correction_abs_bound
    (phi dphi : Z → X → ℝ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ z x p, p ∈ Icc (0 : ℝ) 1 → |dphi z x p| ≤ B)
    (L : LevelData Z X) (e : NuisanceBin L) (he : BinAdmissible M L e)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ r : RegularIndex L, ∀ᵐ x ∂xLaw M, c ≤ e.tauLev r x)
    (k j : ℕ) (hk : k ≤ L.K) :
    ∀ᵐ o ∂observationLaw M, |binaryRegularPolicyCorrection phi dphi L e k j o| ≤
      ((L.T k j).card + (L.T k (j-1)).card) * B / c := by
  filter_upwards [fitted_RqBin_abs_bound M dphi B hB hb L e he c hc hclip k j hk,
    fitted_RqBin_abs_bound M dphi B hB hb L e he c hc hclip k (j-1) hk] with o ht hb'
  have hi : |Iact phi L e k j o.1| ≤ 1 := by
    unfold Iact indicator
    split_ifs <;> norm_num
  have hei : |Edom phi L e k j o.1 * Iact phi L e k j o.1| ≤ 1 := by
    unfold Edom Iact indicator
    split_ifs <;> norm_num
  unfold binaryRegularPolicyCorrection
  calc
    _ ≤ |Iact phi L e k j o.1 * RqBin dphi L e k j o| +
        |Edom phi L e k j o.1 * Iact phi L e k j o.1 * RqBin dphi L e k (j-1) o| :=
      abs_sub _ _
    _ ≤ (L.T k j).card * B / c + (L.T k (j-1)).card * B / c := by
      rw [abs_mul, abs_mul]
      exact add_le_add
        ((mul_le_mul hi ht (abs_nonneg _) zero_le_one).trans_eq (one_mul _))
        ((mul_le_mul hei hb' (abs_nonneg _) zero_le_one).trans_eq (one_mul _))
    _ = _ := by ring

-- @node: fitted_weighted_regular_policy_correction_memLp
/-- If [the policy is a policy map](hyp:hphi), [dphi is its derivative](hyp:hd),
[the derivative is bounded and Lipschitz on the unit interval](hyp:hDerivative),
[the fitted binary nuisance specification is admissible](hyp:he), [c is
positive](hyp:hc), [all fitted regular treatment masses are at least c almost
everywhere](hyp:hclip), and [k is at most the highest level](hyp:hk), then [the
fitted regular policy correction multiplied by its fitted gamma weight is square
integrable under the observation law](goal). -/
lemma fitted_weighted_regular_policy_correction_memLp
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e : NuisanceBin L) (he : BinAdmissible M L e)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ r : RegularIndex L, ∀ᵐ x ∂xLaw M, c ≤ e.tauLev r x)
    (k j : ℕ) (hk : k ≤ L.K) :
    MemLp (fun o : Obs X Z => regularValue e.gamma k j o.1 *
      binaryRegularPolicyCorrection phi dphi L e k j o) 2 (observationLaw M) := by
  have hg := (fitted_regular_gamma_memLp M L e he k j).comp_measurePreserving
    (observationLaw_fst_measurePreserving M)
  have hr := fitted_regular_policy_correction_memLp M phi dphi hphi hd hDerivative
    L e he c hc hclip k j hk
  apply hr.norm.mono' (by first | fun_prop | exact hg.1.mul hr.1)
  filter_upwards [observationLaw_covariate_ae M _
    (fitted_regular_gamma_abs_bound M L e he k j)] with o ho
  rw [norm_mul, Real.norm_eq_abs (regularValue e.gamma k j o.1)]
  exact mul_le_of_le_one_left (norm_nonneg _) ho

-- @node: nuisanceRates_weighted_regular_policy_correction_sq_tendsto_probability_zero
/-- Suppose [the policy is a policy map](hyp:hphi), [dphi is its
derivative](hyp:hd), [the derivative is bounded and Lipschitz on the unit
interval](hyp:hDerivative), [the reference nuisance specification is
admissible](hyp:he0), and [every fitted nuisance specification is
admissible](hyp:heh). If [c is positive](hyp:hc), [reference and fitted regular
treatment masses are at least c almost everywhere](hyp:hclip), the fitted
[propensities](hyp:hrp), [level treatment probabilities](hyp:hrlev), [binary
outcome regressions](hyp:hrP), [regular treatment masses](hyp:hrt), [shares at
every regular index](hyp:hrs), and [gamma weights](hyp:hrg) satisfy the finite
nuisance rate conditions, [k is below the highest level](hyp:hk), [j is a valid
positive boundary at k](hyp:hj), [sep is positive](hyp:hsep), and [the reference
adjacent pooled policy values and the distances of the residual treatment mass
from both values are at least sep almost everywhere](hyp:hgap), then [the
observation-law integrated squared difference between fitted and reference
gamma-weighted regular policy corrections, using fits at sample size twice
n plus two, converges to zero in probability](goal). -/
lemma nuisanceRates_weighted_regular_policy_correction_sq_tendsto_probability_zero
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
    (hrg : FiniteNuisanceRates M μ (fun n a => (eh n a).gamma) e0.gamma)
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k)
    (sep : ℝ) (hsep : 0 < sep)
    (hgap : ∀ᵐ x ∂xLaw M,
      sep ≤ pooledQBin phi L e0 k j x - pooledQBin phi L e0 k (j-1) x ∧
      sep ≤ |positiveValue e0.pLev (k+1) x - binFullJ L e0 k x -
        pooledQBin phi L e0 k (j-1) x| ∧
      sep ≤ |positiveValue e0.pLev (k+1) x - binFullJ L e0 k x -
        pooledQBin phi L e0 k j x|) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o : Obs X Z,
        (regularValue (eh (2*(n+1)) a).gamma k j o.1 *
            binaryRegularPolicyCorrection phi dphi L (eh (2*(n+1)) a) k j o -
          regularValue e0.gamma k j o.1 *
            binaryRegularPolicyCorrection phi dphi L e0 k j o)^2 ∂observationLaw M)
      atTop (fun _ _ => 0) := by
  obtain ⟨B, D, hB, hD, hb⟩ := hDerivative
  have hDerivative : PolicyDerivativeBoundedLipschitz dphi := ⟨B, D, hB, hD, hb⟩
  let r : RegularIndex L := ⟨(k,j), hk.le, hj⟩
  have hg (e : NuisanceBin L) : regularValue e.gamma k j = e.gamma r := by
    funext x
    simp only [regularValue, dif_pos r.property, r]
  have hmp := observationLaw_fst_measurePreserving M
  have hw (e : NuisanceBin L) (he : BinAdmissible M L e) :=
    (fitted_regular_gamma_memLp M L e he k j).comp_measurePreserving hmp
  have hR (e : NuisanceBin L) (he : BinAdmissible M L e)
      (ht : ∀ r, ∀ᵐ x ∂xLaw M, c ≤ e.tauLev r x) :=
    fitted_regular_policy_correction_memLp M phi dphi hphi hd hDerivative L e he c hc ht k j hk.le
  have hRm : AEStronglyMeasurable (binaryRegularPolicyCorrection phi dphi L e0 k j)
      (observationLaw M) := by
    first | fun_prop | exact (fitted_regular_policy_correction_aestronglyMeasurable
      M phi dphi hphi hd hDerivative L e0 he0 k j hk.le)
  apply dml_ae_weighted_residual_sq_tendsto_probability_zero μ (observationLaw M)
    (fun o => regularValue e0.gamma k j o.1) (binaryRegularPolicyCorrection phi dphi L e0 k j)
    (fun n a o => regularValue (eh (2*(n+1)) a).gamma k j o.1)
    (fun n a => binaryRegularPolicyCorrection phi dphi L (eh (2*(n+1)) a) k j)
    1 (((L.T k j).card + (L.T k (j-1)).card) * B / c)
    (hw e0 he0).1 hRm (fun n a => (hw _ (heh _ a)).1)
    (fun n a => (hR _ (heh _ a) (fun r => (hclip _ a r).mono (fun _ hx => hx.2))).1)
  · exact fun n a => (hw _ (heh _ a)).sub (hw e0 he0)
  · intro n a
    exact (hR _ (heh _ a) (fun r => (hclip _ a r).mono (fun _ hx => hx.2))).sub
      (hR e0 he0 (fun r => (hclip (2*(n+1)) a r).mono (fun _ hx => hx.1)))
  · exact fun n a => observationLaw_covariate_ae M _
      (fitted_regular_gamma_abs_bound M L _ (heh _ a) k j)
  · exact fun n a => fitted_regular_policy_correction_abs_bound M phi dphi B hB
      (fun z x p hp => (hb z x p p hp hp).1) L e0 he0 c hc
      (fun r => (hclip n a r).mono (fun _ hx => hx.1)) k j hk.le
  · simpa only [hg] using nuisanceRates_covariate_sq_tendsto_probability_zero M μ e0.gamma
      (fun n a => (eh n a).gamma) (fun i => (he0.2.2.2.2.2.1 i).2)
      (fun n a i => ((heh n a).2.2.2.2.2.1 i).2) hrg r
  · exact nuisanceRates_regular_policy_correction_sq_tendsto_probability_zero M μ
      phi dphi hphi hd hDerivative L e0 eh he0 heh c hc hclip
      hrp hrlev hrP hrt hrs k j hk.le sep hsep hgap

end Papers.TbsPrteOptimalTransport

module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLStructuralZeroFractionalRates
public import Papers.TbsPrteOptimalTransport.Helpers.DMLActivePolicyConvergence
public import Papers.TbsPrteOptimalTransport.Helpers.DMLFractionalTreatmentConvergence
/-! Binary branch energy on observation space and coefficient convergence.
The population bound includes the structural zero using outcome margins.
Coefficient convergence then follows from domination by that branch energy. -/
public section
set_option linter.style.openClassical false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: nuisanceRates_population_binary_branch_observation_sq_tendsto_probability_zero
/-- Assume [a valid policy map](hyp:hphi), [its specified derivative](hyp:hd),
[a bounded Lipschitz derivative](hyp:hDerivative), [the structural model
assumptions](hyp:hStruct), [known outcome endpoints](hyp:hend), [finite
instrument reduction](hyp:hf), [binary outcomes almost surely](hyp:hy),
[policy-invariant level ordering](hyp:hOrder), [policy levels off the
boundary](hyp:hOff), [separated baseline and policy propensity gaps](hyp:hGap),
[policy overlap](hyp:hpol), [a discrete outcome gap](hyp:hOutcome), [admissible
population nuisances](hyp:he0), and [admissible fitted nuisances](hyp:heh).
If [instrument propensities satisfy quarter-rate control](hyp:hrp),
[level propensities satisfy quarter-rate control](hyp:hrlev),
[success regressions satisfy quarter-rate control](hyp:hrP), and [all regular
cell instrument shares satisfy quarter-rate control](hyp:hrs), then for [a level below the level count](hyp:hk)
and [a valid positive policy-cell index](hyp:hj), [the observation-law integral
of the sum of squared errors in the active, boundary, and dominance branch
indicators converges to zero in probability along even sample sizes](goal). -/
lemma nuisanceRates_population_binary_branch_observation_sq_tendsto_probability_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (hStruct : StructuralAssumptions M) (hend : OutcomeEndpointsKnown M)
    (hf : InstrumentFiniteReduction Z) (hy : OutcomeBinaryAE M)
    (L : LevelData Z X) (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (hOff : PolicyLevelOffBoundary L) (gap : ℝ)
    (hGap : PropensityGapSeparationWitness M.prop (policyProp phi M.prop) gap)
    (cpi : ℝ) (hpol : PolicyOverlap M L cpi) (ch : ℝ)
    (hOutcome : DiscreteOutcomeGapWitness M L ch)
    (eh : ℕ → A → NuisanceBin L)
    (he0 : BinAdmissible M L (eta0Bin M L)) (heh : ∀ n a, BinAdmissible M L (eh n a))
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) (eta0Bin M L).prop)
    (hrlev : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) (eta0Bin M L).pLev)
    (hrP : FiniteNuisanceRates M μ (fun n a => (eh n a).P1) (eta0Bin M L).P1)
    (hrs : ∀ a : RegularIndex L,
      FiniteNuisanceRates M μ (fun n t => (eh n t).share a) ((eta0Bin M L).share a))
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o : Obs X Z,
        (Iact phi L (eh (2*(n+1)) a) k j o.1 - Iact phi L (eta0Bin M L) k j o.1)^2 +
        (Dbd phi L (eh (2*(n+1)) a) k j o.1 - Dbd phi L (eta0Bin M L) k j o.1)^2 +
        (Edom phi L (eh (2*(n+1)) a) k j o.1 - Edom phi L (eta0Bin M L) k j o.1)^2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  have hr := nuisanceRates_population_binary_branch_energy_isLittleOp M μ
    phi dphi hphi hd hDerivative hStruct hend hf hy L hOrder hOff gap hGap
    cpi hpol ch hOutcome he0 eh heh hrp hrlev hrP hrs k j hk hj
  have hl := dml_half_rate_energy_l2_tendsto_probability_zero μ _
    (fun n a => integral_nonneg fun x =>
      add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)) hr
  have hc : Continuous (fun t : ℝ => t^2) := by fun_prop
  have hs := Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt
    hc.continuousAt hl
  simp only [Real.sq_sqrt (integral_nonneg fun x =>
    add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)),
    zero_pow (by norm_num : 2 ≠ 0)] at hs
  have heq (n : ℕ) (a : A) :
      (∫ o : Obs X Z,
        (Iact phi L (eh (2*(n+1)) a) k j o.1 - Iact phi L (eta0Bin M L) k j o.1)^2 +
        (Dbd phi L (eh (2*(n+1)) a) k j o.1 - Dbd phi L (eta0Bin M L) k j o.1)^2 +
        (Edom phi L (eh (2*(n+1)) a) k j o.1 - Edom phi L (eta0Bin M L) k j o.1)^2
        ∂observationLaw M) =
      ∫ x,
        (Iact phi L (eh (2*(n+1)) a) k j x - Iact phi L (eta0Bin M L) k j x)^2 +
        (Dbd phi L (eh (2*(n+1)) a) k j x - Dbd phi L (eta0Bin M L) k j x)^2 +
        (Edom phi L (eh (2*(n+1)) a) k j x - Edom phi L (eta0Bin M L) k j x)^2 ∂xLaw M := by
    obtain ⟨hi, hd, he⟩ := fitted_fractional_branches_memLp M phi hphi L (eta0Bin M L) he0 k j
    obtain ⟨hi', hd', he'⟩ := fitted_fractional_branches_memLp M phi hphi L _ (heh _ a) k j
    have hm := (((hi'.sub hi).1.pow 2).add ((hd'.sub hd).1.pow 2)).add
      ((he'.sub he).1.pow 2)
    have hmp := observationLaw_fst_measurePreserving M
    rw [← hmp.map_eq]
    exact (integral_map hmp.aemeasurable (by rw [hmp.map_eq]; exact hm)).symm
  simpa only [heq] using hs

-- @node: nuisanceRates_fractional_treatment_coefficient_sq_tendsto_probability_zero_of_branch_convergence
/-- For [a valid policy map](hyp:hphi) with [the specified derivative](hyp:hd)
and [a bounded Lipschitz derivative](hyp:hDerivative), assume [admissible
reference nuisances](hyp:he0), [admissible fitted nuisances](hyp:heh), and
[quarter-rate control of instrument propensities](hyp:hrp),
[quarter-rate control of level propensities](hyp:hrlev),
[quarter-rate control of success regressions](hyp:hrP), and
[quarter-rate control of all regular cell shares](hyp:hrs). If [the integrated sum of squared active, boundary,
and dominance indicator errors vanishes in probability](hyp:hbranch), [the
integrated squared error of the fractional treatment coefficient vanishes in
probability along even sample sizes, whether the coefficient is the boundary
indicator or the product of dominance and active indicators](goal). -/
lemma nuisanceRates_fractional_treatment_coefficient_sq_tendsto_probability_zero_of_branch_convergence
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
    (hbranch : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o : Obs X Z,
        (Iact phi L (eh (2*(n+1)) a) k j o.1 - Iact phi L e0 k j o.1)^2 +
        (Dbd phi L (eh (2*(n+1)) a) k j o.1 - Dbd phi L e0 k j o.1)^2 +
        (Edom phi L (eh (2*(n+1)) a) k j o.1 - Edom phi L e0 k j o.1)^2
        ∂observationLaw M) atTop (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o : Obs X Z,
        ((if b then Dbd phi L (eh (2*(n+1)) a) k j o.1 else
            Edom phi L (eh (2*(n+1)) a) k j o.1 * Iact phi L (eh (2*(n+1)) a) k j o.1) -
          (if b then Dbd phi L e0 k j o.1 else
            Edom phi L e0 k j o.1 * Iact phi L e0 k j o.1))^2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  have hr := hbranch
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

-- @node: nuisanceRates_fractional_policy_coefficient_sq_tendsto_probability_zero_of_branch_convergence
/-- Assume [a valid policy map](hyp:hphi), [its specified derivative](hyp:hd),
[a bounded Lipschitz derivative](hyp:hDerivative), [admissible reference
nuisances](hyp:he0), [admissible fitted nuisances](hyp:heh),
[quarter-rate control of instrument propensities](hyp:hrp),
[quarter-rate control of level propensities](hyp:hrlev),
[quarter-rate control of success regressions](hyp:hrP), and
[quarter-rate control of all regular cell shares](hyp:hrs). If [the integrated sum of squared errors of the three branch
indicators tends to zero in probability](hyp:hbranch), [the fractional policy
coefficient has integrated squared error tending to zero in probability along
even sample sizes, both for the active indicator and for its product with the
dominance indicator](goal). -/
lemma nuisanceRates_fractional_policy_coefficient_sq_tendsto_probability_zero_of_branch_convergence
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
    (hbranch : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o : Obs X Z,
        (Iact phi L (eh (2*(n+1)) a) k j o.1 - Iact phi L e0 k j o.1)^2 +
        (Dbd phi L (eh (2*(n+1)) a) k j o.1 - Dbd phi L e0 k j o.1)^2 +
        (Edom phi L (eh (2*(n+1)) a) k j o.1 - Edom phi L e0 k j o.1)^2
        ∂observationLaw M) atTop (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o : Obs X Z,
        ((if b then Iact phi L (eh (2*(n+1)) a) k j o.1 else
            Edom phi L (eh (2*(n+1)) a) k j o.1 * Iact phi L (eh (2*(n+1)) a) k j o.1) -
          (if b then Iact phi L e0 k j o.1 else
            Edom phi L e0 k j o.1 * Iact phi L e0 k j o.1))^2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  have hr := hbranch
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

-- @node: nuisanceRates_Dbd_RP_sq_tendsto_probability_zero_of_branch_convergence
/-- Under [a valid policy map](hyp:hphi), [its specified derivative](hyp:hd),
[a bounded Lipschitz derivative](hyp:hDerivative), [admissible reference
nuisances](hyp:he0), [admissible fitted nuisances](hyp:heh), and [binary
outcomes almost surely](hyp:hy), suppose [the denominator bound is positive](hyp:hc)
and [reference and fitted assignment probabilities exceed it almost
everywhere](hyp:hclip). With [quarter-rate control of instrument
propensities](hyp:hrp), [quarter-rate control of level propensities](hyp:hrlev),
[quarter-rate control of success regressions](hyp:hrP),
[quarter-rate control of assignment probabilities](hyp:hrpi),
[quarter-rate control of all regular cell shares](hyp:hrs),
[a residual index no larger than the level count](hyp:hi),
and [vanishing integrated squared error of the three branch indicators in
probability](hyp:hbranch), [the product of the boundary indicator and the
inverse-weighted success residual has integrated squared error tending to zero
in probability along even sample sizes](goal). -/
lemma nuisanceRates_Dbd_RP_sq_tendsto_probability_zero_of_branch_convergence
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
    (k j i : ℕ) (hi : i ≤ L.K) (hbranch : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o : Obs X Z,
        (Iact phi L (eh (2*(n+1)) a) k j o.1 - Iact phi L e0 k j o.1)^2 +
        (Dbd phi L (eh (2*(n+1)) a) k j o.1 - Dbd phi L e0 k j o.1)^2 +
        (Edom phi L (eh (2*(n+1)) a) k j o.1 - Edom phi L e0 k j o.1)^2
        ∂observationLaw M) atTop (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o,
        (Dbd phi L (eh (2*(n+1)) a) k j o.1 * RP L (eh (2*(n+1)) a) i o -
          Dbd phi L e0 k j o.1 * RP L e0 i o)^2 ∂observationLaw M)
      atTop (fun _ _ => 0) := by
  have hmp := observationLaw_fst_measurePreserving M
  have hD (e : NuisanceBin L) (he : BinAdmissible M L e) :=
    ((fitted_fractional_branches_memLp M phi hphi L e he k j).2.1).comp_measurePreserving hmp
  have hr := hbranch
  have hrD : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o : Obs X Z,
        (Dbd phi L (eh (2*(n+1)) a) k j o.1 - Dbd phi L e0 k j o.1)^2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
    apply probability_zero_of_nonneg_le μ _ _ hr
    intro n
    apply Eventually.of_forall
    intro a
    refine ⟨integral_nonneg (fun o => sq_nonneg _), ?_⟩
    have h0 := fitted_fractional_branches_memLp M phi hphi L e0 he0 k j
    have hh := fitted_fractional_branches_memLp M phi hphi L _ (heh (2*(n+1)) a) k j
    have hI := ((hh.1.sub h0.1).comp_measurePreserving hmp).integrable_sq
    have hD' := ((hh.2.1.sub h0.2.1).comp_measurePreserving hmp).integrable_sq
    have hE := ((hh.2.2.sub h0.2.2).comp_measurePreserving hmp).integrable_sq
    apply integral_mono hD' ((hI.add hD').add hE)
    intro o
    dsimp only [Pi.sub_apply, Pi.add_apply, Function.comp_apply]
    linarith [sq_nonneg (Iact phi L (eh (2*(n+1)) a) k j o.1 - Iact phi L e0 k j o.1),
      sq_nonneg (Edom phi L (eh (2*(n+1)) a) k j o.1 - Edom phi L e0 k j o.1)]
  apply dml_ae_weighted_residual_sq_tendsto_probability_zero μ (observationLaw M)
    (fun o => Dbd phi L e0 k j o.1) (RP L e0 i)
    (fun n a o => Dbd phi L (eh (2*(n+1)) a) k j o.1)
    (fun n a => RP L (eh (2*(n+1)) a) i) 1 (1/c)
    (hD e0 he0).1 (by fun_prop) (fun n a => (hD _ (heh _ a)).1)
    (by intro n a; first | fun_prop | exact (fitted_RP_measurable M L _ (heh _ a) i).aestronglyMeasurable)
  · exact fun n a => (hD _ (heh _ a)).sub (hD e0 he0)
  · intro n a
    exact (fitted_RP_memLp M L _ (heh _ a) hy c hc
      (fun t => (hclip _ a t).mono (fun _ hx => hx.2)) i hi).sub
      (fitted_RP_memLp M L e0 he0 hy c hc
        (fun t => (hclip (2*(n+1)) a t).mono (fun _ hx => hx.1)) i hi)
  · intro n a
    exact Eventually.of_forall (fun o => by unfold Dbd indicator; split_ifs <;> norm_num)
  · exact fun n a => fitted_RP_abs_bound M L e0 he0 hy c hc
      (fun t => (hclip n a t).mono (fun _ hx => hx.1)) i hi
  · exact hrD
  · exact nuisanceRates_RP_sq_tendsto_probability_zero M μ L e0 eh he0 heh
      hy c hc hclip hrP hrpi i hi

end Papers.TbsPrteOptimalTransport

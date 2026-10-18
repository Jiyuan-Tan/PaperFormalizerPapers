module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLStructuralZeroBranchRates
public import Papers.TbsPrteOptimalTransport.Helpers.DMLFractionalBranchRates
public import Papers.TbsPrteOptimalTransport.Helpers.StructuralZeroPopulation
/-! Nuisance-rate control of the binary score branches at the structural zero.
The lower affine argument stays exactly zero. Outcome margins suffice without
uniform separation of the first policy level from zero. -/
public section
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.openClassical false
set_option linter.unusedSectionVars false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

-- @node: binary_structural_zero_branch_memLp_component_energy_bound
/-- If [the margin is positive](hyp:hc), [the true policy argument and upper boundary
have finite second moments](hyp:hq,hb), [their fitted counterparts have finite second
moments](hyp:hqh,hbh), and [almost everywhere the true upper boundary and its distance
from the policy argument are at least the margin](hyp:hgap), then [the sum of squared
branch-indicator errors at the fixed zero lower argument is integrable, and its
integral is at most thirty-six divided by the squared margin times the sum of the
policy-argument and boundary squared-error integrals](goal). -/
lemma binary_structural_zero_branch_memLp_component_energy_bound
    {B : Type*} [MeasurableSpace B] (ν : Measure B)
    (q b qh bh : B → ℝ) (c : ℝ) (hc : 0 < c)
    (hq : MemLp q 2 ν) (hb : MemLp b 2 ν)
    (hqh : MemLp qh 2 ν) (hbh : MemLp bh 2 ν)
    (hgap : ∀ᵐ x ∂ν, c ≤ b x ∧ c ≤ |b x - q x|) :
    Integrable (fun x => binaryBranchSqError (q x) 0 (b x) (qh x) 0 (bh x)) ν ∧
      (∫ x, binaryBranchSqError (q x) 0 (b x) (qh x) 0 (bh x) ∂ν) ≤
        (36 / c ^ 2) * ((∫ x, (qh x - q x)^2 ∂ν) + ∫ x, (bh x - b x)^2 ∂ν) := by
  let Q := hq.1.mk q
  let B := hb.1.mk b
  let Qh := hqh.1.mk qh
  let Bh := hbh.1.mk bh
  have eqQ : q =ᵐ[ν] Q := hq.1.ae_eq_mk
  have eqB : b =ᵐ[ν] B := hb.1.ae_eq_mk
  have eqQh : qh =ᵐ[ν] Qh := hqh.1.ae_eq_mk
  have eqBh : bh =ᵐ[ν] Bh := hbh.1.ae_eq_mk
  have hg : ∀ᵐ x ∂ν, c ≤ B x ∧ c ≤ |B x - Q x| := by
    filter_upwards [hgap, eqQ, eqB] with x hx hqx hbx
    simpa only [← hqx, ← hbx] using hx
  have heq : (fun x => binaryBranchSqError (q x) 0 (b x) (qh x) 0 (bh x))
      =ᵐ[ν] (fun x => binaryBranchSqError (Q x) 0 (B x) (Qh x) 0 (Bh x)) := by
    filter_upwards [eqQ, eqB, eqQh, eqBh] with x h1 h2 h3 h4
    rw [h1, h2, h3, h4]
  obtain ⟨hi, ht⟩ := binary_structural_zero_branch_component_energy_bound ν Q B Qh Bh c hc
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    ((hqh.ae_eq eqQh).sub (hq.ae_eq eqQ))
    ((hbh.ae_eq eqBh).sub (hb.ae_eq eqB)) hg
  refine ⟨hi.congr heq.symm, ?_⟩
  rw [integral_congr_ae heq]
  have eQ : (∫ x, (Qh x - Q x)^2 ∂ν) = ∫ x, (qh x - q x)^2 ∂ν := by
    apply integral_congr_ae
    filter_upwards [eqQ, eqQh] with x h1 h2
    rw [h1, h2]
  have eB : (∫ x, (Bh x - B x)^2 ∂ν) = ∫ x, (bh x - b x)^2 ∂ν := by
    apply integral_congr_ae
    filter_upwards [eqB, eqBh] with x h1 h2
    rw [h1, h2]
  simpa only [eQ, eB] using ht

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: nuisanceRates_structural_zero_fractional_branch_energy_isLittleOp
/-- Suppose [the policy map is valid](hyp:hphi), [its specified derivative is correct](hyp:hd),
[that derivative is bounded and Lipschitz](hyp:hDerivative), [the reference binary
nuisances are admissible](hyp:he0), and [all fitted binary nuisances are admissible](hyp:heh).
If [propensity errors satisfy the finite nuisance rate conditions](hyp:hrp), [level
errors satisfy those conditions](hyp:hrlev), [binary success-probability errors satisfy
them](hyp:hrP), [instrument-share errors satisfy them for every regular component](hyp:hrs),
[the margin is positive](hyp:hc), and [the reference first-level success-adjusted
boundary and its distance from the first pooled policy argument are bounded below
by that margin almost everywhere](hyp:hgap), then [the integrated sum of squared
activity, interior-boundary, and dominance indicator errors for the first fractional
component is of smaller order in probability than the inverse square root of the
training size, with training size twice the evaluation size](goal). -/
lemma nuisanceRates_structural_zero_fractional_branch_energy_isLittleOp
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
    (c : ℝ) (hc : 0 < c)
    (hgap : ∀ᵐ x ∂xLaw M,
      c ≤ positiveValue e0.pLev 1 x - binFullJ L e0 0 x ∧
      c ≤ |positiveValue e0.pLev 1 x - binFullJ L e0 0 x - pooledQBin phi L e0 0 1 x|) :
    Causalean.Stat.IsLittleOp
      (fun n a => ∫ x,
        (Iact phi L (eh (2*(n+1)) a) 0 1 x - Iact phi L e0 0 1 x)^2 +
        (Dbd phi L (eh (2*(n+1)) a) 0 1 x - Dbd phi L e0 0 1 x)^2 +
        (Edom phi L (eh (2*(n+1)) a) 0 1 x - Edom phi L e0 0 1 x)^2 ∂xLaw M)
      (fun n => ((2*(n+1) : ℕ) : ℝ)^(-1/2 : ℝ)) μ := by
  obtain ⟨B, Lip, hB, hLip, hder⟩ := hDerivative
  have hlip := policy_lipschitz_of_derivative_bound phi dphi hd B
    (fun z x p hp => (hder z x p p hp hp).1)
  have hpool := nuisanceRates_pooledQBin_quarter_rate M μ phi hphi B hB hlip
    L e0 eh he0 heh hrp hrlev hrs
  have hb := nuisanceRates_binary_boundary_quarter_rate M μ L e0 eh he0 heh hrlev hrP
  have he := dml_three_component_energies_isLittleOp μ (xLaw M)
    (fun n a x => pooledQBin phi L (eh (2*(n+1)) a) 0 1 x - pooledQBin phi L e0 0 1 x)
    (fun n a x => pooledQBin phi L (eh (2*(n+1)) a) 0 0 x - pooledQBin phi L e0 0 0 x)
    (fun n a x => (positiveValue (eh (2*(n+1)) a).pLev 1 x -
      binFullJ L (eh (2*(n+1)) a) 0 x) -
      (positiveValue e0.pLev 1 x - binFullJ L e0 0 x))
    (hpool (0,1)) (hpool (0,0)) (hb 0)
  have hz (e : NuisanceBin L) (x : X) : pooledQBin phi L e 0 0 x = 0 := by
    simp [pooledQBin, positiveValue]
  simp only [hz, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    integral_zero, add_zero] at he
  apply Causalean.Stat.IsLittleOp.of_abs_le_const_mul (by positivity : 0 < 36 / c^2) he
  intro n a
  rw [abs_of_nonneg (integral_nonneg fun x =>
    add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _))]
  have boundary (e : NuisanceBin L) (he : BinAdmissible M L e) :
      MemLp (fun x => positiveValue e.pLev 1 x - binFullJ L e 0 x) 2 (xLaw M) :=
    ((fitted_positive_treatment_assignment_memLp M L e he 1).1).sub
      ((fitted_positive_success_memLp M L e he 1).sub
        (fitted_positive_success_memLp M L e he 0))
  have ht := (binary_structural_zero_branch_memLp_component_energy_bound (xLaw M)
    (pooledQBin phi L e0 0 1) (fun x => positiveValue e0.pLev 1 x - binFullJ L e0 0 x)
    (pooledQBin phi L (eh (2*(n+1)) a) 0 1)
    (fun x => positiveValue (eh (2*(n+1)) a).pLev 1 x - binFullJ L (eh (2*(n+1)) a) 0 x)
    c hc (fitted_pooledQBin_memLp M phi hphi L e0 he0 0 1) (boundary e0 he0)
    (fitted_pooledQBin_memLp M phi hphi L _ (heh _ a) 0 1)
    (boundary _ (heh _ a)) hgap).2
  simp only [binaryBranchSqError, Iact, Dbd, Edom, Nat.reduceSub, hz] at ht ⊢
  exact ht.trans (mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity))

-- @node: nuisanceRates_structural_zero_fractional_branch_l2_tendsto_probability_zero
/-- Suppose [the policy map is valid](hyp:hphi), [the policy is differentiable with
the specified derivative](hyp:hd), [the derivative is bounded and Lipschitz](hyp:hDerivative),
[the reference nuisances are admissible](hyp:he0), and [all fitted nuisances are
admissible](hyp:heh). If [propensity, positive-level, and binary success-probability
errors satisfy the finite nuisance rate conditions](hyp:hrp,hrlev,hrP), [all regular
instrument-share errors satisfy those conditions](hyp:hrs), [the margin is positive](hyp:hc), and [the
reference first-level success-adjusted boundary and its distance from the first
pooled policy argument are at least the margin almost everywhere](hyp:hgap), then [the
square root of the integrated sum of squared activity, interior-boundary, and
dominance indicator errors for the first fractional component converges to zero in
probability along training sizes twice the evaluation size](goal). -/
lemma nuisanceRates_structural_zero_fractional_branch_l2_tendsto_probability_zero
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
    (c : ℝ) (hc : 0 < c)
    (hgap : ∀ᵐ x ∂xLaw M,
      c ≤ positiveValue e0.pLev 1 x - binFullJ L e0 0 x ∧
      c ≤ |positiveValue e0.pLev 1 x - binFullJ L e0 0 x - pooledQBin phi L e0 0 1 x|) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt (∫ x,
        (Iact phi L (eh (2*(n+1)) a) 0 1 x - Iact phi L e0 0 1 x)^2 +
        (Dbd phi L (eh (2*(n+1)) a) 0 1 x - Dbd phi L e0 0 1 x)^2 +
        (Edom phi L (eh (2*(n+1)) a) 0 1 x - Edom phi L e0 0 1 x)^2 ∂xLaw M))
      atTop (fun _ _ => 0) := by
  apply dml_half_rate_energy_l2_tendsto_probability_zero
  · intro n a
    exact integral_nonneg fun x =>
      add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)
  · exact nuisanceRates_structural_zero_fractional_branch_energy_isLittleOp M μ
      phi dphi hphi hd hDerivative L e0 eh he0 heh hrp hrlev hrP hrs c hc hgap

-- @node: nuisanceRates_population_binary_branch_energy_isLittleOp
/-- Suppose [the policy map is valid](hyp:hphi), [its derivative is correct](hyp:hd),
[the derivative is bounded and Lipschitz](hyp:hDerivative), [the model satisfies the
structural assumptions](hyp:hStruct), [outcome endpoints are known](hyp:hend), [the
instrument admits finite reduction](hyp:hf), and [outcomes are binary almost surely](hyp:hy).
Assume [policy and baseline level orders agree](hyp:hOrder), [policy levels avoid
boundaries](hyp:hOff), [propensity gaps are uniformly separated](hyp:hGap), [policy
overlap holds](hyp:hpol), [discrete outcome gaps are uniformly separated](hyp:hOutcome),
[the population binary nuisances are admissible](hyp:he0), and [all fitted nuisances
are admissible](hyp:heh). If [propensity, level, and success-probability errors satisfy
the finite nuisance rate conditions](hyp:hrp,hrlev,hrP), [all regular instrument-share
errors satisfy those conditions](hyp:hrs), [the component's level is below the terminal level](hyp:hk),
and [its within-level index lies in the regular range](hyp:hj), then [its integrated
sum of squared activity, interior-boundary, and dominance indicator errors relative
to the population nuisances is of smaller order in probability than the inverse
square root of the training size, evaluated at training sizes twice the evaluation
size](goal). -/
lemma nuisanceRates_population_binary_branch_energy_isLittleOp
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
    (he0 : BinAdmissible M L (eta0Bin M L)) (eh : ℕ → A → NuisanceBin L)
    (heh : ∀ n a, BinAdmissible M L (eh n a))
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) (eta0Bin M L).prop)
    (hrlev : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) (eta0Bin M L).pLev)
    (hrP : FiniteNuisanceRates M μ (fun n a => (eh n a).P1) (eta0Bin M L).P1)
    (hrs : ∀ a : RegularIndex L,
      FiniteNuisanceRates M μ (fun n t => (eh n t).share a) ((eta0Bin M L).share a))
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k) :
    Causalean.Stat.IsLittleOp
      (fun n a => ∫ x,
        (Iact phi L (eh (2*(n+1)) a) k j x - Iact phi L (eta0Bin M L) k j x)^2 +
        (Dbd phi L (eh (2*(n+1)) a) k j x - Dbd phi L (eta0Bin M L) k j x)^2 +
        (Edom phi L (eh (2*(n+1)) a) k j x - Edom phi L (eta0Bin M L) k j x)^2 ∂xLaw M)
      (fun n => ((2*(n+1) : ℕ) : ℝ)^(-1/2 : ℝ)) μ := by
  by_cases hz : k = 0 ∧ j = 1
  · obtain ⟨rfl, rfl⟩ := hz
    exact nuisanceRates_structural_zero_fractional_branch_energy_isLittleOp M μ
      phi dphi hphi hd hDerivative L (eta0Bin M L) eh he0 heh hrp hrlev hrP hrs
      ch hOutcome.1 (population_binary_structural_zero_joint_margins M hStruct hend hf hy
        phi L hOrder cpi hpol ch hOutcome hk hj.2)
  · have hzero : k ≠ 0 ∨ j ≠ 1 := by tauto
    exact nuisanceRates_fractional_branch_energy_isLittleOp M μ phi dphi hphi hd
      hDerivative L (eta0Bin M L) eh he0 heh hrp hrlev hrP hrs k j
      (min gap ch) (lt_min hGap.1 hOutcome.1)
      (population_binary_regular_joint_margins M hStruct hend hf phi L hOrder hOff
        gap hGap cpi hpol ch hOutcome k j hk hj hzero)

end Papers.TbsPrteOptimalTransport

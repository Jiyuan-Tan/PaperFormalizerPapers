module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLPooledPolicyConvergence
public import Papers.TbsPrteOptimalTransport.Helpers.DMLBinaryBranchRates
/-! Fractional binary branch rates from the original nuisance components.
Almost-everywhere measurable arguments are replaced by measurable versions only
inside the gap bound; the conclusions concern the actual fitted score branches. -/
public section
set_option linter.style.openClassical false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

-- Clipping provides MemLp, even when the policy is measurable only on [0,1].
-- Transport the existing gap estimate through measurable versions.
-- @node: binary_branch_memLp_component_energy_bound
/-- Suppose [the separation constant is positive](hyp:hc), the reference
[upper endpoint](hyp:hq), [lower endpoint](hyp:hl), and [boundary](hyp:hb), and
their fitted [upper endpoint](hyp:hqh), [lower endpoint](hyp:hlh), and
[boundary](hyp:hbh) are square integrable. If [the reference interval width and
the boundary's distances from both endpoints are almost surely at least the
separation constant](hyp:hgap), then [the sum of squared branch-indicator errors
is integrable and its integral is at most 36 divided by the squared separation
constant times the sum of the three integrated squared input errors](goal). -/
lemma binary_branch_memLp_component_energy_bound {B : Type*} [MeasurableSpace B]
    (ν : Measure B) (q l b qh lh bh : B → ℝ) (c : ℝ) (hc : 0 < c)
    (hq : MemLp q 2 ν) (hl : MemLp l 2 ν) (hb : MemLp b 2 ν)
    (hqh : MemLp qh 2 ν) (hlh : MemLp lh 2 ν) (hbh : MemLp bh 2 ν)
    (hgap : ∀ᵐ x ∂ν, c ≤ q x - l x ∧ c ≤ |b x - l x| ∧ c ≤ |b x - q x|) :
    Integrable (fun x => binaryBranchSqError (q x) (l x) (b x) (qh x) (lh x) (bh x)) ν ∧
      (∫ x, binaryBranchSqError (q x) (l x) (b x) (qh x) (lh x) (bh x) ∂ν) ≤
        (36 / c ^ 2) * ((∫ x, (qh x - q x)^2 ∂ν) +
          (∫ x, (lh x - l x)^2 ∂ν) + ∫ x, (bh x - b x)^2 ∂ν) := by
  let Q := hq.1.mk q
  let L := hl.1.mk l
  let B := hb.1.mk b
  let Qh := hqh.1.mk qh
  let Lh := hlh.1.mk lh
  let Bh := hbh.1.mk bh
  have eqQ : q =ᵐ[ν] Q := hq.1.ae_eq_mk
  have eqL : l =ᵐ[ν] L := hl.1.ae_eq_mk
  have eqB : b =ᵐ[ν] B := hb.1.ae_eq_mk
  have eqQh : qh =ᵐ[ν] Qh := hqh.1.ae_eq_mk
  have eqLh : lh =ᵐ[ν] Lh := hlh.1.ae_eq_mk
  have eqBh : bh =ᵐ[ν] Bh := hbh.1.ae_eq_mk
  have hg : ∀ᵐ x ∂ν, c ≤ Q x - L x ∧ c ≤ |B x - L x| ∧ c ≤ |B x - Q x| := by
    filter_upwards [hgap, eqQ, eqL, eqB] with x hx hqx hlx hbx
    simpa only [← hqx, ← hlx, ← hbx] using hx
  have heq : (fun x => binaryBranchSqError (q x) (l x) (b x) (qh x) (lh x) (bh x))
      =ᵐ[ν] (fun x => binaryBranchSqError (Q x) (L x) (B x) (Qh x) (Lh x) (Bh x)) := by
    filter_upwards [eqQ, eqL, eqB, eqQh, eqLh, eqBh] with x h1 h2 h3 h4 h5 h6
    rw [h1, h2, h3, h4, h5, h6]
  obtain ⟨hi, ht⟩ := binary_branch_component_energy_bound ν Q L B Qh Lh Bh c hc
    (by fun_prop) (by fun_prop) (by fun_prop)
    (by fun_prop) (by fun_prop) (by fun_prop)
    ((hqh.ae_eq eqQh).sub (hq.ae_eq eqQ))
    ((hlh.ae_eq eqLh).sub (hl.ae_eq eqL))
    ((hbh.ae_eq eqBh).sub (hb.ae_eq eqB)) hg
  refine ⟨hi.congr heq.symm, ?_⟩
  rw [integral_congr_ae heq]
  have eQ : (∫ x, (Qh x - Q x)^2 ∂ν) = ∫ x, (qh x - q x)^2 ∂ν := by
    apply integral_congr_ae
    filter_upwards [eqQ, eqQh] with x h1 h2
    rw [h1, h2]
  have eL : (∫ x, (Lh x - L x)^2 ∂ν) = ∫ x, (lh x - l x)^2 ∂ν := by
    apply integral_congr_ae
    filter_upwards [eqL, eqLh] with x h1 h2
    rw [h1, h2]
  have eB : (∫ x, (Bh x - B x)^2 ∂ν) = ∫ x, (bh x - b x)^2 ∂ν := by
    apply integral_congr_ae
    filter_upwards [eqB, eqBh] with x h1 h2
    rw [h1, h2]
  simpa only [eQ, eL, eB] using ht

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- The third affine hinge argument uses the same coherent success vector.
-- @node: nuisanceRates_binary_boundary_quarter_rate
/-- If [the reference binary nuisances](hyp:he0) and [every fitted nuisance
vector](hyp:heh) are admissible, and componentwise L2 errors are of smaller order
in probability than the inverse fourth root of sample size for
[level propensities](hyp:hrlev) and [treated-outcome masses](hyp:hrP), then [the
fitted boundary given by the next level propensity minus the full treated-outcome
increment has componentwise L2 errors of smaller order in probability than the
inverse fourth root of sample size relative to its reference counterpart](goal). -/
lemma nuisanceRates_binary_boundary_quarter_rate {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (L : LevelData Z X) (e0 : NuisanceBin L)
    (eh : ℕ → A → NuisanceBin L) (he0 : BinAdmissible M L e0)
    (heh : ∀ n a, BinAdmissible M L (eh n a))
    (hrlev : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrP : FiniteNuisanceRates M μ (fun n a => (eh n a).P1) e0.P1) :
    FiniteNuisanceRates M μ
      (fun n a k x => positiveValue (eh n a).pLev (k+1) x - binFullJ L (eh n a) k x)
      (fun k x => positiveValue e0.pLev (k+1) x - binFullJ L e0 k x) := by
  have hl := nuisanceRates_positiveValue M μ L.K _ _ hrlev
  have hJ := nuisanceRates_binFullJ_quarter_rate M μ L e0 eh he0 heh hrP
  intro k
  have hs := (hl (k+1)).add_eventually_nonneg_rate
    (Eventually.of_forall (fun _ => Real.rpow_nonneg (by positivity) _)) (hJ k)
  apply Causalean.Stat.IsLittleOp.of_abs_le_const_mul one_pos hs
  intro n a
  rw [one_mul, abs_of_nonneg (show 0 ≤ finiteL2Error M _ _ from Real.sqrt_nonneg _)]
  have hp (e : NuisanceBin L) (he : BinAdmissible M L e) :=
    (fitted_positive_treatment_assignment_memLp M L e he (k+1)).1
  have hj (e : NuisanceBin L) (he : BinAdmissible M L e) :
      MemLp (binFullJ L e k) 2 (xLaw M) :=
    (fitted_positive_success_memLp M L e he (k+1)).sub
      (fitted_positive_success_memLp M L e he k)
  exact (dml_l2Error_sub_le M _ _ _ _ (hp e0 he0) (hp _ (heh _ a))
    (hj e0 he0) (hj _ (heh _ a))).trans (le_abs_self _)

-- @node: nuisanceRates_fractional_branch_energy_isLittleOp
/-- For [a valid policy map](hyp:hphi) with [the specified derivative](hyp:hd)
and [a bounded Lipschitz derivative](hyp:hDerivative), assume admissible
[reference nuisances](hyp:he0) and [fitted nuisances at every sample size](hyp:heh),
with componentwise L2 errors of smaller order in probability than the inverse
fourth root of sample size for [propensities](hyp:hrp), [level propensities](hyp:hrlev),
[treated-outcome masses](hyp:hrP), and [each regular component's instrument shares](hyp:hrs).
If [the separation constant is positive](hyp:hc) and [the reference pooled-policy
interval width and the boundary's distances from both endpoints are almost
surely at least that constant](hyp:hgap), then [the integrated sum of squared
errors in the three fractional branch indicators at sample sizes twice one more
than the index is of smaller order in probability than the inverse square root
of that sample size](goal). -/
lemma nuisanceRates_fractional_branch_energy_isLittleOp
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
    (k j : ℕ) (c : ℝ) (hc : 0 < c)
    (hgap : ∀ᵐ x ∂xLaw M,
      c ≤ pooledQBin phi L e0 k j x - pooledQBin phi L e0 k (j-1) x ∧
      c ≤ |positiveValue e0.pLev (k+1) x - binFullJ L e0 k x -
        pooledQBin phi L e0 k (j-1) x| ∧
      c ≤ |positiveValue e0.pLev (k+1) x - binFullJ L e0 k x -
        pooledQBin phi L e0 k j x|) :
    Causalean.Stat.IsLittleOp
      (fun n a => ∫ x,
        (Iact phi L (eh (2*(n+1)) a) k j x - Iact phi L e0 k j x)^2 +
        (Dbd phi L (eh (2*(n+1)) a) k j x - Dbd phi L e0 k j x)^2 +
        (Edom phi L (eh (2*(n+1)) a) k j x - Edom phi L e0 k j x)^2 ∂xLaw M)
      (fun n => ((2*(n+1) : ℕ) : ℝ)^(-1/2 : ℝ)) μ := by
  obtain ⟨B, Lip, hB, hLip, hder⟩ := hDerivative
  have hlip := policy_lipschitz_of_derivative_bound phi dphi hd B
    (fun z x p hp => (hder z x p p hp hp).1)
  have hpool := nuisanceRates_pooledQBin_quarter_rate M μ phi hphi B hB hlip
    L e0 eh he0 heh hrp hrlev hrs
  have hb := nuisanceRates_binary_boundary_quarter_rate M μ L e0 eh he0 heh hrlev hrP
  have he := dml_three_component_energies_isLittleOp μ (xLaw M)
    (fun n a x => pooledQBin phi L (eh (2*(n+1)) a) k j x - pooledQBin phi L e0 k j x)
    (fun n a x => pooledQBin phi L (eh (2*(n+1)) a) k (j-1) x -
      pooledQBin phi L e0 k (j-1) x)
    (fun n a x => (positiveValue (eh (2*(n+1)) a).pLev (k+1) x -
      binFullJ L (eh (2*(n+1)) a) k x) -
      (positiveValue e0.pLev (k+1) x - binFullJ L e0 k x))
    (hpool (k,j)) (hpool (k,j-1)) (hb k)
  apply Causalean.Stat.IsLittleOp.of_abs_le_const_mul (by positivity : 0 < 36 / c^2) he
  intro n a
  rw [abs_of_nonneg (integral_nonneg fun x =>
    add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _))]
  have boundary (e : NuisanceBin L) (he : BinAdmissible M L e) :
      MemLp (fun x => positiveValue e.pLev (k+1) x - binFullJ L e k x) 2 (xLaw M) :=
    ((fitted_positive_treatment_assignment_memLp M L e he (k+1)).1).sub
      ((fitted_positive_success_memLp M L e he (k+1)).sub
        (fitted_positive_success_memLp M L e he k))
  have ht := (binary_branch_memLp_component_energy_bound (xLaw M)
    (pooledQBin phi L e0 k j) (pooledQBin phi L e0 k (j-1))
    (fun x => positiveValue e0.pLev (k+1) x - binFullJ L e0 k x)
    (pooledQBin phi L (eh (2*(n+1)) a) k j)
    (pooledQBin phi L (eh (2*(n+1)) a) k (j-1))
    (fun x => positiveValue (eh (2*(n+1)) a).pLev (k+1) x -
      binFullJ L (eh (2*(n+1)) a) k x) c hc
    (fitted_pooledQBin_memLp M phi hphi L e0 he0 k j)
    (fitted_pooledQBin_memLp M phi hphi L e0 he0 k (j-1)) (boundary e0 he0)
    (fitted_pooledQBin_memLp M phi hphi L _ (heh _ a) k j)
    (fitted_pooledQBin_memLp M phi hphi L _ (heh _ a) k (j-1))
    (boundary _ (heh _ a)) hgap).2
  exact ht.trans (mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity))

-- This is the nonsmooth L2 input for the centered score fluctuation argument.
-- It controls the actual fitted indicators, including fitted ties.
-- @node: nuisanceRates_fractional_branch_l2_tendsto_probability_zero
/-- For [a valid policy map](hyp:hphi) with [the specified derivative](hyp:hd)
and [a bounded Lipschitz derivative](hyp:hDerivative), assume admissible
[reference nuisances](hyp:he0) and [fitted nuisances at every sample size](hyp:heh),
with componentwise L2 errors of smaller order in probability than the inverse
fourth root of sample size for [propensities](hyp:hrp), [level propensities](hyp:hrlev),
[treated-outcome masses](hyp:hrP), and [each regular component's instrument shares](hyp:hrs).
If [the separation constant is positive](hyp:hc) and [the reference pooled-policy
interval width and the boundary's distances from both endpoints are almost
surely at least that constant](hyp:hgap), then [the square root of the integrated
sum of squared errors in the three fractional branch indicators at sample sizes
twice one more than the index converges in probability to zero](goal). -/
lemma nuisanceRates_fractional_branch_l2_tendsto_probability_zero
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
    (k j : ℕ) (c : ℝ) (hc : 0 < c)
    (hgap : ∀ᵐ x ∂xLaw M,
      c ≤ pooledQBin phi L e0 k j x - pooledQBin phi L e0 k (j-1) x ∧
      c ≤ |positiveValue e0.pLev (k+1) x - binFullJ L e0 k x -
        pooledQBin phi L e0 k (j-1) x| ∧
      c ≤ |positiveValue e0.pLev (k+1) x - binFullJ L e0 k x -
        pooledQBin phi L e0 k j x|) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt (∫ x,
        (Iact phi L (eh (2*(n+1)) a) k j x - Iact phi L e0 k j x)^2 +
        (Dbd phi L (eh (2*(n+1)) a) k j x - Dbd phi L e0 k j x)^2 +
        (Edom phi L (eh (2*(n+1)) a) k j x - Edom phi L e0 k j x)^2 ∂xLaw M))
      atTop (fun _ _ => 0) := by
  apply dml_half_rate_energy_l2_tendsto_probability_zero
  · intro n a
    exact integral_nonneg fun x =>
      add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)
  · exact nuisanceRates_fractional_branch_energy_isLittleOp M μ phi dphi hphi hd
      hDerivative L e0 eh he0 heh hrp hrlev hrP hrs k j c hc hgap

end Papers.TbsPrteOptimalTransport

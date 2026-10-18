module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLWeightedHinge
public import Papers.TbsPrteOptimalTransport.Helpers.DMLFractionalBranchRates
/-! Quadratic bias of the fitted fractional binary hinge with its fitted product weight.
Measurable versions are used only for the analytic bound. The conclusions concern
actual clipped nuisances and retain fitted branch indicators, including ties. -/
public section
set_option linter.style.openClassical false
set_option linter.style.whitespace false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

-- The documented policy domain gives almost-everywhere measurable arguments;
-- no global measurability of the policy outside [0,1] is required.
-- @node: binary_hinge_weighted_memLp_energy_bound
/-- Suppose [the separation constant is positive](hyp:hc), [the weight bound
is nonnegative](hyp:hW), and the reference [upper endpoint](hyp:hq), [lower
endpoint](hyp:hl), and [boundary](hyp:hb), and fitted [upper endpoint](hyp:hqh),
[lower endpoint](hyp:hlh), and [boundary](hyp:hbh) are square integrable. For a
[measurable weight](hyp:hw) [almost surely bounded by the weight bound](hyp:hwb),
if [the reference interval width and the boundary's distances from both endpoints
are almost surely at least the separation constant](hyp:hgap), then [the weighted
hinge remainder is integrable and its absolute integral is at most 78 times the
weight bound divided by the separation constant times the sum of the three
integrated squared input errors](goal). -/
lemma binary_hinge_weighted_memLp_energy_bound {B : Type*} [MeasurableSpace B]
    (ν : Measure B) (q l b qh lh bh w : B → ℝ) (c W : ℝ)
    (hc : 0 < c) (hW : 0 ≤ W)
    (hq : MemLp q 2 ν) (hl : MemLp l 2 ν) (hb : MemLp b 2 ν)
    (hqh : MemLp qh 2 ν) (hlh : MemLp lh 2 ν) (hbh : MemLp bh 2 ν)
    (hw : Measurable w) (hwb : ∀ᵐ x ∂ν, ‖w x‖ ≤ W)
    (hgap : ∀ᵐ x ∂ν, c ≤ q x - l x ∧ c ≤ |b x - l x| ∧ c ≤ |b x - q x|) :
    Integrable (fun x => w x * binaryFittedHingeRemainder
      (q x) (l x) (b x) (qh x) (lh x) (bh x)) ν ∧
    |∫ x, w x * binaryFittedHingeRemainder
      (q x) (l x) (b x) (qh x) (lh x) (bh x) ∂ν| ≤
      (78 * W / c) * ((∫ x, (qh x - q x)^2 ∂ν) +
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
  have heq : (fun x => w x * binaryFittedHingeRemainder
      (q x) (l x) (b x) (qh x) (lh x) (bh x)) =ᵐ[ν]
      (fun x => w x * binaryFittedHingeRemainder
        (Q x) (L x) (B x) (Qh x) (Lh x) (Bh x)) := by
    filter_upwards [eqQ, eqL, eqB, eqQh, eqLh, eqBh] with x h1 h2 h3 h4 h5 h6
    rw [h1, h2, h3, h4, h5, h6]
  obtain ⟨hi, ht⟩ := binary_hinge_weighted_component_energy_bound ν Q L B Qh Lh Bh w c W
    hc hW (by fun_prop) (by fun_prop) (by fun_prop)
    (by fun_prop) (by fun_prop) (by fun_prop) hw hwb
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

-- The actual fitted gamma weight is measurable and bounded by clipping.
-- @node: fitted_fractional_hinge_bias_energy_bound
/-- For [a valid policy map](hyp:hphi) and admissible [reference](hyp:he0) and
[fitted](hyp:he) binary nuisances, assume [the separation constant is positive](hyp:hc)
and [the reference pooled-policy interval width and the boundary's distances from
both endpoints are almost surely at least that constant](hyp:hgap). Then [the
hinge remainder multiplied by the fitted component weight is integrable, and its
absolute integral is at most 78 divided by the separation constant times the sum
of the integrated squared errors in the upper pooled-policy endpoint, lower
pooled-policy endpoint, and boundary](goal). -/
lemma fitted_fractional_hinge_bias_energy_bound
    (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (L : LevelData Z X) (e0 e : NuisanceBin L)
    (he0 : BinAdmissible M L e0) (he : BinAdmissible M L e)
    (k j : ℕ) (c : ℝ) (hc : 0 < c)
    (hgap : ∀ᵐ x ∂xLaw M,
      c ≤ pooledQBin phi L e0 k j x - pooledQBin phi L e0 k (j-1) x ∧
      c ≤ |positiveValue e0.pLev (k+1) x - binFullJ L e0 k x -
        pooledQBin phi L e0 k (j-1) x| ∧
      c ≤ |positiveValue e0.pLev (k+1) x - binFullJ L e0 k x -
        pooledQBin phi L e0 k j x|) :
    let R := fun x => binaryFittedHingeRemainder
      (pooledQBin phi L e0 k j x) (pooledQBin phi L e0 k (j-1) x)
      (positiveValue e0.pLev (k+1) x - binFullJ L e0 k x)
      (pooledQBin phi L e k j x) (pooledQBin phi L e k (j-1) x)
      (positiveValue e.pLev (k+1) x - binFullJ L e k x)
    Integrable (fun x => regularValue e.gamma k j x * R x) (xLaw M) ∧
    |∫ x, regularValue e.gamma k j x * R x ∂xLaw M| ≤ (78 / c) *
      ((∫ x, (pooledQBin phi L e k j x - pooledQBin phi L e0 k j x)^2 ∂xLaw M) +
        (∫ x, (pooledQBin phi L e k (j-1) x - pooledQBin phi L e0 k (j-1) x)^2 ∂xLaw M) +
        ∫ x, ((positiveValue e.pLev (k+1) x - binFullJ L e k x) -
          (positiveValue e0.pLev (k+1) x - binFullJ L e0 k x))^2 ∂xLaw M) := by
  have hw : Measurable (regularValue e.gamma k j) := by
    first | fun_prop | skip
    unfold regularValue
    split_ifs
    · exact (he.2.2.2.2.2.1 _).2
    · fun_prop
  have hwb : ∀ᵐ x ∂xLaw M, ‖regularValue e.gamma k j x‖ ≤ 1 := by
    unfold regularValue
    split_ifs with hi
    · filter_upwards [he.2.2.2.2.1 ⟨(k,j), hi⟩] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg hx.2.1]
      exact hx.2.2
    · simp
  have boundary (e : NuisanceBin L) (he : BinAdmissible M L e) :
      MemLp (fun x => positiveValue e.pLev (k+1) x - binFullJ L e k x) 2 (xLaw M) :=
    ((fitted_positive_treatment_assignment_memLp M L e he (k+1)).1).sub
      ((fitted_positive_success_memLp M L e he (k+1)).sub
        (fitted_positive_success_memLp M L e he k))
  simpa only [mul_one] using binary_hinge_weighted_memLp_energy_bound (xLaw M)
    (pooledQBin phi L e0 k j) (pooledQBin phi L e0 k (j-1))
    (fun x => positiveValue e0.pLev (k+1) x - binFullJ L e0 k x)
    (pooledQBin phi L e k j) (pooledQBin phi L e k (j-1))
    (fun x => positiveValue e.pLev (k+1) x - binFullJ L e k x)
    (regularValue e.gamma k j) c 1 hc zero_le_one
    (fitted_pooledQBin_memLp M phi hphi L e0 he0 k j)
    (fitted_pooledQBin_memLp M phi hphi L e0 he0 k (j-1)) (boundary e0 he0)
    (fitted_pooledQBin_memLp M phi hphi L e he k j)
    (fitted_pooledQBin_memLp M phi hphi L e he k (j-1)) (boundary e he) hw hwb hgap

-- The second-order branch bias follows from original nuisance rates, rather
-- than an assumed rate for the score or a branch-recovery event.
-- @node: nuisanceRates_fractional_hinge_bias_root_n_negligible
/-- For [a valid policy map](hyp:hphi) with [the specified derivative](hyp:hd)
and [a bounded Lipschitz derivative](hyp:hDerivative), assume admissible
[reference](hyp:he0) and [fitted nuisances at every sample size](hyp:heh), with
componentwise L2 errors of smaller order in probability than the inverse fourth
root of sample size for [propensities](hyp:hrp), [level propensities](hyp:hrlev),
[treated-outcome masses](hyp:hrP), and [every regular component's instrument shares](hyp:hrs).
If [the separation constant is positive](hyp:hc) and [the reference pooled-policy
interval width and the boundary's distances from both endpoints are almost surely
at least that constant](hyp:hgap), then [the integral of the fitted-weighted hinge
remainder at sample sizes twice one more than the index, scaled by the square
root of one more than the index, converges in probability to zero](goal). -/
lemma nuisanceRates_fractional_hinge_bias_root_n_negligible
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
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) * ∫ x,
        regularValue (eh (2*(n+1)) a).gamma k j x * binaryFittedHingeRemainder
          (pooledQBin phi L e0 k j x) (pooledQBin phi L e0 k (j-1) x)
          (positiveValue e0.pLev (k+1) x - binFullJ L e0 k x)
          (pooledQBin phi L (eh (2*(n+1)) a) k j x)
          (pooledQBin phi L (eh (2*(n+1)) a) k (j-1) x)
          (positiveValue (eh (2*(n+1)) a).pLev (k+1) x -
            binFullJ L (eh (2*(n+1)) a) k x) ∂xLaw M) atTop (fun _ _ => 0) := by
  obtain ⟨B, Lip, hB, hLip, hder⟩ := hDerivative
  have hlip := policy_lipschitz_of_derivative_bound phi dphi hd B
    (fun z x p hp => (hder z x p p hp hp).1)
  have hpool := nuisanceRates_pooledQBin_quarter_rate M μ phi hphi B hB hlip
    L e0 eh he0 heh hrp hrlev hrs
  have hb := nuisanceRates_binary_boundary_quarter_rate M μ L e0 eh he0 heh hrlev hrP
  have henergy := dml_three_component_energies_isLittleOp μ (xLaw M)
    (fun n a x => pooledQBin phi L (eh (2*(n+1)) a) k j x - pooledQBin phi L e0 k j x)
    (fun n a x => pooledQBin phi L (eh (2*(n+1)) a) k (j-1) x -
      pooledQBin phi L e0 k (j-1) x)
    (fun n a x => (positiveValue (eh (2*(n+1)) a).pLev (k+1) x -
      binFullJ L (eh (2*(n+1)) a) k x) -
      (positiveValue e0.pLev (k+1) x - binFullJ L e0 k x))
    (hpool (k,j)) (hpool (k,j-1)) (hb k)
  apply dml_root_n_bias_tendsto_probability
  apply Causalean.Stat.IsLittleOp.of_abs_le_const_mul (by positivity : 0 < 78 / c) henergy
  intro n a
  exact (fitted_fractional_hinge_bias_energy_bound M phi hphi L e0 (eh (2*(n+1)) a)
    he0 (heh _ a) k j c hc hgap).2.trans
      (mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity))

-- This exact expansion connects the analytic hinge remainder to the conditional
-- mean of the score, retaining the fitted baseline and both policy corrections.
-- @node: fitted_fractional_component_bias_split
/-- [The fitted fractional hinge plus its regression and policy conditional-mean
corrections minus the reference hinge equals the hinge remainder plus three
terms: the boundary indicator times the discrepancy between mass-ratio-adjusted
regression corrections and the boundary change, the active indicator times the
upper policy correction plus its endpoint change, and minus the product of the
dominance and active indicators times the lower policy correction plus its
endpoint change and, for the first sublevel, the level-propensity correction](goal). -/
lemma fitted_fractional_component_bias_split
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (e0 e : NuisanceBin L) (k j : ℕ) (x : X) :
    let dq := fun i => pooledQBin phi L e k i x - pooledQBin phi L e0 k i x
    let db := (positiveValue e.pLev (k+1) x - binFullJ L e k x) -
      (positiveValue e0.pLev (k+1) x - binFullJ L e0 k x)
    let rP := fun i => positiveValue e0.piLev i x *
      (positiveValue e0.P1 i x - positiveValue e.P1 i x) / positiveValue e.piLev i x
    let rp := fun i => positiveValue e0.piLev i x *
      (positiveValue e0.pLev i x - positiveValue e.pLev i x) / positiveValue e.piLev i x
    let Q := fun i => ∑ z, instProb M z x * RqBin dphi L e k i (x,z,M.prop z x,0)
    hMinus phi L e k j x + binaryRegularRegressionMean phi L e0 e k j x +
      binaryRegularPolicyMean M phi dphi L e k j x - hMinus phi L e0 k j x =
    binaryFittedHingeRemainder
      (pooledQBin phi L e0 k j x) (pooledQBin phi L e0 k (j-1) x)
      (positiveValue e0.pLev (k+1) x - binFullJ L e0 k x)
      (pooledQBin phi L e k j x) (pooledQBin phi L e k (j-1) x)
      (positiveValue e.pLev (k+1) x - binFullJ L e k x) +
    Dbd phi L e k j x * (rP (k+1) - rP k - rp (k+1) - db) +
    Iact phi L e k j x * (Q j + dq j) -
    Edom phi L e k j x * Iact phi L e k j x *
      ((if j = 1 then rp k else 0) + Q (j-1) + dq (j-1)) := by
  dsimp only
  rw [hMinus_binaryFittedHingeRemainder_eq]
  dsimp only [binaryRegularRegressionMean, binaryRegularPolicyMean]
  by_cases hj : j = 1
  · simp only [if_pos hj]
    ring
  · simp only [if_neg hj]
    ring

end Papers.TbsPrteOptimalTransport

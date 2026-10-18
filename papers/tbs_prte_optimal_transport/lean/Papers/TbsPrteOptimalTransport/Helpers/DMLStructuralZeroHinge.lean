module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLStructuralZeroFractionalRates
public import Papers.TbsPrteOptimalTransport.Helpers.DMLFractionalPolicyBias
/-! Quadratic fitted hinge bias at the fixed zero boundary. Outcome margins
control the remainder without uniform separation of the policy level from zero. -/
public section
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedTactic false
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Filter Set
open scoped Classical Topology

-- @node: binary_structural_zero_hinge_linear_bound
/-- If [the fitted policy argument differs from its true value by at most the error
bound](hyp:hq) and [the fitted upper boundary differs from its true value by at most
the same bound](hyp:hb), then [the absolute fitted hinge remainder with the lower
argument fixed at zero is at most four times that error bound](goal). -/
lemma binary_structural_zero_hinge_linear_bound {q b qh bh err : ℝ}
    (hq : |qh - q| ≤ err) (hb : |bh - b| ≤ err) :
    |binaryFittedHingeRemainder q 0 b qh 0 bh| ≤ 4 * err := by
  have he : 0 ≤ err := (abs_nonneg _).trans hq
  have hm : |max 0 bh - max 0 b| ≤ err :=
    (abs_max_sub_max_le_max 0 bh 0 b).trans (max_le (by simpa using he) hb)
  have ha : |(qh - max 0 bh) - (q - max 0 b)| ≤ 2 * err := by
    have hid : (qh - max 0 bh) - (q - max 0 b) =
        (qh - q) - (max 0 bh - max 0 b) := by ring
    rw [hid]
    exact (abs_sub _ _).trans (by linarith)
  have hh : |max 0 (qh - max 0 bh) - max 0 (q - max 0 b)| ≤ 2 * err :=
    (abs_max_sub_max_le_max 0 _ 0 _).trans (max_le (by simpa using (by linarith : 0 ≤ 2 * err)) ha)
  have hi : |indicator (qh > max 0 bh) * (qh - q)| ≤ err := by
    unfold indicator
    split_ifs <;> simpa using (by first | exact hq | exact he)
  have hd : |indicator (0 < bh ∧ bh < qh) * (bh - b)| ≤ err := by
    unfold indicator
    split_ifs <;> simpa using (by first | exact hb | exact he)
  have hc := (abs_sub _ _).trans (add_le_add hi hd)
  unfold binaryFittedHingeRemainder
  simp only [sub_self, mul_zero, sub_zero]
  exact (abs_sub _ _).trans ((add_le_add hh hc).trans (by ring_nf; rfl))

-- @node: binary_structural_zero_hinge_quadratic_bound
/-- If [the margin is positive](hyp:hc), [the true upper boundary is at least the
margin](hyp:hbc), [its distance from the true policy argument is at least the margin](hyp:hbq),
and [the fitted policy argument and upper boundary each have absolute error at most
the error bound](hyp:hq,hb), then [the absolute fitted hinge remainder with lower
argument fixed at zero is at most eight divided by the margin times the squared
error bound](goal). -/
lemma binary_structural_zero_hinge_quadratic_bound {q b qh bh err c : ℝ}
    (hc : 0 < c) (hbc : c ≤ b) (hbq : c ≤ |b - q|)
    (hq : |qh - q| ≤ err) (hb : |bh - b| ≤ err) :
    |binaryFittedHingeRemainder q 0 b qh 0 bh| ≤ (8 / c) * err ^ 2 := by
  have he0 : 0 ≤ err := (abs_nonneg _).trans hq
  by_cases he : err < c / 2
  · obtain ⟨hi, hd, _⟩ := binary_structural_zero_branches_stable hc hbc hbq hq hb he
    have hb0 : 0 < b := hc.trans_le hbc
    have hbh0 : 0 < bh := by have := (abs_le.mp hb).1; linarith
    have hr : binaryFittedHingeRemainder q 0 b qh 0 bh = 0 := by
      unfold binaryFittedHingeRemainder
      rw [hi, hd, max_eq_right hb0.le, max_eq_right hbh0.le]
      by_cases hlt : b < q
      · have hqh : bh < qh := by
          have hs : c ≤ q - b := by
            simpa only [abs_of_neg (sub_neg.mpr hlt), neg_sub] using hbq
          have := (abs_le.mp hq).1
          have := (abs_le.mp hb).2
          linarith
        simp only [indicator, if_pos hlt, if_pos (And.intro hb0 hlt),
          max_eq_right (sub_nonneg.mpr hlt.le), max_eq_right (sub_nonneg.mpr hqh.le),
          sub_self, mul_zero, sub_zero, one_mul]
        ring
      · have hqh : qh ≤ bh := by
          have hs : c ≤ b - q := by
            simpa only [abs_of_nonneg (sub_nonneg.mpr (le_of_not_gt hlt))] using hbq
          have := (abs_le.mp hq).2
          have := (abs_le.mp hb).1
          linarith
        simp only [indicator, if_neg hlt, if_neg (show ¬ (0 < b ∧ b < q) from fun h => hlt h.2),
          max_eq_left (sub_nonpos.mpr (le_of_not_gt hlt)),
          max_eq_left (sub_nonpos.mpr hqh), sub_self, mul_zero, zero_mul]
    rw [hr, abs_zero]
    positivity
  · apply (binary_structural_zero_hinge_linear_bound hq hb).trans
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hc).mpr
    have hlarge : c / 2 ≤ err := le_of_not_gt he
    nlinarith [mul_nonneg he0 (show 0 ≤ 2 * err - c by linarith)]

-- @node: binary_structural_zero_hinge_weighted_component_energy_bound
/-- Suppose [the margin is positive](hyp:hc), [the weight bound is nonnegative](hyp:hW),
[the true policy argument and upper boundary are measurable](hyp:hq,hb), [their fitted
counterparts are measurable](hyp:hqh,hbh), [the weight is measurable](hyp:hw), [its
absolute value is at most the weight bound almost everywhere](hyp:hwb), [the two
component errors have finite second moments](hyp:heq,heb), and [the true upper boundary
and its distance from the policy argument are at least the margin almost everywhere](hyp:hgap).
Then [the weighted fitted hinge remainder at the fixed zero lower argument is integrable,
and its absolute integral is at most twenty-four times the weight bound divided by
the margin times the sum of the two component squared-error integrals](goal). -/
lemma binary_structural_zero_hinge_weighted_component_energy_bound
    {X : Type*} [MeasurableSpace X] (ν : Measure X)
    (q b qh bh w : X → ℝ) (c W : ℝ) (hc : 0 < c) (hW : 0 ≤ W)
    (hq : Measurable q) (hb : Measurable b)
    (hqh : Measurable qh) (hbh : Measurable bh)
    (hw : Measurable w) (hwb : ∀ᵐ x ∂ν, ‖w x‖ ≤ W)
    (heq : MemLp (fun x => qh x - q x) 2 ν)
    (heb : MemLp (fun x => bh x - b x) 2 ν)
    (hgap : ∀ᵐ x ∂ν, c ≤ b x ∧ c ≤ |b x - q x|) :
    Integrable (fun x => w x * binaryFittedHingeRemainder
      (q x) 0 (b x) (qh x) 0 (bh x)) ν ∧
    |∫ x, w x * binaryFittedHingeRemainder (q x) 0 (b x) (qh x) 0 (bh x) ∂ν| ≤
      (24 * W / c) * ((∫ x, (qh x - q x)^2 ∂ν) + ∫ x, (bh x - b x)^2 ∂ν) := by
  obtain ⟨he, henergy⟩ := integral_sq_abs_sum_three_le ν
    (fun x => qh x - q x) (fun x => bh x - b x) (fun _ => 0)
    heq heb MemLp.zero
  simp only [abs_zero, add_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), integral_zero]
    at he henergy
  let R := fun x => w x * binaryFittedHingeRemainder (q x) 0 (b x) (qh x) 0 (bh x)
  let E := fun x => |qh x - q x| + |bh x - b x|
  have hm : Measurable R := by dsimp only [R]; unfold binaryFittedHingeRemainder; fun_prop
  have hdom : Integrable (fun x => (W * (8 / c)) * E x ^ 2) ν :=
    he.integrable_sq.const_mul _
  have hbound : ∀ᵐ x ∂ν, |R x| ≤ (W * (8 / c)) * E x ^ 2 := by
    filter_upwards [hgap, hwb] with x hx hwx
    have hqE : |qh x - q x| ≤ E x := by dsimp only [E]; linarith [abs_nonneg (bh x - b x)]
    have hbE : |bh x - b x| ≤ E x := by dsimp only [E]; linarith [abs_nonneg (qh x - q x)]
    have hr := binary_structural_zero_hinge_quadratic_bound hc hx.1 hx.2 hqE hbE
    dsimp only [R]
    rw [abs_mul]
    calc
      _ ≤ W * ((8 / c) * E x ^ 2) :=
        mul_le_mul (by simpa only [Real.norm_eq_abs] using hwx) hr (abs_nonneg _) hW
      _ = _ := by ring
  have hi : Integrable R ν := hdom.mono' hm.aestronglyMeasurable (by
    simpa only [Real.norm_eq_abs] using hbound)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ x, |R x| ∂ν := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm R
    _ ≤ ∫ x, (W * (8 / c)) * E x ^ 2 ∂ν := integral_mono_ae hi.abs hdom hbound
    _ = (W * (8 / c)) * ∫ x, E x ^ 2 ∂ν := integral_const_mul _ _
    _ ≤ (W * (8 / c)) * (3 * ((∫ x, (qh x - q x)^2 ∂ν) +
        ∫ x, (bh x - b x)^2 ∂ν)) := mul_le_mul_of_nonneg_left henergy (by positivity)
    _ = _ := by ring

-- @node: binary_structural_zero_hinge_weighted_memLp_energy_bound
/-- Suppose [the margin is positive](hyp:hc), [the weight bound is nonnegative](hyp:hW),
[the true policy argument and upper boundary have finite second moments](hyp:hq,hb),
[their fitted counterparts have finite second moments](hyp:hqh,hbh), [the weight is
measurable](hyp:hw), [its absolute value is bounded by the weight bound almost everywhere](hyp:hwb),
and [the true upper boundary and its distance from the policy argument are at least
the margin almost everywhere](hyp:hgap). Then [the weighted fitted hinge remainder
at the fixed zero lower argument is integrable, and its absolute integral is at most
twenty-four times the weight bound divided by the margin times the sum of the two
component squared-error integrals](goal). -/
lemma binary_structural_zero_hinge_weighted_memLp_energy_bound
    {X : Type*} [MeasurableSpace X] (ν : Measure X)
    (q b qh bh w : X → ℝ) (c W : ℝ) (hc : 0 < c) (hW : 0 ≤ W)
    (hq : MemLp q 2 ν) (hb : MemLp b 2 ν)
    (hqh : MemLp qh 2 ν) (hbh : MemLp bh 2 ν)
    (hw : Measurable w) (hwb : ∀ᵐ x ∂ν, ‖w x‖ ≤ W)
    (hgap : ∀ᵐ x ∂ν, c ≤ b x ∧ c ≤ |b x - q x|) :
    Integrable (fun x => w x * binaryFittedHingeRemainder
      (q x) 0 (b x) (qh x) 0 (bh x)) ν ∧
    |∫ x, w x * binaryFittedHingeRemainder (q x) 0 (b x) (qh x) 0 (bh x) ∂ν| ≤
      (24 * W / c) * ((∫ x, (qh x - q x)^2 ∂ν) + ∫ x, (bh x - b x)^2 ∂ν) := by
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
  have heq : (fun x => w x * binaryFittedHingeRemainder (q x) 0 (b x) (qh x) 0 (bh x))
      =ᵐ[ν] (fun x => w x * binaryFittedHingeRemainder (Q x) 0 (B x) (Qh x) 0 (Bh x)) := by
    filter_upwards [eqQ, eqB, eqQh, eqBh] with x h1 h2 h3 h4
    rw [h1, h2, h3, h4]
  obtain ⟨hi, ht⟩ := binary_structural_zero_hinge_weighted_component_energy_bound
    ν Q B Qh Bh w c W hc hW (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    hw hwb ((hqh.ae_eq eqQh).sub (hq.ae_eq eqQ))
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

-- @node: fitted_structural_zero_hinge_bias_energy_bound
/-- For [a valid policy map](hyp:hphi), [admissible reference binary nuisances](hyp:he0),
and [admissible fitted binary nuisances](hyp:he), suppose [the margin is positive](hyp:hc)
and [the reference first-level success-adjusted boundary and its distance from the
first pooled policy argument are at least the margin almost everywhere](hyp:hgap).
Then [the first fractional component's fitted hinge remainder, weighted by its fitted
regular coefficient, is integrable, and its absolute mean is bounded by twenty-four
divided by the margin times the sum of the squared-error integrals for the upper
and lower pooled policy arguments and the success-adjusted boundary](goal). -/
lemma fitted_structural_zero_hinge_bias_energy_bound
    (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (L : LevelData Z X) (e0 e : NuisanceBin L)
    (he0 : BinAdmissible M L e0) (he : BinAdmissible M L e)
    (c : ℝ) (hc : 0 < c)
    (hgap : ∀ᵐ x ∂xLaw M,
      c ≤ positiveValue e0.pLev 1 x - binFullJ L e0 0 x ∧
      c ≤ |positiveValue e0.pLev 1 x - binFullJ L e0 0 x -
        pooledQBin phi L e0 0 1 x|) :
    let R := fun x => binaryFittedHingeRemainder
      (pooledQBin phi L e0 0 1 x) (pooledQBin phi L e0 0 0 x)
      (positiveValue e0.pLev 1 x - binFullJ L e0 0 x)
      (pooledQBin phi L e 0 1 x) (pooledQBin phi L e 0 0 x)
      (positiveValue e.pLev 1 x - binFullJ L e 0 x)
    Integrable (fun x => regularValue e.gamma 0 1 x * R x) (xLaw M) ∧
    |∫ x, regularValue e.gamma 0 1 x * R x ∂xLaw M| ≤ (24 / c) *
      ((∫ x, (pooledQBin phi L e 0 1 x - pooledQBin phi L e0 0 1 x)^2 ∂xLaw M) +
        (∫ x, (pooledQBin phi L e 0 0 x - pooledQBin phi L e0 0 0 x)^2 ∂xLaw M) +
        ∫ x, ((positiveValue e.pLev 1 x - binFullJ L e 0 x) -
          (positiveValue e0.pLev 1 x - binFullJ L e0 0 x))^2 ∂xLaw M) := by
  have hw : Measurable (regularValue e.gamma 0 1) := by
    first | fun_prop | skip
    unfold regularValue
    split_ifs
    · exact (he.2.2.2.2.2.1 _).2
    · fun_prop
  have hwb : ∀ᵐ x ∂xLaw M, ‖regularValue e.gamma 0 1 x‖ ≤ 1 := by
    unfold regularValue
    split_ifs with hi
    · filter_upwards [he.2.2.2.2.1 ⟨(0,1), hi⟩] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg hx.2.1]
      exact hx.2.2
    · simp
  have boundary (e : NuisanceBin L) (he : BinAdmissible M L e) :
      MemLp (fun x => positiveValue e.pLev 1 x - binFullJ L e 0 x) 2 (xLaw M) :=
    ((fitted_positive_treatment_assignment_memLp M L e he 1).1).sub
      ((fitted_positive_success_memLp M L e he 1).sub
        (fitted_positive_success_memLp M L e he 0))
  have hz (e : NuisanceBin L) (x : X) : pooledQBin phi L e 0 0 x = 0 := by
    simp [pooledQBin, positiveValue]
  dsimp only
  simp only [hz, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), integral_zero, add_zero]
  simpa only [mul_one] using binary_structural_zero_hinge_weighted_memLp_energy_bound
    (xLaw M) (pooledQBin phi L e0 0 1)
    (fun x => positiveValue e0.pLev 1 x - binFullJ L e0 0 x)
    (pooledQBin phi L e 0 1)
    (fun x => positiveValue e.pLev 1 x - binFullJ L e 0 x)
    (regularValue e.gamma 0 1) c 1 hc zero_le_one
    (fitted_pooledQBin_memLp M phi hphi L e0 he0 0 1) (boundary e0 he0)
    (fitted_pooledQBin_memLp M phi hphi L e he 0 1) (boundary e he) hw hwb hgap

-- The second-order branch bias follows from original nuisance rates, rather
-- than an assumed rate for the score or a branch-recovery event.
-- @node: nuisanceRates_structural_zero_hinge_bias_root_n_negligible
/-- Suppose [the policy map is valid](hyp:hphi), [its specified derivative is correct](hyp:hd),
[the derivative is bounded and Lipschitz](hyp:hDerivative), [the reference binary
nuisances are admissible](hyp:he0), and [all fitted nuisances are admissible](hyp:heh).
If [propensity errors satisfy the finite nuisance rate conditions](hyp:hrp), [level
errors satisfy those conditions](hyp:hrlev), [binary success-probability errors satisfy
them](hyp:hrP), [all regular instrument-share errors satisfy them](hyp:hrs), [the
margin is positive](hyp:hc), and [the reference first-level success-adjusted boundary
and its distance from the first pooled policy argument are at least the margin almost
everywhere](hyp:hgap), then [the mean fitted hinge remainder for the first fractional
component, weighted by its fitted regular coefficient and multiplied by the square
root of the evaluation size, converges to zero in probability when the training
size is twice the evaluation size](goal). -/
lemma nuisanceRates_structural_zero_hinge_bias_root_n_negligible
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
      c ≤ |positiveValue e0.pLev 1 x - binFullJ L e0 0 x -
        pooledQBin phi L e0 0 1 x|) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) * ∫ x,
        regularValue (eh (2*(n+1)) a).gamma 0 1 x * binaryFittedHingeRemainder
          (pooledQBin phi L e0 0 1 x) (pooledQBin phi L e0 0 0 x)
          (positiveValue e0.pLev 1 x - binFullJ L e0 0 x)
          (pooledQBin phi L (eh (2*(n+1)) a) 0 1 x)
          (pooledQBin phi L (eh (2*(n+1)) a) 0 0 x)
          (positiveValue (eh (2*(n+1)) a).pLev 1 x -
            binFullJ L (eh (2*(n+1)) a) 0 x) ∂xLaw M) atTop (fun _ _ => 0) := by
  obtain ⟨B, Lip, hB, hLip, hder⟩ := hDerivative
  have hlip := policy_lipschitz_of_derivative_bound phi dphi hd B
    (fun z x p hp => (hder z x p p hp hp).1)
  have hpool := nuisanceRates_pooledQBin_quarter_rate M μ phi hphi B hB hlip
    L e0 eh he0 heh hrp hrlev hrs
  have hb := nuisanceRates_binary_boundary_quarter_rate M μ L e0 eh he0 heh hrlev hrP
  have henergy := dml_three_component_energies_isLittleOp μ (xLaw M)
    (fun n a x => pooledQBin phi L (eh (2*(n+1)) a) 0 1 x - pooledQBin phi L e0 0 1 x)
    (fun n a x => pooledQBin phi L (eh (2*(n+1)) a) 0 0 x -
      pooledQBin phi L e0 0 0 x)
    (fun n a x => (positiveValue (eh (2*(n+1)) a).pLev 1 x -
      binFullJ L (eh (2*(n+1)) a) 0 x) -
      (positiveValue e0.pLev 1 x - binFullJ L e0 0 x))
    (hpool (0,1)) (hpool (0,0)) (hb 0)
  apply dml_root_n_bias_tendsto_probability
  apply Causalean.Stat.IsLittleOp.of_abs_le_const_mul (by positivity : 0 < 24 / c) henergy
  intro n a
  exact (fitted_structural_zero_hinge_bias_energy_bound M phi hphi L e0 (eh (2*(n+1)) a)
    he0 (heh _ a) c hc hgap).2.trans
      (mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity))

-- @node: nuisanceRates_population_binary_hinge_bias_root_n_negligible
/-- Suppose [the policy map is valid](hyp:hphi), [its specified derivative is correct](hyp:hd),
[the derivative is bounded and Lipschitz](hyp:hDerivative), [the structural model
assumptions hold](hyp:hStruct), [outcome endpoints are known](hyp:hend), [the instrument
admits finite reduction](hyp:hf), and [outcomes are binary almost surely](hyp:hy).
Assume [baseline and policy level orders agree](hyp:hOrder), [policy levels avoid
boundaries](hyp:hOff), [propensity gaps are uniformly separated](hyp:hGap), [policy
overlap holds](hyp:hpol), [discrete outcome gaps are uniformly separated](hyp:hOutcome),
[the population nuisances are admissible](hyp:he0), and [all fitted nuisances are
admissible](hyp:heh). If [propensity, level, and success-probability errors satisfy
the finite nuisance rate conditions](hyp:hrp,hrlev,hrP), [all regular instrument-share
errors satisfy those conditions](hyp:hrs), [the component's level is below the terminal
level](hyp:hk), and [its within-level index is in the regular range](hyp:hj), then
[the component's population-reference fitted hinge remainder, weighted by its fitted
regular coefficient and multiplied by the square root of the evaluation size, converges
to zero in probability along training sizes twice the evaluation size](goal). -/
lemma nuisanceRates_population_binary_hinge_bias_root_n_negligible
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
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) * ∫ x,
        regularValue (eh (2*(n+1)) a).gamma k j x * binaryFittedHingeRemainder
          (pooledQBin phi L (eta0Bin M L) k j x)
          (pooledQBin phi L (eta0Bin M L) k (j-1) x)
          (positiveValue (eta0Bin M L).pLev (k+1) x - binFullJ L (eta0Bin M L) k x)
          (pooledQBin phi L (eh (2*(n+1)) a) k j x)
          (pooledQBin phi L (eh (2*(n+1)) a) k (j-1) x)
          (positiveValue (eh (2*(n+1)) a).pLev (k+1) x -
            binFullJ L (eh (2*(n+1)) a) k x) ∂xLaw M) atTop (fun _ _ => 0) := by
  by_cases hz : k = 0 ∧ j = 1
  · obtain ⟨rfl, rfl⟩ := hz
    exact nuisanceRates_structural_zero_hinge_bias_root_n_negligible M μ
      phi dphi hphi hd hDerivative L (eta0Bin M L) eh he0 heh hrp hrlev hrP hrs
      ch hOutcome.1 (population_binary_structural_zero_joint_margins M hStruct hend hf hy
        phi L hOrder cpi hpol ch hOutcome hk hj.2)
  · have hzero : k ≠ 0 ∨ j ≠ 1 := by tauto
    exact nuisanceRates_fractional_hinge_bias_root_n_negligible M μ phi dphi hphi hd
      hDerivative L (eta0Bin M L) eh he0 heh hrp hrlev hrP hrs k j
      (min gap ch) (lt_min hGap.1 hOutcome.1)
      (population_binary_regular_joint_margins M hStruct hend hf phi L hOrder hOff
        gap hGap cpi hpol ch hOutcome k j hk hj hzero)

-- @node: fitted_population_binary_hinge_bias_integrable
/-- Suppose [the policy map is valid](hyp:hphi), [the structural assumptions hold](hyp:hStruct),
[outcome endpoints are known](hyp:hend), [the instrument admits finite reduction](hyp:hf),
[outcomes are binary almost surely](hyp:hy), [baseline and policy level orders agree](hyp:hOrder),
[policy levels avoid boundaries](hyp:hOff), [propensity gaps are uniformly separated](hyp:hGap),
[policy overlap holds](hyp:hpol), and [discrete outcome gaps are uniformly separated](hyp:hOutcome).
If [the population binary nuisances are admissible](hyp:he0), [the fitted binary
nuisances are admissible](hyp:he), [the component's level is below the terminal level](hyp:hk),
and [its within-level index is in the regular range](hyp:hj), then [the fitted regular
coefficient times the component's fitted hinge remainder relative to the population
nuisances is integrable over the covariate distribution](goal). -/
lemma fitted_population_binary_hinge_bias_integrable
    (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hStruct : StructuralAssumptions M) (hend : OutcomeEndpointsKnown M)
    (hf : InstrumentFiniteReduction Z) (hy : OutcomeBinaryAE M)
    (L : LevelData Z X) (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (hOff : PolicyLevelOffBoundary L) (gap : ℝ)
    (hGap : PropensityGapSeparationWitness M.prop (policyProp phi M.prop) gap)
    (cpi : ℝ) (hpol : PolicyOverlap M L cpi) (ch : ℝ)
    (hOutcome : DiscreteOutcomeGapWitness M L ch)
    (he0 : BinAdmissible M L (eta0Bin M L)) (e : NuisanceBin L)
    (he : BinAdmissible M L e)
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k) :
    Integrable (fun x => regularValue e.gamma k j x * binaryFittedHingeRemainder
      (pooledQBin phi L (eta0Bin M L) k j x)
      (pooledQBin phi L (eta0Bin M L) k (j-1) x)
      (positiveValue (eta0Bin M L).pLev (k+1) x - binFullJ L (eta0Bin M L) k x)
      (pooledQBin phi L e k j x) (pooledQBin phi L e k (j-1) x)
      (positiveValue e.pLev (k+1) x - binFullJ L e k x)) (xLaw M) := by
  by_cases hz : k = 0 ∧ j = 1
  · obtain ⟨rfl, rfl⟩ := hz
    exact (fitted_structural_zero_hinge_bias_energy_bound M phi hphi L
      (eta0Bin M L) e he0 he ch hOutcome.1
      (population_binary_structural_zero_joint_margins M hStruct hend hf hy
        phi L hOrder cpi hpol ch hOutcome hk hj.2)).1
  · have hzero : k ≠ 0 ∨ j ≠ 1 := by tauto
    exact (fitted_fractional_hinge_bias_energy_bound M phi hphi L (eta0Bin M L) e
      he0 he k j (min gap ch) (lt_min hGap.1 hOutcome.1)
      (population_binary_regular_joint_margins M hStruct hend hf phi L hOrder hOff
        gap hGap cpi hpol ch hOutcome k j hk hj hzero)).1

-- @node: nuisanceRates_population_fractional_component_conditional_bias_root_n_negligible
/-- Suppose [the policy map is valid](hyp:hphi), [its specified derivative is correct](hyp:hd),
[the derivative is bounded and Lipschitz](hyp:hDerivative), [the structural assumptions
hold](hyp:hStruct), [outcome endpoints are known](hyp:hend), [the instrument admits
finite reduction](hyp:hf), [outcomes are binary almost surely](hyp:hy), [baseline and
policy level orders agree](hyp:hOrder), and [policy overlap holds](hyp:hov). Assume
[the population binary nuisances are admissible](hyp:he0), [all fitted nuisances are
admissible](hyp:heh), [policy levels avoid boundaries](hyp:hOff), [propensity gaps
are uniformly separated](hyp:hGap), [discrete outcome gaps are uniformly separated](hyp:hOutcome),
[the regular component's level is below the terminal level](hyp:hk), [the clipping
floor is positive](hyp:hc), [all fitted level-selection denominators are at least that
floor almost everywhere](hyp:hpi), and [all fitted share-normalization denominators
are at least that floor almost everywhere](hyp:htau). If [propensity, positive-level, binary success,
and level-selection probability errors satisfy the finite nuisance rate conditions](hyp:hrp,hrlev,hrP,hrpi),
[all instrument-share errors satisfy those conditions](hyp:hrs), and [share-normalization
denominator errors satisfy them](hyp:hrt), then [the covariate mean of the fitted
regular coefficient times the fitted lower-hinge contribution plus its regression
and policy mean corrections minus the population lower-hinge contribution, multiplied
by the square root of the evaluation size, converges to zero in probability along
training sizes twice the evaluation size](goal). -/
lemma nuisanceRates_population_fractional_component_conditional_bias_root_n_negligible
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (hStruct : StructuralAssumptions M) (hend : OutcomeEndpointsKnown M)
    (hf : InstrumentFiniteReduction Z) (hy : OutcomeBinaryAE M)
    (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : PolicyOverlap M L cpi)
    (he0 : BinAdmissible M L (eta0Bin M L)) (eh : ℕ → A → NuisanceBin L)
    (heh : ∀ n a, BinAdmissible M L (eh n a))
    (hOff : PolicyLevelOffBoundary L) (gap : ℝ)
    (hGap : PropensityGapSeparationWitness M.prop (policyProp phi M.prop) gap)
    (ch : ℝ) (hOutcome : DiscreteOutcomeGapWitness M L ch)
    (r : RegularIndex L) (hk : r.val.1 < L.K) (c : ℝ) (hc : 0 < c)
    (hpi : ∀ n a i, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).piLev i x)
    (htau : ∀ n a t, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).tauLev t x)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) M.prop)
    (hrlev : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) (eta0Bin M L).pLev)
    (hrP : FiniteNuisanceRates M μ (fun n a => (eh n a).P1) (eta0Bin M L).P1)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) (eta0Bin M L).piLev)
    (hrs : ∀ t, FiniteNuisanceRates M μ (fun n a => (eh n a).share t) ((eta0Bin M L).share t))
    (hrt : FiniteNuisanceRates M μ (fun n a => (eh n a).tauLev) (eta0Bin M L).tauLev)
    :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) * ∫ x,
        regularValue (eh (2*(n+1)) a).gamma r.val.1 r.val.2 x *
          (hMinus phi L (eh (2*(n+1)) a) r.val.1 r.val.2 x +
            binaryRegularRegressionMean phi L (eta0Bin M L) (eh (2*(n+1)) a)
              r.val.1 r.val.2 x +
            binaryRegularPolicyMean M phi dphi L (eh (2*(n+1)) a) r.val.1 r.val.2 x -
            hMinus phi L (eta0Bin M L) r.val.1 r.val.2 x) ∂xLaw M)
      atTop (fun _ _ => 0) := by
  let H := fun n a x => regularValue (eh n a).gamma r.val.1 r.val.2 x *
    binaryFittedHingeRemainder
      (pooledQBin phi L (eta0Bin M L) r.val.1 r.val.2 x)
      (pooledQBin phi L (eta0Bin M L) r.val.1 (r.val.2 - 1) x)
      (positiveValue (eta0Bin M L).pLev (r.val.1 + 1) x -
        binFullJ L (eta0Bin M L) r.val.1 x)
      (pooledQBin phi L (eh n a) r.val.1 r.val.2 x)
      (pooledQBin phi L (eh n a) r.val.1 (r.val.2 - 1) x)
      (positiveValue (eh n a).pLev (r.val.1 + 1) x - binFullJ L (eh n a) r.val.1 x)
  let R := fun n a x => regularValue (eh n a).gamma r.val.1 r.val.2 x *
    (binaryRegularRegressionMean phi L (eta0Bin M L) (eh n a) r.val.1 r.val.2 x -
      Dbd phi L (eh n a) r.val.1 r.val.2 x *
        ((positiveValue (eh n a).pLev (r.val.1 + 1) x - binFullJ L (eh n a) r.val.1 x) -
          (positiveValue (eta0Bin M L).pLev (r.val.1 + 1) x -
            binFullJ L (eta0Bin M L) r.val.1 x)) -
      (if r.val.2 = 1 then Edom phi L (eh n a) r.val.1 r.val.2 x *
        Iact phi L (eh n a) r.val.1 r.val.2 x *
        (positiveValue (eh n a).pLev r.val.1 x - positiveValue (eta0Bin M L).pLev r.val.1 x)
      else 0))
  let U := fun n a x =>
    (regularValue (eh n a).gamma r.val.1 r.val.2 x * Iact phi L (eh n a) r.val.1 r.val.2 x) *
    (pooledQBin phi L (eh n a) r.val.1 r.val.2 x +
      (∑ z, instProb M z x * RqBin dphi L (eh n a) r.val.1 r.val.2 (x,z,M.prop z x,0)) -
      pooledQBin phi L (eta0Bin M L) r.val.1 r.val.2 x)
  let V := fun n a x => if r.val.2 = 1 then 0 else
    (regularValue (eh n a).gamma r.val.1 r.val.2 x * Edom phi L (eh n a) r.val.1 r.val.2 x *
      Iact phi L (eh n a) r.val.1 r.val.2 x) *
    (pooledQBin phi L (eh n a) r.val.1 (r.val.2 - 1) x +
      (∑ z, instProb M z x * RqBin dphi L (eh n a) r.val.1 (r.val.2 - 1) (x,z,M.prop z x,0)) -
      pooledQBin phi L (eta0Bin M L) r.val.1 (r.val.2 - 1) x)
  have iH (n : ℕ) (a : A) : Integrable (H n a) (xLaw M) :=
    fitted_population_binary_hinge_bias_integrable M phi hphi hStruct hend hf hy
      L hOrder hOff gap hGap cpi hov ch hOutcome he0 (eh n a) (heh n a)
      r.val.1 r.val.2 hk r.property.2
  have iR (n : ℕ) (a : A) : Integrable (R n a) (xLaw M) :=
    fitted_fractional_regression_centering_integrable M phi hphi L (eta0Bin M L)
      (eh n a) he0 (heh n a) c hc r.val.1 r.val.2 (hpi n a)
  have iU (n : ℕ) (a : A) : Integrable (U n a) (xLaw M) := by
    have hw := fitted_fractional_upper_weight_memLp_bound M phi hphi L (eh n a)
      (heh n a) r.val.1 r.val.2
    exact fitted_binary_conditional_policy_weighted_integrable M phi dphi hphi hd hDerivative
      L hOrder cpi hov he0 (eh n a) (heh n a) r c 1 hc zero_le_one (htau n a r)
      _ hw.1.1 hw.2
  have iV (n : ℕ) (a : A) : Integrable (V n a) (xLaw M) := by
    dsimp only [V]
    by_cases hj : r.val.2 = 1
    · simp only [if_pos hj]
      exact integrable_zero _ _ _
    · simp only [if_neg hj]
      have hprev : r.val.1 ≤ L.K ∧ 1 ≤ r.val.2-1 ∧ r.val.2-1 ≤ L.l r.val.1 := by
        have := r.property
        omega
      let t : RegularIndex L := ⟨(r.val.1, r.val.2-1), hprev⟩
      have hw := fitted_fractional_lower_weight_memLp_bound M phi hphi L (eh n a)
        (heh n a) r.val.1 r.val.2
      exact fitted_binary_conditional_policy_weighted_integrable M phi dphi hphi hd hDerivative
        L hOrder cpi hov he0 (eh n a) (heh n a) t c 1 hc zero_le_one (htau n a t)
        _ hw.1.1 hw.2
  have hH := nuisanceRates_population_binary_hinge_bias_root_n_negligible M μ phi dphi
    hphi hd hDerivative hStruct hend hf hy L hOrder hOff gap hGap cpi hov ch hOutcome
    he0 eh heh hrp hrlev hrP hrs r.val.1 r.val.2 hk r.property.2
  have hR := nuisanceRates_fractional_regression_centering_root_n_negligible M μ phi hphi
    L (eta0Bin M L) eh he0 heh c hc r.val.1 r.val.2 hpi hrP hrlev hrpi
  have hU := nuisanceRates_fractional_upper_policy_correction_root_n_negligible M μ
    phi dphi hphi hd hDerivative L hOrder cpi hov he0 eh heh r c hc
    (fun n a => htau n a r) hrp (hrs r) hrt
  have hV := nuisanceRates_fractional_lower_policy_correction_root_n_negligible M μ
    phi dphi hphi hd hDerivative L hOrder cpi hov he0 eh heh r c hc htau hrp hrs hrt
  have hRneg := Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt
    (show Continuous (fun t : ℝ => -t) by fun_prop).continuousAt hR
  have hUneg := Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt
    (show Continuous (fun t : ℝ => -t) by fun_prop).continuousAt hU
  have hs := ((hH.sub hRneg).sub hUneg).sub hV
  simp only [neg_zero, sub_zero, sub_neg_eq_add] at hs
  convert hs using 1
  funext n a
  have hid : (fun x => regularValue (eh (2*(n+1)) a).gamma r.val.1 r.val.2 x *
      (hMinus phi L (eh (2*(n+1)) a) r.val.1 r.val.2 x +
        binaryRegularRegressionMean phi L (eta0Bin M L) (eh (2*(n+1)) a) r.val.1 r.val.2 x +
        binaryRegularPolicyMean M phi dphi L (eh (2*(n+1)) a) r.val.1 r.val.2 x -
        hMinus phi L (eta0Bin M L) r.val.1 r.val.2 x)) =
      (fun x => H (2*(n+1)) a x + R (2*(n+1)) a x + U (2*(n+1)) a x - V (2*(n+1)) a x) := by
    funext x
    rw [fitted_fractional_component_centered_bias_eq M phi dphi L (eta0Bin M L)
      (eh (2*(n+1)) a) r.val.1 r.val.2 x]
    dsimp only [H, R, U, V]
    by_cases hj : r.val.2 = 1
    · simp only [if_pos hj]; ring
    · simp only [if_neg hj]; ring
  rw [hid, integral_sub ((iH _ a).fun_add (iR _ a) |>.fun_add (iU _ a)) (iV _ a),
    integral_add ((iH _ a).fun_add (iR _ a)) (iU _ a),
    integral_add (iH _ a) (iR _ a), mul_sub, mul_add, mul_add]

end Papers.TbsPrteOptimalTransport

module
public import Papers.TbsPrteOptimalTransport.Helpers.JointTailConditional
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationFullJointDerivative
public import Mathlib.Analysis.Calculus.MeanValue
/-! Quadratic remainders for simultaneous tail-score nuisance paths. -/
public section

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Set Filter
open scoped Topology
universe v

-- The derivative is evaluated at the fitted propensity, as in the policy residual.
-- @node: policy_debiased_quadratic_remainder
/-- If [the Lipschitz constant is nonnegative](hyp:hL), [the initial argument](hyp:ha)
and [the perturbed argument](hyp:hb) lie between zero and one, [the function has the
specified derivative throughout that interval, using derivatives within the interval
at its endpoints](hyp:hd), and [the derivative satisfies the specified Lipschitz bound](hyp:hlip),
then [the absolute difference between the perturbed function value minus the argument
displacement times the derivative at the perturbed argument and the initial function
value is at most the Lipschitz constant times the squared displacement](goal). -/
lemma policy_debiased_quadratic_remainder (f df : ℝ → ℝ) (L a b : ℝ)
    (hL : 0 ≤ L) (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    (hd : ∀ p ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (df p) (Icc 0 1) p)
    (hlip : ∀ p ∈ Icc (0 : ℝ) 1, ∀ q ∈ Icc (0 : ℝ) 1,
      |df p - df q| ≤ L * |p - q|) :
    |f b - (b-a) * df b - f a| ≤ L * (b-a)^2 := by
  have hs : uIcc a b ⊆ Icc (0 : ℝ) 1 := uIcc_subset_Icc ha hb
  have hdist : ∀ p ∈ uIcc a b, |p-b| ≤ |b-a| := by
    intro p hp
    rcases le_total a b with hab | hba
    · rw [uIcc_of_le hab] at hp
      rw [abs_of_nonpos (by linarith [hp.2]), abs_of_nonneg (by linarith)]
      linarith [hp.1]
    · rw [uIcc_of_ge hba] at hp
      rw [abs_of_nonneg (by linarith [hp.1]), abs_of_nonpos (by linarith)]
      linarith [hp.2]
  have hdg : ∀ p ∈ uIcc a b, HasDerivWithinAt
      (fun p => f p - (p-a) * df b) (df p - df b) (uIcc a b) p := by
    intro p hp
    convert! ((hd p (hs hp)).mono hs).sub
      (((hasDerivAt_id p).sub_const a).mul_const (df b)).hasDerivWithinAt using 1
    simp
  have hbound : ∀ p ∈ uIcc a b, ‖df p - df b‖ ≤ L * |b-a| := by
    intro p hp
    rw [Real.norm_eq_abs]
    exact (hlip p (hs hp) b hb).trans (mul_le_mul_of_nonneg_left (hdist p hp) hL)
  have h := (convex_uIcc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    hdg hbound left_mem_uIcc right_mem_uIcc
  simpa only [sub_self, zero_mul, sub_zero, Real.norm_eq_abs, mul_assoc,
    ← sq, sq_abs] using h

-- @node: policy_debiased_affine_remainder_bound
/-- If [the policy has the specified propensity derivative](hyp:hd), [the Lipschitz
constant is nonnegative](hyp:hL), [the derivative satisfies that uniform Lipschitz
bound on the unit interval](hyp:hlip), [the initial propensity lies in that interval](hyp:hp),
and [its affine perturbation also lies there](hyp:ht), then [the absolute change in
the policy after subtracting the path displacement times its derivative at the
perturbed propensity is at most the Lipschitz constant times the squared propensity
direction times the squared path parameter](goal). -/
lemma policy_debiased_affine_remainder_bound {X Z : Type v}
    (phi dphi : Z → X → ℝ → ℝ) (hd : PolicyDifferentiable phi dphi)
    (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ z x a b, a ∈ Icc (0 : ℝ) 1 → b ∈ Icc (0 : ℝ) 1 →
      |dphi z x a - dphi z x b| ≤ L * |a - b|)
    (z : Z) (x : X) (p dp t : ℝ)
    (hp : p ∈ Icc (0 : ℝ) 1) (ht : p + t * dp ∈ Icc (0 : ℝ) 1) :
    |phi z x (p + t * dp) - t * (dphi z x (p + t * dp) * dp) - phi z x p| ≤
      (L * dp^2) * t^2 := by
  have h := policy_debiased_quadratic_remainder (phi z x) (dphi z x) L p
    (p + t * dp) hL hp ht (hd z x) (fun a ha b hb => hlip z x a b ha hb)
  convert h using 1 <;> ring_nf

-- The denominator and signed coefficient interactions use the same exact
-- scalar identity as the full-interval product, with the opposite orientation.
-- @node: tail_baseline_joint_remainder_bound
/-- If [the denominator lower bound is positive](hyp:hc) and [the perturbed denominator
is at least that bound](hyp:hpi), then [the absolute change from the initial negative
propensity times tail weight to the negative perturbed propensity times initial tail
weight plus the path parameter times the perturbed tail-weight-to-denominator ratio
times the propensity direction and initial denominator is at most the squared path
parameter times the absolute propensity direction times the sum of the absolute
initial tail weight times the absolute denominator direction and the absolute tail-weight
direction times the absolute initial denominator, divided by the lower bound](goal). -/
lemma tail_baseline_joint_remainder_bound (p dp pi dpi g dg t c : ℝ)
    (hc : 0 < c) (hpi : c ≤ pi + t * dpi) :
    |-(p + t * dp) * g +
      t * ((g + t * dg) / (pi + t * dpi) * (dp * pi)) + p * g| ≤
      t^2 * (|dp| * (|g| * |dpi| + |dg| * |pi|) / c) := by
  have h := binary_full_joint_scalar_remainder_bound p g pi dp dg dpi t c hc hpi
  have heq : -(p + t * dp) * g +
      t * ((g + t * dg) / (pi + t * dpi) * (dp * pi)) + p * g =
      -((p + t * dp) * g + (g + t * dg) * pi * (p - (p + t * dp)) /
        (pi + t * dpi) - p * g) := by ring
  rw [heq, abs_neg]
  exact h

-- An L2 direction suffices for the integrated policy contribution. The
-- nonnegative instrument mass may depend on X; its upper bound is one.
-- @node: policy_debiased_weighted_integral_orthogonality
/-- If [the policy has the specified propensity derivative](hyp:hd), [the Lipschitz
constant is nonnegative](hyp:hLip), [the derivative satisfies that uniform Lipschitz
bound on the unit interval](hyp:hlip), [the propensity direction is square integrable](hyp:hdp),
[the mass lies between zero and one almost everywhere](hyp:hmass), [the initial
propensity does too](hyp:hp), [the affine propensity path stays in that interval
almost everywhere throughout a neighborhood of zero](hyp:hpath), [the mass-weighted
debiased policy is almost everywhere strongly measurable for path parameters near
zero](hyp:hmeas), and [the initial mass-weighted policy is integrable](hyp:hbase), then
[the integral of the mass-weighted perturbed policy minus its derivative-based path
correction has derivative zero at zero](goal). -/
lemma policy_debiased_weighted_integral_orthogonality {X Z : Type v}
    [MeasurableSpace X] (ν : Measure X)
    (phi dphi : Z → X → ℝ → ℝ) (hd : PolicyDifferentiable phi dphi)
    (Lip : ℝ) (hLip : 0 ≤ Lip)
    (hlip : ∀ z x a b, a ∈ Icc (0 : ℝ) 1 → b ∈ Icc (0 : ℝ) 1 →
      |dphi z x a - dphi z x b| ≤ Lip * |a - b|)
    (z : Z) (p dp mass : X → ℝ) (hdp : MemLp dp 2 ν)
    (hmass : ∀ᵐ x ∂ν, mass x ∈ Icc (0 : ℝ) 1)
    (hp : ∀ᵐ x ∂ν, p x ∈ Icc (0 : ℝ) 1)
    (hpath : ∀ᶠ t : ℝ in nhds 0, ∀ᵐ x ∂ν, p x + t * dp x ∈ Icc (0 : ℝ) 1)
    (hmeas : ∀ᶠ t : ℝ in nhds 0, AEStronglyMeasurable (fun x => mass x *
      (phi z x (p x + t * dp x) - t * (dphi z x (p x + t * dp x) * dp x))) ν)
    (hbase : Integrable (fun x => mass x * phi z x (p x)) ν) :
    HasDerivAt (fun t : ℝ => ∫ x, mass x *
      (phi z x (p x + t * dp x) - t * (dphi z x (p x + t * dp x) * dp x)) ∂ν) 0 0 := by
  let F : ℝ → X → ℝ := fun t x => mass x *
    (phi z x (p x + t * dp x) - t * (dphi z x (p x + t * dp x) * dp x))
  have h0 : F 0 = fun x => mass x * phi z x (p x) := by
    funext x
    simp only [F, zero_mul, add_zero, sub_zero]
  have hbound : ∀ᶠ t : ℝ in nhds 0,
      |(∫ x, F t x ∂ν) - ∫ x, F 0 x ∂ν| ≤ (Lip * ∫ x, (dp x)^2 ∂ν) * t^2 := by
    filter_upwards [hpath, hmeas] with t ht hm
    have hb : ∀ᵐ x ∂ν, |F t x - F 0 x| ≤ (Lip * t^2) * (dp x)^2 := by
      filter_upwards [ht, hp, hmass] with x hx hpx hmx
      have h := policy_debiased_affine_remainder_bound phi dphi hd Lip hLip hlip
        z x (p x) (dp x) t hpx hx
      simp only [F, zero_mul, add_zero, sub_zero]
      rw [← mul_sub, abs_mul, abs_of_nonneg hmx.1]
      calc
        _ ≤ mass x * ((Lip * (dp x)^2) * t^2) :=
          mul_le_mul_of_nonneg_left h hmx.1
        _ ≤ 1 * ((Lip * (dp x)^2) * t^2) :=
          mul_le_mul_of_nonneg_right hmx.2 (by positivity)
        _ = _ := by ring
    have hdom : Integrable (fun x => (Lip * t^2) * (dp x)^2) ν :=
      hdp.integrable_sq.const_mul _
    have hi0 : Integrable (F 0) ν := by rw [h0]; exact hbase
    have hir : Integrable (fun x => F t x - F 0 x) ν :=
      hdom.mono' (hm.sub hi0.aestronglyMeasurable)
        (by simpa only [Real.norm_eq_abs] using hb)
    have hit : Integrable (F t) ν := by
      convert! hir.fun_add hi0 using 1
      funext x
      ring
    rw [← integral_sub hit hi0]
    calc
      _ ≤ ∫ x, |F t x - F 0 x| ∂ν := by
        simpa only [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (fun x => F t x - F 0 x)
      _ ≤ ∫ x, (Lip * t^2) * (dp x)^2 ∂ν := integral_mono_ae hir.abs hdom hb
      _ = _ := by rw [integral_const_mul]; ring
  have ho : (fun t : ℝ => (∫ x, F t x ∂ν) - ∫ x, F 0 x ∂ν)
      =O[nhds 0] (fun t => t^2) := by
    apply Asymptotics.IsBigO.of_bound (Lip * ∫ x, (dp x)^2 ∂ν)
    filter_upwards [hbound] with t ht
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)] using ht
  apply HasDerivAt.of_isLittleO
  simpa only [F, smul_zero, sub_zero] using
    ho.trans_isLittleO (Asymptotics.isLittleO_pow_id (𝕜 := ℝ) (by norm_num : 1 < 2))

-- @node: tail_joint_finite_mean_remainder_bound
/-- If [the policy has the specified propensity derivative](hyp:hd), [the Lipschitz
constant is nonnegative](hyp:hLip), [the derivative satisfies that uniform Lipschitz
bound on the unit interval](hyp:hlip), [the denominator lower bound is positive](hyp:hc),
[the perturbed denominator is at least that bound](hyp:hpi), [the finite instrument
masses are nonnegative](hyp:hmass), [the initial propensities lie between zero and one](hyp:hp),
and [their affine perturbations also lie there](hyp:ht), then [the absolute change in
the outcome-floor-scaled finite debiased-policy sum with its joint baseline correction
is at most the squared path parameter times the absolute outcome floor times the sum
of the mass-weighted Lipschitz constant times squared policy directions and the
absolute baseline propensity direction times the sum of the absolute initial tail
weight times the absolute denominator direction and the absolute tail-weight
direction times the absolute initial denominator, divided by the denominator lower bound](goal). -/
lemma tail_joint_finite_mean_remainder_bound {X Z : Type v}
    (phi dphi : Z → X → ℝ → ℝ) (hd : PolicyDifferentiable phi dphi)
    (Lip : ℝ) (hLip : 0 ≤ Lip)
    (hlip : ∀ z x a b, a ∈ Icc (0 : ℝ) 1 → b ∈ Icc (0 : ℝ) 1 →
      |dphi z x a - dphi z x b| ≤ Lip * |a - b|)
    (s : Finset Z) (x : X) (p dp mass : Z → ℝ)
    (pk dpk pi dpi g dg ymin t c : ℝ)
    (hc : 0 < c) (hpi : c ≤ pi + t * dpi)
    (hmass : ∀ z ∈ s, 0 ≤ mass z)
    (hp : ∀ z ∈ s, p z ∈ Icc (0 : ℝ) 1)
    (ht : ∀ z ∈ s, p z + t * dp z ∈ Icc (0 : ℝ) 1) :
    |ymin * ((∑ z ∈ s, mass z * (phi z x (p z + t * dp z) -
        t * (dphi z x (p z + t * dp z) * dp z))) -
      (pk + t * dpk) * g + t * ((g + t * dg) / (pi + t * dpi) * (dpk * pi))) -
      ymin * ((∑ z ∈ s, mass z * phi z x (p z)) - pk * g)| ≤
    (|ymin| * ((∑ z ∈ s, mass z * (Lip * (dp z)^2)) +
      |dpk| * (|g| * |dpi| + |dg| * |pi|) / c)) * t^2 := by
  classical
  let r : Z → ℝ := fun z => mass z * (phi z x (p z + t * dp z) -
    t * (dphi z x (p z + t * dp z) * dp z) - phi z x (p z))
  have hr : |∑ z ∈ s, r z| ≤ (∑ z ∈ s, mass z * (Lip * (dp z)^2)) * t^2 := by
    calc
      _ ≤ ∑ z ∈ s, |r z| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ z ∈ s, mass z * (Lip * (dp z)^2) * t^2 := by
        apply Finset.sum_le_sum
        intro z hz
        dsimp only [r]
        rw [abs_mul, abs_of_nonneg (hmass z hz)]
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
          (policy_debiased_affine_remainder_bound phi dphi hd Lip hLip hlip
            z x (p z) (dp z) t (hp z hz) (ht z hz)) (hmass z hz)
      _ = _ := by rw [Finset.sum_mul]
  have hb := tail_baseline_joint_remainder_bound pk dpk pi dpi g dg t c hc hpi
  have heq : ymin * ((∑ z ∈ s, mass z * (phi z x (p z + t * dp z) -
        t * (dphi z x (p z + t * dp z) * dp z))) -
      (pk + t * dpk) * g + t * ((g + t * dg) / (pi + t * dpi) * (dpk * pi))) -
      ymin * ((∑ z ∈ s, mass z * phi z x (p z)) - pk * g) =
      ymin * ((∑ z ∈ s, r z) + (-(pk + t * dpk) * g +
        t * ((g + t * dg) / (pi + t * dpi) * (dpk * pi)) + pk * g)) := by
    dsimp only [r]
    simp_rw [mul_sub]
    simp_rw [Finset.sum_sub_distrib]
    ring
  rw [heq, abs_mul]
  calc
    _ ≤ |ymin| * (|∑ z ∈ s, r z| + |-(pk + t * dpk) * g +
        t * ((g + t * dg) / (pi + t * dpi) * (dpk * pi)) + pk * g|) :=
      mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg ymin)
    _ ≤ |ymin| * ((∑ z ∈ s, mass z * (Lip * (dp z)^2)) * t^2 +
        t^2 * (|dpk| * (|g| * |dpi| + |dg| * |pi|) / c)) :=
      mul_le_mul_of_nonneg_left (add_le_add hr hb) (abs_nonneg ymin)
    _ = _ := by ring

universe u
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- This is a bound on the actual score's conditional mean, rather than only
-- the plug-in tail functional. All nuisance fields may move simultaneously.
-- @node: commonTailScore_joint_conditional_remainder_bound
/-- Suppose [the policy has the specified propensity derivative](hyp:hd), [the Lipschitz
constant is nonnegative](hyp:hLip), [the derivative satisfies that uniform Lipschitz
bound on the unit interval](hyp:hlip), [there is at least one level](hyp:hK), [final-level
propensities equal the final baseline propensity](hyp:hlevel), [final-level masses sum
to the assignment denominator](hyp:hpi), and [tail-region masses sum to the tail weight](hyp:hg).
If [the denominator lower bound is positive](hyp:hc), [the perturbed final denominator
is at least that bound](hyp:hden), [tail-region masses are nonnegative](hyp:hmass),
[initial tail-region propensities lie between zero and one](hyp:hp), and [their affine
perturbations also lie there](hyp:ht), then [the absolute change in the finite weighted
mean of the common tail score, holding treatment at its initial propensity, is at
most the squared path parameter times the absolute outcome floor times the sum of
the tail-region mass-weighted Lipschitz constant times squared propensity directions
and the absolute final-level propensity direction times the sum of the absolute
initial tail weight times the absolute final denominator direction and the absolute
tail-weight direction times the absolute initial final denominator, divided by the
denominator lower bound](goal). -/
lemma commonTailScore_joint_conditional_remainder_bound
    (phi dphi : Z → X → ℝ → ℝ) (hd : PolicyDifferentiable phi dphi)
    (Lip : ℝ) (hLip : 0 ≤ Lip)
    (hlip : ∀ z x a b, a ∈ Icc (0 : ℝ) 1 → b ∈ Icc (0 : ℝ) 1 →
      |dphi z x a - dphi z x b| ≤ Lip * |a - b|)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (prop dp : Z → X → ℝ) (pk dpk pi dpi : PositiveIndex L.K → X → ℝ)
    (g dg : X → ℝ) (x : X) (mass : Z → ℝ) (t c : ℝ)
    (hlevel : ∀ z ∈ L.S L.K, prop z x = positiveValue pk L.K x)
    (hpi : ∑ z ∈ L.S L.K, mass z = positiveValue pi L.K x)
    (hg : ∑ z ∈ policyUnion L L.K 1, mass z = g x)
    (hc : 0 < c)
    (hden : c ≤ positiveValue pi L.K x + t * positiveValue dpi L.K x)
    (hmass : ∀ z ∈ policyUnion L L.K 1, 0 ≤ mass z)
    (hp : ∀ z ∈ policyUnion L L.K 1, prop z x ∈ Icc (0 : ℝ) 1)
    (ht : ∀ z ∈ policyUnion L L.K 1, prop z x + t * dp z x ∈ Icc (0 : ℝ) 1) :
    |(∑ z, mass z * commonTailScore M phi dphi L
        (fun z x => prop z x + t * dp z x)
        (fun k x => pk k x + t * dpk k x)
        (fun k x => pi k x + t * dpi k x)
        (fun x => g x + t * dg x) (x, z, prop z x, 0)) -
      (∑ z, mass z * commonTailScore M phi dphi L
        prop pk pi g (x, z, prop z x, 0))| ≤
    (|M.yMin| * ((∑ z ∈ policyUnion L L.K 1, mass z * (Lip * (dp z x)^2)) +
      |positiveValue dpk L.K x| * (|g x| * |positiveValue dpi L.K x| +
        |dg x| * |positiveValue pi L.K x|) / c)) * t^2 := by
  have h0 := commonTailScore_joint_finite_conditional_mean M phi dphi L hK
    prop dp pk dpk pi dpi g dg x mass 0 hlevel hpi hg
  simp only [zero_mul, add_zero, sub_zero] at h0
  rw [commonTailScore_joint_finite_conditional_mean M phi dphi L hK
    prop dp pk dpk pi dpi g dg x mass t hlevel hpi hg, h0]
  exact tail_joint_finite_mean_remainder_bound phi dphi hd Lip hLip hlip
    (policyUnion L L.K 1) x (fun z => prop z x) (fun z => dp z x) mass
    (positiveValue pk L.K x) (positiveValue dpk L.K x)
    (positiveValue pi L.K x) (positiveValue dpi L.K x) (g x) (dg x) M.yMin t c
    hc hden hmass hp ht

end Papers.TbsPrteOptimalTransport

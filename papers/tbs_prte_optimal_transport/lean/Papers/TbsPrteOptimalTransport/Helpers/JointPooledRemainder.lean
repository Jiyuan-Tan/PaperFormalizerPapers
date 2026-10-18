module
public import Papers.TbsPrteOptimalTransport.Helpers.JointTailRemainder
/-! Quadratic pooled-policy remainders with moving simplex shares and denominators. -/
public section

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Set Filter
open scoped Classical Topology
universe v

-- @node: policy_bounded_derivative_increment
/-- If [the initial argument](hyp:ha) and [the final argument](hyp:hb) lie in
the unit interval, [the function has the specified derivative within that
interval](hyp:hd), and [the derivative's absolute value is bounded by B](hyp:hbound),
then [the absolute change in the function is at most B times the distance between
the arguments](goal). -/
lemma policy_bounded_derivative_increment (f df : ℝ → ℝ) (B a b : ℝ)
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    (hd : ∀ p ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (df p) (Icc 0 1) p)
    (hbound : ∀ p ∈ Icc (0 : ℝ) 1, |df p| ≤ B) :
    |f b - f a| ≤ B * |b-a| := by
  have hs : uIcc a b ⊆ Icc (0 : ℝ) 1 := uIcc_subset_Icc ha hb
  simpa only [Real.norm_eq_abs] using
    (convex_uIcc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun p hp => (hd p (hs hp)).mono hs)
      (fun p hp => by simpa only [Real.norm_eq_abs] using hbound p (hs hp))
      left_mem_uIcc right_mem_uIcc

-- The standalone share term vanishes by the simplex constraint and the common
-- policy level. The remaining share and denominator terms are products of errors.
-- @node: pooled_policy_joint_remainder_identity
/-- If [the perturbed pooled denominator is nonzero](hyp:htau), [instrument
masses equal baseline shares times the baseline denominator](hyp:ha), [baseline
policy values coincide across the pool](hyp:hcommon), and [share directions sum
to zero](hyp:hsimplex), then [the change in the debiased pooled value equals the
sum of the baseline-share-weighted policy remainders, the path parameter times
the share-direction-weighted policy increments, and the squared path parameter
times the denominator direction divided by the perturbed denominator times the
baseline-share-weighted derivative-direction products](goal). -/
lemma pooled_policy_joint_remainder_identity {Z : Type v}
    (s : Finset Z) (a da mass f f0 df dp : Z → ℝ) (q tau dtau t : ℝ)
    (htau : tau + t * dtau ≠ 0)
    (ha : ∀ z ∈ s, mass z = a z * tau)
    (hcommon : ∀ z ∈ s, f0 z = q) (hsimplex : ∑ z ∈ s, da z = 0) :
    (∑ z ∈ s, (a z + t * da z) * f z) -
        t * ((tau + t * dtau)⁻¹ * ∑ z ∈ s, mass z * df z * dp z) -
        (∑ z ∈ s, a z * f0 z) =
      (∑ z ∈ s, a z * (f z - t * (df z * dp z) - f0 z)) +
      t * (∑ z ∈ s, da z * (f z - f0 z)) +
      t^2 * (dtau / (tau + t * dtau) * ∑ z ∈ s, a z * df z * dp z) := by
  have hz : ∑ z ∈ s, da z * f0 z = 0 := by
    calc
      _ = ∑ z ∈ s, da z * q := Finset.sum_congr rfl (fun z hz => by rw [hcommon z hz])
      _ = 0 := by rw [← Finset.sum_mul, hsimplex, zero_mul]
  have hm : (∑ z ∈ s, mass z * df z * dp z) =
      tau * ∑ z ∈ s, a z * df z * dp z := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z hz
    rw [ha z hz]
    ring
  rw [hm]
  simp_rw [add_mul, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hta : (∑ z ∈ s, t * da z * f z) = t * ∑ z ∈ s, da z * f z := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z hz
    ring
  have htf : (∑ z ∈ s, a z * (t * (df z * dp z))) =
      t * ∑ z ∈ s, a z * df z * dp z := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z hz
    ring
  rw [hta, htf]
  rw [hz]
  field_simp [htau]
  <;> ring

-- @node: pooled_policy_debiased_joint_remainder_bound
/-- Suppose [the policy has the specified derivative](hyp:hd), [B](hyp:hB) and
[the Lipschitz constant](hyp:hLip) are nonnegative, [the derivative is bounded in
absolute value by B on the unit interval](hyp:hbound), and [its changes are bounded
by the Lipschitz constant times argument changes there](hyp:hlip). If [c is
positive](hyp:hc), [the perturbed denominator is at least c](hyp:hden), [masses
equal baseline shares times the baseline denominator](hyp:ha), [baseline](hyp:hp)
and [perturbed propensities](hyp:ht) lie in the unit interval, [baseline policy
values are common across the pool](hyp:hcommon), and [share directions sum to
zero](hyp:hsimplex), then [the absolute debiased pooled increment is bounded by
the squared path parameter times the sum of three terms: absolute-share-weighted
squared propensity directions times the Lipschitz constant, absolute share and
propensity direction products times B, and the absolute denominator direction
divided by c times the absolute-share-weighted propensity directions times B](goal). -/
lemma pooled_policy_debiased_joint_remainder_bound {X Z : Type v}
    (phi dphi : Z → X → ℝ → ℝ) (hd : PolicyDifferentiable phi dphi)
    (B Lip : ℝ) (hB : 0 ≤ B) (hLip : 0 ≤ Lip)
    (hbound : ∀ z x p, p ∈ Icc (0 : ℝ) 1 → |dphi z x p| ≤ B)
    (hlip : ∀ z x p r, p ∈ Icc (0 : ℝ) 1 → r ∈ Icc (0 : ℝ) 1 →
      |dphi z x p - dphi z x r| ≤ Lip * |p-r|)
    (s : Finset Z) (x : X) (p dp a da mass : Z → ℝ) (q tau dtau t c : ℝ)
    (hc : 0 < c) (hden : c ≤ tau + t * dtau)
    (ha : ∀ z ∈ s, mass z = a z * tau)
    (hp : ∀ z ∈ s, p z ∈ Icc (0 : ℝ) 1)
    (ht : ∀ z ∈ s, p z + t * dp z ∈ Icc (0 : ℝ) 1)
    (hcommon : ∀ z ∈ s, phi z x (p z) = q)
    (hsimplex : ∑ z ∈ s, da z = 0) :
    |(∑ z ∈ s, (a z + t * da z) * phi z x (p z + t * dp z)) -
        t * ((tau + t * dtau)⁻¹ *
          ∑ z ∈ s, mass z * dphi z x (p z + t * dp z) * dp z) -
        (∑ z ∈ s, a z * phi z x (p z))| ≤
      ((∑ z ∈ s, |a z| * (Lip * (dp z)^2)) +
        (∑ z ∈ s, |da z| * (B * |dp z|)) +
        |dtau| / c * (∑ z ∈ s, |a z| * B * |dp z|)) * t^2 := by
  have hpos : 0 < tau + t * dtau := hc.trans_le hden
  rw [pooled_policy_joint_remainder_identity s a da mass
    (fun z => phi z x (p z + t * dp z)) (fun z => phi z x (p z))
    (fun z => dphi z x (p z + t * dp z)) dp q tau dtau t hpos.ne'
    ha hcommon hsimplex]
  have hfirst : |∑ z ∈ s, a z * (phi z x (p z + t * dp z) -
      t * (dphi z x (p z + t * dp z) * dp z) - phi z x (p z))| ≤
      (∑ z ∈ s, |a z| * (Lip * (dp z)^2)) * t^2 := by
    calc
      _ ≤ ∑ z ∈ s, |a z * (phi z x (p z + t * dp z) -
          t * (dphi z x (p z + t * dp z) * dp z) - phi z x (p z))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ z ∈ s, |a z| * (Lip * (dp z)^2) * t^2 := by
        apply Finset.sum_le_sum
        intro z hz
        rw [abs_mul]
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
          (policy_debiased_affine_remainder_bound phi dphi hd Lip hLip hlip
            z x (p z) (dp z) t (hp z hz) (ht z hz)) (abs_nonneg (a z))
      _ = _ := (Finset.sum_mul ..).symm
  have hshare : |t * ∑ z ∈ s, da z *
      (phi z x (p z + t * dp z) - phi z x (p z))| ≤
      (∑ z ∈ s, |da z| * (B * |dp z|)) * t^2 := by
    have hi (z) (hz : z ∈ s) :
        |phi z x (p z + t * dp z) - phi z x (p z)| ≤ B * (|t| * |dp z|) := by
      simpa only [add_sub_cancel_left, abs_mul] using
        policy_bounded_derivative_increment (phi z x) (dphi z x) B (p z)
          (p z + t * dp z) (hp z hz) (ht z hz) (hd z x) (hbound z x)
    rw [abs_mul]
    calc
      _ ≤ |t| * ∑ z ∈ s, |da z *
          (phi z x (p z + t * dp z) - phi z x (p z))| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg t)
      _ ≤ |t| * ∑ z ∈ s, (|da z| * (B * |dp z|)) * |t| := by
        gcongr with z hz
        rw [abs_mul]
        calc
          _ ≤ |da z| * (B * (|t| * |dp z|)) :=
            mul_le_mul_of_nonneg_left (hi z hz) (abs_nonneg _)
          _ = _ := by ring
      _ = _ := by rw [← Finset.sum_mul, mul_left_comm, ← sq, sq_abs]
  have hsum : |∑ z ∈ s, a z * dphi z x (p z + t * dp z) * dp z| ≤
      ∑ z ∈ s, |a z| * B * |dp z| := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro z hz
    simp only [abs_mul]
    gcongr
    exact hbound z x _ (ht z hz)
  have hdenom : |t^2 * (dtau / (tau + t * dtau) *
      ∑ z ∈ s, a z * dphi z x (p z + t * dp z) * dp z)| ≤
      (|dtau| / c * ∑ z ∈ s, |a z| * B * |dp z|) * t^2 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg t), abs_mul, abs_div, abs_of_pos hpos]
    calc
      _ ≤ t^2 * (|dtau| / c * ∑ z ∈ s, |a z| * B * |dp z|) := by
        gcongr
      _ = _ := by ring
  calc
    _ ≤ (|∑ z ∈ s, a z * (phi z x (p z + t * dp z) -
        t * (dphi z x (p z + t * dp z) * dp z) - phi z x (p z))| +
      |t * ∑ z ∈ s, da z * (phi z x (p z + t * dp z) - phi z x (p z))|) +
      |t^2 * (dtau / (tau + t * dtau) *
        ∑ z ∈ s, a z * dphi z x (p z + t * dp z) * dp z)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := by nlinarith [hfirst, hshare, hdenom]

-- This is the pooled level plus the actual finite conditional policy residual;
-- every field of the affine nuisance vector is allowed to move.
-- @node: pooledQBin_joint_conditional_remainder_bound
/-- Suppose [the policy has the specified derivative](hyp:hd), [B](hyp:hB) and
[the Lipschitz constant](hyp:hLip) are nonnegative, and [the derivative is bounded
by B](hyp:hbound) and [Lipschitz on the unit interval](hyp:hlip). If [c is
positive](hyp:hc), [the baseline pooled denominator is nonzero](hyp:htau), [the
perturbed denominator is at least c](hyp:hden), [baseline shares are normalized
instrument masses](hyp:hshare), [baseline](hyp:hp) and [perturbed propensities](hyp:ht)
lie in the unit interval, [baseline policy values equal the common level](hyp:hcommon),
and [share directions sum to zero](hyp:hsimplex), then [the perturbed pooled level
plus its finite conditional residual differs from the baseline pooled level by
at most the squared path parameter times the sum of the share-weighted squared
propensity directions times the Lipschitz constant, absolute share-propensity
direction products times B, and the absolute denominator direction divided by c
times the share-weighted absolute propensity directions times B](goal). -/
lemma pooledQBin_joint_conditional_remainder_bound {X Z : Type v}
    [Fintype Z] [DecidableEq Z]
    (phi dphi : Z → X → ℝ → ℝ) (hd : PolicyDifferentiable phi dphi)
    (B Lip : ℝ) (hB : 0 ≤ B) (hLip : 0 ≤ Lip)
    (hbound : ∀ z x p, p ∈ Icc (0 : ℝ) 1 → |dphi z x p| ≤ B)
    (hlip : ∀ z x p r, p ∈ Icc (0 : ℝ) 1 → r ∈ Icc (0 : ℝ) 1 →
      |dphi z x p - dphi z x r| ≤ Lip * |p-r|)
    (L : LevelData Z X) (e del : NuisanceBin L) (a : RegularIndex L)
    (x : X) (mass : Z → ℝ) (t c : ℝ) (hc : 0 < c)
    (htau : e.tauLev a x ≠ 0) (hden : c ≤ e.tauLev a x + t * del.tauLev a x)
    (hshare : ∀ z ∈ L.T a.val.1 a.val.2, e.share a z x = mass z / e.tauLev a x)
    (hp : ∀ z ∈ L.T a.val.1 a.val.2, e.prop z x ∈ Icc (0 : ℝ) 1)
    (ht : ∀ z ∈ L.T a.val.1 a.val.2, e.prop z x + t * del.prop z x ∈ Icc (0 : ℝ) 1)
    (hcommon : ∀ z ∈ L.T a.val.1 a.val.2,
      phi z x (e.prop z x) = L.qLev a.val.1 a.val.2 x)
    (hsimplex : ∑ z ∈ L.T a.val.1 a.val.2, del.share a z x = 0) :
    |pooledQBin phi L (e + t • del) a.val.1 a.val.2 x +
        (∑ z, mass z * RqBin dphi L (e + t • del) a.val.1 a.val.2
          (x, z, e.prop z x, 0)) - pooledQBin phi L e a.val.1 a.val.2 x| ≤
      ((∑ z ∈ L.T a.val.1 a.val.2, |e.share a z x| * (Lip * (del.prop z x)^2)) +
        (∑ z ∈ L.T a.val.1 a.val.2, |del.share a z x| * (B * |del.prop z x|)) +
        |del.tauLev a x| / c *
          (∑ z ∈ L.T a.val.1 a.val.2, |e.share a z x| * B * |del.prop z x|)) * t^2 := by
  have hj0 : a.val.2 ≠ 0 := by have := a.property; omega
  have hj : ¬ L.l a.val.1 < a.val.2 := not_lt.mpr a.property.2.2
  have hbad : ¬ (a.val.2 = 0 ∨ L.l a.val.1 < a.val.2) := by omega
  have ha : ∀ z ∈ L.T a.val.1 a.val.2, mass z = e.share a z x * e.tauLev a x := by
    intro z hz
    rw [hshare z hz, div_mul_cancel₀ _ htau]
  have hb := pooled_policy_debiased_joint_remainder_bound phi dphi hd B Lip hB hLip
    hbound hlip (L.T a.val.1 a.val.2) x (fun z => e.prop z x)
    (fun z => del.prop z x) (fun z => e.share a z x) (fun z => del.share a z x)
    mass (L.qLev a.val.1 a.val.2 x) (e.tauLev a x) (del.tauLev a x) t c
    hc hden ha hp ht hcommon hsimplex
  rw [RqBin_finite_conditional_mean]
  simp only [pooledQBin, if_neg hj0, if_neg hj, if_neg hbad,
    regularValue, dif_pos a.property]
  change |(∑ z ∈ L.T a.val.1 a.val.2,
      (e.share a z x + t * del.share a z x) * phi z x (e.prop z x + t * del.prop z x)) +
    (e.tauLev a x + t * del.tauLev a x)⁻¹ *
      (∑ z ∈ L.T a.val.1 a.val.2, mass z * dphi z x (e.prop z x + t * del.prop z x) *
        (e.prop z x - (e.prop z x + t * del.prop z x))) -
    (∑ z ∈ L.T a.val.1 a.val.2, e.share a z x * phi z x (e.prop z x))| ≤ _
  have hsum : (∑ z ∈ L.T a.val.1 a.val.2,
      mass z * dphi z x (e.prop z x + t * del.prop z x) *
        (e.prop z x - (e.prop z x + t * del.prop z x))) =
      -t * ∑ z ∈ L.T a.val.1 a.val.2,
        mass z * dphi z x (e.prop z x + t * del.prop z x) * del.prop z x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z hz
    ring
  rw [hsum]
  convert hb using 1
  congr 1
  ring

-- Products of two L2 directions are integrable; no bounded direction is needed.
-- @node: pooled_policy_joint_L2_envelope_integrable
/-- If [each propensity direction in the finite pool is square integrable](hyp:hp),
[each share direction in that pool is square integrable](hyp:ha), and [the
denominator direction is square integrable](hyp:htau), then [the finite sum of
the Lipschitz constant times squared propensity directions, B times absolute
share-propensity direction products, and B divided by c times absolute
denominator-propensity direction products is integrable](goal). -/
lemma pooled_policy_joint_L2_envelope_integrable {X Z : Type v} [MeasurableSpace X]
    (ν : Measure X) (s : Finset Z) (dp da : Z → X → ℝ) (dtau : X → ℝ)
    (B Lip c : ℝ) (hp : ∀ z ∈ s, MemLp (dp z) 2 ν)
    (ha : ∀ z ∈ s, MemLp (da z) 2 ν) (htau : MemLp dtau 2 ν) :
    Integrable (fun x => ∑ z ∈ s, (Lip * (dp z x)^2 +
      B * |da z x * dp z x| + (B/c) * |dtau x * dp z x|)) ν := by
  apply integrable_finsetSum
  intro z hz
  exact ((hp z hz).integrable_sq.const_mul Lip).fun_add
    (((ha z hz).integrable_mul (hp z hz)).abs.const_mul B) |>.fun_add
      ((htau.integrable_mul (hp z hz)).abs.const_mul (B/c))

-- The true simplex shares are bounded by one. This removes them from the
-- envelope, leaving only squares and pairwise products of nuisance directions.
-- @node: pooled_policy_joint_remainder_envelope_le
/-- If [B](hyp:hB) and [the Lipschitz constant](hyp:hLip) are nonnegative,
[c is positive](hyp:hc), and [every baseline share has absolute value at most
one](hyp:ha), then [the pooled remainder coefficient is bounded above by the
sum of the Lipschitz constant times squared propensity directions, B times
absolute share-propensity direction products, and B divided by c times absolute
denominator-propensity direction products](goal). -/
lemma pooled_policy_joint_remainder_envelope_le {Z : Type v}
    (s : Finset Z) (a da dp : Z → ℝ) (dtau B Lip c : ℝ)
    (hB : 0 ≤ B) (hLip : 0 ≤ Lip) (hc : 0 < c)
    (ha : ∀ z ∈ s, |a z| ≤ 1) :
    (∑ z ∈ s, |a z| * (Lip * (dp z)^2)) +
      (∑ z ∈ s, |da z| * (B * |dp z|)) +
      |dtau| / c * (∑ z ∈ s, |a z| * B * |dp z|) ≤
      ∑ z ∈ s, (Lip * (dp z)^2 + B * |da z * dp z| + (B/c) * |dtau * dp z|) := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro z hz
  simp only [abs_mul]
  have hsq : |a z| * (Lip * (dp z)^2) ≤ Lip * (dp z)^2 := by
    exact mul_le_of_le_one_left (by positivity) (ha z hz)
  have hden : |dtau| / c * (|a z| * B * |dp z|) ≤
      (B/c) * (|dtau| * |dp z|) := by
    calc
      _ ≤ |dtau| / c * (1 * B * |dp z|) := by gcongr; exact ha z hz
      _ = _ := by ring
  nlinarith [hsq, hden]

-- The explicit quadratic envelope is integrated first. Pointwise conditional
-- derivatives alone would not justify this population derivative.
-- @node: pooled_policy_debiased_joint_integral_orthogonality
/-- Suppose [the policy has the specified derivative](hyp:hd), [B](hyp:hB) and
[the Lipschitz constant](hyp:hLip) are nonnegative, and [the derivative is bounded
by B](hyp:hbound) and [Lipschitz on the unit interval](hyp:hlip). Assume [c is
positive](hyp:hc), [propensity directions](hyp:hdp), [share directions](hyp:hda),
and [the denominator direction](hyp:hdtau) are square integrable, and [the
baseline pooled value is integrable](hyp:hbase). If [almost everywhere baseline
masses equal shares times the denominator, absolute shares are at most one,
propensities lie in the unit interval, policy values are common, and share
directions sum to zero](hyp:horigin), [near zero the perturbed denominator is at
least c and perturbed propensities remain in the unit interval almost
everywhere](hyp:hpath), and [the debiased pooled value is almost everywhere
strongly measurable near zero](hyp:hmeas), then [its integral has derivative zero
at zero along the joint affine path](goal). -/
lemma pooled_policy_debiased_joint_integral_orthogonality {X Z : Type v}
    [MeasurableSpace X] (ν : Measure X)
    (phi dphi : Z → X → ℝ → ℝ) (hd : PolicyDifferentiable phi dphi)
    (B Lip : ℝ) (hB : 0 ≤ B) (hLip : 0 ≤ Lip)
    (hbound : ∀ z x p, p ∈ Icc (0 : ℝ) 1 → |dphi z x p| ≤ B)
    (hlip : ∀ z x p r, p ∈ Icc (0 : ℝ) 1 → r ∈ Icc (0 : ℝ) 1 →
      |dphi z x p - dphi z x r| ≤ Lip * |p-r|)
    (s : Finset Z) (p dp a da mass : Z → X → ℝ) (q tau dtau : X → ℝ)
    (c : ℝ) (hc : 0 < c)
    (hdp : ∀ z ∈ s, MemLp (dp z) 2 ν)
    (hda : ∀ z ∈ s, MemLp (da z) 2 ν) (hdtau : MemLp dtau 2 ν)
    (hbase : Integrable (fun x => ∑ z ∈ s, a z x * phi z x (p z x)) ν)
    (horigin : ∀ᵐ x ∂ν, (∀ z ∈ s, mass z x = a z x * tau x ∧
      |a z x| ≤ 1 ∧ p z x ∈ Icc (0 : ℝ) 1 ∧ phi z x (p z x) = q x) ∧
      ∑ z ∈ s, da z x = 0)
    (hpath : ∀ᶠ t : ℝ in nhds 0, ∀ᵐ x ∂ν,
      c ≤ tau x + t * dtau x ∧ ∀ z ∈ s, p z x + t * dp z x ∈ Icc (0 : ℝ) 1)
    (hmeas : ∀ᶠ t : ℝ in nhds 0, AEStronglyMeasurable (fun x =>
      (∑ z ∈ s, (a z x + t * da z x) * phi z x (p z x + t * dp z x)) -
        t * ((tau x + t * dtau x)⁻¹ *
          ∑ z ∈ s, mass z x * dphi z x (p z x + t * dp z x) * dp z x)) ν) :
    HasDerivAt (fun t : ℝ => ∫ x,
      (∑ z ∈ s, (a z x + t * da z x) * phi z x (p z x + t * dp z x)) -
        t * ((tau x + t * dtau x)⁻¹ *
          ∑ z ∈ s, mass z x * dphi z x (p z x + t * dp z x) * dp z x) ∂ν) 0 0 := by
  let F : ℝ → X → ℝ := fun t x =>
    (∑ z ∈ s, (a z x + t * da z x) * phi z x (p z x + t * dp z x)) -
      t * ((tau x + t * dtau x)⁻¹ *
        ∑ z ∈ s, mass z x * dphi z x (p z x + t * dp z x) * dp z x)
  let E : X → ℝ := fun x => ∑ z ∈ s, (Lip * (dp z x)^2 +
    B * |da z x * dp z x| + (B/c) * |dtau x * dp z x|)
  have hiE : Integrable E ν :=
    pooled_policy_joint_L2_envelope_integrable ν s dp da dtau B Lip c hdp hda hdtau
  have h0 : F 0 = fun x => ∑ z ∈ s, a z x * phi z x (p z x) := by
    funext x
    simp only [F, zero_mul, add_zero, sub_zero]
  have hi0 : Integrable (F 0) ν := by rw [h0]; exact hbase
  have hboundInt : ∀ᶠ t : ℝ in nhds 0,
      |(∫ x, F t x ∂ν) - ∫ x, F 0 x ∂ν| ≤ (∫ x, E x ∂ν) * t^2 := by
    filter_upwards [hpath, hmeas] with t ht hm
    have hb : ∀ᵐ x ∂ν, |F t x - F 0 x| ≤ E x * t^2 := by
      filter_upwards [horigin, ht] with x hx htx
      have h := pooled_policy_debiased_joint_remainder_bound phi dphi hd B Lip hB hLip
        hbound hlip s x (fun z => p z x) (fun z => dp z x) (fun z => a z x)
        (fun z => da z x) (fun z => mass z x) (q x) (tau x) (dtau x) t c hc htx.1
        (fun z hz => (hx.1 z hz).1) (fun z hz => (hx.1 z hz).2.2.1) htx.2
        (fun z hz => (hx.1 z hz).2.2.2) hx.2
      have he := pooled_policy_joint_remainder_envelope_le s (fun z => a z x)
        (fun z => da z x) (fun z => dp z x) (dtau x) B Lip c hB hLip hc
        (fun z hz => (hx.1 z hz).2.1)
      simpa only [F, zero_mul, add_zero, sub_zero, E] using
        h.trans (mul_le_mul_of_nonneg_right he (sq_nonneg t))
    have hir : Integrable (fun x => F t x - F 0 x) ν :=
      (hiE.mul_const (t^2)).mono' (hm.sub hi0.aestronglyMeasurable)
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
      _ ≤ ∫ x, E x * t^2 ∂ν := integral_mono_ae hir.abs (hiE.mul_const (t^2)) hb
      _ = _ := integral_mul_const _ _
  have ho : (fun t : ℝ => (∫ x, F t x ∂ν) - ∫ x, F 0 x ∂ν)
      =O[nhds 0] (fun t => t^2) := by
    apply Asymptotics.IsBigO.of_bound (∫ x, E x ∂ν)
    filter_upwards [hboundInt] with t ht
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)] using ht
  apply HasDerivAt.of_isLittleO
  simpa only [F, smul_zero, sub_zero] using
    ho.trans_isLittleO (Asymptotics.isLittleO_pow_id (𝕜 := ℝ) (by norm_num : 1 < 2))

end Papers.TbsPrteOptimalTransport

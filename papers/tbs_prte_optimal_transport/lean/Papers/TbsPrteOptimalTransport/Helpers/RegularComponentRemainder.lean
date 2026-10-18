module
public import Papers.TbsPrteOptimalTransport.Helpers.RegularPolicyMean
public import Papers.TbsPrteOptimalTransport.Helpers.BinaryScoreRemainder
/-! Combining fitted binary branch control with regression and policy residual means. -/
public section
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Set
open scoped Classical

-- The fitted - denominator residual differs from minus the regression error
-- by a product of errors; only the fitted denominator needs a lower bound.
-- @node: fitted_ipw_residual_centering_error
/-- If [c is positive](hyp:hc) and [the fitted assignment probability is at least c](hyp:hp),
[the absolute difference between the inverse-weighted residual mean and the negative
regression change is bounded by the product of the absolute assignment and regression errors divided by c](goal). -/
lemma fitted_ipw_residual_centering_error {p0 p v0 v c : ℝ}
    (hc : 0 < c) (hp : c ≤ p) :
    |p0 * (v0 - v) / p + (v - v0)| ≤ |p - p0| * |v - v0| / c := by
  have hp0 : 0 < p := hc.trans_le hp
  have hid : p0 * (v0 - v) / p + (v - v0) = (p - p0) * (v - v0) / p := by
    field_simp
    <;> ring
  rw [hid, abs_div, abs_mul, abs_of_pos hp0]
  exact div_le_div_of_nonneg_left (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hc hp

-- Residual means cancel the fitted linear term. Only their approximation
-- errors and the quadratic branch remainder survive, including at fitted ties.
-- @node: binary_hinge_debiased_residual_remainder
/-- Suppose [c is positive](hyp:hc), [the upper and lower hinge endpoints are separated
by at least c](hyp:hlq), and [the boundary is at least c from the lower endpoint](hyp:hbl)
and [from the upper endpoint](hyp:hbq). If [the upper endpoint perturbation](hyp:hq),
[the lower endpoint perturbation](hyp:hl), and [the boundary perturbation](hyp:hb) each
have absolute value at most err, while [the boundary residual differs from its perturbation
by at most EB](hyp:hrB), [the upper residual plus its perturbation is bounded by EQ](hyp:hrQ),
and [the lower residual plus its perturbation is bounded by EL](hyp:hrL), [the absolute
hinge change with fitted-branch residual corrections is at most 26 times err squared
divided by c, plus EB, EQ, and EL](goal). -/
lemma binary_hinge_debiased_residual_remainder
    {q l b dq dl db err c rB rQ rL EB EQ EL : ℝ}
    (hc : 0 < c) (hlq : c ≤ q - l) (hbl : c ≤ |b - l|) (hbq : c ≤ |b - q|)
    (hq : |dq| ≤ err) (hl : |dl| ≤ err) (hb : |db| ≤ err)
    (hrB : |rB - db| ≤ EB) (hrQ : |rQ + dq| ≤ EQ) (hrL : |rL + dl| ≤ EL) :
    |max 0 (q + dq - max (l + dl) (b + db)) - max 0 (q - max l b) +
      indicator (l + dl < b + db ∧ b + db < q + dq) * rB +
      indicator (q + dq > max (l + dl) (b + db)) * rQ -
      indicator (l + dl > b + db) * indicator (q + dq > max (l + dl) (b + db)) * rL| ≤
      (26 / c) * err ^ 2 + EB + EQ + EL := by
  let I := indicator (q + dq > max (l + dl) (b + db))
  let D := indicator (l + dl < b + db ∧ b + db < q + dq)
  let E := indicator (l + dl > b + db)
  let R := max 0 (q + dq - max (l + dl) (b + db)) - max 0 (q - max l b) -
    (I * dq - D * db - E * I * dl)
  have hR : |R| ≤ (26 / c) * err ^ 2 :=
    binary_hinge_fitted_score_remainder hc hlq hbl hbq hq hl hb
  have hB : |D * (rB - db)| ≤ EB := by
    dsimp only [D]
    unfold indicator
    split_ifs
    · simpa using hrB
    · simpa using (abs_nonneg (rB - db)).trans hrB
  have hQ : |I * (rQ + dq)| ≤ EQ := by
    dsimp only [I]
    unfold indicator
    split_ifs
    · simpa using hrQ
    · simpa using (abs_nonneg (rQ + dq)).trans hrQ
  have hL : |E * I * (rL + dl)| ≤ EL := by
    dsimp only [E, I]
    unfold indicator
    split_ifs <;> first
      | simpa using hrL
      | simpa using (abs_nonneg (rL + dl)).trans hrL
  have hid : max 0 (q + dq - max (l + dl) (b + db)) - max 0 (q - max l b) +
      D * rB + I * rQ - E * I * rL = R + D * (rB - db) + I * (rQ + dq) - E * I * (rL + dl) := by
    dsimp only [R]
    ring
  change |max 0 (q + dq - max (l + dl) (b + db)) - max 0 (q - max l b) +
    D * rB + I * rQ - E * I * rL| ≤ _
  rw [hid]
  have hsum₁ : |R + D * (rB - db)| ≤ |R|+|D * (rB - db)| := by
    simpa only [Real.norm_eq_abs] using norm_add_le R (D * (rB - db))
  have hsum₂ : |R + D * (rB - db) + I * (rQ + dq)| ≤ |R + D * (rB - db)|+|I * (rQ + dq)| := by
    simpa only [Real.norm_eq_abs] using norm_add_le (R + D * (rB - db)) (I * (rQ + dq))
  exact (abs_sub _ _).trans (add_le_add
    (hsum₂.trans (add_le_add (hsum₁.trans (add_le_add hR hB)) hQ)) hL)

-- Integrating the debiased score expression preserves the quadratic bound.
-- In applications EB, EQ, and EL are denominator and pooled - policy products.
-- @node: binary_hinge_debiased_integrated_remainder
/-- For [positive separation c](hyp:hc), suppose [the upper endpoint](hyp:hq),
[lower endpoint](hyp:hl), [boundary](hyp:hb), [upper perturbation](hyp:hdq),
[lower perturbation](hyp:hdl), [boundary perturbation](hyp:hdb), [boundary residual](hyp:hrB),
[upper residual](hyp:hrQ), and [lower residual](hyp:hrL) are measurable.
If [err is square integrable](hyp:herr), [EB](hyp:hEB), [EQ](hyp:hEQ), and [EL](hyp:hEL)
are integrable, [the endpoint gap and both boundary distances are at least c almost everywhere](hyp:hgap),
[all three perturbations are bounded in absolute value by err almost everywhere](hyp:herrors),
and [the three residual centering errors are bounded by EB, EQ, and EL almost everywhere](hyp:hres),
[the hinge change with fitted-branch residual corrections is integrable and its absolute
integral is bounded by 26 divided by c times the integral of err squared plus the three envelope integrals](goal). -/
lemma binary_hinge_debiased_integrated_remainder {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (q l b dq dl db rB rQ rL err EB EQ EL : X → ℝ) (c : ℝ)
    (hc : 0 < c)
    (hq : Measurable q) (hl : Measurable l) (hb : Measurable b)
    (hdq : Measurable dq) (hdl : Measurable dl) (hdb : Measurable db)
    (hrB : Measurable rB) (hrQ : Measurable rQ) (hrL : Measurable rL)
    (herr : MemLp err 2 μ) (hEB : Integrable EB μ)
    (hEQ : Integrable EQ μ) (hEL : Integrable EL μ)
    (hgap : ∀ᵐ x ∂μ, c ≤ q x - l x ∧ c ≤ |b x - l x| ∧ c ≤ |b x - q x|)
    (herrors : ∀ᵐ x ∂μ, |dq x| ≤ err x ∧ |dl x| ≤ err x ∧ |db x| ≤ err x)
    (hres : ∀ᵐ x ∂μ, |rB x - db x| ≤ EB x ∧
      |rQ x + dq x| ≤ EQ x ∧ |rL x + dl x| ≤ EL x) :
    let R := fun x => max 0 (q x + dq x - max (l x + dl x) (b x + db x)) -
      max 0 (q x - max (l x) (b x)) +
      indicator (l x + dl x < b x + db x ∧ b x + db x < q x + dq x) * rB x +
      indicator (q x + dq x > max (l x + dl x) (b x + db x)) * rQ x -
      indicator (l x + dl x > b x + db x) *
        indicator (q x + dq x > max (l x + dl x) (b x + db x)) * rL x
    Integrable R μ ∧ |∫ x, R x ∂μ| ≤
      (26 / c) * (∫ x, err x ^ 2 ∂μ) + (∫ x, EB x ∂μ) +
        (∫ x, EQ x ∂μ) + (∫ x, EL x ∂μ) := by
  dsimp only
  let R := fun x => max 0 (q x + dq x - max (l x + dl x) (b x + db x)) -
    max 0 (q x - max (l x) (b x)) +
    indicator (l x + dl x < b x + db x ∧ b x + db x < q x + dq x) * rB x +
    indicator (q x + dq x > max (l x + dl x) (b x + db x)) * rQ x -
    indicator (l x + dl x > b x + db x) *
      indicator (q x + dq x > max (l x + dl x) (b x + db x)) * rL x
  have hI : Measurable (fun x =>
      indicator (q x + dq x > max (l x + dl x) (b x + db x))) := by
    first | fun_prop
          | unfold indicator
            exact Measurable.ite (measurableSet_lt ((hl.add hdl).max (hb.add hdb))
              (hq.add hdq)) measurable_const measurable_const
  have hD : Measurable (fun x =>
      indicator (l x + dl x < b x + db x ∧ b x + db x < q x + dq x)) := by
    first | fun_prop
          | unfold indicator
            exact Measurable.ite ((measurableSet_lt (hl.add hdl) (hb.add hdb)).inter
              (measurableSet_lt (hb.add hdb) (hq.add hdq))) measurable_const measurable_const
  have hE : Measurable (fun x => indicator (l x + dl x > b x + db x)) := by
    first | fun_prop
          | unfold indicator
            exact Measurable.ite (measurableSet_lt (hb.add hdb) (hl.add hdl))
              measurable_const measurable_const
  have hR : Measurable R := by
    dsimp only [R]
    fun_prop
  have hbound : ∀ᵐ x ∂μ, |R x| ≤ (26 / c) * err x ^ 2 + EB x + EQ x + EL x := by
    filter_upwards [hgap, herrors, hres] with x hg he hr
    exact binary_hinge_debiased_residual_remainder hc hg.1 hg.2.1 hg.2.2
      he.1 he.2.1 he.2.2 hr.1 hr.2.1 hr.2.2
  have hs : Integrable (fun x => (26 / c) * err x ^ 2) μ := herr.integrable_sq.const_mul _
  have hi : Integrable R μ := ((hs.fun_add hEB).fun_add hEQ).fun_add hEL |>.mono'
    hR.aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hbound)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ x, |R x| ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm R
    _ ≤ ∫ x, (26 / c) * err x ^ 2 + EB x + EQ x + EL x ∂μ :=
      integral_mono_ae hi.abs (((hs.fun_add hEB).fun_add hEQ).fun_add hEL) hbound
    _ = _ := by
      rw [integral_add ((hs.fun_add hEB).fun_add hEQ) hEL,
        integral_add (hs.fun_add hEB) hEQ, integral_add hs hEB, integral_const_mul]

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X]
  [StandardBorelSpace Z] [Nonempty Z] [Fintype Z]

-- This is the population expression supplied by the six - correction tower
-- transfer. The lower residual includes the fixed q_0 = p_k convention.
-- @node: binary_regular_regression_centering_error
/-- If [c is positive](hyp:hc), [k is below the last treatment level](hyp:hk), and
[every positive-level fitted assignment probability is at least c](hyp:hpi), [the
absolute discrepancy between the combined inverse-weighted regression residual means
and the boundary change is bounded by the assignment error at level k plus one times
the sum of its outcome and propensity regression errors, plus the assignment error at
level k times its outcome regression error, all divided by c](goal). -/
lemma binary_regular_regression_centering_error
    (L : LevelData Z X) (e0 e : NuisanceBin L) (k : ℕ) (x : X) (c : ℝ)
    (hc : 0 < c) (hk : k < L.K)
    (hpi : ∀ i, 1 ≤ i → i ≤ L.K → c ≤ positiveValue e.piLev i x) :
    let rP := fun i => positiveValue e0.piLev i x *
      (positiveValue e0.P1 i x - positiveValue e.P1 i x) / positiveValue e.piLev i x
    let rp := fun i => positiveValue e0.piLev i x *
      (positiveValue e0.pLev i x - positiveValue e.pLev i x) / positiveValue e.piLev i x
    |(rP (k + 1) - rP k - rp (k + 1)) -
      ((positiveValue e.pLev (k + 1) x - binFullJ L e k x) -
        (positiveValue e0.pLev (k + 1) x - binFullJ L e0 k x))| ≤
      |positiveValue e.piLev (k + 1) x - positiveValue e0.piLev (k + 1) x| *
        (|positiveValue e.P1 (k + 1) x - positiveValue e0.P1 (k + 1) x| +
          |positiveValue e.pLev (k + 1) x - positiveValue e0.pLev (k + 1) x|) / c +
      |positiveValue e.piLev k x - positiveValue e0.piLev k x| *
        |positiveValue e.P1 k x - positiveValue e0.P1 k x| / c := by
  dsimp only
  have hr (v0 v : PositiveIndex L.K → X → ℝ) (i : ℕ) (hi : i ≤ L.K) :
      |positiveValue e0.piLev i x * (positiveValue v0 i x - positiveValue v i x) /
          positiveValue e.piLev i x + (positiveValue v i x - positiveValue v0 i x)| ≤
        |positiveValue e.piLev i x - positiveValue e0.piLev i x| *
          |positiveValue v i x - positiveValue v0 i x| / c := by
    by_cases hz : i = 0
    · subst i
      simp [positiveValue]
    · exact fitted_ipw_residual_centering_error hc (hpi i (by omega) hi)
  have hplus := hr e0.P1 e.P1 (k + 1) (by omega)
  have hminus := hr e0.P1 e.P1 k hk.le
  have hprop := hr e0.pLev e.pLev (k + 1) (by omega)
  let A := positiveValue e0.piLev (k + 1) x *
    (positiveValue e0.P1 (k + 1) x - positiveValue e.P1 (k + 1) x) /
      positiveValue e.piLev (k + 1) x +
        (positiveValue e.P1 (k + 1) x - positiveValue e0.P1 (k + 1) x)
  let B := positiveValue e0.piLev k x *
    (positiveValue e0.P1 k x - positiveValue e.P1 k x) / positiveValue e.piLev k x +
      (positiveValue e.P1 k x - positiveValue e0.P1 k x)
  let C := positiveValue e0.piLev (k + 1) x *
    (positiveValue e0.pLev (k + 1) x - positiveValue e.pLev (k + 1) x) /
      positiveValue e.piLev (k + 1) x +
        (positiveValue e.pLev (k + 1) x - positiveValue e0.pLev (k + 1) x)
  have h := (abs_sub (A - B) C).trans (add_le_add
    ((abs_sub A B).trans (add_le_add hplus hminus)) hprop)
  convert! h using 1
  · congr 1
    dsimp only [A, B, C, binFullJ]
    ring
  · ring

-- This is the population expression supplied by the six - correction tower
-- transfer. The lower residual includes the fixed q_0 = p_k convention.
-- @node: binary_regular_component_mean_remainder_bound
/-- Suppose [c is positive](hyp:hc), [the true pooled policy endpoints are separated by
at least c](hyp:hlq), and [the true regression boundary is at least c from the lower](hyp:hbl)
and [upper pooled endpoint](hyp:hbq). If [the upper pooled endpoint error](hyp:hq),
[lower pooled endpoint error](hyp:hl), and [regression boundary error](hyp:hb) are each
bounded by err, [bounds EB, EQ, and EL on the regression, upper policy, and lower policy
residual centering errors imply that the fitted hinge plus its regression and policy
mean corrections differs from the true hinge by at most 26 times err squared divided
by c, plus EB, EQ, and EL](goal). -/
lemma binary_regular_component_mean_remainder_bound
    (M : LatentIVModel Ω X Z) (phi dphi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (e0 e : NuisanceBin L) (k j : ℕ) (x : X)
    (err c EB EQ EL : ℝ)
    (hc : 0 < c)
    (hlq : c ≤ pooledQBin phi L e0 k j x - pooledQBin phi L e0 k (j - 1) x)
    (hbl : c ≤ |positiveValue e0.pLev (k + 1) x - binFullJ L e0 k x -
      pooledQBin phi L e0 k (j - 1) x|)
    (hbq : c ≤ |positiveValue e0.pLev (k + 1) x - binFullJ L e0 k x -
      pooledQBin phi L e0 k j x|)
    (hq : |pooledQBin phi L e k j x - pooledQBin phi L e0 k j x| ≤ err)
    (hl : |pooledQBin phi L e k (j - 1) x - pooledQBin phi L e0 k (j - 1) x| ≤ err)
    (hb : |(positiveValue e.pLev (k + 1) x - binFullJ L e k x) -
      (positiveValue e0.pLev (k + 1) x - binFullJ L e0 k x)| ≤ err) :
    let rP := fun i => positiveValue e0.piLev i x *
      (positiveValue e0.P1 i x - positiveValue e.P1 i x) / positiveValue e.piLev i x
    let rp := fun i => positiveValue e0.piLev i x *
      (positiveValue e0.pLev i x - positiveValue e.pLev i x) / positiveValue e.piLev i x
    let Q := fun i => ∑ z, instProb M z x * RqBin dphi L e k i (x,z,M.prop z x,0)
    |(rP (k + 1) - rP k - rp (k + 1)) -
      ((positiveValue e.pLev (k + 1) x - binFullJ L e k x) -
        (positiveValue e0.pLev (k + 1) x - binFullJ L e0 k x))| ≤ EB →
    |Q j + (pooledQBin phi L e k j x - pooledQBin phi L e0 k j x)| ≤ EQ →
    |(if j = 1 then rp k else 0) + Q (j - 1) +
      (pooledQBin phi L e k (j - 1) x - pooledQBin phi L e0 k (j - 1) x)| ≤ EL →
    |hMinus phi L e k j x + binaryRegularRegressionMean phi L e0 e k j x +
      binaryRegularPolicyMean M phi dphi L e k j x - hMinus phi L e0 k j x| ≤
      (26 / c) * err ^ 2 + EB + EQ + EL := by
  dsimp only
  intro hrB hrQ hrL
  have hh := binary_hinge_debiased_residual_remainder hc hlq hbl hbq hq hl hb hrB hrQ hrL
  simp only [add_sub_cancel] at hh
  convert hh using 1
  congr 1
  unfold hMinus binaryRegularRegressionMean binaryRegularPolicyMean Dbd Iact Edom
  split_ifs <;> ring

end Papers.TbsPrteOptimalTransport

module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLFittedPolicyResidual
public import Papers.TbsPrteOptimalTransport.Helpers.DMLRemainderRates
/-! Fitted branch weights preserve the debiased pooling remainder and its DML rate. -/
public section

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Filter Set
open scoped Topology

universe v
variable {X Z : Type v} [MeasurableSpace X] [MeasurableSpace Z]
  [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]

-- The weight may depend on the fitted active branch. Only its clipping bound
-- enters, so no agreement of fitted and population branches is assumed.
-- @node: fitted_pooled_policy_weighted_quadratic_bound
/-- Suppose [dphi is the policy derivative](hyp:hd), [B is nonnegative](hyp:hB),
[Lip is nonnegative](hyp:hLip), [c is positive](hyp:hc), and on the unit interval
[the derivative has absolute value at most B](hyp:hbound) and [is Lipschitz with
constant Lip](hyp:hlip). Assume almost everywhere that [the fitted denominator
is at least c](hyp:hden), [each instrument mass equals its reference share times
the reference denominator](hyp:ha), [reference probabilities](hyp:hp) and
[fitted probabilities](hyp:hph) lie in the unit interval, [the reference policy
values all equal q](hyp:hcommon), [reference shares sum to one](hyp:hs), [fitted
shares sum to one](hyp:hsh), and [reference shares have absolute value at most
one](hyp:hab). If [each probability error](hyp:hep), [each share error](hyp:hea),
and [the denominator error](hyp:het) are square integrable, [the debiased pooled
policy residual is strongly measurable up to a null set](hyp:hm), [W is
nonnegative](hyp:hW), [reg is nonnegative](hyp:hreg), [wt is
nonnegative](hyp:hwt), [the weight is measurable](hyp:hw) and [bounded in
absolute value by W almost everywhere](hyp:hwb), [each probability error has L2
norm at most reg](hyp:hepNorm), [each share error has L2 norm at most
wt](hyp:heaNorm), and [the denominator error has L2 norm at most wt](hyp:hetNorm),
then [the weighted debiased pooled policy residual is integrable and its integral
has absolute value at most W times the number of instruments times the sum of
Lip times reg squared and the product of B plus B/c, reg, and wt](goal). -/
lemma fitted_pooled_policy_weighted_quadratic_bound
    (ν : Measure X) (phi dphi : Z → X → ℝ → ℝ)
    (hd : PolicyDifferentiable phi dphi)
    (B Lip c : ℝ) (hB : 0 ≤ B) (hLip : 0 ≤ Lip) (hc : 0 < c)
    (hbound : ∀ z x p, p ∈ Icc (0 : ℝ) 1 → |dphi z x p| ≤ B)
    (hlip : ∀ z x p r, p ∈ Icc (0 : ℝ) 1 → r ∈ Icc (0 : ℝ) 1 →
      |dphi z x p - dphi z x r| ≤ Lip * |p - r|)
    (s : Finset Z) (p ph a ah mass : Z → X → ℝ) (q tau th : X → ℝ)
    (hden : ∀ᵐ x ∂ν, c ≤ th x)
    (ha : ∀ᵐ x ∂ν, ∀ z ∈ s, mass z x = a z x * tau x)
    (hp : ∀ᵐ x ∂ν, ∀ z ∈ s, p z x ∈ Icc (0 : ℝ) 1)
    (hph : ∀ᵐ x ∂ν, ∀ z ∈ s, ph z x ∈ Icc (0 : ℝ) 1)
    (hcommon : ∀ᵐ x ∂ν, ∀ z ∈ s, phi z x (p z x) = q x)
    (hs : ∀ᵐ x ∂ν, ∑ z ∈ s, a z x = 1)
    (hsh : ∀ᵐ x ∂ν, ∑ z ∈ s, ah z x = 1)
    (hab : ∀ᵐ x ∂ν, ∀ z ∈ s, |a z x| ≤ 1)
    (hep : ∀ z ∈ s, MemLp (fun x => ph z x - p z x) 2 ν)
    (hea : ∀ z ∈ s, MemLp (fun x => ah z x - a z x) 2 ν)
    (het : MemLp (fun x => th x - tau x) 2 ν)
    (hm : AEStronglyMeasurable (fun x =>
      (∑ z ∈ s, ah z x * phi z x (ph z x)) +
        (th x)⁻¹ * (∑ z ∈ s, mass z x * dphi z x (ph z x) * (p z x - ph z x)) - q x) ν)
    (w : X → ℝ) (W reg wt : ℝ) (hW : 0 ≤ W)
    (hreg : 0 ≤ reg) (hwt : 0 ≤ wt)
    (hw : Measurable w) (hwb : ∀ᵐ x ∂ν, ‖w x‖ ≤ W)
    (hepNorm : ∀ z ∈ s, (eLpNorm (fun x => ph z x - p z x) 2 ν).toReal ≤ reg)
    (heaNorm : ∀ z ∈ s, (eLpNorm (fun x => ah z x - a z x) 2 ν).toReal ≤ wt)
    (hetNorm : (eLpNorm (fun x => th x - tau x) 2 ν).toReal ≤ wt) :
    let R := fun x => (∑ z ∈ s, ah z x * phi z x (ph z x)) +
      (th x)⁻¹ * (∑ z ∈ s, mass z x * dphi z x (ph z x) * (p z x - ph z x)) - q x
    Integrable (fun x => w x * R x) ν ∧
      |∫ x, w x * R x ∂ν| ≤
        W * (s.card : ℝ) * (Lip * reg ^ 2 + (B + B / c) * (reg * wt)) := by
  let R := fun x => (∑ z ∈ s, ah z x * phi z x (ph z x)) +
      (th x)⁻¹ * (∑ z ∈ s, mass z x * dphi z x (ph z x) * (p z x - ph z x)) - q x
  obtain ⟨hi, hb⟩ := fitted_pooled_policy_integrated_L2_bound
    ν phi dphi hd B Lip c hB hLip hc hbound hlip s p ph a ah mass q tau th
    hden ha hp hph hcommon hs hsh hab hep hea het hm
  have hiw : Integrable (fun x => w x * R x) ν :=
    hi.bdd_mul hw.aestronglyMeasurable hwb
  have hsquare (z : Z) (hz : z ∈ s) :
      (∫ x, (ph z x - p z x)^2 ∂ν) ≤ reg ^ 2 := by
    have hcs := Causalean.Stat.integral_abs_mul_le_eLpNorm_mul_eLpNorm
      (hep z hz) (hep z hz)
    have hid : (fun x => |(ph z x - p z x) * (ph z x - p z x)|) =
        (fun x => (ph z x - p z x)^2) := by
      funext x
      rw [← sq, abs_of_nonneg (sq_nonneg _)]
    rw [hid] at hcs
    exact hcs.trans (by
      simpa only [sq] using mul_le_mul (hepNorm z hz) (hepNorm z hz)
        ENNReal.toReal_nonneg hreg)
  refine ⟨hiw, ?_⟩
  calc
    _ ≤ ∫ x, |w x * R x| ∂ν := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x => w x * R x)
    _ ≤ ∫ x, W * |R x| ∂ν := by
      apply integral_mono_ae hiw.abs (hi.abs.const_mul W)
      filter_upwards [hwb] with x hx
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (by simpa only [Real.norm_eq_abs] using hx) (abs_nonneg _)
    _ = W * ∫ x, |R x| ∂ν := integral_const_mul _ _
    _ ≤ W * (∑ z ∈ s,
        (Lip * (∫ x, (ph z x - p z x)^2 ∂ν) +
          B * ((eLpNorm (fun x => ah z x - a z x) 2 ν).toReal *
            (eLpNorm (fun x => ph z x - p z x) 2 ν).toReal) +
          (B / c) * ((eLpNorm (fun x => th x - tau x) 2 ν).toReal *
            (eLpNorm (fun x => ph z x - p z x) 2 ν).toReal))) :=
      mul_le_mul_of_nonneg_left hb hW
    _ ≤ W * (∑ _z ∈ s, (Lip * reg ^ 2 + (B + B / c) * (reg * wt))) := by
      apply mul_le_mul_of_nonneg_left _ hW
      apply Finset.sum_le_sum
      intro z hz
      calc
        _ ≤ Lip * reg ^ 2 + B * (wt * reg) + (B / c) * (wt * reg) := by
          gcongr <;> first | exact hsquare z hz | exact heaNorm z hz |
            exact hepNorm z hz
        _ = _ := by ring
    _ = _ := by simp; ring

-- Training-sample dependent weights are permitted, including fitted branch
-- indicators. The rate is derived from nuisance norms and the bound above.
-- @node: fitted_pooled_policy_weighted_root_n_negligible
/-- Suppose [dphi is the policy derivative](hyp:hd), [B is nonnegative](hyp:hB),
[Lip is nonnegative](hyp:hLip), [c is positive](hyp:hc), [W is
nonnegative](hyp:hW), and on the unit interval [the derivative has absolute value
at most B](hyp:hbound) and [is Lipschitz with constant Lip](hyp:hlip). Assume
[every fitted denominator is at least c almost everywhere](hyp:hden), [each
instrument mass equals its reference share times the reference denominator almost
everywhere](hyp:ha), [reference probabilities](hyp:hp) and [all fitted
probabilities](hyp:hph) lie in the unit interval almost everywhere, [reference
policy values all equal q almost everywhere](hyp:hcommon), [reference
shares](hyp:hs) and [all fitted shares](hyp:hsh) sum to one almost everywhere,
and [reference shares have absolute value at most one almost everywhere](hyp:hab).
If [every fitted probability error](hyp:hep), [every fitted share error](hyp:hea),
and [every fitted denominator error](hyp:het) are square integrable, [every
debiased pooled policy residual is strongly measurable up to a null set](hyp:hm),
[the probability error bounds are nonnegative](hyp:hreg), [the share and
denominator error bounds are nonnegative](hyp:hwt), [all weights are
measurable](hyp:hw) and [bounded in absolute value by W almost
everywhere](hyp:hwb), [probability error L2 norms are bounded by reg](hyp:hepNorm),
[share error L2 norms are bounded by wt](hyp:heaNorm), [denominator error L2 norms
are bounded by wt](hyp:hetNorm), and [reg](hyp:hr) and [wt](hyp:hwtRate) are
little-o in probability of the inverse fourth root of twice n plus two, then [the
weighted population debiased pooled policy residual multiplied by the square root
of n plus one converges to zero in probability](goal). -/
lemma fitted_pooled_policy_weighted_root_n_negligible {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (ν : Measure X) (phi dphi : Z → X → ℝ → ℝ)
    (hd : PolicyDifferentiable phi dphi)
    (B Lip c W : ℝ) (hB : 0 ≤ B) (hLip : 0 ≤ Lip) (hc : 0 < c) (hW : 0 ≤ W)
    (hbound : ∀ z x p, p ∈ Icc (0 : ℝ) 1 → |dphi z x p| ≤ B)
    (hlip : ∀ z x p r, p ∈ Icc (0 : ℝ) 1 → r ∈ Icc (0 : ℝ) 1 →
      |dphi z x p - dphi z x r| ≤ Lip * |p - r|)
    (s : Finset Z) (p a mass : Z → X → ℝ) (q tau : X → ℝ)
    (ph ah : ℕ → A → Z → X → ℝ) (th w : ℕ → A → X → ℝ)
    (reg wt : ℕ → A → ℝ)
    (hden : ∀ n t, ∀ᵐ x ∂ν, c ≤ th n t x)
    (ha : ∀ᵐ x ∂ν, ∀ z ∈ s, mass z x = a z x * tau x)
    (hp : ∀ᵐ x ∂ν, ∀ z ∈ s, p z x ∈ Icc (0 : ℝ) 1)
    (hph : ∀ n t, ∀ᵐ x ∂ν, ∀ z ∈ s, ph n t z x ∈ Icc (0 : ℝ) 1)
    (hcommon : ∀ᵐ x ∂ν, ∀ z ∈ s, phi z x (p z x) = q x)
    (hs : ∀ᵐ x ∂ν, ∑ z ∈ s, a z x = 1)
    (hsh : ∀ n t, ∀ᵐ x ∂ν, ∑ z ∈ s, ah n t z x = 1)
    (hab : ∀ᵐ x ∂ν, ∀ z ∈ s, |a z x| ≤ 1)
    (hep : ∀ n t z, z ∈ s → MemLp (fun x => ph n t z x - p z x) 2 ν)
    (hea : ∀ n t z, z ∈ s → MemLp (fun x => ah n t z x - a z x) 2 ν)
    (het : ∀ n t, MemLp (fun x => th n t x - tau x) 2 ν)
    (hm : ∀ n t, AEStronglyMeasurable (fun x =>
      (∑ z ∈ s, ah n t z x * phi z x (ph n t z x)) +
        (th n t x)⁻¹ * (∑ z ∈ s, mass z x * dphi z x (ph n t z x) *
          (p z x - ph n t z x)) - q x) ν)
    (hreg : ∀ n t, 0 ≤ reg n t) (hwt : ∀ n t, 0 ≤ wt n t)
    (hw : ∀ n t, Measurable (w n t)) (hwb : ∀ n t, ∀ᵐ x ∂ν, ‖w n t x‖ ≤ W)
    (hepNorm : ∀ n t z, z ∈ s →
      (eLpNorm (fun x => ph n t z x - p z x) 2 ν).toReal ≤ reg n t)
    (heaNorm : ∀ n t z, z ∈ s →
      (eLpNorm (fun x => ah n t z x - a z x) 2 ν).toReal ≤ wt n t)
    (hetNorm : ∀ n t, (eLpNorm (fun x => th n t x - tau x) 2 ν).toReal ≤ wt n t)
    (hr : Causalean.Stat.IsLittleOp reg
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ)) μ)
    (hwtRate : Causalean.Stat.IsLittleOp wt
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ)) μ) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => Real.sqrt ((n + 1 : ℕ) : ℝ) * ∫ x, w n t x *
        ((∑ z ∈ s, ah n t z x * phi z x (ph n t z x)) +
          (th n t x)⁻¹ * (∑ z ∈ s, mass z x * dphi z x (ph n t z x) *
            (p z x - ph n t z x)) - q x) ∂ν) atTop (fun _ _ => 0) := by
  let C := W * (s.card : ℝ) * (Lip + B + B / c) + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  apply dml_quadratic_bias_root_n_negligible μ _ reg wt C hC hr hwtRate
  intro n t
  have hb := (fitted_pooled_policy_weighted_quadratic_bound ν phi dphi hd
    B Lip c hB hLip hc hbound hlip s p (ph n t) a (ah n t) mass q tau (th n t)
    (hden n t) ha hp (hph n t) hcommon hs (hsh n t) hab
    (hep n t) (hea n t) (het n t) (hm n t) (w n t) W (reg n t) (wt n t) hW
    (hreg n t) (hwt n t) (hw n t) (hwb n t)
    (hepNorm n t) (heaNorm n t) (hetNorm n t)).2
  apply hb.trans
  have hn : 0 ≤ reg n t * wt n t := mul_nonneg (hreg n t) (hwt n t)
  calc
    _ ≤ W * (s.card : ℝ) *
        ((Lip + B + B / c) * (reg n t ^ 2 + reg n t * wt n t)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [mul_nonneg (by positivity : 0 ≤ B + B / c) (sq_nonneg (reg n t)),
        mul_nonneg hLip hn]
    _ = (C - 1) * (reg n t ^ 2 + reg n t * wt n t) := by dsimp only [C]; ring
    _ ≤ C * (reg n t ^ 2 + reg n t * wt n t) :=
      mul_le_mul_of_nonneg_right (by linarith) (add_nonneg (sq_nonneg _) hn)

-- Fitted branch weights need only be measurable almost everywhere on the
-- documented policy domain. Representatives leave the actual bias unchanged.
-- @node: fitted_pooled_policy_ae_weighted_quadratic_bound
/-- Suppose [dphi is the policy derivative](hyp:hd), [B is nonnegative](hyp:hB),
[Lip is nonnegative](hyp:hLip), [c is positive](hyp:hc), and on the unit interval
[the derivative has absolute value at most B](hyp:hbound) and [is Lipschitz with
constant Lip](hyp:hlip). Assume almost everywhere that [the fitted denominator
is at least c](hyp:hden), [each instrument mass equals its reference share times
the reference denominator](hyp:ha), [reference probabilities](hyp:hp) and
[fitted probabilities](hyp:hph) lie in the unit interval, [reference policy
values all equal q](hyp:hcommon), [reference shares sum to one](hyp:hs), [fitted
shares sum to one](hyp:hsh), and [reference shares have absolute value at most
one](hyp:hab). If [each probability error](hyp:hep), [each share error](hyp:hea),
and [the denominator error](hyp:het) are square integrable, [the debiased pooled
policy residual is strongly measurable up to a null set](hyp:hm), [W is
nonnegative](hyp:hW), [reg is nonnegative](hyp:hreg), [wt is
nonnegative](hyp:hwt), [the weight is strongly measurable up to a null
set](hyp:hw) and [bounded in absolute value by W almost everywhere](hyp:hwb),
[each probability error has L2 norm at most reg](hyp:hepNorm), [each share error
has L2 norm at most wt](hyp:heaNorm), and [the denominator error has L2 norm at
most wt](hyp:hetNorm), then [the weighted debiased pooled policy residual is
integrable and its integral has absolute value at most W times the number of
instruments times the sum of Lip times reg squared and the product of B plus
B/c, reg, and wt](goal). -/
lemma fitted_pooled_policy_ae_weighted_quadratic_bound
    (ν : Measure X) (phi dphi : Z → X → ℝ → ℝ)
    (hd : PolicyDifferentiable phi dphi)
    (B Lip c : ℝ) (hB : 0 ≤ B) (hLip : 0 ≤ Lip) (hc : 0 < c)
    (hbound : ∀ z x p, p ∈ Icc (0 : ℝ) 1 → |dphi z x p| ≤ B)
    (hlip : ∀ z x p r, p ∈ Icc (0 : ℝ) 1 → r ∈ Icc (0 : ℝ) 1 →
      |dphi z x p - dphi z x r| ≤ Lip * |p - r|)
    (s : Finset Z) (p ph a ah mass : Z → X → ℝ) (q tau th : X → ℝ)
    (hden : ∀ᵐ x ∂ν, c ≤ th x)
    (ha : ∀ᵐ x ∂ν, ∀ z ∈ s, mass z x = a z x * tau x)
    (hp : ∀ᵐ x ∂ν, ∀ z ∈ s, p z x ∈ Icc (0 : ℝ) 1)
    (hph : ∀ᵐ x ∂ν, ∀ z ∈ s, ph z x ∈ Icc (0 : ℝ) 1)
    (hcommon : ∀ᵐ x ∂ν, ∀ z ∈ s, phi z x (p z x) = q x)
    (hs : ∀ᵐ x ∂ν, ∑ z ∈ s, a z x = 1)
    (hsh : ∀ᵐ x ∂ν, ∑ z ∈ s, ah z x = 1)
    (hab : ∀ᵐ x ∂ν, ∀ z ∈ s, |a z x| ≤ 1)
    (hep : ∀ z ∈ s, MemLp (fun x => ph z x - p z x) 2 ν)
    (hea : ∀ z ∈ s, MemLp (fun x => ah z x - a z x) 2 ν)
    (het : MemLp (fun x => th x - tau x) 2 ν)
    (hm : AEStronglyMeasurable (fun x =>
      (∑ z ∈ s, ah z x * phi z x (ph z x)) +
        (th x)⁻¹ * (∑ z ∈ s, mass z x * dphi z x (ph z x) * (p z x - ph z x)) - q x) ν)
    (w : X → ℝ) (W reg wt : ℝ) (hW : 0 ≤ W)
    (hreg : 0 ≤ reg) (hwt : 0 ≤ wt)
    (hw : AEStronglyMeasurable w ν) (hwb : ∀ᵐ x ∂ν, ‖w x‖ ≤ W)
    (hepNorm : ∀ z ∈ s, (eLpNorm (fun x => ph z x - p z x) 2 ν).toReal ≤ reg)
    (heaNorm : ∀ z ∈ s, (eLpNorm (fun x => ah z x - a z x) 2 ν).toReal ≤ wt)
    (hetNorm : (eLpNorm (fun x => th x - tau x) 2 ν).toReal ≤ wt) :
    let R := fun x => (∑ z ∈ s, ah z x * phi z x (ph z x)) +
      (th x)⁻¹ * (∑ z ∈ s, mass z x * dphi z x (ph z x) * (p z x - ph z x)) - q x
    Integrable (fun x => w x * R x) ν ∧
      |∫ x, w x * R x ∂ν| ≤
        W * (s.card : ℝ) * (Lip * reg ^ 2 + (B + B / c) * (reg * wt)) := by
  let R := fun x => (∑ z ∈ s, ah z x * phi z x (ph z x)) +
    (th x)⁻¹ * (∑ z ∈ s, mass z x * dphi z x (ph z x) * (p z x - ph z x)) - q x
  let w' := hw.mk w
  have hw' : Measurable w' := by
    first | fun_prop | exact hw.stronglyMeasurable_mk.measurable
  have heq : w =ᵐ[ν] w' := hw.ae_eq_mk
  have hb' : ∀ᵐ x ∂ν, ‖w' x‖ ≤ W := by
    filter_upwards [hwb, heq] with x hx he
    simpa only [← he] using hx
  obtain ⟨hi, hb⟩ := fitted_pooled_policy_weighted_quadratic_bound
    ν phi dphi hd B Lip c hB hLip hc hbound hlip s p ph a ah mass q tau th
    hden ha hp hph hcommon hs hsh hab hep hea het hm w' W reg wt hW hreg hwt
    hw' hb' hepNorm heaNorm hetNorm
  dsimp only at hi hb ⊢
  have heR : (fun x => w x * R x) =ᵐ[ν] (fun x => w' x * R x) := by
    filter_upwards [heq] with x hx
    rw [hx]
  exact ⟨hi.congr heR.symm, by rw [integral_congr_ae heR]; exact hb⟩

-- @node: fitted_pooled_policy_ae_weighted_root_n_negligible
/-- Suppose [dphi is the policy derivative](hyp:hd), [B is nonnegative](hyp:hB),
[Lip is nonnegative](hyp:hLip), [c is positive](hyp:hc), [W is
nonnegative](hyp:hW), and on the unit interval [the derivative has absolute value
at most B](hyp:hbound) and [is Lipschitz with constant Lip](hyp:hlip). Assume
[all fitted denominators are at least c almost everywhere](hyp:hden), [each
instrument mass equals its reference share times the reference denominator almost
everywhere](hyp:ha), [reference probabilities](hyp:hp) and [all fitted
probabilities](hyp:hph) lie in the unit interval almost everywhere, [reference
policy values all equal q almost everywhere](hyp:hcommon), [reference
shares](hyp:hs) and [all fitted shares](hyp:hsh) sum to one almost everywhere,
and [reference shares have absolute value at most one almost everywhere](hyp:hab).
If [every probability error](hyp:hep), [every share error](hyp:hea), and [every
denominator error](hyp:het) are square integrable, [every debiased pooled policy
residual is strongly measurable up to a null set](hyp:hm), [reg is
nonnegative](hyp:hreg), [wt is nonnegative](hyp:hwt), [each weight is strongly
measurable up to a null set](hyp:hw) and [bounded in absolute value by W almost
everywhere](hyp:hwb), [probability error L2 norms are at most reg](hyp:hepNorm),
[share error L2 norms are at most wt](hyp:heaNorm), [denominator error L2 norms
are at most wt](hyp:hetNorm), and [reg](hyp:hr) and [wt](hyp:hwtRate) are little-o
in probability of the inverse fourth root of twice n plus two, then [the weighted
population debiased pooled policy residual multiplied by the square root of n
plus one converges to zero in probability](goal). -/
lemma fitted_pooled_policy_ae_weighted_root_n_negligible {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (ν : Measure X) (phi dphi : Z → X → ℝ → ℝ)
    (hd : PolicyDifferentiable phi dphi)
    (B Lip c W : ℝ) (hB : 0 ≤ B) (hLip : 0 ≤ Lip) (hc : 0 < c) (hW : 0 ≤ W)
    (hbound : ∀ z x p, p ∈ Icc (0 : ℝ) 1 → |dphi z x p| ≤ B)
    (hlip : ∀ z x p r, p ∈ Icc (0 : ℝ) 1 → r ∈ Icc (0 : ℝ) 1 →
      |dphi z x p - dphi z x r| ≤ Lip * |p - r|)
    (s : Finset Z) (p a mass : Z → X → ℝ) (q tau : X → ℝ)
    (ph ah : ℕ → A → Z → X → ℝ) (th w : ℕ → A → X → ℝ)
    (reg wt : ℕ → A → ℝ)
    (hden : ∀ n t, ∀ᵐ x ∂ν, c ≤ th n t x)
    (ha : ∀ᵐ x ∂ν, ∀ z ∈ s, mass z x = a z x * tau x)
    (hp : ∀ᵐ x ∂ν, ∀ z ∈ s, p z x ∈ Icc (0 : ℝ) 1)
    (hph : ∀ n t, ∀ᵐ x ∂ν, ∀ z ∈ s, ph n t z x ∈ Icc (0 : ℝ) 1)
    (hcommon : ∀ᵐ x ∂ν, ∀ z ∈ s, phi z x (p z x) = q x)
    (hs : ∀ᵐ x ∂ν, ∑ z ∈ s, a z x = 1)
    (hsh : ∀ n t, ∀ᵐ x ∂ν, ∑ z ∈ s, ah n t z x = 1)
    (hab : ∀ᵐ x ∂ν, ∀ z ∈ s, |a z x| ≤ 1)
    (hep : ∀ n t z, z ∈ s → MemLp (fun x => ph n t z x - p z x) 2 ν)
    (hea : ∀ n t z, z ∈ s → MemLp (fun x => ah n t z x - a z x) 2 ν)
    (het : ∀ n t, MemLp (fun x => th n t x - tau x) 2 ν)
    (hm : ∀ n t, AEStronglyMeasurable (fun x =>
      (∑ z ∈ s, ah n t z x * phi z x (ph n t z x)) +
        (th n t x)⁻¹ * (∑ z ∈ s, mass z x * dphi z x (ph n t z x) *
          (p z x - ph n t z x)) - q x) ν)
    (hreg : ∀ n t, 0 ≤ reg n t) (hwt : ∀ n t, 0 ≤ wt n t)
    (hw : ∀ n t, AEStronglyMeasurable (w n t) ν) (hwb : ∀ n t, ∀ᵐ x ∂ν, ‖w n t x‖ ≤ W)
    (hepNorm : ∀ n t z, z ∈ s →
      (eLpNorm (fun x => ph n t z x - p z x) 2 ν).toReal ≤ reg n t)
    (heaNorm : ∀ n t z, z ∈ s →
      (eLpNorm (fun x => ah n t z x - a z x) 2 ν).toReal ≤ wt n t)
    (hetNorm : ∀ n t, (eLpNorm (fun x => th n t x - tau x) 2 ν).toReal ≤ wt n t)
    (hr : Causalean.Stat.IsLittleOp reg
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ)) μ)
    (hwtRate : Causalean.Stat.IsLittleOp wt
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ)) μ) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => Real.sqrt ((n + 1 : ℕ) : ℝ) * ∫ x, w n t x *
        ((∑ z ∈ s, ah n t z x * phi z x (ph n t z x)) +
          (th n t x)⁻¹ * (∑ z ∈ s, mass z x * dphi z x (ph n t z x) *
            (p z x - ph n t z x)) - q x) ∂ν) atTop (fun _ _ => 0) := by
  let C := W * (s.card : ℝ) * (Lip + B + B / c) + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  apply dml_quadratic_bias_root_n_negligible μ _ reg wt C hC hr hwtRate
  intro n t
  have hb := (fitted_pooled_policy_ae_weighted_quadratic_bound ν phi dphi hd
    B Lip c hB hLip hc hbound hlip s p (ph n t) a (ah n t) mass q tau (th n t)
    (hden n t) ha hp (hph n t) hcommon hs (hsh n t) hab
    (hep n t) (hea n t) (het n t) (hm n t) (w n t) W (reg n t) (wt n t) hW
    (hreg n t) (hwt n t) (hw n t) (hwb n t)
    (hepNorm n t) (heaNorm n t) (hetNorm n t)).2
  apply hb.trans
  have hn : 0 ≤ reg n t * wt n t := mul_nonneg (hreg n t) (hwt n t)
  calc
    _ ≤ W * (s.card : ℝ) *
        ((Lip + B + B / c) * (reg n t ^ 2 + reg n t * wt n t)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [mul_nonneg (by positivity : 0 ≤ B + B / c) (sq_nonneg (reg n t)),
        mul_nonneg hLip hn]
    _ = (C - 1) * (reg n t ^ 2 + reg n t * wt n t) := by dsimp only [C]; ring
    _ ≤ C * (reg n t ^ 2 + reg n t * wt n t) :=
      mul_le_mul_of_nonneg_right (by linarith) (add_nonneg (sq_nonneg _) hn)


end Papers.TbsPrteOptimalTransport

module
public import Papers.TsAdaptiveEstimationInference.Helpers.TRAEVectorCoordinates
/-! Population coordinate norms for localized iterative TRAE increments. -/
public section
set_option linter.style.longLine false
set_option linter.unusedVariables false
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory
open scoped ENNReal
variable {W X Z : Type*} [MeasurableSpace W] [MeasurableSpace X]
  [MeasurableSpace Z] (V : IVWorld W X Z)

/-- If [the model classes are bounded by B](hyp:hB), [these bounds hold outside
one common null set](hyp:hCommonB), and [k is an admissible critic](hyp:hk), then
[the absolute value of its instrument-based representative is almost everywhere
at most its essential supremum under the instrument distribution, including
when that supremum is zero](goal). -/
-- @node: trae_critic_ae_infinity_bound
lemma trae_critic_ae_infinity_bound (B : ℝ) (hB : TRAEBoundedness V B) (hCommonB : TRAECommonNullSetBoundedness V B)
    (k : V.Qbar.toSubmodule) (hk : k ∈ V.F) :
    ∀ᵐ w ∂V.law, |dualVersion V k (V.zOf w)| ≤
      (eLpNorm (dualVersion V k) ⊤ (V.law.map V.zOf)).toReal := by
  have ha : ∀ᵐ z ∂V.law.map V.zOf, ‖dualVersion V k z‖ ≤ B := by
    apply (ae_map_iff V.measurable_z.aemeasurable (by
      exact measurableSet_le ((V.dual_measurable k).norm) measurable_const)).2
    filter_upwards [hB.2.2.2.1] with w hw
    simpa only [Real.norm_eq_abs] using hw k hk
  have he := eLpNormEssSup_le_of_ae_bound ha
  have hfin : eLpNormEssSup (dualVersion V k) (V.law.map V.zOf) ≠ ⊤ :=
    ne_of_lt (he.trans_lt ENNReal.ofReal_lt_top)
  have hbound : ∀ᵐ z ∂V.law.map V.zOf, |dualVersion V k z| ≤
      (eLpNorm (dualVersion V k) ⊤ (V.law.map V.zOf)).toReal := by
    filter_upwards [ae_le_eLpNormEssSup (f := dualVersion V k)
      (μ := V.law.map V.zOf)] with z hz
    have ht := ENNReal.toReal_mono hfin hz
    simpa only [toReal_enorm, Real.norm_eq_abs, eLpNorm_exponent_top] using ht
  exact ae_of_ae_map V.measurable_z.aemeasurable hbound

/-- [The population integral of the squared difference between the
instrument-based representatives of f and k equals the squared L2 norm of
their difference](goal). -/
-- @node: trae_dual_difference_energy
lemma trae_dual_difference_energy (f k : V.Qbar.toSubmodule) :
    (∫ w, (dualVersion V f (V.zOf w) - dualVersion V k (V.zOf w)) ^ 2
      ∂V.law) = ‖f - k‖ ^ 2 := by
  calc
    _ = ∫ w, ((f - k : V.Qbar.toSubmodule) : Lp ℝ 2 V.law) w ^ 2 ∂V.law := by
      apply integral_congr_ae
      filter_upwards [V.dual_coherent f, V.dual_coherent k,
        Lp.coeFn_sub (f : Lp ℝ 2 V.law) (k : Lp ℝ 2 V.law)] with w hf hk he
      change (V.dualRealization f (V.zOf w) - V.dualRealization k (V.zOf w)) ^ 2 = _
      rw [hf, hk]
      exact congrArg (fun x : ℝ => x ^ 2) he.symm
    _ = _ := by
      simpa only [L2.inner_def, RCLike.inner_apply, conj_trivial, ← pow_two,
        Submodule.norm_coe] using
        real_inner_self_eq_norm_sq ((f - k : V.Qbar.toSubmodule) : Lp ℝ 2 V.law)

/-- If [the model classes are bounded by B](hyp:hB), [these bounds hold outside
one common null set](hyp:hCommonB), [h is an admissible hypothesis](hyp:hh), and
[k is an admissible critic](hyp:hk), then [the population L2 norm of the
difference between the products h times f and g times k is at most twice the
sum of B times the critic difference norm and the hypothesis difference norm
times the essential supremum of k's instrument-based representative](goal).

Coherence is used only under the population integral. -/
-- @node: trae_product_increment_input_norm
lemma trae_product_increment_input_norm (B : ℝ) (hB : TRAEBoundedness V B) (hCommonB : TRAECommonNullSetBoundedness V B)
    (h g : V.Hbar.toSubmodule) (f k : V.Qbar.toSubmodule)
    (hh : h ∈ V.H) (hk : k ∈ V.F) :
    inputL2Norm V.law (fun w =>
      primalVersion V h (V.xOf w) * dualVersion V f (V.zOf w) -
        primalVersion V g (V.xOf w) * dualVersion V k (V.zOf w)) ≤
      2 * (B * ‖f - k‖ + ‖h - g‖ *
        (eLpNorm (dualVersion V k) ⊤ (V.law.map V.zOf)).toReal) := by
  let L := (eLpNorm (dualVersion V k) ⊤ (V.law.map V.zOf)).toReal
  let p := fun w => primalVersion V h (V.xOf w) - primalVersion V g (V.xOf w)
  let q := fun w => dualVersion V f (V.zOf w) - dualVersion V k (V.zOf w)
  have hp : MemLp p 2 V.law := by
    apply (memLp_congr_ae ((V.primal_coherent h).sub (V.primal_coherent g))).2
    exact (Lp.memLp (h : Lp ℝ 2 V.law)).sub (Lp.memLp (g : Lp ℝ 2 V.law))
  have hq : MemLp q 2 V.law := by
    apply (memLp_congr_ae ((V.dual_coherent f).sub (V.dual_coherent k))).2
    exact (Lp.memLp (f : Lp ℝ 2 V.law)).sub (Lp.memLp (k : Lp ℝ 2 V.law))
  have hpint : (∫ w, p w ^ 2 ∂V.law) = ‖h - g‖ ^ 2 :=
    trae_primal_difference_energy V h g
  have hqint : (∫ w, q w ^ 2 ∂V.law) = ‖f - k‖ ^ 2 :=
    trae_dual_difference_energy V f k
  have hpoint : ∀ᵐ w ∂V.law,
      (primalVersion V h (V.xOf w) * dualVersion V f (V.zOf w) -
        primalVersion V g (V.xOf w) * dualVersion V k (V.zOf w)) ^ 2 ≤
        2 * B ^ 2 * q w ^ 2 + 2 * L ^ 2 * p w ^ 2 := by
    filter_upwards [hB.2.2.1, trae_critic_ae_infinity_bound V B hB hCommonB k hk] with w hw hwk
    have hh2 : primalVersion V h (V.xOf w) ^ 2 ≤ B ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hw h hh) 2
    have hk2 : dualVersion V k (V.zOf w) ^ 2 ≤ L ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hwk 2
    have hb := mul_le_mul_of_nonneg_right hh2 (sq_nonneg (q w))
    have hc := mul_le_mul_of_nonneg_right hk2 (sq_nonneg (p w))
    have hs := sq_nonneg (primalVersion V h (V.xOf w) * q w -
      p w * dualVersion V k (V.zOf w))
    dsimp [p, q] at *
    nlinarith only [hb, hc, hs]
  have hi := integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun w => sq_nonneg
      (primalVersion V h (V.xOf w) * dualVersion V f (V.zOf w) -
        primalVersion V g (V.xOf w) * dualVersion V k (V.zOf w)))
    ((hq.integrable_sq.const_mul (2 * B ^ 2)).add
      (hp.integrable_sq.const_mul (2 * L ^ 2))) hpoint
  simp only [Pi.add_apply] at hi
  rw [integral_add (hq.integrable_sq.const_mul _) (hp.integrable_sq.const_mul _),
    integral_const_mul, integral_const_mul, hpint, hqint] at hi
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity [hB.1], ?_⟩
  have hcross : 0 ≤ B * ‖f - k‖ * (‖h - g‖ * L) := by positivity [hB.1]
  change _ ≤ (2 * (B * ‖f - k‖ + ‖h - g‖ * L)) ^ 2
  nlinarith only [hi, hcross, sq_nonneg (B * ‖f - k‖),
    sq_nonneg (‖h - g‖ * L)]

/-- Assume [the model classes are bounded by B](hyp:hB), [these bounds hold
outside one common null set](hyp:hCommonB), and [the population second moment
of each moment-map difference between admissible critics is bounded by Cm
times their squared L2 distance](hyp:hm). Then [one positive constant bounds
the sum of the population L2 norms of the moment-map, hypothesis-critic product
and critic increments by the hypothesis difference norm times the essential
supremum of the second critic plus the critic difference norm, uniformly over
admissible first hypotheses, arbitrary second hypotheses and admissible
critics](goal). -/
-- @node: trae_increment_input_norms
lemma trae_increment_input_norms (B Cm : ℝ) (hB : TRAEBoundedness V B) (hCommonB : TRAECommonNullSetBoundedness V B)
    (hm : ∀ f ∈ V.F, ∀ k ∈ V.F,
      (∫ w, V.m (f - k) w ^ 2 ∂V.law) ≤ Cm * ‖f - k‖ ^ 2) :
    ∃ N > 0, ∀ h ∈ V.H, ∀ g : V.Hbar.toSubmodule, ∀ f ∈ V.F, ∀ k ∈ V.F,
      inputL2Norm V.law (V.m f - V.m k) +
        inputL2Norm V.law (fun w =>
          primalVersion V h (V.xOf w) * dualVersion V f (V.zOf w) -
            primalVersion V g (V.xOf w) * dualVersion V k (V.zOf w)) +
        inputL2Norm V.law (fun w =>
          dualVersion V f (V.zOf w) - dualVersion V k (V.zOf w)) ≤
      N * (‖h - g‖ * (eLpNorm (dualVersion V k) ⊤
        (V.law.map V.zOf)).toReal + ‖f - k‖) := by
  let M := max Cm 0
  let N := Real.sqrt M + 2 * B + 3
  refine ⟨N, by dsimp [N]; positivity [hB.1], ?_⟩
  intro h hh g f hf k hk
  have hmle : inputL2Norm V.law (V.m f - V.m k) ≤ Real.sqrt M * ‖f - k‖ := by
    rw [← map_sub]
    unfold inputL2Norm
    calc
      _ ≤ Real.sqrt (M * ‖f - k‖ ^ 2) := Real.sqrt_le_sqrt
        ((hm f hf k hk).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)))
      _ = _ := by rw [Real.sqrt_mul (le_max_right _ _), Real.sqrt_sq (norm_nonneg _)]
  have hprod := trae_product_increment_input_norm V B hB hCommonB h g f k hh hk
  have hdual : inputL2Norm V.law (fun w =>
      dualVersion V f (V.zOf w) - dualVersion V k (V.zOf w)) = ‖f - k‖ := by
    rw [inputL2Norm, trae_dual_difference_energy, Real.sqrt_sq (norm_nonneg _)]
  rw [hdual]
  have hN2 : 2 ≤ N := by dsimp [N]; nlinarith only [hB.1, Real.sqrt_nonneg M]
  have hNcoef : Real.sqrt M + 2 * B + 1 ≤ N := by dsimp [N]; linarith
  have hx := mul_le_mul_of_nonneg_right hN2
    (show 0 ≤ ‖h - g‖ * (eLpNorm (dualVersion V k) ⊤
      (V.law.map V.zOf)).toReal by positivity)
  have hy := mul_le_mul_of_nonneg_right hNcoef (norm_nonneg (f - k))
  nlinarith only [hmle, hprod, hx, hy]

/-- If [N is nonnegative](hyp:hN), [K is nonnegative](hyp:hK), [the radius r is
nonnegative](hyp:hr), [A is nonnegative](hyp:hA), [D is nonnegative](hyp:hD), and
[the sum of the three coordinate sizes is at most N times the sum of A and
D](hyp:hcoords), then [K times the sum of r times those coordinate sizes and
squared r is at most K times N plus one, times the sum of r times A, r times D
and squared r](goal). -/
-- @node: trae_increment_remainder_le
lemma trae_increment_remainder_le (N K r x y z A D : ℝ)
    (hN : 0 ≤ N) (hK : 0 ≤ K) (hr : 0 ≤ r) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hcoords : x + y + z ≤ N * (A + D)) :
    K * (r * (x + y + z) + r ^ 2) ≤
      K * (N + 1) * (r * A + r * D + r ^ 2) := by
  rw [mul_assoc K (N + 1)]
  apply mul_le_mul_of_nonneg_left _ hK
  have hi := mul_le_mul_of_nonneg_left hcoords hr
  nlinarith only [hi, mul_nonneg hN (sq_nonneg r), mul_nonneg hr hA,
    mul_nonneg hr hD]

end Papers.TsAdaptiveEstimationInference

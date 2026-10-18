module
public import Papers.TbsNeuralCausalPi.Helpers.DoseResponseNonDescendant
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
/-! # Bounds for structural regression versions outside observational support

The observational conditional-expectation bound supplies one anchor in the
allowed input domain. Its diameter and the structural Lipschitz inequality
then bound the regression throughout that domain, including off support.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory Filter
open scoped NNReal ENNReal

/-- If [the covariate map is measurable](hyp:hs), [the regression function is
measurable](hyp:hf), [the outcome is almost surely bounded in absolute value by K](hyp:hY),
and [the regression evaluated at the covariates equals the conditional expectation
almost surely](hyp:hreg), then [the regression is bounded in absolute value by K
almost everywhere under the covariate law](goal). -/
-- @node: regression_version_ae_abs_le
lemma regression_version_ae_abs_le
    {Ω X : Type*} {m : MeasurableSpace Ω} [MeasurableSpace Ω] [MeasurableSpace X]
    (mu : Measure Ω) (s : Ω → X) (hs : Measurable s)
    (Y : Ω → ℝ) (f : X → ℝ) (hf : Measurable f) (K : ℝ)
    (hY : ∀ᵐ z ∂mu, |Y z| ≤ K)
    (hreg : (fun z => f (s z)) =ᵐ[mu] mu[Y | m]) :
    ∀ᵐ x ∂mu.map s, |f x| ≤ K := by
  have hc := ae_bdd_abs_condExp_of_ae_bdd_abs (m := m) hY
  apply (ae_map_iff hs.aemeasurable
    (measurableSet_le hf.abs measurable_const)).2
  filter_upwards [hc, hreg] with z hz heq
  rw [heq]
  exact hz

/-- For [a nonnegative Lipschitz constant L](hyp:L), if [the probability law
assigns full mass to Q](hyp:hQ), [the function is almost surely bounded in absolute
value by K](hyp:hbound), [it is L-Lipschitz on Q](hyp:hLip), and [any two points
of Q are at distance at most D](hyp:hdiam), then [its absolute value everywhere
on Q is at most K + L D](goal). -/
-- @node: lipschitzOn_abs_le_of_ae_anchor
lemma lipschitzOn_abs_le_of_ae_anchor
    {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    (mu : Measure X) [IsProbabilityMeasure mu] (Q : Set X)
    (f : X → ℝ) (L : ℝ≥0) (K D : ℝ)
    (hQ : ∀ᵐ x ∂mu, x ∈ Q) (hbound : ∀ᵐ x ∂mu, |f x| ≤ K)
    (hLip : LipschitzOnWith L f Q)
    (hdiam : ∀ x ∈ Q, ∀ y ∈ Q, dist x y ≤ D) :
    ∀ x ∈ Q, |f x| ≤ K + L * D := by
  obtain ⟨a, haQ, ha⟩ := (hQ.and hbound).exists
  intro x hx
  calc
    |f x| ≤ |f x - f a| + |f a| := by
      simpa only [sub_add_cancel] using abs_add_le (f x - f a) (f a)
    _ ≤ (L : ℝ) * dist x a + K := by
      have h := hLip.dist_le_mul x hx a haQ
      rw [Real.dist_eq] at h
      exact add_le_add h ha
    _ ≤ K + L * D := by
      have h := mul_le_mul_of_nonneg_left (hdiam x hx a haQ) L.coe_nonneg
      linarith

/-- If [every coordinate of x has absolute value at most K](hyp:hx) and
[every coordinate of y has absolute value at most K](hyp:hy), then [their
one-norm distance in q dimensions is at most 2 K q](goal). -/
-- @node: l1_coordinate_box_dist_le
lemma l1_coordinate_box_dist_le {q : ℕ} {K : ℝ} {x y : L1Vec q}
    (hx : ∀ j, |x.ofLp j| ≤ K) (hy : ∀ j, |y.ofLp j| ≤ K) :
    dist x y ≤ 2 * K * q := by
  rw [PiLp.dist_eq_of_L1]
  calc
    (∑ j : Fin q, dist (x.ofLp j) (y.ofLp j)) ≤ ∑ _j : Fin q, 2 * K := by
      apply Finset.sum_le_sum
      intro j _
      rw [Real.dist_eq]
      exact (abs_sub _ _).trans (by linarith [hx j, hy j])
    _ = _ := by simp; ring

/-- Suppose [the covariate map is measurable](hyp:hs), [the regression is
measurable](hyp:hf), [Q is measurable](hyp:hQ), and [L is a nonnegative
constant](hyp:L). If [the covariates lie in Q almost surely](hyp:hsQ), [every
coordinate on Q is bounded in absolute value by K](hyp:hbox), [the outcome is
almost surely bounded in absolute value by K](hyp:hY), [the regression at the
covariates equals the conditional expectation almost surely](hyp:hreg), and
[the regression is L-Lipschitz on Q](hyp:hLip), then [its absolute value on Q
is at most K times (1 + 2 q L)](goal). -/
-- @node: bounded_regression_on_coordinate_domain
lemma bounded_regression_on_coordinate_domain
    {Ω : Type*} {m : MeasurableSpace Ω} [MeasurableSpace Ω] {q : ℕ}
    (mu : Measure Ω) [IsProbabilityMeasure mu] (s : Ω → L1Vec q) (hs : Measurable s)
    (Y : Ω → ℝ) (f : L1Vec q → ℝ) (hf : Measurable f)
    (Q : Set (L1Vec q)) (hQ : MeasurableSet Q) (K : ℝ) (L : ℝ≥0)
    (hsQ : ∀ᵐ z ∂mu, s z ∈ Q)
    (hbox : ∀ x ∈ Q, ∀ j, |x.ofLp j| ≤ K)
    (hY : ∀ᵐ z ∂mu, |Y z| ≤ K)
    (hreg : (fun z => f (s z)) =ᵐ[mu] mu[Y | m])
    (hLip : LipschitzOnWith L f Q) :
    ∀ x ∈ Q, |f x| ≤ K * (1 + 2 * q * L) := by
  have : IsProbabilityMeasure (mu.map s) := Measure.isProbabilityMeasure_map hs.aemeasurable
  have hcarry : ∀ᵐ x ∂mu.map s, x ∈ Q :=
    (ae_map_iff hs.aemeasurable hQ).2 hsQ
  have hb := regression_version_ae_abs_le mu s hs Y f hf K hY hreg
  have h := lipschitzOn_abs_le_of_ae_anchor (mu.map s) Q f L K (2 * K * q)
    hcarry hb hLip (fun x hx y hy => l1_coordinate_box_dist_le (hbox x hx) (hbox y hy))
  intro x hx
  calc
    |f x| ≤ K + L * (2 * K * q) := h x hx
    _ = K * (1 + 2 * q * L) := by ring

/-- If [d decomposes as b + c](hyp:hd) and [the absolute value of c is at most
R](hyp:hc), then [the square of d is at most twice the square of b plus twice
the square of R](goal). -/
-- @node: dose_response_square_le_of_decomposition
lemma dose_response_square_le_of_decomposition {d b c R : ℝ}
    (hd : d = b + c) (hc : |c| ≤ R) : d^2 ≤ 2*b^2 + 2*R^2 := by
  have hc2 : c^2 ≤ R^2 := by
    have h := mul_self_le_mul_self (abs_nonneg c) hc
    simpa only [← sq, sq_abs] using h
  rw [hd]
  nlinarith [sq_nonneg (b-c)]

/-- If [d is measurable](hyp:hd), [the square of b is integrable](hyp:hb),
[delta is positive](hyp:hdelta), [d equals b + c almost everywhere](hyp:hdecomp),
[the absolute value of c is at most Ly W almost everywhere](hyp:hc), and
[delta times the integral of the square of b is at most CW W](hyp:hreg), then
[the integral of the square of d is at most 2 CW W / delta plus
2 Ly squared W squared times the total mass of the measure](goal). -/
-- @node: dose_response_integrated_decomposition_le
lemma dose_response_integrated_decomposition_le
    {X : Type*} [MeasurableSpace X] (mu : Measure X) [IsFiniteMeasure mu]
    (d b c : X → ℝ) (hd : Measurable d)
    (hb : Integrable (fun t => (b t)^2) mu)
    (Ly W CW delta : ℝ) (hdelta : 0 < delta)
    (hdecomp : ∀ᵐ t ∂mu, d t = b t + c t)
    (hc : ∀ᵐ t ∂mu, |c t| ≤ Ly * W)
    (hreg : delta * (∫ t, (b t)^2 ∂mu) ≤ CW * W) :
    (∫ t, (d t)^2 ∂mu) ≤
      2*CW/delta*W + 2*Ly^2*W^2*(mu Set.univ).toReal := by
  have hpoint : ∀ᵐ t ∂mu, (d t)^2 ≤ 2*(b t)^2 + 2*(Ly*W)^2 := by
    filter_upwards [hdecomp, hc] with t ht hct
    exact dose_response_square_le_of_decomposition ht hct
  have hmajor : Integrable (fun t => 2*(b t)^2 + 2*(Ly*W)^2) mu :=
    (hb.const_mul 2).add (integrable_const _)
  have hdm : AEStronglyMeasurable (fun t => (d t)^2) mu := by fun_prop
  have hdi : Integrable (fun t => (d t)^2) mu := by
    apply hmajor.mono' hdm
    filter_upwards [hpoint] with t ht
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (d t))] using ht
  have hquot : (∫ t, (b t)^2 ∂mu) ≤ CW * W / delta :=
    (le_div_iff₀ hdelta).2 (by simpa only [mul_comm] using hreg)
  calc
    (∫ t, (d t)^2 ∂mu) ≤ ∫ t, (2*(b t)^2 + 2*(Ly*W)^2) ∂mu :=
      integral_mono_ae hdi hmajor hpoint
    _ = 2*(∫ t, (b t)^2 ∂mu) + 2*(Ly*W)^2*(mu Set.univ).toReal := by
      rw [integral_add (hb.const_mul 2) (integrable_const _), integral_const_mul]
      simp only [integral_const, smul_eq_mul, Measure.real]
      ring
    _ ≤ 2*(CW*W/delta) + 2*(Ly*W)^2*(mu Set.univ).toReal := by
      gcongr
    _ = _ := by ring

end Papers.TbsNeuralCausalPi

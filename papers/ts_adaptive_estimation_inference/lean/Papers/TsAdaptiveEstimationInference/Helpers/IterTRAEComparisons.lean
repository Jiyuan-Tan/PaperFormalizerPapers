module
public import Papers.TsAdaptiveEstimationInference.Helpers.IterTRAESetup
/-! Deterministic game comparisons used by iterative TRAE propagation. -/
public section
set_option linter.style.haveILetI false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.style.longLine false
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory
open scoped Topology
variable {𝒲 𝒳 𝒵 Ω : Type*} [MeasurableSpace 𝒲] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒵] [MeasurableSpace Ω]
  (V : IVWorld 𝒲 𝒳 𝒵) (P : Measure Ω)
  (sample : AnalysisSample V P) (split : SampleSplit)

/-- [For any primal hypothesis and dual critic in their respective Hilbert
spaces, the TRAE game integrand is integrable under the population law](goal). -/
-- @node: traeIntegrand_integrable
lemma traeIntegrand_integrable (h : V.Hbar.toSubmodule) (f : V.Qbar.toSubmodule) :
    Integrable (traeIntegrand V h f) V.law := by
  have hprod : (fun w => primalVersion V h (V.xOf w) * dualVersion V f (V.zOf w))
      =ᵐ[V.law] (fun w => (h : Lp ℝ 2 V.law) w * (f : Lp ℝ 2 V.law) w) :=
    (V.primal_coherent h).mul (V.dual_coherent f)
  have hsquare : (fun w => dualVersion V f (V.zOf w) ^ 2)
      =ᵐ[V.law] (fun w => (f : Lp ℝ 2 V.law) w ^ 2) :=
    (V.dual_coherent f).mono fun w hw => congrArg (fun x : ℝ => x ^ 2) hw
  have hp : Integrable (fun w => primalVersion V h (V.xOf w) *
      dualVersion V f (V.zOf w)) V.law := by
    apply Integrable.congr _ hprod.symm
    simpa only [RCLike.inner_apply, conj_trivial, mul_comm] using
      (L2.integrable_inner (𝕜 := ℝ) (h : Lp ℝ 2 V.law) (f : Lp ℝ 2 V.law))
  have hq : Integrable (fun w => dualVersion V f (V.zOf w) ^ 2) V.law := by
    apply Integrable.congr _ hsquare.symm
    simpa only [RCLike.inner_apply, conj_trivial, pow_two] using
      (L2.integrable_inner (𝕜 := ℝ) (f : Lp ℝ 2 V.law) (f : Lp ℝ 2 V.law))
  have hi := ((V.integrable_m f).const_mul 2 |>.sub (hp.const_mul 2)).sub hq
  convert hi using 1
  ext w
  simp only [traeIntegrand, Pi.sub_apply]
  ring

/-- Under [the range condition](hyp:hRange), [the population game value at any
hypothesis and critic equals the squared norm of the projected residual minus
the squared distance between the critic and that residual](goal). -/
-- @node: trae_integrand_quadratic
lemma trae_integrand_quadratic (hRange : RangeCondition V)
    (h : V.Hbar.toSubmodule) (f : V.Qbar.toSubmodule) :
    (∫ w, traeIntegrand V h f w ∂V.law) =
      ‖projCondExpOp V (minNormSolution V - h)‖ ^ 2 -
        ‖f - projCondExpOp V (minNormSolution V - h)‖ ^ 2 := by
  rw [trae_integrand_mean V hRange, norm_sub_sq_real]
  rw [real_inner_comm f]
  ring

/-- Under [the range condition](hyp:hRange), with [a nonnegative deviation
constant](hyp:hC) and [a nonnegative radius](hyp:hr), if [every feasible critic's
absolute empirical game deviation at the hypothesis is bounded by the constant
times the radius times its norm plus the squared radius](hyp:habs), [the set of
empirical game values over feasible critics is bounded above](goal). -/
-- @node: trae_empirical_bddAbove
lemma trae_empirical_bddAbove (hRange : RangeCondition V) (n : ℕ) (ω : Ω)
    (C r : ℝ) (hC : 0 ≤ C) (hr : 0 ≤ r) (h : V.Hbar.toSubmodule)
    (habs : ∀ f ∈ V.F,
      |blockAverage V P sample (split.fit n) (traeIntegrand V h f) ω -
        ∫ w, traeIntegrand V h f w ∂V.law| ≤ C * (r * ‖f‖ + r ^ 2)) :
    BddAbove (Set.range (fun f : V.F =>
      blockAverage V P sample (split.fit n) (traeIntegrand V h f) ω)) := by
  let R := ‖projCondExpOp V (minNormSolution V - h)‖
  refine ⟨(R + C * r) ^ 2 + C * r ^ 2, ?_⟩
  rintro _ ⟨f, rfl⟩
  have ha := (abs_le.mp (habs f f.property)).2
  rw [trae_integrand_mean V hRange] at ha
  have hi := real_inner_le_norm (projCondExpOp V (minNormSolution V - h)) f
  change inner ℝ (projCondExpOp V (minNormSolution V - h)) f ≤ R * ‖(f : V.Qbar.toSubmodule)‖ at hi
  nlinarith [sq_nonneg (‖(f : V.Qbar.toSubmodule)‖ - (R + C * r)), mul_nonneg (mul_nonneg hC hr) (norm_nonneg (f : V.Qbar.toSubmodule))]

/-- Assume [the range condition](hyp:hRange), [feasibility of residual
critics](hyp:hClose), [a nonnegative deviation constant](hyp:hC), [a nonnegative
radius](hyp:hr), [a class hypothesis](hyp:hh), and [a class comparator](hyp:hg).
If [absolute game deviations at the hypothesis obey the radius-times-critic-norm
bound](hyp:habs), [increments from the comparator and its residual critic obey
the localized bound in hypothesis distance, residual-critic supremum norm, and
critic distance](hyp:hinc), and [the empirical excess loss is at most the
penalty times the center increment](hyp:hopt), [the population excess loss is at
most that same penalty term plus the squared deviation constant plus twice that
constant plus one, multiplied by the sum of the radius times hypothesis
distance times residual-critic supremum norm, the radius times projected
hypothesis distance, and the squared radius](goal). -/
-- @node: iter_trae_biasless_on_event
lemma iter_trae_biasless_on_event (hRange : RangeCondition V)
    (hClose : ClosenessCondition V) (n : ℕ) (ω : Ω) (C r lam I : ℝ)
    (hC : 0 ≤ C) (hr : 0 ≤ r)
    (h g : V.Hbar.toSubmodule) (hh : h ∈ V.H) (hg : g ∈ V.H)
    (habs : ∀ f ∈ V.F,
      |blockAverage V P sample (split.fit n) (traeIntegrand V h f) ω -
        ∫ w, traeIntegrand V h f w ∂V.law| ≤ C * (r * ‖f‖ + r ^ 2))
    (hinc : ∀ a ∈ V.H, ∀ f ∈ V.F,
      |blockAverage V P sample (split.fit n)
          (fun w => traeIntegrand V a f w - traeIntegrand V g
            (projCondExpOp V (minNormSolution V - g)) w) ω -
        ∫ w, traeIntegrand V a f w - traeIntegrand V g
          (projCondExpOp V (minNormSolution V - g)) w ∂V.law| ≤
      C * (r * ‖a - g‖ *
        (eLpNorm (dualVersion V (projCondExpOp V (minNormSolution V - g)))
          ⊤ (V.law.map V.zOf)).toReal +
        r * ‖f - projCondExpOp V (minNormSolution V - g)‖ + r ^ 2))
    (hopt : traeEmpiricalLoss V P sample split n ω h -
      traeEmpiricalLoss V P sample split n ω g ≤ lam * I) :
    traePopulationLoss V h - traePopulationLoss V g ≤ lam * I +
      (C ^ 2 + 2 * C + 1) *
        (r * ‖h - g‖ *
          (eLpNorm (dualVersion V (projCondExpOp V (minNormSolution V - g)))
            ⊤ (V.law.map V.zOf)).toReal +
          r * ‖projCondExpOp V (h - g)‖ + r ^ 2) := by
  let k := projCondExpOp V (minNormSolution V - g)
  let fbar := projCondExpOp V (minNormSolution V - h)
  let emp := fun a f => blockAverage V P sample (split.fit n) (traeIntegrand V a f) ω
  let pop := fun a f => ∫ w, traeIntegrand V a f w ∂V.law
  have hk : k ∈ V.F := hClose g hg
  have hfbar : fbar ∈ V.F := hClose h hh
  haveI : Nonempty V.F := ⟨⟨k, hk⟩⟩
  have hlin (a : V.Hbar.toSubmodule) (f : V.Qbar.toSubmodule) :
      blockAverage V P sample (split.fit n)
        (fun w => traeIntegrand V a f w - traeIntegrand V g k w) ω -
      (∫ w, traeIntegrand V a f w - traeIntegrand V g k w ∂V.law) =
      (emp a f - emp g k) - (pop a f - pop g k) := by
    rw [integral_sub (traeIntegrand_integrable V a f) (traeIntegrand_integrable V g k)]
    dsimp [emp, pop, blockAverage]
    rw [Finset.sum_sub_distrib]
    ring
  have hquad (f : V.Qbar.toSubmodule) : pop g f - pop g k = -‖f - k‖ ^ 2 := by
    dsimp [pop]
    rw [trae_integrand_quadratic V hRange, trae_integrand_quadratic V hRange]
    change ‖k‖ ^ 2 - ‖f - k‖ ^ 2 - (‖k‖ ^ 2 - ‖k - k‖ ^ 2) = _
    simp
  have hgUpper : traeEmpiricalLoss V P sample split n ω g ≤
      emp g k + (C ^ 2 + C) * r ^ 2 := by
    unfold traeEmpiricalLoss
    apply ciSup_le
    intro f
    have hi := (abs_le.mp (hinc g hg f f.property)).2
    rw [hlin, hquad] at hi
    simp only [sub_self, norm_zero, mul_zero, zero_mul, zero_add] at hi
    nlinarith [sq_nonneg (‖(f : V.Qbar.toSubmodule) - k‖ - C * r)]
  have hhLower : emp h fbar ≤ traeEmpiricalLoss V P sample split n ω h :=
    le_ciSup (trae_empirical_bddAbove V P sample split hRange n ω C r hC hr h habs)
      (⟨fbar, hfbar⟩ : V.F)
  have hdiff : ‖fbar - k‖ = ‖projCondExpOp V (h - g)‖ := by
    have he : fbar - k = -(projCondExpOp V (h - g)) := by
      dsimp [fbar, k]
      simp only [map_sub]
      abel
    rw [he, norm_neg]
  have hpop : pop h fbar - pop g k = traePopulationLoss V h - traePopulationLoss V g := by
    dsimp [pop]
    rw [trae_integrand_quadratic V hRange, trae_integrand_quadratic V hRange,
      traePopulationLoss_eq V hRange hClose h hh, traePopulationLoss_eq V hRange hClose g hg]
    have he (a : V.Hbar.toSubmodule) :
        projCondExpOp V (minNormSolution V - a) = -(projCondExpOp V (a - minNormSolution V)) := by
      rw [← map_neg, neg_sub]
    simp only [fbar, k, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), sub_zero, he, norm_neg]
  have hi := (abs_le.mp (hinc h hh fbar hfbar)).1
  rw [hlin, hpop, hdiff] at hi
  have hs : 0 ≤ r * ‖h - g‖ *
      (eLpNorm (dualVersion V k) ⊤ (V.law.map V.zOf)).toReal +
        r * ‖projCondExpOp V (h - g)‖ := by positivity
  have hD : C ≤ C ^ 2 + 2 * C + 1 := by nlinarith [sq_nonneg C]
  have he := mul_le_mul_of_nonneg_right hD hs
  nlinarith [sq_nonneg r]

/-- Assume [the range condition](hyp:hRange), [feasibility of residual
critics](hyp:hClose), [a nonnegative deviation constant](hyp:hC), [a nonnegative
radius](hyp:hr), [a class hypothesis](hyp:hh), and [a class comparator](hyp:hg).
If [absolute game deviations at the hypothesis satisfy the localized critic-norm
bound](hyp:habs), [the comparator's empirical loss is at most five quarters of
its population loss plus the constant times the squared radius](hyp:hgUpper),
and [the empirical excess loss is at most the penalty times the center
increment](hyp:hopt), [the population excess loss is at most that penalty term
plus the squared constant plus four times the constant plus one, multiplied by
the sum of the comparator's squared projected error, the radius times the
projected hypothesis-comparator distance, and the squared radius](goal). -/
-- @node: iter_trae_ordinary_on_event
lemma iter_trae_ordinary_on_event (hRange : RangeCondition V)
    (hClose : ClosenessCondition V) (n : ℕ) (ω : Ω) (C r lam I : ℝ)
    (hC : 0 ≤ C) (hr : 0 ≤ r)
    (h g : V.Hbar.toSubmodule) (hh : h ∈ V.H) (hg : g ∈ V.H)
    (habs : ∀ f ∈ V.F,
      |blockAverage V P sample (split.fit n) (traeIntegrand V h f) ω -
        ∫ w, traeIntegrand V h f w ∂V.law| ≤ C * (r * ‖f‖ + r ^ 2))
    (hgUpper : traeEmpiricalLoss V P sample split n ω g ≤
      (5 / 4 : ℝ) * traePopulationLoss V g + C * r ^ 2)
    (hopt : traeEmpiricalLoss V P sample split n ω h -
      traeEmpiricalLoss V P sample split n ω g ≤ lam * I) :
    traePopulationLoss V h - traePopulationLoss V g ≤ lam * I +
      (C ^ 2 + 4 * C + 1) *
        (‖projCondExpOp V (g - minNormSolution V)‖ ^ 2 +
          r * ‖projCondExpOp V (h - g)‖ + r ^ 2) := by
  let fbar := projCondExpOp V (minNormSolution V - h)
  have hfbar : fbar ∈ V.F := hClose h hh
  have hb := trae_empirical_bddAbove V P sample split hRange n ω C r hC hr h habs
  have he := le_ciSup hb (⟨fbar, hfbar⟩ : V.F)
  have ha := (abs_le.mp (habs fbar hfbar)).1
  have hp : (∫ w, traeIntegrand V h fbar w ∂V.law) = traePopulationLoss V h := by
    rw [trae_integrand_quadratic V hRange, traePopulationLoss_eq V hRange hClose h hh]
    have heq : projCondExpOp V (minNormSolution V - h) =
        -(projCondExpOp V (h - minNormSolution V)) := by rw [← map_neg, neg_sub]
    simp only [fbar, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), sub_zero, heq, norm_neg]
  rw [hp] at ha
  have hnorm : ‖fbar‖ ≤ ‖projCondExpOp V (g - minNormSolution V)‖ +
      ‖projCondExpOp V (h - g)‖ := by
    have heq : fbar = -(projCondExpOp V (g - minNormSolution V) +
        projCondExpOp V (h - g)) := by
      dsimp [fbar]
      simp only [map_sub]
      abel
    rw [heq, norm_neg]
    exact norm_add_le _ _
  rw [traePopulationLoss_eq V hRange hClose g hg] at hgUpper
  have hn := mul_le_mul_of_nonneg_left hnorm (mul_nonneg hC hr)
  have hy := mul_nonneg hC (sq_nonneg (r - ‖projCondExpOp V (g - minNormSolution V)‖))
  have hD : C ≤ C ^ 2 + 4 * C + 1 := by nlinarith [sq_nonneg C]
  have hD' : 3 * C ≤ C ^ 2 + 4 * C + 1 := by nlinarith [sq_nonneg C]
  have hD'' : C / 2 + 1 / 4 ≤ C ^ 2 + 4 * C + 1 := by nlinarith [sq_nonneg C]
  have h₁ := mul_le_mul_of_nonneg_right hD (mul_nonneg hr (norm_nonneg (projCondExpOp V (h - g))))
  have h₂ := mul_le_mul_of_nonneg_right hD' (sq_nonneg r)
  have h₃ := mul_le_mul_of_nonneg_right hD'' (sq_nonneg ‖projCondExpOp V (g - minNormSolution V)‖)
  have h₄ := mul_nonneg hC (sq_nonneg r)
  change blockAverage V P sample (split.fit n) (traeIntegrand V h fbar) ω ≤
    traeEmpiricalLoss V P sample split n ω h at he
  rw [traePopulationLoss_eq V hRange hClose g hg]
  nlinarith only [ha, he, hopt, hgUpper, hn, hy, h₁, h₂, h₃, h₄]

/-- Under [TRAE boundedness with envelope bound B](hyp:hB) and [a common
almost-sure envelope for the representatives](hyp:hCommonB), [any feasible
critic](hyp:hf) [has essential-supremum norm at most B under the instrument
distribution](goal). -/
-- @node: trae_critic_infinity_le
lemma trae_critic_infinity_le (B : ℝ) (hB : TRAEBoundedness V B) (hCommonB : TRAECommonNullSetBoundedness V B)
    (f : V.Qbar.toSubmodule) (hf : f ∈ V.F) :
    (eLpNorm (dualVersion V f) ⊤ (V.law.map V.zOf)).toReal ≤ B := by
  have ha : ∀ᵐ z ∂V.law.map V.zOf, ‖dualVersion V f z‖ ≤ B := by
    apply (ae_map_iff V.measurable_z.aemeasurable (by
      exact measurableSet_le ((V.dual_measurable f).norm) measurable_const)).2
    filter_upwards [hCommonB.mono (fun _ hw => hw.2.1)] with w hw
    simpa only [Real.norm_eq_abs] using hw f hf
  have he := eLpNormEssSup_le_of_ae_bound ha
  change eLpNorm (dualVersion V f) ⊤ (V.law.map V.zOf) ≤ ENNReal.ofReal B at he
  exact (ENNReal.toReal_le_toReal (ne_of_lt (he.trans_lt ENNReal.ofReal_lt_top))
    ENNReal.ofReal_ne_top).2 he |>.trans_eq (ENNReal.toReal_ofReal hB.1)

/-- For [a positive weight c](hyp:hc), [the product of two real numbers a and b
is at most c times a squared plus b squared divided by four times c](goal). -/
-- @node: iter_trae_young
lemma iter_trae_young (a b c : ℝ) (hc : 0 < c) :
    a * b ≤ c * a ^ 2 + b ^ 2 / (4 * c) := by
  have hy : a * b * (4 * c) ≤ (c * a ^ 2 + b ^ 2 / (4 * c)) * (4 * c) := by
    field_simp
    nlinarith only [sq_nonneg (2 * c * a - b)]
  exact (mul_le_mul_iff_left₀ (by positivity : 0 < 4 * c)).mp hy

/-- Suppose [the current error e, previous error p, projected error u, and
radius r are nonnegative](hyp:he,hp,hu,hr), [the penalty is positive](hyp:hlam)
and [the penalty is at most two](hyp:hlam2), and [K, C, and B are
nonnegative](hyp:hK,hC,hB). If [the penalty times e squared
plus u squared is at most K times the sum of r e B, r u, and r squared, plus
the penalty times C times the sum of r times the sum of e and p, r squared,
and e p](hyp:hb), [e squared is at most sixteen times the square of the sum of
K times the sum of B and one, twice C, and one, multiplied by the sum of r squared divided by the
squared penalty and p squared](goal). -/
-- @node: iter_trae_strong_absorb
lemma iter_trae_strong_absorb (e p u r lam K C B : ℝ)
    (he : 0 ≤ e) (hp : 0 ≤ p) (hu : 0 ≤ u) (hr : 0 ≤ r)
    (hlam : 0 < lam) (hlam2 : lam ≤ 2)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hb : lam * e ^ 2 + u ^ 2 ≤
      K * (r * e * B + r * u + r ^ 2) +
        lam * C * (r * (e + p) + r ^ 2 + e * p)) :
    e ^ 2 ≤ (16 * (K * (B + 1) + 2 * C + 1) ^ 2) *
      (r ^ 2 / lam ^ 2 + p ^ 2) := by
  let D := K * (B + 1) + 2 * C + 1
  have hlC := mul_le_mul_of_nonneg_right hlam2 hC
  have hD : 1 ≤ D := by dsimp [D]; nlinarith only [hK, hC, mul_nonneg hK hB]
  have hcoeff : K * B + lam * C ≤ D := by dsimp [D]; nlinarith only [hlC, hK, hC]
  have hcoeff' : K + lam * C ≤ D := by dsimp [D]; nlinarith only [hlC, hK, hC, mul_nonneg hK hB]
  have hKD : K ≤ D := by dsimp [D]; nlinarith only [hK, hC, mul_nonneg hK hB]
  have hCD : C ≤ D := by dsimp [D]; nlinarith only [hK, hC, mul_nonneg hK hB]
  have hmajor : lam * e ^ 2 + u ^ 2 ≤
      D * r * e + D * r * u + D * r ^ 2 + lam * D * r * p + lam * D * e * p := by
    have h₁ := mul_le_mul_of_nonneg_right hcoeff (mul_nonneg hr he)
    have h₂ := mul_le_mul_of_nonneg_right hcoeff' (sq_nonneg r)
    have h₃ := mul_le_mul_of_nonneg_right hKD (mul_nonneg hr hu)
    have h₄ := mul_le_mul_of_nonneg_right hCD (show 0 ≤ lam * r * p by positivity)
    have h₅ := mul_le_mul_of_nonneg_right hCD (show 0 ≤ lam * e * p by positivity)
    nlinarith only [hb, h₁, h₂, h₃, h₄, h₅]
  have h₁ := iter_trae_young e (D * r) (lam / 4) (by positivity)
  have h₂ := iter_trae_young u (D * r) (1 / 2) (by norm_num)
  have h₃ := iter_trae_young e (D * p) (1 / 4) (by norm_num)
  have h₄ := iter_trae_young r (D * p) (1 / 2) (by norm_num)
  norm_num at h₁ h₂ h₃ h₄
  simp only [show 4 * (lam / 4) = lam by ring, mul_pow] at h₁
  have h₃' := mul_le_mul_of_nonneg_left h₃ hlam.le
  have h₄' := mul_le_mul_of_nonneg_left h₄ hlam.le
  have hm : lam / 2 * e ^ 2 ≤
      D ^ 2 * r ^ 2 / lam + D ^ 2 * r ^ 2 / 2 + D * r ^ 2 +
        lam / 2 * r ^ 2 + (3 / 2 : ℝ) * lam * D ^ 2 * p ^ 2 := by
    nlinarith only [hmajor, h₁, h₂, h₃', h₄']
  have hlD : lam * D ≤ 2 * D := mul_le_mul_of_nonneg_right hlam2 (by linarith only [hD])
  have hlDsq : lam * D ^ 2 ≤ 2 * D ^ 2 := mul_le_mul_of_nonneg_right hlam2 (sq_nonneg D)
  have hlSq : lam ^ 2 ≤ 4 := by nlinarith only [hlam, hlam2]
  have hDsq : D ≤ D ^ 2 := by nlinarith only [hD]
  have hmul := mul_le_mul_of_nonneg_left hm hlam.le
  have hcancel : lam * (D ^ 2 * r ^ 2 / lam) = D ^ 2 * r ^ 2 := by field_simp
  rw [mul_add, mul_add, mul_add, mul_add, hcancel] at hmul
  have h₅ := mul_le_mul_of_nonneg_right hlDsq (show 0 ≤ r ^ 2 / 2 by positivity)
  have h₆ := mul_le_mul_of_nonneg_right hlD (sq_nonneg r)
  have h₇ := mul_le_mul_of_nonneg_right hlSq (show 0 ≤ r ^ 2 / 2 by positivity)
  have h₈ := mul_le_mul_of_nonneg_right hDsq (sq_nonneg r)
  have h₉ := mul_le_mul_of_nonneg_right (show 1 ≤ D ^ 2 by nlinarith only [hD]) (sq_nonneg r)
  have hfinal : lam ^ 2 * e ^ 2 ≤ 16 * D ^ 2 * (r ^ 2 + lam ^ 2 * p ^ 2) := by
    nlinarith only [hmul, h₅, h₆, h₇, h₈, h₉, mul_nonneg (sq_nonneg lam) (mul_nonneg (sq_nonneg D) (sq_nonneg p))]
  have heq : 16 * D ^ 2 * (r ^ 2 / lam ^ 2 + p ^ 2) * lam ^ 2 =
      16 * D ^ 2 * (r ^ 2 + lam ^ 2 * p ^ 2) := by
    field_simp
    <;> ring
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hlam)).mp
  change e ^ 2 * lam ^ 2 ≤ 16 * D ^ 2 * (r ^ 2 / lam ^ 2 + p ^ 2) * lam ^ 2
  rw [heq]
  nlinarith only [hfinal]

/-- Suppose [the current error e, previous error p, projected error u, and
radius r are nonnegative](hyp:he,hp,hu,hr), [the penalty is positive](hyp:hlam)
and [the penalty is at most two](hyp:hlam2), and [K and C are
nonnegative](hyp:hK,hC). If [the penalty times e squared plus u squared is
at most K times the sum of v squared, r u, and r squared, plus the penalty
times C times the sum of r times the sum of e and p, r squared, and e p](hyp:hb), [u
squared is at most sixteen times the square of K plus C plus one, multiplied
by the sum of v squared, r squared, and the penalty times p squared](goal). -/
-- @node: iter_trae_weak_absorb
lemma iter_trae_weak_absorb (e p u v r lam K C : ℝ)
    (he : 0 ≤ e) (hp : 0 ≤ p) (hu : 0 ≤ u) (hr : 0 ≤ r)
    (hlam : 0 < lam) (hlam2 : lam ≤ 2) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hb : lam * e ^ 2 + u ^ 2 ≤ K * (v ^ 2 + r * u + r ^ 2) +
      lam * C * (r * (e + p) + r ^ 2 + e * p)) :
    u ^ 2 ≤ (16 * (K + C + 1) ^ 2) * (v ^ 2 + r ^ 2 + lam * p ^ 2) := by
  have h₁ := iter_trae_young u (K * r) (1 / 2) (by norm_num)
  have h₂ := mul_le_mul_of_nonneg_left
    (iter_trae_young e (C * r) (1 / 4) (by norm_num)) hlam.le
  have h₃ := mul_le_mul_of_nonneg_left
    (iter_trae_young e (C * p) (1 / 4) (by norm_num)) hlam.le
  have h₄ := mul_le_mul_of_nonneg_left
    (iter_trae_young r (C * p) (1 / 2) (by norm_num)) hlam.le
  norm_num at h₁ h₂ h₃ h₄
  have hm : u ^ 2 / 2 ≤ K * v ^ 2 +
      (K ^ 2 / 2 + lam * C ^ 2 + lam / 2 + lam * C + K) * r ^ 2 +
        (3 / 2 : ℝ) * lam * C ^ 2 * p ^ 2 := by
    nlinarith only [hb, h₁, h₂, h₃, h₄, mul_nonneg hlam.le (sq_nonneg e)]
  let A := 16 * (K + C + 1) ^ 2
  have hA : 2 * K ≤ A := by dsimp [A]; nlinarith only [sq_nonneg K, sq_nonneg C, mul_nonneg hK hC, hK, hC]
  have hA' : 3 * C ^ 2 ≤ A := by dsimp [A]; nlinarith only [sq_nonneg K, sq_nonneg C, mul_nonneg hK hC, hK, hC]
  have hA'' : 2 * (K ^ 2 / 2 + lam * C ^ 2 + lam / 2 + lam * C + K) ≤ A := by
    have h₅ := mul_le_mul_of_nonneg_right hlam2 (sq_nonneg C)
    have h₆ := mul_le_mul_of_nonneg_right hlam2 hC
    dsimp [A]
    nlinarith only [h₅, h₆, hlam2, hK, hC, sq_nonneg K, sq_nonneg C, mul_nonneg hK hC]
  have h₅ := mul_le_mul_of_nonneg_right hA (sq_nonneg v)
  have h₆ := mul_le_mul_of_nonneg_right hA' (show 0 ≤ lam * p ^ 2 by positivity)
  have h₇ := mul_le_mul_of_nonneg_right hA'' (sq_nonneg r)
  change u ^ 2 ≤ A * (v ^ 2 + r ^ 2 + lam * p ^ 2)
  nlinarith only [hm, h₅, h₆, h₇]

end Papers.TsAdaptiveEstimationInference

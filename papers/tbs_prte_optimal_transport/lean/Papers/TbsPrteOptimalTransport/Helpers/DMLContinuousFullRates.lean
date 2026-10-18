module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousFullContrast
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousWeightedFullResidual
public import Papers.TbsPrteOptimalTransport.Helpers.DMLPooledPolicyConvergence
/-! Quarter-power rates of the continuous full-interval contrast.
Clipping bounds each product error by its two component errors. The adjacent
contrast consequently retains the original nuisance rate needed in the bias expansion. -/
public section
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: fitted_continuous_full_coordinate_memLp
/-- If [the continuous nuisance record is admissible](hyp:he), then [its treatment
propensity and its upper and lower full-interval outcome means at any index are
square-integrable under the covariate distribution](goal). -/
lemma fitted_continuous_full_coordinate_memLp (L : LevelData Z X)
    (e : NuisanceCont L) (he : ContAdmissible M L e) (k : ℕ) :
    MemLp (positiveValue e.pLev k) 2 (xLaw M) ∧
    MemLp (fun x => fullValue e.JfullPlus k x) 2 (xLaw M) ∧
    MemLp (minusFullValue e k) 2 (xLaw M) := by
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  obtain ⟨hp, hjp, hjm⟩ := fitted_continuous_full_coordinates M L e he k
  refine ⟨MemLp.of_bound hp.1.aestronglyMeasurable 1 ?_,
    MemLp.of_bound hjp.1.aestronglyMeasurable (max |M.yMin| |M.yMax|) ?_,
    MemLp.of_bound hjm.1.aestronglyMeasurable (max |M.yMin| |M.yMax|) ?_⟩
  · simpa only [Real.norm_eq_abs] using hp.2
  · simpa only [Real.norm_eq_abs] using hjp.2
  · simpa only [Real.norm_eq_abs] using hjm.2

-- The product decomposition uses the fitted propensity and the true outcome
-- mean, so their clipped ranges give constants one and B respectively.
-- @node: dml_l2Error_bounded_product_le
/-- Suppose [the true propensity](hyp:hp), [the fitted propensity](hyp:hph),
[the true outcome regression](hyp:hj), and [the fitted outcome regression](hyp:hjh)
are square-integrable. If [the bound is nonnegative](hyp:hB), [the fitted propensity
has absolute value at most one almost surely](hyp:hpb), and [the true regression
has absolute value at most that bound almost surely](hyp:hjb), then [the L2 error
of their fitted product is at most the bound times the propensity L2 error plus
the regression L2 error](goal). -/
lemma dml_l2Error_bounded_product_le (p ph j jh : X → ℝ)
    (hp : MemLp p 2 (xLaw M)) (hph : MemLp ph 2 (xLaw M))
    (hj : MemLp j 2 (xLaw M)) (hjh : MemLp jh 2 (xLaw M))
    (B : ℝ) (hB : 0 ≤ B)
    (hpb : ∀ᵐ x ∂xLaw M, |ph x| ≤ 1)
    (hjb : ∀ᵐ x ∂xLaw M, |j x| ≤ B) :
    finiteL2Error M (fun x => ph x * jh x) (fun x => p x * j x) ≤
      B * finiteL2Error M ph p + finiteL2Error M jh j := by
  let dp := fun x => ph x - p x
  let dj := fun x => jh x - j x
  let E := fun x => B * ‖dp x‖ + ‖dj x‖
  have hdp : MemLp dp 2 (xLaw M) := hph.sub hp
  have hdj : MemLp dj 2 (xLaw M) := hjh.sub hj
  have hE : MemLp E 2 (xLaw M) := (hdp.norm.const_mul B).add hdj.norm
  have hbound : ∀ᵐ x ∂xLaw M, ‖ph x * jh x - p x * j x‖ ≤ E x := by
    filter_upwards [hpb, hjb] with x hx hy
    have hid : ph x * jh x - p x * j x =
        (ph x - p x) * j x + ph x * (jh x - j x) := by ring
    rw [hid, Real.norm_eq_abs]
    apply (abs_add_le _ _).trans
    dsimp only [E, dp, dj]
    rw [abs_mul, abs_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact add_le_add (by simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left hy (abs_nonneg (ph x - p x)))
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hx (abs_nonneg (jh x - j x)))
  have hdiff : MemLp (fun x => ph x * jh x - p x * j x) 2 (xLaw M) :=
    hE.mono' (by
      first | fun_prop | exact (hph.1.mul hjh.1).sub (hp.1.mul hj.1)) hbound
  have hmono : eLpNorm (fun x => ph x * jh x - p x * j x) 2 (xLaw M) ≤
      eLpNorm E 2 (xLaw M) := by
    apply eLpNorm_mono_ae_real
    simpa only [Real.norm_eq_abs] using hbound
  have hb := eLpNorm_add_le (hdp.norm.const_mul B).1 hdj.norm.1
    (by norm_num : (1 : ENNReal) ≤ 2)
  have hfin := ENNReal.add_ne_top.mpr
    ⟨(hdp.norm.const_mul B).eLpNorm_ne_top, hdj.norm.eLpNorm_ne_top⟩
  rw [l2Error_eq_eLpNorm M _ _ hdiff, l2Error_eq_eLpNorm M _ _ hdp,
    l2Error_eq_eLpNorm M _ _ hdj]
  apply (ENNReal.toReal_mono hfin (hmono.trans hb)).trans_eq
  rw [ENNReal.toReal_add (hdp.norm.const_mul B).eLpNorm_ne_top hdj.norm.eLpNorm_ne_top]
  have hsmul : eLpNorm (fun x => B * ‖dp x‖) 2 (xLaw M) =
      ‖B‖ₑ * eLpNorm (fun x => ‖dp x‖) 2 (xLaw M) :=
    eLpNorm_const_smul B (fun x => ‖dp x‖) 2 (xLaw M)
  rw [hsmul, eLpNorm_norm, eLpNorm_norm, ENNReal.toReal_mul, toReal_enorm,
    Real.norm_of_nonneg hB]

-- @node: fitted_contFullJ_l2Error_bound
/-- If [the reference nuisance record is admissible](hyp:he0) and [the fitted
record is admissible](hyp:he), then [the L2 error in the adjacent full-interval
contrast is bounded by the sum, over its two endpoints, of the propensity L2
error times the largest absolute outcome endpoint and the outcome-mean L2 error](goal). -/
lemma fitted_contFullJ_l2Error_bound (L : LevelData Z X)
    (e0 e : NuisanceCont L) (he0 : ContAdmissible M L e0)
    (he : ContAdmissible M L e) (k : ℕ) :
    finiteL2Error M (contFullJ L e k) (contFullJ L e0 k) ≤
      max |M.yMin| |M.yMax| * finiteL2Error M (positiveValue e.pLev (k+1))
        (positiveValue e0.pLev (k+1)) +
      finiteL2Error M (fun x => fullValue e.JfullPlus k x) (fun x => fullValue e0.JfullPlus k x) +
      (max |M.yMin| |M.yMax| * finiteL2Error M (positiveValue e.pLev k)
        (positiveValue e0.pLev k) + finiteL2Error M (minusFullValue e k) (minusFullValue e0 k)) := by
  let P := fun (e' : NuisanceCont L) (b : Bool) =>
    positiveValue e'.pLev (if b then k+1 else k)
  let J := fun (e' : NuisanceCont L) (b : Bool) x =>
    if b then fullValue e'.JfullPlus k x else minusFullValue e' k x
  have hprod (b : Bool) : finiteL2Error M (fun x => P e b x * J e b x)
      (fun x => P e0 b x * J e0 b x) ≤
      max |M.yMin| |M.yMax| * finiteL2Error M (P e b) (P e0 b) +
        finiteL2Error M (J e b) (J e0 b) := by
    have hp0 := (fitted_continuous_full_coordinate_memLp M L e0 he0 (if b then k+1 else k)).1
    have hp := (fitted_continuous_full_coordinate_memLp M L e he (if b then k+1 else k)).1
    have hj0 : MemLp (J e0 b) 2 (xLaw M) := by
      cases b
      · exact (fitted_continuous_full_coordinate_memLp M L e0 he0 k).2.2
      · exact (fitted_continuous_full_coordinate_memLp M L e0 he0 k).2.1
    have hj : MemLp (J e b) 2 (xLaw M) := by
      cases b
      · exact (fitted_continuous_full_coordinate_memLp M L e he k).2.2
      · exact (fitted_continuous_full_coordinate_memLp M L e he k).2.1
    apply dml_l2Error_bounded_product_le M _ _ _ _ hp0 hp hj0 hj _
      ((abs_nonneg _).trans (le_max_left _ _))
      (fitted_continuous_full_coordinates M L e he (if b then k+1 else k)).1.2
    cases b
    · exact (fitted_continuous_full_coordinates M L e0 he0 k).2.2.2
    · exact (fitted_continuous_full_coordinates M L e0 he0 k).2.1.2
  have hs := dml_l2Error_sub_le M _ _ _ _
    (fitted_continuous_full_product_memLp M L e0 he0 true k)
    (fitted_continuous_full_product_memLp M L e he true k)
    (fitted_continuous_full_product_memLp M L e0 he0 false k)
    (fitted_continuous_full_product_memLp M L e he false k)
  exact hs.trans (add_le_add (hprod true) (hprod false))

-- @node: nuisanceRates_contFullJ_quarter_rate
/-- If [the reference nuisance is admissible](hyp:he0), [every fitted nuisance is
admissible](hyp:heh), and [the treatment propensities](hyp:hrp), [upper full-interval
means](hyp:hrplus), and [lower full-interval means](hyp:hrminus) have L2 errors
of smaller order in probability than the inverse fourth root of sample size,
then [the adjacent full-interval contrasts have the same rate](goal). -/
lemma nuisanceRates_contFullJ_quarter_rate {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (L : LevelData Z X) (e0 : NuisanceCont L)
    (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L e0) (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrplus : FiniteNuisanceRates M μ (fun n a => (eh n a).JfullPlus) e0.JfullPlus)
    (hrminus : FiniteNuisanceRates M μ (fun n a => (eh n a).JfullMinus) e0.JfullMinus) :
    FiniteNuisanceRates M μ (fun n a k => contFullJ L (eh n a) k) (contFullJ L e0) := by
  obtain ⟨hp, hjp, hjm⟩ := nuisanceRates_continuous_full_values M μ L e0 eh hrp hrplus hrminus
  intro k
  have hn : ∀ᶠ n : ℕ in atTop, 0 ≤ ((2*(n+1) : ℕ) : ℝ)^(-1/4 : ℝ) := Eventually.of_forall (fun n : ℕ =>
    Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ ((2*(n+1) : ℕ) : ℝ)) (-1/4 : ℝ))
  have hs := ((hp (k+1)).add_eventually_nonneg_rate hn (hjp k)).add_eventually_nonneg_rate hn
    ((hp k).add_eventually_nonneg_rate hn (hjm k))
  let B := max |M.yMin| |M.yMax|
  have hB : 0 ≤ B := (abs_nonneg _).trans (le_max_left _ _)
  apply Causalean.Stat.IsLittleOp.of_abs_le_const_mul (by positivity : 0 < B + 1) hs
  intro n a
  dsimp only [finiteL2Error]
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  have hb := fitted_contFullJ_l2Error_bound M L e0 (eh (2*(n+1)) a) he0 (heh _ a) k
  apply hb.trans
  dsimp only [finiteL2Error]
  conv_rhs => arg 2; rw [abs_of_nonneg (by positivity)]
  dsimp only [B]
  nlinarith [mul_nonneg hB (Real.sqrt_nonneg
      (∫ x, (fullValue (eh (2*(n+1)) a).JfullPlus k x - fullValue e0.JfullPlus k x)^2 ∂xLaw M)),
    mul_nonneg hB (Real.sqrt_nonneg
      (∫ x, (minusFullValue (eh (2*(n+1)) a) k x - minusFullValue e0 k x)^2 ∂xLaw M)),
    Real.sqrt_nonneg (∫ x, (positiveValue (eh (2*(n+1)) a).pLev (k+1) x -
      positiveValue e0.pLev (k+1) x)^2 ∂xLaw M),
    Real.sqrt_nonneg (∫ x, (positiveValue (eh (2*(n+1)) a).pLev k x -
      positiveValue e0.pLev k x)^2 ∂xLaw M)]

-- This is the product-score remainder (gammaHat - gamma) * (JHat - J)
-- in the roadmap, rather than the first-order plug-in target error.
-- @node: fitted_continuous_full_product_cross_error_bound
/-- If [the reference nuisance is admissible](hyp:he0) and [the fitted nuisance is
admissible](hyp:he), then [the product of the signed-weight error and the
full-interval contrast error is integrable, and its absolute expectation is at
most the product of their L2 errors](goal). -/
lemma fitted_continuous_full_product_cross_error_bound (L : LevelData Z X)
    (e0 e : NuisanceCont L) (he0 : ContAdmissible M L e0)
    (he : ContAdmissible M L e) (k : Fin L.K) :
    Integrable (fun x => (e.gammaFull k x - e0.gammaFull k x) *
      (contFullJ L e k x - contFullJ L e0 k x)) (xLaw M) ∧
    |∫ x, (e.gammaFull k x - e0.gammaFull k x) *
      (contFullJ L e k x - contFullJ L e0 k x) ∂xLaw M| ≤
      finiteL2Error M (e.gammaFull k) (e0.gammaFull k) *
        finiteL2Error M (contFullJ L e k) (contFullJ L e0 k) := by
  have hg := (fitted_continuous_gammaFull_memLp M L e he k).sub
    (fitted_continuous_gammaFull_memLp M L e0 he0 k)
  have hj := (fitted_contFullJ_memLp M L e he k).sub
    (fitted_contFullJ_memLp M L e0 he0 k)
  refine ⟨hg.integrable_mul hj, ?_⟩
  rw [l2Error_eq_eLpNorm M _ _ hg, l2Error_eq_eLpNorm M _ _ hj]
  calc
    _ ≤ ∫ x, |(e.gammaFull k x - e0.gammaFull k x) *
        (contFullJ L e k x - contFullJ L e0 k x)| ∂xLaw M := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun x => (e.gammaFull k x - e0.gammaFull k x) *
          (contFullJ L e k x - contFullJ L e0 k x))
    _ ≤ _ := Causalean.Stat.integral_abs_mul_le_eLpNorm_mul_eLpNorm hg hj

-- @node: nuisanceRates_continuous_full_product_cross_error_root_n_negligible
/-- Suppose [the reference nuisance is admissible](hyp:he0), [all fitted nuisances
are admissible](hyp:heh), and [treatment propensities](hyp:hrp), [upper outcome
means](hyp:hrplus), [lower outcome means](hyp:hrminus), and [signed full-interval
weights](hyp:hrg) have L2 errors of smaller order in probability than the inverse
fourth root of sample size. Then [the expectation of the product of the
signed-weight and contrast errors, multiplied by the square root of the half-sample
size, converges in probability to zero](goal). -/
lemma nuisanceRates_continuous_full_product_cross_error_root_n_negligible
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (L : LevelData Z X) (e0 : NuisanceCont L) (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L e0) (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrplus : FiniteNuisanceRates M μ (fun n a => (eh n a).JfullPlus) e0.JfullPlus)
    (hrminus : FiniteNuisanceRates M μ (fun n a => (eh n a).JfullMinus) e0.JfullMinus)
    (hrg : FiniteNuisanceRates M μ (fun n a => (eh n a).gammaFull) e0.gammaFull)
    (k : Fin L.K) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
        (∫ x, ((eh (2*(n+1)) a).gammaFull k x - e0.gammaFull k x) *
          (contFullJ L (eh (2*(n+1)) a) k x - contFullJ L e0 k x) ∂xLaw M))
      atTop (fun _ _ => 0) := by
  have hrJ := nuisanceRates_contFullJ_quarter_rate M μ L e0 eh he0 heh hrp hrplus hrminus
  have hr := dml_quarter_rate_product μ _ _ (hrg k) (hrJ k)
  apply dml_root_n_bias_tendsto_probability μ
  apply Causalean.Stat.IsLittleOp.of_abs_le_const_mul one_pos hr
  intro n a
  rw [one_mul]
  exact (fitted_continuous_full_product_cross_error_bound M L e0
    (eh (2*(n+1)) a) he0 (heh _ a) k).2.trans (le_abs_self _)

end Papers.TbsPrteOptimalTransport

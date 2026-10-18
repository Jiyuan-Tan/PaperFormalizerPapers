module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousFullRates
/-! Absolute product remainders for the finite continuous full-interval block.
The componentwise quarter-power nuisance rates control the sum of absolute
cross-errors, before any cancellation in the score expectation. -/
public section
set_option linter.style.openClassical false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: fitted_continuous_full_product_absolute_cross_error_bound
/-- If [the reference nuisances are admissible](hyp:he0) and [the fitted nuisances
are admissible](hyp:he), [the absolute product of the instrument-weight error
and full-interval outcome-contrast error is integrable, and its covariate mean
is bounded by the product of their root mean squared errors](goal). -/
lemma fitted_continuous_full_product_absolute_cross_error_bound (L : LevelData Z X)
    (e0 e : NuisanceCont L) (he0 : ContAdmissible M L e0)
    (he : ContAdmissible M L e) (k : Fin L.K) :
    Integrable (fun x => |(e.gammaFull k x - e0.gammaFull k x) *
      (contFullJ L e k x - contFullJ L e0 k x)|) (xLaw M) ∧
    (∫ x, |(e.gammaFull k x - e0.gammaFull k x) *
      (contFullJ L e k x - contFullJ L e0 k x)| ∂xLaw M) ≤
      finiteL2Error M (e.gammaFull k) (e0.gammaFull k) *
        finiteL2Error M (contFullJ L e k) (contFullJ L e0 k) := by
  have hg := (fitted_continuous_gammaFull_memLp M L e he k).sub
    (fitted_continuous_gammaFull_memLp M L e0 he0 k)
  have hj := (fitted_contFullJ_memLp M L e he k).sub
    (fitted_contFullJ_memLp M L e0 he0 k)
  refine ⟨(hg.integrable_mul hj).abs, ?_⟩
  rw [l2Error_eq_eLpNorm M _ _ hg, l2Error_eq_eLpNorm M _ _ hj]
  exact Causalean.Stat.integral_abs_mul_le_eLpNorm_mul_eLpNorm hg hj

-- @node: fitted_continuous_full_product_block_absolute_cross_error_bound
/-- For [admissible reference nuisances](hyp:he0) and [admissible fitted
nuisances](hyp:he), [the sum across levels of absolute products of instrument-weight
errors and full-interval outcome-contrast errors is integrable, and its covariate
mean is bounded by the sum of the products of the corresponding root mean
squared errors](goal). -/
lemma fitted_continuous_full_product_block_absolute_cross_error_bound (L : LevelData Z X)
    (e0 e : NuisanceCont L) (he0 : ContAdmissible M L e0)
    (he : ContAdmissible M L e) :
    Integrable (fun x => ∑ k : Fin L.K, |(e.gammaFull k x - e0.gammaFull k x) *
      (contFullJ L e k x - contFullJ L e0 k x)|) (xLaw M) ∧
    (∫ x, ∑ k : Fin L.K, |(e.gammaFull k x - e0.gammaFull k x) *
      (contFullJ L e k x - contFullJ L e0 k x)| ∂xLaw M) ≤
      ∑ k : Fin L.K, finiteL2Error M (e.gammaFull k) (e0.gammaFull k) *
        finiteL2Error M (contFullJ L e k) (contFullJ L e0 k) := by
  have hi k := (fitted_continuous_full_product_absolute_cross_error_bound M L e0 e he0 he k).1
  refine ⟨integrable_finsetSum _ (fun k _ => hi k), ?_⟩
  rw [integral_finsetSum _ (fun k _ => hi k)]
  exact Finset.sum_le_sum (fun k _ =>
    (fitted_continuous_full_product_absolute_cross_error_bound M L e0 e he0 he k).2)

-- @node: fitted_continuous_full_product_block_quadratic_cross_error_bound
/-- With [admissible reference nuisances](hyp:he0) and [admissible fitted
nuisances](hyp:he), if [every full-interval outcome-contrast root mean squared
error is at most the regression bound](hyp:hj) and [every instrument-weight root
mean squared error is at most the weight bound](hyp:hg), then [the covariate mean
of the sum of absolute cross-error products is at most the number of levels
times the regression bound times the weight bound](goal). -/
lemma fitted_continuous_full_product_block_quadratic_cross_error_bound (L : LevelData Z X)
    (e0 e : NuisanceCont L) (he0 : ContAdmissible M L e0)
    (he : ContAdmissible M L e) (reg wt : ℝ)
    (hj : ∀ k : Fin L.K, finiteL2Error M (contFullJ L e k) (contFullJ L e0 k) ≤ reg)
    (hg : ∀ k : Fin L.K, finiteL2Error M (e.gammaFull k) (e0.gammaFull k) ≤ wt) :
    (∫ x, ∑ k : Fin L.K, |(e.gammaFull k x - e0.gammaFull k x) *
      (contFullJ L e k x - contFullJ L e0 k x)| ∂xLaw M) ≤
      (L.K : ℝ) * (reg * wt) := by
  apply (fitted_continuous_full_product_block_absolute_cross_error_bound M L e0 e he0 he).2.trans
  calc
    _ ≤ ∑ _k : Fin L.K, wt * reg := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul (hg k) (hj k) (Real.sqrt_nonneg _) (by
        exact (Real.sqrt_nonneg _).trans (hg k))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

-- @node: nuisanceRates_continuous_full_product_block_absolute_cross_error_root_n_negligible
/-- If [the reference nuisances are admissible](hyp:he0), [all fitted nuisances
are admissible](hyp:heh), and the componentwise nuisance rates hold for [treatment
probabilities](hyp:hrp), [upper full-interval means](hyp:hrplus), [lower full-interval
means](hyp:hrminus), and [instrument weights](hyp:hrg), then [the covariate mean
of the sum across levels of absolute instrument-weight-error times outcome-contrast-error
products, evaluated using fits at twice the half-sample size and multiplied by
the square root of the half-sample size, converges in probability to zero](goal). -/
lemma nuisanceRates_continuous_full_product_block_absolute_cross_error_root_n_negligible
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (L : LevelData Z X) (e0 : NuisanceCont L) (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L e0) (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrplus : FiniteNuisanceRates M μ (fun n a => (eh n a).JfullPlus) e0.JfullPlus)
    (hrminus : FiniteNuisanceRates M μ (fun n a => (eh n a).JfullMinus) e0.JfullMinus)
    (hrg : FiniteNuisanceRates M μ (fun n a => (eh n a).gammaFull) e0.gammaFull) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
        (∫ x, ∑ k : Fin L.K,
          |((eh (2*(n+1)) a).gammaFull k x - e0.gammaFull k x) *
            (contFullJ L (eh (2*(n+1)) a) k x - contFullJ L e0 k x)| ∂xLaw M))
      atTop (fun _ _ => 0) := by
  let ks := (Finset.univ : Finset (Fin L.K)).toList
  let reg := fun n a => maxErrors (ks.map (fun k : Fin L.K =>
    finiteL2Error M (contFullJ L (eh (2*(n+1)) a) k) (contFullJ L e0 k)))
  let wt := fun n a => maxErrors (ks.map (fun k : Fin L.K =>
    finiteL2Error M ((eh (2*(n+1)) a).gammaFull k) (e0.gammaFull k)))
  have hrJ := nuisanceRates_contFullJ_quarter_rate M μ L e0 eh he0 heh hrp hrplus hrminus
  have hr := nuisanceRates_finite_maxErrors M μ
    (fun n a (k : Fin L.K) => contFullJ L (eh n a) k)
    (fun k : Fin L.K => contFullJ L e0 k) ks (fun k : Fin L.K => hrJ k)
  have hw := nuisanceRates_finite_maxErrors M μ
    (fun n a => (eh n a).gammaFull) e0.gammaFull ks hrg
  have hp := dml_quarter_rate_product μ reg wt hr hw
  apply dml_root_n_bias_tendsto_probability μ
  apply Causalean.Stat.IsLittleOp.of_abs_le_const_mul (by positivity : 0 < (L.K : ℝ) + 1) hp
  intro n a
  rw [abs_of_nonneg (integral_nonneg (fun _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))),
    abs_of_nonneg (mul_nonneg (maxErrors_nonneg _) (maxErrors_nonneg _))]
  have hb := fitted_continuous_full_product_block_quadratic_cross_error_bound M L e0
    (eh (2*(n+1)) a) he0 (heh _ a) (reg n a) (wt n a)
    (fun k => le_maxErrors_of_mem (List.mem_map.mpr ⟨k, by simp [ks], rfl⟩))
    (fun k => le_maxErrors_of_mem (List.mem_map.mpr ⟨k, by simp [ks], rfl⟩))
  exact hb.trans (mul_le_mul_of_nonneg_right (by linarith)
    (mul_nonneg (maxErrors_nonneg _) (maxErrors_nonneg _)))

end Papers.TbsPrteOptimalTransport

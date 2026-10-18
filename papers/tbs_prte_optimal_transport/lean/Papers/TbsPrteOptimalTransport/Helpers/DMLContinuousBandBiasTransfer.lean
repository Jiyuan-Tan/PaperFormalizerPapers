module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousBandBiasDecomposition
public import StatLean.AsymptoticStatistics.ForMathlib.TendstoInMeasureAlgebra
/-! Removing the second-order gamma/target term from continuous band bias.
The exact product-score decomposition and the component nuisance rates show
that the product bias and weighted component correction agree at root-n scale.
This leaves the component correction itself to be bounded by the policy and
quantile remainder argument. -/
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

-- @node: continuous_band_product_signed_cross_block_bound
/-- If [the reference continuous nuisances are admissible](hyp:he0) and [the fitted continuous nuisances are admissible](hyp:he),
then [the absolute sum over any finite block of the mean products of fitted-minus-reference band-weight and band-target errors is bounded by the mean sum of their absolute products](goal). -/
lemma continuous_band_product_signed_cross_block_bound
    (L : LevelData Z X) (e0 e : NuisanceCont L)
    (he0 : ContAdmissible M L e0) (he : ContAdmissible M L e)
    (t : Finset (ℕ × ℕ)) :
    |∑ i ∈ t, ∫ x, (regularValue e.gamma i.1 i.2 x -
        regularValue e0.gamma i.1 i.2 x) *
      (contJ L e i.1 (i.2-1) x - contJ L e0 i.1 (i.2-1) x) ∂xLaw M| ≤
    ∫ x, ∑ i ∈ t, |(regularValue e.gamma i.1 i.2 x -
        regularValue e0.gamma i.1 i.2 x) *
      (contJ L e i.1 (i.2-1) x - contJ L e0 i.1 (i.2-1) x)| ∂xLaw M := by
  have hi (i : ℕ × ℕ) := (fitted_continuous_band_product_absolute_cross_error_bound
    M L e0 e he0 he i.1 i.2).1
  rw [integral_finsetSum t (fun i _ => hi i)]
  apply (Finset.abs_sum_le_sum_abs _ t).trans
  apply Finset.sum_le_sum
  intro i _
  simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
    (fun x => (regularValue e.gamma i.1 i.2 x - regularValue e0.gamma i.1 i.2 x) *
      (contJ L e i.1 (i.2-1) x - contJ L e0 i.1 (i.2-1) x))

-- @node: encoded_continuous_band_product_signed_cross_block_root_n_negligible
/-- Suppose [the reference continuous nuisances are admissible](hyp:he0),
[all random fitted nuisances are admissible](hyp:heh), and
[each encoded fitted nuisance component's L2 error relative to the reference is negligible in probability compared with the inverse fourth root of the sample size](hyp:hr).
Then [at sample sizes twice the quantity n + 1, the sum over any finite block of the mean products of band-weight and band-target errors, multiplied by the square root of n + 1, converges to zero in probability](goal). -/
lemma encoded_continuous_band_product_signed_cross_block_root_n_negligible
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (L : LevelData Z X) (e0 : NuisanceCont L) (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L e0) (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hr : FiniteNuisanceRates M μ (fun n a => contComponent M L (eh n a))
      (contComponent M L e0)) (t : Finset (ℕ × ℕ)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
        ∑ i ∈ t, ∫ x, (regularValue (eh (2*(n+1)) a).gamma i.1 i.2 x -
            regularValue e0.gamma i.1 i.2 x) *
          (contJ L (eh (2*(n+1)) a) i.1 (i.2-1) x -
            contJ L e0 i.1 (i.2-1) x) ∂xLaw M)
      atTop (fun _ _ => 0) := by
  have h := encoded_continuous_band_product_block_cross_root_n_negligible
    M μ L e0 eh he0 heh hr t
  rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm] at h ⊢
  intro eps heps
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (h eps heps) (fun _ => zero_le)
  intro n
  apply measure_mono
  intro a ha
  simp only [Set.mem_ofPred_eq, sub_zero, Real.norm_eq_abs] at ha ⊢
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)] at ha ⊢
  exact ha.trans (mul_le_mul_of_nonneg_left
    ((continuous_band_product_signed_cross_block_bound M L e0
      (eh (2*(n+1)) a) he0 (heh _ a) t).trans (le_abs_self _))
    (Real.sqrt_nonneg _))

-- @node: encoded_continuous_band_product_bias_component_difference_root_n_negligible
/-- Suppose [the true continuous nuisances are admissible](hyp:he0), [all random fitted nuisances are admissible](hyp:heh),
[each encoded component's L2 error relative to truth is negligible in probability compared with the inverse fourth root of the sample size](hyp:hr),
[every level-band pair in the finite block has a valid level and positive band index](hyp:hidx), and
[each fitted weight times its preceding component score is integrable at every sample size and realization](hyp:hi).
Then [at sample sizes twice the quantity n + 1, the difference between the block's product-score bias and its summed mean fitted-weighted component corrections, multiplied by the square root of n + 1, converges to zero in probability](goal). -/
lemma encoded_continuous_band_product_bias_component_difference_root_n_negligible
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hr : FiniteNuisanceRates M μ (fun n a => contComponent M L (eh n a))
      (contComponent M L (trueNuisance M L)))
    (t : Finset (ℕ × ℕ))
    (hidx : ∀ i ∈ t, i.1 ≤ L.K ∧ 1 ≤ i.2 ∧ i.2 ≤ L.l i.1)
    (hi : ∀ n a i, i ∈ t → Integrable (fun o : Obs X Z =>
      regularValue (eh n a).gamma i.1 i.2 o.1 *
        contScoreComponents M phi dphi L (eh n a) i.1 (i.2-1) o) (observationLaw M)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
        (((∫ o : Obs X Z, ∑ i ∈ t,
            psiProd M phi dphi L (eh (2*(n+1)) a) i.1 i.2 o ∂observationLaw M) -
          (∫ x, ∑ i ∈ t, gamma M L i.1 i.2 x *
            contJ L (trueNuisance M L) i.1 (i.2-1) x ∂xLaw M)) -
        (∑ i ∈ t, ∫ o : Obs X Z, regularValue (eh (2*(n+1)) a).gamma i.1 i.2 o.1 *
          (contScoreComponents M phi dphi L (eh (2*(n+1)) a) i.1 (i.2-1) o -
            contJ L (trueNuisance M L) i.1 (i.2-1) o.1) ∂observationLaw M)))
      atTop (fun _ _ => 0) := by
  have h := encoded_continuous_band_product_signed_cross_block_root_n_negligible
    M μ L (trueNuisance M L) eh he0 heh hr t
  have hn := (show TendstoInMeasure μ _ atTop (fun _ => (0 : ℝ)) from h).neg_zero
  change TendstoInMeasure μ _ atTop (fun _ => (0 : ℝ))
  convert hn using 1
  funext n a
  rw [continuous_band_product_block_exact_bias_decomposition M phi dphi L
    (eh (2*(n+1)) a) (heh _ a) he0 t hidx (hi _ a)]
  simp only [Pi.neg_apply]
  ring

end Papers.TbsPrteOptimalTransport

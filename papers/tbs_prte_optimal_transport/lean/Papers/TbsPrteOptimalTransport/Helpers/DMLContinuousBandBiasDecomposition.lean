module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousBandProductMean
/-! Exact bias decomposition of the fitted continuous band product score.
The instrument tower identity isolates the weighted component correction and
the second-order product of the gamma and band-target errors. No population
centering or remainder bound is assumed in these identities. -/
public section
set_option linter.style.haveILetI false
set_option linter.style.openClassical false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: fitted_continuous_regular_gamma_measurable
/-- If [the fitted continuous nuisance functions are admissible](hyp:he), then
[the fitted regular-band weight at any level and band index is measurable, with zero used outside the valid index range](goal). -/
@[fun_prop] lemma fitted_continuous_regular_gamma_measurable
    (L : LevelData Z X) (e : NuisanceCont L) (he : ContAdmissible M L e)
    (k j : ℕ) : Measurable (regularValue e.gamma k j) := by
  first | fun_prop | skip
  rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hm, _⟩
  unfold regularValue
  split_ifs
  · exact hm _
  · fun_prop

-- @node: fitted_continuous_regular_gamma_memLp
/-- If [the fitted continuous nuisance functions are admissible](hyp:he), then
[the fitted regular-band weight at any level and band index is square integrable under the covariate distribution](goal). -/
lemma fitted_continuous_regular_gamma_memLp
    (L : LevelData Z X) (e : NuisanceCont L) (he : ContAdmissible M L e)
    (k j : ℕ) : MemLp (regularValue e.gamma k j) 2 (xLaw M) := by
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  apply MemLp.of_bound
    (fitted_continuous_regular_gamma_measurable M L e he k j).aestronglyMeasurable 1
  rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hb, _⟩
  unfold regularValue
  split_ifs with h
  · filter_upwards [hb ⟨(k,j),h⟩] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
    exact hx.2
  · exact Eventually.of_forall (fun _ => by norm_num)

-- @node: fitted_continuous_band_product_mean_decomposition
/-- Suppose [the fitted continuous nuisance functions are admissible](hyp:he),
[the level index is at most the maximum level](hyp:hk), [the band index lies between one and the number of bands at that level](hyp:hj), and
[the fitted band weight times the preceding component score is integrable](hyp:hi).
Then [the product score is integrable and its mean equals the mean of that weighted component score plus the covariate mean of the fitted band target times the true-minus-fitted band weight](goal). -/
lemma fitted_continuous_band_product_mean_decomposition
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (e : NuisanceCont L) (he : ContAdmissible M L e)
    (k j : ℕ) (hk : k ≤ L.K) (hj : 1 ≤ j ∧ j ≤ L.l k)
    (hi : Integrable (fun o : Obs X Z => regularValue e.gamma k j o.1 *
      contScoreComponents M phi dphi L e k (j-1) o) (observationLaw M)) :
    Integrable (psiProd M phi dphi L e k j) (observationLaw M) ∧
    (∫ o, psiProd M phi dphi L e k j o ∂observationLaw M) =
      (∫ o : Obs X Z, regularValue e.gamma k j o.1 *
        contScoreComponents M phi dphi L e k (j-1) o ∂observationLaw M) +
      ∫ x, contJ L e k (j-1) x *
        (gamma M L k j x - regularValue e.gamma k j x) ∂xLaw M := by
  obtain ⟨ir, mr⟩ := fitted_continuous_band_share_correction_mean M L e he k j hk hj
  have hid : psiProd M phi dphi L e k j =
      (fun o : Obs X Z => regularValue e.gamma k j o.1 *
        contScoreComponents M phi dphi L e k (j-1) o +
        contJ L e k (j-1) o.1 *
          (indicator (o.2.1 ∈ policyUnion L k j) - regularValue e.gamma k j o.1)) := by
    funext o
    simp only [psiProd]
  rw [hid]
  exact ⟨hi.fun_add ir, by rw [integral_add hi ir, mr]⟩

-- @node: continuous_band_product_exact_bias_decomposition
/-- Suppose [the fitted nuisances are admissible](hyp:he), [the true nuisances are admissible](hyp:he0),
[the level index is at most the maximum level](hyp:hk), [the band index is valid and positive](hyp:hj), and
[the fitted band weight times the preceding component score is integrable](hyp:hi).
Then [the product-score mean minus the true band-weighted target equals the mean fitted weight times the component score minus its true target, less the covariate mean of the product of the fitted-minus-true band-weight and band-target errors](goal). -/
lemma continuous_band_product_exact_bias_decomposition
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (e : NuisanceCont L) (he : ContAdmissible M L e)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (k j : ℕ) (hk : k ≤ L.K) (hj : 1 ≤ j ∧ j ≤ L.l k)
    (hi : Integrable (fun o : Obs X Z => regularValue e.gamma k j o.1 *
      contScoreComponents M phi dphi L e k (j-1) o) (observationLaw M)) :
    (∫ o, psiProd M phi dphi L e k j o ∂observationLaw M) -
      (∫ x, gamma M L k j x * contJ L (trueNuisance M L) k (j-1) x ∂xLaw M) =
    (∫ o : Obs X Z, regularValue e.gamma k j o.1 *
      (contScoreComponents M phi dphi L e k (j-1) o -
        contJ L (trueNuisance M L) k (j-1) o.1) ∂observationLaw M) -
    (∫ x, (regularValue e.gamma k j x -
        regularValue (trueNuisance M L).gamma k j x) *
      (contJ L e k (j-1) x - contJ L (trueNuisance M L) k (j-1) x) ∂xLaw M) := by
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  have hg := fitted_continuous_regular_gamma_memLp M L e he k j
  have hg0 := fitted_continuous_regular_gamma_memLp M L _ he0 k j
  have hJ := fitted_contJ_memLp M L e he k (j-1)
  have hJ0 := fitted_contJ_memLp M L _ he0 k (j-1)
  have htrue (x : X) : regularValue (trueNuisance M L).gamma k j x =
      gamma M L k j x := by
    simp only [regularValue, trueNuisance, dif_pos (show
      k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k from ⟨hk,hj⟩)]
  have hg0' : MemLp (gamma M L k j) 2 (xLaw M) := by
    rw [← show regularValue (trueNuisance M L).gamma k j = gamma M L k j from funext htrue]
    exact hg0
  have igJ0 := hg.integrable_mul hJ0
  change Integrable (fun x => regularValue e.gamma k j x *
    contJ L (trueNuisance M L) k (j-1) x) (xLaw M) at igJ0
  have itJ0 := hg0'.integrable_mul hJ0
  change Integrable (fun x => gamma M L k j x *
    contJ L (trueNuisance M L) k (j-1) x) (xLaw M) at itJ0
  have ir : Integrable (fun x => contJ L e k (j-1) x *
      (gamma M L k j x - regularValue e.gamma k j x)) (xLaw M) :=
    hJ.integrable_mul (hg0'.sub hg)
  have igJ0o := (hg.comp_measurePreserving (observationLaw_fst_measurePreserving M)).integrable_mul
    (hJ0.comp_measurePreserving (observationLaw_fst_measurePreserving M))
  change Integrable (fun o : Obs X Z => regularValue e.gamma k j o.1 *
    contJ L (trueNuisance M L) k (j-1) o.1) (observationLaw M) at igJ0o
  have ineg : Integrable (fun x => -(contJ L e k (j-1) x *
    (gamma M L k j x - regularValue e.gamma k j x))) (xLaw M) := ir.neg
  have mc := observationLaw_covariate_integral M
    (fun x => regularValue e.gamma k j x * contJ L (trueNuisance M L) k (j-1) x)
    (by fun_prop)
  have cross : (∫ x, (regularValue e.gamma k j x -
        regularValue (trueNuisance M L).gamma k j x) *
      (contJ L e k (j-1) x - contJ L (trueNuisance M L) k (j-1) x) ∂xLaw M) =
      -(∫ x, contJ L e k (j-1) x *
        (gamma M L k j x - regularValue e.gamma k j x) ∂xLaw M) -
      (∫ x, regularValue e.gamma k j x *
        contJ L (trueNuisance M L) k (j-1) x ∂xLaw M) +
      ∫ x, gamma M L k j x * contJ L (trueNuisance M L) k (j-1) x ∂xLaw M := by
    rw [← integral_neg, ← integral_sub ineg igJ0,
      ← integral_add (ineg.sub' igJ0) itJ0]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [htrue]
    ring
  rw [(fitted_continuous_band_product_mean_decomposition M phi dphi L e he
    k j hk hj hi).2, cross]
  simp only [mul_sub]
  rw [integral_sub hi igJ0o, mc]
  ring

-- @node: fitted_continuous_band_product_bias_bound
/-- Suppose [the fitted nuisances are admissible](hyp:he), [the true nuisances are admissible](hyp:he0),
[the level index is at most the maximum level](hyp:hk), [the band index is valid and positive](hyp:hj), and
[the fitted band weight times the preceding component score is integrable](hyp:hi).
Then [the absolute product-score bias relative to the true band-weighted target is bounded by the absolute mean fitted-weighted component correction plus the product of the L2 errors of the band weight and band target](goal). -/
lemma fitted_continuous_band_product_bias_bound
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (e : NuisanceCont L) (he : ContAdmissible M L e)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (k j : ℕ) (hk : k ≤ L.K) (hj : 1 ≤ j ∧ j ≤ L.l k)
    (hi : Integrable (fun o : Obs X Z => regularValue e.gamma k j o.1 *
      contScoreComponents M phi dphi L e k (j-1) o) (observationLaw M)) :
    |(∫ o, psiProd M phi dphi L e k j o ∂observationLaw M) -
      (∫ x, gamma M L k j x * contJ L (trueNuisance M L) k (j-1) x ∂xLaw M)| ≤
    |∫ o : Obs X Z, regularValue e.gamma k j o.1 *
      (contScoreComponents M phi dphi L e k (j-1) o -
        contJ L (trueNuisance M L) k (j-1) o.1) ∂observationLaw M| +
    finiteL2Error M (regularValue e.gamma k j) (regularValue (trueNuisance M L).gamma k j) *
      finiteL2Error M (contJ L e k (j-1)) (contJ L (trueNuisance M L) k (j-1)) := by
  rw [continuous_band_product_exact_bias_decomposition M phi dphi L e he he0
    k j hk hj hi]
  apply (abs_sub _ _).trans
  apply add_le_add_right
  apply le_trans _ (fitted_continuous_band_product_absolute_cross_error_bound M L
    (trueNuisance M L) e he0 he k j).2
  simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
    (fun x => (regularValue e.gamma k j x - regularValue (trueNuisance M L).gamma k j x) *
      (contJ L e k (j-1) x - contJ L (trueNuisance M L) k (j-1) x))

-- @node: continuous_band_product_block_exact_bias_decomposition
/-- Suppose [the fitted nuisances are admissible](hyp:he), [the true nuisances are admissible](hyp:he0),
[every level-band pair in the finite block has a valid level and positive band index](hyp:hidx), and
[each fitted band weight times its preceding component score is integrable](hyp:hi).
Then [the mean of the block's product-score sum minus its true band-weighted target equals the sum of the mean fitted-weighted component corrections minus the sum of the mean products of band-weight and band-target errors](goal). -/
lemma continuous_band_product_block_exact_bias_decomposition
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (e : NuisanceCont L) (he : ContAdmissible M L e)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (t : Finset (ℕ × ℕ))
    (hidx : ∀ i ∈ t, i.1 ≤ L.K ∧ 1 ≤ i.2 ∧ i.2 ≤ L.l i.1)
    (hi : ∀ i ∈ t, Integrable (fun o : Obs X Z => regularValue e.gamma i.1 i.2 o.1 *
      contScoreComponents M phi dphi L e i.1 (i.2-1) o) (observationLaw M)) :
    (∫ o : Obs X Z, ∑ i ∈ t, psiProd M phi dphi L e i.1 i.2 o ∂observationLaw M) -
      (∫ x, ∑ i ∈ t, gamma M L i.1 i.2 x *
        contJ L (trueNuisance M L) i.1 (i.2-1) x ∂xLaw M) =
    (∑ i ∈ t, ∫ o : Obs X Z, regularValue e.gamma i.1 i.2 o.1 *
      (contScoreComponents M phi dphi L e i.1 (i.2-1) o -
        contJ L (trueNuisance M L) i.1 (i.2-1) o.1) ∂observationLaw M) -
    ∑ i ∈ t, ∫ x, (regularValue e.gamma i.1 i.2 x -
        regularValue (trueNuisance M L).gamma i.1 i.2 x) *
      (contJ L e i.1 (i.2-1) x - contJ L (trueNuisance M L) i.1 (i.2-1) x) ∂xLaw M := by
  have ip i hit := (fitted_continuous_band_product_mean_decomposition M phi dphi L
    e he i.1 i.2 (hidx i hit).1 (hidx i hit).2 (hi i hit)).1
  have it (i : ℕ × ℕ) (hit : i ∈ t) : Integrable (fun x => gamma M L i.1 i.2 x *
      contJ L (trueNuisance M L) i.1 (i.2-1) x) (xLaw M) := by
    have ht : regularValue (trueNuisance M L).gamma i.1 i.2 = gamma M L i.1 i.2 := by
      funext x
      simp only [regularValue, trueNuisance, dif_pos (hidx i hit)]
    rw [← ht]
    exact (fitted_continuous_regular_gamma_memLp M L _ he0 i.1 i.2).integrable_mul
      (fitted_contJ_memLp M L _ he0 i.1 (i.2-1))
  rw [integral_finsetSum t ip, integral_finsetSum t it,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hit
  exact continuous_band_product_exact_bias_decomposition M phi dphi L e he he0
    i.1 i.2 (hidx i hit).1 (hidx i hit).2 (hi i hit)

-- @node: fitted_continuous_band_product_block_bias_bound
/-- Suppose [the fitted nuisances are admissible](hyp:he), [the true nuisances are admissible](hyp:he0),
[all level-band pairs in the finite block have valid levels and positive band indices](hyp:hidx), and
[each fitted band weight times its preceding component score is integrable](hyp:hi).
Then [the absolute bias of the block's product-score sum relative to its true target is bounded by the sum of the absolute mean fitted-weighted component corrections plus the sum of the products of the band-weight and band-target L2 errors](goal). -/
lemma fitted_continuous_band_product_block_bias_bound
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (e : NuisanceCont L) (he : ContAdmissible M L e)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (t : Finset (ℕ × ℕ))
    (hidx : ∀ i ∈ t, i.1 ≤ L.K ∧ 1 ≤ i.2 ∧ i.2 ≤ L.l i.1)
    (hi : ∀ i ∈ t, Integrable (fun o : Obs X Z => regularValue e.gamma i.1 i.2 o.1 *
      contScoreComponents M phi dphi L e i.1 (i.2-1) o) (observationLaw M)) :
    |(∫ o : Obs X Z, ∑ i ∈ t, psiProd M phi dphi L e i.1 i.2 o ∂observationLaw M) -
      (∫ x, ∑ i ∈ t, gamma M L i.1 i.2 x *
        contJ L (trueNuisance M L) i.1 (i.2-1) x ∂xLaw M)| ≤
    (∑ i ∈ t, |∫ o : Obs X Z, regularValue e.gamma i.1 i.2 o.1 *
      (contScoreComponents M phi dphi L e i.1 (i.2-1) o -
        contJ L (trueNuisance M L) i.1 (i.2-1) o.1) ∂observationLaw M|) +
    ∑ i ∈ t, finiteL2Error M (regularValue e.gamma i.1 i.2)
        (regularValue (trueNuisance M L).gamma i.1 i.2) *
      finiteL2Error M (contJ L e i.1 (i.2-1)) (contJ L (trueNuisance M L) i.1 (i.2-1)) := by
  rw [continuous_band_product_block_exact_bias_decomposition M phi dphi L e he he0
    t hidx hi]
  apply (abs_sub _ _).trans
  apply add_le_add
  · exact Finset.abs_sum_le_sum_abs _ t
  · apply (Finset.abs_sum_le_sum_abs _ t).trans
    apply Finset.sum_le_sum
    intro i _
    apply le_trans _ (fitted_continuous_band_product_absolute_cross_error_bound M L
      (trueNuisance M L) e he0 he i.1 i.2).2
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
      (fun x => (regularValue e.gamma i.1 i.2 x -
        regularValue (trueNuisance M L).gamma i.1 i.2 x) *
        (contJ L e i.1 (i.2-1) x - contJ L (trueNuisance M L) i.1 (i.2-1) x))

end Papers.TbsPrteOptimalTransport

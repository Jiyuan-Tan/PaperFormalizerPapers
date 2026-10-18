module
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationContinuousFullMean
/-! Simultaneous signed full-interval weight directions of the continuous total score. -/
public section
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- The prefactor and the signed assignment correction have opposite changes.
-- @node: continuous_full_product_weight_path
/-- For [a level index strictly below the number of levels](hyp:hk), [adding a scalar multiple of a direction to the full-interval weights changes the full product score by that scalar times the direction at the selected level times the difference between the debiased full-interval score and its plug-in value](goal). -/
lemma continuous_full_product_weight_path (L : LevelData Z X) (eta : NuisanceCont L)
    (d : Fin L.K → X → ℝ) (k : ℕ) (hk : k < L.K) (o : Obs X Z) (t : ℝ) :
    psiFullProd L {eta with gammaFull := fun a x => eta.gammaFull a x + t * d a x} k o =
      psiFullProd L eta k o + t * (d ⟨k, hk⟩ o.1 *
        (psiFullJ L eta k o - contFullJ L eta k o.1)) := by
  have hs : psiFullJ L
      {eta with gammaFull := fun a x => eta.gammaFull a x + t * d a x} k o =
      psiFullJ L eta k o := rfl
  have hj : contFullJ L
      {eta with gammaFull := fun a x => eta.gammaFull a x + t * d a x} k o.1 =
      contFullJ L eta k o.1 := rfl
  simp only [psiFullProd, hs, hj, fullValue, dif_pos hk]
  ring

-- All regular products and the final-bin score are independent of gamma_full.
-- @node: continuous_total_full_weight_path
/-- With [a positive number of levels](hyp:hK), [perturbing all full-interval weights by a scalar times a direction changes the total continuous score by that scalar times the sum, over levels, of the direction multiplied by the difference between the debiased full-interval score and its plug-in value](goal). -/
lemma continuous_total_full_weight_path (phi dphi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (hK : LevelCountPos L.K) (eta : NuisanceCont L)
    (d : Fin L.K → X → ℝ) (o : Obs X Z) (t : ℝ) :
    psiCont M phi dphi L hK o
      {eta with gammaFull := fun a x => eta.gammaFull a x + t * d a x} =
    psiCont M phi dphi L hK o eta + t *
      ∑ k ∈ Finset.range L.K, fullValue d k o.1 *
        (psiFullJ L eta k o - contFullJ L eta k o.1) := by
  have hr : ∀ k j, psiProd M phi dphi L
      {eta with gammaFull := fun a x => eta.gammaFull a x + t * d a x} k j o =
      psiProd M phi dphi L eta k j o := fun _ _ => rfl
  simp only [psiCont, hr]
  rw [Finset.mul_sum]
  have hf : ∀ k ∈ Finset.range L.K,
      psiFullProd L {eta with gammaFull := fun a x => eta.gammaFull a x + t * d a x} k o +
        ∑ j ∈ Finset.Icc 1 (L.l k), psiProd M phi dphi L eta k j o =
      (psiFullProd L eta k o +
        ∑ j ∈ Finset.Icc 1 (L.l k), psiProd M phi dphi L eta k j o) +
        t * (fullValue d k o.1 * (psiFullJ L eta k o - contFullJ L eta k o.1)) := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    rw [continuous_full_product_weight_path L eta d k hk', fullValue, dif_pos hk']
    ring
  rw [Finset.sum_congr rfl hf, Finset.sum_add_distrib]
  ring

-- Only primitive outcome and propensity residual integrability is assumed.
-- Their population centering supplies the cancellation for every full weight.
-- @node: population_continuous_total_full_weight_integral_path
/-- Under [threshold crossing](hyp:h), [a positive number of levels](hyp:hK), and [level ordering preserved by the policy](hyp:hOrder), take [measurable full-weight directions](hyp:hd). If the direction-weighted [positive outcome residuals](hyp:hp), [negative outcome residuals](hyp:hm), [upper propensity residuals multiplied by positive full-interval values](hyp:hrp), and [lower propensity residuals multiplied by negative full-interval values](hyp:hrm) are integrable and [the true total score is integrable](hyp:hbase), then [every scalar perturbation of the true full-interval weights leaves the population mean of the continuous score unchanged](goal). -/
lemma population_continuous_total_full_weight_integral_path
    (h : ThresholdCrossing M) (phi dphi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (d : Fin L.K → X → ℝ) (hd : ∀ a, Measurable (d a))
    (hp : ∀ k (hk : k < L.K), Integrable (fun o : Obs X Z => d ⟨k, hk⟩ o.1 *
      continuousFullOutcomeResidual L (trueNuisance M L) true k o) (observationLaw M))
    (hm : ∀ k (hk : k < L.K), Integrable (fun o : Obs X Z => d ⟨k, hk⟩ o.1 *
      continuousFullOutcomeResidual L (trueNuisance M L) false k o) (observationLaw M))
    (hrp : ∀ k (hk : k < L.K), Integrable (fun o : Obs X Z =>
      (d ⟨k, hk⟩ o.1 * fullValue (trueNuisance M L).JfullPlus k o.1) *
        RpCont L (trueNuisance M L) (k + 1) o) (observationLaw M))
    (hrm : ∀ k (hk : k < L.K), Integrable (fun o : Obs X Z =>
      (d ⟨k, hk⟩ o.1 * minusFullValue (trueNuisance M L) k o.1) *
        RpCont L (trueNuisance M L) k o) (observationLaw M))
    (hbase : Integrable (fun o => psiCont M phi dphi L hK o (trueNuisance M L))
      (observationLaw M)) (t : ℝ) :
    (∫ o, psiCont M phi dphi L hK o
      {trueNuisance M L with gammaFull := fun a x =>
        (trueNuisance M L).gammaFull a x + t * d a x} ∂observationLaw M) =
    ∫ o, psiCont M phi dphi L hK o (trueNuisance M L) ∂observationLaw M := by
  have hc k (hk : k < L.K) := population_continuous_full_correction_weighted_zero
    M h (policyProp phi M.prop) L hOrder k hk (d ⟨k, hk⟩) (hd ⟨k, hk⟩)
    (hp k hk) (hm k hk) (hrp k hk) (hrm k hk)
  have hi : ∀ k ∈ Finset.range L.K, Integrable (fun o : Obs X Z => fullValue d k o.1 *
      (psiFullJ L (trueNuisance M L) k o - contFullJ L (trueNuisance M L) k o.1))
      (observationLaw M) := by
    intro k hk
    simpa only [fullValue, dif_pos (Finset.mem_range.mp hk)] using
      (hc k (Finset.mem_range.mp hk)).1
  have hz : (∫ o : Obs X Z, ∑ k ∈ Finset.range L.K, fullValue d k o.1 *
      (psiFullJ L (trueNuisance M L) k o - contFullJ L (trueNuisance M L) k o.1)
      ∂observationLaw M) = 0 := by
    rw [integral_finsetSum _ hi]
    apply Finset.sum_eq_zero
    intro k hk
    simpa only [fullValue, dif_pos (Finset.mem_range.mp hk)] using
      (hc k (Finset.mem_range.mp hk)).2
  simp_rw [continuous_total_full_weight_path]
  rw [integral_add hbase ((integrable_finsetSum _ hi).const_mul t),
    integral_const_mul, hz, mul_zero, add_zero]

-- @node: population_continuous_total_full_weight_orthogonality
/-- Under [threshold crossing](hyp:h), [a positive number of levels](hyp:hK), and [policy-invariant level ordering](hyp:hOrder), take [measurable full-weight directions](hyp:hd). If the direction-weighted [positive outcome residuals](hyp:hp), [negative outcome residuals](hyp:hm), [upper propensity corrections](hyp:hrp), and [lower propensity corrections](hyp:hrm) are integrable and [the true total score is integrable](hyp:hbase), then [the population mean of the continuous score has derivative zero at the true full-interval weights along this direction](goal). -/
lemma population_continuous_total_full_weight_orthogonality
    (h : ThresholdCrossing M) (phi dphi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (d : Fin L.K → X → ℝ) (hd : ∀ a, Measurable (d a))
    (hp : ∀ k (hk : k < L.K), Integrable (fun o : Obs X Z => d ⟨k, hk⟩ o.1 *
      continuousFullOutcomeResidual L (trueNuisance M L) true k o) (observationLaw M))
    (hm : ∀ k (hk : k < L.K), Integrable (fun o : Obs X Z => d ⟨k, hk⟩ o.1 *
      continuousFullOutcomeResidual L (trueNuisance M L) false k o) (observationLaw M))
    (hrp : ∀ k (hk : k < L.K), Integrable (fun o : Obs X Z =>
      (d ⟨k, hk⟩ o.1 * fullValue (trueNuisance M L).JfullPlus k o.1) *
        RpCont L (trueNuisance M L) (k + 1) o) (observationLaw M))
    (hrm : ∀ k (hk : k < L.K), Integrable (fun o : Obs X Z =>
      (d ⟨k, hk⟩ o.1 * minusFullValue (trueNuisance M L) k o.1) *
        RpCont L (trueNuisance M L) k o) (observationLaw M))
    (hbase : Integrable (fun o => psiCont M phi dphi L hK o (trueNuisance M L))
      (observationLaw M)) :
    HasDerivAt (fun t : ℝ => ∫ o, psiCont M phi dphi L hK o
      {trueNuisance M L with gammaFull := fun a x =>
        (trueNuisance M L).gammaFull a x + t * d a x} ∂observationLaw M) 0 0 := by
  have heq : (fun t : ℝ => ∫ o, psiCont M phi dphi L hK o
      {trueNuisance M L with gammaFull := fun a x =>
        (trueNuisance M L).gammaFull a x + t * d a x} ∂observationLaw M) =
      (fun _ : ℝ => ∫ o, psiCont M phi dphi L hK o (trueNuisance M L)
        ∂observationLaw M) := by
    funext t
    exact population_continuous_total_full_weight_integral_path M h phi dphi L hK
      hOrder d hd hp hm hrp hrm hbase t
  rw [heq]
  exact hasDerivAt_const 0 _

end Papers.TbsPrteOptimalTransport

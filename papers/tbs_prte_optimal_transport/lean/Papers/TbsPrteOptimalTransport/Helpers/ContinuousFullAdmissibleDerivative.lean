module
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousFullProductJointBias
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousDirectionRegularity
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousFullBounds
/-! Full-interval joint path controls derived from continuous nuisance admissibility. -/
public section
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

-- Using the fitted propensity in the product expansion avoids a separate
-- quadratic direction term: it remains in the unit interval by admissibility.
-- @node: continuous_full_affine_product_error_bound
/-- If [the perturbed propensity has absolute value at most one](hyp:hp),
[the baseline outcome mean has absolute value at most the outcome bound](hyp:hj), and
[the propensity direction](hyp:hdp) and [outcome direction](hyp:hdj) have their respective absolute bounds,
[the absolute change in their affine product is at most the path magnitude times the sum of the outcome-direction bound and the propensity-direction bound times the outcome bound](goal). -/
lemma continuous_full_affine_product_error_bound (p j dp dj t P J Y : ℝ)
    (hp : |p + t * dp| ≤ 1) (hj : |j| ≤ Y)
    (hdp : |dp| ≤ P) (hdj : |dj| ≤ J) :
    |(p + t * dp) * (j + t * dj) - p * j| ≤ (J + P * Y) * |t| := by
  have hP : 0 ≤ P := (abs_nonneg dp).trans hdp
  have hid : (p + t * dp) * (j + t * dj) - p * j =
      (p + t * dp) * (t * dj) + (t * dp) * j := by ring
  rw [hid]
  calc
    _ ≤ |(p + t * dp) * (t * dj)| + |(t * dp) * j| := abs_add_le _ _
    _ = |p + t * dp| * (|t| * |dj|) + (|t| * |dp|) * |j| := by
      simp only [abs_mul]
    _ ≤ 1 * (|t| * J) + (|t| * P) * Y := by gcongr
    _ = _ := by ring

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: continuous_nuisance_path_zero
/-- [At path parameter zero, an affine continuous nuisance path equals its baseline nuisance collection](goal). -/
lemma continuous_nuisance_path_zero (L : LevelData Z X) (eta del : NuisanceCont L) :
    eta + (0 : ℝ) • del = eta := by
  cases eta
  change NuisanceCont.mk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _
  congr 1 <;> ext <;> simp <;> change (0 : ℝ) * _ = 0 <;> exact zero_mul _

-- One constant works for both sides and every full interval. No regularity
-- premise is added: the direction bounds and measurable paths are derived.
-- @node: continuous_full_coefficient_path_regular
/-- If [the continuous nuisance direction is admissible at the baseline nuisance collection](hyp:hd),
[there is a nonnegative constant such that, near zero and for every full interval and both sides, the perturbed and baseline regression coefficients are measurable and their absolute difference is almost surely at most that constant times the path magnitude](goal). -/
lemma continuous_full_coefficient_path_regular (L : LevelData Z X)
    (eta del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl eta) (.inl del)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ t : ℝ in 𝓝 0, ∀ (k : Fin L.K) (plus : Bool),
      Measurable (continuousFullRegressionCoefficient L (eta + t • del) plus k) ∧
      Measurable (continuousFullRegressionCoefficient L eta plus k) ∧
      ∀ᵐ x ∂xLaw M,
        |continuousFullRegressionCoefficient L (eta + t • del) plus k x -
          continuousFullRegressionCoefficient L eta plus k x| ≤ D * |t| := by
  obtain ⟨P, hP, hp⟩ := continuous_baseline_direction_regular M L eta del hd
  obtain ⟨J, hJ, hjp, hjm⟩ := continuous_full_outcome_direction_regular M L eta del hd
  obtain ⟨r, hr, hpath⟩ := hd.admissible
  have h0 := hpath 0 (by simpa using hr)
  rw [continuous_nuisance_path_zero] at h0
  rcases h0 with ⟨_, _, _, hp0, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, hjp0, hjpm0, hjm0, hjmm0, _⟩
  refine ⟨J + P * (|M.yMin| + |M.yMax|), by positivity, ?_⟩
  filter_upwards [continuousAt_id.abs.eventually_lt_const (by simpa using hr)] with t ht
  have had := hpath t ht
  rcases had with ⟨_, _, hpt, hpmt, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, _, hjpmt, _, hjmmt, _⟩
  intro k plus
  refine ⟨by fun_prop, by fun_prop, ?_⟩
  have hscalar (p j dp dj : ℝ) (hpt : p + t * dp ∈ Icc 0 1)
      (hj0 : j ∈ Icc M.yMin M.yMax) (hp : ‖dp‖ ≤ P) (hj : ‖dj‖ ≤ J) :
      |(p + t * dp) * (j + t * dj) - p * j| ≤
        (J + P * (|M.yMin| + |M.yMax|)) * |t| := by
    apply continuous_full_affine_product_error_bound
    · rw [abs_of_nonneg hpt.1]; exact hpt.2
    · rw [abs_le]
      constructor <;> nlinarith [neg_abs_le M.yMin, le_abs_self M.yMax,
        abs_nonneg M.yMin, abs_nonneg M.yMax, hj0.1, hj0.2]
    · simpa only [Real.norm_eq_abs] using hp
    · simpa only [Real.norm_eq_abs] using hj
  cases plus
  · by_cases hk : k.val = 0
    · simp only [continuousFullRegressionCoefficient, Bool.false_eq_true, if_false,
        if_pos hk, sub_self, abs_zero]
      exact Filter.Eventually.of_forall fun _ => by positivity
    · let a : PositiveIndex L.K := ⟨k, by omega, by omega⟩
      let b : {k : ℕ // 1 ≤ k ∧ k < L.K} := ⟨k, by omega, k.isLt⟩
      have ha : 1 ≤ k.val ∧ k.val ≤ L.K := a.property
      have hb : 1 ≤ k.val ∧ k.val < L.K := b.property
      filter_upwards [hpt a, hjm0 b, (hp a).2, (hjm b).2] with x hpx hjx hdpx hdjx
      simp only [continuousFullRegressionCoefficient, Bool.false_eq_true, if_false,
        if_neg hk, positiveValue, minusFullValue, dif_pos ha, dif_pos hb]
      exact hscalar (eta.pLev a x) (eta.JfullMinus b x)
          (del.pLev a x) (del.JfullMinus b x) hpx hjx hdpx hdjx
  · let a : PositiveIndex L.K := ⟨k+1, by omega, by omega⟩
    have ha : 1 ≤ k.val+1 ∧ k.val+1 ≤ L.K := a.property
    filter_upwards [hpt a, hjp0 k, (hp a).2, (hjp k).2] with x hpx hjx hdpx hdjx
    simp only [continuousFullRegressionCoefficient, if_true, positiveValue,
      fullValue, dif_pos ha, dif_pos k.isLt]
    exact hscalar (eta.pLev a x) (eta.JfullPlus k x)
        (del.pLev a x) (del.JfullPlus k x) hpx hjx hdpx hdjx

-- This is the full-interval part of the actual simultaneous nuisance
-- derivative. All local bounds required by the quadratic bias theorem are
-- discharged from the admissible path and population overlap.
-- @node: population_continuous_full_joint_product_orthogonality_of_admissible
/-- Under the [structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
[invariant level ordering](hyp:hL), and [baseline assignment overlap](hyp:hov), take
[an admissible continuous nuisance direction at the population nuisance collection](hyp:hd).
Then [the expected full-interval product score along the affine nuisance path has derivative zero at zero, and the score is integrable throughout some neighborhood of zero](goal). -/
lemma population_continuous_full_joint_product_orthogonality_of_admissible
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (q : Z → X → ℝ) (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del))
    (k : Fin L.K) :
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z,
      psiFullProd L (trueNuisance M L + t • del) k o ∂observationLaw M) 0 0 ∧
    (∀ᶠ t : ℝ in 𝓝 0, Integrable
      (psiFullProd L (trueNuisance M L + t • del) k) (observationLaw M)) := by
  haveI : IsProbabilityMeasure (observationLaw M) := by
    unfold observationLaw
    exact Measure.isProbabilityMeasure_map
      (M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY))).aemeasurable
  obtain ⟨D, hD, hcoef⟩ := continuous_full_coefficient_path_regular M L _ del hd
  obtain ⟨C, hC, hpi⟩ := continuous_assignment_direction_regular M L _ del hd
  obtain ⟨G, hG, hg⟩ := continuous_full_weight_direction_regular M L _ del hd
  obtain ⟨r, hr, hpath⟩ := hd.admissible
  apply population_continuous_full_joint_product_orthogonality M h he q L hL
    (fun t => trueNuisance M L + t • del)
    (continuous_nuisance_path_zero L _ del) k 1 D C G (cpi/2)
    (by norm_num) hD hC hG (div_pos hov.1 (by norm_num))
  filter_upwards [hcoef, continuous_assignment_path_uniform_lower_bound M L cpi hov del hd,
    continuousAt_id.abs.eventually_lt_const (by simpa using hr)] with t ht hclip htr
  have had := hpath t htr
  have hpim := had.2.2.2.2.2.1
  have hgm := had.2.2.2.2.2.2.2.2.2.2.2.1 k
  have hgb := had.2.2.2.2.2.2.2.2.2.2.1 k
  have hcm (plus : Bool) := (ht k plus).1
  have hjm : Measurable (contFullJ L (trueNuisance M L + t • del) k) := by
    first | fun_prop | skip
    have hid : contFullJ L (trueNuisance M L + t • del) k = fun x =>
        continuousFullRegressionCoefficient L (trueNuisance M L + t • del) true k x -
        continuousFullRegressionCoefficient L (trueNuisance M L + t • del) false k x := by
      funext x
      exact continuous_full_J_eq_regression_coefficient_contrast L _ k x
    rw [hid]
    fun_prop
  have hjbound : ∀ᵐ x ∂xLaw M,
      ‖contFullJ L (trueNuisance M L + t • del) k x‖ ≤
        2 * D * |t| + 2 * outcomeMagnitude M := by
    filter_upwards [(ht k true).2.2, (ht k false).2.2,
      population_contFullJ_norm_bound M h he q L hL k] with x hp hm hbase
    have hid : contFullJ L (trueNuisance M L + t • del) k x =
        (continuousFullRegressionCoefficient L (trueNuisance M L + t • del) true k x -
          continuousFullRegressionCoefficient L (trueNuisance M L) true k x) -
        (continuousFullRegressionCoefficient L (trueNuisance M L + t • del) false k x -
          continuousFullRegressionCoefficient L (trueNuisance M L) false k x) +
        contFullJ L (trueNuisance M L) k x := by
      rw [continuous_full_J_eq_regression_coefficient_contrast,
        continuous_full_J_eq_regression_coefficient_contrast]
      ring
    rw [hid, Real.norm_eq_abs]
    calc
      _ ≤ |continuousFullRegressionCoefficient L (trueNuisance M L + t • del) true k x -
          continuousFullRegressionCoefficient L (trueNuisance M L) true k x| +
        |continuousFullRegressionCoefficient L (trueNuisance M L + t • del) false k x -
          continuousFullRegressionCoefficient L (trueNuisance M L) false k x| +
        |contFullJ L (trueNuisance M L) k x| :=
          (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ _ := by simp only [Real.norm_eq_abs] at hbase; linarith
  have iji : Integrable (fun o : Obs X Z =>
      contFullJ L (trueNuisance M L + t • del) k o.1) (observationLaw M) :=
    Integrable.of_bound (hjm.comp measurable_fst).aestronglyMeasurable
      (2 * D * |t| + 2 * outcomeMagnitude M) (observationLaw_covariate_ae M _ hjbound)
  refine ⟨hpim, hclip, hgm, hjm, iji, ?_, ?_, ?_, ?_, ?_⟩
  · intro plus
    have hcm0 := (ht k plus).2.1
    fun_prop
  · filter_upwards [hgb] with x hx
    rw [Real.norm_eq_abs, abs_le]
    exact hx
  · exact fun plus => (ht k plus).2.2
  · intro a
    filter_upwards [(hpi a).2] with x hx
    change |((trueNuisance M L).piLev a x + t * del.piLev a x) -
      (trueNuisance M L).piLev a x| ≤ C * |t|
    simpa only [add_sub_cancel_left, abs_mul, mul_comm, Real.norm_eq_abs] using
      mul_le_mul_of_nonneg_left hx (abs_nonneg t)
  · filter_upwards [(hg k).2] with x hx
    change |gammaFull M L k x - (gammaFull M L k x + t * del.gammaFull k x)| ≤ G * |t|
    simpa only [sub_add_cancel_left, abs_neg, abs_mul, mul_comm, Real.norm_eq_abs] using
      mul_le_mul_of_nonneg_left hx (abs_nonneg t)

end Papers.TbsPrteOptimalTransport

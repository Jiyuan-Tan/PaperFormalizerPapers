module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousEncodedQuantile
/-! Bounded fitted weights preserve quantile-indicator L2 convergence.
The conditional disagreement probability controls the weighted discrepancy;
no convergence rate for the multiplying weight is needed. -/
public section
set_option linter.unusedFintypeInType false
set_option linter.unusedTactic false
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]

-- @node: treatedLaw_weighted_quantile_indicator_integrated_sq_bound
/-- If [the reference threshold](hyp:ha), [fitted threshold](hyp:hb), and
[weight](hyp:hw) are measurable and [the weight has absolute value at most D
almost everywhere](hyp:hwBound), then [the conditional treated mean squared
weighted difference of their lower-tail indicators is integrable over covariates,
and its population integral is at most D squared times the population integrated
squared unweighted indicator difference](goal). -/
lemma treatedLaw_weighted_quantile_indicator_integrated_sq_bound
    (M : LatentIVModel Ω X Z) (L : LevelData Z X) (k : ℕ)
    (a b w : X → ℝ) (D : ℝ)
    (ha : Measurable a) (hb : Measurable b) (hw : Measurable w)
    (hwBound : ∀ᵐ x ∂xLaw M, |w x| ≤ D) :
    Integrable (fun x => ∫ y,
      (w x * (indicator (y ≤ b x) - indicator (y ≤ a x))) ^ 2
        ∂treatedLaw M L k x) (xLaw M) ∧
    (∫ x, ∫ y, (w x * (indicator (y ≤ b x) - indicator (y ≤ a x))) ^ 2
      ∂treatedLaw M L k x ∂xLaw M) ≤
      D ^ 2 * (∫ x, ∫ y, (indicator (y ≤ b x) - indicator (y ≤ a x)) ^ 2
        ∂treatedLaw M L k x ∂xLaw M) := by
  have : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  let R := fun x => ∫ y, (indicator (y ≤ b x) - indicator (y ≤ a x)) ^ 2
    ∂treatedLaw M L k x
  have hRm : Measurable R := by fun_prop
  have hR0 (x : X) : 0 ≤ R x := integral_nonneg fun y => sq_nonneg _
  have hR1 (x : X) : R x ≤ 1 := by
    let := treatedLaw_isFiniteMeasure M L k x
    dsimp only [R]
    rw [quantile_indicator_sq_integral]
    exact (measureReal_mono (subset_univ _)).trans (treatedLaw_mass_le_one M L k x)
  have hRi : Integrable R (xLaw M) := by
    apply Integrable.of_bound hRm.aestronglyMeasurable 1
    exact Eventually.of_forall (fun x => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hR0 x)] using hR1 x)
  have hid (x : X) :
      (∫ y, (w x * (indicator (y ≤ b x) - indicator (y ≤ a x))) ^ 2
        ∂treatedLaw M L k x) = w x ^ 2 * R x := by
    simp_rw [mul_pow]
    exact integral_const_mul _ _
  have hbound : ∀ᵐ x ∂xLaw M, w x ^ 2 * R x ≤ D ^ 2 * R x := by
    filter_upwards [hwBound] with x hx
    have hD : 0 ≤ D := (abs_nonneg _).trans hx
    have hs : w x ^ 2 ≤ D ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (w x)) hx 2
    exact mul_le_mul_of_nonneg_right hs (hR0 x)
  have hwi : Integrable (fun x => w x ^ 2 * R x) (xLaw M) :=
    (hRi.const_mul (D ^ 2)).mono' (by fun_prop) (by
      filter_upwards [hbound] with x hx
      simpa only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (hR0 x))]
        using hx)
  simp_rw [hid]
  refine ⟨hwi, ?_⟩
  calc
    _ ≤ ∫ x, D ^ 2 * R x ∂xLaw M :=
      integral_mono_ae hwi (hRi.const_mul _) hbound
    _ = _ := integral_const_mul _ _

-- @node: treatedLaw_weighted_quantile_indicator_sq_tendsto_probability_zero
/-- If [the reference threshold is measurable](hyp:ht), [all fitted thresholds
are measurable](hyp:hf), [all fitted weights are measurable](hyp:hw), [the
weights have absolute value at most D almost everywhere](hyp:hwb), and [the
population integrated squared unweighted lower-tail indicator error using fits
at sample size twice n plus two converges to zero in probability](hyp:hi), then
[the same integrated squared indicator error multiplied inside the square by
the corresponding fitted weight also converges to zero in probability](goal). -/
lemma treatedLaw_weighted_quantile_indicator_sq_tendsto_probability_zero
    (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X) (k : ℕ)
    (truth : X → ℝ) (fit w : ℕ → A → X → ℝ) (D : ℝ)
    (ht : Measurable truth) (hf : ∀ n a, Measurable (fit n a))
    (hw : ∀ n a, Measurable (w n a))
    (hwb : ∀ n a, ∀ᵐ x ∂xLaw M, |w n a x| ≤ D)
    (hi : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ x, ∫ y,
        (indicator (y ≤ fit (2 * (n + 1)) a x) - indicator (y ≤ truth x)) ^ 2
          ∂treatedLaw M L k x ∂xLaw M) atTop (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ x, ∫ y,
        (w (2 * (n + 1)) a x * (indicator (y ≤ fit (2 * (n + 1)) a x) -
          indicator (y ≤ truth x))) ^ 2
          ∂treatedLaw M L k x ∂xLaw M) atTop (fun _ _ => 0) := by
  have hcont : Continuous (fun t : ℝ => D ^ 2 * t) := by fun_prop
  have h := Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt
    hcont.continuousAt hi
  simp only [mul_zero] at h
  apply probability_zero_of_nonneg_le μ _ _ h
  intro n
  apply Eventually.of_forall
  intro a
  exact ⟨integral_nonneg fun x => integral_nonneg fun y => sq_nonneg _,
    (treatedLaw_weighted_quantile_indicator_integrated_sq_bound M L k truth
      (fit (2 * (n + 1)) a) (w (2 * (n + 1)) a) D ht (hf _ a) (hw _ a) (hwb _ a)).2⟩

-- The coefficient used in the continuous product score is bounded by one
-- directly from clipping; its estimated value may depend on the training data.
-- @node: encoded_continuous_weighted_quantile_indicator_sq_tendsto_probability_zero
/-- Suppose [the true continuous nuisance specification is admissible](hyp:he0),
[every fitted specification satisfies continuous clipping](hyp:hclip), [its
fitted shares lie in the simplex](hyp:hshares), [all encoded fitted components
are measurable](hyp:hm), [the boundary density bounds hold](hyp:hd), and [the
encoded components satisfy the finite nuisance rate conditions](hyp:hrates).
If [the treated level is one above the boundary's level, or is that same level
when positive](hyp:hk'), then [the population integrated squared lower-tail
indicator error at that boundary, multiplied inside the square by the fitted
gamma weight at g times the fitted treatment probability at that level and using
fits at sample size twice n plus two, converges to zero in probability](goal). -/
lemma encoded_continuous_weighted_quantile_indicator_sq_tendsto_probability_zero
    [Fintype Z] (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n a, ContClipping M L (eh n a))
    (hshares : ∀ n a, ContFittedSharesSimplex L (eh n a))
    (hm : ∀ n a c, Measurable (contComponent M L (eh n a) c))
    (hd : BoundaryDensitiesBounded M L)
    (hrates : FiniteNuisanceRates M μ (fun n a => contComponent M L (eh n a))
      (contComponent M L (trueNuisance M L)))
    (c : BoundaryIndex L) (g : RegularIndex L) (k' : ℕ)
    (hk' : k' = c.val.1 + 1 ∨ (1 ≤ c.val.1 ∧ k' = c.val.1)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ x, ∫ y,
        (((eh (2 * (n + 1)) a).gamma g x *
            positiveValue (eh (2 * (n + 1)) a).pLev k' x) *
          (indicator (y ≤ (eh (2 * (n + 1)) a).nu c x) -
            indicator (y ≤ (trueNuisance M L).nu c x))) ^ 2
          ∂treatedLaw M L k' x ∂xLaw M) atTop (fun _ _ => 0) := by
  let er := fun n a => restrictContShares L (eh n a)
  have her n a : ContAdmissible M L (er n a) :=
    restrictContShares_admissible_of_encoded_clipping M L (eh n a)
      (hclip n a) (hshares n a) (hm n a)
  have hcoords n a : Measurable ((er n a).nu c) ∧
      Measurable (fun x => (er n a).gamma g x * positiveValue (er n a).pLev k' x) ∧
      (∀ᵐ x ∂xLaw M, |(er n a).gamma g x * positiveValue (er n a).pLev k' x| ≤ 1) := by
    rcases her n a with ⟨_, _, hp, hpm, _, _, _, _, _, _, _, _, hg, hgm,
      _, _, hn, hnm, _⟩
    have hpm' : Measurable (positiveValue (er n a).pLev k') := by
      first | fun_prop | skip
      change Measurable (fun x => positiveValue (er n a).pLev k' x)
      by_cases hi : 1 ≤ k' ∧ k' ≤ L.K
      · simpa only [positiveValue, dif_pos hi] using hpm ⟨k', hi⟩
      · simpa only [positiveValue, dif_neg hi] using
          (measurable_const : Measurable (fun _ : X => (0 : ℝ)))
    refine ⟨hnm c, by fun_prop, ?_⟩
    by_cases hi : 1 ≤ k' ∧ k' ≤ L.K
    · filter_upwards [hg g, hp ⟨k', hi⟩] with x hx hy
      simp only [positiveValue, dif_pos hi]
      rw [abs_mul, abs_of_nonneg hx.1, abs_of_nonneg hy.1]
      exact (mul_le_mul hx.2 hy.2 hy.1 zero_le_one).trans (by norm_num)
    · simp only [positiveValue, dif_neg hi, mul_zero, abs_zero]
      exact Eventually.of_forall (fun _ => zero_le_one)
  have ht : Measurable ((trueNuisance M L).nu c) := by
    first | fun_prop | skip
    rcases he0 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hnu, _⟩
    exact hnu c
  exact treatedLaw_weighted_quantile_indicator_sq_tendsto_probability_zero
    M μ L k' ((trueNuisance M L).nu c) (fun n a => (er n a).nu c)
    (fun n a x => (er n a).gamma g x * positiveValue (er n a).pLev k' x)
    1 ht (fun n a => (hcoords n a).1) (fun n a => (hcoords n a).2.1)
    (fun n a => (hcoords n a).2.2)
    (encoded_continuous_quantile_oracle_remainders M μ L he0 eh hclip hshares hm
      hd hrates c k' hk').2

end Papers.TbsPrteOptimalTransport

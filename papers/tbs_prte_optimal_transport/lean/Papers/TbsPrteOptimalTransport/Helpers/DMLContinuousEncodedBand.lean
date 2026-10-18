module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLChangingBandWeights
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousFullContrast
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousBandIndicatorJoint
/-! Convergence of centered continuous score bands from encoded nuisance rates.
Fixed endpoints have identically zero indicator error. Estimated endpoints use
the density bound, and the changing product coefficient uses its own L2 rate. -/
public section
set_option linter.style.openClassical false
set_option linter.unnecessarySimpa false
set_option linter.unreachableTactic false
set_option linter.unusedFintypeInType false
set_option linter.unusedTactic false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]

-- @node: encoded_continuous_nuValue_indicator_sq_tendsto_probability_zero
/-- Suppose [the true continuous nuisance record is admissible](hyp:he0), [all fitted records obey clipping bounds](hyp:hclip),
[their shares form simplices on policy sets](hyp:hshares), [their encoded coordinates are measurable](hyp:hm),
[the boundary densities are bounded](hyp:hd), and [the encoded nuisance family satisfies the finite nuisance rates](hyp:hr).
For [a treated level equal to the boundary level plus one, or to the boundary level when that level is positive](hyp:hk'),
[the population squared difference between fitted and true lower-tail indicators at the selected boundary converges in probability to zero, using fits at sample size twice a positive integer](goal). -/
lemma encoded_continuous_nuValue_indicator_sq_tendsto_probability_zero
    [Fintype Z] (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n a, ContClipping M L (eh n a))
    (hshares : ∀ n a, ContFittedSharesSimplex L (eh n a))
    (hm : ∀ n a c, Measurable (contComponent M L (eh n a) c))
    (hd : BoundaryDensitiesBounded M L)
    (hr : FiniteNuisanceRates M μ (fun n a => contComponent M L (eh n a))
      (contComponent M L (trueNuisance M L)))
    (k j k' : ℕ) (hk' : k' = k + 1 ∨ (1 ≤ k ∧ k' = k)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ x, ∫ y,
        (indicator (y ≤ nuValue M (eh (2*(n+1)) a) k j x) -
          indicator (y ≤ nuValue M (trueNuisance M L) k j x)) ^ 2
        ∂treatedLaw M L k' x ∂xLaw M) atTop (fun _ _ => 0) := by
  classical
  have hz : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun _ : ℕ => fun _ : A => (0 : ℝ)) atTop (fun _ _ => 0) := by
    rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm]
    intro eps heps
    simpa [not_le_of_gt heps] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (𝓝 0))
  by_cases hj : j = 0
  · simpa only [nuValue, if_pos hj, sub_self, zero_pow (by norm_num : 2 ≠ 0),
      integral_zero] using hz
  · by_cases hb : k < L.K ∧ 1 ≤ j ∧ j ≤ L.l k
    · simpa only [nuValue, if_neg hj, dif_pos hb] using
        (encoded_continuous_quantile_oracle_remainders M μ L he0 eh hclip hshares hm
          hd hr ⟨(k, j), hb⟩ k' hk').2
    · simpa only [nuValue, if_neg hj, dif_neg hb, sub_self,
        zero_pow (by norm_num : 2 ≠ 0), integral_zero] using hz

-- Includes the first band with its fixed lower endpoint and the terminal fixed
-- upper endpoint, as well as bands between two fitted boundary quantiles.
-- @node: encoded_continuous_changing_weight_centered_band_sq_tendsto_probability_zero
/-- Suppose [the true nuisance record is admissible](hyp:he0), [the fitted records obey clipping bounds](hyp:hclip),
[their shares form simplices on policy sets](hyp:hshares), [their encoded coordinates are measurable](hyp:hm),
[boundary densities are bounded](hyp:hd), and [the encoded nuisance family satisfies the finite nuisance rates](hyp:hr).
For [a treated level equal to the boundary level plus one, or to that level when positive](hyp:hk'),
[the population second moment of the conditionally centered difference between fitted and true band indicators weighted by the selected regular product weight converges in probability to zero, using fits at sample size twice a positive integer](goal). -/
lemma encoded_continuous_changing_weight_centered_band_sq_tendsto_probability_zero
    [Fintype Z] (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n a, ContClipping M L (eh n a))
    (hshares : ∀ n a, ContFittedSharesSimplex L (eh n a))
    (hm : ∀ n a c, Measurable (contComponent M L (eh n a) c))
    (hd : BoundaryDensitiesBounded M L)
    (hr : FiniteNuisanceRates M μ (fun n a => contComponent M L (eh n a))
      (contComponent M L (trueNuisance M L)))
    (g : RegularIndex L) (k j₀ j₁ k' : ℕ)
    (hk' : k' = k + 1 ∨ (1 ≤ k ∧ k' = k)) :
    let d : ℕ → A → X × ℝ → ℝ := fun n a p =>
      (eh (2*(n+1)) a).gamma g p.1 *
        indicator (nuValue M (eh (2*(n+1)) a) k j₀ p.1 < p.2 ∧
          p.2 ≤ nuValue M (eh (2*(n+1)) a) k j₁ p.1) -
      (trueNuisance M L).gamma g p.1 *
        indicator (nuValue M (trueNuisance M L) k j₀ p.1 < p.2 ∧
          p.2 ≤ nuValue M (trueNuisance M L) k j₁ p.1)
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ x, ∫ y, (d n a (x, y) -
        ∫ z, d n a (x, z) ∂treatedLaw M L k' x) ^ 2
        ∂treatedLaw M L k' x ∂xLaw M) atTop (fun _ _ => 0) := by
  classical
  let er := fun n a => restrictContShares L (eh n a)
  have her n a : ContAdmissible M L (er n a) :=
    restrictContShares_admissible_of_encoded_clipping M L (eh n a)
      (hclip n a) (hshares n a) (hm n a)
  have hgamma (e : NuisanceCont L) (he : ContAdmissible M L e) :
      Measurable (e.gamma g) ∧ (∀ᵐ x ∂xLaw M, |e.gamma g x| ≤ 1) := by
    rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hg, hgm, _⟩
    refine ⟨?_, ?_⟩
    · first | fun_prop | exact hgm g
    · filter_upwards [hg g] with x hx
      simpa only [abs_of_nonneg hx.1] using hx.2
  have hmem (e : NuisanceCont L) (he : ContAdmissible M L e) :
      MemLp (e.gamma g) 2 (xLaw M) := by
    have : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
    apply MemLp.of_bound (by first | fun_prop | exact (hgamma e he).1.aestronglyMeasurable) 1
    simpa only [Real.norm_eq_abs] using (hgamma e he).2
  obtain ⟨_, _, _, _, _, _, hrg, _⟩ :=
    continuous_component_rates_to_oracle_rates M μ L eh (trueNuisance M L) hr
  exact treatedLaw_changing_weight_centered_band_sq_tendsto_probability_zero
    M μ L k' (nuValue M (trueNuisance M L) k j₀)
    (nuValue M (trueNuisance M L) k j₁) ((trueNuisance M L).gamma g)
    (fun n a => nuValue M (er n a) k j₀)
    (fun n a => nuValue M (er n a) k j₁) (fun n a => (er n a).gamma g) 1
    (by fun_prop) (by fun_prop) (hgamma _ he0).1
    (fun n a => continuous_admissible_nuValue_measurable M L _ (her n a) k j₀)
    (fun n a => continuous_admissible_nuValue_measurable M L _ (her n a) k j₁)
    (fun n a => (hgamma _ (her n a)).1)
    (fun n a => (hgamma _ (her n a)).2)
    (fun n a => (hmem _ (her n a)).sub (hmem _ he0))
    (encoded_continuous_nuValue_indicator_sq_tendsto_probability_zero
      M μ L he0 eh hclip hshares hm hd hr k j₀ k' hk')
    (encoded_continuous_nuValue_indicator_sq_tendsto_probability_zero
      M μ L he0 eh hclip hshares hm hd hr k j₁ k' hk')
    (nuisanceRates_xLaw_sq_tendsto_probability_zero M μ _ _ hrg g)

-- @node: nuisanceRates_continuous_band_coefficient_sq_tendsto_probability_zero
/-- If [the reference record is admissible](hyp:he0), [all fitted records are admissible](hyp:heh),
[treatment probabilities satisfy the finite nuisance rates](hyp:hrp), and [regular product weights satisfy those rates](hyp:hrg), then
[the population squared error of the selected regular product weight times treatment-probability coefficient converges in probability to zero, using fits at sample size twice a positive integer](goal). -/
lemma nuisanceRates_continuous_band_coefficient_sq_tendsto_probability_zero
    [Fintype Z] (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X)
    (e0 : NuisanceCont L) (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L e0) (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrg : FiniteNuisanceRates M μ (fun n a => (eh n a).gamma) e0.gamma)
    (g : RegularIndex L) (i : ℕ) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ x,
        ((eh (2*(n+1)) a).gamma g x * positiveValue (eh (2*(n+1)) a).pLev i x -
          e0.gamma g x * positiveValue e0.pLev i x) ^ 2 ∂xLaw M)
      atTop (fun _ _ => 0) := by
  classical
  have : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  have hg (e : NuisanceCont L) (he : ContAdmissible M L e) :
      Measurable (e.gamma g) ∧ (∀ᵐ x ∂xLaw M, |e.gamma g x| ≤ 1) := by
    rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hg, hgm, _⟩
    refine ⟨?_, ?_⟩
    · first | fun_prop | exact hgm g
    · filter_upwards [hg g] with x hx
      simpa only [abs_of_nonneg hx.1] using hx.2
  have hp (e : NuisanceCont L) (he : ContAdmissible M L e) :=
    (fitted_continuous_full_coordinates M L e he i).1
  have hgm (e : NuisanceCont L) (he : ContAdmissible M L e) :
      MemLp (e.gamma g) 2 (xLaw M) := by
    apply MemLp.of_bound (by first | fun_prop | exact (hg e he).1.aestronglyMeasurable) 1
    simpa only [Real.norm_eq_abs] using (hg e he).2
  have hpm (e : NuisanceCont L) (he : ContAdmissible M L e) :
      MemLp (positiveValue e.pLev i) 2 (xLaw M) := by
    apply MemLp.of_bound (by first | fun_prop | exact (hp e he).1.aestronglyMeasurable) 1
    simpa only [Real.norm_eq_abs] using (hp e he).2
  exact dml_weighted_residual_sq_tendsto_probability_zero μ (xLaw M)
    (e0.gamma g) (positiveValue e0.pLev i)
    (fun n a => (eh (2*(n+1)) a).gamma g)
    (fun n a => positiveValue (eh (2*(n+1)) a).pLev i) 1 1
    (hg e0 he0).1 (hp e0 he0).1
    (fun n a => (hg _ (heh _ a)).1) (fun n a => (hp _ (heh _ a)).1)
    (fun n a => (hgm _ (heh _ a)).sub (hgm e0 he0))
    (fun n a => (hpm _ (heh _ a)).sub (hpm e0 he0))
    (fun n a => (hg _ (heh _ a)).2) (fun _ _ => (hp e0 he0).2)
    (nuisanceRates_xLaw_sq_tendsto_probability_zero M μ _ _ hrg g)
    (nuisanceRates_xLaw_sq_tendsto_probability_zero M μ _ _
      (nuisanceRates_positiveValue M μ L.K _ _ hrp) i)

-- The actual indicator part of a continuous product score carries gamma * p.
-- Neither convergence of that product nor of the score is assumed here.
-- @node: encoded_continuous_propensity_weighted_centered_band_sq_tendsto_probability_zero
/-- Suppose [the true nuisance record is admissible](hyp:he0), [fitted records obey clipping bounds](hyp:hclip),
[their shares form simplices on policy sets](hyp:hshares), [their encoded coordinates are measurable](hyp:hm),
[boundary densities are bounded](hyp:hd), and [the encoded nuisance family satisfies the finite nuisance rates](hyp:hr).
For [a treated level equal to the boundary level plus one, or to that level when positive](hyp:hk'),
[the population second moment of the conditionally centered difference between fitted and true band indicators weighted by the selected regular product weight times treatment probability converges in probability to zero, using fits at sample size twice a positive integer](goal). -/
lemma encoded_continuous_propensity_weighted_centered_band_sq_tendsto_probability_zero
    [Fintype Z] (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n a, ContClipping M L (eh n a))
    (hshares : ∀ n a, ContFittedSharesSimplex L (eh n a))
    (hm : ∀ n a c, Measurable (contComponent M L (eh n a) c))
    (hd : BoundaryDensitiesBounded M L)
    (hr : FiniteNuisanceRates M μ (fun n a => contComponent M L (eh n a))
      (contComponent M L (trueNuisance M L)))
    (g : RegularIndex L) (k j₀ j₁ k' : ℕ)
    (hk' : k' = k + 1 ∨ (1 ≤ k ∧ k' = k)) :
    let d : ℕ → A → X × ℝ → ℝ := fun n a p =>
      ((eh (2*(n+1)) a).gamma g p.1 * positiveValue (eh (2*(n+1)) a).pLev k' p.1) *
        indicator (nuValue M (eh (2*(n+1)) a) k j₀ p.1 < p.2 ∧
          p.2 ≤ nuValue M (eh (2*(n+1)) a) k j₁ p.1) -
      ((trueNuisance M L).gamma g p.1 * positiveValue (trueNuisance M L).pLev k' p.1) *
        indicator (nuValue M (trueNuisance M L) k j₀ p.1 < p.2 ∧
          p.2 ≤ nuValue M (trueNuisance M L) k j₁ p.1)
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ x, ∫ y, (d n a (x, y) -
        ∫ z, d n a (x, z) ∂treatedLaw M L k' x) ^ 2
        ∂treatedLaw M L k' x ∂xLaw M) atTop (fun _ _ => 0) := by
  classical
  let er := fun n a => restrictContShares L (eh n a)
  have her n a : ContAdmissible M L (er n a) :=
    restrictContShares_admissible_of_encoded_clipping M L (eh n a)
      (hclip n a) (hshares n a) (hm n a)
  let w := fun (e : NuisanceCont L) x => e.gamma g x * positiveValue e.pLev k' x
  have hw (e : NuisanceCont L) (he : ContAdmissible M L e) :
      Measurable (w e) ∧ (∀ᵐ x ∂xLaw M, |w e x| ≤ 1) := by
    have hp := (fitted_continuous_full_coordinates M L e he k').1
    rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hg, hgm, _⟩
    refine ⟨?_, ?_⟩
    · first | fun_prop | exact (hgm g).mul hp.1
    · filter_upwards [hg g, hp.2] with x hx hy
      dsimp only [w]
      rw [abs_mul, abs_of_nonneg hx.1]
      exact (mul_le_mul hx.2 hy (abs_nonneg _) zero_le_one).trans (by norm_num)
  have hmem (e : NuisanceCont L) (he : ContAdmissible M L e) :
      MemLp (w e) 2 (xLaw M) := by
    have : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
    apply MemLp.of_bound (by first | fun_prop | exact (hw e he).1.aestronglyMeasurable) 1
    simpa only [Real.norm_eq_abs] using (hw e he).2
  obtain ⟨_, hrp, _, _, _, _, hrg, _⟩ :=
    continuous_component_rates_to_oracle_rates M μ L eh (trueNuisance M L) hr
  exact treatedLaw_changing_weight_centered_band_sq_tendsto_probability_zero
    M μ L k' (nuValue M (trueNuisance M L) k j₀)
    (nuValue M (trueNuisance M L) k j₁) (w (trueNuisance M L))
    (fun n a => nuValue M (er n a) k j₀)
    (fun n a => nuValue M (er n a) k j₁) (fun n a => w (er n a)) 1
    (by fun_prop) (by fun_prop) (hw _ he0).1
    (fun n a => continuous_admissible_nuValue_measurable M L _ (her n a) k j₀)
    (fun n a => continuous_admissible_nuValue_measurable M L _ (her n a) k j₁)
    (fun n a => (hw _ (her n a)).1) (fun n a => (hw _ (her n a)).2)
    (fun n a => (hmem _ (her n a)).sub (hmem _ he0))
    (encoded_continuous_nuValue_indicator_sq_tendsto_probability_zero
      M μ L he0 eh hclip hshares hm hd hr k j₀ k' hk')
    (encoded_continuous_nuValue_indicator_sq_tendsto_probability_zero
      M μ L he0 eh hclip hshares hm hd hr k j₁ k' hk')
    (nuisanceRates_continuous_band_coefficient_sq_tendsto_probability_zero
      M μ L (trueNuisance M L) er he0 her hrp hrg g k')

end Papers.TbsPrteOptimalTransport

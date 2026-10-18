module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousComponentBridge
public import Papers.TbsPrteOptimalTransport.Helpers.DMLIndicatorRates
public import Papers.TbsPrteOptimalTransport.Helpers.DMLQuantileBiasRates
/-! Quantile-boundary remainders from the encoded continuous nuisance conditions.
Clipping supplies the moments needed for indicator convergence, while local
density bounds give quadratic bias control, including remote boundary errors. -/
public section
set_option linter.style.openClassical false
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
  [Nonempty X] [Nonempty Z] [Fintype Z]

-- @node: nuisanceRates_continuous_quantile_indicator_sq_tendsto_probability_zero
/-- If [the true nuisance record is admissible](hyp:he0), [all fitted records are admissible](hyp:heh),
[boundary densities are bounded](hyp:hd), and [the quantile-boundary estimates satisfy the finite nuisance rates](hyp:hrates), then,
for [a treated level equal to the boundary level plus one, or to the boundary level when positive](hyp:hk'),
[the population squared difference between fitted and true lower-tail indicators at the selected boundary converges in probability to zero, using fits at sample size twice a positive integer](goal). -/
lemma nuisanceRates_continuous_quantile_indicator_sq_tendsto_probability_zero
    (M : LatentIVModel Ω X Z) {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (L : LevelData Z X) (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hd : BoundaryDensitiesBounded M L)
    (hrates : FiniteNuisanceRates M μ (fun n a => (eh n a).nu) (trueNuisance M L).nu)
    (c : BoundaryIndex L) (k' : ℕ)
    (hk' : k' = c.val.1 + 1 ∨ (1 ≤ c.val.1 ∧ k' = c.val.1)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ x, ∫ y,
        (indicator (y ≤ (eh (2*(n+1)) a).nu c x) -
          indicator (y ≤ (trueNuisance M L).nu c x))^2
          ∂treatedLaw M L k' x ∂xLaw M) atTop (fun _ _ => 0) := by
  obtain ⟨r, C, hr, hC, hdensity⟩ := dml_quantile_boundary_density_constants M L hd
  have : IsProbabilityMeasure (xLaw M) :=
    Measure.isProbabilityMeasure_map M.measX.aemeasurable
  rcases he0 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hn0, hm0, _⟩
  have hnh n a : ∀ c, ∀ᵐ x ∂xLaw M, (eh n a).nu c x ∈ Icc M.yMin M.yMax := by
    rcases heh n a with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hn, _⟩
    exact hn
  have hmh n a (c : BoundaryIndex L) : Measurable ((eh n a).nu c) := by
    first | fun_prop | skip
    rcases heh n a with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _⟩
    exact hm c
  have ht : MemLp ((trueNuisance M L).nu c) 2 (xLaw M) := by
    apply memLp_of_bounded (hn0 c)
    fun_prop
  have hf n a : MemLp ((eh n a).nu c) 2 (xLaw M) := by
    apply memLp_of_bounded (hnh n a c)
    fun_prop
  exact nuisanceRates_quantile_indicator_sq_tendsto_probability_zero M μ L k'
    (trueNuisance M L).nu (fun n a => (eh n a).nu) c r C (hm0 c)
    (fun n a => hmh n a c) hr hC (fun n a => (hf n a).sub ht)
    (hdensity c k' hk') hrates

-- @node: encoded_continuous_quantile_oracle_remainders
/-- Suppose [the true nuisance record is admissible](hyp:he0), [fitted records obey clipping bounds](hyp:hclip),
[their shares form simplices on policy sets](hyp:hshares), [their encoded coordinates are measurable](hyp:hm),
[boundary densities are bounded](hyp:hd), and [the encoded nuisance family satisfies the finite nuisance rates](hyp:hr).
For [a treated level equal to the boundary level plus one, or to the boundary level when positive](hyp:hk'),
[both the square-root-scaled integral of fitted boundary minus outcome over the interval between the true and fitted boundaries, and the population squared difference of their lower-tail indicators, converge in probability to zero, using fits at sample size twice a positive integer and scaling by the square root of that integer](goal). -/
lemma encoded_continuous_quantile_oracle_remainders
    (M : LatentIVModel Ω X Z) {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (L : LevelData Z X)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n a, ContClipping M L (eh n a))
    (hshares : ∀ n a, ContFittedSharesSimplex L (eh n a))
    (hm : ∀ n a c, Measurable (contComponent M L (eh n a) c))
    (hd : BoundaryDensitiesBounded M L)
    (hr : FiniteNuisanceRates M μ (fun n a => contComponent M L (eh n a))
      (contComponent M L (trueNuisance M L)))
    (c : BoundaryIndex L) (k' : ℕ)
    (hk' : k' = c.val.1 + 1 ∨ (1 ≤ c.val.1 ∧ k' = c.val.1)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
        (∫ x, ∫ y in
          Ioc (min ((trueNuisance M L).nu c x) ((eh (2*(n+1)) a).nu c x))
            (max ((trueNuisance M L).nu c x) ((eh (2*(n+1)) a).nu c x)),
          (eh (2*(n+1)) a).nu c x - y ∂treatedLaw M L k' x ∂xLaw M))
      atTop (fun _ _ => 0) ∧
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ x, ∫ y,
        (indicator (y ≤ (eh (2*(n+1)) a).nu c x) -
          indicator (y ≤ (trueNuisance M L).nu c x))^2
          ∂treatedLaw M L k' x ∂xLaw M) atTop (fun _ _ => 0) := by
  let er := fun n a => restrictContShares L (eh n a)
  have her n a : ContAdmissible M L (er n a) :=
    restrictContShares_admissible_of_encoded_clipping M L (eh n a)
      (hclip n a) (hshares n a) (hm n a)
  obtain ⟨_, _, _, _, _, _, _, _, hrnu, _⟩ :=
    continuous_component_rates_to_oracle_rates M μ L eh (trueNuisance M L) hr
  exact ⟨nuisanceRates_continuous_quantile_boundary_bias_root_n_negligible
    M μ L er he0 her hd hrnu c k' hk',
    nuisanceRates_continuous_quantile_indicator_sq_tendsto_probability_zero
      M μ L er he0 her hd hrnu c k' hk'⟩

end Papers.TbsPrteOptimalTransport

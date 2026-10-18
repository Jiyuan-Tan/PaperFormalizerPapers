module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousFullResidual
/-! Second moments and convergence of signed, fitted-weight continuous
full-interval outcome residuals, derived from clipping and component rates. -/
public section
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.unreachableTactic false
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

-- @node: fitted_continuous_gammaFull_coordinates
/-- For level data and fitted nuisances, [admissibility](hyp:he) implies that
[each full-interval signed weight is measurable and has absolute value at most one
almost surely under the covariate distribution](goal). -/
lemma fitted_continuous_gammaFull_coordinates (L : LevelData Z X)
    (e : NuisanceCont L) (he : ContAdmissible M L e) (k : Fin L.K) :
    Measurable (e.gammaFull k) ∧ ∀ᵐ x ∂xLaw M, |e.gammaFull k x| ≤ 1 := by
  refine ⟨?_, ?_⟩
  · first | fun_prop | exact he.2.2.2.2.2.2.2.2.2.2.2.1 k
  · filter_upwards [he.2.2.2.2.2.2.2.2.2.2.1 k] with x hx
    exact abs_le.mpr hx

-- @node: fitted_continuous_gammaFull_memLp
/-- If [the fitted nuisances are admissible](hyp:he), then [each full-interval
signed weight has a finite second moment under the covariate distribution](goal). -/
lemma fitted_continuous_gammaFull_memLp (L : LevelData Z X)
    (e : NuisanceCont L) (he : ContAdmissible M L e) (k : Fin L.K) :
    MemLp (e.gammaFull k) 2 (xLaw M) := by
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  apply MemLp.of_bound (by
    first | fun_prop | exact (fitted_continuous_gammaFull_coordinates M L e he k).1.aestronglyMeasurable) 1
  simpa only [Real.norm_eq_abs] using (fitted_continuous_gammaFull_coordinates M L e he k).2

-- @node: fitted_continuous_weighted_full_residual_memLp
/-- Suppose [the fitted nuisances are admissible](hyp:he), [potential outcomes
obey the support restriction](hyp:hp), [observed outcomes satisfy consistency](hyp:hcons),
and [the outcome endpoints are known](hyp:hend). If [the clipping constant is
positive](hyp:hc) and [every fitted assignment probability is at least that
constant almost surely](hyp:hclip), then [the full-interval outcome residual,
multiplied by its fitted signed weight, has a finite second moment under the
observation distribution, for either sign and every full interval](goal). -/
lemma fitted_continuous_weighted_full_residual_memLp (L : LevelData Z X)
    (e : NuisanceCont L) (he : ContAdmissible M L e)
    (hp : PotentialSupport M) (hcons : Consistency M) (hend : OutcomeEndpointsKnown M)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (plus : Bool) (k : Fin L.K) :
    MemLp (fun o => e.gammaFull k o.1 * continuousFullOutcomeResidual L e plus k o)
      2 (observationLaw M) := by
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  have hg := (fitted_continuous_gammaFull_coordinates M L e he k).1
  have hr := fitted_continuous_full_residual_measurable M L e he plus k
  apply MemLp.of_bound (by first | fun_prop | exact
    ((hg.comp measurable_fst).mul hr).aestronglyMeasurable)
    (2 * max |M.yMin| |M.yMax| / c)
  filter_upwards [fitted_continuous_full_residual_abs_bound M L e he hp hcons hend
    c hc hclip plus k k.isLt, observationLaw_covariate_ae M _
      (fitted_continuous_gammaFull_coordinates M L e he k).2] with o hr hg
  rw [Real.norm_eq_abs, abs_mul]
  exact (mul_le_mul hg hr (abs_nonneg _) zero_le_one).trans_eq (one_mul _)

-- @node: nuisanceRates_continuous_weighted_full_residual_sq_tendsto_probability_zero
/-- For [a sequence of fitted continuous nuisances](hyp:eh), suppose [the reference
nuisances are admissible](hyp:he0), [every fitted nuisance is admissible](hyp:heh),
[potential outcomes obey the support restriction](hyp:hp), [consistency holds](hyp:hcons),
and [the outcome endpoints are known](hyp:hend). If [the clipping constant is
positive](hyp:hc), [reference and fitted assignment probabilities are uniformly
bounded below by it almost surely](hyp:hclip), and the [assignment probabilities](hyp:hrpi),
[upper full-interval regressions](hyp:hrplus), [lower full-interval regressions](hyp:hrminus),
and [signed full-interval weights](hyp:hrg) satisfy their finite nuisance rate
conditions, then [the observation-integrated squared error of the signed-weighted
outcome residual converges in probability to zero, for either sign and each full
interval, along sample sizes twice one plus the sequence index](goal). -/
lemma nuisanceRates_continuous_weighted_full_residual_sq_tendsto_probability_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (L : LevelData Z X) (e0 : NuisanceCont L) (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L e0) (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hp : PotentialSupport M) (hcons : Consistency M) (hend : OutcomeEndpointsKnown M)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a (i : PositiveIndex L.K), ∀ᵐ x ∂xLaw M,
      c ≤ e0.piLev i x ∧ c ≤ (eh n a).piLev i x)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) e0.piLev)
    (hrplus : FiniteNuisanceRates M μ (fun n a => (eh n a).JfullPlus) e0.JfullPlus)
    (hrminus : FiniteNuisanceRates M μ (fun n a => (eh n a).JfullMinus) e0.JfullMinus)
    (hrg : FiniteNuisanceRates M μ (fun n a => (eh n a).gammaFull) e0.gammaFull)
    (plus : Bool) (k : Fin L.K) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o,
        ((eh (2*(n+1)) a).gammaFull k o.1 *
            continuousFullOutcomeResidual L (eh (2*(n+1)) a) plus k o -
          e0.gammaFull k o.1 * continuousFullOutcomeResidual L e0 plus k o)^2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  have hg0 := (fitted_continuous_gammaFull_coordinates M L e0 he0 k).1
  have hgh n a := (fitted_continuous_gammaFull_coordinates M L (eh n a) (heh n a) k).1
  apply dml_weighted_residual_sq_tendsto_probability_zero μ (observationLaw M)
    (fun o => e0.gammaFull k o.1) (continuousFullOutcomeResidual L e0 plus k)
    (fun n a o => (eh (2*(n+1)) a).gammaFull k o.1)
    (fun n a => continuousFullOutcomeResidual L (eh (2*(n+1)) a) plus k)
    1 (2 * max |M.yMin| |M.yMax| / c)
    (by fun_prop) (by fun_prop) (by intro n a; fun_prop)
    (by intro n a; first | fun_prop | exact
      fitted_continuous_full_residual_measurable M L _ (heh _ a) plus k)
  · intro n a
    exact ((fitted_continuous_gammaFull_memLp M L _ (heh _ a) k).sub
      (fitted_continuous_gammaFull_memLp M L e0 he0 k)).comp_measurePreserving
        (observationLaw_fst_measurePreserving M)
  · intro n a
    exact (fitted_continuous_full_residual_memLp M L _ (heh _ a) hp hcons hend c hc
      (fun i => (hclip _ a i).mono (fun _ hx => hx.2)) plus k k.isLt).sub
        (fitted_continuous_full_residual_memLp M L e0 he0 hp hcons hend c hc
          (fun i => (hclip (2*(n+1)) a i).mono (fun _ hx => hx.1)) plus k k.isLt)
  · intro n a
    exact observationLaw_covariate_ae M _
      (fitted_continuous_gammaFull_coordinates M L _ (heh _ a) k).2
  · intro n a
    exact fitted_continuous_full_residual_abs_bound M L e0 he0 hp hcons hend c hc
      (fun i => (hclip n a i).mono (fun _ hx => hx.1)) plus k k.isLt
  · exact nuisanceRates_covariate_sq_tendsto_probability_zero M μ _ _
      (fun k => (fitted_continuous_gammaFull_coordinates M L e0 he0 k).1)
      (fun n a k => (fitted_continuous_gammaFull_coordinates M L _ (heh n a) k).1) hrg k
  · exact nuisanceRates_continuous_full_residual_sq_tendsto_probability_zero M μ L e0 eh
      he0 heh hp hcons hend c hc hclip hrpi hrplus hrminus plus k k.isLt

-- @node: nuisanceRates_continuous_weighted_full_residual_block_sq_tendsto_probability_zero
/-- For [a sequence of fitted continuous nuisances](hyp:eh), assume [admissibility
of the reference nuisances](hyp:he0) and [all fitted nuisances](hyp:heh),
[the potential-outcome support restriction](hyp:hp), [consistency](hyp:hcons), and
[known outcome endpoints](hyp:hend). Under [a positive clipping constant](hyp:hc),
[a common almost-sure lower bound on reference and fitted assignment probabilities](hyp:hclip),
and finite nuisance rate conditions for [assignment probabilities](hyp:hrpi),
[upper regressions](hyp:hrplus), [lower regressions](hyp:hrminus), and
[signed weights](hyp:hrg), [the observation-integrated square of the sum of
signed-weighted outcome-residual errors over all full intervals converges in
probability to zero, for either sign, using fits at sample sizes twice one plus
the sequence index](goal). -/
lemma nuisanceRates_continuous_weighted_full_residual_block_sq_tendsto_probability_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (L : LevelData Z X) (e0 : NuisanceCont L) (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L e0) (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hp : PotentialSupport M) (hcons : Consistency M) (hend : OutcomeEndpointsKnown M)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a (i : PositiveIndex L.K), ∀ᵐ x ∂xLaw M,
      c ≤ e0.piLev i x ∧ c ≤ (eh n a).piLev i x)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) e0.piLev)
    (hrplus : FiniteNuisanceRates M μ (fun n a => (eh n a).JfullPlus) e0.JfullPlus)
    (hrminus : FiniteNuisanceRates M μ (fun n a => (eh n a).JfullMinus) e0.JfullMinus)
    (hrg : FiniteNuisanceRates M μ (fun n a => (eh n a).gammaFull) e0.gammaFull)
    (plus : Bool) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o,
        (∑ k : Fin L.K,
          ((eh (2*(n+1)) a).gammaFull k o.1 *
              continuousFullOutcomeResidual L (eh (2*(n+1)) a) plus k o -
            e0.gammaFull k o.1 * continuousFullOutcomeResidual L e0 plus k o))^2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  apply dml_finset_sum_sq_tendsto_probability_zero
  · intro k hk n a
    exact (fitted_continuous_weighted_full_residual_memLp M L _ (heh _ a)
      hp hcons hend c hc (fun i => (hclip _ a i).mono (fun _ hx => hx.2)) plus k).sub
        (fitted_continuous_weighted_full_residual_memLp M L e0 he0
          hp hcons hend c hc
          (fun i => (hclip (2*(n+1)) a i).mono (fun _ hx => hx.1)) plus k)
  · intro k hk
    exact nuisanceRates_continuous_weighted_full_residual_sq_tendsto_probability_zero
      M μ L e0 eh he0 heh hp hcons hend c hc hclip hrpi hrplus hrminus hrg plus k

end Papers.TbsPrteOptimalTransport

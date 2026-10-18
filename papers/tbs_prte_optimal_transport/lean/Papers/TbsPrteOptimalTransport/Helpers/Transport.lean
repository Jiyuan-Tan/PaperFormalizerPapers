module
public import Causalean.Stat.Coupling.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Causalean.Stat.Quantile.Quantile
public import Toolkit.Tricks.Probability.Moments.QuantileVersions
/-! Product-cost transport and the single lower-quantile convention. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Set
open scoped ENNReal
open Causalean.Stat
open Toolkit.Tricks.Probability.Moments
-- @env: S2
variable (mu nu : Measure ℝ) (Qmu Qnu : ℝ → ℝ)
-- @node: ass:1d-ot-probability-laws
/-- The [quantile-pair condition](goal) for [the first law](hyp:mu), [the second law](hyp:nu),
[the first quantile function](hyp:Qmu), and [the second quantile function](hyp:Qnu) requires
[the first law to be a probability measure](step:1), [the second law to be a probability
measure](step:2), [the first function to equal its law's lower quantile on the open unit
interval](step:3), and [the second function to equal its law's lower quantile there](step:4). -/
def IsQuantilePair : Prop :=
  IsProbabilityMeasure mu ∧ -- @realizes \mu(probability law on ℝ)
  IsProbabilityMeasure nu ∧ -- @realizes \nu(probability law on ℝ)
  (∀ t ∈ Ioo (0 : ℝ) 1, Qmu t = quantile mu t) ∧ -- @realizes Q_\mu(lower inverse on (0,1))
  (∀ t ∈ Ioo (0 : ℝ) 1, Qnu t = quantile nu t) -- @realizes Q_\nu(lower inverse on (0,1))
-- @node: ass:1d-ot-moment-support
/-- For [the first law](hyp:mu) and [the second law](hyp:nu), the [support-or-moment
condition](goal) holds when either the first law is concentrated on a bounded symmetric
interval and the second has a finite absolute first moment, or the reverse holds. -/
def BoundedSupportOrFirstMoment : Prop :=
  ((∃ B : ℝ, mu (Icc (-B) B)ᶜ = 0) ∧ Integrable id nu) ∨
  ((∃ B : ℝ, nu (Icc (-B) B)ᶜ = 0) ∧ Integrable id mu)
-- @node: ass:1d-ot-product-cost
/-- For [a cost function of two real outcomes](hyp:c), the [product-cost condition](goal)
requires the cost of every pair to equal the product of its two outcomes. -/
def IsProductCost (c : ℝ → ℝ → ℝ) : Prop := ∀ a b, c a b = a * b
  -- @realizes c(product cost on ℝ × ℝ)
-- @node: ass:couplings-probability-measure
/-- For [a measure on pairs of real outcomes](hyp:pi), the [coupling probability
condition](goal) requires its total mass to be one. -/
def CouplingIsProbability (pi : Measure (ℝ × ℝ)) : Prop := IsProbabilityMeasure pi
  -- @realizes \pi(probability measure on ℝ × ℝ)
-- @node: ass:couplings-marginals
/-- For [a joint measure](hyp:pi) and [two prescribed](hyp:mu) [marginal laws](hyp:nu),
the [marginal condition](goal) requires [the first-coordinate law to equal the first
prescribed law](step:1) and [the second-coordinate law to equal the second prescribed
law](step:2). -/
def CouplingMarginals (pi : Measure (ℝ × ℝ)) : Prop := pi.map Prod.fst = mu ∧ pi.map Prod.snd = nu
-- @node: def:couplings
/-- A [coupling](goal) is [a joint probability measure](hyp:pi) with [the prescribed first
marginal](hyp:mu) and [the prescribed second marginal](hyp:nu). -/
abbrev IsCoupling {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (pi : Measure (A × B)) (mu : Measure A) (nu : Measure B) := Causalean.Stat.IsCoupling pi mu nu
  -- @realizes \Pi(coupling class with prescribed marginals)
/-- For [the first law](hyp:mu) and [the second law](hyp:nu), the [quantile distance
integral](goal) is the integral over the open unit interval of the absolute difference
between their lower quantiles. -/
noncomputable def quantileDistanceIntegral : ℝ := ∫ t in Ioo (0 : ℝ) 1, |quantile mu t - quantile nu t|
-- @node: ass:pin-20
/-- For [two real laws](hyp:mu,nu) and [their proposed quantile functions](hyp:Qmu,Qnu),
the [lower-quantile convention](goal) requires, at every probability strictly between zero
and one, [the first function to equal the infimum of outcomes whose cumulative probability
reaches that level](step:1) and [the second function to satisfy the same formula for the
second law](step:2). -/
def LowerQuantileReading : Prop :=
  ∀ t ∈ Ioo (0 : ℝ) 1,
    Qmu t = sInf {a : ℝ | t ≤ (mu (Iic a)).toReal} ∧
    Qnu t = sInf {b : ℝ | t ≤ (nu (Iic b)).toReal}
-- @node: ass:pin-63
/-- For [the first and second laws](hyp:mu,nu) and [their respective candidate quantiles](hyp:Qmu,Qnu),
the [alternative lower-quantile convention](goal) requires, throughout the open unit
interval, [the first quantile to be the infimum of outcomes with cumulative probability
at least the requested level](step:1) and [the second quantile to be the analogous infimum
for the second law](step:2). -/
def LowerQuantileReading' : Prop :=
  ∀ t ∈ Ioo (0 : ℝ) 1,
    Qmu t = sInf {a : ℝ | t ≤ (mu (Iic a)).toReal} ∧
    Qnu t = sInf {b : ℝ | t ≤ (nu (Iic b)).toReal}
-- @node: ass:pin-30
/-- The [lower-quantile distance convention](goal) says that, for any two real probability
laws, their quantile distance integral equals the integral over the open unit interval
of the absolute difference of their lower quantiles. -/
def W1LowerQuantileReading : Prop :=
  ∀ mu nu : Measure ℝ, IsProbabilityMeasure mu → IsProbabilityMeasure nu →
    quantileDistanceIntegral mu nu = ∫ t in Ioo (0 : ℝ) 1, |quantile mu t - quantile nu t|

-- @node: isCoupling_iff
/-- [A joint measure is a coupling of the two prescribed real laws if and only if it is
a probability measure and has those two marginals](goal). -/
lemma isCoupling_iff (pi : Measure (ℝ × ℝ)) :
    IsCoupling pi mu nu ↔ CouplingIsProbability pi ∧ CouplingMarginals mu nu pi := by
  constructor
  · intro h
    exact ⟨h.isProbabilityMeasure, h.map_fst, h.map_snd⟩
  · rintro ⟨hp, hf, hs⟩
    exact ⟨hp, hf, hs⟩
-- @node: strictQuantile_ae_lower
/-- For a real probability law, [the strict and lower quantiles agree almost everywhere
under the uniform law on the open unit interval](goal). -/
lemma strictQuantile_ae_lower (rho : Measure ℝ) [IsProbabilityMeasure rho] :
    strictQuantile rho =ᵐ[unifOI] quantile rho := by
  have h := countable_strictQuantile_ne_quantile rho
  apply (ae_restrict_iff' measurableSet_Ioo).2
  filter_upwards [h.ae_notMem volume] with t ht hmem
  exact not_ne_iff.mp (fun hne => ht ⟨hmem, hne⟩)
-- @node: quantile_versions_same_laws
/-- For a real probability law, [strict and lower quantiles applied to a uniform draw have
the same distribution, both directly and after reflecting the draw about one half](goal). -/
lemma quantile_versions_same_laws (rho : Measure ℝ) [IsProbabilityMeasure rho] :
    unifOI.map (strictQuantile rho) = unifOI.map (quantile rho) ∧
    unifOI.map (fun t => strictQuantile rho (1 - t)) =
      unifOI.map (fun t => quantile rho (1 - t)) := by
  have h := strictQuantile_ae_lower rho
  constructor
  · exact Measure.map_congr h
  · apply Measure.map_congr
    apply ae_of_ae_map (f := fun t : ℝ => 1 - t)
      (p := fun t => strictQuantile rho t = quantile rho t)
      (measurable_const.sub measurable_id).aemeasurable
    rw [map_one_sub_unifOI]
    exact h
-- @node: quantile_versions_same_integrals
/-- For two real probability laws, [replacing strict quantiles by lower quantiles leaves
their product integral unchanged, both when the quantiles use the same uniform index and
when the second uses one minus that index](goal). -/
lemma quantile_versions_same_integrals (mu nu : Measure ℝ)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] :
    (∫ t in Ioo (0 : ℝ) 1, strictQuantile mu t * strictQuantile nu t) =
      (∫ t in Ioo (0 : ℝ) 1, quantile mu t * quantile nu t) ∧
    (∫ t in Ioo (0 : ℝ) 1, strictQuantile mu t * strictQuantile nu (1 - t)) =
      (∫ t in Ioo (0 : ℝ) 1, quantile mu t * quantile nu (1 - t)) := by
  exact integral_strictQuantile_mul_eq mu nu


-- @node: def:wasserstein-distance
/-- For [the first probability law](hyp:mu1) and [the second probability law](hyp:nu1),
the [extended Wasserstein distance of order one](goal) is the nonnegative, possibly infinite
integral of their absolute lower-quantile difference over the open unit interval. -/
noncomputable def w1Quantile (mu1 nu1 : ProbabilityMeasure ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal |quantile mu1.toMeasure t - quantile nu1.toMeasure t|
  -- @realizes W_1(extended nonnegative distance on arbitrary real probability laws)
-- @node: w1Quantile_nonneg
/-- [The extended quantile Wasserstein distance between any two real probability laws
is nonnegative](goal). -/
lemma w1Quantile_nonneg (mu1 nu1 : ProbabilityMeasure ℝ) :
    0 ≤ w1Quantile mu1 nu1 := by
  exact bot_le
  -- @realizes W_1(nonnegative extended distance)
-- @node: w1Quantile_finite_moment
/-- If [the first probability law has a finite absolute first moment](hyp:hmu) and
[the second does too](hyp:hnu), [their extended quantile Wasserstein distance is finite,
and its real value equals the ordinary integral of the absolute lower-quantile
difference](goal). -/
lemma w1Quantile_finite_moment (mu1 nu1 : ProbabilityMeasure ℝ)
    (hmu : Integrable id mu1.toMeasure) (hnu : Integrable id nu1.toMeasure) :
    w1Quantile mu1 nu1 < ⊤ ∧
    (w1Quantile mu1 nu1).toReal = quantileDistanceIntegral mu1.toMeasure nu1.toMeasure := by
  have hqmu : Integrable (quantile mu1.toMeasure) unifOI := by
    have h : Integrable id (unifOI.map (quantile mu1.toMeasure)) := by
      rw [quantile_map_uniform]
      exact hmu
    exact h.comp_aemeasurable (aemeasurable_quantile_unifOI mu1.toMeasure)
  have hqnu : Integrable (quantile nu1.toMeasure) unifOI := by
    have h : Integrable id (unifOI.map (quantile nu1.toMeasure)) := by
      rw [quantile_map_uniform]
      exact hnu
    exact h.comp_aemeasurable (aemeasurable_quantile_unifOI nu1.toMeasure)
  have habs := (hqmu.sub hqnu).abs
  have heq : w1Quantile mu1 nu1 =
      ENNReal.ofReal (quantileDistanceIntegral mu1.toMeasure nu1.toMeasure) := by
    exact (ofReal_integral_eq_lintegral_ofReal habs
      (Filter.Eventually.of_forall fun t => abs_nonneg _)).symm
  refine ⟨heq.trans_lt ENNReal.ofReal_lt_top, ?_⟩
  rw [heq, ENNReal.toReal_ofReal]
  exact integral_nonneg (fun t => abs_nonneg _)
end Papers.TbsPrteOptimalTransport

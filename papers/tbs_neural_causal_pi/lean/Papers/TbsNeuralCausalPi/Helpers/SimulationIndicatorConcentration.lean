module
public import Papers.TbsNeuralCausalPi.Helpers.EmpiricalWasserstein
public import Papers.TbsNeuralCausalPi.Helpers.EmpiricalContrasts
public import Papers.TbsNeuralCausalPi.Helpers.SimulationShattering
/-! # Scalar indicator concentration for finite simulation tables

The scalar specialization of the uniform Wasserstein theorem controls means
of the finite-type and ambiguity indicators. Failure events are compared as
arbitrary sets, so the argument requires no measurable supremum over networks.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.deprecated false
open MeasureTheory
open scoped ENNReal
noncomputable section

/-- For [a Boolean indicator](hyp:B) and [an observation](hyp:x), [the indicator
vector](goal) is the one-dimensional vector equal to one when the indicator is
true at that observation and zero otherwise. -/
-- @node: simulationIndicatorVector
def simulationIndicatorVector {X : Type*} (B : X → Bool) (x : X) : L1Vec 1 :=
  WithLp.toLp 1 (fun _ => if B x then 1 else 0)

-- @node: simulationIndicatorVector_measurable
/-- If [a Boolean indicator is measurable](hyp:hB), then [its one-dimensional
zero-one vector representation is measurable](goal). -/
@[fun_prop] lemma simulationIndicatorVector_measurable {X : Type*} [MeasurableSpace X]
    {B : X → Bool} (hB : Measurable B) : Measurable (simulationIndicatorVector B) := by
  exact (measurable_of_countable
    (fun b : Bool => WithLp.toLp 1 (fun _ : Fin 1 => if b then (1 : ℝ) else 0))).comp hB

/-- For [a family of Boolean indicators](hyp:B), if [the associated scalar
zero-one functions have pseudo-dimension at most v](hyp:hv), then [the class
of their one-dimensional vector representations has coordinate pseudo-dimension
strictly below v + 1](goal). -/
-- @node: simulationIndicatorVector_pseudodim
lemma simulationIndicatorVector_pseudodim {X I : Type*} (B : I → X → Bool)
    {v : ℕ} (hv : Causalean.Stat.Concentration.HasPseudoDimAtMost
      (fun i x => if B i x then (1 : ℝ) else 0) v) :
    CoordinatePseudoDimBound (Set.range (fun i => simulationIndicatorVector (B i)))
      (v + 1 : ℝ) := by
  classical
  refine ⟨by positivity, fun j => ⟨v, by linarith, ?_⟩⟩
  intro m sample
  have heq : Causalean.Stat.Concentration.growthFamily
      (Causalean.Stat.Concentration.subgraphClassifier
        (fun f : Set.range (fun i => simulationIndicatorVector (B i)) =>
          fun x => (f.val x).ofLp j)) sample =
      Causalean.Stat.Concentration.growthFamily
        (Causalean.Stat.Concentration.subgraphClassifier
          (fun i x => if B i x then (1 : ℝ) else 0)) sample := by
    ext s
    simp only [Causalean.Stat.Concentration.mem_growthFamily_iff]
    constructor
    · rintro ⟨⟨f, i, rfl⟩, h⟩
      exact ⟨i, h⟩
    · rintro ⟨i, h⟩
      exact ⟨⟨_, Set.mem_range_self i⟩, h⟩
  rw [heq]
  exact hv m sample

-- @node: simulationIndicatorVector_bounded
/-- For [any family of Boolean indicators](hyp:B), [all one-dimensional
indicator vectors have norm at most one, uniformly over the family and its
input observations](goal). -/
lemma simulationIndicatorVector_bounded {X I : Type*} (B : I → X → Bool) :
    ClassUniformlyBounded (Set.range (fun i => simulationIndicatorVector (B i))) 1 := by
  refine ⟨by norm_num, ?_⟩
  rintro f ⟨i, rfl⟩ x
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro j
  cases h : B i x <;> simp [simulationIndicatorVector, h]

/-- For [a population probability law](hyp:mu), suppose [a one-dimensional
output map is measurable](hyp:hf) and [its scalar value is bounded in absolute
value by K at every input](hyp:hbound). For [a positive sample size](hyp:hm)
and [a sample of observations](hyp:x), [the absolute difference between the
population scalar mean and the sample average is at most the Wasserstein-1
distance between the population and empirical output laws](goal). -/
-- @node: scalar_mean_discrepancy_le_wasserstein
lemma scalar_mean_discrepancy_le_wasserstein
    {X : Type*} [MeasurableSpace X] (mu : ProbabilityMeasure X)
    {f : X → L1Vec 1} (hf : Measurable f) {K : ℝ}
    (hbound : ∀ x, |(f x).ofLp 0| ≤ K)
    {m : ℕ} (hm : 0 < m) (x : Fin m → X) :
    ENNReal.ofReal |(∫ y, (f y).ofLp 0 ∂(mu : Measure X)) -
      (m : ℝ)⁻¹ * ∑ i, (f (x i)).ofLp 0| ≤
        wasserstein1 ((mu : Measure X).map f) ((empiricalMeasure x).map f) := by
  letI := empiricalMeasure_probability hm x
  have hc : LipschitzWith 1 (fun y : L1Vec 1 => y.ofLp 0) := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    simpa using PiLp.dist_apply_le a b 0
  have hi (Q : Measure X) [IsProbabilityMeasure Q] :
      Integrable (fun y : L1Vec 1 => y.ofLp 0) (Q.map f) := by
    apply (integrable_map_measure (by fun_prop) hf.aemeasurable).mpr
    exact (integrable_const K).mono' (by fun_prop)
      (Filter.Eventually.of_forall (fun y => by simpa only [Real.norm_eq_abs, Function.comp_apply] using hbound y))
  have hpos := Toolkit.Foundations.MeasureTheory.lipschitzContrast_le_wasserstein1
    hc (hi (mu : Measure X)) (hi (empiricalMeasure x))
  have hneg := Toolkit.Foundations.MeasureTheory.lipschitzContrast_le_wasserstein1
    hc.neg (hi (mu : Measure X)).neg (hi (empiricalMeasure x)).neg
  rw [← wasserstein1_eq_toolkit] at hpos hneg
  simp only [Toolkit.Foundations.MeasureTheory.lipschitzContrast, Pi.neg_apply, integral_neg] at hpos hneg
  rw [pushforward_test_contrast_eq_average mu hf (by fun_prop) x] at hpos
  have heq := pushforward_test_contrast_eq_average mu hf
    (show Measurable (fun y : L1Vec 1 => y.ofLp 0) by fun_prop) x
  rw [show -(∫ y, y.ofLp 0 ∂((mu : Measure X).map f)) -
      -(∫ y, y.ofLp 0 ∂((empiricalMeasure x).map f)) =
      -((∫ y, y.ofLp 0 ∂((mu : Measure X).map f)) -
        (∫ y, y.ofLp 0 ∂((empiricalMeasure x).map f))) by ring, heq] at hneg
  rw [abs_eq_max_neg, ENNReal.ofReal_max]
  exact max_le hpos hneg

/-- Assuming [the Anthony–Bartlett packing bound](hyp:hpacking) and [the
Anthony–Bartlett squared-loss bound](hyp:hsquared), [there are positive universal
constants C and c such that every measurable, Borel-parametrized Boolean class
of pseudo-dimension at most v on a standard Borel population space satisfies
the following bound: for m positive independent observations and positive δ
and ε, the probability that any indicator's sample average differs from its
population mean by more than δ + ε is at most
$\exp(C((1+\delta^{-1})\log(2+\delta^{-1})+(v+1)\log(2+\epsilon^{-1}))-cm\epsilon^2)$](goal). -/
-- @node: uniform_simulation_indicator_concentration
lemma uniform_simulation_indicator_concentration
    (hpacking : AnthonyBartlettPacking) (hsquared : AnthonyBartlettSquaredLoss) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (X : Type) [MeasurableSpace X] [StandardBorelSpace X] (mu : ProbabilityMeasure X)
        (I : Type*) (B : I → X → Bool) (v : ℕ),
        Causalean.Stat.Concentration.HasPseudoDimAtMost
          (fun i x => if B i x then (1 : ℝ) else 0) v →
        (∀ i, Measurable (B i)) → BorelParametrizedClass (Set.range B) →
        ∀ m : ℕ, 0 < m → ∀ delta eps : ℝ, 0 < delta → 0 < eps →
          (Measure.pi (fun _ : Fin m => (mu : Measure _)))
            {x | ∃ i, delta + eps <
              |(∫ y, (if B i y then (1 : ℝ) else 0) ∂(mu : Measure _)) -
                (m : ℝ)⁻¹ * ∑ j, if B i (x j) then (1 : ℝ) else 0|} ≤
            ENNReal.ofReal (Real.exp
              (C * ((1 + delta⁻¹) * Real.log (2 + delta⁻¹) +
                (v + 1 : ℝ) * Real.log (2 + eps⁻¹)) - c * m * eps^2)) := by
  obtain ⟨C, c, hC, hc, htail⟩ :=
    uniform_empirical_wasserstein_measurable_input 1 1 (by norm_num) hpacking hsquared
  refine ⟨C, c, hC, hc, ?_⟩
  intro X _ _ mu I B v hv hB hparam m hm delta eps hdelta heps
  let F := Set.range (fun i => simulationIndicatorVector (B i))
  have hF : ∀ f ∈ F, Measurable f := by
    rintro f ⟨i, rfl⟩
    exact simulationIndicatorVector_measurable (hB i)
  let encode : Bool → L1Vec 1 :=
    fun b => WithLp.toLp 1 (fun _ : Fin 1 => if b then (1 : ℝ) else 0)
  have hparamF : BorelParametrizedClass F := by
    have heq : F = (fun f => encode ∘ f) '' Set.range B := by
      ext f
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨B i, Set.mem_range_self i, rfl⟩
      · rintro ⟨b, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
    rw [heq]
    exact hparam.postcomp encode (measurable_of_countable _)
  have hsource := htail X mu F (v + 1) (simulationIndicatorVector_pseudodim B hv)
    (simulationIndicatorVector_bounded B) hF hparamF m hm delta eps hdelta heps
  apply le_trans (measure_mono ?_) (by simpa using hsource)
  rintro x ⟨i, hi⟩
  apply lt_of_lt_of_le
    ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (add_pos hdelta heps).le).mpr hi)
  apply le_trans _ (le_iSup (fun f : F => wasserstein1
    ((mu : Measure _).map f.val) ((empiricalMeasure x).map f.val))
      ⟨simulationIndicatorVector (B i), Set.mem_range_self i⟩)
  exact scalar_mean_discrepancy_le_wasserstein mu
    (simulationIndicatorVector_measurable (hB i))
    (K := 1) (fun y => by cases h : B i y <;> simp [simulationIndicatorVector, h]) hm x

/-- Assuming [the Anthony–Bartlett packing bound](hyp:hpacking) and [the
Anthony–Bartlett squared-loss bound](hyp:hsquared), [there are positive universal
constants C and c such that any Boolean class contained in a measurable,
Borel-parametrized envelope of pseudo-dimension at most v on a standard Borel
population space obeys this uniform deviation bound: for m positive independent
observations and positive δ and ε, the outer probability that an indicator's
sample average differs from its population mean by more than δ + ε is at most
$\exp(C((1+\delta^{-1})\log(2+\delta^{-1})+(v+1)\log(2+\epsilon^{-1}))-cm\epsilon^2)$](goal). -/
lemma uniform_simulation_indicator_concentration_of_envelope
    (hpacking : AnthonyBartlettPacking) (hsquared : AnthonyBartlettSquaredLoss) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (X : Type) [MeasurableSpace X] [StandardBorelSpace X] (mu : ProbabilityMeasure X)
        (I : Type*) (B : I → X → Bool) (v : ℕ), BooleanClassEnvelope B v →
        ∀ m : ℕ, 0 < m → ∀ delta eps : ℝ, 0 < delta → 0 < eps →
          (Measure.pi (fun _ : Fin m => (mu : Measure _)))
            {x | ∃ i, delta + eps <
              |(∫ y, (if B i y then (1 : ℝ) else 0) ∂(mu : Measure _)) -
                (m : ℝ)⁻¹ * ∑ j, if B i (x j) then (1 : ℝ) else 0|} ≤
            ENNReal.ofReal (Real.exp
              (C * ((1 + delta⁻¹) * Real.log (2 + delta⁻¹) +
                (v + 1 : ℝ) * Real.log (2 + eps⁻¹)) - c * m * eps^2)) := by
  obtain ⟨C, c, hC, hc, htail⟩ :=
    uniform_simulation_indicator_concentration hpacking hsquared
  refine ⟨C, c, hC, hc, ?_⟩
  intro X _ _ mu I B v henv m hm delta eps hdelta heps
  obtain ⟨H, hH, hsub, hdim⟩ := henv
  have hrange : Set.range (fun f : H => f.val) = H := Subtype.range_coe
  have hsource := htail X mu H (fun f => f.val) v hdim
    (fun f => hH.measurable f.val f.property) (by simpa only [hrange] using hH) m hm delta eps hdelta heps
  apply (measure_mono ?_).trans hsource
  rintro x ⟨i, hi⟩
  exact ⟨⟨B i, hsub (Set.mem_range_self i)⟩, hi⟩

/-- For [a finite measure](hyp:mu) and [a measurable Boolean indicator](hyp:hB),
[the integral of its zero-one value equals the real-valued measure of the set
where it is true](goal). -/
-- @node: simulation_indicator_integral_eq_probability
lemma simulation_indicator_integral_eq_probability
    {X : Type*} [MeasurableSpace X] (mu : Measure X) [IsFiniteMeasure mu]
    {B : X → Bool} (hB : Measurable B) :
    (∫ y, (if B y then (1 : ℝ) else 0) ∂mu) = mu.real {y | B y = true} := by
  have hset : MeasurableSet {y | B y = true} := hB (measurableSet_singleton true)
  have heq : (fun y => if B y then (1 : ℝ) else 0) =
      ({y | B y = true} : Set X).indicator (fun _ => (1 : ℝ)) := by
    funext y
    simp only [Set.indicator, Set.mem_setOf_eq]
  rw [heq, integral_indicator hset, setIntegral_const]
  simp

/-- For [a measure on the underlying outcome space](hyp:Q), [a population
probability law](hyp:mu), and [a collection of observation maps](hyp:draws),
suppose [the joint sample map is measurable](hyp:hdraws) and [its distribution
is the product of the population law](hyp:hlaw). For [any Boolean indicator
family](hyp:B) and [deviation threshold e](hyp:e), [the outer measure of the
event that some indicator's sample average differs from its population mean
by more than e is at most the outer measure of the corresponding event under
independent sampling from the population law](goal). -/
-- @node: simulation_indicator_failure_measure_le_iid
lemma simulation_indicator_failure_measure_le_iid
    {X Omega I : Type*} [MeasurableSpace X] [MeasurableSpace Omega]
    (Q : Measure Omega) (mu : ProbabilityMeasure X) {m : ℕ}
    (draws : Fin m → Omega → X) (hdraws : Measurable (fun w j => draws j w))
    (hlaw : Q.map (fun w j => draws j w) = Measure.pi (fun _ : Fin m => (mu : Measure X)))
    (B : I → X → Bool) (e : ℝ) :
    Q {w | ∃ i, e <
      |(∫ y, (if B i y then (1 : ℝ) else 0) ∂(mu : Measure X)) -
        (m : ℝ)⁻¹ * ∑ j, if B i (draws j w) then (1 : ℝ) else 0|} ≤
      (Measure.pi (fun _ : Fin m => (mu : Measure X)))
        {x | ∃ i, e <
          |(∫ y, (if B i y then (1 : ℝ) else 0) ∂(mu : Measure X)) -
            (m : ℝ)⁻¹ * ∑ j, if B i (x j) then (1 : ℝ) else 0|} := by
  rw [← hlaw]
  exact Measure.le_map_apply hdraws.aemeasurable _

end
end Papers.TbsNeuralCausalPi

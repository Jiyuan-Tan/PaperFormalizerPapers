module
public import Papers.OaiMetricMarkovCotype.Helpers.Resolvent
public import Papers.OaiMetricMarkovCotype.Helpers.HarmonicMartingale
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-! # The martingale attached to the geometrically killed walk -/

public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace Papers.OaiMetricMarkovCotype

variable {n : ℕ} {𝓑 : Type*} [Fintype 𝓑]

-- @node: stoppedInitialLaw_isProbabilityMeasure
/-- If [the state masses are nonnegative and sum to one](hyp:hπ), then
[the initial alive-state law is a probability measure](goal). -/
lemma stoppedInitialLaw_isProbabilityMeasure (π : Fin n → ℝ) (hπ : IsProbabilityVector π) :
    IsProbabilityMeasure (stoppedInitialLaw π) := by
  constructor
  change (∑ i, ENNReal.ofReal (π i) • Measure.dirac (Sum.inl i) : Measure (StoppedState n))
    Set.univ = 1
  simp only [Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hπ.1 i), hπ.2]
  norm_num

-- @node: stoppedWalkValue_martingale
/-- If [the time parameter is strictly positive](hyp:ht),
[the initial state masses are nonnegative and sum to one](hyp:hπ), and
[the transition matrix is stochastic](hyp:hA), then
[the process taking resolvent values while alive and target values after death
is a martingale under the stopped-walk law and its natural filtration](goal). -/
lemma stoppedWalkValue_martingale (t : ℕ) (ht : GeometricParameterDomain t)
    (π : Fin n → ℝ) (hπ : IsProbabilityVector π)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsStochastic A)
    (z : Fin n → 𝓑 → ℝ) :
    Martingale (stoppedWalkValue (resolvent t ht A z) z) (stoppedWalkFiltration n)
      (stoppedWalkMeasure t ht π A hA) := by
  classical
  let := stoppedState_measurableSingletonClass n
  let := stoppedInitialLaw_isProbabilityMeasure π hπ
  let := stoppedWalkKernel_isMarkov t ht A hA
  let g : StoppedState n → 𝓑 → ℝ := Sum.elim (resolvent t ht A z) z
  have hgm : Measurable g := by fun_prop
  have hgi (ν : Measure (StoppedState n)) [IsFiniteMeasure ν] : Integrable g ν := by
    apply Integrable.of_bound hgm.aestronglyMeasurable (∑ s, ‖g s‖)
    exact ae_of_all ν fun s =>
      Finset.single_le_sum (fun s _ => norm_nonneg (g s)) (Finset.mem_univ s)
  have hgdirac (c : ℝ) (s : StoppedState n) :
      Integrable g (ENNReal.ofReal c • Measure.dirac s) :=
    (hgi (Measure.dirac s)).smul_measure ENNReal.ofReal_ne_top
  have hp : 0 ≤ geomKillProb t ht := by unfold geomKillProb; positivity
  have hq : 0 ≤ geomSurvProb t ht := (geomSurvProb_pos_lt_one t ht).1.le
  have hg (s : StoppedState n) : ∫ b, g b ∂stoppedWalkKernel t ht A s = g s := by
    cases s with
    | inl i =>
      change (∫ b, g b ∂(ENNReal.ofReal (geomKillProb t ht) • Measure.dirac (Sum.inr i) +
        ∑ j, ENNReal.ofReal (geomSurvProb t ht * A i j) • Measure.dirac (Sum.inl j))) =
          resolvent t ht A z i
      rw [integral_add_measure (hgdirac _ _)
        (integrable_finsetSum_measure.mpr (fun j _ => hgdirac _ _)),
        integral_finsetSum_measure (fun j _ => hgdirac _ _)]
      simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal hp,
        ENNReal.toReal_ofReal (mul_nonneg hq (hA.nonneg _ _)), g, Sum.elim_inl, Sum.elim_inr]
      rw [resolvent_fixed_point t ht A hA z i, Finset.smul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [smul_smul]
    | inr i =>
      change (∫ b, g b ∂Measure.dirac (Sum.inr i)) = g (Sum.inr i)
      exact integral_dirac _ _
  convert finite_kernel_harmonic_martingale (stoppedInitialLaw π)
    (stoppedWalkKernel t ht A) g hg using 1
  · funext m ω
    unfold stoppedWalkValue
    cases ω m <;> rfl
  · rfl
  · rfl

-- @node: stoppedWalkValue_mem_unitCube
/-- If [the time parameter is strictly positive](hyp:ht),
[the transition matrix is stochastic](hyp:hA), and
[every target vector has all coordinates between zero and one](hyp:hz), then
[the stopped-walk value, using resolvent vectors while alive, has all coordinates
between zero and one at every time on every path](goal). -/
lemma stoppedWalkValue_mem_unitCube (t : ℕ) (ht : GeometricParameterDomain t)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsStochastic A)
    (z : Fin n → 𝓑 → ℝ) (hz : ∀ i, z i ∈ unitCube 𝓑)
    (m : ℕ) (ω : StoppedPath n) :
    stoppedWalkValue (resolvent t ht A z) z m ω ∈ unitCube 𝓑 := by
  unfold stoppedWalkValue
  cases ω m with
  | inl i => exact resolvent_mem_unitCube t ht A hA z hz i
  | inr i => exact hz i

-- @node: stoppedWalkKernel_integral_alive
/-- If [the time parameter is strictly positive](hyp:ht) and
[the transition matrix is stochastic](hyp:hA), then
[the expected scalar payoff after one transition from an alive index equals the
killing probability times the payoff at the dead copy of that index plus the
survival probability times the transition-weighted average payoff at alive indices](goal). -/
lemma stoppedWalkKernel_integral_alive (t : ℕ) (ht : GeometricParameterDomain t)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsStochastic A)
    (f : StoppedState n → ℝ) (i : Fin n) :
    (∫ s, f s ∂stoppedWalkKernel t ht A (Sum.inl i)) =
      geomKillProb t ht * f (Sum.inr i) +
        geomSurvProb t ht * ∑ j, A i j * f (Sum.inl j) := by
  classical
  let := stoppedState_measurableSingletonClass n
  have hi (c : ℝ) (s : StoppedState n) :
      Integrable f (ENNReal.ofReal c • Measure.dirac s) :=
    (Integrable.of_finite (μ := Measure.dirac s)).smul_measure ENNReal.ofReal_ne_top
  have hp : 0 ≤ geomKillProb t ht := by unfold geomKillProb; positivity
  have hq := (geomSurvProb_pos_lt_one t ht).1.le
  change (∫ s, f s ∂(ENNReal.ofReal (geomKillProb t ht) • Measure.dirac (Sum.inr i) +
    ∑ j, ENNReal.ofReal (geomSurvProb t ht * A i j) • Measure.dirac (Sum.inl j))) = _
  rw [integral_add_measure (hi _ _)
    (integrable_finsetSum_measure.mpr (fun j _ => hi _ _)),
    integral_finsetSum_measure (fun j _ => hi _ _)]
  simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal hp,
    ENNReal.toReal_ofReal (mul_nonneg hq (hA.nonneg _ _)), smul_eq_mul]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

-- @node: stoppedInitialLaw_integral
/-- If [the state masses are nonnegative and sum to one](hyp:hπ), then
[the integral of any scalar payoff under the initial law equals the sum of its
alive-state values weighted by those masses](goal). -/
lemma stoppedInitialLaw_integral (π : Fin n → ℝ) (hπ : IsProbabilityVector π)
    (f : StoppedState n → ℝ) :
    (∫ s, f s ∂stoppedInitialLaw π) = ∑ i, π i * f (Sum.inl i) := by
  classical
  let := stoppedState_measurableSingletonClass n
  unfold stoppedInitialLaw
  rw [integral_finsetSum_measure (fun i _ =>
    (Integrable.of_finite (μ := Measure.dirac (Sum.inl i))).smul_measure
      ENNReal.ofReal_ne_top)]
  simp only [integral_smul_measure, integral_dirac,
    ENNReal.toReal_ofReal (hπ.1 _), smul_eq_mul]

-- @node: cubicMap_binary
/-- If [every coordinate of a vector is zero or one](hyp:hz), then
[cubic smoothing leaves the vector unchanged](goal). -/
lemma cubicMap_binary (z : 𝓑 → ℝ) (hz : BinaryVector z) : cubicMap z = z := by
  funext B
  rcases hz B with hB | hB <;> norm_num [cubicMap, cubicSmooth, hB]

-- @node: weightedL1Norm_sub_comm
/-- [The weighted ℓ¹ size of the difference of two vectors is unchanged when
the order of subtraction is reversed](goal). -/
lemma weightedL1Norm_sub_comm (w u v : 𝓑 → ℝ) :
    weightedL1Norm w (u - v) = weightedL1Norm w (v - u) := by
  unfold weightedL1Norm
  simp only [Pi.sub_apply, abs_sub_comm]

-- @node: stoppedWalkKernel_cubic_energy
/-- If [the time parameter is strictly positive](hyp:ht),
[the transition matrix is stochastic](hyp:hA), and
[every target vector has only zero and one coordinates](hyp:hz), then, for
[any vectors attached to alive states](hyp:h),
[the state-mass-weighted expected squared weighted ℓ¹ jump in the cubically
smoothed value after one step from an alive state equals the killing probability
times the approximation cost plus the survival probability times the smoothed energy](goal). -/
lemma stoppedWalkKernel_cubic_energy (t : ℕ) (ht : GeometricParameterDomain t)
    (π : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsStochastic A)
    (w : 𝓑 → ℝ) (z h : Fin n → 𝓑 → ℝ) (hz : ∀ i, BinaryVector (z i)) :
    (∑ i, π i * ∫ s, weightedL1Norm w
      (cubicMap (Sum.elim h z s) - cubicMap (h i)) ^ 2
        ∂stoppedWalkKernel t ht A (Sum.inl i)) =
      geomKillProb t ht * approxCost π w z h +
        geomSurvProb t ht * smoothedEnergy π A w h := by
  classical
  simp_rw [stoppedWalkKernel_integral_alive t ht A hA,
    Sum.elim_inl, Sum.elim_inr, cubicMap_binary _ (hz _)]
  simp_rw [weightedL1Norm_sub_comm w (cubicMap (h _)) (cubicMap (h _))]
  unfold approxCost smoothedEnergy
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl
  · intro i _
    ring
  · intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

-- @node: stoppedWalkMeasure_isProbabilityMeasure
/-- If [the time parameter is strictly positive](hyp:ht),
[the initial state masses are nonnegative and sum to one](hyp:hπ), and
[the transition matrix is stochastic](hyp:hA), then
[the stopped-walk path law is a probability measure](goal). -/
lemma stoppedWalkMeasure_isProbabilityMeasure (t : ℕ) (ht : GeometricParameterDomain t)
    (π : Fin n → ℝ) (hπ : IsProbabilityVector π)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsStochastic A) :
    IsProbabilityMeasure (stoppedWalkMeasure t ht π A hA) := by
  let := stoppedInitialLaw_isProbabilityMeasure π hπ
  unfold stoppedWalkMeasure
  infer_instance

-- @node: stoppedWalk_integral_zero
/-- If [the time parameter is strictly positive](hyp:ht),
[the initial state masses are nonnegative and sum to one](hyp:hπ), and
[the transition matrix is stochastic](hyp:hA), then
[the expected scalar payoff at time zero under the stopped-walk law equals
the initial-mass-weighted sum of the alive-state payoffs](goal). -/
lemma stoppedWalk_integral_zero (t : ℕ) (ht : GeometricParameterDomain t)
    (π : Fin n → ℝ) (hπ : IsProbabilityVector π)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsStochastic A)
    (f : StoppedState n → ℝ) :
    (∫ ω, f (ω 0) ∂stoppedWalkMeasure t ht π A hA) =
      ∑ i, π i * f (Sum.inl i) := by
  let := stoppedState_measurableSingletonClass n
  let := stoppedInitialLaw_isProbabilityMeasure π hπ
  let := stoppedWalkKernel_isMarkov t ht A hA
  have hcoord : Measurable (fun ω : StoppedPath n => ω 0) := measurable_pi_apply 0
  have hf : AEStronglyMeasurable f
      ((stoppedWalkMeasure t ht π A hA).map (fun ω => ω 0)) := by fun_prop
  rw [← integral_map hcoord.aemeasurable hf]
  change (∫ s, f s ∂((Toolkit.Foundations.Probability.Processes.pathLaw
    (X := fun _ => StoppedState n)
    (stoppedInitialLaw π)
    (Toolkit.Foundations.Probability.Processes.homogeneousTransition
      (stoppedWalkKernel t ht A))).map
      (Toolkit.Foundations.Probability.Processes.coordinate (fun _ => StoppedState n) 0))) = _
  rw [Toolkit.Foundations.Probability.Processes.map_coordinate_zero]
  exact stoppedInitialLaw_integral π hπ f

-- @node: stoppedWalk_survival_integral
/-- If [the time parameter is strictly positive](hyp:ht),
[the initial state masses are nonnegative and sum to one](hyp:hπ), and
[the transition matrix is stochastic](hyp:hA), then
[the expectation of the indicator that the stopped walk is alive at a given
time equals the one-step survival probability raised to that time](goal). -/
lemma stoppedWalk_survival_integral (t : ℕ) (ht : GeometricParameterDomain t)
    (π : Fin n → ℝ) (hπ : IsProbabilityVector π)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsStochastic A) (m : ℕ) :
    (∫ ω, Sum.elim (fun _ => (1 : ℝ)) (fun _ => 0) (ω m)
      ∂stoppedWalkMeasure t ht π A hA) = geomSurvProb t ht ^ m := by
  classical
  let := stoppedState_measurableSingletonClass n
  let := stoppedInitialLaw_isProbabilityMeasure π hπ
  let := stoppedWalkKernel_isMarkov t ht A hA
  let f : StoppedState n → ℝ := Sum.elim (fun _ => 1) (fun _ => 0)
  have hk (s : StoppedState n) :
      (∫ b, f b ∂stoppedWalkKernel t ht A s) = geomSurvProb t ht * f s := by
    cases s with
    | inl i => simp [stoppedWalkKernel_integral_alive t ht A hA, f, hA.row_sums i]
    | inr i =>
      change (∫ b, f b ∂Measure.dirac (Sum.inr i)) = _
      simp [f]
  induction m with
  | zero => simpa [f, hπ.2] using stoppedWalk_integral_zero t ht π hπ A hA f
  | succ m ih =>
    change (∫ ω, f (ω (m + 1)) ∂stoppedWalkMeasure t ht π A hA) = _
    have hstep := finite_kernel_integral_transition (stoppedInitialLaw π)
      (stoppedWalkKernel t ht A) (fun _ b => f b) m
    change (∫ ω, f (ω (m + 1)) ∂stoppedWalkMeasure t ht π A hA) = _ at hstep
    rw [hstep]
    simp_rw [hk]
    rw [integral_const_mul]
    change geomSurvProb t ht *
      (∫ ω, Sum.elim (fun _ => (1 : ℝ)) (fun _ => 0) (ω m)
        ∂stoppedWalkMeasure t ht π A hA) = _
    rw [ih, pow_succ, mul_comm]

-- @node: stoppedWalk_survival_measure
/-- If [the time parameter is strictly positive](hyp:ht),
[the initial state masses are nonnegative and sum to one](hyp:hπ), and
[the transition matrix is stochastic](hyp:hA), then
[the probability that the stopped walk is alive at a given time equals the
one-step survival probability raised to that time](goal). -/
lemma stoppedWalk_survival_measure (t : ℕ) (ht : GeometricParameterDomain t)
    (π : Fin n → ℝ) (hπ : IsProbabilityVector π)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsStochastic A) (m : ℕ) :
    stoppedWalkMeasure t ht π A hA {ω | (ω m).isLeft} =
      ENNReal.ofReal (geomSurvProb t ht ^ m) := by
  let := stoppedState_measurableSingletonClass n
  let := stoppedWalkMeasure_isProbabilityMeasure t ht π hπ A hA
  have hs : MeasurableSet {ω : StoppedPath n | (ω m).isLeft} :=
    (measurableSet_singleton true).preimage (by fun_prop)
  have heq : (stoppedWalkMeasure t ht π A hA).real {ω | (ω m).isLeft} =
      geomSurvProb t ht ^ m := by
    rw [← integral_indicator_one hs]
    convert stoppedWalk_survival_integral t ht π hπ A hA m using 1
    apply integral_congr_ae
    exact ae_of_all _ fun ω => by cases hω : ω m <;> simp [Set.indicator, hω]
  rw [← heq, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]

-- @node: stoppedWalk_eventually_dead
/-- If [the time parameter is strictly positive](hyp:ht),
[the initial state masses are nonnegative and sum to one](hyp:hπ), and
[the transition matrix is stochastic](hyp:hA), then
[almost every stopped-walk path is dead at all sufficiently large times](goal). -/
lemma stoppedWalk_eventually_dead (t : ℕ) (ht : GeometricParameterDomain t)
    (π : Fin n → ℝ) (hπ : IsProbabilityVector π)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsStochastic A) :
    ∀ᵐ ω ∂stoppedWalkMeasure t ht π A hA,
      ∀ᶠ m in Filter.atTop, ¬ (ω m).isLeft := by
  apply ae_eventually_notMem (s := fun m => {ω : StoppedPath n | (ω m).isLeft})
  simp_rw [stoppedWalk_survival_measure t ht π hπ A hA]
  have hq := geomSurvProb_pos_lt_one t ht
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => pow_nonneg hq.1.le m)
    (hasSum_geometric_of_lt_one hq.1.le hq.2).summable]
  exact ENNReal.ofReal_ne_top

-- @node: stoppedWalk_dead_absorbing
/-- If [the time parameter is strictly positive](hyp:ht),
[the initial state masses are nonnegative and sum to one](hyp:hπ), and
[the transition matrix is stochastic](hyp:hA), then
[almost every stopped-walk path has the following property at every time and index:
if its current state is the dead copy of that index, its next state is the same dead state](goal). -/
lemma stoppedWalk_dead_absorbing (t : ℕ) (ht : GeometricParameterDomain t)
    (π : Fin n → ℝ) (hπ : IsProbabilityVector π)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsStochastic A) :
    ∀ᵐ ω ∂stoppedWalkMeasure t ht π A hA,
      ∀ m i, ω m = Sum.inr i → ω (m + 1) = Sum.inr i := by
  classical
  let := stoppedState_measurableSingletonClass n
  let := stoppedInitialLaw_isProbabilityMeasure π hπ
  let := stoppedWalkKernel_isMarkov t ht A hA
  let := stoppedWalkMeasure_isProbabilityMeasure t ht π hπ A hA
  apply ae_all_iff.mpr
  intro m
  apply ae_all_iff.mpr
  intro i
  let F : StoppedState n → StoppedState n → ℝ :=
    fun a b => if a = Sum.inr i ∧ b ≠ Sum.inr i then 1 else 0
  have hk (a : StoppedState n) : (∫ b, F a b ∂stoppedWalkKernel t ht A a) = 0 := by
    cases a with
    | inl j => simp [F]
    | inr j =>
      change (∫ b, F (Sum.inr j) b ∂Measure.dirac (Sum.inr j)) = 0
      simp [F]
  have hstep := finite_kernel_integral_transition (stoppedInitialLaw π)
    (stoppedWalkKernel t ht A) F m
  have hzero : (∫ ω, F (ω m) (ω (m + 1)) ∂stoppedWalkMeasure t ht π A hA) = 0 := by
    change (∫ ω, F (ω m) (ω (m + 1)) ∂stoppedWalkMeasure t ht π A hA) = _ at hstep
    rw [hstep]
    simp_rw [hk, integral_zero]
  have hmeas : Measurable (Function.uncurry F) := by fun_prop
  have hi : Integrable (fun ω : StoppedPath n => F (ω m) (ω (m + 1)))
      (stoppedWalkMeasure t ht π A hA) := by
    have hpair : Measurable (fun ω : StoppedPath n => (ω m, ω (m + 1))) :=
      (measurable_pi_apply m).prodMk (measurable_pi_apply (m + 1))
    apply Integrable.of_bound (hmeas.comp hpair).aestronglyMeasurable 1
    exact ae_of_all _ fun ω => by dsimp [F]; split <;> norm_num
  have hn : 0 ≤ (fun ω : StoppedPath n => F (ω m) (ω (m + 1))) := by
    intro ω
    dsimp [F]
    split <;> norm_num
  have hz := (integral_eq_zero_iff_of_nonneg hn hi).mp hzero
  filter_upwards [hz] with ω hω hdead
  by_contra hnext
  have hbad : F (ω m) (ω (m + 1)) = 1 := if_pos ⟨hdead, hnext⟩
  rw [hbad] at hω
  norm_num at hω

-- @node: stoppedWalk_eventually_constant_dead
/-- If [the time parameter is strictly positive](hyp:ht),
[the initial state masses are nonnegative and sum to one](hyp:hπ), and
[the transition matrix is stochastic](hyp:hA), then
[almost every stopped-walk path eventually remains at the dead copy of a single index](goal). -/
lemma stoppedWalk_eventually_constant_dead (t : ℕ) (ht : GeometricParameterDomain t)
    (π : Fin n → ℝ) (hπ : IsProbabilityVector π)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsStochastic A) :
    ∀ᵐ ω ∂stoppedWalkMeasure t ht π A hA,
      ∃ i : Fin n, ∀ᶠ m in Filter.atTop, ω m = Sum.inr i := by
  filter_upwards [stoppedWalk_eventually_dead t ht π hπ A hA,
    stoppedWalk_dead_absorbing t ht π hπ A hA] with ω hdead habs
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hdead
  have hn := hN N le_rfl
  obtain ⟨i, hi⟩ : ∃ i : Fin n, ω N = Sum.inr i := by
    cases hs : ω N with
    | inl j => simp [hs] at hn
    | inr i => exact ⟨i, rfl⟩
  refine ⟨i, Filter.eventually_atTop.mpr ⟨N, ?_⟩⟩
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => exact hi
  | succ m hm ih => exact habs m i ih

-- @node: stoppedWalkValue_tendsto_terminal
/-- If [the time parameter is strictly positive](hyp:ht),
[the initial state masses are nonnegative and sum to one](hyp:hπ), and
[the transition matrix is stochastic](hyp:hA), then, for
[any vectors attached to alive states](hyp:h) and any vectors attached to dead states,
[almost every stopped-walk
value sequence converges to the dead-state vector at some index](goal). -/
lemma stoppedWalkValue_tendsto_terminal (t : ℕ) (ht : GeometricParameterDomain t)
    (π : Fin n → ℝ) (hπ : IsProbabilityVector π)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsStochastic A)
    (h z : Fin n → 𝓑 → ℝ) :
    ∀ᵐ ω ∂stoppedWalkMeasure t ht π A hA,
      ∃ i : Fin n, Filter.Tendsto (fun m => stoppedWalkValue h z m ω)
        Filter.atTop (nhds (z i)) := by
  filter_upwards [stoppedWalk_eventually_constant_dead t ht π hπ A hA] with ω hω
  obtain ⟨i, hi⟩ := hω
  refine ⟨i, tendsto_const_nhds.congr' ?_⟩
  filter_upwards [hi] with m hm
  simp [stoppedWalkValue, hm]

end Papers.OaiMetricMarkovCotype

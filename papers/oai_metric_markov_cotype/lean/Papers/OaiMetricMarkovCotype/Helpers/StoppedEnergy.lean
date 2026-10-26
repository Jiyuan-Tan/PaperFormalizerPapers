module
public import Papers.OaiMetricMarkovCotype.Helpers.TerminalMartingale
public import Papers.OaiMetricMarkovCotype.Helpers.HilbertMarkov

/-! # Stationary occupation and total cubic energy of the killed walk -/

public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace Papers.OaiMetricMarkovCotype

variable {n : ℕ} {𝓑 : Type*} [Fintype 𝓑]

/-- For [a strictly positive integer time parameter](hyp:ht), [probability weights on the
states](hyp:hπ), and [a stochastic transition matrix](hyp:hA) [satisfying detailed balance](hyp:hrev),
[the expected value of a state function set to zero after absorption equals its initial
weighted average times the survival probability raised to the observation time](goal). -/
-- @node: stoppedWalk_alive_integral
lemma stoppedWalk_alive_integral (t : ℕ) (ht : GeometricParameterDomain t)
    (π : Fin n → ℝ) (hπ : IsProbabilityVector π)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsStochastic A)
    (hrev : IsReversible A π) (m : ℕ) (f : Fin n → ℝ) :
    (∫ ω, Sum.elim f (fun _ => 0) (ω m) ∂stoppedWalkMeasure t ht π A hA) =
      geomSurvProb t ht ^ m * ∑ i, π i * f i := by
  classical
  let := stoppedState_measurableSingletonClass n
  let := stoppedInitialLaw_isProbabilityMeasure π hπ
  let := stoppedWalkKernel_isMarkov t ht A hA
  induction m generalizing f with
  | zero => simpa using stoppedWalk_integral_zero t ht π hπ A hA (Sum.elim f (fun _ => 0))
  | succ m ih =>
    let g : Fin n → ℝ := fun i => geomSurvProb t ht * ∑ j, A i j * f j
    have hk (a : StoppedState n) :
        (∫ b, Sum.elim f (fun _ => 0) b ∂stoppedWalkKernel t ht A a) =
          Sum.elim g (fun _ => 0) a := by
      cases a with
      | inl i => simp [stoppedWalkKernel_integral_alive t ht A hA, g]
      | inr i =>
        change (∫ b, Sum.elim f (fun _ => 0) b ∂Measure.dirac (Sum.inr i)) = 0
        simp
    have hstep := finite_kernel_integral_transition (stoppedInitialLaw π)
      (stoppedWalkKernel t ht A) (fun _ b => Sum.elim f (fun _ => 0) b) m
    change (∫ ω, Sum.elim f (fun _ => 0) (ω (m + 1))
      ∂stoppedWalkMeasure t ht π A hA) = _ at hstep
    rw [hstep]
    simp_rw [hk]
    change (∫ ω, Sum.elim g (fun _ => 0) (ω m)
      ∂stoppedWalkMeasure t ht π A hA) = _
    rw [ih]
    have hg : (∑ i, π i * g i) = geomSurvProb t ht * ∑ j, π j * f j := by
      simp only [g, Finset.mul_sum]
      calc
        (∑ i, ∑ j, π i * (geomSurvProb t ht * (A i j * f j))) =
            ∑ j, ∑ i, geomSurvProb t ht * ((π i * A i j) * f j) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = _ := by
          simp only [← Finset.mul_sum, ← Finset.sum_mul,
            reversible_weighted_columns π A hA hrev]
    rw [hg, pow_succ]
    ring

/-- For [a strictly positive integer time parameter](hyp:ht), [probability state weights](hyp:hπ),
and [a stochastic matrix](hyp:hA) [satisfying detailed balance](hyp:hrev), suppose
[a transition reward is zero for a self-transition at every absorbing state](hyp:hF).
Then [its expected reward at each time equals the survival probability raised to that time
times the initial weighted average of the one-step reward from live states](goal). -/
-- @node: stoppedWalk_transition_integral
lemma stoppedWalk_transition_integral (t : ℕ) (ht : GeometricParameterDomain t)
    (π : Fin n → ℝ) (hπ : IsProbabilityVector π)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsStochastic A)
    (hrev : IsReversible A π) (F : StoppedState n → StoppedState n → ℝ)
    (hF : ∀ i, F (Sum.inr i) (Sum.inr i) = 0) (m : ℕ) :
    (∫ ω, F (ω m) (ω (m + 1)) ∂stoppedWalkMeasure t ht π A hA) =
      geomSurvProb t ht ^ m * ∑ i, π i *
        ∫ s, F (Sum.inl i) s ∂stoppedWalkKernel t ht A (Sum.inl i) := by
  let := stoppedState_measurableSingletonClass n
  let := stoppedInitialLaw_isProbabilityMeasure π hπ
  let := stoppedWalkKernel_isMarkov t ht A hA
  have hk (a : StoppedState n) :
      (∫ b, F a b ∂stoppedWalkKernel t ht A a) =
        Sum.elim (fun i => ∫ b, F (Sum.inl i) b
          ∂stoppedWalkKernel t ht A (Sum.inl i)) (fun _ => 0) a := by
    cases a with
    | inl i => rfl
    | inr i =>
      change (∫ b, F (Sum.inr i) b ∂Measure.dirac (Sum.inr i)) = 0
      simpa using hF i
  have hstep := finite_kernel_integral_transition (stoppedInitialLaw π)
    (stoppedWalkKernel t ht A) F m
  change (∫ ω, F (ω m) (ω (m + 1)) ∂stoppedWalkMeasure t ht π A hA) = _ at hstep
  rw [hstep]
  trans ∫ ω, Sum.elim (fun i => ∫ b, F (Sum.inl i) b
    ∂stoppedWalkKernel t ht A (Sum.inl i)) (fun _ => 0) (ω m)
      ∂stoppedWalkMeasure t ht π A hA
  · exact integral_congr_ae (ae_of_all _ fun ω => hk (ω m))
  exact stoppedWalk_alive_integral t ht π hπ A hA hrev m _

/-- For [a strictly positive integer time parameter](hyp:ht), [probability state weights](hyp:hπ),
and [a stochastic matrix](hyp:hA) [satisfying detailed balance](hyp:hrev), take
[live-state vector values](hyp:h) and [binary terminal vectors](hyp:hz).
Then [the expected squared weighted L1 size of a cubic-transformed jump equals the survival
probability raised to its time times the sum of the killing-probability-weighted approximation
cost and the survival-probability-weighted smoothed energy](goal). -/
-- @node: stoppedWalk_cubic_jump_integral
lemma stoppedWalk_cubic_jump_integral (t : ℕ) (ht : GeometricParameterDomain t)
    (π : Fin n → ℝ) (hπ : IsProbabilityVector π)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsStochastic A)
    (hrev : IsReversible A π) (w : 𝓑 → ℝ) (z h : Fin n → 𝓑 → ℝ)
    (hz : ∀ i, BinaryVector (z i)) (m : ℕ) :
    (∫ ω, weightedL1Norm w
      (cubicMap (stoppedWalkValue h z (m + 1) ω) -
        cubicMap (stoppedWalkValue h z m ω)) ^ 2 ∂stoppedWalkMeasure t ht π A hA) =
      geomSurvProb t ht ^ m * (geomKillProb t ht * approxCost π w z h +
        geomSurvProb t ht * smoothedEnergy π A w h) := by
  let F : StoppedState n → StoppedState n → ℝ := fun a b =>
    weightedL1Norm w (cubicMap (Sum.elim h z b) - cubicMap (Sum.elim h z a)) ^ 2
  have hF (i : Fin n) : F (Sum.inr i) (Sum.inr i) = 0 := by
    simp [F, weightedL1Norm]
  have heq : (fun ω => weightedL1Norm w
      (cubicMap (stoppedWalkValue h z (m + 1) ω) -
        cubicMap (stoppedWalkValue h z m ω)) ^ 2) =
      (fun ω : StoppedPath n => F (ω m) (ω (m + 1))) := by
    funext ω
    unfold F stoppedWalkValue
    cases ω m <;> cases ω (m + 1) <;> rfl
  rw [heq, stoppedWalk_transition_integral t ht π hπ A hA hrev F hF m]
  congr 1
  exact stoppedWalkKernel_cubic_energy t ht π A hA w z h hz

-- @node: integrable_stoppedWalk_pair_score
/-- For [a strictly positive integer time parameter](hyp:ht), [probability state weights](hyp:hπ),
and [a stochastic transition matrix](hyp:hA), [any real score of two consecutive stopped-walk
states is integrable at each fixed time](goal). -/
lemma integrable_stoppedWalk_pair_score (t : ℕ) (ht : GeometricParameterDomain t)
    (π : Fin n → ℝ) (hπ : IsProbabilityVector π)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsStochastic A)
    (F : StoppedState n → StoppedState n → ℝ) (m : ℕ) :
    Integrable (fun ω : StoppedPath n => F (ω m) (ω (m + 1)))
      (stoppedWalkMeasure t ht π A hA) := by
  classical
  let := stoppedState_measurableSingletonClass n
  let := stoppedWalkMeasure_isProbabilityMeasure t ht π hπ A hA
  have hm : Measurable (fun ω : StoppedPath n => F (ω m) (ω (m + 1))) := by fun_prop
  apply Integrable.of_bound hm.aestronglyMeasurable (∑ a, ∑ b, ‖F a b‖)
  exact ae_of_all _ fun ω =>
    (Finset.single_le_sum (fun b _ => norm_nonneg (F (ω m) b))
      (Finset.mem_univ (ω (m + 1)))).trans
      (Finset.single_le_sum (fun a _ => Finset.sum_nonneg fun b _ => norm_nonneg (F a b))
        (Finset.mem_univ (ω m)))

/-- For [a strictly positive integer time parameter](hyp:ht), [probability state weights](hyp:hπ),
and [a stochastic matrix](hyp:hA) [satisfying detailed balance](hyp:hrev), suppose a reward
[vanishes on absorbing self-transitions](hyp:hF) and [is nonnegative for every pair of states](hyp:hF0).
Then [the expected total reward along the stopped path equals the initial weighted average
of the one-step reward from live states divided by the killing probability, viewed as an
extended nonnegative real number](goal). -/
-- @node: stoppedWalk_total_reward
lemma stoppedWalk_total_reward (t : ℕ) (ht : GeometricParameterDomain t)
    (π : Fin n → ℝ) (hπ : IsProbabilityVector π)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsStochastic A)
    (hrev : IsReversible A π) (F : StoppedState n → StoppedState n → ℝ)
    (hF : ∀ i, F (Sum.inr i) (Sum.inr i) = 0) (hF0 : ∀ a b, 0 ≤ F a b) :
    (∫⁻ ω, ∑' m : ℕ, ENNReal.ofReal (F (ω m) (ω (m + 1)))
      ∂stoppedWalkMeasure t ht π A hA) =
      ENNReal.ofReal ((∑ i, π i * ∫ s, F (Sum.inl i) s
        ∂stoppedWalkKernel t ht A (Sum.inl i)) / geomKillProb t ht) := by
  let := stoppedState_measurableSingletonClass n
  let C := ∑ i, π i * ∫ s, F (Sum.inl i) s
    ∂stoppedWalkKernel t ht A (Sum.inl i)
  have hq := geomSurvProb_pos_lt_one t ht
  have hC : 0 ≤ C := Finset.sum_nonneg fun i _ =>
    mul_nonneg (hπ.1 i) (integral_nonneg (hF0 (Sum.inl i)))
  have hs : HasSum (fun m : ℕ => geomSurvProb t ht ^ m * C)
      (C / geomKillProb t ht) := by
    have h := (hasSum_geometric_of_lt_one hq.1.le hq.2).mul_right C
    simpa [geomSurvProb, div_eq_mul_inv, mul_comm] using h
  rw [lintegral_tsum (fun m => by fun_prop)]
  have he (m : ℕ) :
      (∫⁻ ω, ENNReal.ofReal (F (ω m) (ω (m + 1)))
        ∂stoppedWalkMeasure t ht π A hA) =
      ENNReal.ofReal (geomSurvProb t ht ^ m * C) := by
    rw [← ofReal_integral_eq_lintegral_ofReal
      (integrable_stoppedWalk_pair_score t ht π hπ A hA F m)
      (ae_of_all _ fun ω => hF0 (ω m) (ω (m + 1))),
      stoppedWalk_transition_integral t ht π hπ A hA hrev F hF m]
  simp_rw [he]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => mul_nonneg (pow_nonneg hq.1.le m) hC)
    hs.summable, hs.tsum_eq]

/-- For [a strictly positive integer time parameter](hyp:ht), [probability state weights](hyp:hπ),
and [a stochastic matrix](hyp:hA) [satisfying detailed balance](hyp:hrev), take
[live-state vector values](hyp:h) and [binary terminal vectors](hyp:hz).
Then [the expected total squared weighted L1 size of the cubic-transformed jumps equals
the approximation cost plus the time parameter times the smoothed energy, viewed as an
extended nonnegative real number](goal). -/
-- @node: stoppedWalk_total_cubic_energy
lemma stoppedWalk_total_cubic_energy (t : ℕ) (ht : GeometricParameterDomain t)
    (π : Fin n → ℝ) (hπ : IsProbabilityVector π)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsStochastic A)
    (hrev : IsReversible A π) (w : 𝓑 → ℝ) (z h : Fin n → 𝓑 → ℝ)
    (hz : ∀ i, BinaryVector (z i)) :
    (∫⁻ ω, ∑' m : ℕ, ENNReal.ofReal (weightedL1Norm w
      (cubicMap (stoppedWalkValue h z (m + 1) ω) -
        cubicMap (stoppedWalkValue h z m ω)) ^ 2)
        ∂stoppedWalkMeasure t ht π A hA) =
      ENNReal.ofReal (approxCost π w z h + (t : ℝ) * smoothedEnergy π A w h) := by
  let F : StoppedState n → StoppedState n → ℝ := fun a b =>
    weightedL1Norm w (cubicMap (Sum.elim h z b) - cubicMap (Sum.elim h z a)) ^ 2
  have heq : (fun ω => ∑' m : ℕ, ENNReal.ofReal (weightedL1Norm w
      (cubicMap (stoppedWalkValue h z (m + 1) ω) -
        cubicMap (stoppedWalkValue h z m ω)) ^ 2)) =
      (fun ω : StoppedPath n => ∑' m : ℕ, ENNReal.ofReal (F (ω m) (ω (m + 1)))) := by
    funext ω
    congr 1
    funext m
    unfold F stoppedWalkValue
    cases ω m <;> cases ω (m + 1) <;> rfl
  have hF (i : Fin n) : F (Sum.inr i) (Sum.inr i) = 0 := by
    simp [F, weightedL1Norm]
  rw [heq, stoppedWalk_total_reward t ht π hπ A hA hrev F hF (fun _ _ => sq_nonneg _)]
  have hc := stoppedWalkKernel_cubic_energy t ht π A hA w z h hz
  change (∑ i, π i * ∫ s, F (Sum.inl i) s
    ∂stoppedWalkKernel t ht A (Sum.inl i)) = _ at hc
  rw [hc]
  congr 1
  have hp : geomKillProb t ht ≠ 0 := by unfold geomKillProb; positivity
  apply (div_eq_iff hp).mpr
  unfold geomSurvProb geomKillProb
  field_simp
  ring

/-- For [a strictly positive integer time parameter](hyp:ht), [probability state weights](hyp:hπ),
and [a stochastic matrix](hyp:hA) [satisfying detailed balance](hyp:hrev), assume
[strictly positive coordinate weights](hyp:hw), [a nonempty finite coordinate set](hyp:hfinite),
and [binary input vectors](hyp:hz). Then [the approximation cost of the resolvent plus the
time parameter times its smoothed energy is at most 108 times the expected quartic potential
between the initial input vector and the stopped walk's terminal value](goal). -/
-- @node: stoppedWalk_approxCost_add_energy_le
lemma stoppedWalk_approxCost_add_energy_le (t : ℕ) (ht : GeometricParameterDomain t)
    (π : Fin n → ℝ) (hπ : IsProbabilityVector π)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsStochastic A)
    (hrev : IsReversible A π) (w : 𝓑 → ℝ) (hw : PositiveWeights w)
    (hfinite : FiniteCutIndex 𝓑) (z : Fin n → 𝓑 → ℝ)
    (hz : ∀ i, BinaryVector (z i)) :
    approxCost π w z (resolvent t ht A z) +
        (t : ℝ) * smoothedEnergy π A w (resolvent t ht A z) ≤
      108 * ∫ ω, quarticPotential w (stoppedWalkValue z z 0 ω)
        (stoppedWalkTerminal (resolvent t ht A z) z ω)
          ∂stoppedWalkMeasure t ht π A hA := by
  have he := stoppedWalk_cubic_energy_bound t ht π hπ A hA w hw hfinite z hz
  rw [stoppedWalk_total_cubic_energy t ht π hπ A hA hrev w z (resolvent t ht A z) hz] at he
  exact (ENNReal.ofReal_le_ofReal_iff (by
    apply mul_nonneg (by norm_num)
    exact integral_nonneg fun ω => sq_nonneg _)).mp he

end Papers.OaiMetricMarkovCotype

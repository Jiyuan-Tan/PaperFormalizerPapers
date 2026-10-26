module
public import Papers.OaiMetricMarkovCotype.Helpers.CutAssembly

/-! # Joint initial and terminal laws of the killed walk -/

public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology
namespace Papers.OaiMetricMarkovCotype

/-- [For a finite-state Markov chain, the expected payoff depending on the initial
state and the states at times m and m + 1 equals the expectation obtained by
first averaging its last argument under the transition law from the state at
time m](goal). -/
-- @node: finite_kernel_integral_initial_transition
lemma finite_kernel_integral_initial_transition
    {α : Type*} [Fintype α] [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (μ₀ : Measure α) [IsProbabilityMeasure μ₀]
    (K : Kernel α α) [IsMarkovKernel K] (F : α → α → α → ℝ) (m : ℕ) :
    (∫ ω, F (ω 0) (ω m) (ω (m + 1))
      ∂Toolkit.Foundations.Probability.Processes.pathLaw μ₀
        (Toolkit.Foundations.Probability.Processes.homogeneousTransition K)) =
    ∫ ω, (∫ s, F (ω 0) (ω m) s ∂K (ω m))
      ∂Toolkit.Foundations.Probability.Processes.pathLaw μ₀
        (Toolkit.Foundations.Probability.Processes.homogeneousTransition K) := by
  classical
  let κ := Toolkit.Foundations.Probability.Processes.homogeneousTransition K
  let μ := Toolkit.Foundations.Probability.Processes.pathLaw μ₀ κ
  let 𝓕 := Toolkit.Foundations.Probability.Processes.naturalFiltration (fun _ => α)
  let G : Toolkit.Foundations.Probability.Processes.History (fun _ => α) m × α → ℝ :=
    fun p => F (p.1 ⟨0, Finset.mem_Iic.mpr (Nat.zero_le m)⟩)
      (p.1 ⟨m, Finset.mem_Iic.mpr le_rfl⟩) p.2
  have hF : Measurable (fun p : α × α × α => F p.1 p.2.1 p.2.2) := by fun_prop
  have hG : Measurable G := by
    have hprev : Measurable (fun p :
        Toolkit.Foundations.Probability.Processes.History (fun _ => α) m × α =>
          p.1 ⟨m, Finset.mem_Iic.mpr le_rfl⟩) :=
      (measurable_pi_apply _).comp measurable_fst
    have hzero : Measurable (fun p :
        Toolkit.Foundations.Probability.Processes.History (fun _ => α) m × α =>
          p.1 ⟨0, Finset.mem_Iic.mpr (Nat.zero_le m)⟩) :=
      (measurable_pi_apply _).comp measurable_fst
    exact hF.comp (hzero.prodMk (hprev.prodMk measurable_snd))
  have hb (a b c : α) : ‖F a b c‖ ≤ ∑ i : α, ∑ j : α, ∑ k : α, ‖F i j k‖ := by
    exact (Finset.single_le_sum (fun k _ => norm_nonneg (F a b k))
      (Finset.mem_univ c)).trans ((Finset.single_le_sum
        (fun j _ => Finset.sum_nonneg fun k _ => norm_nonneg (F a j k))
        (Finset.mem_univ b)).trans (Finset.single_le_sum
          (fun i _ => Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ =>
            norm_nonneg (F i j k)) (Finset.mem_univ a)))
  have hi : Integrable G ((μ.map
      (Toolkit.Foundations.Probability.Processes.history (fun _ => α) m)).compProd (κ m)) := by
    apply Integrable.of_bound hG.aestronglyMeasurable (∑ i : α, ∑ j : α, ∑ k : α, ‖F i j k‖)
    exact ae_of_all _ fun p => hb _ _ _
  have hc := Toolkit.Foundations.Probability.Processes.condExp_history_next
    (X := fun _ => α) (E := ℝ) μ₀ κ m G hi
  change (∫ ω, F (ω 0) (ω m) (ω (m + 1)) ∂μ) = _
  rw [← integral_condExp (𝓕.le m)]
  exact integral_congr_ae hc

/-- For [a positive integer time parameter](hyp:ht), [an initial probability
vector](hyp:hπ), and [a stochastic transition matrix](hyp:hA), [the expected score
of the starting index and the index at time m, counted as zero if the walk has
died, equals the m-step survival probability times the sum of the scores
weighted by the initial probabilities and the m-step transition probabilities](goal). -/
-- @node: stoppedWalk_initial_alive_integral
lemma stoppedWalk_initial_alive_integral {n : ℕ} (t : ℕ)
    (ht : GeometricParameterDomain t) (π : Fin n → ℝ) (hπ : IsProbabilityVector π)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsStochastic A)
    (m : ℕ) (f : Fin n → Fin n → ℝ) :
    (∫ ω, Sum.elim (f (Sum.elim id id (ω 0))) (fun _ => 0) (ω m)
      ∂stoppedWalkMeasure t ht π A hA) =
      geomSurvProb t ht ^ m * ∑ i, ∑ j, π i * (A ^ m) i j * f i j := by
  classical
  let := stoppedState_measurableSingletonClass n
  let := stoppedInitialLaw_isProbabilityMeasure π hπ
  let := stoppedWalkKernel_isMarkov t ht A hA
  induction m generalizing f with
  | zero =>
    simpa [Matrix.one_apply] using
      stoppedWalk_integral_zero t ht π hπ A hA
        (fun a => Sum.elim (f (Sum.elim id id a)) (fun _ => 0) a)
  | succ m ih =>
    let g : Fin n → Fin n → ℝ := fun i j =>
      geomSurvProb t ht * ∑ k, A j k * f i k
    have hk (a b : StoppedState n) :
        (∫ c, Sum.elim (f (Sum.elim id id a)) (fun _ => 0) c
          ∂stoppedWalkKernel t ht A b) =
        Sum.elim (g (Sum.elim id id a)) (fun _ => 0) b := by
      cases b with
      | inl j => simp [stoppedWalkKernel_integral_alive t ht A hA, g]
      | inr j =>
        change (∫ c, Sum.elim (f (Sum.elim id id a)) (fun _ => 0) c
          ∂Measure.dirac (Sum.inr j)) = 0
        simp
    have hstep := finite_kernel_integral_initial_transition (stoppedInitialLaw π)
      (stoppedWalkKernel t ht A)
      (fun a _ c => Sum.elim (f (Sum.elim id id a)) (fun _ => 0) c) m
    change (∫ ω, Sum.elim (f (Sum.elim id id (ω 0))) (fun _ => 0) (ω (m + 1))
      ∂stoppedWalkMeasure t ht π A hA) = _ at hstep
    rw [hstep]
    simp_rw [hk]
    change (∫ ω, Sum.elim (g (Sum.elim id id (ω 0))) (fun _ => 0) (ω m)
      ∂stoppedWalkMeasure t ht π A hA) = _
    rw [ih]
    simp only [g, pow_succ, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring

/-- For [a positive integer time parameter](hyp:ht), [an initial probability
vector](hyp:hπ), and [a stochastic transition matrix](hyp:hA), [every real score
of the killed walk's states at two fixed times is integrable under its path
law](goal). -/
-- @node: integrable_stoppedWalk_two_time_score
lemma integrable_stoppedWalk_two_time_score {n : ℕ} (t : ℕ)
    (ht : GeometricParameterDomain t) (π : Fin n → ℝ) (hπ : IsProbabilityVector π)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsStochastic A)
    (F : StoppedState n → StoppedState n → ℝ) (r s : ℕ) :
    Integrable (fun ω : StoppedPath n => F (ω r) (ω s))
      (stoppedWalkMeasure t ht π A hA) := by
  classical
  let := stoppedState_measurableSingletonClass n
  let := stoppedWalkMeasure_isProbabilityMeasure t ht π hπ A hA
  have hm : Measurable (fun ω : StoppedPath n => F (ω r) (ω s)) := by fun_prop
  apply Integrable.of_bound hm.aestronglyMeasurable (∑ a, ∑ b, ‖F a b‖)
  exact ae_of_all _ fun ω =>
    (Finset.single_le_sum (fun b _ => norm_nonneg (F (ω r) b))
      (Finset.mem_univ (ω s))).trans
      (Finset.single_le_sum (fun a _ => Finset.sum_nonneg fun b _ => norm_nonneg (F a b))
        (Finset.mem_univ (ω r)))

/-- For [a positive integer time parameter](hyp:ht), [an initial probability
vector](hyp:hπ), and [a stochastic transition matrix](hyp:hA), [the expected score
of the initial index and the dead endpoint at time m, counted as zero while
the walk is alive, equals the sum over times s before m of the initial and
s-step transition weighted scores multiplied by the probability of surviving
s steps and then being killed](goal). -/
-- @node: stoppedWalk_initial_dead_integral
lemma stoppedWalk_initial_dead_integral {n : ℕ} (t : ℕ)
    (ht : GeometricParameterDomain t) (π : Fin n → ℝ) (hπ : IsProbabilityVector π)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsStochastic A)
    (m : ℕ) (f : Fin n → Fin n → ℝ) :
    (∫ ω, Sum.elim (fun _ => 0) (f (Sum.elim id id (ω 0))) (ω m)
      ∂stoppedWalkMeasure t ht π A hA) =
      ∑ s ∈ Finset.range m, geomKillProb t ht * geomSurvProb t ht ^ s *
        ∑ i, ∑ j, π i * (A ^ s) i j * f i j := by
  classical
  let := stoppedState_measurableSingletonClass n
  let := stoppedInitialLaw_isProbabilityMeasure π hπ
  let := stoppedWalkKernel_isMarkov t ht A hA
  let D : StoppedState n → StoppedState n → ℝ :=
    fun a b => Sum.elim (fun _ => 0) (f (Sum.elim id id a)) b
  let L : StoppedState n → StoppedState n → ℝ :=
    fun a b => Sum.elim (f (Sum.elim id id a)) (fun _ => 0) b
  have hk (a b : StoppedState n) :
      (∫ c, D a c ∂stoppedWalkKernel t ht A b) =
        D a b + geomKillProb t ht * L a b := by
    cases b with
    | inl j => simp [D, L, stoppedWalkKernel_integral_alive t ht A hA]
    | inr j =>
      change (∫ c, D a c ∂Measure.dirac (Sum.inr j)) = _
      simp [D, L]
  induction m with
  | zero =>
    simpa [D] using stoppedWalk_integral_zero t ht π hπ A hA (fun a => D a a)
  | succ m ih =>
    have hstep := finite_kernel_integral_initial_transition (stoppedInitialLaw π)
      (stoppedWalkKernel t ht A) (fun a _ c => D a c) m
    change (∫ ω, D (ω 0) (ω (m + 1)) ∂stoppedWalkMeasure t ht π A hA) = _ at hstep
    change (∫ ω, D (ω 0) (ω (m + 1)) ∂stoppedWalkMeasure t ht π A hA) = _
    rw [hstep]
    simp_rw [hk]
    change (∫ ω, D (ω 0) (ω m) + geomKillProb t ht * L (ω 0) (ω m)
      ∂stoppedWalkMeasure t ht π A hA) = _
    rw [integral_add (integrable_stoppedWalk_two_time_score t ht π hπ A hA D 0 m)
      ((integrable_stoppedWalk_two_time_score t ht π hπ A hA L 0 m).const_mul _),
      integral_const_mul]
    change (∫ ω, Sum.elim (fun _ => 0) (f (Sum.elim id id (ω 0))) (ω m)
      ∂stoppedWalkMeasure t ht π A hA) + geomKillProb t ht *
      (∫ ω, Sum.elim (f (Sum.elim id id (ω 0))) (fun _ => 0) (ω m)
        ∂stoppedWalkMeasure t ht π A hA) = _
    rw [ih, stoppedWalk_initial_alive_integral t ht π hπ A hA, Finset.sum_range_succ]
    ring

/-- For [a positive integer time parameter](hyp:ht), [an initial probability
vector](hyp:hπ), and [a stochastic transition matrix](hyp:hA), [the expected
squared distance from the initial ℓ¹ point to the reconstructed terminal cut
value of the killed walk equals the geometric mixture of the original chain's
squared endpoint distances, weighted by the initial probabilities, the s-step
transition probabilities, and the probability of surviving s steps and then
being killed](goal). -/
-- @node: stoppedWalk_cut_endpoint_geometric_mixture
lemma stoppedWalk_cut_endpoint_geometric_mixture {n : ℕ} (t : ℕ)
    (ht : GeometricParameterDomain t) (π : Fin n → ℝ) (hπ : IsProbabilityVector π)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsStochastic A)
    (x : Fin n → RealEllOne) :
    (∫ ω, dist (Sum.elim x x (ω 0))
      (cutReconstruction x
        (stoppedWalkTerminal (resolvent t ht A (cutEncoding x)) (cutEncoding x) ω)) ^ 2
          ∂stoppedWalkMeasure t ht π A hA) =
      ∑' s : ℕ, geomKillProb t ht * geomSurvProb t ht ^ s *
        ∑ i, ∑ j, π i * (A ^ s) i j * dist (x i) (x j) ^ 2 := by
  classical
  let := stoppedState_measurableSingletonClass n
  let := stoppedWalkMeasure_isProbabilityMeasure t ht π hπ A hA
  let F : ℕ → StoppedPath n → ℝ := fun m ω =>
    Sum.elim (fun _ => 0)
      (fun j => dist (Sum.elim x x (ω 0)) (x j) ^ 2) (ω m)
  have hmeas (m : ℕ) : AEStronglyMeasurable (F m)
      (stoppedWalkMeasure t ht π A hA) := by
    exact (integrable_stoppedWalk_two_time_score t ht π hπ A hA
      (fun a b => Sum.elim (fun _ => 0) (fun j => dist (Sum.elim x x a) (x j) ^ 2) b)
      0 m).aestronglyMeasurable
  have hb (m : ℕ) (ω : StoppedPath n) :
      ‖F m ω‖ ≤ ∑ i, ∑ j, dist (x i) (x j) ^ 2 := by
    have hpair (i j : Fin n) : dist (x i) (x j) ^ 2 ≤
        ∑ i, ∑ j, dist (x i) (x j) ^ 2 :=
      (Finset.single_le_sum (fun j _ => sq_nonneg (dist (x i) (x j)))
        (Finset.mem_univ j)).trans
        (Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun j _ =>
          sq_nonneg (dist (x i) (x j))) (Finset.mem_univ i))
    dsimp [F]
    cases hm : ω m with
    | inl j => simpa using
        (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
          sq_nonneg (dist (x i) (x j)))
    | inr j =>
      simp only [Sum.elim_inr, abs_pow, abs_of_nonneg dist_nonneg]
      cases hzero : ω 0 <;> exact hpair _ _
  have hlim : ∀ᵐ ω ∂stoppedWalkMeasure t ht π A hA,
      Filter.Tendsto (fun m => F m ω) Filter.atTop
        (𝓝 (dist (Sum.elim x x (ω 0))
          (cutReconstruction x
            (stoppedWalkTerminal (resolvent t ht A (cutEncoding x))
              (cutEncoding x) ω)) ^ 2)) := by
    filter_upwards [stoppedWalk_eventually_constant_dead t ht π hπ A hA] with ω hω
    obtain ⟨j, hj⟩ := hω
    have hv : Filter.Tendsto
        (fun m => stoppedWalkValue (resolvent t ht A (cutEncoding x)) (cutEncoding x) m ω)
        Filter.atTop (𝓝 (cutEncoding x j)) :=
      tendsto_const_nhds.congr' (hj.mono fun m hm => by simp [stoppedWalkValue, hm])
    have heq : stoppedWalkTerminal (resolvent t ht A (cutEncoding x))
        (cutEncoding x) ω = cutEncoding x j := hv.limUnder_eq
    rw [heq, cutReconstruction_encoding]
    exact tendsto_const_nhds.congr' (hj.mono fun m hm => by simp [F, hm])
  have hc := tendsto_integral_of_dominated_convergence
    (fun _ : StoppedPath n => ∑ i, ∑ j, dist (x i) (x j) ^ 2)
    hmeas (integrable_const _) (fun m => ae_of_all _ (hb m)) hlim
  have hid (m : ℕ) : (∫ ω, F m ω ∂stoppedWalkMeasure t ht π A hA) =
      ∑ s ∈ Finset.range m, geomKillProb t ht * geomSurvProb t ht ^ s *
        ∑ i, ∑ j, π i * (A ^ s) i j * dist (x i) (x j) ^ 2 := by
    convert stoppedWalk_initial_dead_integral t ht π hπ A hA m
      (fun i j => dist (x i) (x j) ^ 2) using 1
    apply integral_congr_ae
    exact ae_of_all _ fun ω => by
      dsimp [F]
      cases ω 0 <;> rfl
  simp_rw [hid] at hc
  have hn (s : ℕ) : 0 ≤ geomKillProb t ht * geomSurvProb t ht ^ s *
      ∑ i, ∑ j, π i * (A ^ s) i j * dist (x i) (x j) ^ 2 := by
    apply mul_nonneg
    · exact mul_nonneg (by unfold geomKillProb; positivity)
        (pow_nonneg (geomSurvProb_pos_lt_one t ht).1.le s)
    · exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
        mul_nonneg (mul_nonneg (hπ.1 i) ((isStochastic_pow A hA s).nonneg i j))
          (sq_nonneg _)
  exact ((hasSum_iff_tendsto_nat_of_nonneg hn _).mpr hc).tsum_eq.symm

end Papers.OaiMetricMarkovCotype

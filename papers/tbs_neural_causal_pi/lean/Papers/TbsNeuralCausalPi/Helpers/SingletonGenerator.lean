module
public import Papers.TbsNeuralCausalPi.Helpers.HilbertCurve
public import Papers.TbsNeuralCausalPi.Helpers.WideSecondBlocks
public import Papers.TbsNeuralCausalPi.Helpers.GeneratorMixing
public import Papers.TbsNeuralCausalPi.Helpers.GeneratorMixtureLaw
/-! # Exact component blocks for singleton-supported generators

Zero-dimensional charts need no approximation theorem. Constant affine outputs
generate their component laws exactly, at every width and depth. The only
remaining error is the soft categorical selector.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
open scoped NNReal ENNReal
noncomputable section

/-- Given [a nonnegative chart Lipschitz bound](hyp:L), suppose [the probability
law has the specified finite support components](hyp:hsupp), [these components
have Lipschitz homeomorphic cube charts with that bound](hyp:hcharts), and
[every chart has dimension zero](hyp:hzero). Then [there is a positive common
box radius such that, at every pair of width and depth budgets and every
positive temperature, a three-part generator has the exact component masses,
first blocks mapping into the chart cubes, second blocks mapping all inputs
into their components and the common box, and component-mixture law exactly
equal to the target probability law](goal). -/
-- @node: exists_singleton_generator_blocks
lemma exists_singleton_generator_blocks {d N : ℕ}
    (P : ProbabilityMeasure (L1Vec d)) (S : Fin N → Set (L1Vec d))
    (dC : Fin N → ℕ) (L : ℝ≥0)
    (hsupp : SupportFiniteComponents (P : Measure _) S)
    (hcharts : ComponentsLipschitzHomeomorphic S dC L)
    (hzero : ∀ i, dC i = 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ W1 L1 W2 L2 : ℕ, ∀ tau : ℝ, 0 < tau →
      ∃ Q : ThreePartGenerator N d dC W1 L1 W2 L2 tau,
        (∀ i, Q.p i = ((P : Measure _) (S i)).toReal) ∧
        (∀ i, Set.MapsTo (Q.g1 i).eval (unitCube 1) (unitCube (dC i))) ∧
        (∀ i, Set.MapsTo (Q.g2 i).eval Set.univ (S i)) ∧
        (∀ i x, (Q.g2 i).eval x ∈ boundedCube d K) ∧
        (∑ i, ENNReal.ofReal (Q.p i) •
          (uniformCubeLaw 1).map ((Q.g2 i).eval ∘ (Q.g1 i).eval)) = (P : Measure _) := by
  classical
  have hsingle (i : Fin N) : ∃ c : L1Vec d, S i = {c} := by
    obtain ⟨f, hf⟩ := hcharts i
    rw [hzero i] at f
    exact zeroDim_chart_singleton f
  choose c hc using hsingle
  obtain ⟨K, hK, hbox⟩ := exists_component_bounding_box hcharts
  have hp := support_component_real_masses P hsupp hcharts
  refine ⟨K, hK, ?_⟩
  intro W1 L1 W2 L2 tau htau
  let Q : ThreePartGenerator N d dC W1 L1 W2 L2 tau :=
    { g1 := fun i => zeroNet 1 (dC i) W1 L1
      g2 := fun i => constantNet (dC i) W2 L2 (c i)
      p := fun i => ((P : Measure _) (S i)).toReal
      weights := ⟨fun i => (hp.1 i).le, hp.2⟩
      positiveWeights := hp.1
      temperature := htau }
  have hmem (i : Fin N) : c i ∈ S i := by rw [hc i]; exact Set.mem_singleton _
  have heval (i : Fin N) (x : L1Vec (dC i)) : (Q.g2 i).eval x = c i :=
    constantNet_eval _ _ _ _ _
  refine ⟨Q, fun i => rfl, ?_, ?_, ?_, ?_⟩
  · intro i x hx j
    exact (Nat.not_lt_zero j.val (hzero i ▸ j.isLt)).elim
  · intro i x hx
    rw [heval]
    exact hmem i
  · intro i x
    rw [heval]
    exact hbox i (hmem i)
  · rw [support_components_cond_mixture P hsupp hcharts]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    let mu : ProbabilityMeasure (L1Vec d) :=
      ⟨ProbabilityTheory.cond (P : Measure _) (S i),
        support_component_cond_probability P hsupp hcharts i⟩
    have hmass : (mu : Measure _) {c i} = 1 := by
      rw [← hc i]
      exact ProbabilityTheory.cond_apply_self
        (ne_of_gt (support_component_mass_pos P hsupp hcharts i)) (measure_ne_top _ _)
    have hmu := probability_eq_dirac_of_singleton_mass mu (c i) hmass
    have hcomp : (Q.g2 i).eval ∘ (Q.g1 i).eval = fun _ => c i := funext fun x => heval i _
    rw [hcomp, show ProbabilityTheory.cond (P : Measure _) (S i) = _ from hmu]
    let := uniformCubeLaw_probability 1
    simp

/-- Given [a nonnegative chart Lipschitz bound](hyp:L), suppose [the probability
law has the specified finite support components](hyp:hsupp), [these components
admit Lipschitz homeomorphic cube charts with that bound](hyp:hcharts), and
[all chart dimensions are zero](hyp:hzero). Then [a positive constant exists
such that, for all width and depth budgets and temperatures strictly between
zero and one, a three-part generator has the exact component masses, maps the
input cube through each chart cube into its component, and approximates the
target law in Wasserstein distance within that constant times temperature
minus temperature times its logarithm](goal). -/
-- @node: singleton_generator_approximation
lemma singleton_generator_approximation {d N : ℕ}
    (P : ProbabilityMeasure (L1Vec d)) (S : Fin N → Set (L1Vec d))
    (dC : Fin N → ℕ) (L : ℝ≥0)
    (hsupp : SupportFiniteComponents (P : Measure _) S)
    (hcharts : ComponentsLipschitzHomeomorphic S dC L)
    (hzero : ∀ i, dC i = 0) :
    ∃ A : ℝ, 0 < A ∧ ∀ W1 L1 W2 L2 : ℕ, ∀ tau : ℝ,
      0 < tau → tau < 1 →
      ∃ Q : ThreePartGenerator N d dC W1 L1 W2 L2 tau,
        (∀ i, Q.p i = ((P : Measure _) (S i)).toReal) ∧
        (∀ i, Set.MapsTo (Q.g1 i).eval (unitCube 1) (unitCube (dC i))) ∧
        (∀ i, Set.MapsTo (Q.g2 i).eval (unitCube (dC i)) (S i)) ∧
        wasserstein1 (generatorLaw Q) (P : Measure _) ≤
          ENNReal.ofReal (A * (tau - tau * Real.log tau)) := by
  obtain ⟨K, hK, hblocks⟩ := exists_singleton_generator_blocks P S dC L hsupp hcharts hzero
  let a : ℝ := 2 * (N-1 : ℕ)
  let b : ℝ := 2 * N * (N-1 : ℕ) * Real.exp (-1)
  let M : ℝ := d * K * (a+b)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨M+1, by positivity, ?_⟩
  intro W1 L1 W2 L2 tau htau htau1
  obtain ⟨Q, hp, hcube, hzero, hbox, hmix⟩ := hblocks W1 L1 W2 L2 tau htau
  have hN : 0 < N := by
    by_contra hn
    have hz : N = 0 := by omega
    subst N
    have hw := Q.weights.2
    simp at hw
  refine ⟨Q, hp, hcube, fun i x hx => hzero i (Set.mem_univ x), ?_⟩
  have hhard := generator_hard_law_eq_mixture Q hN
  rw [hmix] at hhard
  have hsoft := generator_soft_hard_wasserstein_le Q (by omega) K hK.le hbox htau1
  rw [hhard] at hsoft
  have hlog : Real.log tau ≤ 0 := Real.log_nonpos htau.le htau1.le
  have hneglog : 0 ≤ -(tau * Real.log tau) := by
    exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos htau.le hlog)
  have hT : 0 ≤ tau - tau * Real.log tau := by linarith
  refine hsoft.trans ?_
  rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ d*K)]
  apply ENNReal.ofReal_le_ofReal
  change (d : ℝ)*K*(a*tau-b*tau*Real.log tau) ≤ (M+1)*(tau-tau*Real.log tau)
  have hlocal : a*tau-b*tau*Real.log tau ≤ (a+b)*(tau-tau*Real.log tau) := by
    nlinarith [mul_nonneg ha hneglog, mul_nonneg hb htau.le]
  calc
    _ ≤ (d : ℝ)*K*((a+b)*(tau-tau*Real.log tau)) :=
      mul_le_mul_of_nonneg_left hlocal (by positivity)
    _ = M*(tau-tau*Real.log tau) := by dsimp [M]; ring
    _ ≤ _ := by nlinarith

end
end Papers.TbsNeuralCausalPi

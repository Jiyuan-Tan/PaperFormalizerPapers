module
public import Papers.OaiMetricMarkovCotype.Helpers.StoppedMartingale
public import Papers.OaiMetricMarkovCotype.TMartingale
public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-! # Terminal values and the cubic energy estimate for the killed walk -/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
namespace Papers.OaiMetricMarkovCotype

variable {n : ℕ} {𝓑 : Type*} [Fintype 𝓑]

/-- With [n possible state indices](hyp:n) and [a finite coordinate set](hyp:𝓑),
for [vectors h assigned to live states](hyp:h), [vectors z assigned to
stopped states](hyp:z), and [a stopped-walk path ω](hyp:ω), [the terminal
vector](goal) is the canonical limit of the walk's vector values along that path. -/
-- @node: stoppedWalkTerminal
def stoppedWalkTerminal (h z : Fin n → 𝓑 → ℝ) (ω : StoppedPath n) : 𝓑 → ℝ :=
  limUnder atTop (fun m => stoppedWalkValue h z m ω)

/-- For [vectors h assigned to live states](hyp:h) and vectors z assigned to
stopped states, the walk's vector value at any fixed time is
[strongly measurable as a function of the path](goal). -/
@[fun_prop]
-- @node: stronglyMeasurable_stoppedWalkValue
lemma stronglyMeasurable_stoppedWalkValue (h z : Fin n → 𝓑 → ℝ) (m : ℕ) :
    StronglyMeasurable (stoppedWalkValue h z m) := by
  let := stoppedState_measurableSingletonClass n
  first | fun_prop | skip
  have hg : Measurable (Sum.elim h z) := by fun_prop
  have hc : Measurable (fun ω : StoppedPath n => ω m) := measurable_pi_apply m
  convert (hg.comp hc).stronglyMeasurable using 1
  funext ω
  unfold stoppedWalkValue Function.comp
  dsimp only
  cases ω m <;> rfl

/-- For [vectors h assigned to live states](hyp:h) and vectors z assigned to
stopped states, [the terminal vector is strongly measurable as a function of
the path](goal). -/
@[fun_prop]
-- @node: stronglyMeasurable_stoppedWalkTerminal
lemma stronglyMeasurable_stoppedWalkTerminal (h z : Fin n → 𝓑 → ℝ) :
    StronglyMeasurable (stoppedWalkTerminal h z) := by
  exact StronglyMeasurable.limUnder (fun m => stronglyMeasurable_stoppedWalkValue h z m)

-- @node: stoppedWalkTerminal_eq_input
/-- If [the geometric time parameter is positive](hyp:ht), [π is a probability
vector](hyp:hπ), and [A is a stochastic transition matrix](hyp:hA), then for
[live-state vectors h](hyp:h) and stopped-state vectors z, [almost every stopped
walk has a terminal vector equal to one of the vectors z, and its successive
vector values converge to that terminal vector](goal). -/
lemma stoppedWalkTerminal_eq_input (t : ℕ) (ht : GeometricParameterDomain t)
    (π : Fin n → ℝ) (hπ : IsProbabilityVector π)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsStochastic A)
    (h z : Fin n → 𝓑 → ℝ) :
    ∀ᵐ ω ∂stoppedWalkMeasure t ht π A hA,
      ∃ i : Fin n, stoppedWalkTerminal h z ω = z i ∧
        Tendsto (fun m => stoppedWalkValue h z m ω) atTop
          (𝓝 (stoppedWalkTerminal h z ω)) := by
  filter_upwards [stoppedWalkValue_tendsto_terminal t ht π hπ A hA h z] with ω hω
  obtain ⟨i, hi⟩ := hω
  have heq : stoppedWalkTerminal h z ω = z i := hi.limUnder_eq
  exact ⟨i, heq, heq.symm ▸ hi⟩

-- @node: stoppedWalkValue_cubeMartingale
/-- If [the geometric time parameter is positive](hyp:ht), [π is a probability
vector](hyp:hπ), [A is stochastic](hyp:hA), and [every input vector z lies in
the unit cube](hyp:hz), then [the stopped walk with resolvent live-state values
is a martingale for its natural filtration, all its values lie in the cube,
and it converges almost surely to its cube-valued terminal vector](goal). -/
lemma stoppedWalkValue_cubeMartingale (t : ℕ) (ht : GeometricParameterDomain t)
    (π : Fin n → ℝ) (hπ : IsProbabilityVector π)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsStochastic A)
    (z : Fin n → 𝓑 → ℝ) (hz : ∀ i, z i ∈ unitCube 𝓑) :
    CubeMartingale (stoppedWalkMeasure t ht π A hA) (stoppedWalkFiltration n)
      (stoppedWalkValue (resolvent t ht A z) z)
      (stoppedWalkTerminal (resolvent t ht A z) z) := by
  refine ⟨stoppedWalkValue_martingale t ht π hπ A hA z,
    stoppedWalkValue_mem_unitCube t ht A hA z hz, ?_, ?_⟩
  · filter_upwards [stoppedWalkTerminal_eq_input t ht π hπ A hA
      (resolvent t ht A z) z] with ω hω
    exact hω.choose_spec.2
  · filter_upwards [stoppedWalkTerminal_eq_input t ht π hπ A hA
      (resolvent t ht A z) z] with ω hω
    obtain ⟨i, hi, _⟩ := hω
    rw [hi]
    exact hz i

/-- If [every vector z has only zero and one coordinates](hyp:hz), then
[the stopped walk's time-zero value with z assigned to both live and stopped
states is measurable with respect to the initial information and is binary
on every path](goal). -/
-- @node: stoppedWalk_initialBinaryCenter
lemma stoppedWalk_initialBinaryCenter (z : Fin n → 𝓑 → ℝ)
    (hz : ∀ i, BinaryVector (z i)) :
    InitialBinaryCenter (stoppedWalkFiltration n) (stoppedWalkValue z z 0) := by
  let := stoppedState_measurableSingletonClass n
  constructor
  · first | fun_prop | skip
    have hg : Measurable (Sum.elim z z) := by fun_prop
    convert (hg.comp
      (Toolkit.Foundations.Probability.Processes.adapted_coordinate
        (fun _ => StoppedState n) 0)).stronglyMeasurable using 1 <;> try rfl
    funext ω
    unfold stoppedWalkValue Function.comp
      Toolkit.Foundations.Probability.Processes.coordinate
    cases ω 0 <;> rfl
  · intro ω
    unfold stoppedWalkValue
    cases ω 0 <;> exact hz _

-- @node: binaryVector_mem_unitCube
/-- If [every coordinate of z is zero or one](hyp:hz), then [z belongs to
the unit cube](goal). -/
lemma binaryVector_mem_unitCube {z : 𝓑 → ℝ} (hz : BinaryVector z) :
    z ∈ unitCube 𝓑 := by
  intro B _
  rcases hz B with hB | hB <;> simp [hB]

/-- Suppose [the geometric time parameter is positive](hyp:ht), [π is a
probability vector](hyp:hπ), [A is stochastic](hyp:hA), [all coordinate weights
are strictly positive](hyp:hw), [the finite coordinate set is nonempty](hyp:hfinite),
and [each input vector z is binary](hyp:hz). Then [the expected sum of squared
weighted ℓ₁ increments of the cubically smoothed resolvent stopped walk is at
most 108 times the expected quartic potential of its terminal vector relative
to its initial binary center](goal). -/
-- @node: stoppedWalk_cubic_energy_bound
lemma stoppedWalk_cubic_energy_bound (t : ℕ) (ht : GeometricParameterDomain t)
    (π : Fin n → ℝ) (hπ : IsProbabilityVector π)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsStochastic A)
    (w : 𝓑 → ℝ) (hw : PositiveWeights w) (hfinite : FiniteCutIndex 𝓑)
    (z : Fin n → 𝓑 → ℝ) (hz : ∀ i, BinaryVector (z i)) :
    (∫⁻ ω, ∑' m : ℕ, ENNReal.ofReal
      (weightedL1Norm w
        (cubicMap (stoppedWalkValue (resolvent t ht A z) z (m + 1) ω) -
          cubicMap (stoppedWalkValue (resolvent t ht A z) z m ω)) ^ 2)
        ∂stoppedWalkMeasure t ht π A hA) ≤
      ENNReal.ofReal (108 * ∫ ω, quarticPotential w (stoppedWalkValue z z 0 ω)
        (stoppedWalkTerminal (resolvent t ht A z) z ω)
          ∂stoppedWalkMeasure t ht π A hA) := by
  let := stoppedWalkMeasure_isProbabilityMeasure t ht π hπ A hA
  have hM := stoppedWalkValue_cubeMartingale t ht π hπ A hA z
    (fun i => binaryVector_mem_unitCube (hz i))
  have he := stoppedWalk_initialBinaryCenter z hz
  obtain ⟨henergy, hpotential⟩ := martingale_cubic_energy_bound
    (stoppedWalkMeasure t ht π A hA) (stoppedWalkFiltration n) w
    (stoppedWalkValue (resolvent t ht A z) z)
    (stoppedWalkTerminal (resolvent t ht A z) z) (stoppedWalkValue z z 0)
    hfinite hw hM he
  exact henergy.trans (ENNReal.ofReal_le_ofReal hpotential)

-- @node: stoppedWalk_initial_quartic_integral
/-- If [the geometric time parameter is positive](hyp:ht), [π is a probability
vector](hyp:hπ), and [A is stochastic](hyp:hA), then for weights w,
[live-state vectors h](hyp:h), and stopped-state vectors z, [the expected
time-zero quartic potential of the walk relative to its initial z center equals
the π-weighted sum of the quartic potentials of h relative to z at each state](goal). -/
lemma stoppedWalk_initial_quartic_integral (t : ℕ) (ht : GeometricParameterDomain t)
    (π : Fin n → ℝ) (hπ : IsProbabilityVector π)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsStochastic A)
    (w : 𝓑 → ℝ) (h z : Fin n → 𝓑 → ℝ) :
    (∫ ω, quarticPotential w (stoppedWalkValue z z 0 ω)
      (stoppedWalkValue h z 0 ω) ∂stoppedWalkMeasure t ht π A hA) =
      ∑ i, π i * quarticPotential w (z i) (h i) := by
  convert stoppedWalk_integral_zero t ht π hπ A hA
    (fun s => quarticPotential w (Sum.elim z z s) (Sum.elim h z s)) using 1 <;> try rfl
  apply integral_congr_ae
  exact ae_of_all _ fun ω => by
    dsimp only [stoppedWalkValue]
    cases ω 0 <;> rfl

end Papers.OaiMetricMarkovCotype

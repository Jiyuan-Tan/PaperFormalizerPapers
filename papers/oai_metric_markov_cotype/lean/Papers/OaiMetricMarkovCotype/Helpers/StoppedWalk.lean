module
public import Papers.OaiMetricMarkovCotype.Helpers.Cuts
public import Toolkit.Foundations.Probability.Processes.PathLaw
public import Toolkit.Foundations.Probability.Processes.NaturalFiltration
public import Toolkit.Foundations.Probability.Processes.DeterministicIteration

/-! # Resolvent smoothing and the alive/dead stopped walk

Alive and dead states are the two summands of `Fin n ⊕ Fin n`. The path
filtration reveals the initial state and transitions only through the current time.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace Papers.OaiMetricMarkovCotype

variable {n : ℕ} {𝓑 : Type*} [Fintype 𝓑]

/-- For [a natural-number time](hyp:t) [that is strictly positive](hyp:h_time),
[a transition matrix](hyp:A), [state-indexed vectors](hyp:z), and [a starting index](hyp:i),
the [resolvent vector](goal) is the killing probability times the infinite sum of the
matrix-averaged vectors after each number of steps, weighted by that power of the survival probability.

@realizes h_i(geometric average p times the sum of q^s A^s z)
@realizes \E_i(starting-state expectation represented by the resolvent series) -/
def resolvent (t : ℕ) (h_time : GeometricParameterDomain t)
    (A : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → 𝓑 → ℝ)
    (i : Fin n) : 𝓑 → ℝ :=
  geomKillProb t h_time • ∑' s : ℕ, geomSurvProb t h_time ^ s • ∑ j, (A ^ s) i j • z j

open Classical in
-- @node: def:y
/-- Given [a natural-number time](hyp:t) [that is strictly positive](hyp:h_time),
[state weights](hyp:_π), [a transition matrix](hyp:A), and [input points in real ℓ¹](hyp:x),
the [modified points](goal) equal the input points when all coincide; otherwise they are
reconstructed from the cubic smoothing of the resolvent of their cut encodings.

@realizes y_i(input point in the coincident case; otherwise T of the smoothed resolvent) -/
def modifiedPoints (t : ℕ) (h_time : GeometricParameterDomain t)
    (_π : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → RealEllOne) : Fin n → RealEllOne :=
  if ∀ i j, x i = x j then x else
    fun i => cutReconstruction x (cubicMap (resolvent t h_time A (cutEncoding x) i))

/-- For [a number of indices](hyp:n), the [stopped state space](goal) consists of
an alive copy and a dead copy of those indices. -/
abbrev StoppedState (n : ℕ) := Fin n ⊕ Fin n
/-- For [a number of indices](hyp:n), the [stopped path space](goal) consists of
sequences of alive or dead indexed states, one state at each nonnegative integer time. -/
abbrev StoppedPath (n : ℕ) :=
  Toolkit.Foundations.Probability.Processes.Path (fun _ => StoppedState n)

/-- For [state masses](hyp:π), the [initial stopped-walk measure](goal) puts the
nonnegative part of each mass on the corresponding alive state. -/
def stoppedInitialLaw (π : Fin n → ℝ) : Measure (StoppedState n) :=
  ∑ i, ENNReal.ofReal (π i) • Measure.dirac (Sum.inl i)

-- @node: stoppedState_measurableSingletonClass
/-- [The finite alive/dead state space has measurable singletons](goal). -/
lemma stoppedState_measurableSingletonClass (n : ℕ) :
    MeasurableSingletonClass (StoppedState n) := by
  constructor
  intro s
  cases s with
  | inl i => simpa using (measurableSet_singleton i).inl_image (β := Fin n)
  | inr i => simpa using (measurableSet_singleton i).inr_image (α := Fin n)

/-- For [a natural-number time](hyp:t) [that is strictly positive](hyp:h_time)
and [a transition matrix](hyp:A), the [stopped-walk transition kernel](goal)
[uses the measurable-singleton structure on the state space](step:1), then
[kills an alive state at its current index with the killing probability, moves it
to alive indices with masses given by the nonnegative parts of survival probability
times transition entries, and leaves a dead state fixed](step:2). -/
def stoppedWalkKernel (t : ℕ) (h_time : GeometricParameterDomain t)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    Kernel (StoppedState n) (StoppedState n) :=
  letI := stoppedState_measurableSingletonClass n
  Kernel.ofFunOfCountable (fun s => match s with
    | Sum.inl i => ENNReal.ofReal (geomKillProb t h_time) • Measure.dirac (Sum.inr i) +
        ∑ j, ENNReal.ofReal (geomSurvProb t h_time * A i j) • Measure.dirac (Sum.inl j)
    | Sum.inr i => Measure.dirac (Sum.inr i))

-- @node: stoppedWalkKernel_isMarkov
/-- If [the time parameter is strictly positive](hyp:h_time)
and [the transition matrix is stochastic](hyp:h_stochastic), then
[the stopped-walk kernel assigns a probability distribution to every state](goal). -/
lemma stoppedWalkKernel_isMarkov (t : ℕ) (h_time : GeometricParameterDomain t)
    (A : Matrix (Fin n) (Fin n) ℝ) (h_stochastic : IsStochastic A) :
    IsMarkovKernel (stoppedWalkKernel t h_time A) := by
  have hp : 0 ≤ geomKillProb t h_time := by
    unfold geomKillProb
    positivity
  have hp_le : geomKillProb t h_time ≤ 1 := by
    unfold geomKillProb
    exact (div_le_one (by positivity)).2 (by norm_num)
  have hq : 0 ≤ geomSurvProb t h_time := sub_nonneg.mpr hp_le
  constructor
  intro s
  constructor
  cases s with
  | inl i =>
    change (ENNReal.ofReal (geomKillProb t h_time) • Measure.dirac (Sum.inr i) +
      ∑ j, ENNReal.ofReal (geomSurvProb t h_time * A i j) •
        Measure.dirac (Sum.inl j) : Measure (StoppedState n)) Set.univ = 1
    simp only [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem
      (Set.mem_univ _), smul_eq_mul, mul_one, Measure.finsetSum_apply]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg hq (h_stochastic.nonneg i j))]
    rw [← ENNReal.ofReal_add hp (Finset.sum_nonneg (fun j _ =>
      mul_nonneg hq (h_stochastic.nonneg i j)))]
    rw [← Finset.mul_sum, h_stochastic.row_sums i]
    simp [geomSurvProb]
  | inr i =>
    change (Measure.dirac (Sum.inr i) : Measure (StoppedState n)) Set.univ = 1
    simp

/-- Given [a natural-number time](hyp:t) [that is strictly positive](hyp:h_time),
[initial state masses](hyp:π), and [a transition matrix](hyp:A)
[that is stochastic](hyp:h_stochastic), the [stopped-walk path measure](goal)
[uses the probability transition kernel](step:1) and
[forms the path law from the initial alive-state measure and repeated application of that kernel](step:2). -/
def stoppedWalkMeasure (t : ℕ) (h_time : GeometricParameterDomain t)
    (π : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (h_stochastic : IsStochastic A) : Measure (StoppedPath n) :=
  letI := stoppedWalkKernel_isMarkov t h_time A h_stochastic
  Toolkit.Foundations.Probability.Processes.pathLaw (stoppedInitialLaw π)
    (Toolkit.Foundations.Probability.Processes.homogeneousTransition (stoppedWalkKernel t h_time A))

/-- For [a number of indices](hyp:n), the [stopped-walk filtration](goal) reveals
the initial alive or dead state and all transitions through the current time.

@realizes \calF_m(natural filtration: initial state and first m transitions) -/
def stoppedWalkFiltration (n : ℕ) :
    Filtration ℕ (inferInstance : MeasurableSpace (StoppedPath n)) :=
  Toolkit.Foundations.Probability.Processes.naturalFiltration (fun _ => StoppedState n)

-- @node: def:stopped-walk
/-- Given [vectors attached to alive states](hyp:h), [vectors attached to dead states](hyp:z),
[a time](hyp:m), and [a stopped path](hyp:ω), the [walk value](goal) is
[the alive vector at the current index when the state is alive](step:1), or
[the dead vector at the current index when the state is dead](step:2).

@realizes M_m(attached value h at alive states and z at dead states) -/
def stoppedWalkValue (h z : Fin n → 𝓑 → ℝ) (m : ℕ) (ω : StoppedPath n) : 𝓑 → ℝ :=
  match ω m with
  | Sum.inl i => h i
  | Sum.inr i => z i

/-- For [state masses](hyp:π), [coordinate weights](hyp:w), [target vectors](hyp:z),
and [approximating vectors](hyp:h), the [approximation cost](goal) is the sum over
states of the state mass times the squared weighted ℓ¹ distance from the target
to the cubically smoothed approximation.

@realizes B(scalar approximation cost, nonnegative on ApproxCostData) -/
def approxCost (π : Fin n → ℝ) (w : 𝓑 → ℝ) (z h : Fin n → 𝓑 → ℝ) : ℝ :=
  ∑ i, π i * weightedL1Norm w (z i - cubicMap (h i)) ^ 2

/-- For [state masses](hyp:π), the [approximation-cost admissibility condition](goal)
requires every state mass to be nonnegative. -/
def ApproxCostData (π : Fin n → ℝ) : Prop :=
  ∀ i, 0 ≤ π i -- @realizes B(nonnegative state masses in the scalar cost)

-- @node: approxCost_nonneg
/-- If [every state mass is nonnegative](hyp:hπ), then
[the approximation cost is nonnegative](goal), for any coordinate weights,
target vectors, and [approximating vectors](hyp:h). -/
lemma approxCost_nonneg (π : Fin n → ℝ) (hπ : ApproxCostData π)
    (w : 𝓑 → ℝ) (z h : Fin n → 𝓑 → ℝ) :
    0 ≤ approxCost π w z h := by -- @realizes B(scalar cost in the nonnegative reals)
  unfold approxCost
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hπ i) (sq_nonneg _)

/-- Given [state masses](hyp:π), [a transition matrix](hyp:A), [coordinate weights](hyp:w),
and [state-indexed vectors](hyp:h), the [smoothed energy](goal) sums the squared
weighted ℓ¹ distances between cubically smoothed vectors over all ordered pairs
of states, weighted by the starting mass times the transition entry.

@realizes E_A(one-step squared smoothed energy) -/
def smoothedEnergy (π : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (w : 𝓑 → ℝ) (h : Fin n → 𝓑 → ℝ) : ℝ :=
  ∑ i, ∑ j, π i * A i j * weightedL1Norm w (cubicMap (h i) - cubicMap (h j)) ^ 2

/-- For [state masses](hyp:π) and [a transition matrix](hyp:A), the
[smoothed-energy admissibility condition](goal) requires
[all state masses to be nonnegative](step:1) and
[all transition entries to be nonnegative](step:2). -/
def SmoothedEnergyData (π : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i, 0 ≤ π i) ∧ -- @realizes E_A(nonnegative state masses)
  StochasticNonnegative A -- @realizes E_A(nonnegative transition entries)

-- @node: ass:pin-1
/-- For [state masses](hyp:π), [coordinate weights](hyp:w), [target vectors](hyp:z),
and [approximating vectors](hyp:h), the [approximation-cost identity](goal) asserts
that the cost equals the state-mass-weighted sum of squared weighted ℓ¹ distances
between each target and its cubically smoothed approximation. -/
def ApproxCostReading (π : Fin n → ℝ) (w : 𝓑 → ℝ) (z h : Fin n → 𝓑 → ℝ) : Prop :=
  approxCost π w z h = ∑ i, π i * weightedL1Norm w (z i - cubicMap (h i)) ^ 2

end Papers.OaiMetricMarkovCotype

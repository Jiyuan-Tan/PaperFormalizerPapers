module
public import Papers.OaiMetricMarkovCotype.Basic
public import Papers.OaiMetricMarkovCotype.Helpers.GeometricMoments
public import Toolkit.Foundations.Probability.LimitTheorems.FiniteMarkovChain
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Analysis.Subadditive

/-! # Geometric endpoint comparison for stationary finite chains -/

@[expose] public section

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Papers.OaiMetricMarkovCotype

variable {Ω X : Type*} [MeasurableSpace Ω] [MetricSpace X] {n : ℕ}

-- @node: ass:comparison-chain
/-- Under [the measure μ](hyp:μ), [the finite-state process U](hyp:U) is
[a stationary finite Markov chain](goal) if there exist a transition matrix and
initial masses such that [the matrix is stochastic](step:1), [the masses are
stationary for that matrix](step:2), and [the process has the corresponding
finite-dimensional Markov path probabilities](step:3). -/
def StationaryFiniteChain (μ : Measure Ω) (U : ℕ → Ω → Fin n) : Prop :=
  ∃ (A : Matrix (Fin n) (Fin n) ℝ) (π : Fin n → ℝ),
    Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation.IsStochasticMatrix A ∧
    Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation.IsStationary A π ∧
    Toolkit.Foundations.Probability.LimitTheorems.HasMatrixMarkovLaw μ U π A
    -- @realizes X_s(stationary finite-dimensional Markov path law)

-- @node: ass:comparison-data
/-- For [a number n of states](hyp:n) and [metric-space points indexed by those
states](hyp:_x), [admissible comparison data means that the state set is nonempty](goal). -/
def ComparisonData (n : ℕ) (_x : Fin n → X) : Prop := 0 < n

-- @node: ass:comparison-time
/-- [A time t](hyp:t) satisfies [the positive-time condition](goal) when it is
strictly greater than zero. -/
def PositiveTime (t : ℕ) : Prop := 0 < t

-- @node: ass:comparison-independence
/-- Under [the measure μ](hyp:μ), [independence of the geometric time from the
walk](goal) means that [the random time S](hyp:S) is independent of the entire
trajectory of [the finite-state process U](hyp:U). -/
def GeometricIndependentOfWalk (μ : Measure Ω) (U : ℕ → Ω → Fin n) (S : Ω → ℕ) : Prop :=
  ProbabilityTheory.IndepFun S (fun ω s => U s ω) μ

-- @node: ass:comparison-geometric-law
/-- Under [the measure μ](hyp:μ), [the random time S](hyp:S) has [the geometric
law](goal) with [time parameter t](hyp:t), assumed [strictly positive](hyp:h_time),
when [S is measurable](step:1) and [the probability of S equaling s is the killing
probability times the s-th power of the survival probability, for every
nonnegative integer s](step:2). -/
def GeometricLaw (μ : Measure Ω) (S : Ω → ℕ) (t : ℕ) (h_time : PositiveTime t) : Prop :=
  Measurable S ∧ -- @realizes S(natural-valued geometric random variable)
  ∀ s : ℕ, μ.real {ω | S ω = s} = geomKillProb t h_time * geomSurvProb t h_time ^ s
  -- @realizes S(geometric mass p q^s, counting live transitions)

/-- For [a measure μ](hyp:μ), [a finite-state process U](hyp:U), [metric-space
points x assigned to the states](hyp:x), and [a time s](hyp:s), [the endpoint
cost](goal) is the expected squared distance between the point at time s and
the initial point.

@realizes D(expected squared distance from the initial state at time s) -/
def endpointCost (μ : Measure Ω) (U : ℕ → Ω → Fin n) (x : Fin n → X) (s : ℕ) : ℝ :=
  ∫ ω, dist (x (U s ω)) (x (U 0 ω)) ^ 2 ∂μ

/-- For [a measure μ](hyp:μ), [a finite-state process U](hyp:U), [metric-space
points x assigned to the states](hyp:x), and [a time horizon t](hyp:t), [the
Cesàro endpoint cost](goal) is the sum of expected squared endpoint distances
at times one through t, divided by t.

@realizes W(Cesàro average of endpoint costs at times one through t) -/
def cesaroEndpointCost (μ : Measure Ω) (U : ℕ → Ω → Fin n) (x : Fin n → X)
    (t : ℕ) : ℝ := (1 / (t : ℝ)) * ∑ s ∈ Finset.Icc 1 t, endpointCost μ U x s

/-- For [a random time S](hyp:S), [a block length t](hyp:t), and [an outcome
ω](hyp:ω), [the geometric block index](goal) is the integer quotient of S at
that outcome by t.

@realizes J(natural block quotient S divided by positive time t) -/
def geometricBlock (S : Ω → ℕ) (t : ℕ) (ω : Ω) : ℕ := S ω / t

/-- For [a random time S](hyp:S), [a block length t](hyp:t), and [an outcome
ω](hyp:ω), [the geometric remainder](goal) is the remainder when S at that
outcome is divided by t.

@realizes R(natural remainder S modulo positive time t) -/
def geometricRemainder (S : Ω → ℕ) (t : ℕ) (ω : Ω) : ℕ := S ω % t

/-- If [the initial masses π are stationary for the transition matrix A](hyp:hπ)
and [U has the Markov path law determined by π and A](hyp:hlaw), then
[the process obtained by dropping its initial observation has the same Markov
path law](goal). -/
-- @node: stationaryMatrixLaw_tail
lemma stationaryMatrixLaw_tail (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : ℕ → Ω → Fin n) (A : Matrix (Fin n) (Fin n) ℝ) (π : Fin n → ℝ)
    (hπ : Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation.IsStationary A π)
    (hlaw : Toolkit.Foundations.Probability.LimitTheorems.HasMatrixMarkovLaw μ U π A) :
    Toolkit.Foundations.Probability.LimitTheorems.HasMatrixMarkovLaw μ (fun k => U (k + 1)) π A := by
  classical
  obtain ⟨hU, hpaths⟩ := hlaw
  refine ⟨(fun k => hU (k + 1)), ?_⟩
  intro m x
  let E : Fin n → Set Ω := fun i =>
    {ω | ∀ j : Fin (m + 2), U j ω =
      (Fin.cons (α := fun _ : Fin (m + 2) => Fin n) i x) j}
  have heq : {ω | ∀ j : Fin (m + 1), U (j + 1) ω = x j} = ⋃ i, E i := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro h
      refine ⟨U 0 ω, ?_⟩
      intro j
      refine Fin.cases ?_ (fun k => ?_) j
      · simp
      · simpa using h k
    · rintro ⟨i, hi⟩ j
      simpa using hi j.succ
  have hd : Pairwise (fun i j => Disjoint (E i) (E j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro ω hi hj
    have hi0 := hi 0
    have hj0 := hj 0
    simp only [Fin.cons_zero, Fin.val_zero] at hi0 hj0
    exact hij (hi0.symm.trans hj0)
  have hmeas (i : Fin n) : MeasurableSet (E i) := by
    simp only [E, Set.ofPred_forall]
    exact MeasurableSet.iInter fun j =>
      hU j (t := {(Fin.cons (α := fun _ : Fin (m + 2) => Fin n) i x) j}) trivial
  have hw (i : Fin n) : μ.real (E i) =
      π i * A i (x 0) * ∏ j : Fin m, A (x j.castSucc) (x j.succ) := by
    rw [show E i = {ω | ∀ j : Fin (m + 2), U j ω =
      (Fin.cons (α := fun _ : Fin (m + 2) => Fin n) i x) j} from rfl,
      hpaths, Fin.prod_univ_succ]
    simp only [Fin.castSucc_zero, Fin.castSucc_succ, Fin.cons_zero, Fin.cons_succ]
    ring
  rw [heq, measureReal_iUnion_fintype hd hmeas]
  simp_rw [hw]
  rw [← Finset.sum_mul]
  have hstat : (∑ i, π i * A i (x 0)) = π (x 0) := congrFun hπ.2 (x 0)
  rw [hstat]

/-- If [U has the Markov path law with initial masses π and transition matrix
A](hyp:hlaw), then [the expected score of its first m + 1 observations equals
the sum over all such paths of the score times the initial mass and the product
of transition probabilities](goal). -/
-- @node: integral_matrixPath_score
lemma integral_matrixPath_score (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : ℕ → Ω → Fin n) (A : Matrix (Fin n) (Fin n) ℝ) (π : Fin n → ℝ)
    (hlaw : Toolkit.Foundations.Probability.LimitTheorems.HasMatrixMarkovLaw μ U π A)
    (m : ℕ) (v : (Fin (m + 1) → Fin n) → ℝ) :
    (∫ ω, v (fun i => U i ω) ∂μ) =
      ∑ a : Fin (m + 1) → Fin n,
        (π (a 0) * ∏ i : Fin m, A (a i.castSucc) (a i.succ)) * v a := by
  classical
  let : MeasurableSpace (Fin n) := ⊤
  have htop : (inferInstance : MeasurableSpace (Fin (m + 1) → Fin n)) = ⊤ := by
    ext s
    exact iff_of_true MeasurableSet.of_discrete trivial
  have hm : @Measurable Ω (Fin (m + 1) → Fin n) _ ⊤ (fun ω i => U i ω) := by
    rw [← htop]
    exact measurable_pi_iff.mpr fun i => hlaw.1 i
  rw [Toolkit.Foundations.Probability.Conditioning.integral_finite_score μ hm v]
  apply Finset.sum_congr rfl
  intro a _
  have he : {ω | (fun i : Fin (m + 1) => U i ω) = a} =
      {ω | ∀ i : Fin (m + 1), U i ω = a i} := by
    ext ω
    exact funext_iff
  rw [he, hlaw.2]

/-- If [U is a stationary finite Markov chain](hyp:hchain), then [its expected
squared endpoint distance at lag s is unchanged by dropping the initial
observation](goal). -/
-- @node: endpointCost_tail
lemma endpointCost_tail (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : ℕ → Ω → Fin n) (x : Fin n → X) (hchain : StationaryFiniteChain μ U)
    (s : ℕ) : endpointCost μ (fun k => U (k + 1)) x s = endpointCost μ U x s := by
  obtain ⟨A, π, _, hπ, hlaw⟩ := hchain
  have htail := stationaryMatrixLaw_tail μ U A π hπ hlaw
  let v : (Fin (s + 1) → Fin n) → ℝ := fun a => dist (x (a (Fin.last s))) (x (a 0)) ^ 2
  exact (integral_matrixPath_score μ (fun k => U (k + 1)) A π htail s v).trans
    (integral_matrixPath_score μ U A π hlaw s v).symm

/-- If [U is a stationary finite Markov chain](hyp:hchain), then [the expected
squared distance between its metric-space points at times r and r + s equals
the endpoint cost at lag s](goal). -/
-- @node: endpointCost_shift
lemma endpointCost_shift (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : ℕ → Ω → Fin n) (x : Fin n → X) (hchain : StationaryFiniteChain μ U)
    (r s : ℕ) :
    (∫ ω, dist (x (U (s + r) ω)) (x (U r ω)) ^ 2 ∂μ) = endpointCost μ U x s := by
  induction r generalizing U with
  | zero => rfl
  | succ r ih =>
    obtain ⟨A, π, hA, hπ, hlaw⟩ := hchain
    have hc : StationaryFiniteChain μ (fun k => U (k + 1)) :=
      ⟨A, π, hA, hπ, stationaryMatrixLaw_tail μ U A π hπ hlaw⟩
    exact (ih (fun k => U (k + 1)) hc).trans
      (endpointCost_tail μ U x ⟨A, π, hA, hπ, hlaw⟩ s)

-- @node: endpointCost_zero
/-- [The expected squared distance from the initial point to itself, namely
the endpoint cost at time zero, is zero](goal). -/
lemma endpointCost_zero (μ : Measure Ω) (U : ℕ → Ω → Fin n) (x : Fin n → X) :
    endpointCost μ U x 0 = 0 := by
  simp [endpointCost]

-- @node: endpointCost_nonneg
/-- [The expected squared distance between the initial point and the point
at any time s is nonnegative](goal). -/
lemma endpointCost_nonneg (μ : Measure Ω) (U : ℕ → Ω → Fin n) (x : Fin n → X)
    (s : ℕ) : 0 ≤ endpointCost μ U x s := by
  exact integral_nonneg fun _ => sq_nonneg _

/-- If [D is nonnegative at every time](hyp:hD) and [its square root is
subadditive](hyp:hsub), then [D at r + s is at most twice D at r plus twice
D at s](goal). -/
-- @node: sqrtSubadditive_two_term_bound
lemma sqrtSubadditive_two_term_bound (D : ℕ → ℝ) (hD : ∀ s, 0 ≤ D s)
    (hsub : Subadditive (fun s => Real.sqrt (D s))) (r s : ℕ) :
    D (r + s) ≤ 2 * D r + 2 * D s := by
  have h := hsub r s
  have hsq : D (r + s) ≤ (Real.sqrt (D r) + Real.sqrt (D s)) ^ 2 := by
    nlinarith [Real.sq_sqrt (hD (r + s)), Real.sqrt_nonneg (D (r + s)),
      Real.sqrt_nonneg (D r), Real.sqrt_nonneg (D s)]
  nlinarith [Real.sq_sqrt (hD r), Real.sq_sqrt (hD s),
    sq_nonneg (Real.sqrt (D r) - Real.sqrt (D s))]

/-- If [D is zero at time zero](hyp:hzero), [D is nonnegative at every
time](hyp:hD), [its square root is subadditive](hyp:hsub), and [t is strictly
positive](hyp:ht), then [D at t is at most four times its average over times
one through t](goal). -/
-- @node: sqrtSubadditive_time_bound
lemma sqrtSubadditive_time_bound (D : ℕ → ℝ) (hzero : D 0 = 0)
    (hD : ∀ s, 0 ≤ D s) (hsub : Subadditive (fun s => Real.sqrt (D s)))
    (t : ℕ) (ht : 0 < t) :
    D t ≤ (4 / (t : ℝ)) * ∑ r ∈ Finset.Icc 1 t, D r := by
  have hreflect : (∑ r ∈ Finset.Icc 1 t, D (t - r)) =
      ∑ r ∈ Finset.range t, D r := by
    apply Finset.sum_bij (fun r _ => t - r)
    · intro r hr
      simp only [Finset.mem_Icc] at hr
      simp only [Finset.mem_range]
      omega
    · intro a ha b hb hab
      simp only [Finset.mem_Icc] at ha hb
      omega
    · intro r hr
      simp only [Finset.mem_range] at hr
      refine ⟨t - r, ?_, ?_⟩
      · simp only [Finset.mem_Icc]
        omega
      · omega
    · intro r hr
      rfl
  have hrange : (∑ r ∈ Finset.range (t + 1), D r) =
      ∑ r ∈ Finset.Icc 1 t, D r := by
    rw [Finset.sum_range_eq_add_Ico D (Nat.succ_pos t), hzero, zero_add]
    congr 1
  have hrem : (∑ r ∈ Finset.Icc 1 t, D (t - r)) ≤
      ∑ r ∈ Finset.Icc 1 t, D r := by
    rw [hreflect, ← hrange, Finset.sum_range_succ]
    exact le_add_of_nonneg_right (hD t)
  have hsum := Finset.sum_le_sum (s := Finset.Icc 1 t) (fun r hr => by
    have hrle := (Finset.mem_Icc.mp hr).2
    simpa [Nat.add_sub_of_le hrle] using
      sqrtSubadditive_two_term_bound D hD hsub r (t - r))
  simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel,
    nsmul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ htR).mpr
  nlinarith

/-- If [D is nonnegative at every time](hyp:hD) and [its square root is
subadditive](hyp:hsub), then [D at j times t plus r is at most twice j squared
times D at t plus twice D at r](goal). -/
-- @node: sqrtSubadditive_block_bound
lemma sqrtSubadditive_block_bound (D : ℕ → ℝ) (hD : ∀ s, 0 ≤ D s)
    (hsub : Subadditive (fun s => Real.sqrt (D s))) (j t r : ℕ) :
    D (j * t + r) ≤ 2 * (j : ℝ) ^ 2 * D t + 2 * D r := by
  have h := hsub.apply_mul_add_le j t r
  have ha : 0 ≤ (j : ℝ) * Real.sqrt (D t) := by positivity
  have hs : D (j * t + r) ≤
      ((j : ℝ) * Real.sqrt (D t) + Real.sqrt (D r)) ^ 2 := by
    nlinarith [Real.sq_sqrt (hD (j * t + r)), Real.sqrt_nonneg (D (j * t + r)),
      Real.sqrt_nonneg (D r)]
  have ht := Real.sq_sqrt (hD t)
  have hr := Real.sq_sqrt (hD r)
  have hmul := congrArg (fun a : ℝ => (j : ℝ) ^ 2 * a) ht
  nlinarith [sq_nonneg ((j : ℝ) * Real.sqrt (D t) - Real.sqrt (D r))]

/-- If [the finite-valued observation V is measurable](hyp:hV) and [the
finite-valued observation W is measurable](hyp:hW), then [every real score
of the pair has a finite second moment under the probability measure μ](goal). -/
-- @node: memLp_finitePair_score
lemma memLp_finitePair_score (μ : Measure Ω) [IsProbabilityMeasure μ]
    (V W : Ω → Fin n) (hV : @Measurable Ω (Fin n) _ ⊤ V)
    (hW : @Measurable Ω (Fin n) _ ⊤ W) (g : Fin n → Fin n → ℝ) :
    MemLp (fun ω => g (V ω) (W ω)) 2 μ := by
  classical
  let : MeasurableSpace (Fin n) := ⊤
  have hm : Measurable (fun ω => g (V ω) (W ω)) := by
    fun_prop
  apply MemLp.of_bound hm.aestronglyMeasurable (∑ i, ∑ j, ‖g i j‖)
  apply Filter.Eventually.of_forall
  intro ω
  exact (Finset.single_le_sum (fun j _ => norm_nonneg (g (V ω) j))
    (Finset.mem_univ (W ω))).trans
    (Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg (g i j))
      (Finset.mem_univ (V ω)))

/-- If [f is square-integrable](hyp:hf) and [g is square-integrable](hyp:hg), [f is everywhere
nonnegative](hyp:hf0), and [g is everywhere nonnegative](hyp:hg0), then
[the square root of the integral of their squared sum is at most the sum of
the square roots of their individual squared integrals](goal). -/
-- @node: sqrt_integral_sq_add_le
lemma sqrt_integral_sq_add_le (μ : Measure Ω) (f g : Ω → ℝ)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hf0 : ∀ ω, 0 ≤ f ω) (hg0 : ∀ ω, 0 ≤ g ω) :
    Real.sqrt (∫ ω, (f ω + g ω) ^ 2 ∂μ) ≤
      Real.sqrt (∫ ω, f ω ^ 2 ∂μ) + Real.sqrt (∫ ω, g ω ^ 2 ∂μ) := by
  have hfg : (∫ ω, f ω * g ω ∂μ) ≤
      Real.sqrt (∫ ω, f ω ^ 2 ∂μ) * Real.sqrt (∫ ω, g ω ^ 2 ∂μ) := by
    have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
      (Filter.Eventually.of_forall hf0) (Filter.Eventually.of_forall hg0)
      (by simpa using hf) (by simpa using hg)
    simpa [Real.sqrt_eq_rpow, Real.rpow_two] using h
  have hexpand : (∫ ω, (f ω + g ω) ^ 2 ∂μ) =
      (∫ ω, f ω ^ 2 ∂μ) + 2 * (∫ ω, f ω * g ω ∂μ) + (∫ ω, g ω ^ 2 ∂μ) := by
    simp_rw [add_sq, mul_assoc]
    have hi : Integrable (fun ω => 2 * (f ω * g ω)) μ := (hf.integrable_mul hg).const_mul 2
    have hi' : Integrable (fun ω => f ω ^ 2 + 2 * (f ω * g ω)) μ := hf.integrable_sq.add hi
    rw [integral_add hi' hg.integrable_sq, integral_add hf.integrable_sq hi,
      integral_const_mul]
  have hsq : (∫ ω, (f ω + g ω) ^ 2 ∂μ) ≤
      (Real.sqrt (∫ ω, f ω ^ 2 ∂μ) + Real.sqrt (∫ ω, g ω ^ 2 ∂μ)) ^ 2 := by
    rw [hexpand]
    nlinarith [Real.sq_sqrt (integral_nonneg (μ := μ) fun ω => sq_nonneg (f ω)),
      Real.sq_sqrt (integral_nonneg (μ := μ) fun ω => sq_nonneg (g ω))]
  exact (Real.sqrt_le_left (by positivity)).mpr hsq

/-- If [U is a stationary finite Markov chain](hyp:hchain), then [the square
root of its expected squared endpoint distance is subadditive in time](goal). -/
-- @node: endpointCost_sqrt_subadditive
lemma endpointCost_sqrt_subadditive (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : ℕ → Ω → Fin n) (x : Fin n → X) (hchain : StationaryFiniteChain μ U) :
    Subadditive (fun s => Real.sqrt (endpointCost μ U x s)) := by
  intro r s
  have hm (a b : ℕ) : MemLp (fun ω => dist (x (U a ω)) (x (U b ω))) 2 μ := by
    obtain ⟨A, π, _, _, hlaw⟩ := hchain
    exact memLp_finitePair_score μ _ _ (hlaw.1 a) (hlaw.1 b) (fun i j => dist (x i) (x j))
  have htri : (∫ ω, dist (x (U (r + s) ω)) (x (U 0 ω)) ^ 2 ∂μ) ≤
      ∫ ω, (dist (x (U (r + s) ω)) (x (U r ω)) +
        dist (x (U r ω)) (x (U 0 ω))) ^ 2 ∂μ := by
    apply integral_mono (hm (r + s) 0).integrable_sq
      ((hm (r + s) r).add (hm r 0)).integrable_sq
    intro ω
    exact pow_le_pow_left₀ (dist_nonneg) (dist_triangle _ _ _) 2
  calc
    _ ≤ Real.sqrt (∫ ω, (dist (x (U (r + s) ω)) (x (U r ω)) +
        dist (x (U r ω)) (x (U 0 ω))) ^ 2 ∂μ) := Real.sqrt_le_sqrt htri
    _ ≤ Real.sqrt (∫ ω, dist (x (U (r + s) ω)) (x (U r ω)) ^ 2 ∂μ) +
        Real.sqrt (endpointCost μ U x r) :=
      sqrt_integral_sq_add_le μ _ _ (hm (r + s) r) (hm r 0)
        (fun _ => dist_nonneg) (fun _ => dist_nonneg)
    _ = _ := by rw [Nat.add_comm r s, endpointCost_shift μ U x hchain r s]; exact add_comm _ _

/-- If [D is zero at time zero](hyp:hzero), [D is nonnegative at every
time](hyp:hD), [its square root is subadditive](hyp:hsub), and [the geometric
time parameter t is strictly positive](hyp:ht), then [the geometric average
of D with the killing and survival probabilities associated with t is at most
28 times the average of D over times one through t](goal). -/
-- @node: geometric_sqrtSubadditive_comparison
lemma geometric_sqrtSubadditive_comparison (D : ℕ → ℝ) (hzero : D 0 = 0)
    (hD : ∀ s, 0 ≤ D s) (hsub : Subadditive (fun s => Real.sqrt (D s)))
    (t : ℕ) (ht : GeometricParameterDomain t) :
    (∑' s : ℕ, geomKillProb t ht * geomSurvProb t ht ^ s * D s) ≤
      (28 / (t : ℝ)) * ∑ s ∈ Finset.Icc 1 t, D s := by
  classical
  let p := geomKillProb t ht
  let q := geomSurvProb t ht
  have hq := geomSurvProb_pos_lt_one t ht
  have hp : 0 ≤ p := by dsimp [p, geomKillProb]; positivity
  have hn : ‖q‖ < 1 := by
    simpa [q, Real.norm_eq_abs, abs_of_pos hq.1] using hq.2
  have hjs : Summable (fun s : ℕ => p * q ^ s * ((s / t : ℕ) : ℝ) ^ 2) := by
    have hmajor := (summable_pow_mul_geometric_of_norm_lt_one 2 hn).mul_left p
    apply hmajor.of_nonneg_of_le
    · intro s
      exact mul_nonneg (mul_nonneg hp (pow_nonneg hq.1.le _)) (sq_nonneg _)
    · intro s
      have hs : ((s / t : ℕ) : ℝ) ≤ s := by exact_mod_cast Nat.div_le_self s t
      have hs2 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (s / t : ℕ)) hs 2
      nlinarith [mul_le_mul_of_nonneg_left hs2 (mul_nonneg hp (pow_nonneg hq.1.le s))]
  have hrs : Summable (fun s : ℕ => p * q ^ s * D (s % t)) := by
    apply summable_geometric_weighted_bounded hq.1.le hq.2 hp _
      (∑ r : Fin t, ‖D r‖)
    intro s
    exact Finset.single_le_sum (fun (r : Fin t) _ => norm_nonneg (D r))
      (Finset.mem_univ (⟨s % t, Nat.mod_lt s ht⟩ : Fin t))
  have hupper := (hjs.mul_left (2 * D t)).add (hrs.mul_left 2)
  have hpoint (s : ℕ) : p * q ^ s * D s ≤
      (2 * D t) * (p * q ^ s * ((s / t : ℕ) : ℝ) ^ 2) +
        2 * (p * q ^ s * D (s % t)) := by
    have hb := sqrtSubadditive_block_bound D hD hsub (s / t) t (s % t)
    rw [Nat.div_add_mod'] at hb
    nlinarith [mul_le_mul_of_nonneg_left hb (mul_nonneg hp (pow_nonneg hq.1.le s))]
  have hds := hupper.of_nonneg_of_le
    (fun s => mul_nonneg (mul_nonneg hp (pow_nonneg hq.1.le s)) (hD s)) hpoint
  calc
    _ ≤ ∑' s : ℕ, ((2 * D t) * (p * q ^ s * ((s / t : ℕ) : ℝ) ^ 2) +
        2 * (p * q ^ s * D (s % t))) := hds.tsum_le_tsum hpoint hupper
    _ = (2 * D t) * (∑' s : ℕ, p * q ^ s * ((s / t : ℕ) : ℝ) ^ 2) +
        2 * (∑' s : ℕ, p * q ^ s * D (s % t)) := by
      rw [(hjs.mul_left (2 * D t)).tsum_add (hrs.mul_left 2),
        tsum_mul_left, tsum_mul_left]
    _ ≤ (2 * D t) * 3 + 2 * ((2 / (t : ℝ)) * ∑ s ∈ Finset.Icc 1 t, D s) :=
      add_le_add (mul_le_mul_of_nonneg_left (geometric_block_secondMoment_bound t ht)
        (mul_nonneg (by norm_num) (hD t))) (mul_le_mul_of_nonneg_left
          (geometric_remainder_sum_bound t ht D hD hzero) (by norm_num))
    _ ≤ _ := by
      have htime := sqrtSubadditive_time_bound D hzero hD hsub t ht
      calc
        _ ≤ (2 * ((4 / (t : ℝ)) * ∑ s ∈ Finset.Icc 1 t, D s)) * 3 +
            2 * ((2 / (t : ℝ)) * ∑ s ∈ Finset.Icc 1 t, D s) := by
          gcongr
        _ = _ := by ring

/-- If [U is a stationary finite Markov chain](hyp:hchain), [t is strictly
positive](hyp:ht), [S is independent of the entire walk](hyp:hind), and [S has
the geometric law associated with t](hyp:hgeom), then [the expected squared
endpoint distance at time S equals the geometric weighted sum of the
fixed-time endpoint costs](goal). -/
-- @node: endpointCost_geometric_mixture
lemma endpointCost_geometric_mixture (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : ℕ → Ω → Fin n) (x : Fin n → X) (t : ℕ) (S : Ω → ℕ)
    (hchain : StationaryFiniteChain μ U) (ht : PositiveTime t)
    (hind : GeometricIndependentOfWalk μ U S) (hgeom : GeometricLaw μ S t ht) :
    (∫ ω, dist (x (U (S ω) ω)) (x (U 0 ω)) ^ 2 ∂μ) =
      ∑' s : ℕ, geomKillProb t ht * geomSurvProb t ht ^ s * endpointCost μ U x s := by
  classical
  let : MeasurableSpace (Fin n) := ⊤
  obtain ⟨A, π, _, _, hlaw⟩ := hchain
  have hU := hlaw.1
  have hS := hgeom.1
  have hV : Measurable (fun ω => U (S ω) ω) := by
    first
    | fun_prop
    | exact
        (measurable_from_prod_countable_left (f := fun a : Ω × ℕ => U a.2 a.1) hU).comp
          (measurable_id.prodMk hS)
  let F : Ω → ℝ := fun ω => dist (x (U (S ω) ω)) (x (U 0 ω)) ^ 2
  have hF : Integrable F μ :=
    (memLp_finitePair_score μ _ _ hV (hU 0) (fun i j => dist (x i) (x j) ^ 2)).integrable
      (by norm_num)
  let E : ℕ → Set Ω := fun s => {ω | S ω = s}
  have hm (s : ℕ) : MeasurableSet (E s) := hS (measurableSet_singleton s)
  have hd : Pairwise (fun i j => Disjoint (E i) (E j)) := by
    intro i j hij
    exact Set.disjoint_left.mpr fun ω hi hj => hij (hi.symm.trans hj)
  have hunion : (⋃ s, E s) = Set.univ := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨S ω, rfl⟩
  have hs (s : ℕ) : (∫ ω in E s, F ω ∂μ) = μ.real (E s) * endpointCost μ U x s := by
    let f : ℕ → ℝ := ({s} : Set ℕ).indicator (fun _ => 1)
    let g : (ℕ → Fin n) → ℝ := fun w => dist (x (w s)) (x (w 0)) ^ 2
    have hf : Measurable f := by fun_prop
    have hg : Measurable g := by
      have hscore : Measurable (fun a : Fin n × Fin n => dist (x a.1) (x a.2) ^ 2) := by
        first | fun_prop | exact measurable_of_countable _
      have hpair : Measurable (fun w : ℕ → Fin n => (w s, w 0)) :=
        (measurable_pi_apply s).prodMk (measurable_pi_apply 0)
      exact hscore.comp hpair
    have hfg := (hind.comp hf hg).integral_fun_mul_eq_mul_integral
      ((hf.comp hS).aestronglyMeasurable)
      ((hg.comp (measurable_pi_iff.mpr hU)).aestronglyMeasurable)
    have heq : (∫ ω, f (S ω) * g (fun k => U k ω) ∂μ) = ∫ ω in E s, F ω ∂μ := by
      rw [← integral_indicator (hm s)]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro ω
      by_cases h : S ω = s
      · simp [f, g, E, F, h]
      · simp [f, E, h]
    simp only [Function.comp_apply] at hfg
    rw [heq] at hfg
    have hfi : (∫ ω, f (S ω) ∂μ) = μ.real (E s) := by
      have he : (fun ω => f (S ω)) = (E s).indicator (fun _ => (1 : ℝ)) := by
        funext ω
        by_cases h : S ω = s <;> simp [f, E, h]
      rw [he, integral_indicator (hm s)]
      simp
    rw [hfi] at hfg
    exact hfg
  calc
    _ = ∫ ω in ⋃ s, E s, F ω ∂μ := by rw [hunion, Measure.restrict_univ]
    _ = ∑' s : ℕ, ∫ ω in E s, F ω ∂μ :=
      integral_iUnion hm hd hF.integrableOn
    _ = _ := by
      apply tsum_congr
      intro s
      rw [hs, hgeom.2 s]

-- @node: lem:comparison
/-- If [U is a stationary finite Markov chain](hyp:h_chain), [the family of
metric-space points has a nonempty state index set](hyp:h_data), [t is strictly
positive](hyp:h_time), [S is independent of the whole walk](hyp:h_independent),
and [S has the geometric law associated with t](hyp:h_geometric), then [the
expected squared distance from the initial point to the point at time S is at
most 28 times the average endpoint cost over times one through t](goal). -/
lemma geometric_endpoint_comparison (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : ℕ → Ω → Fin n) (x : Fin n → X) (t : ℕ) (S : Ω → ℕ)
    (h_chain : StationaryFiniteChain μ U) (h_data : ComparisonData n x)
    (h_time : PositiveTime t) (h_independent : GeometricIndependentOfWalk μ U S)
    (h_geometric : GeometricLaw μ S t h_time) :
    (∫ ω, dist (x (U (S ω) ω)) (x (U 0 ω)) ^ 2 ∂μ) ≤
      (28 / (t : ℝ)) * ∑ s ∈ Finset.Icc 1 t, endpointCost μ U x s := by
  rw [endpointCost_geometric_mixture μ U x t S h_chain h_time h_independent h_geometric]
  exact geometric_sqrtSubadditive_comparison (endpointCost μ U x)
    (endpointCost_zero μ U x) (endpointCost_nonneg μ U x)
    (endpointCost_sqrt_subadditive μ U x h_chain) t h_time

end Papers.OaiMetricMarkovCotype

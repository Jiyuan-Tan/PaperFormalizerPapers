module
public import Papers.TbsNeuralCausalPi.Helpers.EstimationSamplingTolerance
public import Papers.TbsNeuralCausalPi.Helpers.CausalTableMeshSampling
public import Papers.TbsNeuralCausalPi.Helpers.ObservationalSamplingRate
public import Papers.TbsNeuralCausalPi.Helpers.ObservationalCompactConcentration
public import Papers.TbsNeuralCausalPi.Helpers.ObservationalFournierSampling
/-! # Current-representation constraint control from conditional latent tails

The simulation concentration theorem is applied to the actual restricted
architectures and full exogenous draws. The cited conditional joint-latent theorem and the zero-dimensional finite
observation branch supply the observational tail. Both the inverse-square failure
bound and its almost-sure consequence use the prescribed sampling tolerance.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory Filter
open scoped NNReal ENNReal Topology

variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
  {C : Fin b → Set (Fin n)}

-- @node: consistencyGrowth_current_class_sampling_of_compact_latent_tails
/-- Assume [the Anthony–Bartlett packing bound](hyp:hpacking) and [squared-loss
bound](hyp:hsquared). For [output, candidate Lipschitz, and true-mechanism Lipschitz
bounds](hyp:K,L,Ltrue), suppose [the true model's variables satisfy the output
bound](hyp:hK) and [its continuous mechanisms satisfy the true Lipschitz bound](hyp:hL).
With [private-coordinate dimensions for each generator block](hyp:dC), [positive
simulation sizes](hyp:hm), [positive regularization parameters](hyp:hlam), and
[the consistency growth schedule](hyp:hgrowth), take [observed samples](hyp:sample)
and [simulation inputs](hyp:draws) such that [the observations are complete
independent draws from the true law](hyp:hsample) and [the full simulation inputs
are independent draws from their prescribed law](hyp:hsim). If [the categorical
stratum tail constants are nonnegative](hyp:hBobs) and [eventually, in each
positive-probability stratum, the empirical conditional compact latent law has
Wasserstein error within the observational rate except with probability at most
the stratum constant times inverse sample size to the fourth power, whenever
the stratum count is at least half its expectation](hyp:hobs), then [there exist
positive sampling and failure constants such that the probability of any current
restricted candidate violating either population Wasserstein versus empirical
Sinkhorn comparison within the prescribed sampling tolerance is eventually at
most the failure constant times inverse sample size squared, and almost surely
both comparisons hold eventually for every current restricted candidate](goal). -/
lemma consistencyGrowth_current_class_sampling_of_compact_latent_tails
    (hpacking : AnthonyBartlettPacking) (hsquared : AnthonyBartlettSquaredLoss)
    {Omega : Type*} [MeasurableSpace Omega]
    (Q : Measure Omega) [IsProbabilityMeasure Q]
    (M : CanonicalSCM kind dims dag G C) (K L Ltrue : ℝ≥0)
    (hK : VariablesBoundedAt M.toEuclideanSCM K)
    (hL : ContinuousMechanismsLipschitz M.toEuclideanSCM Ltrue)
    {counts : Fin b → ℕ} (F0 : ℕ → StructuralClass kind dims dag C)
    (dC : ∀ j, Fin (counts j) → ℕ) (D c1 c2 : ℕ)
    {dU : ℕ} (m W0 L1 L2 : ℕ → ℕ) (tau lam : ℕ → ℝ)
    (hm : ∀ r, 0 < m r) (hlam : ∀ r, 0 < lam r)
    (hgrowth : ConsistencyGrowthSchedule dU m W0 L1 L2 tau lam)
    (sample : ∀ r, Fin r → Omega → Joint kind)
    (draws : ∀ r, Fin (m r) → Omega → SimulationInput kind counts)
    (hsample : ObservationalSampleCompleteIID Q M.toEuclideanSCM sample)
    (hsim : SimulationDrawsIID Q m draws)
    (Bobs : CategoricalStratum kind → ℝ) (hBobs : ∀ c, 0 ≤ Bobs c)
    (hobs : ∀ᶠ r : ℕ in atTop, ∀ c,
      0 < (observationalLaw M.toEuclideanSCM).real (observedCategoricalStratum ⁻¹' {c}) →
      ∀ N : ℕ, r * (observationalLaw M.toEuclideanSCM).real
          (observedCategoricalStratum ⁻¹' {c}) / 2 ≤ N →
      (Measure.pi (fun _ : Fin N =>
        (categoricalStratumCompactLatentLaw M.toEuclideanSCM K hK c :
          Measure (jointLatentCube dims K))))
        {z | ¬ wasserstein1
          (categoricalStratumCompactLatentLaw M.toEuclideanSCM K hK c :
            Measure (jointLatentCube dims K))
          (empiricalMeasure z) ≤ ENNReal.ofReal (observationalRateScale (∑ j, dims j) r)} ≤
        ENNReal.ofReal (Bobs c * (r : ℝ)^(-(4 : ℤ)))) :
    ∃ cs B : ℝ, 0 < cs ∧ 0 < B ∧
      (∀ᶠ r in atTop,
        Q {w | ∃ R : NCMIn kind dims dag G C counts (F0 r)
            (generatorClassN counts dC K D c1 c2 L1 L2 tau r),
          restrictedCandidate K L R ∧
          let e := sinkhornDivergence (lam r)
            (fun i => jointVector (ncmEval R (draws r i w)))
            (fun i => jointVector (sample r i w)) (uniformWeights (m r)) (uniformWeights r)
          let s := sN cs (∑ j, dims j) m L1 L2 lam r
          ¬ (wasserstein1 (observationalLaw R.canonical.toEuclideanSCM)
              (observationalLaw M.toEuclideanSCM) ≤ ENNReal.ofReal (e + s) ∧
            ENNReal.ofReal (e - s) ≤ wasserstein1
              (observationalLaw R.canonical.toEuclideanSCM)
              (observationalLaw M.toEuclideanSCM))} ≤
          ENNReal.ofReal (B * (r : ℝ)^(-(2 : ℤ)))) ∧
      (∀ᵐ w ∂Q, ∀ᶠ r in atTop,
        ∀ R : NCMIn kind dims dag G C counts (F0 r)
            (generatorClassN counts dC K D c1 c2 L1 L2 tau r),
          restrictedCandidate K L R →
          let e := sinkhornDivergence (lam r)
            (fun i => jointVector (ncmEval R (draws r i w)))
            (fun i => jointVector (sample r i w)) (uniformWeights (m r)) (uniformWeights r)
          let s := sN cs (∑ j, dims j) m L1 L2 lam r
          wasserstein1 (observationalLaw R.canonical.toEuclideanSCM)
              (observationalLaw M.toEuclideanSCM) ≤ ENNReal.ofReal (e + s) ∧
            ENNReal.ofReal (e - s) ≤ wasserstein1
              (observationalLaw R.canonical.toEuclideanSCM)
              (observationalLaw M.toEuclideanSCM)) := by
  classical
  let p0 : ∀ i k, kind i = Sum.inr k → probabilitySimplex k := fun i k hi =>
    ⟨Pi.single ⟨0, M.categoricalPositive i k hi⟩ 1, single_mem_stdSimplex ℝ _⟩
  obtain ⟨A, hA, hsimulation⟩ := consistencyGrowth_uniform_simulation_cubic_tail
    hpacking hsquared M p0 K L F0 dC D c1 c2 m W0 L1 L2 tau lam hgrowth Q draws hsim
  obtain ⟨T, Bo, hT, hBo, hobservation⟩ :=
    canonical_observational_sampling_rate_of_compact_latent_tails
      Q M.toEuclideanSCM K Ltrue hK hL sample
      (fun r i => ((hsample r).2 i).1) (fun r => (hsample r).1)
      (fun r i => ((hsample r).2 i).2) Bobs hBobs hobs
  obtain ⟨cs, B, hcs, hB, hconstraint⟩ :=
    consistencyGrowth_constraint_threshold_of_sampling_tails
      Q M.toEuclideanSCM K L hK F0
      (fun r => generatorClassN counts dC K D c1 c2 L1 L2 tau r)
      m W0 L1 L2 tau lam hm hlam hgrowth sample draws hsample
      A T Bo hA.le hT.le hBo.le hsimulation hobservation
  refine ⟨cs, B, hcs, hB, hconstraint, ?_⟩
  exact estimation_ae_eventually_uniform_constraint_control Q
    (fun _ R => restrictedCandidate K L R)
    (fun _ R => wasserstein1 (observationalLaw R.canonical.toEuclideanSCM)
      (observationalLaw M.toEuclideanSCM))
    (fun r R w => sinkhornDivergence (lam r)
      (fun i => jointVector (ncmEval R (draws r i w)))
      (fun i => jointVector (sample r i w)) (uniformWeights (m r)) (uniformWeights r))
    (sN cs (∑ j, dims j) m L1 L2 lam) B hconstraint

-- @node: consistencyGrowth_current_class_sampling_of_fournier
/-- Assume [the Fournier–Guillin small-deviation bound](hyp:hFournierGuillin_of_gate),
[the Anthony–Bartlett packing bound](hyp:hpacking), and [the Anthony–Bartlett
squared-loss bound](hyp:hsquared). For [output, candidate Lipschitz, and
true-mechanism Lipschitz bounds](hyp:K,L,Ltrue), suppose [the true variables are
bounded by the output bound](hyp:hK), [the true continuous mechanisms satisfy
the true Lipschitz bound](hyp:hL), and [the total latent dimension is positive](hyp:hd).
Given [private-coordinate dimensions for each generator block](hyp:dC),
[positive simulation sizes](hyp:hm), [positive regularization parameters](hyp:hlam),
and [a consistency growth schedule](hyp:hgrowth), let [the observed samples](hyp:sample)
be [complete independent draws from the true observational law](hyp:hsample) and
[the simulation inputs](hyp:draws) be [independent draws from the full prescribed
simulation law](hyp:hsim). Then [positive sampling and failure constants exist
such that, eventually, the probability that any current restricted candidate's
population Wasserstein distance lies outside its empirical Sinkhorn divergence
plus or minus the prescribed sampling tolerance is at most the failure constant
times inverse sample size squared; almost surely, eventually every current
restricted candidate satisfies both comparisons, with real bounds truncated
at zero](goal). -/
lemma consistencyGrowth_current_class_sampling_of_fournier
    (hFournierGuillin_of_gate : FournierGuillinSmallDeviation)
    (hpacking : AnthonyBartlettPacking) (hsquared : AnthonyBartlettSquaredLoss)
    {Omega : Type*} [MeasurableSpace Omega]
    (Q : Measure Omega) [IsProbabilityMeasure Q]
    (M : CanonicalSCM kind dims dag G C) (K L Ltrue : ℝ≥0)
    (hK : VariablesBoundedAt M.toEuclideanSCM K)
    (hL : ContinuousMechanismsLipschitz M.toEuclideanSCM Ltrue)
    {counts : Fin b → ℕ} (F0 : ℕ → StructuralClass kind dims dag C)
    (dC : ∀ j, Fin (counts j) → ℕ) (D c1 c2 : ℕ)
    {dU : ℕ} (m W0 L1 L2 : ℕ → ℕ) (tau lam : ℕ → ℝ)
    (hm : ∀ r, 0 < m r) (hlam : ∀ r, 0 < lam r)
    (hgrowth : ConsistencyGrowthSchedule dU m W0 L1 L2 tau lam)
    (sample : ∀ r, Fin r → Omega → Joint kind)
    (draws : ∀ r, Fin (m r) → Omega → SimulationInput kind counts)
    (hsample : ObservationalSampleCompleteIID Q M.toEuclideanSCM sample)
    (hsim : SimulationDrawsIID Q m draws)
    (hd : 0 < ∑ j, dims j) :
    ∃ cs B : ℝ, 0 < cs ∧ 0 < B ∧
      (∀ᶠ r in atTop,
        Q {w | ∃ R : NCMIn kind dims dag G C counts (F0 r)
            (generatorClassN counts dC K D c1 c2 L1 L2 tau r),
          restrictedCandidate K L R ∧
          let e := sinkhornDivergence (lam r)
            (fun i => jointVector (ncmEval R (draws r i w)))
            (fun i => jointVector (sample r i w)) (uniformWeights (m r)) (uniformWeights r)
          let s := sN cs (∑ j, dims j) m L1 L2 lam r
          ¬ (wasserstein1 (observationalLaw R.canonical.toEuclideanSCM)
              (observationalLaw M.toEuclideanSCM) ≤ ENNReal.ofReal (e + s) ∧
            ENNReal.ofReal (e - s) ≤ wasserstein1
              (observationalLaw R.canonical.toEuclideanSCM)
              (observationalLaw M.toEuclideanSCM))} ≤
          ENNReal.ofReal (B * (r : ℝ)^(-(2 : ℤ)))) ∧
      (∀ᵐ w ∂Q, ∀ᶠ r in atTop,
        ∀ R : NCMIn kind dims dag G C counts (F0 r)
            (generatorClassN counts dC K D c1 c2 L1 L2 tau r),
          restrictedCandidate K L R →
          let e := sinkhornDivergence (lam r)
            (fun i => jointVector (ncmEval R (draws r i w)))
            (fun i => jointVector (sample r i w)) (uniformWeights (m r)) (uniformWeights r)
          let s := sN cs (∑ j, dims j) m L1 L2 lam r
          wasserstein1 (observationalLaw R.canonical.toEuclideanSCM)
              (observationalLaw M.toEuclideanSCM) ≤ ENNReal.ofReal (e + s) ∧
            ENNReal.ofReal (e - s) ≤ wasserstein1
              (observationalLaw R.canonical.toEuclideanSCM)
              (observationalLaw M.toEuclideanSCM)) := by
  obtain ⟨Bobs, rate, hBobs, hrate, hexp⟩ :=
    categoricalStratum_vector_exponential_bound_of_fournier
      hFournierGuillin_of_gate M.toEuclideanSCM K hK hd
  have hobs := categoricalStratum_compact_latent_tails_of_exponential_bound
    M.toEuclideanSCM K hK hd Bobs rate hBobs hrate hexp
  exact consistencyGrowth_current_class_sampling_of_compact_latent_tails
    hpacking hsquared Q M K L Ltrue hK hL F0 dC D c1 c2
    m W0 L1 L2 tau lam hm hlam hgrowth sample draws hsample hsim Bobs hBobs hobs

-- @node: consistencyGrowth_current_class_sampling
/-- Under [the Fournier–Guillin small-deviation bound](hyp:hFournierGuillin_of_gate),
[the Anthony–Bartlett packing bound](hyp:hpacking), and [its squared-loss bound](hyp:hsquared),
fix [output, candidate Lipschitz, and true-mechanism Lipschitz bounds](hyp:K,L,Ltrue)
with [true variables bounded by the output bound](hyp:hK) and [true continuous
mechanisms satisfying the true Lipschitz bound](hyp:hL). For [private-coordinate
dimensions assigned to the generator blocks](hyp:dC), assume [simulation sizes
are positive](hyp:hm), [regularization parameters are positive](hyp:hlam), and
[the consistency growth schedule holds](hyp:hgrowth); take [observed samples](hyp:sample)
that are [complete independent draws from the true observational law](hyp:hsample)
and [simulation inputs](hyp:draws) that are [independent draws from their full
prescribed law](hyp:hsim). Then [there are positive sampling and failure constants
such that, eventually, the probability of either population Wasserstein versus
empirical Sinkhorn comparison failing for any current restricted candidate,
using the prescribed sampling tolerance as slack, is at most the failure constant
times inverse sample size squared, and almost surely both comparisons eventually
hold for every current restricted candidate](goal).

This includes total latent dimension zero. The comparisons bound population
distance above by empirical divergence plus tolerance and below by empirical
divergence minus tolerance, with the real bounds truncated at zero. -/
lemma consistencyGrowth_current_class_sampling
    (hFournierGuillin_of_gate : FournierGuillinSmallDeviation)
    (hpacking : AnthonyBartlettPacking) (hsquared : AnthonyBartlettSquaredLoss)
    {Omega : Type*} [MeasurableSpace Omega]
    (Q : Measure Omega) [IsProbabilityMeasure Q]
    (M : CanonicalSCM kind dims dag G C) (K L Ltrue : ℝ≥0)
    (hK : VariablesBoundedAt M.toEuclideanSCM K)
    (hL : ContinuousMechanismsLipschitz M.toEuclideanSCM Ltrue)
    {counts : Fin b → ℕ} (F0 : ℕ → StructuralClass kind dims dag C)
    (dC : ∀ j, Fin (counts j) → ℕ) (D c1 c2 : ℕ)
    {dU : ℕ} (m W0 L1 L2 : ℕ → ℕ) (tau lam : ℕ → ℝ)
    (hm : ∀ r, 0 < m r) (hlam : ∀ r, 0 < lam r)
    (hgrowth : ConsistencyGrowthSchedule dU m W0 L1 L2 tau lam)
    (sample : ∀ r, Fin r → Omega → Joint kind)
    (draws : ∀ r, Fin (m r) → Omega → SimulationInput kind counts)
    (hsample : ObservationalSampleCompleteIID Q M.toEuclideanSCM sample)
    (hsim : SimulationDrawsIID Q m draws) :
    ∃ cs B : ℝ, 0 < cs ∧ 0 < B ∧
      (∀ᶠ r in atTop,
        Q {w | ∃ R : NCMIn kind dims dag G C counts (F0 r)
            (generatorClassN counts dC K D c1 c2 L1 L2 tau r),
          restrictedCandidate K L R ∧
          let e := sinkhornDivergence (lam r)
            (fun i => jointVector (ncmEval R (draws r i w)))
            (fun i => jointVector (sample r i w)) (uniformWeights (m r)) (uniformWeights r)
          let s := sN cs (∑ j, dims j) m L1 L2 lam r
          ¬ (wasserstein1 (observationalLaw R.canonical.toEuclideanSCM)
              (observationalLaw M.toEuclideanSCM) ≤ ENNReal.ofReal (e + s) ∧
            ENNReal.ofReal (e - s) ≤ wasserstein1
              (observationalLaw R.canonical.toEuclideanSCM)
              (observationalLaw M.toEuclideanSCM))} ≤
          ENNReal.ofReal (B * (r : ℝ)^(-(2 : ℤ)))) ∧
      (∀ᵐ w ∂Q, ∀ᶠ r in atTop,
        ∀ R : NCMIn kind dims dag G C counts (F0 r)
            (generatorClassN counts dC K D c1 c2 L1 L2 tau r),
          restrictedCandidate K L R →
          let e := sinkhornDivergence (lam r)
            (fun i => jointVector (ncmEval R (draws r i w)))
            (fun i => jointVector (sample r i w)) (uniformWeights (m r)) (uniformWeights r)
          let s := sN cs (∑ j, dims j) m L1 L2 lam r
          wasserstein1 (observationalLaw R.canonical.toEuclideanSCM)
              (observationalLaw M.toEuclideanSCM) ≤ ENNReal.ofReal (e + s) ∧
            ENNReal.ofReal (e - s) ≤ wasserstein1
              (observationalLaw R.canonical.toEuclideanSCM)
              (observationalLaw M.toEuclideanSCM)) := by
  classical
  let p0 : ∀ i k, kind i = Sum.inr k → probabilitySimplex k := fun i k hi =>
    ⟨Pi.single ⟨0, M.categoricalPositive i k hi⟩ 1, single_mem_stdSimplex ℝ _⟩
  obtain ⟨A, hA, hsimulation⟩ := consistencyGrowth_uniform_simulation_cubic_tail
    hpacking hsquared M p0 K L F0 dC D c1 c2 m W0 L1 L2 tau lam hgrowth Q draws hsim
  obtain ⟨T, Bo, hT, hBo, hobservation⟩ :=
    canonical_observational_sampling_rate_of_fournier
      hFournierGuillin_of_gate Q M.toEuclideanSCM K Ltrue hK hL sample
      (fun r i => ((hsample r).2 i).1) (fun r => (hsample r).1)
      (fun r i => ((hsample r).2 i).2)
  obtain ⟨cs, B, hcs, hB, hconstraint⟩ :=
    consistencyGrowth_constraint_threshold_of_sampling_tails
      Q M.toEuclideanSCM K L hK F0
      (fun r => generatorClassN counts dC K D c1 c2 L1 L2 tau r)
      m W0 L1 L2 tau lam hm hlam hgrowth sample draws hsample
      A T Bo hA.le hT.le hBo.le hsimulation hobservation
  refine ⟨cs, B, hcs, hB, hconstraint, ?_⟩
  exact estimation_ae_eventually_uniform_constraint_control Q
    (fun _ R => restrictedCandidate K L R)
    (fun _ R => wasserstein1 (observationalLaw R.canonical.toEuclideanSCM)
      (observationalLaw M.toEuclideanSCM))
    (fun r R w => sinkhornDivergence (lam r)
      (fun i => jointVector (ncmEval R (draws r i w)))
      (fun i => jointVector (sample r i w)) (uniformWeights (m r)) (uniformWeights r))
    (sN cs (∑ j, dims j) m L1 L2 lam) B hconstraint

end Papers.TbsNeuralCausalPi

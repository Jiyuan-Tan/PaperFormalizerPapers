module
public import Papers.TbsNeuralCausalPi.Helpers.EstimationCurrentClassSampling
public import Papers.TbsNeuralCausalPi.Helpers.BoundedObservationalTransport
/-! # Construction and sampling thresholds for consistency -/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
set_option linter.unusedVariables false
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
noncomputable section
variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
  {C : Fin b → Set (Fin n)}
variable {Omega : Type*} [MeasurableSpace Omega]

-- @node: consistency_tolerance_thresholds_from_constructions
/-- Given [structural regularity and support bounds L and K](hyp:L,K),
[latent chart domains](hyp:sets), [chart dimensions](hyp:dC), [a chart Lipschitz bound](hyp:Lchart),
and [the model's architecture construction premises](hyp:hmodel), assume
[quantized generation](hyp:hPerekrestenko_of_gate),
[coordinate approximation](hyp:hYarotskyCoordinate_of_gate),
[structural approximation](hyp:hYarotskyStructural_of_gate),
[packing bounds](hyp:hAnthonyBartlettPacking_of_gate),
[squared-loss complexity bounds](hyp:hAnthonyBartlettSquaredLoss_of_gate), and
[small-deviation concentration](hyp:hFournierGuillin_of_gate).
If [the architecture thresholds are valid](hyp:ha), [the architecture factors meet those thresholds](hyp:hfactors),
[simulation counts](hyp:hm), [temperatures](hyp:htau), and [regularization levels](hyp:hlam) are positive,
and [the schedules satisfy the consistency growth conditions](hyp:hgrowth), then for
[observational samples](hyp:sample) and [simulation draws](hyp:draws) that are
[complete and identically and independently distributed under the model](hyp:hsample),
[identically and independently distributed simulation inputs](hyp:hsim), and
[independent of one another](hyp:hsimind), with [positive maximum structural input dimension](hyp:hdin)
and [positive maximum latent dimension](hyp:hdU),
[there are two positive tolerance constants: eventually a restricted neural candidate approximates the observational law within the first tolerance rate, and the probability that any restricted candidate violates the population-to-empirical transport bounds with the second tolerance rate is eventually at most a positive constant times the inverse square of sample size](goal). -/
lemma consistency_tolerance_thresholds_from_constructions
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (M : CanonicalSCM kind dims dag G C) (L K : ℝ≥0)
    (counts : Fin b → ℕ) (sets : ∀ j, Fin (counts j) → Set (L1Vec (dims j)))
    (dC : ∀ j, Fin (counts j) → ℕ) (Lchart : ℝ≥0)
    (hmodel : ArchitectureConstructionPremises M L K counts sets dC Lchart)
    (c0 c1 c2 : ℕ)
    (hPerekrestenko_of_gate : PerekrestenkoQuantizedGeneration)
    (hYarotskyCoordinate_of_gate : YarotskyCoordinateApprox)
    (hYarotskyStructural_of_gate : YarotskyStructuralApprox)
    (hAnthonyBartlettPacking_of_gate : AnthonyBartlettPacking)
    (hAnthonyBartlettSquaredLoss_of_gate : AnthonyBartlettSquaredLoss)
    (hFournierGuillin_of_gate : FournierGuillinSmallDeviation)
    (a0 a1 a2 : ℕ)
    (ha : ArchitectureConstructionThresholds M K (LhatF M.toEuclideanSCM L)
      counts dC a0 a1 a2)
    (hfactors : ArchitectureFactorSelection a0 a1 a2 c0 c1 c2)
    (m W0 L1 L2 : ℕ → ℕ) (tau lam : ℕ → ℝ)
    (hm : ∀ r, 0 < m r) (htau : TemperaturesPositive tau) (hlam : ∀ r, 0 < lam r)
    (hgrowth : ConsistencyGrowthSchedule (maxLatentDim M.toEuclideanSCM) m W0 L1 L2 tau lam)
    (sample : ∀ r, Fin r → Omega → Joint kind)
    (draws : ∀ r, Fin (m r) → Omega → SimulationInput kind counts)
    (hsample : ObservationalSampleCompleteIID mu M.toEuclideanSCM sample)
    (hsim : SimulationDrawsIID mu m draws)
    (hsimind : SimulationIndependentOfSample mu m sample draws)
    (hdin : 0 < maxInDim M.toEuclideanSCM) (hdU : 0 < maxLatentDim M.toEuclideanSCM) :
    ∃ thresholds : ℝ × ℝ, 0 < thresholds.1 ∧ 0 < thresholds.2 ∧
      (∀ᶠ r in atTop,
        ∃ R : NCMIn kind dims dag G C counts
          (structuralClassN M K (LhatF M.toEuclideanSCM L) W0 c0 r)
          (generatorClassN counts dC K (maxLatentDim M.toEuclideanSCM) c1 c2 L1 L2 tau r),
          restrictedCandidate K (LhatF M.toEuclideanSCM L) R ∧
          wasserstein1 (observationalLaw R.canonical.toEuclideanSCM)
            (observationalLaw M.toEuclideanSCM) ≤
            ENNReal.ofReal (epsN thresholds.1 (maxInDim M.toEuclideanSCM)
              (maxLatentDim M.toEuclideanSCM) hdin hdU W0 L1 L2 tau r)) ∧
      (∃ B : ℝ, 0 < B ∧ ∀ᶠ r in atTop,
        mu {w | ∃ R : NCMIn kind dims dag G C counts
          (structuralClassN M K (LhatF M.toEuclideanSCM L) W0 c0 r)
          (generatorClassN counts dC K (maxLatentDim M.toEuclideanSCM) c1 c2 L1 L2 tau r),
          restrictedCandidate K (LhatF M.toEuclideanSCM L) R ∧
          let empirical := sinkhornDivergence (lam r)
            (fun i => jointVector (ncmEval R (draws r i w)))
            (fun i => jointVector (sample r i w)) (uniformWeights (m r)) (uniformWeights r)
          let population := wasserstein1 (observationalLaw R.canonical.toEuclideanSCM)
            (observationalLaw M.toEuclideanSCM)
          let slack := sN thresholds.2 (∑ j, dims j) m L1 L2 lam r
          ¬ (population ≤ ENNReal.ofReal (empirical + slack) ∧
            ENNReal.ofReal (empirical - slack) ≤ population)} ≤
          ENNReal.ofReal (B * (r : ℝ)^(-(2 : ℤ)))) := by
  obtain ⟨A, hA, hparameterApprox⟩ := consistencyGrowth_eventually_parameter_approximation
    M K (LhatF M.toEuclideanSCM L) counts dC a0 a1 a2 c0 c1 c2 ha hfactors
    m W0 L1 L2 tau lam htau hgrowth hdin hdU
  obtain ⟨Q, hQ, htransport⟩ := bounded_observational_wasserstein_bound_left
    (kind := kind) (dims := dims) (dag := dag) (G := G) (C := C) (LhatF M.toEuclideanSCM L)
  obtain ⟨cs, B, hcs, hB, hsampling, _⟩ := consistencyGrowth_current_class_sampling
    hFournierGuillin_of_gate hAnthonyBartlettPacking_of_gate
    hAnthonyBartlettSquaredLoss_of_gate mu M K (LhatF M.toEuclideanSCM L) L
    hmodel.2.2.2.1 hmodel.2.2.2.2.2.2.2.1
    (fun r => structuralClassN M K (LhatF M.toEuclideanSCM L) W0 c0 r)
    dC (maxLatentDim M.toEuclideanSCM) c1 c2 m W0 L1 L2 tau lam
    hm hlam hgrowth sample draws hsample hsim
  refine ⟨((Q : ℝ) * A, cs), mul_pos (by exact_mod_cast hQ) hA, hcs, ?_,
    ⟨B, hB, hsampling⟩⟩
  obtain ⟨hw, ht, _⟩ := consistencyGrowth_width_temperature_bias hgrowth
  filter_upwards [hparameterApprox, hw.eventually (eventually_gt_atTop (0 : ℝ)),
    ht.eventually (gt_mem_nhds zero_lt_one)] with r hr hwr htr
  obtain ⟨R, hR, herr⟩ := hr
  refine ⟨R, hR, ?_⟩
  have hrate : 0 < (W0 r : ℝ)^(-(1 : ℝ) / maxInDim M.toEuclideanSCM) +
      (L1 r : ℝ)^(-(2 : ℝ) / maxLatentDim M.toEuclideanSCM) +
      (L2 r : ℝ)^(-(2 : ℝ) / maxLatentDim M.toEuclideanSCM) +
      tau r * (1 - Real.log (tau r)) := by
    have hg : 0 ≤ tau r * (1 - Real.log (tau r)) :=
      mul_nonneg (htau r).le (by
        have hl := Real.log_nonpos (htau r).le htr.le
        linarith)
    have hwpos := Real.rpow_pos_of_pos hwr (-(1 : ℝ) / maxInDim M.toEuclideanSCM)
    have h1pos := Real.rpow_nonneg (Nat.cast_nonneg (L1 r) : (0 : ℝ) ≤ L1 r)
      (-(2 : ℝ) / maxLatentDim M.toEuclideanSCM)
    have h2pos := Real.rpow_nonneg (Nat.cast_nonneg (L2 r) : (0 : ℝ) ≤ L2 r)
      (-(2 : ℝ) / maxLatentDim M.toEuclideanSCM)
    linarith
  have hscale : (Q : ℝ≥0∞) * ENNReal.ofReal
      (epsN A _ _ hdin hdU W0 L1 L2 tau r) =
      ENNReal.ofReal (epsN ((Q : ℝ) * A) _ _ hdin hdU W0 L1 L2 tau r) := by
    unfold epsN
    rw [if_pos (mul_pos hA hrate),
      if_pos (mul_pos (mul_pos (by exact_mod_cast hQ) hA) hrate)]
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul Q.coe_nonneg]
    congr 1
    ring
  have h := (htransport M R.canonical K hmodel.2.2.2.1
    (fun i => (hR i).1)).trans (mul_le_mul' le_rfl herr)
  rw [hscale] at h
  have hsymm : wasserstein1 (observationalLaw R.canonical.toEuclideanSCM)
      (observationalLaw M.toEuclideanSCM) =
      wasserstein1 (observationalLaw M.toEuclideanSCM)
        (observationalLaw R.canonical.toEuclideanSCM) := by
    simpa only [ProbabilityMeasure.coe_mk] using wasserstein1_symm
      (⟨observationalLaw R.canonical.toEuclideanSCM,
        observationalLaw_probability R.canonical.toEuclideanSCM⟩ : ProbabilityMeasure (Joint kind))
      (⟨observationalLaw M.toEuclideanSCM,
        observationalLaw_probability M.toEuclideanSCM⟩ : ProbabilityMeasure (Joint kind))
  exact hsymm.trans_le h

/-- For [a sampling probability measure mu](hyp:mu) on [the sampling space Omega](hyp:Omega),
[a canonical causal model M](hyp:M) with [n nodes](hyp:n), [b latent blocks](hyp:b),
[node types](hyp:kind), [latent dimensions](hyp:dims), [directed graph](hyp:dag),
[bidirected graph](hyp:G), and [latent component incidence](hyp:C),
[structural regularity and support bounds L and K](hyp:L,K),
[chart counts](hyp:counts), [chart domains](hyp:sets), [chart dimensions](hyp:dC),
and [a chart Lipschitz bound](hyp:Lchart) satisfying [the architecture construction premises](hyp:hmodel),
the [selected pair of positive approximation and sampling tolerance thresholds](goal)
is chosen from the construction and concentration result using
[architecture factors c0, c1, and c2](hyp:c0,c1,c2),
[quantized generation](hyp:hPerekrestenko_of_gate), [coordinate approximation](hyp:hYarotskyCoordinate_of_gate),
[structural approximation](hyp:hYarotskyStructural_of_gate), [packing bounds](hyp:hAnthonyBartlettPacking_of_gate),
[squared-loss complexity bounds](hyp:hAnthonyBartlettSquaredLoss_of_gate),
[small-deviation concentration](hyp:hFournierGuillin_of_gate),
[construction thresholds a0, a1, and a2](hyp:a0,a1,a2) [valid for this model](hyp:ha),
and [factors satisfying those thresholds](hyp:hfactors).
The choice also uses [simulation count and network width and depth schedules](hyp:m,W0,L1,L2),
[temperature and regularization schedules](hyp:tau,lam),
[positive simulation counts](hyp:hm), [positive temperatures](hyp:htau),
[positive regularization levels](hyp:hlam), [the consistency growth conditions](hyp:hgrowth),
[observational samples](hyp:sample), [simulation draws](hyp:draws),
[complete identically and independently distributed observational sampling](hyp:hsample),
[identically and independently distributed simulation inputs](hyp:hsim),
[independence between sampling and simulation](hyp:hsimind),
[positive maximum structural input dimension](hyp:hdin), and [positive maximum latent dimension](hyp:hdU). -/
def selectedConsistencyToleranceThresholds
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (M : CanonicalSCM kind dims dag G C) (L K : ℝ≥0)
    (counts : Fin b → ℕ) (sets : ∀ j, Fin (counts j) → Set (L1Vec (dims j)))
    (dC : ∀ j, Fin (counts j) → ℕ) (Lchart : ℝ≥0)
    (hmodel : ArchitectureConstructionPremises M L K counts sets dC Lchart)
    (c0 c1 c2 : ℕ)
    (hPerekrestenko_of_gate : PerekrestenkoQuantizedGeneration)
    (hYarotskyCoordinate_of_gate : YarotskyCoordinateApprox)
    (hYarotskyStructural_of_gate : YarotskyStructuralApprox)
    (hAnthonyBartlettPacking_of_gate : AnthonyBartlettPacking)
    (hAnthonyBartlettSquaredLoss_of_gate : AnthonyBartlettSquaredLoss)
    (hFournierGuillin_of_gate : FournierGuillinSmallDeviation)
    (a0 a1 a2 : ℕ)
    (ha : ArchitectureConstructionThresholds M K (LhatF M.toEuclideanSCM L)
      counts dC a0 a1 a2)
    (hfactors : ArchitectureFactorSelection a0 a1 a2 c0 c1 c2)
    (m W0 L1 L2 : ℕ → ℕ) (tau lam : ℕ → ℝ)
    (hm : ∀ r, 0 < m r) (htau : TemperaturesPositive tau) (hlam : ∀ r, 0 < lam r)
    (hgrowth : ConsistencyGrowthSchedule (maxLatentDim M.toEuclideanSCM) m W0 L1 L2 tau lam)
    (sample : ∀ r, Fin r → Omega → Joint kind)
    (draws : ∀ r, Fin (m r) → Omega → SimulationInput kind counts)
    (hsample : ObservationalSampleCompleteIID mu M.toEuclideanSCM sample)
    (hsim : SimulationDrawsIID mu m draws)
    (hsimind : SimulationIndependentOfSample mu m sample draws)
    (hdin : 0 < maxInDim M.toEuclideanSCM) (hdU : 0 < maxLatentDim M.toEuclideanSCM) : ℝ × ℝ :=
  Classical.choose (consistency_tolerance_thresholds_from_constructions
    mu M L K counts sets dC Lchart hmodel c0 c1 c2
    hPerekrestenko_of_gate hYarotskyCoordinate_of_gate hYarotskyStructural_of_gate hAnthonyBartlettPacking_of_gate hAnthonyBartlettSquaredLoss_of_gate hFournierGuillin_of_gate a0 a1 a2 ha hfactors
    m W0 L1 L2 tau lam hm htau hlam hgrowth sample draws hsample hsim hsimind hdin hdU)

end
end Papers.TbsNeuralCausalPi

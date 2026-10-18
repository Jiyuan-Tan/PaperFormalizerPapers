module
public import Papers.TbsNeuralCausalPi.Helpers.StructuralCompactness
public import Papers.TbsNeuralCausalPi.Helpers.EstimationCompactness
/-! # Sequential lower bounds in the population parameter distance

The compactness step uses the concrete `paramDist` subsequence theorem directly.
The continuity and population-error estimates remain explicit inputs: neither
the causal transport estimate nor the sampling estimate is asserted here.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory Filter
open scoped NNReal ENNReal Topology

/-- Suppose [every parameter sequence has a subsequence converging in the given distance](hyp:hcompact),
[the objective is sequentially continuous in that distance](hyp:hf),
[the constraint function is sequentially continuous in that distance](hyp:hg),
[the constraint is nonnegative](hyp:hgnonneg), and [the constraint thresholds tend to zero](hyp:hbeta).
If [the proposed lower bound bounds the objective whenever the constraint is zero](hyp:hlower)
and [a real number lies strictly below that bound](hyp:hc), then
[eventually every parameter satisfying the threshold constraint has objective strictly above that number](goal). -/
-- @node: estimation_sequential_eventually_lower
lemma estimation_sequential_eventually_lower
    {P : Type*} (d : P → P → ℝ) (f g : P → ℝ) (beta : ℕ → ℝ)
    (hcompact : ∀ x : ℕ → P, ∃ q : P, ∃ phi : ℕ → ℕ,
      StrictMono phi ∧ Tendsto (fun r => d (x (phi r)) q) atTop (𝓝 0))
    (hf : ∀ (x : ℕ → P) q, Tendsto (fun r => d (x r) q) atTop (𝓝 0) →
      Tendsto (fun r => f (x r)) atTop (𝓝 (f q)))
    (hg : ∀ (x : ℕ → P) q, Tendsto (fun r => d (x r) q) atTop (𝓝 0) →
      Tendsto (fun r => g (x r)) atTop (𝓝 (g q)))
    (hgnonneg : ∀ q, 0 ≤ g q) (hbeta : Tendsto beta atTop (𝓝 0))
    (lower : EReal) (hlower : ∀ q, g q = 0 → lower ≤ (f q : EReal))
    {c : ℝ} (hc : (c : EReal) < lower) :
    ∀ᶠ r in atTop, ∀ q, g q ≤ beta r → c < f q := by
  classical
  by_contra h
  have hbad : ∃ᶠ r in atTop, ∃ q, g q ≤ beta r ∧ f q ≤ c := by
    have hfreq : ∃ᶠ r in atTop, ¬ (∀ q, g q ≤ beta r → c < f q) := by
      simpa only [Filter.Frequently, not_not] using h
    exact hfreq.mono (fun _ hr => by
      simpa only [not_forall, Classical.not_imp, not_lt, exists_prop] using hr)
  obtain ⟨s, hs, hbad⟩ := extraction_of_frequently_atTop hbad
  choose x hxg hxf using hbad
  obtain ⟨q, phi, hphi, hdist⟩ := hcompact x
  have hindices : Tendsto (fun r => s (phi r)) atTop atTop :=
    hs.tendsto_atTop.comp hphi.tendsto_atTop
  have hz : Tendsto (fun r => g (x (phi r))) atTop (𝓝 0) :=
    squeeze_zero (fun r => hgnonneg _) (fun r => hxg (phi r)) (hbeta.comp hindices)
  have hgq : g q = 0 := tendsto_nhds_unique (hg _ q hdist) hz
  have hfq : f q ≤ c := le_of_tendsto' (hf _ q hdist) (fun r => hxf (phi r))
  exact (not_lt_of_ge ((hlower q hgq).trans (EReal.coe_le_coe_iff.mpr hfq))) hc

/-- For [a sequence of maps from representations to parameters](hyp:p),
[admissibility criteria](hyp:admissible), and [feasibility criteria](hyp:feasible), suppose
[every parameter sequence has a distance-convergent subsequence](hyp:hcompact),
[the objective is sequentially continuous in that distance](hyp:hf),
[the constraint function is sequentially continuous in that distance](hyp:hg),
[the constraint is nonnegative](hyp:hgnonneg), and [the thresholds tend to zero](hyp:hbeta).
If [the proposed lower bound bounds the objective on the zero-constraint set](hyp:hlower)
and [eventually every admissible, feasible representation has constraint at most its threshold](hyp:hcontrol),
then [the lower bound is at most the lower limit of the objective infima over admissible, feasible representations](goal).

Empty feasible classes and arbitrary finite prefixes are allowed. -/
-- @node: estimation_sequential_le_liminf_representation_iInf
lemma estimation_sequential_le_liminf_representation_iInf
    {P : Type*} {A : ℕ → Type*} (p : ∀ r, A r → P)
    (admissible feasible : ∀ r, A r → Prop)
    (d : P → P → ℝ) (f g : P → ℝ) (beta : ℕ → ℝ)
    (hcompact : ∀ x : ℕ → P, ∃ q : P, ∃ phi : ℕ → ℕ,
      StrictMono phi ∧ Tendsto (fun r => d (x (phi r)) q) atTop (𝓝 0))
    (hf : ∀ (x : ℕ → P) q, Tendsto (fun r => d (x r) q) atTop (𝓝 0) →
      Tendsto (fun r => f (x r)) atTop (𝓝 (f q)))
    (hg : ∀ (x : ℕ → P) q, Tendsto (fun r => d (x r) q) atTop (𝓝 0) →
      Tendsto (fun r => g (x r)) atTop (𝓝 (g q)))
    (hgnonneg : ∀ q, 0 ≤ g q) (hbeta : Tendsto beta atTop (𝓝 0))
    (lower : EReal) (hlower : ∀ q, g q = 0 → lower ≤ (f q : EReal))
    (hcontrol : ∀ᶠ r in atTop, ∀ a, admissible r a → feasible r a →
      g (p r a) ≤ beta r) :
    lower ≤ liminf (fun r => ⨅ a : A r, ⨅ (_ : admissible r a),
      ⨅ (_ : feasible r a), (f (p r a) : EReal)) atTop := by
  apply (le_liminf_iff').mpr
  intro y hy
  induction y using EReal.rec with
  | bot => exact Eventually.of_forall (fun _ => bot_le)
  | top => exact False.elim (not_lt_of_ge le_top hy)
  | coe c =>
    filter_upwards [estimation_sequential_eventually_lower d f g beta
      hcompact hf hg hgnonneg hbeta lower hlower hy, hcontrol] with r hr hrc
    exact le_iInf (fun a => le_iInf (fun ha => le_iInf (fun hfeas =>
      EReal.coe_le_coe_iff.mpr (hr (p r a) (hrc a ha hfeas)).le)))

variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
  {C : Fin b → Set (Fin n)}

/-- For [structural and generator regularity bounds](hyp:K,L),
[observed samples at each sample size](hyp:sample), [simulation draws at each stage](hyp:draws),
and [maps from neural causal models to population parameters](hyp:p), assume
[the restricted empirical objectives are well defined at every stage](hyp:hdefined),
[the population objective is sequentially continuous in the population parameter distance](hyp:hf),
[the population constraint is sequentially continuous in that distance](hyp:hg),
[the constraint is nonnegative](hyp:hgnonneg), and
[its thresholds tend to zero](hyp:hbeta).
If [the proposed lower bound bounds the objective on the zero-constraint set](hyp:hlower),
[the population objective agrees with each model's intervention objective](hyp:hobjective), and
[eventually restricted models satisfying the empirical Sinkhorn constraint satisfy the population threshold constraint](hyp:hcontrol),
then [the lower limit of the restricted empirical partial-identification values is at least the proposed lower bound](goal). -/
-- @node: restrictedEmpiricalPIValue_liminf_ge_of_paramDist_control
lemma restrictedEmpiricalPIValue_liminf_ge_of_paramDist_control
    {counts : Fin b → ℕ}
    (F0 : ℕ → StructuralClass kind dims dag C) (F1 : ℕ → GeneratorClass dims counts)
    (K L : ℝ≥0) {I : Type*} [MeasurableSpace I]
    (t : I → LawIntervention kind) (muT : Measure I) [IsProbabilityMeasure muT] (F : Joint kind → ℝ)
    (hdefined : ∀ r, empiricalObjectivesDefined (G := G) (F0 r) (F1 r)
      (restrictedCandidate K L) t muT F)
    (m : ℕ → ℕ) (sample : ∀ r, Fin r → Joint kind)
    (draws : ∀ r, Fin (m r) → SimulationInput kind counts)
    (lam alpha beta : ℕ → ℝ)
    (p : ∀ r, NCMIn kind dims dag G C counts (F0 r) (F1 r) →
      PopulationParam kind dims dag C K L)
    (f g : PopulationParam kind dims dag C K L → ℝ)
    (hf : ∀ (x : ℕ → PopulationParam kind dims dag C K L) q,
      Tendsto (fun r => paramDist (x r) q) atTop (𝓝 0) →
      Tendsto (fun r => f (x r)) atTop (𝓝 (f q)))
    (hg : ∀ (x : ℕ → PopulationParam kind dims dag C K L) q,
      Tendsto (fun r => paramDist (x r) q) atTop (𝓝 0) →
      Tendsto (fun r => g (x r)) atTop (𝓝 (g q)))
    (hgnonneg : ∀ q, 0 ≤ g q) (hbeta : Tendsto beta atTop (𝓝 0))
    (lower : EReal) (hlower : ∀ q, g q = 0 → lower ≤ (f q : EReal))
    (hobjective : ∀ r R, f (p r R) = objectiveIntegral R.canonical.toEuclideanSCM t muT F)
    (hcontrol : ∀ᶠ r in atTop,
      ∀ R : NCMIn kind dims dag G C counts (F0 r) (F1 r),
      restrictedCandidate K L R →
      sinkhornDivergence (lam r) (fun i => jointVector (ncmEval R (draws r i)))
        (fun i => jointVector (sample r i)) (uniformWeights (m r)) (uniformWeights r) ≤
          alpha r → g (p r R) ≤ beta r) :
    lower ≤ liminf (fun r => restrictedEmpiricalPIValue (G := G) (F0 r) (F1 r)
      K L t muT F (sample r) (draws r) (lam r) (alpha r) (hdefined r)) atTop := by
  have h := estimation_sequential_le_liminf_representation_iInf p
    (fun _ => restrictedCandidate K L)
    (fun r R => sinkhornDivergence (lam r) (fun i => jointVector (ncmEval R (draws r i)))
      (fun i => jointVector (sample r i)) (uniformWeights (m r)) (uniformWeights r) ≤ alpha r)
    paramDist f g beta (estimation_population_paramDist_subsequence K L)
    hf hg hgnonneg hbeta lower hlower hcontrol
  simpa only [hobjective, restrictedEmpiricalPIValue, empiricalPIValueOn, empiricalLawSinkhorn,
    trueObjective, finiteIteratedObjective, objectiveIntegral] using h

end Papers.TbsNeuralCausalPi

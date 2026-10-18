module
public import Papers.TbsNeuralCausalPi.Helpers.ConvgOpt
/-! # Compactness lower bounds for representation-based empirical infima

Only population parameters live in the compact space. The empirical constraint
may depend on the representation, and its infimum need not be attained. All
control hypotheses are eventual, permitting the arbitrary finite prefixes in
the consistency theorem.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory Filter
open scoped NNReal ENNReal Topology

variable {P : Type*} [MetricSpace P]

-- @node: estimation_compact_sublevel_eventually_lower
/-- If [the parameter set is compact](hyp:hcompact), [the objective](hyp:hf) and
[constraint error](hyp:hg) are continuous on it, [the error is nonnegative](hyp:hgnonneg)
and [vanishes somewhere in the set](hyp:hzero), and [the error tolerances converge
to zero](hyp:hbeta), then for [any number strictly below the minimum objective
under zero error](hyp:hc), [eventually every parameter in the set whose error is
within tolerance has objective strictly above that number](goal). -/
lemma estimation_compact_sublevel_eventually_lower
    (S : Set P) (f g : P → ℝ) (beta : ℕ → ℝ)
    (hcompact : IsCompact S) (hf : ContinuousOn f S) (hg : ContinuousOn g S)
    (hgnonneg : ∀ p ∈ S, 0 ≤ g p)
    (hzero : ∃ p ∈ S, g p = 0)
    (hbeta : Tendsto beta atTop (𝓝 0)) {c : ℝ}
    (hc : c < convgOptLimitValue f S g) :
    ∀ᶠ r in atTop, ∀ p ∈ S, g p ≤ beta r → c < f p := by
  classical
  obtain ⟨p0, hp0, hg0⟩ := hzero
  have hmin : ∀ r, ∃ p ∈ {p ∈ S | g p ≤ max 0 (beta r)},
      IsMinOn f {p ∈ S | g p ≤ max 0 (beta r)} p := by
    intro r
    have hclosed : IsClosed {p ∈ S | g p ≤ max 0 (beta r)} :=
      hcompact.isClosed.isClosed_le hg continuousOn_const
    have hsubcompact : IsCompact {p ∈ S | g p ≤ max 0 (beta r)} :=
      hcompact.of_isClosed_subset hclosed (fun _ hp => hp.1)
    exact hsubcompact.exists_isMinOn
      ⟨p0, hp0, hg0 ▸ le_max_left _ _⟩ (hf.mono (fun _ hp => hp.1))
  choose p hp hpm using hmin
  have hmax : Tendsto (fun r => max 0 (beta r)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (0 : ℝ))).max hbeta
  filter_upwards [convgOpt_eventually_lower S f g p (fun r => max 0 (beta r))
    hcompact hf hg hgnonneg (fun r => (hp r).1) (fun r => (hp r).2) hmax hc]
    with r hr
  intro q hq hgq
  exact hr.trans_le (hpm r ⟨hq, hgq.trans (le_max_right _ _)⟩)

-- @node: estimation_le_liminf_representation_iInf
/-- Given [maps from representations to population parameters](hyp:p) and
[criteria for admissibility and empirical feasibility](hyp:admissible,feasible),
suppose [the population parameter set is compact](hyp:hcompact), [the objective](hyp:hf)
and [constraint error](hyp:hg) are continuous there, [the error is nonnegative](hyp:hgnonneg)
and [zero at some parameter in the set](hyp:hzero), and [the error tolerance tends
to zero](hyp:hbeta). If [eventually every admissible, feasible representation maps
into this set with error within tolerance](hyp:hcontrol), then [the minimum
population objective under zero error is at most the lower limit of the infima
over admissible, empirically feasible representations](goal).

An empty feasible class has infimum positive infinity. -/
lemma estimation_le_liminf_representation_iInf
    {A : ℕ → Type*} (p : ∀ r, A r → P)
    (admissible feasible : ∀ r, A r → Prop)
    (S : Set P) (f g : P → ℝ) (beta : ℕ → ℝ)
    (hcompact : IsCompact S) (hf : ContinuousOn f S) (hg : ContinuousOn g S)
    (hgnonneg : ∀ q ∈ S, 0 ≤ g q)
    (hzero : ∃ q ∈ S, g q = 0)
    (hbeta : Tendsto beta atTop (𝓝 0))
    (hcontrol : ∀ᶠ r in atTop, ∀ a, admissible r a → feasible r a →
      p r a ∈ S ∧ g (p r a) ≤ beta r) :
    (convgOptLimitValue f S g : EReal) ≤
      liminf (fun r => ⨅ a : A r, ⨅ (_ : admissible r a), ⨅ (_ : feasible r a),
        (f (p r a) : EReal)) atTop := by
  apply (le_liminf_iff').mpr
  intro y hy
  induction y using EReal.rec with
  | bot => exact Eventually.of_forall (fun _ => bot_le)
  | top => exact False.elim (not_lt_of_ge le_top hy)
  | coe c =>
    have hc : c < convgOptLimitValue f S g := EReal.coe_lt_coe_iff.mp hy
    filter_upwards [estimation_compact_sublevel_eventually_lower S f g beta
      hcompact hf hg hgnonneg hzero hbeta hc, hcontrol] with r hr hrc
    apply le_iInf
    intro a
    apply le_iInf
    intro ha
    apply le_iInf
    intro hfeas
    obtain ⟨hmem, hbound⟩ := hrc a ha hfeas
    exact EReal.coe_le_coe_iff.mpr (hr (p r a) hmem hbound).le

variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
  {C : Fin b → Set (Fin n)}

-- @node: restrictedEmpiricalPIValue_liminf_ge_of_compact_control
/-- For [output and Lipschitz bounds](hyp:K,L), [well-defined empirical objectives](hyp:hdefined),
[observed samples](hyp:sample), [simulation inputs](hyp:draws), and [maps from
neural representations to population parameters](hyp:p), assume [the population
set is compact](hyp:hcompact), [the objective](hyp:hf) and [constraint error](hyp:hg)
are continuous on it, [the error is nonnegative](hyp:hgnonneg) and [zero somewhere
in the set](hyp:hzero), and [the error tolerances tend to zero](hyp:hbeta). If
[the parameter objective equals each representation's intervention objective](hyp:hobjective)
and [eventually every restricted, empirically feasible model maps into the set
with error within tolerance](hyp:hcontrol), then [the zero-error population
minimum is at most the lower limit of the restricted empirical policy values](goal). -/
lemma restrictedEmpiricalPIValue_liminf_ge_of_compact_control
    {counts : Fin b → ℕ}
    (F0 : ℕ → StructuralClass kind dims dag C) (F1 : ℕ → GeneratorClass dims counts)
    (K L : ℝ≥0) {I : Type*} [MeasurableSpace I]
    (t : I → LawIntervention kind) (muT : Measure I) [IsProbabilityMeasure muT] (F : Joint kind → ℝ)
    (hdefined : ∀ r, empiricalObjectivesDefined (G := G) (F0 r) (F1 r)
      (restrictedCandidate K L) t muT F)
    (m : ℕ → ℕ) (sample : ∀ r, Fin r → Joint kind)
    (draws : ∀ r, Fin (m r) → SimulationInput kind counts)
    (lam alpha beta : ℕ → ℝ)
    (p : ∀ r, NCMIn kind dims dag G C counts (F0 r) (F1 r) → P)
    (S : Set P) (f g : P → ℝ)
    (hcompact : IsCompact S) (hf : ContinuousOn f S) (hg : ContinuousOn g S)
    (hgnonneg : ∀ q ∈ S, 0 ≤ g q) (hzero : ∃ q ∈ S, g q = 0)
    (hbeta : Tendsto beta atTop (𝓝 0))
    (hobjective : ∀ r R, f (p r R) = objectiveIntegral R.canonical.toEuclideanSCM t muT F)
    (hcontrol : ∀ᶠ r in atTop,
      ∀ R : NCMIn kind dims dag G C counts (F0 r) (F1 r),
      restrictedCandidate K L R →
      sinkhornDivergence (lam r) (fun i => jointVector (ncmEval R (draws r i)))
        (fun i => jointVector (sample r i)) (uniformWeights (m r)) (uniformWeights r) ≤
          alpha r → p r R ∈ S ∧ g (p r R) ≤ beta r) :
    (convgOptLimitValue f S g : EReal) ≤
      liminf (fun r => restrictedEmpiricalPIValue (G := G) (F0 r) (F1 r) K L t muT F
        (sample r) (draws r) (lam r) (alpha r) (hdefined r)) atTop := by
  have h := estimation_le_liminf_representation_iInf p
    (fun _ => restrictedCandidate K L)
    (fun r R => sinkhornDivergence (lam r) (fun i => jointVector (ncmEval R (draws r i)))
      (fun i => jointVector (sample r i)) (uniformWeights (m r)) (uniformWeights r) ≤ alpha r)
    S f g beta hcompact hf hg hgnonneg hzero hbeta hcontrol
  simpa only [hobjective, restrictedEmpiricalPIValue, empiricalPIValueOn, empiricalLawSinkhorn,
    trueObjective, finiteIteratedObjective, objectiveIntegral] using h

end Papers.TbsNeuralCausalPi

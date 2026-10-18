module
public import Papers.TbsNeuralCausalPi.Helpers.EstimationAssembly
public import Mathlib.Analysis.PSeries
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
/-! # Almost-sure sampling control and eventual empirical feasibility

The sampling estimate remains an input to these assembly lemmas. Borel--Cantelli
uses outer measures, so no measurability of a representation supremum is needed.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory Filter
open scoped NNReal ENNReal Topology

-- @node: estimation_ae_eventually_of_inverse_square_bound
/-- If [the measure of each bad event is eventually bounded by a fixed constant
times the inverse square of its index](hyp:hbad), then [almost every outcome
belongs to no bad event after some finite index](goal). -/
lemma estimation_ae_eventually_of_inverse_square_bound
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    (bad : ℕ → Set Omega) (B : ℝ)
    (hbad : ∀ᶠ r in atTop, mu (bad r) ≤ ENNReal.ofReal (B * (r : ℝ) ^ (-(2 : ℤ)))) :
    ∀ᵐ w ∂mu, ∀ᶠ r in atTop, w ∉ bad r := by
  classical
  obtain ⟨N, hN⟩ := eventually_atTop.mp hbad
  let tail : ℕ → Set Omega := fun r => if N ≤ r then bad r else ∅
  have hsum : Summable (fun r : ℕ => B * (r : ℝ) ^ (-(2 : ℤ))) := by
    simpa only [zpow_neg, zpow_ofNat] using
      ((Real.summable_nat_pow_inv (p := 2)).mpr (by norm_num)).mul_left B
  have htail : (∑' r, mu (tail r)) ≠ ⊤ := by
    apply ne_of_lt
    apply lt_of_le_of_lt (ENNReal.tsum_le_tsum (fun r => ?_)) hsum.tsum_ofReal_lt_top
    by_cases hr : N ≤ r
    · simpa only [tail, if_pos hr] using hN r hr
    · simp only [tail, if_neg hr, measure_empty]
      exact bot_le
  filter_upwards [ae_eventually_notMem htail] with w hw
  filter_upwards [hw, eventually_ge_atTop N] with r hr hNr
  simpa only [tail, if_pos hNr] using hr

-- @node: estimation_ae_eventually_uniform_constraint_control
/-- For [an admissibility criterion at each sample size](hyp:admissible),
[nonnegative, possibly infinite population discrepancies](hyp:population), and
[random real-valued empirical discrepancies](hyp:empirical), suppose [the measure
of an outcome where any admissible representation violates either comparison
within the prescribed slack is eventually bounded by a constant times inverse
sample size squared](hyp:hbad). Then [almost surely, eventually all admissible
representations have population discrepancy at most empirical discrepancy plus
slack and at least empirical discrepancy minus slack, with both real bounds
truncated at zero](goal). -/
lemma estimation_ae_eventually_uniform_constraint_control
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    {A : ℕ → Type*} (admissible : ∀ r, A r → Prop)
    (population : ∀ r, A r → ℝ≥0∞) (empirical : ∀ r, A r → Omega → ℝ)
    (slack : ℕ → ℝ) (B : ℝ)
    (hbad : ∀ᶠ r in atTop,
      mu {w | ∃ a : A r, admissible r a ∧
        ¬ (population r a ≤ ENNReal.ofReal (empirical r a w + slack r) ∧
          ENNReal.ofReal (empirical r a w - slack r) ≤ population r a)} ≤
        ENNReal.ofReal (B * (r : ℝ) ^ (-(2 : ℤ)))) :
    ∀ᵐ w ∂mu, ∀ᶠ r in atTop, ∀ a : A r, admissible r a →
      population r a ≤ ENNReal.ofReal (empirical r a w + slack r) ∧
        ENNReal.ofReal (empirical r a w - slack r) ≤ population r a := by
  classical
  filter_upwards [estimation_ae_eventually_of_inverse_square_bound mu _ B hbad] with w hw
  filter_upwards [hw] with r hr
  intro a ha
  by_contra h
  exact hr ⟨a, ha, h⟩

variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
  {C : Fin b → Set (Fin n)}

-- @node: estimation_eventually_feasible_and_population_control
/-- For [output and Lipschitz bounds](hyp:K,L), [observed samples](hyp:sample), and
[simulation inputs](hyp:draws), assume [the approximation tolerances](hyp:hepsilon)
and [sampling slacks](hyp:hslack) are eventually nonnegative, [the feasibility
radius eventually equals their sum](hyp:hradius), and [eventually a restricted
candidate approximates the reference observational law within the approximation
tolerance](hyp:happrox). If [failure of the simultaneous two-sided population
versus empirical discrepancy comparisons has measure eventually bounded by a
constant times inverse sample size squared](hyp:hbad), then [almost surely,
eventually there exists an empirically feasible restricted candidate and every
such candidate's observational Wasserstein error is at most twice the
feasibility radius, truncated at zero](goal). -/
lemma estimation_eventually_feasible_and_population_control
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    {counts : Fin b → ℕ}
    (M : CanonicalSCM kind dims dag G C)
    (F0 : ℕ → StructuralClass kind dims dag C) (F1 : ℕ → GeneratorClass dims counts)
    (K L : ℝ≥0) (m : ℕ → ℕ)
    (sample : ∀ r, Fin r → Omega → Joint kind)
    (draws : ∀ r, Fin (m r) → Omega → SimulationInput kind counts)
    (lam epsilon slack alpha : ℕ → ℝ) (B : ℝ)
    (hepsilon : ∀ᶠ r in atTop, 0 ≤ epsilon r)
    (hslack : ∀ᶠ r in atTop, 0 ≤ slack r)
    (hradius : ∀ᶠ r in atTop, alpha r = epsilon r + slack r)
    (happrox : ∀ᶠ r in atTop,
      ∃ R : NCMIn kind dims dag G C counts (F0 r) (F1 r),
        restrictedCandidate K L R ∧
        wasserstein1 (observationalLaw R.canonical.toEuclideanSCM)
          (observationalLaw M.toEuclideanSCM) ≤ ENNReal.ofReal (epsilon r))
    (hbad : ∀ᶠ r in atTop,
      mu {w | ∃ R : NCMIn kind dims dag G C counts (F0 r) (F1 r),
        restrictedCandidate K L R ∧
        let e := sinkhornDivergence (lam r)
          (fun i => jointVector (ncmEval R (draws r i w)))
          (fun i => jointVector (sample r i w)) (uniformWeights (m r)) (uniformWeights r)
        let p := wasserstein1 (observationalLaw R.canonical.toEuclideanSCM)
          (observationalLaw M.toEuclideanSCM)
        ¬ (p ≤ ENNReal.ofReal (e + slack r) ∧ ENNReal.ofReal (e - slack r) ≤ p)} ≤
          ENNReal.ofReal (B * (r : ℝ) ^ (-(2 : ℤ)))) :
    ∀ᵐ w ∂mu, ∀ᶠ r in atTop,
      (∃ R : NCMIn kind dims dag G C counts (F0 r) (F1 r),
        restrictedCandidate K L R ∧
        sinkhornDivergence (lam r)
          (fun i => jointVector (ncmEval R (draws r i w)))
          (fun i => jointVector (sample r i w))
          (uniformWeights (m r)) (uniformWeights r) ≤ alpha r) ∧
      (∀ R : NCMIn kind dims dag G C counts (F0 r) (F1 r),
        restrictedCandidate K L R →
        sinkhornDivergence (lam r)
          (fun i => jointVector (ncmEval R (draws r i w)))
          (fun i => jointVector (sample r i w))
          (uniformWeights (m r)) (uniformWeights r) ≤ alpha r →
        wasserstein1 (observationalLaw R.canonical.toEuclideanSCM)
          (observationalLaw M.toEuclideanSCM) ≤ ENNReal.ofReal (2 * alpha r)) := by
  have hcontrol := estimation_ae_eventually_uniform_constraint_control mu
    (fun _ => restrictedCandidate K L)
    (fun _ R => wasserstein1 (observationalLaw R.canonical.toEuclideanSCM)
      (observationalLaw M.toEuclideanSCM))
    (fun r R w => sinkhornDivergence (lam r)
      (fun i => jointVector (ncmEval R (draws r i w)))
      (fun i => jointVector (sample r i w)) (uniformWeights (m r)) (uniformWeights r))
    slack B hbad
  filter_upwards [hcontrol] with w hw
  filter_upwards [hw, happrox, hepsilon, hslack, hradius] with r hc ha he hs hr
  obtain ⟨R, hR, herr⟩ := ha
  constructor
  · refine ⟨R, hR, ?_⟩
    rw [hr]
    exact estimation_feasible_of_population_approximation he herr (hc R hR).2
  · intro R hR hf
    exact estimation_population_error_of_feasible (hc R hR).1 hf (by rw [hr]; linarith)

-- @node: restrictedEmpiricalPIValue_limsup_le_of_recovery
/-- For [output and Lipschitz bounds](hyp:K,L), [well-defined empirical objectives](hyp:hdefined),
[observed samples](hyp:sample), and [simulation inputs](hyp:draws), suppose [the
objective upper bounds converge to the target value](hyp:hupper) and [eventually
there is a restricted, empirically feasible representation whose intervention
objective is at most the corresponding upper bound](hyp:hrecovery). Then [the
upper limit of the restricted empirical policy values is at most the target](goal). -/
lemma restrictedEmpiricalPIValue_limsup_le_of_recovery
    {counts : Fin b → ℕ}
    (F0 : ℕ → StructuralClass kind dims dag C) (F1 : ℕ → GeneratorClass dims counts)
    (K L : ℝ≥0) {I : Type*} [MeasurableSpace I]
    (t : I → LawIntervention kind) (muT : Measure I) [IsProbabilityMeasure muT] (F : Joint kind → ℝ)
    (hdefined : ∀ r, empiricalObjectivesDefined (G := G) (F0 r) (F1 r)
      (restrictedCandidate K L) t muT F)
    (m : ℕ → ℕ) (sample : ∀ r, Fin r → Joint kind)
    (draws : ∀ r, Fin (m r) → SimulationInput kind counts)
    (lam alpha upper : ℕ → ℝ) (target : ℝ)
    (hupper : Tendsto upper atTop (𝓝 target))
    (hrecovery : ∀ᶠ r in atTop,
      ∃ R : NCMIn kind dims dag G C counts (F0 r) (F1 r),
        restrictedCandidate K L R ∧
        sinkhornDivergence (lam r) (fun i => jointVector (ncmEval R (draws r i)))
          (fun i => jointVector (sample r i)) (uniformWeights (m r)) (uniformWeights r) ≤
            alpha r ∧
        objectiveIntegral R.canonical.toEuclideanSCM t muT F ≤ upper r) :
    limsup (fun r => restrictedEmpiricalPIValue (G := G) (F0 r) (F1 r) K L t muT F
      (sample r) (draws r) (lam r) (alpha r) (hdefined r)) atTop ≤ (target : EReal) := by
  have hbound : ∀ᶠ r in atTop,
      restrictedEmpiricalPIValue (G := G) (F0 r) (F1 r) K L t muT F
        (sample r) (draws r) (lam r) (alpha r) (hdefined r) ≤ (upper r : EReal) := by
    filter_upwards [hrecovery] with r hr
    obtain ⟨R, hR, hf, ho⟩ := hr
    exact iInf_le_of_le R (iInf_le_of_le hR
      (iInf_le_of_le hf (EReal.coe_le_coe_iff.mpr ho)))
  have hlim : Tendsto (fun r => (upper r : EReal)) atTop (𝓝 (target : EReal)) :=
    continuous_coe_real_ereal.continuousAt.tendsto.comp hupper
  exact (limsup_le_limsup hbound).trans_eq hlim.limsup_eq

-- @node: estimation_eventually_recovery_of_uniform_constraint_control
/-- For [an admissibility criterion](hyp:admissible), [population discrepancies](hyp:population),
and [empirical discrepancies and objective values](hyp:empirical,objective), assume
[the approximation tolerance is eventually nonnegative](hyp:hepsilon), [the
feasibility radius eventually equals approximation tolerance plus slack](hyp:hradius),
[eventually an admissible representation has population error within tolerance
and objective below the prescribed upper bound](hyp:happrox), and [eventually
every admissible representation's empirical error minus slack, truncated at zero,
is at most its population error](hyp:hcontrol). Then [eventually an admissible
representation is empirically feasible and retains the objective upper bound](goal). -/
lemma estimation_eventually_recovery_of_uniform_constraint_control
    {A : ℕ → Type*} (admissible : ∀ r, A r → Prop)
    (population : ∀ r, A r → ℝ≥0∞) (empirical objective : ∀ r, A r → ℝ)
    (epsilon slack alpha upper : ℕ → ℝ)
    (hepsilon : ∀ᶠ r in atTop, 0 ≤ epsilon r)
    (hradius : ∀ᶠ r in atTop, alpha r = epsilon r + slack r)
    (happrox : ∀ᶠ r in atTop, ∃ a : A r, admissible r a ∧
      population r a ≤ ENNReal.ofReal (epsilon r) ∧ objective r a ≤ upper r)
    (hcontrol : ∀ᶠ r in atTop, ∀ a : A r, admissible r a →
      ENNReal.ofReal (empirical r a - slack r) ≤ population r a) :
    ∀ᶠ r in atTop, ∃ a : A r, admissible r a ∧
      empirical r a ≤ alpha r ∧ objective r a ≤ upper r := by
  filter_upwards [hepsilon, hradius, happrox, hcontrol] with r he hr ha hc
  obtain ⟨a, hadm, hpop, hobj⟩ := ha
  refine ⟨a, hadm, ?_, hobj⟩
  rw [hr]
  exact estimation_feasible_of_population_approximation he hpop (hc a hadm)

-- @node: restrictedEmpiricalPIValue_ae_limsup_le_of_population_recovery
/-- For [output and Lipschitz bounds](hyp:K,L), [well-defined empirical objectives](hyp:hdefined),
[observed samples](hyp:sample), and [simulation inputs](hyp:draws), suppose [the
approximation tolerance is eventually nonnegative](hyp:hepsilon), [the feasibility
radius eventually equals approximation tolerance plus slack](hyp:hradius), and
[the objective upper bounds converge to the target](hyp:hupper). If [eventually
one restricted representation both approximates the reference observational law
within tolerance and satisfies the objective upper bound](hyp:happrox), and
[failure of the simultaneous two-sided population versus empirical discrepancy
comparisons has measure eventually bounded by a constant times inverse sample
size squared](hyp:hbad), then [almost surely the upper limit of the restricted
empirical policy values is at most the target](goal). -/
lemma restrictedEmpiricalPIValue_ae_limsup_le_of_population_recovery
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    {counts : Fin b → ℕ} (M : CanonicalSCM kind dims dag G C)
    (F0 : ℕ → StructuralClass kind dims dag C) (F1 : ℕ → GeneratorClass dims counts)
    (K L : ℝ≥0) {I : Type*} [MeasurableSpace I]
    (t : I → LawIntervention kind) (muT : Measure I) [IsProbabilityMeasure muT] (F : Joint kind → ℝ)
    (hdefined : ∀ r, empiricalObjectivesDefined (G := G) (F0 r) (F1 r)
      (restrictedCandidate K L) t muT F)
    (m : ℕ → ℕ) (sample : ∀ r, Fin r → Omega → Joint kind)
    (draws : ∀ r, Fin (m r) → Omega → SimulationInput kind counts)
    (lam epsilon slack alpha upper : ℕ → ℝ) (target B : ℝ)
    (hepsilon : ∀ᶠ r in atTop, 0 ≤ epsilon r)
    (hradius : ∀ᶠ r in atTop, alpha r = epsilon r + slack r)
    (hupper : Tendsto upper atTop (𝓝 target))
    (happrox : ∀ᶠ r in atTop,
      ∃ R : NCMIn kind dims dag G C counts (F0 r) (F1 r),
        restrictedCandidate K L R ∧
        wasserstein1 (observationalLaw R.canonical.toEuclideanSCM)
          (observationalLaw M.toEuclideanSCM) ≤ ENNReal.ofReal (epsilon r) ∧
        objectiveIntegral R.canonical.toEuclideanSCM t muT F ≤ upper r)
    (hbad : ∀ᶠ r in atTop,
      mu {w | ∃ R : NCMIn kind dims dag G C counts (F0 r) (F1 r),
        restrictedCandidate K L R ∧
        let e := sinkhornDivergence (lam r)
          (fun i => jointVector (ncmEval R (draws r i w)))
          (fun i => jointVector (sample r i w)) (uniformWeights (m r)) (uniformWeights r)
        let p := wasserstein1 (observationalLaw R.canonical.toEuclideanSCM)
          (observationalLaw M.toEuclideanSCM)
        ¬ (p ≤ ENNReal.ofReal (e + slack r) ∧ ENNReal.ofReal (e - slack r) ≤ p)} ≤
          ENNReal.ofReal (B * (r : ℝ) ^ (-(2 : ℤ)))) :
    ∀ᵐ w ∂mu,
      limsup (fun r => restrictedEmpiricalPIValue (G := G) (F0 r) (F1 r) K L t muT F
        (fun i => sample r i w) (fun i => draws r i w) (lam r) (alpha r) (hdefined r)) atTop ≤
          (target : EReal) := by
  have hcontrol := estimation_ae_eventually_uniform_constraint_control mu
    (fun _ => restrictedCandidate K L)
    (fun _ R => wasserstein1 (observationalLaw R.canonical.toEuclideanSCM)
      (observationalLaw M.toEuclideanSCM))
    (fun r R w => sinkhornDivergence (lam r)
      (fun i => jointVector (ncmEval R (draws r i w)))
      (fun i => jointVector (sample r i w)) (uniformWeights (m r)) (uniformWeights r))
    slack B hbad
  filter_upwards [hcontrol] with w hw
  apply restrictedEmpiricalPIValue_limsup_le_of_recovery F0 F1 K L t muT F hdefined m
    (fun r i => sample r i w) (fun r i => draws r i w) lam alpha upper target hupper
  apply estimation_eventually_recovery_of_uniform_constraint_control
    (fun _ => restrictedCandidate K L)
    (fun _ R => wasserstein1 (observationalLaw R.canonical.toEuclideanSCM)
      (observationalLaw M.toEuclideanSCM))
    (fun r R => sinkhornDivergence (lam r)
      (fun i => jointVector (ncmEval R (draws r i w)))
      (fun i => jointVector (sample r i w)) (uniformWeights (m r)) (uniformWeights r))
    (fun _ R => objectiveIntegral R.canonical.toEuclideanSCM t muT F)
    epsilon slack alpha upper hepsilon hradius happrox
  exact hw.mono (fun r hr R hR => (hr R hR).2)

end Papers.TbsNeuralCausalPi

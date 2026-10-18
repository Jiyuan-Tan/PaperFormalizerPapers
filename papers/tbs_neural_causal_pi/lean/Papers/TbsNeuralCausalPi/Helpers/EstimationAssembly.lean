module
public import Papers.TbsNeuralCausalPi.Setup.Optimization
/-! # Deterministic feasibility and infimum steps for empirical estimation

These lemmas apply after the approximation, sampling and causal-effect estimates
have been established. They retain the representation-based empirical constraint
and do not require the optimization infimum to be attained.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
open scoped NNReal ENNReal

/-- If [epsilon is nonnegative](hyp:hepsilon), [the population discrepancy is
at most epsilon](hyp:happrox), and [the nonnegative part of the empirical
discrepancy minus slack is at most the population discrepancy](hyp:hsample),
then [the empirical discrepancy is at most epsilon plus slack](goal). -/
-- @node: estimation_feasible_of_population_approximation
lemma estimation_feasible_of_population_approximation
    {population : ℝ≥0∞} {empirical epsilon slack : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (happrox : population ≤ ENNReal.ofReal epsilon)
    (hsample : ENNReal.ofReal (empirical - slack) ≤ population) :
    empirical ≤ epsilon + slack := by
  have h := (ENNReal.ofReal_le_ofReal_iff hepsilon).mp (hsample.trans happrox)
  linarith

/-- If [the population discrepancy is at most the nonnegative part of the
empirical discrepancy plus slack](hyp:hsample), [the empirical discrepancy is
at most alpha](hyp:hfeasible), and [the slack is at most alpha](hyp:hslack), then
[the population discrepancy is at most the nonnegative part of twice
alpha](goal). -/
-- @node: estimation_population_error_of_feasible
lemma estimation_population_error_of_feasible
    {population : ℝ≥0∞} {empirical alpha slack : ℝ}
    (hsample : population ≤ ENNReal.ofReal (empirical + slack))
    (hfeasible : empirical ≤ alpha) (hslack : slack ≤ alpha) :
    population ≤ ENNReal.ofReal (2 * alpha) := by
  exact hsample.trans (ENNReal.ofReal_le_ofReal (by linarith))

/-- If [there is an admissible, feasible candidate](hyp:hne) and [every such
candidate's objective lies between the lower and upper bounds](hyp:hbound),
then [the extended-real infimum over admissible, feasible candidates lies
between those same bounds](goal). -/
-- @node: estimation_iInf_mem_interval
lemma estimation_iInf_mem_interval {A : Type*} (admissible feasible : A → Prop)
    (objective : A → ℝ) {lower upper : ℝ}
    (hne : ∃ a, admissible a ∧ feasible a)
    (hbound : ∀ a, admissible a → feasible a →
      lower ≤ objective a ∧ objective a ≤ upper) :
    (lower : EReal) ≤ (⨅ a, ⨅ (_ : admissible a), ⨅ (_ : feasible a),
      (objective a : EReal)) ∧
    (⨅ a, ⨅ (_ : admissible a), ⨅ (_ : feasible a),
      (objective a : EReal)) ≤ (upper : EReal) := by
  constructor
  · exact le_iInf (fun a => le_iInf (fun ha => le_iInf (fun hf =>
      EReal.coe_le_coe_iff.mpr (hbound a ha hf).1)))
  · obtain ⟨a, ha, hf⟩ := hne
    exact iInf_le_of_le a (iInf_le_of_le ha (iInf_le_of_le hf
      (EReal.coe_le_coe_iff.mpr (hbound a ha hf).2)))

/-- If [there is an admissible, feasible candidate](hyp:hne) and [every such
candidate's objective differs from the target by at most error](hyp:hbound),
then [their extended-real objective infimum is finite and its real value
differs from the target by at most error](goal). -/
-- @node: estimation_iInf_error
lemma estimation_iInf_error {A : Type*} (admissible feasible : A → Prop)
    (objective : A → ℝ) (target error : ℝ)
    (hne : ∃ a, admissible a ∧ feasible a)
    (hbound : ∀ a, admissible a → feasible a → |objective a - target| ≤ error) :
    let v : EReal := ⨅ a, ⨅ (_ : admissible a), ⨅ (_ : feasible a),
      (objective a : EReal)
    v ≠ ⊤ ∧ v ≠ ⊥ ∧ |v.toReal - target| ≤ error := by
  dsimp only
  have hb := estimation_iInf_mem_interval admissible feasible objective
    (lower := target - error) (upper := target + error) hne
    (fun a ha hf => by
      have h := abs_le.mp (hbound a ha hf)
      constructor <;> linarith)
  have ht : (⨅ a, ⨅ (_ : admissible a), ⨅ (_ : feasible a),
      (objective a : EReal)) ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hb.2 (EReal.coe_lt_top _))
  have hbot : (⨅ a, ⨅ (_ : admissible a), ⨅ (_ : feasible a),
      (objective a : EReal)) ≠ ⊥ := ne_of_gt (lt_of_lt_of_le (EReal.bot_lt_coe _) hb.1)
  refine ⟨ht, hbot, abs_le.mpr ?_⟩
  have hl := EReal.toReal_le_toReal hb.1 (EReal.coe_ne_bot _) ht
  have hu := EReal.toReal_le_toReal hb.2 hbot (EReal.coe_ne_top _)
  simp only [EReal.toReal_coe] at hl hu
  constructor <;> linarith

/-- If [a is nonnegative](hyp:ha), [b is nonnegative](hyp:hb), [c is
nonnegative](hyp:hc), and [w is nonnegative](hyp:hw),
[alpha is nonnegative](hyp:halpha) and [at most one](hyp:halpha_one), and
[w is at most c times alpha](hyp:herror), then [the square root of a w + b w²
is at most the square root of a c + b c² times the square root of alpha](goal). -/
-- @node: estimation_sqrt_quadratic_bound
lemma estimation_sqrt_quadratic_bound {a b c w alpha : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hw : 0 ≤ w)
    (halpha : 0 ≤ alpha) (halpha_one : alpha ≤ 1) (herror : w ≤ c * alpha) :
    Real.sqrt (a * w + b * w^2) ≤
      Real.sqrt (a * c + b * c^2) * Real.sqrt alpha := by
  have hsq : w^2 ≤ c^2 * alpha := by
    calc
      w^2 ≤ (c * alpha)^2 := pow_le_pow_left₀ hw herror 2
      _ = c^2 * alpha^2 := mul_pow c alpha 2
      _ ≤ c^2 * alpha := mul_le_mul_of_nonneg_left
        (by nlinarith : alpha^2 ≤ alpha) (sq_nonneg c)
  calc
    Real.sqrt (a * w + b * w^2) ≤ Real.sqrt ((a * c + b * c^2) * alpha) := by
      apply Real.sqrt_le_sqrt
      nlinarith [mul_le_mul_of_nonneg_left herror ha,
        mul_le_mul_of_nonneg_left hsq hb]
    _ = _ := Real.sqrt_mul (by positivity) _

/-- If [the failure bound is nonnegative](hyp:hfailure), [the bad event has
outer probability at most that bound](hyp:hbad), and [the good event contains
the complement of the bad event](hyp:hgood), then [the good event has outer
probability at least the nonnegative part of one minus the failure bound](goal). -/
-- @node: estimation_success_measure_of_bad_bound
lemma estimation_success_measure_of_bad_bound {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu] (bad good : Set Omega)
    {failure : ℝ} (hfailure : 0 ≤ failure)
    (hbad : mu bad ≤ ENNReal.ofReal failure) (hgood : badᶜ ⊆ good) :
    ENNReal.ofReal (1 - failure) ≤ mu good := by
  rw [ENNReal.ofReal_sub 1 hfailure, ENNReal.ofReal_one]
  apply tsub_le_iff_right.mpr
  calc
    1 = mu (badᶜ ∪ bad) := by simp
    _ ≤ mu badᶜ + mu bad := measure_union_le _ _
    _ ≤ mu good + ENNReal.ofReal failure := add_le_add (measure_mono hgood) hbad

variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)} {C : Fin b → Set (Fin n)}

/-- For [nonnegative output and Lipschitz bounds K and L](hyp:K,L), suppose
[the restricted empirical objectives are well defined](hyp:hdefined), [at
least one restricted candidate meets the empirical Sinkhorn constraint at
radius alpha](hyp:hne), and [every such candidate's intervention objective
differs from the target by at most error](hyp:hbound). Then [the restricted
empirical partial-identification value is finite and its real value differs
from the target by at most error](goal). -/
-- @node: restrictedEmpiricalPIValue_error_of_uniform_bound
lemma restrictedEmpiricalPIValue_error_of_uniform_bound {counts : Fin b → ℕ}
    (F0 : StructuralClass kind dims dag C) (F1 : GeneratorClass dims counts)
    (K L : ℝ≥0) {I : Type*} [MeasurableSpace I]
    (t : I → LawIntervention kind) (muT : Measure I) [IsProbabilityMeasure muT] (F : Joint kind → ℝ)
    (hdefined : empiricalObjectivesDefined (G := G) F0 F1
      (restrictedCandidate K L) t muT F) {r m : ℕ}
    (sample : Fin r → Joint kind) (draws : Fin m → SimulationInput kind counts)
    (lam alpha target error : ℝ)
    (hne : ∃ R : NCMIn kind dims dag G C counts F0 F1,
      restrictedCandidate K L R ∧
      sinkhornDivergence lam (fun i => jointVector (ncmEval R (draws i)))
        (fun i => jointVector (sample i)) (uniformWeights m) (uniformWeights r) ≤ alpha)
    (hbound : ∀ R : NCMIn kind dims dag G C counts F0 F1,
      restrictedCandidate K L R →
      sinkhornDivergence lam (fun i => jointVector (ncmEval R (draws i)))
        (fun i => jointVector (sample i)) (uniformWeights m) (uniformWeights r) ≤ alpha →
      |objectiveIntegral R.canonical.toEuclideanSCM t muT F - target| ≤ error) :
    let v := restrictedEmpiricalPIValue (G := G) F0 F1 K L t muT F sample draws lam alpha hdefined
    v ≠ ⊤ ∧ v ≠ ⊥ ∧ |v.toReal - target| ≤ error := by
  exact estimation_iInf_error (restrictedCandidate K L)
    (fun R => sinkhornDivergence lam (fun i => jointVector (ncmEval R (draws i)))
      (fun i => jointVector (sample i)) (uniformWeights m) (uniformWeights r) ≤ alpha)
    (fun R => objectiveIntegral R.canonical.toEuclideanSCM t muT F) target error hne hbound

/-- For [nonnegative output and Lipschitz bounds K and L](hyp:K,L), assume
[the restricted empirical objectives are well defined](hyp:hdefined),
[A is nonnegative](hyp:hA), [a is nonnegative](hyp:ha), [b is
nonnegative](hyp:hb), and [c is nonnegative](hyp:hc),
[alpha is nonnegative](hyp:halpha) and [at most one](hyp:halpha_one), and
[at least one restricted candidate meets the empirical Sinkhorn constraint
at radius alpha](hyp:hne). If [every feasible restricted candidate has a
nonnegative discrepancy w at most c alpha and objective error at most A times
the square root of a w + b w²](hyp:hestimate), then [the restricted empirical
partial-identification value is finite and its error from the target is at
most A times the square root of a c + b c² times the square root of alpha](goal). -/
-- @node: restrictedEmpiricalPIValue_error_of_quadratic_bound
lemma restrictedEmpiricalPIValue_error_of_quadratic_bound {counts : Fin b → ℕ}
    (F0 : StructuralClass kind dims dag C) (F1 : GeneratorClass dims counts)
    (K L : ℝ≥0) {I : Type*} [MeasurableSpace I]
    (t : I → LawIntervention kind) (muT : Measure I) [IsProbabilityMeasure muT] (F : Joint kind → ℝ)
    (hdefined : empiricalObjectivesDefined (G := G) F0 F1
      (restrictedCandidate K L) t muT F) {r m : ℕ}
    (sample : Fin r → Joint kind) (draws : Fin m → SimulationInput kind counts)
    (lam alpha target A a b c : ℝ)
    (w : NCMIn kind dims dag G C counts F0 F1 → ℝ)
    (hA : 0 ≤ A) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (halpha : 0 ≤ alpha) (halpha_one : alpha ≤ 1)
    (hne : ∃ R : NCMIn kind dims dag G C counts F0 F1,
      restrictedCandidate K L R ∧
      sinkhornDivergence lam (fun i => jointVector (ncmEval R (draws i)))
        (fun i => jointVector (sample i)) (uniformWeights m) (uniformWeights r) ≤ alpha)
    (hestimate : ∀ R : NCMIn kind dims dag G C counts F0 F1,
      restrictedCandidate K L R →
      sinkhornDivergence lam (fun i => jointVector (ncmEval R (draws i)))
        (fun i => jointVector (sample i)) (uniformWeights m) (uniformWeights r) ≤ alpha →
      0 ≤ w R ∧ w R ≤ c * alpha ∧
        |objectiveIntegral R.canonical.toEuclideanSCM t muT F - target| ≤
          A * Real.sqrt (a * w R + b * (w R)^2)) :
    let v := restrictedEmpiricalPIValue (G := G) F0 F1 K L t muT F sample draws lam alpha hdefined
    v ≠ ⊤ ∧ v ≠ ⊥ ∧
      |v.toReal - target| ≤ (A * Real.sqrt (a * c + b * c^2)) * Real.sqrt alpha := by
  apply restrictedEmpiricalPIValue_error_of_uniform_bound
    F0 F1 K L t muT F hdefined sample draws lam alpha target _ hne
  intro R hR hfeasible
  obtain ⟨hw, herr, hquad⟩ := hestimate R hR hfeasible
  calc
    |objectiveIntegral R.canonical.toEuclideanSCM t muT F - target| ≤
        A * Real.sqrt (a * w R + b * (w R)^2) := hquad
    _ ≤ A * (Real.sqrt (a * c + b * c^2) * Real.sqrt alpha) :=
      mul_le_mul_of_nonneg_left
        (estimation_sqrt_quadratic_bound ha hb hc hw halpha halpha_one herr) hA
    _ = _ := (mul_assoc _ _ _).symm

end Papers.TbsNeuralCausalPi

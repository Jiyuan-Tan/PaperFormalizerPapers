module
public import Papers.TbsNeuralCausalPi.Helpers.EstimationAssembly
/-! # Finite-sample rate assembly for the restricted empirical optimization

Population approximation and simultaneous two-sided constraint control imply
feasibility. The quadratic objective estimate then passes to the actual
extended-real infimum. These are conditional assembly lemmas: the sampling
estimate and the causal-effect estimate remain separate proof obligations.
No measurability of the supremum over representations is required.
-/
public section
namespace Papers.TbsNeuralCausalPi
set_option linter.style.longLine false
set_option linter.style.whitespace false
open MeasureTheory Filter
open scoped NNReal ENNReal Topology

/-- For a [population discrepancy](hyp:population), assume [nonnegative approximation
error](hyp:hepsilon), [nonnegative sampling slack](hyp:hslack), [a radius equal
to their sum](hyp:hradius), [a radius at most one](hyp:halpha_one), and nonnegative
[density factor](hyp:hdensity), [linear coefficient](hyp:ha), and [quadratic
coefficient](hyp:hb). If [an admissible population approximation meets the error
tolerance](hyp:happrox), [every admissible empirical discrepancy controls the
population discrepancy from both sides up to the slack](hyp:hcontrol), and
[objective error obeys the density-scaled square-root linear-plus-quadratic
population discrepancy bound](hyp:hquadratic), then [the empirically constrained
infimum is finite and its target error is at most density times the square root
of twice the linear coefficient plus four times the quadratic coefficient,
times the square root of the radius](goal). -/
-- @node: estimation_iInf_rate_of_constraint_control
lemma estimation_iInf_rate_of_constraint_control
    {A : Type*} (admissible : A → Prop) (objective : A → ℝ)
    (population : A → ℝ≥0∞) (empirical : A → ℝ)
    (epsilon slack alpha target density a b : ℝ)
    (hepsilon : 0 ≤ epsilon) (hslack : 0 ≤ slack)
    (hradius : alpha = epsilon + slack) (halpha_one : alpha ≤ 1)
    (hdensity : 0 ≤ density) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (happrox : ∃ x, admissible x ∧ population x ≤ ENNReal.ofReal epsilon)
    (hcontrol : ∀ x, admissible x →
      population x ≤ ENNReal.ofReal (empirical x + slack) ∧
        ENNReal.ofReal (empirical x - slack) ≤ population x)
    (hquadratic : ∀ x, admissible x →
      |objective x - target| ≤
        density * Real.sqrt (a * (population x).toReal + b * (population x).toReal^2)) :
    let v : EReal := ⨅ x, ⨅ (_ : admissible x), ⨅ (_ : empirical x ≤ alpha),
      (objective x : EReal)
    v ≠ ⊤ ∧ v ≠ ⊥ ∧
      |v.toReal - target| ≤
        (density * Real.sqrt (2 * a + 4 * b)) * Real.sqrt alpha := by
  have halpha : 0 ≤ alpha := by linarith
  have hslack_alpha : slack ≤ alpha := by linarith
  obtain ⟨x, hx, herr⟩ := happrox
  have hne : ∃ x, admissible x ∧ empirical x ≤ alpha := by
    refine ⟨x, hx, ?_⟩
    rw [hradius]
    exact estimation_feasible_of_population_approximation hepsilon herr (hcontrol x hx).2
  apply estimation_iInf_error admissible (fun x => empirical x ≤ alpha)
    objective target _ hne
  intro x hx hfeasible
  have hp := estimation_population_error_of_feasible (hcontrol x hx).1
    hfeasible hslack_alpha
  have hreal : (population x).toReal ≤ 2 * alpha := by
    have h := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hp
    simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * alpha)] using h
  calc
    |objective x - target| ≤
        density * Real.sqrt (a * (population x).toReal + b * (population x).toReal^2) :=
      hquadratic x hx
    _ ≤ density * (Real.sqrt (a * 2 + b * 2^2) * Real.sqrt alpha) :=
      mul_le_mul_of_nonneg_left
        (estimation_sqrt_quadratic_bound ha hb (by norm_num) ENNReal.toReal_nonneg
          halpha halpha_one hreal) hdensity
    _ = _ := by
      rw [show a * 2 + b * 2^2 = 2 * a + 4 * b by ring, mul_assoc]

/-- For a [population discrepancy](hyp:population), assume [nonnegative approximation
error](hyp:hepsilon), [nonnegative slack](hyp:hslack), [radius equal to their
sum](hyp:hradius), [radius at most one](hyp:halpha_one), and nonnegative
[density factor](hyp:hdensity), [linear coefficient](hyp:ha), [quadratic
coefficient](hyp:hb), and [failure allowance](hyp:hfailure).
If [an admissible population approximation meets the error tolerance](hyp:happrox),
[each admissible objective error obeys the density-scaled square-root quadratic
discrepancy bound](hyp:hquadratic), and [the outer measure of any violation of
simultaneous two-sided empirical control is at most the failure allowance](hyp:hbad),
then [with measure at least one minus that allowance, the constrained infimum is
finite and its target error is at most density times the square root of twice
the linear coefficient plus four times the quadratic coefficient, times the
square root of the radius](goal). -/
-- @node: estimation_iInf_rate_success_measure
lemma estimation_iInf_rate_success_measure
    {Omega A : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (admissible : A → Prop) (objective : A → ℝ) (population : A → ℝ≥0∞)
    (empirical : A → Omega → ℝ)
    (epsilon slack alpha target density a b failure : ℝ)
    (hepsilon : 0 ≤ epsilon) (hslack : 0 ≤ slack)
    (hradius : alpha = epsilon + slack) (halpha_one : alpha ≤ 1)
    (hdensity : 0 ≤ density) (ha : 0 ≤ a) (hb : 0 ≤ b) (hfailure : 0 ≤ failure)
    (happrox : ∃ x, admissible x ∧ population x ≤ ENNReal.ofReal epsilon)
    (hquadratic : ∀ x, admissible x →
      |objective x - target| ≤
        density * Real.sqrt (a * (population x).toReal + b * (population x).toReal^2))
    (hbad : mu {w | ∃ x, admissible x ∧
      ¬ (population x ≤ ENNReal.ofReal (empirical x w + slack) ∧
        ENNReal.ofReal (empirical x w - slack) ≤ population x)} ≤ ENNReal.ofReal failure) :
    ENNReal.ofReal (1 - failure) ≤
      mu {w | let v : EReal := ⨅ x, ⨅ (_ : admissible x),
          ⨅ (_ : empirical x w ≤ alpha), (objective x : EReal)
        v ≠ ⊤ ∧ v ≠ ⊥ ∧ |v.toReal - target| ≤
          (density * Real.sqrt (2 * a + 4 * b)) * Real.sqrt alpha} := by
  apply estimation_success_measure_of_bad_bound mu _ _ hfailure hbad
  intro w hw
  have hcontrol : ∀ x, admissible x →
      population x ≤ ENNReal.ofReal (empirical x w + slack) ∧
        ENNReal.ofReal (empirical x w - slack) ≤ population x := by
    intro x hx
    by_contra h
    exact hw ⟨x, hx, h⟩
  exact estimation_iInf_rate_of_constraint_control admissible objective population
    (fun x => empirical x w) epsilon slack alpha target density a b
    hepsilon hslack hradius halpha_one hdensity ha hb happrox hcontrol hquadratic

/-- If [eventually the value is finite and has target error at most D times the
square root of the radius with measure at least one minus B divided by the
squared sample size](hyp:hprob), then [one positive constant A can replace both
B and D in these bounds for all sufficiently large sample sizes](goal). -/
-- @node: estimation_rate_single_constant
lemma estimation_rate_single_constant
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    (value : ℕ → Omega → EReal) (alpha : ℕ → ℝ) (target B D : ℝ)
    (hprob : ∀ᶠ r : ℕ in atTop,
      ENNReal.ofReal (1 - B * (r : ℝ)^(-(2 : ℤ))) ≤
        mu {w | value r w ≠ ⊤ ∧ value r w ≠ ⊥ ∧
          |(value r w).toReal - target| ≤ D * Real.sqrt (alpha r)}) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ r : ℕ in atTop,
      ENNReal.ofReal (1 - A * (r : ℝ)^(-(2 : ℤ))) ≤
        mu {w | value r w ≠ ⊤ ∧ value r w ≠ ⊥ ∧
          |(value r w).toReal - target| ≤ A * Real.sqrt (alpha r)} := by
  let A := max 1 (max B D)
  have hA : 0 < A := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hBA : B ≤ A := (le_max_left B D).trans (le_max_right _ _)
  have hDA : D ≤ A := (le_max_right B D).trans (le_max_right _ _)
  refine ⟨A, hA, ?_⟩
  filter_upwards [hprob] with r hr
  calc
    ENNReal.ofReal (1 - A * (r : ℝ)^(-(2 : ℤ))) ≤
        ENNReal.ofReal (1 - B * (r : ℝ)^(-(2 : ℤ))) := by
      apply ENNReal.ofReal_le_ofReal
      exact sub_le_sub_left
        (mul_le_mul_of_nonneg_right hBA (by positivity)) 1
    _ ≤ _ := hr
    _ ≤ _ := by
      apply measure_mono
      intro w hw
      exact ⟨hw.1, hw.2.1,
        hw.2.2.trans (mul_le_mul_of_nonneg_right hDA (Real.sqrt_nonneg _))⟩

variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
  {C : Fin b → Set (Fin n)}

/-- For [candidate bounds K and L](hyp:K,L), suppose [the restricted empirical
objectives are defined](hyp:hdefined), [the approximation error is nonnegative](hyp:hepsilon),
[the slack is nonnegative](hyp:hslack), [the radius is their sum](hyp:hradius),
[the radius is at most one](hyp:halpha_one), and the [density factor](hyp:hdensity),
[linear coefficient](hyp:ha), [quadratic coefficient](hyp:hb), and [failure
allowance are nonnegative](hyp:hfailure). If [a restricted neural causal model
approximates the observational law within the error tolerance](hyp:happrox),
[each restricted candidate's objective error obeys the density-scaled square-root
quadratic Wasserstein bound](hyp:hquadratic), and [the outer measure of any
failure of two-sided Sinkhorn control is at most the failure allowance](hyp:hbad),
then [with measure at least one minus that allowance the restricted empirical
value is finite and differs from the true objective by at most density times
the square root of twice the linear coefficient plus four times the quadratic
coefficient, times the square root of the radius](goal). -/
-- @node: restrictedEmpiricalPIValue_rate_success_measure
lemma restrictedEmpiricalPIValue_rate_success_measure
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu] {counts : Fin b → ℕ}
    (M : CanonicalSCM kind dims dag G C)
    (F0 : StructuralClass kind dims dag C) (F1 : GeneratorClass dims counts)
    (K L : ℝ≥0) {I : Type*} [MeasurableSpace I]
    (t : I → LawIntervention kind) (muT : Measure I) [IsProbabilityMeasure muT] (F : Joint kind → ℝ)
    (hdefined : empiricalObjectivesDefined (G := G) F0 F1 (restrictedCandidate K L) t muT F)
    {r m : ℕ} (sample : Fin r → Omega → Joint kind)
    (draws : Fin m → Omega → SimulationInput kind counts)
    (lam epsilon slack alpha density a b failure : ℝ)
    (hepsilon : 0 ≤ epsilon) (hslack : 0 ≤ slack)
    (hradius : alpha = epsilon + slack) (halpha_one : alpha ≤ 1)
    (hdensity : 0 ≤ density) (ha : 0 ≤ a) (hb : 0 ≤ b) (hfailure : 0 ≤ failure)
    (happrox : ∃ R : NCMIn kind dims dag G C counts F0 F1,
      restrictedCandidate K L R ∧
      wasserstein1 (observationalLaw R.canonical.toEuclideanSCM)
        (observationalLaw M.toEuclideanSCM) ≤ ENNReal.ofReal epsilon)
    (hquadratic : ∀ R : NCMIn kind dims dag G C counts F0 F1,
      restrictedCandidate K L R →
      let w := wasserstein1 (observationalLaw R.canonical.toEuclideanSCM)
        (observationalLaw M.toEuclideanSCM)
      |objectiveIntegral R.canonical.toEuclideanSCM t muT F -
        objectiveIntegral M.toEuclideanSCM t muT F| ≤
          density * Real.sqrt (a * w.toReal + b * w.toReal^2))
    (hbad : mu {w | ∃ R : NCMIn kind dims dag G C counts F0 F1,
      restrictedCandidate K L R ∧
      let e := sinkhornDivergence lam (fun i => jointVector (ncmEval R (draws i w)))
        (fun i => jointVector (sample i w)) (uniformWeights m) (uniformWeights r)
      let p := wasserstein1 (observationalLaw R.canonical.toEuclideanSCM)
        (observationalLaw M.toEuclideanSCM)
      ¬ (p ≤ ENNReal.ofReal (e + slack) ∧ ENNReal.ofReal (e - slack) ≤ p)} ≤
        ENNReal.ofReal failure) :
    ENNReal.ofReal (1 - failure) ≤
      mu {w | let v := (restrictedEmpiricalPIValue (G := G) F0 F1 K L t muT F
          (fun i => sample i w) (fun i => draws i w) lam alpha hdefined)
        v ≠ ⊤ ∧ v ≠ ⊥ ∧
          |v.toReal - objectiveIntegral M.toEuclideanSCM t muT F| ≤
            (density * Real.sqrt (2 * a + 4 * b)) * Real.sqrt alpha} := by
  exact estimation_iInf_rate_success_measure mu (restrictedCandidate K L)
    (fun R => objectiveIntegral R.canonical.toEuclideanSCM t muT F)
    (fun R => wasserstein1 (observationalLaw R.canonical.toEuclideanSCM)
      (observationalLaw M.toEuclideanSCM))
    (fun R w => sinkhornDivergence lam (fun i => jointVector (ncmEval R (draws i w)))
      (fun i => jointVector (sample i w)) (uniformWeights m) (uniformWeights r))
    epsilon slack alpha (objectiveIntegral M.toEuclideanSCM t muT F)
    density a b failure hepsilon hslack hradius halpha_one hdensity ha hb hfailure
    happrox hquadratic hbad

end Papers.TbsNeuralCausalPi

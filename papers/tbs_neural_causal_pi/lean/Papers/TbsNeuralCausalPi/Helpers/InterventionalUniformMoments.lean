module
public import Papers.TbsNeuralCausalPi.Helpers.InterventionalMoments
public import Papers.TbsNeuralCausalPi.Helpers.DoseResponseRegression
/-! # Uniform moments over bounded admissible interventions

Finite causal evaluation preserves a uniform coordinate bound when the assigned
values and the non-Gumbel inputs are bounded. This yields square-integrable
dose-response functions without an additional moment premise.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory Filter
open scoped NNReal ENNReal
variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}

-- @node: evalSteps_uniformly_bounded_of_nonGumbel_bounded
/-- For [a nonnegative Lipschitz constant](hyp:L), suppose [the continuous
mechanisms obey that Lipschitz bound on their admissible domains](hyp:hcont) and
[the bound on assigned-vector norms is nonnegative](hyp:hB). Then [there is a
nonnegative uniform bound on all joint coordinates after the specified number
of evaluation steps, simultaneously over admissible interventions with assigned
norms within that bound and exogenous inputs with non-Gumbel block coordinates
within the given noise bound](goal). -/
lemma evalSteps_uniformly_bounded_of_nonGumbel_bounded
    (M : EuclideanSCM kind dims) (L : ℝ≥0)
    (hcont : ContinuousMechanismsLipschitz M L) (K B : ℝ) (hB : 0 ≤ B) (r : ℕ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ (t : Intervention kind), AdmissibleIntervention kind t →
      (∀ i v, t i = some v → ‖v‖ ≤ B) → ∀ u : Exogenous kind dims,
      (∀ k j, |(blockProjection k u).ofLp j| ≤ K) →
      ∀ i j, |(evalSteps M t u r).ofLp ⟨i,j⟩| ≤ R := by
  classical
  induction r with
  | zero => exact ⟨0, le_rfl, by intros; simp [evalSteps]⟩
  | succ r ih =>
    obtain ⟨R, hR, hv⟩ := ih
    choose Q hQ hnode using fun i => nodeValue_bounded_on_coordinate_boxes M L hcont i R K
    let R' := R + ∑ i, Q i + B
    have hsum : 0 ≤ ∑ i, Q i := Finset.sum_nonneg (fun i _ => hQ i)
    have hRR : R ≤ R' := by dsimp [R']; linarith
    have hBR : B ≤ R' := by dsimp [R']; linarith
    have hQR (i : Fin n) : Q i ≤ R' := by
      have hi := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => hQ j)
        (Finset.mem_univ i)
      dsimp [R']; linarith
    refine ⟨R', hR.trans hRR, ?_⟩
    intro t ht htb u hu i j
    simp only [evalSteps, WithLp.ofLp_toLp]
    by_cases hi : M.dag.topoOrder i = r
    · simp only [hi, if_true]
      cases he : t i with
      | none =>
        simp only [Option.getD_none]
        exact (hnode i _ u (evalSteps_structuralInput_mem_domain M t ht u i r hi)
          (hv t ht htb u hu) hu j).trans (hQR i)
      | some v =>
        simp only [Option.getD_some]
        exact (PiLp.norm_apply_le v j).trans ((htb i v he).trans hBR)
    · simp only [hi, if_false]
      exact (hv t ht htb u hu i j).trans hRR

-- @node: meanOutcome_uniformly_bounded
/-- For [a nonnegative Lipschitz constant](hyp:L), suppose [the continuous
mechanisms obey that Lipschitz bound on their admissible domains](hyp:hcont),
[observational coordinates and non-Gumbel block coordinates are almost surely
bounded by the given positive constant](hyp:hbound), [the treatment has one
coordinate](hyp:hT), [the outcome has one coordinate](hyp:hY), and [the dose bound
is nonnegative](hyp:hB). Then [there is a nonnegative uniform bound on the
absolute mean outcome for every dose within that bound whose treatment
intervention is admissible](goal). -/
lemma meanOutcome_uniformly_bounded
    (M : EuclideanSCM kind dims) (L : ℝ≥0)
    (hcont : ContinuousMechanismsLipschitz M L) (K : ℝ)
    (hbound : VariablesBoundedAt M K) (T Y : Fin n)
    (hT : valueDim (kind T) = 1) (hY : valueDim (kind Y) = 1)
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ t : ℝ, |t| ≤ B →
      AdmissibleIntervention kind (singleIntervention T t) →
        |meanOutcome M T Y hY t| ≤ R := by
  letI := M.probability
  obtain ⟨R, hR, hv⟩ := evalSteps_uniformly_bounded_of_nonGumbel_bounded
    M L hcont K B hB (n*n+n)
  refine ⟨R, hR, ?_⟩
  intro t ht hadm
  have htb : ∀ (i : Fin n) (v : L1Vec (valueDim (kind i))),
      singleIntervention T t i = some v → ‖v‖ ≤ B := by
    intro i v hi
    by_cases hiT : i = T
    · subst i
      have heq : WithLp.toLp 1 (fun _ : Fin (valueDim (kind T)) => t) = v := by
        simpa [singleIntervention] using hi
      rw [← heq, PiLp.norm_eq_of_L1]
      simpa [hT, Real.norm_eq_abs] using ht
    · simp [singleIntervention, hiT] at hi
  change ‖∫ u, scalarOutcome Y hY (intervenedEval M (singleIntervention T t) u)
    ∂M.latentLaw‖ ≤ R
  have hb : ∀ᵐ u ∂M.latentLaw,
      ‖scalarOutcome Y hY (intervenedEval M (singleIntervention T t) u)‖ ≤ R := by
    filter_upwards [hbound.2] with u hu
    exact hv _ hadm htb u hu.2 Y _
  simpa using norm_integral_le_of_norm_le_const hb

-- @node: meanOutcome_integrable_sq_of_bounded_doses
/-- For [a nonnegative Lipschitz constant](hyp:L), suppose [the continuous
mechanisms obey that Lipschitz bound on their admissible domains](hyp:hcont),
[observational coordinates and non-Gumbel block coordinates are almost surely
bounded by the given positive constant](hyp:hbound), [the treatment has one
coordinate](hyp:hT), [the outcome has one coordinate](hyp:hY), and [the dose bound
is nonnegative](hyp:hB). If [almost every dose under the finite reference measure
lies within that bound and defines an admissible treatment intervention](hyp:hdoses),
[the squared mean outcome is integrable under that reference measure](goal). -/
lemma meanOutcome_integrable_sq_of_bounded_doses
    (M : EuclideanSCM kind dims) (L : ℝ≥0)
    (hcont : ContinuousMechanismsLipschitz M L) (K : ℝ)
    (hbound : VariablesBoundedAt M K) (T Y : Fin n)
    (hT : valueDim (kind T) = 1) (hY : valueDim (kind Y) = 1)
    (rho : Measure ℝ) [IsFiniteMeasure rho] (B : ℝ) (hB : 0 ≤ B)
    (hdoses : ∀ᵐ t ∂rho, |t| ≤ B ∧
      AdmissibleIntervention kind (singleIntervention T t)) :
    Integrable (fun t => (meanOutcome M T Y hY t)^2) rho := by
  obtain ⟨R, hR, hm⟩ := meanOutcome_uniformly_bounded M L hcont K hbound T Y hT hY B hB
  apply Integrable.of_bound (by fun_prop) (R^2)
  filter_upwards [hdoses] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hR).2 (hm t ht.1 ht.2)

end Papers.TbsNeuralCausalPi

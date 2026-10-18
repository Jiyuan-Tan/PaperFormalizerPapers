module
public import Papers.TbsNeuralCausalPi.Setup.Assumptions.Estimation
public import Papers.TbsNeuralCausalPi.Setup.CitedResults
public import Papers.TbsNeuralCausalPi.Helpers.WassersteinBounds
public import Papers.TbsNeuralCausalPi.Helpers.ApproximationStep
public import Papers.TbsNeuralCausalPi.Helpers.ApproximationLatents
public import Papers.TbsNeuralCausalPi.Helpers.ApproximationTransport
public import Papers.TbsNeuralCausalPi.Helpers.ApproximationSelectorStep
public import Papers.TbsNeuralCausalPi.Helpers.ApproximationSchedule
public import Papers.TbsNeuralCausalPi.Helpers.ApproximationContinuous
public import Papers.TbsNeuralCausalPi.Helpers.ApproximationCategorical
/-! # Uniform comparison of canonical intervention laws -/
public section
namespace Papers.TbsNeuralCausalPi
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
noncomputable section
attribute [local instance] Classical.propDecidable

variable {n : ℕ} {kind : Fin n → NodeKind}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}

-- @node: thm:approximation
/-- For [a nonnegative Lipschitz bound L](hyp:L) and [a real magnitude bound K](hyp:K) that [is positive](hyp:hK), [there is a nonnegative comparison constant, chosen before latent block dimensions, structural classes, models, and interventions, such that the Wasserstein distance between the two models' laws under any common intervention is at most this constant times the sum of their uniform structural errors on the true model's domains and their latent-law Wasserstein distance, whenever the true mechanisms satisfy the L-Lipschitz restrictions, the comparison mechanisms belong to the chosen admissible class, the true latent blocks are independent with a Gumbel decomposition, categorical mechanisms use Gumbel argmax with L-Lipschitz propensities, continuous mechanisms are L-Lipschitz, and the true variables obey the bound K](goal). -/
theorem approximation_wasserstein_bound (L : ℝ≥0) (K : ℝ) (hK : 0 < K) :
    ∃ A : ℝ≥0, ∀ (b : ℕ) (dims : Fin b → ℕ) (C : Fin b → Set (Fin n)),
      ∀ (Fhat : AdmissibleStructuralClass kind dims dag C) (M Mhat : CanonicalSCM kind dims dag G C), -- @realizes C_{\mathcal{G}}(L,K)(comparison constant chosen before models and interventions) -- @realizes \hat{\mathcal{F}}(comparison structural class with no neural or Lipschitz requirement)
      M ∈ canonicalClass (domainLipClass M L) → Mhat ∈ canonicalClass Fhat →
      LatentBlocksIndependent M.toEuclideanSCM →
      LatentGumbelDecomposition M.toEuclideanSCM →
      CategoricalGumbelArgmax M.toEuclideanSCM M.f →
      ContinuousMechanismsLipschitz M.toEuclideanSCM L →
      CategoricalPropensityLipschitz M.toEuclideanSCM M.f L →
      VariablesBoundedAt M.toEuclideanSCM K →
      ∀ t : LawIntervention kind,
        wasserstein1 (interventionalLaw M.toEuclideanSCM t)
          (interventionalLaw Mhat.toEuclideanSCM t) ≤
          (A : ℝ≥0∞) * ((∑ i, supDistOn (M.domain i) (M.f i) (Mhat.f i)) +
            wasserstein1 M.latentLaw Mhat.latentLaw) := by
  classical
  let D : ℝ≥0 := (Finset.univ.sup (fun i : Fin n =>
    match kind i with
    | .inl _ => 0
    | .inr k => k - 1) : ℕ)
  let A : ℝ≥0 := max (1 + L) (1 + D * L / 2)
  let B : ℝ≥0 := max 1 (Finset.univ.sup (fun i : Fin n =>
    match kind i with
    | .inl d => (d : ℝ≥0)
    | .inr k => (k : ℝ≥0) * (k - 1 : ℕ) / 2))
  have hA : 1 ≤ A := le_trans (le_add_right le_rfl : 1 ≤ 1 + L) (le_max_left _ _)
  refine ⟨approximationPropagationConstant A B n, ?_⟩
  intro b dims C Fhat M Mhat hM hMhat hind hdecomp hcat hcont hprop hbound t
  apply approximation_interventional_bound_of_history_steps M Mhat t A B
    (∑ i, supDistOn (M.domain i) (M.f i) (Mhat.f i)) hA
  intro i
  cases hti : t.val i with
  | some v =>
    have htrans := approximationHistory_intervened_step_transport_le M Mhat t.val i v hti
    have hA' : (1 : ℝ≥0∞) ≤ (A : ℝ≥0∞) := by exact_mod_cast hA
    exact (htrans.trans (le_mul_of_one_le_left' hA')).trans (le_add_right le_rfl)
  | none =>
    cases hi : kind i with
    | inl d =>
      have hlocal := approximationHistory_continuous_step_transport_le M Mhat t i d hi hti L (hM i)
      have hAA : ((1 + L : ℝ≥0) : ℝ≥0∞) ≤ (A : ℝ≥0∞) := by
        exact_mod_cast (le_max_left (1+L) (1+D*L/2))
      have hdB : (d : ℝ≥0) ≤ B := by
        have hd := Finset.le_sup (f := fun j : Fin n =>
          match kind j with
          | .inl d => (d : ℝ≥0)
          | .inr k => (k : ℝ≥0) * (k - 1 : ℕ) / 2) (Finset.mem_univ i)
        apply le_trans ?_ (le_max_right _ _)
        simpa only [hi] using hd
      have hdB' : (d : ℝ≥0∞) ≤ (B : ℝ≥0∞) := by exact_mod_cast hdB
      have he : supDistOn (M.domain i) (M.f i) (Mhat.f i) ≤
          ∑ j, supDistOn (M.domain j) (M.f j) (Mhat.f j) :=
        Finset.single_le_sum (f := fun j => supDistOn (M.domain j) (M.f j) (Mhat.f j))
          (fun _ _ => zero_le) (Finset.mem_univ i)
      exact hlocal.trans (add_le_add (mul_le_mul' hAA le_rfl) (mul_le_mul' hdB' he))
    | inr k =>
      have hlocal := approximationHistory_categorical_step_transport_le M Mhat t i k hi hti L
        (hM i)
      have hkD : ((k-1 : ℕ) : ℝ≥0) ≤ D := by
        dsimp only [D]
        have hd := Finset.le_sup (f := fun j : Fin n =>
          match kind j with
          | .inl _ => 0
          | .inr k => k - 1) (Finset.mem_univ i)
        exact_mod_cast (show k - 1 ≤ (Finset.univ.sup (fun j : Fin n =>
          match kind j with
          | .inl _ => 0
          | .inr k => k - 1) : ℕ) from by simpa only [hi] using hd)
      have hAA : ((1 + (k-1 : ℕ) * L / 2 : ℝ≥0) : ℝ≥0∞) ≤ (A : ℝ≥0∞) := by
        have hh : (1 + (k-1 : ℕ) * L / 2 : ℝ≥0) ≤ 1 + D * L / 2 := by
          gcongr <;> first | fun_prop | assumption | positivity
        exact_mod_cast hh.trans (le_max_right (1+L) (1+D*L/2))
      have hkB : (k : ℝ≥0) * (k-1 : ℕ) / 2 ≤ B := by
        have hd := Finset.le_sup (f := fun j : Fin n =>
          match kind j with
          | .inl d => (d : ℝ≥0)
          | .inr k => (k : ℝ≥0) * (k - 1 : ℕ) / 2) (Finset.mem_univ i)
        apply le_trans ?_ (le_max_right _ _)
        simpa only [hi] using hd
      have hkB' : ((k * (k-1 : ℕ) / 2 : ℝ≥0) : ℝ≥0∞) ≤ (B : ℝ≥0∞) := by
        exact_mod_cast hkB
      have he : supDistOn (M.domain i) (M.f i) (Mhat.f i) ≤
          ∑ j, supDistOn (M.domain j) (M.f j) (Mhat.f j) :=
        Finset.single_le_sum (f := fun j => supDistOn (M.domain j) (M.f j) (Mhat.f j))
          (fun _ _ => zero_le) (Finset.mem_univ i)
      exact hlocal.trans (add_le_add (mul_le_mul' hAA le_rfl) (mul_le_mul' hkB' he))

end
end Papers.TbsNeuralCausalPi

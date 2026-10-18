module
public import Papers.TbsNeuralCausalPi.Helpers.BoundedHistoryTransport
public import Papers.TbsNeuralCausalPi.Helpers.ApproximationCategorical
public import Papers.TbsNeuralCausalPi.Helpers.DeepModelAssembly
/-! # Bounded true histories in the observational coupling recurrence -/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory Filter
open scoped NNReal ENNReal
noncomputable section

variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
  {C : Fin b → Set (Fin n)}

/-- For [a nonnegative bound K](hyp:K), if [the model's observed variables and
non-Gumbel latent coordinates are bounded by K](hyp:hbound), [almost every
observational history just before node i is admissible and supplies a structural
input in that node's admissible cube of radius K](goal). -/
-- @node: approximationHistoryInput_observational_bounded_ae
lemma approximationHistoryInput_observational_bounded_ae
    (M : CanonicalSCM kind dims dag G C) (K : ℝ≥0)
    (hbound : VariablesBoundedAt M.toEuclideanSCM K) (i : Fin n) :
    ∀ᵐ x ∂M.latentLaw.map (fun u => approximationHistory M.toEuclideanSCM
        (fun _ => none) u (dag.topoOrder i)),
      x ∈ approximationHistoryDomain (dag := dag) (dag.topoOrder i) ∧
        approximationHistoryInput (C := C) i x ∈
          M.domain i (some (-(K : ℝ), K)) := by
  apply (ae_map_iff (approximationHistory_measurable M.toEuclideanSCM
    (fun _ => none) _).aemeasurable (by
      apply (approximationHistoryDomain_measurableSet _).inter
      apply MeasurableSet.preimage _ (by fun_prop)
      apply (admissibleStructuralInputs_measurableSet dag (canonicalIncidence C) i).inter
      simp only [structuralInputDomain, Set.ofPred_forall]
      exact MeasurableSet.iInter fun j => measurableSet_Icc.preimage (by fun_prop))).2
  filter_upwards [hbound.2] with u hu
  have hx := approximationHistory_mem_domain M (noIntervention kind) u (dag.topoOrder i)
  refine ⟨hx, (approximationHistoryInput_mem_domain M i _ hx).1, ?_⟩
  rintro (⟨p,j⟩ | ⟨a,j⟩)
  · change (evalSteps M.toEuclideanSCM (fun _ => none) u (dag.topoOrder i)).ofLp
      ⟨p.val,j⟩ ∈ Set.Icc (-(K : ℝ)) K
    rw [evalSteps_coordinate_eq_intervenedEval M.toEuclideanSCM _ u p.val _
      (dag.topoOrder_lt _ _ (dag.mem_parents.mp p.property)) j]
    exact abs_le.mp (hu.1 p.val j)
  · exact abs_le.mp (hu.2 a.val j)

/-- For [nonnegative constants K and L](hyp:K,L), suppose [the true model's
observed variables and non-Gumbel latent coordinates are bounded by K](hyp:hbound),
[node i is continuous with d coordinates](hyp:hi), and [the candidate's mechanism
at i is L-Lipschitz on its admissible domain](hyp:hLip). Then [the Wasserstein
distance between observational histories after node i is at most 1 + L times
their distance before i plus d times the uniform mechanism error on the true
admissible input cube of radius K](goal). -/
-- @node: approximationHistory_continuous_bounded_step
lemma approximationHistory_continuous_bounded_step
    (M N : CanonicalSCM kind dims dag G C) (K L : ℝ≥0)
    (hbound : VariablesBoundedAt M.toEuclideanSCM K)
    (i : Fin n) (d : ℕ) (hi : kind i = .inl d)
    (hLip : LipschitzOnWith L (N.f i) (N.domain i)) :
    wasserstein1
      (M.latentLaw.map (fun u => approximationHistory M.toEuclideanSCM
        (fun _ => none) u (dag.topoOrder i + 1)))
      (N.latentLaw.map (fun u => approximationHistory N.toEuclideanSCM
        (fun _ => none) u (dag.topoOrder i + 1))) ≤
      ((1 + L : ℝ≥0) : ℝ≥0∞) * wasserstein1
        (M.latentLaw.map (fun u => approximationHistory M.toEuclideanSCM
          (fun _ => none) u (dag.topoOrder i)))
        (N.latentLaw.map (fun u => approximationHistory N.toEuclideanSCM
          (fun _ => none) u (dag.topoOrder i))) +
      (d : ℝ≥0∞) * supDistOn (M.domain i (some (-(K : ℝ), K))) (M.f i) (N.f i) := by
  letI := M.latentLaw_probability
  letI := N.latentLaw_probability
  letI : IsProbabilityMeasure (M.latentLaw.map (fun u => approximationHistory
      M.toEuclideanSCM (fun _ => none) u (dag.topoOrder i))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  letI : IsProbabilityMeasure (N.latentLaw.map (fun u => approximationHistory
      N.toEuclideanSCM (fun _ => none) u (dag.topoOrder i))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  let T := approximationHistoryDomain (kind := kind) (dims := dims) (dag := dag)
    (dag.topoOrder i)
  let S := {x ∈ T | approximationHistoryInput (C := C) i x ∈
    M.domain i (some (-(K : ℝ), K))}
  have hcarry : ∀ᵐ x ∂N.latentLaw.map (fun u => approximationHistory N.toEuclideanSCM
      (fun _ => none) u (dag.topoOrder i)), x ∈ T := by
    apply (ae_map_iff (approximationHistory_measurable N.toEuclideanSCM
      (fun _ => none) _).aemeasurable (approximationHistoryDomain_measurableSet _)).2
    exact Filter.Eventually.of_forall fun u =>
      approximationHistory_mem_domain N (noIntervention kind) u _
  have h := approximation_wasserstein_map_perturbation_left_le _ _ S T
    (fun _ hx => hx.1) (approximationHistoryInput_observational_bounded_ae M K hbound i)
    hcarry (approximationContinuousUpdate M i d hi) (approximationContinuousUpdate N i d hi)
    (by fun_prop) (by fun_prop) (1 + L)
    (approximationContinuousUpdate_lipschitzOn N i d hi L hLip)
    ((d : ℝ≥0∞) * supDistOn (M.domain i (some (-(K : ℝ), K))) (M.f i) (N.f i)) (by
      intro x hx
      have h := approximationHistorySetNode_edist_values_le i
        (approximationContinuousValue M i d hi x) (approximationContinuousValue N i d hi x) x
      rw [approximationContinuousValue_edist] at h
      exact h.trans (by
        simpa only [hi, outputDim] using approximation_edist_le_dim_supDistOn
          (M.domain i (some (-(K : ℝ), K))) (M.f i) (N.f i) hx.2))
  rw [Measure.map_map (by fun_prop)
      (approximationHistory_measurable M.toEuclideanSCM (fun _ => none) _),
    Measure.map_map (by fun_prop)
      (approximationHistory_measurable N.toEuclideanSCM (fun _ => none) _)] at h
  simpa only [Function.comp_def, approximationContinuousUpdate,
    ← approximationHistory_continuous_step_eq _ (fun _ => none) i d hi rfl] using h

/-- For [nonnegative constants K and L](hyp:K,L), suppose [the true model's
observed variables and non-Gumbel latent coordinates are bounded by K](hyp:hbound),
[node i has k categories](hyp:hi), and [the candidate's propensity map at i is
L-Lipschitz on its admissible domain](hyp:hLip). Then [the Wasserstein distance
between observational histories after i is at most 1 + (k − 1)L/2 times their
distance before i plus k(k − 1)/2 times the uniform propensity error on the true
admissible input cube of radius K](goal). -/
-- @node: approximationHistory_categorical_bounded_step
lemma approximationHistory_categorical_bounded_step
    (M N : CanonicalSCM kind dims dag G C) (K L : ℝ≥0)
    (hbound : VariablesBoundedAt M.toEuclideanSCM K)
    (i : Fin n) (k : ℕ) (hi : kind i = .inr k)
    (hLip : LipschitzOnWith L (N.f i) (N.domain i)) :
    wasserstein1
      (M.latentLaw.map (fun u => approximationHistory M.toEuclideanSCM
        (fun _ => none) u (dag.topoOrder i + 1)))
      (N.latentLaw.map (fun u => approximationHistory N.toEuclideanSCM
        (fun _ => none) u (dag.topoOrder i + 1))) ≤
      ((1 + (k-1 : ℕ) * L / 2 : ℝ≥0) : ℝ≥0∞) * wasserstein1
        (M.latentLaw.map (fun u => approximationHistory M.toEuclideanSCM
          (fun _ => none) u (dag.topoOrder i)))
        (N.latentLaw.map (fun u => approximationHistory N.toEuclideanSCM
          (fun _ => none) u (dag.topoOrder i))) +
      ((k * (k-1 : ℕ) / 2 : ℝ≥0) : ℝ≥0∞) *
        supDistOn (M.domain i (some (-(K : ℝ), K))) (M.f i) (N.f i) := by
  letI := M.latentLaw_probability
  letI := N.latentLaw_probability
  let mu := M.latentLaw.map (fun u => approximationHistory M.toEuclideanSCM
    (fun _ => none) u (dag.topoOrder i))
  let nu := N.latentLaw.map (fun u => approximationHistory N.toEuclideanSCM
    (fun _ => none) u (dag.topoOrder i))
  letI : IsProbabilityMeasure mu := Measure.isProbabilityMeasure_map (by fun_prop)
  letI : IsProbabilityMeasure nu := Measure.isProbabilityMeasure_map (by fun_prop)
  let T := approximationHistoryDomain (kind := kind) (dims := dims) (dag := dag)
    (dag.topoOrder i)
  let S := {x ∈ T | approximationHistoryInput (C := C) i x ∈
    M.domain i (some (-(K : ℝ), K))}
  have hcarry : ∀ᵐ x ∂nu, x ∈ T := by
    apply (ae_map_iff (approximationHistory_measurable N.toEuclideanSCM
      (fun _ => none) _).aemeasurable (approximationHistoryDomain_measurableSet _)).2
    exact Filter.Eventually.of_forall fun u =>
      approximationHistory_mem_domain N (noIntervention kind) u _
  have hsup : supDistOn S (approximationHistoryPropensity M i k hi)
      (approximationHistoryPropensity N i k hi) ≤
      supDistOn (M.domain i (some (-(K : ℝ), K))) (M.f i) (N.f i) := by
    apply iSup_le
    intro x
    apply le_iSup_of_le (⟨approximationHistoryInput i x.val, x.property.2⟩ :
      M.domain i (some (-(K : ℝ), K)))
    apply ENNReal.ofReal_le_ofReal
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
    intro j
    exact norm_le_pi_norm
      ((M.f i (approximationHistoryInput i x.val) -
        N.f i (approximationHistoryInput i x.val)).ofLp)
      (Fin.cast (congrArg outputDim hi).symm j)
  have h := approximation_selector_history_step_left
    (fun m hm => M.positive_categories i m (hi.trans hm)) mu nu S T
    (approximationHistoryDomain_measurableSet _) (fun _ hx => hx.1)
    (approximationHistoryInput_observational_bounded_ae M K hbound i) hcarry
    (approximationHistoryPropensity M i k hi) (approximationHistoryPropensity N i k hi)
    (by fun_prop) (by fun_prop)
    (approximationHistoryPropensity_simplex M i k hi)
    (approximationHistoryPropensity_simplex N i k hi)
    (approximationCategoricalUpdate i k) (by fun_prop) L (k-1 : ℕ)
    (approximationHistoryPropensity_lipschitzOn N i k hi L hLip)
    (fun x _ y _ a c => approximationCategoricalUpdate_dist_le i k hi x y a c)
  have h' := h.trans (add_le_add le_rfl (mul_le_mul' le_rfl hsup))
  rw [approximationHistory_categorical_successor_law_of_noise_law M
      (canonical_latent_blocks_independent M) (fun _ => none) i k hi rfl
      (canonical_categorical_noise_law M i k hi),
    approximationHistory_categorical_successor_law_of_noise_law N
      (canonical_latent_blocks_independent N) (fun _ => none) i k hi rfl
      (canonical_categorical_noise_law N i k hi)]
  exact h'

/-- For [a nonnegative Lipschitz bound L](hyp:L), [there is a positive constant Q
such that, whenever the true model's observed and non-Gumbel latent variables
are bounded by K and every candidate mechanism is L-Lipschitz on its admissible
domain, the observational Wasserstein distance is at most Q times the sum of
uniform mechanism errors on the true input cubes of radius K and the
Wasserstein distances between corresponding latent block laws](goal). -/
-- @node: bounded_observational_wasserstein_bound_left
lemma bounded_observational_wasserstein_bound_left (L : ℝ≥0) :
    ∃ Q : ℝ≥0, 0 < Q ∧ ∀ (M N : CanonicalSCM kind dims dag G C) (K : ℝ≥0),
      VariablesBoundedAt M.toEuclideanSCM K →
      (∀ i, LipschitzOnWith L (N.f i) (N.domain i)) →
      wasserstein1 (observationalLaw M.toEuclideanSCM)
        (observationalLaw N.toEuclideanSCM) ≤
        (Q : ℝ≥0∞) * ((∑ i,
          supDistOn (M.domain i (some (-(K : ℝ), K))) (M.f i) (N.f i)) +
          ∑ j, wasserstein1 (M.blockLaw j : Measure (L1Vec (dims j)))
            (N.blockLaw j : Measure (L1Vec (dims j)))) := by
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
  refine ⟨approximationPropagationConstant A B n + 1, by positivity, ?_⟩
  intro M N K hbound hLip
  have hlocal := approximation_interventional_bound_of_history_steps M N
    (noIntervention kind) A B
    (∑ i, supDistOn (M.domain i (some (-(K : ℝ), K))) (M.f i) (N.f i)) hA ?_
  · apply hlocal.trans
    apply mul_le_mul'
    · exact_mod_cast (le_add_of_nonneg_right (by positivity : (0 : ℝ≥0) ≤ 1) :
        approximationPropagationConstant A B n ≤ approximationPropagationConstant A B n + 1)
    · exact add_le_add le_rfl (deep_ncm_latent_error_le_sum M N)
  intro i
  have he : supDistOn (M.domain i (some (-(K : ℝ), K))) (M.f i) (N.f i) ≤
      ∑ j, supDistOn (M.domain j (some (-(K : ℝ), K))) (M.f j) (N.f j) :=
    Finset.single_le_sum (f := fun j =>
      supDistOn (M.domain j (some (-(K : ℝ), K))) (M.f j) (N.f j))
      (fun _ _ => zero_le) (Finset.mem_univ i)
  cases hi : kind i with
  | inl d =>
    have h := approximationHistory_continuous_bounded_step M N K L hbound i d hi (hLip i)
    have hAA : ((1 + L : ℝ≥0) : ℝ≥0∞) ≤ (A : ℝ≥0∞) := by
      exact_mod_cast (le_max_left (1 + L) (1 + D * L / 2))
    have hdB : (d : ℝ≥0) ≤ B := by
      have hd := Finset.le_sup (f := fun j : Fin n =>
        match kind j with
        | .inl d => (d : ℝ≥0)
        | .inr k => (k : ℝ≥0) * (k - 1 : ℕ) / 2) (Finset.mem_univ i)
      apply le_trans ?_ (le_max_right _ _)
      simpa only [hi] using hd
    have hdB' : (d : ℝ≥0∞) ≤ (B : ℝ≥0∞) := by exact_mod_cast hdB
    exact h.trans (add_le_add (mul_le_mul' hAA le_rfl) (mul_le_mul' hdB' he))
  | inr k =>
    have h := approximationHistory_categorical_bounded_step M N K L hbound i k hi (hLip i)
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
        gcongr
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
    exact h.trans (add_le_add (mul_le_mul' hAA le_rfl) (mul_le_mul' hkB' he))

end
end Papers.TbsNeuralCausalPi

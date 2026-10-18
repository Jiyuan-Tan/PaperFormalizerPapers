module
public import Papers.TbsNeuralCausalPi.Helpers.BoxApproximation
public import Papers.TbsNeuralCausalPi.Helpers.GeneratorMixtureLaw
public import Papers.TbsNeuralCausalPi.Helpers.ApproximationLatents
/-! # Neural causal model assembly from structural and latent networks -/
public section
namespace Papers.TbsNeuralCausalPi
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped NNReal ENNReal
noncomputable section

variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)} {C : Fin b → Set (Fin n)}

-- @node: networkOnStructuralInput_finiteCoordinates
/-- For [a canonical causal model](hyp:M), [a node](hyp:i), [a ReLU network with
that node's input and output dimensions](hyp:q), and [an input vector](hyp:x),
[evaluating the network through the model's structural input coordinates gives
the same output as evaluating it directly on the vector](goal). -/
lemma networkOnStructuralInput_finiteCoordinates (M : CanonicalSCM kind dims dag G C)
    (i : Fin n) {W L : ℕ}
    (q : ReLUNet (structuralInputSize M.toEuclideanSCM i) (outputDim (kind i)) W L)
    (x : L1Vec (structuralInputSize M.toEuclideanSCM i)) :
    networkOnStructuralInput M i q (structuralFiniteCoordinates M.toEuclideanSCM i x) =
      q.eval x := by
  unfold networkOnStructuralInput structuralFiniteCoordinates
  congr 1
  apply PiLp.ext
  intro j
  change x.ofLp ((Fintype.equivFin _) ((Fintype.equivFin _).symm j)) = x.ofLp j
  rw [Equiv.apply_symm_apply]

/-- Given [a canonical causal model](hyp:M), [latent component counts](hyp:counts),
[chart dimensions](hyp:dC), [structural ReLU networks](hyp:q),
[three-part latent generators](hyp:Q), [structural function classes](hyp:F0),
and [generator classes](hyp:F1), suppose [the structural networks belong to their classes](hyp:hF0),
[the generators belong to their classes](hyp:hF1), and [every categorical network
output on the model's domain is nonnegative with positive total mass](hyp:hmass).
[There exists a neural causal model in those classes whose raw structural functions
are the given networks, whose categorical structural outputs are divided by their
coordinate sum while continuous outputs are retained, and whose independent latent
block laws are the given generator laws](goal). -/
-- @node: deep_ncm_of_networks
lemma deep_ncm_of_networks (M : CanonicalSCM kind dims dag G C)
    (counts : Fin b → ℕ) (dC : ∀ j, Fin (counts j) → ℕ)
    {W0 L0 W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (q : ∀ i, ReLUNet (structuralInputSize M.toEuclideanSCM i)
      (outputDim (kind i)) W0 L0)
    (Q : ∀ j, ThreePartGenerator (counts j) (dims j) (dC j) W1 L1 W2 L2 tau)
    (F0 : StructuralClass kind dims dag C) (F1 : GeneratorClass dims counts)
    (hF0 : ∀ i, networkOnStructuralInput M i (q i) ∈ F0 i)
    (hF1 : ∀ j, (Q j).eval ∈ F1 j)
    (hmass : ∀ i k, kind i = Sum.inr k → ∀ x ∈ M.domain i,
      (∀ j, 0 ≤ (networkOnStructuralInput M i (q i) x).ofLp j) ∧
        0 < ∑ j, (networkOnStructuralInput M i (q i) x).ofLp j) :
    ∃ N : NCMIn kind dims dag G C counts F0 F1,
      (∀ i, N.rawStructural i = networkOnStructuralInput M i (q i)) ∧
      (∀ i x, N.canonical.f i x =
        if (kind i).isRight then WithLp.toLp 1 (fun j =>
          (networkOnStructuralInput M i (q i) x).ofLp j /
            ∑ l, (networkOnStructuralInput M i (q i) x).ofLp l)
        else networkOnStructuralInput M i (q i) x) ∧
      (∀ j, (N.canonical.blockLaw j : Measure _) = generatorLaw (Q j)) := by
  classical
  let raw := fun i => networkOnStructuralInput M i (q i)
  have hraw (i) : Measurable (raw i) := by
    unfold raw networkOnStructuralInput
    apply (q i).eval_measurable.comp
    fun_prop
  let f := fun i x => if (kind i).isRight then WithLp.toLp 1
    (fun j => (raw i x).ofLp j / ∑ l, (raw i x).ofLp l) else raw i x
  have hf (i) : Measurable (f i) := by
    dsimp only [f]
    have hr := hraw i
    split_ifs <;> fun_prop
  let law (j : Fin b) : ProbabilityMeasure (L1Vec (dims j)) := by
    letI := generatorInputLaw_probability (counts j)
    exact ⟨generatorLaw (Q j), Measure.isProbabilityMeasure_map (by fun_prop)⟩
  let N : CanonicalSCM kind dims dag G C := {
    categoricalPositive := M.categoricalPositive
    component := M.component
    exhaustive := M.exhaustive
    distinct := M.distinct
    f := f
    structuralMeasurable := hf
    blockLaw := law
    simplex := by
      intro i k hi x hx
      have hm := hmass i k hi x (by exact ⟨hx, Set.mem_univ x⟩)
      have hp := canonical_normalized_mem_simplex (raw i x).ofLp hm.1 hm.2
      simp only [f, hi, Sum.isRight_inr, ↓reduceIte, WithLp.ofLp_toLp]
      refine ⟨fun j => hp.1 _, ?_⟩
      exact (Equiv.sum_comp (finCongr (congrArg outputDim hi).symm)
        (fun j => (raw i x).ofLp j / ∑ l, (raw i x).ofLp l)).trans hp.2 }
  refine ⟨{
    canonical := N
    rawStructural := raw
    structuralMem := hF0
    structuralNetworks := ?_
    continuousEq := ?_
    categoricalEq := ?_
    generator := fun j => (Q j).eval
    generatorMem := hF1
    generatorNetworks := ?_
    blockLaw_eq := fun _ => rfl }, fun _ => rfl, fun _ _ => rfl, fun _ => rfl⟩
  · intro i
    refine ⟨W0, L0, q i, ?_⟩
    intro x
    dsimp only [raw, networkOnStructuralInput, structuralFiniteCoordinates]
    congr 1
    apply PiLp.ext
    intro j
    change x.ofLp ((Fintype.equivFin _ ) ((Fintype.equivFin _).symm j)) = x.ofLp j
    rw [Equiv.apply_symm_apply]
  · intro i d hi
    funext x
    simp only [N, f, hi, Sum.isRight_inl, Bool.false_eq_true, ↓reduceIte]
  · intro i k hi
    refine ⟨fun x hx _ _ => ?_, ?_⟩
    · simp only [N, f, hi, Sum.isRight_inr, ↓reduceIte]
    · exact hmass i k hi
  · intro j
    exact Or.inr ⟨dC j, W1, L1, W2, L2, tau, Q j, Or.inl rfl⟩

/-- For [two canonical causal models with the same node types and latent block
dimensions](hyp:M,N), [the Wasserstein distance between their full latent laws is
at most the sum of the Wasserstein distances between corresponding private block laws](goal). -/
-- @node: deep_ncm_latent_error_le_sum
lemma deep_ncm_latent_error_le_sum (M N : CanonicalSCM kind dims dag G C) :
    wasserstein1 M.latentLaw N.latentLaw ≤
      ∑ j, wasserstein1 (M.blockLaw j : Measure _) (N.blockLaw j : Measure (L1Vec (dims j))) := by
  rw [canonical_latent_wasserstein_eq_nonGumbel]
  by_cases hb : 1 ≤ b
  · let (j : Fin b) := (M.blockLaw j).prop
    let (j : Fin b) := (N.blockLaw j).prop
    exact wasserstein_pi_le dims _ _
  · have hb0 : b = 0 := by omega
    subst b
    have he : (fun j => (M.blockLaw j : Measure (L1Vec (dims j)))) =
        (fun j => (N.blockLaw j : Measure (L1Vec (dims j)))) := by
      funext j
      exact Fin.elim0 j
    rw [he]
    let rho := (Measure.pi (fun j => (N.blockLaw j : Measure (L1Vec (dims j))))).map
      (fun z => WithLp.toLp 1 (fun c : Σ j, Fin (dims j) => (z c.1).ofLp c.2))
    let (j : Fin 0) : IsProbabilityMeasure (N.blockLaw j : Measure (L1Vec (dims j))) :=
      (N.blockLaw j).prop
    let : IsProbabilityMeasure rho := Measure.isProbabilityMeasure_map
      (show Measurable (fun z : ∀ j, L1Vec (dims j) => WithLp.toLp 1
        (fun c : Σ j, Fin (dims j) => (z c.1).ofLp c.2)) from by fun_prop).aemeasurable
    have hc : Causalean.Stat.IsCoupling (rho.prod rho) rho rho :=
      ⟨inferInstance, by simp, by simp⟩
    calc
      wasserstein1 rho rho ≤ ∫⁻ z, edist z.1 z.2 ∂rho.prod rho :=
        Toolkit.Foundations.MeasureTheory.wasserstein1_le_cost hc
      _ = 0 := by
        have hall (x y : WithLp 1 ((Σ j : Fin 0, Fin (dims j)) → ℝ)) : x = y := by
          apply PiLp.ext
          intro c
          exact Fin.elim0 c.1
        have hz : (fun z : WithLp 1 ((Σ j : Fin 0, Fin (dims j)) → ℝ) ×
            WithLp 1 ((Σ j : Fin 0, Fin (dims j)) → ℝ) => edist z.1 z.2) = 0 := by
          funext z
          rw [hall z.1 z.2, edist_self]
          rfl
        rw [hz]
        change (∫⁻ _, 0 ∂rho.prod rho) = 0
        exact lintegral_zero
      _ ≤ _ := bot_le

/-- For [a canonical causal model](hyp:M), [a structural Lipschitz bound](hyp:L),
and [a truncation bound](hyp:B), assume [each categorical label count is at most
the truncation bound](hyp:hlabels), [the model's structural functions satisfy the
domain Lipschitz restrictions](hyp:hclass), [the maximum structural input dimension
is positive](hyp:hdin), and [the structural approximation theorem holds](hyp:hgate).
[There exist a positive error constant, a positive width factor, and a depth threshold
such that every larger depth and every family of latent generators in prescribed
generator classes admit a neural causal model in those classes, with structural
network width the chosen factor times the maximum input and output dimensions,
uniform structural error relative to the truncated model on each full domain at
most the constant times depth to the power minus two over the maximum input dimension,
and full latent Wasserstein error at most the sum of the block generator errors](goal). -/
-- @node: deep_ncm_structural_networks
lemma deep_ncm_structural_networks
    (M : CanonicalSCM kind dims dag G C) (L B : ℝ≥0)
    (hlabels : ∀ i k, kind i = Sum.inr k → (k : ℝ) ≤ B)
    (hclass : M ∈ canonicalClass (domainLipClass M L))
    (hdin : 0 < maxInDim M.toEuclideanSCM)
    (hgate : YarotskyStructuralApprox) :
    ∃ A : ℝ, 0 < A ∧ ∃ c0 B0 : ℕ, 0 < c0 ∧ 1 ≤ B0 ∧
      ∀ L0 : ℕ, B0 ≤ L0 →
      ∀ (counts : Fin b → ℕ) (dC : ∀ j, Fin (counts j) → ℕ)
        (W1 L1 W2 L2 : ℕ) (tau : ℝ)
        (Q : ∀ j, ThreePartGenerator (counts j) (dims j) (dC j) W1 L1 W2 L2 tau)
        (F1 : GeneratorClass dims counts),
        (∀ j, (Q j).eval ∈ F1 j) →
        ∃ N : NCMIn kind dims dag G C counts
          (fun i => {f | ∃ q : ReLUNet (structuralInputSize M.toEuclideanSCM i)
            (outputDim (kind i))
            (c0 * maxInDim M.toEuclideanSCM * maxOutDim M.toEuclideanSCM) L0,
            ∀ x, f (structuralFiniteCoordinates M.toEuclideanSCM i x) = q.eval x}) F1,
          (∀ i, supDistOn (M.domain i) ((boxTruncatedSCM M B hlabels).f i)
            (N.canonical.f i) ≤
            ENNReal.ofReal (A * (L0 : ℝ)^(-(2 : ℝ)/maxInDim M.toEuclideanSCM))) ∧
          wasserstein1 M.latentLaw N.canonical.latentLaw ≤
            ∑ j, wasserstein1 (M.blockLaw j : Measure _) (generatorLaw (Q j)) := by
  obtain ⟨A, hA, c0, B0, hc0, hB0, happ⟩ :=
    box_structural_approx M L B hlabels hclass hdin hgate
  refine ⟨A, hA, c0, B0, hc0, hB0, ?_⟩
  intro L0 hL0 counts dC W1 L1 W2 L2 tau Q F1 hF1
  obtain ⟨q, hmass, herr⟩ := happ L0 hL0
  obtain ⟨N, hraw, hf, hlaw⟩ := deep_ncm_of_networks M counts dC q Q
    (fun i => {f | ∃ q : ReLUNet (structuralInputSize M.toEuclideanSCM i)
      (outputDim (kind i))
      (c0 * maxInDim M.toEuclideanSCM * maxOutDim M.toEuclideanSCM) L0,
      ∀ x, f (structuralFiniteCoordinates M.toEuclideanSCM i x) = q.eval x}) F1
    (fun i => ⟨q i, networkOnStructuralInput_finiteCoordinates M i (q i)⟩) hF1 hmass
  refine ⟨N, ?_, ?_⟩
  · intro i
    have heq : N.canonical.f i = fun x => if (kind i).isRight then
        WithLp.toLp 1 (fun j => (networkOnStructuralInput M i (q i) x).ofLp j /
          ∑ l, (networkOnStructuralInput M i (q i) x).ofLp l)
        else networkOnStructuralInput M i (q i) x := funext (hf i)
    rw [heq]
    exact herr i
  · calc
      _ ≤ ∑ j, wasserstein1 (M.blockLaw j : Measure (L1Vec (dims j)))
          (N.canonical.blockLaw j : Measure (L1Vec (dims j))) :=
        deep_ncm_latent_error_le_sum M N.canonical
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hlaw j]


/-- Given [a canonical causal model](hyp:M), [a structural Lipschitz bound](hyp:L),
and [a truncation bound](hyp:B), suppose [all categorical label counts are at most
that bound](hyp:hlabels), [the model belongs to the domain Lipschitz class](hyp:hclass),
[its maximum structural input dimension is positive](hyp:hdin), and
[structural approximation is available](hyp:hgate). [There are a positive error
constant and a depth threshold such that every larger depth and every family of
latent generators in specified generator classes admit a neural causal model in
those classes, with structural network width the universal structural width factor
times the maximum input and output dimensions, uniform error relative to the truncated
model on every full structural domain bounded by the constant times depth to the power
minus two over the maximum input dimension, and latent Wasserstein error bounded by
the sum of the private block generator errors](goal). -/
lemma deep_ncm_structural_networks_explicit
    (M : CanonicalSCM kind dims dag G C) (L B : ℝ≥0)
    (hlabels : ∀ i k, kind i = Sum.inr k → (k : ℝ) ≤ B)
    (hclass : M ∈ canonicalClass (domainLipClass M L))
    (hdin : 0 < maxInDim M.toEuclideanSCM)
    (hgate : YarotskyStructuralApprox) :
    ∃ A : ℝ, 0 < A ∧ ∃ B0 : ℕ, 1 ≤ B0 ∧
      ∀ L0 : ℕ, B0 ≤ L0 →
      ∀ (counts : Fin b → ℕ) (dC : ∀ j, Fin (counts j) → ℕ)
        (W1 L1 W2 L2 : ℕ) (tau : ℝ)
        (Q : ∀ j, ThreePartGenerator (counts j) (dims j) (dC j) W1 L1 W2 L2 tau)
        (F1 : GeneratorClass dims counts),
        (∀ j, (Q j).eval ∈ F1 j) →
        ∃ N : NCMIn kind dims dag G C counts
          (fun i => {f | ∃ q : ReLUNet (structuralInputSize M.toEuclideanSCM i)
            (outputDim (kind i))
            (deepStructuralWidthFactor * maxInDim M.toEuclideanSCM * maxOutDim M.toEuclideanSCM) L0,
            ∀ x, f (structuralFiniteCoordinates M.toEuclideanSCM i x) = q.eval x}) F1,
          (∀ i, supDistOn (M.domain i) ((boxTruncatedSCM M B hlabels).f i)
            (N.canonical.f i) ≤
            ENNReal.ofReal (A * (L0 : ℝ)^(-(2 : ℝ)/maxInDim M.toEuclideanSCM))) ∧
          wasserstein1 M.latentLaw N.canonical.latentLaw ≤
            ∑ j, wasserstein1 (M.blockLaw j : Measure _) (generatorLaw (Q j)) := by
  obtain ⟨A, hA, B0, hB0, happ⟩ :=
    box_structural_approx_explicit M L B hlabels hclass hdin hgate
  refine ⟨A, hA, B0, hB0, ?_⟩
  intro L0 hL0 counts dC W1 L1 W2 L2 tau Q F1 hF1
  obtain ⟨q, hmass, herr⟩ := happ L0 hL0
  obtain ⟨N, hraw, hf, hlaw⟩ := deep_ncm_of_networks M counts dC q Q
    (fun i => {f | ∃ q : ReLUNet (structuralInputSize M.toEuclideanSCM i)
      (outputDim (kind i))
      (deepStructuralWidthFactor * maxInDim M.toEuclideanSCM * maxOutDim M.toEuclideanSCM) L0,
      ∀ x, f (structuralFiniteCoordinates M.toEuclideanSCM i x) = q.eval x}) F1
    (fun i => ⟨q i, networkOnStructuralInput_finiteCoordinates M i (q i)⟩) hF1 hmass
  refine ⟨N, ?_, ?_⟩
  · intro i
    have heq : N.canonical.f i = fun x => if (kind i).isRight then
        WithLp.toLp 1 (fun j => (networkOnStructuralInput M i (q i) x).ofLp j /
          ∑ l, (networkOnStructuralInput M i (q i) x).ofLp l)
        else networkOnStructuralInput M i (q i) x := funext (hf i)
    rw [heq]
    exact herr i
  · calc
      _ ≤ ∑ j, wasserstein1 (M.blockLaw j : Measure (L1Vec (dims j)))
          (N.canonical.blockLaw j : Measure (L1Vec (dims j))) :=
        deep_ncm_latent_error_le_sum M N.canonical
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hlaw j]

end
end Papers.TbsNeuralCausalPi

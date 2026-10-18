module
public import Papers.TbsNeuralCausalPi.Helpers.ArchitecturePremises
public import Papers.TbsNeuralCausalPi.Helpers.StructuralCanonicalExtension
public import Papers.TbsNeuralCausalPi.Helpers.StructuralScalarExtension
public import Papers.TbsNeuralCausalPi.Helpers.StructuralSliceExtension
public import Papers.TbsNeuralCausalPi.Helpers.StructuralSimplexExtension
public import Papers.TbsNeuralCausalPi.Helpers.GeneratorArchitectureBudgets
public import Papers.TbsNeuralCausalPi.Helpers.InterventionDomains
public import Papers.TbsNeuralCausalPi.Helpers.DoseResponseRegression
/-! # Combining structural extensions and clipped latent generator budgets

The all-continuous branch uses the true full-domain maps directly. Scalar
continuous and binary categorical nodes also have exact range-preserving
extensions when their parents include categorical variables.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
open scoped NNReal ENNReal
noncomputable section
variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)} {C : Fin b → Set (Fin n)}

-- @node: variablesBoundedAt_one_le_of_categorical
/-- If [the model's variables obey the common bound K](hyp:hbound) and
[node i is categorical with k categories](hyp:hi), then [K is at least
one](goal), because categorical labels are numbered starting at one. -/
lemma variablesBoundedAt_one_le_of_categorical
    (M : EuclideanSCM kind dims) (K : ℝ) (hbound : VariablesBoundedAt M K)
    (i : Fin n) (k : ℕ) (hi : kind i = .inr k) : 1 ≤ K := by
  let := M.probability
  obtain ⟨u, hu⟩ := hbound.2.exists
  obtain ⟨label, hlabel⟩ := evalSteps_intervention_categorical_label M
    (fun _ => none) (noIntervention_admissible kind) u i k hi
    (n * n + n) (scm_topoOrder_lt_horizon M i)
  let j : Fin (valueDim (kind i)) := ⟨0, by simp [hi, valueDim]⟩
  have hb := hu.1 i j
  change |(evalSteps M (fun _ => none) u (n * n + n)).ofLp ⟨i,j⟩| ≤ K at hb
  rw [hlabel j, abs_of_nonneg (by positivity)] at hb
  have hpos : (1 : ℝ) ≤ (label.val + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  exact hpos.trans hb

-- @node: architecture_thresholds_of_cube_extension
/-- For [nonnegative mechanism regularity and output bounds L and K](hyp:L,K),
[latent component sets](hyp:sets), [their chart dimensions](hyp:dC), and
[a nonnegative chart regularity bound](hyp:Lchart), suppose [the model and
components satisfy the architecture construction premises](hyp:hmodel) and
[the Yarotsky coordinate approximation result holds](hyp:hgate). Given
[structural extensions f on ambient input spaces](hyp:f) that [are Lipschitz
on the input boxes with the dimension-adjusted bound](hyp:hf), [have continuous
outputs of one-norm at most K](hyp:hcont), [have categorical outputs in the
probability simplex](hyp:hcat), and [agree with the original mechanisms on
their box-restricted domains](hyp:hagree), [there exist three positive
architecture thresholds that are admissible factors for themselves and certify
the structural and latent network constructions for these data](goal). -/
lemma architecture_thresholds_of_cube_extension
    (M : CanonicalSCM kind dims dag G C) (L K : ℝ≥0) (counts : Fin b → ℕ)
    (sets : ∀ j, Fin (counts j) → Set (L1Vec (dims j)))
    (dC : ∀ j, Fin (counts j) → ℕ) (Lchart : ℝ≥0)
    (hmodel : ArchitectureConstructionPremises M L K counts sets dC Lchart)
    (hgate : YarotskyCoordinateApprox)
    (f : ∀ i, Input kind dims dag C i → L1Vec (outputDim (kind i)))
    (hf : ∀ i, LipschitzOnWith (LhatF M.toEuclideanSCM L) (f i) (inputCube K i))
    (hcont : ∀ i, (kind i).isLeft = true → ∀ x ∈ inputCube K i, ‖f i x‖ ≤ K)
    (hcat : ∀ i, (kind i).isRight = true → ∀ x ∈ inputCube K i,
      (f i x).ofLp ∈ probabilitySimplex (outputDim (kind i)))
    (hagree : ∀ i x, x ∈ M.domain i (some (-(K : ℝ), K)) → f i x = M.f i x) :
    ∃ a : ℕ × ℕ × ℕ,
      ArchitectureFactorSelection a.1 a.2.1 a.2.2 a.1 a.2.1 a.2.2 ∧
      ArchitectureConstructionThresholds M K (LhatF M.toEuclideanSCM L)
        counts dC a.1 a.2.1 a.2.2 := by
  classical
  rcases hmodel with ⟨hind, hdec, harg, hbound, hreg, hdim, hunit,
    hLip, hprop, hstruct, hout, hsupp, hcharts, hdom, hboundary⟩
  have hcatK (i : Fin n) (hi : (kind i).isRight = true) : (1 : ℝ) ≤ K := by
    cases hk : kind i with
    | inl d => simp [hk] at hi
    | inr k => exact variablesBoundedAt_one_le_of_categorical M.toEuclideanSCM K hbound i k hk
  obtain ⟨a0, B0, ha0, hB0, A0, hA0, hstructural⟩ :=
    restricted_candidates_from_structural_budgets M K (LhatF M.toEuclideanSCM L) hbound.1 hdim.1 hcatK
      f hf hcont hcat
  obtain ⟨a1, a2, ha1, ha2, A1, hA1, B1, hB1, tb, htb, htb1, hlatent⟩ :=
    canonical_clipped_generators_architecture_budgets M K Lchart counts sets dC
      hbound hdim.2 hsupp hcharts hdom hboundary hgate
  refine ⟨(a0, a1, a2), ⟨ha0, ha1, ha2, le_rfl, le_rfl, le_rfl⟩,
    hdim.1, hdim.2, A0 * LhatF M.toEuclideanSCM L + A1 + 1, by positivity,
    max B0 B1, tb, htb, ?_⟩
  intro c0 c1 c2 hc W0 L1 L2 hW hL1 hL2 tau htau htaub
  obtain ⟨g, hg, hgbox, hgerr⟩ := hlatent c1 c2 hc.2.2.2.2.1 hc.2.2.2.2.2
    L1 L2 ((le_max_right B0 B1).trans hL1) ((le_max_right B0 B1).trans hL2)
    tau htau (htaub.trans_le (min_le_right _ _))
  obtain ⟨R, hR, hRlaw, hRerr⟩ := hstructural c0 W0 hc.2.2.2.1
    ((le_max_left B0 B1).trans hW) counts dC (maxLatentDim M.toEuclideanSCM)
    c1 c2 L1 L2 tau g hg
  refine ⟨R, hR, ?_⟩
  have hs : (∑ i, supDistOn (M.domain i (some (-(K : ℝ), K)))
      (M.f i) (R.canonical.f i)) ≤
      ∑ i, supDistOn (inputCube K i) (f i) (R.canonical.f i) := by
    apply Finset.sum_le_sum
    intro i _
    apply iSup_le
    intro x
    have hx : x.val ∈ inputCube K i := by
      intro j
      exact abs_le.mpr (x.property.2 j)
    rw [← hagree i x.val x.property]
    exact le_iSup_of_le ⟨x.val, hx⟩ le_rfl
  have hgerr' : (∑ j, wasserstein1 (M.blockLaw j : Measure (L1Vec (dims j)))
      (R.canonical.blockLaw j : Measure (L1Vec (dims j)))) ≤
      ENNReal.ofReal (A1 * ((L1 : ℝ)^(-(2 : ℝ)/maxLatentDim M.toEuclideanSCM) +
        (L2 : ℝ)^(-(2 : ℝ)/maxLatentDim M.toEuclideanSCM) +
        tau * (1 - Real.log tau))) := by
    simpa only [hRlaw] using hgerr
  have hx : 0 ≤ (W0 : ℝ)^(-(1 : ℝ)/maxInDim M.toEuclideanSCM) := by positivity
  have hy : 0 ≤ (L1 : ℝ)^(-(2 : ℝ)/maxLatentDim M.toEuclideanSCM) +
      (L2 : ℝ)^(-(2 : ℝ)/maxLatentDim M.toEuclideanSCM) +
      tau * (1 - Real.log tau) := by
    have ht1 : tau ≤ 1 := (htaub.trans_le (min_le_left _ _)).le
    have hl : Real.log tau ≤ 0 := Real.log_nonpos htau.le ht1
    exact add_nonneg (add_nonneg (by positivity) (by positivity))
      (mul_nonneg htau.le (by linarith))
  refine (add_le_add (hs.trans hRerr) hgerr').trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (mul_nonneg hA1.le hy)]
  apply ENNReal.ofReal_le_ofReal
  have hcross0 := mul_nonneg (mul_nonneg hA0.le (LhatF M.toEuclideanSCM L).coe_nonneg) hy
  have hcross1 := mul_nonneg hA1.le hx
  nlinarith

-- @node: L_le_LhatF_of_positive_output
/-- For [a nonnegative Lipschitz constant L](hyp:L), if [the model's maximum
input dimension is positive](hyp:hin) and [node i has positive output
dimension](hyp:hout), then [L is at most its dimension-adjusted structural
Lipschitz bound](goal). -/
lemma L_le_LhatF_of_positive_output
    (M : EuclideanSCM kind dims) (L : ℝ≥0)
    (hin : 0 < maxInDim M) (i : Fin n) (hout : 0 < outputDim (kind i)) :
    L ≤ LhatF M L := by
  have hm : outputDim (kind i) ≤ maxOutDim M :=
    Finset.le_sup (f := fun j => outputDim (kind j)) (Finset.mem_univ i)
  have hi : (1 : ℝ) ≤ maxInDim M := by exact_mod_cast hin
  have ho : (1 : ℝ) ≤ maxOutDim M := by exact_mod_cast (hout.trans_le hm)
  have hprod : (1 : ℝ) ≤ maxInDim M * maxOutDim M := by nlinarith
  have hs := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ maxInDim M * maxOutDim M)
  have hn := Real.sqrt_nonneg ((maxInDim M : ℝ) * maxOutDim M)
  have hroot : 1 ≤ Real.sqrt ((maxInDim M : ℝ) * maxOutDim M) := by nlinarith
  change (L : ℝ) ≤ Real.sqrt ((maxInDim M : ℝ) * maxOutDim M) * L
  nlinarith [L.coe_nonneg]

-- @node: architecture_thresholds_of_continuous_nodes
/-- For [nonnegative mechanism regularity and output bounds L and K](hyp:L,K),
[latent component sets](hyp:sets), [their chart dimensions](hyp:dC), and
[a nonnegative chart regularity bound](hyp:Lchart), if [the model and components
satisfy the architecture construction premises](hyp:hmodel), [the Yarotsky
coordinate approximation result holds](hyp:hgate), and [every node is
continuous](hyp:hcontinuous), then [there exist three positive architecture
thresholds that are admissible factors for themselves and certify the structural
and latent network constructions for these data](goal). -/
lemma architecture_thresholds_of_continuous_nodes
    (M : CanonicalSCM kind dims dag G C) (L K : ℝ≥0) (counts : Fin b → ℕ)
    (sets : ∀ j, Fin (counts j) → Set (L1Vec (dims j)))
    (dC : ∀ j, Fin (counts j) → ℕ) (Lchart : ℝ≥0)
    (hmodel : ArchitectureConstructionPremises M L K counts sets dC Lchart)
    (hgate : YarotskyCoordinateApprox)
    (hcontinuous : ∀ i, (kind i).isLeft = true) :
    ∃ a : ℕ × ℕ × ℕ,
      ArchitectureFactorSelection a.1 a.2.1 a.2.2 a.1 a.2.1 a.2.2 ∧
      ArchitectureConstructionThresholds M K (LhatF M.toEuclideanSCM L)
        counts dC a.1 a.2.1 a.2.2 := by
  have hdomain (i : Fin n) : M.domain i none = Set.univ :=
    canonical_domain_eq_univ_of_continuous_parents M i (fun p _ => hcontinuous p)
  have hLip (i : Fin n) : LipschitzWith (LhatF M.toEuclideanSCM L) (M.f i) := by
    by_cases ho : 0 < outputDim (kind i)
    · have h := hmodel.2.2.2.2.2.2.2.2.2.1 i
      rw [hdomain] at h
      exact (lipschitzOnWith_univ.mp h).weaken
        (L_le_LhatF_of_positive_output M.toEuclideanSCM L hmodel.2.2.2.2.2.1.1 i ho)
    · apply LipschitzWith.of_dist_le_mul
      intro x y
      have heq : M.f i x = M.f i y := by
        apply PiLp.ext
        intro j
        exact (ho (Nat.zero_lt_of_lt j.isLt)).elim
      rw [heq, dist_self]
      positivity
  apply architecture_thresholds_of_cube_extension M L K counts sets dC Lchart hmodel hgate
    M.f (fun i => (hLip i).lipschitzOnWith) ?_ ?_ (fun _ _ _ => rfl)
  · intro i hi x hx
    have he : ∃ d, kind i = Sum.inl d := by
      cases hk : kind i with
      | inl d => exact ⟨d, rfl⟩
      | inr k => simp [hk] at hi
    obtain ⟨d, hd⟩ := he
    exact hmodel.2.2.2.2.2.2.2.2.2.2.1 i d hd x (by rw [hdomain]; trivial)
  · intro i hi
    have he : (kind i).isRight = false := by
      have h := hcontinuous i
      cases hk : kind i <;> simp_all
    simp [he] at hi

-- @node: architecture_thresholds_of_scalar_binary_nodes
/-- For [nonnegative mechanism regularity and output bounds L and K](hyp:L,K),
[latent component sets](hyp:sets), [their chart dimensions](hyp:dC), and
[a nonnegative chart regularity bound](hyp:Lchart), if [the model and components
satisfy the architecture construction premises](hyp:hmodel), [the Yarotsky
coordinate approximation result holds](hyp:hgate), and [every node is either
scalar continuous or binary categorical](hyp:hkind), then [there exist three
positive architecture thresholds that are admissible factors for themselves
and certify the structural and latent network constructions for these data](goal). -/
lemma architecture_thresholds_of_scalar_binary_nodes
    (M : CanonicalSCM kind dims dag G C) (L K : ℝ≥0) (counts : Fin b → ℕ)
    (sets : ∀ j, Fin (counts j) → Set (L1Vec (dims j)))
    (dC : ∀ j, Fin (counts j) → ℕ) (Lchart : ℝ≥0)
    (hmodel : ArchitectureConstructionPremises M L K counts sets dC Lchart)
    (hgate : YarotskyCoordinateApprox)
    (hkind : ∀ i, kind i = Sum.inl 1 ∨ kind i = Sum.inr 2) :
    ∃ a : ℕ × ℕ × ℕ,
      ArchitectureFactorSelection a.1 a.2.1 a.2.2 a.1 a.2.1 a.2.2 ∧
      ArchitectureConstructionThresholds M K (LhatF M.toEuclideanSCM L)
        counts dC a.1 a.2.1 a.2.2 := by
  classical
  have hext (i : Fin n) :
      ∃ g : Input kind dims dag C i → L1Vec (outputDim (kind i)),
        LipschitzWith L g ∧
        ((kind i).isLeft = true → ∀ x, ‖g x‖ ≤ K) ∧
        ((kind i).isRight = true → ∀ x,
          (g x).ofLp ∈ probabilitySimplex (outputDim (kind i))) ∧
        Set.EqOn g (M.f i) (M.domain i none) := by
    have hf := hmodel.2.2.2.2.2.2.2.2.2.1 i
    rcases hkind i with hi | hi
    · obtain ⟨g, hg, hb, heq⟩ := canonical_scalar_structural_extension M i hi L K hf
        (hmodel.2.2.2.2.2.2.2.2.2.2.1 i 1 hi)
      exact ⟨g, hg, fun _ => hb, by simp [hi], heq⟩
    · obtain ⟨g, hg, hs, heq⟩ := canonical_binary_structural_extension M i hi L hf
      exact ⟨g, hg, by simp [hi], fun _ => hs, heq⟩
  choose f hf hb hs heq using hext
  apply architecture_thresholds_of_cube_extension M L K counts sets dC Lchart
    hmodel hgate f ?_ ?_ ?_ ?_
  · intro i
    apply (hf i).lipschitzOnWith.weaken
    apply L_le_LhatF_of_positive_output M.toEuclideanSCM L
      hmodel.2.2.2.2.2.1.1 i
    rcases hkind i with hi | hi <;> simp [hi, outputDim]
  · intro i hi x hx
    exact hb i hi x
  · intro i hi x hx
    exact hs i hi x
  · intro i x hx
    exact heq i ⟨hx.1, Set.mem_univ _⟩

end
end Papers.TbsNeuralCausalPi

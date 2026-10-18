module
public import Papers.TbsNeuralCausalPi.Helpers.FixedLabelPrefixCausality
/-! # One finite propensity alphabet for all categorical nodes

The alphabet precedes the candidate model. Deterministic simplex rounding
preserves prefix causality while its entropy counts only genuine categorical
nodes, all complete label strata, and the common non-Gumbel grid.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
open scoped NNReal ENNReal
noncomputable section

variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
  {C : Fin b → Set (Fin n)}

-- @node: CategoricalNodeIndex
/-- For [n nodes](hyp:n) with [a specification of each node's continuous or categorical type](hyp:kind), the [categorical node index set](goal) consists of nodes paired with their categorical label count and evidence that they have that type. -/
abbrev CategoricalNodeIndex (kind : Fin n → NodeKind) :=
  Σ i : Fin n, {k : ℕ // kind i = Sum.inr k}

-- @node: categoricalNodeIndex_projection_injective
/-- [Distinct categorical node indices identify distinct nodes](goal), since a node's type uniquely determines its categorical label count. -/
lemma categoricalNodeIndex_projection_injective :
    Function.Injective (fun a : CategoricalNodeIndex kind => a.1) := by
  rintro ⟨i, k, hi⟩ ⟨j, l, hj⟩ hij
  dsimp only at hij
  subst j
  have hkl : k = l := Sum.inr.inj (hi.symm.trans hj)
  subst l
  rfl

-- @node: categoricalNodeIndexFinite
/-- For [n nodes](hyp:n) with [the given assignment of node types](hyp:kind), [the categorical node index set is finite](goal). -/
instance categoricalNodeIndexFinite : Finite (CategoricalNodeIndex kind) :=
  Finite.of_injective _ categoricalNodeIndex_projection_injective

-- @node: categoricalNodeIndexFintype
/-- For [n nodes](hyp:n) with [the given assignment of node types](hyp:kind), [the categorical node index set is equipped with a finite enumeration](goal). -/
instance categoricalNodeIndexFintype : Fintype (CategoricalNodeIndex kind) :=
  Fintype.ofFinite _

-- @node: causalPropensityTableGrid
/-- For [n nodes](hyp:n) with [the assignment of node types](hyp:kind), [a reference probability vector at each categorical node](hyp:p0), [a rounding denominator R](hyp:R), and [a shared grid size s](hyp:s), the [finite propensity table alphabet](goal) contains all combinations of simplex grid tables across categorical nodes and complete label strata, with s probability vectors per table. -/
def causalPropensityTableGrid
    (p0 : ∀ i k, kind i = Sum.inr k → probabilitySimplex k) (R s : ℕ) :
    Finset (∀ i k, kind i = Sum.inr k →
      CategoricalStratum kind → Fin s → probabilitySimplex k) := by
  classical
  exact (Fintype.piFinset (fun a : CategoricalNodeIndex kind =>
    Fintype.piFinset (fun _ : CategoricalStratum kind =>
      simplexTableGrid (p0 a.1 a.2.val a.2.property) R s))).image
        (fun t i k hi => t ⟨i, ⟨k, hi⟩⟩)

-- @node: causalPropensityTableGrid_round_mem
/-- Given [a reference probability vector at every categorical node](hyp:p0) and [a table of probability vectors indexed by categorical nodes, complete label strata, and s grid positions](hyp:p), [rounding every entry at denominator R produces a member of the finite propensity table alphabet with the same grid size s](goal). -/
lemma causalPropensityTableGrid_round_mem
    (p0 : ∀ i k, kind i = Sum.inr k → probabilitySimplex k) (R s : ℕ)
    (p : ∀ i k, kind i = Sum.inr k →
      CategoricalStratum kind → Fin s → probabilitySimplex k) :
    (fun i k hi c j => simplexRound (p0 i k hi) R (p i k hi c j)) ∈
      causalPropensityTableGrid p0 R s := by
  classical
  unfold causalPropensityTableGrid
  apply Finset.mem_image.mpr
  refine ⟨(fun a c j => simplexRound (p0 a.1 a.2.val a.2.property) R
    (p a.1 a.2.val a.2.property c j)), ?_, rfl⟩
  apply Fintype.mem_piFinset.mpr
  intro a
  apply Fintype.mem_piFinset.mpr
  intro c
  exact simplexTableGrid_round_mem _ R s _

-- @node: causalPropensityTableGrid_nonempty
/-- Given [a reference probability vector at every categorical node](hyp:p0), [the propensity table alphabet is nonempty for every rounding denominator and grid size](goal). -/
lemma causalPropensityTableGrid_nonempty
    (p0 : ∀ i k, kind i = Sum.inr k → probabilitySimplex k) (R s : ℕ) :
    (causalPropensityTableGrid p0 R s).Nonempty :=
  ⟨_, causalPropensityTableGrid_round_mem p0 R s (fun i k hi _ _ => p0 i k hi)⟩

/-- Given [a reference probability vector at every categorical node](hyp:p0), [the logarithm of the propensity table alphabet's size is at most the sum, over categorical nodes and complete label strata, of the node's label count times the shared grid size s, multiplied by the logarithm of R plus one](goal). -/
-- @node: causalPropensityTableGrid_log_card_le
lemma causalPropensityTableGrid_log_card_le
    (p0 : ∀ i k, kind i = Sum.inr k → probabilitySimplex k) (R s : ℕ) :
    Real.log ((causalPropensityTableGrid p0 R s).card : ℝ) ≤
      (∑ a : CategoricalNodeIndex kind,
        (∑ _c : CategoricalStratum kind, ((a.2.val * s : ℕ) : ℝ))) *
          Real.log (R + 1 : ℕ) := by
  classical
  let A := fun a : CategoricalNodeIndex kind =>
    Fintype.piFinset (fun _ : CategoricalStratum kind =>
      simplexTableGrid (p0 a.1 a.2.val a.2.property) R s)
  have hne (a : CategoricalNodeIndex kind) : (A a).Nonempty := by
    refine ⟨fun _ j => simplexRound (p0 a.1 a.2.val a.2.property) R
      (p0 a.1 a.2.val a.2.property), Fintype.mem_piFinset.mpr ?_⟩
    intro c
    exact simplexTableGrid_round_mem _ R s _
  have hinner (a : CategoricalNodeIndex kind) :
      Real.log ((A a).card : ℝ) ≤
        (∑ _c : CategoricalStratum kind, ((a.2.val * s : ℕ) : ℝ)) *
          Real.log (R + 1 : ℕ) := by
    dsimp [A]
    rw [Fintype.card_piFinset, Nat.cast_prod,
      Real.log_prod (fun _ _ => by
        exact_mod_cast (show 0 < (simplexTableGrid
          (p0 a.1 a.2.val a.2.property) R s).card from
          Finset.Nonempty.card_pos ⟨_, simplexTableGrid_round_mem _ R s
            (fun _ => p0 a.1 a.2.val a.2.property)⟩).ne')]
    simpa only [Finset.sum_mul] using
      Finset.sum_le_sum (fun _ (_ : _ ∈ Finset.univ) =>
        simplexTableGrid_log_card_le (p0 a.1 a.2.val a.2.property) R s)
  have hcard : (causalPropensityTableGrid p0 R s).card ≤
      (Fintype.piFinset A).card := by
    unfold causalPropensityTableGrid
    exact Finset.card_image_le
  have hcardR : ((causalPropensityTableGrid p0 R s).card : ℝ) ≤
      ((Fintype.piFinset A).card : ℝ) := by exact_mod_cast hcard
  apply (Real.log_le_log
    (by exact_mod_cast (causalPropensityTableGrid_nonempty p0 R s).card_pos)
    hcardR).trans
  rw [Fintype.card_piFinset, Nat.cast_prod,
    Real.log_prod (fun a _ => by exact_mod_cast (hne a).card_pos.ne')]
  simpa only [Finset.sum_mul] using Finset.sum_le_sum (fun a _ => hinner a)

/-- Given [a reference probability vector at every categorical node](hyp:p0), [the logarithm of the propensity table alphabet's size is at most the sum of label counts over all categorical nodes and complete label strata, times the shared grid size s, times the logarithm of R plus one](goal). -/
-- @node: causalPropensityTableGrid_log_card_le_entries
lemma causalPropensityTableGrid_log_card_le_entries
    (p0 : ∀ i k, kind i = Sum.inr k → probabilitySimplex k) (R s : ℕ) :
    Real.log ((causalPropensityTableGrid p0 R s).card : ℝ) ≤
      (∑ a : CategoricalNodeIndex kind,
        ∑ _c : CategoricalStratum kind, (a.2.val : ℝ)) * s *
          Real.log (R + 1 : ℕ) := by
  simpa only [Nat.cast_mul, Finset.sum_mul] using
    causalPropensityTableGrid_log_card_le p0 R s

/-- Given [reference probability vectors for all categorical nodes](hyp:p0) and [a nonnegative regularity bound L](hyp:L), assume [the continuous mechanisms are L-Lipschitz](hyp:hcont), [the categorical propensities satisfy the L-Lipschitz bound](hyp:hprop), [the rounding denominator R is positive](hyp:hR), and [coding every latent point selects a grid point within distance rho](hyp:hgrid). Then [the finite alphabet contains a table approximating every fixed-label propensity coordinate within rho times its propagated Lipschitz bound plus the reciprocal of R, and giving identical tables whenever label assignments agree at all earlier nodes](goal). -/
-- @node: exists_causalPropensityTableGrid_approximation
lemma exists_causalPropensityTableGrid_approximation
    (p0 : ∀ i k, kind i = Sum.inr k → probabilitySimplex k)
    (M : CanonicalSCM kind dims dag G C) (L : ℝ≥0)
    (hcont : ContinuousMechanismsLipschitz M.toEuclideanSCM L)
    (hprop : CategoricalPropensityLipschitz M.toEuclideanSCM M.f L)
    {s R : ℕ} (hR : 0 < R) {K rho : ℝ}
    (grid : Fin s → boundedCube (∑ j, dims j) K)
    (code : boundedCube (∑ j, dims j) K → Fin s)
    (hgrid : ∀ x, dist x.val (grid (code x)).val ≤ rho) :
    ∃ table ∈ causalPropensityTableGrid p0 R s,
      (∀ i k hi c x j,
        |(fixedLabelCategoricalPropensity M c i k hi
            ((jointLatentVectorEquiv dims).symm x.val)).val j -
          (table i k hi c (code x)).val j| ≤
        (L * ((structuralInputSize M.toEuclideanSCM i : ℝ≥0) *
          (fixedLabelLipschitzBudget M.toEuclideanSCM L (dag.topoOrder i) + 1)) : ℝ≥0) *
            rho + (R : ℝ)⁻¹) ∧
      ∀ i k hi c c',
        (∀ j, dag.topoOrder j < dag.topoOrder i → c j = c' j) →
          table i k hi c = table i k hi c' := by
  let table := fun i k hi c j => simplexRound (p0 i k hi) R
    (fixedLabelCategoricalPropensity M c i k hi
      ((jointLatentVectorEquiv dims).symm (grid j).val))
  refine ⟨table, causalPropensityTableGrid_round_mem p0 R s _, ?_, ?_⟩
  · intro i k hi c x j
    let z := (jointLatentVectorEquiv dims).symm x.val
    let z' := (jointLatentVectorEquiv dims).symm (grid (code x)).val
    have hLip := (fixedLabelCategoricalPropensity_coordinate_lipschitz
      M L hcont hprop c i k hi j).dist_le_mul z z'
    rw [Real.dist_eq] at hLip
    have hz : dist z z' ≤ rho := by
      simpa only [z, z', LinearIsometryEquiv.dist_map] using hgrid x
    have hround := (simplexRound_coordinate_error (p0 i k hi) hR
      (fixedLabelCategoricalPropensity M c i k hi z') j).le
    rw [abs_sub_comm] at hround
    exact (abs_sub_le _ ((fixedLabelCategoricalPropensity M c i k hi z').val j) _).trans
      (add_le_add (hLip.trans (mul_le_mul_of_nonneg_left hz (by positivity))) hround)
  · intro i k hi c c' hc
    funext j
    exact rounded_fixedLabelCategoricalPropensity_eq_of_prefix M c c' i k hi _
      (p0 i k hi) R hc

/-- Given [reference probability vectors for all categorical nodes](hyp:p0), [a positive rounding tolerance eta](hyp:heta), and [a coded latent grid with approximation distance at most rho](hyp:hgrid), [there is a nonempty finite table alphabet whose logarithmic size is at most the total label count across nodes and complete strata times the grid size times the logarithm of two plus the reciprocal of eta; for every canonical model with continuous mechanisms and categorical propensities bounded in Lipschitz constant by L, it contains a table with coordinate error at most rho times the propagated Lipschitz bound plus eta, depending on labels only through earlier nodes](goal). -/
-- @node: exists_causalPropensityTableGrid_mesh
lemma exists_causalPropensityTableGrid_mesh
    (p0 : ∀ i k, kind i = Sum.inr k → probabilitySimplex k)
    {s : ℕ} {K rho eta : ℝ} (heta : 0 < eta)
    (grid : Fin s → boundedCube (∑ j, dims j) K)
    (code : boundedCube (∑ j, dims j) K → Fin s)
    (hgrid : ∀ x, dist x.val (grid (code x)).val ≤ rho) :
    ∃ T : Finset (∀ i k, kind i = Sum.inr k →
        CategoricalStratum kind → Fin s → probabilitySimplex k),
      T.Nonempty ∧
      Real.log (T.card : ℝ) ≤
        (∑ a : CategoricalNodeIndex kind,
          ∑ _c : CategoricalStratum kind, (a.2.val : ℝ)) * s *
            Real.log (2 + eta⁻¹) ∧
      ∀ (M : CanonicalSCM kind dims dag G C) (L : ℝ≥0),
        ContinuousMechanismsLipschitz M.toEuclideanSCM L →
        CategoricalPropensityLipschitz M.toEuclideanSCM M.f L →
        ∃ table ∈ T,
          (∀ i k hi c x j,
            |(fixedLabelCategoricalPropensity M c i k hi
                ((jointLatentVectorEquiv dims).symm x.val)).val j -
              (table i k hi c (code x)).val j| ≤
            (L * ((structuralInputSize M.toEuclideanSCM i : ℝ≥0) *
              (fixedLabelLipschitzBudget M.toEuclideanSCM L (dag.topoOrder i) + 1)) : ℝ≥0) *
                rho + eta) ∧
          ∀ i k hi c c',
            (∀ j, dag.topoOrder j < dag.topoOrder i → c j = c' j) →
              table i k hi c = table i k hi c' := by
  let R := ⌈eta⁻¹⌉₊
  have hR : 0 < R := Nat.ceil_pos.mpr (inv_pos.mpr heta)
  have hRr : (0 : ℝ) < R := Nat.cast_pos.mpr hR
  have hmesh : (R : ℝ)⁻¹ ≤ eta := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hRr).mpr
    have h := mul_le_mul_of_nonneg_left (Nat.le_ceil eta⁻¹) heta.le
    simpa only [mul_inv_cancel₀ heta.ne'] using h
  have hlog : Real.log (R + 1 : ℕ) ≤ Real.log (2 + eta⁻¹) := by
    apply Real.log_le_log (by positivity)
    have h := (Nat.ceil_lt_add_one (inv_nonneg.mpr heta.le)).le
    dsimp [R]
    push_cast
    linarith
  refine ⟨causalPropensityTableGrid p0 R s,
    causalPropensityTableGrid_nonempty p0 R s,
    (causalPropensityTableGrid_log_card_le_entries p0 R s).trans ?_, ?_⟩
  · exact mul_le_mul_of_nonneg_left hlog (by positivity)
  · intro M L hcont hprop
    obtain ⟨table, ht, herr, hcausal⟩ := exists_causalPropensityTableGrid_approximation
      p0 M L hcont hprop hR grid code hgrid
    exact ⟨table, ht, fun i k hi c x j =>
      (herr i k hi c x j).trans (add_le_add_right hmesh _), hcausal⟩

/-- Given [reference probability vectors for all categorical nodes](hyp:p0), [a nonnegative latent cube radius K](hyp:hK), and [a positive mesh rho](hyp:hrho) [at most one](hyp:hrho1), [there exist a positive finite grid size, a measurable code on the joint latent cube, and a nonempty finite propensity table alphabet: its logarithmic size is bounded by the total label count across nodes and complete strata times $(1+2K(D+1))^D\rho^{-D}\log(2+\rho^{-1})$, and every canonical model with Lipschitz bound L admits a table with coordinate error at most rho times its propagated Lipschitz bound plus rho, depending on labels only through earlier nodes](goal), where D is the total non-Gumbel latent dimension. -/
-- @node: exists_causalPropensityAlphabet_quantizer
lemma exists_causalPropensityAlphabet_quantizer
    (p0 : ∀ i k, kind i = Sum.inr k → probabilitySimplex k)
    {K rho : ℝ} (hK : 0 ≤ K) (hrho : 0 < rho) (hrho1 : rho ≤ 1) :
    ∃ s : ℕ, 0 < s ∧
      ∃ code : boundedCube (∑ j, dims j) K → Fin s, Measurable code ∧
      ∃ T : Finset (∀ i k, kind i = Sum.inr k →
          CategoricalStratum kind → Fin s → probabilitySimplex k),
        T.Nonempty ∧
        Real.log (T.card : ℝ) ≤
          ((∑ a : CategoricalNodeIndex kind,
            ∑ _c : CategoricalStratum kind, (a.2.val : ℝ)) *
            (1 + 2 * K * ((∑ j, dims j) + 1)) ^ (∑ j, dims j)) *
              (rho⁻¹) ^ (∑ j, dims j) * Real.log (2 + rho⁻¹) ∧
        ∀ (M : CanonicalSCM kind dims dag G C) (L : ℝ≥0),
          ContinuousMechanismsLipschitz M.toEuclideanSCM L →
          CategoricalPropensityLipschitz M.toEuclideanSCM M.f L →
          ∃ table ∈ T,
            (∀ i k hi c x j,
              |(fixedLabelCategoricalPropensity M c i k hi
                  ((jointLatentVectorEquiv dims).symm x.val)).val j -
                (table i k hi c (code x)).val j| ≤
              (L * ((structuralInputSize M.toEuclideanSCM i : ℝ≥0) *
                (fixedLabelLipschitzBudget M.toEuclideanSCM L (dag.topoOrder i) + 1)) : ℝ≥0) *
                  rho + rho) ∧
            ∀ i k hi c c',
              (∀ j, dag.topoOrder j < dag.topoOrder i → c j = c' j) →
                table i k hi c = table i k hi c' := by
  obtain ⟨s, hs, hcard, grid, code, hcode, hgrid⟩ :=
    exists_simulation_cube_quantizer (∑ j, dims j) hK hrho
  obtain ⟨T, hT, hentropy, happ⟩ := exists_causalPropensityTableGrid_mesh
    (dag := dag) (G := G) (C := C) p0 hrho grid code hgrid
  refine ⟨s, hs, code, hcode, T, hT, hentropy.trans ?_, happ⟩
  have hsbound : (s : ℝ) ≤
      (1 + 2 * K * ((∑ j, dims j) + 1)) ^ (∑ j, dims j) *
        (rho⁻¹) ^ (∑ j, dims j) := by
    rw [hcard, Nat.cast_pow]
    exact simulation_cube_quantizer_card_le _ hK hrho hrho1
  have hlog : 0 ≤ Real.log (2 + rho⁻¹) := Real.log_nonneg (by have := inv_pos.mpr hrho; linarith)
  calc
    _ ≤ (∑ a : CategoricalNodeIndex kind,
          ∑ _c : CategoricalStratum kind, (a.2.val : ℝ)) *
        ((1 + 2 * K * ((∑ j, dims j) + 1)) ^ (∑ j, dims j) *
          (rho⁻¹) ^ (∑ j, dims j)) * Real.log (2 + rho⁻¹) := by
      gcongr
    _ = _ := by ring

end
end Papers.TbsNeuralCausalPi

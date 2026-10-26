module
public import Papers.OaiUniformInfluenceHypergraph.Helpers.LowDegree
public import Papers.OaiUniformInfluenceHypergraph.Helpers.Restriction

/-! # Averaged block restriction estimate -/

public section

open scoped BigOperators
open Causalean.Experimentation.DesignBased

namespace Papers.OaiUniformInfluenceHypergraph

-- @node: joinedSupport_parts
/-- [Combining a set of edges meeting a vertex block with a set of edges avoiding it,
then separating the result by whether edges meet the block, recovers both original sets](goal). -/
lemma joinedSupport_parts {n r : ℕ} (B : Finset (Fin n))
    (A : Finset (FreeCoord (r := r) B)) (D : Finset (AssignedCoord (r := r) B)) :
    (joinedSupport B A D).subtype (fun e => e ∈ freeEdges B) = A ∧
    (joinedSupport B A D).subtype (fun e => e ∉ freeEdges B) = D := by
  classical
  constructor
  · ext e
    simp only [Finset.mem_subtype, joinedSupport, Finset.mem_union, Finset.mem_image]
    constructor
    · rintro (⟨a, ha, he⟩ | ⟨d, hd, he⟩)
      · exact Subtype.val_injective he ▸ ha
      · exact False.elim (d.property (he.symm ▸ e.property))
    · intro he
      exact Or.inl ⟨e, he, rfl⟩
  · ext e
    simp only [Finset.mem_subtype, joinedSupport, Finset.mem_union, Finset.mem_image]
    constructor
    · rintro (⟨a, ha, he⟩ | ⟨d, hd, he⟩)
      · exact False.elim (e.property (he ▸ a.property))
      · exact Subtype.val_injective he ▸ hd
    · intro he
      exact Or.inr ⟨e, he, rfl⟩

-- @node: joinedSupport_split
/-- [Splitting an edge set into edges meeting a vertex block and edges avoiding it,
then recombining the two parts, recovers the original edge set](goal). -/
lemma joinedSupport_split {n r : ℕ} (B : Finset (Fin n)) (S : Finset (Edge n r)) :
    joinedSupport B (S.subtype (fun e => e ∈ freeEdges B))
      (S.subtype (fun e => e ∉ freeEdges B)) = S := by
  classical
  ext e
  simp only [joinedSupport, Finset.mem_union, Finset.mem_image, Finset.mem_subtype]
  by_cases he : e ∈ freeEdges B
  · constructor
    · rintro (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩) <;> exact ha
    · intro hS
      exact Or.inl ⟨⟨e, he⟩, hS, rfl⟩
  · constructor
    · rintro (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩) <;> exact ha
    · intro hS
      exact Or.inr ⟨⟨e, he⟩, hS, rfl⟩

-- @node: joinedSupport_inter_card
/-- [The number of edges meeting a vertex block in a support assembled from free and
assigned edges equals the number of free edges used to assemble it](goal). -/
lemma joinedSupport_inter_card {n r : ℕ} (B : Finset (Fin n))
    (A : Finset (FreeCoord (r := r) B)) (D : Finset (AssignedCoord (r := r) B)) :
    (joinedSupport B A D ∩ freeEdges B).card = A.card := by
  classical
  have he : joinedSupport B A D ∩ freeEdges B = A.image Subtype.val := by
    ext e
    simp only [joinedSupport, Finset.mem_inter, Finset.mem_union, Finset.mem_image]
    constructor
    · rintro ⟨ha | ⟨d, hd, rfl⟩, he⟩
      · exact ha
      · exact False.elim (d.property he)
    · rintro ⟨a, ha, rfl⟩
      exact ⟨Or.inl ⟨a, ha, rfl⟩, a.property⟩
  rw [he, Finset.card_image_of_injective _ Subtype.val_injective]

-- @node: sum_joinedSupport
/-- [Summing a real-valued function over all edge supports equals summing it over all
pairs of supports meeting and avoiding a fixed vertex block, evaluated at their union](goal). -/
lemma sum_joinedSupport {n r : ℕ} (B : Finset (Fin n)) (g : Finset (Edge n r) → ℝ) :
    (∑ S, g S) = ∑ A : Finset (FreeCoord (r := r) B),
      ∑ D : Finset (AssignedCoord (r := r) B), g (joinedSupport B A D) := by
  classical
  let e : (Finset (FreeCoord (r := r) B) × Finset (AssignedCoord (r := r) B)) ≃
      Finset (Edge n r) :=
    { toFun := fun AD => joinedSupport B AD.1 AD.2
      invFun := fun S => (S.subtype (fun e => e ∈ freeEdges B),
        S.subtype (fun e => e ∉ freeEdges B))
      left_inv := fun AD => Prod.ext (joinedSupport_parts B AD.1 AD.2).1
        (joinedSupport_parts B AD.1 AD.2).2
      right_inv := joinedSupport_split B }
  rw [← e.sum_comp g, Fintype.sum_prod_type]
  rfl

-- @node: fixed_block_lowDegree_mass_le
/-- Suppose [the bias is strictly between zero and one](hyp:hp),
[the block size is at least the edge size plus one and at most the vertex count](hyp:hdom),
[the Boolean hypergraph property is invariant under vertex relabeling](hyp:hf), and
[the chosen vertex block has the prescribed size m](hyp:hB).
Then [the sum of squared Fourier coefficients over supports having between one and
the block cutoff many edges meeting this block is at most m to the power −1/4
times the sum of influences of edges meeting the block](goal). -/
lemma fixed_block_lowDegree_mass_le (r m n : ℕ) (p : ℝ)
    (f : (Edge n r → Bool) → Bool) (hp : BiasInterior p)
    (hdom : BlockDomain r m n) (hf : IsHypergraphProperty f)
    (B : Finset (Fin n)) (hB : B.card = m) :
    (∑ S ∈ Finset.univ.filter (fun S : Finset (Edge n r) =>
      1 ≤ (S ∩ freeEdges B).card ∧ ((S ∩ freeEdges B).card : ℝ) ≤ blockCutoff p m),
        hyperFourierCoeff p f S ^ 2) ≤
      (m : ℝ) ^ (-(1 : ℝ) / 4) * ∑ e ∈ freeEdges B, edgeInfluence p f e := by
  classical
  by_cases hr : r = 0
  · subst r
    have hfree : freeEdges (r := 0) B = ∅ := by
      ext e
      have he : e.val = ∅ := Finset.card_eq_zero.mp e.property
      simp [freeEdges, he]
    simp [hfree]
  have hm : LowDegreeParam (m : ℝ) := by
    change (2 : ℝ) ≤ m
    exact_mod_cast (show 2 ≤ m by have := hdom.1; omega)
  let D := biasedLaw (AssignedCoord (r := r) B) p
  let C := Finset.univ.filter (fun A : Finset (FreeCoord (r := r) B) =>
    1 ≤ A.card ∧ (A.card : ℝ) ≤ blockCutoff p m)
  have hmass : (∑ S ∈ Finset.univ.filter (fun S : Finset (Edge n r) =>
      1 ≤ (S ∩ freeEdges B).card ∧ ((S ∩ freeEdges B).card : ℝ) ≤ blockCutoff p m),
      hyperFourierCoeff p f S ^ 2) =
      D.E (fun y => ∑ A ∈ C, fourierCoeff p (restrictedFunction f B y) A ^ 2) := by
    rw [FiniteDesign.E_sum]
    dsimp only [D]
    simp_rw [averaged_restricted_fourierCoeff_sq p hp f hf B]
    simp only [C, Finset.sum_filter]
    rw [sum_joinedSupport B]
    simp_rw [joinedSupport_inter_card]
    apply Finset.sum_congr rfl
    intro A _
    split_ifs <;> simp
  have hinf : D.E (fun y => totalCoordInfluence p (restrictedFunction f B y)) =
      ∑ e ∈ freeEdges B, edgeInfluence p f e := by
    simp only [totalCoordInfluence]
    rw [FiniteDesign.E_sum]
    dsimp only [D]
    simp_rw [averaged_restricted_influence p hp f hf B]
    exact (Finset.sum_subtype (freeEdges B) (fun _ => Iff.rfl) (edgeInfluence p f)).symm
  rw [hmass]
  calc
    _ ≤ D.E (fun y => (m : ℝ) ^ (-(1 : ℝ) / 4) *
        totalCoordInfluence p (restrictedFunction f B y)) := by
      apply Finset.sum_le_sum
      intro y _
      apply mul_le_mul_of_nonneg_left _ (D.p_nonneg y)
      exact sum_lowDegree_fourierCoeff_sq_le p m (restrictedFunction f B y) hp hm
        (restrictedFunction_smallIndividualInfluences p hp f hf m B hB hdom.1 y)
    _ = _ := by rw [FiniteDesign.E_const_mul, hinf]


-- @node: lem:block
/-- If [the bias is strictly between zero and one](hyp:hp),
[the block size m is at least the edge size r plus one and at most the vertex count n](hyp:hdom),
and [the Boolean hypergraph property is invariant under vertex relabeling](hyp:hf),
then [the sum of squared Fourier coefficients weighted by the probability that a
uniform block captures between one and the block cutoff many support edges is at
most m to the power −1/4 times rm/n times the total edge influence](goal). -/
lemma sum_blockProb_mul_fourierCoeff_sq_le (r m n : ℕ) (p : ℝ)
    (f : (Edge n r → Bool) → Bool) (hp : BiasInterior p)
    (hdom : BlockDomain r m n) (hf : IsHypergraphProperty f) :
    (∑ S : Finset (Edge n r),
      blockCaptureProb n r m hdom.2 (blockCutoff p m) S * hyperFourierCoeff p f S ^ 2) ≤
      (m : ℝ) ^ (-(1 : ℝ) / 4) * ((r : ℝ) * m / n) * totalEdgeInfluence p f := by
  classical
  let D := blockLaw n m hdom.2
  have havg : (∑ S : Finset (Edge n r),
      blockCaptureProb n r m hdom.2 (blockCutoff p m) S * hyperFourierCoeff p f S ^ 2) =
      D.E (fun B => ∑ S ∈ Finset.univ.filter (fun S : Finset (Edge n r) =>
        1 ≤ (S ∩ freeEdges B.val).card ∧
          ((S ∩ freeEdges B.val).card : ℝ) ≤ blockCutoff p m),
        hyperFourierCoeff p f S ^ 2) := by
    simp only [Finset.sum_filter]
    rw [D.E_sum]
    apply Finset.sum_congr rfl
    intro S _
    calc
      _ = D.E (fun B => FiniteDesign.ind (fun B =>
          1 ≤ (S ∩ freeEdges B.val).card ∧
          ((S ∩ freeEdges B.val).card : ℝ) ≤ blockCutoff p m) B *
          hyperFourierCoeff p f S ^ 2) := (D.E_mul_const _ _).symm
      _ = _ := D.E_congr (fun B => by simp [FiniteDesign.ind])
  rw [havg]
  calc
    _ ≤ D.E (fun B => (m : ℝ) ^ (-(1 : ℝ) / 4) *
        ∑ e ∈ freeEdges B.val, edgeInfluence p f e) := by
      apply Finset.sum_le_sum
      intro B _
      exact mul_le_mul_of_nonneg_left
        (fixed_block_lowDegree_mass_le r m n p f hp hdom hf B.val B.property) (D.p_nonneg B)
    _ = (m : ℝ) ^ (-(1 : ℝ) / 4) *
        D.E (fun B => ∑ e ∈ freeEdges B.val, edgeInfluence p f e) := D.E_const_mul _ _
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (averaged_free_totalInfluence_le n r m hdom.2 p hp f hf)
        (Real.rpow_nonneg (Nat.cast_nonneg m) _)


end Papers.OaiUniformInfluenceHypergraph

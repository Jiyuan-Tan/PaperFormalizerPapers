module
public import Papers.OaiSharpThresholdMonotone.Helpers.LowDegree
public import Papers.OaiSharpThresholdMonotone.Helpers.OrbitCounting

/-! # Block averaging of the restricted low-degree estimate -/

public section

open scoped BigOperators
open Causalean.Experimentation.DesignBased

namespace Papers.OaiSharpThresholdMonotone

variable {n m : ℕ}

-- @node: blockLaw_uniform
/-- If [the block size m does not exceed the vertex count n](hyp:hmn),
[sampling an m-vertex block by complete randomization gives the uniform distribution
over all such blocks](goal). -/
lemma blockLaw_uniform (hmn : m ≤ n) : UniformBlockLaw n m (blockLaw n m hmn) := by
  intro B
  rfl

-- @node: edge_meets_block_probability_le
/-- For [a probability distribution over m-vertex blocks](hyp:π), if
[the block size m lies between 3 and n](hyp:hm) and
[this distribution is uniform](hyp:hπ), then
[the probability that a given edge has an endpoint in the sampled block is at most
2m/n](goal). -/
lemma edge_meets_block_probability_le
    (π : FiniteDesign {B : Finset (Fin n) // B.card = m})
    (hm : BlockSize m n) (hπ : UniformBlockLaw n m π) (e : GraphEdge n) :
    π.Pr (fun B => e ∈ freeEdges B.val) ≤ 2 * (m : ℝ) / n := by
  classical
  have hmn : m ≤ n := hm.2
  have hinc (v : Fin n) : π.Pr (fun B => v ∈ B.val) = (m : ℝ) / n := by
    calc
      _ = (blockLaw n m hmn).Pr (fun B => v ∈ B.val) := by
        unfold FiniteDesign.Pr FiniteDesign.E
        apply Finset.sum_congr rfl
        intro B _
        rw [hπ B, blockLaw_uniform hmn B]
      _ = _ := by
        simpa [blockLaw] using completeRandomization_incl m
          ((Fintype.card_fin n).symm ▸ hmn) v
  have hbound (B : {B : Finset (Fin n) // B.card = m}) :
      FiniteDesign.ind (fun B => e ∈ freeEdges B.val) B ≤
        ∑ v ∈ e.val, FiniteDesign.ind (fun B => v ∈ B.val) B := by
    by_cases he : e ∈ freeEdges B.val
    · obtain ⟨v, hv⟩ := (Finset.mem_filter.mp he).2
      obtain ⟨hve, hvB⟩ := Finset.mem_inter.mp hv
      calc
        _ = FiniteDesign.ind (fun B => v ∈ B.val) B := by
          simp [FiniteDesign.ind, he, hvB]
        _ ≤ _ := Finset.single_le_sum
          (fun (w : Fin n) _ => FiniteDesign.ind_nonneg
            (fun (B : {B : Finset (Fin n) // B.card = m}) => w ∈ B.val) B) hve
    · simp only [FiniteDesign.ind, he, if_false]
      exact Finset.sum_nonneg (fun v _ => by positivity)
  calc
    _ ≤ π.E (fun B => ∑ v ∈ e.val, FiniteDesign.ind (fun B => v ∈ B.val) B) :=
      Finset.sum_le_sum (fun B _ => mul_le_mul_of_nonneg_left (hbound B) (π.p_nonneg B))
    _ = ∑ v ∈ e.val, π.Pr (fun B => v ∈ B.val) := π.E_sum _ _
    _ = 2 * (m : ℝ) / n := by simp [hinc, e.property]; ring

-- @node: averaged_free_totalInfluence_le
/-- For [an edge probability strictly between zero and one](hyp:hp) and
[a probability distribution over m-vertex blocks](hyp:π), if
[the block size m lies between 3 and n](hyp:hm) and
[m-vertex blocks are sampled uniformly](hyp:hπ), then
[the expected sum of influences of edges meeting the block is at most 2m/n times
the graph function's total influence](goal). -/
lemma averaged_free_totalInfluence_le (p : ℝ) (hp : BiasInterior p)
    (f : GraphConfig n → Bool) (π : FiniteDesign {B : Finset (Fin n) // B.card = m})
    (hm : BlockSize m n) (hπ : UniformBlockLaw n m π) :
    π.E (fun B => ∑ e ∈ freeEdges B.val, edgeInfluence p f e) ≤
      2 * (m : ℝ) / n * graphTotalInfluence p f := by
  classical
  calc
    _ = π.E (fun B => ∑ e : GraphEdge n,
        FiniteDesign.ind (fun B => e ∈ freeEdges B.val) B * edgeInfluence p f e) := by
      apply π.E_congr
      intro B
      simp [FiniteDesign.ind, freeEdges, Finset.sum_filter]
    _ = ∑ e : GraphEdge n, π.Pr (fun B => e ∈ freeEdges B.val) *
        edgeInfluence p f e := by
      rw [π.E_sum]
      apply Finset.sum_congr rfl
      intro e _
      exact π.E_mul_const _ _
    _ ≤ ∑ e : GraphEdge n, (2 * (m : ℝ) / n) * edgeInfluence p f e := by
      apply Finset.sum_le_sum
      intro e _
      exact mul_le_mul_of_nonneg_right
        (edge_meets_block_probability_le π hm hπ e)
        ((biasedLaw (GraphEdge n) p).Pr_nonneg _)
    _ = _ := by rw [← Finset.mul_sum]; rfl

-- @node: fixed_block_lowDegree_mass_le
/-- For [an edge probability strictly between zero and one](hyp:hp) and
[a graph function invariant under relabeling vertices](hyp:hf), if
[the vertex block contains at least three vertices](hyp:hm), then
[the sum of squared Fourier coefficients whose edge sets meet the block in between
one and the block's low-degree cutoff many edges is at most the block size to the
power −1/4 times the sum of influences of edges meeting the block](goal). -/
lemma fixed_block_lowDegree_mass_le (p : ℝ) (hp : BiasInterior p)
    (f : GraphConfig n → Bool) (hf : GraphSymmetric f) (B : Finset (Fin n))
    (hm : 3 ≤ B.card) :
    ∑ S ∈ Finset.univ.filter (fun S : Finset (GraphEdge n) =>
      1 ≤ (S ∩ freeEdges B).card ∧ ((S ∩ freeEdges B).card : ℝ) ≤ lowCutoff p B.card),
      graphFourierCoeff p f S ^ 2 ≤
      (B.card : ℝ) ^ (-(1 / 4 : ℝ)) * ∑ e ∈ freeEdges B, edgeInfluence p f e := by
  classical
  let ν := biasedLaw {e // e ∉ freeEdges B} p
  have hν : ExteriorBernoulliLaw (freeEdges B) p ν := by
    intro y
    simp only [ν, biasedLaw_eq_bernoulliDesign p ⟨hp.1.le, hp.2.le⟩,
      bernoulliDesign, prodDesign_p, coinDesign]
    apply Finset.prod_congr rfl
    intro e _
    cases y e <;> rfl
  have hm2 : (2 : ℝ) ≤ B.card := by exact_mod_cast (by omega : 2 ≤ B.card)
  have hk : PositiveCutoff (lowCutoff p B.card) := by
    unfold PositiveCutoff lowCutoff
    exact div_pos (mul_pos (biasScale_pos_le_half p hp).1
      (Real.log_pos (by linarith))) (by norm_num)
  have hbool : BooleanGraphFunction f := by
    intro x
    cases h : f x <;> simp [boolValue, h]
  obtain ⟨hmass, hinf⟩ := restriction_mass_and_influence p (lowCutoff p B.card)
    f (freeEdges B) ν hp hbool (Finset.subset_univ _) hν hk
  rw [← hmass, ← hinf, ← ν.E_const_mul]
  unfold FiniteDesign.E
  apply Finset.sum_le_sum
  intro y _
  apply mul_le_mul_of_nonneg_left _ (ν.p_nonneg y)
  exact sum_lowDegree_fourierCoeff_sq_le p B.card (lowCutoff p B.card)
    (restrictFn f (freeEdges B) y) (inferInstance : Finite _) hp hm2
    (restrictedFunction_smallIndividualInfluences p hp f hf B hm y) rfl

-- @node: prop:block
/-- For [an edge probability strictly between zero and one](hyp:hp) and
[a graph function invariant under vertex relabeling](hyp:hf), consider
[a probability distribution over m-vertex blocks](hyp:π). Suppose
[the block size m lies between 3 and n](hyp:hm) and
[m-vertex blocks are sampled uniformly](hyp:hπ). Then
[the sum of squared Fourier coefficients, each weighted by the probability that its
edge set meets the block in between one and the low-degree cutoff many edges, is at
most 2m/n times m to the power −1/4 times the total influence](goal). -/
lemma block_average_lowDegree_mass_le (p : ℝ) (f : GraphConfig n → Bool)
    (π : FiniteDesign {B : Finset (Fin n) // B.card = m})
    (hp : BiasInterior p) (hf : GraphSymmetric f) (hm : BlockSize m n)
    (hπ : UniformBlockLaw n m π) :
    ∑ S : Finset (GraphEdge n),
      π.Pr (fun B => 1 ≤ (S ∩ freeEdges B.val).card ∧
        ((S ∩ freeEdges B.val).card : ℝ) ≤ lowCutoff p m) * graphFourierCoeff p f S ^ 2 ≤
      2 * (m : ℝ) / n * (m : ℝ) ^ (-(1 / 4 : ℝ)) * graphTotalInfluence p f := by
  classical
  have hfixed (B : {B : Finset (Fin n) // B.card = m}) :=
    fixed_block_lowDegree_mass_le p hp f hf B.val (B.property.symm ▸ hm.1)
  calc
    _ = π.E (fun B => ∑ S ∈ Finset.univ.filter
        (fun S : Finset (GraphEdge n) => 1 ≤ (S ∩ freeEdges B.val).card ∧
          ((S ∩ freeEdges B.val).card : ℝ) ≤ lowCutoff p m),
          graphFourierCoeff p f S ^ 2) := by
      simp_rw [FiniteDesign.Pr, ← π.E_mul_const]
      rw [← π.E_sum]
      apply π.E_congr
      intro B
      simp [FiniteDesign.ind, Finset.sum_filter]
    _ ≤ π.E (fun B => (m : ℝ) ^ (-(1 / 4 : ℝ)) *
        ∑ e ∈ freeEdges B.val, edgeInfluence p f e) := by
      unfold FiniteDesign.E
      apply Finset.sum_le_sum
      intro B _
      apply mul_le_mul_of_nonneg_left _ (π.p_nonneg B)
      simpa only [B.property] using hfixed B
    _ = (m : ℝ) ^ (-(1 / 4 : ℝ)) *
        π.E (fun B => ∑ e ∈ freeEdges B.val, edgeInfluence p f e) := π.E_const_mul _ _
    _ ≤ (m : ℝ) ^ (-(1 / 4 : ℝ)) *
        (2 * (m : ℝ) / n * graphTotalInfluence p f) :=
      mul_le_mul_of_nonneg_left (averaged_free_totalInfluence_le p hp f π hm hπ)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = _ := by ring

end Papers.OaiSharpThresholdMonotone

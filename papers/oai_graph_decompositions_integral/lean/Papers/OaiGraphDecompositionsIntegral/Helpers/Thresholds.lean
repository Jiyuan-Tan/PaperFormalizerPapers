module
public import Papers.OaiGraphDecompositionsIntegral.Basic
public import Mathlib.Topology.Order.Compact

/-! # Attainment of the finite graph threshold extrema

These are local proof obligations ensuring that the infimum and supremum encodings
agree with the printed minimum and maximum, without adding consumer premises.
-/

public section

open Causalean.Experimentation.DesignBased
open scoped BigOperators

namespace Papers.OaiGraphDecompositionsIntegral

variable {V : Type} [Fintype V]

omit [Fintype V] in
-- @node: containmentProb_continuous
/-- [The probability that a random n-vertex host contains a copy of J is a
continuous function of the edge inclusion parameter](goal), with that parameter
clamped to the unit interval. -/
@[fun_prop]
lemma containmentProb_continuous (J : SimpleGraph V) (n : ℕ) :
    Continuous (containmentProb J n) := by
  classical
  unfold containmentProb productMeasure Toolkit.Foundations.Probability.bernoulliCube
    bernoulliDesign prodDesign FiniteDesign.Pr FiniteDesign.E coinDesign
  apply continuous_finsetSum
  intro z _
  apply Continuous.mul _ continuous_const
  change Continuous (fun p : ℝ => ∏ e : KEdge n,
    bif z e then max 0 (min p 1) else 1 - max 0 (min p 1))
  apply continuous_finsetProd
  intro e _
  cases z e <;> simp only [cond_false, cond_true] <;> fun_prop

-- @node: containmentThresholdRaw_isLeast
/-- If [J has at most n vertices](hyp:hsize), [its raw containment threshold
is the least edge inclusion probability in the unit interval for which a
random n-vertex host contains a copy of J with probability at least one half](goal). -/
lemma containmentThresholdRaw_isLeast (J : SimpleGraph V) (n : ℕ)
    (hsize : Fintype.card V ≤ n) :
    IsLeast {p : ℝ | p ∈ Set.Icc 0 1 ∧ (1 / 2 : ℝ) ≤ containmentProb J n p}
      (containmentThresholdRaw J n) := by
  classical
  have hcopy : ContainsCopy J (hostGraph (fun _ : KEdge n => true)) := by
    have htop : hostGraph (fun _ : KEdge n => true) = ⊤ := by
      ext v w
      simp [hostGraph, SimpleGraph.fromEdgeSet_adj]
    rw [htop]
    apply SimpleGraph.isContained_top_iff.mpr
    exact Function.Embedding.nonempty_of_card_le (by simpa using hsize)
  have hone : (1 / 2 : ℝ) ≤ containmentProb J n 1 := by
    let z : KEdge n → Bool := fun _ => true
    have hp : (randomHost n 1 ⟨by norm_num, le_rfl⟩).p z = 1 := by
      simp [randomHost, Toolkit.Foundations.Probability.bernoulliCube,
        bernoulliDesign, prodDesign, coinDesign, z]
    have hterm : (randomHost n 1 ⟨by norm_num, le_rfl⟩).p z *
        FiniteDesign.ind (fun z => ContainsCopy J (hostGraph z)) z = 1 := by
      rw [hp]
      simp [FiniteDesign.ind, z, hcopy]
    have hsum := Finset.single_le_sum
      (s := Finset.univ) (f := fun z => (randomHost n 1 ⟨by norm_num, le_rfl⟩).p z *
        FiniteDesign.ind (fun z => ContainsCopy J (hostGraph z)) z)
      (fun z _ => mul_nonneg ((randomHost n 1 ⟨by norm_num, le_rfl⟩).p_nonneg z)
        (FiniteDesign.ind_nonneg _ z)) (Finset.mem_univ z)
    rw [hterm] at hsum
    exact le_trans (by norm_num : (1 / 2 : ℝ) ≤ 1) hsum
  apply IsCompact.isLeast_sInf
  · exact isCompact_Icc.inter_right
      (isClosed_le continuous_const (containmentProb_continuous J n))
  · exact ⟨1, ⟨by norm_num, by norm_num⟩, hone⟩

-- @node: expectationThresholdRaw_isGreatest
/-- If [H has at least one edge](hyp:hedge) and [has at most n vertices](hyp:hsize),
[its raw expectation threshold is the greatest parameter in the unit interval
for which the family of n-vertex host edge sets containing H admits a cover
of cost at most one half](goal). -/
lemma expectationThresholdRaw_isGreatest (H : SimpleGraph V) (n : ℕ)
    (hedge : H.edgeSet.Nonempty) (hsize : Fintype.card V ≤ n) :
    IsGreatest
      {p : ℝ | p ∈ Set.Icc 0 1 ∧ HasCoverOfCostLe (containmentFamily H n) p (1 / 2)}
      (expectationThresholdRaw H n) := by
  classical
  have hclosed : IsClosed {p : ℝ |
      HasCoverOfCostLe (containmentFamily H n) p (1 / 2)} := by
    have heq : {p : ℝ | HasCoverOfCostLe (containmentFamily H n) p (1 / 2)} =
        ⋃ C : {C : Finset (Finset (KEdge n)) // Covers C (containmentFamily H n)},
          {p : ℝ | p ∈ Set.Icc 0 1 ∧ coverPolynomial C.val p ≤ 1 / 2} := by
      ext p
      simp [HasCoverOfCostLe, coverCost, and_left_comm, and_assoc]
    rw [heq]
    apply isClosed_iUnion_of_finite
    intro C
    have hc : Continuous (fun p : ℝ => coverPolynomial C.val p) := by
      unfold coverPolynomial
      fun_prop
    exact isClosed_Icc.inter (isClosed_le hc continuous_const)
  have hzero : HasCoverOfCostLe (containmentFamily H n) 0 (1 / 2) := by
    let C : Finset (Finset (KEdge n)) := Finset.univ.erase ∅
    have hnonempty : ∀ G ∈ containmentFamily H n, G ≠ ∅ := by
      intro G hG hGzero
      subst G
      obtain ⟨f⟩ := hG
      have hbot : graphOfEdges (∅ : Finset (KEdge n)) = ⊥ := by
        ext a b
        simp [graphOfEdges, hostGraph]
      have hH : H = ⊥ := by
        ext v w
        constructor
        · intro hvw
          have h := f.toHom.map_adj hvw
          simp only [hbot, SimpleGraph.bot_adj] at h
        · simp
      exact (SimpleGraph.edgeSet_nonempty.mp hedge) hH
    refine ⟨C, ?_, ⟨by norm_num, by norm_num⟩, ?_⟩
    · intro G hG
      exact ⟨G, by simp [C, hnonempty G hG], Finset.Subset.refl G⟩
    · change coverPolynomial C 0 ≤ 1 / 2
      have hcost : coverPolynomial C 0 = 0 := by
        apply Finset.sum_eq_zero
        intro S hS
        have hSzero : S ≠ ∅ := (Finset.mem_erase.mp hS).1
        exact zero_pow (Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hSzero))
      rw [hcost]
      norm_num
  apply IsCompact.isGreatest_sSup
  · exact isCompact_Icc.inter_right hclosed
  · exact ⟨0, ⟨by norm_num, by norm_num⟩, hzero⟩

end Papers.OaiGraphDecompositionsIntegral

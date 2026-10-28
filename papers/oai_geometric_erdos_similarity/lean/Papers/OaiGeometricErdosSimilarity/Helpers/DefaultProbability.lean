module
public import Papers.OaiGeometricErdosSimilarity.Helpers.TableDefinitions

/-! # Independent selector bits and the no-default routing probability

At each internal vertex the default is chosen exactly when all its nondefault bits are false.
The continuation reads only deeper edges, so product-block independence gives the depth recurrence.
-/

@[expose] public section

namespace Papers.OaiGeometricErdosSimilarity

open Causalean.Experimentation.DesignBased
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {q p : ℝ} {M d g r0 n0 : ℕ}

-- @node: chooseChild_congr
/-- If [the branching number is at least two](hyp:hM) and [two selector assignments agree on every nondefault child edge of a vertex](hyp:h), then [they select the same child at that vertex](goal). -/
lemma chooseChild_congr (hM : BranchingDomain M) (ξ ξ' : NondefaultEdge M d → Bool)
    (U : InternalVertex M d)
    (h : ∀ (i : Fin M) (hi : i.val + 1 < M),
      ξ (nondefaultChildEdge U i hi) = ξ' (nondefaultChildEdge U i hi)) :
    chooseChild hM ξ U = chooseChild hM ξ' U := by
  unfold chooseChild
  congr 2
  funext i
  split
  · exact h i _
  · rfl

-- @node: chooseChild_eq_default_iff
/-- When [the branching number is at least two](hyp:hM), [a vertex selects its default child exactly when all its nondefault child bits are false](goal). -/
lemma chooseChild_eq_default_iff (hM : BranchingDomain M)
    (ξ : NondefaultEdge M d → Bool) (U : InternalVertex M d) :
    chooseChild hM ξ U = defaultChild hM ↔
      ∀ (i : Fin M) (hi : i.val + 1 < M), ξ (nondefaultChildEdge U i hi) = false := by
  classical
  unfold chooseChild
  generalize hf : (List.finRange M).find? _ = f
  cases f with
  | none =>
      simp only [Option.getD_none, true_iff]
      have hh := List.find?_eq_none.mp hf
      intro i hi
      have := hh i (by simp)
      simpa [hi] using this
  | some j =>
      have hj := List.find?_some hf
      have hj' : j.val + 1 < M := by
        by_contra h
        simp [h] at hj
      have hb : ξ (nondefaultChildEdge U j hj') = true := by simpa [hj'] using hj
      have hne : j ≠ defaultChild hM := by
        intro he
        have hv := congrArg Fin.val he
        change j.val = M - 1 at hv
        omega
      simp only [Option.getD_some, hne, false_iff]
      intro hall
      have := hall j hj'
      rw [hb] at this
      contradiction

-- @node: selectorSurvival
/-- Given [a branching number of at least two](hyp:hM) and [a Boolean assignment to nondefault edges](hyp:ξ), the [survival score for a starting vertex and a step budget](goal) is [one when the budget is zero](step:1); [with a positive budget, it is zero if an internal vertex selects the default child, otherwise continues at the selected child with one fewer step, and is one at a leaf](step:2). -/
noncomputable def selectorSurvival (hM : BranchingDomain M)
    (ξ : NondefaultEdge M d → Bool) : ℕ → TreeVertex M d → ℝ
  | 0, _ => 1
  | fuel + 1, v =>
    if hv : v.1.val < d then
      if chooseChild hM ξ ⟨v, hv⟩ = defaultChild hM then 0
      else selectorSurvival hM ξ fuel (child ⟨v, hv⟩ (chooseChild hM ξ ⟨v, hv⟩))
    else 1

-- @node: selectorSurvival_congr_deeper
/-- If [the branching number is at least two](hyp:hM) and [two selector assignments agree on every edge ending deeper than the starting vertex](hyp:h), then [their survival scores from that vertex agree for any given step budget](goal). -/
lemma selectorSurvival_congr_deeper (hM : BranchingDomain M)
    (ξ ξ' : NondefaultEdge M d → Bool) (fuel : ℕ) (v : TreeVertex M d)
    (h : ∀ e : NondefaultEdge M d, v.1.val < e.val.val.1.val → ξ e = ξ' e) :
    selectorSurvival hM ξ fuel v = selectorSurvival hM ξ' fuel v := by
  induction fuel generalizing v with
  | zero => rfl
  | succ fuel ih =>
      by_cases hv : v.1.val < d
      · have hc : chooseChild hM ξ ⟨v, hv⟩ = chooseChild hM ξ' ⟨v, hv⟩ := by
          apply chooseChild_congr
          intro i hi
          apply h
          change v.1.val < v.1.val + 1
          omega
        simp only [selectorSurvival, dif_pos hv, hc]
        split
        · rfl
        · apply ih
          intro e he
          apply h
          change v.1.val + 1 < e.val.val.1.val at he
          omega
      · simp [selectorSurvival, hv]

-- @node: selectorSurvival_eq_indicator
/-- If [the branching number is at least two](hyp:hM) and [the step budget covers the remaining depth from the starting vertex](hyp:hfuel), then [the survival score is one exactly when the walk contains no internal vertex selecting its default child, and zero otherwise](goal). -/
lemma selectorSurvival_eq_indicator (hM : BranchingDomain M)
    (ξ : NondefaultEdge M d → Bool) (fuel : ℕ) (v : TreeVertex M d)
    (hfuel : d - v.1.val ≤ fuel) :
    selectorSurvival hM ξ fuel v =
      if (walkVertices hM ξ fuel v).findSome? (fun w =>
        if hw : w.1.val < d then
          if chooseChild hM ξ ⟨w, hw⟩ = defaultChild hM then some ⟨w, hw⟩ else none
        else none) = (none : Option (InternalVertex M d)) then 1 else 0 := by
  induction fuel generalizing v with
  | zero =>
      have hv : ¬ v.1.val < d := by omega
      simp [selectorSurvival, walkVertices, hv]
  | succ fuel ih =>
      by_cases hv : v.1.val < d
      · have hf : d - (child ⟨v, hv⟩ (chooseChild hM ξ ⟨v, hv⟩)).1.val ≤ fuel := by
          change d - (v.1.val + 1) ≤ fuel
          omega
        by_cases hc : chooseChild hM ξ ⟨v, hv⟩ = defaultChild hM
        · simp [selectorSurvival, walkVertices, hv, hc]
        · simpa [selectorSurvival, walkVertices, hv, hc] using
            ih (child ⟨v, hv⟩ (chooseChild hM ξ ⟨v, hv⟩)) hf
      · simp [selectorSurvival, walkVertices, hv]

-- @node: nondefaultChildEdge_childIndex
/-- If [a child index lies strictly before the default index](hyp:hi), then [the edge to that nondefault child has precisely that child index](goal). -/
lemma nondefaultChildEdge_childIndex (U : InternalVertex M d) (i : Fin M)
    (hi : i.val + 1 < M) : childIndex (nondefaultChildEdge U i hi).val = i := by
  change Fin.lastCases i U.val.2 ⟨U.val.1.val + 1 - 1, _⟩ = i
  have hlast : (⟨U.val.1.val + 1 - 1, lastIndex_lt (childEdge U i)⟩ :
      Fin (U.val.1.val + 1)) = Fin.last U.val.1.val := by
    apply Fin.ext
    simp
  rw [hlast, Fin.lastCases_last]

-- @node: pr_chooseChild_default
/-- When [the branching number is at least two](hyp:hM), [the probability under the random table law that a fixed vertex selects its default child at a fixed real point is one half raised to the number of nondefault children](goal). -/
lemma pr_chooseChild_default (hM : BranchingDomain M) (x : ℝ) (U : InternalVertex M d) :
    (tableLaw q M d g r0 n0 p).Pr
      (fun ω => chooseChild hM (exposedValues ω x) U = defaultChild hM) =
      (1 / 2 : ℝ) ^ (M - 1) := by
  classical
  let idx : Fin (M - 1) → Fin M := fun i =>
    ⟨i.val, lt_of_lt_of_le i.isLt (Nat.sub_le M 1)⟩
  have hidx (i : Fin (M - 1)) : (idx i).val + 1 < M := by
    have := i.isLt
    change i.val + 1 < M
    omega
  let addr : Fin (M - 1) → TableAddr q M d g r0 n0 := fun i =>
    Sum.inl (exposedAddr q M d g r0 n0 x (nondefaultChildEdge U (idx i) (hidx i)))
  have hinj : Function.Injective addr := by
    intro i j hij
    have he := congrArg (fun a : SelAddr q M d g r0 n0 => childIndex a.1.val)
      (Sum.inl.inj hij)
    simp only [exposedAddr, nondefaultChildEdge_childIndex] at he
    exact Fin.ext (congrArg (fun k : Fin M => k.val) he)
  let S := Finset.univ.image addr
  have hevent (ω : Outcome q M d g r0 n0) :
      chooseChild hM (exposedValues ω x) U = defaultChild hM ↔
      ∀ a ∈ S, ω a = false := by
    rw [chooseChild_eq_default_iff]
    constructor
    · intro h a ha
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      exact h (idx i) (hidx i)
    · intro h i hi
      have hlt : i.val < M - 1 := by omega
      have he : idx ⟨i.val, hlt⟩ = i := Fin.ext rfl
      have hb := h (addr ⟨i.val, hlt⟩) (Finset.mem_image.mpr
        ⟨⟨i.val, hlt⟩, Finset.mem_univ _, rfl⟩)
      simpa only [addr, he, exposedValues] using hb
  have hind : FiniteDesign.ind
      (fun ω => chooseChild hM (exposedValues ω x) U = defaultChild hM) =
      (fun ω => ∏ a ∈ S, if ω a then (0 : ℝ) else 1) := by
    funext ω
    by_cases h : ∀ a ∈ S, ω a = false
    · rw [FiniteDesign.ind, if_pos ((hevent ω).mpr h)]
      symm
      apply Finset.prod_eq_one
      intro a ha
      simp [h a ha]
    · rw [FiniteDesign.ind, if_neg (fun he => h ((hevent ω).mp he))]
      push Not at h
      obtain ⟨a, ha, hb⟩ := h
      have hat : ω a = true := by cases hω : ω a <;> simp_all
      exact (Finset.prod_eq_zero ha (by simp [hat])).symm
  unfold FiniteDesign.Pr tableLaw
  rw [hind, bernoulliDesign_E_prod_finset (tableParameter p)
    (tableParameter_nonneg p) (tableParameter_le_one p) S
    (fun _ b => if b then (0 : ℝ) else 1)]
  have hpS (a : TableAddr q M d g r0 n0) (ha : a ∈ S) : tableParameter p a = 1 / 2 := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    rfl
  calc
    _ = ∏ _a ∈ S, (1 / 2 : ℝ) := by
      apply Finset.prod_congr rfl
      intro a ha
      rw [hpS a ha]
      norm_num
    _ = (1 / 2 : ℝ) ^ (M - 1) := by
      rw [Finset.prod_const, Finset.card_image_of_injective _ hinj]
      simp

-- @node: selectorStep_factor
/-- When [the branching number is at least two](hyp:hM), [the expected product of the indicator that a specified child is selected and is nondefault and the subsequent survival score from that child equals the product of their expectations](goal), under the random table law at a fixed real point. -/
lemma selectorStep_factor (hM : BranchingDomain M) (x : ℝ) (U : InternalVertex M d)
    (fuel : ℕ) (i : Fin M) :
    (tableLaw q M d g r0 n0 p).E (fun ω =>
      (if chooseChild hM (exposedValues ω x) U = i ∧ i ≠ defaultChild hM then 1 else 0) *
        selectorSurvival hM (exposedValues ω x) fuel (child U i)) =
    (tableLaw q M d g r0 n0 p).E (fun ω =>
      if chooseChild hM (exposedValues ω x) U = i ∧ i ≠ defaultChild hM then 1 else 0) *
    (tableLaw q M d g r0 n0 p).E (fun ω =>
      selectorSurvival hM (exposedValues ω x) fuel (child U i)) := by
  classical
  let A : Finset (TableAddr q M d g r0 n0) := Finset.univ.filter (fun a =>
    match a with
    | Sum.inl a => a.1.val.val.1.val ≤ U.val.1.val + 1
    | Sum.inr _ => False)
  apply FiniteDesign.E_prod_block_mul _ A
  · intro ω ω' h
    have hc : chooseChild hM (exposedValues ω x) U =
        chooseChild hM (exposedValues ω' x) U := by
      apply chooseChild_congr
      intro j hj
      apply h (Sum.inl (exposedAddr q M d g r0 n0 x (nondefaultChildEdge U j hj)))
      simp [A, exposedAddr, nondefaultChildEdge, childEdge, child]
    rw [hc]
  · intro ω ω' h
    apply selectorSurvival_congr_deeper
    intro e he
    apply h (Sum.inl (exposedAddr q M d g r0 n0 x e))
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, exposedAddr]
    change U.val.1.val + 1 < e.val.val.1.val at he
    omega

-- @node: selectorSurvival_succ_sum
/-- When [the branching number is at least two](hyp:hM), [the survival score at an internal vertex with one extra step equals the sum over children of their remaining survival scores, weighted by the indicator that each child is selected and is nondefault](goal). -/
lemma selectorSurvival_succ_sum (hM : BranchingDomain M)
    (ξ : NondefaultEdge M d → Bool) (fuel : ℕ) (U : InternalVertex M d) :
    selectorSurvival hM ξ (fuel + 1) U.val =
      ∑ i : Fin M, (if chooseChild hM ξ U = i ∧ i ≠ defaultChild hM then 1 else 0) *
        selectorSurvival hM ξ fuel (child U i) := by
  classical
  rw [selectorSurvival, dif_pos U.property,
    Finset.sum_eq_single (chooseChild hM ξ U)]
  · by_cases hc : chooseChild hM ξ U = defaultChild hM <;> simp [hc]
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

-- @node: chooseChild_weight_sum
/-- When [the branching number is at least two](hyp:hM), [the sum over children of the indicators that each is selected and is nondefault equals one minus the indicator of selecting the default child](goal). -/
lemma chooseChild_weight_sum (hM : BranchingDomain M)
    (ξ : NondefaultEdge M d → Bool) (U : InternalVertex M d) :
    (∑ i : Fin M, if chooseChild hM ξ U = i ∧ i ≠ defaultChild hM then (1 : ℝ) else 0) =
      1 - (if chooseChild hM ξ U = defaultChild hM then 1 else 0) := by
  classical
  rw [Finset.sum_eq_single (chooseChild hM ξ U)]
  · by_cases hc : chooseChild hM ξ U = defaultChild hM <;> simp [hc]
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

-- @node: tableLaw_E_selectorSurvival
/-- If [the branching number is at least two](hyp:hM) and [the step budget does not exceed the remaining depth from the starting vertex](hyp:hfuel), then [the expected survival score under the random table law is the budget-th power of one minus one half raised to the number of nondefault children](goal). -/
lemma tableLaw_E_selectorSurvival (hM : BranchingDomain M) (x : ℝ) (fuel : ℕ)
    (v : TreeVertex M d) (hfuel : fuel ≤ d - v.1.val) :
    (tableLaw q M d g r0 n0 p).E
      (fun ω => selectorSurvival hM (exposedValues ω x) fuel v) =
      (1 - (1 / 2 : ℝ) ^ (M - 1)) ^ fuel := by
  classical
  induction fuel generalizing v with
  | zero => simp [selectorSurvival]
  | succ fuel ih =>
      have hv : v.1.val < d := by omega
      let U : InternalVertex M d := ⟨v, hv⟩
      have hstep : (tableLaw q M d g r0 n0 p).E
          (fun ω => selectorSurvival hM (exposedValues ω x) (fuel + 1) v) =
          (tableLaw q M d g r0 n0 p).E (fun ω => ∑ i : Fin M,
            (if chooseChild hM (exposedValues ω x) U = i ∧ i ≠ defaultChild hM then 1 else 0) *
              selectorSurvival hM (exposedValues ω x) fuel (child U i)) := by
        apply FiniteDesign.E_congr
        intro ω
        exact selectorSurvival_succ_sum hM (exposedValues ω x) fuel U
      rw [hstep, FiniteDesign.E_sum]
      simp_rw [selectorStep_factor]
      have hchild (i : Fin M) : (tableLaw q M d g r0 n0 p).E (fun ω =>
          selectorSurvival hM (exposedValues ω x) fuel (child U i)) =
          (1 - (1 / 2 : ℝ) ^ (M - 1)) ^ fuel := by
        apply ih
        change fuel ≤ d - (v.1.val + 1)
        omega
      simp_rw [hchild]
      rw [← Finset.sum_mul]
      have hweights : (∑ i : Fin M, (tableLaw q M d g r0 n0 p).E (fun ω =>
          if chooseChild hM (exposedValues ω x) U = i ∧ i ≠ defaultChild hM then 1 else 0)) =
          1 - (1 / 2 : ℝ) ^ (M - 1) := by
        rw [← FiniteDesign.E_sum]
        have he : (tableLaw q M d g r0 n0 p).E (fun ω => ∑ i : Fin M,
            if chooseChild hM (exposedValues ω x) U = i ∧ i ≠ defaultChild hM then 1 else 0) =
            (tableLaw q M d g r0 n0 p).E (fun ω => 1 -
              if chooseChild hM (exposedValues ω x) U = defaultChild hM then 1 else 0) := by
          apply FiniteDesign.E_congr
          intro ω
          exact chooseChild_weight_sum hM (exposedValues ω x) U
        rw [he, FiniteDesign.E_sub, FiniteDesign.E_const]
        change 1 - (tableLaw q M d g r0 n0 p).Pr
          (fun ω => chooseChild hM (exposedValues ω x) U = defaultChild hM) = _
        rw [pr_chooseChild_default]
      rw [hweights, pow_succ]
      ring

-- @node: fair_default_probability_zpow
/-- If [the branching number M is at least two](hyp:hM), then [one half raised to M minus one equals two raised to the integer power one minus M](goal). -/
lemma fair_default_probability_zpow (hM : BranchingDomain M) :
    (1 / 2 : ℝ) ^ (M - 1) = (2 : ℝ) ^ (1 - (M : ℤ)) := by
  have hM1 : 1 ≤ M := le_trans (by decide : 1 ≤ 2) hM
  have hz : 1 - (M : ℤ) = -((M - 1 : ℕ) : ℤ) := by
    rw [Int.natCast_sub hM1]
    ring
  rw [hz, zpow_neg, zpow_natCast, one_div_pow, one_div]

-- @node: pr_noDefaultEvent
/-- When [the branching number M is at least two](hyp:hM), [the probability under the random table law that routing at a fixed real point never selects a default child equals one minus two to the power one minus M, all raised to the tree depth](goal).

This establishes `NoDefaultProbability` from the fair selector product law. -/
lemma pr_noDefaultEvent (hM : BranchingDomain M) (x : ℝ) :
    (tableLaw q M d g r0 n0 p).Pr (noDefaultEvent q M d g r0 n0 hM x) =
      (1 - (2 : ℝ) ^ (1 - (M : ℤ))) ^ d := by
  have hind : FiniteDesign.ind (noDefaultEvent q M d g r0 n0 hM x) =
      fun ω => selectorSurvival hM (exposedValues ω x) d (root M d) := by
    funext ω
    rw [selectorSurvival_eq_indicator hM (exposedValues ω x) d (root M d)
      (Nat.sub_le _ _)]
    unfold FiniteDesign.ind noDefaultEvent firstDefault
    congr 1
  unfold FiniteDesign.Pr
  rw [hind, tableLaw_E_selectorSurvival hM x d (root M d) (by simp [root]),
    fair_default_probability_zpow hM]

end Papers.OaiGeometricErdosSimilarity

module
public import Papers.OaiGraphDecompositionsIntegral.Helpers.StarsQuantities
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Component budgets supplied by the star-forest support hypothesis

Distinct nontrivial connected components have disjoint supports, each with
at least two positive-degree vertices. This supplies the component count
and occupied-size bounds used in the trial estimates.
-/

public section

open scoped BigOperators

namespace Papers.OaiGraphDecompositionsIntegral

variable {V : Type} [Fintype V] [DecidableEq V]

/-- If [the connected component C has at least two vertices](hyp:hC), then
[every vertex in C has positive degree in J](goal). -/
-- @node: star_component_subset_nonisolated
lemma star_component_subset_nonisolated (J : SimpleGraph V) [DecidableRel J.Adj]
    (C : J.ConnectedComponent) (hC : 2 ≤ C.supp.toFinset.card) :
    C.supp.toFinset ⊆ nonisolated J := by
  classical
  obtain ⟨a, b, ha, hb, hab⟩ := Finset.one_lt_card_iff.mp (by omega : 1 < C.supp.toFinset.card)
  intro v hv
  have hv' : v ∈ C.supp := by simpa using hv
  have hw : ∃ w ∈ C.supp, v ≠ w := by
    by_cases hva : v = a
    · exact ⟨b, by simpa using hb, by simpa [hva] using hab⟩
    · exact ⟨a, by simpa using ha, hva⟩
  obtain ⟨w, hw, hne⟩ := hw
  have hs := SimpleGraph.mem_support_of_reachable hne (C.reachable_of_mem_supp hv' hw)
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (J.degree_pos_iff_mem_support v).mpr hs⟩

/-- If [every connected component in C has at least two vertices](hyp:hC),
then [twice the number of components in C is at most the number of
positive-degree vertices in J](goal). -/
-- @node: star_components_card_le_support
lemma star_components_card_le_support (J : SimpleGraph V) [DecidableRel J.Adj]
    (C : Finset J.ConnectedComponent) (hC : ∀ c ∈ C, 2 ≤ c.supp.toFinset.card) :
    2 * C.card ≤ (nonisolated J).card := by
  classical
  have hdis : (C : Set J.ConnectedComponent).PairwiseDisjoint
      (fun c => c.supp.toFinset) := by
    intro c hc d hd hne
    exact Set.disjoint_toFinset.mpr (J.pairwise_disjoint_supp_connectedComponent hne)
  have hsub : C.biUnion (fun c => c.supp.toFinset) ⊆ nonisolated J := by
    intro v hv
    obtain ⟨c, hc, hvc⟩ := Finset.mem_biUnion.mp hv
    exact star_component_subset_nonisolated J c (hC c hc) hvc
  calc
    2 * C.card = ∑ _c ∈ C, 2 := by simp [Nat.mul_comm]
    _ ≤ ∑ c ∈ C, c.supp.toFinset.card := Finset.sum_le_sum (fun c hc => hC c hc)
    _ = (C.biUnion (fun c => c.supp.toFinset)).card := (Finset.card_biUnion hdis).symm
    _ ≤ _ := Finset.card_le_card hsub

omit [DecidableEq V] in
/-- If [J is a star forest](hyp:hstar) and [every size ell in S is at least
one](hyp:hS), then [twice the sum over S of the numbers of components with
ell leaves is at most the number of positive-degree vertices in J](goal). -/
-- @node: star_multiplicity_sum_le_support
lemma star_multiplicity_sum_le_support (J : SimpleGraph V) [DecidableRel J.Adj]
    (hstar : IsStarForest J) (S : Finset ℕ) (hS : ∀ ell ∈ S, 1 ≤ ell) :
    2 * (∑ ell ∈ S, if h : 1 ≤ ell then starMultiplicity J hstar ell h else 0) ≤
      (nonisolated J).card := by
  classical
  let F := fun ell : ℕ => Finset.univ.filter
    (fun C : J.ConnectedComponent => C.supp.toFinset.card = ell + 1)
  have hdis : (S : Set ℕ).PairwiseDisjoint F := by
    intro a ha b hb hne
    apply Finset.disjoint_left.mpr
    intro C hCa hCb
    have h1 := (Finset.mem_filter.mp hCa).2
    have h2 := (Finset.mem_filter.mp hCb).2
    exact hne (by omega)
  have hcard : (S.biUnion F).card =
      ∑ ell ∈ S, if h : 1 ≤ ell then starMultiplicity J hstar ell h else 0 := by
    rw [Finset.card_biUnion hdis]
    apply Finset.sum_congr rfl
    intro ell hell
    simp only [dif_pos (hS ell hell), starMultiplicity]
    apply congrArg Finset.card
    ext C
    simp only [F, Finset.mem_filter, Finset.mem_univ, true_and,
      ← Set.ncard_eq_toFinset_card']
  rw [← hcard]
  apply star_components_card_le_support
  intro C hC
  obtain ⟨ell, hell, hCell⟩ := Finset.mem_biUnion.mp hC
  have hcardC := (Finset.mem_filter.mp hCell).2
  have hpos := hS ell hell
  omega

omit [DecidableEq V] in
/-- If [J is a star forest](hyp:hstar), [at most n/100 of its vertices have
positive degree](hyp:hsupport), and [every size ell in S is at least one](hyp:hS),
then [the sum over S of the numbers of components with ell leaves is at most n/200](goal). -/
-- @node: star_multiplicity_sum_le
lemma star_multiplicity_sum_le (J : SimpleGraph V) [DecidableRel J.Adj]
    (hstar : IsStarForest J) (n : ℕ) (hsupport : StarsSupport J n)
    (S : Finset ℕ) (hS : ∀ ell ∈ S, 1 ≤ ell) :
    (∑ ell ∈ S, (((if h : 1 ≤ ell then starMultiplicity J hstar ell h else 0) : ℕ) : ℝ)) ≤
      (n : ℝ) / 200 := by
  classical
  have hb := star_multiplicity_sum_le_support J hstar S hS
  have hr : 2 * (∑ ell ∈ S,
      (((if h : 1 ≤ ell then starMultiplicity J hstar ell h else 0) : ℕ) : ℝ)) ≤
      ((nonisolated J).card : ℝ) := by exact_mod_cast hb
  change ((nonisolated J).card : ℝ) ≤ (n : ℝ) / 100 at hsupport
  linarith

omit [DecidableEq V] in
/-- If [J is a star forest](hyp:hstar), [ell is at least one](hyp:hell),
[at most n/100 vertices of J have positive degree](hyp:hsupport), and
[there is at least one component with ell leaves](hyp:hm), then
[ell is at most n/100](goal). -/
-- @node: star_occupied_size_le
lemma star_occupied_size_le (J : SimpleGraph V) [DecidableRel J.Adj]
    (hstar : IsStarForest J) (n ell : ℕ) (hell : 1 ≤ ell)
    (hsupport : StarsSupport J n) (hm : 0 < starMultiplicity J hstar ell hell) :
    (ell : ℝ) ≤ (n : ℝ) / 100 := by
  classical
  obtain ⟨C, hC⟩ := Finset.card_pos.mp hm
  have hcard : C.supp.toFinset.card = ell + 1 := by
    have hc := (Finset.mem_filter.mp hC).2
    simpa only [← Set.ncard_eq_toFinset_card'] using hc
  have hle := Finset.card_le_card (star_component_subset_nonisolated J C (by omega))
  have hellsupport : ell ≤ (nonisolated J).card := by omega
  have hr : (ell : ℝ) ≤ (nonisolated J).card := by exact_mod_cast hellsupport
  exact hr.trans hsupport

end Papers.OaiGraphDecompositionsIntegral

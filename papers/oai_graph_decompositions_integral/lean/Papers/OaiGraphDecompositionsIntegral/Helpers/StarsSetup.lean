module
public import Papers.OaiGraphDecompositionsIntegral.Helpers.StarsEmbedding
public import Papers.OaiGraphDecompositionsIntegral.Helpers.StarsComponents
public import Papers.OaiGraphDecompositionsIntegral.Helpers.StarsCopyCover
public import Mathlib.Data.List.NodupEquivFin

/-! # Enumerating the star demands and reserving the host bins -/

public section

open scoped BigOperators

namespace Papers.OaiGraphDecompositionsIntegral

/-- If [J is a star forest](hyp:hstar), [its components with at least two vertices
can be enumerated by a list of positive leaf counts, with each component having
one more vertex than its leaf count; the list records each star multiplicity,
and both its sum and twice its length are at most the number of nonisolated
vertices](goal). -/
-- @node: star_component_demands
lemma star_component_demands {V : Type} [Fintype V] [DecidableEq V]
    (J : SimpleGraph V) [DecidableRel J.Adj] (hstar : IsStarForest J) :
    ∃ L : List ℕ,
      ∃ e : Fin L.length ≃ {C : J.ConnectedComponent // 2 ≤ C.supp.ncard},
      (∀ i : Fin L.length, (e i).val.supp.ncard = L[i] + 1) ∧
      (∀ ell ∈ L, 1 ≤ ell) ∧
      (∀ ell (hell : 1 ≤ ell), L.count ell = starMultiplicity J hstar ell hell) ∧
      L.sum ≤ (nonisolated J).card ∧
      2 * L.length ≤ (nonisolated J).card := by
  classical
  let C := Finset.univ.filter (fun c : J.ConnectedComponent => 2 ≤ c.supp.ncard)
  let f := fun c : J.ConnectedComponent => c.supp.ncard - 1
  let L := C.toList.map f
  let e₀ := List.Nodup.getEquiv C.toList C.nodup_toList
  let e₁ : {c // c ∈ C.toList} ≃ {c : J.ConnectedComponent // 2 ≤ c.supp.ncard} :=
    Equiv.subtypeEquivRight (fun c => by simp [C])
  let e : Fin L.length ≃ {c : J.ConnectedComponent // 2 ≤ c.supp.ncard} :=
    (finCongr (by simp [L])).trans (e₀.trans e₁)
  have hC (c) (hc : c ∈ C) : 2 ≤ c.supp.ncard := (Finset.mem_filter.mp hc).2
  refine ⟨L, e, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    have hi : (e i).val = C.toList[i.val]'(by simpa [L] using i.isLt) := rfl
    have hp := (e i).property
    change (e i).val.supp.ncard = (C.toList.map f)[i.val] + 1
    rw [List.getElem_map, ← hi]
    dsimp [f]
    omega
  · intro ell hell
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hell
    have hp := hC c (Finset.mem_toList.mp hc)
    dsimp [f]
    omega
  · intro ell hell
    change (C.toList.map f).count ell = _
    rw [List.count_eq_length_filter, List.filter_map, List.length_map]
    rw [← List.toFinset_card_of_nodup (C.nodup_toList.filter _)]
    rw [List.toFinset_filter, Finset.toList_toFinset]
    unfold starMultiplicity
    congr 1
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply,
      beq_iff_eq, C, f, ← Set.ncard_eq_toFinset_card']
    omega
  · have hdis : (C : Set J.ConnectedComponent).PairwiseDisjoint
        (fun c => c.supp.toFinset) := by
      intro c hc d hd hne
      exact Set.disjoint_toFinset.mpr (J.pairwise_disjoint_supp_connectedComponent hne)
    have hsub : C.biUnion (fun c => c.supp.toFinset) ⊆ nonisolated J := by
      intro v hv
      obtain ⟨c, hc, hvc⟩ := Finset.mem_biUnion.mp hv
      exact star_component_subset_nonisolated J c
        (by simpa [Set.ncard_eq_toFinset_card'] using hC c hc) hvc
    calc
      L.sum = ∑ c ∈ C, f c := Finset.sum_map_toList _ _
      _ ≤ ∑ c ∈ C, c.supp.toFinset.card := by
        apply Finset.sum_le_sum
        intro c hc
        dsimp [f]
        rw [← Set.ncard_eq_toFinset_card']
        omega
      _ = (C.biUnion (fun c => c.supp.toFinset)).card := (Finset.card_biUnion hdis).symm
      _ ≤ _ := Finset.card_le_card hsub
  · have hb := star_components_card_le_support J C
      (fun c hc => by simpa [Set.ncard_eq_toFinset_card'] using hC c hc)
    simpa [L] using hb

/-- If [the host order n is at least two](hyp:hn) and [one hundred times the
support budget t is at most n](hyp:ht), [there are a leaf set and a sequence of
centers outside it, with the first floor of n divided by two centers distinct,
and with at least the available leaf count plus t vertices in the leaf set](goal). -/
-- @node: star_host_bins
lemma star_host_bins (n t : ℕ) (hn : 2 ≤ n) (ht : 100 * t ≤ n) :
    ∃ (Y : Finset (Fin n)) (c : ℕ → Fin n),
      (∀ j, c j ∉ Y) ∧
      (∀ k < n / 2, ∀ j < k, c j ≠ c k) ∧
      availableLeaves n + t ≤ Fintype.card ↥Y := by
  classical
  have hh : 0 < n / 2 := by omega
  let C : Finset (Fin n) := Finset.univ.filter (fun v => v.val < n / 2)
  let Y := Cᶜ
  let c : ℕ → Fin n := fun j => ⟨j % (n / 2),
    (Nat.mod_lt j hh).trans_le (Nat.div_le_self n 2)⟩
  have hcardC : C.card = n / 2 := by
    simpa [C, Nat.min_eq_right (Nat.div_le_self n 2)] using
      (Fin.card_filter_val_lt (n := n) (m := n / 2))
  have hcardY : Fintype.card ↥Y = n - n / 2 := by
    simp [Y, Finset.card_compl, hcardC]
  refine ⟨Y, c, ?_, ?_, ?_⟩
  · intro j
    simp only [Y, Finset.mem_compl, not_not, C, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact Nat.mod_lt j hh
  · intro k hk j hj he
    have he' := congrArg Fin.val he
    dsimp [c] at he'
    rw [Nat.mod_eq_of_lt (hj.trans hk), Nat.mod_eq_of_lt hk] at he'
    omega
  · rw [hcardY]
    unfold availableLeaves
    omega

end Papers.OaiGraphDecompositionsIntegral

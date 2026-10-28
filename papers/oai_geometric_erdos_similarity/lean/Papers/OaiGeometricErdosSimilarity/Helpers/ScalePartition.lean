module
public import Papers.OaiGeometricErdosSimilarity.Helpers.Routing

/-! # Finite partitions of a real interval by boundary points -/

public section

namespace Papers.OaiGeometricErdosSimilarity

attribute [local instance] Classical.propDecidable

-- @node: adjacentPairs_card_le
/-- [The number of increasing consecutive pairs in a finite set E of real
numbers is at most the number of elements of E](goal). -/
lemma adjacentPairs_card_le (E : Finset ℝ) :
    ((E.product E).filter (fun ab => ab.1 < ab.2 ∧
      ¬ ∃ c ∈ E, ab.1 < c ∧ c < ab.2)).card ≤ E.card := by
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro ab hab
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hab).1).1
  · intro ab hab cd hcd heq
    have hab' := (Finset.mem_filter.mp hab).2
    have hcd' := (Finset.mem_filter.mp hcd).2
    have hb := (Finset.mem_product.mp (Finset.mem_filter.mp hab).1).2
    have hd := (Finset.mem_product.mp (Finset.mem_filter.mp hcd).1).2
    apply Prod.ext heq
    apply le_antisymm
    · by_contra h
      exact hab'.2 ⟨cd.2, hd, by simpa [heq] using hcd'.1, lt_of_not_ge h⟩
    · by_contra h
      exact hcd'.2 ⟨ab.2, hb, by simpa [← heq] using hab'.1, lt_of_not_ge h⟩

-- @node: endpoint_midpoints_card_le
/-- [Adding the midpoints between consecutive elements of a finite real set E
produces a set with at most twice as many elements as E](goal). -/
lemma endpoint_midpoints_card_le (E : Finset ℝ) :
    (E ∪ ((E.product E).filter (fun ab => ab.1 < ab.2 ∧
      ¬ ∃ c ∈ E, ab.1 < c ∧ c < ab.2)).image (fun ab => (ab.1 + ab.2) / 2)).card ≤
      2 * E.card := by
  exact (Finset.card_union_le _ _).trans
    ((Nat.add_le_add_left ((Finset.card_image_le).trans (adjacentPairs_card_le E)) _).trans
      (by omega))

-- @node: endpoint_midpoints_mem_Icc
/-- If [every element of E lies between one and two, inclusive](hyp:hE), and
[t is an element of E or a midpoint between consecutive elements of E](hyp:ht),
then [t lies between one and two, inclusive](goal). -/
lemma endpoint_midpoints_mem_Icc (E : Finset ℝ)
    (hE : ∀ s ∈ E, s ∈ Set.Icc (1 : ℝ) 2) (t : ℝ)
    (ht : t ∈ E ∪ ((E.product E).filter (fun ab => ab.1 < ab.2 ∧
      ¬ ∃ c ∈ E, ab.1 < c ∧ c < ab.2)).image (fun ab => (ab.1 + ab.2) / 2)) :
    t ∈ Set.Icc (1 : ℝ) 2 := by
  rcases Finset.mem_union.mp ht with ht | ht
  · exact hE t ht
  · obtain ⟨ab, hab, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hab).1
    have ha' := hE _ ha
    have hb' := hE _ hb
    constructor <;> linarith [ha'.1, ha'.2, hb'.1, hb'.2]

-- @node: endpoint_midpoints_cover
/-- If [E contains one](hyp:h1) and [two](hyp:h2), and [t lies between one and
two, inclusive](hyp:ht), then [E together with its consecutive midpoints
contains a representative that either equals t or lies with t strictly
between the same two consecutive elements of E](goal). -/
lemma endpoint_midpoints_cover (E : Finset ℝ) (h1 : 1 ∈ E) (h2 : 2 ∈ E)
    (t : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) 2) :
    ∃ t' ∈ E ∪ ((E.product E).filter (fun ab => ab.1 < ab.2 ∧
      ¬ ∃ c ∈ E, ab.1 < c ∧ c < ab.2)).image (fun ab => (ab.1 + ab.2) / 2),
      t' = t ∨ ∃ a ∈ E, ∃ b ∈ E,
        a < t ∧ t < b ∧ a < t' ∧ t' < b ∧ ¬ ∃ c ∈ E, a < c ∧ c < b := by
  by_cases htE : t ∈ E
  · exact ⟨t, Finset.mem_union_left _ htE, Or.inl rfl⟩
  have ht1 : 1 < t := lt_of_le_of_ne ht.1 (by intro h; exact htE (h ▸ h1))
  have ht2 : t < 2 := lt_of_le_of_ne ht.2 (by intro h; exact htE (h.symm ▸ h2))
  let L := E.filter (· < t)
  let R := E.filter (t < ·)
  have hL : L.Nonempty := ⟨1, Finset.mem_filter.mpr ⟨h1, ht1⟩⟩
  have hR : R.Nonempty := ⟨2, Finset.mem_filter.mpr ⟨h2, ht2⟩⟩
  let a := L.max' hL
  let b := R.min' hR
  have ha := Finset.mem_filter.mp (Finset.max'_mem L hL)
  have hb := Finset.mem_filter.mp (Finset.min'_mem R hR)
  have hgap : ¬ ∃ c ∈ E, a < c ∧ c < b := by
    rintro ⟨c, hc, hac, hcb⟩
    rcases lt_trichotomy c t with hct | hct | hct
    · exact (not_lt_of_ge (Finset.le_max' L c (Finset.mem_filter.mpr ⟨hc, hct⟩))) hac
    · exact htE (hct ▸ hc)
    · exact (not_lt_of_ge (Finset.min'_le R c (Finset.mem_filter.mpr ⟨hc, hct⟩))) hcb
  refine ⟨(a + b) / 2, Finset.mem_union_right _ (Finset.mem_image.mpr
    ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha.1, hb.1⟩,
      lt_trans ha.2 hb.2, hgap⟩, rfl⟩), Or.inr ?_⟩
  exact ⟨a, ha.1, b, hb.1, ha.2, hb.2, by linarith [ha.2, hb.2],
    by linarith [ha.2, hb.2], hgap⟩

end Papers.OaiGeometricErdosSimilarity

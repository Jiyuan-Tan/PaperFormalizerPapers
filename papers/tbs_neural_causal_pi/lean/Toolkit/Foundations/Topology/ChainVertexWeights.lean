module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Data.Real.Basic

/-!
# Vertex coordinates of weighted chains of finite sets

Distributing the weight of each set in a finite family equally among its elements turns
weights on nested sets into ordinary coordinates on elements (`chainVertexWeight`). This
module provides:

* `sum_chainVertexWeight`: the coordinates sum to the total set weight;
* `chainVertexWeight_pos_iff`: with positive weights, the positive coordinates are exactly
  the elements of the union of the family;
* `chainVertexWeight_levelSets`, `chainVertexWeight_unique`: a chain of nonempty sets with
  positive weights is recovered from its coordinates, through their upper level sets;
* `exists_chainVertexWeight`: every probability vector on a finite set arises from a chain
  of nonempty subsets with positive weights summing to one.

These are the coordinate facts behind the geometric barycentric subdivision (Matoušek,
*Using the Borsuk–Ulam Theorem*, Definition 1.7.2 and Exercise 1.7.1); nothing here uses
simplicial complexes.
-/

@[expose] public section

namespace Toolkit.Foundations.Topology

variable {ι : Type*} [DecidableEq ι]

/-- For [a finite family of finite sets](hyp:C) of [elements of a fixed
type](hyp:ι) with [real weights](hyp:w),
the [coordinate of an element](goal) [at the chosen element](hyp:v) adds the
equal shares of the weights of all sets containing that element. -/
noncomputable def chainVertexWeight (C : Finset (Finset ι)) (w : Finset ι → ℝ)
    (v : ι) : ℝ :=
  ∑ s ∈ C, if v ∈ s then w s / (s.card : ℝ) else 0

/-- If [every set in a finite family is nonempty](hyp:hne) and [lies in a
common finite universe](hyp:hsub), [summing the distributed coordinates over
that universe recovers the total set weight](goal). -/
theorem sum_chainVertexWeight {C : Finset (Finset ι)} {U : Finset ι}
    (hne : ∀ s ∈ C, s.Nonempty) (hsub : ∀ s ∈ C, s ⊆ U)
    (w : Finset ι → ℝ) :
    ∑ v ∈ U, chainVertexWeight C w v = ∑ s ∈ C, w s := by
  -- Swap the two finite sums. The inner sum is card(s) copies of
  -- w(s)/card(s); nonemptiness permits cancellation of card(s).
  classical
  unfold chainVertexWeight
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr (hsub t ht)]
  simp only [Finset.sum_const, nsmul_eq_mul]
  exact mul_div_cancel₀ (w t) (Nat.cast_ne_zero.mpr (hne t ht).card_ne_zero)

/-- If [all set weights are strictly positive](hyp:hw), [an element has a
positive distributed coordinate exactly when it belongs to the union of the
family](goal). -/
theorem chainVertexWeight_pos_iff {C : Finset (Finset ι)} {w : Finset ι → ℝ}
    (hw : ∀ s ∈ C, 0 < w s) (v : ι) :
    0 < chainVertexWeight C w v ↔ v ∈ C.biUnion id := by
  -- All summands are nonnegative. A summand is positive exactly when its
  -- set contains v, since membership then guarantees a positive cardinality.
  classical
  have hn : ∀ t ∈ C, 0 ≤ (if v ∈ t then w t / (t.card : ℝ) else 0) := by
    intro t ht
    split_ifs
    · exact div_nonneg (hw t ht).le (Nat.cast_nonneg _)
    · exact le_rfl
  rw [chainVertexWeight, Finset.sum_pos_iff_of_nonneg hn]
  simp only [Finset.mem_biUnion, id_eq]
  constructor
  · rintro ⟨t, ht, hp⟩
    by_cases hv : v ∈ t
    · exact ⟨t, ht, hv⟩
    · simp [hv] at hp
  · rintro ⟨t, ht, hv⟩
    exact ⟨t, ht, by
      simp only [if_pos hv]
      exact div_pos (hw t ht) (Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨v, hv⟩))⟩

/-- For [a family of nonempty sets](hyp:hne) [nested by inclusion](hyp:hchain)
with [strictly positive weights](hyp:hw), [the distinct upper level sets of
the distributed coordinates recover exactly the original family](goal). -/
theorem chainVertexWeight_levelSets {C : Finset (Finset ι)} {w : Finset ι → ℝ}
    (hne : ∀ s ∈ C, s.Nonempty)
    (hchain : ∀ s ∈ C, ∀ t ∈ C, s ⊆ t ∨ t ⊆ s)
    (hw : ∀ s ∈ C, 0 < w s) :
    C = (C.biUnion id).image (fun v => (C.biUnion id).filter
      (fun u => chainVertexWeight C w v ≤ chainVertexWeight C w u)) := by
  -- For each set s choose v in s outside its largest proper predecessor.
  -- Sets containing v are precisely the supersets of s. Their sum is the
  -- coordinate threshold cutting out s: strict positivity separates layers.
  -- Conversely choose the smallest chain member containing a given v.
  classical
  have hp : ∀ t ∈ C, 0 < w t / (t.card : ℝ) := fun t ht =>
    div_pos (hw t ht) (Nat.cast_pos.mpr (hne t ht).card_pos)
  have hmono : ∀ u v : ι, (∀ t ∈ C, v ∈ t → u ∈ t) →
      chainVertexWeight C w v ≤ chainVertexWeight C w u := by
    intro u v huv
    apply Finset.sum_le_sum
    intro t ht
    by_cases hv : v ∈ t
    · simp [hv, huv t ht hv]
    · simp only [if_neg hv]
      split_ifs
      · exact (hp t ht).le
      · exact le_rfl
  have hsep : ∀ t ∈ C, ∀ u ∈ t, ∀ v, v ∉ t →
      chainVertexWeight C w v < chainVertexWeight C w u := by
    intro t ht u hu v hv
    apply Finset.sum_lt_sum
    · intro r hr
      by_cases hvr : v ∈ r
      · have htr : t ⊆ r := (hchain t ht r hr).resolve_right (fun h => hv (h hvr))
        simp [hvr, htr hu]
      · simp only [if_neg hvr]
        split_ifs
        · exact (hp r hr).le
        · exact le_rfl
    · exact ⟨t, ht, by simpa [hu, hv] using hp t ht⟩
  apply Finset.Subset.antisymm
  · intro t ht
    obtain ⟨v, hv, hmin⟩ := t.exists_min_image (chainVertexWeight C w) (hne t ht)
    refine Finset.mem_image.mpr ⟨v, Finset.mem_biUnion.mpr ⟨t, ht, hv⟩, ?_⟩
    ext u
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨huU, hu⟩
      by_contra hut
      exact (not_le_of_gt (hsep t ht v hv u hut)) hu
    · intro hu
      exact ⟨Finset.mem_biUnion.mpr ⟨t, ht, hu⟩, hmin u hu⟩
  · intro t ht
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ht
    have hnon : (C.filter (fun r => v ∈ r)).Nonempty := by
      obtain ⟨r, hr, hvr⟩ := Finset.mem_biUnion.mp hv
      exact ⟨r, Finset.mem_filter.mpr ⟨hr, hvr⟩⟩
    obtain ⟨r, hr, hmin⟩ := (C.filter (fun r => v ∈ r)).exists_min_image
      Finset.card hnon
    obtain ⟨hrC, hvr⟩ := Finset.mem_filter.mp hr
    have heq : (C.biUnion id).filter
        (fun u => chainVertexWeight C w v ≤ chainVertexWeight C w u) = r := by
      ext u
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨_, hu⟩
        by_contra hur
        exact (not_le_of_gt (hsep r hrC v hvr u hur)) hu
      · intro hu
        refine ⟨Finset.mem_biUnion.mpr ⟨r, hrC, hu⟩, hmono u v ?_⟩
        intro q hq hvq
        rcases hchain r hrC q hq with hrq | hqr
        · exact hrq hu
        · have hc := hmin q (Finset.mem_filter.mpr ⟨hq, hvq⟩)
          have he : q = r := Finset.eq_of_subset_of_card_le hqr hc
          simpa [he] using hu
    simpa [heq] using hrC

/-- Two [families of nonempty sets](hyp:hCne,hDne), each [nested by
inclusion](hyp:hCchain,hDchain) and carrying [strictly positive
weights](hyp:hw,hz), [are equal](goal) if [their distributed coordinates agree
at every element](hyp:heq). -/
theorem chainVertexWeight_unique {C D : Finset (Finset ι)}
    (hCne : ∀ s ∈ C, s.Nonempty) (hDne : ∀ s ∈ D, s.Nonempty)
    (hCchain : ∀ s ∈ C, ∀ t ∈ C, s ⊆ t ∨ t ⊆ s)
    (hDchain : ∀ s ∈ D, ∀ t ∈ D, s ⊆ t ∨ t ⊆ s)
    {w z : Finset ι → ℝ} (hw : ∀ s ∈ C, 0 < w s) (hz : ∀ s ∈ D, 0 < z s)
    (heq : chainVertexWeight C w = chainVertexWeight D z) : C = D := by
  classical
  have hU : C.biUnion id = D.biUnion id := by
    ext v
    rw [← chainVertexWeight_pos_iff hw v, ← chainVertexWeight_pos_iff hz v, heq]
  rw [chainVertexWeight_levelSets hCne hCchain hw,
    chainVertexWeight_levelSets hDne hDchain hz, hU, heq]

/-- For [nonnegative weights on a finite set](hyp:ha) [summing to
one](hyp:hsum), [there is a nonempty nested family of nonempty subsets and
strictly positive weights of total one whose distributed coordinates are the
original weights](goal). -/
theorem exists_chainVertexWeight {s : Finset ι} {a : ι → ℝ}
    (ha : ∀ v ∈ s, 0 ≤ a v) (hsum : ∑ v ∈ s, a v = 1) :
    ∃ C : Finset (Finset ι), C.Nonempty ∧
      (∀ t ∈ C, t.Nonempty ∧ t ⊆ s) ∧
      (∀ t ∈ C, ∀ u ∈ C, t ⊆ u ∨ u ⊆ t) ∧
      ∃ w : Finset ι → ℝ, (∀ t ∈ C, 0 < w t) ∧
        (∑ t ∈ C, w t = 1) ∧ ∀ v ∈ s, chainVertexWeight C w v = a v := by
  -- Peel off the smallest coordinate: the whole set carries weight
  -- card(s) * min, and the excess coordinates are decomposed recursively.
  classical
  -- First construct a decomposition without a normalization requirement.
  have decomp : ∀ (S : Finset ι) (b : ι → ℝ), (∀ v ∈ S, 0 ≤ b v) →
      ∃ C : Finset (Finset ι),
        (∀ t ∈ C, t.Nonempty ∧ t ⊆ S) ∧
        (∀ t ∈ C, ∀ u ∈ C, t ⊆ u ∨ u ⊆ t) ∧
        ∃ w : Finset ι → ℝ, (∀ t ∈ C, 0 < w t) ∧
          ∀ v ∈ S, chainVertexWeight C w v = b v := by
    intro S
    induction S using Finset.strongInductionOn with
    | _ S ih =>
      intro b hb
      by_cases hS : S.Nonempty
      · obtain ⟨v, hv, hmin⟩ := S.exists_min_image b hS
        obtain ⟨C, hC, hchain, w, hw, heq⟩ :=
          ih (S.erase v) (Finset.erase_ssubset hv) (fun u => b u - b v)
            (fun u hu => sub_nonneg.mpr (hmin u (Finset.mem_of_mem_erase hu)))
        have hzero : chainVertexWeight C w v = 0 := by
          apply Finset.sum_eq_zero
          intro t ht
          have hvt : v ∉ t := fun h => (Finset.mem_erase.mp ((hC t ht).2 h)).1 rfl
          simp [hvt]
        have hres : ∀ u ∈ S, chainVertexWeight C w u = b u - b v := by
          intro u hu
          by_cases huv : u = v
          · simpa [huv] using hzero
          · exact heq u (Finset.mem_erase.mpr ⟨huv, hu⟩)
        by_cases hz : b v = 0
        · refine ⟨C, ?_, hchain, w, hw, ?_⟩
          · intro t ht
            exact ⟨(hC t ht).1, (hC t ht).2.trans (Finset.erase_subset v S)⟩
          · intro u hu
            simpa [hz] using hres u hu
        · have hp : 0 < b v := lt_of_le_of_ne (hb v hv) (Ne.symm hz)
          have hSC : S ∉ C := by
            intro h
            exact (Finset.mem_erase.mp ((hC S h).2 hv)).1 rfl
          let W : Finset ι → ℝ := fun t => if t = S then (S.card : ℝ) * b v else w t
          have hW : ∀ t ∈ C, W t = w t := by
            intro t ht
            have hne : t ≠ S := fun h => hSC (h ▸ ht)
            simp [W, hne]
          refine ⟨insert S C, ?_, ?_, W, ?_, ?_⟩
          · intro t ht
            rcases Finset.mem_insert.mp ht with rfl | ht
            · exact ⟨hS, Finset.Subset.refl _⟩
            · exact ⟨(hC t ht).1, (hC t ht).2.trans (Finset.erase_subset v S)⟩
          · intro t ht u hu
            rcases Finset.mem_insert.mp ht with ht | ht
            · refine Or.inr ?_
              rw [ht]
              rcases Finset.mem_insert.mp hu with hu | hu
              · rw [hu]
              · exact (hC u hu).2.trans (Finset.erase_subset v S)
            · rcases Finset.mem_insert.mp hu with hu | hu
              · exact Or.inl (hu ▸ (hC t ht).2.trans (Finset.erase_subset v S))
              · exact hchain t ht u hu
          · intro t ht
            rcases Finset.mem_insert.mp ht with rfl | ht
            · simpa [W] using mul_pos (Nat.cast_pos.mpr hS.card_pos) hp
            · rw [hW t ht]
              exact hw t ht
          · intro u hu
            have hcoord : chainVertexWeight C W u = chainVertexWeight C w u := by
              apply Finset.sum_congr rfl
              intro t ht
              rw [hW t ht]
            have hcard : (S.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hS.card_ne_zero
            unfold chainVertexWeight
            rw [Finset.sum_insert hSC]
            change (if u ∈ S then W S / (S.card : ℝ) else 0) +
              chainVertexWeight C W u = b u
            rw [if_pos hu, hcoord, hres u hu]
            simp only [W, if_pos rfl]
            rw [mul_div_cancel_left₀ (b v) hcard]
            ring
      · refine ⟨∅, ?_, ?_, fun _ => 0, ?_, ?_⟩
        · simp
        · simp
        · simp
        · simp [Finset.not_nonempty_iff_eq_empty.mp hS]
  obtain ⟨C, hC, hchain, w, hw, heq⟩ := decomp s a ha
  have htotal : ∑ t ∈ C, w t = 1 := by
    rw [← sum_chainVertexWeight (fun t ht => (hC t ht).1)
      (fun t ht => (hC t ht).2) w]
    exact (Finset.sum_congr rfl heq).trans hsum
  have hnon : C.Nonempty := by
    by_contra h
    have hempty := Finset.not_nonempty_iff_eq_empty.mp h
    simp [hempty] at htotal
  exact ⟨C, hnon, hC, hchain, w, hw, htotal, heq⟩

end Toolkit.Foundations.Topology

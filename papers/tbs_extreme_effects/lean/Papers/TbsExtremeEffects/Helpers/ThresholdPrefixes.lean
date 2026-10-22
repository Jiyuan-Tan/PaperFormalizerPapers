module
public import Papers.TbsExtremeEffects.Helpers.ThresholdSampling
public import Mathlib.Data.Fin.Tuple.Sort

/-! Pathwise reduction of strict-threshold signed sums to decreasing-radius
prefix sums. Clipping at the band's lower endpoint preserves the terminal
square energy, including when radii coincide. -/

public section
namespace Papers.TbsExtremeEffects
open scoped BigOperators

-- @node: antitone_threshold_sum_eq_prefix
/-- If the radii are [ordered from largest to smallest](hyp:hR), then the sum of terms whose radius exceeds a threshold equals the corresponding [initial-prefix sum](goal). -/
lemma antitone_threshold_sum_eq_prefix {n : ℕ} (R a : Fin n → ℝ)
    (hR : Antitone R) (t : ℝ) :
    ∑ i : Fin n, (if t < R i then a i else 0) =
      ∑ i : Fin n, (if i.val < (Finset.univ.filter (fun j => t < R j)).card
        then a i else 0) := by
  classical
  apply Finset.sum_congr rfl
  intro i _
  have hi : i.val < (Finset.univ.filter (fun j => t < R j)).card ↔ t < R i :=
    Tuple.lt_card_gt_iff_apply_gt_of_antitone hR
  simp only [hi]

-- @node: threshold_sum_eq_permuted_prefix
/-- Given a permutation under which radii are [ordered from largest to smallest](hyp:hR), every thresholded sum can be represented by [some prefix with length at most the sample size](goal). -/
lemma threshold_sum_eq_permuted_prefix {n : ℕ} (R a : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) (hR : Antitone (fun i => R (σ i))) (t : ℝ) :
    ∃ k ≤ n, (∑ i : Fin n, if t < R i then a i else 0) =
      ∑ i : Fin n, if i.val < k then a (σ i) else 0 := by
  classical
  refine ⟨(Finset.univ.filter (fun i => t < R (σ i))).card, ?_, ?_⟩
  · exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_fin n)
  · calc
      _ = ∑ i : Fin n, if t < R (σ i) then a (σ i) else 0 :=
        (Equiv.sum_comp σ (fun i => if t < R i then a i else 0)).symm
      _ = _ := antitone_threshold_sum_eq_prefix _ _ hR t

-- @node: threshold_band_signed_prefix_reduction
/-- There is a [permutation](goal) that orders the radii decreasingly, represents every thresholded signed sum above the lower endpoint as a clipped prefix sum, and preserves the clipped square energy. -/
lemma threshold_band_signed_prefix_reduction {n : ℕ} (R a : Fin n → ℝ) (ell : ℝ) :
    ∃ σ : Equiv.Perm (Fin n),
      Antitone (fun i => R (σ i)) ∧
      (∀ t ≥ ell, ∃ k ≤ n,
        (∑ i : Fin n, if t < R i then a i else 0) =
          ∑ i : Fin n, if i.val < k then
            (if ell < R (σ i) then a (σ i) else 0) else 0) ∧
      (∑ i : Fin n, (if ell < R (σ i) then a (σ i) else 0) ^ 2) =
        ∑ i : Fin n, if ell < R i then (a i) ^ 2 else 0 := by
  classical
  let σ := Fin.revPerm.trans (Tuple.sort R)
  have hR : Antitone (fun i => R (σ i)) := by
    intro i j hij
    exact Tuple.monotone_sort R (Fin.rev_le_rev.mpr hij)
  refine ⟨σ, hR, ?_, ?_⟩
  · intro t ht
    obtain ⟨k, hk, hsum⟩ := threshold_sum_eq_permuted_prefix R
      (fun i => if ell < R i then a i else 0) σ hR t
    refine ⟨k, hk, ?_⟩
    rw [← hsum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : t < R i
    · simp [hi, ht.trans_lt hi]
    · simp [hi]
  · calc
      _ = ∑ i : Fin n, if ell < R (σ i) then (a (σ i)) ^ 2 else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        split_ifs <;> simp
      _ = _ := Equiv.sum_comp σ (fun i => if ell < R i then (a i) ^ 2 else 0)

-- @node: threshold_band_bound_of_prefix_bound
/-- If the permuted radii are [decreasing](hyp:hR) and every clipped prefix sum is [bounded by the stated constant](hyp:hPrefix), then every thresholded sum in the band is [bounded by that constant](goal). -/
lemma threshold_band_bound_of_prefix_bound {n : ℕ} (R a : Fin n → ℝ)
    (ell B : ℝ) (σ : Equiv.Perm (Fin n))
    (hR : Antitone (fun i => R (σ i)))
    (hPrefix : ∀ k ≤ n,
      |∑ i : Fin n, if i.val < k then
        (if ell < R (σ i) then a (σ i) else 0) else 0| ≤ B) :
    ∀ t ≥ ell, |∑ i : Fin n, if t < R i then a i else 0| ≤ B := by
  classical
  intro t ht
  obtain ⟨k, hk, hsum⟩ := threshold_sum_eq_permuted_prefix R
    (fun i => if ell < R i then a i else 0) σ hR t
  have hclip : (∑ i : Fin n, if t < R i then a i else 0) =
      ∑ i : Fin n, if t < R i then (if ell < R i then a i else 0) else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : t < R i
    · simp [hi, ht.trans_lt hi]
    · simp [hi]
  rw [hclip, hsum]
  exact hPrefix k hk

-- @node: threshold_band_rademacher_prefix_reduction
/-- When every supplied sign has [square equal to one](hyp:heps), there is a [decreasing-radius permutation and clipped-prefix representation that preserves unsigned square energy](goal). -/
lemma threshold_band_rademacher_prefix_reduction {n : ℕ}
    (R z eps : Fin n → ℝ) (heps : ∀ i, eps i ^ 2 = 1) (ell : ℝ) :
    ∃ σ : Equiv.Perm (Fin n),
      Antitone (fun i => R (σ i)) ∧
      (∀ t ≥ ell, ∃ k ≤ n,
        (∑ i : Fin n, if t < R i then eps i * z i else 0) =
          ∑ i : Fin n, if i.val < k then
            (if ell < R (σ i) then eps (σ i) * z (σ i) else 0) else 0) ∧
      (∑ i : Fin n, (if ell < R (σ i) then eps (σ i) * z (σ i) else 0) ^ 2) =
        ∑ i : Fin n, if ell < R i then (z i) ^ 2 else 0 := by
  obtain ⟨σ, hR, hPrefix, hEnergy⟩ :=
    threshold_band_signed_prefix_reduction R (fun i => eps i * z i) ell
  refine ⟨σ, hR, hPrefix, hEnergy.trans ?_⟩
  apply Finset.sum_congr rfl
  intro i _
  split_ifs
  · rw [mul_pow, heps i, one_mul]
  · rfl

end Papers.TbsExtremeEffects

module
public import Papers.OaiGeometricErdosSimilarity.Basic
public import Mathlib.MeasureTheory.Measure.Real

/-! # Density bounds for the intervals preceding grid boundaries -/

public section

namespace Papers.OaiGeometricErdosSimilarity

open MeasureTheory
open scoped BigOperators

-- @node: periodicDensity_mono
/-- If [a set A of real numbers is contained in a set B](hyp:hAB), then
[the periodic density of A is no greater than that of B](goal). -/
lemma periodicDensity_mono {A B : Set ℝ} (hAB : A ⊆ B) :
    periodicDensity A ≤ periodicDensity B := by
  exact measureReal_mono (Set.inter_subset_inter_left _ hAB)
    (measure_ne_top_of_subset Set.inter_subset_right (by simp [lebesgueMeasure]))

-- @node: periodicDensity_iUnion_le
/-- For [a finite indexed family A of sets of real numbers](hyp:A),
[the periodic density of their union is at most the sum of their periodic densities](goal). -/
lemma periodicDensity_iUnion_le {ι : Type*} [Fintype ι] (A : ι → Set ℝ) :
    periodicDensity (⋃ i, A i) ≤ ∑ i, periodicDensity (A i) := by
  unfold periodicDensity
  rw [Set.iUnion_inter]
  exact measureReal_iUnion_fintype_le _

-- @node: boundary_intervals_density_le
/-- For [a natural-number resolution N](hyp:N) with [N strictly positive](hyp:hN)
and [a real interval width δ](hyp:δ) with [δ nonnegative](hyp:hδ),
[the periodic density of the union, over all integers k, of the intervals from
k divided by N minus δ, included, to k divided by N, excluded, is at most N times δ](goal).

There are only N relevant right endpoints inside one period when Nδ < 1.
For larger δ, the unit-interval measure bound suffices. -/
lemma boundary_intervals_density_le (N : ℕ) (hN : 0 < N) (δ : ℝ) (hδ : 0 ≤ δ) :
    periodicDensity {x : ℝ | ∃ k : ℤ, x ∈ Set.Ico ((k : ℝ) / N - δ) ((k : ℝ) / N)} ≤
      N * δ := by
  by_cases hlarge : 1 ≤ (N : ℝ) * δ
  · exact (periodicDensity_mem_Icc _).2.trans hlarge
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  let A : ℕ → Set ℝ := fun k => Set.Ico ((k : ℝ) / N - δ) ((k : ℝ) / N)
  have hcover : {x : ℝ | ∃ k : ℤ,
      x ∈ Set.Ico ((k : ℝ) / N - δ) ((k : ℝ) / N)} ∩ Set.Ico 0 1 ⊆
      ⋃ k ∈ Finset.Icc 1 N, A k := by
    rintro x ⟨⟨k, hk⟩, hx⟩
    have hkpos : (0 : ℝ) < k := by
      have := (lt_div_iff₀ hNr).mp hk.2
      nlinarith [hx.1]
    have hkupper : (k : ℝ) < (N : ℝ) + 1 := by
      have h := (div_le_iff₀ hNr).mp (show (k : ℝ) / N ≤ x + δ by linarith [hk.1])
      nlinarith [hx.2]
    have hk1 : 1 ≤ k := by
      have : (0 : ℤ) < k := by exact_mod_cast hkpos
      omega
    have hkN : k ≤ (N : ℤ) := by
      have : k < (N : ℤ) + 1 := by exact_mod_cast hkupper
      omega
    apply Set.mem_iUnion.mpr
    refine ⟨k.toNat, Set.mem_iUnion.mpr ⟨Finset.mem_Icc.mpr ?_, ?_⟩⟩
    · omega
    · have hcast : (k.toNat : ℝ) = (k : ℝ) := by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega : 0 ≤ k)]
      simpa only [A, hcast] using hk
  have hfinite : volume (⋃ k ∈ Finset.Icc 1 N, A k) ≠ ⊤ := by
    apply ne_of_lt
    apply measure_biUnion_lt_top (Finset.finite_toSet _)
    intro k hk
    exact measure_Ico_lt_top
  have hbound := (measureReal_mono hcover hfinite).trans
    (measureReal_biUnion_finset_le (μ := volume) (Finset.Icc 1 N) A)
  have hmeasure (k : ℕ) : volume.real (A k) = δ := by
    dsimp [A]
    rw [Real.volume_real_Ico_of_le (by linarith)]
    ring
  simp only [hmeasure] at hbound
  simpa [periodicDensity, lebesgueMeasure, measureReal_def, Nat.card_Icc,
    Nat.sub_add_cancel hN] using hbound

end Papers.OaiGeometricErdosSimilarity

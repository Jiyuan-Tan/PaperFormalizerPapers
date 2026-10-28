module

public import Papers.OaiBoundDyadicTriangular.Helpers.AtomReindex
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Cubic integrals of the dyadic step functions -/

public section

open MeasureTheory
open scoped BigOperators

namespace Papers.OaiBoundDyadicTriangular

-- @node: dyadicInterval_left_mem
/-- For any integer scale and natural-number interval index, [the left endpoint
belongs to the corresponding dyadic interval](goal). -/
lemma dyadicInterval_left_mem (m : ℤ) (a : ℕ) :
    (2 : ℝ) ^ m * a ∈ dyadicInterval m a := by
  constructor
  · exact le_rfl
  · apply mul_lt_mul_of_pos_left _ (by positivity)
    exact_mod_cast Nat.lt_succ_self a

-- @node: dyadicInterval_pairwiseDisjoint
/-- At any integer scale, [dyadic intervals with distinct natural-number indices
are disjoint](goal). -/
lemma dyadicInterval_pairwiseDisjoint (m : ℤ) :
    Pairwise (fun a b => Disjoint (dyadicInterval m a) (dyadicInterval m b)) := by
  intro a b hab
  apply Set.disjoint_left.mpr
  intro x ha hb
  have hp : 0 < (2 : ℝ) ^ m := by positivity
  rcases lt_or_gt_of_ne hab with h | h
  · have hn : (a : ℝ) + 1 ≤ b := by exact_mod_cast h
    exact (not_lt_of_ge (hb.1.trans' (mul_le_mul_of_nonneg_left hn hp.le))) ha.2
  · have hn : (b : ℝ) + 1 ≤ a := by exact_mod_cast h
    exact (not_lt_of_ge (ha.1.trans' (mul_le_mul_of_nonneg_left hn hp.le))) hb.2

-- @node: iUnion_dyadicInterval
/-- At any integer scale, [the union of all dyadic intervals with natural-number
indices is the nonnegative real half-line](goal). -/
lemma iUnion_dyadicInterval (m : ℤ) : (⋃ a : ℕ, dyadicInterval m a) = Rplus := by
  ext x
  simp only [Set.mem_iUnion, Rplus, Set.mem_Ici]
  constructor
  · rintro ⟨a, ha⟩
    exact (by positivity : 0 ≤ (2 : ℝ) ^ m * a).trans ha.1
  · intro hx
    refine ⟨⌊x / (2 : ℝ) ^ m⌋₊, ?_⟩
    have hp : 0 < (2 : ℝ) ^ m := by positivity
    constructor
    · have h := Nat.floor_le (div_nonneg hx hp.le)
      simpa [mul_comm] using (le_div_iff₀ hp).mp h
    · have h := Nat.lt_floor_add_one (x / (2 : ℝ) ^ m)
      simpa [mul_comm] using (div_lt_iff₀ hp).mp h

-- @node: dyadicRect_pairwiseDisjoint
/-- At any integer scale, [dyadic rectangles indexed by distinct pairs of natural
numbers are disjoint](goal). -/
lemma dyadicRect_pairwiseDisjoint (m : ℤ) :
    Pairwise (fun p q : ℕ × ℕ => Disjoint
      (dyadicInterval m p.1 ×ˢ dyadicInterval m p.2)
      (dyadicInterval m q.1 ×ˢ dyadicInterval m q.2)) := by
  intro p q hpq
  apply Set.disjoint_left.mpr
  rintro x ⟨hx, hy⟩ ⟨hx', hy'⟩
  by_cases h : p.1 = q.1
  · exact Set.disjoint_left.mp (dyadicInterval_pairwiseDisjoint m
      (show p.2 ≠ q.2 from fun he => hpq (Prod.ext h he))) hy hy'
  · exact Set.disjoint_left.mp (dyadicInterval_pairwiseDisjoint m h) hx hx'

-- @node: iUnion_dyadicRect
/-- At any integer scale, [the union of all dyadic rectangles indexed by pairs of
natural numbers is the nonnegative quadrant](goal). -/
lemma iUnion_dyadicRect (m : ℤ) :
    (⋃ p : ℕ × ℕ, dyadicInterval m p.1 ×ˢ dyadicInterval m p.2) = Rplus ×ˢ Rplus := by
  rw [Set.iUnion_prod, iUnion_dyadicInterval]

-- @node: volume_dyadicRect
/-- For any integer scale m and pair of natural-number indices, [the Lebesgue area
of the corresponding dyadic rectangle is two raised to twice m](goal). -/
lemma volume_dyadicRect (m : ℤ) (p : ℕ × ℕ) :
    volume (dyadicInterval m p.1 ×ˢ dyadicInterval m p.2) =
      ENNReal.ofReal ((2 : ℝ) ^ (2 * m)) := by
  rw [MeasureTheory.Measure.volume_eq_prod, Measure.prod_prod]
  simp only [dyadicInterval, Real.volume_Ico]
  have he (a : ℕ) : (2 : ℝ) ^ m * (a + 1) - (2 : ℝ) ^ m * a = (2 : ℝ) ^ m := by ring
  simp only [he, ← ENNReal.ofReal_mul (by positivity : 0 ≤ (2 : ℝ) ^ m)]
  rw [← zpow_add₀ (by norm_num), two_mul]

-- @node: lintegral_cube_dyadicRect
/-- If [each input function is constant on every dyadic rectangle at scale m](hyp:hAtoms),
then, for any vertex and rectangle index pair, [the integral of the absolute cube
of that vertex's function over the rectangle equals two raised to twice m times
the absolute cube of its value at the rectangle's lower-left corner](goal). -/
lemma lintegral_cube_dyadicRect (F : Fin 3 → ℝ × ℝ → ℝ) (m : ℤ)
    (hAtoms : StepAtoms F m) (v : Fin 3) (p : ℕ × ℕ) :
    (∫⁻ x in dyadicInterval m p.1 ×ˢ dyadicInterval m p.2, ‖F v x‖ₑ ^ (3 : ℕ)) =
      ENNReal.ofReal ((2 : ℝ) ^ (2 * m) *
        |F v ((2 : ℝ) ^ m * p.1, (2 : ℝ) ^ m * p.2)| ^ 3) := by
  have hc : ∀ᵐ x ∂volume.restrict (dyadicInterval m p.1 ×ˢ dyadicInterval m p.2),
      F v x = F v ((2 : ℝ) ^ m * p.1, (2 : ℝ) ^ m * p.2) := by
    filter_upwards [ae_restrict_mem (measurableSet_Ico.prod measurableSet_Ico)] with x hx
    exact hAtoms v p.1 p.2 _ _ hx
      ⟨dyadicInterval_left_mem m p.1, dyadicInterval_left_mem m p.2⟩
  rw [lintegral_congr_ae (hc.mono (fun _ hx => congrArg (fun y : ℝ => ‖y‖ₑ ^ (3 : ℕ)) hx)),
    lintegral_const, Measure.restrict_apply_univ, volume_dyadicRect,
    Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ |F v ((2 : ℝ) ^ m * p.1, (2 : ℝ) ^ m * p.2)| ^ 3)]
  congr 1
  ring

-- @node: lintegral_cube_eq_gridCubeMass
/-- If [each input function vanishes outside a bounded square in the nonnegative
quadrant](hyp:hCompact) and [is constant on every dyadic rectangle at scale m](hyp:hAtoms),
then, for any vertex, [the integral of its absolute cube over the quadrant equals
its grid cube mass at scale m, viewed as a nonnegative extended real number](goal). -/
lemma lintegral_cube_eq_gridCubeMass (F : Fin 3 → ℝ × ℝ → ℝ) (m : ℤ)
    (hCompact : StepCompact F) (hAtoms : StepAtoms F m) (v : Fin 3) :
    (∫⁻ x, ‖F v x‖ₑ ^ (3 : ℕ) ∂quadrantMeasure) =
      ENNReal.ofReal (gridCubeMass F m v) := by
  change (∫⁻ x in Rplus ×ˢ Rplus, ‖F v x‖ₑ ^ (3 : ℕ)) = _
  rw [← iUnion_dyadicRect m, lintegral_iUnion
    (s := fun p : ℕ × ℕ => dyadicInterval m p.1 ×ˢ dyadicInterval m p.2)
    (fun _ => measurableSet_Ico.prod measurableSet_Ico)
    (dyadicRect_pairwiseDisjoint m)]
  simp_rw [lintegral_cube_dyadicRect F m hAtoms v]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun p => by positivity)
    ((summable_of_hasFiniteSupport (step_grid_cubes_hasFiniteSupport F m hCompact v)).mul_left _),
    tsum_mul_left]
  rfl

-- @node: gridCubeMass_eq_eLpNorm_cube
/-- If [each input function vanishes outside a bounded square in the nonnegative
quadrant](hyp:hCompact) and [is constant on every dyadic rectangle at scale m](hyp:hAtoms),
then, for any vertex, [its grid cube mass at scale m equals the cube of its L³ norm
on the quadrant after converting that norm to a real number](goal). -/
lemma gridCubeMass_eq_eLpNorm_cube (F : Fin 3 → ℝ × ℝ → ℝ) (m : ℤ)
    (hCompact : StepCompact F) (hAtoms : StepAtoms F m) (v : Fin 3) :
    gridCubeMass F m v = (eLpNorm (F v) 3 quadrantMeasure).toReal ^ 3 := by
  have h := eLpNorm_nnreal_pow_eq_lintegral
    (f := F v) (μ := quadrantMeasure) (p := (3 : NNReal)) (by norm_num)
  norm_num only [NNReal.coe_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_ofNat] at h
  rw [lintegral_cube_eq_gridCubeMass F m hCompact hAtoms v] at h
  have hg : 0 ≤ gridCubeMass F m v := by
    unfold gridCubeMass
    positivity
  have ht := congrArg ENNReal.toReal h
  simpa only [ENNReal.toReal_pow, ENNReal.toReal_ofReal hg] using ht.symm

end Papers.OaiBoundDyadicTriangular

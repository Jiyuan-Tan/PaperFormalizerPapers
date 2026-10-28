module
public import Papers.OaiGraphDecompositionsIntegral.Helpers.FiniteHoeffding
public import Papers.OaiGraphDecompositionsIntegral.Helpers.BernoulliTests
public import Causalean.Stat.FiniteDesign.ProductMeasure
public import Causalean.Stat.FiniteDesign.FiniteDesignMeasure
public import Mathlib.Probability.Moments.SubGaussian

/-! # Hoeffding concentration for a fixed source test

The smoothing extension and the source neighborhood are independent Bernoulli-r
subsets. Their union is Bernoulli-tau, so the mean is x(Q). This is a paper-owned
proof obligation, not an additional gate.
-/

public section

open Causalean.Experimentation.DesignBased MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Papers.OaiGraphDecompositionsIntegral

attribute [local instance] Classical.propDecidable

-- @node: sourceTest_failure_bound
/-- If [Y has fewer than n vertices](hyp:hY) and [the edge probability r is
nonnegative](hyp:hr0) and [at most one](hyp:hr1), then [the probability that
the average smoothed test value over neighborhoods outside Y exceeds twice
its mean xQ is at most exp(−2(n − |Y|)xQ²)](goal). -/
lemma sourceTest_failure_bound {n : ℕ} (Y : Finset (Fin n)) (hY : Y.card < n)
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (Q : Finset (Finset ↥Y)) :
    (randomHost n r ⟨hr0, hr1⟩).Pr (fun z => ¬ SourceTest Y r Q (hostGraph z)) ≤
      Real.exp (-2 * ((n : ℝ) - Y.card) * xQ r Q ^ 2) := by
  let : MeasurableSpace Bool := ⊤
  let I := ↥(Finset.univ \ Y)
  let X : I → (KEdge n → Bool) → ℝ := fun w z =>
    smoothedTest ↥Y r Q (neighborhoodIn Y (hostGraph z) w.val)
  have hcard : (Fintype.card I : ℝ) = (n : ℝ) - Y.card := by
    dsimp [I]
    rw [Fintype.card_coe, Finset.card_sdiff_of_subset (Finset.subset_univ Y)]
    simp only [Finset.card_univ, Fintype.card_fin]
    exact Nat.cast_sub hY.le
  have hk : 0 < (Fintype.card I : ℝ) := by
    rw [hcard]
    exact sub_pos.mpr (by exact_mod_cast hY)
  have hx : 0 ≤ xQ r Q := FiniteDesign.Pr_nonneg _ _
  have hb (w : I) (z : KEdge n → Bool) : X w z ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨FiniteDesign.Pr_nonneg _ _, FiniteDesign.Pr_le_one _ _⟩
  have hm (w : I) : (randomHost n r ⟨hr0, hr1⟩).E (X w) = xQ r Q :=
    neighborhood_smoothedTest_mean Y w.val (Finset.mem_sdiff.mp w.property).2 r hr0 hr1 Q
  have htail := finiteDesign_hoeffding_upper (randomHost n r ⟨hr0, hr1⟩) X
    (neighborhood_statistics_independent Y r ⟨hr0, hr1⟩ (smoothedTest ↥Y r Q))
    (xQ r Q) ((Fintype.card I : ℝ) * xQ r Q) hb hm (mul_nonneg hk.le hx)
  have hprob : (randomHost n r ⟨hr0, hr1⟩).Pr (fun z => ¬ SourceTest Y r Q (hostGraph z)) ≤
      (randomHost n r ⟨hr0, hr1⟩).Pr (fun z => (Fintype.card I : ℝ) * xQ r Q +
        (Fintype.card I : ℝ) * xQ r Q ≤ ∑ w, X w z) := by
    apply FiniteDesign.Pr_mono
    intro z hz
    have hsum : (∑ w : I, X w z) =
        ∑ w ∈ Finset.univ \ Y, smoothedTest ↥Y r Q (neighborhoodIn Y (hostGraph z) w) := by
      exact Finset.sum_coe_sort _ (fun w => smoothedTest ↥Y r Q
        (neighborhoodIn Y (hostGraph z) w))
    change ¬ (1 / ((n : ℝ) - Y.card)) * _ ≤ 2 * xQ r Q at hz
    rw [← hsum, ← hcard] at hz
    have hz' := (lt_of_not_ge hz)
    have := (lt_div_iff₀ hk).mp (show 2 * xQ r Q < (∑ w : I, X w z) /
        (Fintype.card I : ℝ) by simpa only [one_div, div_eq_inv_mul, mul_one] using hz')
    nlinarith
  refine hprob.trans (htail.trans_eq ?_)
  congr 1
  field_simp
  rw [← hcard]
  ring

-- @node: targetTest_failure_bound
/-- If [Y has fewer than n vertices](hyp:hY) and [r lies between zero and one](hyp:hr),
then [under edge density 1 − (1 − r)³², the probability that the fraction of
vertices outside Y whose neighborhoods satisfy Q falls below three quarters
of its mean xStarQ is at most exp(−(n − |Y|)xStarQ²/8)](goal). -/
lemma targetTest_failure_bound {n : ℕ} (Y : Finset (Fin n)) (hY : Y.card < n)
    (r : ℝ) (hr : r ∈ Set.Icc 0 1) (Q : Finset (Finset ↥Y)) :
    (randomHost n (targetDensity r) (targetDensity_unitInterval hr)).Pr (fun z =>
      ¬ ((3 / 4 : ℝ) * xStarQ r Q ≤
        (1 / ((n : ℝ) - Y.card)) *
          (((Finset.univ \ Y).filter
            (fun w => Satisfies Q (neighborhoodIn Y (hostGraph z) w))).card : ℝ))) ≤
      Real.exp (-((n : ℝ) - Y.card) * xStarQ r Q ^ 2 / 8) := by
  let : MeasurableSpace Bool := ⊤
  let I := ↥(Finset.univ \ Y)
  let X : I → (KEdge n → Bool) → ℝ := fun w z =>
    if Satisfies Q (neighborhoodIn Y (hostGraph z) w.val) then 1 else 0
  have hcard : (Fintype.card I : ℝ) = (n : ℝ) - Y.card := by
    dsimp [I]
    rw [Fintype.card_coe, Finset.card_sdiff_of_subset (Finset.subset_univ Y)]
    simp only [Finset.card_univ, Fintype.card_fin]
    exact Nat.cast_sub hY.le
  have hk : 0 < (Fintype.card I : ℝ) := by
    rw [hcard]
    exact sub_pos.mpr (by exact_mod_cast hY)
  have hx : 0 ≤ xStarQ r Q := FiniteDesign.Pr_nonneg _ _
  have hb (w : I) (z : KEdge n → Bool) : X w z ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [X]
    split_ifs <;> norm_num
  have hm (w : I) :
      (randomHost n (targetDensity r) (targetDensity_unitInterval hr)).E (X w) = xStarQ r Q :=
    neighborhood_indicator_mean Y w.val (Finset.mem_sdiff.mp w.property).2 r hr Q
  have hind :
      iIndepFun X (randomHost n (targetDensity r) (targetDensity_unitInterval hr)).toMeasure :=
    neighborhood_statistics_independent Y (targetDensity r) (targetDensity_unitInterval hr)
      (fun S => if Satisfies Q S then 1 else 0)
  have htail := finiteDesign_hoeffding_lower
    (randomHost n (targetDensity r) (targetDensity_unitInterval hr)) X hind
    (xStarQ r Q) ((Fintype.card I : ℝ) * xStarQ r Q / 4) hb hm (by positivity)
  have hevent (z : KEdge n → Bool) :
      ¬ ((3 / 4 : ℝ) * xStarQ r Q ≤ (1 / ((n : ℝ) - Y.card)) *
        (((Finset.univ \ Y).filter
          (fun w => Satisfies Q (neighborhoodIn Y (hostGraph z) w))).card : ℝ)) →
      (∑ w, X w z) ≤ (Fintype.card I : ℝ) * xStarQ r Q -
        (Fintype.card I : ℝ) * xStarQ r Q / 4 := by
    have hsum : (∑ w : I, X w z) =
        (((Finset.univ \ Y).filter
          (fun w => Satisfies Q (neighborhoodIn Y (hostGraph z) w))).card : ℝ) := by
      rw [show (∑ w : I, X w z) = ∑ w ∈ Finset.univ \ Y,
        if Satisfies Q (neighborhoodIn Y (hostGraph z) w) then (1 : ℝ) else 0 from
          Finset.sum_coe_sort _ (fun w => if Satisfies Q
            (neighborhoodIn Y (hostGraph z) w) then (1 : ℝ) else 0)]
      simp
    intro hz
    rw [← hsum, ← hcard] at hz
    have hz' := (lt_of_not_ge hz)
    have := (div_lt_iff₀ hk).mp (show (∑ w : I, X w z) / (Fintype.card I : ℝ) <
        (3 / 4 : ℝ) * xStarQ r Q by simpa only [one_div, div_eq_inv_mul, mul_one] using hz')
    linarith
  refine (FiniteDesign.Pr_mono _ _ _ hevent).trans (htail.trans_eq ?_)
  congr 1
  field_simp
  rw [← hcard]
  ring

-- @node: lem:transfer-hoeffding
/-- [There is a positive absolute constant c such that, for every host order n,
density r and size bound s satisfying the transfer parameter conditions, every
vertex set Y with at most n to the two-thirds power vertices and at most half
the host vertices, and every admissible test family Q whose smoothed mean is
at least n to the power −1/100, the source test fails with probability at most
exp(−c n to the power 98/100)](goal).

Hoeffding (1963), *Probability inequalities for sums of bounded random variables*;
handle `cite:hoeffding63`. The finite-design concentration bridge is proved here. -/
lemma transfer_hoeffding :
    ∃ c : ℝ, 0 < c ∧ -- @realizes c(positive absolute concentration constant)
      ∀ (n : ℕ) (r : ℝ) (s : ℕ) (hp : TransferParameters n r s),
      ∀ Y : Finset (Fin n), (Y.card : ℝ) ≤ (n : ℝ) ^ ((2 : ℝ) / 3) →
        2 * Y.card ≤ n →
      ∀ Q : Finset (Finset ↥Y), AdmissibleTest r s Q →
        (n : ℝ) ^ (-(1 : ℝ) / 100) ≤ xQ r Q →
        (randomHost n r ⟨hp.1.le, hp.2.1.le⟩).Pr (fun z => ¬ SourceTest Y r Q (hostGraph z)) ≤
          Real.exp (-c * (n : ℝ) ^ ((98 : ℝ) / 100)) := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro n r s hp Y _ hhalf Q hQ hx
  have hn : 0 < n := by
    obtain ⟨T, hT⟩ := hQ.1.1
    have hTpos := (hQ.1.2 T hT).1
    obtain ⟨y, _⟩ := Finset.card_pos.mp hTpos
    exact lt_of_le_of_lt (Nat.zero_le y.val.val) y.val.isLt
  have hY : Y.card < n := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hk : (n : ℝ) ≤ 2 * ((n : ℝ) - Y.card) := by
    have : 2 * (Y.card : ℝ) ≤ (n : ℝ) := by exact_mod_cast hhalf
    linarith
  have hx0 : 0 ≤ xQ r Q := FiniteDesign.Pr_nonneg _ _
  have hpower : (n : ℝ) ^ ((98 : ℝ) / 100) =
      (n : ℝ) * ((n : ℝ) ^ (-(1 : ℝ) / 100)) ^ 2 := by
    calc
      (n : ℝ) ^ ((98 : ℝ) / 100) =
          (n : ℝ) ^ (1 + (-(1 : ℝ) / 100) * (2 : ℕ)) := by congr 1; norm_num
      _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ ((-(1 : ℝ) / 100) * (2 : ℕ)) :=
        Real.rpow_add hnR _ _
      _ = _ := by rw [Real.rpow_one, Real.rpow_mul_natCast hnR.le]
  have hsq : ((n : ℝ) ^ (-(1 : ℝ) / 100)) ^ 2 ≤ xQ r Q ^ 2 := by
    exact pow_le_pow_left₀ (Real.rpow_nonneg hnR.le _) hx 2
  apply (sourceTest_failure_bound Y hY r hp.1.le hp.2.1.le Q).trans
  apply Real.exp_le_exp.mpr
  rw [hpower]
  have hmul := mul_le_mul hk hsq (sq_nonneg _) (le_trans hnR.le hk)
  nlinarith


end Papers.OaiGraphDecompositionsIntegral

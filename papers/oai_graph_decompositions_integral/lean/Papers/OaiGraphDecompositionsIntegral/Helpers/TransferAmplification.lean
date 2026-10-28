module
public import Papers.OaiGraphDecompositionsIntegral.Helpers.BernoulliTests

/-! # Amplification by sixteen independent Bernoulli unions -/

public section

open Causalean.Experimentation.DesignBased
open scoped BigOperators

namespace Papers.OaiGraphDecompositionsIntegral

attribute [local instance] Classical.propDecidable

-- @node: transfer_expectation_mono
/-- If [f is no larger than g at every outcome](hyp:h), then
[the expectation of f under the finite probability design D is no larger than that of g](goal). -/
lemma transfer_expectation_mono {Ω : Type} [Fintype Ω] (D : FiniteDesign Ω)
    {f g : Ω → ℝ} (h : ∀ z, f z ≤ g z) : D.E f ≤ D.E g := by
  unfold FiniteDesign.E
  exact Finset.sum_le_sum (fun z _ => mul_le_mul_of_nonneg_left (h z) (D.p_nonneg z))

-- @node: satisfaction_union_amplification
/-- If [p is nonnegative](hyp:hp0) and [p is at most one](hyp:hp1), then
[the probability that an independent random subset with inclusion probability 1 − (1 − p)²
contains no member of Q is at most the square of the corresponding failure probability
at inclusion probability p](goal). -/
lemma satisfaction_union_amplification {Y : Type} [Fintype Y] [DecidableEq Y]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (Q : Finset (Finset Y)) :
    1 - (productMeasure Y (unionDensity p)).Pr (fun z => Satisfies Q (toFinset' z)) ≤
      (1 - (productMeasure Y p).Pr (fun z => Satisfies Q (toFinset' z))) ^ 2 := by
  let D := productMeasure Y p
  let a : (Y → Bool) → ℝ := FiniteDesign.ind (fun z => Satisfies Q (toFinset' z))
  have hpoint (z w : Y → Bool) :
      a z + a w - a z * a w ≤
        FiniteDesign.ind (fun v => Satisfies Q (toFinset' v)) (fun y => z y || w y) := by
    have hz : toFinset' z ⊆ toFinset' (fun y => z y || w y) := by
      intro y hy; simp_all [toFinset']
    have hw : toFinset' w ⊆ toFinset' (fun y => z y || w y) := by
      intro y hy; simp_all [toFinset']
    by_cases hsz : Satisfies Q (toFinset' z)
    · obtain ⟨T, hT, hsub⟩ := hsz
      have hu : Satisfies Q (toFinset' (fun y => z y || w y)) := ⟨T, hT, hsub.trans hz⟩
      simp [a, FiniteDesign.ind, show Satisfies Q (toFinset' z) from ⟨T, hT, hsub⟩, hu]
    · by_cases hsw : Satisfies Q (toFinset' w)
      · obtain ⟨T, hT, hsub⟩ := hsw
        have hu : Satisfies Q (toFinset' (fun y => z y || w y)) := ⟨T, hT, hsub.trans hw⟩
        simp [a, FiniteDesign.ind, hsz, show Satisfies Q (toFinset' w) from ⟨T, hT, hsub⟩, hu]
      · simpa [a, FiniteDesign.ind, hsz, hsw] using
          FiniteDesign.ind_nonneg (fun v => Satisfies Q (toFinset' v))
            (fun y => z y || w y)
  have h := transfer_expectation_mono D (fun z => transfer_expectation_mono D (hpoint z))
  simp_rw [FiniteDesign.E_sub, FiniteDesign.E_add, FiniteDesign.E_const,
    FiniteDesign.E_const_mul, FiniteDesign.E_mul_const] at h
  rw [productMeasure_E_union p hp0 hp1] at h
  change D.E a + D.E a - D.E a * D.E a ≤
    (productMeasure Y (unionDensity p)).Pr (fun z => Satisfies Q (toFinset' z)) at h
  change 1 - _ ≤ (1 - D.E a) ^ 2
  nlinarith

-- @node: satisfaction_iterated_amplification
/-- If [p is nonnegative](hyp:hp0) and [p is at most one](hyp:hp1), then
[the probability that an independent random subset at inclusion probability
1 − (1 − p) raised to 2ᵏ contains no member of Q is at most the failure probability
at inclusion probability p raised to 2ᵏ](goal). -/
lemma satisfaction_iterated_amplification {Y : Type} [Fintype Y] [DecidableEq Y]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (Q : Finset (Finset Y)) (k : ℕ) :
    1 - (productMeasure Y (1 - (1 - p) ^ (2 ^ k))).Pr
        (fun z => Satisfies Q (toFinset' z)) ≤
      (1 - (productMeasure Y p).Pr (fun z => Satisfies Q (toFinset' z))) ^ (2 ^ k) := by
  induction k with
  | zero => simpa
  | succ k ih =>
    let q := 1 - (1 - p) ^ (2 ^ k)
    have hq0 : 0 ≤ q := by
      have := pow_le_one₀ (show 0 ≤ 1 - p by linarith) (show 1 - p ≤ 1 by linarith)
        (n := 2 ^ k)
      dsimp [q]; linarith
    have hq1 : q ≤ 1 := by
      have := pow_nonneg (show 0 ≤ 1 - p by linarith) (2 ^ k)
      dsimp [q]; linarith
    have heq : unionDensity q = 1 - (1 - p) ^ (2 ^ (k + 1)) := by
      dsimp [unionDensity, q]
      rw [sub_sub_cancel, ← pow_mul, pow_succ]
    have hstep := satisfaction_union_amplification q hq0 hq1 Q
    rw [heq] at hstep
    have hnonneg : 0 ≤ 1 - (productMeasure Y q).Pr
        (fun z => Satisfies Q (toFinset' z)) := sub_nonneg.mpr (FiniteDesign.Pr_le_one _ _)
    have hsquare := pow_le_pow_left₀ hnonneg ih 2
    rw [← pow_mul, ← pow_succ] at hsquare
    exact hstep.trans hsquare

-- @node: transfer_amplification
/-- If [r is nonnegative](hyp:hr0) and [r is at most one](hyp:hr1), then
[the probability of containing a member of Q at density 1 − (1 − r)³² is at least
one minus the sixteenth power of the failure probability at density 1 − (1 − r)²](goal). -/
lemma transfer_amplification {Y : Type} [Fintype Y] [DecidableEq Y]
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (Q : Finset (Finset Y)) :
    1 - (1 - xQ r Q) ^ 16 ≤ xStarQ r Q := by
  have ht := unionDensity_mem_Icc hr0 hr1
  have h := satisfaction_iterated_amplification (unionDensity r) ht.1 ht.2 Q 4
  have heq : 1 - (1 - unionDensity r) ^ (2 ^ 4) = targetDensity r := by
    norm_num [unionDensity, targetDensity, ← pow_mul]
  rw [heq] at h
  change 1 - xStarQ r Q ≤ (1 - xQ r Q) ^ (2 ^ 4) at h
  norm_num at h
  linarith

-- @node: transfer_amplification_cases
/-- If [r is nonnegative](hyp:hr0) and [r is at most one](hyp:hr1), then
[the probability of containing a member of Q at density 1 − (1 − r)³² is at least
eight times its probability at density 1 − (1 − r)² when the latter is at most 1/16,
and is at least one half when the latter exceeds 1/16](goal). -/
lemma transfer_amplification_cases {Y : Type} [Fintype Y] [DecidableEq Y]
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (Q : Finset (Finset Y)) :
    (xQ r Q ≤ 1 / 16 → 8 * xQ r Q ≤ xStarQ r Q) ∧
      (1 / 16 < xQ r Q → (1 / 2 : ℝ) ≤ xStarQ r Q) := by
  let x := xQ r Q
  let y := xStarQ r Q
  have hx0 : 0 ≤ x := FiniteDesign.Pr_nonneg _ _
  have hx1 : x ≤ 1 := FiniteDesign.Pr_le_one _ _
  have hy0 : 0 ≤ y := FiniteDesign.Pr_nonneg _ _
  have ha := transfer_amplification hr0 hr1 Q
  change 1 - (1 - x) ^ 16 ≤ y at ha
  have hb := one_add_mul_le_pow (show -2 ≤ x by linarith) 16
  norm_num at hb
  have hprod : ((1 - x) * (1 + x)) ^ 16 ≤ 1 :=
    pow_le_one₀ (mul_nonneg (by linarith) (by linarith)) (by nlinarith)
  rw [mul_pow] at hprod
  have hm := mul_le_mul_of_nonneg_left hb (pow_nonneg (show 0 ≤ 1 - x by linarith) 16)
  have hmul := mul_le_mul_of_nonneg_right ha (show 0 ≤ 1 + 16 * x by positivity)
  have hratio : 16 * x ≤ y * (1 + 16 * x) := by nlinarith
  constructor
  · intro hx
    change 8 * x ≤ y
    have hm := mul_nonneg hy0 (show 0 ≤ 1 - 16 * x by linarith)
    nlinarith
  · intro hx
    change 1 / 2 ≤ y
    by_contra hy
    have hm := mul_nonneg (show 0 ≤ 16 * x - 1 by linarith)
      (show 0 ≤ 1 / 2 - y by linarith)
    nlinarith

end Papers.OaiGraphDecompositionsIntegral

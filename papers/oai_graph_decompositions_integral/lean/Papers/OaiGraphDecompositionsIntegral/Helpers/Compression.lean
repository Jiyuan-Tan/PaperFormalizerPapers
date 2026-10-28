module
public import Papers.OaiGraphDecompositionsIntegral.Basic
public import Toolkit.Foundations.Probability.BiasedCube
public import Causalean.Experimentation.DesignBased.ProductBlock

/-! # Compression after an independent Bernoulli extension -/

public section

open Causalean.Experimentation.DesignBased
open scoped BigOperators

namespace Papers.OaiGraphDecompositionsIntegral

variable {Y : Type} [Fintype Y] [DecidableEq Y]

omit [DecidableEq Y] in
-- @node: compression_subset_bits
/-- [A finite set is contained in the subset selected by Boolean indicators
if and only if every indicator on that set is true](goal). -/
lemma compression_subset_bits (T : Finset Y) (z : Y → Bool) :
    T ⊆ toFinset' z ↔ ∀ i ∈ T, z i = true := by
  simp [toFinset', Finset.subset_iff]

-- @node: compression_inclusion_probability
/-- If [r is strictly between zero and one](hyp:hr), then [the probability
that a Bernoulli-r subset contains T is r raised to the number of elements
of T](goal). -/
lemma compression_inclusion_probability (r : ℝ) (hr : CompressionDensity r)
    (T : Finset Y) :
    (productMeasure Y r).Pr (fun z => T ⊆ toFinset' z) = r ^ T.card := by
  classical
  have hi (z : Y → Bool) :
      FiniteDesign.ind (fun z => T ⊆ toFinset' z) z = ∏ i ∈ T, treatInd i z := by
    by_cases h : T ⊆ toFinset' z
    · have ht := (compression_subset_bits T z).mp h
      simp only [FiniteDesign.ind, if_pos h]
      symm
      apply Finset.prod_eq_one
      intro i hi
      simp [treatInd, ht i hi]
    · have ht : ∃ i ∈ T, z i = false := by
        have hn := h
        rw [compression_subset_bits] at hn
        push Not at hn
        obtain ⟨i, hi, hz⟩ := hn
        exact ⟨i, hi, Bool.eq_false_iff.mpr hz⟩
      obtain ⟨i, hi, hz⟩ := ht
      rw [Finset.prod_eq_zero hi (by simp [treatInd, hz])]
      simp [FiniteDesign.ind, h]
  unfold productMeasure
  rw [Toolkit.Foundations.Probability.bernoulliCube_eq r hr.1.le hr.2.le]
  change (bernoulliDesign _ _ _).E _ = _
  rw [FiniteDesign.E_congr _ hi, bernoulliDesign_E_treatInd_prod]
  simp

-- @node: compression_smoothed_mono
/-- If [S is contained in T](hyp:hST), then [the probability of satisfying
the requirement family after an independent Bernoulli-r extension is no smaller
starting from T than starting from S](goal). -/
lemma compression_smoothed_mono (r : ℝ) (Q : Finset (Finset Y))
    {S T : Finset Y} (hST : S ⊆ T) :
    smoothedTest Y r Q S ≤ smoothedTest Y r Q T := by
  classical
  apply FiniteDesign.Pr_mono
  rintro z ⟨U, hU, hUS⟩
  exact ⟨U, hU, hUS.trans (Finset.union_subset_union hST (Finset.Subset.refl _))⟩

open Classical in
-- @node: compression_increment
/-- If [r is strictly between zero and one](hyp:hr), then [adding T to a
requirement family increases its Bernoulli-r satisfaction probability by r to
the size of T times one minus the satisfaction probability after independently
extending T with a Bernoulli-r subset](goal). -/
lemma compression_increment (r : ℝ) (hr : CompressionDensity r)
    (Q : Finset (Finset Y)) (T : Finset Y) :
    (productMeasure Y r).Pr (fun z => Satisfies (insert T Q) (toFinset' z)) =
      (productMeasure Y r).Pr (fun z => Satisfies Q (toFinset' z)) +
        r ^ T.card * (1 - smoothedTest Y r Q T) := by
  classical
  let D := productMeasure Y r
  let A := fun z : Y → Bool => T ⊆ toFinset' z
  let B := fun z : Y → Bool => Satisfies Q (toFinset' z)
  let C := fun z : Y → Bool => Satisfies Q (T ∪ toFinset' z)
  have hforce (z : Y → Bool) (hz : A z) : C z ↔ B z := by
    dsimp [C, B]
    rw [Finset.union_eq_right.mpr hz]
  have hfactor : D.Pr (fun z => A z ∧ ¬ C z) = D.Pr A * D.Pr (fun z => ¬ C z) := by
    have heq : D.Pr (fun z => A z ∧ ¬ C z) =
        D.E (fun z => FiniteDesign.ind A z * FiniteDesign.ind (fun z => ¬ C z) z) := by
      apply D.E_congr
      intro z
      by_cases ha : A z <;> by_cases hc : C z <;> simp [FiniteDesign.ind, ha, hc]
    rw [heq]
    change D.E _ = D.E _ * D.E _
    dsimp [D, productMeasure]
    rw [Toolkit.Foundations.Probability.bernoulliCube_eq r hr.1.le hr.2.le]
    apply FiniteDesign.E_prod_block_mul _ T
    · intro z z' h
      have ha : A z ↔ A z' := by
        simp only [A, compression_subset_bits]
        exact forall₂_congr fun i hi => by rw [h i hi]
      simp only [FiniteDesign.ind, ha]
    · intro z z' h
      have hu : T ∪ toFinset' z = T ∪ toFinset' z' := by
        ext i
        by_cases hi : i ∈ T
        · simp [hi]
        · simp [hi, toFinset', h i hi]
      simp only [FiniteDesign.ind, C, hu]
  have hcompl : D.Pr (fun z => ¬ C z) = 1 - smoothedTest Y r Q T := by
    have h := D.Pr_split (fun _ => True) C
    have hone : D.Pr (fun _ => True) = 1 := by
      change D.E (fun _ => (1 : ℝ)) = 1
      exact D.E_const 1
    have hc : D.Pr (fun z => True ∧ C z) = smoothedTest Y r Q T := by
      apply D.Pr_congr
      intro z
      simp [C]
    have hnc : D.Pr (fun z => True ∧ ¬ C z) = D.Pr (fun z => ¬ C z) := by
      apply D.Pr_congr
      intro z
      simp
    rw [hone, hc, hnc] at h
    linarith
  have hsplit := D.Pr_split (fun z => Satisfies (insert T Q) (toFinset' z)) B
  have hb : D.Pr (fun z => Satisfies (insert T Q) (toFinset' z) ∧ B z) = D.Pr B := by
    apply D.Pr_congr
    intro z
    constructor
    · exact And.right
    · rintro ⟨U, hU, hUz⟩
      exact ⟨⟨U, Finset.mem_insert_of_mem hU, hUz⟩, U, hU, hUz⟩
  have hn : D.Pr (fun z => Satisfies (insert T Q) (toFinset' z) ∧ ¬ B z) =
      D.Pr (fun z => A z ∧ ¬ C z) := by
    apply D.Pr_congr
    intro z
    constructor
    · rintro ⟨⟨U, hU, hUz⟩, hnB⟩
      have ha : A z := by
        rcases Finset.mem_insert.mp hU with hU | hU
        · simpa [hU] using hUz
        · exact False.elim (hnB ⟨U, hU, hUz⟩)
      exact ⟨ha, fun hc => hnB ((hforce z ha).mp hc)⟩
    · rintro ⟨ha, hnC⟩
      exact ⟨⟨T, Finset.mem_insert_self _ _, ha⟩, fun hb => hnC ((hforce z ha).mpr hb)⟩
  rw [hb, hn, hfactor, hcompl] at hsplit
  change D.Pr _ = D.Pr B + _
  rw [hsplit]
  congr 1
  rw [show D.Pr A = r ^ T.card from compression_inclusion_probability r hr T]

-- @node: lem:compression
/-- Suppose [the ground set is finite](hyp:hground), [r is strictly between zero
and one](hyp:hr), [s is a positive integer](hyp:hs), and [R is a nonempty family
whose members have between one and s elements](hyp:hR). Then [R contains a
nonempty subfamily Q of size at most the ceiling of twice r to the power minus s,
such that every set satisfying R has probability at least one-half of satisfying
Q after an independent Bernoulli-r extension](goal). -/
lemma compression (r : ℝ) (s : ℕ) (R : Finset (Finset Y))
    (hground : CompressionGround Y) (hr : CompressionDensity r)
    (hs : CompressionSize s) (hR : CompressionFamily R s) :
    ∃ Q : Finset (Finset Y), Q ⊆ R ∧ Q.Nonempty ∧
      (Q.card : ℝ) ≤ (⌈2 * r ^ (-(s : ℤ))⌉ : ℤ) ∧
      ∀ S : Finset Y, Satisfies R S → (1 / 2 : ℝ) ≤ smoothedTest Y r Q S := by
  classical
  let D := productMeasure Y r
  let mass := fun Q : Finset (Finset Y) => D.Pr (fun z => Satisfies Q (toFinset' z))
  let c : ℝ := (1 / 2) * r ^ s
  have hc : 0 < c := mul_pos (by norm_num) (pow_pos hr.1 _)
  -- Each greedy addition preserves this probability budget. Choose one with
  -- maximal cardinality to express termination without an arbitrary ordering.
  let candidates := R.powerset.filter (fun Q => c * (Q.card : ℝ) ≤ mass Q)
  have hstart : (∅ : Finset (Finset Y)) ∈ candidates := by
    simp only [candidates, Finset.mem_filter, Finset.mem_powerset,
      Finset.empty_subset, Finset.card_empty, Nat.cast_zero, mul_zero, true_and]
    exact D.Pr_nonneg _
  obtain ⟨Q, hQ, hmax⟩ := candidates.exists_max_image Finset.card ⟨∅, hstart⟩
  obtain ⟨hQR, hbudget⟩ := Finset.mem_filter.mp hQ
  have hQR' : Q ⊆ R := Finset.mem_powerset.mp hQR
  have hterminal : ∀ T ∈ R, (1 / 2 : ℝ) ≤ smoothedTest Y r Q T := by
    intro T hTR
    by_contra hbad
    have hbad' : smoothedTest Y r Q T < 1 / 2 := lt_of_not_ge hbad
    have hpow : r ^ s ≤ r ^ T.card :=
      pow_le_pow_of_le_one hr.1.le hr.2.le (hR.2 T hTR).2
    have hincrement := compression_increment r hr Q T
    have hgain : c < r ^ T.card * (1 - smoothedTest Y r Q T) := by
      calc
        c ≤ r ^ T.card * (1 / 2) := by dsimp [c]; nlinarith
        _ < r ^ T.card * (1 - smoothedTest Y r Q T) :=
          mul_lt_mul_of_pos_left (by linarith) (pow_pos hr.1 _)
    have hTQ : T ∉ Q := by
      intro hTQ
      rw [Finset.insert_eq_of_mem hTQ] at hincrement
      have : r ^ T.card * (1 - smoothedTest Y r Q T) = 0 := by linarith
      linarith
    have hnext : insert T Q ∈ candidates := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_powerset.mpr (Finset.insert_subset hTR hQR'), ?_⟩
      rw [Finset.card_insert_of_notMem hTQ, Nat.cast_add, Nat.cast_one]
      change c * ((Q.card : ℝ) + 1) ≤ mass (insert T Q)
      change mass (insert T Q) = mass Q + _ at hincrement
      nlinarith
    have hcard := hmax (insert T Q) hnext
    rw [Finset.card_insert_of_notMem hTQ] at hcard
    omega
  have hnonempty : Q.Nonempty := by
    by_contra h
    have hzero : Q = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    obtain ⟨T, hT⟩ := hR.1
    have ht := hterminal T hT
    have hempty : smoothedTest Y r Q T = 0 := by
      rw [hzero]
      change D.E _ = 0
      have he : (FiniteDesign.ind (fun z => Satisfies (∅ : Finset (Finset Y))
          (T ∪ toFinset' z))) = fun _ => (0 : ℝ) := by
        funext z
        simp [FiniteDesign.ind, Satisfies]
      rw [he, D.E_const]
    linarith
  have hbound : (Q.card : ℝ) ≤ 2 * r ^ (-(s : ℤ)) := by
    have hm : mass Q ≤ 1 := D.Pr_le_one _
    have hp : 0 < r ^ s := pow_pos hr.1 _
    have hdiv : (Q.card : ℝ) ≤ 2 / r ^ s := by
      apply (le_div_iff₀ hp).mpr
      dsimp [c] at hbudget
      nlinarith
    simpa only [zpow_neg, zpow_natCast, div_eq_mul_inv] using hdiv
  refine ⟨Q, hQR', hnonempty, hbound.trans (Int.le_ceil _), ?_⟩
  intro S hS
  obtain ⟨T, hTR, hTS⟩ := hS
  exact (hterminal T hTR).trans (compression_smoothed_mono r Q hTS)

end Papers.OaiGraphDecompositionsIntegral

module
public import Papers.OaiGeometricErdosSimilarity.Helpers.ScaleDefinitions
public import Papers.OaiGeometricErdosSimilarity.Helpers.ScalePartition

/-! # Counting scale boundaries and representatives -/

public section

namespace Papers.OaiGeometricErdosSimilarity

open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {q : ℝ} {M d g r0 n0 : ℕ}

-- @node: grid_crossings_card_le
/-- If [the grid resolution N is positive](hyp:hN), [the slope v is positive](hyp:hv),
and [every scale in the finite set S lies between one and two and makes x + tv an
integer multiple of 1/N](hyp:hS), then [S contains at most 1 + Nv scales](goal). -/
lemma grid_crossings_card_le (S : Finset ℝ) (N : ℕ) (hN : 0 < N)
    (x v : ℝ) (hv : 0 < v)
    (hS : ∀ t ∈ S, t ∈ Set.Icc (1 : ℝ) 2 ∧ ∃ k : ℤ, x + t * v = k / N) :
    (S.card : ℝ) ≤ 1 + N * v := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  let f := fun t : ℝ => ⌊(N : ℝ) * (x + t * v)⌋
  have hf (t : ℝ) (ht : t ∈ S) : (f t : ℝ) = (N : ℝ) * (x + t * v) := by
    obtain ⟨_, k, hk⟩ := hS t ht
    simp only [f, hk, mul_div_cancel₀ _ hNr.ne', Int.floor_intCast]
  let A := (N : ℝ) * (x + v)
  let B := (N : ℝ) * (x + 2 * v)
  have hmap : Set.MapsTo f (S : Set ℝ) (Finset.Icc ⌈A⌉ ⌊B⌋ : Finset ℤ) := by
    intro t ht
    have ht' := (hS t ht).1
    apply Finset.mem_Icc.mpr
    constructor
    · apply Int.ceil_le.mpr
      rw [hf t ht]
      dsimp [A]
      exact mul_le_mul_of_nonneg_left (by nlinarith [ht'.1]) hNr.le
    · apply Int.le_floor.mpr
      rw [hf t ht]
      dsimp [B]
      exact mul_le_mul_of_nonneg_left (by nlinarith [ht'.2]) hNr.le
  have hinj : Set.InjOn f (S : Set ℝ) := by
    intro t ht s hs heq
    have heq' := congrArg (fun k : ℤ => (k : ℝ)) heq
    rw [hf t ht, hf s hs] at heq'
    nlinarith [mul_pos hNr hv]
  have hc := Finset.card_le_card_of_injOn f hmap hinj
  by_cases h : ⌈A⌉ ≤ ⌊B⌋
  · have hcast : ((Finset.Icc ⌈A⌉ ⌊B⌋).card : ℝ) =
        (⌊B⌋ : ℝ) + 1 - (⌈A⌉ : ℝ) := by
      rw [Int.card_Icc]
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega : 0 ≤ ⌊B⌋ + 1 - ⌈A⌉)]
      push_cast
      rfl
    have hc' : (S.card : ℝ) ≤ (⌊B⌋ : ℝ) + 1 - (⌈A⌉ : ℝ) := by
      exact (Nat.cast_le.mpr hc : (S.card : ℝ) ≤ _).trans_eq hcast
    have ha := Int.le_ceil A
    have hb := Int.floor_le B
    dsimp [A, B] at ha hb
    nlinarith
  · have hzero : S.card = 0 := by
      have : (Finset.Icc ⌈A⌉ ⌊B⌋).card = 0 := by
        rw [Finset.card_eq_zero, Finset.Icc_eq_empty_of_lt (lt_of_not_ge h)]
      omega
    rw [hzero, Nat.cast_zero]
    positivity

-- @node: local_grid_resolution_mul_pow_le
/-- If [q lies strictly between zero and one](hyp:hq), [M is at least two](hyp:hM),
[the depth is positive](hyp:hd), [the gap is positive](hyp:hg), [the base length is
positive](hyp:hr), and [n belongs to child i's local window at U](hyp:hn), then
[the grid resolution at that child's block endpoint times qⁿ is at most twice the
grid constant times q raised to minus twice U's local window length](goal). -/
lemma local_grid_resolution_mul_pow_le (hq : QDomain q) (hM : BranchingDomain M)
    (hd : DepthDomain d) (hg : GapDomain g) (hr : BaseLengthDomain r0)
    (U : InternalVertex M d) (i : Fin M) (n : ℕ)
    (hn : n ∈ windowSet q M d g r0 n0 (localEdge U i)) :
    (gridResolution q (blockEndpoint q M d g r0 n0 (localEdge U i)) : ℝ) * q ^ n ≤
      2 * gridConst q * q ^ (-(2 * (localLength M g r0 U : ℤ))) := by
  let B := blockEndpoint q M d g r0 n0 (localEdge U i)
  have hspan := blockEndpoint_sub_windowStart_le (n0 := n0) q g r0 hq hM hd hg hr
    (localEdge U i) (vertexHeight U.val) (localEdge_sourceHeight U i)
  have hnlo := (Finset.mem_Icc.mp hn).1
  have hexp : -(2 * (localLength M g r0 U : ℤ)) ≤ -(B : ℤ) + (n : ℤ) := by
    dsimp [B, localLength]
    omega
  have hsize := (gridSizeComparison_of_qDomain q hq B).2.le
  have hpow := zpow_le_zpow_right_of_le_one₀ hq.1 hq.2.le hexp
  have hc : 0 ≤ 2 * gridConst q := by
    unfold gridConst
    have hq1 : 0 < 1 - q := sub_pos.mpr hq.2
    positivity
  calc
    _ ≤ (2 * gridConst q * q ^ (-(B : ℤ))) * q ^ n :=
      mul_le_mul_of_nonneg_right hsize (pow_pos hq.1 n).le
    _ = 2 * gridConst q * q ^ (-(B : ℤ) + (n : ℤ)) := by
      rw [zpow_add₀ hq.1.ne', zpow_natCast]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow hc

-- @node: scaleBreakpoints_card_le
/-- If [q lies strictly between zero and one](hyp:hq), [M is at least two](hyp:hM),
[the depth is positive](hyp:hd), [the gap is positive](hyp:hg), and [the base length
is positive](hyp:hr), then [the number of scale breakpoints at U and x is at most
(M − 1)r times (1 + 2cq⁻²ʳ), where r is U's local window length and c is the grid
constant](goal). -/
lemma scaleBreakpoints_card_le (hq : QDomain q) (hM : BranchingDomain M)
    (hd : DepthDomain d) (hg : GapDomain g) (hr : BaseLengthDomain r0)
    (U : InternalVertex M d) (x : ℝ) :
    ((scaleBreakpoints_finite (g := g) (r0 := r0) (n0 := n0) hq U x).toFinset.card : ℝ) ≤
      ((M : ℝ) - 1) * localLength M g r0 U *
        (1 + 2 * gridConst q * q ^ (-(2 * (localLength M g r0 U : ℤ)))) := by
  let B := (scaleBreakpoints_finite (g := g) (r0 := r0) (n0 := n0) hq U x).toFinset
  let I := localIndexPairs q M d g r0 n0 U
  let F := fun a : Fin M × ℕ => B.filter (fun t => localPoint x t q a.2 ∈
    gridLattice q (blockEndpoint q M d g r0 n0 (localEdge U a.1)))
  have hcover : B ⊆ I.biUnion F := by
    intro t ht
    obtain ⟨ht', a, ha, hlat⟩ := (Set.Finite.mem_toFinset _).mp ht
    exact Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_filter.mpr ⟨ht, hlat⟩⟩
  have hF (a : Fin M × ℕ) (ha : a ∈ I) :
      ((F a).card : ℝ) ≤ 1 + 2 * gridConst q * q ^ (-(2 * (localLength M g r0 U : ℤ))) := by
    have hgrid := grid_crossings_card_le (F a)
      (gridResolution q (blockEndpoint q M d g r0 n0 (localEdge U a.1)))
      (gridResolution_pos q _) x (q ^ a.2) (pow_pos hq.1 _) ?_
    · exact hgrid.trans (add_le_add_right
        (local_grid_resolution_mul_pow_le hq hM hd hg hr U a.1 a.2
          ((mem_localIndexPairs_iff U a).mp ha).2) 1)
    · intro t ht
      have htB := (Finset.mem_filter.mp ht).1
      have htlat := (Finset.mem_filter.mp ht).2
      exact ⟨((Set.Finite.mem_toFinset _).mp htB).1, htlat⟩
  calc
    _ ≤ ((I.biUnion F).card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card hcover)
    _ ≤ ∑ a ∈ I, ((F a).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ I, (1 + 2 * gridConst q * q ^ (-(2 * (localLength M g r0 U : ℤ)))) :=
      Finset.sum_le_sum hF
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, I, localIndexPairs_card hq hM hd hg hr,
        Nat.cast_mul, Nat.cast_sub (by unfold BranchingDomain at hM; omega : 1 ≤ M), Nat.cast_one]

-- @node: scaleRepresentatives_card_le
/-- If [q lies strictly between zero and one](hyp:hq), [M is at least two](hyp:hM),
[the depth is positive](hyp:hd), [the gap is positive](hyp:hg), and [the base length
is positive](hyp:hr), then [the number of representative scales at U and x is at most
the scale-count bound 4 + 2(M − 1)r(1 + 2cq⁻²ʳ), with r equal to U's local window
length and c equal to the grid constant](goal). -/
lemma scaleRepresentatives_card_le (hq : QDomain q) (hM : BranchingDomain M)
    (hd : DepthDomain d) (hg : GapDomain g) (hr : BaseLengthDomain r0)
    (U : InternalVertex M d) (x : ℝ) :
    ((scaleRepresentatives (g := g) (r0 := r0) (n0 := n0) hq U x).card : ℝ) ≤
      scaleCount M q (localLength M g r0 U) := by
  have hb := scaleBreakpoints_card_le (n0 := n0) hq hM hd hg hr U x
  have he : (scaleEndpoints (g := g) (r0 := r0) (n0 := n0) hq U x).card ≤
      2 + (scaleBreakpoints_finite (g := g) (r0 := r0) (n0 := n0) hq U x).toFinset.card := by
    exact (Finset.card_union_le _ _).trans (by norm_num)
  have hc := endpoint_midpoints_card_le (scaleEndpoints (g := g) (r0 := r0) (n0 := n0) hq U x)
  change (scaleRepresentatives hq U x).card ≤ _ at hc
  have he' : ((scaleEndpoints (g := g) (r0 := r0) (n0 := n0) hq U x).card : ℝ) ≤
      2 + (scaleBreakpoints_finite (g := g) (r0 := r0) (n0 := n0) hq U x).toFinset.card := by
    exact_mod_cast he
  have hc' : ((scaleRepresentatives (g := g) (r0 := r0) (n0 := n0) hq U x).card : ℝ) ≤
      2 * (scaleEndpoints (g := g) (r0 := r0) (n0 := n0) hq U x).card := by exact_mod_cast hc
  unfold scaleCount
  nlinarith

end Papers.OaiGeometricErdosSimilarity

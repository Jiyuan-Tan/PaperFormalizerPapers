module
public import Papers.OaiUniformInfluenceHypergraph.Helpers.Block
public import Papers.OaiUniformInfluenceHypergraph.Helpers.Capture
public import Papers.OaiUniformInfluenceHypergraph.Helpers.LargeN

/-! # The uniform variance bound

The captured-mass estimate completes its definition node. The constant in the
main theorem is chosen before `n`, `p`, and `f`; no monotonicity is assumed.
-/

public section

open scoped BigOperators

namespace Papers.OaiUniformInfluenceHypergraph

/-- Suppose [the bias is strictly between zero and one](hyp:hp), [the block size
is at least r + 1 and at most n](hyp:hblock), [the Boolean response is invariant
under vertex permutations](hyp:hf), [r is at least three and at most n, and the
block size is between one and n](hyp:hd), [the block cutoff is positive](hyp:hk),
and [r times the induced support cutoff times (m − 1)/(n − 1) is at most
one half](hyp:hc). Then [the Fourier mass on nonempty supports up to that cutoff
is at most 2r times m raised to −1/4 times total edge influence](goal). -/
-- @node: capturedMass_le
lemma capturedMass_le (r m n : ℕ) (p : ℝ) (f : (Edge n r → Bool) → Bool)
    (hp : BiasInterior p) (hblock : BlockDomain r m n) (hf : IsHypergraphProperty f)
    (hd : CaptureDomain n r m) (hk : CapturePositiveCutoff (blockCutoff p m))
    (hc : CaptureCondition r n m (blockCutoff p m)) :
    capturedMass p f (supportCutoff r (blockCutoff p m)) ≤
      2 * r * (m : ℝ) ^ (-(1 : ℝ) / 4) * totalEdgeInfluence p f := by
  classical
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hd.2.2.1
  have hnpos : (0 : ℝ) < n := by
    have : 3 ≤ n := hd.1.trans hd.2.1
    exact_mod_cast (show 0 < n by omega)
  have hcap : (m : ℝ) / (2 * n) *
      capturedMass p f (supportCutoff r (blockCutoff p m)) ≤
      ∑ S : Finset (Edge n r),
        blockCaptureProb n r m hblock.2 (blockCutoff p m) S * hyperFourierCoeff p f S ^ 2 := by
    unfold capturedMass
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ S ∈ Finset.univ.filter (fun S : Finset (Edge n r) =>
          1 ≤ S.card ∧ (S.card : ℝ) ≤ supportCutoff r (blockCutoff p m)),
          blockCaptureProb n r m hblock.2 (blockCutoff p m) S * hyperFourierCoeff p f S ^ 2 := by
        apply Finset.sum_le_sum
        intro S hS
        exact mul_le_mul_of_nonneg_right
          (blockProb_capture_ge n r m (blockCutoff p m) hd hk hc S
            (Finset.mem_filter.mp hS).2) (sq_nonneg _)
      _ ≤ _ := Finset.sum_le_univ_sum_of_nonneg (fun S =>
        mul_nonneg ((blockLaw n m hblock.2).Pr_nonneg _) (sq_nonneg _))
  have hbound := hcap.trans (sum_blockProb_mul_fourierCoeff_sq_le r m n p f hp hblock hf)
  have hcancel : (m : ℝ) ^ (-(1 : ℝ) / 4) * ((r : ℝ) * m / n) * totalEdgeInfluence p f =
      (m : ℝ) / (2 * n) *
        (2 * r * (m : ℝ) ^ (-(1 : ℝ) / 4) * totalEdgeInfluence p f) := by
    field_simp
    <;> ring
  rw [hcancel] at hbound
  exact (mul_le_mul_iff_right₀ (div_pos hmpos (by positivity))).mp hbound


/-- [For an interior bias and a response invariant under vertex permutations,
if r + 1 ≤ m ≤ n, r ≥ 3, the block cutoff is positive, and r times the induced
support cutoff times (m − 1)/(n − 1) is at most one half, then the Fourier mass
on nonempty supports up to that cutoff is at most 2r times m raised to −1/4
times total edge influence](goal). -/
-- keep: Proof witness for the public CapturedMassEstimate proposition (def:captured-mass, eq:captured-mass); the main proof uses capturedMass_le directly.
lemma capturedMassEstimate_holds (r m n : ℕ) (p : ℝ) (f : (Edge n r → Bool) → Bool) :
    CapturedMassEstimate r m n p f := by
  intro hp hblock hf hd hk hc
  exact capturedMass_le r m n p f hp hblock hf hd hk hc

-- @node: variance_largeN_le
/-- Suppose [r is at least three](hyp:hr), [n is at least r](hyp:hn),
[the bias is strictly between zero and one](hyp:hp), and [the Boolean response
is invariant under vertex permutations](hyp:hf). If [the square-root block size
is at least r + 1](hyp:hm), [its logarithm is at least log(n)/3](hyp:hlog),
[r times log(n) raised to r/(r − 1) times n raised to −1/2 is at most one
half](hyp:hcapture), and [the block size raised to −1/4 times log(n) raised to
r/(r − 1) is at most one](hyp:hdecay), then [the response variance is at most
(2r + (192r) raised to r/(r − 1)) divided by log(n) raised to r/(r − 1),
times total edge influence](goal). -/
lemma variance_largeN_le (r n : ℕ) (hr : MainUniformity r) (hn : MainVertexCount n r)
    (p : ℝ) (hp : BiasInterior p) (f : (Edge n r → Bool) → Bool) (hf : IsHypergraphProperty f)
    (hm : r + 1 ≤ sqrtBlockSize n)
    (hlog : Real.log (n : ℝ) / 3 ≤ Real.log (sqrtBlockSize n : ℝ))
    (hcapture : (r : ℝ) * Real.log (n : ℝ) ^ captureExponent r *
      (n : ℝ) ^ (-(1 : ℝ) / 2) ≤ 1 / 2)
    (hdecay : (sqrtBlockSize n : ℝ) ^ (-(1 : ℝ) / 4) *
      Real.log (n : ℝ) ^ captureExponent r ≤ 1) :
    (biasedLaw (Edge n r) p).Var (boolValue f) ≤
      (2 * r + (192 * (r : ℝ)) ^ captureExponent r) /
        Real.log (n : ℝ) ^ captureExponent r * totalEdgeInfluence p f := by
  classical
  obtain ⟨hd, hk, hc⟩ := largeN_capture_parameters r n hr hn p hp hm hcapture
  have hm2 : 2 ≤ sqrtBlockSize n := by have : 3 ≤ r := hr; omega
  have hlogpos : 0 < Real.log (n : ℝ) := by
    apply Real.log_pos
    have : 3 ≤ r := hr
    have : r ≤ n := hn
    exact_mod_cast (show 1 < n by omega)
  have hpowpos := Real.rpow_pos_of_pos hlogpos (captureExponent r)
  have hI : 0 ≤ totalEdgeInfluence p f := (totalCoordInfluence_nonneg_le_card p f).1
  have hlo := capturedMass_le r (sqrtBlockSize n) n p f hp
    ⟨hm, sqrtBlockSize_le n⟩ hf hd hk hc
  have hdecay : (sqrtBlockSize n : ℝ) ^ (-(1 : ℝ) / 4) ≤
      1 / Real.log (n : ℝ) ^ captureExponent r :=
    (le_div_iff₀ hpowpos).mpr hdecay
  have hlo' : capturedMass p f (supportCutoff r (blockCutoff p (sqrtBlockSize n))) ≤
      (2 * r / Real.log (n : ℝ) ^ captureExponent r) * totalEdgeInfluence p f := by
    calc
      _ ≤ _ := hlo
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ hI
        simpa only [div_eq_mul_inv, mul_one, one_mul, mul_assoc] using
          mul_le_mul_of_nonneg_left hdecay (by positivity : (0 : ℝ) ≤ 2 * r)
  have hhi := (spectral_tail_le p hp f _ (supportCutoff_pos r hr _ hk)).trans
    (mul_le_mul_of_nonneg_right (bias_cancellation_le r n (sqrtBlockSize n) hr hn hm2 p hp hlog) hI)
  have hsplit : (biasedLaw (Edge n r) p).Var (boolValue f) =
      capturedMass p f (supportCutoff r (blockCutoff p (sqrtBlockSize n))) +
      ∑ S ∈ Finset.univ.filter (fun S : Finset (Edge n r) =>
        supportCutoff r (blockCutoff p (sqrtBlockSize n)) < (S.card : ℝ)),
        fourierCoeff p f S ^ 2 := by
    rw [variance_eq_sum_fourierCoeff_sq p hp f]
    unfold capturedMass
    simp only [hyperFourierCoeff, Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro S _
    by_cases he : S = ∅
    · subst S
      simp [not_lt.mpr (supportCutoff_pos r hr _ hk).le]
    · have hcard : 1 ≤ S.card := Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr he)
      by_cases hle : (S.card : ℝ) ≤ supportCutoff r (blockCutoff p (sqrtBlockSize n))
      · simp [he, hcard, hle, not_lt.mpr hle]
      · simp [he, hcard, hle, lt_of_not_ge hle]
  rw [hsplit]
  calc
    _ ≤ _ := add_le_add hlo' hhi
    _ = _ := by change _ + _ * totalEdgeInfluence p f = _; ring

-- @node: variance_bound_positive_constant
/-- [For every edge size r at least three, there is a strictly positive constant
C depending only on r such that, for every n at least r, every bias strictly
between zero and one, and every Boolean
response invariant under vertex permutations, the response variance is at most
C divided by log(n) raised to r/(r − 1), times total edge influence](goal). -/
lemma variance_bound_positive_constant :
    ∀ (r : ℕ), MainUniformity r →
      ∃ C : ℝ, 0 < C ∧ -- @realizes C_r(positive explicit constant chosen before n,p,f)
        ∀ (n : ℕ), MainVertexCount n r → ∀ (p : ℝ), MainBias p → BiasInterior p →
          ∀ (f : (Edge n r → Bool) → Bool), IsHypergraphProperty f →
            (biasedLaw (Edge n r) p).Var (boolValue f) ≤
              C / Real.log (n : ℝ) ^ captureExponent r * totalEdgeInfluence p f := by
  intro r hr
  obtain ⟨N, hrN, hN⟩ := exists_largeN_threshold r hr
  let A : ℝ := 2 * r + (192 * (r : ℝ)) ^ captureExponent r
  let C : ℝ := max A (Real.log (N : ℝ) ^ captureExponent r / 4)
  have hrpos : (0 : ℝ) < r := by
    exact_mod_cast (show 0 < r from lt_of_lt_of_le (by decide : 0 < 3) hr)
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨C, hA.trans_le (le_max_left _ _), ?_⟩
  intro n hn p _ hp f hf
  have hn1 : 1 < (n : ℝ) := by
    have : 3 ≤ r := hr
    have : r ≤ n := hn
    exact_mod_cast (show 1 < n by omega)
  have hlog := Real.log_pos hn1
  have hpow := Real.rpow_pos_of_pos hlog (captureExponent r)
  have hI : 0 ≤ totalEdgeInfluence p f := (totalCoordInfluence_nonneg_le_card p f).1
  by_cases hlarge : N ≤ n
  · obtain ⟨hm, hl, hc, hd⟩ := hN n hlarge
    exact (variance_largeN_le r n hr hn p hp f hf hm hl hc hd).trans
      (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (le_max_left _ _) hpow.le) hI)
  · have hnN : (n : ℝ) ≤ N := by exact_mod_cast (show n ≤ N by omega)
    have hlogs : Real.log (n : ℝ) ≤ Real.log (N : ℝ) :=
      Real.log_le_log (by linarith) hnN
    have hpows : Real.log (n : ℝ) ^ captureExponent r ≤
        Real.log (N : ℝ) ^ captureExponent r := by
      gcongr
      linarith [(captureExponent_bounds r hr).1]
    have hquarter : (1 : ℝ) / 4 ≤ C / Real.log (n : ℝ) ^ captureExponent r := by
      apply (le_div_iff₀ hpow).mpr
      calc
        _ = Real.log (n : ℝ) ^ captureExponent r / 4 := by ring
        _ ≤ Real.log (N : ℝ) ^ captureExponent r / 4 := by linarith
        _ ≤ C := le_max_right _ _
    have hs := biasScale_pos_le_half p hp
    have hsquare : biasScale p ^ 2 ≤ (1 : ℝ) / 4 := by nlinarith
    exact (variance_le_biasScale_sq_mul_influence p hp f).trans
      (mul_le_mul_of_nonneg_right (hsquare.trans hquarter) hI)

-- @node: thm:main
/-- [For every edge size r at least three, there is a nonnegative constant C
depending only on r such that, for every n at least r, every bias strictly
between zero and one, and every Boolean
response invariant under vertex permutations, the response variance is at most
C divided by log(n) raised to r/(r − 1), times total edge influence](goal). -/
theorem variance_le_div_log_pow_mul_totalInfluence :
    ∀ (r : ℕ), MainUniformity r →
      ∃ C : ℝ, 0 ≤ C ∧ -- @realizes C_r(nonnegative constant chosen before n,p,f)
        ∀ (n : ℕ), MainVertexCount n r → ∀ (p : ℝ), MainBias p → BiasInterior p →
          ∀ (f : (Edge n r → Bool) → Bool), IsHypergraphProperty f →
            (biasedLaw (Edge n r) p).Var (boolValue f) ≤
              C / Real.log (n : ℝ) ^ captureExponent r * totalEdgeInfluence p f := by
  intro r hr
  obtain ⟨C, hC, hbound⟩ := variance_bound_positive_constant r hr
  exact ⟨C, hC.le, hbound⟩

end Papers.OaiUniformInfluenceHypergraph

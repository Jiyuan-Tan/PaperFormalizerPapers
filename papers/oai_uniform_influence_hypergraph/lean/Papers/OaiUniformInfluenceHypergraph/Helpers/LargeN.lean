module
public import Papers.OaiUniformInfluenceHypergraph.Helpers.Fourier
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.Order.Floor.Ring

/-! # The vertex threshold and the uniform cancellation of the bias

The threshold is existentially chosen before the bias and Boolean function.
Its four properties are derived here from growth estimates.
-/

@[expose] public section

open scoped BigOperators

namespace Papers.OaiUniformInfluenceHypergraph

-- @realizes m(floor of sqrt n in the large-n branch)
/-- For a [nonnegative integer vertex count n](hyp:n), the [square-root block
size](goal) is the greatest nonnegative integer no larger than the square root of n. -/
noncomputable def sqrtBlockSize (n : ℕ) : ℕ := ⌊Real.sqrt (n : ℝ)⌋₊

-- @node: log_rpow_mul_neg_tendsto
/-- If [b is positive](hyp:hb), then [the a-th power of the natural logarithm
of n, multiplied by n to the power −b, converges to zero as the integer n
tends to infinity](goal), for every real exponent a. -/
lemma log_rpow_mul_neg_tendsto (a b : ℝ) (hb : 0 < b) :
    Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ) ^ a * (n : ℝ) ^ (-b))
      Filter.atTop (nhds 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop a hb).tendsto_div_nhds_zero
  have hn : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  convert h.comp hn using 1
  funext n
  simp only [Function.comp_apply, Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]

-- @node: sqrtBlockSize_ge_third_eventually
/-- [For all sufficiently large nonnegative integers n, the square-root block
size is at least the cube root of n](goal). -/
lemma sqrtBlockSize_ge_third_eventually :
    ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ) ^ (1 / 3 : ℝ) ≤ (sqrtBlockSize n : ℝ) := by
  have htwo := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 6)).eventually_ge_atTop 2
  have hone := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).eventually_ge_atTop 1
  have hn : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  filter_upwards [hn.eventually htwo, hn.eventually hone] with n htwo hone
  have hnpos : (0 : ℝ) < n := by
    by_contra h
    have hz : (n : ℝ) = 0 := le_antisymm (not_lt.mp h) (Nat.cast_nonneg n)
    norm_num [hz] at hone
  have hs : Real.sqrt (n : ℝ) = (n : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) ^ (1 / 6 : ℝ) := by
    rw [← Real.rpow_add hnpos]
    norm_num [Real.sqrt_eq_rpow]
  have hf := Nat.lt_floor_add_one (Real.sqrt (n : ℝ))
  change Real.sqrt (n : ℝ) < (sqrtBlockSize n : ℝ) + 1 at hf
  rw [hs] at hf
  nlinarith [mul_le_mul_of_nonneg_left htwo (by positivity : 0 ≤ (n : ℝ) ^ (1 / 3 : ℝ))]

-- @node: exists_largeN_threshold
/-- If [the integer uniformity r is at least three](hyp:hr), then [there is an
integer threshold N greater than r such that, for every n at least N, writing
m for the square-root block size and α for r divided by r − 1, one has
m ≥ r + 1, log m ≥ log n / 3, r (log n)^α n^(−1/2) ≤ 1/2, and
m^(−1/4) (log n)^α ≤ 1](goal). -/
lemma exists_largeN_threshold (r : ℕ) (hr : MainUniformity r) :
    ∃ N : ℕ, r < N ∧ ∀ n : ℕ, N ≤ n → -- @realizes N_r(integer threshold depending only on r)
      r + 1 ≤ sqrtBlockSize n ∧
      Real.log (n : ℝ) / 3 ≤ Real.log (sqrtBlockSize n : ℝ) ∧
      (r : ℝ) * Real.log (n : ℝ) ^ captureExponent r * (n : ℝ) ^ (-(1 : ℝ) / 2) ≤ 1 / 2 ∧
      (sqrtBlockSize n : ℝ) ^ (-(1 : ℝ) / 4) * Real.log (n : ℝ) ^ captureExponent r ≤ 1 := by
  have hn : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have hcube := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp hn).eventually_ge_atTop
    ((r : ℝ) + 1)
  have hdecay := log_rpow_mul_neg_tendsto (captureExponent r) (1 / 2) (by norm_num)
  have hscaled := hdecay.const_mul (r : ℝ)
  simp only [mul_zero] at hscaled
  have hsmall := hscaled.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hlast := (log_rpow_mul_neg_tendsto (captureExponent r) (1 / 12) (by norm_num)).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hall : ∀ᶠ n : ℕ in Filter.atTop,
      r + 1 ≤ sqrtBlockSize n ∧
      Real.log (n : ℝ) / 3 ≤ Real.log (sqrtBlockSize n : ℝ) ∧
      (r : ℝ) * Real.log (n : ℝ) ^ captureExponent r * (n : ℝ) ^ (-(1 : ℝ) / 2) ≤ 1 / 2 ∧
      (sqrtBlockSize n : ℝ) ^ (-(1 : ℝ) / 4) * Real.log (n : ℝ) ^ captureExponent r ≤ 1 := by
    filter_upwards [sqrtBlockSize_ge_third_eventually, hcube, hsmall, hlast,
      Filter.eventually_ge_atTop 1] with n hfloor hcube hsmall hlast hn1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hm : r + 1 ≤ sqrtBlockSize n := by exact_mod_cast hcube.trans hfloor
    refine ⟨hm, ?_, ?_, ?_⟩
    · have hl := Real.log_le_log (Real.rpow_pos_of_pos hnpos _) hfloor
      rw [Real.log_rpow hnpos] at hl
      linarith
    · simpa only [neg_div, mul_assoc] using hsmall.le
    · have hi := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hnpos (1 / 3))
        hfloor (by norm_num : -(1 : ℝ) / 4 ≤ 0)
      rw [← Real.rpow_mul hnpos.le] at hi
      norm_num at hi
      calc
        _ ≤ (n : ℝ) ^ (-(1 : ℝ) / 12) * Real.log (n : ℝ) ^ captureExponent r :=
          by simpa only [neg_div] using
            mul_le_mul_of_nonneg_right hi
              (show 0 ≤ Real.log (n : ℝ) ^ captureExponent r by positivity)
        _ ≤ 1 := by simpa only [mul_comm, neg_div] using hlast.le
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hall
  refine ⟨max N (r + 1), by omega, ?_⟩
  intro n hmax
  exact hN n (le_trans (le_max_left _ _) hmax)

-- @node: sqrtBlockSize_le
/-- [The square-root block size of any nonnegative integer n is no larger
than n itself](goal). -/
lemma sqrtBlockSize_le (n : ℕ) : sqrtBlockSize n ≤ n := by
  unfold sqrtBlockSize
  apply Nat.floor_le_of_le
  apply Real.sqrt_le_self_iff.mpr
  rcases n with _ | n
  · exact Or.inl (by simp)
  · exact Or.inr (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))

-- @node: largeN_capture_parameters
/-- Suppose [the uniformity r is at least three](hyp:hr), [the vertex count n
is at least r](hyp:hn), and [the bias p lies strictly between zero and one](hyp:hp).
If [the square-root block size m is at least r + 1](hyp:hm) and
[r (log n)^α n^(−1/2) ≤ 1/2, where α = r/(r − 1)](hyp:hlarge), then
[r ≥ 3, n ≥ r, and 1 ≤ m ≤ n; the cutoff k = σ log m / 64 is positive;
and r (k/r)^α (m − 1)/(n − 1) ≤ 1/2, where σ is the square root of
p times one minus p](goal). -/
lemma largeN_capture_parameters (r n : ℕ) (hr : MainUniformity r) (hn : MainVertexCount n r)
    (p : ℝ) (hp : BiasInterior p) (hm : r + 1 ≤ sqrtBlockSize n)
    (hlarge : (r : ℝ) * Real.log (n : ℝ) ^ captureExponent r *
      (n : ℝ) ^ (-(1 : ℝ) / 2) ≤ 1 / 2) :
    CaptureDomain n r (sqrtBlockSize n) ∧
      CapturePositiveCutoff (blockCutoff p (sqrtBlockSize n)) ∧
      CaptureCondition r n (sqrtBlockSize n) (blockCutoff p (sqrtBlockSize n)) := by
  have hr3 : 3 ≤ r := hr
  have hrn : r ≤ n := hn
  have hm2 : 2 ≤ sqrtBlockSize n := by omega
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hm1 : (1 : ℝ) < sqrtBlockSize n := by exact_mod_cast (show 1 < sqrtBlockSize n by omega)
  have hmn := sqrtBlockSize_le n
  have hlm : 0 < Real.log (sqrtBlockSize n : ℝ) := Real.log_pos hm1
  have hln : 0 < Real.log (n : ℝ) := Real.log_pos hn1
  have hlogs : Real.log (sqrtBlockSize n : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by linarith) (by exact_mod_cast hmn)
  have hk : CapturePositiveCutoff (blockCutoff p (sqrtBlockSize n)) :=
    lowCutoff_pos p _ hp (by change (2 : ℝ) ≤ sqrtBlockSize n; exact_mod_cast hm2)
  refine ⟨⟨hr3, hrn, by omega, hmn⟩, hk, ?_⟩
  have hbase : blockCutoff p (sqrtBlockSize n) / r ≤ Real.log (n : ℝ) := by
    apply (div_le_iff₀ hrpos).mpr
    have hs := biasScale_pos_le_half p hp
    have hklog : blockCutoff p (sqrtBlockSize n) ≤ Real.log (sqrtBlockSize n : ℝ) := by
      unfold blockCutoff lowCutoff
      apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 64)).mpr
      nlinarith
    exact hklog.trans (hlogs.trans (le_mul_of_one_le_right hln.le hr1))
  have hsupport : supportCutoff r (blockCutoff p (sqrtBlockSize n)) ≤
      Real.log (n : ℝ) ^ captureExponent r := by
    unfold supportCutoff
    exact Real.rpow_le_rpow (div_nonneg hk.le hrpos.le) hbase
      (by linarith [(captureExponent_bounds r hr).1])
  have hroot := Real.sqrt_nonneg (n : ℝ)
  have hrootsq := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hroot1 : 1 ≤ Real.sqrt (n : ℝ) := by nlinarith
  have hfloor : (sqrtBlockSize n : ℝ) ≤ Real.sqrt (n : ℝ) := Nat.floor_le hroot
  have hratio : ((sqrtBlockSize n : ℝ) - 1) / ((n : ℝ) - 1) ≤
      (n : ℝ) ^ (-(1 : ℝ) / 2) := by
    have heq : (n : ℝ) ^ (-(1 : ℝ) / 2) = 1 / Real.sqrt (n : ℝ) := by
      rw [Real.sqrt_eq_rpow, show -(1 : ℝ) / 2 = -(1 / 2 : ℝ) by ring,
        Real.rpow_neg (Nat.cast_nonneg n)]
      simp only [one_div]
    rw [heq]
    apply (div_le_div_iff₀ (by linarith : (0 : ℝ) < n - 1)
      (by linarith : 0 < Real.sqrt (n : ℝ))).mpr
    nlinarith
  unfold CaptureCondition
  calc
    _ ≤ (r : ℝ) * Real.log (n : ℝ) ^ captureExponent r *
        (n : ℝ) ^ (-(1 : ℝ) / 2) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hsupport (Nat.cast_nonneg r)
      · exact hratio
      · exact div_nonneg (by linarith) (by linarith)
      · positivity
    _ ≤ 1 / 2 := hlarge

-- @node: bias_cancellation_eq
/-- If [the uniformity r is at least three](hyp:hr), [the block size m is at
least two](hyp:hm), and [the bias p lies strictly between zero and one](hyp:hp),
then [σ² divided by the support cutoff at k = σ log m / 64 equals
(64r)^α σ^(2 − α) / (log m)^α, where σ is the square root of p times
one minus p and α = r/(r − 1)](goal). -/
lemma bias_cancellation_eq (r m : ℕ) (hr : MainUniformity r) (hm : 2 ≤ m)
    (p : ℝ) (hp : BiasInterior p) :
    biasScale p ^ 2 / supportCutoff r (blockCutoff p m) =
      (64 * (r : ℝ)) ^ captureExponent r * biasScale p ^ (2 - captureExponent r) /
        Real.log (m : ℝ) ^ captureExponent r := by
  have hs := (biasScale_pos_le_half p hp).1
  have hrpos : (0 : ℝ) < r := by
    have : 3 ≤ r := hr
    exact_mod_cast (show 0 < r by omega)
  have hlog : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  have hbase : blockCutoff p m / r = biasScale p * Real.log (m : ℝ) / (64 * r) := by
    unfold blockCutoff lowCutoff
    ring
  rw [supportCutoff, hbase, Real.div_rpow (mul_pos hs hlog).le (by positivity),
    Real.mul_rpow hs.le hlog.le, Real.rpow_sub hs]
  field_simp
  rw [Real.rpow_two]

-- @node: bias_cancellation_le
/-- Suppose [the uniformity r is at least three](hyp:hr), [the vertex count n
is at least r](hyp:hn), [the block size m is at least two](hyp:hm), and
[the bias p lies strictly between zero and one](hyp:hp). If
[log m ≥ log n / 3](hyp:hlog), then [σ² divided by the support cutoff at
k = σ log m / 64 is at most (192r)^α / (log n)^α, where σ is the square
root of p times one minus p and α = r/(r − 1)](goal). -/
lemma bias_cancellation_le (r n m : ℕ) (hr : MainUniformity r) (hn : MainVertexCount n r)
    (hm : 2 ≤ m) (p : ℝ) (hp : BiasInterior p)
    (hlog : Real.log (n : ℝ) / 3 ≤ Real.log (m : ℝ)) :
    biasScale p ^ 2 / supportCutoff r (blockCutoff p m) ≤
      (192 * (r : ℝ)) ^ captureExponent r / Real.log (n : ℝ) ^ captureExponent r := by
  have hs := biasScale_pos_le_half p hp
  have ha := captureExponent_bounds r hr
  have hrpos : (0 : ℝ) < r := by
    have : 3 ≤ r := hr
    exact_mod_cast (show 0 < r by omega)
  have hnpos : 1 < (n : ℝ) := by
    have : r ≤ n := hn
    have : 3 ≤ r := hr
    exact_mod_cast (show 1 < n by omega)
  have hln := Real.log_pos hnpos
  have hlm : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  have hpow : biasScale p ^ (2 - captureExponent r) ≤ 1 :=
    Real.rpow_le_one hs.1.le (by linarith [hs.2]) (by linarith [ha.2])
  have hlogpow : Real.log (n : ℝ) ^ captureExponent r ≤
      (3 * Real.log (m : ℝ)) ^ captureExponent r := by
    gcongr <;> linarith
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hlm.le] at hlogpow
  have hconst : (192 * (r : ℝ)) ^ captureExponent r =
      (64 * (r : ℝ)) ^ captureExponent r * 3 ^ captureExponent r := by
    rw [← Real.mul_rpow (by positivity) (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  rw [bias_cancellation_eq r m hr hm p hp]
  calc
    _ ≤ (64 * (r : ℝ)) ^ captureExponent r / Real.log (m : ℝ) ^ captureExponent r := by
      apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg hlm.le _)
      exact mul_le_of_le_one_right (Real.rpow_nonneg (by positivity) _) hpow
    _ ≤ _ := by
      apply (div_le_div_iff₀ (Real.rpow_pos_of_pos hlm _) (Real.rpow_pos_of_pos hln _)).mpr
      rw [hconst, mul_assoc]
      exact mul_le_mul_of_nonneg_left hlogpow (Real.rpow_nonneg (by positivity) _)

-- @node: spectral_tail_le
/-- For [a Boolean-valued function h on a finite Boolean cube](hyp:h), if
[the bias p lies strictly between zero and one](hyp:hp) and [the degree
threshold L is positive](hyp:hL), then [the sum of squared Fourier coefficients
at degrees greater than L is at most p times one minus p, divided by L,
times the total coordinate influence of h](goal). -/
lemma spectral_tail_le (p : ℝ) (hp : BiasInterior p) {J : Type*} [Fintype J] [DecidableEq J]
    (h : (J → Bool) → Bool) (L : ℝ) (hL : 0 < L) :
    (∑ S ∈ Finset.univ.filter (fun S : Finset J => L < (S.card : ℝ)), fourierCoeff p h S ^ 2) ≤
      biasScale p ^ 2 / L * totalCoordInfluence p h := by
  have hdiv : biasScale p ^ 2 / L * totalCoordInfluence p h =
      (biasScale p ^ 2 * totalCoordInfluence p h) / L := by ring
  rw [hdiv]
  apply (le_div_iff₀ hL).mpr
  calc
    (∑ S ∈ Finset.univ.filter (fun S : Finset J => L < (S.card : ℝ)),
        fourierCoeff p h S ^ 2) * L =
      ∑ S ∈ Finset.univ.filter (fun S : Finset J => L < (S.card : ℝ)),
        L * fourierCoeff p h S ^ 2 := by rw [Finset.sum_mul]; simp_rw [mul_comm L]
    _ ≤ ∑ S ∈ Finset.univ.filter (fun S : Finset J => L < (S.card : ℝ)),
        (S.card : ℝ) * fourierCoeff p h S ^ 2 := by
      apply Finset.sum_le_sum
      intro S hS
      exact mul_le_mul_of_nonneg_right (Finset.mem_filter.mp hS).2.le (sq_nonneg _)
    _ ≤ ∑ S : Finset J, (S.card : ℝ) * fourierCoeff p h S ^ 2 :=
      Finset.sum_le_univ_sum_of_nonneg (fun S => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
    _ = biasScale p ^ 2 * totalCoordInfluence p h :=
      weightedSpectralMass_eq p hp h

end Papers.OaiUniformInfluenceHypergraph

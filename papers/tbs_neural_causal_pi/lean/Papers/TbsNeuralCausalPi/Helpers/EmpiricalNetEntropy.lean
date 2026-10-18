module
public import Papers.TbsNeuralCausalPi.Helpers.EmpiricalTestNets
/-! # Logarithmic entropy of the anchored cube test net

The explicit grid and value-bin count is converted to the entropy term in
the uniform Wasserstein deviation bound. Constants depend only on the
output dimension and range, and the estimates allow every positive radius.
-/
public section
namespace Papers.TbsNeuralCausalPi
set_option linter.style.whitespace false

/-- If [a is nonnegative](hyp:ha) and [t is nonnegative](hyp:ht),
[(1 + at) raised to the natural-number dimension d is at most
(1 + a) raised to d times (1 + t raised to d)](goal). -/
-- @node: empirical_grid_polynomial_le
lemma empirical_grid_polynomial_le (d : ℕ) {a t : ℝ}
    (ha : 0 ≤ a) (ht : 0 ≤ t) :
    (1 + a*t)^d ≤ (1+a)^d * (1+t^d) := by
  rcases le_total t 1 with htone | honet
  · have hbase : 1+a*t ≤ 1+a := by nlinarith
    calc
      _ ≤ (1+a)^d := pow_le_pow_left₀ (by positivity) hbase d
      _ ≤ _ := by nlinarith [pow_nonneg ht d, pow_nonneg (by positivity : 0 ≤ 1+a) d]
  · have hbase : 1+a*t ≤ (1+a)*t := by nlinarith
    calc
      _ ≤ ((1+a)*t)^d := pow_le_pow_left₀ (by positivity) hbase d
      _ = (1+a)^d*t^d := mul_pow _ _ _
      _ ≤ _ := by nlinarith [pow_nonneg (by positivity : 0 ≤ 1+a) d]

/-- If [a is nonnegative](hyp:ha) and [δ is positive](hyp:hdelta),
[log(1 + a/δ) is at most (1 + log(1 + a)/log 2) log(2 + 1/δ)](goal). -/
-- @node: empirical_value_bin_log_le
lemma empirical_value_bin_log_le {a delta : ℝ} (ha : 0 ≤ a) (hdelta : 0 < delta) :
    Real.log (1+a/delta) ≤
      (1 + Real.log (1+a) / Real.log 2) * Real.log (2+delta⁻¹) := by
  have hi : 0 ≤ delta⁻¹ := inv_nonneg.mpr hdelta.le
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log 2 ≤ Real.log (2+delta⁻¹) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hloga : 0 ≤ Real.log (1+a) := Real.log_nonneg (by linarith)
  have hbase : 1+a/delta ≤ (1+a)*(2+delta⁻¹) := by
    rw [div_eq_mul_inv]
    nlinarith
  have h := Real.log_le_log (by positivity : 0 < 1+a/delta) hbase
  rw [Real.log_mul (by positivity : 1+a ≠ 0) (by positivity : 2+delta⁻¹ ≠ 0)] at h
  have habsorb : Real.log (1+a) ≤
      (Real.log (1+a) / Real.log 2) * Real.log (2+delta⁻¹) := by
    calc
      _ = (Real.log (1+a) / Real.log 2) * Real.log 2 := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hlog (div_nonneg hloga hlog2.le)
  nlinarith

/-- If [a is nonnegative](hyp:ha), [b is nonnegative](hyp:hb),
[δ is positive](hyp:hdelta), and [the finite set has at most
(floor(a/δ) + 1) raised to the power (floor(b/δ) + 1)ᵈ elements](hyp:hcard),
[the logarithm of its size is at most
(1 + b)ᵈ(1 + log(1 + a)/log 2)(1 + δ⁻ᵈ) log(2 + 1/δ)](goal).

The logarithm of zero is taken to be zero. -/
-- @node: empirical_pattern_card_log_le
lemma empirical_pattern_card_log_le {I : Type*} (T : Finset I) (d : ℕ)
    {a b delta : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hdelta : 0 < delta)
    (hcard : T.card ≤ (⌊a/delta⌋₊+1)^((⌊b/delta⌋₊+1)^d)) :
    Real.log (T.card : ℝ) ≤
      ((1+b)^d * (1 + Real.log (1+a) / Real.log 2)) *
        ((1+delta^(-(d : ℤ))) * Real.log (2+delta⁻¹)) := by
  have ha0 : 0 ≤ a/delta := div_nonneg ha hdelta.le
  have hb0 : 0 ≤ b/delta := div_nonneg hb hdelta.le
  have hlog0 : 0 ≤ Real.log (2+delta⁻¹) :=
    Real.log_nonneg (by linarith [inv_nonneg.mpr hdelta.le])
  have hcoef : 0 ≤ 1 + Real.log (1+a) / Real.log 2 := by
    have := Real.log_nonneg (by linarith : 1 ≤ 1+a)
    have := Real.log_pos (by norm_num : (1:ℝ) < 2)
    positivity
  have hzpow : (delta⁻¹)^d = delta^(-(d : ℤ)) := by simp
  have hgrid : (((⌊b/delta⌋₊+1)^d : ℕ) : ℝ) ≤
      (1+b)^d * (1+delta^(-(d : ℤ))) := by
    calc
      _ = ((⌊b/delta⌋₊ : ℝ)+1)^d := by norm_cast
      _ ≤ (1+b/delta)^d :=
        pow_le_pow_left₀ (by positivity) (by linarith [Nat.floor_le hb0]) d
      _ = (1+b*delta⁻¹)^d := by rw [div_eq_mul_inv]
      _ ≤ _ := by
        simpa only [hzpow] using empirical_grid_polynomial_le d hb (inv_nonneg.mpr hdelta.le)
  have hbins : Real.log ((⌊a/delta⌋₊ : ℝ)+1) ≤
      (1 + Real.log (1+a) / Real.log 2) * Real.log (2+delta⁻¹) := by
    exact (Real.log_le_log (by positivity) (by linarith [Nat.floor_le ha0])).trans
      (empirical_value_bin_log_le ha hdelta)
  by_cases hz : T.card = 0
  · simp only [hz, Nat.cast_zero, Real.log_zero]
    exact mul_nonneg (mul_nonneg (pow_nonneg (by positivity) d) hcoef)
      (mul_nonneg (by positivity) hlog0)
  · have hpos : (0:ℝ) < T.card := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hz)
    have hcount : (T.card : ℝ) ≤
        ((⌊a/delta⌋₊ : ℝ)+1)^((⌊b/delta⌋₊+1)^d) := by exact_mod_cast hcard
    calc
      _ ≤ Real.log (((⌊a/delta⌋₊ : ℝ)+1)^((⌊b/delta⌋₊+1)^d)) :=
        Real.log_le_log hpos hcount
      _ = (((⌊b/delta⌋₊+1)^d : ℕ) : ℝ) * Real.log ((⌊a/delta⌋₊ : ℝ)+1) :=
        Real.log_pow _ _
      _ ≤ ((1+b)^d * (1+delta^(-(d : ℤ)))) *
          ((1 + Real.log (1+a) / Real.log 2) * Real.log (2+delta⁻¹)) :=
        mul_le_mul hgrid hbins
          (Real.log_nonneg (by
            have := (Nat.cast_nonneg (⌊a/delta⌋₊) : (0:ℝ) ≤ ⌊a/delta⌋₊)
            linarith))
          (by positivity)
      _ = _ := by ring

/-- For [a nonnegative cube bound K](hyp:hK), [there is a positive constant C
such that, for every positive δ, a finite set of tests that vanish at zero
and are one-Lipschitz on the d-dimensional cube has log cardinality at most
C(1 + δ⁻ᵈ) log(2 + 1/δ), and approximates every such test uniformly on the
cube within δ/2](goal). -/
-- @node: exists_anchored_cube_test_net_entropy
lemma exists_anchored_cube_test_net_entropy (d : ℕ) {K : ℝ} (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ delta : ℝ, 0 < delta →
      ∃ T : Finset (L1Vec d → ℝ),
        (∀ g ∈ T, LipschitzOnWith 1 g (boundedCube d K) ∧ g 0 = 0) ∧
        Real.log (T.card : ℝ) ≤
          C * ((1+delta^(-(d : ℤ))) * Real.log (2+delta⁻¹)) ∧
        ∀ h : L1Vec d → ℝ, LipschitzOnWith 1 h (boundedCube d K) → h 0 = 0 →
          ∃ g ∈ T, ∀ x ∈ boundedCube d K, |h x-g x| ≤ delta/2 := by
  let a : ℝ := 16*d*K
  let b : ℝ := 16*K*(d+1)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  refine ⟨(1+b)^d * (1 + Real.log (1+a) / Real.log 2), ?_, ?_⟩
  · have hlog : 0 ≤ Real.log (1+a) := Real.log_nonneg (by linarith)
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  · intro delta hdelta
    obtain ⟨T, hT, hcard, hnet⟩ := exists_anchored_cube_test_net d hK hdelta
    exact ⟨T, hT, empirical_pattern_card_log_le T d ha hb hdelta hcard, hnet⟩

end Papers.TbsNeuralCausalPi

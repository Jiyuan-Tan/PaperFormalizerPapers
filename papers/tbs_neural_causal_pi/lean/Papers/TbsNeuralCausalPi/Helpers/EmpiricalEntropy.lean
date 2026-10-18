module
public import Papers.TbsNeuralCausalPi.Setup.CitedResults
/-! # Exponential forms of the empirical covering bounds

These estimates retain the range dependence when converting the square-root
cover into the logarithmic entropy in the uniform Wasserstein tail bound.
-/
public section
namespace Papers.TbsNeuralCausalPi
open scoped ENNReal

/-- If [b is positive](hyp:hb), [four times the d-th power of
e(v + 1)bᵛ, multiplied by exp(t), is at most
exp(log 4 + d + dv(1 + log b) + t)](goal). -/
-- @node: empirical_cover_prefactor_le_exp
lemma empirical_cover_prefactor_le_exp (d v : ℕ) {b t : ℝ} (hb : 0 < b) :
    4 * (ENNReal.ofReal ((Real.exp 1 * (v+1) * b^v)^d)) *
        ENNReal.ofReal (Real.exp t) ≤
      ENNReal.ofReal (Real.exp
        (Real.log 4 + d + d * v * (1 + Real.log b) + t)) := by
  have hv : (0 : ℝ) < v+1 := by positivity
  have hlog : Real.log ((v : ℝ)+1) ≤ v := by
    simpa using Real.log_le_sub_one_of_pos hv
  have hid : (4 : ℝ) * (Real.exp 1 * (v+1) * b^v)^d * Real.exp t =
      Real.exp (Real.log 4 + d * (1 + Real.log ((v : ℝ)+1) +
        v * Real.log b) + t) := by
    simp only [Real.exp_add, Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ) < 4),
      Real.exp_log hv, Real.exp_log hb, mul_pow]
  have hreal : (4 : ℝ) * (Real.exp 1 * (v+1) * b^v)^d * Real.exp t ≤
      Real.exp (Real.log 4 + d + d * v * (1 + Real.log b) + t) := by
    rw [hid]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg d : (0:ℝ) ≤ d)]
  have hnonneg : 0 ≤ (Real.exp 1 * ((v : ℝ)+1) * b^v)^d := by positivity
  simpa only [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4),
    ENNReal.ofReal_mul (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hnonneg),
    ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hreal

/-- If [a is nonnegative](hyp:ha) and [the tolerance ε is positive](hyp:heps),
[log(2 + a/ε²) is at most (2 + log(2 + a)/log 2) log(2 + 1/ε)](goal). -/
-- @node: empirical_inverse_square_log_le
lemma empirical_inverse_square_log_le {a eps : ℝ} (ha : 0 ≤ a) (heps : 0 < eps) :
    Real.log (2 + a / eps^2) ≤
      (2 + Real.log (2+a) / Real.log 2) * Real.log (2 + eps⁻¹) := by
  have hi : 0 ≤ eps⁻¹ := inv_nonneg.mpr heps.le
  have hB : 0 < 2+a := by linarith
  have hT : 0 < 2+eps⁻¹ := by positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogB : 0 ≤ Real.log (2+a) := Real.log_nonneg (by linarith)
  have hlogT : Real.log 2 ≤ Real.log (2+eps⁻¹) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hpoly : 2 + a / eps^2 ≤ (2+a) * (2+eps⁻¹)^2 := by
    have heq : a / eps^2 = a * (eps⁻¹)^2 := by ring
    rw [heq]
    calc
      _ ≤ (2+a) * (1+(eps⁻¹)^2) := by nlinarith [sq_nonneg (eps⁻¹)]
      _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith) hB.le
  have hlog := Real.log_le_log (by positivity : 0 < 2+a/eps^2) hpoly
  rw [Real.log_mul hB.ne' (pow_pos hT 2).ne', Real.log_pow] at hlog
  have habsorb : Real.log (2+a) ≤
      (Real.log (2+a) / Real.log 2) * Real.log (2+eps⁻¹) := by
    calc
      _ = (Real.log (2+a) / Real.log 2) * Real.log 2 := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hlogT (div_nonneg hlogB hlog2.le)
  nlinarith

/-- For [a positive range R](hyp:hR), [there exist positive constants C and c,
depending only on dimension d and R, such that for every sample size n,
integer v, real upper bound D on v, and positive ε, the product of four,
the d-th power of e(v + 1)(2 + 1024e/(ε/(2R))²)ᵛ, and
exp(−n(ε/(2R))²/32) is at most
exp(C(1 + D log(2 + 1/ε)) − cnε²)](goal). -/
-- @node: empirical_sqrt_cover_tail_constants
lemma empirical_sqrt_cover_tail_constants (d : ℕ) {R : ℝ} (hR : 0 < R) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (v n : ℕ) (dF eps : ℝ),
      (v : ℝ) ≤ dF → 0 < eps →
      4 * ENNReal.ofReal ((Real.exp 1 * (v+1) *
          (2 + 1024 * Real.exp 1 / (eps/(2*R))^2)^v)^d) *
          ENNReal.ofReal (Real.exp (-((eps/(2*R))^2 * n)/32)) ≤
        ENNReal.ofReal (Real.exp
          (C * (1 + dF * Real.log (2+eps⁻¹)) - c * n * eps^2)) := by
  let a := 4096 * Real.exp 1 * R^2
  let B := 2 + (1 + Real.log (2+a)) / Real.log 2
  let C := max (Real.log 4 + d) ((d : ℝ)*B) + 1
  let c := 1 / (128 * R^2)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogB : 0 ≤ Real.log (2+a) := Real.log_nonneg (by linarith)
  have hB : 0 < B := by dsimp [B]; positivity
  have hC0 : Real.log 4 + d ≤ C := by
    dsimp [C]
    exact (le_max_left _ _).trans (by linarith)
  have hC1 : (d : ℝ)*B ≤ C := by
    dsimp [C]
    exact (le_max_right _ _).trans (by linarith)
  have hC : 0 < C := lt_of_le_of_lt (by positivity : 0 ≤ (d : ℝ)*B)
    (lt_of_lt_of_le (by linarith : (d : ℝ)*B < (d : ℝ)*B+1)
      (by dsimp [C]; linarith [le_max_right (Real.log 4 + d) ((d : ℝ)*B)]))
  refine ⟨C, c, hC, by dsimp [c]; positivity, ?_⟩
  intro v n dF eps hv heps
  have hi : 0 ≤ eps⁻¹ := inv_nonneg.mpr heps.le
  have hL : 0 ≤ Real.log (2+eps⁻¹) := Real.log_nonneg (by linarith)
  have hlogT : Real.log 2 ≤ Real.log (2+eps⁻¹) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hunit : 1 ≤ Real.log (2+eps⁻¹) / Real.log 2 :=
    (le_div_iff₀ hlog2).mpr (by simpa using hlogT)
  have hlog := empirical_inverse_square_log_le ha heps
  have hentropy : 1 + Real.log (2+a/eps^2) ≤ B * Real.log (2+eps⁻¹) := by
    dsimp [B]
    calc
      _ ≤ Real.log (2+eps⁻¹) / Real.log 2 +
          (2 + Real.log (2+a) / Real.log 2) * Real.log (2+eps⁻¹) :=
        add_le_add hunit hlog
      _ = _ := by ring
  have hscale : 1024 * Real.exp 1 / (eps/(2*R))^2 = a / eps^2 := by
    dsimp [a]
    field_simp
    ring
  have hdecay : -((eps/(2*R))^2 * (n : ℝ))/32 = -c * n * eps^2 := by
    dsimp [c]
    field_simp
    ring
  have hbase : 0 < 2 + 1024 * Real.exp 1 / (eps/(2*R))^2 := by positivity
  refine (empirical_cover_prefactor_le_exp d v hbase).trans ?_
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  rw [hscale, hdecay]
  have hdF : 0 ≤ dF := (Nat.cast_nonneg v).trans hv
  have hterm : (d : ℝ)*v*(1+Real.log (2+a/eps^2)) ≤
      C * (dF * Real.log (2+eps⁻¹)) := by
    calc
      _ ≤ (d : ℝ)*v*(B * Real.log (2+eps⁻¹)) :=
        mul_le_mul_of_nonneg_left hentropy (by positivity)
      _ = ((d : ℝ)*B)*((v : ℝ)*Real.log (2+eps⁻¹)) := by ring
      _ ≤ C * (dF * Real.log (2+eps⁻¹)) :=
        mul_le_mul hC1 (mul_le_mul_of_nonneg_right hv hL)
          (by positivity) hC.le
  nlinarith

/-- For [nonnegative, possibly infinite weights p](hyp:p), if
[the logarithm of the finite index set's size is at most the entropy bound](hyp:hcard)
and [each weight on that set is at most the exponential of a common rate](hyp:hp),
[their sum is at most the exponential of the entropy bound plus that rate](goal). -/
-- @node: empirical_finite_sum_exp_le
lemma empirical_finite_sum_exp_le {I : Type*} (H : Finset I)
    (p : I → ℝ≥0∞) {entropy rate : ℝ}
    (hcard : Real.log (H.card : ℝ) ≤ entropy)
    (hp : ∀ i ∈ H, p i ≤ ENNReal.ofReal (Real.exp rate)) :
    ∑ i ∈ H, p i ≤ ENNReal.ofReal (Real.exp (entropy + rate)) := by
  have hcount : (H.card : ℝ) ≤ Real.exp entropy := by
    by_cases hz : H.card = 0
    · simp only [hz, Nat.cast_zero]
      exact (Real.exp_pos _).le
    · have hpos : (0 : ℝ) < H.card := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hz)
      calc
        _ = Real.exp (Real.log (H.card : ℝ)) := (Real.exp_log hpos).symm
        _ ≤ _ := Real.exp_le_exp.mpr hcard
  calc
    _ ≤ ∑ _i ∈ H, ENNReal.ofReal (Real.exp rate) := Finset.sum_le_sum hp
    _ = ENNReal.ofReal ((H.card : ℝ) * Real.exp rate) := by
      simp only [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
        ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (Real.exp entropy * Real.exp rate) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcount (Real.exp_pos _).le)
    _ = _ := by rw [Real.exp_add]

/-- If [C₀ is nonnegative](hyp:hC₀), [C₂ is nonnegative](hyp:hC₂),
[D is at least log 2](hyp:hD), and [E is nonnegative](hyp:hE),
[C₂D + C₀(1 + E) is at most (C₀ + C₂ + C₀/log 2)(D + E)](goal). -/
-- @node: empirical_entropy_constants_absorb
lemma empirical_entropy_constants_absorb {C₀ C₂ D E : ℝ}
    (hC₀ : 0 ≤ C₀) (hC₂ : 0 ≤ C₂) (hD : Real.log 2 ≤ D) (hE : 0 ≤ E) :
    C₂ * D + C₀ * (1+E) ≤
      (C₀ + C₂ + C₀ / Real.log 2) * (D+E) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD0 : 0 ≤ D := hlog.le.trans hD
  have hc : C₀ ≤ (C₀ / Real.log 2) * D := by
    calc
      _ = (C₀ / Real.log 2) * Real.log 2 := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hD (div_nonneg hC₀ hlog.le)
  nlinarith [mul_nonneg hC₀ hD0, mul_nonneg hC₂ hE,
    mul_nonneg (div_nonneg hC₀ hlog.le) hE]

end Papers.TbsNeuralCausalPi

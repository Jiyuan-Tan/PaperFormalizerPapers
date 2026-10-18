module
public import Papers.TbsNeuralCausalPi.Helpers.StructuralGluing
public import Papers.TbsNeuralCausalPi.Helpers.WideQuantization
public import Papers.TbsNeuralCausalPi.Helpers.ReLUDepthPadding
/-! # Fixed-depth structural approximation with exact Lipschitz control -/
public section
namespace Papers.TbsNeuralCausalPi
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
open scoped NNReal
/-- For [an input dimension](hyp:d) that is [at least one](hyp:hd),
[a positive constant depending only on that dimension exists such that every
function of positive output dimension with a given Lipschitz bound on the
unit cube admits a ReLU approximation at every width at least that constant,
with depth equal to the ceiling of the constant times one plus the logarithm
of the input dimension; the network retains the Lipschitz bound globally,
takes values in the convex hull of the target's unit-cube image, and has
one-norm error at most the constant times the Lipschitz bound times width
raised to minus the reciprocal of the input dimension](goal). -/
-- @node: relu_fixedDepth_lipschitz_approx
lemma relu_fixedDepth_lipschitz_approx (d : ℕ) (hd : 1 ≤ d) :
    ∃ c : ℝ, 0 < c ∧ ∀ (k : ℕ), 1 ≤ k → ∀ (L : ℝ≥0) (f : L1Vec d → L1Vec k),
      LipschitzOnWith L f (unitCube d) →
      ∀ W : ℕ, c ≤ W →
        ∃ q : ReLUNet d k W (⌈c * (1+Real.log d)⌉₊),
          LipschitzWith L q.eval ∧
          (∀ x, q.eval x ∈ convexHull ℝ (f '' unitCube d)) ∧
          ∀ x ∈ unitCube d, ‖q.eval x-f x‖ ≤ c * L * (W : ℝ) ^ (-(1:ℝ)/d) := by
  let B := 6 * ((d+1)*(d+1))
  let A := 2^d * B
  let depth := Nat.clog 2 ((d+1)*(d+1)) + 1 + 2
  let E : ℝ := 6 * d * (A : ℝ) ^ ((d : ℝ)⁻¹)
  let c : ℝ := (A * 2^d : ℕ) + d + depth + E + 1
  have hdpos : 0 < d := by omega
  have hA : 0 < A := by dsimp [A, B]; positivity
  have hE : 0 < E := by dsimp [E]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, ?_⟩
  intro k hk L f hf W hW
  have hthreshold : (A : ℝ) * (2 : ℝ)^d ≤ W := by
    have : ((A * 2^d : ℕ) : ℝ) ≤ c := by dsimp [c]; linarith [(show (0:ℝ) ≤ (A * 2^d : ℕ) from Nat.cast_nonneg _), (show (0:ℝ) ≤ d from Nat.cast_nonneg _), (show (0:ℝ) ≤ depth from Nat.cast_nonneg _)]
    exact (by exact_mod_cast this : (A : ℝ) * (2 : ℝ)^d ≤ c).trans hW
  let R := ⌊((W : ℝ) / A) ^ (d : ℝ)⁻¹⌋₊
  have hb := wide_refinement_budget hdpos (by exact_mod_cast hA) hthreshold
  have hR : 0 < R := by dsimp [R]; omega
  have hmesh : A * R^d ≤ W := by exact_mod_cast hb.2.1
  have hwidth : max ((R+1)^d * B) d ≤ W := by
    apply max_le
    · calc
        (R+1)^d * B ≤ (2*R)^d * B := by gcongr; omega
        _ = A * R^d := by dsimp [A]; rw [mul_pow]; ring
        _ ≤ W := hmesh
    · have : (d : ℝ) ≤ c := by dsimp [c]; linarith [(show (0:ℝ) ≤ (A * 2^d : ℕ) from Nat.cast_nonneg _), (show (0:ℝ) ≤ d from Nat.cast_nonneg _), (show (0:ℝ) ≤ depth from Nat.cast_nonneg _)]
      exact_mod_cast this.trans hW
  have hdepth : depth ≤ ⌈c * (1 + Real.log d)⌉₊ := by
    have hlog : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast hd)
    have hdc : (depth : ℝ) ≤ c := by dsimp [c]; linarith [(show (0:ℝ) ≤ (A * 2^d : ℕ) from Nat.cast_nonneg _), (show (0:ℝ) ≤ d from Nat.cast_nonneg _), (show (0:ℝ) ≤ depth from Nat.cast_nonneg _)]
    have hreal : (depth : ℝ) ≤ c * (1 + Real.log d) := hdc.trans (le_mul_of_one_le_right hc.le (by linarith))
    exact_mod_cast hreal.trans (Nat.le_ceil (c * (1 + Real.log d)))
  obtain ⟨q, hLip, hconv, herr⟩ := structural_lipschitz_approx_mesh d k R hR L f hf
  obtain ⟨Q, hQ⟩ := relu_pad_depth (q.widen hwidth)
    (by omega) hdepth
  refine ⟨Q, ?_, ?_, ?_⟩
  · rw [hQ, ReLUNet.widen_eval]
    exact hLip
  · rw [hQ, ReLUNet.widen_eval]
    exact hconv
  · intro x hx
    rw [hQ, ReLUNet.widen_eval]
    refine (herr x hx).trans ?_
    have hr := wide_refinement_error_rate hdpos (by exact_mod_cast hA) hthreshold
    have hr' : (d : ℝ) / R ≤ E * (W : ℝ)^(-(1:ℝ)/d) := by
      refine le_trans ?_ hr
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg R)
      nlinarith [(show (0:ℝ) ≤ d from Nat.cast_nonneg _)]
    have hEc : E ≤ c := by dsimp [c]; linarith [(show (0:ℝ) ≤ (A * 2^d : ℕ) from Nat.cast_nonneg _), (show (0:ℝ) ≤ d from Nat.cast_nonneg _), (show (0:ℝ) ≤ depth from Nat.cast_nonneg _)]
    calc
      (L : ℝ) * d / R = L * ((d : ℝ) / R) := by ring
      _ ≤ L * (E * (W : ℝ)^(-(1:ℝ)/d)) :=
        mul_le_mul_of_nonneg_left hr' L.coe_nonneg
      _ = E * (L * (W : ℝ)^(-(1:ℝ)/d)) := by ring
      _ ≤ c * (L * (W : ℝ)^(-(1:ℝ)/d)) :=
        mul_le_mul_of_nonneg_right hEc
          (mul_nonneg L.coe_nonneg (Real.rpow_nonneg (Nat.cast_nonneg W) _))
      _ = c * L * (W : ℝ)^(-(1:ℝ)/d) := by ring

end Papers.TbsNeuralCausalPi

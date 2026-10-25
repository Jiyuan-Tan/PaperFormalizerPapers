module
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVCalibrationBounds
/-! Final calibration transfer for the recursive RDIV event.

The preliminary event already controls the operator and pilot errors at the
same public nuisance scale. The remaining Bernstein comparison is transferred
locally, with a constant independent of confidence, horizon and source data.
-/
public section
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory
variable {W X Z Ω : Type*} [MeasurableSpace W] [MeasurableSpace X]
  [MeasurableSpace Z]

/-- Under [the RDIV model](hyp:hIV), [density realizability](hyp:hDensity),
[density bounds](hyp:hBounds), and [the hypothesis envelope B](hyp:hHyp), assume
[B is nonnegative](hyp:hB), [the selected density belongs to its class](hyp:hg),
[the density-rate constant](hyp:hCd) and [density radius](hyp:hg0) are nonnegative,
and [integrated squared Hellinger error is at most the rate constant times the
squared density radius](hyp:hRate). If [that radius is at most the base nuisance
scale](hyp:hbase), [the nuisance multiplier absorbs twice B times the square
root of the rate constant](hyp:hκ), and [the final nuisance scale is that
multiplier times the base scale](hyp:hν), then [the operator error is at most
the final nuisance scale uniformly over the hypothesis class](goal).

Absorb the density-to-operator constant in the existing calibration
multiplier. This uses the density rate at its actual confidence argument;
no comparison between different confidence-indexed curves is made. -/
-- @node: iter_rdiv_operator_rate_of_inflation
lemma iter_rdiv_operator_rate_of_inflation (V : IVWorld W X Z)
    (mu : Measure X) (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (gHat : ℕ → Ω → X → Z → ℝ) (support : Set (X × Z))
    (B c₀ CG Cd g baseν κν ν : ℝ) (n : ℕ) (ω : Ω)
    (hIV : RDIVSetting V mu g₀) (hDensity : DensityRealizable V mu G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hHyp : HypothesisClassBounded V support B) (hB : 0 ≤ B)
    (hg : gHat n ω ∈ G) (hCd : 0 ≤ Cd) (hg0 : 0 ≤ g)
    (hRate : (∫ z, hellingerSqDensity mu (fun x => gHat n ω x z)
      (fun x => g₀ x z) ∂V.law.map V.zOf) ≤ Cd * g ^ 2)
    (hbase : g ≤ baseν) (hκ : 2 * B * Real.sqrt Cd ≤ κν)
    (hν : ν = κν * baseν) :
    ∀ h ∈ V.H, inputL2Norm (V.law.map V.zOf)
      (estimatedOperator V mu gHat n ω h - dualVersion V (projCondExpOp V h)) ≤ ν := by
  intro h hh
  have hrate := rdiv_estimated_operator_global_rate V mu G g₀ gHat support
    B c₀ CG Cd g n ω hIV hDensity hBounds hHyp hB hg hCd hg0 hRate h hh
  apply hrate.trans
  rw [hν]
  exact (mul_le_mul_of_nonneg_left hbase (by positivity)).trans
    (mul_le_mul_of_nonneg_right hκ (hg0.trans hbase))

/-- Under [the RDIV model](hyp:hIV), [the range condition](hyp:hRange),
[density realizability](hyp:hDensity), [density bounds](hyp:hBounds), [the
hypothesis envelope B](hyp:hHyp), [nonnegative B](hyp:hB), and [a nonnegative
residual comparison constant K](hyp:hK), [any class-valued density and candidate
with a square-integrable pilot, pilot and operator errors at most the nuisance
scale, and a residual squared-norm comparison at nonnegative radius at most
twice that scale has calibration error relative to the true projected squared
error at most (16 K + 9) times the nuisance scale times projected error plus
(16 K + 9) times the squared nuisance scale](goal).

Convert Bernstein's fitted-residual comparison to the true projected
error using the normalized pilot and density comparisons. This deterministic
step consumes no additional probability and applies to each fitted iterate. -/
-- @node: iter_rdiv_calibration_comparison_of_nuisance_bounds
lemma iter_rdiv_calibration_comparison_of_nuisance_bounds (V : IVWorld W X Z)
    (mu : Measure X) (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (gHat : ℕ → Ω → X → Z → ℝ) (rHat : ℕ → Ω → Z → ℝ)
    (support : Set (X × Z)) (B c₀ CG K : ℝ)
    (hIV : RDIVSetting V mu g₀) (hRange : RangeCondition V)
    (hDensity : DensityRealizable V mu G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hHyp : HypothesisClassBounded V support B) (hB : 0 ≤ B) (hK : 0 ≤ K) :
    ∀ (n : ℕ) (ω : Ω) (h : V.Hbar.toSubmodule) (D a ν : ℝ),
    gHat n ω ∈ G → h ∈ V.H → MemLp (rHat n ω) 2 (V.law.map V.zOf) →
    0 ≤ a → a ≤ 2 * ν →
    inputL2Norm (V.law.map V.zOf)
      (rHat n ω - dualVersion V (momentRepresenter V)) ≤ ν →
    inputL2Norm (V.law.map V.zOf)
      (estimatedOperator V mu gHat n ω h - dualVersion V (projCondExpOp V h)) ≤ ν →
    |D - inputL2Norm (V.law.map V.zOf)
      (rHat n ω - estimatedOperator V mu gHat n ω h) ^ 2| ≤
      K * (a * inputL2Norm (V.law.map V.zOf)
        (rHat n ω - estimatedOperator V mu gHat n ω h) + a ^ 2) →
    |D - ‖projCondExpOp V (h - minNormSolution V)‖ ^ 2| ≤
      (16 * K + 9) * ν * ‖projCondExpOp V (h - minNormSolution V)‖ +
        (16 * K + 9) * ν ^ 2 := by
  intro n ω h D a ν hg hh hr ha haν hpilot hop hBernstein
  let q := rHat n ω - estimatedOperator V mu gHat n ω h
  let u := dualVersion V (momentRepresenter V) - dualVersion V (projCondExpOp V h)
  have hq : MemLp q 2 (V.law.map V.zOf) := hr.sub
    (rdiv_density_operator_memLp V mu G g₀ (gHat n ω) support B c₀ CG
      hIV hDensity hBounds hHyp hB hg h hh)
  have hu : MemLp u 2 (V.law.map V.zOf) :=
    (rdiv_dual_input_memLp_norm V (momentRepresenter V)).1.sub
      (rdiv_dual_input_memLp_norm V (projCondExpOp V h)).1
  have hν : 0 ≤ ν := (Real.sqrt_nonneg _).trans hpilot
  have hpert : inputL2Norm (V.law.map V.zOf) (q - u) ≤ 2 * ν := by
    have heq : q - u =
        (rHat n ω - dualVersion V (momentRepresenter V)) -
          (estimatedOperator V mu gHat n ω h - dualVersion V (projCondExpOp V h)) := by
      dsimp [q, u]
      abel
    rw [heq]
    apply (rdiv_inputL2Norm_sub_le _ _ _
      (hr.sub (rdiv_dual_input_memLp_norm V (momentRepresenter V)).1)
      ((rdiv_density_operator_memLp V mu G g₀ (gHat n ω) support B c₀ CG
        hIV hDensity hBounds hHyp hB hg h hh).sub
          (rdiv_dual_input_memLp_norm V (projCondExpOp V h)).1)).trans
    change inputL2Norm (V.law.map V.zOf)
        (rHat n ω - dualVersion V (momentRepresenter V)) +
      inputL2Norm (V.law.map V.zOf)
        (estimatedOperator V mu gHat n ω h - dualVersion V (projCondExpOp V h)) ≤ 2 * ν
    linarith only [hpilot, hop]
  have hbern : |D - inputL2Norm (V.law.map V.zOf) q ^ 2| ≤
      (4 * K) * (ν * inputL2Norm (V.law.map V.zOf) q + ν ^ 2) := by
    apply hBernstein.trans
    have hq0 : 0 ≤ inputL2Norm (V.law.map V.zOf) q := Real.sqrt_nonneg _
    have hlin := mul_le_mul_of_nonneg_right haν hq0
    have hquad : a ^ 2 ≤ 4 * ν ^ 2 := by nlinarith only [ha, haν, hν]
    have hprod := mul_le_mul_of_nonneg_left (add_le_add hlin hquad) hK
    have hrest := mul_nonneg hK (mul_nonneg hν hq0)
    nlinarith only [hprod, hrest]
  have hb := rdiv_calibration_residual_transfer (V.law.map V.zOf) q u hq hu
    D ν ν (4 * K) 2 hν hν (by positivity) (by norm_num) le_rfl hpert hbern
  dsimp only [u] at hb
  rw [rdiv_true_residual_input_norm V hRange h] at hb
  apply hb.trans
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith only [hK]) hν) (norm_nonneg _)
  · exact mul_le_mul_of_nonneg_right (by nlinarith only [hK]) (sq_nonneg ν)

end Papers.TsAdaptiveEstimationInference

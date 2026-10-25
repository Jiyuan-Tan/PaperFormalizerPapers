module
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVFittingBounds
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVFittingEvent
/-! The localized fitting comparison with the preliminary density held fixed. -/
public section

namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory Filter

variable {𝒲 𝒳 𝒵 Ω : Type*} [MeasurableSpace 𝒲] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒵] [MeasurableSpace Ω]
  (V : IVWorld 𝒲 𝒳 𝒵) (P : Measure Ω) [IsProbabilityMeasure P]
  (sample : AnalysisSample V P) (split : SampleSplit)

/-- Assuming [localized Lipschitz vector concentration](hyp:hVector), [every
conditional-density IV model satisfying the range condition, minimum-norm
solution realizability, density realizability and bounds, outcome and
hypothesis bounds, measurable likelihood-maximizer selection, class
measurability, and coherent fitting-supremum versions admits a positive
constant with the following property: at every positive sample size,
confidence level between zero and one, and grid penalty in `(0, 2]`, any radius
above the confidence floor that bounds both input and density-transformed
critical radii gives, for almost every preliminary realization, a fitting
event of probability at least one minus the confidence level on which all
comparator-centered conditional-versus-empirical penalized-risk errors are
bounded by the constant times the radius times the transformed input L2
distance plus the radius times the Hilbert distance plus squared radius](goal). -/
lemma rdiv_frozen_fitting_primitive
    (hVector : LipschitzVectorLocalizedConcentration V P sample split) :
  ∀ (mu : Measure 𝒳) (G : Set (𝒳 → 𝒵 → ℝ)) (g₀ : 𝒳 → 𝒵 → ℝ)
    (gHat : ℕ → Ω → 𝒳 → 𝒵 → ℝ) (support : Set (𝒳 × 𝒵))
    (B c₀ CG ρ : ℝ),
    RDIVSetting V mu g₀ → RangeCondition V → H0MemHypothesisClass V →
    DensityRealizable V mu G g₀ → DensityBounds G g₀ support c₀ CG →
    OutcomeBounded V B → HypothesisClassBounded V support B →
    MLEMaximizerSelected V P sample split G gHat →
    RDIVClassesMeasurable V P sample split mu G g₀ gHat →
    RDIVFittingSupremumVersion V P sample split mu gHat ρ →
    ∃ C > 0, ∀ (n : ℕ) (ζ r lam : ℝ), 0 < n →
      ζ ∈ Set.Ioo (0 : ℝ) 1 → lam ∈ regGrid ρ n → lam ∈ Set.Ioc (0 : ℝ) 2 →
      confidenceFloor n ζ ≤ r →
      IsCriticalRadiusBound (V.law.map V.xOf) (primalVersion V '' V.H) n r →
      (∀ g ∈ G, IsCriticalRadiusBound (V.law.map V.zOf)
        (densityOperator mu g '' (primalVersion V '' V.H)) n r) →
      ∀ᵐ preliminary ∂P,
        1 - ζ ≤ P.real {ω | ∀ h ∈ V.H,
          |(conditionalRisk V mu gHat n preliminary lam h -
              conditionalRisk V mu gHat n preliminary lam (minNormSolution V)) -
            (empiricalRisk V P sample split mu (fun _ _ => gHat n preliminary) n ω lam h -
              empiricalRisk V P sample split mu (fun _ _ => gHat n preliminary) n ω lam
                (minNormSolution V))| ≤
          C * (r * inputL2Norm (V.law.map V.zOf)
            (densityOperator mu (gHat n preliminary)
              (primalVersion V h - primalVersion V (minNormSolution V))) +
            r * ‖h - minNormSolution V‖ + r ^ 2)} := by
  exact hVector inferInstance

/-- Assume [localized Lipschitz vector concentration](hyp:hVector), [a grid
ratio at least one half and less than one](hyp:hρ), [a failure budget between
zero and one](hyp:hξ), [the conditional-density IV setting](hyp:hIV), [the range
condition](hyp:hRange), [membership of the minimum-norm solution in the
hypothesis class](hyp:hRealizable), [density-class realizability](hyp:hDensity),
[common-support density bounds](hyp:hBounds), [outcomes bounded by B](hyp:hOutcome),
[a hypothesis envelope of size B](hyp:hHyp), [measurable likelihood-maximizer
selection](hyp:hMLE), [the RDIV class measurability conditions](hyp:hMeas),
[coherent measurable fitting-supremum versions at rational radii](hyp:hFittingVersion),
[bounds on the hypothesis critical radii](hyp:hRadius), and [the confidence
floor for both radii](hyp:hFloor). Then [there is a positive constant such that,
for every positive sample size and grid penalty, almost every preliminary
realization gives a fitting event of probability at least one minus one
quarter of grid confidence on which all conditional-versus-empirical
penalized-risk differences from the minimum-norm solution are bounded by the
constant times the hypothesis radius times Hilbert distance plus squared
radius, evaluating the radius at one quarter of grid confidence](goal). -/
-- @node: rdiv_frozen_fitting_comparison
lemma rdiv_frozen_fitting_comparison
    (μ : Measure 𝒳) (G : Set (𝒳 → 𝒵 → ℝ)) (g₀ : 𝒳 → 𝒵 → ℝ)
    (gHat : ℕ → Ω → 𝒳 → 𝒵 → ℝ) (support : Set (𝒳 × 𝒵))
    (B c₀ CG ρ ξ : ℝ) (δG δH : ℕ → ℝ → ℝ)
    (hVector : LipschitzVectorLocalizedConcentration V P sample split)
    (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1) (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1)
    (hIV : RDIVSetting V μ g₀) (hRange : RangeCondition V)
    (hRealizable : H0MemHypothesisClass V)
    (hDensity : DensityRealizable V μ G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hOutcome : OutcomeBounded V B) (hHyp : HypothesisClassBounded V support B)
    (hMLE : MLEMaximizerSelected V P sample split G gHat)
    (hMeas : RDIVClassesMeasurable V P sample split μ G g₀ gHat)
    (hFittingVersion : RDIVFittingSupremumVersion V P sample split μ gHat ρ)
    (hRadius : HypothesisCriticalRadiusBound V μ G δH ρ)
    (hFloor : RDIVRadiusFloor δG δH ρ) :
    ∃ C > 0, ∀ n : ℕ, 0 < n → ∀ lam ∈ regGrid ρ n,
      ∀ᵐ preliminary ∂P,
        1 - gridConfidence ρ ξ n / 4 ≤ P.real {ω | ∀ h ∈ V.H,
          |(conditionalRisk V μ gHat n preliminary lam h -
              conditionalRisk V μ gHat n preliminary lam (minNormSolution V)) -
            (empiricalRisk V P sample split μ (fun _ _ => gHat n preliminary) n ω lam h -
              empiricalRisk V P sample split μ (fun _ _ => gHat n preliminary) n ω lam
                (minNormSolution V))| ≤
          C * (δH n (gridConfidence ρ ξ n / 4) * ‖h - minNormSolution V‖ +
            δH n (gridConfidence ρ ξ n / 4) ^ 2)} := by
  obtain ⟨C₀, hC₀, hlocal⟩ :=
    rdiv_frozen_fitting_primitive V P sample split hVector μ G g₀ gHat support B c₀ CG ρ
    hIV hRange hRealizable hDensity hBounds hOutcome hHyp hMLE hMeas hFittingVersion
  obtain ⟨c, hc, hfloor⟩ := hFloor
  let K := max 1 c⁻¹
  have hK : 1 ≤ K := le_max_left _ _
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  let C₁ := C₀ * (Real.sqrt (CG / c₀) + 1)
  have hC₁ : 0 < C₁ := by dsimp [C₁]; positivity
  refine ⟨C₁ * K ^ 2, by positivity, ?_⟩
  intro n hn lam hlam
  have hquarter : ξ / 4 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [hξ.1, hξ.2]
  have heq : gridConfidence ρ (ξ / 4) n = gridConfidence ρ ξ n / 4 := by
    unfold gridConfidence
    ring
  have hη : gridConfidence ρ ξ n / 4 ∈ Set.Ioo (0 : ℝ) 1 := by
    have hk : (1 : ℝ) ≤ (terminalIndex ρ n + 1 : ℕ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
    have hx := hξ.1
    have hηle : gridConfidence ρ ξ n ≤ ξ := by
      unfold gridConfidence
      exact (div_le_iff₀ (by positivity)).2 (by nlinarith only [hk, hx])
    constructor
    · unfold gridConfidence
      positivity
    · linarith only [hηle, hξ.2]
  let r := δH n (gridConfidence ρ ξ n / 4)
  have hradius := hRadius n hn (ξ / 4) hquarter
  rw [heq] at hradius
  have hr : 0 < r := hradius.1.1
  have hfloor' : confidenceFloor n (gridConfidence ρ ξ n / 4) ≤ K * r := by
    have hf := (hfloor n hn (ξ / 4) hquarter).2
    rw [heq] at hf
    have hi : c⁻¹ * (c * confidenceFloor n (gridConfidence ρ ξ n / 4)) =
        confidenceFloor n (gridConfidence ρ ξ n / 4) := by field_simp
    calc
      _ = c⁻¹ * (c * confidenceFloor n (gridConfidence ρ ξ n / 4)) := hi.symm
      _ ≤ c⁻¹ * r := mul_le_mul_of_nonneg_left hf (inv_nonneg.mpr hc.le)
      _ ≤ K * r := mul_le_mul_of_nonneg_right (le_max_right _ _) hr.le
  have hdom : lam ∈ Set.Ioc (0 : ℝ) 2 := by
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hlam
    have hρpos : 0 < ρ := by linarith only [hρ.1]
    refine ⟨mul_pos (by norm_num) (pow_pos hρpos k), ?_⟩
    have hp := pow_le_pow_of_le_one hρpos.le hρ.2.le (Nat.zero_le k)
    simpa only [gridValue, pow_zero, mul_one] using
      mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 2)
  have hrr : r ≤ K * r := by nlinarith only [hK, hr]
  have hp := hlocal n (gridConfidence ρ ξ n / 4) (K * r) lam hn hη hlam hdom hfloor'
    (criticalRadiusBound_mono _ _ n _ _ hradius.1 hrr)
    (fun g hg => criticalRadiusBound_mono _ _ n _ _ (hradius.2 g hg) hrr)
  filter_upwards [hp, (hMLE n hn).1] with preliminary hpre hg
  apply hpre.trans
  apply measureReal_mono (h₂ := measure_ne_top P _)
  intro ω hω h hh
  have hb := rdiv_fitting_deviation_reduction V μ G g₀ (gHat n preliminary)
    support c₀ CG C₀ (K * r) _ hIV hDensity hBounds hg.1 hC₀.le
    (mul_nonneg hK0.le hr.le) h (minNormSolution V) (hω h hh)
  apply hb.trans
  change C₁ * (K * r * ‖h - minNormSolution V‖ + (K * r) ^ 2) ≤
    C₁ * K ^ 2 * (r * ‖h - minNormSolution V‖ + r ^ 2)
  have hKK : K ≤ K ^ 2 := by nlinarith only [hK]
  have hterm := mul_le_mul_of_nonneg_right hKK
    (mul_nonneg hr.le (norm_nonneg (h - minNormSolution V)))
  nlinarith only [mul_le_mul_of_nonneg_left hterm hC₁.le]

end Papers.TsAdaptiveEstimationInference

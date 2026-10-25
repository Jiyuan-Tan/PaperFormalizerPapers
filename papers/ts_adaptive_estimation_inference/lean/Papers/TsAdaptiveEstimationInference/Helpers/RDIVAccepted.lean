module
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVSetup
/-! Deterministic weak and strong RDIV errors on the common comparison event. -/
public section
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory
open scoped Topology
variable {𝒲 𝒳 𝒵 Ω : Type*} [MeasurableSpace 𝒲] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒵] [MeasurableSpace Ω]
  (V : IVWorld 𝒲 𝒳 𝒵) (P : Measure Ω)
  (sample : AnalysisSample V P) (split : SampleSplit)

/-- Assume [C is positive](hyp:hC), [the preliminary, fitting, and calibration
comparisons hold on E with constant C](hyp:hEvent), [the minimum-norm solution
belongs to the hypothesis class](hyp:hRealizable), [the density and hypothesis
radii are nonnegative](hyp:hG,hH), and [both radii are at most δ](hyp:hGδ,hHδ).
For [an outcome in E](hyp:hω), [a hypothesis in the class](hyp:hh), and
[a penalty on the regularization grid](hyp:hlam), [the absolute difference
between population and empirical excess risks is at most twice C times the
sum of δ times the distance to the minimum-norm solution and δ squared](goal). -/
-- @node: rdiv_population_empirical_comparison
lemma rdiv_population_empirical_comparison
    (mu : Measure 𝒳) (g₀ : 𝒳 → 𝒵 → ℝ)
    (gHat : ℕ → Ω → 𝒳 → 𝒵 → ℝ) (rHat : ℕ → Ω → 𝒵 → ℝ)
    (ρ ξ C δ : ℝ) (ν : ℕ → ℝ) (δG δH δr : ℕ → ℝ → ℝ)
    (candidate : ℕ → ℝ → Ω → V.Hbar.toSubmodule)
    (n : ℕ) (E : Set Ω) (hC : 0 < C)
    (hEvent : RDIVComparisonsOn V P sample split mu g₀ gHat rHat ρ ξ ν
      δG δH δr candidate n E C)
    (hRealizable : H0MemHypothesisClass V)
    (hG : 0 ≤ δG n (ξ / 4)) (hH : 0 ≤ δH n (gridConfidence ρ ξ n / 4))
    (hGδ : δG n (ξ / 4) ≤ δ) (hHδ : δH n (gridConfidence ρ ξ n / 4) ≤ δ)
    (ω : Ω) (hω : ω ∈ E) (h : V.Hbar.toSubmodule) (hh : h ∈ V.H)
    (lam : ℝ) (hlam : lam ∈ regGrid ρ n) :
    |(populationRisk V lam h - populationRisk V lam (minNormSolution V)) -
      (empiricalRisk V P sample split mu gHat n ω lam h -
        empiricalRisk V P sample split mu gHat n ω lam (minNormSolution V))| ≤
      (2 * C) * (δ * ‖h - minNormSolution V‖ + δ ^ 2) := by
  have hp := (hEvent ω hω).1.2.2.2.2.2 h hh (minNormSolution V) hRealizable
  have hf := (hEvent ω hω).2.1 lam hlam h hh
  have he : (populationRisk V lam h - populationRisk V lam (minNormSolution V)) -
      (empiricalRisk V P sample split mu gHat n ω lam h -
        empiricalRisk V P sample split mu gHat n ω lam (minNormSolution V)) =
      -((conditionalPopulationLoss V mu gHat n ω h -
          conditionalPopulationLoss V mu gHat n ω (minNormSolution V)) -
        (rdivPopulationLoss V h - rdivPopulationLoss V (minNormSolution V))) +
      ((conditionalRisk V mu gHat n ω lam h -
          conditionalRisk V mu gHat n ω lam (minNormSolution V)) -
        (empiricalRisk V P sample split mu gHat n ω lam h -
          empiricalRisk V P sample split mu gHat n ω lam (minNormSolution V))) := by
    unfold populationRisk conditionalRisk
    ring
  rw [he]
  have ht := abs_add_le
    (-((conditionalPopulationLoss V mu gHat n ω h -
      conditionalPopulationLoss V mu gHat n ω (minNormSolution V)) -
      (rdivPopulationLoss V h - rdivPopulationLoss V (minNormSolution V))))
    ((conditionalRisk V mu gHat n ω lam h -
      conditionalRisk V mu gHat n ω lam (minNormSolution V)) -
      (empiricalRisk V P sample split mu gHat n ω lam h -
        empiricalRisk V P sample split mu gHat n ω lam (minNormSolution V)))
  rw [abs_neg] at ht
  apply ht.trans
  apply (add_le_add hp hf).trans
  have hm : C * δG n (ξ / 4) * ‖h - minNormSolution V‖ +
      C * (δH n (gridConfidence ρ ξ n / 4) * ‖h - minNormSolution V‖ +
        δH n (gridConfidence ρ ξ n / 4) ^ 2) ≤
      C * δ * ‖h - minNormSolution V‖ + C * (δ * ‖h - minNormSolution V‖ + δ ^ 2) := by
    gcongr
  exact hm.trans (by nlinarith only [mul_nonneg hC.le (sq_nonneg δ)])

/-- Assume [the grid ratio is at least one half and less than one](hyp:hρ),
[the comparison constant is positive](hyp:hCevent), [the RDIV model conditions
hold](hyp:hIV), [the moment representer lies in the operator range](hyp:hRange),
[the source condition holds with exponent β and witness w₀](hyp:hSource),
[the minimum-norm solution belongs to the hypothesis class](hyp:hRealizable),
[the outcome is bounded by B](hyp:hOutcome), and [the candidates attain the
empirical minima](hyp:hMinima). If [the density and hypothesis radii are
nonnegative at every positive sample size](hyp:hG,hH) and [both are bounded by
δ at every positive sample size](hyp:hGδ,hHδ), [there is a positive constant
uniform over positive sample sizes, comparison events, outcomes in those events,
and grid penalties, such that squared projected error is bounded by that
constant times the calibration statistic plus noise, and squared solution error
is bounded by that constant times stability plus the same statistic-and-noise
sum raised to the source interpolation exponent](goal). -/
-- @node: rdiv_accepted_bounds_local
lemma rdiv_accepted_bounds_local
    (mu : Measure 𝒳) (g₀ : 𝒳 → 𝒵 → ℝ)
    (gHat : ℕ → Ω → 𝒳 → 𝒵 → ℝ) (rHat : ℕ → Ω → 𝒵 → ℝ)
    (ρ ξ B β Cevent : ℝ) (δ ν : ℕ → ℝ) (δG δH δr : ℕ → ℝ → ℝ)
    (w₀ : V.Hbar.toSubmodule) (candidate : ℕ → ℝ → Ω → V.Hbar.toSubmodule)
    (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1) (hCevent : 0 < Cevent)
    (hIV : RDIVSetting V mu g₀) (hRange : RangeCondition V)
    (hSource : BetaSourceCondition V β w₀) (hRealizable : H0MemHypothesisClass V)
    (hOutcome : OutcomeBounded V B)
    (hMinima : RDIVMinimaAttained V P sample split mu gHat ρ candidate)
    (hG : ∀ n, 0 < n → 0 ≤ δG n (ξ / 4))
    (hH : ∀ n, 0 < n → 0 ≤ δH n (gridConfidence ρ ξ n / 4))
    (hGδ : ∀ n, 0 < n → δG n (ξ / 4) ≤ δ n)
    (hHδ : ∀ n, 0 < n → δH n (gridConfidence ρ ξ n / 4) ≤ δ n) :
    ∃ C > 0, ∀ n : ℕ, 0 < n → ∀ E : Set Ω,
      RDIVComparisonsOn V P sample split mu g₀ gHat rHat ρ ξ ν δG δH δr candidate n E Cevent →
      ∀ ω ∈ E, ∀ lam ∈ regGrid ρ n,
        ‖projCondExpOp V (candidate n lam ω - minNormSolution V)‖ ^ 2 ≤
          C * (rdivCalibrationStat V P sample split mu gHat rHat n ω (candidate n lam ω) +
            rdivNoiseLevel (δ n) (ν n) lam) ∧
        ‖candidate n lam ω - minNormSolution V‖ ^ 2 ≤ C * (rdivStability (δ n) lam +
          (rdivCalibrationStat V P sample split mu gHat rHat n ω (candidate n lam ω) +
            rdivNoiseLevel (δ n) (ν n) lam) ^ interpolationExponent β) := by
  obtain ⟨Cs, hCs, hsource⟩ := (variational_source V β w₀ hSource).2
    (1 / 4) (by norm_num)
  let Ce := 2 * Cevent
  let K := 2 + Cevent ^ 2 + 2 * Cevent
  let S := Cs * ‖w₀‖ ^ (2 / (1 + truncatedSource β))
  let A := 2 * Ce ^ 2 + 4 * Ce
  let C := K + A + 2 * S * K ^ interpolationExponent β + 1
  have hCe : 0 < Ce := by dsimp [Ce]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have ha : 0 ≤ interpolationExponent β := by
    unfold interpolationExponent truncatedSource
    positivity [hSource.1]
  refine ⟨C, hC, ?_⟩
  intro n hn E hEvent ω hω lam hlam
  have hlam0 : 0 < lam := by
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hlam
    exact mul_pos (by norm_num) (pow_pos (by linarith [hρ.1]) k)
  have hlam2 : lam ≤ 2 := by
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hlam
    have hp := pow_le_pow_of_le_one (by linarith [hρ.1] : 0 ≤ ρ) hρ.2.le (Nat.zero_le k)
    simpa [gridValue] using mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 2)
  let h := candidate n lam ω
  let u := h - minNormSolution V
  let U := ‖u‖
  let W := ‖projCondExpOp V u‖ ^ 2
  let D := rdivCalibrationStat V P sample split mu gHat rHat n ω h
  let Q := D + rdivNoiseLevel (δ n) (ν n) lam
  have hW : 0 ≤ W := sq_nonneg _
  have hD : 0 ≤ D := by
    dsimp [D, rdivCalibrationStat, blockAverage]
    positivity
  have hQ : 0 ≤ Q := by dsimp [Q, rdivNoiseLevel]; positivity
  have hc := (abs_le.mp ((hEvent ω hω).2.2 lam hlam)).1
  change -(Cevent * ν n * ‖projCondExpOp V u‖ + Cevent * ν n ^ 2) ≤ D - W at hc
  have hy : Cevent * ν n * ‖projCondExpOp V u‖ ≤
      W / 2 + Cevent ^ 2 * ν n ^ 2 / 2 := by
    change Cevent * ν n * ‖projCondExpOp V u‖ ≤
      ‖projCondExpOp V u‖ ^ 2 / 2 + Cevent ^ 2 * ν n ^ 2 / 2
    nlinarith only [sq_nonneg (‖projCondExpOp V u‖ - Cevent * ν n)]
  have hweak : W ≤ K * Q := by
    have hv : 0 ≤ δ n ^ 2 / lam := by positivity
    dsimp [K, Q, rdivNoiseLevel]
    nlinarith only [hc, hy, hD, hv, sq_nonneg (ν n), sq_nonneg Cevent,
      mul_nonneg hCevent.le (sq_nonneg (ν n)),
      mul_nonneg (sq_nonneg Cevent) hD, mul_nonneg hCevent.le hD,
      mul_nonneg (sq_nonneg Cevent) hv, mul_nonneg hCevent.le hv]
  have hh := ((hMinima n hn lam hlam).1 ω).1
  have hopt := ((hMinima n hn lam hlam).1 ω).2 (minNormSolution V) hRealizable
  have herr := (abs_le.mp (rdiv_population_empirical_comparison V P sample split
    mu g₀ gHat rHat ρ ξ Cevent (δ n) ν δG δH δr candidate n E hCevent hEvent
    hRealizable (hG n hn) (hH n hn) (hGδ n hn) (hHδ n hn) ω hω h hh lam hlam)).2
  have hnorm : ‖h‖ ^ 2 - ‖minNormSolution V‖ ^ 2 =
      U ^ 2 + 2 * inner ℝ (minNormSolution V) u := by
    have he : h = minNormSolution V + u := by dsimp [u]; abel
    conv_lhs => rw [he, norm_add_sq_real]
    dsimp [U]
    ring
  have hpop : populationRisk V lam h - populationRisk V lam (minNormSolution V) =
      W + lam * (U ^ 2 + 2 * inner ℝ (minNormSolution V) u) := by
    rw [populationRisk, populationRisk,
      rdivPopulationLoss_eq V mu g₀ hIV hRange B hOutcome h,
      rdivPopulationLoss_eq V mu g₀ hIV hRange B hOutcome (minNormSolution V)]
    simp only [sub_self, map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero]
    rw [show ‖projCondExpOp V (h - minNormSolution V)‖ ^ 2 = W from rfl]
    calc
      _ = W + lam * (‖h‖ ^ 2 - ‖minNormSolution V‖ ^ 2) := by ring
      _ = _ := by rw [hnorm]
  rw [hpop] at herr
  have hbasic : lam * U ^ 2 ≤ Ce * (δ n * U + δ n ^ 2) +
      2 * lam * |inner ℝ (minNormSolution V) u| := by
    have hi := mul_le_mul_of_nonneg_left (neg_abs_le (inner ℝ (minNormSolution V) u))
      (by positivity : 0 ≤ 2 * lam)
    change empiricalRisk V P sample split mu gHat n ω lam h ≤ _ at hopt
    change W + lam * (U ^ 2 + 2 * inner ℝ (minNormSolution V) u) - _ ≤
      Ce * (δ n * U + δ n ^ 2) at herr
    linarith only [herr, hopt, hi, hW]
  have hyoung : Ce * δ n * U ≤ lam / 4 * U ^ 2 + Ce ^ 2 * (δ n ^ 2 / lam) := by
    apply (mul_le_mul_iff_left₀ hlam0).mp
    have he : lam * (δ n ^ 2 / lam) = δ n ^ 2 := mul_div_cancel₀ _ hlam0.ne'
    nlinarith only [sq_nonneg (lam * U - 2 * Ce * δ n), he]
  have hs := (hsource u).2
  have he : ‖projCondExpOp V u‖ ^ (2 * truncatedSource β / (1 + truncatedSource β)) =
      W ^ interpolationExponent β := by
    dsimp [W]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    congr 1
    unfold interpolationExponent
    ring
  rw [he] at hs
  change 2 * |inner ℝ (minNormSolution V) u| ≤ (1 / 4 : ℝ) * U ^ 2 +
    S * W ^ interpolationExponent β at hs
  have hnoise : δ n ^ 2 ≤ 2 * (δ n ^ 2 / lam) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hlam0).2
    nlinarith only [mul_le_mul_of_nonneg_right hlam2 (sq_nonneg (δ n))]
  have hstrong : U ^ 2 ≤ A * rdivStability (δ n) lam + 2 * S * W ^ interpolationExponent β := by
    apply (mul_le_mul_iff_right₀ hlam0).mp
    have hs' := mul_le_mul_of_nonneg_left hs hlam0.le
    have hn' := mul_le_mul_of_nonneg_left hnoise hCe.le
    have he' : lam * rdivStability (δ n) lam = δ n ^ 2 / lam := by
      unfold rdivStability
      field_simp
    dsimp only [A]
    rw [mul_add, ← mul_assoc lam, mul_comm lam (2 * Ce ^ 2 + 4 * Ce),
      mul_assoc, he']
    nlinarith only [hbasic, hyoung, hs', hn']
  have hpower : W ^ interpolationExponent β ≤ K ^ interpolationExponent β *
      Q ^ interpolationExponent β := by
    rw [← Real.mul_rpow hK.le hQ]
    exact Real.rpow_le_rpow hW hweak ha
  have hKC : K ≤ C := by
    dsimp only [C]
    have : 0 ≤ 2 * S * K ^ interpolationExponent β := by positivity
    linarith
  have hAC : A ≤ C := by
    dsimp only [C]
    have : 0 ≤ 2 * S * K ^ interpolationExponent β := by positivity
    linarith
  have hSC : 2 * S * K ^ interpolationExponent β ≤ C := by
    dsimp only [C]
    linarith
  constructor
  · exact hweak.trans (mul_le_mul_of_nonneg_right hKC hQ)
  · change U ^ 2 ≤ C * (rdivStability (δ n) lam + Q ^ interpolationExponent β)
    calc
      _ ≤ A * rdivStability (δ n) lam + 2 * S * W ^ interpolationExponent β := hstrong
      _ ≤ C * rdivStability (δ n) lam + C * Q ^ interpolationExponent β := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right hAC (by unfold rdivStability; positivity)
        · calc
            _ ≤ 2 * S * (K ^ interpolationExponent β * Q ^ interpolationExponent β) :=
              mul_le_mul_of_nonneg_left hpower (by positivity)
            _ ≤ _ := by
              rw [← mul_assoc]
              exact mul_le_mul_of_nonneg_right hSC (Real.rpow_nonneg hQ _)
      _ = _ := by ring

end Papers.TsAdaptiveEstimationInference

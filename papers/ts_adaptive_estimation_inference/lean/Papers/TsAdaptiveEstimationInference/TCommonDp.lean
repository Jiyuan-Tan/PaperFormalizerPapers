module
public import Papers.TsAdaptiveEstimationInference.Helpers.Discrepancy
/-! TCommonDp for adaptive inverse problems. -/
public section
set_option linter.style.longLine false
namespace Papers.TsAdaptiveEstimationInference

open MeasureTheory
open scoped Topology
-- @node: thm:common-dp
/-- Under [the admissible discrepancy-comparison constants and exponents](hyp:hParameters),
[there is a positive constant such that, for a grid factor between one-half inclusive
and one exclusive and a positive sample size, whenever
the noise level is nonnegative, the stability region contains only
positive penalties at most two, the discrepancy controls both
prediction and estimation errors on the event, the grid segment
above the oracle penalty is stable, noise decreases along that
segment, and the oracle bias crosses below half the noise,
every outcome in the event admits acceptance, the search stops no later than
the oracle index, the selected penalty is at least the oracle penalty, and its
squared prediction and estimation errors are bounded respectively by a constant
times oracle noise and by a constant times the sum of oracle noise divided by
the oracle penalty and oracle noise to the interpolation exponent](goal). -/
theorem common_dp (CA CV Cb γ q : ℝ)
    (hParameters : GenericDPParameters CA CV Cb γ q) :
    ∃ C > 0, ∀ {Ω H Q : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [NormedAddCommGroup Q] [NormedSpace ℝ H] [NormedSpace ℝ Q]
    (P : Measure Ω) [IsProbabilityMeasure P] (T : H →L[ℝ] Q) (h₀ : H)
    (ρ ξ : ℝ) (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1)
    (n : ℕ) (hn : 0 < n) (S : Set ℝ) (E : Set Ω) (lamo : ℝ)
    (candidate : ℝ → Ω → H) (D : Ω → H → ℝ) (A : ℝ → ℝ)
    (hNoise : NoiseLevelNonneg ρ n A) (hStability : StabilityRegionSubset S)
    (hComparisons : GenericEventComparisons P T h₀ ρ ξ CA CV Cb γ q n S E candidate D A)
    (hSegment : OracleSegmentStable ρ n S lamo)
    (hMonotone : NoiseLevelAntitoneOnSegment ρ n A lamo)
    (hCrossing : OracleCrossing A Cb q lamo),
    ∀ ω ∈ E,
      Accepts ρ n (fun lam => D ω (candidate lam ω)) A ∧
      (∃ kOracle ≤ terminalIndex ρ n, lamo = gridValue ρ kOracle ∧
        discrepancyIndex ρ n (fun lam => D ω (candidate lam ω)) A ≤ kOracle) ∧
      lamo ≤ selectedPenalty ρ n (fun lam => D ω (candidate lam ω)) A ∧
      ‖T (candidate (selectedPenalty ρ n (fun lam => D ω (candidate lam ω)) A) ω - h₀)‖ ^ 2 ≤
        C * A lamo ∧
      ‖candidate (selectedPenalty ρ n (fun lam => D ω (candidate lam ω)) A) ω - h₀‖ ^ 2 ≤
        C * (A lamo / lamo + A lamo ^ γ) := by
  classical
  rcases hParameters with ⟨hCA, hCV, hCb, hγ, hq⟩
  let K : ℝ := 5 / 2
  let C : ℝ := max (CA * K) (CV * (K + K ^ γ))
  have hK : 0 < K := by norm_num [K]
  have hC : 0 < C := lt_of_lt_of_le (mul_pos hCA hK) (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro Ω H Q _ _ _ _ _ P _ T h₀ ρ ξ hρ n hn S E lamo candidate D A
    hNoise hStability hComparisons hSegment hMonotone hCrossing ω hω
  have hρpos : 0 < ρ := by linarith [hρ.1]
  have hgrid : ∀ k, 0 < gridValue ρ k ∧ gridValue ρ k ≤ 2 := by
    intro k
    constructor
    · exact mul_pos (by norm_num) (pow_pos hρpos k)
    · have hp := pow_le_pow_of_le_one hρpos.le hρ.2.le (Nat.zero_le k)
      simpa [gridValue] using mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 2)
  have hoGrid := hSegment.1
  have ho2 : lamo ≤ 2 := by
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hoGrid
    rw [← hk]
    exact (hgrid k).2
  have hoS : lamo ∈ S := hSegment.2 ⟨hoGrid, le_rfl, ho2⟩
  have hopos := (hStability hoS).1
  have hoComp := hComparisons.2.2 ω hω lamo hoGrid hoS
  have hoAccept : D ω (candidate lamo ω) ≤ 3 / 2 * A lamo := by
    have hc := hCrossing
    dsimp [OracleCrossing] at hc
    linarith [hoComp.1]
  obtain ⟨ko, hko, heq⟩ := Finset.mem_image.mp hoGrid
  have hko' : ko ≤ terminalIndex ρ n := by simpa using Finset.mem_range.mp hko
  let d : ℝ → ℝ := fun lam => D ω (candidate lam ω)
  have he : ∃ k, k ≤ terminalIndex ρ n ∧ d (gridValue ρ k) ≤ 3 / 2 * A (gridValue ρ k) :=
    ⟨ko, hko', by simpa [d, heq] using hoAccept⟩
  have hi : discrepancyIndex ρ n d A = Nat.find he := by
    simp [discrepancyIndex, he]
  have hiBound : discrepancyIndex ρ n d A ≤ ko := by
    rw [hi]
    exact Nat.find_min' he ⟨hko', by simpa [d, heq] using hoAccept⟩
  have hiSpec : discrepancyIndex ρ n d A ≤ terminalIndex ρ n ∧
      d (gridValue ρ (discrepancyIndex ρ n d A)) ≤
        3 / 2 * A (gridValue ρ (discrepancyIndex ρ n d A)) := by
    rw [hi]
    exact Nat.find_spec he
  let lam := selectedPenalty ρ n d A
  have hlamGrid : lam ∈ regGrid ρ n := by
    exact Finset.mem_image.mpr ⟨discrepancyIndex ρ n d A,
      Finset.mem_range.mpr (Nat.lt_succ_of_le hiSpec.1), rfl⟩
  have hlamo : lamo ≤ lam := by
    rw [← heq]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one hρpos.le hρ.2.le hiBound) (by norm_num)
  have hlam2 : lam ≤ 2 := (hgrid _).2
  have hlamS : lam ∈ S := hSegment.2 ⟨hlamGrid, hlamo, hlam2⟩
  have hlampos : 0 < lam := (hStability hlamS).1
  have hmono : A lam ≤ A lamo :=
    hMonotone ⟨hoGrid, le_rfl, ho2⟩ ⟨hlamGrid, hlamo, hlam2⟩ hlamo
  have hAo : 0 ≤ A lamo := hNoise lamo hoGrid
  have hAl : 0 ≤ A lam := hNoise lam hlamGrid
  have hcomp := hComparisons.2.2 ω hω lam hlamGrid hlamS
  have hsum : D ω (candidate lam ω) + A lam ≤ K * A lamo := by
    have ha : D ω (candidate lam ω) ≤ 3 / 2 * A lam := hiSpec.2
    dsimp [K]
    linarith
  have hsumNonneg : 0 ≤ D ω (candidate lam ω) + A lam := by
    have hz := sq_nonneg ‖T (candidate lam ω - h₀)‖
    nlinarith [hcomp.2.1]
  have hdiv : (D ω (candidate lam ω) + A lam) / lam ≤ K * (A lamo / lamo) := by
    calc
      _ ≤ (K * A lamo) / lam := div_le_div_of_nonneg_right hsum hlampos.le
      _ ≤ (K * A lamo) / lamo :=
        div_le_div_of_nonneg_left (mul_nonneg hK.le hAo) hopos hlamo
      _ = _ := by ring
  have hpow : (D ω (candidate lam ω) + A lam) ^ γ ≤ K ^ γ * A lamo ^ γ := by
    calc
      _ ≤ (K * A lamo) ^ γ := Real.rpow_le_rpow hsumNonneg hsum hγ.1.le
      _ = _ := Real.mul_rpow hK.le hAo
  refine ⟨he, ⟨ko, hko', heq.symm, hiBound⟩, hlamo, ?_, ?_⟩
  · calc
      _ ≤ CA * (D ω (candidate lam ω) + A lam) := hcomp.2.1
      _ ≤ CA * (K * A lamo) := mul_le_mul_of_nonneg_left hsum hCA.le
      _ ≤ C * A lamo := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) hAo
  · have hratio : 0 ≤ A lamo / lamo := div_nonneg hAo hopos.le
    have hpower : 0 ≤ A lamo ^ γ := Real.rpow_nonneg hAo _
    have hKpow : 0 ≤ K ^ γ := Real.rpow_nonneg hK.le _
    calc
      _ ≤ CV * ((D ω (candidate lam ω) + A lam) / lam +
          (D ω (candidate lam ω) + A lam) ^ γ) := hcomp.2.2
      _ ≤ CV * (K * (A lamo / lamo) + K ^ γ * A lamo ^ γ) :=
        mul_le_mul_of_nonneg_left (add_le_add hdiv hpow) hCV.le
      _ ≤ (CV * (K + K ^ γ)) * (A lamo / lamo + A lamo ^ γ) := by
        nlinarith [mul_nonneg (mul_nonneg hCV.le hK.le) hpower,
          mul_nonneg (mul_nonneg hCV.le hKpow) hratio]
      _ ≤ C * (A lamo / lamo + A lamo ^ γ) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (add_nonneg hratio hpower)

end Papers.TsAdaptiveEstimationInference

module

public import Papers.OaiLinearVarianceRandom.TMain
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Central survival-level windows have square-root width -/

@[expose] public section

noncomputable section
namespace Papers.OaiLinearVarianceRandom
open MeasureTheory ProbabilityTheory
set_option linter.unusedVariables false

/-- For [a real variance-bound constant](hyp:C), [a variable count](hyp:n),
[a real tail level](hyp:η) [strictly between zero and one half](hyp:hη),
[the window deviation radius](goal) is the square root of twice the constant
times the variable count divided by the tail level. -/
def windowRadius (C : ℝ) (n : ℕ) (η : ℝ) (hη : WindowEta η) : ℝ :=
  Real.sqrt (2 * C * n / η) -- @realizes t(deviation radius sqrt of two C n divided by eta)

/-- Assuming [Wilson's separation property for survival levels](hyp:hWilson_of_gate),
[for every fixed tail level strictly between zero and one half there are
positive lower and upper constants and a variable-count threshold such that,
above that threshold and with at least three variables, every independent
uniform measurable clause process has its gap between the survival-level
locations at that level and its complement bounded below and above by those
constants times the square root of the variable count](goal). -/
-- @node: thm:window
theorem levelLocation_window_theta_sqrt (hWilson_of_gate : WilsonSeparation) :
    ∀ η : ℝ, WindowEta η →
      ∃ c1 : ℝ, 0 < c1 ∧ ∃ c2 : ℝ, 0 < c2 ∧ ∃ N : ℕ,
        ∀ n : ℕ, N ≤ n → MainN n →
        ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (Cseq : ℕ → Ω → ProperClause n), IsUniformClauseProcess μ Cseq →
          let H := fun ω => hittingTime (fun j => Cseq j ω)
          c1 * Real.sqrt n ≤ (levelLocation μ H η : ℝ) - (levelLocation μ H (1 - η) : ℝ) ∧
          (levelLocation μ H η : ℝ) - (levelLocation μ H (1 - η) : ℝ) ≤ c2 * Real.sqrt n := by
  intro η hη
  obtain ⟨hη0, hηhalf⟩ := hη
  obtain ⟨a, ha, N, hN⟩ := hWilson_of_gate (1 - η) η
    ⟨hη0, by linarith, by linarith⟩
  obtain ⟨C, hC⟩ := (var_hittingTime_theta_n hWilson_of_gate).1
  let B := max C 1
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right C 1)
  let A := Real.sqrt (2 * B / η)
  have hA : 0 < A := Real.sqrt_pos.2 (by positivity)
  have hAsq : A ^ 2 = 2 * B / η := Real.sq_sqrt (by positivity)
  obtain ⟨M, hM⟩ := exists_nat_ge ((2 / a) ^ 2)
  refine ⟨a / 2, half_pos ha, 2 * A + 1, by positivity, max N (max M 1), ?_⟩
  intro n hn hmain Ω _ μ _ Cseq hlaw
  let H := fun ω => hittingTime (fun j => Cseq j ω)
  let X := fun ω => (H ω : ℝ)
  let lo := levelLocation μ H (1 - η)
  let hi := levelLocation μ H η
  have hlo := levelLocation_pos_and_spec hmain μ Cseq hlaw (1 - η)
    ⟨by linarith, by linarith⟩
  have hhi := levelLocation_pos_and_spec hmain μ Cseq hlaw η
    ⟨hη0, by linarith⟩
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hnM : M ≤ n := (le_max_left M 1).trans ((le_max_right _ _).trans hn)
  have hn1 : 1 ≤ n := (le_max_right M 1).trans ((le_max_right _ _).trans hn)
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt n := by
    apply Real.le_sqrt_of_sq_le
    exact_mod_cast hn1
  constructor
  · have hprev : 1 - η < survivalFn μ H (lo - 1) :=
      hlo.2.2 (lo - 1) (Nat.sub_lt hlo.1 (by norm_num))
    have hsep := hN n hnN hmain Ω μ Cseq hlaw
      ((lo - 1 : ℕ) : ℤ) (hi : ℤ) (by
        simpa only [WilsonEndpoints, survivalFnInt, Int.natCast_nonneg, not_lt_of_ge,
          if_false, Nat.cast_lt, survivalFn] using And.intro hprev.le hhi.2.1)
    have hradius : 2 / a ≤ Real.sqrt n := Real.le_sqrt_of_sq_le
      (hM.trans (by exact_mod_cast hnM))
    have htwo : 2 ≤ a * Real.sqrt n := by
      have := (div_le_iff₀ ha).mp hradius
      simpa only [mul_comm] using this
    simp only [Int.cast_natCast] at hsep
    rw [Nat.cast_sub (show 1 ≤ lo from hlo.1), Nat.cast_one] at hsep
    change a / 2 * Real.sqrt n ≤ (hi : ℝ) - (lo : ℝ)
    nlinarith
  · let t := A * Real.sqrt n
    let av := ∫ ω, X ω ∂μ
    have ht : 0 < t := mul_pos hA (lt_of_lt_of_le zero_lt_one hsqrt1)
    have htsq : t ^ 2 = 2 * B * n / η := by
      dsimp [t]
      rw [mul_pow, hAsq, Real.sq_sqrt (Nat.cast_nonneg n)]
      ring
    have hX : MemLp X 2 μ := hittingTime_memLp_two hmain μ Cseq hlaw
    have hv : variance X μ ≤ B * n :=
      (hC n hmain Ω μ Cseq hlaw).trans
        (mul_le_mul_of_nonneg_right (le_max_left C 1) (Nat.cast_nonneg n))
    have hcheb : μ.real {ω | t ≤ |X ω - av|} ≤ η / 2 := by
      have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top
        (meas_ge_le_variance_div_sq hX ht)
      have hh' : μ.real {ω | t ≤ |X ω - av|} ≤ variance X μ / t ^ 2 := by
        simpa only [ENNReal.toReal_ofReal
          (div_nonneg (variance_nonneg X μ) (sq_nonneg _)), ← measureReal_def] using hh
      apply hh'.trans
      apply (div_le_iff₀ (sq_pos_of_pos ht)).2
      rw [htsq]
      have he : η / 2 * (2 * B * n / η) = B * n := by field_simp
      rwa [he]
    have hmH : Measurable H := measurable_hittingTime Cseq hlaw.1
    have hloav : av - t < (lo : ℝ) := by
      by_contra! hle
      have hmass : μ.real {ω | H ω ≤ lo} ≤ η / 2 := by
        apply (measureReal_mono ?_).trans hcheb
        intro ω hω
        have hx : X ω ≤ (lo : ℝ) := by
          change H ω ≤ lo at hω
          change (H ω : ℝ) ≤ (lo : ℝ)
          exact_mod_cast hω
        exact (by linarith : t ≤ -(X ω - av)).trans (neg_le_abs _)
      have hcomp := measureReal_compl (μ := μ) (hmH (measurableSet_Iic (a := lo)))
      have hs : survivalFn μ H lo = 1 - μ.real {ω | H ω ≤ lo} := by
        simp only [survivalFn]
        have he : {ω | lo < H ω} = {ω | H ω ≤ lo}ᶜ := by
          ext ω; simp
        rw [he]
        simpa only [Set.preimage, Set.mem_Iic, probReal_univ] using hcomp
      have hspec : survivalFn μ H lo ≤ 1 - η := hlo.2.1
      rw [hs] at hspec
      linarith
    let k : ℕ := ⌈av + t⌉₊
    have hsurv : survivalFn μ H k ≤ η := by
      have hmass : μ.real {ω | k < H ω} ≤ η / 2 := by
        apply (measureReal_mono ?_).trans hcheb
        intro ω hω
        have hx : (k : ℝ) < X ω := by
          change k < H ω at hω
          change (k : ℝ) < (H ω : ℝ)
          exact_mod_cast hω
        have hk : av + t ≤ (k : ℝ) := Nat.le_ceil _
        exact (by linarith : t ≤ X ω - av).trans (le_abs_self _)
      have hs : survivalFn μ H k = μ.real {ω | k < H ω} := by
        simp [survivalFn]
      rw [hs]
      linarith
    have hhik : hi ≤ k := Nat.sInf_le (s := {j : ℕ | survivalFn μ H j ≤ η}) hsurv
    have hav : 0 ≤ av := integral_nonneg (fun ω => Nat.cast_nonneg _)
    have hk : (k : ℝ) < av + t + 1 := Nat.ceil_lt_add_one (by linarith)
    have hhikR : (hi : ℝ) ≤ k := by exact_mod_cast hhik
    change (hi : ℝ) - (lo : ℝ) ≤ (2 * A + 1) * Real.sqrt n
    dsimp [t] at hloav hk
    nlinarith


end Papers.OaiLinearVarianceRandom

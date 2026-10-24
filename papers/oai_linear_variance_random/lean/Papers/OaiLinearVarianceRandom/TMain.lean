module

public import Papers.OaiLinearVarianceRandom.Helpers.Omission
public import Papers.OaiLinearVarianceRandom.Helpers.Moments
public import Papers.OaiLinearVarianceRandom.TDelay
public import Papers.OaiLinearVarianceRandom.Helpers.HittingMoments
public import Papers.OaiLinearVarianceRandom.Helpers.UpperVariance
public import Papers.OaiLinearVarianceRandom.Helpers.HittingTail

/-! # Linear variance of the first unsatisfiable prefix -/

public section

namespace Papers.OaiLinearVarianceRandom
open MeasureTheory ProbabilityTheory
set_option linter.unusedVariables false

/-- Assuming [Wilson's separation property for survival levels](hyp:hWilson_of_gate),
[there is a universal positive constant such that, for all sufficiently large
variable counts of at least three and every independent uniform measurable
clause process, the upper hitting-time quartile exceeds the lower quartile by
at least that constant times the square root of the variable count](goal). -/
-- @node: quartile_gap_of_gate
lemma quartile_gap_of_gate (hWilson_of_gate : WilsonSeparation) :
    ∃ c0 : ℝ, 0 < c0 ∧ -- @realizes c_0(positive absolute separation constant)
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → MainN n →
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (Cseq : ℕ → Ω → ProperClause n), IsUniformClauseProcess μ Cseq →
        c0 * Real.sqrt n ≤ (upperQuartile μ Cseq : ℝ) - (lowerQuartile μ Cseq : ℝ) := by
  obtain ⟨a, ha, N, hN⟩ := hWilson_of_gate (3 / 4) (1 / 4)
    (by norm_num [WilsonLevels])
  obtain ⟨M, hM⟩ := exists_nat_ge ((2 / a) ^ 2)
  refine ⟨a / 2, half_pos ha, max N M, ?_⟩
  intro n hn hmain Ω _ μ _ Cseq hlaw
  let H := fun ω => hittingTime (fun j => Cseq j ω)
  let lo := lowerQuartile μ Cseq
  let hi := upperQuartile μ Cseq
  have hlo := levelLocation_pos_and_spec hmain μ Cseq hlaw (3 / 4) (by norm_num)
  have hhi := levelLocation_pos_and_spec hmain μ Cseq hlaw (1 / 4) (by norm_num)
  have hlopos : 0 < lo := hlo.1
  have hprev : (3 / 4 : ℝ) < survivalFn μ H (lo - 1) :=
    hlo.2.2 (lo - 1) (Nat.sub_lt hlopos (by norm_num))
  have hnext : survivalFn μ H hi ≤ (1 / 4 : ℝ) := hhi.2.1
  have hsep := hN n ((le_max_left N M).trans hn) hmain Ω μ Cseq hlaw
    ((lo - 1 : ℕ) : ℤ) (hi : ℤ) (by
      simpa only [WilsonEndpoints, survivalFnInt, Int.natCast_nonneg, not_lt_of_ge,
        if_false, Nat.cast_lt, survivalFn] using And.intro hprev.le hnext)
  have hradius : 2 / a ≤ Real.sqrt n := Real.le_sqrt_of_sq_le
    (hM.trans (by exact_mod_cast ((le_max_right N M).trans hn)))
  have htwo : 2 ≤ a * Real.sqrt n := by
    have := (div_le_iff₀ ha).mp hradius
    simpa only [mul_comm] using this
  simp only [Int.cast_natCast] at hsep
  rw [Nat.cast_sub (by omega : 1 ≤ lo), Nat.cast_one] at hsep
  change a / 2 * Real.sqrt n ≤ (hi : ℝ) - (lo : ℝ)
  nlinarith

/-- Assuming [Wilson's separation property for survival levels](hyp:hWilson_of_gate),
[there are a universal positive constant and a deterministic real threshold
such that, for every variable count of at least three above that threshold and
every independent uniform measurable clause process, the hitting-time variance
is at least that constant times the variable count](goal). -/
-- @node: var_hittingTime_lower_linear
lemma var_hittingTime_lower_linear (hWilson_of_gate : WilsonSeparation) :
    ∃ c : ℝ, 0 < c ∧ ∃ n0 : ℝ,
      ∀ n : ℕ, n0 ≤ n → MainN n →
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (Cseq : ℕ → Ω → ProperClause n), IsUniformClauseProcess μ Cseq →
        c * n ≤ variance (fun ω => (hittingTime (fun j => Cseq j ω) : ℝ)) μ := by
  obtain ⟨c0, hc0, N, hgap⟩ := quartile_gap_of_gate hWilson_of_gate
  refine ⟨c0 ^ 2 / 16, by positivity, (N : ℝ), ?_⟩
  intro n hn hmain Ω _ μ _ Cseq hlaw
  have hnN : N ≤ n := by exact_mod_cast hn
  let H := fun ω => hittingTime (fun j => Cseq j ω)
  let X := fun ω => (H ω : ℝ)
  let a := lowerQuartile μ Cseq
  let b := upperQuartile μ Cseq
  have hsep : c0 * Real.sqrt n ≤ (b : ℝ) - (a : ℝ) :=
    hgap n hnN hmain Ω μ Cseq hlaw
  have hab : (a : ℝ) ≤ b := by
    have : 0 ≤ c0 * Real.sqrt n := mul_nonneg hc0.le (Real.sqrt_nonneg _)
    linarith
  have hmH : Measurable H := measurable_hittingTime Cseq hlaw.1
  have ha := (levelLocation_pos_and_spec hmain μ Cseq hlaw (3 / 4)
    (by norm_num)).2.1
  have hb := levelLocation_pos_and_spec hmain μ Cseq hlaw (1 / 4) (by norm_num)
  have hlow : (1 / 4 : ℝ) ≤ μ.real {ω | X ω ≤ (a : ℝ)} := by
    have he : {ω | X ω ≤ (a : ℝ)} = {ω | a < H ω}ᶜ := by
      ext ω
      simp [X]
    rw [he, measureReal_compl (measurableSet_lt measurable_const hmH)]
    have hs : survivalFn μ H a = μ.real {ω | a < H ω} := by
      simp [survivalFn]
    change survivalFn μ H a ≤ 3 / 4 at ha
    rw [hs] at ha
    simp only [probReal_univ]
    linarith
  have hhigh : (1 / 4 : ℝ) ≤ μ.real {ω | (b : ℝ) ≤ X ω} := by
    have hprev := hb.2.2 (b - 1) (Nat.sub_lt hb.1 (by omega : 0 < 1))
    have he : {ω | (b : ℝ) ≤ X ω} = {ω | b - 1 < H ω} := by
      ext ω
      have hbpos : 0 < b := hb.1
      simp only [Set.mem_setOf_eq, X, Nat.cast_le]
      omega
    rw [he]
    have hs : survivalFn μ H (b - 1) = μ.real {ω | b - 1 < H ω} := by
      simp [survivalFn]
    change (1 / 4 : ℝ) < survivalFn μ H (b - 1) at hprev
    exact le_of_lt (by simpa only [hs] using hprev)
  have hv := variance_lower_of_quarter_events μ X
    (hittingTime_memLp_two hmain μ Cseq hlaw) a b hab hlow hhigh
  have hsq : (c0 * Real.sqrt n) ^ 2 ≤ ((b : ℝ) - (a : ℝ)) ^ 2 := by
    exact pow_le_pow_left₀ (by positivity) hsep 2
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)] at hsq
  change c0 ^ 2 / 16 * (n : ℝ) ≤ variance X μ
  nlinarith

/-- Assuming [Wilson's separation property for survival levels](hyp:hWilson_of_gate),
[the hitting-time variance for independent uniform measurable clause processes
has a universal linear upper bound for every variable count of at least three,
and a universal positive linear lower bound for all sufficiently large variable
counts](goal). -/
-- @node: thm:main
theorem var_hittingTime_theta_n (hWilson_of_gate : WilsonSeparation) :
    (∃ C : ℝ, -- @realizes C(finite real bound chosen before n and world)
      ∀ n : ℕ, MainN n →
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (Cseq : ℕ → Ω → ProperClause n), IsUniformClauseProcess μ Cseq →
        variance (fun ω => (hittingTime (fun j => Cseq j ω) : ℝ)) μ ≤ C * n) ∧
    (∃ c : ℝ, 0 < c ∧ -- @realizes c(positive absolute lower-bound constant)
      ∃ n0 : ℝ, -- @realizes n_0(real deterministic threshold independent of n and world)
      ∀ n : ℕ, n0 ≤ n → MainN n →
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (Cseq : ℕ → Ω → ProperClause n), IsUniformClauseProcess μ Cseq →
        c * n ≤ variance (fun ω => (hittingTime (fun j => Cseq j ω) : ℝ)) μ) := by
  constructor
  · obtain ⟨B, hB, hcap⟩ := variance_cappedTime_linear
    obtain ⟨Q, hQ, herror⟩ := hittingTime_cap_error_bound
    refine ⟨2 * (B + 500) + 2 * Q, ?_⟩
    intro n hn Ω _ μ _ Cseq hlaw
    let H := fun ω => (hittingTime (fun j => Cseq j ω) : ℝ)
    let T := fun ω => (cappedTime (fun j => Cseq j ω) : ℝ)
    have hH : MemLp H 2 μ := hittingTime_memLp_two hn μ Cseq hlaw
    have hmT : Measurable T := by
      have hm := (measurable_hittingTime Cseq hlaw.1).min
        (measurable_const (a := capL n))
      exact (measurable_of_countable (fun k : ℕ => (k : ℝ))).comp hm
    have hT : MemLp T 2 μ := hH.mono' hmT.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
        dsimp [T, H, cappedTime]
        exact_mod_cast Nat.min_le_left (hittingTime (fun j => Cseq j ω)) (capL n)))
    have hc : variance T μ ≤ (B + 500) * n := by
      by_cases hn6 : OmissionN n
      · exact (hcap n hn6 Ω μ Cseq hlaw).trans
          (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg n))
      · have hn5 : (n : ℝ) ≤ 5 := by
          unfold OmissionN at hn6
          exact_mod_cast (by omega : n ≤ 5)
        have hpoint (ω : Ω) : T ω ^ 2 ≤ (10 * (n : ℝ)) ^ 2 := by
          apply pow_le_pow_left₀ (Nat.cast_nonneg _)
          dsimp [T, cappedTime]
          exact_mod_cast (show min (hittingTime (fun j => Cseq j ω)) (capL n) ≤ 10 * n
            from Nat.min_le_right _ _)
        have hi := integral_mono_ae hT.integrable_sq
          (integrable_const ((10 * (n : ℝ)) ^ 2))
          (Filter.Eventually.of_forall hpoint)
        simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hi
        have hv := variance_le_expectation_sq hT.aestronglyMeasurable
        simp only [Pi.pow_apply] at hv
        have hn0 := Nat.cast_nonneg (α := ℝ) n
        have hBn := mul_nonneg hB hn0
        nlinarith [mul_nonneg hn0 (sub_nonneg.mpr hn5)]
    have herr : (∫ ω, (H ω - T ω) ^ 2 ∂μ) ≤ Q := by
      convert herror n hn Ω μ Cseq hlaw using 1
      apply integral_congr_ae
      filter_upwards [] with ω
      dsimp [H, T, cappedTime]
      rw [← Nat.cast_sub (Nat.min_le_left _ _)]
      congr 2
      omega
    have hvar := variance_le_twice_comparison_error μ H T hH hT
    have hn1 : (1 : ℝ) ≤ n := by unfold MainN at hn; exact_mod_cast (by omega : 1 ≤ n)
    have hQn : Q ≤ Q * n := by nlinarith
    change variance H μ ≤ _
    nlinarith
  · exact var_hittingTime_lower_linear hWilson_of_gate

end Papers.OaiLinearVarianceRandom

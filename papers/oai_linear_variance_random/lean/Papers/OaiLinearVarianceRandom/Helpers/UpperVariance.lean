module

public import Papers.OaiLinearVarianceRandom.Helpers.Omission
public import Papers.OaiLinearVarianceRandom.Helpers.Moments
public import Papers.OaiLinearVarianceRandom.TDelay

/-! # Integrating the conditional delay estimate and the capped variance bound -/

public section

namespace Papers.OaiLinearVarianceRandom
open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {n : ℕ} {Ω : Type} [MeasurableSpace Ω]

/-- Suppose [A is nonnegative](hyp:hA), [there are at least six variables](hyp:hn),
[the clauses are measurable independent uniform draws](hyp:hlaw), and [the omitted
index lies between one and the cap](hyp:hi). If [under the fixed-clause measure,
the third incidence moment is at most A, the incidence moment of order three
halves restricted to at least one collision is at most A divided by n, and the
probability of at least two collisions is at most A divided by n squared](hyp:hmom),
then [the expected squared omission delay under that measure is at most A times
the sum of twice the squared occupation constant, twenty times that constant,
and one hundred](goal). -/
-- @node: integral_delay_sq_fixed_le
lemma integral_delay_sq_fixed_le (A : ℝ) (hA : 0 ≤ A)
    (hn : OmissionN n) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Cseq : ℕ → Ω → ProperClause n) (hlaw : IsUniformClauseProcess μ Cseq)
    (i : ℕ) (hi : DelayIndex i (capL n)) (c0 : ProperClause n)
    (hmom : (∫ ω, (incidenceParam c0 Cseq i ω : ℝ) ^ 3
        ∂fixedClauseMeasure μ Cseq i c0) ≤ A ∧
      (∫ ω, (incidenceParam c0 Cseq i ω : ℝ) ^ beta *
        (if 1 ≤ collisionCount c0 Cseq i ω then 1 else 0)
        ∂fixedClauseMeasure μ Cseq i c0) ≤ A / n ∧
      (fixedClauseMeasure μ Cseq i c0).real {ω | 2 ≤ collisionCount c0 Cseq i ω}
        ≤ A / (n : ℝ) ^ 2) :
    (∫ ω, (delay (fun j => Cseq j ω) i : ℝ) ^ 2
      ∂fixedClauseMeasure μ Cseq i c0) ≤
      (2 * occupationK ^ 2 + 20 * occupationK + 100) * A := by
  classical
  let ν := fixedClauseMeasure μ Cseq i c0
  let d := fun ω => (incidenceParam c0 Cseq i ω : ℝ)
  let V := collisionCount c0 Cseq i
  haveI : IsProbabilityMeasure ν := fixedClauseMeasure_isProbabilityMeasure μ Cseq hlaw i hi.1 c0
  have hint (f : ℕ → ℕ → ℝ) : Integrable
      (fun ω => f (incidenceParam c0 Cseq i ω) (V ω)) ν :=
    integrable_exposure_counts μ Cseq hlaw i hi.1 c0 f
  have h0 : Integrable (fun ω => d ω ^ 3) ν := hint (fun k _ => (k : ℝ) ^ 3)
  have h1 : Integrable (fun ω => d ω ^ beta * (if 1 ≤ V ω then 1 else 0)) ν :=
    hint (fun k v => (k : ℝ) ^ beta * (if 1 ≤ v then 1 else 0))
  have h2 : Integrable (fun ω => if 2 ≤ V ω then (1 : ℝ) else 0) ν :=
    hint (fun _ v => if 2 ≤ v then 1 else 0)
  have hbound := condExp_delay_sq_le hn μ Cseq hlaw i hi c0
  have hdom : ν[(fun ω => (delay (fun j => Cseq j ω) i : ℝ) ^ 2) |
      exposureSigma c0 Cseq i] ≤ᵐ[ν] fun ω =>
        2 * occupationK ^ 2 * d ω ^ 3 +
        (2 * occupationK * capL n) *
          (d ω ^ beta * (if 1 ≤ V ω then 1 else 0)) +
        (capL n : ℝ) ^ 2 * (if 2 ≤ V ω then 1 else 0) := by
    filter_upwards [hbound] with ω hω
    apply hω.trans
    dsimp [d, V]
    have hk : 0 ≤ occupationK := by norm_num [occupationK]
    have hd : 0 ≤ (incidenceParam c0 Cseq i ω : ℝ) := Nat.cast_nonneg _
    have hfirst : 2 * occupationK ^ 2 * (incidenceParam c0 Cseq i ω : ℝ) ^ 3 *
        (if collisionCount c0 Cseq i ω = 0 then 1 else 0) ≤
        2 * occupationK ^ 2 * (incidenceParam c0 Cseq i ω : ℝ) ^ 3 := by
      split_ifs <;> simp <;> positivity
    have hsecond : (if collisionCount c0 Cseq i ω = 1 then (1 : ℝ) else 0) ≤
        (if 1 ≤ collisionCount c0 Cseq i ω then 1 else 0) := by
      split_ifs <;> norm_num at * <;> omega
    have hsecond' := mul_le_mul_of_nonneg_left hsecond
      (show 0 ≤ 2 * occupationK * capL n *
        (incidenceParam c0 Cseq i ω : ℝ) ^ beta by positivity)
    nlinarith
  have h := integral_mono_ae integrable_condExp
    (((h0.const_mul _).add (h1.const_mul _)).add (h2.const_mul _)) hdom
  rw [integral_condExp (exposureSigma_le c0 Cseq hlaw.1 i)] at h
  simp only [Pi.add_apply] at h
  have hsum := integral_add ((h0.const_mul (2 * occupationK ^ 2)).add
    (h1.const_mul (2 * occupationK * capL n))) (h2.const_mul ((capL n : ℝ) ^ 2))
  simp only [Pi.add_apply] at hsum
  rw [hsum, integral_add (h0.const_mul (2 * occupationK ^ 2))
    (h1.const_mul (2 * occupationK * capL n))] at h
  simp only [integral_const_mul] at h
  have hevent : (∫ ω, (if 2 ≤ V ω then (1 : ℝ) else 0) ∂ν) =
      ν.real {ω | 2 ≤ V ω} := by
    have hm : MeasurableSet {ω | 2 ≤ V ω} := by
      have hc : Measurable V := by
        unfold V collisionCount
        have hs : Measurable (fun ω => ∑ j ∈ (Finset.Icc 1 (capL n)).erase i,
            if 2 ≤ (rootLiterals c0 (Cseq j ω)).card then (1 : ℕ) else 0) := by
          apply Finset.measurable_sum
          intro j hj
          exact (measurable_of_finite (fun c : ProperClause n =>
            if 2 ≤ (rootLiterals c0 c).card then (1 : ℕ) else 0)).comp
            (hlaw.1 j (Finset.mem_Icc.mp (Finset.mem_erase.mp hj).2).1)
        simpa only [Finset.sum_boole, Nat.cast_id] using hs
      exact measurableSet_le measurable_const hc
    rw [show (fun ω => if 2 ≤ V ω then (1 : ℝ) else 0) =
        {ω | 2 ≤ V ω}.indicator (fun _ => (1 : ℝ)) by ext ω; simp [Set.indicator_apply],
      integral_indicator hm, setIntegral_const, smul_eq_mul, mul_one]
  rw [hevent] at h
  have hnpos : (0 : ℝ) < n := by unfold OmissionN at hn; exact_mod_cast (by omega : 0 < n)
  have hL : (capL n : ℝ) = 10 * n := by simp [capL]
  have hb0 := mul_le_mul_of_nonneg_left hmom.1
    (show 0 ≤ 2 * occupationK ^ 2 by positivity)
  have hb1 := mul_le_mul_of_nonneg_left hmom.2.1
    (show 0 ≤ 2 * occupationK * capL n by norm_num [occupationK])
  have hb2 := mul_le_mul_of_nonneg_left hmom.2.2 (sq_nonneg (capL n : ℝ))
  change _ ≤ _ at h
  dsimp [d, V, ν] at h
  rw [hL] at hb1 hb2 h
  have hnne := ne_of_gt hnpos
  have he1 : (2 * occupationK * (10 * n)) * (A / n) = 20 * occupationK * A := by field_simp; ring
  have he2 : (10 * (n : ℝ)) ^ 2 * (A / (n : ℝ) ^ 2) = 100 * A := by field_simp; ring
  rw [he1] at hb1
  rw [he2] at hb2
  linarith

/-- If [every positively indexed clause is measurable](hyp:hC) and [a real
observable of the clause sequence depends only on the first ten times n clauses](hyp:hf),
then [that observable is integrable under any finite measure on outcomes](goal). -/
-- @node: integrable_capped_observable
lemma integrable_capped_observable (μ : Measure Ω) [IsFiniteMeasure μ]
    (Cseq : ℕ → Ω → ProperClause n)
    (hC : ∀ j, 1 ≤ j → Measurable (Cseq j)) (c0 : ProperClause n)
    (f : (ℕ → ProperClause n) → ℝ)
    (hf : ∀ c c', (∀ j ∈ Finset.Icc 1 (capL n), c j = c' j) → f c = f c') :
    Integrable (fun ω => f (fun j => Cseq j ω)) μ := by
  classical
  let J := Finset.Icc 1 (capL n)
  let X : Ω → (J → ProperClause n) := fun ω j => Cseq j ω
  let extend : (J → ProperClause n) → ℕ → ProperClause n :=
    fun cs j => if h : j ∈ J then cs ⟨j, h⟩ else c0
  have hm : Measurable X := by
    apply measurable_pi_lambda
    intro j
    exact hC j (Finset.mem_Icc.mp j.property).1
  have hint : Integrable (fun cs => f (extend cs)) (μ.map X) := Integrable.of_finite
  have h := (integrable_map_measure (measurable_of_finite
    (fun cs => f (extend cs))).aestronglyMeasurable hm.aemeasurable).mp hint
  apply h.congr
  filter_upwards [] with ω
  apply hf
  intro j hj
  change (if h : j ∈ J then X ω ⟨j, h⟩ else c0) = Cseq j ω
  rw [dif_pos hj]

/-- For [independent uniformly distributed measurable clauses](hyp:hlaw) and
[a positive omitted index](hyp:hi), if [a real observable is integrable under
every measure fixing the omitted clause](hyp:hf) and [its integral under each
such measure is at most B](hyp:hb), then [its unconditional integral is at most B](goal). -/
-- @node: integral_le_of_fixedClauseMeasure
lemma integral_le_of_fixedClauseMeasure (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Cseq : ℕ → Ω → ProperClause n) (hlaw : IsUniformClauseProcess μ Cseq)
    (i : ℕ) (hi : 1 ≤ i) (f : Ω → ℝ) (B : ℝ)
    (hf : ∀ c0, Integrable f (fixedClauseMeasure μ Cseq i c0))
    (hb : ∀ c0, (∫ ω, f ω ∂fixedClauseMeasure μ Cseq i c0) ≤ B) :
    (∫ ω, f ω ∂μ) ≤ B := by
  classical
  have heq := sum_meas_smul_cond_fiber (hlaw.1 i hi) μ
  change (∑ c0 : ProperClause n, μ {ω | Cseq i ω = c0} •
    fixedClauseMeasure μ Cseq i c0) = μ at heq
  have hiw (c0 : ProperClause n) : Integrable f
      (μ {ω | Cseq i ω = c0} • fixedClauseMeasure μ Cseq i c0) :=
    (hf c0).smul_measure (measure_ne_top μ _)
  have hiint := integral_finsetSum_measure (s := Finset.univ) (fun c0 _ => hiw c0)
  rw [heq] at hiint
  rw [hiint]
  simp only [integral_smul_measure, smul_eq_mul]
  calc
    _ ≤ ∑ c0 : ProperClause n, (μ {ω | Cseq i ω = c0}).toReal * B :=
      Finset.sum_le_sum (fun c0 _ => mul_le_mul_of_nonneg_left (hb c0) ENNReal.toReal_nonneg)
    _ = B := by
      rw [← Finset.sum_mul]
      have hm : ∑ c0 : ProperClause n, (μ {ω | Cseq i ω = c0}).toReal = 1 := by
        have hmass : ∑ c0 : ProperClause n, μ {ω | Cseq i ω = c0} = 1 := by
          simpa [Set.preimage] using (sum_measure_preimage_singleton (μ := μ) Finset.univ
            (fun c0 _ => (hlaw.1 i hi) (measurableSet_singleton c0)))
        rw [← ENNReal.toReal_sum (fun _ _ => measure_ne_top μ _), hmass]
        norm_num
      rw [hm, one_mul]

/-- [There is a universal nonnegative constant B such that, for every variable
count of at least six and every independent uniform measurable clause process,
the variance of the hitting time capped at ten times the variable count is at
most B times the variable count](goal). -/
-- @node: variance_cappedTime_linear
lemma variance_cappedTime_linear :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, OmissionN n →
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (Cseq : ℕ → Ω → ProperClause n), IsUniformClauseProcess μ Cseq →
      variance (fun ω => (cappedTime (fun j => Cseq j ω) : ℝ)) μ ≤ B * n := by
  obtain ⟨A, hA, hmom⟩ := incidence_moments_bound
  let D := (2 * occupationK ^ 2 + 20 * occupationK + 100) * A
  have hD : 0 ≤ D := by dsimp [D]; norm_num [occupationK]; positivity
  refine ⟨10 * D, by positivity, ?_⟩
  intro n hn Ω _ μ _ Cseq hlaw
  have henergy (i : ℕ) (hi : i ∈ Finset.Icc 1 (capL n)) :
      (∫ ω, (delay (fun j => Cseq j ω) i : ℝ) ^ 2 ∂μ) ≤ D := by
    have hi' : DelayIndex i (capL n) := Finset.mem_Icc.mp hi
    apply integral_le_of_fixedClauseMeasure μ Cseq hlaw i hi'.1
    · intro c0
      haveI := fixedClauseMeasure_isProbabilityMeasure μ Cseq hlaw i hi'.1 c0
      apply integrable_capped_observable _ Cseq hlaw.1 c0
        (fun c => (delay c i : ℝ) ^ 2)
      intro c c' heq
      simp only [delay, omittedCappedTime_congr c c' i (fun j hj _ => heq j hj),
        cappedTime_congr c c' heq]
    · intro c0
      exact integral_delay_sq_fixed_le A hA.le hn μ Cseq hlaw i hi' c0
        (hmom n hn i ⟨hn, hi'.1, hi'.2⟩ Ω μ Cseq hlaw c0)
  calc
    _ ≤ ∑ i ∈ Finset.Icc 1 (capL n),
        ∫ ω, (delay (fun j => Cseq j ω) i : ℝ) ^ 2 ∂μ :=
      variance_cappedTime_le_sum_delay_sq hn μ Cseq hlaw
    _ ≤ ∑ _i ∈ Finset.Icc 1 (capL n), D := Finset.sum_le_sum henergy
    _ = (10 * D) * n := by simp [capL]; ring

end Papers.OaiLinearVarianceRandom

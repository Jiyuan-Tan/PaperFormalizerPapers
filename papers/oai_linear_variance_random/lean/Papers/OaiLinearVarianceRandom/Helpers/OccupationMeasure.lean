module

public import Papers.OaiLinearVarianceRandom.Helpers.OccupationPaths

/-! # Measurability and integrability for the occupation estimate -/

public section

namespace Papers.OaiLinearVarianceRandom
open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {n : ℕ} {Ω : Type} [MeasurableSpace Ω]

/-- If [every positive-index clause observation is measurable](hyp:hC), then
[the information revealed by the root exposure is contained in the ambient
sigma-algebra](goal). -/
-- @node: exposureSigma_le
lemma exposureSigma_le (c0 : ProperClause n) (Cseq : ℕ → Ω → ProperClause n)
    (hC : ∀ j, 1 ≤ j → Measurable (Cseq j)) (i : ℕ) :
    exposureSigma c0 Cseq i ≤ ‹MeasurableSpace Ω› := by
  classical
  letI : MeasurableSpace (Finset (Fin n × Bool) × Option (ProperClause n)) := ⊤
  apply iSup_le
  intro j
  apply iSup_le
  intro hj
  exact ((measurable_of_finite (expose c0)).comp
    (hC j (Finset.mem_Icc.mp (Finset.mem_erase.mp hj).2).1)).comap_le

-- @node: ordinaryFiltration_le
/-- If [every positive-index clause observation is measurable](hyp:hC), then
[the information from the root exposure and the ordinary clause contents
through any given time is contained in the ambient sigma-algebra](goal). -/
lemma ordinaryFiltration_le (c0 : ProperClause n) (Cseq : ℕ → Ω → ProperClause n)
    (hC : ∀ j, 1 ≤ j → Measurable (Cseq j)) (i m : ℕ) :
    ordinaryFiltration c0 Cseq i m ≤ ‹MeasurableSpace Ω› := by
  classical
  apply sup_le (exposureSigma_le c0 Cseq hC i)
  apply iSup_le
  intro j
  apply iSup_le
  intro hj
  letI : MeasurableSpace (Option (ProperClause n)) := ⊤
  exact ((measurable_of_finite (ordinaryContents c0)).comp
    (hC j (Finset.mem_Icc.mp (Finset.mem_erase.mp hj).2).1)).comap_le

-- @node: testFiltration_le
/-- If [every positive-index clause observation is measurable](hyp:hC), then
[the information from the root exposure, ordinary clause contents, and test
contents through any given time is contained in the ambient sigma-algebra](goal). -/
lemma testFiltration_le (c0 : ProperClause n) (Cseq : ℕ → Ω → ProperClause n)
    (hC : ∀ j, 1 ≤ j → Measurable (Cseq j)) (i m : ℕ) :
    testFiltration c0 Cseq i m ≤ ‹MeasurableSpace Ω› := by
  classical
  apply sup_le (ordinaryFiltration_le c0 Cseq hC i m)
  apply iSup_le
  intro j
  apply iSup_le
  intro hj
  letI : MeasurableSpace (Option (Finset (Fin n × Bool))) := ⊤
  exact ((measurable_of_finite (testContents c0)).comp
    (hC j (Finset.mem_Icc.mp (Finset.mem_erase.mp hj).2).1)).comap_le

-- @node: occupationTerm_integrable
/-- If [there are at least six variables](hyp:hn), [every positive-index clause
observation is measurable](hyp:hC), and [the observation time lies between
the omitted index and the cap](hyp:hs), then [the occupation term at that
time is integrable under any finite measure](goal). -/
lemma occupationTerm_integrable (hn : OmissionN n) (μ : Measure Ω) [IsFiniteMeasure μ]
    (c0 : ProperClause n) (Cseq : ℕ → Ω → ProperClause n)
    (hC : ∀ j, 1 ≤ j → Measurable (Cseq j)) (i s : ℕ)
    (hs : i ≤ s ∧ s ≤ capL n) : Integrable (occupationTerm c0 Cseq i s) μ := by
  classical
  have hle := ordinaryFiltration_le c0 Cseq hC i s
  have hp := (killProcess_stronglyMeasurable c0 Cseq i s hs).mono hle
  have hS := (nonrootSolutions_measurable c0 Cseq i s hs).mono hle le_rfl
  have hnonempty : MeasurableSet {ω | (nonrootSolutions c0 Cseq i s ω).Nonempty} :=
    hS (t := {S | S.Nonempty}) (by trivial)
  apply Integrable.of_bound (f := occupationTerm c0 Cseq i s) (C := 1)
  · have hind : Measurable (fun ω => if (nonrootSolutions c0 Cseq i s ω).Nonempty
        then (1 : ℝ) else 0) := Measurable.ite hnonempty measurable_const measurable_const
    exact (hind.mul (hp.measurable.pow_const beta)).aestronglyMeasurable
  · filter_upwards [] with ω
    have hb := killProcess_bounds hn c0 Cseq i s ω
    have hp0 := Real.rpow_nonneg hb.1 beta
    have hp1 := Real.rpow_le_one (z := beta) hb.1 hb.2 (by norm_num [beta])
    simp only [occupationTerm]
    split_ifs <;> simp [Real.norm_eq_abs, abs_of_nonneg hp0, hp1]

end Papers.OaiLinearVarianceRandom

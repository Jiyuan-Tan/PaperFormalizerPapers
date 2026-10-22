module
public import Papers.TbsExtremeEffects.Helpers.ThresholdSampling

/-! Markov calibration of square envelopes for the two uniform threshold
processes. The envelope expectation is localized to the nuisance event; no
conditioning on a selected threshold is involved. -/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- If [the envelope is integrable](hyp:hInt), [nonnegative almost surely](hyp:hNonneg), [the confidence level is positive](hyp:hd), and [its mean is at most the budget](hyp:hMean), then [the chance that it exceeds six times that budget divided by the confidence level is at most one sixth of the confidence level](goal). -/
-- @node: square_envelope_failure_sixth
lemma square_envelope_failure_sixth {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (H : Ω → ℝ)
    (hInt : Integrable H P) (hNonneg : ∀ᵐ w ∂P, 0 ≤ H w)
    {K delta : ℝ} (hd : 0 < delta) (hMean : (∫ w, H w ∂P) ≤ K) :
    P.real {w | 6 * K / delta < H w} ≤ delta / 6 := by
  have hMarkov := score_sampling_markov P hInt hNonneg
    (delta := 2 * delta / 3) (by positivity)
  have hScale : 4 / (2 * delta / 3) = 6 / delta := by field_simp; ring
  rw [hScale] at hMarkov
  have hBudget : (2 * delta / 3) / 4 = delta / 6 := by ring
  rw [hBudget] at hMarkov
  apply (measureReal_mono (μ := P) (h₂ := measure_ne_top P _) ?_).trans hMarkov
  intro w hw
  have hThreshold : (6 / delta) * (∫ z, H z ∂P) ≤ 6 * K / delta := by
    calc
      _ ≤ (6 / delta) * K := mul_le_mul_of_nonneg_left hMean (by positivity)
      _ = _ := by ring
  exact hThreshold.trans_lt hw

/-- If [a square envelope dominates every indexed quantity on the good set](hyp:hDom), [the envelope cap is nonnegative](hyp:hR), [the observation is in that good set](hyp:hw), and [its envelope is below the cap](hyp:hH), then [every indexed quantity is bounded in absolute value by the square root of the cap](goal). -/
-- @node: uniform_abs_bound_of_square_envelope
lemma uniform_abs_bound_of_square_envelope {Ω ι : Type*}
    (A : ι → Ω → ℝ) (T : Set ι) (G : Set Ω) (H : Ω → ℝ)
    (hDom : ∀ w ∈ G, ∀ t ∈ T, A t w ^ 2 ≤ H w)
    {R : ℝ} (hR : 0 ≤ R) {w : Ω} (hw : w ∈ G) (hH : H w ≤ R) :
    ∀ t ∈ T, |A t w| ≤ Real.sqrt R := by
  intro t ht
  apply (Real.le_sqrt (abs_nonneg _) hR).mpr
  simpa only [sq_abs] using (hDom w hw t ht).trans hH

/-- If [the two envelopes are measurable](hyp:hMeas), [integrable](hyp:hInt), [nonnegative almost surely](hyp:hNonneg), [the confidence level is positive](hyp:hd), [the score-envelope mean has its budget](hyp:hScore), [the count-envelope mean has its budget](hyp:hCount), and [both envelopes dominate their threshold processes on the good set](hyp:hDom), then [there are measurable maximal events](goal) whose removals are small and on whose intersection both processes satisfy the displayed uniform bounds. -/
-- @node: threshold_maximal_events_of_square_envelopes
lemma threshold_maximal_events_of_square_envelopes
    {q d : ℕ} {M : ExtremeModel q d} (E : NeteExperiment M) (kind : EstimatorKind)
    (n : ℕ) (T : Set ℝ) (G : Set E.Om) (H : Fin 2 → E.Om → ℝ)
    (hMeas : ∀ i, Measurable (H i)) (hInt : ∀ i, Integrable (H i) E.P)
    (hNonneg : ∀ i, ∀ᵐ w ∂E.P, 0 ≤ H i w)
    {V pi delta : ℝ} (hd : 0 < delta)
    (hScore : ∫ w, H 0 w ∂E.P ≤ 8 * (n : ℝ) * V * pi)
    (hCount : ∫ w, H 1 w ∂E.P ≤ 8 * (n : ℝ) * pi)
    (hDom : ∀ w ∈ G, ∀ t ∈ T,
      thresholdCenteredScore E kind n t w ^ 2 ≤ H 0 w ∧
      thresholdCenteredCount E n t w ^ 2 ≤ H 1 w) :
    ∃ S : Fin 2 → Set E.Om, (∀ i, MeasurableSet (S i)) ∧
      E.P.real (G \ S 0) ≤ delta / 6 ∧ E.P.real (G \ S 1) ≤ delta / 6 ∧
      ∀ w ∈ G, (∀ i, w ∈ S i) → ∀ t ∈ T,
        |thresholdCenteredScore E kind n t w| ≤
          Real.sqrt (48 * (n : ℝ) * V * pi / delta) ∧
        |thresholdCenteredCount E n t w| ≤
          Real.sqrt (48 * (n : ℝ) * pi / delta) := by
  let R : Fin 2 → ℝ := ![48 * (n : ℝ) * V * pi / delta,
    48 * (n : ℝ) * pi / delta]
  let S : Fin 2 → Set E.Om := fun i => {w | H i w ≤ R i}
  have hR0 : ∀ i, 0 ≤ R i := by
    intro i
    fin_cases i
    · have hK := (integral_nonneg_of_ae (hNonneg 0)).trans hScore
      have h := mul_nonneg (show 0 ≤ 6 / delta by positivity) hK
      convert h using 1 <;> first | rfl | (dsimp [R]; ring)
    · have hK := (integral_nonneg_of_ae (hNonneg 1)).trans hCount
      have h := mul_nonneg (show 0 ≤ 6 / delta by positivity) hK
      convert h using 1 <;> first | rfl | (dsimp [R]; ring)
  have hFailure (i : Fin 2) : E.P.real (G \ S i) ≤ delta / 6 := by
    have hBound : E.P.real {w | R i < H i w} ≤ delta / 6 := by
      fin_cases i
      · convert square_envelope_failure_sixth E.P (H 0) (hInt 0) (hNonneg 0) hd hScore using 1 <;>
          dsimp [R] <;> congr 1 <;> ext w <;> congr 1 <;> ring
      · convert square_envelope_failure_sixth E.P (H 1) (hInt 1) (hNonneg 1) hd hCount using 1 <;>
          dsimp [R] <;> congr 1 <;> ext w <;> congr 1 <;> ring
    apply (measureReal_mono (μ := E.P) (h₂ := measure_ne_top E.P _) ?_).trans hBound
    intro w hw
    exact lt_of_not_ge (show ¬ H i w ≤ R i from hw.2)
  refine ⟨S, fun i => measurableSet_le (hMeas i) measurable_const,
    hFailure 0, hFailure 1, ?_⟩
  intro w hw hS t ht
  constructor
  · exact uniform_abs_bound_of_square_envelope
      (thresholdCenteredScore E kind n) T G (H 0)
      (fun w hw t ht => (hDom w hw t ht).1) (hR0 0) hw (hS 0) t ht
  · exact uniform_abs_bound_of_square_envelope
      (thresholdCenteredCount E n) T G (H 1)
      (fun w hw t ht => (hDom w hw t ht).2) (hR0 1) hw (hS 1) t ht

/-- If [the two envelopes are measurable](hyp:hMeas), [integrable](hyp:hInt), [nonnegative almost surely](hyp:hNonneg), [the confidence level is positive](hyp:hd), [the score-envelope mean has its budget](hyp:hScore), [the count-envelope mean has its budget](hyp:hCount), and [both envelopes dominate their threshold processes almost surely on the good set](hyp:hDom), then [there are measurable maximal events](goal) with the same small-removal and uniform-bound guarantees.

Almost-sure simultaneous domination suffices: remove a measurable null superset of its exceptional set from both sampling events. -/
-- @node: threshold_maximal_events_of_ae_square_envelopes
lemma threshold_maximal_events_of_ae_square_envelopes
    {q d : ℕ} {M : ExtremeModel q d} (E : NeteExperiment M) (kind : EstimatorKind)
    (n : ℕ) (T : Set ℝ) (G : Set E.Om) (H : Fin 2 → E.Om → ℝ)
    (hMeas : ∀ i, Measurable (H i)) (hInt : ∀ i, Integrable (H i) E.P)
    (hNonneg : ∀ i, ∀ᵐ w ∂E.P, 0 ≤ H i w)
    {V pi delta : ℝ} (hd : 0 < delta)
    (hScore : ∫ w, H 0 w ∂E.P ≤ 8 * (n : ℝ) * V * pi)
    (hCount : ∫ w, H 1 w ∂E.P ≤ 8 * (n : ℝ) * pi)
    (hDom : ∀ᵐ w ∂E.P, w ∈ G → ∀ t ∈ T,
      thresholdCenteredScore E kind n t w ^ 2 ≤ H 0 w ∧
      thresholdCenteredCount E n t w ^ 2 ≤ H 1 w) :
    ∃ S : Fin 2 → Set E.Om, (∀ i, MeasurableSet (S i)) ∧
      E.P.real (G \ S 0) ≤ delta / 6 ∧ E.P.real (G \ S 1) ≤ delta / 6 ∧
      ∀ w ∈ G, (∀ i, w ∈ S i) → ∀ t ∈ T,
        |thresholdCenteredScore E kind n t w| ≤
          Real.sqrt (48 * (n : ℝ) * V * pi / delta) ∧
        |thresholdCenteredCount E n t w| ≤
          Real.sqrt (48 * (n : ℝ) * pi / delta) := by
  classical
  obtain ⟨N, hNsub, hN, hNzero⟩ := exists_measurable_superset_of_null (ae_iff.mp hDom)
  have hPoint : ∀ w ∈ G \ N, ∀ t ∈ T,
      thresholdCenteredScore E kind n t w ^ 2 ≤ H 0 w ∧
      thresholdCenteredCount E n t w ^ 2 ≤ H 1 w := by
    intro w hw
    have hg : w ∈ G → ∀ t ∈ T,
        thresholdCenteredScore E kind n t w ^ 2 ≤ H 0 w ∧
        thresholdCenteredCount E n t w ^ 2 ≤ H 1 w := by
      by_contra h
      exact hw.2 (hNsub h)
    exact hg hw.1
  obtain ⟨S, hS, hSF, hCF, hBound⟩ := threshold_maximal_events_of_square_envelopes
    E kind n T (G \ N) H hMeas hInt hNonneg hd hScore hCount hPoint
  have hFailure (i : Fin 2) : E.P.real (G \ (S i \ N)) ≤
      E.P.real ((G \ N) \ S i) := by
    calc
      _ ≤ E.P.real (((G \ N) \ S i) ∪ N) := by
        apply measureReal_mono (h₂ := measure_ne_top E.P _)
        intro w hw
        by_cases hwN : w ∈ N
        · exact Or.inr hwN
        · exact Or.inl ⟨⟨hw.1, hwN⟩, fun hs => hw.2 ⟨hs, hwN⟩⟩
      _ ≤ E.P.real ((G \ N) \ S i) + E.P.real N := measureReal_union_le _ _
      _ = _ := by simp [measureReal_def, hNzero]
  refine ⟨fun i => S i \ N, fun i => (hS i).diff hN,
    (hFailure 0).trans hSF, (hFailure 1).trans hCF, ?_⟩
  intro w hw hAll
  exact hBound w ⟨hw, (hAll 0).2⟩ (fun i => (hAll i).1)

end Papers.TbsExtremeEffects

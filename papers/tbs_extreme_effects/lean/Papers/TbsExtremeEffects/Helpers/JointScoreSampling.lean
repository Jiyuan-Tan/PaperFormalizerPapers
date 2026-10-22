module
public import Papers.TbsExtremeEffects.Helpers.TrainingScore

/-! Shared nuisance and count events for simultaneous DR and IPW sampling bounds.
The four truncated failures and two optional variance failures are localized
before adjoining the Hill event, so shared failures are counted only once. -/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
variable {q d : ℕ} {M : ExtremeModel q d}

/-- For [measurable events `S`](hyp:hS) and [`T`](hyp:hT), if [the base event `A` has probability at least `1-a`](hyp:hA), [its failure to lie in `S` has probability at most `b`](hyp:hAS), and [its failure to lie in `T` has probability at most `c`](hyp:hAT), then [their intersection with the base event has probability at least `1-(a+b+c)`](goal).
@node: probability_localized_pair_lower -/
lemma probability_localized_pair_lower {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (A S T : Set Ω)
    (hS : MeasurableSet S) (hT : MeasurableSet T) {a b c : ℝ}
    (hA : 1 - a ≤ P.real A) (hAS : P.real (A \ S) ≤ b)
    (hAT : P.real (A \ T) ≤ c) :
    1 - (a + b + c) ≤ P.real ((A ∩ S) ∩ T) := by
  have hsplitS := measureReal_inter_add_sdiff (μ := P) (s := A) hS
  have hsplitT := measureReal_inter_add_sdiff (μ := P) (s := A ∩ S) hT
  have hsub : (A ∩ S) \ T ⊆ A \ T := fun _ hw => ⟨hw.1.1, hw.2⟩
  have hbadT : P.real ((A ∩ S) \ T) ≤ c :=
    (measureReal_mono (μ := P) (h₂ := measure_ne_top P _) hsub).trans hAT
  linarith

/-- Given [an even sample size](hyp:hn), [IID sampling](hyp:hIID), [regularly varying noise](hyp:hRV), [exponent training](hyp:hTraining), [a measurable nuisance event](hyp:hG), [a measurable nonzero-count event](hyp:hN), [measurable score bounds](hyp:hB), [nonnegative score bounds](hyp:hBpos), [a positive confidence level](hyp:hd), [the nuisance-event probability bound](hyp:hGprob), [the count-event probability bound](hyp:hNprob), [the Hill-event probability bound](hyp:hHprob), [nonzero evaluation counts on the count event](hyp:hcount), [score integrability on the nuisance event](hyp:hf), and [conditional second-moment control](hyp:hMem), [the displayed simultaneous score-sampling event has probability at least `1-5 delta/6`](goal).
@node: joint_score_sampling_probability -/
lemma joint_score_sampling_probability (E : NeteExperiment M)
    (n : ℕ) (hn : EvenSampleSize n) (hIID : IIDSampling E n)
    (hRV : NoiseRegularlyVarying M) (hTraining : ExponentTraining E n)
    (t : ℝ) (G N H : Set E.Om) (hG : MeasurableSet[trainSigma E n] G)
    (hN : MeasurableSet N)
    (B : EstimatorKind → E.Om → ℝ)
    (hB : ∀ kind, Measurable[trainSigma E n] (B kind))
    (hBpos : ∀ kind w, 0 ≤ B kind w)
    {delta : ℝ} (hd : 0 < delta)
    (hGprob : 1 - delta / 12 ≤ E.P.real G)
    (hNprob : 1 - delta / 12 ≤ E.P.real N)
    (hHprob : 1 - delta / 6 ≤ E.P.real H)
    (hcount : ∀ w ∈ N, evalCount E n t w ≠ 0)
    (hf : ∀ kind, ∀ᵐ w ∂E.P,
      w ∈ G → Integrable (score E kind n w) (obsTailLaw M t))
    (useVariance : Prop)
    (hMem : useVariance → ∀ kind, ∀ᵐ w ∂E.P,
      w ∈ G → MemLp (score E kind n w) 2 (obsTailLaw M t)) :
    1 - 5 * delta / 6 ≤ E.P.real {w |
      w ∈ G ∧ w ∈ N ∧ w ∈ H ∧
      (∀ kind, |etaEstimate E kind n t w -
        ∫ z, score E kind n w z ∂obsTailLaw M t| ≤
          scoreSamplingRadius (obsTailLaw M t) (score E kind n w)
            (evalCount E n t w) (B kind w) (delta / 3)) ∧
      (useVariance → ∀ kind, |etaEstimate E kind n t w -
        ∫ z, score E kind n w z ∂obsTailLaw M t| ≤
          Real.sqrt (4 * (scoreVariance E kind n t w).toReal /
            ((delta / 3) * evalCount E n t w)))} := by
  classical
  let R (kind : EstimatorKind) := {w |
    |etaEstimate E kind n t w - ∫ z, score E kind n w z ∂obsTailLaw M t| ≤
      scoreSamplingRadius (obsTailLaw M t) (score E kind n w)
        (evalCount E n t w) (B kind w) (delta / 3)}
  let F (kind : EstimatorKind) := {w |
    |etaEstimate E kind n t w - ∫ z, score E kind n w z ∂obsTailLaw M t| ≤
      Real.sqrt (4 * (scoreVariance E kind n t w).toReal /
        ((delta / 3) * evalCount E n t w))}
  have hR (kind) : MeasurableSet (R kind) :=
    measurableSet_score_truncation_event E kind hRV hTraining t (delta / 3)
      (B kind) ((hB kind).mono (trainSigma_le E n) le_rfl)
  have hF (kind) : MeasurableSet (F kind) :=
    measurableSet_score_variance_event E kind hRV hTraining t (delta / 3)
  have hGN : 1 - delta / 6 ≤ E.P.real (G ∩ N) := by
    have h := probability_intersection_lower E.P G N hN hGprob hNprob
    linarith
  have hbadR (kind) : E.P.real ((G ∩ N) \ R kind) ≤ delta / 6 := by
    have h := score_evaluation_localized_truncated_failure E kind n hn hIID hRV
      hTraining t G N hG hN (B kind) (hB kind) (hBpos kind) (by positivity)
      hcount (hf kind) (delta := delta / 3)
    exact h.trans (by ring_nf; rfl)
  let A := ((G ∩ N) ∩ R .dr) ∩ R .ipw
  have hA : 1 - delta / 2 ≤ E.P.real A := by
    have h := probability_localized_pair_lower E.P (G ∩ N) (R .dr) (R .ipw)
      (hR .dr) (hR .ipw) hGN (hbadR .dr) (hbadR .ipw)
    dsimp only [A]
    linarith
  let J := A ∩ {w | useVariance → ∀ kind, w ∈ F kind}
  have hJ : 1 - 2 * delta / 3 ≤ E.P.real J := by
    by_cases hV : useVariance
    · have hbadF (kind) : E.P.real (A \ F kind) ≤ delta / 12 := by
        have h := score_evaluation_localized_variance_failure E kind n hn hIID hRV
          hTraining t G N hG hN (by positivity) hcount (hMem hV kind)
          (delta := delta / 3)
        have hsub : A \ F kind ⊆ (G ∩ N) \ F kind :=
          fun _ hw => ⟨hw.1.1.1, hw.2⟩
        exact ((measureReal_mono (μ := E.P) (h₂ := measure_ne_top E.P _) hsub).trans h).trans
          (by ring_nf; rfl)
      have h := probability_localized_pair_lower E.P A (F .dr) (F .ipw)
        (hF .dr) (hF .ipw) hA (hbadF .dr) (hbadF .ipw)
      have hsets : J = (A ∩ F .dr) ∩ F .ipw := by
        ext w
        simp only [J, Set.mem_inter_iff, Set.mem_setOf_eq, hV, true_implies]
        constructor
        · intro hw
          exact ⟨⟨hw.1, hw.2 .dr⟩, hw.2 .ipw⟩
        · rintro ⟨⟨hw, hdr⟩, hipw⟩
          exact ⟨hw, fun kind => by cases kind; exact hipw; exact hdr⟩
      rw [hsets]
      linarith
    · have hsets : J = A := by
        ext w
        simp only [J, Set.mem_inter_iff, Set.mem_setOf_eq, hV, false_implies, and_true]
      rw [hsets]
      linarith
  have hJmeas : MeasurableSet J := by
    have hAmeas : MeasurableSet A :=
      (((trainSigma_le E n) _ hG).inter hN).inter (hR .dr) |>.inter (hR .ipw)
    by_cases hV : useVariance
    · have hsets : {w | useVariance → ∀ kind, w ∈ F kind} = F .dr ∩ F .ipw := by
        ext w
        simp only [Set.mem_setOf_eq, Set.mem_inter_iff, hV, true_implies]
        constructor
        · intro hw; exact ⟨hw .dr, hw .ipw⟩
        · rintro ⟨hdr, hipw⟩ kind
          cases kind
          · exact hipw
          · exact hdr
      exact hAmeas.inter (hsets ▸ ((hF .dr).inter (hF .ipw)))
    · have hsets : {w | useVariance → ∀ kind, w ∈ F kind} = Set.univ := by
        ext w
        simp only [Set.mem_setOf_eq, hV, false_implies, Set.mem_univ]
      exact hAmeas.inter (hsets ▸ MeasurableSet.univ)
  have hFinal := probability_intersection_lower E.P H J hJmeas hHprob hJ
  apply (show 1 - 5 * delta / 6 ≤ E.P.real (H ∩ J) by linarith).trans
  apply measureReal_mono (h₂ := measure_ne_top E.P _)
  rintro w ⟨hwH, ⟨⟨⟨⟨hwG, hwN⟩, hdr⟩, hipw⟩, hvar⟩⟩
  exact ⟨hwG, hwN, hwH, (fun kind => by cases kind; exact hipw; exact hdr), hvar⟩

end Papers.TbsExtremeEffects

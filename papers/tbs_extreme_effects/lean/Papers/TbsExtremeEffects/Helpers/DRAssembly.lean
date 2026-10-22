module
public import Papers.TbsExtremeEffects.Helpers.ScoreMoments

/-! Truncation and event assembly for the doubly robust first-factor bound. -/

@[expose] public section
set_option linter.style.longLine false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {q d : ℕ} {M : ExtremeModel q d}

/-- If [both estimated treatment probabilities are nonzero](hyp:hph,hph'), [the doubly robust conditional bias equals the propensity error times the displayed sum of outcome-model errors](goal).

@node: dr_conditional_bias_identity
-/
lemma dr_conditional_bias_identity {p ph m1 m0 g1 g0 : ℝ}
    (hph : ph ≠ 0) (hph' : 1 - ph ≠ 0) :
    g1 - g0 + p / ph * (m1 - g1) - (1 - p) / (1 - ph) * (m0 - g0) -
      (m1 - m0) = (p - ph) * ((m1 - g1) / ph + (m0 - g0) / (1 - ph)) := by
  field_simp
  <;> ring

/-- If [the overlap constant is positive](hyp:hc), [the estimated treated probability is at least that constant](hyp:hph), [its complement is also at least that constant](hyp:hph'), [the propensity error is bounded](hyp:hp), and [both treatment-specific outcome-model errors are bounded](hyp:h1,h0), then [the absolute conditional bias is at most `(2 / c) * rp * rg`](goal).

@node: dr_conditional_bias_bound
-/
lemma dr_conditional_bias_bound {p ph m1 m0 g1 g0 c rp rg : ℝ}
    (hc : 0 < c) (hph : c ≤ ph) (hph' : c ≤ 1 - ph)
    (hp : |p - ph| ≤ rp) (h1 : |m1 - g1| ≤ rg) (h0 : |m0 - g0| ≤ rg) :
    |g1 - g0 + p / ph * (m1 - g1) - (1 - p) / (1 - ph) * (m0 - g0) -
      (m1 - m0)| ≤ (2 / c) * rp * rg := by
  have hp0 : 0 ≤ rp := (abs_nonneg _).trans hp
  have hg0 : 0 ≤ rg := (abs_nonneg _).trans h1
  have hpos := hc.trans_le hph
  have hpos' := hc.trans_le hph'
  rw [dr_conditional_bias_identity hpos.ne' hpos'.ne', abs_mul]
  have hb1 : |(m1 - g1) / ph| ≤ rg / c := by
    rw [abs_div, abs_of_pos hpos]
    exact div_le_div₀ hg0 h1 hc hph
  have hb0 : |(m0 - g0) / (1 - ph)| ≤ rg / c := by
    rw [abs_div, abs_of_pos hpos']
    exact div_le_div₀ hg0 h0 hc hph'
  calc
    |p - ph| * |(m1 - g1) / ph + (m0 - g0) / (1 - ph)| ≤
        rp * (rg / c + rg / c) :=
      mul_le_mul hp ((abs_add_le _ _).trans (add_le_add hb1 hb0))
        (abs_nonneg _) hp0
    _ = (2 / c) * rp * rg := by ring

/-- If [the truncated part is integrable](hyp:hs) and [the tail part is integrable](hyp:hl), then [the integral of a function is the sum of its values inside and outside the truncation threshold](goal).

@node: truncated_integral_split
-/
lemma truncated_integral_split {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (B : ℝ)
    (hs : Integrable (fun z => if |f z| ≤ B then f z else 0) μ)
    (hl : Integrable (fun z => if B < |f z| then f z else 0) μ) :
    (∫ z, f z ∂μ) = (∫ z, if |f z| ≤ B then f z else 0 ∂μ) +
      ∫ z, if B < |f z| then f z else 0 ∂μ := by
  rw [← integral_add hs hl]
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : |f z| ≤ B <;> simp [hz, not_lt_of_ge, lt_of_not_ge]

/-- [The absolute integral over observations beyond the truncation threshold is bounded by the integral of their absolute values](goal).

@node: truncated_tail_integral_bound
-/
lemma truncated_tail_integral_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (B : ℝ) :
    |∫ z, if B < |f z| then f z else 0 ∂μ| ≤
      ∫ z, if B < |f z| then |f z| else 0 ∂μ := by
  calc
    _ ≤ ∫ z, |if B < |f z| then f z else 0| ∂μ := abs_integral_le_integral_abs
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with z
      split_ifs <;> simp

/-- If [the averaging weight is nonnegative](hyp:hb), [the truncated part is integrable](hyp:hs), [the tail part is integrable](hyp:hl), [the empirical truncated average is within `s` of its mean](hyp:hsmall), and [the empirical absolute tail average is at most `r`](hyp:hlarge), then [the full empirical-average error is bounded by `s`, `r`, and the population absolute-tail integral](goal).

@node: truncated_average_error_bound
-/
lemma truncated_average_error_bound {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (B : ℝ) (I : Finset ι) (z : ι → Ω)
    (b s r : ℝ) (hb : 0 ≤ b)
    (hs : Integrable (fun z => if |f z| ≤ B then f z else 0) μ)
    (hl : Integrable (fun z => if B < |f z| then f z else 0) μ)
    (hsmall : |b * ∑ i ∈ I, (if |f (z i)| ≤ B then f (z i) else 0) -
      ∫ z, if |f z| ≤ B then f z else 0 ∂μ| ≤ s)
    (hlarge : b * ∑ i ∈ I, (if B < |f (z i)| then |f (z i)| else 0) ≤ r) :
    |b * ∑ i ∈ I, f (z i) - ∫ z, f z ∂μ| ≤
      s + r + ∫ z, if B < |f z| then |f z| else 0 ∂μ := by
  have hsum : (∑ i ∈ I, f (z i)) =
      (∑ i ∈ I, if |f (z i)| ≤ B then f (z i) else 0) +
      ∑ i ∈ I, if B < |f (z i)| then f (z i) else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hz : |f (z i)| ≤ B <;> simp [hz, not_lt_of_ge, lt_of_not_ge]
  have htail : |b * ∑ i ∈ I, (if B < |f (z i)| then f (z i) else 0)| ≤ r := by
    rw [abs_mul, abs_of_nonneg hb]
    apply le_trans (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hb)
    simpa only [apply_ite abs, abs_zero] using hlarge
  rw [hsum, truncated_integral_split μ f B hs hl]
  have heq : b * ((∑ i ∈ I, if |f (z i)| ≤ B then f (z i) else 0) +
      ∑ i ∈ I, if B < |f (z i)| then f (z i) else 0) -
      ((∫ z, if |f z| ≤ B then f z else 0 ∂μ) +
        ∫ z, if B < |f z| then f z else 0 ∂μ) =
      (b * (∑ i ∈ I, if |f (z i)| ≤ B then f (z i) else 0) -
        ∫ z, if |f z| ≤ B then f z else 0 ∂μ) +
      (b * (∑ i ∈ I, if B < |f (z i)| then f (z i) else 0) -
        ∫ z, if B < |f z| then f z else 0 ∂μ) := by ring
  rw [heq]
  rw [add_assoc]
  exact (abs_add_le _ _).trans (add_le_add hsmall
    ((abs_sub _ _).trans (add_le_add htail (truncated_tail_integral_bound μ f B))))

/-- If [the second event is measurable](hyp:hT), [the first event has probability at least `1 - a`](hyp:hS), and [the second has probability at least `1 - b`](hyp:hTp), then [their intersection has probability at least `1 - (a + b)`](goal).

@node: probability_intersection_lower
-/
lemma probability_intersection_lower {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (S T : Set Ω) (hT : MeasurableSet T)
    {a b : ℝ} (hS : 1 - a ≤ P.real S) (hTp : 1 - b ≤ P.real T) :
    1 - (a + b) ≤ P.real (S ∩ T) := by
  have hunion : P.real (S ∪ T) ≤ 1 := by
    simpa using (measureReal_mono (μ := P) (Set.subset_univ (S ∪ T)))
  have hadd := measureReal_union_add_inter (μ := P) (s := S) hT
  linarith

/-- If [each of the last three events is measurable](hyp:hN,hS,hT) and [each of four events has probability at least `1 - delta / 4`](hyp:hGp,hNp,hSp,hTp), then [all four events hold together with probability at least `1 - delta`](goal).

@node: probability_four_events_lower
-/
lemma probability_four_events_lower {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (G N S T : Set Ω)
    (hN : MeasurableSet N) (hS : MeasurableSet S) (hT : MeasurableSet T)
    {delta : ℝ} (hGp : 1 - delta / 4 ≤ P.real G)
    (hNp : 1 - delta / 4 ≤ P.real N) (hSp : 1 - delta / 4 ≤ P.real S)
    (hTp : 1 - delta / 4 ≤ P.real T) :
    1 - delta ≤ P.real (((G ∩ N) ∩ S) ∩ T) := by
  have hGN := probability_intersection_lower P G N hN hGp hNp
  have hGNS := probability_intersection_lower P (G ∩ N) S hS hGN hSp
  have hGNST := probability_intersection_lower P ((G ∩ N) ∩ S) T hT hGNS hTp
  convert hGNST using 1 <;> ring

/-- If [every one of four events is measurable](hyp:hmeas), [each has probability at least `1 - delta / 4`](hyp:hprob), and [their simultaneous occurrence implies a target event](hyp:himp), then [the target event has probability at least `1 - delta`](goal).

@node: probability_four_events_imp
-/
lemma probability_four_events_imp {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (S : Fin 4 → Set Ω)
    (hmeas : ∀ i, MeasurableSet (S i)) {delta : ℝ}
    (hprob : ∀ i, 1 - delta / 4 ≤ P.real (S i)) (T : Set Ω)
    (himp : ∀ w, (∀ i, w ∈ S i) → w ∈ T) : 1 - delta ≤ P.real T := by
  apply (probability_four_events_lower P (S 0) (S 1) (S 2) (S 3)
    (hmeas 1) (hmeas 2) (hmeas 3) (hprob 0) (hprob 1) (hprob 2) (hprob 3)).trans
  apply measureReal_mono (h₂ := measure_ne_top P _)
  intro w hw
  apply himp w
  intro i
  fin_cases i
  · exact hw.1.1.1
  · exact hw.1.1.2
  · exact hw.1.2
  · exact hw.2

/-- If [the evaluation count is nonzero](hyp:hcount), [the truncated score is integrable](hyp:hs), [the score tail is integrable](hyp:hl), [the truncated empirical error has its stated bound](hyp:hsmall), [the empirical tail has its stated bound](hyp:hlarge), and [the score mean is close to the target](hyp:hmean), then [the doubly robust estimate has the stated truncated-error bound](goal).

@node: dr_truncated_bound_of_components
-/
lemma dr_truncated_bound_of_components (E : NeteExperiment M)
    (n : ℕ) (t delta c Cgb K : ℝ) (Rp Rg Ralpha : ℕ → ℝ → ℝ)
    (B : E.Om → ℝ) (w : E.Om) (hcount : evalCount E n t w ≠ 0)
    (hs : Integrable (fun z => if |score E .dr n w z| ≤ B w then score E .dr n w z
      else 0) (obsTailLaw M t))
    (hl : Integrable (fun z => if B w < |score E .dr n w z| then score E .dr n w z
      else 0) (obsTailLaw M t))
    (hsmall : |(evalCount E n t w : ℝ)⁻¹ * ∑ i ∈ evalSet E n t w,
      (if |score E .dr n w (obs E n w i)| ≤ B w then score E .dr n w (obs E n w i)
        else 0) - ∫ z, if |score E .dr n w z| ≤ B w then score E .dr n w z else 0
          ∂obsTailLaw M t| ≤
      Real.sqrt (4 * truncatedSecondMoment E .dr n t B w / (delta * evalCount E n t w)))
    (hlarge : (evalCount E n t w : ℝ)⁻¹ * ∑ i ∈ evalSet E n t w,
      (if B w < |score E .dr n w (obs E n w i)| then |score E .dr n w (obs E n w i)|
        else 0) ≤ (4 / delta) * scoreTailMoment E .dr n t B w)
    (hmean : |(∫ z, score E .dr n w z ∂obsTailLaw M t) - etaTarget M| ≤
      etaRemainder E .dr c Cgb K Rp Rg Ralpha n t (delta / 4) w) :
    |etaEstimate E .dr n t w - etaTarget M| ≤
      etaTruncatedError E .dr c Cgb K Rp Rg Ralpha n t delta B w := by
  have hsample := truncated_average_error_bound (obsTailLaw M t) (score E .dr n w)
    (B w) (evalSet E n t w) (obs E n w) (evalCount E n t w : ℝ)⁻¹
    (Real.sqrt (4 * truncatedSecondMoment E .dr n t B w / (delta * evalCount E n t w)))
    ((4 / delta) * scoreTailMoment E .dr n t B w) (by positivity) hs hl hsmall hlarge
  change |etaDR E n t w - etaTarget M| ≤ _
  rw [etaDR, if_neg hcount]
  change |(evalCount E n t w : ℝ)⁻¹ * ∑ i ∈ evalSet E n t w,
    score E .dr n w (obs E n w i) - etaTarget M| ≤ _
  calc
    _ ≤ |(evalCount E n t w : ℝ)⁻¹ * ∑ i ∈ evalSet E n t w,
        score E .dr n w (obs E n w i) - ∫ z, score E .dr n w z ∂obsTailLaw M t| +
        |(∫ z, score E .dr n w z ∂obsTailLaw M t) - etaTarget M| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add hsample hmean
    _ = _ := by unfold etaTruncatedError scoreTailMoment; ring

/-- If [the estimate is close to its score mean with the stated variance bound](hyp:hsample) and [that score mean is close to the target](hyp:hmean), then [the target-estimation error is at most the sum of those two bounds](goal).

@node: dr_variance_bound_of_components
-/
lemma dr_variance_bound_of_components (E : NeteExperiment M)
    (n : ℕ) (t delta c Cgb K : ℝ) (Rp Rg Ralpha : ℕ → ℝ → ℝ) (w : E.Om)
    (hsample : |etaEstimate E .dr n t w -
      ∫ z, score E .dr n w z ∂obsTailLaw M t| ≤
        Real.sqrt (4 * (scoreVariance E .dr n t w).toReal / (delta * evalCount E n t w)))
    (hmean : |(∫ z, score E .dr n w z ∂obsTailLaw M t) - etaTarget M| ≤
      etaRemainder E .dr c Cgb K Rp Rg Ralpha n t (delta / 4) w) :
    (fun err V delta count remainder : ℝ =>
        err ≤ Real.sqrt (4 * V / (delta * count)) + remainder) |etaEstimate E .dr n t w - etaTarget M|
      (scoreVariance E .dr n t w).toReal delta (evalCount E n t w)
      (etaRemainder E .dr c Cgb K Rp Rg Ralpha n t (delta / 4) w) := by
  exact (abs_sub_le _ (∫ z, score E .dr n w z ∂obsTailLaw M t) _).trans
    (add_le_add hsample hmean)

/-- For [an experiment](hyp:E), [sample size](hyp:n), [tail threshold and confidence/overlap constants](hyp:t,delta,c,Cgb,K), [nuisance-rate functions](hyp:Rp,Rg,Ralpha), and [a truncation level chosen from the outcome](hyp:B), [a truncated-event certificate](goal) asserts that: [four measurable events are supplied](step:1), [each has probability at least `1 - delta / 4`](step:2), and [their intersection gives the count, integrability, empirical-error, tail, and mean-error conditions needed for the truncated bound](step:3).

@node: DrTruncatedEventCertificate
-/
def DrTruncatedEventCertificate (E : NeteExperiment M)
    (n : ℕ) (t delta c Cgb K : ℝ) (Rp Rg Ralpha : ℕ → ℝ → ℝ) (B : E.Om → ℝ) : Prop :=
  ∃ S : Fin 4 → Set E.Om, (∀ i, MeasurableSet (S i)) ∧
    (∀ i, 1 - delta / 4 ≤ E.P.real (S i)) ∧
    ∀ w, (∀ i, w ∈ S i) →
      (n : ℝ) * tailProb M t / 4 ≤ evalCount E n t w ∧
      evalCount E n t w ≠ 0 ∧
      Integrable (fun z => if |score E .dr n w z| ≤ B w then score E .dr n w z
        else 0) (obsTailLaw M t) ∧
      Integrable (fun z => if B w < |score E .dr n w z| then score E .dr n w z
        else 0) (obsTailLaw M t) ∧
      |(evalCount E n t w : ℝ)⁻¹ * ∑ i ∈ evalSet E n t w,
        (if |score E .dr n w (obs E n w i)| ≤ B w then score E .dr n w (obs E n w i)
          else 0) - ∫ z, if |score E .dr n w z| ≤ B w then score E .dr n w z else 0
            ∂obsTailLaw M t| ≤
        Real.sqrt (4 * truncatedSecondMoment E .dr n t B w / (delta * evalCount E n t w)) ∧
      (evalCount E n t w : ℝ)⁻¹ * ∑ i ∈ evalSet E n t w,
        (if B w < |score E .dr n w (obs E n w i)| then |score E .dr n w (obs E n w i)|
          else 0) ≤ (4 / delta) * scoreTailMoment E .dr n t B w ∧
      |(∫ z, score E .dr n w z ∂obsTailLaw M t) - etaTarget M| ≤
        etaRemainder E .dr c Cgb K Rp Rg Ralpha n t (delta / 4) w

/-- If [a truncated-event certificate is available](hyp:h), then [the count threshold and the truncated doubly robust error bound hold jointly with probability at least `1 - delta`](goal).

@node: dr_truncated_probability_of_certificate
-/
lemma dr_truncated_probability_of_certificate (E : NeteExperiment M)
    (n : ℕ) (t delta c Cgb K : ℝ) (Rp Rg Ralpha : ℕ → ℝ → ℝ) (B : E.Om → ℝ)
    (h : DrTruncatedEventCertificate E n t delta c Cgb K Rp Rg Ralpha B) :
    1 - delta ≤ E.P.real {w | (n : ℝ) * tailProb M t / 4 ≤ evalCount E n t w ∧
      |etaEstimate E .dr n t w - etaTarget M| ≤
        etaTruncatedError E .dr c Cgb K Rp Rg Ralpha n t delta B w} := by
  obtain ⟨S, hmeas, hprob, hpoint⟩ := h
  apply probability_four_events_imp E.P S hmeas hprob
  intro w hw
  obtain ⟨hcount, hnonzero, hs, hl, hsmall, hlarge, hmean⟩ := hpoint w hw
  exact ⟨hcount, dr_truncated_bound_of_components E n t delta c Cgb K Rp Rg Ralpha B w
    hnonzero hs hl hsmall hlarge hmean⟩

/-- For [an experiment](hyp:E), [sample size](hyp:n), [tail threshold and confidence/overlap constants](hyp:t,delta,c,Cgb,K), and [nuisance-rate functions](hyp:Rp,Rg,Ralpha), [a variance-event certificate](goal) asserts that: [four measurable events are supplied](step:1), [each has probability at least `1 - delta / 4`](step:2), and [their intersection gives the count, finite-variance, sampling-error, and mean-error conditions](step:3).

@node: DrVarianceEventCertificate
-/
def DrVarianceEventCertificate (E : NeteExperiment M)
    (n : ℕ) (t delta c Cgb K : ℝ) (Rp Rg Ralpha : ℕ → ℝ → ℝ) : Prop :=
  ∃ S : Fin 4 → Set E.Om, (∀ i, MeasurableSet (S i)) ∧
    (∀ i, 1 - delta / 4 ≤ E.P.real (S i)) ∧
    ∀ w, (∀ i, w ∈ S i) →
      (n : ℝ) * tailProb M t / 4 ≤ evalCount E n t w ∧
      scoreVariance E .dr n t w ≠ ∞ ∧
      |etaEstimate E .dr n t w - ∫ z, score E .dr n w z ∂obsTailLaw M t| ≤
        Real.sqrt (4 * (scoreVariance E .dr n t w).toReal / (delta * evalCount E n t w)) ∧
      |(∫ z, score E .dr n w z ∂obsTailLaw M t) - etaTarget M| ≤
        etaRemainder E .dr c Cgb K Rp Rg Ralpha n t (delta / 4) w

/-- If [a variance-event certificate is available](hyp:h), then [the count threshold, finite score variance, and variance-based doubly robust error bound hold jointly with probability at least `1 - delta`](goal).

@node: dr_variance_probability_of_certificate
-/
lemma dr_variance_probability_of_certificate (E : NeteExperiment M)
    (n : ℕ) (t delta c Cgb K : ℝ) (Rp Rg Ralpha : ℕ → ℝ → ℝ)
    (h : DrVarianceEventCertificate E n t delta c Cgb K Rp Rg Ralpha) :
    1 - delta ≤ E.P.real {w | (n : ℝ) * tailProb M t / 4 ≤ evalCount E n t w ∧
      scoreVariance E .dr n t w ≠ ∞ ∧
      (fun err V delta count remainder : ℝ =>
        err ≤ Real.sqrt (4 * V / (delta * count)) + remainder) |etaEstimate E .dr n t w - etaTarget M|
        (scoreVariance E .dr n t w).toReal delta (evalCount E n t w)
        (etaRemainder E .dr c Cgb K Rp Rg Ralpha n t (delta / 4) w)} := by
  obtain ⟨S, hmeas, hprob, hpoint⟩ := h
  apply probability_four_events_imp E.P S hmeas hprob
  intro w hw
  obtain ⟨hcount, hfinite, hsample, hmean⟩ := hpoint w hw
  exact ⟨hcount, hfinite,
    dr_variance_bound_of_components E n t delta c Cgb K Rp Rg Ralpha w hsample hmean⟩

end Papers.TbsExtremeEffects

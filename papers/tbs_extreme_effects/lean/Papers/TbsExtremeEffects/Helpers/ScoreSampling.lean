module
public import Papers.TbsExtremeEffects.Helpers.DRAssembly
public import Papers.TbsExtremeEffects.Helpers.TailSurvival
public import Causalean.Mathlib.Probability.IidMeanVariance

/-! Fixed-fit, positive-size sampling bounds for the DR and IPW scores.
The zero-moment cases are handled almost surely, without dividing by zero. -/

@[expose] public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Classical

/-- If [the random variable is square-integrable](hyp:hX), [the proposed variance bound is nonnegative](hyp:hv), [its variance is at most that bound](hyp:hvar), and [the failure probability is positive](hyp:hd), then [the probability that its centered value exceeds the Chebyshev radius is at most one quarter of that failure probability](goal). -/
-- @node: score_sampling_chebyshev
lemma score_sampling_chebyshev {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : MemLp X 2 P)
    {v delta : ℝ} (hv : 0 ≤ v) (hvar : variance X P ≤ v) (hd : 0 < delta) :
    P.real {w | Real.sqrt (4 * v / delta) < |X w - ∫ z, X z ∂P|} ≤ delta / 4 := by
  by_cases hz : v = 0
  · have hzero : variance X P = 0 := le_antisymm (by simpa [hz] using hvar)
      (variance_nonneg X P)
    have hae := ae_eq_integral_of_variance_eq_zero hX hzero
    have hnull : P {w | Real.sqrt (4 * v / delta) < |X w - ∫ z, X z ∂P|} = 0 := by
      apply measure_mono_null (t := {w | X w ≠ ∫ z, X z ∂P})
      · intro w hw heq
        simp [heq, hz] at hw
      · exact ae_iff.mp hae
    simp only [Measure.real, hnull, ENNReal.toReal_zero]
    positivity
  · have hvpos : 0 < v := lt_of_le_of_ne hv (Ne.symm hz)
    have hspos : 0 < Real.sqrt (4 * v / delta) := Real.sqrt_pos.mpr (by positivity)
    have hcheb := meas_ge_le_variance_div_sq hX hspos
    have hreal : P.real {w | Real.sqrt (4 * v / delta) ≤ |X w - ∫ z, X z ∂P|} ≤
        variance X P / (Real.sqrt (4 * v / delta)) ^ 2 := by
      have h := ENNReal.toReal_mono (by simp) hcheb
      simpa only [Measure.real, ENNReal.toReal_ofReal (div_nonneg (variance_nonneg X P) (sq_nonneg _))] using h
    apply (measureReal_mono (μ := P) (h₂ := measure_ne_top P _)
      (fun w (hw : Real.sqrt (4 * v / delta) < |X w - ∫ z, X z ∂P|) => hw.le)).trans
    apply hreal.trans
    rw [Real.sq_sqrt (by positivity : 0 ≤ 4 * v / delta)]
    apply (div_le_iff₀ (by positivity : 0 < 4 * v / delta)).mpr
    have heq : delta / 4 * (4 * v / delta) = v := by field_simp <;> ring
    rw [heq]
    exact hvar

/-- If [the random variable is integrable](hyp:hX), [it is almost surely nonnegative](hyp:hpos), and [the failure probability is positive](hyp:hd), then [the probability that it exceeds four times its mean divided by that probability is at most one quarter of it](goal). -/
-- @node: score_sampling_markov
lemma score_sampling_markov {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : Integrable X P)
    (hpos : ∀ᵐ w ∂P, 0 ≤ X w) {delta : ℝ} (hd : 0 < delta) :
    P.real {w | (4 / delta) * (∫ z, X z ∂P) < X w} ≤ delta / 4 := by
  have ha : 0 ≤ ∫ z, X z ∂P := integral_nonneg_of_ae hpos
  by_cases hz : (∫ z, X z ∂P) = 0
  · have hae : X =ᵐ[P] 0 := (integral_eq_zero_iff_of_nonneg_ae hpos hX).mp hz
    have hnull : P {w | (4 / delta) * (∫ z, X z ∂P) < X w} = 0 := by
      apply measure_mono_null (t := {w | X w ≠ 0})
      · intro w hw heq
        simp [hz, heq] at hw
      · exact ae_iff.mp hae
    simp only [Measure.real, hnull, ENNReal.toReal_zero]
    positivity
  · have hapos : 0 < ∫ z, X z ∂P := lt_of_le_of_ne ha (Ne.symm hz)
    have ht : 0 < (4 / delta) * (∫ z, X z ∂P) := by positivity
    have hmarkov := mul_meas_ge_le_integral_of_nonneg hpos hX
      ((4 / delta) * (∫ z, X z ∂P))
    have hcal : P.real {w | (4 / delta) * (∫ z, X z ∂P) ≤ X w} ≤ delta / 4 := by
      apply (mul_le_mul_iff_right₀ ht).mp
      have heq : ((4 / delta) * (∫ z, X z ∂P)) * (delta / 4) = ∫ z, X z ∂P := by
        field_simp
        <;> ring
      rw [heq]
      exact hmarkov
    exact (measureReal_mono (μ := P) (h₂ := measure_ne_top P _)
      (s₁ := {w | (4 / delta) * (∫ z, X z ∂P) < X w})
      (s₂ := {w | (4 / delta) * (∫ z, X z ∂P) ≤ X w})
      (by
        intro w hw
        change (4 / delta) * (∫ z, X z ∂P) < X w at hw
        change (4 / delta) * (∫ z, X z ∂P) ≤ X w
        exact hw.le)).trans hcal

/-- If [the score is measurable](hyp:hf) and [the truncation level is nonnegative](hyp:hB), then [the score set to zero outside that level is square-integrable](goal). -/
-- @node: score_truncation_memLp
lemma score_truncation_memLp {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {f : Ω → ℝ} (hf : Measurable f)
    {B : ℝ} (hB : 0 ≤ B) :
    MemLp (fun z => if |f z| ≤ B then f z else 0) 2 P := by
  apply MemLp.of_bound (C := B)
  · apply Measurable.aestronglyMeasurable
    first | fun_prop | skip
    have habs : Measurable (fun z => |f z|) := by fun_prop
    exact hf.ite (measurableSet_le habs measurable_const) measurable_const
  · apply Eventually.of_forall
    intro z
    split_ifs with hz
    · simpa only [Real.norm_eq_abs] using hz
    · simpa using hB

/-- If [the score is square-integrable](hyp:hf), then [its average over the supplied number of iid draws is square-integrable under their product law](goal). -/
-- @node: score_iid_average_memLp
lemma score_iid_average_memLp {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (m : ℕ) {f : Ω → ℝ}
    (hf : MemLp f 2 P) :
    MemLp (fun z : Fin m → Ω => (m : ℝ)⁻¹ * ∑ i, f (z i)) 2
      (Measure.pi fun _ : Fin m => P) := by
  apply MemLp.const_mul
  exact memLp_finset_sum Finset.univ fun i _ =>
    hf.comp_measurePreserving (measurePreserving_eval (fun _ : Fin m => P) i)

/-- If [the iid sample size is positive](hyp:hm), [the score is square-integrable](hyp:hf), and [the failure probability is positive](hyp:hd), then [the iid sample mean deviates from its population mean beyond its variance-based radius with probability at most one quarter of that probability](goal). -/
-- @node: score_iid_variance_failure
lemma score_iid_variance_failure {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {m : ℕ} (hm : 0 < m)
    {f : Ω → ℝ} (hf : MemLp f 2 P) {delta : ℝ} (hd : 0 < delta) :
    (Measure.pi fun _ : Fin m => P).real {z |
      Real.sqrt (4 * variance f P / (delta * m)) <
        |(m : ℝ)⁻¹ * ∑ i, f (z i) - ∫ w, f w ∂P|} ≤ delta / 4 := by
  have hmean := Causalean.Mathlib.Probability.iid_average_integral P m hm f
    (hf.integrable (by norm_num))
  have hvar := Causalean.Mathlib.Probability.iid_average_variance P m f hf
  have h := score_sampling_chebyshev (Measure.pi fun _ : Fin m => P)
    (score_iid_average_memLp P m hf)
    (v := (m : ℝ)⁻¹ * variance f P)
    (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg m)) (variance_nonneg f P)) hvar.le hd
  have heq : 4 * ((m : ℝ)⁻¹ * variance f P) / delta =
      4 * variance f P / (delta * m) := by ring
  simpa only [hmean, heq] using h

/-- If [the iid sample size is positive](hyp:hm), [the score is measurable](hyp:hf), [the truncation level is nonnegative](hyp:hB), and [the failure probability is positive](hyp:hd), then [the bounded-score sample mean exceeds its second-moment radius with probability at most one quarter of that probability](goal). -/
-- @node: score_iid_truncation_failure
lemma score_iid_truncation_failure {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {m : ℕ} (hm : 0 < m)
    {f : Ω → ℝ} (hf : Measurable f) {B delta : ℝ} (hB : 0 ≤ B) (hd : 0 < delta) :
    (Measure.pi fun _ : Fin m => P).real {z |
      Real.sqrt (4 * (∫ w, if |f w| ≤ B then (f w)^2 else 0 ∂P) / (delta * m)) <
        |(m : ℝ)⁻¹ * ∑ i, (if |f (z i)| ≤ B then f (z i) else 0) -
          ∫ w, if |f w| ≤ B then f w else 0 ∂P|} ≤ delta / 4 := by
  let F : Ω → ℝ := fun w => if |f w| ≤ B then f w else 0
  have hF := score_truncation_memLp P hf hB
  have hv := variance_le_expectation_sq hF.aestronglyMeasurable
  have hmoment : (∫ w, F w ^ 2 ∂P) =
      ∫ w, if |f w| ≤ B then (f w)^2 else 0 ∂P := by
    apply integral_congr_ae
    exact Eventually.of_forall fun w => by simp [F]
  have hmono : Real.sqrt (4 * variance F P / (delta * m)) ≤
      Real.sqrt (4 * (∫ w, if |f w| ≤ B then (f w)^2 else 0 ∂P) / (delta * m)) := by
    apply Real.sqrt_le_sqrt
    rw [← hmoment]
    gcongr
    exact hv
  apply (measureReal_mono (μ := Measure.pi fun _ : Fin m => P)
    (fun z hz => lt_of_le_of_lt hmono hz)).trans
  exact score_iid_variance_failure P hm hF hd

/-- If [the iid sample size is positive](hyp:hm), [the score is integrable](hyp:hf), and [the failure probability is positive](hyp:hd), then [the average contribution from observations above the supplied cutoff is too large with probability at most one quarter of that probability](goal). -/
-- @node: score_iid_tail_failure
lemma score_iid_tail_failure {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {m : ℕ} (hm : 0 < m)
    {f : Ω → ℝ} (hf : Integrable f P) (B : ℝ) {delta : ℝ} (hd : 0 < delta) :
    (Measure.pi fun _ : Fin m => P).real {z |
      (4 / delta) * (∫ w, if B < |f w| then |f w| else 0 ∂P) <
        (m : ℝ)⁻¹ * ∑ i, (if B < |f (z i)| then |f (z i)| else 0)} ≤ delta / 4 := by
  let F : Ω → ℝ := fun w => if B < |f w| then |f w| else 0
  have hF : Integrable F P := by
    first | fun_prop | skip
    exact hf.abs.indicator₀ (hf.abs.aemeasurable.nullMeasurable measurableSet_Ioi)
  have hAv : Integrable (fun z : Fin m → Ω => (m : ℝ)⁻¹ * ∑ i, F (z i))
      (Measure.pi fun _ : Fin m => P) := by
    apply Integrable.const_mul
    exact integrable_finset_sum Finset.univ fun i _ => integrable_comp_eval hF
  have hpos : ∀ z : Fin m → Ω, 0 ≤ (m : ℝ)⁻¹ * ∑ i, F (z i) := by
    intro z
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg fun i _ => by dsimp [F]; split_ifs <;> positivity
  have h := score_sampling_markov (Measure.pi fun _ : Fin m => P) hAv
    (Eventually.of_forall hpos) hd
  rw [Causalean.Mathlib.Probability.iid_average_integral P m hm F hF] at h
  exact h

/-- If [the iid sample size is positive](hyp:hm), [the score is measurable](hyp:hf), [it is integrable](hyp:hInt), [the cutoff is nonnegative](hyp:hB), and [the failure probability is positive](hyp:hd), then [the full sample mean exceeds the combined truncated sampling bound with probability at most half that probability](goal).

Combining the bounded and tail failures gives the paper's truncation display. -/
-- @node: score_iid_truncated_failure
lemma score_iid_truncated_failure {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {m : ℕ} (hm : 0 < m)
    {f : Ω → ℝ} (hf : Measurable f) (hInt : Integrable f P)
    {B delta : ℝ} (hB : 0 ≤ B) (hd : 0 < delta) :
    (Measure.pi fun _ : Fin m => P).real {z |
      Real.sqrt (4 * (∫ w, if |f w| ≤ B then (f w)^2 else 0 ∂P) / (delta * m)) +
          (1 + 4 / delta) * (∫ w, if B < |f w| then |f w| else 0 ∂P) <
        |(m : ℝ)⁻¹ * ∑ i, f (z i) - ∫ w, f w ∂P|} ≤ delta / 2 := by
  let Q := Measure.pi fun _ : Fin m => P
  let v := ∫ w, if |f w| ≤ B then (f w)^2 else 0 ∂P
  let a := ∫ w, if B < |f w| then |f w| else 0 ∂P
  let S : Set (Fin m → Ω) := {z | Real.sqrt (4 * v / (delta * m)) <
    |(m : ℝ)⁻¹ * ∑ i, (if |f (z i)| ≤ B then f (z i) else 0) -
      ∫ w, if |f w| ≤ B then f w else 0 ∂P|}
  let T : Set (Fin m → Ω) := {z | (4 / delta) * a <
    (m : ℝ)⁻¹ * ∑ i, (if B < |f (z i)| then |f (z i)| else 0)}
  have hs : Integrable (fun w => if |f w| ≤ B then f w else 0) P := by
    first | fun_prop | skip
    exact (score_truncation_memLp P hf hB).integrable (by norm_num)
  have hl : Integrable (fun w => if B < |f w| then f w else 0) P := by
    first | fun_prop | skip
    have habs : Measurable (fun w => |f w|) := by fun_prop
    exact hInt.indicator (measurableSet_lt measurable_const habs)
  have hsubset : {z | Real.sqrt (4 * v / (delta * m)) + (1 + 4 / delta) * a <
      |(m : ℝ)⁻¹ * ∑ i, f (z i) - ∫ w, f w ∂P|} ⊆ S ∪ T := by
    intro z hz
    by_contra hnot
    have hnotS : z ∉ S := fun h => hnot (Or.inl h)
    have hnotT : z ∉ T := fun h => hnot (Or.inr h)
    change ¬ Real.sqrt (4 * v / (delta * m)) <
      |(m : ℝ)⁻¹ * ∑ i, (if |f (z i)| ≤ B then f (z i) else 0) -
        ∫ w, if |f w| ≤ B then f w else 0 ∂P| at hnotS
    change ¬ (4 / delta) * a < (m : ℝ)⁻¹ * ∑ i,
      (if B < |f (z i)| then |f (z i)| else 0) at hnotT
    have hsmall := le_of_not_gt hnotS
    have hlarge := le_of_not_gt hnotT
    have hbound := truncated_average_error_bound P f B Finset.univ z (m : ℝ)⁻¹
      (Real.sqrt (4 * v / (delta * m))) ((4 / delta) * a) (by positivity)
      hs hl hsmall hlarge
    have heq : Real.sqrt (4 * v / (delta * m)) + (4 / delta) * a + a =
        Real.sqrt (4 * v / (delta * m)) + (1 + 4 / delta) * a := by ring
    rw [heq] at hbound
    exact (not_lt_of_ge hbound) hz
  calc
    _ ≤ Q.real (S ∪ T) := measureReal_mono (h₂ := measure_ne_top Q _) hsubset
    _ ≤ Q.real S + Q.real T := measureReal_union_le S T
    _ ≤ delta / 4 + delta / 4 := add_le_add
      (score_iid_truncation_failure P hm hf hB hd) (score_iid_tail_failure P hm hInt B hd)
    _ = delta / 2 := by ring

/-- [The frozen-fit sampling radius](goal) for [a distribution](hyp:mu), [a score](hyp:f), [a sample size](hyp:m), [a cutoff](hyp:B), and [a failure probability](hyp:delta) is the sum of its truncated second-moment and tail-moment terms. -/
-- @node: scoreSamplingRadius
noncomputable def scoreSamplingRadius {Z : Type*} [MeasurableSpace Z]
    (mu : Measure Z) (f : Z → ℝ) (m : ℕ) (B delta : ℝ) : ℝ :=
  Real.sqrt (4 * (∫ z, if |f z| ≤ B then (f z)^2 else 0 ∂mu) / (delta * m)) +
    (1 + 4 / delta) * (∫ z, if B < |f z| then |f z| else 0 ∂mu)

/-- [The frozen-fit iid failure probability](goal) for [a distribution](hyp:mu), [a score](hyp:f), [a sample size](hyp:m), [a cutoff](hyp:B), and [a failure probability](hyp:delta) is the product-law probability that the sample mean misses its population mean by more than the sampling radius. -/
-- @node: scoreIidFailure
noncomputable def scoreIidFailure {Z : Type*} [MeasurableSpace Z]
    (mu : Measure Z) (f : Z → ℝ) (m : ℕ) (B delta : ℝ) : ℝ :=
  (Measure.pi fun _ : Fin m => mu).real {z |
    scoreSamplingRadius mu f m B delta < |(m : ℝ)⁻¹ * ∑ i, f (z i) - ∫ z, f z ∂mu|}

/-- If [the count event is measurable](hyp:hN), [the failure probability is positive](hyp:hd), [the good event has probability at least one minus a quarter of it](hyp:hGprob), [the count event has the same probability bound](hyp:hNprob), [counts are positive on that event](hyp:hm), [cutoffs are nonnegative](hyp:hB), [scores are measurable and integrable on the good event almost surely](hyp:hf), [the accuracy event is measurable](hyp:hR), and [its conditional-law failure probability transfers to the iid bound](hyp:hTransfer), then [the good, count, and accuracy events occur jointly with probability at least one minus the failure probability](goal).

The transfer inequality is the remaining conditional-law obligation, not an assumption on the population model. -/
-- @node: score_sampling_probability_of_transfer_ae
lemma score_sampling_probability_of_transfer_ae {Ω Z : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Z]
    (P : Measure Ω) [IsProbabilityMeasure P] (mu : Measure Z) [IsProbabilityMeasure mu]
    (f : Ω → Z → ℝ) (m : Ω → ℕ) (B estimate : Ω → ℝ)
    (G N : Set Ω) (hN : MeasurableSet N) {delta : ℝ} (hd : 0 < delta)
    (hGprob : 1 - delta / 4 ≤ P.real G) (hNprob : 1 - delta / 4 ≤ P.real N)
    (hm : ∀ w ∈ N, 0 < m w) (hB : ∀ w, 0 ≤ B w)
    (hf : ∀ᵐ w ∂P, w ∈ G → Measurable (f w) ∧ Integrable (f w) mu)
    (hR : MeasurableSet {w | |estimate w - ∫ z, f w z ∂mu| ≤
      scoreSamplingRadius mu (f w) (m w) (B w) delta})
    (hTransfer : P.real ((G ∩ N) \ {w | |estimate w - ∫ z, f w z ∂mu| ≤
        scoreSamplingRadius mu (f w) (m w) (B w) delta}) ≤
      ∫ w, if w ∈ G ∩ N then scoreIidFailure mu (f w) (m w) (B w) delta else 0 ∂P) :
    1 - delta ≤ P.real ((G ∩ N) ∩ {w | |estimate w - ∫ z, f w z ∂mu| ≤
      scoreSamplingRadius mu (f w) (m w) (B w) delta}) := by
  have hGN := probability_intersection_lower P G N hN hGprob hNprob
  have hbound : ∀ᵐ w ∂P,
      ‖if w ∈ G ∩ N then scoreIidFailure mu (f w) (m w) (B w) delta else 0‖ ≤
        delta / 2 := by
    filter_upwards [hf] with w hfw
    split_ifs with hw
    · have hnonneg : 0 ≤ scoreIidFailure mu (f w) (m w) (B w) delta :=
        ENNReal.toReal_nonneg
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      exact score_iid_truncated_failure mu (hm w hw.2) (hfw hw.1).1
        (hfw hw.1).2 (hB w) hd
    · simp only [norm_zero]
      positivity
  have hInt := norm_integral_le_of_norm_le_const hbound
  simp only [Real.norm_eq_abs, probReal_univ, mul_one] at hInt
  have hbad := hTransfer.trans ((le_abs_self _).trans hInt)
  have hsplit := measureReal_inter_add_sdiff (μ := P) (s := G ∩ N) hR
  linarith

/-- If [the count event is measurable](hyp:hN), [the failure probability is positive](hyp:hd), [the good and count events each have probability at least one minus a quarter of it](hyp:hGprob,hNprob), [counts are positive on the count event](hyp:hm), [cutoffs are nonnegative](hyp:hB), [scores are measurable and integrable on the good event](hyp:hf), [the accuracy event is measurable](hyp:hR), and [its failure transfers to the iid law](hyp:hTransfer), then [all three events occur jointly with probability at least one minus the failure probability](goal). -/
-- @node: score_sampling_probability_of_transfer
lemma score_sampling_probability_of_transfer {Ω Z : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Z]
    (P : Measure Ω) [IsProbabilityMeasure P] (mu : Measure Z) [IsProbabilityMeasure mu]
    (f : Ω → Z → ℝ) (m : Ω → ℕ) (B estimate : Ω → ℝ)
    (G N : Set Ω) (hN : MeasurableSet N) {delta : ℝ} (hd : 0 < delta)
    (hGprob : 1 - delta / 4 ≤ P.real G) (hNprob : 1 - delta / 4 ≤ P.real N)
    (hm : ∀ w ∈ N, 0 < m w) (hB : ∀ w, 0 ≤ B w)
    (hf : ∀ w ∈ G, Measurable (f w) ∧ Integrable (f w) mu)
    (hR : MeasurableSet {w | |estimate w - ∫ z, f w z ∂mu| ≤
      scoreSamplingRadius mu (f w) (m w) (B w) delta})
    (hTransfer : P.real ((G ∩ N) \ {w | |estimate w - ∫ z, f w z ∂mu| ≤
        scoreSamplingRadius mu (f w) (m w) (B w) delta}) ≤
      ∫ w, if w ∈ G ∩ N then scoreIidFailure mu (f w) (m w) (B w) delta else 0 ∂P) :
    1 - delta ≤ P.real ((G ∩ N) ∩ {w | |estimate w - ∫ z, f w z ∂mu| ≤
      scoreSamplingRadius mu (f w) (m w) (B w) delta}) := by
  exact score_sampling_probability_of_transfer_ae P mu f m B estimate G N hN hd
    hGprob hNprob hm hB (Eventually.of_forall hf) hR hTransfer

/-- [The finite-variance iid failure probability](goal) for [a distribution](hyp:mu), [a score](hyp:f), [a sample size](hyp:m), and [a failure probability](hyp:delta) is the chance that its sample mean exceeds the variance-based radius. -/
-- @node: scoreIidVarianceFailure
noncomputable def scoreIidVarianceFailure {Z : Type*} [MeasurableSpace Z]
    (mu : Measure Z) (f : Z → ℝ) (m : ℕ) (delta : ℝ) : ℝ :=
  (Measure.pi fun _ : Fin m => mu).real {z |
    Real.sqrt (4 * variance f mu / (delta * m)) <
      |(m : ℝ)⁻¹ * ∑ i, f (z i) - ∫ z, f z ∂mu|}

/-- If [the count event is measurable](hyp:hN), [the failure probability is positive](hyp:hd), [the good event has probability at least one minus a quarter of it](hyp:hGprob), [the count event has the same probability bound](hyp:hNprob), [counts are positive there](hyp:hm), [scores are square-integrable on the good event almost surely](hyp:hf), [the variance-radius event is measurable](hyp:hR), and [its conditional-law failure transfers to the iid bound](hyp:hTransfer), then [the good, count, and variance-radius events occur jointly with probability at least one minus the failure probability](goal).

Nuisance and count failures need not be independent. -/
-- @node: score_variance_probability_of_transfer_ae
lemma score_variance_probability_of_transfer_ae {Ω Z : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Z]
    (P : Measure Ω) [IsProbabilityMeasure P] (mu : Measure Z) [IsProbabilityMeasure mu]
    (f : Ω → Z → ℝ) (m : Ω → ℕ) (estimate : Ω → ℝ)
    (G N : Set Ω) (hN : MeasurableSet N) {delta : ℝ} (hd : 0 < delta)
    (hGprob : 1 - delta / 4 ≤ P.real G) (hNprob : 1 - delta / 4 ≤ P.real N)
    (hm : ∀ w ∈ N, 0 < m w)
    (hf : ∀ᵐ w ∂P, w ∈ G → MemLp (f w) 2 mu)
    (hR : MeasurableSet {w | |estimate w - ∫ z, f w z ∂mu| ≤
      Real.sqrt (4 * variance (f w) mu / (delta * m w))})
    (hTransfer : P.real ((G ∩ N) \ {w | |estimate w - ∫ z, f w z ∂mu| ≤
        Real.sqrt (4 * variance (f w) mu / (delta * m w))}) ≤
      ∫ w, if w ∈ G ∩ N then scoreIidVarianceFailure mu (f w) (m w) delta else 0 ∂P) :
    1 - delta ≤ P.real ((G ∩ N) ∩ {w | |estimate w - ∫ z, f w z ∂mu| ≤
      Real.sqrt (4 * variance (f w) mu / (delta * m w))}) := by
  have hGN := probability_intersection_lower P G N hN hGprob hNprob
  have hbound : ∀ᵐ w ∂P,
      ‖if w ∈ G ∩ N then scoreIidVarianceFailure mu (f w) (m w) delta else 0‖ ≤
        delta / 4 := by
    filter_upwards [hf] with w hfw
    split_ifs with hw
    · have hnonneg : 0 ≤ scoreIidVarianceFailure mu (f w) (m w) delta :=
        ENNReal.toReal_nonneg
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      exact score_iid_variance_failure mu (hm w hw.2) (hfw hw.1) hd
    · simp only [norm_zero]
      positivity
  have hInt := norm_integral_le_of_norm_le_const hbound
  simp only [Real.norm_eq_abs, probReal_univ, mul_one] at hInt
  have hbad := hTransfer.trans ((le_abs_self _).trans hInt)
  have hsplit := measureReal_inter_add_sdiff (μ := P) (s := G ∩ N) hR
  linarith

variable {q d : ℕ} {M : ExtremeModel q d}

/-- [Each frozen fitted score is measurable as a function of a new observation](goal). -/
-- @node: measurable_score_frozen
@[fun_prop] lemma measurable_score_frozen (E : NeteExperiment M)
    (kind : EstimatorKind) (n : ℕ) (w : E.Om) : Measurable (score E kind n w) := by
  first | fun_prop | skip
  have hdir : Measurable (obsDirection (q := q) (d := d)) := by
    unfold obsDirection
    fun_prop
  have hp : Measurable (fun z : Obs q d => E.pHat n w z.1) :=
    (E.pHat_training n).comp (measurable_const.prodMk measurable_fst)
  have hg (a : Obs q d → Bool) (ha : Measurable a) :
      Measurable (fun z : Obs q d => E.gHat n w z.1 (a z) (obsDirection z)) :=
    (E.gHat_training n).comp (measurable_const.prodMk
      (measurable_fst.prodMk (ha.prodMk hdir)))
  have hY : Measurable (pseudoOutcome E n w) := by
    unfold pseudoOutcome
    fun_prop
  have hD1 : Measurable (fun z : Obs q d => if z.2.1 then (1 : ℝ) else 0) :=
    (measurable_of_finite (fun b : Bool => if b then (1 : ℝ) else 0)).comp
      (measurable_fst.comp measurable_snd)
  have hD0 : Measurable (fun z : Obs q d => if z.2.1 then (0 : ℝ) else 1) :=
    (measurable_of_finite (fun b : Bool => if b then (0 : ℝ) else 1)).comp
      (measurable_fst.comp measurable_snd)
  cases kind
  · exact hY.mul ((hD1.div hp).sub (hD0.div (measurable_const.sub hp)))
  · exact ((hg (fun _ => true) measurable_const).sub (hg (fun _ => false) measurable_const)).add
      (((hD1.sub hp).div (hp.mul (measurable_const.sub hp))).mul
        (hY.sub (hg (fun z => z.2.1) (measurable_fst.comp measurable_snd))))

/-- If [the model has regularly varying noise](hyp:hRV), then [its observation tail law at the supplied threshold is a probability measure](goal). -/
-- @node: obsTailLaw_probability
lemma obsTailLaw_probability (M : ExtremeModel q d) (hRV : NoiseRegularlyVarying M)
    (t : ℝ) : IsProbabilityMeasure (obsTailLaw M t) := by
  have hObs : Measurable (observation M) := by
    first | fun_prop | skip
    exact M.measurable_X.prodMk (M.measurable_D.prodMk
      (M.measurable_Y.prodMk M.measurable_U))
  have hA : MeasurableSet {z : Obs q d | t < l1Norm z.2.2.2} := by
    apply measurableSet_lt measurable_const
    fun_prop
  apply cond_isProbabilityMeasure
  rw [Measure.map_apply hObs hA]
  intro hz
  have hpos := tailProb_pos_of_regularVariation M hRV t
  change M.mu {w | t < radius M w} = 0 at hz
  simp only [tailProb, hz, ENNReal.toReal_zero] at hpos
  exact (lt_irrefl 0) hpos

/-- [The DR truncated-law transfer condition](goal) for [a model](hyp:M), [an experiment](hyp:E), [a sample size](hyp:n), [the threshold, failure probability, and constants](hyp:t,delta,c,Cgb,K), [the nuisance-rate functions](hyp:Rp,Rg,Ralpha), [a cutoff](hyp:B), and [a count event](hyp:N) requires a good event with score integrability, a score-mean remainder bound, measurability of the accuracy event, and conditional-law transfer of its iid failure probability.

Concentration and confidence assembly are proved from these obligations below. -/
-- @node: DrTruncatedLawTransfer
noncomputable def DrTruncatedLawTransfer (E : NeteExperiment M)
    (n : ℕ) (t delta c Cgb K : ℝ) (Rp Rg Ralpha : ℕ → ℝ → ℝ)
    (B : E.Om → ℝ) (N : Set E.Om) : Prop :=
  let R := {w | |etaEstimate E .dr n t w - ∫ z, score E .dr n w z ∂obsTailLaw M t| ≤
    scoreSamplingRadius (obsTailLaw M t) (score E .dr n w) (evalCount E n t w) (B w) delta}
  ∃ G : Set E.Om, 1 - delta / 4 ≤ E.P.real G ∧
    (∀ w ∈ G, Integrable (score E .dr n w) (obsTailLaw M t)) ∧
    (∀ w ∈ G, |(∫ z, score E .dr n w z ∂obsTailLaw M t) - etaTarget M| ≤
      etaRemainder E .dr c Cgb K Rp Rg Ralpha n t (delta / 4) w) ∧
    MeasurableSet R ∧
    E.P.real ((G ∩ N) \ R) ≤ ∫ w, if w ∈ G ∩ N then
      scoreIidFailure (obsTailLaw M t) (score E .dr n w) (evalCount E n t w) (B w) delta
      else 0 ∂E.P

/-- If [the model has regularly varying noise](hyp:hRV), [the failure probability is positive](hyp:hd), [the cutoff is everywhere positive](hyp:hB), [the count event is measurable](hyp:hN), [it has probability at least one minus a quarter of the failure probability](hyp:hNprob), [it supplies enough nonzero evaluation observations](hyp:hNcount), and [the DR conditional-law transfer condition holds](hyp:h), then [the count and displayed truncated DR error bound hold jointly with probability at least one minus the failure probability](goal).

No probability bound for the sampling events is left to assume. -/
-- @node: dr_truncated_probability_of_transfer
lemma dr_truncated_probability_of_transfer (E : NeteExperiment M)
    (hRV : NoiseRegularlyVarying M) (n : ℕ) (t delta c Cgb K : ℝ)
    (Rp Rg Ralpha : ℕ → ℝ → ℝ) (B : E.Om → ℝ) (N : Set E.Om)
    (hd : 0 < delta) (hB : ∀ w, 0 < B w) (hN : MeasurableSet N)
    (hNprob : 1 - delta / 4 ≤ E.P.real N)
    (hNcount : ∀ w ∈ N, (n : ℝ) * tailProb M t / 4 ≤ (evalCount E n t w : ℝ) ∧
      evalCount E n t w ≠ 0)
    (h : DrTruncatedLawTransfer E n t delta c Cgb K Rp Rg Ralpha B N) :
    1 - delta ≤ E.P.real {w | (n : ℝ) * tailProb M t / 4 ≤ evalCount E n t w ∧
      |etaEstimate E .dr n t w - etaTarget M| ≤
        etaTruncatedError E .dr c Cgb K Rp Rg Ralpha n t delta B w} := by
  let := obsTailLaw_probability M hRV t
  obtain ⟨G, hGprob, hf, hMean, hR, hTransfer⟩ := h
  have hprob := score_sampling_probability_of_transfer E.P (obsTailLaw M t)
    (fun w => score E .dr n w) (evalCount E n t) B (etaEstimate E .dr n t)
    G N hN hd hGprob hNprob (fun w hw => Nat.pos_of_ne_zero (hNcount w hw).2)
    (fun w => (hB w).le) (fun w hw => ⟨measurable_score_frozen E .dr n w, hf w hw⟩)
    hR hTransfer
  apply hprob.trans
  apply measureReal_mono (h₂ := measure_ne_top E.P _)
  intro w hw
  refine ⟨(hNcount w hw.1.2).1, ?_⟩
  calc
    _ ≤ |etaEstimate E .dr n t w - ∫ z, score E .dr n w z ∂obsTailLaw M t| +
        |(∫ z, score E .dr n w z ∂obsTailLaw M t) - etaTarget M| := abs_sub_le _ _ _
    _ ≤ scoreSamplingRadius (obsTailLaw M t) (score E .dr n w)
        (evalCount E n t w) (B w) delta +
        etaRemainder E .dr c Cgb K Rp Rg Ralpha n t (delta / 4) w :=
      add_le_add hw.2 (hMean w hw.1.1)
    _ = _ := rfl

end Papers.TbsExtremeEffects

module
public import Papers.TbsExtremeEffects.Helpers.AngularDual
public import Papers.TbsExtremeEffects.Helpers.ScoreMoments
public import Papers.TbsExtremeEffects.Helpers.ScoreIntegrability
public import Papers.TbsExtremeEffects.Helpers.EtaDR
public import Papers.TbsExtremeEffects.Helpers.IPWOutcomeMean
public import Papers.TbsExtremeEffects.Helpers.TrainingScore

/-! The IPW first-factor bound, including the untruncated variance alternative. -/

@[expose] public section
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.unusedVariables false
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology Classical
variable {q d m : ℕ}

variable {M : ExtremeModel q d}

-- @node: ipw_truncated_bound_of_components
/-- If [the evaluation count is nonzero](hyp:hcount), [the truncated score is integrable](hyp:hs), [the discarded score tail is integrable](hyp:hl), [the truncated empirical average is accurate](hyp:hsmall), [the empirical tail is controlled](hyp:hlarge), and [the score mean is close to the target](hyp:hmean), then [the IPW estimate has the stated truncated-error bound](goal). -/
lemma ipw_truncated_bound_of_components (E : NeteExperiment M)
    (n : ℕ) (t delta c Cgb K : ℝ) (Rp Rg Ralpha : ℕ → ℝ → ℝ)
    (B : E.Om → ℝ) (w : E.Om) (hcount : evalCount E n t w ≠ 0)
    (hs : Integrable (fun z => if |score E .ipw n w z| ≤ B w then score E .ipw n w z
      else 0) (obsTailLaw M t))
    (hl : Integrable (fun z => if B w < |score E .ipw n w z| then score E .ipw n w z
      else 0) (obsTailLaw M t))
    (hsmall : |(evalCount E n t w : ℝ)⁻¹ * ∑ i ∈ evalSet E n t w,
      (if |score E .ipw n w (obs E n w i)| ≤ B w then score E .ipw n w (obs E n w i)
        else 0) - ∫ z, if |score E .ipw n w z| ≤ B w then score E .ipw n w z else 0
          ∂obsTailLaw M t| ≤
      Real.sqrt (4 * truncatedSecondMoment E .ipw n t B w / (delta * evalCount E n t w)))
    (hlarge : (evalCount E n t w : ℝ)⁻¹ * ∑ i ∈ evalSet E n t w,
      (if B w < |score E .ipw n w (obs E n w i)| then |score E .ipw n w (obs E n w i)|
        else 0) ≤ (4 / delta) * scoreTailMoment E .ipw n t B w)
    (hmean : |(∫ z, score E .ipw n w z ∂obsTailLaw M t) - etaTarget M| ≤
      etaRemainder E .ipw c Cgb K Rp Rg Ralpha n t (delta / 4) w) :
    |etaEstimate E .ipw n t w - etaTarget M| ≤
      etaTruncatedError E .ipw c Cgb K Rp Rg Ralpha n t delta B w := by
  have hsample := truncated_average_error_bound (obsTailLaw M t) (score E .ipw n w)
    (B w) (evalSet E n t w) (obs E n w) (evalCount E n t w : ℝ)⁻¹
    (Real.sqrt (4 * truncatedSecondMoment E .ipw n t B w / (delta * evalCount E n t w)))
    ((4 / delta) * scoreTailMoment E .ipw n t B w) (by positivity) hs hl hsmall hlarge
  change |etaIPW E n t w - etaTarget M| ≤ _
  rw [etaIPW, if_neg hcount]
  change |(evalCount E n t w : ℝ)⁻¹ * ∑ i ∈ evalSet E n t w,
    score E .ipw n w (obs E n w i) - etaTarget M| ≤ _
  calc
    _ ≤ |(evalCount E n t w : ℝ)⁻¹ * ∑ i ∈ evalSet E n t w,
        score E .ipw n w (obs E n w i) - ∫ z, score E .ipw n w z ∂obsTailLaw M t| +
        |(∫ z, score E .ipw n w z ∂obsTailLaw M t) - etaTarget M| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add hsample hmean
    _ = _ := by unfold etaTruncatedError scoreTailMoment; ring

-- @node: ipw_variance_bound_of_components
/-- If [the empirical IPW estimate is close to its score mean at the variance radius](hyp:hsample) and [that score mean is close to the target](hyp:hmean), then [the estimation error is at most the variance radius plus the remainder](goal). -/
lemma ipw_variance_bound_of_components (E : NeteExperiment M)
    (n : ℕ) (t delta c Cgb K : ℝ) (Rp Rg Ralpha : ℕ → ℝ → ℝ) (w : E.Om)
    (hsample : |etaEstimate E .ipw n t w -
      ∫ z, score E .ipw n w z ∂obsTailLaw M t| ≤
        Real.sqrt (4 * (scoreVariance E .ipw n t w).toReal / (delta * evalCount E n t w)))
    (hmean : |(∫ z, score E .ipw n w z ∂obsTailLaw M t) - etaTarget M| ≤
      etaRemainder E .ipw c Cgb K Rp Rg Ralpha n t (delta / 4) w) :
    (fun err V delta count remainder : ℝ =>
        err ≤ Real.sqrt (4 * V / (delta * count)) + remainder) |etaEstimate E .ipw n t w - etaTarget M|
      (scoreVariance E .ipw n t w).toReal delta (evalCount E n t w)
      (etaRemainder E .ipw c Cgb K Rp Rg Ralpha n t (delta / 4) w) := by
  exact (abs_sub_le _ (∫ z, score E .ipw n w z ∂obsTailLaw M t) _).trans
    (add_le_add hsample hmean)

-- @node: IpwTruncatedEventCertificate
/-- [The truncated-event certificate](goal), for [the experiment](hyp:E), [sample size](hyp:n), [threshold and confidence constants](hyp:t,delta,c,Cgb,K), [nuisance-rate functions](hyp:Rp,Rg,Ralpha), and [random truncation level](hyp:B), says that four high-probability measurable events jointly ensure a positive evaluation count, the needed integrability, truncated and tail empirical bounds, and a mean remainder bound [in its sole certificate clause](step:1). -/
def IpwTruncatedEventCertificate (E : NeteExperiment M)
    (n : ℕ) (t delta c Cgb K : ℝ) (Rp Rg Ralpha : ℕ → ℝ → ℝ) (B : E.Om → ℝ) : Prop :=
  ∃ S : Fin 4 → Set E.Om, (∀ i, MeasurableSet (S i)) ∧
    (∀ i, 1 - delta / 4 ≤ E.P.real (S i)) ∧
    ∀ w, (∀ i, w ∈ S i) →
      (n : ℝ) * tailProb M t / 4 ≤ evalCount E n t w ∧
      evalCount E n t w ≠ 0 ∧
      Integrable (fun z => if |score E .ipw n w z| ≤ B w then score E .ipw n w z
        else 0) (obsTailLaw M t) ∧
      Integrable (fun z => if B w < |score E .ipw n w z| then score E .ipw n w z
        else 0) (obsTailLaw M t) ∧
      |(evalCount E n t w : ℝ)⁻¹ * ∑ i ∈ evalSet E n t w,
        (if |score E .ipw n w (obs E n w i)| ≤ B w then score E .ipw n w (obs E n w i)
          else 0) - ∫ z, if |score E .ipw n w z| ≤ B w then score E .ipw n w z else 0
            ∂obsTailLaw M t| ≤
        Real.sqrt (4 * truncatedSecondMoment E .ipw n t B w / (delta * evalCount E n t w)) ∧
      (evalCount E n t w : ℝ)⁻¹ * ∑ i ∈ evalSet E n t w,
        (if B w < |score E .ipw n w (obs E n w i)| then |score E .ipw n w (obs E n w i)|
          else 0) ≤ (4 / delta) * scoreTailMoment E .ipw n t B w ∧
      |(∫ z, score E .ipw n w z ∂obsTailLaw M t) - etaTarget M| ≤
        etaRemainder E .ipw c Cgb K Rp Rg Ralpha n t (delta / 4) w

-- @node: ipw_truncated_probability_of_certificate
/-- If [a truncated-event certificate is available](hyp:h), then [the event on which the evaluation count is large enough and the IPW error obeys its truncated bound has probability at least `1 - delta`](goal). -/
lemma ipw_truncated_probability_of_certificate (E : NeteExperiment M)
    (n : ℕ) (t delta c Cgb K : ℝ) (Rp Rg Ralpha : ℕ → ℝ → ℝ) (B : E.Om → ℝ)
    (h : IpwTruncatedEventCertificate E n t delta c Cgb K Rp Rg Ralpha B) :
    1 - delta ≤ E.P.real {w | (n : ℝ) * tailProb M t / 4 ≤ evalCount E n t w ∧
      |etaEstimate E .ipw n t w - etaTarget M| ≤
        etaTruncatedError E .ipw c Cgb K Rp Rg Ralpha n t delta B w} := by
  obtain ⟨S, hmeas, hprob, hpoint⟩ := h
  apply probability_four_events_imp E.P S hmeas hprob
  intro w hw
  obtain ⟨hcount, hnonzero, hs, hl, hsmall, hlarge, hmean⟩ := hpoint w hw
  exact ⟨hcount, ipw_truncated_bound_of_components E n t delta c Cgb K Rp Rg Ralpha B w
    hnonzero hs hl hsmall hlarge hmean⟩

/-- [The truncated conditional-law transfer](goal), for [the experiment](hyp:E), [sample size](hyp:n), [threshold and confidence level](hyp:t,delta), [random truncation level](hyp:B), and [training and count events](hyp:G,N), bounds the probability of leaving the sampling-radius event by the corresponding conditional iid failure probability [after defining that sampling-radius event](step:1).

The outcome-mean identity is derived during the probability assembly. -/
-- @node: IpwTruncatedConditionalLaw
noncomputable def IpwTruncatedConditionalLaw (E : NeteExperiment M)
    (n : ℕ) (t delta : ℝ) (B : E.Om → ℝ) (G N : Set E.Om) : Prop :=
  let R := {w | |etaEstimate E .ipw n t w - ∫ z, score E .ipw n w z ∂obsTailLaw M t| ≤
    scoreSamplingRadius (obsTailLaw M t) (score E .ipw n w) (evalCount E n t w) (B w) delta}
  E.P.real ((G ∩ N) \ R) ≤ ∫ w, if w ∈ G ∩ N then
      scoreIidFailure (obsTailLaw M t) (score E .ipw n w) (evalCount E n t w) (B w) delta
      else 0 ∂E.P

/-- Under [regularly varying noise](hyp:hRV), [a conditional-mean version](hyp:hCondMean), [an even sample size](hyp:hn), [exponent training](hyp:hTraining), [estimated overlap](hyp:hOverlap), [a measurable truncation level](hyp:hBmeas), [positive confidence level](hyp:hd), [positive truncation levels](hyp:hB), [a measurable count event](hyp:hN), [high-probability training and count events](hyp:hGprob,hNprob), [sufficient nonzero counts on the count event](hyp:hNcount), [nuisance control on the training event](hyp:hNuisance), [pseudo-outcome integrability](hyp:hInt), [a mean-bound provider](hyp:hProvider), [a valid mean decomposition](hyp:hMean), and [the sampling event probability bound](hyp:hSampling), [the count-and-truncated-IPW-error event has probability at least `1 - delta`](goal).

Score integrability is derived from the pseudo-outcome moment rather than imposed separately. -/
-- @node: ipw_truncated_probability_of_sampling_event
lemma ipw_truncated_probability_of_sampling_event (E : NeteExperiment M)
    (hRV : NoiseRegularlyVarying M) (hCondMean : ConditionalMeanVersion M)
    {n : ℕ} (hn : EvenSampleSize n)
    (hTraining : ExponentTraining E n)
    {t delta c Cgb K : ℝ} (hOverlap : EstimatedOverlap E c)
    (Rp Rg Ralpha : ℕ → ℝ → ℝ) (B : E.Om → ℝ) (hBmeas : Measurable B)
    (G N : Set E.Om)
    (reg : ((Fin q → ℝ) × Bool × (Fin d → ℝ)) → ℝ)
    (hd : 0 < delta) (hB : ∀ w, 0 < B w) (hN : MeasurableSet N)
    (hGprob : 1 - delta / 4 ≤ E.P.real G) (hNprob : 1 - delta / 4 ≤ E.P.real N)
    (hNcount : ∀ w ∈ N, (n : ℝ) * tailProb M t / 4 ≤ (evalCount E n t w : ℝ) ∧
      evalCount E n t w ≠ 0)
    (hNuisance : ∀ w ∈ G, NuisanceAt E n t (delta / 4) Rp Rg Ralpha reg w)
    (hInt : FittedPseudoOutcomeIntegrable E n t G)
    (hProvider : IpwMeanBoundProvider E n t (delta / 4) c Cgb K Rp Rg Ralpha)
    (hMean : ∀ w ∈ G, IpwOutcomeScoreMean E n t w → IpwMeanDecomposition E n t w)
    (hSampling : 1 - delta ≤ E.P.real ((G ∩ N) ∩ {w |
      |etaEstimate E .ipw n t w - ∫ z, score E .ipw n w z ∂obsTailLaw M t| ≤
        scoreSamplingRadius (obsTailLaw M t) (score E .ipw n w)
          (evalCount E n t w) (B w) delta})) :
    1 - delta ≤ E.P.real {w | (n : ℝ) * tailProb M t / 4 ≤ evalCount E n t w ∧
      |etaEstimate E .ipw n t w - etaTarget M| ≤
        etaTruncatedError E .ipw c Cgb K Rp Rg Ralpha n t delta B w} := by
  let := obsTailLaw_probability M hRV t
  have hScore := ipw_score_integrable_on_nuisance_event E hn hOverlap hInt
  have hf : ∀ᵐ w ∂E.P, w ∈ G →
      Measurable (score E .ipw n w) ∧ Integrable (score E .ipw n w) (obsTailLaw M t) := by
    filter_upwards [hScore] with w hw hG
    exact ⟨measurable_score_frozen E .ipw n w, hw hG⟩
  apply hSampling.trans
  change (E.P _).toReal ≤ (E.P _).toReal
  apply ENNReal.toReal_mono (measure_ne_top E.P _)
  apply measure_mono_ae
  filter_upwards [hScore] with w hScorew
  intro hw
  have hIdentity := ipw_outcome_score_mean_of_integrable E hRV hCondMean n t w
    (hScorew hw.1.1)
  refine ⟨(hNcount w hw.1.2).1, ?_⟩
  calc
    _ ≤ |etaEstimate E .ipw n t w - ∫ z, score E .ipw n w z ∂obsTailLaw M t| +
        |(∫ z, score E .ipw n w z ∂obsTailLaw M t) - etaTarget M| := abs_sub_le _ _ _
    _ ≤ scoreSamplingRadius (obsTailLaw M t) (score E .ipw n w)
        (evalCount E n t w) (B w) delta +
        etaRemainder E .ipw c Cgb K Rp Rg Ralpha n t (delta / 4) w :=
      add_le_add hw.2 (hProvider reg w (hNuisance w hw.1.1) (hMean w hw.1.1 hIdentity))
    _ = _ := rfl

-- @node: ipw_truncated_probability_of_conditional_law
/-- Under [regularly varying noise](hyp:hRV), [a conditional-mean version](hyp:hCondMean), [an even sample size](hyp:hn), [exponent training](hyp:hTraining), [estimated overlap](hyp:hOverlap), [a measurable truncation level](hyp:hBmeas), [positive confidence level](hyp:hd), [positive truncation levels](hyp:hB), [a measurable count event](hyp:hN), [high-probability training and count events](hyp:hGprob,hNprob), [sufficient nonzero counts](hyp:hNcount), [nuisance control](hyp:hNuisance), [pseudo-outcome integrability](hyp:hInt), [a mean-bound provider](hyp:hProvider), [a valid mean decomposition](hyp:hMean), and [a truncated conditional-law transfer](hyp:hLaw), [the count-and-truncated-IPW-error event has probability at least `1 - delta`](goal). -/
lemma ipw_truncated_probability_of_conditional_law (E : NeteExperiment M)
    (hRV : NoiseRegularlyVarying M) (hCondMean : ConditionalMeanVersion M)
    {n : ℕ} (hn : EvenSampleSize n)
    (hTraining : ExponentTraining E n)
    {t delta c Cgb K : ℝ} (hOverlap : EstimatedOverlap E c)
    (Rp Rg Ralpha : ℕ → ℝ → ℝ) (B : E.Om → ℝ) (hBmeas : Measurable B)
    (G N : Set E.Om)
    (reg : ((Fin q → ℝ) × Bool × (Fin d → ℝ)) → ℝ)
    (hd : 0 < delta) (hB : ∀ w, 0 < B w) (hN : MeasurableSet N)
    (hGprob : 1 - delta / 4 ≤ E.P.real G) (hNprob : 1 - delta / 4 ≤ E.P.real N)
    (hNcount : ∀ w ∈ N, (n : ℝ) * tailProb M t / 4 ≤ (evalCount E n t w : ℝ) ∧
      evalCount E n t w ≠ 0)
    (hNuisance : ∀ w ∈ G, NuisanceAt E n t (delta / 4) Rp Rg Ralpha reg w)
    (hInt : FittedPseudoOutcomeIntegrable E n t G)
    (hProvider : IpwMeanBoundProvider E n t (delta / 4) c Cgb K Rp Rg Ralpha)
    (hMean : ∀ w ∈ G, IpwOutcomeScoreMean E n t w → IpwMeanDecomposition E n t w)
    (hLaw : IpwTruncatedConditionalLaw E n t delta B G N) :
    1 - delta ≤ E.P.real {w | (n : ℝ) * tailProb M t / 4 ≤ evalCount E n t w ∧
      |etaEstimate E .ipw n t w - etaTarget M| ≤
        etaTruncatedError E .ipw c Cgb K Rp Rg Ralpha n t delta B w} := by
  let := obsTailLaw_probability M hRV t
  have hTransfer := hLaw
  have hR := measurableSet_score_truncation_event E .ipw hRV hTraining t delta B hBmeas
  have hScore := ipw_score_integrable_on_nuisance_event E hn hOverlap hInt
  have hf : ∀ᵐ w ∂E.P, w ∈ G →
      Measurable (score E .ipw n w) ∧ Integrable (score E .ipw n w) (obsTailLaw M t) := by
    filter_upwards [hScore] with w hw hG
    exact ⟨measurable_score_frozen E .ipw n w, hw hG⟩
  have hprob := score_sampling_probability_of_transfer_ae E.P (obsTailLaw M t)
    (fun w => score E .ipw n w) (evalCount E n t) B (etaEstimate E .ipw n t)
    G N hN hd hGprob hNprob (fun w hw => Nat.pos_of_ne_zero (hNcount w hw).2)
    (fun w => (hB w).le) hf hR hTransfer
  apply hprob.trans
  change (E.P _).toReal ≤ (E.P _).toReal
  apply ENNReal.toReal_mono (measure_ne_top E.P _)
  apply measure_mono_ae
  filter_upwards [hScore] with w hScorew
  intro hw
  have hIdentity := ipw_outcome_score_mean_of_integrable E hRV hCondMean n t w
    (hScorew hw.1.1)
  refine ⟨(hNcount w hw.1.2).1, ?_⟩
  calc
    _ ≤ |etaEstimate E .ipw n t w - ∫ z, score E .ipw n w z ∂obsTailLaw M t| +
        |(∫ z, score E .ipw n w z ∂obsTailLaw M t) - etaTarget M| := abs_sub_le _ _ _
    _ ≤ scoreSamplingRadius (obsTailLaw M t) (score E .ipw n w)
        (evalCount E n t w) (B w) delta +
        etaRemainder E .ipw c Cgb K Rp Rg Ralpha n t (delta / 4) w :=
      add_le_add hw.2 (hProvider reg w (hNuisance w hw.1.1) (hMean w hw.1.1 hIdentity))
    _ = _ := rfl

-- @node: IpwVarianceEventCertificate
/-- [The variance-event certificate](goal), for [the experiment](hyp:E), [sample size](hyp:n), [threshold and constants](hyp:t,delta,c,Cgb,K), and [nuisance-rate functions](hyp:Rp,Rg,Ralpha), asserts that four high-probability measurable events jointly give a large evaluation count, finite score variance, a variance sampling bound, and a mean remainder bound [in its sole certificate clause](step:1). -/
def IpwVarianceEventCertificate (E : NeteExperiment M)
    (n : ℕ) (t delta c Cgb K : ℝ) (Rp Rg Ralpha : ℕ → ℝ → ℝ) : Prop :=
  ∃ S : Fin 4 → Set E.Om, (∀ i, MeasurableSet (S i)) ∧
    (∀ i, 1 - delta / 4 ≤ E.P.real (S i)) ∧
    ∀ w, (∀ i, w ∈ S i) →
      (n : ℝ) * tailProb M t / 4 ≤ evalCount E n t w ∧
      scoreVariance E .ipw n t w ≠ ∞ ∧
      |etaEstimate E .ipw n t w - ∫ z, score E .ipw n w z ∂obsTailLaw M t| ≤
        Real.sqrt (4 * (scoreVariance E .ipw n t w).toReal / (delta * evalCount E n t w)) ∧
      |(∫ z, score E .ipw n w z ∂obsTailLaw M t) - etaTarget M| ≤
        etaRemainder E .ipw c Cgb K Rp Rg Ralpha n t (delta / 4) w

-- @node: ipw_variance_probability_of_certificate
/-- If [a variance-event certificate is available](hyp:h), then [the event with a large evaluation count, finite score variance, and the variance IPW error bound has probability at least `1 - delta`](goal). -/
lemma ipw_variance_probability_of_certificate (E : NeteExperiment M)
    (n : ℕ) (t delta c Cgb K : ℝ) (Rp Rg Ralpha : ℕ → ℝ → ℝ)
    (h : IpwVarianceEventCertificate E n t delta c Cgb K Rp Rg Ralpha) :
    1 - delta ≤ E.P.real {w | (n : ℝ) * tailProb M t / 4 ≤ evalCount E n t w ∧
      scoreVariance E .ipw n t w ≠ ∞ ∧
      (fun err V delta count remainder : ℝ =>
        err ≤ Real.sqrt (4 * V / (delta * count)) + remainder) |etaEstimate E .ipw n t w - etaTarget M|
        (scoreVariance E .ipw n t w).toReal delta (evalCount E n t w)
        (etaRemainder E .ipw c Cgb K Rp Rg Ralpha n t (delta / 4) w)} := by
  obtain ⟨S, hmeas, hprob, hpoint⟩ := h
  apply probability_four_events_imp E.P S hmeas hprob
  intro w hw
  obtain ⟨hcount, hfinite, hsample, hmean⟩ := hpoint w hw
  exact ⟨hcount, hfinite,
    ipw_variance_bound_of_components E n t delta c Cgb K Rp Rg Ralpha w hsample hmean⟩

/-- [The variance conditional-law transfer](goal), for [the experiment](hyp:E), [sample size](hyp:n), [threshold and confidence level](hyp:t,delta), and [training and count events](hyp:G,N), bounds departure from the variance sampling radius by its conditional iid failure probability [after defining that radius event](step:1). -/
-- @node: IpwVarianceConditionalLaw
noncomputable def IpwVarianceConditionalLaw (E : NeteExperiment M)
    (n : ℕ) (t delta : ℝ) (G N : Set E.Om) : Prop :=
  let R := {w | |etaEstimate E .ipw n t w - ∫ z, score E .ipw n w z ∂obsTailLaw M t| ≤
    Real.sqrt (4 * (scoreVariance E .ipw n t w).toReal / (delta * evalCount E n t w))}
  E.P.real ((G ∩ N) \ R) ≤ ∫ w, if w ∈ G ∩ N then
      scoreIidVarianceFailure (obsTailLaw M t) (score E .ipw n w) (evalCount E n t w) delta
      else 0 ∂E.P

-- @node: ipw_variance_probability_of_sampling_event
/-- Under [regularly varying noise](hyp:hRV), [a conditional-mean version](hyp:hCondMean), [exponent training](hyp:hTraining), [positive confidence level](hyp:hd), [a measurable count event](hyp:hN), [high-probability training and count events](hyp:hGprob,hNprob), [sufficient nonzero counts](hyp:hNcount), [nuisance and finite-variance control](hyp:hNuisance), [a mean-bound provider](hyp:hProvider), [a valid mean decomposition](hyp:hMean), and [the variance sampling event probability bound](hyp:hSampling), [the count, finite-variance, and variance-IPW-error event has probability at least `1 - delta`](goal). -/
lemma ipw_variance_probability_of_sampling_event (E : NeteExperiment M)
    (hRV : NoiseRegularlyVarying M) (hCondMean : ConditionalMeanVersion M)
    (n : ℕ) (hTraining : ExponentTraining E n)
    (t delta c Cgb K : ℝ)
    (Rp Rg Ralpha : ℕ → ℝ → ℝ) (G N : Set E.Om)
    (reg : ((Fin q → ℝ) × Bool × (Fin d → ℝ)) → ℝ)
    (hd : 0 < delta) (hN : MeasurableSet N)
    (hGprob : 1 - delta / 4 ≤ E.P.real G) (hNprob : 1 - delta / 4 ≤ E.P.real N)
    (hNcount : ∀ w ∈ N, (n : ℝ) * tailProb M t / 4 ≤ (evalCount E n t w : ℝ) ∧
      evalCount E n t w ≠ 0)
    (hNuisance : ∀ w ∈ G, NuisanceAt E n t (delta / 4) Rp Rg Ralpha reg w ∧
      scoreVariance E .ipw n t w ≠ ∞)
    (hProvider : IpwMeanBoundProvider E n t (delta / 4) c Cgb K Rp Rg Ralpha)
    (hMean : ∀ w ∈ G, IpwOutcomeScoreMean E n t w → IpwMeanDecomposition E n t w)
    (hSampling : 1 - delta ≤ E.P.real ((G ∩ N) ∩ {w |
      |etaEstimate E .ipw n t w - ∫ z, score E .ipw n w z ∂obsTailLaw M t| ≤
        Real.sqrt (4 * (scoreVariance E .ipw n t w).toReal /
          (delta * evalCount E n t w))})) :
    1 - delta ≤ E.P.real {w | (n : ℝ) * tailProb M t / 4 ≤ evalCount E n t w ∧
      scoreVariance E .ipw n t w ≠ ∞ ∧
      (fun err V delta count remainder : ℝ =>
        err ≤ Real.sqrt (4 * V / (delta * count)) + remainder) |etaEstimate E .ipw n t w - etaTarget M|
        (scoreVariance E .ipw n t w).toReal delta (evalCount E n t w)
        (etaRemainder E .ipw c Cgb K Rp Rg Ralpha n t (delta / 4) w)} := by
  let := obsTailLaw_probability M hRV t
  have hf : ∀ᵐ w ∂E.P, w ∈ G → MemLp (score E .ipw n w) 2 (obsTailLaw M t) := by
    apply Eventually.of_forall
    intro w hw
    apply (evariance_lt_top_iff_memLp
      (measurable_score_frozen E .ipw n w).aestronglyMeasurable).mp
    exact lt_top_iff_ne_top.mpr (hNuisance w hw).2
  apply hSampling.trans
  change (E.P _).toReal ≤ (E.P _).toReal
  apply ENNReal.toReal_mono (measure_ne_top E.P _)
  apply measure_mono_ae
  filter_upwards [hf] with w hfw
  intro hw
  have hIdentity := ipw_outcome_score_mean_of_integrable E hRV hCondMean n t w
    ((hfw hw.1.1).integrable (by norm_num))
  refine ⟨(hNcount w hw.1.2).1, (hNuisance w hw.1.1).2, ?_⟩
  exact ipw_variance_bound_of_components E n t delta c Cgb K Rp Rg Ralpha w
    hw.2 (hProvider reg w (hNuisance w hw.1.1).1 (hMean w hw.1.1 hIdentity))

-- @node: ipw_variance_probability_of_conditional_law
/-- Under [regularly varying noise](hyp:hRV), [a conditional-mean version](hyp:hCondMean), [exponent training](hyp:hTraining), [positive confidence level](hyp:hd), [a measurable count event](hyp:hN), [high-probability training and count events](hyp:hGprob,hNprob), [sufficient nonzero counts](hyp:hNcount), [nuisance and finite-variance control](hyp:hNuisance), [a mean-bound provider](hyp:hProvider), [a valid mean decomposition](hyp:hMean), and [a variance conditional-law transfer](hyp:hLaw), [the count, finite-variance, and variance-IPW-error event has probability at least `1 - delta`](goal). -/
lemma ipw_variance_probability_of_conditional_law (E : NeteExperiment M)
    (hRV : NoiseRegularlyVarying M) (hCondMean : ConditionalMeanVersion M)
    (n : ℕ) (hTraining : ExponentTraining E n)
    (t delta c Cgb K : ℝ)
    (Rp Rg Ralpha : ℕ → ℝ → ℝ) (G N : Set E.Om)
    (reg : ((Fin q → ℝ) × Bool × (Fin d → ℝ)) → ℝ)
    (hd : 0 < delta) (hN : MeasurableSet N)
    (hGprob : 1 - delta / 4 ≤ E.P.real G) (hNprob : 1 - delta / 4 ≤ E.P.real N)
    (hNcount : ∀ w ∈ N, (n : ℝ) * tailProb M t / 4 ≤ (evalCount E n t w : ℝ) ∧
      evalCount E n t w ≠ 0)
    (hNuisance : ∀ w ∈ G, NuisanceAt E n t (delta / 4) Rp Rg Ralpha reg w ∧
      scoreVariance E .ipw n t w ≠ ∞)
    (hProvider : IpwMeanBoundProvider E n t (delta / 4) c Cgb K Rp Rg Ralpha)
    (hMean : ∀ w ∈ G, IpwOutcomeScoreMean E n t w → IpwMeanDecomposition E n t w)
    (hLaw : IpwVarianceConditionalLaw E n t delta G N) :
    1 - delta ≤ E.P.real {w | (n : ℝ) * tailProb M t / 4 ≤ evalCount E n t w ∧
      scoreVariance E .ipw n t w ≠ ∞ ∧
      (fun err V delta count remainder : ℝ =>
        err ≤ Real.sqrt (4 * V / (delta * count)) + remainder) |etaEstimate E .ipw n t w - etaTarget M|
        (scoreVariance E .ipw n t w).toReal delta (evalCount E n t w)
        (etaRemainder E .ipw c Cgb K Rp Rg Ralpha n t (delta / 4) w)} := by
  let := obsTailLaw_probability M hRV t
  have hTransfer := hLaw
  have hR := measurableSet_score_variance_event E .ipw hRV hTraining t delta
  have hf : ∀ᵐ w ∂E.P, w ∈ G → MemLp (score E .ipw n w) 2 (obsTailLaw M t) := by
    apply Eventually.of_forall
    intro w hw
    apply (evariance_lt_top_iff_memLp
      (measurable_score_frozen E .ipw n w).aestronglyMeasurable).mp
    exact lt_top_iff_ne_top.mpr (hNuisance w hw).2
  have hprob := score_variance_probability_of_transfer_ae E.P (obsTailLaw M t)
    (fun w => score E .ipw n w) (evalCount E n t) (etaEstimate E .ipw n t)
    G N hN hd hGprob hNprob (fun w hw => Nat.pos_of_ne_zero (hNcount w hw).2)
    hf hR hTransfer
  apply hprob.trans
  change (E.P _).toReal ≤ (E.P _).toReal
  apply ENNReal.toReal_mono (measure_ne_top E.P _)
  apply measure_mono_ae
  filter_upwards [hf] with w hfw
  intro hw
  have hIdentity := ipw_outcome_score_mean_of_integrable E hRV hCondMean n t w
    ((hfw hw.1.1).integrable (by norm_num))
  refine ⟨(hNcount w hw.1.2).1, (hNuisance w hw.1.1).2, ?_⟩
  exact ipw_variance_bound_of_components E n t delta c Cgb K Rp Rg Ralpha w
    hw.2 (hProvider reg w (hNuisance w hw.1.1).1 (hMean w hw.1.1 hIdentity))

/-- [The IPW population onset condition](goal), for [the population model](hyp:M) and [tail-index margin and onset threshold](hyp:a0,t0), requires positive tail probability, a bounded tail-error envelope, and a uniform Potter-type tail ratio beyond the onset [in its first clause](step:1) [and second clause](step:2) [and third clause](step:3).

These facts concern only the population, not a fitted score or a success event. -/
def IpwPopulationOnset (M : ExtremeModel q d) (a0 t0 : ℝ) : Prop :=
  (∀ r ≥ t0, 0 < tailProb M r) ∧
  (∀ r ≥ t0, BddAbove (M.e '' Set.Ici r)) ∧
  (∀ r ≥ t0, ∀ u ≥ (1 : ℝ),
    tailProb M (r * u) / tailProb M r ≤
      2 * u ^ (-(M.beta - (M.beta - a0) / 2)))

/-- [The IPW conclusion scope](goal), for [the population model](hyp:M), [tail dimension](hyp:m), [tail parameters](hyp:tp), [outcome bound and tail-index margin](hyp:Cgb,a0), [experiment](hyp:E), [sample size](hyp:n), [onset, threshold, confidence, and overlap constants](hyp:t0,t,delta,c), [nuisance-rate functions](hyp:Rp,Rg,Ralpha), [random truncation level](hyp:B), [selected proof branch](hyp:branch), and [angular constants](hyp:CW,k,tW), collects the baseline assumptions and the branch-specific assumptions [in its first branch](step:1) [and second branch](step:2) [and third branch](step:3).

Applicability conditions for the IPW lemma, with no quantitative conclusion.
`branch = 0` selects the truncated display for the fixed positive training-measurable
`B`; `branch = 1` also requires the angular assumption at `t ≥ tW`;
`branch = 2` also requires almost-sure finite extended conditional IPW variance.
`t0 ≥ 1`, `IpwPopulationOnset M a0 t0`, and `t0 ≤ t` require the evaluated
threshold to lie beyond an onset of the primitive population facts from which
both rate proofs build their cutoffs. No rate conclusion or success probability
is an onset premise.
The bounds themselves remain conclusions of `eta_ipw_rate` and `angular_term_le`. -/
-- @node: ass:pin-42
def IpwConclusionScope (M : ExtremeModel q d) (m : ℕ) (tp : TailParams)
    (Cgb a0 : ℝ) (E : NeteExperiment M) (n : ℕ) (t0 t delta c : ℝ)
    (Rp Rg Ralpha : ℕ → ℝ → ℝ) (B : E.Om → ℝ)
    (branch : Fin 3) (CW k tW : ℝ) : Prop :=
  let baseConditions : Prop :=
    Consistency M ∧ Exogeneity M ∧ NoiseRegularlyVarying M ∧ NoiseIndependent M ∧
    CovariateBounded M ∧ AsymptoticHomogeneity M ∧ Nonempty (ParetoTailModel M m tp) ∧
    AlphaLtBeta M ∧ ConditionalMeanVersion M ∧ IdentificationSideConditions M ∧
    GBound M Cgb ∧ 0 < a0 ∧ a0 < M.beta ∧
    EstimatedOverlap E c ∧
    EvenSampleSize n ∧ -- @realizes n(positive even full-input size)
    IIDSampling E n ∧ ExponentTraining E n ∧
    NuisanceErrorBounds E n Rp Rg Ralpha ∧ NuisanceIntegrability E n Rp Rg Ralpha ∧
    1 ≤ t0 ∧ IpwPopulationOnset M a0 t0 ∧
    t0 ≤ t ∧ -- @realizes t(threshold at or above a sufficient population onset t0 ≥ 1)
    0 < delta ∧ delta < 1 ∧ -- @realizes \delta(confidence tolerance in (0,1))
    Ralpha n (delta / 4) ≤ a0 ∧
    (n : ℝ) * tailProb M t ≥ 16 * Real.log (4 / delta) ∧
    Measurable[trainSigma E n] B ∧ (∀ w, 0 < B w)
  match branch.val with
  | 0 => baseConditions
  | 1 => baseConditions ∧ AngularRateBound M tp CW k tW ∧ tW ≤ t
  | _ => baseConditions ∧ (∀ᵐ w ∂E.P, scoreVariance E .ipw n t w ≠ ∞)

-- @node: lem:eta-ipw
/-- If [consistency](hyp:hConsistency), [exogeneity](hyp:hExogeneity), [regularly varying noise](hyp:hRV), [noise independence](hyp:hNoise), [bounded covariates](hyp:hX), [asymptotic homogeneity](hyp:hHomogeneity), [a Pareto-tail model](hyp:hTail), [a valid tail-index ordering](hyp:hAlpha), [a conditional-mean version](hyp:hMean), [identification side conditions](hyp:hSide), [a generalized-outcome bound](hyp:hGBound), [a positive tail-index margin](hyp:ha0), and [that margin below the tail index](hyp:ha0beta) hold, then [there is an onset threshold from which both truncated and variance IPW rate conclusions hold for every overlapped experiment](goal). -/
lemma eta_ipw_rate (M : ExtremeModel q d)
    (tp : TailParams)
    (hConsistency : Consistency M) (hExogeneity : Exogeneity M)
    (hRV : NoiseRegularlyVarying M) (hNoise : NoiseIndependent M)
    (hX : CovariateBounded M) (hHomogeneity : AsymptoticHomogeneity M)
    (hTail : Nonempty (ParetoTailModel M m tp))
    (hAlpha : AlphaLtBeta M)
    (hMean : ConditionalMeanVersion M)
    (hSide : IdentificationSideConditions M)
    (Cgb : ℝ) (hGBound : GBound M Cgb)
    (a0 : ℝ) (ha0 : 0 < a0) (ha0beta : a0 < M.beta) :
    ∃ t0 : ℝ, 1 ≤ t0 ∧
      ∀ (E : NeteExperiment M) (c : ℝ) (Rp Rg Ralpha : ℕ → ℝ → ℝ),
        EstimatedOverlap E c →
          EtaRateConclusion E .ipw c Cgb (4 / (M.beta - a0)) t0 a0 Rp Rg Ralpha ∧
          EtaVarianceConclusion E .ipw c Cgb (4 / (M.beta - a0)) t0 a0 Rp Rg Ralpha := by
  let K : ℝ := 4 / (M.beta - a0)
  obtain ⟨T, hT, hExponent⟩ :=
    dr_exponent_mean_explicit_bound M hRV hX hHomogeneity hGBound ha0 ha0beta
  obtain ⟨Th, hTh⟩ := eventually_atTop.mp (eBar_eventually_bddAbove M hHomogeneity)
  obtain ⟨Kr, Tr, hKr, hTr, hPower⟩ :=
    tail_power_increment_uniform_bound M hRV ha0 ha0beta
  let t0 := max (max T Th) Tr
  have ht0 : T ≤ t0 := (le_max_left T Th).trans (le_max_left _ _)
  have hth0 : Th ≤ t0 := (le_max_right T Th).trans (le_max_left _ _)
  have htr0 : Tr ≤ t0 := le_max_right _ _
  refine ⟨t0, hT.trans ht0, ?_⟩
  intro E c Rp Rg Ralpha hOverlap
  have hProvider : ∀ n, EvenSampleSize n → NuisanceErrorBounds E n Rp Rg Ralpha →
      ∀ t, t0 ≤ t → ∀ delta, 0 < delta → delta < 1 → Ralpha n (delta / 4) ≤ a0 →
        IpwMeanBoundProvider E n t (delta / 4) c Cgb K Rp Rg Ralpha := by
    intro n hn hNuisance t ht delta hd hd1 ha
    have hd4 : 0 < delta / 4 := by positivity
    have hd41 : delta / 4 < 1 := by linarith
    have hErrors := (nuisanceErrorBounds_components _ _ _ _ _ hNuisance).1 (delta / 4) hd4 hd41
    have htpos : 0 < t := zero_lt_one.trans_le (hT.trans (ht0.trans ht))
    have hb := hTh t (hth0.trans ht)
    exact ipw_mean_bound_provider E hRV hX hHomogeneity hn hOverlap hGBound htpos hb
      Rp Rg Ralpha hErrors.1.2 (hErrors.2.2.1 n) ha
      (hExponent t (ht0.trans ht) E c hOverlap n hn)
      (normalized_contrast_target_bound M hRV hX hHomogeneity hMean hGBound htpos hb
        (angularFactor_target_wasserstein_bound M hRV hNoise hX hHomogeneity htpos))
  have hMeanClosure : ∀ n, EvenSampleSize n → NuisanceErrorBounds E n Rp Rg Ralpha →
      ∀ t, t0 ≤ t → ∀ delta, 0 < delta → delta < 1 → Ralpha n (delta / 4) ≤ a0 →
      ∀ reg w, NuisanceAt E n t (delta / 4) Rp Rg Ralpha reg w →
        IpwOutcomeScoreMean E n t w → IpwMeanDecomposition E n t w := by
    intro n hn hNuisance t ht delta hd hd1 ha reg w hw hOutcome
    have hErrors := (nuisanceErrorBounds_components _ _ _ _ _ hNuisance).1 (delta / 4) (by positivity) (by linarith)
    have hRad := (hPower t (htr0.trans ht) (Ralpha n (delta / 4))
      (hErrors.2.2.1 n) ha).1
    have hIdentity := ipw_conditional_score_mean_of_outcome_score_mean E hRV hNoise
      hX hHomogeneity hMean hn hOverlap hGBound (hT.trans (ht0.trans ht))
      (hTh t (hth0.trans ht)) w
      (by simpa only [abs_sub_comm] using hw.1) hRad hOutcome
    exact ipw_mean_decomposition_of_conditional_score_mean E hRV hX hHomogeneity
      hMean hn hOverlap hGBound (hT.trans (ht0.trans ht)) (hTh t (hth0.trans ht))
      Rp Rg Ralpha hErrors.1.2 reg w hw
      (by simpa only [abs_sub_comm] using hw.1) hRad hIdentity
  constructor
  · intro n hn hIID hTraining hNuisance hIntegrable t ht delta hd hd1 ha hbudget B hB hBpos
    obtain ⟨hN, hNprob, hNpositive⟩ := evaluation_count_event E n t hn hIID hd hd1 hbudget
    have htpos : 0 < t := zero_lt_one.trans_le (hT.trans (ht0.trans ht))
    obtain ⟨reg, hreg, hEvents⟩ := hIntegrable t htpos
    obtain ⟨G, hGmeas, hGprob, hGNuisance, hGInt⟩ :=
      hEvents (delta / 4) (by positivity) (by linarith)
    have hMeanProvider := hProvider n hn hNuisance t ht delta hd hd1 ha
    have hSampling := score_evaluation_truncated_sampling E .ipw n hn hIID hRV hTraining
      t G {w | (n : ℝ) * tailProb M t / 4 ≤ (evalCount E n t w : ℝ)} hGmeas hN B hB
      (fun w => (hBpos w).le) hd hGprob hNprob (fun w hw => hNpositive w hw)
      (ipw_score_integrable_on_nuisance_event E hn hOverlap hGInt)
    change 1 - delta ≤ E.P.real {w | (n : ℝ) * tailProb M t / 4 ≤
      (evalCount E n t w : ℝ) ∧ |etaEstimate E .ipw n t w - etaTarget M| ≤
      etaTruncatedError E .ipw c Cgb K Rp Rg Ralpha n t delta B w}
    exact ipw_truncated_probability_of_sampling_event E hRV hMean hn hTraining hOverlap Rp Rg Ralpha B
      (hB.mono (trainSigma_le E n) le_rfl)
      G {w | (n : ℝ) * tailProb M t / 4 ≤ (evalCount E n t w : ℝ)} reg hd hBpos
      hN hGprob hNprob (fun w hw => ⟨hw, hNpositive w hw⟩) hGNuisance hGInt
      hMeanProvider
      (fun w hw => hMeanClosure n hn hNuisance t ht delta hd hd1 ha reg w
        (hGNuisance w hw)) hSampling
  · intro n hn hIID hTraining hNuisance t ht delta hd hd1 hMoments ha hbudget
    let := obsTailLaw_probability M hRV t
    obtain ⟨hN, hNprob, hNpositive⟩ := evaluation_count_event E n t hn hIID hd hd1 hbudget
    obtain ⟨reg, hreg, G, hGmeas, hGprob, hGInt, hGNuisance⟩ := hMoments
    have hMeanProvider := hProvider n hn hNuisance t ht delta hd hd1 ha
    have hf : ∀ᵐ w ∂E.P, w ∈ G → MemLp (score E .ipw n w) 2 (obsTailLaw M t) := by
      apply Filter.Eventually.of_forall
      intro w hw
      apply (evariance_lt_top_iff_memLp
        (measurable_score_frozen E .ipw n w).aestronglyMeasurable).mp
      exact lt_top_iff_ne_top.mpr (hGNuisance w hw).2
    have hSampling := score_evaluation_variance_sampling E .ipw n hn hIID hRV hTraining
      t G {w | (n : ℝ) * tailProb M t / 4 ≤ (evalCount E n t w : ℝ)} hGmeas hN
      hd hGprob hNprob (fun w hw => hNpositive w hw) hf
    exact ipw_variance_probability_of_sampling_event E hRV hMean n hTraining t delta c Cgb K
      Rp Rg Ralpha G {w | (n : ℝ) * tailProb M t / 4 ≤ (evalCount E n t w : ℝ)}
      reg hd hN hGprob hNprob (fun w hw => ⟨hw, hNpositive w hw⟩) hGNuisance
      hMeanProvider
      (fun w hw => hMeanClosure n hn hNuisance t ht delta hd hd1 ha reg w
        (hGNuisance w hw).1) hSampling

end Papers.TbsExtremeEffects

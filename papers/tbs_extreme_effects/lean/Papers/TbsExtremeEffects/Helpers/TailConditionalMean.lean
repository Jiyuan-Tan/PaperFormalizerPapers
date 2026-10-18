module
public import Papers.TbsExtremeEffects.Helpers.ConditionalConsistency
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Integration of conditional sign means on measurable tail events.
Localization allows the potential outcomes to be integrable only on the tail. -/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

-- @node: conditional_limit_integral_on_event
/-- If [the conditioning sigma-algebra is contained in the ambient one](hyp:hG), [the event is measurable for it](hyp:hA), [every approximating function is integrable](hyp:hF), [the limiting outcome is integrable on that event](hyp:hY), [the approximations are nonnegative and bounded by that outcome](hyp:hbound), [their conditional expectations converge there](hyp:hlim), and [the approximations themselves converge there](hyp:hFlim), then [the conditional-expectation limit is integrable on the event and has the same event integral as the limiting outcome](goal). -/
lemma conditional_limit_integral_on_event {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {G : MeasurableSpace Ω} (hG : G ≤ mΩ)
    {A : Set Ω} (hA : MeasurableSet[G] A) (F : ℕ → Ω → ℝ) (Y H : Ω → ℝ)
    (hF : ∀ k, Integrable (F k) μ) (hY : IntegrableOn Y A μ)
    (hbound : ∀ k, ∀ w, 0 ≤ F k w ∧ F k w ≤ Y w)
    (hlim : ∀ᵐ w ∂μ.restrict A, Tendsto (fun k => μ[F k | G] w) atTop (𝓝 (H w)))
    (hFlim : ∀ᵐ w ∂μ.restrict A, Tendsto (fun k => F k w) atTop (𝓝 (Y w))) :
    IntegrableOn H A μ ∧ (∫ w in A, H w ∂μ) = ∫ w in A, Y w ∂μ := by
  have hAm : @MeasurableSet Ω mΩ A := hG _ hA
  let B : Ω → ℝ := μ[A.indicator Y | G]
  have hB : IntegrableOn B A μ := integrable_condExp.integrableOn
  have hYind : Integrable (A.indicator Y) μ := (integrable_indicator_iff hAm).mpr hY
  have hdom (k : ℕ) : ∀ᵐ w ∂μ.restrict A, ‖μ[F k | G] w‖ ≤ B w := by
    have hle : A.indicator (F k) ≤ᵐ[μ] A.indicator Y := by
      apply Eventually.of_forall
      intro w
      by_cases hw : w ∈ A
      · simpa only [Set.indicator_of_mem hw] using (hbound k w).2
      · simp only [Set.indicator_of_notMem hw, le_refl]
    have hc := condExp_mono ((hF k).indicator hAm) hYind hle (m := G)
    have hi := condExp_indicator (hF k) hA
    have hn := condExp_nonneg (m := G) (μ := μ)
      (Eventually.of_forall fun w => (hbound k w).1)
    filter_upwards [ae_restrict_of_ae hc, ae_restrict_of_ae hi, ae_restrict_of_ae hn,
      ae_restrict_mem hAm] with w hc hi hn hw
    rw [Real.norm_eq_abs, abs_of_nonneg hn]
    rw [hi, Set.indicator_of_mem hw] at hc
    exact hc
  have hH : IntegrableOn H A μ := by
    apply hB.mono' (aestronglyMeasurable_of_tendsto_ae atTop
      (fun k => integrable_condExp.aestronglyMeasurable.restrict) hlim)
    have hd := ae_all_iff.mpr hdom
    filter_upwards [hd, hlim] with w hd hl
    exact le_of_tendsto hl.norm (Eventually.of_forall hd)
  have hcond := tendsto_integral_of_dominated_convergence B
    (fun k => integrable_condExp.aestronglyMeasurable.restrict) hB hdom hlim
  have hraw := tendsto_integral_of_dominated_convergence Y
    (fun k => (hF k).aestronglyMeasurable.restrict) hY
    (fun k => Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hbound k w).1]
      exact (hbound k w).2) hFlim
  have heq : (fun k => ∫ w in A, μ[F k | G] w ∂μ) =
      (fun k => ∫ w in A, F k w ∂μ) := by
    funext k
    exact setIntegral_condExp hG (hF k) hA
  rw [heq] at hcond
  exact ⟨hH, tendsto_nhds_unique hcond hraw⟩

variable {q d : ℕ}

-- @node: conditionalPotentialPart_integral_on_event
/-- For [an extreme-value model](hyp:M), [a treatment value](hyp:a), [a choice of positive or negative part](hyp:negative), [a conditioning sigma-algebra below the ambient sigma-algebra](hyp:hG), [an event measurable for that sigma-algebra](hyp:hA), [a defined conditional potential mean](hyp:hDefined), and [an integrable potential outcome on the event](hyp:hY), [the corresponding limiting conditional part is integrable and its event integral equals the integral of the matching positive part of the potential outcome](goal). -/
lemma conditionalPotentialPart_integral_on_event (M : ExtremeModel q d) (a negative : Bool)
    {G : MeasurableSpace M.Om} (hG : G ≤ M.measurableSpace)
    {A : Set M.Om} (hA : MeasurableSet[G] A)
    (hDefined : ConditionalPotentialMeanDefined M a G)
    (hY : IntegrableOn (potentialOutcome M a) A M.mu) :
    IntegrableOn (fun w => limUnder atTop
      (fun k => conditionalPotentialPart M a negative G k w)) A M.mu ∧
    (∫ w in A, limUnder atTop (fun k => conditionalPotentialPart M a negative G k w) ∂M.mu) =
      ∫ w in A, max (if negative then -potentialOutcome M a w
        else potentialOutcome M a w) 0 ∂M.mu := by
  let : MeasurableSpace M.Om := M.measurableSpace
  have hmeas : Measurable (potentialOutcome M a) := by
    cases a
    · exact M.measurable_Y0
    · exact M.measurable_Y1
  let Y : M.Om → ℝ := fun w =>
    max (if negative then -potentialOutcome M a w else potentialOutcome M a w) 0
  let F : ℕ → M.Om → ℝ := fun k w => min (Y w) (k : ℝ)
  apply conditional_limit_integral_on_event M.mu hG hA F Y
  · intro k
    exact integrable_sign_truncation M.mu hmeas negative k
  · dsimp [Y]
    cases negative
    · exact Integrable.pos_part hY
    · exact Integrable.pos_part hY.neg
  · intro k w
    exact ⟨le_min (le_max_right _ _) (Nat.cast_nonneg k), min_le_left _ _⟩
  · filter_upwards [ae_restrict_of_ae hDefined] with w hw
    have hex : ∃ l : ℝ, Tendsto (fun k => conditionalPotentialPart M a negative G k w)
        atTop (𝓝 l) := by
      cases negative
      · exact hw.1
      · exact hw.2
    obtain ⟨l, hl⟩ := hex
    rw [hl.limUnder_eq]
    exact hl
  · apply Eventually.of_forall
    intro w
    have hev : ∀ᶠ k : ℕ in atTop, Y w ≤ (k : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (Y w))
    apply tendsto_const_nhds.congr'
    filter_upwards [hev] with k hk
    exact (min_eq_left hk).symm

-- @node: conditionalPotentialMean_integral_on_event
/-- For [an extreme-value model](hyp:M), [a treatment value](hyp:a), [a conditioning sigma-algebra below the ambient sigma-algebra](hyp:hG), [an event measurable for it](hyp:hA), [a defined conditional potential mean](hyp:hDefined), and [an integrable potential outcome on the event](hyp:hY), [the conditional potential mean is integrable on that event and has the same event integral as the potential outcome](goal). -/
lemma conditionalPotentialMean_integral_on_event (M : ExtremeModel q d) (a : Bool)
    {G : MeasurableSpace M.Om} (hG : G ≤ M.measurableSpace)
    {A : Set M.Om} (hA : MeasurableSet[G] A)
    (hDefined : ConditionalPotentialMeanDefined M a G)
    (hY : IntegrableOn (potentialOutcome M a) A M.mu) :
    IntegrableOn (conditionalPotentialMean M a G) A M.mu ∧
    (∫ w in A, conditionalPotentialMean M a G w ∂M.mu) =
      ∫ w in A, potentialOutcome M a w ∂M.mu := by
  let : MeasurableSpace M.Om := M.measurableSpace
  have hp := conditionalPotentialPart_integral_on_event M a false hG hA hDefined hY
  have hn := conditionalPotentialPart_integral_on_event M a true hG hA hDefined hY
  refine ⟨hp.1.sub hn.1, ?_⟩
  unfold conditionalPotentialMean
  rw [integral_sub hp.1 hn.1, hp.2, hn.2]
  have hpos : IntegrableOn (fun w => max (potentialOutcome M a w) 0) A M.mu :=
    Integrable.pos_part hY
  have hneg : IntegrableOn (fun w => max (-potentialOutcome M a w) 0) A M.mu :=
    Integrable.pos_part hY.neg
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [← integral_sub hpos hneg]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro w
  dsimp only
  rcases le_total 0 (potentialOutcome M a w) with hw | hw
  · rw [max_eq_left hw, max_eq_right (neg_nonpos.mpr hw), sub_zero]
  · rw [max_eq_right hw, max_eq_left (neg_nonneg.mpr hw)]
    ring

-- @node: conditionalPotentialMean_integral_tailLaw
/-- Given [an extreme-value model](hyp:M), [regularly varying noise](hyp:hRV), [a treatment value](hyp:a), [a tail threshold](hyp:t), [a defined conditional potential mean](hyp:hDefined), and [an integrable potential outcome under the tail law](hyp:hY), [the conditional potential mean is integrable under that tail law and has the same integral](goal). -/
lemma conditionalPotentialMean_integral_tailLaw (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (a : Bool) (t : ℝ)
    (hDefined : ConditionalPotentialMeanDefined M a (sigmaXU M))
    (hY : Integrable (potentialOutcome M a) (tailLaw M t)) :
    Integrable (conditionalPotentialMean M a (sigmaXU M)) (tailLaw M t) ∧
    (∫ w, conditionalPotentialMean M a (sigmaXU M) w ∂tailLaw M t) =
      ∫ w, potentialOutcome M a w ∂tailLaw M t := by
  have hG : sigmaXU M ≤ M.measurableSpace :=
    (M.measurable_X.prodMk M.measurable_U).comap_le
  have hA : MeasurableSet[sigmaXU M] {w | t < radius M w} := by
    refine ⟨{z : (Fin q → ℝ) × (Fin d → ℝ) | t < l1Norm z.2}, ?_, rfl⟩
    exact measurableSet_lt measurable_const (measurable_l1Norm.comp measurable_snd)
  have hpos : M.mu {w | t < radius M w} ≠ 0 := by
    intro hz
    have hp := tailProb_pos_of_regularVariation M hRV t
    simp only [tailProb, hz, ENNReal.toReal_zero] at hp
    exact (lt_irrefl 0) hp
  have hYres : IntegrableOn (potentialOutcome M a) {w | t < radius M w} M.mu :=
    (integrable_inv_smul_measure hpos (measure_ne_top _ _)).mp hY
  have hc := conditionalPotentialMean_integral_on_event M a hG hA hDefined hYres
  refine ⟨hc.1.smul_measure (ENNReal.inv_ne_top.mpr hpos), ?_⟩
  simp only [tailLaw, ProbabilityTheory.cond, integral_smul_measure]
  rw [hc.2]

-- @node: neteAt_eq_conditionalPotentialMean_eventually
/-- If [the model has regularly varying noise](hyp:hRV) and [the identification side conditions hold](hyp:hSide), then [at all sufficiently high tail thresholds, the normalized tail effect equals the tail-law integral of the difference between the treated and untreated conditional potential means](goal). -/
lemma neteAt_eq_conditionalPotentialMean_eventually (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (hSide : IdentificationSideConditions M) :
    ∀ᶠ t in atTop, neteAt M t = ∫ w,
      (conditionalPotentialMean M true (sigmaXU M) w -
        conditionalPotentialMean M false (sigmaXU M) w) / t ^ M.alpha ∂tailLaw M t := by
  filter_upwards [hSide.2.2] with t ht
  have h1 := conditionalPotentialMean_integral_tailLaw M hRV true t
    (hSide.2.1 true).2.1 (ht true)
  have h0 := conditionalPotentialMean_integral_tailLaw M hRV false t
    (hSide.2.1 false).2.1 (ht false)
  have hy1 : Integrable M.Y1 (tailLaw M t) := ht true
  have hy0 : Integrable M.Y0 (tailLaw M t) := ht false
  simp only [potentialOutcome, Bool.false_eq_true, ↓reduceIte] at h1 h0
  unfold neteAt
  rw [integral_div, integral_div, integral_sub hy1 hy0,
    integral_sub h1.1 h0.1, h1.2, h0.2]

end Papers.TbsExtremeEffects

module
public import Papers.TbsExtremeEffects.Helpers.TailConditionalMean
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-! Weighted integration of the conditional sign means of the observed outcome.
Only the weighted outcome needs to be integrable. -/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

/-- If [the conditioning sigma-algebra is contained in the ambient sigma-algebra](hyp:hG), [the weight is measurable with respect to it](hyp:hh), [the weight is nonnegative](hyp:hn), [every approximating function is integrable](hyp:hF), [the weighted limiting outcome is integrable](hyp:hY), [the approximants are nonnegative and bounded by that outcome](hyp:hbound), [their conditional expectations converge almost everywhere](hyp:hlim), and [the approximants themselves converge almost everywhere](hyp:hFlim), then [the weighted conditional limit is integrable and has the same integral as the weighted outcome](goal).

@node: weighted_conditional_limit_integral -/
lemma weighted_conditional_limit_integral {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {G : MeasurableSpace Ω} (hG : G ≤ mΩ)
    (h : Ω → ℝ) (hh : Measurable[G] h) (hn : ∀ w, 0 ≤ h w)
    (F : ℕ → Ω → ℝ) (Y H : Ω → ℝ)
    (hF : ∀ k, Integrable (F k) μ)
    (hY : Integrable (fun w => h w * Y w) μ)
    (hbound : ∀ k w, 0 ≤ F k w ∧ F k w ≤ Y w)
    (hlim : ∀ᵐ w ∂μ, Tendsto (fun k => μ[F k | G] w) atTop (𝓝 (H w)))
    (hFlim : ∀ᵐ w ∂μ, Tendsto (fun k => F k w) atTop (𝓝 (Y w))) :
    Integrable (fun w => h w * H w) μ ∧
      (∫ w, h w * H w ∂μ) = ∫ w, h w * Y w ∂μ := by
  have hFm (k : ℕ) : Integrable (fun w => h w * F k w) μ := by
    apply hY.mono'
    · exact ((hh.mono hG le_rfl).aestronglyMeasurable.mul
        (hF k).aestronglyMeasurable)
    · apply Eventually.of_forall
      intro w
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hn w) (hbound k w).1)]
      exact mul_le_mul_of_nonneg_left (hbound k w).2 (hn w)
  have hpull (k : ℕ) : μ[(fun w => h w * F k w) | G] =ᵐ[μ]
      (fun w => h w * μ[F k | G] w) :=
    condExp_mul_of_stronglyMeasurable_left hh.stronglyMeasurable (hFm k) (hF k)
  let B : Ω → ℝ := μ[(fun w => h w * Y w) | G]
  have hB : Integrable B μ := integrable_condExp
  have hdom (k : ℕ) : ∀ᵐ w ∂μ, ‖h w * μ[F k | G] w‖ ≤ B w := by
    have hle := condExp_mono (hFm k) hY
      (Eventually.of_forall fun w => mul_le_mul_of_nonneg_left (hbound k w).2 (hn w))
      (m := G)
    have hnonneg := condExp_nonneg (m := G) (μ := μ)
      (Eventually.of_forall fun w => (hbound k w).1)
    filter_upwards [hpull k, hle, hnonneg] with w hp hl hnF
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hn w) hnF)]
    simpa only [hp] using hl
  have hweightedLim : ∀ᵐ w ∂μ,
      Tendsto (fun k => h w * μ[F k | G] w) atTop (𝓝 (h w * H w)) :=
    hlim.mono fun w hw => hw.const_mul (h w)
  have hcondInt (k : ℕ) : Integrable (fun w => h w * μ[F k | G] w) μ :=
    integrable_condExp.congr (hpull k)
  have hH : Integrable (fun w => h w * H w) μ := by
    apply hB.mono' (aestronglyMeasurable_of_tendsto_ae atTop
      (fun k => (hcondInt k).aestronglyMeasurable) hweightedLim)
    filter_upwards [ae_all_iff.mpr hdom, hweightedLim] with w hd hl
    exact le_of_tendsto hl.norm (Eventually.of_forall hd)
  have hc := tendsto_integral_of_dominated_convergence B
    (fun k => (hcondInt k).aestronglyMeasurable) hB hdom hweightedLim
  have hr := tendsto_integral_of_dominated_convergence (fun w => h w * Y w)
    (fun k => (hFm k).aestronglyMeasurable) hY
    (fun k => Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hn w) (hbound k w).1)]
      exact mul_le_mul_of_nonneg_left (hbound k w).2 (hn w))
    (hFlim.mono fun w hw => hw.const_mul (h w))
  have heq : (fun k => ∫ w, h w * μ[F k | G] w ∂μ) =
      (fun k => ∫ w, h w * F k w ∂μ) := by
    funext k
    rw [← integral_congr_ae (hpull k), integral_condExp hG]
  rw [heq] at hc
  exact ⟨hH, tendsto_nhds_unique hc hr⟩

variable {q d : ℕ}

/-- If [the conditional observed means are defined](hyp:hDefined), [the weight is measurable with respect to observed information](hyp:hh), [the weight is nonnegative](hyp:hn), and [the weighted outcome is integrable](hyp:hY), then [the weighted limiting positive or negative observed part is integrable and has the integral of the corresponding positive outcome part](goal).

@node: weighted_observed_part_integral -/
lemma weighted_observed_part_integral (M : ExtremeModel q d)
    (hDefined : ConditionalObservedMeanDefined M) (h : M.Om → ℝ)
    (hh : Measurable[sigmaXDU M] h) (hn : ∀ w, 0 ≤ h w)
    (hY : Integrable (fun w => h w * M.Y w) M.mu) (negative : Bool) :
    Integrable (fun w => h w * limUnder atTop
      (fun k => conditionalObservedPart M negative k w)) M.mu ∧
    (∫ w, h w * limUnder atTop (fun k => conditionalObservedPart M negative k w) ∂M.mu) =
      ∫ w, h w * max (if negative then -M.Y w else M.Y w) 0 ∂M.mu := by
  let Y : M.Om → ℝ := fun w => max (if negative then -M.Y w else M.Y w) 0
  let F : ℕ → M.Om → ℝ := fun k w => min (Y w) (k : ℝ)
  have hG : sigmaXDU M ≤ M.measurableSpace :=
    (M.measurable_X.prodMk (M.measurable_D.prodMk M.measurable_U)).comap_le
  have hpart : Integrable (fun w => h w * Y w) M.mu := by
    have hsigned : Integrable (fun w => h w * (if negative then -M.Y w else M.Y w)) M.mu := by
      cases negative
      · exact hY
      · convert hY.neg using 1
        funext w
        simp only [↓reduceIte, Pi.neg_apply, mul_neg]
    apply hsigned.pos_part.congr
    apply Eventually.of_forall
    intro w
    dsimp [Y]
    rw [mul_max_of_nonneg _ _ (hn w), mul_zero]
  apply weighted_conditional_limit_integral M.mu hG h hh hn F Y
  · intro k
    exact integrable_sign_truncation M.mu M.measurable_Y negative k
  · exact hpart
  · intro k w
    exact ⟨le_min (le_max_right _ _) (Nat.cast_nonneg k), min_le_left _ _⟩
  · filter_upwards [hDefined] with w hw
    have hex : ∃ l : ℝ, Tendsto (fun k => conditionalObservedPart M negative k w)
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

/-- If [the fitted regression is a conditional-mean version](hyp:hMean), [the weight is measurable from observed information](hyp:hh), [the weight is nonnegative](hyp:hn), and [the weighted outcome is integrable](hyp:hY), then [the weighted fitted regression is integrable and has the same mean as the weighted outcome](goal).

@node: weighted_observed_mean_integral_nonneg -/
lemma weighted_observed_mean_integral_nonneg (M : ExtremeModel q d)
    (hMean : ConditionalMeanVersion M) (h : M.Om → ℝ)
    (hh : Measurable[sigmaXDU M] h) (hn : ∀ w, 0 ≤ h w)
    (hY : Integrable (fun w => h w * M.Y w) M.mu) :
    Integrable (fun w => h w * M.f (M.X w) (M.D w) (M.U w)) M.mu ∧
      (∫ w, h w * M.f (M.X w) (M.D w) (M.U w) ∂M.mu) =
        ∫ w, h w * M.Y w ∂M.mu := by
  have hp := weighted_observed_part_integral M hMean.2.1 h hh hn hY false
  have hm := weighted_observed_part_integral M hMean.2.1 h hh hn hY true
  have hi : Integrable (fun w => h w * condMeanY M w) M.mu := by
    convert hp.1.sub hm.1 using 1
    funext w
    simp only [condMeanY, mul_sub, Pi.sub_apply]
  have heq : (fun w => h w * M.f (M.X w) (M.D w) (M.U w)) =ᵐ[M.mu]
      (fun w => h w * condMeanY M w) := hMean.2.2.mono fun w hw => congrArg (fun x => h w * x) hw
  refine ⟨hi.congr heq.symm, ?_⟩
  rw [integral_congr_ae heq]
  simp only [condMeanY, mul_sub]
  rw [integral_sub hp.1 hm.1, hp.2, hm.2]
  have hpart (negative : Bool) : Integrable
      (fun w => h w * max (if negative then -M.Y w else M.Y w) 0) M.mu := by
    have hsigned : Integrable (fun w => h w * (if negative then -M.Y w else M.Y w)) M.mu := by
      cases negative
      · exact hY
      · convert hY.neg using 1
        funext w
        simp only [↓reduceIte, Pi.neg_apply, mul_neg]
    apply hsigned.pos_part.congr
    exact Eventually.of_forall fun w => by
      dsimp only
      rw [mul_max_of_nonneg _ _ (hn w), mul_zero]
  rw [← integral_sub (hpart false) (hpart true)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro w
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [← mul_sub]
  congr 1
  rcases le_total 0 (M.Y w) with hy | hy
  · rw [max_eq_left hy, max_eq_right (neg_nonpos.mpr hy), sub_zero]
  · rw [max_eq_right hy, max_eq_left (neg_nonneg.mpr hy)]
    ring

/-- If [the fitted regression is a conditional-mean version](hyp:hMean), [the weight is measurable from observed information](hyp:hh), and [the weighted outcome is integrable](hyp:hY), then [the weighted fitted regression is integrable and has the same mean as the weighted outcome](goal).

@node: weighted_observed_mean_integral -/
lemma weighted_observed_mean_integral (M : ExtremeModel q d)
    (hMean : ConditionalMeanVersion M) (h : M.Om → ℝ)
    (hh : Measurable[sigmaXDU M] h)
    (hY : Integrable (fun w => h w * M.Y w) M.mu) :
    Integrable (fun w => h w * M.f (M.X w) (M.D w) (M.U w)) M.mu ∧
      (∫ w, h w * M.f (M.X w) (M.D w) (M.U w) ∂M.mu) =
        ∫ w, h w * M.Y w ∂M.mu := by
  have hG : sigmaXDU M ≤ M.measurableSpace :=
    (M.measurable_X.prodMk (M.measurable_D.prodMk M.measurable_U)).comap_le
  have hi (negative : Bool) : Integrable
      (fun w => max (if negative then -h w else h w) 0 * M.Y w) M.mu := by
    apply hY.norm.mono'
    · apply Measurable.aestronglyMeasurable
      have hm : Measurable h := hh.mono hG le_rfl
      have hmy := M.measurable_Y
      cases negative <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop
    · apply Eventually.of_forall
      intro w
      rw [norm_mul, Real.norm_eq_abs, norm_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      rw [abs_of_nonneg (le_max_right _ _)]
      cases negative
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact max_le (le_abs_self _) (abs_nonneg _)
      · simp only [↓reduceIte]
        exact max_le (neg_le_abs _) (abs_nonneg _)
  have hp := weighted_observed_mean_integral_nonneg M hMean
    (fun w => max (h w) 0) (hh.max measurable_const) (fun _ => le_max_right _ _) (hi false)
  have hm := weighted_observed_mean_integral_nonneg M hMean
    (fun w => max (-h w) 0) (hh.neg.max measurable_const) (fun _ => le_max_right _ _) (hi true)
  have hsplit (Z : M.Om → ℝ) : (fun w => h w * Z w) =
      (fun w => max (h w) 0 * Z w - max (-h w) 0 * Z w) := by
    funext w
    rcases le_total 0 (h w) with hw | hw
    · rw [max_eq_left hw, max_eq_right (neg_nonpos.mpr hw), zero_mul, sub_zero]
    · rw [max_eq_right hw, max_eq_left (neg_nonneg.mpr hw)]
      ring
  refine ⟨?_, ?_⟩
  · rw [hsplit]
    exact hp.1.sub hm.1
  · rw [hsplit, integral_sub hp.1 hm.1, hp.2, hm.2, hsplit M.Y]
    simpa only [Bool.false_eq_true, ↓reduceIte] using (integral_sub (hi false) (hi true)).symm

/-- If [the noise is regularly varying](hyp:hRV), [the fitted regression is a conditional-mean version](hyp:hMean), [the weight is measurable from observed information](hyp:hh), and [the weighted outcome is integrable under the tail law](hyp:hY), then [the weighted fitted regression is integrable under that tail law and has the same mean as the weighted outcome](goal).

@node: weighted_observed_mean_integral_tailLaw -/
lemma weighted_observed_mean_integral_tailLaw (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (hMean : ConditionalMeanVersion M) (t : ℝ)
    (h : M.Om → ℝ) (hh : Measurable[sigmaXDU M] h)
    (hY : Integrable (fun w => h w * M.Y w) (tailLaw M t)) :
    Integrable (fun w => h w * M.f (M.X w) (M.D w) (M.U w)) (tailLaw M t) ∧
      (∫ w, h w * M.f (M.X w) (M.D w) (M.U w) ∂tailLaw M t) =
        ∫ w, h w * M.Y w ∂tailLaw M t := by
  let A : Set M.Om := {w | t < radius M w}
  have hG : sigmaXDU M ≤ M.measurableSpace :=
    (M.measurable_X.prodMk (M.measurable_D.prodMk M.measurable_U)).comap_le
  have hpair : Measurable[sigmaXDU M] (fun w => (M.X w, M.D w, M.U w)) :=
    Measurable.of_comap_le le_rfl
  have hA : MeasurableSet[sigmaXDU M] A :=
    measurableSet_lt measurable_const (measurable_l1Norm.comp hpair.snd.snd)
  have hAm : MeasurableSet A := hG _ hA
  have hpos : M.mu A ≠ 0 := by
    intro hz
    have hp := tailProb_pos_of_regularVariation M hRV t
    simp only [tailProb, show M.mu {w | t < radius M w} = 0 from hz,
      ENNReal.toReal_zero] at hp
    exact (lt_irrefl 0) hp
  have hYres : IntegrableOn (fun w => h w * M.Y w) A M.mu :=
    (integrable_inv_smul_measure hpos (measure_ne_top _ _)).mp hY
  have hYind : Integrable (fun w => A.indicator h w * M.Y w) M.mu := by
    apply ((integrable_indicator_iff hAm).mpr hYres).congr
    apply Eventually.of_forall
    intro w
    by_cases hw : w ∈ A <;> simp [hw]
  obtain ⟨hInt, hEq⟩ := weighted_observed_mean_integral M hMean
    (A.indicator h) (hh.indicator hA) hYind
  have hIntInd : Integrable (A.indicator
      (fun w => h w * M.f (M.X w) (M.D w) (M.U w))) M.mu := by
    apply hInt.congr
    apply Eventually.of_forall
    intro w
    by_cases hw : w ∈ A <;> simp [hw]
  refine ⟨((integrable_indicator_iff hAm).mp hIntInd).smul_measure
    (ENNReal.inv_ne_top.mpr hpos), ?_⟩
  have heqInd : (∫ w, A.indicator (fun w => h w * M.f (M.X w) (M.D w) (M.U w)) w ∂M.mu) =
      ∫ w, A.indicator (fun w => h w * M.Y w) w ∂M.mu := by
    convert hEq using 1 <;> apply integral_congr_ae <;>
      apply Eventually.of_forall <;> intro w <;>
      by_cases hw : w ∈ A <;> simp [hw]
  rw [integral_indicator hAm, integral_indicator hAm] at heqInd
  simp only [tailLaw, ProbabilityTheory.cond, integral_smul_measure]
  rw [heqInd]

end Papers.TbsExtremeEffects

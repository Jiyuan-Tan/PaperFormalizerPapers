module
public import Papers.TbsExtremeEffects.Helpers.ConditionalMoments
public import Papers.TbsExtremeEffects.Helpers.PotterTwo

/-! Uniform tail-power bounds for the fitted-exponent error.
A finer geometric Potter grid gives the explicit coefficient four divided by
the exponent margin, uniformly over the compact positive moment range. -/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology
variable {q d : ℕ}

/-- If [the target power is smaller than the tail-decay power](hyp:ha) and [the scaled tail probability is bounded by the stated power envelope for every multiplier at least one](hyp:hbound), then [the tail-power kernel is integrable over multipliers above one](goal).

@node: tail_power_kernel_integrable_of_bound -/
lemma tail_power_kernel_integrable_of_bound (M : ExtremeModel q d)
    {t a b D : ℝ} (ha : a < b)
    (hbound : ∀ r ≥ 1, tailProb M (t * r) / tailProb M t ≤ D * r ^ (-b)) :
    IntegrableOn (fun r : ℝ => r ^ (a - 1) *
      (tailProb M (t * r) / tailProb M t)) (Ioi 1) := by
  apply Integrable.mono'
    ((integrableOn_Ioi_rpow_of_lt (by linarith : a - b - 1 < -1)
      (by norm_num : (0 : ℝ) < 1)).const_mul D)
  · apply Measurable.aestronglyMeasurable
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hrpos : 0 < r := by linarith [mem_Ioi.mp hr]
    have hn : 0 ≤ tailProb M (t * r) / tailProb M t :=
      div_nonneg (tailProb_nonneg M _) (tailProb_nonneg M _)
    simp only [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg hrpos.le _), abs_of_nonneg hn]
    calc
      _ ≤ r ^ (a - 1) * (D * r ^ (-b)) :=
        mul_le_mul_of_nonneg_left (hbound r (mem_Ioi.mp hr).le)
          (Real.rpow_nonneg hrpos.le _)
      _ = D * r ^ (a - b - 1) := by
        rw [show a - b - 1 = (a - 1) + (-b) by ring, Real.rpow_add hrpos]
        ring

/-- If [the noise tail is regularly varying](hyp:hRV), [the threshold is positive](hyp:ht), [the moment power is nonnegative](hyp:ha), [that power is below the envelope’s decay exponent](hyp:hab), and [the scaled tail probability obeys the power envelope](hyp:hbound), then [the scaled radius has a finite conditional power moment bounded by one plus the stated tail term](goal).

@node: conditional_scaled_power_bound -/
lemma conditional_scaled_power_bound (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) {t a b D : ℝ}
    (ht : 0 < t) (ha : 0 ≤ a) (hab : a < b)
    (hbound : ∀ r ≥ 1, tailProb M (t * r) / tailProb M t ≤ D * r ^ (-b)) :
    Integrable (fun w => (radius M w / t) ^ a) (tailLaw M t) ∧
      (∫ w, (radius M w / t) ^ a ∂tailLaw M t) ≤ 1 + D * a / (b - a) := by
  let := tailLaw_probability M hRV t
  by_cases hz : a = 0
  · subst a
    simpa using And.intro
      (integrable_const (1 : ℝ) : Integrable (fun _ : M.Om => (1 : ℝ)) (tailLaw M t))
      (le_refl (1 : ℝ))
  have hkernel := tail_power_kernel_integrable_of_bound M hab hbound
  have hTail : IntegrableOn
      (fun r : ℝ => r ^ (a - 1) * (tailLaw M t).real {w | r < radius M w / t})
      (Ioi 1) := by
    apply hkernel.congr_fun _ measurableSet_Ioi
    intro r hr
    dsimp only
    rw [tailLaw_scaled_radius_survival M ht (mem_Ioi.mp hr).le]
  have hZ : Measurable (fun w => radius M w / t) := by fun_prop
  obtain ⟨hInt, hcake⟩ := power_moment_layercake (tailLaw M t) _ hZ
    (scaled_radius_ge_one_tailLaw M ht) hz hTail
  refine ⟨hInt, ?_⟩
  rw [hcake]
  apply add_le_add_right
  have hmajor : IntegrableOn (fun r : ℝ => (D * a) * r ^ (a - b - 1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : a - b - 1 < -1)
      (by norm_num : (0 : ℝ) < 1)).const_mul _
  calc
    _ ≤ ∫ r in Ioi (1 : ℝ), (D * a) * r ^ (a - b - 1) := by
      apply integral_mono_ae
        ((hTail.const_mul a).congr (Eventually.of_forall fun r => by ring)) hmajor
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      have hrpos : 0 < r := by linarith [mem_Ioi.mp hr]
      rw [tailLaw_scaled_radius_survival M ht (mem_Ioi.mp hr).le]
      calc
        _ ≤ a * r ^ (a - 1) * (D * r ^ (-b)) :=
          mul_le_mul_of_nonneg_left (hbound r (mem_Ioi.mp hr).le)
            (mul_nonneg ha (Real.rpow_nonneg hrpos.le _))
        _ = _ := by
          rw [show a - b - 1 = (a - 1) + (-b) by ring, Real.rpow_add hrpos]
          ring
    _ = D * a / (b - a) := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt
        (by linarith : a - b - 1 < -1) (by norm_num : (0 : ℝ) < 1), Real.one_rpow]
      rw [show a - b - 1 + 1 = -(b - a) by ring, div_neg]
      ring

/-- If [the noise tail is regularly varying](hyp:hRV), [the threshold is positive](hyp:ht), [the power is nonnegative](hyp:ha), [it is no larger than the comparison power](hyp:haa0), [the comparison power is below the decay exponent](hyp:ha0b), [the envelope constant is nonnegative](hyp:hD), and [the scaled tail probability obeys the power envelope](hyp:hbound), then [the radius-power increment is integrable and has the displayed conditional expectation bound](goal).

@node: conditional_radius_increment_bound -/
lemma conditional_radius_increment_bound (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) {t a a0 b D : ℝ}
    (ht : 0 < t) (ha : 0 ≤ a) (haa0 : a ≤ a0) (ha0b : a0 < b) (hD : 0 ≤ D)
    (hbound : ∀ r ≥ 1, tailProb M (t * r) / tailProb M t ≤ D * r ^ (-b)) :
    Integrable (fun w => radius M w ^ a - 1) (tailLaw M t) ∧
      (∫ w, radius M w ^ a - 1 ∂tailLaw M t) ≤
        t ^ a - 1 + (D / (b - a0)) * a * t ^ a := by
  let := tailLaw_probability M hRV t
  obtain ⟨hInt, hmoment⟩ := conditional_scaled_power_bound M hRV ht ha
    (haa0.trans_lt ha0b) hbound
  have hrep : (fun w => radius M w ^ a) =ᵐ[tailLaw M t]
      (fun w => t ^ a * (radius M w / t) ^ a) := by
    filter_upwards [scaled_radius_ge_one_tailLaw M ht] with w hw
    have hr : 0 ≤ radius M w := by
      have := (le_div_iff₀ ht).mp hw
      linarith
    rw [Real.div_rpow hr ht.le]
    field_simp
  have hRad : Integrable (fun w => radius M w ^ a) (tailLaw M t) :=
    (hInt.const_mul (t ^ a)).congr hrep.symm
  refine ⟨hRad.sub (integrable_const 1), ?_⟩
  rw [integral_sub hRad (integrable_const 1), integral_congr_ae hrep, integral_const_mul]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  have hfrac : D * a / (b - a) ≤ D * a / (b - a0) :=
    div_le_div_of_nonneg_left (mul_nonneg hD ha) (sub_pos.mpr ha0b) (by linarith)
  have hfinal := mul_le_mul_of_nonneg_left
    (hmoment.trans (add_le_add_right hfrac 1)) (Real.rpow_nonneg ht.le a)
  convert sub_le_sub_right hfinal 1 using 1 <;> first | rfl | ring

/-- If [the noise tail is regularly varying](hyp:hRV), [the maximum moment power is positive](hyp:ha0), and [it is below the tail index](hyp:ha0beta), then [there is a threshold after which every power up to that maximum has an integrable radius-power increment with the displayed explicit bound](goal).

@node: tail_power_increment_explicit_bound -/
lemma tail_power_increment_explicit_bound (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) {a0 : ℝ} (ha0 : 0 < a0) (ha0beta : a0 < M.beta) :
    ∃ t0 : ℝ, 1 ≤ t0 ∧ ∀ t ≥ t0, ∀ a : ℝ, 0 ≤ a → a ≤ a0 →
      Integrable (fun w => radius M w ^ a - 1) (tailLaw M t) ∧
        (∫ w, radius M w ^ a - 1 ∂tailLaw M t) ≤
          t ^ a - 1 + (4 / (M.beta - a0)) * a * t ^ a := by
  let eps := (M.beta - a0) / 2
  have heps : 0 < eps := by dsimp [eps]; linarith
  have hepsbeta : eps < M.beta := by dsimp [eps]; linarith
  have hgap : a0 < M.beta - eps := by dsimp [eps]; linarith
  obtain ⟨T, hT, hbound⟩ := tail_potter_ratio_two (tailProb M) heps hepsbeta
    ((tailProb_antitone M).antitoneOn (Ioi 0))
    (Eventually.of_forall (tailProb_pos_of_regularVariation M hRV))
    (fun b hb => by
      simpa only [mul_comm] using tailProb_ratio_limit M hRV (x := b) (by linarith))
  refine ⟨max 1 T, le_max_left _ _, ?_⟩
  intro t ht a ha haa0
  have hmoment := conditional_radius_increment_bound M hRV
    (hT.trans_le ((le_max_right _ _).trans ht)) ha haa0 hgap
    (by norm_num : (0 : ℝ) ≤ 2) (hbound t ((le_max_right _ _).trans ht))
  have hcoefficient : 2 / (M.beta - eps - a0) = 4 / (M.beta - a0) := by
    dsimp [eps]
    field_simp
    <;> ring
  simpa only [hcoefficient] using hmoment

/-- If [the noise tail is regularly varying](hyp:hRV), [the maximum moment power is positive](hyp:ha0), and [it is below the tail index](hyp:ha0beta), then [there are positive uniform constants controlling every sufficiently high-threshold radius-power increment up to that power](goal).

@node: tail_power_increment_uniform_bound -/
lemma tail_power_increment_uniform_bound (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) {a0 : ℝ} (ha0 : 0 < a0) (ha0beta : a0 < M.beta) :
    ∃ K t0 : ℝ, 0 < K ∧ 1 ≤ t0 ∧ ∀ t ≥ t0, ∀ a : ℝ, 0 ≤ a → a ≤ a0 →
      Integrable (fun w => radius M w ^ a - 1) (tailLaw M t) ∧
        (∫ w, radius M w ^ a - 1 ∂tailLaw M t) ≤ t ^ a - 1 + K * a * t ^ a := by
  obtain ⟨T, hT, hbound⟩ := tail_power_increment_explicit_bound M hRV ha0 ha0beta
  exact ⟨4 / (M.beta - a0), T, by positivity, hT, hbound⟩

end Papers.TbsExtremeEffects

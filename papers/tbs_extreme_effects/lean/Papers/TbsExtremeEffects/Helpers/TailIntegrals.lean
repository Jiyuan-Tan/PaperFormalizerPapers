module
public import Papers.TbsExtremeEffects.Helpers.TailInterpolation
public import Papers.TbsExtremeEffects.Helpers.Potter
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Dominated convergence for the radial layer-cake integrals. -/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
variable {q d : ℕ}

-- @node: pareto_tail_power_integral
/-- If [the exponent $a$ is smaller than $\beta$](hyp:ha), then [one plus the Pareto-tail power integral equals $\beta/(\beta-a)$](goal). -/
lemma pareto_tail_power_integral {beta a : ℝ} (ha : a < beta) :
    (1 : ℝ) + (∫ r : ℝ in Set.Ioi 1, a * r ^ (a - beta - 1)) =
      beta / (beta - a) := by
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : a - beta - 1 < -1)
    (by norm_num : (0 : ℝ) < 1), Real.one_rpow]
  have hne : beta - a ≠ 0 := (sub_pos.mpr ha).ne'
  have hne' : a - beta - 1 + 1 ≠ 0 := by linarith
  field_simp
  ring

-- @node: tail_integral_tendsto_of_bound
/-- For [an extreme-value model](hyp:M), [regularly varying noise](hyp:hRV), [a power exponent](hyp:a), [an integrable dominating function on radii above one](hyp:hB), and [an eventual domination of the scaled tail integrands by that function](hyp:hbound), [the scaled tail integral converges to its Pareto power-integral limit](goal). -/
lemma tail_integral_tendsto_of_bound (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (a : ℝ) (B : ℝ → ℝ)
    (hB : IntegrableOn B (Set.Ioi 1))
    (hbound : ∀ᶠ t in atTop, ∀ r > 1,
      |a * r ^ (a - 1) * (tailProb M (t * r) / tailProb M t)| ≤ B r) :
    Tendsto (fun t => ∫ r : ℝ in Set.Ioi 1,
      a * r ^ (a - 1) * (tailProb M (t * r) / tailProb M t)) atTop
      (𝓝 (∫ r : ℝ in Set.Ioi 1, a * r ^ (a - M.beta - 1))) := by
  apply tendsto_integral_filter_of_dominated_convergence B
  · apply Eventually.of_forall
    intro t
    apply Measurable.aestronglyMeasurable
    fun_prop
  · filter_upwards [hbound] with t ht
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    simpa only [Real.norm_eq_abs] using ht r hr
  · exact hB
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hrpos : 0 < r := by linarith [Set.mem_Ioi.mp hr]
    have hlim := (tailProb_ratio_limit M hRV hrpos).const_mul (a * r ^ (a - 1))
    convert hlim using 1
    have he : a - M.beta - 1 = (a - 1) + (-M.beta) := by ring
    rw [he, Real.rpow_add hrpos]
    congr 1
    ring

-- @node: tail_integral_limit
/-- For [an extreme-value model](hyp:M), [regularly varying noise](hyp:hRV), and [a power exponent below the tail index](hyp:ha), [one plus the scaled tail integral converges to $\beta/(\beta-a)$](goal). -/
lemma tail_integral_limit (M : ExtremeModel q d) (hRV : NoiseRegularlyVarying M)
    {a : ℝ} (ha : a < M.beta) :
    Tendsto (fun t => 1 + ∫ r : ℝ in Set.Ioi 1,
      a * r ^ (a - 1) * (tailProb M (t * r) / tailProb M t))
      atTop (𝓝 (M.beta / (M.beta - a))) := by
  have hlim : Tendsto (fun t => ∫ r : ℝ in Set.Ioi 1,
      a * r ^ (a - 1) * (tailProb M (t * r) / tailProb M t)) atTop
      (𝓝 (∫ r : ℝ in Set.Ioi 1, a * r ^ (a - M.beta - 1))) := by
    rcases lt_trichotomy a 0 with hneg | hzero | hpos
    · apply tail_integral_tendsto_of_bound M hRV a (fun r => |a| * r ^ (a - 1))
      · exact (integrableOn_Ioi_rpow_of_lt (by linarith : a - 1 < -1)
          (by norm_num : (0 : ℝ) < 1)).const_mul |a|
      · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht r hr
        have hratio : 0 ≤ tailProb M (t * r) / tailProb M t :=
          div_nonneg (tailProb_nonneg M _) (tailProb_nonneg M _)
        have hratio_le : tailProb M (t * r) / tailProb M t ≤ 1 := by
          apply (div_le_iff₀ (tailProb_pos_of_regularVariation M hRV t)).2
          simpa using tailProb_antitone M (by nlinarith : t ≤ t * r)
        rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (by linarith) _),
          abs_of_nonneg hratio]
        exact (mul_le_mul_of_nonneg_left hratio_le
          (mul_nonneg (abs_nonneg a) (Real.rpow_nonneg (by linarith) _))).trans_eq (mul_one _)
    · simp only [hzero, zero_mul, integral_zero]
      exact tendsto_const_nhds
    · let eps := min M.beta (M.beta - a) / 2
      have heps : 0 < eps := div_pos (lt_min hRV.1 (sub_pos.mpr ha)) (by norm_num)
      have hepsbeta : eps < M.beta := by
        dsimp [eps]
        linarith [min_le_left M.beta (M.beta - a)]
      have hepsgap : a - M.beta + eps - 1 < -1 := by
        dsimp [eps]
        linarith [min_le_right M.beta (M.beta - a)]
      obtain ⟨T, hT, hbound⟩ := tail_potter_integrand_bound (tailProb M) heps hepsbeta
        ((tailProb_antitone M).antitoneOn (Set.Ioi 0)) (fun t _ => tailProb_nonneg M t)
        (Eventually.of_forall (tailProb_pos_of_regularVariation M hRV))
        (by simpa only [mul_comm] using tailProb_ratio_limit M hRV (x := 2) (by norm_num))
        (a := a)
      apply tail_integral_tendsto_of_bound M hRV a
        (fun r => (|a| * (2 : ℝ) ^ (M.beta - eps)) * r ^ (a - M.beta + eps - 1))
      · exact (integrableOn_Ioi_rpow_of_lt hepsgap (by norm_num : (0 : ℝ) < 1)).const_mul _
      · filter_upwards [eventually_ge_atTop T] with t ht r hr
        exact hbound t ht r hr.le
  have hfinal := hlim.const_add 1
  rw [pareto_tail_power_integral ha] at hfinal
  exact hfinal

end Papers.TbsExtremeEffects

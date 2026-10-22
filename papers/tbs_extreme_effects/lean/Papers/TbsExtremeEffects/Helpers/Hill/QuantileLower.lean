module
public import Papers.TbsExtremeEffects.Helpers.Hill.NominalProductLaw
public import Papers.TbsExtremeEffects.Helpers.TailSurvival

/-! A single nominal component gives a polynomial lower tail and quantile growth. -/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory Filter
open scoped BigOperators Topology

/-- If [the scale is positive](hyp:ha), [the threshold is at least the scale](hyp:hr), [the variable is measurable](hyp:hW), and [its rescaling has the stated Pareto-II law](hyp:hLaw), then [its tail probability is at least the displayed polynomial bound](goal). -/
-- @node: hill_scaled_paretoII_tail_lower
lemma hill_scaled_paretoII_tail_lower {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (W : Ω → ℝ) {beta a r : ℝ}
    (ha : 0 < a) (hr : a ≤ r) (hW : Measurable W)
    (hLaw : IsParetoTypeII (P.map (fun z => W z / a)) beta) :
    (a / 2) ^ beta * r ^ (-beta) ≤ P.real {z | r < W z} := by
  have hrpos : 0 < r := ha.trans_le hr
  rw [hill_scaled_paretoII_survival P W ha hrpos.le hW hLaw]
  have hbase : 1 + r / a ≤ r / (a / 2) := by
    have hratio : 1 ≤ r / a := (le_div_iff₀ ha).mpr (by simpa using hr)
    rw [div_div_eq_mul_div]
    rw [mul_comm r 2, mul_div_assoc]
    nlinarith
  calc
    _ = (r / (a / 2)) ^ (-beta) := by
      rw [Real.div_rpow hrpos.le (by positivity : 0 ≤ a / 2),
        Real.rpow_neg (by positivity : 0 ≤ a / 2), div_inv_eq_mul, mul_comm]
    _ ≤ _ := Real.rpow_le_rpow_of_nonpos (by positivity) hbase
      (by linarith [hLaw.beta_pos])

/-- If [the tail-shape parameter is positive](hyp:hb), [all component weights are positive](hyp:ha), and [the threshold is at least the selected weight](hyp:hr), then [the nominal weighted-sum tail probability has the displayed one-component polynomial lower bound](goal). -/
-- @node: hill_nominal_sum_tail_lower
lemma hill_nominal_sum_tail_lower {m : ℕ} {beta r : ℝ}
    (hb : 0 < beta) (a : Fin m → ℝ) (ha : ∀ i, 0 < a i)
    (i : Fin m) (hr : a i ≤ r) :
    (a i / 2) ^ beta * r ^ (-beta) ≤
      (hillNominalComponentLaw beta m).real {z | r < ∑ j, a j * z j} := by
  let P := hillNominalComponentLaw beta m
  let := hill_nominal_probability hb m
  have hpos : ∀ᵐ z ∂P, ∀ j, 0 ≤ a j * z j := by
    rw [ae_all_iff]
    intro j
    exact hill_scaled_paretoII_nonneg_ae P (fun z => a j * z j) (ha j)
      (by fun_prop) (hill_nominal_weighted_coordinate_law hb a ha j)
  apply (hill_scaled_paretoII_tail_lower P (fun z => a i * z i) (ha i) hr
    (by fun_prop) (hill_nominal_weighted_coordinate_law hb a ha i)).trans
  apply ENNReal.toReal_mono (measure_ne_top P _)
  apply measure_mono_ae
  filter_upwards [hpos] with z hz
  intro hi
  exact hi.trans_le (Finset.single_le_sum (fun j _ => hz j) (Finset.mem_univ i))

/-- If [the tail-shape parameter is positive](hyp:hb), [the matrix is entrywise nonnegative](hyp:hA), [each column has positive ℓ¹ norm](hyp:ha), and [the threshold is at least the selected column norm](hyp:hr), then [the nominal matrix-radius tail probability has the displayed polynomial lower bound](goal). -/
-- @node: hill_nominal_matrix_tail_lower
lemma hill_nominal_matrix_tail_lower {d m : ℕ} {beta r : ℝ}
    (hb : 0 < beta) (A : Matrix (Fin d) (Fin m) ℝ)
    (hA : ∀ r i, 0 ≤ A r i)
    (ha : ∀ i, 0 < l1Norm (fun r => A r i)) (i : Fin m)
    (hr : l1Norm (fun r => A r i) ≤ r) :
    (l1Norm (fun r => A r i) / 2) ^ beta * r ^ (-beta) ≤
      ((hillNominalComponentLaw beta m).map (fun z => l1Norm (A.mulVec z))).real
        (Set.Ioi r) := by
  let P := hillNominalComponentLaw beta m
  let := hill_nominal_probability hb m
  have hpos' : ∀ j : Fin m, ∀ᵐ z ∂P, 0 ≤ z j := by
    intro j
    have hh := hill_scaled_paretoII_nonneg_ae P (fun z => (1 : ℝ) * z j)
      (by norm_num : (0 : ℝ) < 1) (by fun_prop)
      (by simpa only [one_mul, div_one] using hill_nominal_coordinate_law hb j)
    simpa only [one_mul] using hh
  have hpos : ∀ᵐ z ∂P, z ∈ nonnegativeOrthant :=
    (ae_all_iff.mpr hpos' : ∀ᵐ z ∂P, ∀ j : Fin m, 0 ≤ z j)
  rw [map_measureReal_apply (by fun_prop) measurableSet_Ioi]
  apply (hill_nominal_sum_tail_lower hb (fun i => l1Norm (fun r => A r i)) ha i hr).trans
  apply ENNReal.toReal_mono (measure_ne_top P _)
  apply measure_mono_ae
  filter_upwards [hpos] with z hz
  change (r < ∑ j, l1Norm (fun r => A r j) * z j) → r < l1Norm (A.mulVec z)
  rw [hill_radial_matrix_sum A hA hz]
  exact fun h => h

/-- If [the tail exponent is positive](hyp:hb), [the polynomial constant is positive](hyp:hC), [the quantile level is positive](hyp:hv), [the radius is positive](hyp:hr), and [the reciprocal level is at least the polynomial tail bound](hyp:htail), then [the radius is at least the displayed polynomial quantile lower bound](goal). -/
-- @node: hill_quantile_lower_of_polynomial_tail
lemma hill_quantile_lower_of_polynomial_tail {beta C v r : ℝ}
    (hb : 0 < beta) (hC : 0 < C) (hv : 0 < v) (hr : 0 < r)
    (htail : C * r ^ (-beta) ≤ v⁻¹) :
    C ^ (1 / beta) * v ^ (1 / beta) ≤ r := by
  have hpower : C * v ≤ r ^ beta := by
    rw [Real.rpow_neg hr.le, ← div_eq_mul_inv] at htail
    have hh := (div_le_iff₀ (Real.rpow_pos_of_pos hr beta)).mp htail
    have := mul_le_mul_of_nonneg_right hh hv.le
    simpa only [mul_assoc, mul_left_comm v⁻¹, inv_mul_cancel₀ hv.ne', one_mul, mul_one] using this
  calc
    _ = (C * v) ^ (1 / beta) := (Real.mul_rpow hC.le hv.le).symm
    _ ≤ (r ^ beta) ^ (1 / beta) := Real.rpow_le_rpow (by positivity) hpower (by positivity)
    _ = r := by simpa only [one_div] using Real.rpow_rpow_inv hr.le hb.ne'

/-- If [the survival function is antitone](hyp:hF), [its value at the cutoff is positive](hyp:hb), [the reciprocal level is below that value](hyp:hv), and [the quantile has that reciprocal survival value](hyp:hQ), then [the quantile lies above the cutoff](goal). -/
-- @node: hill_quantile_above_cutoff
lemma hill_quantile_above_cutoff (F Q : ℝ → ℝ) (b : ℝ)
    (hF : Antitone F) (hb : 0 < F b) {v : ℝ}
    (hv : v⁻¹ < F b) (hQ : F (Q v) = v⁻¹) : b < Q v := by
  by_contra h
  have hle := hF (le_of_not_gt h)
  rw [hQ] at hle
  exact (not_le_of_gt hv) hle

/-- If [the model noise is regularly varying](hyp:hRV) and [the quantile has reciprocal tail probability above its base level](hyp:hQ), then [there is a positive threshold above the base level after which every quantile exceeds the fixed radius](goal). -/
-- @node: hill_tail_quantile_eventually_above
lemma hill_tail_quantile_eventually_above (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (Q : ℝ → ℝ) {vBase : ℝ}
    (hQ : ∀ v ≥ vBase, tailProb M (Q v) = v⁻¹) (b : ℝ) :
    ∃ V : ℝ, vBase ≤ V ∧ 0 < V ∧ ∀ v ≥ V, b < Q v := by
  have hsmall : ∀ᶠ v : ℝ in atTop, v⁻¹ < tailProb M b :=
    (tendsto_order.mp tendsto_inv_atTop_zero).2 _
      (tailProb_pos_of_regularVariation M hRV b)
  obtain ⟨T, hT⟩ := eventually_atTop.mp hsmall
  refine ⟨max (max vBase T) 1, ?_, ?_, ?_⟩
  · exact (le_max_left _ _).trans (le_max_left _ _)
  · exact zero_lt_one.trans_le (le_max_right _ _)
  · intro v hv
    have hvBase : vBase ≤ v :=
      ((le_max_left _ _).trans (le_max_left _ _)).trans hv
    have hvT : T ≤ v :=
      ((le_max_right _ _).trans (le_max_left _ _)).trans hv
    exact hill_quantile_above_cutoff (tailProb M) Q b (tailProb_antitone M)
      (tailProb_pos_of_regularVariation M hRV b) (hT v hvT) (hQ v hvBase)

end Papers.TbsExtremeEffects

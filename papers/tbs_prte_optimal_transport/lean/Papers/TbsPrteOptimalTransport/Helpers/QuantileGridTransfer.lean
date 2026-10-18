module
public import Papers.TbsPrteOptimalTransport.Helpers.LearnerInterpolation
public import Papers.TbsPrteOptimalTransport.Helpers.QuantileSorting
/-! Transfer of sorted interior-grid errors to integrated quantile interpolation errors. -/
public section
set_option linter.style.openClassical false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

-- @node: interior_grid_sum_eq
/-- [Summing a sequence over the interior grid indices gives the same result whether the indices are enumerated from zero and shifted by one or taken directly from one through the grid size minus one](goal). -/
lemma interior_grid_sum_eq (N : ℕ) (f : ℕ → ℝ) :
    (∑ i : Fin (N - 1), f (i + 1)) = ∑ m ∈ Finset.Icc 1 (N - 1), f m := by
  apply Finset.sum_bij (fun i _ => i.val + 1)
  · intro i hi
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro i hi j hj he
    apply Fin.ext
    omega
  · intro m hm
    have hm' := Finset.mem_Icc.mp hm
    exact ⟨⟨m - 1, by omega⟩, Finset.mem_univ _, by change m - 1 + 1 = m; omega⟩
  · intro i hi
    rfl

-- @node: excluded_quantile_grid_card_le
/-- If [the grid size is positive](hyp:hN), [the number of interior grid points outside the trimmed interval is at most twice the ceiling of the grid size times the trimming width](goal). -/
lemma excluded_quantile_grid_card_le (N : ℕ) (hN : 0 < N) (eps : ℝ) :
    ((Finset.Icc 1 (N - 1)).filter
      (fun (m : ℕ) => (m : ℝ) / N < eps ∨ 1 - eps < (m : ℝ) / N)).card ≤
        2 * Nat.ceil ((N : ℝ) * eps) := by
  let s := Finset.Icc 1 (N - 1)
  let l := s.filter (fun (m : ℕ) => (m : ℝ) / N < eps)
  let r := s.filter (fun (m : ℕ) => 1 - eps < (m : ℝ) / N)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hl : l.card ≤ Nat.ceil ((N : ℝ) * eps) := by
    apply (Finset.card_le_card _).trans_eq (Finset.card_range _)
    intro m hm
    have hml := (Finset.mem_filter.mp hm).2
    apply Finset.mem_range.mpr
    apply Nat.lt_ceil.mpr
    nlinarith [(div_lt_iff₀ hNr).mp hml]
  have hr : r.card ≤ Nat.ceil ((N : ℝ) * eps) := by
    have hinj : Set.InjOn (fun m => N - m) r := by
      intro m hm k hk he
      change N - m = N - k at he
      have hmN := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).2
      have hkN := (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).2
      omega
    have hmaps : Set.MapsTo (fun m => N - m) r (Finset.range (Nat.ceil ((N : ℝ) * eps))) := by
      intro m hm
      have hmN := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).2
      have hmr := (Finset.mem_filter.mp hm).2
      apply Finset.mem_range.mpr
      apply Nat.lt_ceil.mpr
      rw [Nat.cast_sub (by omega : m ≤ N)]
      nlinarith [(lt_div_iff₀ hNr).mp hmr]
    exact (Finset.card_le_card_of_injOn _ hmaps hinj).trans_eq (Finset.card_range _)
  have he : s.filter (fun (m : ℕ) => (m : ℝ) / N < eps ∨ 1 - eps < (m : ℝ) / N) = l ∪ r := by
    ext m
    simp only [l, r, Finset.mem_filter, Finset.mem_union]
    tauto
  rw [he]
  exact (Finset.card_union_le l r).trans (by omega)

-- @node: excluded_quantile_grid_fraction_le
/-- If [the grid size is positive](hyp:hN) and [the trimming width is nonnegative](hyp:heps), [the number of excluded interior points divided by the grid size is at most twice the sum of the trimming width and the reciprocal grid size](goal). -/
lemma excluded_quantile_grid_fraction_le (N : ℕ) (hN : 0 < N) (eps : ℝ)
    (heps : 0 ≤ eps) :
    (((Finset.Icc 1 (N - 1)).filter
      (fun (m : ℕ) => (m : ℝ) / N < eps ∨ 1 - eps < (m : ℝ) / N)).card : ℝ) / N ≤
        2 * (eps + (N : ℝ)⁻¹) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : (((Finset.Icc 1 (N - 1)).filter
      (fun (m : ℕ) => (m : ℝ) / N < eps ∨ 1 - eps < (m : ℝ) / N)).card : ℝ) ≤
        2 * (Nat.ceil ((N : ℝ) * eps) : ℝ) := by
    exact_mod_cast excluded_quantile_grid_card_le N hN eps
  have hceil := Nat.ceil_lt_add_one (mul_nonneg hNr.le heps)
  apply (div_le_iff₀ hNr).mpr
  have hcancel : 2 * (eps + (N : ℝ)⁻¹) * N = 2 * ((N : ℝ) * eps + 1) := by
    field_simp
  rw [hcancel]
  linarith

-- @node: trimmed_quantile_grid_error_sum_le
/-- If [the grid size is positive](hyp:hN), [the trimming width is nonnegative](hyp:heps), [the error cap is nonnegative](hyp:hB), and [every interior grid error is at most that cap](hyp:he), [the full error sum divided by the grid size is at most its trimmed counterpart plus twice the cap times the sum of the trimming width and the reciprocal grid size](goal). -/
lemma trimmed_quantile_grid_error_sum_le (N : ℕ) (hN : 0 < N)
    (eps B : ℝ) (heps : 0 ≤ eps) (hB : 0 ≤ B) (e : ℕ → ℝ)
    (he : ∀ m ∈ Finset.Icc 1 (N - 1), e m ≤ B) :
    (∑ m ∈ Finset.Icc 1 (N - 1), e m) / N ≤
      (∑ m ∈ (Finset.Icc 1 (N - 1)).filter
        (fun (m : ℕ) => eps ≤ (m : ℝ) / N ∧ (m : ℝ) / N ≤ 1 - eps), e m) / N +
        2 * B * (eps + (N : ℝ)⁻¹) := by
  let good := (Finset.Icc 1 (N - 1)).filter
    (fun (m : ℕ) => eps ≤ (m : ℝ) / N ∧ (m : ℝ) / N ≤ 1 - eps)
  let bad := (Finset.Icc 1 (N - 1)).filter
    (fun (m : ℕ) => (m : ℝ) / N < eps ∨ 1 - eps < (m : ℝ) / N)
  have hsplit : (∑ m ∈ good, e m) + (∑ m ∈ bad, e m) =
      ∑ m ∈ Finset.Icc 1 (N - 1), e m := by
    simpa only [good, bad, not_and_or, not_le] using
      Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 (N - 1))
        (fun (m : ℕ) => eps ≤ (m : ℝ) / N ∧ (m : ℝ) / N ≤ 1 - eps) e
  have hb : (∑ m ∈ bad, e m) ≤ (bad.card : ℝ) * B := by
    calc
      _ ≤ ∑ _m ∈ bad, B := Finset.sum_le_sum (fun m hm => he m (Finset.mem_filter.mp hm).1)
      _ = _ := by simp
  have hfrac : (bad.card : ℝ) / N ≤ 2 * (eps + (N : ℝ)⁻¹) :=
    excluded_quantile_grid_fraction_le N hN eps heps
  rw [← hsplit, add_div]
  apply add_le_add (le_refl _)
  calc
    _ ≤ ((bad.card : ℝ) * B) / N := div_le_div_of_nonneg_right hb (Nat.cast_nonneg N)
    _ = ((bad.card : ℝ) / N) * B := by ring
    _ ≤ (2 * (eps + (N : ℝ)⁻¹)) * B := mul_le_mul_of_nonneg_right hfrac hB
    _ = _ := by ring

-- @node: adjacent_grid_error_sum
/-- For [a positive grid size](hyp:hN), [the sum of the two endpoint errors over all adjacent cells equals the two outer endpoint errors plus twice the sum of the interior errors](goal). -/
lemma adjacent_grid_error_sum (e : ℕ → ℝ) (N : ℕ) (hN : 0 < N) :
    (∑ j ∈ Finset.range N, (e j + e (j + 1))) =
      e 0 + e N + 2 * ∑ j ∈ Finset.range (N - 1), e (j + 1) := by
  induction N with
  | zero => omega
  | succ N ih =>
    cases N with
    | zero => simp
    | succ N =>
      rw [Finset.sum_range_succ, ih (by omega)]
      simp only [Nat.add_sub_cancel, Finset.sum_range_succ]
      ring

-- @node: interpolate_quantile_error_interior_integral
/-- For [a positive grid size](hyp:hN), suppose [the target quantile is nondecreasing on the closed unit interval](hyp:hQ), [its values lie between the outcome bounds](hyp:hQr), and [both fitted endpoint values lie between those bounds](hyp:hv0,hvN). Then [the integrated absolute interpolation error over the unit interval, excluding zero, is at most the interior absolute error sum divided by the grid size plus twice the outcome range divided by the grid size](goal). -/
lemma interpolate_quantile_error_interior_integral (N : ℕ) (hN : 0 < N)
    (v : ℕ → ℝ) (Q : ℝ → ℝ) (lo hi : ℝ)
    (hQ : MonotoneOn Q (Icc (0 : ℝ) 1))
    (hQr : ∀ t ∈ Icc (0 : ℝ) 1, Q t ∈ Icc lo hi)
    (hv0 : v 0 ∈ Icc lo hi) (hvN : v N ∈ Icc lo hi) :
    (∫ t in Ioc (0 : ℝ) 1, |interpolate N hN v t - Q t|) ≤
      (∑ j ∈ Finset.range (N - 1),
        |v (j + 1) - Q (((j + 1 : ℕ) : ℝ) / N)|) / N + 2 * (hi - lo) / N := by
  have h0 := hQr 0 ⟨le_rfl, zero_le_one⟩
  have h1 := hQr 1 ⟨zero_le_one, le_rfl⟩
  have he0 : |v 0 - Q 0| ≤ hi - lo := by
    apply abs_le.mpr
    constructor <;> linarith [hv0.1, hv0.2, h0.1, h0.2]
  have heN : |v N - Q 1| ≤ hi - lo := by
    apply abs_le.mpr
    constructor <;> linarith [hvN.1, hvN.2, h1.1, h1.2]
  have hosc : Q 1 - Q 0 ≤ hi - lo := by linarith [h1.2, h0.1]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsum := adjacent_grid_error_sum
    (fun j => |v j - Q ((j : ℝ) / N)|) N hN
  have hnonzero : (N : ℝ) ≠ 0 := ne_of_gt hNr
  simp only [Nat.cast_zero, zero_div, div_self hnonzero] at hsum
  refine (interpolate_quantile_error_unit_integral N hN v Q hQ).trans ?_
  rw [← Finset.sum_div, hsum]
  have hends : |v 0 - Q 0| + |v N - Q 1| ≤ 2 * (hi - lo) := by linarith
  have hbound := add_le_add
    (div_le_div_of_nonneg_right (add_le_add hends
      (le_refl (2 * ∑ j ∈ Finset.range (N - 1), |v (j + 1) - Q (((j + 1 : ℕ) : ℝ) / N)|)))
      (by positivity : 0 ≤ 2 * (N : ℝ)))
    (div_le_div_of_nonneg_right hosc hNr.le)
  exact hbound.trans_eq (by ring)

-- @node: quantile_endpoint_extension_monotone
/-- If [the lower outcome bound does not exceed the upper bound](hyp:hlohi), [the quantile is nondecreasing on the open unit interval](hyp:hQ), and [its interior values lie between the outcome bounds](hyp:hr), [extending it by the lower bound at zero and the upper bound at one gives a nondecreasing function on the closed unit interval](goal). -/
lemma quantile_endpoint_extension_monotone (Q : ℝ → ℝ) (lo hi : ℝ)
    (hlohi : lo ≤ hi) (hQ : MonotoneOn Q (Ioo (0 : ℝ) 1))
    (hr : ∀ t ∈ Ioo (0 : ℝ) 1, Q t ∈ Icc lo hi) :
    MonotoneOn (fun t => if t = 0 then lo else if t = 1 then hi else Q t)
      (Icc (0 : ℝ) 1) := by
  intro s hs t ht hst
  by_cases hs0 : s = 0
  · subst s
    dsimp only
    rw [if_pos (rfl : (0 : ℝ) = 0)]
    split_ifs with ht0 ht1
    · exact le_rfl
    · exact hlohi
    · exact (hr t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩).1
  by_cases ht1 : t = 1
  · subst t
    dsimp only
    rw [if_neg (one_ne_zero : (1 : ℝ) ≠ 0), if_pos (rfl : (1 : ℝ) = 1), if_neg hs0]
    split_ifs with hs1
    · exact le_rfl
    · exact (hr s ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0), lt_of_le_of_ne hs.2 hs1⟩).2
  have hsi : s ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0), lt_of_le_of_lt hst (lt_of_le_of_ne ht.2 ht1)⟩
  have hti : t ∈ Ioo (0 : ℝ) 1 := ⟨hsi.1.trans_le hst, lt_of_le_of_ne ht.2 ht1⟩
  simp only [if_neg hs0, if_neg (ne_of_lt hsi.2), if_neg (ne_of_gt hti.1), if_neg ht1]
  exact hQ hsi hti hst

universe u v
variable {Ω : Type u} {X Z : Type v} {A : Type*}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]

-- @node: interpolated_sorted_quantile_error_integral
/-- Suppose [the outcome endpoints are known](hyp:he), [the grid size is positive](hyp:hN), [there are at least two cells when fitted endpoints are used](hyp:hInterior), [the target quantile is nondecreasing on the open unit interval](hyp:hQ), and [its values lie between the outcome endpoints](hyp:hr). Then [the integrated absolute error of the sorted interpolated fit is at most the unsorted clipped interior error sum divided by the grid size plus twice the outcome range divided by the grid size](goal). -/
lemma interpolated_sorted_quantile_error_integral (M : LatentIVModel Ω X Z)
    (he : OutcomeEndpointsKnown M) (raw : ℕ → A → ℕ → X → ℝ)
    (N : ℕ) (hN : 0 < N) (knownEndpoints : Bool)
    (hInterior : knownEndpoints = false → 2 ≤ N) (n : ℕ) (a : A) (x : X)
    (Q : ℝ → ℝ) (hQ : MonotoneOn Q (Ioo (0 : ℝ) 1))
    (hr : ∀ t ∈ Ioo (0 : ℝ) 1, Q t ∈ Icc M.yMin M.yMax) :
    (∫ t in Ioo (0 : ℝ) 1,
      |interpolatedQuantile M raw N hN knownEndpoints hInterior n a x t - Q t|) ≤
      (∑ i : Fin (N - 1),
        |clippedGrid M raw n a (i + 1) x - Q (gridLevel N hN (i + 1))|) / N +
        2 * (M.yMax - M.yMin) / N := by
  let vs := sortedGrid M raw N n a x
  let v := fun m => if m = 0 then (if knownEndpoints then M.yMin else vs.getD 0 M.yMin)
    else if N ≤ m then (if knownEndpoints then M.yMax else vs.getD (N - 2) M.yMax)
    else vs.getD (m - 1) M.yMin
  let Qe := fun t => if t = 0 then M.yMin else if t = 1 then M.yMax else Q t
  have ho : M.yMin ≤ M.yMax := he.1.2 he.2.1
  have hQe : MonotoneOn Qe (Icc (0 : ℝ) 1) :=
    quantile_endpoint_extension_monotone Q M.yMin M.yMax ho hQ hr
  have hQer : ∀ t ∈ Icc (0 : ℝ) 1, Qe t ∈ Icc M.yMin M.yMax := by
    intro t ht
    dsimp only [Qe]
    split_ifs with ht0 ht1
    · exact ⟨le_rfl, ho⟩
    · exact ⟨ho, le_rfl⟩
    · exact hr t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
  have hvs : ∀ y ∈ vs, y ∈ Icc M.yMin M.yMax := by
    intro y hy
    have hm := (List.mergeSort_perm _ _).mem_iff.mp hy
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hm
    exact ⟨le_min ho (le_max_left _ _), min_le_left _ _⟩
  have hv : ∀ m, v m ∈ Icc M.yMin M.yMax := by
    intro m
    dsimp only [v]
    split_ifs <;> first
      | exact ⟨le_rfl, ho⟩
      | exact ⟨ho, le_rfl⟩
      | exact list_getD_interval _ _ _ _ ⟨le_rfl, ho⟩ hvs _
      | exact list_getD_interval _ _ _ _ ⟨ho, le_rfl⟩ hvs _
  have hi := interpolate_quantile_error_interior_integral N hN v Qe
    M.yMin M.yMax hQe hQer (hv 0) (hv N)
  have hgrid (i : Fin (N - 1)) :
      |v (i + 1) - Qe (((i + 1 : ℕ) : ℝ) / N)| =
        |vs.getD i M.yMin - Q (gridLevel N hN (i + 1))| := by
    have hiN : i.val + 1 < N := by omega
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have ht : (((i + 1 : ℕ) : ℝ) / N) ∈ Ioo (0 : ℝ) 1 := by
      constructor
      · exact div_pos (by positivity) hNr
      · exact (div_lt_one hNr).mpr (by exact_mod_cast hiN)
    simp only [v, Qe, gridLevel, if_neg (show i.val + 1 ≠ 0 by omega),
      if_neg (show ¬N ≤ i.val + 1 by omega), Nat.add_sub_cancel,
      if_neg (ne_of_gt ht.1), if_neg (ne_of_lt ht.2)]
  have hsum : (∑ j ∈ Finset.range (N - 1),
      |v (j + 1) - Qe (((j + 1 : ℕ) : ℝ) / N)|) =
      ∑ i : Fin (N - 1), |vs.getD i M.yMin - Q (gridLevel N hN (i + 1))| := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl (fun i _ => hgrid i)
  rw [hsum] at hi
  have heq : (∫ t in Ioo (0 : ℝ) 1,
      |interpolatedQuantile M raw N hN knownEndpoints hInterior n a x t - Q t|) =
      ∫ t in Ioc (0 : ℝ) 1, |interpolate N hN v t - Qe t| := by
    rw [integral_Ioc_eq_integral_Ioo]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    simp only [interpolatedQuantile, v, vs, Qe,
      if_neg (ne_of_gt ht.1), if_neg (ne_of_lt ht.2)]
  rw [heq]
  exact hi.trans (add_le_add
    (div_le_div_of_nonneg_right
      (sorted_grid_quantile_error_sum_le M raw N hN n a x Q hQ)
      (Nat.cast_nonneg N)) (le_refl _))

-- @node: interpolated_selected_quantile_error_integral
/-- Given [fallback probability laws supported on the outcome set](hyp:zeroLaw), suppose [the structural assumptions hold](hyp:h), [the outcome endpoints are known](hyp:he), [the fitted propensities are jointly measurable at every sample size](hyp:hp), [the grid size is positive](hyp:hN), and [there are at least two cells when fitted endpoints are used](hyp:hInterior). Then [for almost every covariate value, the lower propensity times the integrated absolute error relative to the selected quantile is at most the similarly weighted clipped interior error sum divided by the grid size plus twice the outcome range divided by the grid size](goal). -/
lemma interpolated_selected_quantile_error_integral (M : LatentIVModel Ω X Z)
    (zeroLaw : X → {ν : ProbabilityMeasure ℝ // ν.toMeasure M.Ysetᶜ = 0})
    [MeasurableSpace A] (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (pHat : ℕ → A → Z → X → ℝ) (delta : ℕ → ℝ)
    (hp : ∀ n, Measurable (fun ax : A × Z × X => pHat n ax.1 ax.2.1 ax.2.2))
    (raw : ℕ → A → ℕ → X → ℝ) (N : ℕ) (hN : 0 < N) (knownEndpoints : Bool)
    (hInterior : knownEndpoints = false → 2 ≤ N) (n : ℕ) (a : A) :
    ∀ᵐ x ∂xLaw M,
      pLow M.prop x * (∫ t in Ioo (0 : ℝ) 1,
        |interpolatedQuantile M raw N hN knownEndpoints hInterior n a x t -
          selQuantile M zeroLaw pHat delta n a x t|) ≤
      pLow M.prop x * (N : ℝ)⁻¹ *
        (∑ i : Fin (N - 1), |clippedGrid M raw n a (i + 1) x -
          selQuantile M zeroLaw pHat delta n a x (gridLevel N hN (i + 1))|) +
        2 * (M.yMax - M.yMin) / N := by
  filter_upwards [selected_quantile_supported M zeroLaw h he pHat delta hp n a] with x hx
  have hr : ∀ t ∈ Ioo (0 : ℝ) 1,
      selQuantile M zeroLaw pHat delta n a x t ∈ Icc M.yMin M.yMax := by
    intro t ht
    exact ⟨he.1.2 (hx t ht), he.2.2 (hx t ht)⟩
  have hb := interpolated_sorted_quantile_error_integral M he raw N hN
    knownEndpoints hInterior n a x (selQuantile M zeroLaw pHat delta n a x)
    (Causalean.Stat.monotoneOn_quantile _) hr
  have ha := (population_support_endpoints M x).1
  have hrem : 0 ≤ 2 * (M.yMax - M.yMin) / (N : ℝ) := by
    exact div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr (he.1.2 he.2.1)))
      (Nat.cast_nonneg N)
  have hb' := mul_le_mul_of_nonneg_left hb ha.1
  rw [mul_add, div_eq_mul_inv, ← mul_assoc] at hb'
  refine hb'.trans (add_le_add (le_of_eq (by ring)) ?_)
  exact (mul_le_mul_of_nonneg_right ha.2 hrem).trans_eq (one_mul _)

-- @node: interpolated_selected_trimmed_error_integral
/-- Given [fallback probability laws supported on the outcome set](hyp:zeroLaw), suppose [the structural assumptions hold](hyp:h), [the outcome endpoints are known](hyp:he), [the fitted propensities are jointly measurable at every sample size](hyp:hp), [every grid size is positive](hyp:hMQ), [every trimming width is nonnegative](hyp:heps), and [every grid has at least two cells when fitted endpoints are used](hyp:hInterior). Then [for almost every covariate value, the lower propensity times the integrated absolute error relative to the selected quantile is bounded by the weighted trimmed clipped error sum divided by the grid size, plus twice the outcome range times the trimming width and four times the outcome range divided by the grid size](goal). -/
lemma interpolated_selected_trimmed_error_integral (M : LatentIVModel Ω X Z)
    (zeroLaw : X → {ν : ProbabilityMeasure ℝ // ν.toMeasure M.Ysetᶜ = 0})
    [MeasurableSpace A] (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (pHat : ℕ → A → Z → X → ℝ) (delta : ℕ → ℝ)
    (hp : ∀ n, Measurable (fun ax : A × Z × X => pHat n ax.1 ax.2.1 ax.2.2))
    (raw : ℕ → A → ℕ → X → ℝ) (MQ : ℕ → ℕ) (hMQ : ∀ n, 0 < MQ n)
    (eps : ℕ → ℝ) (heps : ∀ n, 0 ≤ eps n) (knownEndpoints : Bool)
    (hInterior : knownEndpoints = false → ∀ n, 2 ≤ MQ n) (n : ℕ) (a : A) :
    ∀ᵐ x ∂xLaw M,
      pLow M.prop x * (∫ t in Ioo (0 : ℝ) 1,
        |interpolatedQuantile M raw (MQ n) (hMQ n) knownEndpoints
          (fun hk => hInterior hk n) n a x t - selQuantile M zeroLaw pHat delta n a x t|) ≤
      pLow M.prop x * (MQ n : ℝ)⁻¹ *
        (∑ m ∈ interiorIdx MQ hMQ eps n, |clippedGrid M raw n a m x -
          selQuantile M zeroLaw pHat delta n a x (gridLevel (MQ n) (hMQ n) m)|) +
        2 * (M.yMax - M.yMin) * eps n + 4 * (M.yMax - M.yMin) * (MQ n : ℝ)⁻¹ := by
  filter_upwards [interpolated_selected_quantile_error_integral M zeroLaw h he pHat delta hp
    raw (MQ n) (hMQ n) knownEndpoints (fun hk => hInterior hk n) n a,
    selected_quantile_supported M zeroLaw h he pHat delta hp n a] with x hb hx
  let B := M.yMax - M.yMin
  let e := fun m => |clippedGrid M raw n a m x -
    selQuantile M zeroLaw pHat delta n a x (gridLevel (MQ n) (hMQ n) m)|
  have hB : 0 ≤ B := sub_nonneg.mpr (he.1.2 he.2.1)
  have hNr : (0 : ℝ) < MQ n := by exact_mod_cast hMQ n
  have heBound : ∀ m ∈ Finset.Icc 1 (MQ n - 1), e m ≤ B := by
    intro m hm
    have hm' := Finset.mem_Icc.mp hm
    have ht : gridLevel (MQ n) (hMQ n) m ∈ Ioo (0 : ℝ) 1 := by
      constructor
      · exact div_pos (by exact_mod_cast (show 0 < m by omega)) hNr
      · exact (div_lt_one hNr).mpr (by exact_mod_cast (show m < MQ n by omega))
    have hq := hx _ ht
    have hc : clippedGrid M raw n a m x ∈ Icc M.yMin M.yMax :=
      ⟨le_min (he.1.2 he.2.1) (le_max_left _ _), min_le_left _ _⟩
    apply abs_le.mpr
    constructor <;> dsimp only [B] <;> linarith [hc.1, hc.2, he.1.2 hq, he.2.2 hq]
  have htrim := trimmed_quantile_grid_error_sum_le (MQ n) (hMQ n)
    (eps n) B (heps n) hB e heBound
  change (∑ m ∈ Finset.Icc 1 (MQ n - 1), e m) / (MQ n : ℝ) ≤
    (∑ m ∈ interiorIdx MQ hMQ eps n, e m) / (MQ n : ℝ) +
      2 * B * (eps n + (MQ n : ℝ)⁻¹) at htrim
  have ha := (population_support_endpoints M x).1
  have htail : 0 ≤ 2 * B * (eps n + (MQ n : ℝ)⁻¹) :=
    mul_nonneg (mul_nonneg (by norm_num) hB)
      (add_nonneg (heps n) (inv_nonneg.mpr hNr.le))
  have hweight := mul_le_mul_of_nonneg_left htrim ha.1
  rw [mul_add] at hweight
  have hweight' : pLow M.prop x * ((∑ m ∈ Finset.Icc 1 (MQ n - 1), e m) / (MQ n : ℝ)) ≤
      pLow M.prop x * ((∑ m ∈ interiorIdx MQ hMQ eps n, e m) / (MQ n : ℝ)) +
        2 * B * (eps n + (MQ n : ℝ)⁻¹) :=
    hweight.trans (add_le_add (le_refl _)
      ((mul_le_mul_of_nonneg_right ha.2 htail).trans_eq (one_mul _)))
  rw [interior_grid_sum_eq (MQ n) e] at hb
  have hfinal := add_le_add hweight' (le_refl (2 * B / (MQ n : ℝ)))
  apply hb.trans
  convert hfinal using 1 <;> dsimp only [e, B] <;> simp only [div_eq_mul_inv] <;> ring

end Papers.TbsPrteOptimalTransport

module
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousLearners
public import Papers.TbsPrteOptimalTransport.Helpers.RegionIntegration
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
/-!
# Exact grid primitives and cumulative interpolation error

Affine integration gives the trapezoidal primitive at every grid point. Cell
averages recover the off-grid cumulative interpolant; monotonicity bounds their
integrated error by a telescoping sum of cell oscillations.
-/
public section
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z]
variable (M : LatentIVModel Ω X Z)

variable {A : Type*} [MeasurableSpace A]
-- @node: cell_average_index_on_cell
/-- For [a positive number of grid cells](hyp:hN), if [the cell index is below the grid size](hyp:hm)
and [the evaluation rank lies between that cell's left endpoint, included, and right endpoint,
excluded](hyp:ht), then [rounding rank times grid size down and capping at the final cell returns
that cell's index](goal). -/
lemma cell_average_index_on_cell (N : ℕ) (hN : 0 < N) (m : ℕ) (hm : m < N)
    (t : ℝ) (ht : t ∈ Ico ((m : ℝ) / N) (((m + 1 : ℕ) : ℝ) / N)) :
    min (N - 1) (Nat.floor (t * N)) = m := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hf : Nat.floor (t * N) = m := by
    apply (Nat.floor_eq_iff (mul_nonneg
      ((div_nonneg (Nat.cast_nonneg m) hNr.le).trans ht.1) hNr.le)).mpr
    constructor
    · exact (div_le_iff₀ hNr).mp ht.1
    · simpa only [Nat.cast_add, Nat.cast_one] using (lt_div_iff₀ hNr).mp ht.2
  rw [hf, min_eq_right (by omega)]

-- @node: interpolate_grid_value
/-- For [a positive number of grid cells](hyp:hN) and [a node index no greater than the grid size](hyp:hm),
[linear interpolation evaluated at that node equals its prescribed grid value](goal). -/
lemma interpolate_grid_value (N : ℕ) (hN : 0 < N) (v : ℕ → ℝ)
    (m : ℕ) (hm : m ≤ N) : interpolate N hN v ((m : ℝ) / N) = v m := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  by_cases hm0 : m = 0
  · subst m
    simp [interpolate]
  by_cases hmN : m = N
  · subst m
    simp [interpolate, div_self (ne_of_gt hNr)]
  have hmp : 0 < (m : ℝ) / N := div_pos (by exact_mod_cast (by omega : 0 < m)) hNr
  have hml : (m : ℝ) / N < 1 := (div_lt_one hNr).mpr (by exact_mod_cast (by omega : m < N))
  unfold interpolate
  rw [if_neg (not_le.mpr hmp), if_neg (not_le.mpr hml),
    div_mul_cancel₀ _ (ne_of_gt hNr), Nat.floor_natCast,
    min_eq_right (by omega : m ≤ N - 1)]
  simp

-- @node: interpolate_on_open_cell
/-- For [a positive number of grid cells](hyp:hN), [a cell index below the grid size](hyp:hm), and
[a rank strictly inside that cell](hyp:ht), [the interpolated value is the linear blend of its two
endpoint values, with weight on the right endpoint equal to rank times grid size minus the cell index](goal). -/
lemma interpolate_on_open_cell (N : ℕ) (hN : 0 < N) (v : ℕ → ℝ)
    (m : ℕ) (hm : m < N) (t : ℝ)
    (ht : t ∈ Ioo ((m : ℝ) / N) (((m + 1 : ℕ) : ℝ) / N)) :
    interpolate N hN v t =
      (1 - (t * N - m)) * v m + (t * N - m) * v (m + 1) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have ht0 : 0 < t := (div_nonneg (Nat.cast_nonneg m) hNr.le).trans_lt ht.1
  have ht1 : t < 1 := ht.2.trans_le ((div_le_one hNr).mpr (by exact_mod_cast (by omega : m + 1 ≤ N)))
  unfold interpolate
  rw [if_neg (not_le.mpr ht0), if_neg (not_le.mpr ht1),
    cell_average_index_on_cell N hN m hm t ⟨ht.1.le, ht.2⟩]

-- @node: measurable_interpolate
/-- With [a positive number of grid cells](hyp:hN), [the linear interpolant of any real grid values
is measurable as a function of rank](goal). -/
@[fun_prop] lemma measurable_interpolate (N : ℕ) (hN : 0 < N) (v : ℕ → ℝ) :
    Measurable (interpolate N hN v) := by
  unfold interpolate
  apply Measurable.ite measurableSet_Iic measurable_const
  apply Measurable.ite measurableSet_Ici measurable_const
  fun_prop

-- @node: interpolate_integrable_on_unit
/-- With [a positive number of grid cells](hyp:hN), [the linear interpolant of any real grid values
is integrable over the closed unit interval](goal). -/
lemma interpolate_integrable_on_unit (N : ℕ) (hN : 0 < N) (v : ℕ → ℝ) :
    IntegrableOn (interpolate N hN v) (Icc (0 : ℝ) 1) := by
  let C := ∑ m ∈ Finset.range (N + 1), ‖v m‖
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hv (m : ℕ) (hm : m ≤ N) : ‖v m‖ ≤ C := by
    exact Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_range.mpr (by omega))
  apply Integrable.of_bound (measurable_interpolate N hN v).aestronglyMeasurable C
  filter_upwards [] with t
  unfold interpolate
  split_ifs with ht0 ht1
  · exact hv 0 (Nat.zero_le _)
  · exact hv N le_rfl
  · let m := min (N - 1) (Nat.floor (t * N))
    let a := t * N - (m : ℝ)
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have htpos : 0 < t := lt_of_not_ge ht0
    have htlt : t < 1 := lt_of_not_ge ht1
    have hf : Nat.floor (t * N) < N := (Nat.floor_lt (mul_nonneg htpos.le hNr.le)).mpr (by nlinarith)
    have hm : m = Nat.floor (t * N) := min_eq_right (by omega)
    have ha0 : 0 ≤ a := by
      dsimp [a]
      rw [hm]
      exact sub_nonneg.mpr (Nat.floor_le (mul_nonneg htpos.le hNr.le))
    have ha1 : a ≤ 1 := by
      dsimp [a]
      rw [hm]
      linarith [Nat.lt_floor_add_one (t * N)]
    have h0 := hv m (by rw [hm]; omega)
    have h1 := hv (m + 1) (by rw [hm]; omega)
    rw [Real.norm_eq_abs, abs_le] at h0 h1 ⊢
    change -C ≤ (1-a) * v m + a * v (m+1) ∧ (1-a) * v m + a * v (m+1) ≤ C
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr h0.1),
        mul_nonneg ha0 (sub_nonneg.mpr h1.1)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr h0.2),
        mul_nonneg ha0 (sub_nonneg.mpr h1.2)]

-- @node: interpolate_cell_integral
/-- For [a positive number of grid cells](hyp:hN) and [a cell index below the grid size](hyp:hm),
[the integral of the linear interpolant over that cell equals the sum of its endpoint values
divided by twice the grid size](goal). -/
lemma interpolate_cell_integral (N : ℕ) (hN : 0 < N) (v : ℕ → ℝ)
    (m : ℕ) (hm : m < N) :
    (∫ t in Ioc ((m : ℝ)/N) (((m+1 : ℕ) : ℝ)/N), interpolate N hN v t) =
      (v m + v (m+1)) / (2 * N) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hab : (m : ℝ)/N ≤ ((m+1 : ℕ) : ℝ)/N := by
    gcongr
    exact Nat.le_succ m
  let c := v m - (m : ℝ) * (v (m+1) - v m)
  let d := (N : ℝ) * (v (m+1) - v m)
  calc
    _ = ∫ t in Ioc ((m : ℝ)/N) (((m+1 : ℕ) : ℝ)/N), c + t*d := by
      rw [integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
      apply setIntegral_congr_fun measurableSet_Ioo
      intro t ht
      rw [interpolate_on_open_cell N hN v m hm t ht]
      dsimp [c, d]
      ring
    _ = ∫ t in ((m : ℝ)/N)..(((m+1 : ℕ) : ℝ)/N), c + t*d :=
      (intervalIntegral.integral_of_le hab).symm
    _ = _ := by
      have hic : IntervalIntegrable (fun _ : ℝ => c) volume ((m : ℝ)/N) (((m+1 : ℕ) : ℝ)/N) :=
        continuous_const.intervalIntegrable _ _
      have hid : IntervalIntegrable (fun t : ℝ => t*d) volume ((m : ℝ)/N) (((m+1 : ℕ) : ℝ)/N) :=
        (continuous_id.mul_const d).intervalIntegrable _ _
      rw [intervalIntegral.integral_add hic hid,
        intervalIntegral.integral_const, intervalIntegral.integral_mul_const,
        integral_id]
      dsimp [c, d]
      simp only [smul_eq_mul, Nat.cast_add, Nat.cast_one]
      field_simp
      <;> ring

-- @node: interpolate_grid_primitive
/-- For [a positive number of grid cells](hyp:hN) and [a node index no greater than the grid size](hyp:hm),
[the integral of the linear interpolant from zero to that node equals its cumulative trapezoidal
grid sum through that node](goal). -/
lemma interpolate_grid_primitive (N : ℕ) (hN : 0 < N) (v : ℕ → ℝ)
    (m : ℕ) (hm : m ≤ N) :
    quantilePrimitive (interpolate N hN v) ((m : ℝ)/N) =
      cumulativeGrid N hN (interpolate N hN v) m := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hi := interpolate_integrable_on_unit N hN v
  induction m with
  | zero => simp [quantilePrimitive, cumulativeGrid]
  | succ m ih =>
    have hm' : m < N := by omega
    have ha : 0 ≤ (m : ℝ)/N := div_nonneg (Nat.cast_nonneg _) hNr.le
    have hab : (m : ℝ)/N ≤ ((m+1 : ℕ) : ℝ)/N := by
      gcongr
      exact Nat.le_succ m
    have hb : ((m+1 : ℕ) : ℝ)/N ≤ 1 := (div_le_one hNr).mpr (by exact_mod_cast hm)
    rw [quantilePrimitive, integral_adjacent_Ioc _ ha hab
      (hi.mono_set (fun t ht => ⟨ht.1.le, ht.2.trans hb⟩))]
    change quantilePrimitive (interpolate N hN v) ((m : ℝ)/N) + _ = _
    rw [ih hm'.le, interpolate_cell_integral N hN v m hm']
    simp only [cumulativeGrid, Finset.sum_range_succ,
      interpolate_grid_value N hN v m hm'.le,
      interpolate_grid_value N hN v (m+1) hm]
    ring

-- @node: measurable_cell_average_quantile
/-- With [a positive number of grid cells](hyp:hN), [the function that assigns to each rank the
average of the quantile values at its selected cell's endpoints is measurable](goal). -/
@[fun_prop] lemma measurable_cell_average_quantile (N : ℕ) (hN : 0 < N) (Q : ℝ → ℝ) :
    Measurable (cellAverageQuantile N hN Q) := by
  unfold cellAverageQuantile
  fun_prop

-- @node: cell_average_quantile_integrable
/-- With [a positive number of grid cells](hyp:hN), [the function of cell endpoint quantile averages
is integrable over the closed unit interval](goal). -/
lemma cell_average_quantile_integrable (N : ℕ) (hN : 0 < N) (Q : ℝ → ℝ) :
    IntegrableOn (cellAverageQuantile N hN Q) (Icc (0 : ℝ) 1) := by
  let v : ℕ → ℝ := fun m => (Q ((m : ℝ) / N) + Q (((m+1 : ℕ) : ℝ) / N)) / 2
  apply Integrable.of_bound (measurable_cell_average_quantile N hN Q).aestronglyMeasurable
    (∑ m ∈ Finset.range N, ‖v m‖)
  filter_upwards [] with t
  change ‖v (min (N-1) (Nat.floor (t*N)))‖ ≤ _
  apply Finset.single_le_sum (fun m _ => norm_nonneg (v m))
  simp only [Finset.mem_range]
  exact lt_of_le_of_lt (min_le_left _ _) (by omega)

-- @node: cell_average_partial_integral
/-- For [a positive number of grid cells](hyp:hN), [a cell index below the grid size](hyp:hm), and
[a rank in that closed cell](hyp:ht), [the integral of the cell-average quantile from the cell's left
endpoint to that rank equals the distance traveled times the average of the two endpoint quantile values](goal). -/
lemma cell_average_partial_integral (N : ℕ) (hN : 0 < N) (Q : ℝ → ℝ)
    (m : ℕ) (hm : m < N) (t : ℝ)
    (ht : t ∈ Icc ((m : ℝ) / N) (((m+1 : ℕ) : ℝ) / N)) :
    (∫ u in Ioc ((m : ℝ)/N) t, cellAverageQuantile N hN Q u) =
      (t - (m : ℝ)/N) * (Q ((m : ℝ)/N) + Q (((m+1 : ℕ) : ℝ)/N)) / 2 := by
  rw [integral_Ioc_eq_integral_Ioo]
  calc
    _ = ∫ u in Ioo ((m : ℝ)/N) t,
        (Q ((m : ℝ)/N) + Q (((m+1 : ℕ) : ℝ)/N)) / 2 := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro u hu
      dsimp only [cellAverageQuantile]
      rw [cell_average_index_on_cell N hN m hm u ⟨hu.1.le, hu.2.trans_le ht.2⟩]
    _ = _ := by
      rw [setIntegral_const, measureReal_def, Real.volume_Ioo, ENNReal.toReal_ofReal (sub_nonneg.mpr ht.1)]
      simp only [smul_eq_mul]
      ring

-- @node: cell_average_grid_primitive
/-- For [a positive number of grid cells](hyp:hN) and [a node index no greater than the grid size](hyp:hm),
[the integral of the cell-average quantile from zero to that node equals the original quantile's
cumulative trapezoidal grid sum through that node](goal). -/
lemma cell_average_grid_primitive (N : ℕ) (hN : 0 < N) (Q : ℝ → ℝ)
    (m : ℕ) (hm : m ≤ N) :
    quantilePrimitive (cellAverageQuantile N hN Q) ((m : ℝ)/N) =
      cumulativeGrid N hN Q m := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hi := cell_average_quantile_integrable N hN Q
  induction m with
  | zero => simp [quantilePrimitive, cumulativeGrid]
  | succ m ih =>
    have hm' : m < N := by omega
    have ha : 0 ≤ (m : ℝ)/N := div_nonneg (Nat.cast_nonneg _) hNr.le
    have hab : (m : ℝ)/N ≤ ((m+1 : ℕ) : ℝ)/N := by gcongr; exact Nat.le_succ m
    have hb : ((m+1 : ℕ) : ℝ)/N ≤ 1 := (div_le_one hNr).mpr (by exact_mod_cast hm)
    rw [quantilePrimitive, integral_adjacent_Ioc _ ha hab
      (hi.mono_set (fun u hu => ⟨hu.1.le, hu.2.trans hb⟩))]
    change quantilePrimitive (cellAverageQuantile N hN Q) ((m : ℝ)/N) + _ = _
    rw [ih hm'.le, cell_average_partial_integral N hN Q m hm' _ ⟨hab, le_rfl⟩]
    simp only [cumulativeGrid, Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
    field_simp
    <;> ring

-- @node: cell_average_primitive
/-- For [a positive number of grid cells](hyp:hN) and [a rank in the closed unit interval](hyp:ht),
[the integral of the cell-average quantile from zero to that rank equals the linear interpolant
of the original quantile's cumulative trapezoidal grid values](goal). -/
lemma cell_average_primitive (N : ℕ) (hN : 0 < N) (Q : ℝ → ℝ)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    quantilePrimitive (cellAverageQuantile N hN Q) t = interpCumQuantile N hN Q t := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  by_cases ht0 : t = 0
  · subst t
    simp [quantilePrimitive, interpCumQuantile, interpolate, cumulativeGrid]
  by_cases ht1 : t = 1
  · subst t
    rw [show (1 : ℝ) = (N : ℝ)/N from (div_self (ne_of_gt hNr)).symm,
      cell_average_grid_primitive N hN Q N le_rfl]
    simp [interpCumQuantile, interpolate, div_self (ne_of_gt hNr)]
  have htp : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  have htl : t < 1 := lt_of_le_of_ne ht.2 ht1
  let m := Nat.floor (t*N)
  have hm : m < N := (Nat.floor_lt (mul_nonneg htp.le hNr.le)).mpr (by nlinarith)
  have hmin : min (N-1) m = m := min_eq_right (by omega)
  have hmt : (m : ℝ)/N ≤ t := (div_le_iff₀ hNr).mpr (Nat.floor_le (by positivity))
  have htm : t ≤ ((m+1 : ℕ) : ℝ)/N := by
    apply (le_div_iff₀ hNr).mpr
    simpa only [Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one (t*N)).le
  have hi := cell_average_quantile_integrable N hN Q
  rw [quantilePrimitive, integral_adjacent_Ioc _ (by positivity) hmt
    (hi.mono_set (fun u hu => ⟨hu.1.le, hu.2.trans ht.2⟩))]
  change quantilePrimitive (cellAverageQuantile N hN Q) ((m : ℝ)/N) + _ = _
  rw [cell_average_grid_primitive N hN Q m hm.le,
    cell_average_partial_integral N hN Q m hm t ⟨hmt, htm⟩]
  unfold interpCumQuantile interpolate
  rw [if_neg (not_le.mpr htp), if_neg (not_le.mpr htl)]
  change _ = (1 - (t*N - (min (N-1) m : ℕ))) * cumulativeGrid N hN Q (min (N-1) m) +
    (t*N - (min (N-1) m : ℕ)) * cumulativeGrid N hN Q (min (N-1) m + 1)
  rw [hmin]
  simp only [cumulativeGrid, Finset.sum_range_succ]
  field_simp
  <;> ring
-- @node: cumulative_grid_exact
/-- For [a positive number of grid cells](hyp:hN), with [at least two cells whenever outcome endpoints
are not treated as known](hyp:hInterior), and [a node index no greater than the grid size](hyp:hm),
[the cumulative trapezoidal grid sum of the fitted, sorted and clipped quantile equals its integral
from zero to that node](goal). -/
lemma cumulative_grid_exact (raw : ℕ → A → ℕ → X → ℝ) (N : ℕ) (hN : 0 < N)
    (knownEndpoints : Bool) (hInterior : knownEndpoints = false → 2 ≤ N) (n : ℕ) (a : A) (x : X) (m : ℕ) (hm : m ≤ N) :
    cumulativeGrid N hN (interpolatedQuantile M raw N hN knownEndpoints hInterior n a x) m =
      quantilePrimitive (interpolatedQuantile M raw N hN knownEndpoints hInterior n a x) ((m:ℝ)/N) := by
  unfold interpolatedQuantile
  exact (interpolate_grid_primitive N hN _ m hm).symm
-- @node: unit_grid_mem
/-- For [a positive number of grid cells](hyp:hN) and [a natural-number node index no greater than
the grid size](hyp:hm), [the node's rank, its index divided by the grid size, belongs to the closed unit interval](goal). -/
lemma unit_grid_mem (N : ℕ) (hN : 0 < N) (m : ℕ) (hm : m ≤ N) :
    (m : ℝ)/N ∈ Icc (0 : ℝ) 1 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  exact ⟨div_nonneg (Nat.cast_nonneg m) hNr.le,
    (div_le_one hNr).mpr (by exact_mod_cast hm)⟩

-- @node: cell_average_error_on_cell
/-- For [a positive number of grid cells](hyp:hN), [a quantile function nondecreasing on the closed
unit interval](hyp:hQ), [a cell index below the grid size](hyp:hm), and [a rank strictly inside that
cell](hyp:ht), [the absolute difference between the cell-average quantile and the quantile at that
rank is at most the quantile increase across the cell](goal). -/
lemma cell_average_error_on_cell (N : ℕ) (hN : 0 < N) (Q : ℝ → ℝ)
    (hQ : MonotoneOn Q (Icc (0 : ℝ) 1)) (m : ℕ) (hm : m < N) (t : ℝ)
    (ht : t ∈ Ioo ((m : ℝ)/N) (((m+1 : ℕ) : ℝ)/N)) :
    |cellAverageQuantile N hN Q t - Q t| ≤ Q (((m+1 : ℕ) : ℝ)/N) - Q ((m : ℝ)/N) := by
  have ha := unit_grid_mem N hN m hm.le
  have hb := unit_grid_mem N hN (m+1) (by omega)
  have htt : t ∈ Icc (0 : ℝ) 1 := ⟨ha.1.trans ht.1.le, ht.2.le.trans hb.2⟩
  have hlo := hQ ha htt ht.1.le
  have hhi := hQ htt hb ht.2.le
  unfold cellAverageQuantile
  rw [cell_average_index_on_cell N hN m hm t ⟨ht.1.le, ht.2⟩, abs_le]
  constructor <;> linarith

-- @node: cell_average_error_cell_integral
/-- For [a positive number of grid cells](hyp:hN), [a quantile function nondecreasing on the closed
unit interval](hyp:hQ), and [a cell index below the grid size](hyp:hm), [the integrated absolute error
of the cell-average quantile over that cell is at most the quantile increase across the cell divided
by the grid size](goal). -/
lemma cell_average_error_cell_integral (N : ℕ) (hN : 0 < N) (Q : ℝ → ℝ)
    (hQ : MonotoneOn Q (Icc (0 : ℝ) 1)) (m : ℕ) (hm : m < N) :
    (∫ t in Ioc ((m : ℝ)/N) (((m+1 : ℕ) : ℝ)/N),
      |cellAverageQuantile N hN Q t - Q t|) ≤
      (Q (((m+1 : ℕ) : ℝ)/N) - Q ((m : ℝ)/N)) / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have ha := unit_grid_mem N hN m hm.le
  have hb := unit_grid_mem N hN (m+1) (by omega)
  have hi : IntegrableOn (fun t => |cellAverageQuantile N hN Q t - Q t|) (Icc (0 : ℝ) 1) :=
    ((cell_average_quantile_integrable N hN Q).sub (hQ.integrableOn_isCompact isCompact_Icc)).abs
  have hab : (m : ℝ)/N ≤ ((m+1 : ℕ) : ℝ)/N := by
    gcongr
    exact Nat.le_succ m
  rw [integral_Ioc_eq_integral_Ioo]
  calc
    _ ≤ ∫ t in Ioo ((m : ℝ)/N) (((m+1 : ℕ) : ℝ)/N),
        Q (((m+1 : ℕ) : ℝ)/N) - Q ((m : ℝ)/N) := by
      apply integral_mono_ae
        (hi.mono_set (fun t ht => ⟨ha.1.trans ht.1.le, ht.2.le.trans hb.2⟩))
        (integrable_const _)
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact cell_average_error_on_cell N hN Q hQ m hm t ht
    _ = _ := by
      rw [setIntegral_const, measureReal_def, Real.volume_Ioo,
        ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
      simp only [smul_eq_mul, Nat.cast_add, Nat.cast_one]
      ring

-- @node: cell_average_error_prefix_integral
/-- For [a positive number of grid cells](hyp:hN), [a quantile function nondecreasing on the closed
unit interval](hyp:hQ), and [a node index no greater than the grid size](hyp:hm), [the integrated
absolute error of the cell-average quantile from zero to that node is at most the quantile increase
from zero to the node divided by the grid size](goal). -/
lemma cell_average_error_prefix_integral (N : ℕ) (hN : 0 < N) (Q : ℝ → ℝ)
    (hQ : MonotoneOn Q (Icc (0 : ℝ) 1)) (m : ℕ) (hm : m ≤ N) :
    (∫ t in Ioc 0 ((m : ℝ)/N), |cellAverageQuantile N hN Q t - Q t|) ≤
      (Q ((m : ℝ)/N) - Q 0) / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hi : IntegrableOn (fun t => |cellAverageQuantile N hN Q t - Q t|) (Icc (0 : ℝ) 1) :=
    ((cell_average_quantile_integrable N hN Q).sub (hQ.integrableOn_isCompact isCompact_Icc)).abs
  induction m with
  | zero => simp
  | succ m ih =>
    have hm' : m < N := by omega
    have ha := unit_grid_mem N hN m hm'.le
    have hb := unit_grid_mem N hN (m+1) hm
    have hab : (m : ℝ)/N ≤ ((m+1 : ℕ) : ℝ)/N := by
      gcongr
      exact Nat.le_succ m
    rw [integral_adjacent_Ioc _ ha.1 hab
      (hi.mono_set (fun t ht => ⟨ht.1.le, ht.2.trans hb.2⟩))]
    calc
      _ ≤ (Q ((m : ℝ)/N) - Q 0) / N +
          (Q (((m+1 : ℕ) : ℝ)/N) - Q ((m : ℝ)/N)) / N :=
        add_le_add (ih hm'.le) (cell_average_error_cell_integral N hN Q hQ m hm')
      _ = _ := by ring

-- @node: cumulative_interpolation_error
/-- For [a positive number of grid cells](hyp:hN), suppose [the quantile function is nondecreasing
on the closed unit interval](hyp:hQ) and [its values there lie between the model's outcome endpoints](hyp:hb).
At [any rank in the closed unit interval](hyp:ht), [the absolute difference between the interpolated
cumulative trapezoidal values and the exact quantile integral is at most the outcome endpoint range
divided by the grid size](goal). -/
lemma cumulative_interpolation_error (N : ℕ) (hN : 0 < N) (Q : ℝ → ℝ)
    (hQ : MonotoneOn Q (Icc 0 1)) (hb : ∀ t ∈ Icc (0:ℝ) 1, Q t ∈ Icc M.yMin M.yMax)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    |interpCumQuantile N hN Q t - quantilePrimitive Q t| ≤ (M.yMax-M.yMin)/(N:ℝ) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hiQ : IntegrableOn Q (Icc (0 : ℝ) 1) := hQ.integrableOn_isCompact isCompact_Icc
  have hiA := cell_average_quantile_integrable N hN Q
  have his : Ioc 0 t ⊆ Icc (0 : ℝ) 1 := fun u hu => ⟨hu.1.le, hu.2.trans ht.2⟩
  rw [← cell_average_primitive N hN Q t ht, quantilePrimitive, quantilePrimitive,
    ← integral_sub (hiA.mono_set his) (hiQ.mono_set his)]
  calc
    _ ≤ ∫ u in Ioc 0 t, |cellAverageQuantile N hN Q u - Q u| := abs_integral_le_integral_abs
    _ ≤ ∫ u in Ioc 0 1, |cellAverageQuantile N hN Q u - Q u| := by
      have hiErr : IntegrableOn (fun u => |cellAverageQuantile N hN Q u - Q u|) (Icc (0 : ℝ) 1) :=
        (hiA.sub hiQ).abs
      apply setIntegral_mono_set (hiErr.mono_set Ioc_subset_Icc_self)
      · filter_upwards [] with u
        exact abs_nonneg _
      · exact Filter.Eventually.of_forall (Ioc_subset_Ioc_right ht.2)
    _ ≤ (Q 1 - Q 0) / N := by
      simpa only [div_self (ne_of_gt hNr)] using
        cell_average_error_prefix_integral N hN Q hQ N le_rfl
    _ ≤ (M.yMax - M.yMin) / N := by
      apply div_le_div_of_nonneg_right _ hNr.le
      have h0 := hb 0 ⟨le_rfl, zero_le_one⟩
      have h1 := hb 1 ⟨zero_le_one, le_rfl⟩
      linarith [h0.1, h1.2]

-- @node: affine_quantile_cell_error
/-- If [the interpolation weight lies between zero and one](hyp:hα) and [the target value lies
between two reference endpoint values](hyp:hq), then [the absolute error of the linear blend of
two fitted endpoint values relative to that target is at most the same blend of absolute endpoint
errors plus the difference between the reference endpoints](goal). -/
lemma affine_quantile_cell_error (v₀ v₁ q₀ q₁ q α : ℝ)
    (hα : α ∈ Icc (0 : ℝ) 1) (hq : q ∈ Icc q₀ q₁) :
    |(1 - α) * v₀ + α * v₁ - q| ≤
      (1 - α) * |v₀ - q₀| + α * |v₁ - q₁| + (q₁ - q₀) := by
  have hmix : (1 - α) * q₀ + α * q₁ ∈ Icc q₀ q₁ := by
    constructor <;> nlinarith [mul_nonneg hα.1 (sub_nonneg.mpr (hq.1.trans hq.2)),
      mul_nonneg (sub_nonneg.mpr hα.2) (sub_nonneg.mpr (hq.1.trans hq.2))]
  have hosc : |(1 - α) * q₀ + α * q₁ - q| ≤ q₁ - q₀ := by
    rw [abs_le]
    constructor <;> linarith [hmix.1, hmix.2, hq.1, hq.2]
  calc
    _ ≤ |(1 - α) * (v₀ - q₀) + α * (v₁ - q₁)| +
        |(1 - α) * q₀ + α * q₁ - q| := by
      convert abs_add_le ((1 - α) * (v₀ - q₀) + α * (v₁ - q₁))
        ((1 - α) * q₀ + α * q₁ - q) using 1 <;> congr 1 <;> ring
    _ ≤ (|(1 - α) * (v₀ - q₀)| + |α * (v₁ - q₁)|) + (q₁ - q₀) :=
      add_le_add (abs_add_le _ _) hosc
    _ = _ := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hα.2),
        abs_of_nonneg hα.1]

-- @node: interpolate_quantile_error_on_cell
/-- For [a positive number of grid cells](hyp:hN), [a quantile function nondecreasing on the closed
unit interval](hyp:hQ), [a cell index below the grid size](hyp:hm), and [a rank strictly inside that
cell](hyp:ht), [the absolute error of interpolating fitted grid values relative to the quantile is
at most the interpolated absolute errors at grid nodes plus the quantile increase across the cell](goal). -/
lemma interpolate_quantile_error_on_cell (N : ℕ) (hN : 0 < N) (v : ℕ → ℝ)
    (Q : ℝ → ℝ) (hQ : MonotoneOn Q (Icc (0 : ℝ) 1))
    (m : ℕ) (hm : m < N) (t : ℝ)
    (ht : t ∈ Ioo ((m : ℝ)/N) (((m+1 : ℕ) : ℝ)/N)) :
    |interpolate N hN v t - Q t| ≤
      interpolate N hN (fun j => |v j - Q ((j : ℝ)/N)|) t +
      (Q (((m+1 : ℕ) : ℝ)/N) - Q ((m : ℝ)/N)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have ha := unit_grid_mem N hN m hm.le
  have hb := unit_grid_mem N hN (m+1) (by omega)
  have htt : t ∈ Icc (0 : ℝ) 1 := ⟨ha.1.trans ht.1.le, ht.2.le.trans hb.2⟩
  have hα : t * N - m ∈ Icc (0 : ℝ) 1 := by
    have hlo := (div_lt_iff₀ hNr).mp ht.1
    have hhi := (lt_div_iff₀ hNr).mp ht.2
    simp only [Nat.cast_add, Nat.cast_one] at hhi
    constructor <;> linarith
  rw [interpolate_on_open_cell N hN v m hm t ht,
    interpolate_on_open_cell N hN _ m hm t ht]
  exact affine_quantile_cell_error _ _ _ _ _ _ hα
    ⟨hQ ha htt ht.1.le, hQ htt hb ht.2.le⟩

-- @node: interpolate_quantile_error_cell_integral
/-- For [a positive number of grid cells](hyp:hN), [a quantile function nondecreasing on the closed
unit interval](hyp:hQ), and [a cell index below the grid size](hyp:hm), [the integrated absolute error
of the fitted linear interpolant over that cell is at most the sum of the two endpoint absolute
errors divided by twice the grid size, plus the quantile increase across the cell divided by the grid size](goal). -/
lemma interpolate_quantile_error_cell_integral (N : ℕ) (hN : 0 < N) (v : ℕ → ℝ)
    (Q : ℝ → ℝ) (hQ : MonotoneOn Q (Icc (0 : ℝ) 1))
    (m : ℕ) (hm : m < N) :
    (∫ t in Ioc ((m : ℝ)/N) (((m+1 : ℕ) : ℝ)/N),
      |interpolate N hN v t - Q t|) ≤
      (|v m - Q ((m : ℝ)/N)| + |v (m+1) - Q (((m+1 : ℕ) : ℝ)/N)|) /
        (2 * N) + (Q (((m+1 : ℕ) : ℝ)/N) - Q ((m : ℝ)/N)) / N := by
  let e := fun j : ℕ => |v j - Q ((j : ℝ)/N)|
  let d := Q (((m+1 : ℕ) : ℝ)/N) - Q ((m : ℝ)/N)
  have ha := unit_grid_mem N hN m hm.le
  have hb := unit_grid_mem N hN (m+1) (by omega)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hab : (m : ℝ)/N ≤ ((m+1 : ℕ) : ℝ)/N := by
    gcongr
    exact Nat.le_succ m
  have hs : Ioc ((m : ℝ)/N) (((m+1 : ℕ) : ℝ)/N) ⊆ Icc (0 : ℝ) 1 :=
    fun t ht => ⟨ha.1.trans ht.1.le, ht.2.trans hb.2⟩
  have hiUnit : IntegrableOn (fun t => |interpolate N hN v t - Q t|)
      (Icc (0 : ℝ) 1) :=
    ((interpolate_integrable_on_unit N hN v).sub
      (hQ.integrableOn_isCompact isCompact_Icc)).abs
  have hi := hiUnit.mono_set hs
  have hie : IntegrableOn (interpolate N hN e)
      (Ioc ((m : ℝ)/N) (((m+1 : ℕ) : ℝ)/N)) :=
    (interpolate_integrable_on_unit N hN e).mono_set hs
  calc
    _ ≤ ∫ t in Ioc ((m : ℝ)/N) (((m+1 : ℕ) : ℝ)/N),
        interpolate N hN e t + d := by
      rw [integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
      apply integral_mono_ae
        (by simpa only [IntegrableOn, restrict_Ioo_eq_restrict_Ioc] using hi)
        (by
          have hh : IntegrableOn (fun t => interpolate N hN e t + d)
              (Ioc ((m : ℝ)/N) (((m+1 : ℕ) : ℝ)/N)) := hie.add (integrable_const d)
          simpa only [IntegrableOn, restrict_Ioo_eq_restrict_Ioc, Pi.add_apply] using hh)
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact interpolate_quantile_error_on_cell N hN v Q hQ m hm t ht
    _ = _ := by
      rw [integral_add hie (integrable_const d), interpolate_cell_integral N hN e m hm,
        setIntegral_const, measureReal_def, Real.volume_Ioc,
        ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
      dsimp only [e, d]
      simp only [smul_eq_mul, Nat.cast_add, Nat.cast_one]
      ring

-- @node: interpolate_quantile_error_prefix_integral
/-- For [a positive number of grid cells](hyp:hN), [a quantile function nondecreasing on the closed
unit interval](hyp:hQ), and [a node index no greater than the grid size](hyp:hm), [the integrated
absolute error of the fitted linear interpolant from zero to that node is at most the sum over
preceding cells of their two endpoint absolute errors divided by twice the grid size, plus the
quantile increase from zero to the node divided by the grid size](goal). -/
lemma interpolate_quantile_error_prefix_integral (N : ℕ) (hN : 0 < N) (v : ℕ → ℝ)
    (Q : ℝ → ℝ) (hQ : MonotoneOn Q (Icc (0 : ℝ) 1))
    (m : ℕ) (hm : m ≤ N) :
    (∫ t in Ioc 0 ((m : ℝ)/N), |interpolate N hN v t - Q t|) ≤
      (∑ j ∈ Finset.range m,
        (|v j - Q ((j : ℝ)/N)| + |v (j+1) - Q (((j+1 : ℕ) : ℝ)/N)|) /
          (2 * N)) + (Q ((m : ℝ)/N) - Q 0) / N := by
  have hi : IntegrableOn (fun t => |interpolate N hN v t - Q t|) (Icc (0 : ℝ) 1) :=
    ((interpolate_integrable_on_unit N hN v).sub
      (hQ.integrableOn_isCompact isCompact_Icc)).abs
  induction m with
  | zero => simp
  | succ m ih =>
    have hm' : m < N := by omega
    have ha := unit_grid_mem N hN m hm'.le
    have hb := unit_grid_mem N hN (m+1) hm
    have hab : (m : ℝ)/N ≤ ((m+1 : ℕ) : ℝ)/N := by
      gcongr
      exact Nat.le_succ m
    rw [integral_adjacent_Ioc _ ha.1 hab
      (hi.mono_set (fun t ht => ⟨ht.1.le, ht.2.trans hb.2⟩))]
    refine (add_le_add (ih hm'.le)
      (interpolate_quantile_error_cell_integral N hN v Q hQ m hm')).trans_eq ?_
    rw [Finset.sum_range_succ]
    ring

-- @node: interpolate_quantile_error_unit_integral
/-- For [a positive number of grid cells](hyp:hN) and [a quantile function nondecreasing on the closed
unit interval](hyp:hQ), [the integrated absolute error of the fitted linear interpolant over the unit
interval is at most the sum over all cells of their two endpoint absolute errors divided by twice
the grid size, plus the quantile increase from zero to one divided by the grid size](goal). -/
lemma interpolate_quantile_error_unit_integral (N : ℕ) (hN : 0 < N) (v : ℕ → ℝ)
    (Q : ℝ → ℝ) (hQ : MonotoneOn Q (Icc (0 : ℝ) 1)) :
    (∫ t in Ioc (0 : ℝ) 1, |interpolate N hN v t - Q t|) ≤
      (∑ j ∈ Finset.range N,
        (|v j - Q ((j : ℝ)/N)| + |v (j+1) - Q (((j+1 : ℕ) : ℝ)/N)|) /
          (2 * N)) + (Q 1 - Q 0) / N := by
  simpa only [div_self (show (N : ℝ) ≠ 0 by exact_mod_cast hN.ne')] using
    interpolate_quantile_error_prefix_integral N hN v Q hQ N le_rfl

end Papers.TbsPrteOptimalTransport

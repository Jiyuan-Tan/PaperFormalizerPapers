module
public import Papers.TbsPrteOptimalTransport.Helpers.LearnerInterpolation
public import Papers.TbsPrteOptimalTransport.TContinuousRate
/-! Transfer from the exact fitted quantile primitive to its cumulative grid interpolant. -/
public section
set_option linter.unusedVariables false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

-- @node: interpolant_cumulative_error
/-- With [a positive number of grid cells](hyp:hN), if [all grid values lie between the
given lower and upper bounds](hyp:hv) and [the integration limit lies in the unit
interval](hyp:ht), then [the cumulative grid interpolant of their linear interpolation
differs from its exact quantile primitive by at most the range of the bounds divided
by the number of cells](goal). -/
lemma interpolant_cumulative_error (N : ℕ) (hN : 0 < N) (v : ℕ → ℝ)
    (lo hi : ℝ) (hv : ∀ m, v m ∈ Icc lo hi)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    |interpCumQuantile N hN (interpolate N hN v) t -
      quantilePrimitive (interpolate N hN v) t| ≤ (hi - lo) / N := by
  let Q := interpolate N hN v
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have horder : lo ≤ hi := (hv 0).1.trans (hv 0).2
  have hB : 0 ≤ hi - lo := sub_nonneg.mpr horder
  have hiQ := interpolate_integrable_on_unit N hN v
  have hiA := cell_average_quantile_integrable N hN Q
  rw [← cell_average_primitive N hN Q t ht]
  by_cases ht1 : t = 1
  · subst t
    rw [show (1 : ℝ) = (N : ℝ) / N from (div_self hNr.ne').symm,
      cell_average_grid_primitive N hN Q N le_rfl,
      interpolate_grid_primitive N hN v N le_rfl]
    simpa [Q] using div_nonneg hB hNr.le
  have htl : t < 1 := lt_of_le_of_ne ht.2 ht1
  let m := Nat.floor (t * N)
  have hm : m < N := (Nat.floor_lt (mul_nonneg ht.1 hNr.le)).mpr (by nlinarith)
  have ha := unit_grid_mem N hN m hm.le
  have hmt : (m : ℝ) / N ≤ t :=
    (div_le_iff₀ hNr).mpr (Nat.floor_le (mul_nonneg ht.1 hNr.le))
  have htm : t - (m : ℝ) / N ≤ (N : ℝ)⁻¹ := by
    have hh := (Nat.lt_floor_add_one (t * N)).le
    change t * N ≤ (m : ℝ) + 1 at hh
    have hh' := (le_div_iff₀ hNr).mpr hh
    rw [add_div, one_div] at hh'
    linarith
  have hs : Ioc ((m : ℝ) / N) t ⊆ Icc (0 : ℝ) 1 :=
    fun u hu => ⟨ha.1.trans hu.1.le, hu.2.trans ht.2⟩
  rw [quantilePrimitive, quantilePrimitive,
    integral_adjacent_Ioc _ ha.1 hmt (hiA.mono_set (fun u hu => ⟨hu.1.le, hu.2.trans ht.2⟩)),
    integral_adjacent_Ioc _ ha.1 hmt (hiQ.mono_set (fun u hu => ⟨hu.1.le, hu.2.trans ht.2⟩))]
  have hgrid : (∫ u in Ioc 0 ((m : ℝ) / N), cellAverageQuantile N hN Q u) =
      ∫ u in Ioc 0 ((m : ℝ) / N), Q u :=
    (cell_average_grid_primitive N hN Q m hm.le).trans
      (interpolate_grid_primitive N hN v m hm.le).symm
  rw [hgrid]
  rw [show ∀ a b c : ℝ, a + b - (a + c) = b - c by intros; ring,
    ← integral_sub (hiA.mono_set hs) (hiQ.mono_set hs)]
  calc
    _ ≤ ∫ u in Ioc ((m : ℝ) / N) t, |cellAverageQuantile N hN Q u - Q u| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ _u in Ioc ((m : ℝ) / N) t, hi - lo := by
      apply setIntegral_mono_on ((hiA.mono_set hs).sub (hiQ.mono_set hs)).abs
        (integrableOn_const (by simp only [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)) measurableSet_Ioc
      intro u hu
      have hq := interpolate_interval N hN v lo hi hv u
      have h0 := interpolate_interval N hN v lo hi hv
        ((min (N - 1) (Nat.floor (u * N)) : ℕ) / N)
      have h1 := interpolate_interval N hN v lo hi hv
        (((min (N - 1) (Nat.floor (u * N)) + 1 : ℕ) : ℝ) / N)
      change |(Q ((min (N - 1) (Nat.floor (u * N)) : ℕ) / N) +
        Q (((min (N - 1) (Nat.floor (u * N)) + 1 : ℕ) : ℝ) / N)) / 2 - Q u| ≤ hi - lo
      dsimp only [Q]
      exact abs_le.mpr ⟨by linarith [h0.1, h1.1, hq.2],
        by linarith [h0.2, h1.2, hq.1]⟩
    _ = (t - (m : ℝ) / N) * (hi - lo) := by
      rw [setIntegral_const, measureReal_def, Real.volume_Ioc,
        ENNReal.toReal_ofReal (sub_nonneg.mpr hmt)]
      rfl
    _ ≤ (hi - lo) / N := by
      simpa only [div_eq_mul_inv, mul_comm] using mul_le_mul_of_nonneg_right htm hB

universe u v
variable {Ω : Type u} {X Z : Type v} {A : Type*}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]

-- @node: interpolated_quantile_cumulative_error
/-- If [the outcome endpoints are known](hyp:he), [the grid has a positive number of
cells](hyp:hN), [at least two cells are used when endpoints are not imposed](hyp:hInterior),
and [the integration limit lies in the unit interval](hyp:ht), then [the cumulative grid
interpolant of the fitted interpolated quantile differs from its exact primitive by at
most the outcome range divided by the number of cells, for each sample size, sample
realization, and covariate value](goal). -/
lemma interpolated_quantile_cumulative_error (M : LatentIVModel Ω X Z)
    (he : OutcomeEndpointsKnown M) (raw : ℕ → A → ℕ → X → ℝ)
    (N : ℕ) (hN : 0 < N) (knownEndpoints : Bool)
    (hInterior : knownEndpoints = false → 2 ≤ N) (n : ℕ) (a : A) (x : X)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    let Q := interpolatedQuantile M raw N hN knownEndpoints hInterior n a x
    |interpCumQuantile N hN Q t - quantilePrimitive Q t| ≤ (M.yMax - M.yMin) / N := by
  have horder : M.yMin ≤ M.yMax := he.1.2 he.2.1
  have hlo : M.yMin ∈ Icc M.yMin M.yMax := ⟨le_rfl, horder⟩
  have hhi : M.yMax ∈ Icc M.yMin M.yMax := ⟨horder, le_rfl⟩
  have hvs : ∀ y ∈ sortedGrid M raw N n a x, y ∈ Icc M.yMin M.yMax := by
    intro y hy
    have hmem := (List.mergeSort_perm _ _).mem_iff.mp hy
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hmem
    exact ⟨le_min horder (le_max_left _ _), min_le_left _ _⟩
  dsimp only
  unfold interpolatedQuantile
  apply interpolant_cumulative_error N hN _ M.yMin M.yMax _ t ht
  intro m
  split_ifs <;> first
    | exact hlo
    | exact hhi
    | exact list_getD_interval _ _ _ _ hlo hvs _
    | exact list_getD_interval _ _ _ _ hhi hvs _

-- @node: fitted_lower_cumulative_perturbation
/-- If [the policy map is jointly measurable on unit-interval propensities and preserves
the unit interval](hyp:hPolicy), [all fitted propensities
lie in the unit interval](hyp:hp), and [two cumulative quantile functions differ by at
most the error bound at every covariate and unit-interval argument](hyp:hCD), then
[replacing one by the other changes the fitted lower-bound contribution at any
observation by at most twice that error bound](goal). -/
lemma fitted_lower_cumulative_perturbation (M : LatentIVModel Ω X Z)
    (phi : Z → X → ℝ → ℝ) (hPolicy : IsPolicyMap phi)
    (p : Z → X → ℝ) (hp : ∀ z x, p z x ∈ Icc (0 : ℝ) 1)
    (g : ℝ → X → ℝ) (C D : X → ℝ → ℝ) (e : ℝ)
    (hCD : ∀ x t, t ∈ Icc (0 : ℝ) 1 → |C x t - D x t| ≤ e)
    (o : Obs X Z) :
    |fittedInt M false phi p g C o - fittedInt M false phi p g D o| ≤ 2 * e := by
  have he : 0 ≤ e := (abs_nonneg _).trans (hCD o.1 1 ⟨zero_le_one, le_rfl⟩)
  have hl := (propensity_support_endpoints p hp o.1).1
  by_cases hlow : 0 < pLow p o.1
  · let tau := min 1 (phi o.2.1 o.1 (p o.2.1 o.1) / pLow p o.1)
    have ht : tau ∈ Icc (0 : ℝ) 1 :=
      ⟨le_min zero_le_one (div_nonneg (hPolicy.2 o.2.1 o.1 _ (hp _ _)).1 hlow.le),
        min_le_left _ _⟩
    have hdiff : fittedInt M false phi p g C o - fittedInt M false phi p g D o =
        -pLow p o.1 * ((C o.1 1 - D o.1 1) - (C o.1 tau - D o.1 tau)) := by
      simp only [fittedInt, if_pos hlow, Bool.false_eq_true, if_false]
      dsimp only [tau]
      ring
    rw [hdiff, abs_mul, abs_neg, abs_of_nonneg hl.1]
    calc
      _ ≤ pLow p o.1 * (|C o.1 1 - D o.1 1| + |C o.1 tau - D o.1 tau|) :=
        mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using
          (norm_sub_le (C o.1 1 - D o.1 1) (C o.1 tau - D o.1 tau))) hl.1
      _ ≤ pLow p o.1 * (e + e) := by
        gcongr
        · exact hCD _ _ ⟨zero_le_one, le_rfl⟩
        · exact hCD _ _ ht
      _ ≤ 2 * e := by nlinarith [hl.2]
  · simp only [fittedInt, if_neg hlow, sub_self, abs_zero]
    positivity

-- @node: plugin_lower_cumulative_perturbation
/-- If [the policy map is jointly measurable on unit-interval propensities and preserves
the unit interval](hyp:hPolicy), [all fitted propensities
lie in the unit interval](hyp:hp), [the error bound is nonnegative](hyp:he), and [the two
fitted cumulative quantile functions differ uniformly by at most that bound at the
chosen sample size and realization](hyp:hCD), then [the corresponding lower-bound
plug-in estimates differ by at most twice the error bound](goal). -/
lemma plugin_lower_cumulative_perturbation (M : LatentIVModel Ω X Z)
    (μ : Measure A) (S : ObservedSample M μ) (I : SampleSplit A)
    (phi : Z → X → ℝ → ℝ) (hPolicy : IsPolicyMap phi)
    (p : ℕ → A → Z → X → ℝ) (hp : ∀ n a z x, p n a z x ∈ Icc (0 : ℝ) 1)
    (g : ℕ → A → ℝ → X → ℝ) (C D : ℕ → A → X → ℝ → ℝ)
    (n : ℕ) (a : A) (e : ℝ) (he : 0 ≤ e)
    (hCD : ∀ x t, t ∈ Icc (0 : ℝ) 1 → |C n a x t - D n a x t| ≤ e) :
    |plugInRV M μ S I phi p g C n a - plugInRV M μ S I phi p g D n a| ≤ 2 * e := by
  by_cases hI : (I n a).Nonempty
  · simp only [plugInRV, dif_pos hI, unrestrictedPlugInAverage, splitMean]
    rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
      abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
    calc
      _ ≤ ((I n a).card : ℝ)⁻¹ * ∑ i ∈ I n a,
          |fittedInt M false phi (p n a) (g n a) (C n a) (S.Z i a) -
            fittedInt M false phi (p n a) (g n a) (D n a) (S.Z i a)| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _)
          (inv_nonneg.mpr (Nat.cast_nonneg _))
      _ ≤ ((I n a).card : ℝ)⁻¹ * ∑ _i ∈ I n a, 2 * e := by
        gcongr with i hi
        exact fitted_lower_cumulative_perturbation M phi hPolicy (p n a) (hp n a)
          (g n a) (C n a) (D n a) e hCD (S.Z i a)
      _ = 2 * e := by
        rw [Finset.sum_const, nsmul_eq_mul]
        have hn : ((I n a).card : ℝ) ≠ 0 :=
          Nat.cast_ne_zero.mpr (Finset.card_pos.mpr hI).ne'
        field_simp
  · simp only [plugInRV, dif_neg hI, sub_self, abs_zero]
    positivity

-- @node: isBigOp_of_uniform_rate_bound
/-- If [the multiplier is nonnegative](hyp:hC), [the rate is eventually positive](hyp:hr),
and [the random sequence is bounded in absolute value by that multiplier times the
rate for every sample size and realization](hyp:hf), then [the sequence is of that
order in probability under the given measure](goal). -/
lemma isBigOp_of_uniform_rate_bound {μ : Measure A} {f : ℕ → A → ℝ}
    {r : ℕ → ℝ} (C : ℝ) (hC : 0 ≤ C)
    (hr : ∀ᶠ n in atTop, 0 < r n) (hf : ∀ n a, |f n a| ≤ C * r n) :
    Causalean.Stat.IsBigOp f r μ := by
  intro δ hδ
  refine ⟨C + 1, by positivity, ?_⟩
  filter_upwards [hr] with n hn
  have hempty : {a | (C + 1) * r n ≤ ‖f n a‖} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro a ha
    have hb := hf n a
    simp only [Set.mem_setOf_eq, Real.norm_eq_abs] at ha
    nlinarith
  rw [hempty, measure_empty]
  exact bot_le

end Papers.TbsPrteOptimalTransport

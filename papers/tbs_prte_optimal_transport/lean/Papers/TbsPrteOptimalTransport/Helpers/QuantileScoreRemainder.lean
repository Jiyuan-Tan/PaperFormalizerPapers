module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLProcedure
public import Mathlib.MeasureTheory.Function.L2Space
/-! Quadratic control of the combined quantile-boundary score correction. -/
public section

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Set

-- The same interval bound handles both orientations of a moving boundary.
-- @node: quantile_boundary_integral_quadratic
/-- For a finite outcome measure, if [the mass between two thresholds is at most a coefficient times their absolute separation](hyp:hmass), [the absolute integral of the fitted threshold minus the outcome over that interval is at most the coefficient times squared threshold separation](goal). -/
lemma quantile_boundary_integral_quadratic (ν : Measure ℝ) [IsFiniteMeasure ν]
    (a b C : ℝ)
    (hmass : (ν (Ioc (min a b) (max a b))).toReal ≤ C * |b - a|) :
    |∫ y in Ioc (min a b) (max a b), b - y ∂ν| ≤ C * |b - a| ^ 2 := by
  have hbound : ∀ᵐ y ∂ν.restrict (Ioc (min a b) (max a b)),
      ‖b - y‖ ≤ |b - a| := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    rw [Real.norm_eq_abs]
    by_cases hab : a ≤ b
    · simp only [min_eq_left hab, max_eq_right hab] at hy
      rw [abs_of_nonneg (by linarith [hy.2] : 0 ≤ b - y),
        abs_of_nonneg (by linarith : 0 ≤ b - a)]
      linarith [hy.1, hy.2]
    · have hba : b ≤ a := le_of_not_ge hab
      simp only [min_eq_right hba, max_eq_left hba] at hy
      rw [abs_of_nonpos (by linarith [hy.1] : b - y ≤ 0),
        abs_of_nonpos (by linarith : b - a ≤ 0)]
      linarith [hy.1, hy.2]
  have hint := norm_integral_le_of_norm_le_const hbound
  simp only [Real.norm_eq_abs, Measure.real, Measure.restrict_apply_univ] at hint
  calc
    _ ≤ |b - a| * (ν (Ioc (min a b) (max a b))).toReal := hint
    _ ≤ |b - a| * (C * |b - a|) :=
      mul_le_mul_of_nonneg_left hmass (abs_nonneg _)
    _ = _ := by ring

-- A local density bound is used only when the fitted boundary is nearby.
-- @node: quantile_boundary_integral_local
/-- For a finite outcome measure, if [the threshold displacement is within the local radius](hyp:herr) and [every interval within that radius of the reference threshold has mass at most the density cap times its length](hyp:hdensity), [the absolute integral of the fitted threshold minus the outcome between the thresholds is at most the density cap times squared displacement](goal). -/
lemma quantile_boundary_integral_local (ν : Measure ℝ) [IsFiniteMeasure ν]
    (a b r C : ℝ) (herr : |b - a| ≤ r)
    (hdensity : ∀ u v, a - r ≤ u → u ≤ v → v ≤ a + r →
      (ν (Ioc u v)).toReal ≤ C * (v - u)) :
    |∫ y in Ioc (min a b) (max a b), b - y ∂ν| ≤ C * |b - a| ^ 2 := by
  apply quantile_boundary_integral_quadratic
  obtain ⟨hlo, hhi⟩ := abs_le.mp herr
  have hr : 0 ≤ r := (abs_nonneg _).trans herr
  have hmin : a - r ≤ min a b := le_min (by linarith) (by linarith)
  have hmax : max a b ≤ a + r := max_le (by linarith) (by linarith)
  have hmass := hdensity (min a b) (max a b) hmin (min_le_max) hmax
  have hlen : max a b - min a b = |b - a| := by
    by_cases h : a ≤ b
    · rw [max_eq_right h, min_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)]
    · rw [max_eq_left (le_of_not_ge h), min_eq_right (le_of_not_ge h),
        abs_of_nonpos (sub_nonpos.mpr (le_of_not_ge h))]
      ring
  simpa only [hlen] using hmass

-- Large errors are controlled by clipping, without requiring a global density.
-- @node: quantile_remainder_global_quadratic
/-- Suppose [the local radius is positive](hyp:hr), [the local quadratic coefficient is nonnegative](hyp:hC), [the global cap is nonnegative](hyp:hB), [the remainder is bounded by the coefficient times squared error whenever absolute error is within the radius](hyp:hlocal), and [the remainder's absolute value never exceeds the global cap](hyp:hglobal). Then [the absolute remainder is bounded by squared error times the sum of the local coefficient and the global cap divided by squared radius](goal). -/
lemma quantile_remainder_global_quadratic {R e r C B : ℝ}
    (hr : 0 < r) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hlocal : |e| ≤ r → |R| ≤ C * e ^ 2) (hglobal : |R| ≤ B) :
    |R| ≤ (C + B / r ^ 2) * e ^ 2 := by
  by_cases he : |e| ≤ r
  · have hcoef : C ≤ C + B / r ^ 2 := le_add_of_nonneg_right (by positivity)
    exact (hlocal he).trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _))
  · have he2 : r ^ 2 ≤ e ^ 2 := by
      have hlarge : r ≤ |e| := (le_of_not_ge he)
      nlinarith [sq_abs e]
    have hlarge : B ≤ (B / r ^ 2) * e ^ 2 := by
      calc
        B = (B / r ^ 2) * r ^ 2 := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left he2 (by positivity)
    exact hglobal.trans (hlarge.trans (by nlinarith [sq_nonneg e]))

-- Measurability plus the L2 error derives integrability of the remainder.
-- @node: quantile_remainder_integrated_quadratic
/-- Suppose [the local radius is positive](hyp:hr), [the quadratic coefficient is nonnegative](hyp:hC), [the global cap is nonnegative](hyp:hB), [the remainder is almost everywhere strongly measurable](hyp:hR), and [the boundary error is square integrable](hyp:he). If [almost everywhere the remainder is quadratically bounded for errors within the radius](hyp:hlocal) and [its absolute value is at most the global cap](hyp:hglobal), [the remainder is integrable and its absolute integral is at most integrated squared error times the sum of the local coefficient and the global cap divided by squared radius](goal). -/
lemma quantile_remainder_integrated_quadratic {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (R e : X → ℝ) (r C B : ℝ)
    (hr : 0 < r) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hR : AEStronglyMeasurable R μ) (he : MemLp e 2 μ)
    (hlocal : ∀ᵐ x ∂μ, |e x| ≤ r → |R x| ≤ C * e x ^ 2)
    (hglobal : ∀ᵐ x ∂μ, |R x| ≤ B) :
    Integrable R μ ∧
      |∫ x, R x ∂μ| ≤ (C + B / r ^ 2) * ∫ x, e x ^ 2 ∂μ := by
  have hbound : ∀ᵐ x ∂μ, |R x| ≤ (C + B / r ^ 2) * e x ^ 2 := by
    filter_upwards [hlocal, hglobal] with x hx hg
    exact quantile_remainder_global_quadratic hr hC hB hx hg
  have hdom : Integrable (fun x => (C + B / r ^ 2) * e x ^ 2) μ :=
    he.integrable_sq.const_mul _
  have hi : Integrable R μ := hdom.mono' hR (by
    simpa only [Real.norm_eq_abs] using hbound)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ x, |R x| ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm R
    _ ≤ ∫ x, (C + B / r ^ 2) * e x ^ 2 ∂μ :=
      integral_mono_ae hi.abs hdom hbound
    _ = _ := integral_const_mul _ _

-- For an L2 direction, the integrated boundary correction has derivative zero.
-- This uses the quadratic estimate, rather than interchanging a derivative
-- with an integral of moving indicators.
-- @node: quantile_remainder_path_orthogonality
/-- Suppose [the local radius is positive](hyp:hr), [the quadratic coefficient is nonnegative](hyp:hC), [the global cap is nonnegative](hyp:hB), [the remainder is almost everywhere strongly measurable at every path value](hyp:hR), and [the path direction is square integrable](hyp:hd). If [at every path value the remainder is almost surely bounded by the coefficient times squared path displacement whenever that displacement is within the radius](hyp:hlocal), and [the remainder is almost surely bounded in absolute value by the global cap at every path value](hyp:hglobal), [the integrated remainder has derivative zero at path value zero](goal). -/
lemma quantile_remainder_path_orthogonality {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (R : ℝ → X → ℝ) (d : X → ℝ) (r C B : ℝ)
    (hr : 0 < r) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hR : ∀ t, AEStronglyMeasurable (R t) μ) (hd : MemLp d 2 μ)
    (hlocal : ∀ t, ∀ᵐ x ∂μ, |t * d x| ≤ r → |R t x| ≤ C * (t * d x) ^ 2)
    (hglobal : ∀ t, ∀ᵐ x ∂μ, |R t x| ≤ B) :
    HasDerivAt (fun t : ℝ => ∫ x, R t x ∂μ) 0 0 := by
  have hbound : ∀ t : ℝ, |∫ x, R t x ∂μ| ≤
      ((C + B / r ^ 2) * ∫ x, d x ^ 2 ∂μ) * t ^ 2 := by
    intro t
    have hb := (quantile_remainder_integrated_quadratic μ (R t) (fun x => t * d x)
      r C B hr hC hB (hR t) (hd.const_mul t) (hlocal t) (hglobal t)).2
    simp only [mul_pow, integral_const_mul] at hb
    convert hb using 1 <;> ring
  have hz : (∫ x, R 0 x ∂μ) = 0 := by
    have hb := hbound 0
    simpa using (abs_nonpos_iff.mp (by simpa using hb))
  have ho : (fun t : ℝ => ∫ x, R t x ∂μ) =O[nhds 0] (fun t => t ^ 2) := by
    apply Asymptotics.IsBigO.of_bound ((C + B / r ^ 2) * ∫ x, d x ^ 2 ∂μ)
    exact Filter.Eventually.of_forall fun t => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)] using hbound t
  apply HasDerivAt.of_isLittleO
  simpa only [hz, sub_zero, smul_zero] using
    ho.trans_isLittleO (Asymptotics.isLittleO_pow_id (𝕜 := ℝ) (by norm_num : 1 < 2))

section TreatedLaw
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z]

-- Normalizing the selected law gives a finite measure even off support.
-- @node: treatedLaw_isFiniteMeasure
/-- [The conditional outcome measure for treated observations in any instrument selection set is finite at every covariate value, including values outside the covariate support](goal). -/
lemma treatedLaw_isFiniteMeasure (M : LatentIVModel Ω X Z)
    (L : LevelData Z X) (k : ℕ) (x : X) : IsFiniteMeasure (treatedLaw M L k x) := by
  let joint := ProbabilityTheory.condDistrib
    (fun s => (M.Y s, M.W s, M.Zv s)) M.Xv M.law.toMeasure x
  let selected := joint.restrict {a | a.2.1 = 1 ∧ a.2.2 ∈ (L.S k : Set Z)}
  have hm : (selected.map Prod.fst) univ = selected univ := by
    rw [Measure.map_apply measurable_fst MeasurableSet.univ]
    simp
  change IsFiniteMeasure ((selected univ)⁻¹ • selected.map Prod.fst)
  rw [← hm]
  infer_instance

-- Specialize the interval calculation to precisely the density condition
-- used in the continuous-outcome DML regime; the fitted endpoint may lie
-- on either side of the population endpoint.
-- @node: dml_quantile_boundary_local_remainder
/-- If [the boundary density bounds hold](hyp:h), [there are a common positive radius and a coefficient such that, for every valid positive band boundary and either adjacent treated law, almost every covariate value satisfies a quadratic bound: whenever a fitted threshold is within the radius, the absolute integral of that threshold minus the outcome between the two thresholds is at most the coefficient times squared displacement](goal). -/
lemma dml_quantile_boundary_local_remainder (M : LatentIVModel Ω X Z)
    (L : LevelData Z X) (h : BoundaryDensitiesBounded M L) :
    ∃ r C : ℝ, 0 < r ∧
      ∀ k < L.K, ∀ j, 1 ≤ j → j ≤ L.l k →
      ∀ k', k' = k + 1 ∨ (1 ≤ k ∧ k' = k) → ∀ᵐ x ∂xLaw M,
        ∀ b, |b - bandBoundary M L k j x| ≤ r →
          |∫ y in Ioc (min (bandBoundary M L k j x) b)
              (max (bandBoundary M L k j x) b), b - y ∂treatedLaw M L k' x| ≤
            C * |b - bandBoundary M L k j x| ^ 2 := by
  obtain ⟨r, C, hr, hd⟩ := h
  refine ⟨r, C, hr, ?_⟩
  intro k hk j hj hjl k' hk'
  filter_upwards [hd k hk j hj hjl k' hk'] with x hx
  intro b hb
  let := treatedLaw_isFiniteMeasure M L k' x
  exact quantile_boundary_integral_local (treatedLaw M L k' x)
    (bandBoundary M L k j x) b r C hb hx

end TreatedLaw
end Papers.TbsPrteOptimalTransport

module

public import Papers.OaiBoundDyadicTriangular.Helpers.AtomIntegral
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-! # Compact dyadic square averages and approximation in L3 -/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace Papers.OaiBoundDyadicTriangular

-- @node: dyadicCellIndex
/-- For [an integer scale m](hyp:m) and [a real coordinate x](hyp:x), [the dyadic
cell index is the floor of x divided by 2 to the power m, truncated below at zero](goal). -/
noncomputable def dyadicCellIndex (m : ℤ) (x : ℝ) : ℕ := ⌊x / (2 : ℝ) ^ m⌋₊

-- @node: dyadicCell
/-- For [an integer scale m](hyp:m) and [a point x in the plane](hyp:x), [the
dyadic cell is the product of the two half-open dyadic intervals of length 2 to
the power m indexed by the truncated floor indices of x's coordinates](goal). -/
noncomputable def dyadicCell (m : ℤ) (x : ℝ × ℝ) : Set (ℝ × ℝ) :=
  dyadicInterval m (dyadicCellIndex m x.1) ×ˢ dyadicInterval m (dyadicCellIndex m x.2)

-- @node: dyadicMean
/-- For [a real-valued function f on the plane](hyp:f), [an integer scale m](hyp:m),
and [a point x](hyp:x), [the dyadic mean is the integral of f over x's dyadic
cell divided by that cell's area](goal). -/
noncomputable def dyadicMean (f : ℝ × ℝ → ℝ) (m : ℤ) (x : ℝ × ℝ) : ℝ :=
  (volume (dyadicCell m x)).toReal⁻¹ * ∫ y in dyadicCell m x, f y

-- @node: dyadicCellIndex_eq
/-- If [x belongs to the dyadic interval with index a at scale m](hyp:hx),
then [its dyadic cell index at that scale equals a](goal). -/
lemma dyadicCellIndex_eq (m : ℤ) (a : ℕ) {x : ℝ}
    (hx : x ∈ dyadicInterval m a) : dyadicCellIndex m x = a := by
  have hp : 0 < (2 : ℝ) ^ m := by positivity
  have hx0 : 0 ≤ x := (by positivity : 0 ≤ (2 : ℝ) ^ m * a).trans hx.1
  apply (Nat.floor_eq_iff (div_nonneg hx0 hp.le)).mpr
  exact ⟨(le_div_iff₀ hp).mpr (by simpa [mul_comm] using hx.1),
    (div_lt_iff₀ hp).mpr (by simpa [mul_comm] using hx.2)⟩

-- @node: mem_dyadicCell
/-- If [x lies in the nonnegative quadrant](hyp:hx), then [x belongs to its
own dyadic cell at every integer scale m](goal). -/
lemma mem_dyadicCell (m : ℤ) {x : ℝ × ℝ} (hx : x ∈ Rplus ×ˢ Rplus) :
    x ∈ dyadicCell m x := by
  have h (t : ℝ) (ht : 0 ≤ t) : t ∈ dyadicInterval m (dyadicCellIndex m t) := by
    have hp : 0 < (2 : ℝ) ^ m := by positivity
    constructor
    · simpa [mul_comm, dyadicCellIndex] using
        (le_div_iff₀ hp).mp (Nat.floor_le (div_nonneg ht hp.le))
    · simpa [mul_comm, dyadicCellIndex] using
        (div_lt_iff₀ hp).mp (Nat.lt_floor_add_one (t / (2 : ℝ) ^ m))
  exact ⟨h x.1 hx.1, h x.2 hx.2⟩

-- @node: measurableSet_dyadicCell
/-- [The dyadic cell assigned to any point x at any integer scale m is a
measurable subset of the plane](goal). -/
lemma measurableSet_dyadicCell (m : ℤ) (x : ℝ × ℝ) : MeasurableSet (dyadicCell m x) :=
  measurableSet_Ico.prod measurableSet_Ico

-- @node: volume_dyadicCell
/-- [The area of the dyadic cell assigned to x at scale m equals 2 to the
power 2m](goal). -/
lemma volume_dyadicCell (m : ℤ) (x : ℝ × ℝ) :
    volume (dyadicCell m x) = ENNReal.ofReal ((2 : ℝ) ^ (2 * m)) :=
  volume_dyadicRect m (dyadicCellIndex m x.1, dyadicCellIndex m x.2)

-- @node: volume_dyadicCell_pos
/-- [The area of the dyadic cell assigned to x at scale m, expressed as a
real number, is strictly positive](goal). -/
lemma volume_dyadicCell_pos (m : ℤ) (x : ℝ × ℝ) :
    0 < (volume (dyadicCell m x)).toReal := by
  rw [volume_dyadicCell, ENNReal.toReal_ofReal (by positivity)]
  positivity

-- @node: dyadicMean_measurable
/-- [For any real-valued function f on the plane and integer scale m, its
dyadic mean is a measurable function of the evaluation point](goal). -/
@[fun_prop] lemma dyadicMean_measurable (f : ℝ × ℝ → ℝ) (m : ℤ) :
    Measurable (dyadicMean f m) := by
  have hi : Measurable (fun x : ℝ × ℝ =>
      (dyadicCellIndex m x.1, dyadicCellIndex m x.2)) := by
    unfold dyadicCellIndex
    fun_prop
  let a : ℕ × ℕ → ℝ := fun p =>
    (volume (dyadicInterval m p.1 ×ˢ dyadicInterval m p.2)).toReal⁻¹ *
      ∫ y in dyadicInterval m p.1 ×ˢ dyadicInterval m p.2, f y
  change Measurable (a ∘ (fun x : ℝ × ℝ =>
    (dyadicCellIndex m x.1, dyadicCellIndex m x.2)))
  exact (measurable_of_countable a).comp hi

-- @node: dyadicMean_atoms
/-- [The dyadic means of any three functions at scale m are each constant
on every dyadic rectangle at that scale](goal). -/
lemma dyadicMean_atoms (f : Fin 3 → ℝ × ℝ → ℝ) (m : ℤ) :
    StepAtoms (fun v => dyadicMean (f v) m) m := by
  intro v a b x y hx hy
  simp only [dyadicMean, dyadicCell, dyadicCellIndex_eq m a hx.1,
    dyadicCellIndex_eq m b hx.2, dyadicCellIndex_eq m a hy.1,
    dyadicCellIndex_eq m b hy.2]

-- @node: dyadicMean_norm_le
/-- If [the absolute value of f is at most C throughout x's dyadic cell at
scale m](hyp:hC), then [the absolute value of its dyadic mean at x is at most C](goal). -/
lemma dyadicMean_norm_le (f : ℝ × ℝ → ℝ) (m : ℤ) (x : ℝ × ℝ) (C : ℝ)
    (hC : ∀ y ∈ dyadicCell m x, ‖f y‖ ≤ C) : ‖dyadicMean f m x‖ ≤ C := by
  have hfinite : volume (dyadicCell m x) ≠ ⊤ := by simp [volume_dyadicCell]
  have : IsFiniteMeasure (volume.restrict (dyadicCell m x)) :=
    ⟨by simpa using hfinite.lt_top⟩
  have hi := norm_integral_le_of_norm_le_const (μ := volume.restrict (dyadicCell m x))
    ((ae_restrict_mem (measurableSet_dyadicCell m x)).mono hC)
  have hp := volume_dyadicCell_pos m x
  dsimp only [dyadicMean]
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp)]
  calc
    _ ≤ (volume (dyadicCell m x)).toReal⁻¹ *
        (C * (volume (dyadicCell m x)).toReal) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hp.le)
      simpa [measureReal_def] using hi
    _ = C := by field_simp

-- @node: dyadicMean_sub_const
/-- If [f is integrable over x's dyadic cell at scale m](hyp:hf), then
[averaging f minus a constant c gives the dyadic mean of f minus c](goal). -/
lemma dyadicMean_sub_const (f : ℝ × ℝ → ℝ) (m : ℤ) (x : ℝ × ℝ) (c : ℝ)
    (hf : IntegrableOn f (dyadicCell m x)) :
    dyadicMean (fun y => f y - c) m x = dyadicMean f m x - c := by
  have : IsFiniteMeasure (volume.restrict (dyadicCell m x)) :=
    ⟨by simp [volume_dyadicCell]⟩
  have hp := (volume_dyadicCell_pos m x).ne'
  simp only [dyadicMean, integral_sub hf (integrable_const c), integral_const,
    measureReal_def, Measure.restrict_apply_univ, smul_eq_mul, mul_sub]
  field_simp

-- @node: dyadicCell_subset_quadrant
/-- [Every dyadic cell assigned to a point x at an integer scale m lies
entirely in the nonnegative quadrant](goal). -/
lemma dyadicCell_subset_quadrant (m : ℤ) (x : ℝ × ℝ) :
    dyadicCell m x ⊆ Rplus ×ˢ Rplus := by
  intro y hy
  exact ⟨(by positivity : 0 ≤ (2 : ℝ) ^ m * dyadicCellIndex m x.1).trans hy.1.1,
    (by positivity : 0 ≤ (2 : ℝ) ^ m * dyadicCellIndex m x.2).trans hy.2.1⟩

-- @node: dist_lt_of_mem_dyadicCell
/-- If [x lies in the nonnegative quadrant](hyp:hx) and [y lies in x's
dyadic cell at scale m](hyp:hy), then [the maximum of the absolute coordinate
differences between y and x is less than 2 to the power m](goal). -/
lemma dist_lt_of_mem_dyadicCell (m : ℤ) {x y : ℝ × ℝ}
    (hx : x ∈ Rplus ×ˢ Rplus) (hy : y ∈ dyadicCell m x) :
    dist y x < (2 : ℝ) ^ m := by
  have hx' := mem_dyadicCell m hx
  have h (a b l : ℝ) (ha : a ∈ Set.Ico l (l + (2 : ℝ)^m))
      (hb : b ∈ Set.Ico l (l + (2 : ℝ)^m)) : dist a b < (2 : ℝ)^m := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
  rw [Prod.dist_eq, max_lt_iff]
  constructor
  · apply h _ _ ((2 : ℝ)^m * dyadicCellIndex m x.1)
    · simpa only [dyadicInterval, mul_add, mul_one] using hy.1
    · simpa only [dyadicInterval, mul_add, mul_one] using hx'.1
  · apply h _ _ ((2 : ℝ)^m * dyadicCellIndex m x.2)
    · simpa only [dyadicInterval, mul_add, mul_one] using hy.2
    · simpa only [dyadicInterval, mul_add, mul_one] using hx'.2

-- @node: compactSupport_quadrant_box
/-- If [f has compact support on the plane](hyp:hf), then [there is a
nonnegative real bound R such that f vanishes whenever either coordinate
exceeds R](goal). -/
lemma compactSupport_quadrant_box (f : ℝ × ℝ → ℝ) (hf : HasCompactSupport f) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x : ℝ × ℝ,
      (R < x.1 ∨ R < x.2) → f x = 0 := by
  obtain ⟨R, hR⟩ := hf.isBounded.exists_norm_le
  refine ⟨max R 0, le_max_right _ _, ?_⟩
  intro x hx
  by_contra hn
  have hb : ‖x‖ ≤ R := hR x (subset_tsupport f (Function.mem_support.mpr hn))
  have hx₁ : x.1 ≤ ‖x‖ := (le_abs_self _).trans (norm_fst_le x)
  have hx₂ : x.2 ≤ ‖x‖ := (le_abs_self _).trans (norm_snd_le x)
  rcases hx with hx | hx <;> linarith [le_max_left R 0]

-- @node: dyadicMean_compact
/-- If [f vanishes whenever either coordinate exceeds R](hyp:hf) and
[the integer scale m is nonpositive](hyp:hm), then [its dyadic mean vanishes
at every point in the nonnegative quadrant with either coordinate greater
than R plus one](goal). -/
lemma dyadicMean_compact (f : ℝ × ℝ → ℝ) (R : ℝ)
    (hf : ∀ x : ℝ × ℝ, (R < x.1 ∨ R < x.2) → f x = 0)
    (m : ℤ) (hm : m ≤ 0) :
    ∀ x : ℝ × ℝ, 0 ≤ x.1 → 0 ≤ x.2 →
      (R + 1 < x.1 ∨ R + 1 < x.2) → dyadicMean f m x = 0 := by
  intro x hx₁ hx₂ hx
  have hmesh : (2 : ℝ) ^ m ≤ 1 := by
    exact zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 2) hm
  have hzero : ∀ y ∈ dyadicCell m x, f y = 0 := by
    intro y hy
    have hd := dist_lt_of_mem_dyadicCell m ⟨hx₁, hx₂⟩ hy
    rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq, abs_lt, abs_lt] at hd
    apply hf
    rcases hx with hx | hx
    · exact Or.inl (by linarith [hd.1.1])
    · exact Or.inr (by linarith [hd.2.1])
  have hi : ∫ y in dyadicCell m x, f y = 0 := by
    apply integral_eq_zero_of_ae
    exact (ae_restrict_mem (measurableSet_dyadicCell m x)).mono hzero
  simp [dyadicMean, hi]

-- @node: dyadicMean_uniform_error
/-- If [f is continuous](hyp:hf), [f has compact support](hyp:hc), and
[the tolerance ε is positive](hyp:hε), then [there is a positive mesh threshold
such that every finer dyadic mean differs from f by at most ε everywhere in
the nonnegative quadrant](goal). -/
lemma dyadicMean_uniform_error (f : ℝ × ℝ → ℝ) (hf : Continuous f)
    (hc : HasCompactSupport f) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ m : ℤ, (2 : ℝ)^m < δ →
      ∀ x ∈ Rplus ×ˢ Rplus, ‖dyadicMean f m x - f x‖ ≤ ε := by
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuous_iff.mp
    (hc.uniformContinuous_of_continuous hf) ε hε
  refine ⟨δ, hδ, ?_⟩
  intro m hm x hx
  rw [← dyadicMean_sub_const f m x (f x) ((hf.integrable_of_hasCompactSupport hc).integrableOn)]
  apply dyadicMean_norm_le
  intro y hy
  exact (hclose ((dist_lt_of_mem_dyadicCell m hx hy).trans hm)).le

-- @node: quadrant_box_measure_ne_top
/-- [The square with both coordinates between zero and R has finite
Lebesgue measure restricted to the nonnegative quadrant](goal). -/
lemma quadrant_box_measure_ne_top (R : ℝ) :
    quadrantMeasure (Set.Icc 0 R ×ˢ Set.Icc 0 R) ≠ ⊤ := by
  have hfinite : volume (Set.Icc 0 R ×ˢ Set.Icc 0 R) ≠ ⊤ :=
    (isCompact_Icc.prod isCompact_Icc).measure_ne_top
  exact ne_top_of_le_ne_top hfinite (Measure.restrict_apply_le _ _)

-- @node: quadrant_box_domination
/-- If [the absolute value of f is bounded by C on the nonnegative quadrant](hyp:hC)
and [f vanishes there whenever either coordinate exceeds R](hyp:hR), then
[almost everywhere for quadrant Lebesgue measure, the absolute value of f is
bounded by C times the indicator of the square with coordinates between zero
and R](goal). -/
lemma quadrant_box_domination (f : ℝ × ℝ → ℝ) (R C : ℝ)
    (hC : ∀ x ∈ Rplus ×ˢ Rplus, ‖f x‖ ≤ C)
    (hR : ∀ x ∈ Rplus ×ˢ Rplus, (R < x.1 ∨ R < x.2) → f x = 0) :
    ∀ᵐ x ∂quadrantMeasure, ‖f x‖ ≤
      (Set.Icc 0 R ×ˢ Set.Icc 0 R).indicator (fun _ => C) x := by
  filter_upwards [ae_restrict_mem (measurableSet_Ici.prod measurableSet_Ici)] with x hx
  by_cases hb : x ∈ Set.Icc 0 R ×ˢ Set.Icc 0 R
  · simpa only [Set.indicator_of_mem hb] using hC x hx
  · rw [Set.indicator_of_notMem hb]
    have hout : R < x.1 ∨ R < x.2 := by
      change 0 ≤ x.1 ∧ 0 ≤ x.2 at hx
      simp only [Set.mem_prod, Set.mem_Icc, not_and] at hb
      by_cases h : x.1 ≤ R
      · exact Or.inr (lt_of_not_ge (hb ⟨hx.1, h⟩ hx.2))
      · exact Or.inl (lt_of_not_ge h)
    rw [hR x hx hout, norm_zero]

-- @node: quadrant_memLp_of_box
/-- If [f is measurable](hyp:hf), [its absolute value is bounded by C on the
nonnegative quadrant](hyp:hC), and [it vanishes there whenever either coordinate
exceeds R](hyp:hR), then [f belongs to L³ for quadrant Lebesgue measure](goal). -/
lemma quadrant_memLp_of_box (f : ℝ × ℝ → ℝ) (hf : Measurable f) (R C : ℝ)
    (hC : ∀ x ∈ Rplus ×ˢ Rplus, ‖f x‖ ≤ C)
    (hR : ∀ x ∈ Rplus ×ˢ Rplus, (R < x.1 ∨ R < x.2) → f x = 0) :
    MemLp f 3 quadrantMeasure := by
  have hbox : MemLp ((Set.Icc 0 R ×ˢ Set.Icc 0 R).indicator (fun _ => C))
      3 quadrantMeasure := memLp_indicator_const 3
    (measurableSet_Icc.prod measurableSet_Icc) C (Or.inr (quadrant_box_measure_ne_top R))
  apply hbox.mono' (by fun_prop)
  exact quadrant_box_domination f R C hC hR

-- @node: quadrant_L3_error_bound
/-- If [C is nonnegative](hyp:hC0), [the absolute value of f is bounded by C
on the nonnegative quadrant](hyp:hC), and [f vanishes there whenever either
coordinate exceeds R](hyp:hR), then [the real-valued L³ seminorm of f is at most
C times the cube root of the quadrant measure of the square with coordinates
between zero and R](goal).

The real-valued seminorm uses the convention that an infinite extended seminorm
is represented by zero. -/
lemma quadrant_L3_error_bound (f : ℝ × ℝ → ℝ) (R C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ x ∈ Rplus ×ˢ Rplus, ‖f x‖ ≤ C)
    (hR : ∀ x ∈ Rplus ×ˢ Rplus, (R < x.1 ∨ R < x.2) → f x = 0) :
    (eLpNorm f 3 quadrantMeasure).toReal ≤
      C * (quadrantMeasure (Set.Icc 0 R ×ˢ Set.Icc 0 R) ^ (1 / (3 : ℝ))).toReal := by
  have hbox : MemLp ((Set.Icc 0 R ×ˢ Set.Icc 0 R).indicator (fun _ => C))
      3 quadrantMeasure := memLp_indicator_const 3
    (measurableSet_Icc.prod measurableSet_Icc) C (Or.inr (quadrant_box_measure_ne_top R))
  have hb : eLpNorm f 3 quadrantMeasure ≤
      eLpNorm ((Set.Icc 0 R ×ˢ Set.Icc 0 R).indicator (fun _ => C)) 3 quadrantMeasure := by
    apply eLpNorm_mono_ae
    filter_upwards [quadrant_box_domination f R C hC hR] with x hx
    exact hx.trans (le_abs_self _)
  calc
    _ ≤ (eLpNorm ((Set.Icc 0 R ×ˢ Set.Icc 0 R).indicator (fun _ => C))
        3 quadrantMeasure).toReal := ENNReal.toReal_mono hbox.2.ne hb
    _ = _ := by
      rw [eLpNorm_indicator_const (measurableSet_Icc.prod measurableSet_Icc)
        (by norm_num : (3 : ENNReal) ≠ 0) (by norm_num : (3 : ENNReal) ≠ ⊤),
        ENNReal.toReal_mul, Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg C),
        abs_of_nonneg hC0]
      norm_num

-- @node: dyadicMean_memLp
/-- If [f is continuous](hyp:hf), [f has compact support](hyp:hc), and
[m is a nonpositive integer scale](hyp:hm), then [its dyadic mean at scale m
belongs to L³ for quadrant Lebesgue measure](goal). -/
lemma dyadicMean_memLp (f : ℝ × ℝ → ℝ) (hf : Continuous f) (hc : HasCompactSupport f)
    (m : ℤ) (hm : m ≤ 0) : MemLp (dyadicMean f m) 3 quadrantMeasure := by
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hf
  obtain ⟨R, _, hR⟩ := compactSupport_quadrant_box f hc
  apply quadrant_memLp_of_box _ (by fun_prop) (R + 1) C
  · intro x _
    exact dyadicMean_norm_le f m x C (fun y _ => hC y)
  · intro x hx hout
    exact dyadicMean_compact f R hR m hm x hx.1 hx.2 hout

-- @node: dyadicMean_L3_tendsto
/-- If [f is continuous](hyp:hf) and [f has compact support](hyp:hc), then
[the L³ error of its dyadic means on the nonnegative quadrant tends to zero
as the mesh sizes decrease through the sequence 1, one half, one quarter,
and so on](goal). -/
lemma dyadicMean_L3_tendsto (f : ℝ × ℝ → ℝ) (hf : Continuous f)
    (hc : HasCompactSupport f) :
    Tendsto (fun n : ℕ => (eLpNorm (fun x => dyadicMean f (-(n : ℤ)) x - f x)
      3 quadrantMeasure).toReal) atTop (𝓝 0) := by
  obtain ⟨R, hR0, hR⟩ := compactSupport_quadrant_box f hc
  let A := (quadrantMeasure (Set.Icc 0 (R + 1) ×ˢ Set.Icc 0 (R + 1)) ^
    (1 / (3 : ℝ))).toReal
  have hA : 0 ≤ A := ENNReal.toReal_nonneg
  apply (tendsto_order.2 ⟨?_, ?_⟩)
  · intro a ha
    exact Eventually.of_forall (fun _ => ha.trans_le ENNReal.toReal_nonneg)
  · intro ε hε
    have he : 0 < ε / (A + 1) := div_pos hε (by linarith)
    obtain ⟨δ, hδ, hclose⟩ := dyadicMean_uniform_error f hf hc he
    have hmesh : Tendsto (fun n : ℕ => (2 : ℝ) ^ (-(n : ℤ))) atTop (𝓝 0) := by
      simpa only [zpow_neg, zpow_natCast, inv_pow] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
          (by norm_num : (2 : ℝ)⁻¹ < 1))
    filter_upwards [hmesh.eventually (gt_mem_nhds hδ)] with n hn
    have hb := quadrant_L3_error_bound
      (fun x => dyadicMean f (-(n : ℤ)) x - f x) (R + 1) (ε / (A + 1)) he.le
      (hclose _ hn) (by
        intro x hx hout
        rw [dyadicMean_compact f R hR _ (by omega) x hx.1 hx.2 hout,
          hR x (hout.imp (fun h => by linarith) (fun h => by linarith)), sub_self])
    apply hb.trans_lt
    change ε / (A + 1) * A < ε
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by linarith : 0 < A + 1)).mpr
    nlinarith

-- @node: fact_one_le_L3Exponent
/-- [The L³ exponent satisfies the lower bound of one required for the
normed Lᵖ space construction](goal). -/
instance fact_one_le_L3Exponent : Fact (1 ≤ (3 : ENNReal)) := ⟨by norm_num⟩

-- @node: L3_dist_toLp
/-- If [f belongs to L³ for quadrant Lebesgue measure](hyp:hf) and [g belongs
to the same space](hyp:hg), then [the distance between their L³ equivalence
classes equals the L³ seminorm of their pointwise difference](goal). -/
lemma L3_dist_toLp (f g : ℝ × ℝ → ℝ) (hf : MemLp f 3 quadrantMeasure)
    (hg : MemLp g 3 quadrantMeasure) :
    dist (hf.toLp f) (hg.toLp g) = (eLpNorm (fun x => f x - g x) 3 quadrantMeasure).toReal := by
  rw [dist_edist, Lp.edist_toLp_toLp]
  rfl

-- @node: L3_error_triangle
/-- For [a third real-valued function h on the plane](hyp:h), if [f belongs to
L³ for quadrant Lebesgue measure](hyp:hf), [g belongs to that space](hyp:hg),
and [h belongs to that space](hyp:hh), then [the L³ error
between f and h is at most the sum of the errors between f and g and between
g and h](goal). -/
lemma L3_error_triangle (f g h : ℝ × ℝ → ℝ)
    (hf : MemLp f 3 quadrantMeasure) (hg : MemLp g 3 quadrantMeasure)
    (hh : MemLp h 3 quadrantMeasure) :
    (eLpNorm (fun x => f x - h x) 3 quadrantMeasure).toReal ≤
      (eLpNorm (fun x => f x - g x) 3 quadrantMeasure).toReal +
      (eLpNorm (fun x => g x - h x) 3 quadrantMeasure).toReal := by
  rw [← L3_dist_toLp f h hf hh, ← L3_dist_toLp f g hf hg, ← L3_dist_toLp g h hg hh]
  exact dist_triangle _ _ _

-- @node: continuous_compact_L3_approximation
/-- If [f belongs to L³ for quadrant Lebesgue measure](hyp:hf) and [ε is
positive](hyp:hε), then [there exists a continuous function g with compact
support on the plane that belongs to the same L³ space and has L³ distance
from f at most ε](goal). -/
lemma continuous_compact_L3_approximation (f : ℝ × ℝ → ℝ)
    (hf : MemLp f 3 quadrantMeasure) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : ℝ × ℝ → ℝ, Continuous g ∧ HasCompactSupport g ∧
      MemLp g 3 quadrantMeasure ∧
      (eLpNorm (fun x => g x - f x) 3 quadrantMeasure).toReal ≤ ε := by
  let H := (Rplus ×ˢ Rplus).indicator f
  have hH : MemLp H 3 (volume : Measure (ℝ × ℝ)) :=
    (memLp_indicator_iff_restrict (measurableSet_Ici.prod measurableSet_Ici)).mpr hf
  obtain ⟨g, hc, he, hg, hmem⟩ :=
    hH.exists_hasCompactSupport_eLpNorm_sub_le (by norm_num : (3 : ENNReal) ≠ ⊤)
      (ne_of_gt (ENNReal.ofReal_pos.mpr hε))
  refine ⟨g, hg, hc, hmem.mono_measure Measure.restrict_le_self, ?_⟩
  have heq : (fun x => g x - f x) =ᵐ[quadrantMeasure] -(H - g) := by
    filter_upwards [ae_restrict_mem (measurableSet_Ici.prod measurableSet_Ici)] with x hx
    simp [H, Set.indicator_of_mem hx]
  have hb : eLpNorm (fun x => g x - f x) 3 quadrantMeasure ≤ ENNReal.ofReal ε := by
    rw [eLpNorm_congr_ae heq, eLpNorm_neg]
    exact (eLpNorm_mono_measure (H - g) Measure.restrict_le_self).trans he
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hb).trans_eq (ENNReal.toReal_ofReal hε.le)

-- @node: dyadicMean_properties
/-- If [each of three functions is continuous](hyp:hf) and [each has compact
support](hyp:hc), then [their dyadic means at mesh size 2 to the power minus n
are bounded on the nonnegative quadrant, vanish there outside a bounded box
for each function, are constant on every dyadic rectangle at that scale, and
belong to L³ for quadrant Lebesgue measure](goal). -/
lemma dyadicMean_properties (f : Fin 3 → ℝ × ℝ → ℝ)
    (hf : ∀ v, Continuous (f v)) (hc : ∀ v, HasCompactSupport (f v))
    (n : ℕ) :
    StepBounded (fun v => dyadicMean (f v) (-(n : ℤ))) ∧
    StepCompact (fun v => dyadicMean (f v) (-(n : ℤ))) ∧
    StepAtoms (fun v => dyadicMean (f v) (-(n : ℤ))) (-(n : ℤ)) ∧
    ContinuityInputs (fun v => dyadicMean (f v) (-(n : ℤ))) := by
  refine ⟨?_, ?_, dyadicMean_atoms f _, ?_⟩
  · intro v
    obtain ⟨C, hC⟩ := (hc v).exists_bound_of_continuous (hf v)
    refine ⟨C, ?_⟩
    intro x _
    exact dyadicMean_norm_le (f v) _ x C (fun y _ => hC y)
  · intro v
    obtain ⟨R, _, hR⟩ := compactSupport_quadrant_box (f v) (hc v)
    exact ⟨R + 1, dyadicMean_compact (f v) R hR _ (by omega)⟩
  · intro v
    exact dyadicMean_memLp (f v) (hf v) (hc v) _ (by omega)

-- @node: exists_common_dyadic_L3_approximation
/-- If [each of the three functions in F belongs to L³ for quadrant Lebesgue
measure](hyp:hF) and [ε is positive](hyp:hε), then [there are three approximating
functions G and a common integer scale m no greater than s such that each
approximant is bounded on the nonnegative quadrant, vanishes there outside
a bounded box, is constant on scale-m dyadic rectangles, belongs to L³, and
has L³ error from its corresponding function in F at most ε](goal). -/
lemma exists_common_dyadic_L3_approximation (F : Fin 3 → ℝ × ℝ → ℝ)
    (hF : ContinuityInputs F) (s : ℤ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (G : Fin 3 → ℝ × ℝ → ℝ) (m : ℤ),
      StepBounded G ∧ StepCompact G ∧ StepAtoms G m ∧ ContinuityInputs G ∧ m ≤ s ∧
      ∀ v, (eLpNorm (fun x => G v x - F v x) 3 quadrantMeasure).toReal ≤ ε := by
  have hc (v : Fin 3) := continuous_compact_L3_approximation (F v) (hF v) (ε / 2)
    (by linarith)
  choose f hf hcompact hmem herr using hc
  have he (v : Fin 3) : ∀ᶠ n : ℕ in atTop,
      (eLpNorm (fun x => dyadicMean (f v) (-(n : ℤ)) x - f v x) 3 quadrantMeasure).toReal
        < ε / 2 :=
    (dyadicMean_L3_tendsto (f v) (hf v) (hcompact v)).eventually
      (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 2))
  have hall : ∀ᶠ n : ℕ in atTop, ∀ v : Fin 3,
      (eLpNorm (fun x => dyadicMean (f v) (-(n : ℤ)) x - f v x) 3 quadrantMeasure).toReal
        < ε / 2 := by
    exact eventually_all.mpr he
  have hs : ∀ᶠ n : ℕ in atTop, -(n : ℤ) ≤ s := by
    filter_upwards [eventually_ge_atTop ((-s).toNat)] with n hn
    have hle : -s ≤ ((-s).toNat : ℤ) := by omega
    have hn' : (((-s).toNat : ℕ) : ℤ) ≤ n := by exact_mod_cast hn
    omega
  obtain ⟨n, hn, hns⟩ := (hall.and hs).exists
  let G := fun v => dyadicMean (f v) (-(n : ℤ))
  obtain ⟨hB, hC, hA, hL⟩ := dyadicMean_properties f hf hcompact n
  refine ⟨G, -(n : ℤ), hB, hC, hA, hL, hns, ?_⟩
  intro v
  exact (L3_error_triangle (G v) (f v) (F v) (hL v) (hmem v) (hF v)).trans
    (by linarith [hn v, herr v])

-- @node: common_dyadic_L3_sequence
/-- If [each of the three functions in F belongs to L³ for quadrant Lebesgue
measure](hyp:hF), then [there is a sequence of triples of approximants, each
bounded on the nonnegative quadrant, vanishing there outside bounded boxes,
constant on dyadic rectangles at a common integer scale no greater than s,
and belonging to L³, such that each component's L³ error tends to zero and
its L³ norm tends to that of the corresponding component of F](goal). -/
lemma common_dyadic_L3_sequence (F : Fin 3 → ℝ × ℝ → ℝ)
    (hF : ContinuityInputs F) (s : ℤ) :
    ∃ (G : ℕ → Fin 3 → ℝ × ℝ → ℝ) (m : ℕ → ℤ),
      (∀ j, StepBounded (G j) ∧ StepCompact (G j) ∧ StepAtoms (G j) (m j) ∧
        ContinuityInputs (G j)) ∧
      (∀ j, m j ≤ s) ∧
      (∀ v, Tendsto (fun j =>
        (eLpNorm (fun x => G j v x - F v x) 3 quadrantMeasure).toReal) atTop (𝓝 0)) ∧
      (∀ v, Tendsto (fun j => (eLpNorm (G j v) 3 quadrantMeasure).toReal) atTop
        (𝓝 ((eLpNorm (F v) 3 quadrantMeasure).toReal))) := by
  have ha (j : ℕ) := exists_common_dyadic_L3_approximation F hF s
    (1 / ((j : ℝ) + 1)) (by positivity)
  choose G m hB hC hA hL hs he using ha
  have hdiff (v : Fin 3) : Tendsto (fun j =>
      (eLpNorm (fun x => G j v x - F v x) 3 quadrantMeasure).toReal) atTop (𝓝 0) :=
    squeeze_zero (fun _ => ENNReal.toReal_nonneg) (fun j => he j v)
      tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨G, m, fun j => ⟨hB j, hC j, hA j, hL j⟩, hs, hdiff, ?_⟩
  intro v
  have ht : Tendsto (fun j => (hL j v).toLp (G j v)) atTop (𝓝 ((hF v).toLp (F v))) := by
    apply (tendsto_iff_dist_tendsto_zero).mpr
    simpa only [L3_dist_toLp] using hdiff v
  simpa only [Lp.norm_toLp] using ht.norm

end Papers.OaiBoundDyadicTriangular

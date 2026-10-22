module
public import Causalean.Stat.EmpiricalProcess.Countable.Threshold
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Order.Group.Lattice

/-! A deterministic countable skeleton for population-centered strict-tail
processes. The skeleton is shared by every integrable frozen score and keeps
the band boundary and atoms. -/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory Filter
open scoped BigOperators Topology
open Causalean.Stat.EmpiricalProcess.Countable

/-- For [a score](hyp:R), [a marked value](hyp:f), and [a threshold](hyp:t), [the strict-threshold contribution equals its affine closed-threshold representation](goal). -/
-- @node: strict_threshold_eq_affine_closed
lemma strict_threshold_eq_affine_closed {Ω : Type*} (R f : Ω → ℝ) (t : ℝ) :
    (fun x => if t < R x then f x else 0) =
      thresholdFunction true R f (-f) t := by
  funext x
  by_cases h : t < R x
  · simp [thresholdFunction, h, not_le_of_gt h]
  · simp [thresholdFunction, h, le_of_not_gt h]

/-- If [the score is measurable](hyp:hR), [the mark is integrable](hyp:hf), and [a sequence of thresholds approaches the target from the prescribed side](hyp:hs), then [the corresponding truncated integrals converge to the truncated integral at the target threshold](goal). -/
-- @node: strict_threshold_integral_tendsto
lemma strict_threshold_integral_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (R f : Ω → ℝ) (hR : Measurable R) (hf : Integrable f μ)
    (s : ℕ → ℝ) (t : ℝ) (hs : OneSidedApproximates true s t) :
    Tendsto (fun k => ∫ x, (if s k < R x then f x else 0) ∂μ)
      atTop (𝓝 (∫ x, (if t < R x then f x else 0) ∂μ)) := by
  simp_rw [strict_threshold_eq_affine_closed]
  exact thresholdFunction_integral_tendsto μ true R f (-f) hR hf hf.neg s t hs

/-- Given [a measurable score](hyp:hR) and [a threshold set](hyp:T), there is [a countable subset](goal) on which checking the uniform centered strict-threshold bound is equivalent to checking it on the full set, for every integrable mark, sample, and bound. -/
-- @node: centered_strict_threshold_countable_reduction
lemma centered_strict_threshold_countable_reduction {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (R : Ω → ℝ) (hR : Measurable R) (T : Set ℝ) :
    ∃ D : Set ℝ, D.Countable ∧ D ⊆ T ∧
      ∀ (f : Ω → ℝ), Integrable f μ → ∀ (n : ℕ) (x : Fin n → Ω) (B : ℝ),
        (∀ t ∈ T,
          |(∑ i : Fin n, if t < R (x i) then f (x i) else 0) -
            (n : ℝ) * ∫ y, (if t < R y then f y else 0) ∂μ| ≤ B) ↔
        (∀ t ∈ D,
          |(∑ i : Fin n, if t < R (x i) then f (x i) else 0) -
            (n : ℝ) * ∫ y, (if t < R y then f y else 0) ∂μ| ≤ B) := by
  obtain ⟨D, hD, hDT, _, hApprox⟩ := exists_countable_oneSided_skeleton true T
  refine ⟨D, hD, hDT, ?_⟩
  intro f hf n x B
  constructor
  · intro h t ht
    exact h t (hDT ht)
  · intro h t ht
    obtain ⟨s, hsD, hs⟩ := hApprox t ht
    have hPoint (i : Fin n) :
        Tendsto (fun k => if s k < R (x i) then f (x i) else 0) atTop
          (𝓝 (if t < R (x i) then f (x i) else 0)) := by
      have hp := thresholdFunction_tendsto true R f (-f) s t hs (x i)
      simpa only [← strict_threshold_eq_affine_closed] using hp
    have hSum := tendsto_finsetSum Finset.univ (fun i _ => hPoint i)
    have hMean := strict_threshold_integral_tendsto μ R f hR hf s t hs
    exact le_of_tendsto ((hSum.sub (tendsto_const_nhds.mul hMean)).abs)
      (Eventually.of_forall (fun k => h (s k) (hsD k)))

-- @node: measurable_centered_strict_threshold_sum
/-- If [the score is measurable](hyp:hR), [the marked function is jointly measurable](hyp:hf), and [each sampled observation map is measurable](hyp:hx), then [the centered strict-threshold sum at the threshold is measurable](goal). -/
@[fun_prop]
lemma measurable_centered_strict_threshold_sum {Ω W : Type*}
    [MeasurableSpace Ω] [MeasurableSpace W]
    (μ : Measure Ω) [SFinite μ] (R : Ω → ℝ) (hR : Measurable R)
    (f : W → Ω → ℝ) (hf : Measurable (Function.uncurry f))
    {n : ℕ} (x : Fin n → W → Ω) (hx : ∀ i, Measurable (x i)) (t : ℝ) :
    Measurable (fun w => (∑ i : Fin n, if t < R (x i w) then f w (x i w) else 0) -
      (n : ℝ) * ∫ y, (if t < R y then f w y else 0) ∂μ) := by
  have hmark : Measurable (fun z : W × Ω => if t < R z.2 then f z.1 z.2 else 0) := by
    exact Measurable.ite (measurableSet_lt measurable_const (hR.comp measurable_snd))
      hf measurable_const
  have hsum : Measurable (fun w => ∑ i : Fin n,
      if t < R (x i w) then f w (x i w) else 0) := by
    exact Finset.measurable_fun_sum _ (fun i _ =>
      hmark.comp (measurable_id.prodMk (hx i)))
  exact hsum.sub (measurable_const.mul hmark.stronglyMeasurable.integral_prod_right'.measurable)

/-- If [the score is measurable](hyp:hR), [the marked function is jointly measurable](hyp:hf), [the sampled observation maps are measurable](hyp:hx), [the good set is measurable](hyp:hG), [the marks are integrable on that set](hyp:hInt), and [the bound is measurable](hyp:hB), then [the event that the centered strict-threshold process stays within the bound over the threshold set is measurable](goal). -/
-- @node: measurableSet_centered_strict_threshold_uniform_event
lemma measurableSet_centered_strict_threshold_uniform_event {Ω W : Type*}
    [MeasurableSpace Ω] [MeasurableSpace W]
    (μ : Measure Ω) [SFinite μ] (R : Ω → ℝ) (hR : Measurable R)
    (f : W → Ω → ℝ) (hf : Measurable (Function.uncurry f))
    {n : ℕ} (x : Fin n → W → Ω) (hx : ∀ i, Measurable (x i))
    (T : Set ℝ) (G : Set W) (hG : MeasurableSet G)
    (hInt : ∀ w ∈ G, Integrable (f w) μ) (B : W → ℝ) (hB : Measurable B) :
    MeasurableSet {w | w ∈ G ∧ ∀ t ∈ T,
      |(∑ i : Fin n, if t < R (x i w) then f w (x i w) else 0) -
        (n : ℝ) * ∫ y, (if t < R y then f w y else 0) ∂μ| ≤ B w} := by
  obtain ⟨D, hD, _, hReduction⟩ :=
    centered_strict_threshold_countable_reduction μ R hR T
  let : Countable D := hD.to_subtype
  have hEq : {w | w ∈ G ∧ ∀ t ∈ T,
      |(∑ i : Fin n, if t < R (x i w) then f w (x i w) else 0) -
        (n : ℝ) * ∫ y, (if t < R y then f w y else 0) ∂μ| ≤ B w} =
      G ∩ ⋂ t : D, {w |
        |(∑ i : Fin n, if t.1 < R (x i w) then f w (x i w) else 0) -
          (n : ℝ) * ∫ y, (if t.1 < R y then f w y else 0) ∂μ| ≤ B w} := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    by_cases hw : w ∈ G
    · simp only [hw, true_and]
      rw [hReduction (f w) (hInt w hw) n (fun i => x i w) (B w)]
      exact ⟨fun h t => h t.1 t.2, fun h t ht => h ⟨t, ht⟩⟩
    · simp [hw]
  rw [hEq]
  exact hG.inter (MeasurableSet.iInter fun t => measurableSet_le
    (measurable_centered_strict_threshold_sum μ R hR f hf x hx t.1).abs hB)

end Papers.TbsExtremeEffects

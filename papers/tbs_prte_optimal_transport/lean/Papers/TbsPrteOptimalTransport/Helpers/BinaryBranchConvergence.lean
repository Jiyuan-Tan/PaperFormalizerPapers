module
public import Papers.TbsPrteOptimalTransport.Helpers.BinaryScoreRemainder
/-! Gap control of the binary score's fitted active-branch indicators in L2. -/
@[expose] public section

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Filter
open scoped Topology

-- @node: binaryBranchSqError
/-- For [population upper, lower, and boundary values](hyp:q,l,b) and
[their fitted counterparts](hyp:qh,lh,bh), the [binary branch squared error](goal)
is the sum of squared changes in the indicators for the upper value exceeding
both other values, the boundary lying strictly between the lower and upper
values, and the lower value exceeding the boundary. -/
noncomputable def binaryBranchSqError (q l b qh lh bh : ℝ) : ℝ :=
  (indicator (qh > max lh bh) - indicator (q > max l b)) ^ 2 +
  (indicator (lh < bh ∧ bh < qh) - indicator (l < b ∧ b < q)) ^ 2 +
  (indicator (lh > bh) - indicator (l > b)) ^ 2

-- @node: score_indicator_sub_sq_le_one
/-- [The squared difference between the zero-one indicators of any two events
is at most one](goal). -/
lemma score_indicator_sub_sq_le_one (P Q : Prop) :
    (indicator P - indicator Q) ^ 2 ≤ 1 := by
  classical
  unfold indicator
  split_ifs <;> norm_num

-- The small-error event has exactly the population branches. On its
-- complement each squared indicator difference is at most one.
-- @node: binary_branch_sq_error_bound
/-- If [the separation constant is positive](hyp:hc), [the upper value exceeds
the lower by at least that constant](hyp:hlq), [the boundary is separated from
the lower](hyp:hbl) and [upper values by that constant](hyp:hbq), and
[the fitted upper](hyp:hq), [lower](hyp:hl), and [boundary values each have
absolute error at most the error envelope](hyp:hb), then [the sum of the three
squared branch-indicator errors is at most twelve times the squared envelope
divided by the squared separation constant](goal). -/
lemma binary_branch_sq_error_bound {q l b qh lh bh err c : ℝ}
    (hc : 0 < c) (hlq : c ≤ q - l) (hbl : c ≤ |b - l|) (hbq : c ≤ |b - q|)
    (hq : |qh - q| ≤ err) (hl : |lh - l| ≤ err) (hb : |bh - b| ≤ err) :
    binaryBranchSqError q l b qh lh bh ≤ (12 / c ^ 2) * err ^ 2 := by
  have he0 : 0 ≤ err := (abs_nonneg _).trans hq
  by_cases he : err < c / 2
  · obtain ⟨hI, hD, hE⟩ := binary_hinge_fitted_branches_stable
      hc hlq hbl hbq hq hl hb he
    simp only [add_sub_cancel] at hI hD hE
    simp only [binaryBranchSqError, hI, hD, hE, sub_self, zero_pow,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_add]
    positivity
  · have hlarge : c / 2 ≤ err := le_of_not_gt he
    have hbound : binaryBranchSqError q l b qh lh bh ≤ 3 := by
      unfold binaryBranchSqError
      have hI := score_indicator_sub_sq_le_one (qh > max lh bh) (q > max l b)
      have hD := score_indicator_sub_sq_le_one (lh < bh ∧ bh < qh) (l < b ∧ b < q)
      have hE := score_indicator_sub_sq_le_one (lh > bh) (l > b)
      linarith
    apply hbound.trans
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (sq_pos_of_pos hc)).mpr
    nlinarith [mul_nonneg (show 0 ≤ 2 * err - c by linarith)
      (show 0 ≤ 2 * err + c by positivity)]

-- @node: measurable_binaryBranchSqError
/-- If [the population upper](hyp:hq), [lower](hyp:hl), and [boundary
functions](hyp:hb), and [the fitted upper](hyp:hqh), [lower](hyp:hlh), and
[boundary functions are measurable](hyp:hbh), then [their binary branch
squared error is measurable](goal). -/
@[fun_prop] lemma measurable_binaryBranchSqError {X : Type*} [MeasurableSpace X]
    (q l b qh lh bh : X → ℝ) (hq : Measurable q) (hl : Measurable l)
    (hb : Measurable b) (hqh : Measurable qh) (hlh : Measurable lh)
    (hbh : Measurable bh) :
    Measurable (fun x => binaryBranchSqError (q x) (l x) (b x) (qh x) (lh x) (bh x)) := by
  have hI : Measurable (fun x => indicator (q x > max (l x) (b x))) := by
    unfold indicator
    exact Measurable.ite (measurableSet_lt (hl.max hb) hq)
      measurable_const measurable_const
  have hIh : Measurable (fun x => indicator (qh x > max (lh x) (bh x))) := by
    unfold indicator
    exact Measurable.ite (measurableSet_lt (hlh.max hbh) hqh)
      measurable_const measurable_const
  have hD : Measurable (fun x => indicator (l x < b x ∧ b x < q x)) := by
    unfold indicator
    exact Measurable.ite ((measurableSet_lt hl hb).inter (measurableSet_lt hb hq))
      measurable_const measurable_const
  have hDh : Measurable (fun x => indicator (lh x < bh x ∧ bh x < qh x)) := by
    unfold indicator
    exact Measurable.ite ((measurableSet_lt hlh hbh).inter (measurableSet_lt hbh hqh))
      measurable_const measurable_const
  have hE : Measurable (fun x => indicator (l x > b x)) := by
    unfold indicator
    exact Measurable.ite (measurableSet_lt hb hl) measurable_const measurable_const
  have hEh : Measurable (fun x => indicator (lh x > bh x)) := by
    unfold indicator
    exact Measurable.ite (measurableSet_lt hbh hlh) measurable_const measurable_const
  unfold binaryBranchSqError
  fun_prop

-- @node: binary_branch_integrated_sq_error_bound
/-- Suppose [the separation constant is positive](hyp:hc), [the population
upper](hyp:hq), [lower](hyp:hl), and [boundary functions](hyp:hb) and [their
fitted upper](hyp:hqh), [lower](hyp:hlh), and [boundary counterparts are
measurable](hyp:hbh), and [the error envelope is square integrable](hyp:herr).
If [the upper and lower values and both boundary distances are separated by
the constant almost everywhere](hyp:hgap) and [all three fitting errors are
bounded by the envelope almost everywhere](hyp:herrors), then [the branch
squared error is integrable and its integral is at most twelve divided by the
squared separation constant times the integral of the squared envelope](goal). -/
lemma binary_branch_integrated_sq_error_bound {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (q l b qh lh bh err : X → ℝ) (c : ℝ)
    (hc : 0 < c) (hq : Measurable q) (hl : Measurable l) (hb : Measurable b)
    (hqh : Measurable qh) (hlh : Measurable lh) (hbh : Measurable bh)
    (herr : MemLp err 2 μ)
    (hgap : ∀ᵐ x ∂μ, c ≤ q x - l x ∧ c ≤ |b x - l x| ∧ c ≤ |b x - q x|)
    (herrors : ∀ᵐ x ∂μ, |qh x - q x| ≤ err x ∧ |lh x - l x| ≤ err x ∧
      |bh x - b x| ≤ err x) :
    let R := fun x => binaryBranchSqError (q x) (l x) (b x) (qh x) (lh x) (bh x)
    Integrable R μ ∧ (∫ x, R x ∂μ) ≤ (12 / c ^ 2) * ∫ x, err x ^ 2 ∂μ := by
  dsimp only
  let R := fun x => binaryBranchSqError (q x) (l x) (b x) (qh x) (lh x) (bh x)
  have hm : Measurable R := by
    dsimp only [R]
    fun_prop
  have hnonneg : ∀ x, 0 ≤ R x := fun x =>
    add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)
  have hbound : ∀ᵐ x ∂μ, R x ≤ (12 / c ^ 2) * err x ^ 2 := by
    filter_upwards [hgap, herrors] with x hg he
    exact binary_branch_sq_error_bound hc hg.1 hg.2.1 hg.2.2 he.1 he.2.1 he.2.2
  have hdom := herr.integrable_sq.const_mul (12 / c ^ 2)
  have hi : Integrable R μ := hdom.mono' hm.aestronglyMeasurable (by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hnonneg _)] using hbound)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ x, (12 / c ^ 2) * err x ^ 2 ∂μ := integral_mono_ae hi hdom hbound
    _ = _ := integral_const_mul _ _

universe v

-- This is the exact collection of nonsmooth coefficients in the binary score.
-- @node: hMinus_branch_sq_error_bound
/-- If [the gap constant is positive](hyp:hc), [the adjacent pooled policy
values differ by at least that constant](hyp:hlq), [the regression-adjusted
boundary is that far from the lower](hyp:hbl) and [upper pooled values](hyp:hbq),
and [the upper pooled value](hyp:hq), [lower pooled value](hyp:hl), and
[adjusted boundary each change by at most the error envelope](hyp:hb), then
[the sum of squared changes in the three binary score branch indicators is
at most twelve times the squared envelope divided by the squared gap](goal). -/
lemma hMinus_branch_sq_error_bound {X Z : Type v}
    (phi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (e0 e1 : NuisanceBin L) (k j : ℕ) (x : X) (err c : ℝ)
    (hc : 0 < c)
    (hlq : c ≤ pooledQBin phi L e0 k j x - pooledQBin phi L e0 k (j - 1) x)
    (hbl : c ≤ |positiveValue e0.pLev (k + 1) x - binFullJ L e0 k x -
      pooledQBin phi L e0 k (j - 1) x|)
    (hbq : c ≤ |positiveValue e0.pLev (k + 1) x - binFullJ L e0 k x -
      pooledQBin phi L e0 k j x|)
    (hq : |pooledQBin phi L e1 k j x - pooledQBin phi L e0 k j x| ≤ err)
    (hl : |pooledQBin phi L e1 k (j - 1) x - pooledQBin phi L e0 k (j - 1) x| ≤ err)
    (hb : |(positiveValue e1.pLev (k + 1) x - binFullJ L e1 k x) -
      (positiveValue e0.pLev (k + 1) x - binFullJ L e0 k x)| ≤ err) :
    (Iact phi L e1 k j x - Iact phi L e0 k j x) ^ 2 +
    (Dbd phi L e1 k j x - Dbd phi L e0 k j x) ^ 2 +
    (Edom phi L e1 k j x - Edom phi L e0 k j x) ^ 2 ≤
      (12 / c ^ 2) * err ^ 2 := by
  exact binary_branch_sq_error_bound hc hlq hbl hbq hq hl hb

-- Convergence of the integrated squared envelope suffices. This conclusion
-- controls all three indicator errors simultaneously, with no pointwise
-- convergence of the fitted nuisances required.
-- @node: binary_branch_integrated_sq_error_tendsto_zero
/-- Suppose [the separation constant is positive](hyp:hc), [the population
upper](hyp:hq), [lower](hyp:hl), and [boundary functions are measurable](hyp:hb),
as are [every fitted upper](hyp:hqh), [lower](hyp:hlh), and [boundary
function](hyp:hbh), and [each error envelope is square integrable](hyp:herr).
If [the three population separations are at least the constant almost
everywhere](hyp:hgap), [each fit's three errors are bounded by its envelope
almost everywhere](hyp:herrors), and [the integrals of the squared envelopes
converge to zero](hyp:hconv), then [the integrated binary branch squared
errors converge to zero](goal). -/
lemma binary_branch_integrated_sq_error_tendsto_zero {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (q l b : X → ℝ) (qh lh bh err : ℕ → X → ℝ) (c : ℝ)
    (hc : 0 < c) (hq : Measurable q) (hl : Measurable l) (hb : Measurable b)
    (hqh : ∀ n, Measurable (qh n)) (hlh : ∀ n, Measurable (lh n))
    (hbh : ∀ n, Measurable (bh n)) (herr : ∀ n, MemLp (err n) 2 μ)
    (hgap : ∀ᵐ x ∂μ, c ≤ q x - l x ∧ c ≤ |b x - l x| ∧ c ≤ |b x - q x|)
    (herrors : ∀ n, ∀ᵐ x ∂μ, |qh n x - q x| ≤ err n x ∧
      |lh n x - l x| ≤ err n x ∧ |bh n x - b x| ≤ err n x)
    (hconv : Tendsto (fun n => ∫ x, err n x ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x,
      binaryBranchSqError (q x) (l x) (b x) (qh n x) (lh n x) (bh n x) ∂μ)
      atTop (𝓝 0) := by
  apply squeeze_zero
  · intro n
    apply integral_nonneg
    intro x
    exact add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)
  · intro n
    exact (binary_branch_integrated_sq_error_bound μ q l b (qh n) (lh n) (bh n)
      (err n) c hc hq hl hb (hqh n) (hlh n) (hbh n) (herr n) hgap (herrors n)).2
  · simpa only [mul_zero] using hconv.const_mul (12 / c ^ 2)

end Papers.TbsPrteOptimalTransport

module
public import Papers.TbsPrteOptimalTransport.Helpers.JointFullRegressionWeights
/-! Weighted quadratic regression cancellation for regular binary intervals. -/
public section
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Set Filter
open scoped Classical Topology
universe v

-- The product-score weight must remain inside the integral. Its boundedness
-- preserves the pointwise quadratic bound even if fitted branches change.
-- @node: binary_weighted_regression_integrated_remainder
/-- Suppose [the weight bound is nonnegative](hyp:hB), [the separation constant is
positive](hyp:hc), [the weight is measurable](hyp:hw) and [bounded in absolute value by
that bound almost everywhere](hyp:hwb). Assume [the upper pooled endpoint](hyp:hq),
[the lower pooled endpoint](hyp:hl), [the baseline regression boundary](hyp:hb), and
[the adjacent regression-direction difference](hyp:hd) are measurable, [the error envelope
is square integrable](hyp:herr), [the endpoints are separated by at least the separation
constant and the boundary is at least that far from each endpoint almost everywhere](hyp:hgap),
and [the direction difference is bounded in absolute value by the envelope almost
everywhere](hyp:herrors). Then [the weighted change in the lower branch minus its fitted
boundary correction is integrable, and its absolute integral is at most the weight bound
times 26 divided by the separation constant, times the envelope's second moment, times
the squared path displacement](goal). -/
lemma binary_weighted_regression_integrated_remainder
    {X Z : Type v} [MeasurableSpace X] (μ : Measure X)
    (phi : Z → X → ℝ → ℝ) (L : LevelData Z X) (e : NuisanceBin L)
    (d : PositiveIndex L.K → X → ℝ) (k j : ℕ) (w err : X → ℝ)
    (B c t : ℝ) (hB : 0 ≤ B) (hc : 0 < c)
    (hw : Measurable w) (hwb : ∀ᵐ x ∂μ, |w x| ≤ B)
    (hq : Measurable (pooledQBin phi L e k j))
    (hl : Measurable (pooledQBin phi L e k (j - 1)))
    (hb : Measurable (fun x => positiveValue e.pLev (k + 1) x - binFullJ L e k x))
    (hd : Measurable (fun x => positiveValue d (k + 1) x - positiveValue d k x))
    (herr : MemLp err 2 μ)
    (hgap : ∀ᵐ x ∂μ,
      c ≤ pooledQBin phi L e k j x - pooledQBin phi L e k (j - 1) x ∧
      c ≤ |positiveValue e.pLev (k + 1) x - binFullJ L e k x -
        pooledQBin phi L e k (j - 1) x| ∧
      c ≤ |positiveValue e.pLev (k + 1) x - binFullJ L e k x - pooledQBin phi L e k j x|)
    (herrors : ∀ᵐ x ∂μ, |positiveValue d (k + 1) x - positiveValue d k x| ≤ err x) :
    let et := {e with P1 := fun a x => e.P1 a x + t * d a x}
    let R := fun x => w x * (hMinus phi L et k j x - hMinus phi L e k j x -
      Dbd phi L et k j x * (t * (positiveValue d (k + 1) x - positiveValue d k x)))
    Integrable R μ ∧ |∫ x, R x ∂μ| ≤
      (B * (26 / c) * ∫ x, err x ^ 2 ∂μ) * t ^ 2 := by
  dsimp only
  let et := {e with P1 := fun a x => e.P1 a x + t * d a x}
  let R := fun x => w x * (hMinus phi L et k j x - hMinus phi L e k j x -
    Dbd phi L et k j x * (t * (positiveValue d (k + 1) x - positiveValue d k x)))
  change Integrable R μ ∧ _
  have hq' : ∀ a, pooledQBin phi L et k a = pooledQBin phi L e k a := fun _ => rfl
  have hb' : (fun x => positiveValue et.pLev (k + 1) x - binFullJ L et k x) =
      (fun x => (positiveValue e.pLev (k + 1) x - binFullJ L e k x) +
        t * (-(positiveValue d (k + 1) x - positiveValue d k x))) := by
    funext x
    exact binary_regression_boundary_path L e d k x t
  have hbt : Measurable (fun x => positiveValue et.pLev (k + 1) x - binFullJ L et k x) := by
    rw [hb']
    fun_prop
  have hD : Measurable (Dbd phi L et k j) := by
    unfold Dbd indicator
    exact Measurable.ite ((measurableSet_lt hl hbt).inter (measurableSet_lt hbt hq))
      measurable_const measurable_const
  have hH : Measurable (hMinus phi L et k j) := by
    unfold hMinus
    change Measurable (fun x => max 0 (pooledQBin phi L et k j x -
      max (pooledQBin phi L et k (j - 1) x)
        (positiveValue et.pLev (k + 1) x - binFullJ L et k x)))
    simp only [hq']
    exact measurable_const.max (hq.sub (hl.max hbt))
  have hH0 : Measurable (hMinus phi L e k j) := by
    unfold hMinus
    exact measurable_const.max (hq.sub (hl.max hb))
  have hR : Measurable R := by
    dsimp only [R]
    exact hw.mul ((hH.sub hH0).sub (hD.mul (hd.const_mul t)))
  have hbound : ∀ᵐ x ∂μ, |R x| ≤ B * (26 / c) * (|t| * err x) ^ 2 := by
    filter_upwards [hgap, herrors, hwb] with x hg he hwx
    have he0 : 0 ≤ err x := (abs_nonneg _).trans he
    have hbt : |(positiveValue et.pLev (k+1) x - binFullJ L et k x) -
        (positiveValue e.pLev (k+1) x - binFullJ L e k x)| ≤ |t| * err x := by
      rw [congrFun hb' x, add_sub_cancel_left, abs_mul, abs_neg]
      exact mul_le_mul_of_nonneg_left he (abs_nonneg t)
    have h := hMinus_fitted_score_remainder phi L e et k j x (|t| * err x) c
      hc hg.1 hg.2.1 hg.2.2
      (by simp only [congrFun (hq' j) x, sub_self, abs_zero]; positivity)
      (by simp only [congrFun (hq' (j-1)) x, sub_self, abs_zero]; positivity) hbt
    have hr : |hMinus phi L et k j x - hMinus phi L e k j x -
        Dbd phi L et k j x * (t * (positiveValue d (k+1) x - positiveValue d k x))| ≤
        (26 / c) * (|t| * err x) ^ 2 := by
      simp only [congrFun (hq' j) x, congrFun (hq' (j-1)) x,
        congrFun hb' x, add_sub_cancel_left, sub_self, mul_zero, sub_zero,
        mul_neg, zero_sub, neg_neg] at h
      exact h
    dsimp only [R]
    rw [abs_mul]
    calc
      _ ≤ B * ((26 / c) * (|t| * err x) ^ 2) :=
        mul_le_mul hwx hr (abs_nonneg _) hB
      _ = _ := by ring
  have hdom : Integrable (fun x => B * (26 / c) * (|t| * err x) ^ 2) μ :=
    (herr.const_mul |t|).integrable_sq.const_mul _
  have hi : Integrable R μ := hdom.mono' hR.aestronglyMeasurable (by
    simpa only [Real.norm_eq_abs] using hbound)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ x, |R x| ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm R
    _ ≤ ∫ x, B * (26 / c) * (|t| * err x) ^ 2 ∂μ := integral_mono_ae hi.abs hdom hbound
    _ = _ := by
      simp only [mul_pow, integral_const_mul, sq_abs]
      ring

-- @node: binary_weighted_regression_integrated_orthogonality
/-- Suppose [the weight bound is nonnegative](hyp:hB), [the separation constant is
positive](hyp:hc), [the weight is measurable](hyp:hw) and [almost everywhere bounded in
absolute value by that bound](hyp:hwb). If [the upper pooled endpoint](hyp:hq), [the lower
pooled endpoint](hyp:hl), [the baseline regression boundary](hyp:hb), and [the adjacent
regression-direction difference](hyp:hd) are measurable, [the error envelope is square
integrable](hyp:herr), [the endpoints are separated and the boundary stays away from each
endpoint by at least the separation constant almost everywhere](hyp:hgap), and [the
direction difference is dominated in absolute value by the envelope almost
everywhere](hyp:herrors), then [the integral of the weighted lower-branch change minus its
fitted boundary correction has derivative zero at zero path displacement](goal). -/
lemma binary_weighted_regression_integrated_orthogonality
    {X Z : Type v} [MeasurableSpace X] (μ : Measure X)
    (phi : Z → X → ℝ → ℝ) (L : LevelData Z X) (e : NuisanceBin L)
    (d : PositiveIndex L.K → X → ℝ) (k j : ℕ) (w err : X → ℝ)
    (B c : ℝ) (hB : 0 ≤ B) (hc : 0 < c)
    (hw : Measurable w) (hwb : ∀ᵐ x ∂μ, |w x| ≤ B)
    (hq : Measurable (pooledQBin phi L e k j))
    (hl : Measurable (pooledQBin phi L e k (j - 1)))
    (hb : Measurable (fun x => positiveValue e.pLev (k + 1) x - binFullJ L e k x))
    (hd : Measurable (fun x => positiveValue d (k + 1) x - positiveValue d k x))
    (herr : MemLp err 2 μ)
    (hgap : ∀ᵐ x ∂μ,
      c ≤ pooledQBin phi L e k j x - pooledQBin phi L e k (j - 1) x ∧
      c ≤ |positiveValue e.pLev (k + 1) x - binFullJ L e k x -
        pooledQBin phi L e k (j - 1) x| ∧
      c ≤ |positiveValue e.pLev (k + 1) x - binFullJ L e k x - pooledQBin phi L e k j x|)
    (herrors : ∀ᵐ x ∂μ, |positiveValue d (k + 1) x - positiveValue d k x| ≤ err x) :
    HasDerivAt (fun t : ℝ => ∫ x,
      let et := {e with P1 := fun a x => e.P1 a x + t * d a x}
      w x * (hMinus phi L et k j x - hMinus phi L e k j x -
        Dbd phi L et k j x * (t * (positiveValue d (k + 1) x - positiveValue d k x)))
      ∂μ) 0 0 := by
  let F := fun t : ℝ => ∫ x,
    let et := {e with P1 := fun a x => e.P1 a x + t * d a x}
    w x * (hMinus phi L et k j x - hMinus phi L e k j x -
      Dbd phi L et k j x * (t * (positiveValue d (k + 1) x - positiveValue d k x))) ∂μ
  change HasDerivAt F 0 0
  have hbound : ∀ t, |F t| ≤ (B * (26 / c) * ∫ x, err x ^ 2 ∂μ) * t ^ 2 :=
    fun t => (binary_weighted_regression_integrated_remainder μ phi L e d k j w err
      B c t hB hc hw hwb hq hl hb hd herr hgap herrors).2
  have hz : F 0 = 0 := by
    exact abs_nonpos_iff.mp (by simpa using hbound 0)
  have ho : F =O[nhds 0] (fun t : ℝ => t ^ 2) := by
    apply Asymptotics.IsBigO.of_bound (B * (26 / c) * ∫ x, err x ^ 2 ∂μ)
    exact Filter.Eventually.of_forall fun t => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)] using hbound t
  apply HasDerivAt.of_isLittleO
  simpa only [hz, sub_zero, smul_zero] using
    ho.trans_isLittleO (Asymptotics.isLittleO_pow_id (𝕜 := ℝ) (by norm_num : 1 < 2))

universe u
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- Only the band's separation is an input. Population measurability, the
-- product-weight bound, and a square-integrable envelope are all derived.
-- @node: population_binary_weighted_regression_remainder_of_admissible
/-- Under [the threshold-crossing model](hyp:h), [a valid policy map](hyp:hphi), and
[measurable baseline levels](hyp:hlev), consider [a binary nuisance direction](hyp:del)
that [is admissible at the true nuisance](hyp:hd). If [the separation constant is
positive](hyp:hc) and [the two pooled endpoints are separated by at least that constant
and the baseline boundary is at least that far from each endpoint almost
everywhere](hyp:hgap), [the population integral of the lower-branch change minus its
fitted boundary correction, weighted by the instrument-set probability, has derivative
zero at zero along the regression path](goal). -/
lemma population_binary_weighted_regression_remainder_of_admissible
    (h : ThresholdCrossing M) (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (L : LevelData Z X) (hlev : ∀ i, Measurable (L.pLev i))
    (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del))
    (k j : ℕ) (c : ℝ) (hc : 0 < c)
    (hgap : ∀ᵐ x ∂xLaw M,
      c ≤ pooledQBin phi L (eta0Bin M L) k j x - pooledQBin phi L (eta0Bin M L) k (j-1) x ∧
      c ≤ |positiveValue (eta0Bin M L).pLev (k+1) x - binFullJ L (eta0Bin M L) k x -
        pooledQBin phi L (eta0Bin M L) k (j-1) x| ∧
      c ≤ |positiveValue (eta0Bin M L).pLev (k+1) x - binFullJ L (eta0Bin M L) k x -
        pooledQBin phi L (eta0Bin M L) k j x|) :
    HasDerivAt (fun t : ℝ => ∫ x,
      let et := {eta0Bin M L with P1 := fun a x => (eta0Bin M L).P1 a x + t * del.P1 a x}
      gamma M L k j x * (hMinus phi L et k j x - hMinus phi L (eta0Bin M L) k j x -
        Dbd phi L et k j x * (t * (positiveValue del.P1 (k+1) x - positiveValue del.P1 k x)))
      ∂xLaw M) 0 0 := by
  haveI : IsProbabilityMeasure (xLaw M) := Measure.isProbabilityMeasure_map M.measX.aemeasurable
  obtain ⟨C, hC, hr⟩ := binary_regression_direction_regular M L (eta0Bin M L) del hd
  have hpos i := binary_positive_regression_direction_regular M L del.P1 C hC hr i
  have hdm : Measurable (fun x => positiveValue del.P1 (k+1) x - positiveValue del.P1 k x) :=
    (hpos (k+1)).1.sub (hpos k).1
  have hdb : ∀ᵐ x ∂xLaw M, |positiveValue del.P1 (k+1) x - positiveValue del.P1 k x| ≤ 2*C := by
    filter_upwards [(hpos (k+1)).2, (hpos k).2] with x hp hm
    have hn := norm_sub_le (positiveValue del.P1 (k+1) x) (positiveValue del.P1 k x)
    rw [Real.norm_eq_abs] at hn
    linarith
  have hp : Measurable (positiveValue (eta0Bin M L).pLev (k+1)) := by
    unfold positiveValue
    split_ifs
    · exact hlev (k+1)
    · fun_prop
  have hb : Measurable (fun x => positiveValue (eta0Bin M L).pLev (k+1) x -
      binFullJ L (eta0Bin M L) k x) := by fun_prop
  have hw : Measurable (gamma M L k j) :=
    population_instrument_set_probability_measurable M (policyUnion L k j)
  have hwb : ∀ᵐ x ∂xLaw M, |gamma M L k j x| ≤ 1 := by
    apply Filter.Eventually.of_forall
    intro x
    have hx := population_instrument_set_probability_range M (policyUnion L k j) x
    simpa only [gamma, abs_of_nonneg hx.1] using hx.2
  exact binary_weighted_regression_integrated_orthogonality (xLaw M) phi L (eta0Bin M L)
    del.P1 k j (gamma M L k j) (fun _ => 2*C) 1 c zero_le_one hc hw hwb
    (population_pooledQBin_measurable M h phi hphi L hlev k j)
    (population_pooledQBin_measurable M h phi hphi L hlev k (j-1)) hb hdm
    (memLp_const (2*C)) hgap hdb

-- This connects the integrated branch remainder to the actual product score:
-- the remaining terms are fitted covariate coefficients times primitive
-- population residuals, and normalized assignment corrections.
-- @node: binary_regular_product_regression_path_decomposition
/-- [Along a binary treated-outcome-regression path, the regular product score equals the fitted
lower branch times the policy-union indicator plus the baseline instrument weight times
the sum of the fitted-boundary-weighted adjacent treated-outcome residual difference, the negative
upper treatment-residual correction, the negative first-band lower treatment-residual
correction, the upper and negative lower pooled-residual corrections, and the negative
path-displacement correction formed from normalized adjacent assignment indicators and
regression directions](goal). -/
lemma binary_regular_product_regression_path_decomposition
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X) (e : NuisanceBin L)
    (d : PositiveIndex L.K → X → ℝ) (k j : ℕ) (o : Obs X Z) (t : ℝ) :
    let et := {e with P1 := fun a x => e.P1 a x + t * d a x}
    psiProdBin phi dphi L et k j o =
      hMinus phi L et k j o.1 * indicator (o.2.1 ∈ policyUnion L k j) +
      regularValue e.gamma k j o.1 *
        (Dbd phi L et k j o.1 * (RP L e (k+1) o - RP L e k o) -
        Dbd phi L et k j o.1 * Rp L e (k+1) o -
        (if j = 1 then Edom phi L et k j o.1 * Iact phi L et k j o.1 * Rp L e k o else 0) +
        Iact phi L et k j o.1 * RqBin dphi L e k j o -
        Edom phi L et k j o.1 * Iact phi L et k j o.1 * RqBin dphi L e k (j-1) o -
        Dbd phi L et k j o.1 * t *
          (indicator (o.2.1 ∈ L.S (k+1)) / positiveValue e.piLev (k+1) o.1 *
            positiveValue d (k+1) o.1 -
          indicator (o.2.1 ∈ L.S k) / positiveValue e.piLev k o.1 * positiveValue d k o.1)) := by
  dsimp only
  simp only [psiProdBin]
  rw [binary_regression_score_path_decomposition]
  ring

end Papers.TbsPrteOptimalTransport

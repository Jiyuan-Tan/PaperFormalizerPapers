module
public import Papers.TbsPrteOptimalTransport.Helpers.WeightedBinaryRegression
/-! Regression-only branch remainders need endpoint margins, including the fixed zero. -/
public section
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Set Filter
open scoped Classical Topology

-- @node: binary_hinge_regression_endpoint_remainder
/-- If [the margin c is positive](hyp:hc), [the boundary b is at least c away from
the lower endpoint l](hyp:hbl), and [b is at least c away from the upper endpoint q](hyp:hbq),
then [the absolute change in the positive part of q minus the larger of l and b,
after perturbing b by db and adding db when the perturbed boundary lies strictly
between l and q, is at most twice the squared perturbation divided by c](goal). -/
lemma binary_hinge_regression_endpoint_remainder {q l b db c : ℝ}
    (hc : 0 < c) (hbl : c ≤ |b - l|) (hbq : c ≤ |b - q|) :
    |max 0 (q - max l (b + db)) - max 0 (q - max l b) +
      indicator (l < b + db ∧ b + db < q) * db| ≤ (2 / c) * db ^ 2 := by
  by_cases he : |db| < c
  · have hd := abs_le.mp (le_of_lt he)
    have hz : max 0 (q - max l (b + db)) - max 0 (q - max l b) +
        indicator (l < b + db ∧ b + db < q) * db = 0 := by
      by_cases h : l < b
      · have hs : c ≤ b - l := by rw [abs_of_nonneg (by linarith)] at hbl; exact hbl
        have ht : l < b + db := by linarith [neg_abs_le db]
        rw [max_eq_right h.le, max_eq_right ht.le]
        by_cases hq : b < q
        · have hsq : c ≤ q - b := by
            rw [abs_of_nonpos (by linarith)] at hbq
            linarith
          have hqt : b + db < q := by linarith [le_abs_self db]
          rw [max_eq_right (by linarith : 0 ≤ q-(b + db)),
            max_eq_right (by linarith : 0 ≤ q - b)]
          simp only [indicator, ht, hqt, and_self, if_true, one_mul]
          ring
        · have hsq : c ≤ b - q := by
            rw [abs_of_nonneg (by linarith)] at hbq; exact hbq
          have hqt : q < b + db := by linarith [neg_abs_le db]
          rw [max_eq_left (by linarith : q-(b + db) ≤ 0),
            max_eq_left (by linarith : q - b ≤ 0)]
          simp [indicator, not_lt_of_ge hqt.le]
      · have hs : c ≤ l - b := by
          rw [abs_of_nonpos (by linarith)] at hbl
          linarith
        have ht : b + db < l := by linarith [le_abs_self db]
        rw [max_eq_left (by linarith : b ≤ l), max_eq_left ht.le]
        simp [indicator, not_lt_of_ge ht.le]
    rw [hz, abs_zero]
    positivity
  · have hh : |max 0 (q - max l (b + db)) - max 0 (q - max l b)| ≤ |db| := by
      have hm := abs_max_sub_max_le_max l (b + db) l b
      simp only [sub_self, add_sub_cancel_left, abs_zero, max_eq_right (abs_nonneg db)] at hm
      have ho := abs_max_sub_max_le_max 0 (q - max l (b + db)) 0 (q - max l b)
      have hid : (q - max l (b + db)) - (q - max l b) = -(max l (b + db)-max l b) := by ring
      rw [hid, abs_neg] at ho
      exact ho.trans (max_le (by simp) hm)
    have hi : |indicator (l < b + db ∧ b + db < q) * db| ≤ |db| := by
      unfold indicator
      split_ifs <;> simp
    calc
      _ ≤ |max 0 (q - max l (b + db)) - max 0 (q - max l b)| +
          |indicator (l < b + db ∧ b + db < q) * db| := abs_add_le _ _
      _ ≤ 2 * |db| := by linarith
      _ ≤ (2 / c) * db ^ 2 := by
        have he' : c ≤ |db| := le_of_not_gt he
        rw [div_mul_eq_mul_div]
        apply (le_div_iff₀ hc).mpr
        have hmul := mul_le_mul_of_nonneg_right he' (abs_nonneg db)
        nlinarith [sq_abs db]

-- The product-score weight must remain inside the integral. Its boundedness
-- preserves the pointwise quadratic bound even if fitted branches change.
-- @node: binary_weighted_regression_endpoint_integrated_remainder
/-- Suppose [the weight bound B is nonnegative](hyp:hB), [the endpoint margin c is
positive](hyp:hc), [the weight is measurable](hyp:hw) and [bounded in absolute value
by B almost everywhere](hyp:hwb), [the upper pooled endpoint is measurable](hyp:hq),
[the lower pooled endpoint is measurable](hyp:hl), [the regression boundary is
measurable](hyp:hb), [the adjacent-level regression direction difference is measurable](hyp:hd),
[the error envelope is square integrable](hyp:herr), [the regression boundary is
at least c away from both pooled endpoints almost everywhere](hyp:hgap), and
[the absolute direction difference is bounded by the envelope almost everywhere](hyp:herrors).
Then [perturbing the treated regression by t times the direction gives an integrable
weighted hinge remainder after subtracting the perturbed-branch linear correction;
the absolute integral of this remainder is at most B times twice the envelope's
integrated square divided by c, multiplied by t squared](goal). -/
lemma binary_weighted_regression_endpoint_integrated_remainder
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
      c ≤ |positiveValue e.pLev (k + 1) x - binFullJ L e k x -
        pooledQBin phi L e k (j - 1) x| ∧
      c ≤ |positiveValue e.pLev (k + 1) x - binFullJ L e k x - pooledQBin phi L e k j x|)
    (herrors : ∀ᵐ x ∂μ, |positiveValue d (k + 1) x - positiveValue d k x| ≤ err x) :
    let et := {e with P1 := fun a x => e.P1 a x + t * d a x}
    let R := fun x => w x * (hMinus phi L et k j x - hMinus phi L e k j x -
      Dbd phi L et k j x * (t * (positiveValue d (k + 1) x - positiveValue d k x)))
    Integrable R μ ∧ |∫ x, R x ∂μ| ≤
      (B * (2 / c) * ∫ x, err x ^ 2 ∂μ) * t ^ 2 := by
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
  have hbound : ∀ᵐ x ∂μ, |R x| ≤ B * (2 / c) * (|t| * err x) ^ 2 := by
    filter_upwards [hgap, herrors, hwb] with x hg he hwx
    have he0 : 0 ≤ err x := (abs_nonneg _).trans he
    have h := binary_hinge_regression_endpoint_remainder hc hg.1 hg.2
      (q := pooledQBin phi L e k j x) (l := pooledQBin phi L e k (j - 1) x)
      (b := positiveValue e.pLev (k + 1) x - binFullJ L e k x)
      (db := t * (-(positiveValue d (k + 1) x - positiveValue d k x)))
    have hr : |hMinus phi L et k j x - hMinus phi L e k j x -
        Dbd phi L et k j x * (t * (positiveValue d (k + 1) x - positiveValue d k x))| ≤
        (2 / c) * (|t| * err x) ^ 2 := by
      have hid : hMinus phi L et k j x - hMinus phi L e k j x -
          Dbd phi L et k j x * (t * (positiveValue d (k + 1) x - positiveValue d k x)) =
          max 0 (pooledQBin phi L e k j x - max (pooledQBin phi L e k (j - 1) x)
            ((positiveValue e.pLev (k + 1) x - binFullJ L e k x) +
              t * (-(positiveValue d (k + 1) x - positiveValue d k x)))) -
          max 0 (pooledQBin phi L e k j x - max (pooledQBin phi L e k (j - 1) x)
            (positiveValue e.pLev (k + 1) x - binFullJ L e k x)) +
          indicator (pooledQBin phi L e k (j - 1) x <
              (positiveValue e.pLev (k + 1) x - binFullJ L e k x) +
                t * (-(positiveValue d (k + 1) x - positiveValue d k x)) ∧
            (positiveValue e.pLev (k + 1) x - binFullJ L e k x) +
              t * (-(positiveValue d (k + 1) x - positiveValue d k x)) < pooledQBin phi L e k j x) *
              (t * (-(positiveValue d (k + 1) x - positiveValue d k x))) := by
        simp only [hMinus, Dbd, congrFun (hq' j) x, congrFun (hq' (j - 1)) x,
          congrFun hb' x]
        ring
      rw [hid]
      apply h.trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hbd : |t * (-(positiveValue d (k + 1) x - positiveValue d k x))| ≤ |t| * err x := by
        rw [abs_mul, abs_neg]
        exact mul_le_mul_of_nonneg_left he (abs_nonneg t)
      nlinarith [sq_abs (t * (-(positiveValue d (k + 1) x - positiveValue d k x))),
        mul_nonneg (sub_nonneg.mpr hbd) (add_nonneg (abs_nonneg (t * (-(positiveValue d (k + 1) x - positiveValue d k x)))) (by positivity : 0 ≤ |t| * err x))]
    dsimp only [R]
    rw [abs_mul]
    calc
      _ ≤ B * ((2 / c) * (|t| * err x) ^ 2) :=
        mul_le_mul hwx hr (abs_nonneg _) hB
      _ = _ := by ring
  have hdom : Integrable (fun x => B * (2 / c) * (|t| * err x) ^ 2) μ :=
    (herr.const_mul |t|).integrable_sq.const_mul _
  have hi : Integrable R μ := hdom.mono' hR.aestronglyMeasurable (by
    simpa only [Real.norm_eq_abs] using hbound)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ x, |R x| ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm R
    _ ≤ ∫ x, B * (2 / c) * (|t| * err x) ^ 2 ∂μ := integral_mono_ae hi.abs hdom hbound
    _ = _ := by
      simp only [mul_pow, integral_const_mul, sq_abs]
      ring

-- @node: binary_weighted_regression_endpoint_integrated_orthogonality
/-- Suppose [the weight bound B is nonnegative](hyp:hB), [the endpoint margin c is
positive](hyp:hc), [the weight is measurable](hyp:hw) and [bounded in absolute value
by B almost everywhere](hyp:hwb), [the upper pooled endpoint is measurable](hyp:hq),
[the lower pooled endpoint is measurable](hyp:hl), [the regression boundary is
measurable](hyp:hb), [the adjacent-level regression direction difference is measurable](hyp:hd),
[the error envelope is square integrable](hyp:herr), [the regression boundary is
at least c away from both pooled endpoints almost everywhere](hyp:hgap), and
[the absolute direction difference is bounded by the envelope almost everywhere](hyp:herrors).
Then [the integrated weighted hinge remainder, obtained by perturbing the treated
regression along the direction and subtracting the perturbed-branch linear
correction, has derivative zero at perturbation size zero](goal). -/
lemma binary_weighted_regression_endpoint_integrated_orthogonality
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
  have hbound : ∀ t, |F t| ≤ (B * (2 / c) * ∫ x, err x ^ 2 ∂μ) * t ^ 2 :=
    fun t => (binary_weighted_regression_endpoint_integrated_remainder μ phi L e d k j w err
      B c t hB hc hw hwb hq hl hb hd herr hgap herrors).2
  have hz : F 0 = 0 := by
    exact abs_nonpos_iff.mp (by simpa using hbound 0)
  have ho : F =O[nhds 0] (fun t : ℝ => t ^ 2) := by
    apply Asymptotics.IsBigO.of_bound (B * (2 / c) * ∫ x, err x ^ 2 ∂μ)
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
-- @node: population_binary_weighted_regression_endpoint_remainder_of_admissible
/-- Under [the threshold-crossing model](hyp:h), with [a valid policy map](hyp:hphi),
[measurable propensity levels](hyp:hlev), [an admissible binary nuisance direction
at the population nuisance](hyp:hd), [a positive margin c](hyp:hc), and
[the population regression boundary separated by at least c from both pooled
endpoints almost everywhere](hyp:hgap), [the population hinge remainder weighted
by the policy instrument-set probability has derivative zero at perturbation size
zero when the treated regression is perturbed along that direction and the
perturbed-branch linear correction is subtracted](goal). -/
lemma population_binary_weighted_regression_endpoint_remainder_of_admissible
    (h : ThresholdCrossing M) (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (L : LevelData Z X) (hlev : ∀ i, Measurable (L.pLev i))
    (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del))
    (k j : ℕ) (c : ℝ) (hc : 0 < c)
    (hgap : ∀ᵐ x ∂xLaw M,
      c ≤ |positiveValue (eta0Bin M L).pLev (k + 1) x - binFullJ L (eta0Bin M L) k x -
        pooledQBin phi L (eta0Bin M L) k (j - 1) x| ∧
      c ≤ |positiveValue (eta0Bin M L).pLev (k + 1) x - binFullJ L (eta0Bin M L) k x -
        pooledQBin phi L (eta0Bin M L) k j x|) :
    HasDerivAt (fun t : ℝ => ∫ x,
      let et := {eta0Bin M L with P1 := fun a x => (eta0Bin M L).P1 a x + t * del.P1 a x}
      gamma M L k j x * (hMinus phi L et k j x - hMinus phi L (eta0Bin M L) k j x -
        Dbd phi L et k j x * (t * (positiveValue del.P1 (k + 1) x - positiveValue del.P1 k x)))
      ∂xLaw M) 0 0 := by
  haveI : IsProbabilityMeasure (xLaw M) := Measure.isProbabilityMeasure_map M.measX.aemeasurable
  obtain ⟨C, hC, hr⟩ := binary_regression_direction_regular M L (eta0Bin M L) del hd
  have hpos i := binary_positive_regression_direction_regular M L del.P1 C hC hr i
  have hdm : Measurable (fun x => positiveValue del.P1 (k + 1) x - positiveValue del.P1 k x) :=
    (hpos (k + 1)).1.sub (hpos k).1
  have hdb : ∀ᵐ x ∂xLaw M, |positiveValue del.P1 (k + 1) x - positiveValue del.P1 k x| ≤ 2*C := by
    filter_upwards [(hpos (k + 1)).2, (hpos k).2] with x hp hm
    have hn := norm_sub_le (positiveValue del.P1 (k + 1) x) (positiveValue del.P1 k x)
    rw [Real.norm_eq_abs] at hn
    linarith
  have hp : Measurable (positiveValue (eta0Bin M L).pLev (k + 1)) := by
    unfold positiveValue
    split_ifs
    · exact hlev (k + 1)
    · fun_prop
  have hb : Measurable (fun x => positiveValue (eta0Bin M L).pLev (k + 1) x -
      binFullJ L (eta0Bin M L) k x) := by fun_prop
  have hw : Measurable (gamma M L k j) :=
    population_instrument_set_probability_measurable M (policyUnion L k j)
  have hwb : ∀ᵐ x ∂xLaw M, |gamma M L k j x| ≤ 1 := by
    apply Filter.Eventually.of_forall
    intro x
    have hx := population_instrument_set_probability_range M (policyUnion L k j) x
    simpa only [gamma, abs_of_nonneg hx.1] using hx.2
  exact binary_weighted_regression_endpoint_integrated_orthogonality (xLaw M) phi L (eta0Bin M L)
    del.P1 k j (gamma M L k j) (fun _ => 2*C) 1 c zero_le_one hc hw hwb
    (population_pooledQBin_measurable M h phi hphi L hlev k j)
    (population_pooledQBin_measurable M h phi hphi L hlev k (j - 1)) hb hdm
    (memLp_const (2*C)) hgap hdb


end Papers.TbsPrteOptimalTransport

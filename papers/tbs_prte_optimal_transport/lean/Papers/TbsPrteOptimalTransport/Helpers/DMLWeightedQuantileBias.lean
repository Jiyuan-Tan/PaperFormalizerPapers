module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousEncodedQuantile
/-! Weighted quantile-boundary bias in the continuous oracle score.
Bounded fitted coefficients preserve the local quadratic remainder bound and
the clipping bound for remote errors, without requiring a rate for the coefficient. -/
public section
set_option linter.style.haveILetI false
set_option linter.style.openClassical false
set_option linter.unusedFintypeInType false
set_option linter.unusedTactic false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]

-- @node: treatedLaw_weighted_quantile_boundary_integrated_quadratic
/-- Suppose [the reference threshold](hyp:ha), [fitted threshold](hyp:hb), and
[weight](hyp:hw) are measurable, [the reference threshold](hyp:haRange) and
[fitted threshold](hyp:hbRange) lie within the outcome bounds almost everywhere,
and [the weight has absolute value at most D almost everywhere](hyp:hwBound).
If [r is positive](hyp:hr), [C is nonnegative](hyp:hC), [D is
nonnegative](hyp:hD), and [conditional treated interval masses within radius r
of the reference threshold are at most C times interval length](hyp:hdensity),
then [the weighted conditional integral of the fitted threshold minus the outcome
over the left-open, right-closed interval between the thresholds is integrable,
and its population integral has absolute value at most D times the sum of C and
the outcome range divided by r squared, times the squared L2 threshold
error](goal). -/
lemma treatedLaw_weighted_quantile_boundary_integrated_quadratic
    (M : LatentIVModel Ω X Z) (L : LevelData Z X) (k : ℕ)
    (a b w : X → ℝ) (r C D : ℝ)
    (ha : Measurable a) (hb : Measurable b) (hw : Measurable w)
    (haRange : ∀ᵐ x ∂xLaw M, a x ∈ Icc M.yMin M.yMax)
    (hbRange : ∀ᵐ x ∂xLaw M, b x ∈ Icc M.yMin M.yMax)
    (hwBound : ∀ᵐ x ∂xLaw M, |w x| ≤ D)
    (hr : 0 < r) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hdensity : ∀ᵐ x ∂xLaw M, ∀ u v, a x - r ≤ u → u ≤ v → v ≤ a x + r →
      (treatedLaw M L k x (Ioc u v)).toReal ≤ C * (v - u)) :
    Integrable (fun x => w x * ∫ y in Ioc (min (a x) (b x)) (max (a x) (b x)),
      b x - y ∂treatedLaw M L k x) (xLaw M) ∧
    |∫ x, w x * ∫ y in Ioc (min (a x) (b x)) (max (a x) (b x)),
      b x - y ∂treatedLaw M L k x ∂xLaw M| ≤
      D * (C + (M.yMax - M.yMin) / r ^ 2) * finiteL2Error M b a ^ 2 := by
  haveI : IsProbabilityMeasure (xLaw M) :=
    Measure.isProbabilityMeasure_map M.measX.aemeasurable
  have hwidth : 0 ≤ M.yMax - M.yMin := by
    obtain ⟨x, hx⟩ := haRange.exists
    exact sub_nonneg.mpr (hx.1.trans hx.2)
  have hea : MemLp a 2 (xLaw M) := by
    apply memLp_of_bounded haRange
    fun_prop
  have heb : MemLp b 2 (xLaw M) := by
    apply memLp_of_bounded hbRange
    fun_prop
  have hR : Measurable (fun x => w x *
      ∫ y in Ioc (min (a x) (b x)) (max (a x) (b x)),
        b x - y ∂treatedLaw M L k x) := by fun_prop
  have h := quantile_remainder_integrated_quadratic (xLaw M) _ (fun x => b x - a x)
    r (D * C) (D * (M.yMax - M.yMin)) hr (mul_nonneg hD hC)
    (mul_nonneg hD hwidth) hR.aestronglyMeasurable (heb.sub hea) ?_ ?_
  · refine ⟨h.1, ?_⟩
    have heq : D * C + D * (M.yMax - M.yMin) / r ^ 2 =
        D * (C + (M.yMax - M.yMin) / r ^ 2) := by ring
    simpa only [heq, finiteL2Error,
      Real.sq_sqrt (integral_nonneg fun x => sq_nonneg (b x - a x))] using h.2
  · filter_upwards [hwBound, hdensity] with x hwx hx
    intro he
    let := treatedLaw_isFiniteMeasure M L k x
    have hbnd := quantile_boundary_integral_local (treatedLaw M L k x)
      (a x) (b x) r C he hx
    rw [abs_mul]
    calc
      _ ≤ D * (C * |b x - a x| ^ 2) :=
        mul_le_mul hwx hbnd (abs_nonneg _) hD
      _ = _ := by rw [sq_abs]; ring
  · filter_upwards [hwBound, haRange, hbRange] with x hwx hx hy
    let := treatedLaw_isFiniteMeasure M L k x
    rw [abs_mul]
    exact mul_le_mul hwx
      (quantile_boundary_integral_clipped_bound (treatedLaw M L k x)
        (a x) (b x) M.yMin M.yMax hx hy (treatedLaw_mass_le_one M L k x))
      (abs_nonneg _) hD

-- @node: nuisanceRates_weighted_quantile_boundary_bias_root_n_negligible
/-- Suppose [the reference threshold at coordinate c is measurable](hyp:htruth),
[every fitted threshold at c is measurable](hyp:hfit), [every fitted weight is
measurable](hyp:hw), [the reference threshold](hyp:htruthRange) and [all fitted
thresholds](hyp:hfitRange) lie within the outcome bounds almost everywhere, and
[all weights have absolute value at most D almost everywhere](hyp:hwBound).
If [r is positive](hyp:hr), [C is nonnegative](hyp:hC), [D is
nonnegative](hyp:hD), [conditional treated interval masses near the reference
threshold are at most C times length within radius r](hyp:hdensity), and [the
threshold estimators satisfy the finite nuisance rate conditions](hyp:hrates),
then [the weighted population swept-interval integral of the fitted threshold
minus the outcome, using fits and weights at sample size twice n plus two and
multiplied by the square root of n plus one, converges to zero in
probability](goal). -/
lemma nuisanceRates_weighted_quantile_boundary_bias_root_n_negligible {B : Type*}
    (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X) (k : ℕ)
    (truth : B → X → ℝ) (fit : ℕ → A → B → X → ℝ)
    (w : ℕ → A → X → ℝ) (c : B) (r C D : ℝ)
    (htruth : Measurable (truth c)) (hfit : ∀ n a, Measurable (fit n a c))
    (hw : ∀ n a, Measurable (w n a))
    (htruthRange : ∀ᵐ x ∂xLaw M, truth c x ∈ Icc M.yMin M.yMax)
    (hfitRange : ∀ n a, ∀ᵐ x ∂xLaw M, fit n a c x ∈ Icc M.yMin M.yMax)
    (hwBound : ∀ n a, ∀ᵐ x ∂xLaw M, |w n a x| ≤ D)
    (hr : 0 < r) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hdensity : ∀ᵐ x ∂xLaw M, ∀ u v, truth c x - r ≤ u → u ≤ v →
      v ≤ truth c x + r → (treatedLaw M L k x (Ioc u v)).toReal ≤ C * (v - u))
    (hrates : FiniteNuisanceRates M μ fit truth) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (∫ x, w (2 * (n + 1)) a x * ∫ y in
          Ioc (min (truth c x) (fit (2 * (n + 1)) a c x))
            (max (truth c x) (fit (2 * (n + 1)) a c x)),
          fit (2 * (n + 1)) a c x - y ∂treatedLaw M L k x ∂xLaw M))
      atTop (fun _ _ => 0) := by
  apply dml_root_n_bias_tendsto_probability
  let E := max 1 (D * (C + (M.yMax - M.yMin) / r ^ 2))
  have hE : 0 < E := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hs := dml_quarter_rate_product μ
    (fun n a => finiteL2Error M (fit (2 * (n + 1)) a c) (truth c))
    (fun n a => finiteL2Error M (fit (2 * (n + 1)) a c) (truth c))
    (hrates c) (hrates c)
  apply Causalean.Stat.IsLittleOp.of_abs_le_const_mul hE hs
  intro n a
  have hb := (treatedLaw_weighted_quantile_boundary_integrated_quadratic M L k
    (truth c) (fit (2 * (n + 1)) a c) (w (2 * (n + 1)) a) r C D
    htruth (hfit _ a) (hw _ a) htruthRange (hfitRange _ a) (hwBound _ a)
    hr hC hD hdensity).2
  calc
    _ ≤ D * (C + (M.yMax - M.yMin) / r ^ 2) *
        finiteL2Error M (fit (2 * (n + 1)) a c) (truth c) ^ 2 := hb
    _ ≤ E * finiteL2Error M (fit (2 * (n + 1)) a c) (truth c) ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)
    _ = _ := by rw [← sq, abs_of_nonneg (sq_nonneg _)]

-- The score's fitted product coefficient is bounded by one directly from
-- clipping. No consistency or convergence rate for this coefficient is needed.
-- @node: encoded_continuous_weighted_quantile_bias_root_n_negligible
/-- Suppose [the true continuous nuisance specification is admissible](hyp:he0),
[every fitted specification satisfies continuous clipping](hyp:hclip), [its
fitted shares lie in the simplex](hyp:hshares), [all encoded fitted components
are measurable](hyp:hm), [the boundary density bounds hold](hyp:hd), and [the
encoded components satisfy the finite nuisance rate conditions](hyp:hrates).
If [the treated level is one above the boundary's level, or is that same level
when it is positive](hyp:hk'), then [the population swept-interval quantile
remainder weighted by the fitted gamma weight at g times the fitted treatment
probability at that level, using fits at sample size twice n plus two and
multiplied by the square root of n plus one, converges to zero in
probability](goal). -/
lemma encoded_continuous_weighted_quantile_bias_root_n_negligible
    [Fintype Z] (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n a, ContClipping M L (eh n a))
    (hshares : ∀ n a, ContFittedSharesSimplex L (eh n a))
    (hm : ∀ n a c, Measurable (contComponent M L (eh n a) c))
    (hd : BoundaryDensitiesBounded M L)
    (hrates : FiniteNuisanceRates M μ (fun n a => contComponent M L (eh n a))
      (contComponent M L (trueNuisance M L)))
    (c : BoundaryIndex L) (g : RegularIndex L) (k' : ℕ)
    (hk' : k' = c.val.1 + 1 ∨ (1 ≤ c.val.1 ∧ k' = c.val.1)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (∫ x, ((eh (2 * (n + 1)) a).gamma g x *
            positiveValue (eh (2 * (n + 1)) a).pLev k' x) *
          ∫ y in Ioc
            (min ((trueNuisance M L).nu c x) ((eh (2 * (n + 1)) a).nu c x))
            (max ((trueNuisance M L).nu c x) ((eh (2 * (n + 1)) a).nu c x)),
          (eh (2 * (n + 1)) a).nu c x - y ∂treatedLaw M L k' x ∂xLaw M))
      atTop (fun _ _ => 0) := by
  let er := fun n a => restrictContShares L (eh n a)
  have her n a : ContAdmissible M L (er n a) :=
    restrictContShares_admissible_of_encoded_clipping M L (eh n a)
      (hclip n a) (hshares n a) (hm n a)
  obtain ⟨r, C, hr, hC, hdensity⟩ := dml_quantile_boundary_density_constants M L hd
  obtain ⟨_, _, _, _, _, _, _, _, hrnu, _⟩ :=
    continuous_component_rates_to_oracle_rates M μ L eh (trueNuisance M L) hrates
  have hcoords n a : Measurable ((er n a).nu c) ∧
      (∀ᵐ x ∂xLaw M, (er n a).nu c x ∈ Icc M.yMin M.yMax) ∧
      Measurable (fun x => (er n a).gamma g x * positiveValue (er n a).pLev k' x) ∧
      (∀ᵐ x ∂xLaw M, |(er n a).gamma g x * positiveValue (er n a).pLev k' x| ≤ 1) := by
    rcases her n a with ⟨_, _, hp, hpm, _, _, _, _, _, _, _, _, hg, hgm,
      _, _, hn, hnm, _⟩
    have hpm' : Measurable (positiveValue (er n a).pLev k') := by
      first | fun_prop | skip
      change Measurable (fun x => positiveValue (er n a).pLev k' x)
      by_cases hi : 1 ≤ k' ∧ k' ≤ L.K
      · simpa only [positiveValue, dif_pos hi] using hpm ⟨k', hi⟩
      · simpa only [positiveValue, dif_neg hi] using
          (measurable_const : Measurable (fun _ : X => (0 : ℝ)))
    refine ⟨hnm c, hn c, by fun_prop, ?_⟩
    by_cases hi : 1 ≤ k' ∧ k' ≤ L.K
    · filter_upwards [hg g, hp ⟨k', hi⟩] with x hx hy
      simp only [positiveValue, dif_pos hi]
      rw [abs_mul, abs_of_nonneg hx.1, abs_of_nonneg hy.1]
      exact (mul_le_mul hx.2 hy.2 hy.1 zero_le_one).trans (by norm_num)
    · simp only [positiveValue, dif_neg hi, mul_zero, abs_zero]
      exact Eventually.of_forall (fun _ => zero_le_one)
  rcases he0 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hn0, hm0, _⟩
  exact nuisanceRates_weighted_quantile_boundary_bias_root_n_negligible
    M μ L k' (trueNuisance M L).nu (fun n a => (er n a).nu)
    (fun n a x => (er n a).gamma g x * positiveValue (er n a).pLev k' x)
    c r C 1 (hm0 c) (fun n a => (hcoords n a).1)
    (fun n a => (hcoords n a).2.2.1) (hn0 c)
    (fun n a => (hcoords n a).2.1) (fun n a => (hcoords n a).2.2.2)
    hr hC zero_le_one (hdensity c k' hk') hrnu

end Papers.TbsPrteOptimalTransport

module
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousFittedBoundaryWeights
/-! Simultaneous endpoint cancellation for the continuous band score. -/
@[expose] public section
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Set Filter
open scoped Classical Topology

-- This is the outcome-indicator block, including its two CDF corrections.
-- The Ioc convention agrees with IFJ and keeps endpoint atoms exact.
-- @node: continuous_band_indicator_ramp_identity
/-- If [the lower endpoint a does not exceed the upper endpoint b](hyp:hab), then
[the outcome times its band-membership indicator, plus a times the lower-tail
indicator at a minus b times the lower-tail indicator at b, equals the lower
ramp minus the upper ramp](goal). -/
lemma continuous_band_indicator_ramp_identity (a b y : ℝ) (hab : a ≤ b) :
    y * indicator (a < y ∧ y ≤ b) + a * indicator (y ≤ a) -
      b * indicator (y ≤ b) =
    (a - y) * indicator (y ≤ a) - (b - y) * indicator (y ≤ b) := by
  by_cases hya : y ≤ a
  · have hyb : y ≤ b := hya.trans hab
    simp [indicator, hya, hyb, not_lt.mpr hya]
  · by_cases hyb : y ≤ b
    · simp [indicator, hya, hyb, lt_of_not_ge hya]
    · simp [indicator, hya, hyb]

-- Subtract both linear boundary terms before taking expectations. Both
-- thresholds may move together, and neither conditional law needs to be atomless.
-- @node: continuousDebiasedBandBoundary
/-- For [original lower endpoint a](hyp:a), [original upper endpoint b](hyp:b),
[new lower endpoint a′](hyp:a'), [new upper endpoint b′](hyp:b'), and [outcome
y](hyp:y), the [debiased band boundary change](goal) is the change in the
outcome-weighted band indicator with its endpoint corrections, less the lower
endpoint displacement times the original lower-tail indicator, plus the upper
endpoint displacement times the original lower-tail indicator at b. -/
noncomputable def continuousDebiasedBandBoundary (a b a' b' y : ℝ) : ℝ :=
  (y * indicator (a' < y ∧ y ≤ b') + a' * indicator (y ≤ a') -
    b' * indicator (y ≤ b')) -
  (y * indicator (a < y ∧ y ≤ b) + a * indicator (y ≤ a) -
    b * indicator (y ≤ b)) -
  ((a' - a) * indicator (y ≤ a) - (b' - b) * indicator (y ≤ b))

-- @node: continuous_debiased_band_boundary_difference
/-- If [the original band is ordered](hyp:hab) and [the new band is
ordered](hyp:hab'), then [the debiased band boundary change equals the debiased
lower-endpoint ramp change minus the debiased upper-endpoint ramp change](goal). -/
lemma continuous_debiased_band_boundary_difference (a b a' b' y : ℝ)
    (hab : a ≤ b) (hab' : a' ≤ b') :
    continuousDebiasedBandBoundary a b a' b' y =
    ((a' - y) * indicator (y ≤ a') - (a - y) * indicator (y ≤ a) -
      (a' - a) * indicator (y ≤ a)) -
    ((b' - y) * indicator (y ≤ b') - (b - y) * indicator (y ≤ b) -
      (b' - b) * indicator (y ≤ b)) := by
  unfold continuousDebiasedBandBoundary
  rw [continuous_band_indicator_ramp_identity a' b' y hab',
    continuous_band_indicator_ramp_identity a b y hab]
  ring

-- The swept-interval representation supplies integrability even when the
-- outcome law has no first moment: the remainder has bounded support and size.
-- @node: debiased_quantile_boundary_integrable
/-- [Under any finite outcome measure, the lower-tail ramp change between two
thresholds after subtraction of its linear indicator term is integrable](goal). -/
lemma debiased_quantile_boundary_integrable (ν : Measure ℝ) [IsFiniteMeasure ν]
    (a b : ℝ) :
    Integrable (fun y => (b - y) * indicator (y ≤ b) -
      (a - y) * indicator (y ≤ a) - (b - a) * indicator (y ≤ a)) ν := by
  have hm : Measurable (fun y : ℝ => (b - y) * indicator (y ≤ b) -
      (a - y) * indicator (y ≤ a) - (b - a) * indicator (y ≤ a)) := by
    fun_prop
  apply Integrable.of_bound hm.aestronglyMeasurable |b - a|
  apply Eventually.of_forall
  intro y
  rw [debiased_quantile_boundary_pointwise, norm_mul, Real.norm_eq_abs]
  have hs : |(if a ≤ b then 1 else -1 : ℝ)| = 1 := by
    split_ifs <;> norm_num
  rw [hs, one_mul]
  by_cases hy : y ∈ Ioc (min a b) (max a b)
  · rw [Set.indicator_of_mem hy, Real.norm_eq_abs]
    by_cases hab : a ≤ b
    · simp only [min_eq_left hab, max_eq_right hab, mem_Ioc] at hy
      rw [abs_of_nonneg (by linarith : 0 ≤ b - y),
        abs_of_nonneg (sub_nonneg.mpr hab)]
      linarith [hy.1, hy.2]
    · have hba : b ≤ a := le_of_not_ge hab
      simp only [min_eq_right hba, max_eq_left hba, mem_Ioc] at hy
      rw [abs_of_nonpos (by linarith : b - y ≤ 0),
        abs_of_nonpos (sub_nonpos.mpr hba)]
      linarith [hy.1, hy.2]
  · rw [Set.indicator_of_notMem hy, norm_zero]
    exact abs_nonneg _

-- @node: continuous_debiased_band_boundary_integral
/-- If [the original endpoints are ordered](hyp:hab) and [the new endpoints are
ordered](hyp:hab'), then [the debiased band boundary change is integrable under
the finite outcome measure, and its integral equals the integrated debiased
lower-endpoint ramp change minus the integrated debiased upper-endpoint ramp
change](goal). -/
lemma continuous_debiased_band_boundary_integral (ν : Measure ℝ) [IsFiniteMeasure ν]
    (a b a' b' : ℝ) (hab : a ≤ b) (hab' : a' ≤ b') :
    Integrable (continuousDebiasedBandBoundary a b a' b') ν ∧
    (∫ y, continuousDebiasedBandBoundary a b a' b' y ∂ν) =
    (∫ y, (a' - y) * indicator (y ≤ a') - (a - y) * indicator (y ≤ a) -
      (a' - a) * indicator (y ≤ a) ∂ν) -
    (∫ y, (b' - y) * indicator (y ≤ b') - (b - y) * indicator (y ≤ b) -
      (b' - b) * indicator (y ≤ b) ∂ν) := by
  have ha := debiased_quantile_boundary_integrable ν a a'
  have hb := debiased_quantile_boundary_integrable ν b b'
  have heq : continuousDebiasedBandBoundary a b a' b' = fun y =>
      ((a' - y) * indicator (y ≤ a') - (a - y) * indicator (y ≤ a) -
        (a' - a) * indicator (y ≤ a)) -
      ((b' - y) * indicator (y ≤ b') - (b - y) * indicator (y ≤ b) -
        (b' - b) * indicator (y ≤ b)) := by
    funext y
    exact continuous_debiased_band_boundary_difference a b a' b' y hab hab'
  rw [heq]
  exact ⟨ha.sub' hb, integral_sub ha hb⟩

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- This identifies the nonlinear remainder inside the actual IFJ/IFM block.
-- Its remaining terms are linear CDF residuals, treated by the moment and
-- propensity-representer cancellations elsewhere in the score assembly.
-- @node: continuous_band_quantile_regression_difference
/-- If the two nuisance specifications have [equal level instrument
probabilities](hyp:hpi), [equal upper band moments](hyp:hJp), [equal lower band
moments](hyp:hJm), [equal upper boundary probabilities](hyp:hMp), and [equal lower
boundary probabilities](hyp:hMm), then [the change in the band moment score plus
its two quantile regression corrections equals the inverse-probability weighted
sum of the debiased band boundary change and the two endpoint displacements
times their original indicator residuals; the lower branch at level zero has
weight zero](goal). -/
lemma continuous_band_quantile_regression_difference
    (L : LevelData Z X) (e b : NuisanceCont L) (plus : Bool)
    (hpi : e.piLev = b.piLev) (hJp : e.Jplus = b.Jplus) (hJm : e.Jminus = b.Jminus)
    (hMp : e.Mplus = b.Mplus) (hMm : e.Mminus = b.Mminus)
    (k j : ℕ) (o : Obs X Z) :
    (IFJ M L e plus k j o + nuValue M e k j o.1 * IFM M L e plus k j o -
      nuValue M e k (j+1) o.1 * IFM M L e plus k (j+1) o) -
    (IFJ M L b plus k j o + nuValue M b k j o.1 * IFM M L b plus k j o -
      nuValue M b k (j+1) o.1 * IFM M L b plus k (j+1) o) =
    (if !plus && k == 0 then 0 else
      indicator (o.2.1 ∈ L.S (if plus then k+1 else k)) * o.2.2.1 /
        positiveValue b.piLev (if plus then k+1 else k) o.1) *
    (continuousDebiasedBandBoundary
      (nuValue M b k j o.1) (nuValue M b k (j+1) o.1)
      (nuValue M e k j o.1) (nuValue M e k (j+1) o.1) o.2.2.2 +
      (nuValue M e k j o.1 - nuValue M b k j o.1) *
        (indicator (o.2.2.2 ≤ nuValue M b k j o.1) -
          if plus then boundaryValue b.Mplus k j o.1 else minusBoundaryValue b.Mminus k j o.1) -
      (nuValue M e k (j+1) o.1 - nuValue M b k (j+1) o.1) *
        (indicator (o.2.2.2 ≤ nuValue M b k (j+1) o.1) -
          if plus then boundaryValue b.Mplus k (j+1) o.1
          else minusBoundaryValue b.Mminus k (j+1) o.1)) := by
  unfold continuousDebiasedBandBoundary
  cases plus <;> by_cases hk : k = 0
  all_goals simp [IFJ, IFM, hpi, hJp, hJm, hMp, hMm, hk]
  all_goals ring

-- The two endpoint errors contribute their squared L2 norms. The weight
-- can be signed and need not be independent of either fitted threshold.
-- @node: population_weighted_band_boundary_integrated_quadratic
/-- Suppose [the original lower endpoint](hyp:ha), [original upper
endpoint](hyp:hb), [new lower endpoint](hyp:ha'), [new upper endpoint](hyp:hb'),
and [weight](hyp:hw) are measurable, [the original band](hyp:hab) and [new
band](hyp:hab') are ordered everywhere, and [the lower](hyp:hea) and [upper
endpoint errors](hyp:heb) are square integrable. If [B is nonnegative](hyp:hB),
[r is positive](hyp:hr), [C is nonnegative](hyp:hC), [the weight has absolute
value at most B almost everywhere](hyp:hwb), and the conditional treated outcome
law has [interval mass at most C times length within distance r of the original
lower endpoint](hyp:hda) and [the same bound near the original upper
endpoint](hyp:hdb), then [the weighted conditional mean of the debiased band
change is integrable, and its population mean has absolute value at most
B times the sum of C and 1/r times the sum of the two integrated squared endpoint
errors](goal). -/
lemma population_weighted_band_boundary_integrated_quadratic
    (L : LevelData Z X) (i : ℕ) (a b a' b' w : X → ℝ)
    (ha : Measurable a) (hb : Measurable b)
    (ha' : Measurable a') (hb' : Measurable b') (hw : Measurable w)
    (hab : ∀ x, a x ≤ b x) (hab' : ∀ x, a' x ≤ b' x)
    (hea : MemLp (fun x => a' x - a x) 2 (xLaw M))
    (heb : MemLp (fun x => b' x - b x) 2 (xLaw M))
    (B r C : ℝ) (hB : 0 ≤ B) (hr : 0 < r) (hC : 0 ≤ C)
    (hwb : ∀ᵐ x ∂xLaw M, |w x| ≤ B)
    (hda : ∀ᵐ x ∂xLaw M, ∀ u v, a x - r ≤ u → u ≤ v → v ≤ a x + r →
      (treatedLaw M L i x (Ioc u v)).toReal ≤ C * (v - u))
    (hdb : ∀ᵐ x ∂xLaw M, ∀ u v, b x - r ≤ u → u ≤ v → v ≤ b x + r →
      (treatedLaw M L i x (Ioc u v)).toReal ≤ C * (v - u)) :
    Integrable (fun x => w x * (∫ y,
      continuousDebiasedBandBoundary (a x) (b x) (a' x) (b' x) y
      ∂treatedLaw M L i x)) (xLaw M) ∧
    |∫ x, w x * (∫ y,
      continuousDebiasedBandBoundary (a x) (b x) (a' x) (b' x) y
      ∂treatedLaw M L i x) ∂xLaw M| ≤
      B * (C + 1 / r) * ((∫ x, (a' x - a x)^2 ∂xLaw M) +
        ∫ x, (b' x - b x)^2 ∂xLaw M) := by
  obtain ⟨ia, ba⟩ := population_weighted_quantile_boundary_integrated_quadratic M L i
    a a' w ha ha' hw B hB hwb hea r C hr hC hda
  obtain ⟨ib, bb⟩ := population_weighted_quantile_boundary_integrated_quadratic M L i
    b b' w hb hb' hw B hB hwb heb r C hr hC hdb
  haveI (x : X) : IsFiniteMeasure (treatedLaw M L i x) := treatedLaw_isFiniteMeasure M L i x
  have hid (x : X) := (continuous_debiased_band_boundary_integral
    (treatedLaw M L i x) (a x) (b x) (a' x) (b' x) (hab x) (hab' x)).2
  simp_rw [hid, mul_sub]
  refine ⟨ia.sub' ib, ?_⟩
  rw [integral_sub ia ib]
  exact (abs_sub _ _).trans ((add_le_add ba bb).trans_eq (by ring))

-- Both indicator endpoints move simultaneously along an L2 direction.
-- Local fitted-weight control suffices; no derivative of the weight is used.
-- @node: population_weighted_band_boundary_local_path_orthogonality
/-- Suppose [the lower endpoint](hyp:ha), [upper endpoint](hyp:hb), [lower
direction](hyp:hda), and [upper direction](hyp:hdb) are measurable, with
[square-integrable lower](hyp:hda2) and [upper directions](hyp:hdb2), [the original
band is ordered](hyp:hab), and [both endpoints remain ordered along their linear
paths for all sufficiently small perturbations](hyp:hpath). If [B is
nonnegative](hyp:hB), [r is positive](hyp:hr), [C is nonnegative](hyp:hC), [the
path weights are measurable and bounded in absolute value by B almost everywhere
for all sufficiently small perturbations](hyp:hw), and [conditional treated
interval masses near the lower endpoint](hyp:hdena) and [near the upper
endpoint](hyp:hdenb) are at most C times interval length within radius r, then
[the weighted population debiased band boundary change has derivative zero at
zero along these simultaneous endpoint paths](goal). -/
lemma population_weighted_band_boundary_local_path_orthogonality
    (L : LevelData Z X) (i : ℕ) (a b da db : X → ℝ) (w : ℝ → X → ℝ)
    (ha : Measurable a) (hb : Measurable b)
    (hda : Measurable da) (hdb : Measurable db)
    (hda2 : MemLp da 2 (xLaw M)) (hdb2 : MemLp db 2 (xLaw M))
    (hab : ∀ x, a x ≤ b x)
    (hpath : ∀ᶠ t : ℝ in 𝓝 0, ∀ x, a x + t * da x ≤ b x + t * db x)
    (B r C : ℝ) (hB : 0 ≤ B) (hr : 0 < r) (hC : 0 ≤ C)
    (hw : ∀ᶠ t : ℝ in 𝓝 0, Measurable (w t) ∧ ∀ᵐ x ∂xLaw M, |w t x| ≤ B)
    (hdena : ∀ᵐ x ∂xLaw M, ∀ u v, a x - r ≤ u → u ≤ v → v ≤ a x + r →
      (treatedLaw M L i x (Ioc u v)).toReal ≤ C * (v - u))
    (hdenb : ∀ᵐ x ∂xLaw M, ∀ u v, b x - r ≤ u → u ≤ v → v ≤ b x + r →
      (treatedLaw M L i x (Ioc u v)).toReal ≤ C * (v - u)) :
    HasDerivAt (fun t : ℝ => ∫ x, w t x * (∫ y,
      continuousDebiasedBandBoundary (a x) (b x)
        (a x + t * da x) (b x + t * db x) y ∂treatedLaw M L i x)
      ∂xLaw M) 0 0 := by
  have za := population_weighted_quantile_boundary_local_path_orthogonality M L i
    a da w ha hda hda2 B hB hw r C hr hC hdena
  have zb := population_weighted_quantile_boundary_local_path_orthogonality M L i
    b db w hb hdb hdb2 B hB hw r C hr hC hdenb
  have hz := za.sub zb
  simp only [sub_zero] at hz
  apply hz.congr_of_eventuallyEq
  filter_upwards [hpath, hw] with t ht hwt
  have ia := (population_weighted_quantile_boundary_integrated_quadratic M L i
    a (fun x => a x + t * da x) (w t) ha (by fun_prop) hwt.1 B hB hwt.2
    (by simpa only [add_sub_cancel_left] using hda2.const_mul t)
    r C hr hC hdena).1
  have ib := (population_weighted_quantile_boundary_integrated_quadratic M L i
    b (fun x => b x + t * db x) (w t) hb (by fun_prop) hwt.1 B hB hwt.2
    (by simpa only [add_sub_cancel_left] using hdb2.const_mul t)
    r C hr hC hdenb).1
  haveI (x : X) : IsFiniteMeasure (treatedLaw M L i x) := treatedLaw_isFiniteMeasure M L i x
  simp_rw [(continuous_debiased_band_boundary_integral (treatedLaw M L i _) _ _ _ _
    (hab _) (ht _)).2, mul_sub, add_sub_cancel_left]
  exact (integral_sub (by simpa only [add_sub_cancel_left] using ia)
    (by simpa only [add_sub_cancel_left] using ib))

-- The first band's lower endpoint is fixed. Only the estimated upper
-- endpoint needs a density bound; none is imposed at yMin by this lemma.
-- @node: population_weighted_band_fixed_lower_path_orthogonality
/-- Suppose [the upper endpoint](hyp:hb) and [its direction](hyp:hdb) are
measurable, [the direction is square integrable](hyp:hdb2), [the original band is
ordered](hyp:hab), and [the moving upper endpoint stays above the fixed lower
endpoint for all sufficiently small perturbations](hyp:hpath). If [B is
nonnegative](hyp:hB), [r is positive](hyp:hr), [C is nonnegative](hyp:hC), [the
path weights are measurable and bounded in absolute value by B almost everywhere
near zero](hyp:hw), and [conditional treated interval masses within radius r of
the original upper endpoint are at most C times length](hyp:hdenb), then [the
weighted population debiased band change with fixed lower endpoint has derivative
zero at zero](goal). -/
lemma population_weighted_band_fixed_lower_path_orthogonality
    (L : LevelData Z X) (i : ℕ) (a b db : X → ℝ) (w : ℝ → X → ℝ)
    (hb : Measurable b) (hdb : Measurable db) (hdb2 : MemLp db 2 (xLaw M))
    (hab : ∀ x, a x ≤ b x)
    (hpath : ∀ᶠ t : ℝ in 𝓝 0, ∀ x, a x ≤ b x + t * db x)
    (B r C : ℝ) (hB : 0 ≤ B) (hr : 0 < r) (hC : 0 ≤ C)
    (hw : ∀ᶠ t : ℝ in 𝓝 0, Measurable (w t) ∧ ∀ᵐ x ∂xLaw M, |w t x| ≤ B)
    (hdenb : ∀ᵐ x ∂xLaw M, ∀ u v, b x - r ≤ u → u ≤ v → v ≤ b x + r →
      (treatedLaw M L i x (Ioc u v)).toReal ≤ C * (v - u)) :
    HasDerivAt (fun t : ℝ => ∫ x, w t x * (∫ y,
      continuousDebiasedBandBoundary (a x) (b x) (a x) (b x + t * db x) y
      ∂treatedLaw M L i x) ∂xLaw M) 0 0 := by
  have zb := population_weighted_quantile_boundary_local_path_orthogonality M L i
    b db w hb hdb hdb2 B hB hw r C hr hC hdenb
  have hz := zb.neg
  simp only [neg_zero] at hz
  apply hz.congr_of_eventuallyEq
  filter_upwards [hpath] with t ht
  simp_rw [continuous_debiased_band_boundary_difference _ _ _ _ _ (hab _) (ht _)]
  simp only [sub_self, zero_mul, zero_sub, add_sub_cancel_left,
    integral_neg, mul_neg]
  rfl

end Papers.TbsPrteOptimalTransport

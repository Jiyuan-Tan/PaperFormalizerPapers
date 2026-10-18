module
public import Papers.TbsPrteOptimalTransport.Helpers.Orthogonality
public import Causalean.Stat.Limit.StochasticOrderEnvelope
/-! Tower identities and exact second-order bias for product scores. -/
public section

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory

-- @node: score_weighted_conditional_integral
/-- For [a conditioning information set contained in the ambient information](hyp:hm),
suppose [the weight is measurable with respect to that information](hyp:hw), [the score
and its conditional mean are integrable](hyp:hs,hj), [their products with the weight
are integrable](hyp:hws,hwj), [the conditional expectation of the score equals the given
conditional mean almost surely](hyp:hcond), and [that mean is measurable with respect to
the conditioning information](hyp:hjm). Then [the weighted score and the weighted
conditional mean have equal integrals](goal). -/
lemma score_weighted_conditional_integral {B : Type*} [mB : MeasurableSpace B]
    (ν : Measure B) (m : MeasurableSpace B) (hm : m ≤ mB)
    [SigmaFinite (ν.trim hm)] (w s j : B → ℝ)
    (hw : StronglyMeasurable[m] w) (hs : Integrable s ν) (hj : Integrable j ν)
    (hws : Integrable (fun b => w b * s b) ν)
    (hwj : Integrable (fun b => w b * j b) ν)
    (hcond : ν[s | m] =ᵐ[ν] j) (hjm : StronglyMeasurable[m] j) :
    (∫ b, w b * s b ∂ν) = ∫ b, w b * j b ∂ν := by
  let : MeasurableSpace B := mB
  have hres : Integrable (fun b => w b * (s b - j b)) ν := by
    simpa only [mul_sub, Pi.sub_apply] using hws.sub' hwj
  have hz := score_weighted_conditional_residual_zero ν m hm w s j
    hw hs hj hres hcond hjm
  simp only [mul_sub] at hz
  rw [integral_sub hws hwj] at hz
  exact sub_eq_zero.mp hz

-- Both component residuals are centered conditionally; the weight may be signed.
-- @node: product_score_population_mean
/-- For [a conditioning information set contained in the ambient information](hyp:hm),
suppose [the weight and component mean are measurable with respect to that
information](hyp:hg,hjm), [the component score, component mean, assignment contrast, and
weight are integrable](hyp:hs,hj,ha,hgi), [the weight times the component score and the
weight times the component mean are integrable](hyp:hgs,hgj), and [the component mean
times the assignment contrast minus its mean is integrable](hyp:hres). If [the component
score has the given component mean conditionally](hyp:hscore) and [the assignment
contrast has the given weight as its conditional mean](hyp:hweight), then [the augmented
product score integrates to the integral of the weight times the component mean](goal). -/
lemma product_score_population_mean {B : Type*} [mB : MeasurableSpace B]
    (ν : Measure B) (m : MeasurableSpace B) (hm : m ≤ mB)
    [SigmaFinite (ν.trim hm)] (g s j a : B → ℝ)
    (hg : StronglyMeasurable[m] g) (hjm : StronglyMeasurable[m] j)
    (hs : Integrable s ν) (hj : Integrable j ν)
    (ha : Integrable a ν) (hgi : Integrable g ν)
    (hgs : Integrable (fun b => g b * s b) ν)
    (hgj : Integrable (fun b => g b * j b) ν)
    (hres : Integrable (fun b => j b * (a b - g b)) ν)
    (hscore : ν[s | m] =ᵐ[ν] j) (hweight : ν[a | m] =ᵐ[ν] g) :
    (∫ b, g b * s b + j b * (a b - g b) ∂ν) =
      ∫ b, g b * j b ∂ν := by
  let : MeasurableSpace B := mB
  have hz := score_weighted_conditional_residual_zero ν m hm j a g
    hjm ha hgi hres hweight hg
  rw [integral_add hgs hres, hz, add_zero]
  exact score_weighted_conditional_integral ν m hm g s j hg hs hj hgs hgj hscore hjm

-- This is an exact expansion, before any Cauchy--Schwarz bound or rate argument.
-- @node: product_score_bias_algebra
/-- [The fitted weight times the true component plus its bias, augmented by the fitted
component times the true-minus-fitted weight and centered at the true product, equals
the fitted weight times the component bias minus the product of the two fitting errors](goal). -/
lemma product_score_bias_algebra {g gh j jh b : ℝ} :
    gh * (j + b) + jh * (g - gh) - g * j =
      gh * b - (gh - g) * (jh - j) := by
  ring

-- A fitted component's conditional bias b is propagated with its fitted weight;
-- the other contribution is exactly the product of the two nuisance errors.
-- @node: product_score_exact_bias
/-- For [a conditioning information set contained in the ambient information](hyp:hm),
suppose [the true and fitted weights, fitted component mean, and true component mean
plus bias are measurable with respect to that information](hyp:hg,hgh,hjh,hjb);
[the component score, assignment contrast, true weight, and component mean plus bias
are integrable](hyp:hs,ha,hgi,hjbi); [the fitted weight times the score and times the
component mean plus bias are integrable](hyp:hghs,hghjb); [the fitted component times
the centered assignment contrast and times the true-minus-fitted weight are
integrable](hyp:hres,hcross); and [the true target product is integrable](hyp:htarget).
If [the score's conditional mean is the true component mean plus bias](hyp:hscore) and
[the assignment contrast's conditional mean is the true weight](hyp:hweight), then
[the augmented fitted product's integrated bias equals the integral of the fitted
weight times component bias minus the product of weight and component fitting errors](goal). -/
lemma product_score_exact_bias {B : Type*} [mB : MeasurableSpace B]
    (ν : Measure B) (m : MeasurableSpace B) (hm : m ≤ mB)
    [SigmaFinite (ν.trim hm)] (g gh s j jh a b : B → ℝ)
    (hg : StronglyMeasurable[m] g) (hgh : StronglyMeasurable[m] gh)
    (hjh : StronglyMeasurable[m] jh)
    (hjb : StronglyMeasurable[m] (fun x => j x + b x))
    (hs : Integrable s ν) (ha : Integrable a ν) (hgi : Integrable g ν)
    (hjbi : Integrable (fun x => j x + b x) ν)
    (hghs : Integrable (fun x => gh x * s x) ν)
    (hghjb : Integrable (fun x => gh x * (j x + b x)) ν)
    (hres : Integrable (fun x => jh x * (a x - g x)) ν)
    (hcross : Integrable (fun x => jh x * (g x - gh x)) ν)
    (htarget : Integrable (fun x => g x * j x) ν)
    (hscore : ν[s | m] =ᵐ[ν] (fun x => j x + b x))
    (hweight : ν[a | m] =ᵐ[ν] g) :
    (∫ x, gh x * s x + jh x * (a x - gh x) ∂ν) -
      (∫ x, g x * j x ∂ν) =
      ∫ x, gh x * b x - (gh x - g x) * (jh x - j x) ∂ν := by
  let : MeasurableSpace B := mB
  have hz := score_weighted_conditional_residual_zero ν m hm jh a g
    hjh ha hgi hres hweight hg
  have hsplit : (fun x => jh x * (a x - gh x)) =
      (fun x => jh x * (a x - g x) + jh x * (g x - gh x)) := by
    funext x
    ring
  have hcorr : Integrable (fun x => jh x * (a x - gh x)) ν := by
    rw [hsplit]
    exact hres.add hcross
  rw [integral_add hghs hcorr, hsplit, integral_add hres hcross, hz,
    zero_add]
  rw [score_weighted_conditional_integral ν m hm gh s (fun x => j x + b x)
    hgh hs hjbi hghs hghjb hscore hjb]
  rw [← integral_add hghjb hcross]
  have hsum : Integrable (fun x => gh x * (j x + b x) + jh x * (g x - gh x)) ν :=
    hghjb.add hcross
  rw [← integral_sub hsum htarget]
  apply integral_congr_ae
  filter_upwards [] with x
  exact product_score_bias_algebra

-- The fitted product weight can be signed (as for the full-interval score).
-- Its bound controls the propagated component bias; Cauchy--Schwarz controls
-- the remaining product of nuisance errors.
-- @node: product_score_remainder_L2_bound
/-- If [the fitted weight is almost everywhere strongly measurable](hyp:hgh), [the
component bias is integrable](hyp:hb), [the fitted weight is almost surely bounded in
absolute value by the given constant](hyp:hbound), and [both error functions have finite
second moments](hyp:heg,hej), then [the absolute integral of the weighted component bias
minus the error product is bounded by that constant times the integral of absolute
component bias plus the product of the two L2 norms](goal). -/
lemma product_score_remainder_L2_bound {B : Type*} [MeasurableSpace B]
    (ν : Measure B) (gh b eg ej : B → ℝ) (G : ℝ)
    (hgh : AEStronglyMeasurable gh ν) (hb : Integrable b ν)
    (hbound : ∀ᵐ x ∂ν, |gh x| ≤ G)
    (heg : MemLp eg 2 ν) (hej : MemLp ej 2 ν) :
    |∫ x, gh x * b x - eg x * ej x ∂ν| ≤
      G * (∫ x, |b x| ∂ν) +
        (eLpNorm eg 2 ν).toReal * (eLpNorm ej 2 ν).toReal := by
  have hgb : Integrable (fun x => gh x * b x) ν :=
    hb.bdd_mul hgh (by simpa only [Real.norm_eq_abs] using hbound)
  have heprod : Integrable (fun x => eg x * ej x) ν := heg.integrable_mul hej
  have hmean : |∫ x, gh x * b x ∂ν| ≤ G * (∫ x, |b x| ∂ν) := by
    calc
      _ ≤ ∫ x, |gh x * b x| ∂ν := by
        simpa only [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (fun x => gh x * b x)
      _ ≤ ∫ x, G * |b x| ∂ν := by
        apply integral_mono_ae hgb.abs (hb.abs.const_mul G)
        filter_upwards [hbound] with x hx
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)
      _ = _ := integral_const_mul _ _
  have hcross : |∫ x, eg x * ej x ∂ν| ≤
      (eLpNorm eg 2 ν).toReal * (eLpNorm ej 2 ν).toReal := by
    calc
      _ ≤ ∫ x, |eg x * ej x| ∂ν := by
        simpa only [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (fun x => eg x * ej x)
      _ ≤ _ := Causalean.Stat.integral_abs_mul_le_eLpNorm_mul_eLpNorm heg hej
  rw [integral_sub hgb heprod]
  exact (abs_sub _ _).trans (add_le_add hmean hcross)

-- Assemble the quantitative bound from the conditional score expansion,
-- rather than bounding the plug-in functional alone.
-- @node: product_score_bias_L2_bound
/-- For [a conditioning information set contained in the ambient information](hyp:hm),
suppose [the true and fitted weights, fitted component mean, and true component mean
plus bias are measurable with respect to that information](hyp:hg,hgh,hjh,hjb);
[the component score, assignment contrast, true weight, and component mean plus bias
are integrable](hyp:hs,ha,hgi,hjbi); [the fitted weight times the score and times the
component mean plus bias are integrable](hyp:hghs,hghjb); [the fitted component times
the centered assignment contrast and times the true-minus-fitted weight are
integrable](hyp:hres,hcross); and [the true target product is integrable](hyp:htarget).
If [the score's conditional mean is the true component mean plus bias](hyp:hscore),
[the assignment contrast's conditional mean is the true weight](hyp:hweight), [the
component bias is integrable](hyp:hb), [the fitted weight is almost surely bounded in
absolute value by the given constant](hyp:hbound), and [the weight and component fitting
errors have finite second moments](hyp:heg,hej), then [the absolute integrated bias of
the augmented fitted product is at most that constant times the integral of absolute
component bias plus the product of the L2 norms of the two fitting errors](goal). -/
lemma product_score_bias_L2_bound {B : Type*} [mB : MeasurableSpace B]
    (ν : Measure B) (m : MeasurableSpace B) (hm : m ≤ mB)
    [SigmaFinite (ν.trim hm)] (g gh s j jh a b : B → ℝ) (G : ℝ)
    (hg : StronglyMeasurable[m] g) (hgh : StronglyMeasurable[m] gh)
    (hjh : StronglyMeasurable[m] jh)
    (hjb : StronglyMeasurable[m] (fun x => j x + b x))
    (hs : Integrable s ν) (ha : Integrable a ν) (hgi : Integrable g ν)
    (hjbi : Integrable (fun x => j x + b x) ν)
    (hghs : Integrable (fun x => gh x * s x) ν)
    (hghjb : Integrable (fun x => gh x * (j x + b x)) ν)
    (hres : Integrable (fun x => jh x * (a x - g x)) ν)
    (hcross : Integrable (fun x => jh x * (g x - gh x)) ν)
    (htarget : Integrable (fun x => g x * j x) ν)
    (hscore : ν[s | m] =ᵐ[ν] (fun x => j x + b x))
    (hweight : ν[a | m] =ᵐ[ν] g)
    (hb : Integrable b ν) (hbound : ∀ᵐ x ∂ν, |gh x| ≤ G)
    (heg : MemLp (fun x => gh x - g x) 2 ν)
    (hej : MemLp (fun x => jh x - j x) 2 ν) :
    |(∫ x, gh x * s x + jh x * (a x - gh x) ∂ν) -
        (∫ x, g x * j x ∂ν)| ≤
      G * (∫ x, |b x| ∂ν) +
        (eLpNorm (fun x => gh x - g x) 2 ν).toReal *
          (eLpNorm (fun x => jh x - j x) 2 ν).toReal := by
  let : MeasurableSpace B := mB
  rw [product_score_exact_bias ν m hm g gh s j jh a b
    hg hgh hjh hjb hs ha hgi hjbi hghs hghjb hres hcross htarget hscore hweight]
  exact product_score_remainder_L2_bound ν gh b
    (fun x => gh x - g x) (fun x => jh x - j x) G
    (hgh.mono hm).aestronglyMeasurable hb hbound heg hej

-- The simplex constraint removes the standalone share error before the
-- finite collection of error products is bounded in L2.
-- @node: simplex_pooling_bias_L2_bound
/-- If [the true shares sum to one almost surely over the finite instrument set](hyp:ha),
[the fitted shares also sum to one almost surely](hyp:hah), [every share fitting error
has a finite second moment](hyp:hea), and [each fitted instrument-specific quantity
minus the common reference has a finite second moment](hyp:heq), then [the integral of
the absolute pooled share-error contribution is bounded by the sum, over instruments,
of the share-error L2 norm times the L2 norm of the fitted quantity minus the reference](goal). -/
lemma simplex_pooling_bias_L2_bound {B ι : Type*} [MeasurableSpace B]
    (ν : Measure B) (s : Finset ι) (a ah qh : ι → B → ℝ) (q0 : B → ℝ)
    (ha : ∀ᵐ x ∂ν, ∑ z ∈ s, a z x = 1)
    (hah : ∀ᵐ x ∂ν, ∑ z ∈ s, ah z x = 1)
    (hea : ∀ z ∈ s, MemLp (fun x => ah z x - a z x) 2 ν)
    (heq : ∀ z ∈ s, MemLp (fun x => qh z x - q0 x) 2 ν) :
    (∫ x, |∑ z ∈ s, (ah z x - a z x) * qh z x| ∂ν) ≤
      ∑ z ∈ s, (eLpNorm (fun x => ah z x - a z x) 2 ν).toReal *
        (eLpNorm (fun x => qh z x - q0 x) 2 ν).toReal := by
  have hprod : ∀ z ∈ s, Integrable
      (fun x => (ah z x - a z x) * (qh z x - q0 x)) ν := by
    intro z hz
    exact (hea z hz).integrable_mul (heq z hz)
  have heqae : (fun x => ∑ z ∈ s, (ah z x - a z x) * qh z x) =ᵐ[ν]
      (fun x => ∑ z ∈ s, (ah z x - a z x) * (qh z x - q0 x)) := by
    filter_upwards [ha, hah] with x hx hxhat
    exact simplex_pooling_error_product s
      (fun z => a z x) (fun z => ah z x) (fun z => qh z x) (q0 x) hx hxhat
  calc
    _ = ∫ x, |∑ z ∈ s, (ah z x - a z x) * (qh z x - q0 x)| ∂ν :=
      integral_congr_ae (heqae.fun_comp abs)
    _ ≤ ∫ x, ∑ z ∈ s, |(ah z x - a z x) * (qh z x - q0 x)| ∂ν := by
      apply integral_mono (integrable_finsetSum s hprod).abs
        (integrable_finsetSum s (fun z hz => (hprod z hz).abs))
      intro x
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ z ∈ s, ∫ x, |(ah z x - a z x) * (qh z x - q0 x)| ∂ν :=
      integral_finsetSum s (fun z hz => (hprod z hz).abs)
    _ ≤ _ := Finset.sum_le_sum fun z hz =>
      Causalean.Stat.integral_abs_mul_le_eLpNorm_mul_eLpNorm (hea z hz) (heq z hz)

end Papers.TbsPrteOptimalTransport

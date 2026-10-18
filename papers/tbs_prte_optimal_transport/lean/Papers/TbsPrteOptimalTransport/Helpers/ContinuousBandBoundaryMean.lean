module
public import Papers.TbsPrteOptimalTransport.Helpers.DebiasedBandBoundary
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousBoundaryResidualBounds
/-! Centered linear terms in simultaneous continuous IFJ/IFM boundary changes. -/
public section
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- The two linear boundary terms are actual population CDF residuals. This
-- identity retains the fitted denominator and does not require ordered endpoints.
-- @node: continuous_band_quantile_difference_residual_decomposition
/-- If two nuisance specifications have [equal assignment probabilities](hyp:hpi),
[equal plus-side band outcome regressions](hyp:hJp), [equal minus-side band outcome
regressions](hyp:hJm), [equal plus-side distribution regressions](hyp:hMp), and
[equal minus-side distribution regressions](hyp:hMm), then [the change in the
band outcome influence term plus its two boundary corrections equals the
debiased swept-boundary remainder weighted by the observed level membership,
treatment, and fitted assignment denominator, plus the lower threshold change
times its reference distribution residual minus the analogous upper term](goal). -/
lemma continuous_band_quantile_difference_residual_decomposition
    (L : LevelData Z X) (e b : NuisanceCont L) (plus : Bool)
    (hpi : e.piLev = b.piLev) (hJp : e.Jplus = b.Jplus) (hJm : e.Jminus = b.Jminus)
    (hMp : e.Mplus = b.Mplus) (hMm : e.Mminus = b.Mminus)
    (k j : ℕ) (o : Obs X Z) :
    (IFJ M L e plus k j o + nuValue M e k j o.1 * IFM M L e plus k j o -
      nuValue M e k (j + 1) o.1 * IFM M L e plus k (j + 1) o) -
    (IFJ M L b plus k j o + nuValue M b k j o.1 * IFM M L b plus k j o -
      nuValue M b k (j + 1) o.1 * IFM M L b plus k (j + 1) o) =
    (if !plus && k == 0 then 0 else
      indicator (o.2.1 ∈ L.S (if plus then k + 1 else k)) * o.2.2.1 /
        positiveValue b.piLev (if plus then k + 1 else k) o.1) *
      continuousDebiasedBandBoundary
        (nuValue M b k j o.1) (nuValue M b k (j + 1) o.1)
        (nuValue M e k j o.1) (nuValue M e k (j + 1) o.1) o.2.2.2 +
    (nuValue M e k j o.1 - nuValue M b k j o.1) * IFM M L b plus k j o -
    (nuValue M e k (j + 1) o.1 - nuValue M b k (j + 1) o.1) *
      IFM M L b plus k (j + 1) o := by
  rw [continuous_band_quantile_regression_difference M L e b plus hpi hJp hJm hMp hMm]
  cases plus <;> by_cases hk : k = 0
  all_goals simp [IFM, hk]
  all_goals ring

-- Tower-property cancellation removes both linear CDF residuals. The only
-- remaining mean is the nonlinear swept-boundary remainder, which is controlled
-- by the local density estimate in DebiasedBandBoundary.
-- @node: population_continuous_band_quantile_difference_mean
/-- Suppose [each fitted assignment probability is measurable](hyp:hpi) and
[matches the nuisance specification](hyp:hpiEq), whose [plus-side outcome
regressions](hyp:hJp), [minus-side outcome regressions](hyp:hJm), [plus-side
distribution regressions](hyp:hMp), and [minus-side distribution regressions](hyp:hMm)
equal their population counterparts. For [a valid level](hyp:hk) and [a band
within it](hyp:hj), assume [the lower](hyp:ha) and [upper population boundaries
are measurable](hyp:hb), [the weighted lower](hyp:hwa) and [upper threshold
shifts are measurable](hyp:hwb), [the lower shift equals the fitted threshold
minus its population boundary](hyp:hva), [the upper shift has the corresponding
meaning](hyp:hvb), and [the weighted lower residual term](hyp:ia), [weighted
upper residual term](hyp:ib), and [weighted swept-boundary remainder are
integrable](hyp:ir). Then [the weighted change in the boundary-corrected band
influence term is integrable, and its population mean equals the mean of the
weighted nonlinear swept-boundary remainder using the same fitted assignment
denominator](goal). -/
lemma population_continuous_band_quantile_difference_mean
    (L : LevelData Z X) (e : NuisanceCont L)
    (pi : PositiveIndex L.K → X → ℝ) (hpi : ∀ a, Measurable (pi a))
    (hpiEq : e.piLev = pi)
    (hJp : e.Jplus = (trueNuisance M L).Jplus)
    (hJm : e.Jminus = (trueNuisance M L).Jminus)
    (hMp : e.Mplus = (trueNuisance M L).Mplus)
    (hMm : e.Mminus = (trueNuisance M L).Mminus)
    (plus : Bool) (k j : ℕ) (hk : k < L.K) (hj : j < L.l k)
    (ha : Measurable (bandBoundary M L k j))
    (hb : Measurable (bandBoundary M L k (j + 1)))
    (w va vb : X → ℝ) (hwa : Measurable (fun x => w x * va x))
    (hwb : Measurable (fun x => w x * vb x))
    (hva : ∀ x, va x = nuValue M e k j x - bandBoundary M L k j x)
    (hvb : ∀ x, vb x = nuValue M e k (j + 1) x - bandBoundary M L k (j + 1) x)
    (ia : Integrable (fun o : Obs X Z => (w o.1 * va o.1) *
      IFM M L {trueNuisance M L with piLev := pi} plus k j o) (observationLaw M))
    (ib : Integrable (fun o : Obs X Z => (w o.1 * vb o.1) *
      IFM M L {trueNuisance M L with piLev := pi} plus k (j + 1) o) (observationLaw M))
    (ir : Integrable (fun o : Obs X Z => w o.1 *
      ((if !plus && k == 0 then 0 else
        indicator (o.2.1 ∈ L.S (if plus then k + 1 else k)) * o.2.2.1 /
          positiveValue pi (if plus then k + 1 else k) o.1) *
        continuousDebiasedBandBoundary
          (bandBoundary M L k j o.1) (bandBoundary M L k (j + 1) o.1)
          (nuValue M e k j o.1) (nuValue M e k (j + 1) o.1) o.2.2.2))
        (observationLaw M)) :
    Integrable (fun o : Obs X Z => w o.1 *
      ((IFJ M L e plus k j o + nuValue M e k j o.1 * IFM M L e plus k j o -
        nuValue M e k (j + 1) o.1 * IFM M L e plus k (j + 1) o) -
      (IFJ M L {trueNuisance M L with piLev := pi} plus k j o +
        bandBoundary M L k j o.1 *
          IFM M L {trueNuisance M L with piLev := pi} plus k j o -
        bandBoundary M L k (j + 1) o.1 *
          IFM M L {trueNuisance M L with piLev := pi} plus k (j + 1) o)))
      (observationLaw M) ∧
    (∫ o : Obs X Z, w o.1 *
      ((IFJ M L e plus k j o + nuValue M e k j o.1 * IFM M L e plus k j o -
        nuValue M e k (j + 1) o.1 * IFM M L e plus k (j + 1) o) -
      (IFJ M L {trueNuisance M L with piLev := pi} plus k j o +
        bandBoundary M L k j o.1 *
          IFM M L {trueNuisance M L with piLev := pi} plus k j o -
        bandBoundary M L k (j + 1) o.1 *
          IFM M L {trueNuisance M L with piLev := pi} plus k (j + 1) o))
      ∂observationLaw M) =
    ∫ o : Obs X Z, w o.1 *
      ((if !plus && k == 0 then 0 else
        indicator (o.2.1 ∈ L.S (if plus then k + 1 else k)) * o.2.2.1 /
          positiveValue pi (if plus then k + 1 else k) o.1) *
        continuousDebiasedBandBoundary
          (bandBoundary M L k j o.1) (bandBoundary M L k (j + 1) o.1)
          (nuValue M e k j o.1) (nuValue M e k (j + 1) o.1) o.2.2.2)
      ∂observationLaw M := by
  have za := population_IFM_fitted_denominator_weighted_zero M L pi hpi plus k j hk
    hj.le ha (fun x => w x * va x) hwa ia
  have zb := population_IFM_fitted_denominator_weighted_zero M L pi hpi plus k (j + 1) hk
    (by omega) hb (fun x => w x * vb x) hwb ib
  have hn b (hbl : b ≤ L.l k) x :
      nuValue M {trueNuisance M L with piLev := pi} k b x = bandBoundary M L k b x :=
    population_nuValue_eq_bandBoundary M L k b hk hbl x
  have hid (o : Obs X Z) := continuous_band_quantile_difference_residual_decomposition M L e
    {trueNuisance M L with piLev := pi} plus hpiEq hJp hJm hMp hMm k j o
  simp only [hn j hj.le, hn (j + 1) (by omega)] at hid
  have heq : (fun o : Obs X Z => w o.1 *
      ((IFJ M L e plus k j o + nuValue M e k j o.1 * IFM M L e plus k j o -
        nuValue M e k (j + 1) o.1 * IFM M L e plus k (j + 1) o) -
      (IFJ M L {trueNuisance M L with piLev := pi} plus k j o +
        bandBoundary M L k j o.1 *
          IFM M L {trueNuisance M L with piLev := pi} plus k j o -
        bandBoundary M L k (j + 1) o.1 *
          IFM M L {trueNuisance M L with piLev := pi} plus k (j + 1) o))) =
      (fun o => w o.1 *
        ((if !plus && k == 0 then 0 else
          indicator (o.2.1 ∈ L.S (if plus then k + 1 else k)) * o.2.2.1 /
            positiveValue pi (if plus then k + 1 else k) o.1) *
          continuousDebiasedBandBoundary
            (bandBoundary M L k j o.1) (bandBoundary M L k (j + 1) o.1)
            (nuValue M e k j o.1) (nuValue M e k (j + 1) o.1) o.2.2.2) +
        (w o.1 * va o.1) * IFM M L {trueNuisance M L with piLev := pi} plus k j o -
        (w o.1 * vb o.1) * IFM M L {trueNuisance M L with piLev := pi} plus k (j + 1) o) := by
    funext o
    rw [hid o, hva, hvb]
    ring
  rw [heq]
  refine ⟨(ir.fun_add ia).sub' ib, ?_⟩
  rw [integral_sub (ir.fun_add ia) ib, integral_add ir ia, za, zb]
  ring

-- Changes of either explicit threshold factor multiply a population CDF
-- residual. Even when gamma and pi move together, this expectation vanishes
-- throughout the admissible neighborhood; integrability follows from clipping.
-- @node: population_continuous_fitted_linear_boundary_orthogonality
/-- Given [baseline overlap at the specified positive bound](hyp:hov), [an
admissible continuous nuisance direction from truth](hyp:hd), and [a measurable
population band boundary](hyp:ha), [the population mean of the distribution
residual at that boundary, multiplied by the moving regular-band weight and
the path-scaled threshold direction, has derivative zero at zero, even with
assignment denominators moving along the path](goal). -/
lemma population_continuous_fitted_linear_boundary_orthogonality
    (L : LevelData Z X) (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del))
    (a : BoundaryIndex L) (g : RegularIndex L) (plus : Bool)
    (ha : Measurable (bandBoundary M L a.val.1 a.val.2)) :
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z,
      ((trueNuisance M L + t • del).gamma g o.1 * (t * del.nu a o.1)) *
        IFM M L {trueNuisance M L with piLev := (trueNuisance M L + t • del).piLev}
          plus a.val.1 a.val.2 o ∂observationLaw M) 0 0 := by
  have : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  have hcpi : 0 < cpi := hov.1
  obtain ⟨C, hC, hdir⟩ := continuous_quantile_direction_regular M L
    (trueNuisance M L) del hd
  obtain ⟨r, hr, hpath⟩ := hd.admissible
  apply population_IFM_clipped_local_path_orthogonality M L
    (fun t => (trueNuisance M L + t • del).piLev)
    (fun t x => (trueNuisance M L + t • del).gamma g x * (t * del.nu a x))
    (cpi / 2) (by positivity) _ plus a.val.1 a.val.2 a.property.1 a.property.2.2 ha
  filter_upwards [continuous_assignment_path_uniform_lower_bound M L cpi hov del hd,
    continuousAt_id.abs.eventually_lt_const (by simpa using hr)] with t hclip ht
  have had := hpath t ht
  rcases had with ⟨_, _, _, _, _, hpim, _, _, _, _, _, _, hgb, hgm, _⟩
  have hdm := (hdir a).1
  have hm : Measurable (fun x => (trueNuisance M L + t • del).gamma g x *
      (t * del.nu a x)) := by
    fun_prop
  refine ⟨hpim, hclip, hm, ?_⟩
  apply Integrable.of_bound hm.aestronglyMeasurable (|t| * C)
  filter_upwards [hgb g, (hdir a).2] with x hgx hdx
  rw [norm_mul, norm_mul, Real.norm_eq_abs, abs_of_nonneg hgx.1]
  calc
    _ ≤ 1 * (|t| * C) := mul_le_mul hgx.2
      (mul_le_mul_of_nonneg_left hdx (abs_nonneg t)) (by positivity) zero_le_one
    _ = _ := one_mul _

end Papers.TbsPrteOptimalTransport

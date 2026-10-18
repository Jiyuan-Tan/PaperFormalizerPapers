module
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousPooledJoint
/-! Signed pooled-policy telescopes in the actual continuous band product score. -/
public section
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false
set_option linter.style.longLine false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- Subtracting the true propensity residual with the same fitted denominator
-- converts the conditional pooled remainder into an observation-level telescope.
-- @node: population_continuous_weighted_pooled_policy_telescope
/-- Under [threshold crossing](hyp:h), [a valid policy map](hyp:hphi),
[differentiability with the specified derivative](hyp:hDiff), [a bounded Lipschitz
policy derivative](hyp:hDerivative), [invariant baseline and policy level
ordering](hyp:hOrder), [policy overlap](hyp:hov), and [an admissible joint direction
from truth](hyp:hd), suppose [the weight bound is nonnegative](hyp:hW) and
[near zero the covariate weights are measurable and almost surely bounded by it](hyp:hw).
[The weighted pooled-policy score change, subtracting the true-propensity residual
with the same moving pooled denominator, has expected derivative zero at zero and
is integrable for all sufficiently small perturbations](goal). -/
lemma population_continuous_weighted_pooled_policy_telescope
    (h : ThresholdCrossing M) (phi dphi : Z → X → ℝ → ℝ)
    (hphi : IsPolicyMap phi) (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : PolicyOverlap M L cpi) (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del))
    (a : RegularIndex L) (w : ℝ → X → ℝ) (W : ℝ) (hW : 0 ≤ W)
    (hw : ∀ᶠ t : ℝ in 𝓝 0, Measurable (w t) ∧ ∀ᵐ x ∂xLaw M, ‖w t x‖ ≤ W) :
    let e := fun t : ℝ => trueNuisance M L + t • del
    let b := fun t => {trueNuisance M L with tauLev := (e t).tauLev}
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z, w t o.1 *
      (pooledQ phi L (e t) a.val.1 a.val.2 o.1 + RqCont dphi L (e t) a.val.1 a.val.2 o -
        pooledQ phi L (trueNuisance M L) a.val.1 a.val.2 o.1 -
        RqCont dphi L (b t) a.val.1 a.val.2 o) ∂observationLaw M) 0 0 ∧
    (∀ᶠ t : ℝ in 𝓝 0, Integrable (fun o : Obs X Z => w t o.1 *
      (pooledQ phi L (e t) a.val.1 a.val.2 o.1 + RqCont dphi L (e t) a.val.1 a.val.2 o -
        pooledQ phi L (trueNuisance M L) a.val.1 a.val.2 o.1 -
        RqCont dphi L (b t) a.val.1 a.val.2 o)) (observationLaw M)) := by
  dsimp only
  let e := fun t : ℝ => trueNuisance M L + t • del
  let b := fun t => {trueNuisance M L with tauLev := (e t).tauLev}
  have hp := population_continuous_weighted_pooled_joint_orthogonality M h phi dphi
    hphi hDiff hDerivative L hOrder cpi hov del hd a w W hW hw
  have hdphi := policy_derivative_graph_measurable phi dphi hphi hDiff M.prop
    h.2.1 M.rangeProp
  have hz : ∀ᶠ t : ℝ in 𝓝 0,
      Integrable (fun o : Obs X Z => w t o.1 * RqCont dphi L (b t) a.val.1 a.val.2 o)
        (observationLaw M) ∧
      (∫ o : Obs X Z, w t o.1 * RqCont dphi L (b t) a.val.1 a.val.2 o
        ∂observationLaw M) = 0 := by
    obtain ⟨r, hr, hadm⟩ := hd.admissible
    filter_upwards [hw, continuous_pooled_path_uniform_lower_bound M
      (policyProp phi M.prop) L hOrder cpi hov del hd,
      continuousAt_id.abs.eventually_lt_const (by simpa using hr)] with t hwt hclip ht
    have he := hadm t ht
    have : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
    have iw : Integrable (w t) (xLaw M) :=
      (integrable_const W).mono' hwt.1.aestronglyMeasurable hwt.2
    exact population_RqCont_fitted_pooled_denominator_zero M h dphi hdphi hDerivative
      (policyProp phi M.prop) L hOrder cpi hov (e t).tauLev
      he.2.2.2.2.2.2.2.1 (cpi/2) (div_pos hov.1 (by norm_num)) hclip a
      (w t) hwt.1 iw
  refine ⟨hp.1.congr_of_eventuallyEq ?_, ?_⟩
  · filter_upwards [hp.2, hz] with t hit hzt
    have hid := integral_sub hit hzt.1
    rw [hzt.2, sub_zero] at hid
    simpa only [mul_sub] using hid
  · filter_upwards [hp.2, hz] with t hit hzt
    simpa only [mul_sub] using hit.sub' hzt.1

-- Only the instrument-specific propensity and the pooling shares are frozen.
-- Quantiles, J/M, baseline propensities, pi, tau, and gamma still move jointly.
-- @node: continuous_band_policy_product_difference
/-- [Freezing instrument-specific propensities and pooling shares at truth changes
a band's product score by the upper endpoint's pooled-policy and residual change
weighted by its band weight and quantile, minus the corresponding weighted lower
endpoint change](goal). -/
lemma continuous_band_policy_product_difference
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X) (e : NuisanceCont L)
    (k j : ℕ) (o : Obs X Z) :
    let b := {e with prop := (trueNuisance M L).prop, share := (trueNuisance M L).share}
    psiProd M phi dphi L e k (j+1) o - psiProd M phi dphi L b k (j+1) o =
      (regularValue e.gamma k (j+1) o.1 * nuValue M e k (j+1) o.1) *
        (pooledQ phi L e k (j+1) o.1 + RqCont dphi L e k (j+1) o -
          pooledQ phi L b k (j+1) o.1 - RqCont dphi L b k (j+1) o) -
      (regularValue e.gamma k (j+1) o.1 * nuValue M e k j o.1) *
        (pooledQ phi L e k j o.1 + RqCont dphi L e k j o -
          pooledQ phi L b k j o.1 - RqCont dphi L b k j o) := by
  dsimp only
  simp only [psiProd, Nat.add_sub_cancel, contScoreComponents, contJ, IFJ, IFM,
    nuValue, alphaLow, alphaHigh, RpCont]
  ring

-- The structural boundary i=0 is fixed under this telescope. At every
-- estimated endpoint its moving gamma-times-quantile weight is admissible.
-- @node: population_continuous_band_endpoint_policy_telescope
/-- Under [threshold crossing](hyp:h), [a valid policy map](hyp:hphi),
[policy differentiability](hyp:hDiff), [a bounded Lipschitz policy derivative](hyp:hDerivative),
[invariant baseline and policy level ordering](hyp:hOrder), [policy overlap](hyp:hov),
and [an admissible joint direction from truth](hyp:hd), for [an endpoint at or below
the level's last band boundary](hyp:hi), [the pooled-policy and residual difference
from freezing instrument propensities and pooling shares, multiplied by the moving
band weight and endpoint quantile, has expected derivative zero at zero and is
integrable for all sufficiently small perturbations](goal). -/
lemma population_continuous_band_endpoint_policy_telescope
    (h : ThresholdCrossing M) (phi dphi : Z → X → ℝ → ℝ)
    (hphi : IsPolicyMap phi) (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : PolicyOverlap M L cpi) (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del))
    (g : RegularIndex L) (k : Fin L.K) (i : ℕ) (hi : i ≤ L.l k) :
    let e := fun t : ℝ => trueNuisance M L + t • del
    let b := fun t => {e t with
      prop := (trueNuisance M L).prop,
      share := (trueNuisance M L).share}
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z,
      ((e t).gamma g o.1 * nuValue M (e t) k i o.1) *
        (pooledQ phi L (e t) k i o.1 + RqCont dphi L (e t) k i o -
          pooledQ phi L (b t) k i o.1 - RqCont dphi L (b t) k i o)
        ∂observationLaw M) 0 0 ∧
    (∀ᶠ t : ℝ in 𝓝 0, Integrable (fun o : Obs X Z =>
      ((e t).gamma g o.1 * nuValue M (e t) k i o.1) *
        (pooledQ phi L (e t) k i o.1 + RqCont dphi L (e t) k i o -
          pooledQ phi L (b t) k i o.1 - RqCont dphi L (b t) k i o))
        (observationLaw M)) := by
  dsimp only
  by_cases hi0 : i = 0
  · subst i
    simp only [pooledQ, if_true, RqCont, true_or, add_zero, sub_self, sub_zero, mul_zero]
    simp only [integral_zero]
    exact ⟨hasDerivAt_const (0 : ℝ) (0 : ℝ),
      Eventually.of_forall (fun _ => integrable_zero _ _ _)⟩
  · let a : RegularIndex L := ⟨(k,i), k.isLt.le, by omega, hi⟩
    have hw : ∀ᶠ t : ℝ in 𝓝 0,
        Measurable (fun x => (trueNuisance M L + t • del).gamma g x *
          nuValue M (trueNuisance M L + t • del) k i x) ∧
        ∀ᵐ x ∂xLaw M, ‖(trueNuisance M L + t • del).gamma g x *
          nuValue M (trueNuisance M L + t • del) k i x‖ ≤ |M.yMin| + |M.yMax| := by
      obtain ⟨r, hr, hp⟩ := hd.admissible
      filter_upwards [continuousAt_id.abs.eventually_lt_const (by simpa using hr)] with t ht
      have he := hp t ht
      have hgm := he.2.2.2.2.2.2.2.2.2.2.2.2.2.1 g
      have hnm := continuous_admissible_nuValue_measurable M L _ he k i
      refine ⟨by fun_prop, ?_⟩
      filter_upwards [he.2.2.2.2.2.2.2.2.2.2.2.2.1 g,
        continuous_admissible_nuValue_abs_bound M L _ he k i] with x hg hn
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hg.1]
      calc
        _ ≤ 1 * (|M.yMin| + |M.yMax|) :=
          mul_le_mul hg.2 hn (abs_nonneg _) (by norm_num)
        _ = _ := one_mul _
    have hp := population_continuous_weighted_pooled_policy_telescope M h phi dphi
      hphi hDiff hDerivative L hOrder cpi hov del hd a
      (fun t x => (trueNuisance M L + t • del).gamma g x *
        nuValue M (trueNuisance M L + t • del) k i x)
      (|M.yMin| + |M.yMax|) (by positivity) hw
    dsimp only at hp
    simpa only [a, pooledQ, if_neg hi0, if_neg (show ¬ L.l k < i by omega), shareValue,
      RqCont] using hp

-- Both signed policy channels cancel in the actual product score, with
-- eventual integrability retained for finite sums and subsequent telescopes.
-- @node: population_continuous_band_policy_product_telescope
/-- Under [threshold crossing](hyp:h), [a valid policy map](hyp:hphi),
[policy differentiability](hyp:hDiff), [a bounded Lipschitz policy derivative](hyp:hDerivative),
[invariant baseline and policy level ordering](hyp:hOrder), [policy overlap](hyp:hov),
and [an admissible joint direction from truth](hyp:hd), for [a band index below the
level's band count](hyp:hj), [the product-score difference from freezing instrument
propensities and pooling shares at truth has expected derivative zero at zero and
is integrable for every sufficiently small perturbation](goal). -/
lemma population_continuous_band_policy_product_telescope
    (h : ThresholdCrossing M) (phi dphi : Z → X → ℝ → ℝ)
    (hphi : IsPolicyMap phi) (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : PolicyOverlap M L cpi) (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del))
    (k : Fin L.K) (j : ℕ) (hj : j < L.l k) :
    let e := fun t : ℝ => trueNuisance M L + t • del
    let b := fun t => {e t with
      prop := (trueNuisance M L).prop,
      share := (trueNuisance M L).share}
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z,
      psiProd M phi dphi L (e t) k (j+1) o -
        psiProd M phi dphi L (b t) k (j+1) o ∂observationLaw M) 0 0 ∧
    (∀ᶠ t : ℝ in 𝓝 0, Integrable (fun o : Obs X Z =>
      psiProd M phi dphi L (e t) k (j+1) o -
        psiProd M phi dphi L (b t) k (j+1) o) (observationLaw M)) := by
  dsimp only
  let e := fun t : ℝ => trueNuisance M L + t • del
  let b := fun t => {e t with
    prop := (trueNuisance M L).prop,
    share := (trueNuisance M L).share}
  have hg : k.val ≤ L.K ∧ 1 ≤ j+1 ∧ j+1 ≤ L.l k := by omega
  let g : RegularIndex L := ⟨(k,j+1),hg⟩
  let f := fun (t : ℝ) (i : ℕ) (o : Obs X Z) =>
    ((e t).gamma g o.1 * nuValue M (e t) k i o.1) *
      (pooledQ phi L (e t) k i o.1 + RqCont dphi L (e t) k i o -
        pooledQ phi L (b t) k i o.1 - RqCont dphi L (b t) k i o)
  have hp := population_continuous_band_endpoint_policy_telescope M h phi dphi
    hphi hDiff hDerivative L hOrder cpi hov del hd g k (j+1) (by omega)
  have hm := population_continuous_band_endpoint_policy_telescope M h phi dphi
    hphi hDiff hDerivative L hOrder cpi hov del hd g k j hj.le
  have hid (t : ℝ) : (fun o : Obs X Z =>
      psiProd M phi dphi L (e t) k (j+1) o - psiProd M phi dphi L (b t) k (j+1) o) =
      (fun o => f t (j+1) o - f t j o) := by
    funext o
    rw [continuous_band_policy_product_difference]
    simp only [f, g, regularValue, dif_pos hg]
    rfl
  have hs : HasDerivAt (fun t : ℝ =>
      (∫ o, f t (j+1) o ∂observationLaw M) - ∫ o, f t j o ∂observationLaw M) 0 0 := by
    simpa only [sub_zero] using hp.1.fun_sub hm.1
  refine ⟨hs.congr_of_eventuallyEq ?_, ?_⟩
  · filter_upwards [hp.2, hm.2] with t hit him
    rw [hid t]
    exact integral_sub hit him
  · filter_upwards [hp.2, hm.2] with t hit him
    rw [hid t]
    exact hit.sub' him

-- The finite sum retains both the derivative and the integrability needed by
-- the next telescope in the total continuous score.
-- @node: population_continuous_regular_sum_policy_telescope
/-- Under [threshold crossing](hyp:h), [a valid policy map](hyp:hphi),
[policy differentiability](hyp:hDiff), [a bounded Lipschitz policy derivative](hyp:hDerivative),
[invariant baseline and policy level ordering](hyp:hL), [policy overlap](hyp:hov),
and [an admissible joint direction from truth](hyp:hd), [the sum over all regular
bands of product-score differences from freezing instrument propensities and
pooling shares has expected derivative zero at zero and is integrable for every
sufficiently small perturbation](goal). -/
lemma population_continuous_regular_sum_policy_telescope
    (h : ThresholdCrossing M) (phi dphi : Z → X → ℝ → ℝ)
    (hphi : IsPolicyMap phi) (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : PolicyOverlap M L cpi)
    (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del)) :
    let e := fun t : ℝ => trueNuisance M L + t • del
    let b := fun t => {e t with
      prop := (trueNuisance M L).prop, share := (trueNuisance M L).share}
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z,
      ∑ k : Fin L.K, ∑ j ∈ Finset.range (L.l k),
        (psiProd M phi dphi L (e t) k (j+1) o -
          psiProd M phi dphi L (b t) k (j+1) o) ∂observationLaw M) 0 0 ∧
    (∀ᶠ t : ℝ in 𝓝 0, Integrable (fun o : Obs X Z =>
      ∑ k : Fin L.K, ∑ j ∈ Finset.range (L.l k),
        (psiProd M phi dphi L (e t) k (j+1) o -
          psiProd M phi dphi L (b t) k (j+1) o)) (observationLaw M)) := by
  dsimp only
  let e := fun t : ℝ => trueNuisance M L + t • del
  let b := fun t => {e t with
    prop := (trueNuisance M L).prop, share := (trueNuisance M L).share}
  let f := fun (t : ℝ) (k : Fin L.K) (j : ℕ) (o : Obs X Z) =>
    psiProd M phi dphi L (e t) k (j+1) o - psiProd M phi dphi L (b t) k (j+1) o
  have hcomp (k : Fin L.K) (j : ℕ) (hj : j ∈ Finset.range (L.l k)) :
      HasDerivAt (fun t : ℝ => ∫ o, f t k j o ∂observationLaw M) 0 0 ∧
      ∀ᶠ t : ℝ in 𝓝 0, Integrable (f t k j) (observationLaw M) := by
    have hj' := Finset.mem_range.mp hj
    exact population_continuous_band_policy_product_telescope M h phi dphi hphi hDiff
      hDerivative L hL cpi hov del hd k j hj'
  have hi : ∀ᶠ t : ℝ in 𝓝 0, ∀ k : Fin L.K, ∀ j ∈ Finset.range (L.l k),
      Integrable (f t k j) (observationLaw M) := by
    apply (Filter.eventually_all).mpr
    intro k
    exact (Finset.eventually_all _).mpr (fun j hj => (hcomp k j hj).2)
  have hdSum : HasDerivAt (fun t : ℝ => ∑ k : Fin L.K,
      ∑ j ∈ Finset.range (L.l k), ∫ o, f t k j o ∂observationLaw M) 0 0 := by
    have hdk (k : Fin L.K) : HasDerivAt (fun t : ℝ =>
        ∑ j ∈ Finset.range (L.l k), ∫ o, f t k j o ∂observationLaw M) 0 0 := by
      simpa only [Finset.sum_const_zero] using
        HasDerivAt.fun_sum (fun j hj => (hcomp k j hj).1)
    simpa only [Finset.sum_const_zero] using
      HasDerivAt.fun_sum (fun k (_ : k ∈ Finset.univ) => hdk k)
  refine ⟨hdSum.congr_of_eventuallyEq ?_, ?_⟩
  · filter_upwards [hi] with t ht
    symm
    rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ (ht k))]
    apply Finset.sum_congr rfl
    intro k _
    exact (integral_finsetSum _ (ht k)).symm
  · filter_upwards [hi] with t ht
    exact integrable_finsetSum _ (fun k _ => integrable_finsetSum _ (ht k))


end Papers.TbsPrteOptimalTransport

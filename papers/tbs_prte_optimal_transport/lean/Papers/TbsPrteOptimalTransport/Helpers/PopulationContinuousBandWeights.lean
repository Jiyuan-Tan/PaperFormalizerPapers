module
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationContinuousBandAssembly
/-! Regular product and final-bin weight directions of the continuous population score. -/
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

-- @node: population_continuous_band_correction_weighted_zero
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
[a measurable policy derivative evaluated at baseline propensities](hyp:hdphi),
[covariate-invariant level ordering](hyp:hL), [baseline overlap](hyp:hov),
[policy overlap](hyp:hpol), [a nonfinal bin](hyp:hk), [a band index below its
policy-level count](hyp:hj), [measurable lower](hyp:ha) and [upper boundaries](hyp:hb),
[locally bounded boundary densities](hyp:hd), and [no lower-endpoint atom](hyp:h0),
take [a measurable covariate weight](hyp:hw). If [the weighted band mean contrast](hyp:hbase),
[both weighted treated-band residuals](hyp:hJ), [both lower-boundary-weighted
indicator residuals](hyp:hMa), [both upper-boundary-weighted indicator residuals](hyp:hMb),
[the weighted lower baseline propensity term](hyp:hl), [the weighted upper baseline
propensity term](hyp:hh), [the weighted lower policy residual term](hyp:hql), and
[the weighted upper policy residual term](hyp:hqh) are integrable,
[the weighted difference between the population band score and its band mean
contrast is integrable and has expectation zero](goal). -/
lemma population_continuous_band_correction_weighted_zero
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (phi dphi : Z → X → ℝ → ℝ)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L) (cpi : ℝ)
    (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (k j : ℕ) (hk : k < L.K) (hj : j < L.l k)
    (ha : Measurable (bandBoundary M L k j))
    (hb : Measurable (bandBoundary M L k (j + 1)))
    (hd : BoundaryDensitiesBounded M L) (h0 : NoAtomAtLowerEndpoint M L)
    (w : X → ℝ) (hw : Measurable w)
    (hbase : Integrable (fun o : Obs X Z => w o.1 *
      contJ L (trueNuisance M L) k j o.1) (observationLaw M))
    (hJ : ∀ plus, Integrable (fun o : Obs X Z => w o.1 *
      IFJ M L (trueNuisance M L) plus k j o) (observationLaw M))
    (hMa : ∀ plus, Integrable (fun o : Obs X Z =>
      (w o.1 * bandBoundary M L k j o.1) *
      IFM M L (trueNuisance M L) plus k j o) (observationLaw M))
    (hMb : ∀ plus, Integrable (fun o : Obs X Z =>
      (w o.1 * bandBoundary M L k (j + 1) o.1) *
      IFM M L (trueNuisance M L) plus k (j + 1) o) (observationLaw M))
    (hl : Integrable (fun o : Obs X Z => (w o.1 *
      alphaLow M L (trueNuisance M L) k j o.1) *
      RpCont L (trueNuisance M L) k o) (observationLaw M))
    (hh : Integrable (fun o : Obs X Z => (w o.1 *
      alphaHigh M L (trueNuisance M L) k j o.1) *
      RpCont L (trueNuisance M L) (k + 1) o) (observationLaw M))
    (hql : Integrable (fun o : Obs X Z => (w o.1 * bandBoundary M L k j o.1) *
      RqCont dphi L (trueNuisance M L) k j o) (observationLaw M))
    (hqh : Integrable (fun o : Obs X Z => (w o.1 * bandBoundary M L k (j + 1) o.1) *
      RqCont dphi L (trueNuisance M L) k (j + 1) o) (observationLaw M)) :
    Integrable (fun o : Obs X Z => w o.1 *
      (contScoreComponents M phi dphi L (trueNuisance M L) k j o -
        contJ L (trueNuisance M L) k j o.1)) (observationLaw M) ∧
    (∫ o : Obs X Z, w o.1 *
      (contScoreComponents M phi dphi L (trueNuisance M L) k j o -
        contJ L (trueNuisance M L) k j o.1) ∂observationLaw M) = 0 := by
  obtain ⟨hs, hm⟩ := population_continuous_band_component_weighted_mean M h he
    phi dphi hdphi L hL cpi hov hpol k j hk hj ha hb hd h0 w hw
    hbase hJ hMa hMb hl hh hql hqh
  simp_rw [mul_sub]
  refine ⟨hs.sub' hbase, ?_⟩
  rw [integral_sub hs hbase, hm, sub_self]

-- @node: population_continuous_band_product_weight_orthogonality
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
[a measurable policy derivative evaluated at baseline propensities](hyp:hdphi),
[covariate-invariant level ordering](hyp:hL), [baseline overlap](hyp:hov),
[policy overlap](hyp:hpol), [a nonfinal bin](hyp:hk), [a band index below its
policy-level count](hyp:hj), [measurable lower](hyp:ha) and [upper boundaries](hyp:hb),
[locally bounded boundary densities](hyp:hd), and [no lower-endpoint atom](hyp:h0),
consider [a perturbation direction measurable at the next policy index](hyp:hw).
If [the population product score is integrable](hyp:hprod) and, weighted by that
direction, [the band mean contrast](hyp:hbase), [both treated-band residuals](hyp:hJ),
[both lower-boundary indicator residual terms](hyp:hMa),
[both upper-boundary indicator residual terms](hyp:hMb),
[the lower baseline propensity term](hyp:hl), [the upper baseline propensity term](hyp:hh),
[the lower policy residual term](hyp:hql), and [the upper policy residual term](hyp:hqh)
are integrable, [the population mean product score has derivative zero at zero
along the additive perturbation of the policy-union probability nuisance](goal). -/
lemma population_continuous_band_product_weight_orthogonality
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (phi dphi : Z → X → ℝ → ℝ)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L) (cpi : ℝ)
    (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (k j : ℕ) (hk : k < L.K) (hj : j < L.l k)
    (ha : Measurable (bandBoundary M L k j))
    (hb : Measurable (bandBoundary M L k (j + 1)))
    (hd : BoundaryDensitiesBounded M L) (h0 : NoAtomAtLowerEndpoint M L)
    (d : RegularIndex L → X → ℝ)
    (hw : Measurable (d ⟨(k, j + 1), hk.le, by dsimp only; omega, by dsimp only; omega⟩))
    (hprod : Integrable (psiProd M phi dphi L (trueNuisance M L) k (j + 1))
      (observationLaw M))
    (hbase : Integrable (fun o : Obs X Z => d ⟨(k, j + 1), hk.le, by dsimp only; omega, by dsimp only; omega⟩ o.1 *
      contJ L (trueNuisance M L) k j o.1) (observationLaw M))
    (hJ : ∀ plus, Integrable (fun o : Obs X Z => d ⟨(k, j + 1), hk.le, by dsimp only; omega, by dsimp only; omega⟩ o.1 *
      IFJ M L (trueNuisance M L) plus k j o) (observationLaw M))
    (hMa : ∀ plus, Integrable (fun o : Obs X Z =>
      (d ⟨(k, j + 1), hk.le, by dsimp only; omega, by dsimp only; omega⟩ o.1 * bandBoundary M L k j o.1) *
      IFM M L (trueNuisance M L) plus k j o) (observationLaw M))
    (hMb : ∀ plus, Integrable (fun o : Obs X Z =>
      (d ⟨(k, j + 1), hk.le, by dsimp only; omega, by dsimp only; omega⟩ o.1 * bandBoundary M L k (j + 1) o.1) *
      IFM M L (trueNuisance M L) plus k (j + 1) o) (observationLaw M))
    (hl : Integrable (fun o : Obs X Z => (d ⟨(k, j + 1), hk.le, by dsimp only; omega, by dsimp only; omega⟩ o.1 *
      alphaLow M L (trueNuisance M L) k j o.1) *
      RpCont L (trueNuisance M L) k o) (observationLaw M))
    (hh : Integrable (fun o : Obs X Z => (d ⟨(k, j + 1), hk.le, by dsimp only; omega, by dsimp only; omega⟩ o.1 *
      alphaHigh M L (trueNuisance M L) k j o.1) *
      RpCont L (trueNuisance M L) (k + 1) o) (observationLaw M))
    (hql : Integrable (fun o : Obs X Z => (d ⟨(k, j + 1), hk.le, by dsimp only; omega, by dsimp only; omega⟩ o.1 * bandBoundary M L k j o.1) *
      RqCont dphi L (trueNuisance M L) k j o) (observationLaw M))
    (hqh : Integrable (fun o : Obs X Z => (d ⟨(k, j + 1), hk.le, by dsimp only; omega, by dsimp only; omega⟩ o.1 * bandBoundary M L k (j + 1) o.1) *
      RqCont dphi L (trueNuisance M L) k (j + 1) o) (observationLaw M)) :
    HasDerivAt (fun t : ℝ => ∫ o, psiProd M phi dphi L
      {trueNuisance M L with gamma := fun a x =>
        (trueNuisance M L).gamma a x + t * d a x}
      k (j + 1) o ∂observationLaw M) 0 0 := by
  have hidx : k ≤ L.K ∧ 1 ≤ j + 1 ∧ j + 1 ≤ L.l k := ⟨hk.le, by omega, by omega⟩
  let a : RegularIndex L := ⟨(k, j + 1), hk.le, by dsimp only; omega, by dsimp only; omega⟩
  obtain ⟨hi, hz⟩ := population_continuous_band_correction_weighted_zero M h he
    phi dphi hdphi L hL cpi hov hpol k j hk hj ha hb hd h0 (d a) hw
    hbase hJ hMa hMb hl hh hql hqh
  have hp := product_score_weight_path (observationLaw M)
    (fun o : Obs X Z => (trueNuisance M L).gamma a o.1)
    (fun o : Obs X Z => d a o.1)
    (fun o => contScoreComponents M phi dphi L (trueNuisance M L) k j o)
    (fun o => contJ L (trueNuisance M L) k j o.1)
    (fun o => indicator (o.2.1 ∈ policyUnion L k (j + 1)))
    (by
      change Integrable (fun o => psiProd M phi dphi L (trueNuisance M L) k (j + 1) o) _ at hprod
      simpa only [psiProd, regularValue, dif_pos hidx, Nat.add_sub_cancel] using hprod) hi hz
  have heq : (fun t : ℝ => ∫ o, psiProd M phi dphi L
      {trueNuisance M L with gamma := fun b x =>
        (trueNuisance M L).gamma b x + t * d b x}
      k (j + 1) o ∂observationLaw M) =
      (fun _ : ℝ => ∫ o, psiProd M phi dphi L (trueNuisance M L)
        k (j + 1) o ∂observationLaw M) := by
    funext t
    have hs : ∀ o, contScoreComponents M phi dphi L
        {trueNuisance M L with gamma := fun b x =>
          (trueNuisance M L).gamma b x + t * d b x} k j o =
        contScoreComponents M phi dphi L (trueNuisance M L) k j o := fun _ => rfl
    have hJ' : ∀ x, contJ L
        {trueNuisance M L with gamma := fun b x =>
          (trueNuisance M L).gamma b x + t * d b x} k j x =
        contJ L (trueNuisance M L) k j x := fun _ => rfl
    simpa only [psiProd, regularValue, dif_pos hidx, Nat.add_sub_cancel,
      hs, hJ'] using hp t
  rw [heq]
  exact hasDerivAt_const 0 _

-- The finite sum is unaffected: only the final-bin propensity correction moves.
-- @node: continuous_total_tail_weight_path
/-- With [a positive baseline-level count](hyp:hK), [adding a scalar multiple of
a covariate direction to the tail probability nuisance changes the total continuous
score by minus that scalar times the lower outcome endpoint times the direction
times the final-bin baseline propensity residual](goal). -/
lemma continuous_total_tail_weight_path (phi dphi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (hK : LevelCountPos L.K) (eta : NuisanceCont L)
    (d : X → ℝ) (o : Obs X Z) (t : ℝ) :
    psiCont M phi dphi L hK o
      {eta with gammaTail := fun x => eta.gammaTail x + t * d x} =
    psiCont M phi dphi L hK o eta -
      t * (M.yMin * (d o.1 * RpCont L eta L.K o)) := by
  have hk : L.K ≠ 0 := by unfold LevelCountPos at hK; omega
  have hf : ∀ k, psiFullProd L
      {eta with gammaTail := fun x => eta.gammaTail x + t * d x} k o =
      psiFullProd L eta k o := fun _ => rfl
  have hr : ∀ k j, psiProd M phi dphi L
      {eta with gammaTail := fun x => eta.gammaTail x + t * d x} k j o =
      psiProd M phi dphi L eta k j o := fun _ _ => rfl
  simp only [psiCont, hf, hr, commonTailScore, RpCont, if_neg hk, div_eq_mul_inv]
  ring

-- @node: population_continuous_total_tail_weight_integral_path
/-- Under [threshold crossing](hyp:h), [a positive baseline-level count](hyp:hK),
and [covariate-invariant baseline and policy level ordering](hyp:hOrder), for
[a measurable tail-weight perturbation direction](hyp:hd), if
[the direction times the final-bin baseline propensity residual is integrable](hyp:hi)
and [the unperturbed total continuous score is integrable](hyp:hbase),
[adding any scalar multiple of that direction to the population tail probability
nuisance leaves the expected total score unchanged](goal). -/
lemma population_continuous_total_tail_weight_integral_path
    (h : ThresholdCrossing M) (phi dphi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (d : X → ℝ) (hd : Measurable d)
    (hi : Integrable (fun o : Obs X Z => d o.1 *
      RpCont L (trueNuisance M L) L.K o) (observationLaw M))
    (hbase : Integrable (fun o => psiCont M phi dphi L hK o (trueNuisance M L))
      (observationLaw M)) (t : ℝ) :
    (∫ o, psiCont M phi dphi L hK o
      {trueNuisance M L with gammaTail := fun x =>
        (trueNuisance M L).gammaTail x + t * d x} ∂observationLaw M) =
    ∫ o, psiCont M phi dphi L hK o (trueNuisance M L) ∂observationLaw M := by
  have hz := population_RpCont_weighted_integral_zero M h
    (policyProp phi M.prop) L hOrder L.K d hd hi
  simp_rw [continuous_total_tail_weight_path]
  rw [integral_sub hbase ((hi.const_mul M.yMin).const_mul t),
    integral_const_mul, integral_const_mul, hz, mul_zero, mul_zero, sub_zero]

-- @node: population_continuous_total_tail_weight_orthogonality
/-- Under [threshold crossing](hyp:h), [a positive baseline-level count](hyp:hK),
and [covariate-invariant baseline and policy level ordering](hyp:hOrder), with
[a measurable tail-weight perturbation direction](hyp:hd),
[an integrable product of that direction and the final-bin baseline propensity residual](hyp:hi),
and [an integrable population total continuous score](hyp:hbase),
[the expected total score has derivative zero at zero along the additive
perturbation of the tail probability nuisance](goal). -/
lemma population_continuous_total_tail_weight_orthogonality
    (h : ThresholdCrossing M) (phi dphi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (d : X → ℝ) (hd : Measurable d)
    (hi : Integrable (fun o : Obs X Z => d o.1 *
      RpCont L (trueNuisance M L) L.K o) (observationLaw M))
    (hbase : Integrable (fun o => psiCont M phi dphi L hK o (trueNuisance M L))
      (observationLaw M)) :
    HasDerivAt (fun t : ℝ => ∫ o, psiCont M phi dphi L hK o
      {trueNuisance M L with gammaTail := fun x =>
        (trueNuisance M L).gammaTail x + t * d x} ∂observationLaw M) 0 0 := by
  have heq : (fun t : ℝ => ∫ o, psiCont M phi dphi L hK o
      {trueNuisance M L with gammaTail := fun x =>
        (trueNuisance M L).gammaTail x + t * d x} ∂observationLaw M) =
      (fun _ : ℝ => ∫ o, psiCont M phi dphi L hK o (trueNuisance M L)
        ∂observationLaw M) := by
    funext t
    exact population_continuous_total_tail_weight_integral_path M h phi dphi
      L hK hOrder d hd hi hbase t
  rw [heq]
  exact hasDerivAt_const 0 _

end Papers.TbsPrteOptimalTransport

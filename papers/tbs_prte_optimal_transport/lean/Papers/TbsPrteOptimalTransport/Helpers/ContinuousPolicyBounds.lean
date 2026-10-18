module
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousPropensityBounds
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousTotalBandWeights
/-! Overlap envelopes and unconditional assembly of continuous band moments. -/
public section
set_option linter.style.openClassical false
set_option linter.unusedSectionVars false

set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: population_RqCont_integrable_of_integrable_weight
/-- Under [the threshold-crossing model](hyp:h), suppose [the policy derivative
evaluated at the true propensity is measurable in instrument and covariates](hyp:hdphi),
[the derivative is uniformly bounded and Lipschitz on the unit interval](hyp:hDerivative),
[baseline and policy level ordering is invariant](hyp:hL), and [policy overlap
holds with floor cpi](hyp:hpol). For [a level index no greater than the total
number of levels](hyp:hk) and [a measurable](hyp:hw), [integrable covariate
weight](hyp:hwi), [the weighted continuous policy propensity residual at the truth
is integrable under the observation law](goal). -/
lemma population_RqCont_integrable_of_integrable_weight
    (h : ThresholdCrossing M) (dphi : Z → X → ℝ → ℝ)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L)
    (cpi : ℝ) (hpol : PolicyOverlap M L cpi)
    (k j : ℕ) (hk : k ≤ L.K)
    (w : X → ℝ) (hw : Measurable w) (hwi : Integrable w (xLaw M)) :
    Integrable (fun o : Obs X Z => w o.1 *
      RqCont dphi L (trueNuisance M L) k j o) (observationLaw M) := by
  by_cases hj : 1 ≤ j ∧ j ≤ L.l k
  · have hj0 : ¬ (j = 0 ∨ L.l k < j) := by omega
    have hi : k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k := ⟨hk, hj⟩
    let tau : X → ℝ := fun x => (levelSetProb M L).2 k j x
    have htau : Measurable tau :=
      population_instrument_set_probability_measurable M (L.T k j)
    have hden x : cpi ≤ tau x := hpol.2 x k j hk hj.1 hj.2
      (ordered_policy_level_nonempty M q L hL k j hk hj.1 hj.2)
    have hsel : Measurable (fun o : Obs X Z => indicator (o.2.1 ∈ L.T k j)) := by
      unfold indicator
      exact Measurable.ite ((L.T k j).finite_toSet.measurableSet.preimage
        measurable_snd.fst) measurable_const measurable_const
    have heq o : RqCont dphi L (trueNuisance M L) k j o =
        (tau o.1)⁻¹ * indicator (o.2.1 ∈ L.T k j) *
          dphi o.2.1 o.1 (M.prop o.2.1 o.1) * (o.2.2.1 - M.prop o.2.1 o.1) := by
      rw [population_RqCont_eq_RqBin, population_RqBin_residual_factorization]
      simp only [if_neg hj0, regularValue, dif_pos hi, eta0Bin, tau]
    have hm : Measurable (RqCont dphi L (trueNuisance M L) k j) := by
      first | fun_prop | skip
      change Measurable (fun o : Obs X Z => RqCont dphi L (trueNuisance M L) k j o)
      simp_rw [heq]
      exact ((((htau.comp measurable_fst).inv.mul hsel).mul
        (hdphi.comp (measurable_snd.fst.prodMk measurable_fst))).mul
        (measurable_snd.snd.fst.sub
          (h.2.1.comp (measurable_snd.fst.prodMk measurable_fst))))
    have hobs := M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY))
    have ht : ∀ᵐ o : Obs X Z ∂observationLaw M, ‖o.2.2.1‖ ≤ 1 := by
      apply (ae_map_iff hobs.aemeasurable
        (measurableSet_le (by fun_prop) measurable_const)).mpr
      exact Eventually.of_forall (fun s => by
        rcases M.rangeW s with hs | hs <;> simp [hs])
    obtain ⟨B, Lip, hB, hLip, hb⟩ := hDerivative
    have hbound : ∀ᵐ o : Obs X Z ∂observationLaw M,
        ‖RqCont dphi L (trueNuisance M L) k j o‖ ≤ cpi⁻¹ * B * 2 := by
      filter_upwards [ht] with o hto
      have hpos : 0 < tau o.1 := hpol.1.trans_le (hden o.1)
      have hd : ‖dphi o.2.1 o.1 (M.prop o.2.1 o.1)‖ ≤ B :=
        (hb o.2.1 o.1 (M.prop o.2.1 o.1) (M.prop o.2.1 o.1)
          (M.rangeProp o.2.1 o.1) (M.rangeProp o.2.1 o.1)).1
      have hp : ‖M.prop o.2.1 o.1‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (M.rangeProp _ _).1]
        exact (M.rangeProp _ _).2
      have hdiff : ‖o.2.2.1 - M.prop o.2.1 o.1‖ ≤ 2 :=
        (norm_sub_le _ _).trans (by linarith)
      have hind : ‖indicator (o.2.1 ∈ L.T k j)‖ ≤ 1 := by
        unfold indicator; split_ifs <;> norm_num
      rw [heq, norm_mul, norm_mul, norm_mul, norm_inv,
        Real.norm_eq_abs, abs_of_pos hpos]
      have hcpi : 0 < cpi := hpol.1
      calc
        _ ≤ cpi⁻¹ * 1 * B * 2 := by
          gcongr <;> first | assumption | positivity | exact hden o.1
        _ = _ := by ring
    have hmap : (observationLaw M).map Prod.fst = xLaw M := by
      simpa only [observationLaw, xLaw, Function.comp_def] using
        Measure.map_map measurable_fst hobs
    have hwi' : Integrable (fun o : Obs X Z => w o.1) (observationLaw M) := by
      apply (integrable_map_measure hw.aestronglyMeasurable measurable_fst.aemeasurable).mp
      rwa [hmap]
    simpa only [mul_comm] using hwi'.bdd_mul hm.aestronglyMeasurable hbound
  · have hz o : RqCont dphi L (trueNuisance M L) k j o = 0 := by
      simp [RqCont, show j = 0 ∨ L.l k < j by omega]
    simp_rw [hz, mul_zero]
    exact integrable_zero _ _ _

-- All residual integrability follows from the construction and overlap.
-- @node: population_continuous_band_mean_from_overlap
/-- Under [the structural assumptions](hyp:h) and [known outcome endpoints](hyp:he),
suppose [the policy derivative at the true propensity is measurable](hyp:hdphi),
[the derivative is uniformly bounded and Lipschitz on the unit interval](hyp:hDerivative),
[the policy preserves level ordering](hyp:hL), [baseline overlap](hyp:hov) and
[policy overlap](hyp:hpol) hold with floor cpi, [the level index is below the total
number of levels](hyp:hk), and [the band index is below the number of bands](hyp:hj).
If [the lower band boundary](hyp:ha) and [the upper band boundary](hyp:hb) are
measurable, [boundary densities are bounded](hyp:hd), [there is no atom at the
lower endpoint](hyp:h0), and [the covariate weight is measurable](hyp:hw) and
[integrable](hyp:hwi), then [the weighted continuous band score at the truth is
integrable and its mean equals the weighted true band regression contrast mean](goal). -/
lemma population_continuous_band_mean_from_overlap
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (phi dphi : Z → X → ℝ → ℝ)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (k j : ℕ) (hk : k < L.K) (hj : j < L.l k)
    (ha : Measurable (bandBoundary M L k j))
    (hb : Measurable (bandBoundary M L k (j + 1)))
    (hd : BoundaryDensitiesBounded M L) (h0 : NoAtomAtLowerEndpoint M L)
    (w : X → ℝ) (hw : Measurable w) (hwi : Integrable w (xLaw M)) :
    Integrable (fun o : Obs X Z => w o.1 *
      contScoreComponents M phi dphi L (trueNuisance M L) k j o) (observationLaw M) ∧
    (∫ o : Obs X Z, w o.1 *
      contScoreComponents M phi dphi L (trueNuisance M L) k j o ∂observationLaw M) =
      ∫ o : Obs X Z, w o.1 * contJ L (trueNuisance M L) k j o.1 ∂observationLaw M := by
  apply population_continuous_band_mean_without_propensity_integrability M h he phi dphi
    hdphi L hL cpi hov hpol k j hk hj ha hb hd h0 w hw hwi
  · exact population_RqCont_integrable_of_integrable_weight M h.2.2.2.1 dphi hdphi
      hDerivative (policyProp phi M.prop) L hL cpi hpol k j hk.le
      (fun x => w x * bandBoundary M L k j x) (hw.mul ha)
      (population_bandBoundary_weight_integrable M h he (policyProp phi M.prop)
        L hL k j hk hj.le ha w hwi)
  · exact population_RqCont_integrable_of_integrable_weight M h.2.2.2.1 dphi hdphi
      hDerivative (policyProp phi M.prop) L hL cpi hpol k (j + 1) hk.le
      (fun x => w x * bandBoundary M L k (j + 1) x) (hw.mul hb)
      (population_bandBoundary_weight_integrable M h he (policyProp phi M.prop)
        L hL k (j + 1) hk (by omega) hb w hwi)

-- @node: population_continuous_band_product_mean_from_overlap
/-- Under [the structural assumptions](hyp:h) and [known outcome endpoints](hyp:he),
suppose [the policy derivative at the true propensity is measurable](hyp:hdphi),
[the derivative is uniformly bounded and Lipschitz on the unit interval](hyp:hDerivative),
[the policy preserves level ordering](hyp:hL), [baseline overlap](hyp:hov) and
[policy overlap](hyp:hpol) hold with floor cpi, [the level index is below the total
number of levels](hyp:hk), and [the product-score band index is at least one](hyp:hj)
and [no greater than the number of bands](hyp:hjK). If [the boundary at the
preceding index](hyp:ha) and [the boundary at this index](hyp:hb) are measurable,
[boundary densities are bounded](hyp:hd), [there is no atom at the lower
endpoint](hyp:h0), and [the covariate weight is measurable](hyp:hw) and
[integrable](hyp:hwi), then [the weighted true band product score is integrable
and its mean equals the mean of the preceding band regression contrast times
the covariate weight and the true band assignment probability](goal). -/
lemma population_continuous_band_product_mean_from_overlap
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (phi dphi : Z → X → ℝ → ℝ)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j) (hjK : j ≤ L.l k)
    (ha : Measurable (bandBoundary M L k (j - 1)))
    (hb : Measurable (bandBoundary M L k j))
    (hd : BoundaryDensitiesBounded M L) (h0 : NoAtomAtLowerEndpoint M L)
    (w : X → ℝ) (hw : Measurable w) (hwi : Integrable w (xLaw M)) :
    Integrable (fun o : Obs X Z => w o.1 *
      psiProd M phi dphi L (trueNuisance M L) k j o) (observationLaw M) ∧
    (∫ o : Obs X Z, w o.1 *
      psiProd M phi dphi L (trueNuisance M L) k j o ∂observationLaw M) =
      ∫ o : Obs X Z, (w o.1 * gamma M L k j o.1) *
        contJ L (trueNuisance M L) k (j - 1) o.1 ∂observationLaw M := by
  have hg : Measurable (gamma M L k j) :=
    population_instrument_set_probability_measurable M (policyUnion L k j)
  have hgb : ∀ᵐ x ∂xLaw M, ‖gamma M L k j x‖ ≤ 1 := by
    apply Eventually.of_forall
    intro x
    have hr := population_instrument_set_probability_range M (policyUnion L k j) x
    change gamma M L k j x ∈ Icc (0 : ℝ) 1 at hr
    rw [Real.norm_eq_abs, abs_of_nonneg hr.1]
    exact hr.2
  have iwg : Integrable (fun x => w x * gamma M L k j x) (xLaw M) := by
    simpa only [mul_comm] using hwi.bdd_mul hg.aestronglyMeasurable hgb
  obtain ⟨hs, hm⟩ := population_continuous_band_mean_from_overlap M h he phi dphi hdphi
    hDerivative L hL cpi hov hpol k (j - 1) hk (by omega) ha
    (by simpa only [Nat.sub_add_cancel hj] using hb) hd h0
    (fun x => w x * gamma M L k j x) (hw.mul hg) iwg
  have ib := population_contJ_weighted_integrable M h he (policyProp phi M.prop)
    L hL k (j - 1) hk (by omega) ha
    (by simpa only [Nat.sub_add_cancel hj] using hb) w hw hwi
  obtain ⟨hi, hz⟩ := population_continuous_band_product_assignment_zero M h.2.2.2.1
    (policyProp phi M.prop) L hL k j hk hj hjK ha hb w hw ib
  have hgamma x : regularValue (trueNuisance M L).gamma k j x = gamma M L k j x := by
    simp [regularValue, trueNuisance, hk.le, hj, hjK]
  simp only [hgamma] at hi hz
  simp only [psiProd, hgamma, mul_add, ← mul_assoc]
  refine ⟨hs.fun_add hi, ?_⟩
  rw [integral_add hs hi, hz, add_zero]
  exact hm

-- @node: population_continuous_band_correction_zero_from_overlap
/-- Under [the structural assumptions](hyp:h) and [known outcome endpoints](hyp:he),
assume [the policy derivative at the true propensity is measurable](hyp:hdphi),
[the derivative is uniformly bounded and Lipschitz on the unit interval](hyp:hDerivative),
[the policy preserves level ordering](hyp:hL), [baseline overlap](hyp:hov) and
[policy overlap](hyp:hpol) hold with floor cpi, [the level index is below the total
number of levels](hyp:hk), and [the band index is below the number of bands](hyp:hj).
With [a measurable lower boundary](hyp:ha), [a measurable upper boundary](hyp:hb),
[bounded boundary densities](hyp:hd), [no atom at the lower endpoint](hyp:h0),
and [a measurable](hyp:hw), [integrable covariate weight](hyp:hwi), [the weighted
difference between the true continuous band score and the true band regression
contrast is integrable and has population mean zero](goal). -/
lemma population_continuous_band_correction_zero_from_overlap
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (phi dphi : Z → X → ℝ → ℝ)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (k j : ℕ) (hk : k < L.K) (hj : j < L.l k)
    (ha : Measurable (bandBoundary M L k j))
    (hb : Measurable (bandBoundary M L k (j + 1)))
    (hd : BoundaryDensitiesBounded M L) (h0 : NoAtomAtLowerEndpoint M L)
    (w : X → ℝ) (hw : Measurable w) (hwi : Integrable w (xLaw M)) :
    Integrable (fun o : Obs X Z => w o.1 *
      (contScoreComponents M phi dphi L (trueNuisance M L) k j o -
        contJ L (trueNuisance M L) k j o.1)) (observationLaw M) ∧
    (∫ o : Obs X Z, w o.1 *
      (contScoreComponents M phi dphi L (trueNuisance M L) k j o -
        contJ L (trueNuisance M L) k j o.1) ∂observationLaw M) = 0 := by
  obtain ⟨hs, hm⟩ := population_continuous_band_mean_from_overlap M h he phi dphi hdphi
    hDerivative L hL cpi hov hpol k j hk hj ha hb hd h0 w hw hwi
  have ib := population_contJ_weighted_integrable M h he (policyProp phi M.prop)
    L hL k j hk hj ha hb w hw hwi
  simp_rw [mul_sub]
  refine ⟨hs.sub' ib, ?_⟩
  rw [integral_sub hs ib, hm, sub_self]

-- Simultaneous regular product weights cancel against their assignment corrections.
-- @node: population_continuous_total_band_weight_path_from_overlap
/-- Under [the structural assumptions](hyp:h) and [known outcome endpoints](hyp:he),
suppose [the policy derivative at the true propensity is measurable](hyp:hdphi),
[the derivative is uniformly bounded and Lipschitz on the unit interval](hyp:hDerivative),
[there is at least one level](hyp:hK), [the policy preserves level ordering](hyp:hL),
and [baseline overlap](hyp:hov) and [policy overlap](hyp:hpol) hold with floor cpi.
If [all band boundaries are measurable](hyp:hb), [boundary densities are
bounded](hyp:hd), [there is no atom at the lower endpoint](hyp:h0), [each regular
band weight direction is measurable](hyp:hw) and [integrable](hyp:hwi), and [the
total continuous score at the truth is integrable](hyp:hbase), then [adding any
scalar multiple of these directions to the true regular band weights leaves
the population mean of the total continuous score equal to its mean at the
truth](goal). -/
lemma population_continuous_total_band_weight_path_from_overlap
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (phi dphi : Z → X → ℝ → ℝ)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (hb : ∀ k j, Measurable (bandBoundary M L k j))
    (hd : BoundaryDensitiesBounded M L) (h0 : NoAtomAtLowerEndpoint M L)
    (d : RegularIndex L → X → ℝ)
    (hw : ∀ a, Measurable (d a)) (hwi : ∀ a, Integrable (d a) (xLaw M))
    (hbase : Integrable (fun o => psiCont M phi dphi L hK o (trueNuisance M L))
      (observationLaw M)) (t : ℝ) :
    (∫ o, psiCont M phi dphi L hK o
      {trueNuisance M L with gamma := fun a x => (trueNuisance M L).gamma a x + t * d a x}
      ∂observationLaw M) =
      ∫ o, psiCont M phi dphi L hK o (trueNuisance M L) ∂observationLaw M := by
  have hc k (hk : k < L.K) j (hj : 1 ≤ j ∧ j ≤ L.l k) :=
    population_continuous_band_correction_zero_from_overlap M h he phi dphi hdphi
      hDerivative L hL cpi hov hpol k (j - 1) hk (by omega)
      (hb k (j - 1)) (hb k (j - 1 + 1)) hd h0 (regularValue d k j)
      (by
        change Measurable (fun x => regularValue d k j x)
        simpa only [regularValue, dif_pos (And.intro hk.le hj)] using hw ⟨(k,j), hk.le, hj⟩)
      (by
        change Integrable (fun x => regularValue d k j x) (xLaw M)
        simpa only [regularValue, dif_pos (And.intro hk.le hj)] using hwi ⟨(k,j), hk.le, hj⟩)
  have hi : ∀ k ∈ Finset.range L.K, ∀ j ∈ Finset.Icc 1 (L.l k),
      Integrable (fun o : Obs X Z => regularValue d k j o.1 *
        (contScoreComponents M phi dphi L (trueNuisance M L) k (j - 1) o -
          contJ L (trueNuisance M L) k (j - 1) o.1)) (observationLaw M) := by
    intro k hk j hj
    exact (hc k (Finset.mem_range.mp hk) j (Finset.mem_Icc.mp hj)).1
  have hz : (∫ o : Obs X Z, ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
      regularValue d k j o.1 *
        (contScoreComponents M phi dphi L (trueNuisance M L) k (j - 1) o -
          contJ L (trueNuisance M L) k (j - 1) o.1) ∂observationLaw M) = 0 := by
    rw [integral_finsetSum _ (fun k hk => integrable_finsetSum _ (hi k hk))]
    apply Finset.sum_eq_zero
    intro k hk
    rw [integral_finsetSum _ (hi k hk)]
    apply Finset.sum_eq_zero
    intro j hj
    exact (hc k (Finset.mem_range.mp hk) j (Finset.mem_Icc.mp hj)).2
  simp_rw [continuous_total_band_weight_path]
  rw [integral_add hbase
    ((integrable_finsetSum _ (fun k hk => integrable_finsetSum _ (hi k hk))).const_mul t),
    integral_const_mul, hz, mul_zero, add_zero]

-- @node: population_continuous_total_band_weight_orthogonality_from_overlap
/-- Under [the structural assumptions](hyp:h) and [known outcome endpoints](hyp:he),
assume [the policy derivative at the true propensity is measurable](hyp:hdphi),
[the derivative is uniformly bounded and Lipschitz on the unit interval](hyp:hDerivative),
[there is at least one level](hyp:hK), [the policy preserves level ordering](hyp:hL),
and [baseline overlap](hyp:hov) and [policy overlap](hyp:hpol) hold with floor cpi.
With [measurable band boundaries](hyp:hb), [bounded boundary densities](hyp:hd),
[no atom at the lower endpoint](hyp:h0), [measurable regular band weight
directions](hyp:hw) [that are integrable](hyp:hwi), and [an integrable total
continuous score at the truth](hyp:hbase), [the population mean of the total
continuous score along the affine perturbation of true regular band weights
has derivative zero at zero](goal). -/
lemma population_continuous_total_band_weight_orthogonality_from_overlap
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (phi dphi : Z → X → ℝ → ℝ)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (hb : ∀ k j, Measurable (bandBoundary M L k j))
    (hd : BoundaryDensitiesBounded M L) (h0 : NoAtomAtLowerEndpoint M L)
    (d : RegularIndex L → X → ℝ)
    (hw : ∀ a, Measurable (d a)) (hwi : ∀ a, Integrable (d a) (xLaw M))
    (hbase : Integrable (fun o => psiCont M phi dphi L hK o (trueNuisance M L))
      (observationLaw M)) :
    HasDerivAt (fun t : ℝ => ∫ o, psiCont M phi dphi L hK o
      {trueNuisance M L with gamma := fun a x => (trueNuisance M L).gamma a x + t * d a x}
      ∂observationLaw M) 0 0 := by
  have heq : (fun t : ℝ => ∫ o, psiCont M phi dphi L hK o
      {trueNuisance M L with gamma := fun a x => (trueNuisance M L).gamma a x + t * d a x}
      ∂observationLaw M) =
      (fun _ : ℝ => ∫ o, psiCont M phi dphi L hK o (trueNuisance M L)
        ∂observationLaw M) := by
    funext t
    exact population_continuous_total_band_weight_path_from_overlap M h he phi dphi hdphi
      hDerivative L hK hL cpi hov hpol hb hd h0 d hw hwi hbase t
  rw [heq]
  exact hasDerivAt_const 0 _

end Papers.TbsPrteOptimalTransport

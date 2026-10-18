module
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousPolicyBounds
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousFullMeanOverlap
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationInstrumentMoments
/-! Finite assembly of the continuous score population moments. -/
public section
set_option linter.style.openClassical false
set_option linter.unusedSectionVars false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: population_continuous_prefix_weighted_mean
/-- Under [the structural model assumptions](hyp:h), [known outcome
endpoints](hyp:he), [measurability of the candidate policy derivative at baseline
propensities](hyp:hdphi), [boundedness and Lipschitz continuity of that
derivative](hyp:hDerivative), [a consistent baseline and policy level
ordering](hyp:hL), [baseline overlap](hyp:hov), [policy overlap](hyp:hpol),
[measurable band boundaries](hyp:hb), [bounded boundary densities](hyp:hd), and
[no atom at the lower outcome endpoint](hyp:h0), for [a measurable](hyp:hw) and
[integrable covariate weight](hyp:hwi), [the weighted sum of full and band score
products is integrable, and its mean equals the sum of the weighted full and band
population contrasts multiplied by their instrument probability weights](goal). -/
lemma population_continuous_prefix_weighted_mean
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (phi dphi : Z → X → ℝ → ℝ)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (hb : ∀ k < L.K, ∀ j ≤ L.l k, Measurable (bandBoundary M L k j))
    (hd : BoundaryDensitiesBounded M L) (h0 : NoAtomAtLowerEndpoint M L)
    (w : X → ℝ) (hw : Measurable w) (hwi : Integrable w (xLaw M)) :
    Integrable (fun o : Obs X Z => w o.1 *
      ∑ k ∈ Finset.range L.K, (psiFullProd L (trueNuisance M L) k o +
        ∑ j ∈ Finset.Icc 1 (L.l k), psiProd M phi dphi L (trueNuisance M L) k j o))
      (observationLaw M) ∧
    (∫ o : Obs X Z, w o.1 *
      ∑ k ∈ Finset.range L.K, (psiFullProd L (trueNuisance M L) k o +
        ∑ j ∈ Finset.Icc 1 (L.l k), psiProd M phi dphi L (trueNuisance M L) k j o)
      ∂observationLaw M) =
      ∑ k ∈ Finset.range L.K,
        ((∫ o : Obs X Z, (w o.1 * gammaFull M L k o.1) *
          contFullJ L (trueNuisance M L) k o.1 ∂observationLaw M) +
        ∑ j ∈ Finset.Icc 1 (L.l k), ∫ o : Obs X Z,
          (w o.1 * gamma M L k j o.1) * contJ L (trueNuisance M L) k (j - 1) o.1
          ∂observationLaw M) := by
  have hf k (hk : k < L.K) := population_continuous_full_product_mean_from_overlap
    M h he (policyProp phi M.prop) L hL cpi hov k hk w hw hwi
  have hr k (hk : k < L.K) j (hj : j ∈ Finset.Icc 1 (L.l k)) :=
    population_continuous_band_product_mean_from_overlap M h he phi dphi hdphi
      hDerivative L hL cpi hov hpol k j hk (Finset.mem_Icc.mp hj).1
      (Finset.mem_Icc.mp hj).2 (hb k hk (j - 1) (by have := Finset.mem_Icc.mp hj; omega))
      (hb k hk j (Finset.mem_Icc.mp hj).2) hd h0 w hw hwi
  have hi : ∀ k ∈ Finset.range L.K, Integrable (fun o : Obs X Z =>
      w o.1 * psiFullProd L (trueNuisance M L) k o +
      ∑ j ∈ Finset.Icc 1 (L.l k), w o.1 *
        psiProd M phi dphi L (trueNuisance M L) k j o) (observationLaw M) := by
    intro k hk
    exact (hf k (Finset.mem_range.mp hk)).1.fun_add
      (integrable_finsetSum _ (fun j hj => (hr k (Finset.mem_range.mp hk) j hj).1))
  simp_rw [Finset.mul_sum, mul_add, Finset.mul_sum]
  refine ⟨integrable_finsetSum _ hi, ?_⟩
  rw [integral_finsetSum _ hi]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  rw [integral_add (hf k hk').1
    (integrable_finsetSum _ (fun j hj => (hr k hk' j hj).1)),
    integral_finsetSum _ (fun j hj => (hr k hk' j hj).1), (hf k hk').2]
  congr 1
  exact Finset.sum_congr rfl (fun j hj => (hr k hk' j hj).2)

-- The tail score is shared by the two outcome regimes; no binary-outcome
-- assumption is used in its construction, envelope, or tower calculation.
-- @node: population_continuous_tail_mean_from_overlap
/-- Under [threshold crossing](hyp:h), [a measurable policy map preserving the
unit interval](hyp:hphi), [measurability of the candidate policy derivative at
baseline propensities](hyp:hdphi), [boundedness and Lipschitz continuity of that
derivative](hyp:hDerivative), [a positive number of levels](hyp:hK), [a consistent
baseline and policy level ordering](hyp:hOrder), [measurable level
propensities](hyp:hlev), and [baseline overlap](hyp:hov), [the common tail score
at the true nuisance is integrable and its population mean equals the covariate
average of the tail contribution using the lower outcome endpoint](goal). -/
lemma population_continuous_tail_mean_from_overlap
    (h : ThresholdCrossing M) (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (hlev : ∀ k, Measurable (L.pLev k)) (cpi : ℝ)
    (hov : BaselineOverlapWitness M L cpi) :
    Integrable (commonTailScore M phi dphi L (trueNuisance M L).prop
      (trueNuisance M L).pLev (trueNuisance M L).piLev (trueNuisance M L).gammaTail)
      (observationLaw M) ∧
    (∫ o, commonTailScore M phi dphi L (trueNuisance M L).prop
      (trueNuisance M L).pLev (trueNuisance M L).piLev (trueNuisance M L).gammaTail o
      ∂observationLaw M) =
      ∫ x, tailContribution M false L (policyProp phi M.prop) x ∂xLaw M := by
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  obtain ⟨B, D, hB, hD, hbound⟩ := hDerivative
  have hb : ∀ z x, |dphi z x (M.prop z x)| ≤ B := fun z x =>
    (hbound z x (M.prop z x) (M.prop z x) (M.rangeProp z x) (M.rangeProp z x)).1
  have hplev : Measurable (positiveValue (eta0Bin M L).pLev L.K) := by
    first
    | fun_prop
    | unfold positiveValue
      split_ifs
      · exact hlev L.K
      · fun_prop
  have hpb : ∀ᵐ x ∂xLaw M, positiveValue (eta0Bin M L).pLev L.K x ∈ Icc (0 : ℝ) 1 := by
    apply Eventually.of_forall
    intro x
    simp only [positiveValue, dif_pos (show 1 ≤ L.K ∧ L.K ≤ L.K from ⟨hK, le_rfl⟩), eta0Bin]
    exact hOrder.2.2.2.2.2.2.2.2.2.2.1 x L.K (by omega)
  have hi : Measurable (fun o : Obs X Z => indicator (o.2.1 ∈ policyUnion L L.K 1)) := by
    first
    | fun_prop
    | unfold indicator
      exact Measurable.ite ((policyUnion L L.K 1).finite_toSet.measurableSet.preimage
        measurable_snd.fst) measurable_const measurable_const
  have hib : ∀ o : Obs X Z, |indicator (o.2.1 ∈ policyUnion L L.K 1)| ≤ 1 := by
    intro o
    unfold indicator
    split_ifs <;> norm_num
  have hq := population_policyProp_measurable M h phi hphi
  have htail : Integrable (fun o : Obs X Z => M.yMin *
      indicator (o.2.1 ∈ policyUnion L L.K 1) *
      (phi o.2.1 o.1 (M.prop o.2.1 o.1) - positiveValue (eta0Bin M L).pLev L.K o.1))
      (observationLaw M) := by
    have hm : Measurable (fun o : Obs X Z => M.yMin *
        indicator (o.2.1 ∈ policyUnion L L.K 1) *
        (phi o.2.1 o.1 (M.prop o.2.1 o.1) - positiveValue (eta0Bin M L).pLev L.K o.1)) := by
      first
      | fun_prop
      | exact (measurable_const.mul hi).mul
          ((hq.comp (measurable_snd.fst.prodMk measurable_fst)).sub (hplev.comp measurable_fst))
    apply Integrable.of_bound hm.aestronglyMeasurable (2 * |M.yMin|)
    filter_upwards [observationLaw_covariate_ae M _ hpb] with o ho
    have hqr := hphi.2 o.2.1 o.1 (M.prop o.2.1 o.1) (M.rangeProp _ _)
    have hd : |phi o.2.1 o.1 (M.prop o.2.1 o.1) - positiveValue (eta0Bin M L).pLev L.K o.1| ≤ 2 := by
      rw [abs_le]
      constructor <;> linarith [hqr.1, hqr.2, ho.1, ho.2]
    simp only [Real.norm_eq_abs, abs_mul]
    calc
      _ ≤ |M.yMin| * 1 * 2 := by gcongr; exact hib o
      _ = 2 * |M.yMin| := by ring
  have hw : ∀ᵐ o : Obs X Z ∂observationLaw M, o.2.2.1 ∈ Icc (0 : ℝ) 1 := by
    have hobs := M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY))
    apply (ae_map_iff hobs.aemeasurable
      (measurableSet_Icc.preimage measurable_snd.snd.fst)).2
    exact Filter.Eventually.of_forall (fun s => by
      rcases M.rangeW s with hs | hs <;> simp [hs])
  have htailPolicy : Integrable (fun o : Obs X Z =>
      (M.yMin * indicator (o.2.1 ∈ policyUnion L L.K 1) *
        dphi o.2.1 o.1 (M.prop o.2.1 o.1)) * (o.2.2.1 - M.prop o.2.1 o.1))
      (observationLaw M) := by
    have hm : Measurable (fun o : Obs X Z =>
        (M.yMin * indicator (o.2.1 ∈ policyUnion L L.K 1) *
          dphi o.2.1 o.1 (M.prop o.2.1 o.1)) * (o.2.2.1 - M.prop o.2.1 o.1)) := by
      first
      | fun_prop
      | exact ((measurable_const.mul hi).mul
          (hdphi.comp (measurable_snd.fst.prodMk measurable_fst))).mul
            (measurable_snd.snd.fst.sub (h.2.1.comp (measurable_snd.fst.prodMk measurable_fst)))
    apply Integrable.of_bound hm.aestronglyMeasurable (2 * |M.yMin| * B)
    filter_upwards [hw] with o ho
    have hd : |o.2.2.1 - M.prop o.2.1 o.1| ≤ 2 := by
      rw [abs_le]
      constructor <;> linarith [ho.1, ho.2, (M.rangeProp o.2.1 o.1).1, (M.rangeProp o.2.1 o.1).2]
    simp only [Real.norm_eq_abs, abs_mul]
    calc
      _ ≤ (|M.yMin| * 1 * B) * 2 := by gcongr; exact hib o; exact hb _ _
      _ = 2 * |M.yMin| * B := by ring
  have hgammaTail : Measurable (gammaTail M L) :=
    population_instrument_set_probability_measurable M (policyUnion L L.K 1)
  have hgammaTailI : Integrable (gammaTail M L) (xLaw M) := by
    apply Integrable.of_bound hgammaTail.aestronglyMeasurable 1
    apply Eventually.of_forall
    intro x
    have hr := population_instrument_set_probability_range M (policyUnion L L.K 1) x
    change ‖∑ z ∈ policyUnion L L.K 1, instProb M z x‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg hr.1]
    exact hr.2
  have hpi a : Measurable ((trueNuisance M L).piLev a) :=
    population_instrument_set_probability_measurable M (L.S a.val)
  have hcl a : ∀ᵐ x ∂xLaw M, cpi ≤ (trueNuisance M L).piLev a x :=
    Eventually.of_forall (fun x => hov.2 x a.val a.property.1 a.property.2)
  have htailProp : Integrable (fun o : Obs X Z => gammaTail M L o.1 *
      Rp L (eta0Bin M L) L.K o) (observationLaw M) := by
    exact population_RpCont_integrable_of_integrable_weight M h (policyProp phi M.prop)
      L hOrder (trueNuisance M L).piLev hpi cpi hov.1 hcl L.K
      (gammaTail M L) hgammaTail hgammaTailI
  let tail : Obs X Z → ℝ := commonTailScore M phi dphi L M.prop
    (eta0Bin M L).pLev (eta0Bin M L).piLev (gammaTail M L)
  have hk0 : L.K ≠ 0 := by unfold LevelCountPos at hK; omega
  have htid : ∀ o : Obs X Z, tail o =
      M.yMin * indicator (o.2.1 ∈ policyUnion L L.K 1) *
        (phi o.2.1 o.1 (M.prop o.2.1 o.1) - positiveValue (eta0Bin M L).pLev L.K o.1) +
      (M.yMin * indicator (o.2.1 ∈ policyUnion L L.K 1) *
        dphi o.2.1 o.1 (M.prop o.2.1 o.1)) * (o.2.2.1 - M.prop o.2.1 o.1) -
      M.yMin * (gammaTail M L o.1 * Rp L (eta0Bin M L) L.K o) := by
    intro o
    simp only [tail, commonTailScore, Rp, if_neg hk0, div_eq_mul_inv]
    ring
  have itail : Integrable tail (observationLaw M) := by
    change Integrable (fun o => tail o) _
    simpa only [htid] using (htail.fun_add htailPolicy).sub' (htailProp.const_mul M.yMin)
  have mtail := population_commonTailScore_mean M h phi dphi hphi hdphi L hK hOrder
    htail htailPolicy htailProp (hlev L.K)
  exact ⟨itail, mtail⟩

-- @node: population_continuous_total_mean_from_overlap
/-- Under [the structural model assumptions](hyp:h), [known outcome
endpoints](hyp:he), [a measurable policy map preserving the unit interval](hyp:hphi),
[measurability of the candidate policy derivative at baseline
propensities](hyp:hdphi), [boundedness and Lipschitz continuity of that
derivative](hyp:hDerivative), [a positive number of levels](hyp:hK), [a consistent
baseline and policy level ordering](hyp:hL), [measurable level
propensities](hyp:hlev), [baseline overlap](hyp:hov), [policy overlap](hyp:hpol),
[measurable band boundaries](hyp:hb), [bounded boundary densities](hyp:hd), and
[no atom at the lower outcome endpoint](hyp:h0), [the continuous score at the true
nuisance is integrable, and its population mean is the sum of the instrument
probability-weighted full and band contrast means and the mean tail contribution
using the lower outcome endpoint](goal). -/
lemma population_continuous_total_mean_from_overlap
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (hlev : ∀ k, Measurable (L.pLev k)) (cpi : ℝ)
    (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (hb : ∀ k < L.K, ∀ j ≤ L.l k, Measurable (bandBoundary M L k j))
    (hd : BoundaryDensitiesBounded M L) (h0 : NoAtomAtLowerEndpoint M L) :
    Integrable (fun o => psiCont M phi dphi L hK o (trueNuisance M L))
      (observationLaw M) ∧
    (∫ o, psiCont M phi dphi L hK o (trueNuisance M L) ∂observationLaw M) =
      (∑ k ∈ Finset.range L.K,
        ((∫ o : Obs X Z, gammaFull M L k o.1 *
          contFullJ L (trueNuisance M L) k o.1 ∂observationLaw M) +
        ∑ j ∈ Finset.Icc 1 (L.l k), ∫ o : Obs X Z,
          gamma M L k j o.1 * contJ L (trueNuisance M L) k (j - 1) o.1
          ∂observationLaw M)) +
        ∫ x, tailContribution M false L (policyProp phi M.prop) x ∂xLaw M := by
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  obtain ⟨ip, mp⟩ := population_continuous_prefix_weighted_mean M h he phi dphi hdphi
    hDerivative L hL cpi hov hpol hb hd h0 (fun _ => 1) (by fun_prop)
    (integrable_const 1)
  simp only [one_mul] at ip mp
  obtain ⟨it, mt⟩ := population_continuous_tail_mean_from_overlap M h.2.2.2.1
    phi dphi hphi hdphi hDerivative L hK hL hlev cpi hov
  change Integrable (fun o =>
    (∑ k ∈ Finset.range L.K, (psiFullProd L (trueNuisance M L) k o +
      ∑ j ∈ Finset.Icc 1 (L.l k), psiProd M phi dphi L (trueNuisance M L) k j o)) +
      commonTailScore M phi dphi L (trueNuisance M L).prop (trueNuisance M L).pLev
        (trueNuisance M L).piLev (trueNuisance M L).gammaTail o) (observationLaw M) ∧ _
  refine ⟨ip.fun_add it, ?_⟩
  unfold psiCont
  rw [integral_add ip it, mp, mt]

end Papers.TbsPrteOptimalTransport

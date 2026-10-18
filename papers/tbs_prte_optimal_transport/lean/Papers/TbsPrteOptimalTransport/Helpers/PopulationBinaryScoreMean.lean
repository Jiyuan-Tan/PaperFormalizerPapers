module
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationBinaryRegularProducts
/-! The complete binary score moment from overlap and population constructions. -/
public section
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set
open scoped Classical

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: population_binary_score_mean_of_overlap
/-- Under [the threshold-crossing treatment model](hyp:h), suppose [the policy is a
valid policy map](hyp:hphi), [its derivative at baseline propensities is jointly
measurable](hyp:hdphi), [the derivative bound is nonnegative](hyp:hB), and [the derivative's
absolute value never exceeds that bound](hyp:hb). With [a positive baseline level
count](hyp:hK), [covariate-invariant ordering of baseline and policy levels](hyp:hOrder),
[measurable baseline levels](hyp:hlev), [baseline overlap](hyp:hov), [policy-level
overlap](hyp:hpol), [almost-surely binary outcomes](hyp:hy), and [admissible population
binary nuisances](hyp:he), [the complete population binary score is integrable and
its expectation equals the covariate average of the binary plug-in expression](goal). -/
lemma population_binary_score_mean_of_overlap (h : ThresholdCrossing M)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ z x, |dphi z x (M.prop z x)| ≤ B)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (hlev : ∀ k, Measurable (L.pLev k)) (cpi : ℝ)
    (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (hy : OutcomeBinaryAE M) (he : BinAdmissible M L (eta0Bin M L)) :
    Integrable (fun o => psiBin M phi dphi L hK o (eta0Bin M L)) (observationLaw M) ∧
    (∫ o, psiBin M phi dphi L hK o (eta0Bin M L) ∂observationLaw M) =
      ∫ x, mBin M phi L (eta0Bin M L) x ∂xLaw M := by
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  have hreg : ∀ k < L.K, ∀ j ∈ Finset.Icc 1 (L.l k),
      Integrable (psiProdBin phi dphi L (eta0Bin M L) k j) (observationLaw M) ∧
      (∫ o, psiProdBin phi dphi L (eta0Bin M L) k j o ∂observationLaw M) =
        ∫ x, gamma M L k j x * hMinus phi L (eta0Bin M L) k j x ∂xLaw M := by
    intro k hk j hj
    exact population_binary_regular_product_mean_of_overlap M h phi dphi hphi hdphi
      B hB hb L hOrder hlev cpi hov hpol hy he k j hk (Finset.mem_Icc.mp hj)
  have hful : ∀ k < L.K,
      Integrable (psiFullProdBin L (eta0Bin M L) k) (observationLaw M) ∧
      (∫ o, psiFullProdBin L (eta0Bin M L) k o ∂observationLaw M) =
        ∫ x, gammaFull M L k x * binFullJ L (eta0Bin M L) k x ∂xLaw M := by
    intro k hk
    exact ⟨population_binary_full_product_integrable_of_overlap M L cpi hov hy he ⟨k,hk⟩,
      population_binary_full_product_mean_of_overlap M L cpi hov hy he ⟨k,hk⟩⟩
  have hplev : Measurable (positiveValue (eta0Bin M L).pLev L.K) := by
    first
    | fun_prop
    | unfold positiveValue
      split_ifs
      · exact hlev L.K
      · fun_prop
  have hpb : ∀ᵐ x ∂xLaw M, positiveValue (eta0Bin M L).pLev L.K x ∈ Icc (0 : ℝ) 1 := by
    simpa only [positiveValue, dif_pos (show 1 ≤ L.K ∧ L.K ≤ L.K from ⟨hK, le_rfl⟩),
      eta0Bin] using (he.2.2.1 ⟨L.K, hK, le_rfl⟩).mono (fun _ hx => hx.1)
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
  have hgammaTail : Measurable (gammaTail M L) := he.2.2.2.2.2.2.2.2.2.2.2.2
  have hgammaTailB : ∀ᵐ x ∂xLaw M, ‖gammaTail M L x‖ ≤ 1 := by
    filter_upwards [he.2.2.2.2.2.2.2.2.2.2.2.1] with x hx
    change gammaTail M L x ∈ Icc (0 : ℝ) 1 at hx
    rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
    exact hx.2
  have htailProp := population_binary_weighted_Rp_integrable M L cpi hov he L.K
    (gammaTail M L) hgammaTail 1 hgammaTailB
  have hfullTarget : ∀ k < L.K, Integrable (fun x =>
      gammaFull M L k x * binFullJ L (eta0Bin M L) k x) (xLaw M) := by
    intro k hk
    have hg : Measurable (gammaFull M L k) := he.2.2.2.2.2.2.2.2.2.2.1 ⟨k,hk⟩
    apply Integrable.of_bound (hg.mul (population_binFullJ_measurable M L k)).aestronglyMeasurable 2
    have hp : ∀ i : ℕ, ∀ᵐ x ∂xLaw M, positiveValue (eta0Bin M L).P1 i x ∈ Icc (0 : ℝ) 1 := by
      intro i
      by_cases hi : 1 ≤ i ∧ i ≤ L.K
      · simpa only [positiveValue, dif_pos hi] using
          (he.2.2.1 ⟨i,hi⟩).mono (fun _ hx => hx.2.1)
      · simp only [positiveValue, dif_neg hi]
        exact Filter.Eventually.of_forall (fun _ => ⟨le_rfl, zero_le_one⟩)
    filter_upwards [he.2.2.2.2.2.2.2.2.2.1 ⟨k,hk⟩, hp (k+1), hp k] with x hg hp hm
    have hj : |binFullJ L (eta0Bin M L) k x| ≤ 2 := by
      change |positiveValue (eta0Bin M L).P1 (k+1) x -
        positiveValue (eta0Bin M L).P1 k x| ≤ 2
      rw [abs_le]
      constructor <;> linarith [hp.1, hp.2, hm.1, hm.2]
    have hgb : |gammaFull M L k x| ≤ 1 := abs_le.mpr hg
    simpa only [Pi.mul_apply, Function.comp_apply, id_eq, Pi.sub_apply, Real.norm_eq_abs, abs_mul, one_mul] using
      mul_le_mul hgb hj (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have hregularTarget : ∀ k < L.K, ∀ j, 1 ≤ j → j ≤ L.l k →
      Integrable (fun x => gamma M L k j x * hMinus phi L (eta0Bin M L) k j x) (xLaw M) := by
    intro k hk j hj1 hjl
    let a : RegularIndex L := ⟨(k,j), hk.le, hj1, hjl⟩
    have hg : Measurable (gamma M L k j) := (he.2.2.2.2.2.1 a).2
    apply Integrable.of_bound
      (hg.mul (population_hMinus_measurable M h phi hphi L hlev k j)).aestronglyMeasurable 1
    filter_upwards [he.2.2.2.2.1 a,
      binary_auxiliary_ranges M phi L (eta0Bin M L) hphi he k hk j hj1 hjl] with x hg hh
    have hgg : gamma M L k j x ∈ Icc (0 : ℝ) 1 := hg.2
    change |gamma M L k j x * hMinus phi L (eta0Bin M L) k j x| ≤ 1
    rw [abs_mul, abs_of_nonneg hgg.1, abs_of_nonneg hh.1.1]
    exact mul_le_one₀ hgg.2 hh.1.1 hh.1.2
  have htailTarget : Integrable (fun x => M.yMin * ∑ z ∈ policyUnion L L.K 1,
      instProb M z x * (policyProp phi M.prop z x - L.pLev L.K x)) (xLaw M) := by
    apply Integrable.const_mul
    apply integrable_finsetSum
    intro z hz
    have hm : Measurable (instProb M z) :=
      (Kernel.measurable_coe _ (measurableSet_singleton z)).ennreal_toReal
    apply Integrable.of_bound
      (hm.mul ((hq.comp (measurable_const.prodMk measurable_id)).sub (hlev L.K))).aestronglyMeasurable 2
    filter_upwards [hpb] with x hx
    rw [population_binary_baseline_value M _ L hOrder L.K le_rfl] at hx
    have hqr := hphi.2 z x (M.prop z x) (M.rangeProp _ _)
    have hd : |policyProp phi M.prop z x - L.pLev L.K x| ≤ 2 := by
      change |phi z x (M.prop z x) - L.pLev L.K x| ≤ 2
      rw [abs_le]
      constructor <;> linarith [hqr.1, hqr.2, hx.1, hx.2]
    haveI := M.instKernel_markov
    have hp : |instProb M z x| ≤ 1 := by
      rw [instProb, abs_of_nonneg ENNReal.toReal_nonneg]
      exact measureReal_le_one
    simpa only [Pi.mul_apply, Function.comp_apply, id_eq, Pi.sub_apply, Real.norm_eq_abs, abs_mul, one_mul] using
      mul_le_mul hp hd (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
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
  have icomps : ∀ k ∈ Finset.range L.K, Integrable
      (fun o => psiFullProdBin L (eta0Bin M L) k o +
        ∑ j ∈ Finset.Icc 1 (L.l k), psiProdBin phi dphi L (eta0Bin M L) k j o)
      (observationLaw M) := by
    intro k hk
    exact (hful k (Finset.mem_range.mp hk)).1.fun_add
      (integrable_finsetSum _ (fun j hj => (hreg k (Finset.mem_range.mp hk) j hj).1))
  have iregTarget : ∀ k < L.K, Integrable (fun x => ∑ j ∈ Finset.Icc 1 (L.l k),
      gamma M L k j x * hMinus phi L (eta0Bin M L) k j x) (xLaw M) := by
    intro k hk
    exact integrable_finsetSum _ (fun j hj =>
      hregularTarget k hk j (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2)
  have icompsTarget : ∀ k ∈ Finset.range L.K, Integrable (fun x =>
      gammaFull M L k x * binFullJ L (eta0Bin M L) k x +
      ∑ j ∈ Finset.Icc 1 (L.l k), gamma M L k j x * hMinus phi L (eta0Bin M L) k j x)
      (xLaw M) := by
    intro k hk
    exact (hfullTarget k (Finset.mem_range.mp hk)).fun_add
      (iregTarget k (Finset.mem_range.mp hk))
  have htarget : ∀ x, mBin M phi L (eta0Bin M L) x =
      (∑ k ∈ Finset.range L.K, (gammaFull M L k x * binFullJ L (eta0Bin M L) k x +
        ∑ j ∈ Finset.Icc 1 (L.l k), gamma M L k j x * hMinus phi L (eta0Bin M L) k j x)) +
      M.yMin * ∑ z ∈ policyUnion L L.K 1,
        instProb M z x * (policyProp phi M.prop z x - L.pLev L.K x) := by
    intro x
    simp only [mBin]
    congr 1
    · apply Finset.sum_congr rfl
      intro k hk
      have hk' := Finset.mem_range.mp hk
      simp only [fullValue, dif_pos hk', eta0Bin]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      have ha : k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k :=
        ⟨hk'.le, (Finset.mem_Icc.mp hj).1, (Finset.mem_Icc.mp hj).2⟩
      simp only [regularValue, dif_pos ha]
    · simp only [positiveValue, dif_pos (show 1 ≤ L.K ∧ L.K ≤ L.K from ⟨hK, le_rfl⟩),
        eta0Bin, policyProp]
  constructor
  · exact (integrable_finsetSum _ icomps).fun_add itail
  · simp only [psiBin]
    change (∫ o, (∑ k ∈ Finset.range L.K, (psiFullProdBin L (eta0Bin M L) k o +
      ∑ j ∈ Finset.Icc 1 (L.l k), psiProdBin phi dphi L (eta0Bin M L) k j o)) + tail o
      ∂observationLaw M) = ∫ x, mBin M phi L (eta0Bin M L) x ∂xLaw M
    rw [integral_add (integrable_finsetSum _ icomps) itail,
      integral_finsetSum _ icomps, mtail]
    simp_rw [htarget]
    rw [integral_add (integrable_finsetSum _ icompsTarget) htailTarget,
      integral_finsetSum _ icompsTarget]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    rw [integral_add (hful k hk').1
      (integrable_finsetSum _ (fun j hj => (hreg k hk' j hj).1)),
      (hful k hk').2, integral_finsetSum _ (fun j hj => (hreg k hk' j hj).1),
      integral_add (hfullTarget k hk') (iregTarget k hk'),
      integral_finsetSum _ (fun j hj =>
        hregularTarget k hk' j (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2)]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    exact (hreg k hk' j hj).2

-- @node: population_binary_score_mean_eq_target
/-- Under [the structural model assumptions](hyp:h), [known outcome endpoints](hyp:hEndpoints),
and [a finite instrument reduction](hyp:hf), suppose [the policy is a valid policy
map](hyp:hphi), [its derivative at baseline propensities is jointly measurable](hyp:hdphi),
and [the derivative satisfies boundedness and Lipschitz conditions](hyp:hDerivative).
With [a positive baseline level count](hyp:hK), [covariate-invariant ordering of
baseline and policy levels](hyp:hOrder), [measurable baseline levels](hyp:hlev),
[baseline overlap](hyp:hov), [policy-level overlap](hyp:hpol), [almost-surely binary
outcomes](hyp:hy), and [admissible population binary nuisances](hyp:he), [the complete
population binary score is integrable and its expectation equals the discrete
lower target for the policy propensity](goal). -/
lemma population_binary_score_mean_eq_target (h : StructuralAssumptions M)
    (hEndpoints : OutcomeEndpointsKnown M) (hf : InstrumentFiniteReduction Z)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (hlev : ∀ k, Measurable (L.pLev k)) (cpi : ℝ)
    (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (hy : OutcomeBinaryAE M) (he : BinAdmissible M L (eta0Bin M L)) :
    Integrable (fun o => psiBin M phi dphi L hK o (eta0Bin M L)) (observationLaw M) ∧
    (∫ o, psiBin M phi dphi L hK o (eta0Bin M L) ∂observationLaw M) =
      discreteTarget M false L (policyProp phi M.prop) := by
  obtain ⟨B, D, hB, hD, hbound⟩ := hDerivative
  have hb : ∀ z x, |dphi z x (M.prop z x)| ≤ B := fun z x =>
    (hbound z x (M.prop z x) (M.prop z x) (M.rangeProp z x) (M.rangeProp z x)).1
  obtain ⟨hi, hm⟩ := population_binary_score_mean_of_overlap M h.2.2.2.1
    phi dphi hphi hdphi B hB hb L hK hOrder hlev cpi hov hpol hy he
  refine ⟨hi, hm.trans ?_⟩
  exact population_mBin_integral_eq_discreteTarget M h hEndpoints hf hy phi L hOrder cpi hpol

end Papers.TbsPrteOptimalTransport

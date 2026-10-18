module
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationBinaryComponents
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationInstrumentMoments
/-! Assembly of population binary score moments from structural residual centering. -/
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

-- @node: population_levelShares_measurable
/-- [Each instrument's population share within a policy level is measurable as a
function of covariates](goal). -/
@[fun_prop] lemma population_levelShares_measurable (L : LevelData Z X) (k j : ℕ) (z : Z) :
    Measurable (levelShares M L k j z) := by
  first
  | fun_prop
  |
    unfold levelShares
    split_ifs
    · apply Measurable.div
      · exact (Kernel.measurable_coe _ (measurableSet_singleton z)).ennreal_toReal
      · exact Finset.measurable_sum _ (fun z _ =>
          (Kernel.measurable_coe _ (measurableSet_singleton z)).ennreal_toReal)
    · exact measurable_const

-- @node: population_pooledQBin_measurable
/-- Under [threshold crossing](hyp:h), if [the policy map satisfies its policy restrictions](hyp:hphi)
and [every baseline propensity level is measurable](hyp:hlev), then [each population
pooled policy level is measurable as a function of covariates](goal). -/
@[fun_prop] lemma population_pooledQBin_measurable (h : ThresholdCrossing M)
    (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (L : LevelData Z X) (hlev : ∀ k, Measurable (L.pLev k)) (k j : ℕ) :
    Measurable (pooledQBin phi L (eta0Bin M L) k j) := by
  first
  | fun_prop
  |
    have hp : ∀ k, Measurable (positiveValue (eta0Bin M L).pLev k) := by
      intro k
      unfold positiveValue
      split_ifs
      · exact hlev k
      · exact measurable_const
    unfold pooledQBin
    split_ifs
    · exact hp k
    · exact hp (k + 1)
    · apply Finset.measurable_sum
      intro z hz
      apply Measurable.mul
      · exact population_levelShares_measurable M L k j z
      · exact (population_policyProp_measurable M h phi hphi).comp
          (measurable_const.prodMk measurable_id)
    · simp only [zero_mul, Finset.sum_const_zero]
      exact measurable_const

-- @node: population_hMinus_measurable
/-- Under [threshold crossing](hyp:h), if [the policy map satisfies its policy restrictions](hyp:hphi)
and [all baseline propensity levels are measurable](hyp:hlev), then [the population
binary subinterval positive-part contribution is measurable in covariates](goal). -/
@[fun_prop] lemma population_hMinus_measurable (h : ThresholdCrossing M)
    (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (L : LevelData Z X) (hlev : ∀ k, Measurable (L.pLev k)) (k j : ℕ) :
    Measurable (hMinus phi L (eta0Bin M L) k j) := by
  first
  | fun_prop
  |
    have hq := population_pooledQBin_measurable M h phi hphi L hlev k j
    have hl := population_pooledQBin_measurable M h phi hphi L hlev k (j - 1)
    have hp : Measurable (positiveValue (eta0Bin M L).pLev (k + 1)) := by
      unfold positiveValue
      split_ifs
      · exact hlev (k + 1)
      · exact measurable_const
    unfold hMinus
    fun_prop

-- This is the regular-product step of the paper's tower argument. In
-- particular, its conditional score moment is derived rather than assumed.
-- @node: population_binary_regular_product_mean
/-- Under [threshold crossing](hyp:h), [the policy map restrictions](hyp:hphi), [measurability
of the policy derivative at the true propensity](hyp:hdphi), [invariant level ordering](hyp:hOrder),
and [measurability of all baseline propensity levels](hyp:hlev), take [a baseline index
at most the level count and a policy index between one and its bin's policy count](hyp:ha).
If the population-weighted [upper and lower treated-success residuals](hyp:hPplus,hPminus),
[upper and lower treatment residuals](hyp:hpplus,hpminus), and [upper and preceding
policy residuals](hyp:hqplus,hqminus) are integrable, and [the positive-part contribution
times the policy-union indicator is integrable](hyp:he), then [the regular product
score is integrable and its mean equals the covariate average of the population
policy-union probability times the positive-part contribution](goal). -/
lemma population_binary_regular_product_mean (h : ThresholdCrossing M)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (L : LevelData Z X) (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (hlev : ∀ k, Measurable (L.pLev k))
    (k j : ℕ) (ha : k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k)
    (hPplus : Integrable (fun o : Obs X Z => gamma M L k j o.1 *
      RP L (eta0Bin M L) (k + 1) o) (observationLaw M))
    (hPminus : Integrable (fun o : Obs X Z => gamma M L k j o.1 *
      RP L (eta0Bin M L) k o) (observationLaw M))
    (hpplus : Integrable (fun o : Obs X Z => gamma M L k j o.1 *
      Rp L (eta0Bin M L) (k + 1) o) (observationLaw M))
    (hpminus : Integrable (fun o : Obs X Z => gamma M L k j o.1 *
      Rp L (eta0Bin M L) k o) (observationLaw M))
    (hqplus : Integrable (fun o : Obs X Z => gamma M L k j o.1 *
      RqBin dphi L (eta0Bin M L) k j o) (observationLaw M))
    (hqminus : Integrable (fun o : Obs X Z => gamma M L k j o.1 *
      RqBin dphi L (eta0Bin M L) k (j - 1) o) (observationLaw M))
    (he : Integrable (fun o : Obs X Z => hMinus phi L (eta0Bin M L) k j o.1 *
      indicator (o.2.1 ∈ policyUnion L k j)) (observationLaw M)) :
    Integrable (psiProdBin phi dphi L (eta0Bin M L) k j) (observationLaw M) ∧
    (∫ o, psiProdBin phi dphi L (eta0Bin M L) k j o ∂observationLaw M) =
      ∫ x, gamma M L k j x * hMinus phi L (eta0Bin M L) k j x ∂xLaw M := by
  have hgamma : Measurable (gamma M L k j) := by
    exact Finset.measurable_sum _ (fun z _ =>
      (Kernel.measurable_coe _ (measurableSet_singleton z)).ennreal_toReal)
  have hq := population_pooledQBin_measurable M h phi hphi L hlev k j
  have hl := population_pooledQBin_measurable M h phi hphi L hlev k (j - 1)
  have hp : Measurable (positiveValue (eta0Bin M L).pLev (k + 1)) := by
    unfold positiveValue
    split_ifs
    · exact hlev (k + 1)
    · exact measurable_const
  have hb : Measurable (fun x => positiveValue (eta0Bin M L).pLev (k + 1) x -
      binFullJ L (eta0Bin M L) k x) := by fun_prop
  have hD := binary_Dbd_measurable phi L (eta0Bin M L) k j hq hl hb
  have hE := binary_Edom_measurable phi L (eta0Bin M L) k j hl hb
  have hI := binary_Iact_measurable phi L (eta0Bin M L) k j hq hl hb
  obtain ⟨hi, hz⟩ := population_binary_component_correction_zero M h phi dphi hdphi L hOrder
    k j (gamma M L k j) hgamma hD hE hI hPplus hPminus hpplus hpminus hqplus hqminus
  have hid : ∀ o : Obs X Z, psiProdBin phi dphi L (eta0Bin M L) k j o =
      hMinus phi L (eta0Bin M L) k j o.1 * indicator (o.2.1 ∈ policyUnion L k j) +
      gamma M L k j o.1 * (binScoreComponents phi dphi L (eta0Bin M L) k j o -
        hMinus phi L (eta0Bin M L) k j o.1) := by
    intro o
    simp only [psiProdBin, regularValue, dif_pos ha, eta0Bin]
    ring
  constructor
  · change Integrable (fun o => psiProdBin phi dphi L (eta0Bin M L) k j o) _
    simpa only [hid] using he.fun_add hi
  · simp_rw [hid]
    rw [integral_add he hi, hz, add_zero]
    let f : Z × X → ℝ := fun zx => hMinus phi L (eta0Bin M L) k j zx.2 *
      indicator (zx.1 ∈ policyUnion L k j)
    have hf : Measurable f := by
      dsimp only [f]
      unfold indicator
      exact ((population_hMinus_measurable M h phi hphi L hlev k j).comp measurable_snd).mul
        (Measurable.ite ((policyUnion L k j).finite_toSet.measurableSet.preimage measurable_fst)
          measurable_const measurable_const)
    have hs : ∀ x, (∑ z, instProb M z x * f (z, x)) =
        gamma M L k j x * hMinus phi L (eta0Bin M L) k j x := by
      intro x
      simp only [f, indicator, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_mem, Finset.univ_inter, gamma, Finset.sum_mul]
    have hm := population_instrument_integral M f hf he
    simpa only [hs, f] using hm

-- @node: population_binary_full_product_integrable
/-- If [the full-interval treated-success increment times the difference between the
higher-policy and higher-baseline instrument indicators is integrable](hyp:he), and
[the population full-interval weight times the upper treated-success residual](hyp:hp)
and [the same weight times the lower treated-success residual](hyp:hm) are integrable,
then [the population full-interval binary product score is integrable](goal). -/
lemma population_binary_full_product_integrable (L : LevelData Z X) (k : Fin L.K)
    (he : Integrable (fun o : Obs X Z => binFullJ L (eta0Bin M L) k o.1 *
      (indicator (o.2.1 ∈ higherPolicy L k) - indicator (o.2.1 ∈ higherBaseline L k)))
      (observationLaw M))
    (hp : Integrable (fun o : Obs X Z => gammaFull M L k o.1 *
      RP L (eta0Bin M L) (k + 1) o) (observationLaw M))
    (hm : Integrable (fun o : Obs X Z => gammaFull M L k o.1 *
      RP L (eta0Bin M L) k o) (observationLaw M)) :
    Integrable (psiFullProdBin L (eta0Bin M L) k) (observationLaw M) := by
  have hid : ∀ o : Obs X Z, psiFullProdBin L (eta0Bin M L) k o =
      binFullJ L (eta0Bin M L) k o.1 *
        (indicator (o.2.1 ∈ higherPolicy L k) - indicator (o.2.1 ∈ higherBaseline L k)) +
      gammaFull M L k o.1 * RP L (eta0Bin M L) (k + 1) o -
      gammaFull M L k o.1 * RP L (eta0Bin M L) k o := by
    intro o
    simp only [psiFullProdBin, fullValue, dif_pos k.isLt, eta0Bin]
    ring
  change Integrable (fun o => psiFullProdBin L (eta0Bin M L) k o) _
  simpa only [hid] using (he.fun_add hp).sub' hm

-- No moment equation is an input here. The six regular corrections, the
-- two signed full-interval corrections, and the tail corrections are all
-- centered by their population constructions before taking the finite sum.
-- @node: population_psiBin_mean
/-- Under [threshold crossing](hyp:h), [the policy map restrictions](hyp:hphi), [measurability
of the policy derivative at the true propensity](hyp:hdphi), [a positive baseline level
count](hyp:hK), [invariant level ordering](hyp:hOrder), and [measurability of every baseline
propensity level](hyp:hlev), assume [the six weighted residuals and the positive-part
term times the policy-union indicator are integrable for every regular subinterval](hyp:hregular),
and [the indicator term and both weighted treated-success residuals are integrable
for every full interval](hyp:hfull). If [the tail policy increment](hyp:htail), [the
tail policy-derivative treatment correction](hyp:htailPolicy), [the tail-weighted
baseline treatment residual](hyp:htailProp), [all full-interval covariate target
contributions](hyp:hfullTarget), [all regular covariate target contributions](hyp:hregularTarget),
and [the tail covariate target contribution](hyp:htailTarget) are integrable, then
[the total population binary score is integrable and its mean equals the covariate
average of the binary target function](goal). -/
lemma population_psiBin_mean (h : ThresholdCrossing M)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (hlev : ∀ k, Measurable (L.pLev k))
    (hregular : ∀ k < L.K, ∀ j, 1 ≤ j → j ≤ L.l k →
      Integrable (fun o : Obs X Z => gamma M L k j o.1 *
        RP L (eta0Bin M L) (k + 1) o) (observationLaw M) ∧
      Integrable (fun o : Obs X Z => gamma M L k j o.1 *
        RP L (eta0Bin M L) k o) (observationLaw M) ∧
      Integrable (fun o : Obs X Z => gamma M L k j o.1 *
        Rp L (eta0Bin M L) (k + 1) o) (observationLaw M) ∧
      Integrable (fun o : Obs X Z => gamma M L k j o.1 *
        Rp L (eta0Bin M L) k o) (observationLaw M) ∧
      Integrable (fun o : Obs X Z => gamma M L k j o.1 *
        RqBin dphi L (eta0Bin M L) k j o) (observationLaw M) ∧
      Integrable (fun o : Obs X Z => gamma M L k j o.1 *
        RqBin dphi L (eta0Bin M L) k (j - 1) o) (observationLaw M) ∧
      Integrable (fun o : Obs X Z => hMinus phi L (eta0Bin M L) k j o.1 *
        indicator (o.2.1 ∈ policyUnion L k j)) (observationLaw M))
    (hfull : ∀ k : Fin L.K,
      Integrable (fun o : Obs X Z => binFullJ L (eta0Bin M L) k o.1 *
        (indicator (o.2.1 ∈ higherPolicy L k) - indicator (o.2.1 ∈ higherBaseline L k)))
        (observationLaw M) ∧
      Integrable (fun o : Obs X Z => gammaFull M L k o.1 *
        RP L (eta0Bin M L) (k + 1) o) (observationLaw M) ∧
      Integrable (fun o : Obs X Z => gammaFull M L k o.1 *
        RP L (eta0Bin M L) k o) (observationLaw M))
    (htail : Integrable (fun o : Obs X Z => M.yMin *
      indicator (o.2.1 ∈ policyUnion L L.K 1) *
      (phi o.2.1 o.1 (M.prop o.2.1 o.1) - positiveValue (eta0Bin M L).pLev L.K o.1))
      (observationLaw M))
    (htailPolicy : Integrable (fun o : Obs X Z =>
      (M.yMin * indicator (o.2.1 ∈ policyUnion L L.K 1) *
        dphi o.2.1 o.1 (M.prop o.2.1 o.1)) * (o.2.2.1 - M.prop o.2.1 o.1))
      (observationLaw M))
    (htailProp : Integrable (fun o : Obs X Z => gammaTail M L o.1 *
      Rp L (eta0Bin M L) L.K o) (observationLaw M))
    (hfullTarget : ∀ k < L.K, Integrable (fun x =>
      gammaFull M L k x * binFullJ L (eta0Bin M L) k x) (xLaw M))
    (hregularTarget : ∀ k < L.K, ∀ j, 1 ≤ j → j ≤ L.l k →
      Integrable (fun x => gamma M L k j x * hMinus phi L (eta0Bin M L) k j x) (xLaw M))
    (htailTarget : Integrable (fun x => M.yMin * ∑ z ∈ policyUnion L L.K 1,
      instProb M z x * (policyProp phi M.prop z x - L.pLev L.K x)) (xLaw M)) :
    Integrable (fun o => psiBin M phi dphi L hK o (eta0Bin M L)) (observationLaw M) ∧
    (∫ o, psiBin M phi dphi L hK o (eta0Bin M L) ∂observationLaw M) =
      ∫ x, mBin M phi L (eta0Bin M L) x ∂xLaw M := by
  have hreg : ∀ k < L.K, ∀ j ∈ Finset.Icc 1 (L.l k),
      Integrable (psiProdBin phi dphi L (eta0Bin M L) k j) (observationLaw M) ∧
      (∫ o, psiProdBin phi dphi L (eta0Bin M L) k j o ∂observationLaw M) =
        ∫ x, gamma M L k j x * hMinus phi L (eta0Bin M L) k j x ∂xLaw M := by
    intro k hk j hj
    obtain ⟨hj1, hjl⟩ := Finset.mem_Icc.mp hj
    obtain ⟨iPp, iPm, ipp, ipm, iqp, iqm, ie⟩ := hregular k hk j hj1 hjl
    exact population_binary_regular_product_mean M h phi dphi hphi hdphi L hOrder hlev
      k j ⟨hk.le, hj1, hjl⟩ iPp iPm ipp ipm iqp iqm ie
  have hful : ∀ k < L.K,
      Integrable (psiFullProdBin L (eta0Bin M L) k) (observationLaw M) ∧
      (∫ o, psiFullProdBin L (eta0Bin M L) k o ∂observationLaw M) =
        ∫ x, gammaFull M L k x * binFullJ L (eta0Bin M L) k x ∂xLaw M := by
    intro k hk
    obtain ⟨ie, ip, im⟩ := hfull ⟨k, hk⟩
    exact ⟨population_binary_full_product_integrable M L ⟨k, hk⟩ ie ip im,
      population_binary_full_product_mean M L ⟨k, hk⟩ ie ip im⟩
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

end Papers.TbsPrteOptimalTransport

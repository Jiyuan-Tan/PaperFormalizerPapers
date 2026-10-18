module
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationBinaryTailOrthogonality
/-! Simultaneous product-weight cancellation in the total population binary score. -/
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

-- @node: binary_full_product_weight_path
/-- [Adding a scalar multiple of a family of covariate functions to the full-interval
weights changes each full-interval product score by that scalar times the corresponding
weight perturbation and the difference of the next and current treated-success
residual corrections; the weight perturbation is taken as zero outside the valid
interval range](goal). -/
lemma binary_full_product_weight_path (L : LevelData Z X) (eta : NuisanceBin L)
    (d : Fin L.K → X → ℝ) (k : ℕ) (o : Obs X Z) (t : ℝ) :
    psiFullProdBin L {eta with gammaFull := fun a x => eta.gammaFull a x + t * d a x} k o =
      psiFullProdBin L eta k o +
        t * (fullValue d k o.1 * (RP L eta (k+1) o - RP L eta k o)) := by
  simp only [psiFullProdBin, binFullJ, RP, fullValue]
  split_ifs <;> ring

-- @node: binary_total_full_tail_weight_path
/-- With [a positive baseline level count](hyp:hK), [simultaneously adding scalar
multiples of perturbations to the full-interval and final-bin weights changes the
complete binary score by that scalar times the sum of the full-interval perturbations
times adjacent treated-success residual differences, minus the lower outcome
endpoint times the final-bin perturbation times the final treatment residual correction](goal). -/
lemma binary_total_full_tail_weight_path (phi dphi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (hK : LevelCountPos L.K) (eta : NuisanceBin L)
    (d : Fin L.K → X → ℝ) (dt : X → ℝ) (o : Obs X Z) (t : ℝ) :
    psiBin M phi dphi L hK o {eta with
      gammaFull := fun a x => eta.gammaFull a x + t * d a x
      gammaTail := fun x => eta.gammaTail x + t * dt x} =
    psiBin M phi dphi L hK o eta + t *
      ((∑ k ∈ Finset.range L.K,
        fullValue d k o.1 * (RP L eta (k+1) o - RP L eta k o)) -
        M.yMin * (dt o.1 * Rp L eta L.K o)) := by
  have ht := binary_total_tail_weight_path M phi dphi L hK
    {eta with gammaFull := fun a x => eta.gammaFull a x + t * d a x} dt o t
  rw [ht]
  have hreg : ∀ k j, psiProdBin phi dphi L
      {eta with gammaFull := fun a x => eta.gammaFull a x + t * d a x} k j o =
      psiProdBin phi dphi L eta k j o := fun _ _ => rfl
  simp only [psiBin, binary_full_product_weight_path, hreg]
  have hs : (∑ k ∈ Finset.range L.K,
      (psiFullProdBin L eta k o +
        t * (fullValue d k o.1 * (RP L eta (k+1) o - RP L eta k o)) +
        ∑ j ∈ Finset.Icc 1 (L.l k), psiProdBin phi dphi L eta k j o)) =
      (∑ k ∈ Finset.range L.K,
        (psiFullProdBin L eta k o +
          ∑ j ∈ Finset.Icc 1 (L.l k), psiProdBin phi dphi L eta k j o)) +
      t * ∑ k ∈ Finset.range L.K,
        fullValue d k o.1 * (RP L eta (k+1) o - RP L eta k o) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hs]
  have hp : Rp L {eta with gammaFull := fun a x => eta.gammaFull a x + t * d a x}
      L.K o = Rp L eta L.K o := rfl
  rw [hp]
  ring

-- @node: population_binary_total_full_tail_weight_orthogonality_of_admissible
/-- Under [the threshold-crossing treatment model](hyp:h), suppose [the policy is a
valid policy map](hyp:hphi), [its derivative at baseline propensities is jointly
measurable](hyp:hdphi), [the derivative bound is nonnegative](hyp:hB), and [the derivative's
absolute value never exceeds that bound](hyp:hb). With [a positive baseline level
count](hyp:hK), [covariate-invariant ordering of baseline and policy levels](hyp:hOrder),
[measurable baseline levels](hyp:hlev), [baseline overlap](hyp:hov), [policy-level
overlap](hyp:hpol), [almost-surely binary outcomes](hyp:hy), and [an admissible nuisance
perturbation at the population specification](hyp:hd), [the expected complete binary
score has derivative zero at zero when the full-interval and final-bin weights
are varied together linearly in that direction](goal). -/
lemma population_binary_total_full_tail_weight_orthogonality_of_admissible
    (h : ThresholdCrossing M) (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ z x, |dphi z x (M.prop z x)| ≤ B)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (hlev : ∀ k, Measurable (L.pLev k)) (cpi : ℝ)
    (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (hy : OutcomeBinaryAE M) (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del)) :
    HasDerivAt (fun t : ℝ => ∫ o, psiBin M phi dphi L hK o
      {eta0Bin M L with
        gammaFull := fun a x => (eta0Bin M L).gammaFull a x + t * del.gammaFull a x
        gammaTail := fun x => (eta0Bin M L).gammaTail x + t * del.gammaTail x}
      ∂observationLaw M) 0 0 := by
  have he := binary_admissible_direction_origin M L (eta0Bin M L) del hd
  obtain ⟨C, hC, hreg⟩ := binary_full_weight_direction_regular M L (eta0Bin M L) del hd
  obtain ⟨hmt, Ct, hCt, hbt⟩ := binary_tail_weight_direction_regular M L (eta0Bin M L) del hd
  let r := fun k o => fullValue del.gammaFull k o.1 *
    (RP L (eta0Bin M L) (k+1) o - RP L (eta0Bin M L) k o)
  have ir : ∀ k ∈ Finset.range L.K, Integrable (r k) (observationLaw M) := by
    intro k hk
    let a : Fin L.K := ⟨k, Finset.mem_range.mp hk⟩
    obtain ⟨hm, hbound⟩ := hreg a
    have ip := population_binary_weighted_RP_integrable M L cpi hov hy he (k+1)
      (del.gammaFull a) hm C hbound
    have im := population_binary_weighted_RP_integrable M L cpi hov hy he k
      (del.gammaFull a) hm C hbound
    simpa only [r, fullValue, dif_pos (Finset.mem_range.mp hk), mul_sub] using ip.sub' im
  have zr : ∀ k ∈ Finset.range L.K, (∫ o, r k o ∂observationLaw M) = 0 := by
    intro k hk
    let a : Fin L.K := ⟨k, Finset.mem_range.mp hk⟩
    obtain ⟨hm, hbound⟩ := hreg a
    have ip := population_binary_weighted_RP_integrable M L cpi hov hy he (k+1)
      (del.gammaFull a) hm C hbound
    have im := population_binary_weighted_RP_integrable M L cpi hov hy he k
      (del.gammaFull a) hm C hbound
    simp only [r, fullValue, dif_pos (Finset.mem_range.mp hk), mul_sub]
    rw [integral_sub ip im, population_RP_weighted_integral_zero M L (k+1) _ hm ip,
      population_RP_weighted_integral_zero M L k _ hm im, sub_self]
  have it := population_binary_weighted_Rp_integrable M L cpi hov he L.K
    del.gammaTail hmt Ct hbt
  have zt := population_Rp_weighted_integral_zero M h (policyProp phi M.prop) L hOrder
    L.K del.gammaTail hmt it
  have ibase := (population_binary_score_mean_of_overlap M h phi dphi hphi hdphi
    B hB hb L hK hOrder hlev cpi hov hpol hy he).1
  have ie := (integrable_finsetSum _ ir).sub' (it.const_mul M.yMin)
  have ze : (∫ o, (∑ k ∈ Finset.range L.K, r k o) -
      M.yMin * (del.gammaTail o.1 * Rp L (eta0Bin M L) L.K o) ∂observationLaw M) = 0 := by
    rw [integral_sub (integrable_finsetSum _ ir) (it.const_mul M.yMin),
      integral_finsetSum _ ir, integral_const_mul, zt]
    simp only [Finset.sum_eq_zero zr, mul_zero, sub_self]
  have heq : (fun t : ℝ => ∫ o, psiBin M phi dphi L hK o
      {eta0Bin M L with
        gammaFull := fun a x => (eta0Bin M L).gammaFull a x + t * del.gammaFull a x
        gammaTail := fun x => (eta0Bin M L).gammaTail x + t * del.gammaTail x}
      ∂observationLaw M) =
      (fun _ : ℝ => ∫ o, psiBin M phi dphi L hK o (eta0Bin M L) ∂observationLaw M) := by
    funext t
    simp_rw [binary_total_full_tail_weight_path]
    rw [integral_add ibase (ie.const_mul t), integral_const_mul, ze, mul_zero, add_zero]
  rw [heq]
  exact hasDerivAt_const 0 _

-- @node: binary_total_regular_weight_path
/-- With [a positive baseline level count](hyp:hK), [adding a scalar multiple of a
family of covariate functions to the regular weights changes the complete binary
score by that scalar times the sum, over all baseline intervals and their positive
policy levels, of each weight perturbation times the difference between its binary
component score and lower-band plug-in expression](goal). -/
lemma binary_total_regular_weight_path (phi dphi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (hK : LevelCountPos L.K) (eta : NuisanceBin L)
    (d : RegularIndex L → X → ℝ) (o : Obs X Z) (t : ℝ) :
    psiBin M phi dphi L hK o {eta with gamma := fun a x => eta.gamma a x + t * d a x} =
      psiBin M phi dphi L hK o eta + t *
        ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k), regularValue d k j o.1 *
          (binScoreComponents phi dphi L eta k j o - hMinus phi L eta k j o.1) := by
  have hf : ∀ k, psiFullProdBin L {eta with gamma := fun a x => eta.gamma a x + t * d a x}
      k o = psiFullProdBin L eta k o := fun _ => rfl
  simp only [psiBin, hf, binary_regular_product_weight_path]
  simp_rw [mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

-- @node: population_binary_regular_weight_correction_of_admissible
/-- Under [the threshold-crossing treatment model](hyp:h), suppose [the policy is a
valid policy map](hyp:hphi), [its derivative at baseline propensities is jointly
measurable](hyp:hdphi), [the derivative bound is nonnegative](hyp:hB), and [the derivative's
absolute value never exceeds that bound](hyp:hb). With [covariate-invariant ordering
of baseline and policy levels](hyp:hL), [measurable baseline levels](hyp:hlev),
[baseline overlap](hyp:hov), [policy-level overlap](hyp:hpol), [almost-surely binary
outcomes](hyp:hy), and [an admissible nuisance perturbation at the population
specification](hyp:hd), for [a baseline interval below the final level](hyp:hk) and
[a positive policy-level index within that interval's range](hyp:hj), [the regular
weight perturbation times the difference between the population binary component
score and its lower-band plug-in expression is integrable and has expectation zero](goal). -/
lemma population_binary_regular_weight_correction_of_admissible (h : ThresholdCrossing M)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ z x, |dphi z x (M.prop z x)| ≤ B)
    (L : LevelData Z X) (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (hlev : ∀ k, Measurable (L.pLev k)) (cpi : ℝ)
    (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (hy : OutcomeBinaryAE M) (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del))
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k) :
    Integrable (fun o : Obs X Z => regularValue del.gamma k j o.1 *
      (binScoreComponents phi dphi L (eta0Bin M L) k j o -
        hMinus phi L (eta0Bin M L) k j o.1)) (observationLaw M) ∧
    (∫ o : Obs X Z, regularValue del.gamma k j o.1 *
      (binScoreComponents phi dphi L (eta0Bin M L) k j o -
        hMinus phi L (eta0Bin M L) k j o.1) ∂observationLaw M) = 0 := by
  have he := binary_admissible_direction_origin M L (eta0Bin M L) del hd
  obtain ⟨C, hC, hreg⟩ := binary_regular_weight_direction_regular M L (eta0Bin M L) del hd
  let a : RegularIndex L := ⟨(k,j), hk.le, hj⟩
  obtain ⟨hw, hwB⟩ := hreg a
  have iP (m : ℕ) := population_binary_weighted_RP_integrable M L cpi hov hy he m
    (del.gamma a) hw C hwB
  have ip (m : ℕ) := population_binary_weighted_Rp_integrable M L cpi hov he m
    (del.gamma a) hw C hwB
  have iq (l : ℕ) := population_binary_weighted_RqBin_integrable M h dphi hdphi B hB hb
    phi L hL cpi hpol he k l (del.gamma a) hw C hwB
  have hq := population_pooledQBin_measurable M h phi hphi L hlev k j
  have hl := population_pooledQBin_measurable M h phi hphi L hlev k (j-1)
  have hp : Measurable (positiveValue (eta0Bin M L).pLev (k+1)) := by
    unfold positiveValue
    split_ifs
    · exact hlev (k+1)
    · fun_prop
  have hboundary : Measurable (fun x => positiveValue (eta0Bin M L).pLev (k+1) x -
      binFullJ L (eta0Bin M L) k x) := by fun_prop
  have hval : regularValue del.gamma k j = del.gamma a := by
    funext x
    simp only [regularValue, dif_pos (show k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k from ⟨hk.le, hj⟩)]
    rfl
  rw [hval]
  exact population_binary_component_correction_zero M h phi dphi hdphi L hL
    k j (del.gamma a) hw
    (binary_Dbd_measurable phi L (eta0Bin M L) k j hq hl hboundary)
    (binary_Edom_measurable phi L (eta0Bin M L) k j hl hboundary)
    (binary_Iact_measurable phi L (eta0Bin M L) k j hq hl hboundary)
    (iP (k+1)) (iP k) (ip (k+1)) (ip k) (iq j) (iq (j-1))

-- Regular-product corrections remain centered when the other weights change,
-- since none of those weights enters the component score or its plug-in.
-- @node: population_binary_total_weights_orthogonality_of_admissible
/-- Under [the threshold-crossing treatment model](hyp:h), suppose [the policy is a
valid policy map](hyp:hphi), [its derivative at baseline propensities is jointly
measurable](hyp:hdphi), [the derivative bound is nonnegative](hyp:hB), and [the derivative's
absolute value never exceeds that bound](hyp:hb). With [a positive baseline level
count](hyp:hK), [covariate-invariant ordering of baseline and policy levels](hyp:hOrder),
[measurable baseline levels](hyp:hlev), [baseline overlap](hyp:hov), [policy-level
overlap](hyp:hpol), [almost-surely binary outcomes](hyp:hy), and [an admissible nuisance
perturbation at the population specification](hyp:hd), [the expected complete binary
score has derivative zero at zero when all full-interval, regular, and final-bin
weights are varied together linearly in that direction](goal). -/
lemma population_binary_total_weights_orthogonality_of_admissible
    (h : ThresholdCrossing M) (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ z x, |dphi z x (M.prop z x)| ≤ B)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (hlev : ∀ k, Measurable (L.pLev k)) (cpi : ℝ)
    (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (hy : OutcomeBinaryAE M) (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del)) :
    HasDerivAt (fun t : ℝ => ∫ o, psiBin M phi dphi L hK o
      {eta0Bin M L with
        gammaFull := fun a x => (eta0Bin M L).gammaFull a x + t * del.gammaFull a x
        gamma := fun a x => (eta0Bin M L).gamma a x + t * del.gamma a x
        gammaTail := fun x => (eta0Bin M L).gammaTail x + t * del.gammaTail x}
      ∂observationLaw M) 0 0 := by
  let r := fun k j (o : Obs X Z) => regularValue del.gamma k j o.1 *
    (binScoreComponents phi dphi L (eta0Bin M L) k j o - hMinus phi L (eta0Bin M L) k j o.1)
  have hr : ∀ k ∈ Finset.range L.K, ∀ j ∈ Finset.Icc 1 (L.l k),
      Integrable (r k j) (observationLaw M) ∧ (∫ o, r k j o ∂observationLaw M) = 0 := by
    intro k hk j hj
    exact population_binary_regular_weight_correction_of_admissible M h phi dphi hphi
      hdphi B hB hb L hOrder hlev cpi hov hpol hy del hd k j
      (Finset.mem_range.mp hk) (Finset.mem_Icc.mp hj)
  have ir : ∀ k ∈ Finset.range L.K, Integrable
      (fun o => ∑ j ∈ Finset.Icc 1 (L.l k), r k j o) (observationLaw M) := by
    intro k hk
    exact integrable_finsetSum _ (fun j hj => (hr k hk j hj).1)
  have isum := integrable_finsetSum _ ir
  have zsum : (∫ o, ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k), r k j o
      ∂observationLaw M) = 0 := by
    rw [integral_finsetSum _ ir]
    apply Finset.sum_eq_zero
    intro k hk
    rw [integral_finsetSum _ (fun j hj => (hr k hk j hj).1)]
    exact Finset.sum_eq_zero (fun j hj => (hr k hk j hj).2)
  let et := fun t : ℝ => {eta0Bin M L with
    gammaFull := fun a x => (eta0Bin M L).gammaFull a x + t * del.gammaFull a x
    gammaTail := fun x => (eta0Bin M L).gammaTail x + t * del.gammaTail x}
  have ie : ∀ t, Integrable (fun o => psiBin M phi dphi L hK o (et t)) (observationLaw M) := by
    intro t
    have he := binary_admissible_direction_origin M L (eta0Bin M L) del hd
    have ibase := (population_binary_score_mean_of_overlap M h phi dphi hphi hdphi
      B hB hb L hK hOrder hlev cpi hov hpol hy he).1
    obtain ⟨C, hC, hf⟩ := binary_full_weight_direction_regular M L (eta0Bin M L) del hd
    obtain ⟨hm, Ct, hCt, ht⟩ := binary_tail_weight_direction_regular M L (eta0Bin M L) del hd
    have ifull : ∀ k ∈ Finset.range L.K, Integrable (fun o : Obs X Z =>
        fullValue del.gammaFull k o.1 * (RP L (eta0Bin M L) (k+1) o - RP L (eta0Bin M L) k o))
        (observationLaw M) := by
      intro k hk
      let a : Fin L.K := ⟨k, Finset.mem_range.mp hk⟩
      have ip m := population_binary_weighted_RP_integrable M L cpi hov hy he m
        (del.gammaFull a) (hf a).1 C (hf a).2
      simpa only [fullValue, dif_pos (Finset.mem_range.mp hk), mul_sub] using (ip (k+1)).sub' (ip k)
    have it := population_binary_weighted_Rp_integrable M L cpi hov he L.K del.gammaTail hm Ct ht
    dsimp only [et]
    simp_rw [binary_total_full_tail_weight_path]
    exact ibase.fun_add (((integrable_finsetSum _ ifull).sub' (it.const_mul M.yMin)).const_mul t)
  have heq : (fun t : ℝ => ∫ o, psiBin M phi dphi L hK o
      {eta0Bin M L with
        gammaFull := fun a x => (eta0Bin M L).gammaFull a x + t * del.gammaFull a x
        gamma := fun a x => (eta0Bin M L).gamma a x + t * del.gamma a x
        gammaTail := fun x => (eta0Bin M L).gammaTail x + t * del.gammaTail x}
      ∂observationLaw M) =
      (fun t : ℝ => ∫ o, psiBin M phi dphi L hK o (et t) ∂observationLaw M) := by
    funext t
    have hp := binary_total_regular_weight_path M phi dphi L hK (et t) del.gamma
    have hc : ∀ k j o, binScoreComponents phi dphi L (et t) k j o =
        binScoreComponents phi dphi L (eta0Bin M L) k j o := fun _ _ _ => rfl
    have hh : ∀ k j x, hMinus phi L (et t) k j x =
        hMinus phi L (eta0Bin M L) k j x := fun _ _ _ => rfl
    change (∫ o, psiBin M phi dphi L hK o
      {et t with gamma := fun a x => (et t).gamma a x + t * del.gamma a x}
      ∂observationLaw M) = _
    simp_rw [hp, hc, hh]
    rw [integral_add (ie t) (isum.const_mul t), integral_const_mul, zsum, mul_zero, add_zero]
  rw [heq]
  exact population_binary_total_full_tail_weight_orthogonality_of_admissible M h phi dphi
    hphi hdphi B hB hb L hK hOrder hlev cpi hov hpol hy del hd

end Papers.TbsPrteOptimalTransport

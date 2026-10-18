module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousComponentDecoding
public import Papers.TbsPrteOptimalTransport.Helpers.DMLBinaryComponentDecoding
public import Papers.TbsPrteOptimalTransport.Helpers.PolicyDerivativeMeasurability
/-! Joint measurability of policy evaluations and fixed-label oracle scores.
The auxiliary argument may carry the training sigma algebra. Policy derivatives
are evaluated only on the clipped propensity domain. -/
public section
set_option linter.style.openClassical false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Set
open scoped Classical
universe v w

-- These graph lemmas have coupled function arguments that `fun_prop` cannot
-- register as a function-property rule; call them explicitly.
-- @node: measurable_fitted_policy_graph
/-- For [a valid policy map](hyp:hphi), if [the fitted propensity is jointly measurable in the auxiliary input, instrument, and covariates](hyp:hm) and [always lies between zero and one](hyp:hr), then [evaluating the policy at that propensity is jointly measurable in those inputs](goal). -/
lemma measurable_fitted_policy_graph
    {A : Type w} {X Z : Type v} [MeasurableSpace A] [MeasurableSpace X] [MeasurableSpace Z]
    (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (p : A → Z → X → ℝ)
    (hm : Measurable (fun azx : A × Z × X => p azx.1 azx.2.1 azx.2.2))
    (hr : ∀ a z x, p a z x ∈ Icc (0 : ℝ) 1) :
    Measurable (fun azx : A × Z × X =>
      phi azx.2.1 azx.2.2 (p azx.1 azx.2.1 azx.2.2)) := by
  exact hphi.1.comp (measurable_snd.fst.prodMk
    (measurable_snd.snd.prodMk (hm.subtype_mk
      (h := fun azx => hr azx.1 azx.2.1 azx.2.2))))

-- @node: measurable_fitted_policy_derivative_graph
/-- For [a valid policy map](hyp:hphi) with [the specified derivative on the propensity domain](hyp:hd), if [the fitted propensity is jointly measurable in the auxiliary input, instrument, and covariates](hyp:hm) and [always lies between zero and one](hyp:hr), then [evaluating the policy derivative at that propensity is jointly measurable in those inputs](goal). -/
lemma measurable_fitted_policy_derivative_graph
    {A : Type w} {X Z : Type v} [MeasurableSpace A] [MeasurableSpace X] [MeasurableSpace Z]
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (p : A → Z → X → ℝ)
    (hm : Measurable (fun azx : A × Z × X => p azx.1 azx.2.1 azx.2.2))
    (hr : ∀ a z x, p a z x ∈ Icc (0 : ℝ) 1) :
    Measurable (fun azx : A × Z × X =>
      dphi azx.2.1 azx.2.2 (p azx.1 azx.2.1 azx.2.2)) := by
  have hp : IsPolicyMap (fun (az : A × Z) (ax : A × X) t => phi az.2 ax.2 t) := by
    refine ⟨?_, fun az ax t ht => hphi.2 az.2 ax.2 t ht⟩
    exact hphi.1.comp (measurable_fst.snd.prodMk
      (measurable_snd.fst.snd.prodMk measurable_snd.snd))
  have hm' : Measurable (fun zax : (A × Z) × (A × X) =>
      p zax.2.1 zax.1.2 zax.2.2) :=
    hm.comp (measurable_snd.fst.prodMk
      (measurable_fst.snd.prodMk measurable_snd.snd))
  have hg := policy_derivative_graph_measurable
    (fun (az : A × Z) (ax : A × X) t => phi az.2 ax.2 t)
    (fun (az : A × Z) (ax : A × X) t => dphi az.2 ax.2 t) hp
    (fun az ax t ht => hd az.2 ax.2 t ht)
    (fun az ax => p ax.1 az.2 ax.2) hm' (fun az ax => hr ax.1 az.2 ax.2)
  exact hg.comp ((measurable_fst.prodMk measurable_snd.fst).prodMk
    (measurable_fst.prodMk measurable_snd.snd))

universe u
variable {Ω : Type u} {X Z : Type v} {A : Type w}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]
  [Fintype Z] [DecidableEq Z]

-- @node: measurable_decoded_binary_score
/-- For [a valid policy map](hyp:hphi) with [the specified derivative](hyp:hd) and [a positive number of levels](hyp:hK), suppose [each encoded nuisance component is jointly measurable in the auxiliary input and covariates](hyp:hm) and [the encoded propensity always lies between zero and one](hyp:hr). Then [the binary score formed by decoding those components is jointly measurable in the auxiliary input and the observation](goal). -/
@[fun_prop] lemma measurable_decoded_binary_score
    (M : LatentIVModel Ω X Z) (phi dphi : Z → X → ℝ → ℝ)
    (hphi : IsPolicyMap phi) (hd : PolicyDifferentiable phi dphi)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (F : A → (ℕ × ℕ × ℕ × Z) → X → ℝ)
    (hm : ∀ c, Measurable (fun ax : A × X => F ax.1 c ax.2))
    (hr : ∀ a z x, F a (0, 0, 0, z) x ∈ Icc (0 : ℝ) 1) :
    Measurable (fun ao : A × Obs X Z =>
      psiBin M phi dphi L hK ao.2 (decodeBinComponents L (F ao.1))) := by
  have hp : Measurable (fun azx : A × Z × X => F azx.1 (0, 0, 0, azx.2.1) azx.2.2) := by
    have hh : Measurable (fun zax : Z × A × X => F zax.2.1 (0, 0, 0, zax.1) zax.2.2) :=
      measurable_from_prod_countable_right (fun z => hm (0, 0, 0, z))
    exact hh.comp (measurable_snd.fst.prodMk
      (measurable_fst.prodMk measurable_snd.snd))
  have hq := measurable_fitted_policy_graph phi hphi
    (fun a z x => F a (0, 0, 0, z) x) hp hr
  have hdq := measurable_fitted_policy_derivative_graph phi dphi hphi hd
    (fun a z x => F a (0, 0, 0, z) x) hp hr
  have hF (c) : Measurable (fun ao : A × Obs X Z => F ao.1 c ao.2.1) := by
    fun_prop
  have hqz (z) : Measurable (fun ao : A × Obs X Z =>
      phi z ao.2.1 (F ao.1 (0, 0, 0, z) ao.2.1)) := by
    exact hq.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd.fst))
  have hdqz (z) : Measurable (fun ao : A × Obs X Z =>
      dphi z ao.2.1 (F ao.1 (0, 0, 0, z) ao.2.1)) := by
    exact hdq.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd.fst))
  have hqo : Measurable (fun ao : A × Obs X Z =>
      phi ao.2.2.1 ao.2.1 (F ao.1 (0, 0, 0, ao.2.2.1) ao.2.1)) := by
    exact hq.comp (measurable_fst.prodMk (measurable_snd.snd.fst.prodMk measurable_snd.fst))
  have hdqo : Measurable (fun ao : A × Obs X Z =>
      dphi ao.2.2.1 ao.2.1 (F ao.1 (0, 0, 0, ao.2.2.1) ao.2.1)) := by
    exact hdq.comp (measurable_fst.prodMk (measurable_snd.snd.fst.prodMk measurable_snd.fst))
  have hpo : Measurable (fun ao : A × Obs X Z =>
      F ao.1 (0, 0, 0, ao.2.2.1) ao.2.1) := by
    exact hp.comp (measurable_fst.prodMk (measurable_snd.snd.fst.prodMk measurable_snd.fst))
  have hv (code k : ℕ) : Measurable (fun ao : A × Obs X Z =>
      positiveValue (fun (i : PositiveIndex L.K) x =>
        F ao.1 (code, i, 0, Classical.choice inferInstance) x) k ao.2.1) := by
    unfold positiveValue
    split_ifs <;> fun_prop
  have hrv (code k j : ℕ) : Measurable (fun ao : A × Obs X Z =>
      regularValue (fun (i : RegularIndex L) x =>
        F ao.1 (code, i.val.1, i.val.2, Classical.choice inferInstance) x)
        k j ao.2.1) := by
    unfold regularValue
    split_ifs <;> fun_prop
  have hfv (code k : ℕ) : Measurable (fun ao : A × Obs X Z =>
      fullValue (fun (i : Fin L.K) x =>
        F ao.1 (code, i, 0, Classical.choice inferInstance) x) k ao.2.1) := by
    unfold fullValue
    split_ifs <;> fun_prop
  have hind (s : Finset Z) : Measurable (fun ao : A × Obs X Z =>
      indicator (ao.2.2.1 ∈ s)) := by
    unfold indicator
    exact Measurable.ite (s.finite_toSet.measurableSet.preimage measurable_snd.snd.fst)
      measurable_const measurable_const
  have hieq (z : Z) : Measurable (fun ao : A × Obs X Z =>
      indicator (ao.2.2.1 = z)) := by
    unfold indicator
    exact Measurable.ite ((measurableSet_singleton z).preimage measurable_snd.snd.fst)
      measurable_const measurable_const
  have hpool (k j : ℕ) : Measurable (fun ao : A × Obs X Z =>
      pooledQBin phi L (decodeBinComponents L (F ao.1)) k j ao.2.1) := by
    unfold pooledQBin
    split_ifs
    · exact hv 1 k
    · exact hv 1 (k + 1)
    · simp only [decodeBinComponents]
      exact Finset.measurable_sum _ (fun z hz => (hF (5, k, j, z)).mul (hqz z))
    · simp only [zero_mul, Finset.sum_const_zero]
      fun_prop
  have hJ (k : ℕ) : Measurable (fun ao : A × Obs X Z =>
      binFullJ L (decodeBinComponents L (F ao.1)) k ao.2.1) := by
    exact (hv 2 (k + 1)).sub (hv 2 k)
  have hRP (k : ℕ) : Measurable (fun ao : A × Obs X Z =>
      RP L (decodeBinComponents L (F ao.1)) k ao.2) := by
    unfold RP
    split_ifs
    · fun_prop
    · change Measurable (fun ao : A × Obs X Z =>
        indicator (ao.2.2.1 ∈ L.S k) / positiveValue
          (fun (i : PositiveIndex L.K) x =>
            F ao.1 (3, i, 0, Classical.choice inferInstance) x) k ao.2.1 *
        (ao.2.2.2.2 * ao.2.2.2.1 - positiveValue
          (fun (i : PositiveIndex L.K) x =>
            F ao.1 (2, i, 0, Classical.choice inferInstance) x) k ao.2.1))
      fun_prop
  have hRp (k : ℕ) : Measurable (fun ao : A × Obs X Z =>
      Rp L (decodeBinComponents L (F ao.1)) k ao.2) := by
    unfold Rp
    split_ifs
    · fun_prop
    · change Measurable (fun ao : A × Obs X Z =>
        indicator (ao.2.2.1 ∈ L.S k) / positiveValue
          (fun (i : PositiveIndex L.K) x =>
            F ao.1 (3, i, 0, Classical.choice inferInstance) x) k ao.2.1 *
        (ao.2.2.2.1 - positiveValue
          (fun (i : PositiveIndex L.K) x =>
            F ao.1 (1, i, 0, Classical.choice inferInstance) x) k ao.2.1))
      fun_prop
  have hRq (k j : ℕ) : Measurable (fun ao : A × Obs X Z =>
      RqBin dphi L (decodeBinComponents L (F ao.1)) k j ao.2) := by
    unfold RqBin
    split_ifs
    · fun_prop
    · simp only [decodeBinComponents]
      exact (hrv 4 k j).inv.mul (Finset.measurable_sum _ (fun z hz =>
        ((hdqz z).mul (hieq z)).mul (measurable_snd.snd.snd.fst.sub (hF (0, 0, 0, z)))))
  have hh (k j : ℕ) : Measurable (fun ao : A × Obs X Z =>
      hMinus phi L (decodeBinComponents L (F ao.1)) k j ao.2.1) := by
    unfold hMinus
    change Measurable (fun ao : A × Obs X Z => max 0
      (pooledQBin phi L (decodeBinComponents L (F ao.1)) k j ao.2.1 -
        max (pooledQBin phi L (decodeBinComponents L (F ao.1)) k (j-1) ao.2.1)
          (positiveValue (fun (i : PositiveIndex L.K) x =>
            F ao.1 (1, i, 0, Classical.choice inferInstance) x)
            (k+1) ao.2.1 - binFullJ L (decodeBinComponents L (F ao.1)) k ao.2.1)))
    fun_prop
  have hbd (k j : ℕ) : Measurable (fun ao : A × Obs X Z =>
      Dbd phi L (decodeBinComponents L (F ao.1)) k j ao.2.1) := by
    unfold Dbd indicator
    apply Measurable.ite _ measurable_const measurable_const
    exact (measurableSet_lt (hpool k (j-1)) ((hv 1 (k+1)).sub (hJ k))).inter
      (measurableSet_lt ((hv 1 (k+1)).sub (hJ k)) (hpool k j))
  have hedom (k j : ℕ) : Measurable (fun ao : A × Obs X Z =>
      Edom phi L (decodeBinComponents L (F ao.1)) k j ao.2.1) := by
    unfold Edom indicator
    apply Measurable.ite _ measurable_const measurable_const
    exact measurableSet_lt ((hv 1 (k+1)).sub (hJ k)) (hpool k (j-1))
  have hact (k j : ℕ) : Measurable (fun ao : A × Obs X Z =>
      Iact phi L (decodeBinComponents L (F ao.1)) k j ao.2.1) := by
    unfold Iact indicator
    apply Measurable.ite _ measurable_const measurable_const
    exact measurableSet_lt ((hpool k (j-1)).max ((hv 1 (k+1)).sub (hJ k))) (hpool k j)
  have hcore (k j : ℕ) : Measurable (fun ao : A × Obs X Z =>
      binScoreComponents phi dphi L (decodeBinComponents L (F ao.1)) k j ao.2) := by
    unfold binScoreComponents
    split_ifs <;> fun_prop
  have hfull (k : ℕ) : Measurable (fun ao : A × Obs X Z =>
      psiFullProdBin L (decodeBinComponents L (F ao.1)) k ao.2) := by
    unfold psiFullProdBin
    change Measurable (fun ao : A × Obs X Z =>
      fullValue (fun (i : Fin L.K) x =>
   F ao.1 (6, i, 0, Classical.choice inferInstance) x) k ao.2.1 *
        (binFullJ L (decodeBinComponents L (F ao.1)) k ao.2.1 +
          RP L (decodeBinComponents L (F ao.1)) (k+1) ao.2 -
          RP L (decodeBinComponents L (F ao.1)) k ao.2) +
      binFullJ L (decodeBinComponents L (F ao.1)) k ao.2.1 *
        (indicator (ao.2.2.1 ∈ higherPolicy L k) - indicator (ao.2.2.1 ∈ higherBaseline L k) -
          fullValue (fun (i : Fin L.K) x =>
   F ao.1 (6, i, 0, Classical.choice inferInstance) x) k ao.2.1))
    fun_prop
  have hprod (k j : ℕ) : Measurable (fun ao : A × Obs X Z =>
      psiProdBin phi dphi L (decodeBinComponents L (F ao.1)) k j ao.2) := by
    unfold psiProdBin
    change Measurable (fun ao : A × Obs X Z =>
      regularValue (fun (i : RegularIndex L) x =>
        F ao.1 (7, i.val.1, i.val.2, Classical.choice inferInstance) x)
        k j ao.2.1 * binScoreComponents phi dphi L (decodeBinComponents L (F ao.1)) k j ao.2 +
      hMinus phi L (decodeBinComponents L (F ao.1)) k j ao.2.1 *
        (indicator (ao.2.2.1 ∈ policyUnion L k j) - regularValue
          (fun (i : RegularIndex L) x =>
            F ao.1 (7, i.val.1, i.val.2, Classical.choice inferInstance) x) k j ao.2.1))
    fun_prop
  have htail : Measurable (fun ao : A × Obs X Z =>
      commonTailScore M phi dphi L
        (fun z x => F ao.1 (0, 0, 0, z) x)
        (fun (i : PositiveIndex L.K) x => F ao.1 (1, i, 0, Classical.choice inferInstance) x)
        (fun (i : PositiveIndex L.K) x => F ao.1 (3, i, 0, Classical.choice inferInstance) x)
        (F ao.1 (8, 0, 0, Classical.choice inferInstance)) ao.2) := by
    have hc : Measurable (fun _ : A × Obs X Z => M.yMin) := measurable_const
    have hfirst := (hc.mul (hind (policyUnion L L.K 1))).mul
      (hqo.sub (hv 1 L.K))
    have hsecond := ((hc.mul (hind (policyUnion L L.K 1))).mul hdqo).mul
      (measurable_snd.snd.snd.fst.sub hpo)
    have hthird := (((hc.mul (hF (8, 0, 0, Classical.choice inferInstance))).mul
      (hind (L.S L.K))).div (hv 3 L.K)).mul (measurable_snd.snd.snd.fst.sub (hv 1 L.K))
    unfold commonTailScore
    split_ifs
    · exact (hfirst.add hsecond).sub measurable_const
    · exact (hfirst.add hsecond).sub hthird
  unfold psiBin
  exact (Finset.measurable_sum _ (fun k hk =>
    (hfull k).add (Finset.measurable_sum _ (fun j hj => hprod k j)))).add htail

-- @node: measurable_decoded_continuous_score
/-- Given [a valid policy map](hyp:hphi), [its specified derivative](hyp:hd), and [a positive number of levels](hyp:hK), if [every encoded nuisance component is jointly measurable in the auxiliary input and covariates](hyp:hm) and [the encoded propensity takes values between zero and one](hyp:hr), then [the continuous-outcome score obtained by decoding the components is jointly measurable in the auxiliary input and the observation](goal). -/
@[fun_prop] lemma measurable_decoded_continuous_score
    (M : LatentIVModel Ω X Z) (phi dphi : Z → X → ℝ → ℝ)
    (hphi : IsPolicyMap phi) (hd : PolicyDifferentiable phi dphi)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (F : A → (ℕ × ℕ × ℕ × Z) → X → ℝ)
    (hm : ∀ c, Measurable (fun ax : A × X => F ax.1 c ax.2))
    (hr : ∀ a z x, F a (0, 0, 0, z) x ∈ Icc (0 : ℝ) 1) :
    Measurable (fun ao : A × Obs X Z =>
      psiCont M phi dphi L hK ao.2 (decodeContComponents L (F ao.1))) := by
  have hp : Measurable (fun azx : A × Z × X => F azx.1 (0, 0, 0, azx.2.1) azx.2.2) := by
    have hh : Measurable (fun zax : Z × A × X => F zax.2.1 (0, 0, 0, zax.1) zax.2.2) :=
      measurable_from_prod_countable_right (fun z => hm (0, 0, 0, z))
    exact hh.comp (measurable_snd.fst.prodMk
      (measurable_fst.prodMk measurable_snd.snd))
  have hq := measurable_fitted_policy_graph phi hphi
    (fun a z x => F a (0, 0, 0, z) x) hp hr
  have hdq := measurable_fitted_policy_derivative_graph phi dphi hphi hd
    (fun a z x => F a (0, 0, 0, z) x) hp hr
  have hF (c) : Measurable (fun ao : A × Obs X Z => F ao.1 c ao.2.1) := by
    fun_prop
  have hqz (z) : Measurable (fun ao : A × Obs X Z =>
      phi z ao.2.1 (F ao.1 (0, 0, 0, z) ao.2.1)) := by
    exact hq.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd.fst))
  have hdqz (z) : Measurable (fun ao : A × Obs X Z =>
      dphi z ao.2.1 (F ao.1 (0, 0, 0, z) ao.2.1)) := by
    exact hdq.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd.fst))
  have hqo : Measurable (fun ao : A × Obs X Z =>
      phi ao.2.2.1 ao.2.1 (F ao.1 (0, 0, 0, ao.2.2.1) ao.2.1)) := by
    exact hq.comp (measurable_fst.prodMk (measurable_snd.snd.fst.prodMk measurable_snd.fst))
  have hdqo : Measurable (fun ao : A × Obs X Z =>
      dphi ao.2.2.1 ao.2.1 (F ao.1 (0, 0, 0, ao.2.2.1) ao.2.1)) := by
    exact hdq.comp (measurable_fst.prodMk (measurable_snd.snd.fst.prodMk measurable_snd.fst))
  have hpo : Measurable (fun ao : A × Obs X Z =>
      F ao.1 (0, 0, 0, ao.2.2.1) ao.2.1) := by
    exact hp.comp (measurable_fst.prodMk (measurable_snd.snd.fst.prodMk measurable_snd.fst))
  have hv (code k : ℕ) : Measurable (fun ao : A × Obs X Z =>
      positiveValue (fun (i : PositiveIndex L.K) x =>
        F ao.1 (code, i, 0, Classical.choice inferInstance) x) k ao.2.1) := by
    unfold positiveValue
    split_ifs <;> fun_prop
  have hrv (code k j : ℕ) : Measurable (fun ao : A × Obs X Z =>
      regularValue (fun (i : RegularIndex L) x =>
        F ao.1 (code, i.val.1, i.val.2, Classical.choice inferInstance) x)
        k j ao.2.1) := by
    unfold regularValue
    split_ifs <;> fun_prop
  have hfv (code k : ℕ) : Measurable (fun ao : A × Obs X Z =>
      fullValue (fun (i : Fin L.K) x =>
        F ao.1 (code, i, 0, Classical.choice inferInstance) x) k ao.2.1) := by
    unfold fullValue
    split_ifs <;> fun_prop
  have hind (s : Finset Z) : Measurable (fun ao : A × Obs X Z =>
      indicator (ao.2.2.1 ∈ s)) := by
    unfold indicator
    exact Measurable.ite (s.finite_toSet.measurableSet.preimage measurable_snd.snd.fst)
      measurable_const measurable_const
  have hieq (z : Z) : Measurable (fun ao : A × Obs X Z =>
      indicator (ao.2.2.1 = z)) := by
    unfold indicator
    exact Measurable.ite ((measurableSet_singleton z).preimage measurable_snd.snd.fst)
      measurable_const measurable_const
  have hnu (k j : ℕ) : Measurable (fun ao : A × Obs X Z =>
      nuValue M (decodeContComponents L (F ao.1)) k j ao.2.1) := by
    simp only [nuValue, decodeContComponents]
    split_ifs <;> fun_prop
  have hbp (k j : ℕ) : Measurable (fun ao : A × Obs X Z =>
      boundaryValue (decodeContComponents L (F ao.1)).Mplus k j ao.2.1) := by
    simp only [boundaryValue, decodeContComponents]
    split_ifs <;> fun_prop
  have hbm (k j : ℕ) : Measurable (fun ao : A × Obs X Z =>
      minusBoundaryValue (decodeContComponents L (F ao.1)).Mminus k j ao.2.1) := by
    simp only [minusBoundaryValue, decodeContComponents]
    split_ifs <;> fun_prop
  have hmp (k j : ℕ) : Measurable (fun ao : A × Obs X Z =>
      meanValue (decodeContComponents L (F ao.1)).Jplus k j ao.2.1) := by
    simp only [meanValue, decodeContComponents]
    split_ifs <;> fun_prop
  have hmm (k j : ℕ) : Measurable (fun ao : A × Obs X Z =>
      minusMeanValue (decodeContComponents L (F ao.1)).Jminus k j ao.2.1) := by
    simp only [minusMeanValue, decodeContComponents]
    split_ifs <;> fun_prop
  have hfm (k : ℕ) : Measurable (fun ao : A × Obs X Z =>
      minusFullValue (decodeContComponents L (F ao.1)) k ao.2.1) := by
    simp only [minusFullValue, decodeContComponents]
    split_ifs <;> fun_prop
  have hpool (k j : ℕ) : Measurable (fun ao : A × Obs X Z =>
      pooledQ phi L (decodeContComponents L (F ao.1)) k j ao.2.1) := by
    unfold pooledQ shareValue
    split_ifs
    · exact hv 1 k
    · exact hv 1 (k + 1)
    · simp only [decodeContComponents]
      exact Finset.measurable_sum _ (fun z hz => (hF (4, k, j, z)).mul (hqz z))
    · simp only [zero_mul, Finset.sum_const_zero]
      fun_prop
  have hRp (k : ℕ) : Measurable (fun ao : A × Obs X Z =>
      RpCont L (decodeContComponents L (F ao.1)) k ao.2) := by
    unfold RpCont
    split_ifs
    · fun_prop
    · change Measurable (fun ao : A × Obs X Z =>
        indicator (ao.2.2.1 ∈ L.S k) / positiveValue
          (fun (i : PositiveIndex L.K) x =>
            F ao.1 (2, i, 0, Classical.choice inferInstance) x) k ao.2.1 *
        (ao.2.2.2.1 - positiveValue
          (fun (i : PositiveIndex L.K) x =>
            F ao.1 (1, i, 0, Classical.choice inferInstance) x) k ao.2.1))
      fun_prop
  have hRq (k j : ℕ) : Measurable (fun ao : A × Obs X Z =>
      RqCont dphi L (decodeContComponents L (F ao.1)) k j ao.2) := by
    unfold RqCont
    split_ifs
    · fun_prop
    · simp only [decodeContComponents]
      exact (hrv 3 k j).inv.mul (Finset.measurable_sum _ (fun z hz =>
        ((hdqz z).mul (hieq z)).mul (measurable_snd.snd.snd.fst.sub (hF (0, 0, 0, z)))))
  have hiband (k j : ℕ) : Measurable (fun ao : A × Obs X Z =>
      indicator (nuValue M (decodeContComponents L (F ao.1)) k j ao.2.1 < ao.2.2.2.2 ∧
        ao.2.2.2.2 ≤ nuValue M (decodeContComponents L (F ao.1)) k (j+1) ao.2.1)) := by
    unfold indicator
    exact Measurable.ite
      ((measurableSet_lt (hnu k j) measurable_snd.snd.snd.snd).inter
        (measurableSet_le measurable_snd.snd.snd.snd (hnu k (j+1))))
      measurable_const measurable_const
  have hiboundary (k j : ℕ) : Measurable (fun ao : A × Obs X Z =>
      indicator (ao.2.2.2.2 ≤ nuValue M (decodeContComponents L (F ao.1)) k j ao.2.1)) := by
    unfold indicator
    exact Measurable.ite (measurableSet_le measurable_snd.snd.snd.snd (hnu k j))
      measurable_const measurable_const
  have hIFJ (plus : Bool) (k j : ℕ) : Measurable (fun ao : A × Obs X Z =>
      IFJ M L (decodeContComponents L (F ao.1)) plus k j ao.2) := by
    unfold IFJ
    split_ifs <;> fun_prop
  have hIFM (plus : Bool) (k j : ℕ) : Measurable (fun ao : A × Obs X Z =>
      IFM M L (decodeContComponents L (F ao.1)) plus k j ao.2) := by
    unfold IFM
    split_ifs <;> fun_prop
  have hJ (k j : ℕ) : Measurable (fun ao : A × Obs X Z =>
      contJ L (decodeContComponents L (F ao.1)) k j ao.2.1) := by
    exact ((hv 1 (k+1)).mul (hmp k j)).sub ((hv 1 k).mul (hmm k j))
  have hfullJ (k : ℕ) : Measurable (fun ao : A × Obs X Z =>
      contFullJ L (decodeContComponents L (F ao.1)) k ao.2.1) := by
    exact ((hv 1 (k+1)).mul (hfv 13 k)).sub ((hv 1 k).mul (hfm k))
  have halow (k j : ℕ) : Measurable (fun ao : A × Obs X Z =>
      alphaLow M L (decodeContComponents L (F ao.1)) k j ao.2.1) := by
    unfold alphaLow
    fun_prop
  have hahigh (k j : ℕ) : Measurable (fun ao : A × Obs X Z =>
      alphaHigh M L (decodeContComponents L (F ao.1)) k j ao.2.1) := by
    unfold alphaHigh
    fun_prop
  have hcore (k j : ℕ) : Measurable (fun ao : A × Obs X Z =>
      contScoreComponents M phi dphi L (decodeContComponents L (F ao.1)) k j ao.2) := by
    unfold contScoreComponents
    dsimp only
    split_ifs <;> fun_prop
  have hpsiFullJ (k : ℕ) : Measurable (fun ao : A × Obs X Z =>
      psiFullJ L (decodeContComponents L (F ao.1)) k ao.2) := by
    unfold psiFullJ
    dsimp only
    split_ifs <;> fun_prop
  have hfull (k : ℕ) : Measurable (fun ao : A × Obs X Z =>
      psiFullProd L (decodeContComponents L (F ao.1)) k ao.2) := by
    unfold psiFullProd
    fun_prop
  have hprod (k j : ℕ) : Measurable (fun ao : A × Obs X Z =>
      psiProd M phi dphi L (decodeContComponents L (F ao.1)) k j ao.2) := by
    unfold psiProd
    fun_prop
  have htail : Measurable (fun ao : A × Obs X Z =>
      commonTailScore M phi dphi L
        (fun z x => F ao.1 (0, 0, 0, z) x)
        (fun (i : PositiveIndex L.K) x => F ao.1 (1, i, 0, Classical.choice inferInstance) x)
        (fun (i : PositiveIndex L.K) x => F ao.1 (2, i, 0, Classical.choice inferInstance) x)
        (F ao.1 (7, 0, 0, Classical.choice inferInstance)) ao.2) := by
    have hc : Measurable (fun _ : A × Obs X Z => M.yMin) := measurable_const
    have hfirst := (hc.mul (hind (policyUnion L L.K 1))).mul (hqo.sub (hv 1 L.K))
    have hsecond := ((hc.mul (hind (policyUnion L L.K 1))).mul hdqo).mul
      (measurable_snd.snd.snd.fst.sub hpo)
    have hthird := (((hc.mul (hF (7, 0, 0, Classical.choice inferInstance))).mul
      (hind (L.S L.K))).div (hv 2 L.K)).mul (measurable_snd.snd.snd.fst.sub (hv 1 L.K))
    unfold commonTailScore
    split_ifs
    · exact (hfirst.add hsecond).sub measurable_const
    · exact (hfirst.add hsecond).sub hthird
  unfold psiCont
  exact (Finset.measurable_sum _ (fun k hk =>
    (hfull k).add (Finset.measurable_sum _ (fun j hj => hprod k j)))).add htail

-- Coordinate measurability is relative to the training view, so the score
-- remains a training predictor even though its argument is a new observation.
-- @node: training_measurable_binary_score_of_components
/-- For [a valid policy map](hyp:hphi) with [the specified derivative](hyp:hd) and [a positive level count](hyp:hK), if [each fitted binary nuisance component is measurable using only the training view and its prediction covariates](hyp:hm) and [all fitted propensities lie between zero and one](hyp:hr), then [the fitted binary score is measurable using only the training view and a new observation](goal). -/
lemma training_measurable_binary_score_of_components
    (M : LatentIVModel Ω X Z) {μ : Measure A} [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ : SampleSplit A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (L : LevelData Z X)
    (hK : LevelCountPos L.K) (eh : ℕ → A → NuisanceBin L)
    (hm : ∀ c, TrainingPredictorMeasurable M S I₁
      (fun n a => binComponent L (eh n a) c))
    (hr : ∀ n a z x, (eh n a).prop z x ∈ Icc (0 : ℝ) 1) :
    TrainingPredictorMeasurable M S I₁
      (fun n a o => psiBin M phi dphi L hK o (eh n a)) := by
  dsimp only [TrainingPredictorMeasurable] at hm ⊢
  intro n
  let mTrain : MeasurableSpace A :=
    MeasurableSpace.comap (trainingView M S I₁ n) inferInstance
  let : MeasurableSpace A := mTrain
  have hf : Measurable[mTrain.prod inferInstance] (fun ao : A × Obs X Z =>
      psiBin M phi dphi L hK ao.2
        (decodeBinComponents L (binComponent L (eh n ao.1)))) :=
    measurable_decoded_binary_score M phi dphi hphi hd L hK
    (fun a => binComponent L (eh n a)) (fun c => hm c n) (hr n)
  simp only [psiBin_decodeBinComponents_binComponent] at hf
  convert hf using 1
  funext ⟨a, o⟩
  exact Function.uncurry_apply_pair _ a o

-- @node: training_measurable_continuous_score_of_components
/-- With [a valid policy map](hyp:hphi), [its specified derivative](hyp:hd), and [a positive level count](hyp:hK), assume [every fitted continuous-outcome nuisance component is measurable from the training view and its prediction covariates](hyp:hm) and [the fitted propensities always lie between zero and one](hyp:hr). Then [the resulting continuous-outcome score is measurable from the training view and a new observation](goal). -/
lemma training_measurable_continuous_score_of_components
    (M : LatentIVModel Ω X Z) {μ : Measure A} [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ : SampleSplit A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (L : LevelData Z X)
    (hK : LevelCountPos L.K) (eh : ℕ → A → NuisanceCont L)
    (hm : ∀ c, TrainingPredictorMeasurable M S I₁
      (fun n a => contComponent M L (eh n a) c))
    (hr : ∀ n a z x, (eh n a).prop z x ∈ Icc (0 : ℝ) 1) :
    TrainingPredictorMeasurable M S I₁
      (fun n a o => psiCont M phi dphi L hK o (eh n a)) := by
  dsimp only [TrainingPredictorMeasurable] at hm ⊢
  intro n
  let mTrain : MeasurableSpace A :=
    MeasurableSpace.comap (trainingView M S I₁ n) inferInstance
  let : MeasurableSpace A := mTrain
  have hf : Measurable[mTrain.prod inferInstance] (fun ao : A × Obs X Z =>
      psiCont M phi dphi L hK ao.2
        (decodeContComponents L (contComponent M L (eh n ao.1)))) :=
    measurable_decoded_continuous_score M phi dphi hphi hd L hK
    (fun a => contComponent M L (eh n a)) (fun c => hm c n) (hr n)
  simp only [psiCont_decodeContComponents_contComponent] at hf
  convert hf using 1
  funext ⟨a, o⟩
  exact Function.uncurry_apply_pair _ a o

end Papers.TbsPrteOptimalTransport

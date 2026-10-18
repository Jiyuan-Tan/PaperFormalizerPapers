module
public import Papers.TbsPrteOptimalTransport.TJSpecialization
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationBinaryMoments
/-! Identification of the population binary plug-in with the discrete target.
The normalized instrument shares recover each common policy level. The binary
quantile-band specialization then identifies every term of the plug-in target. -/
public section
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set
open scoped Classical

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: population_binary_baseline_value
/-- If [baseline and policy propensity levels have covariate-invariant ordering](hyp:hL)
and [the baseline index is at most the final level](hyp:hk), [the population binary
baseline propensity value equals the recorded baseline level at every covariate value](goal). -/
lemma population_binary_baseline_value (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (k : ℕ) (hk : k ≤ L.K) (x : X) :
    positiveValue (eta0Bin M L).pLev k x = L.pLev k x := by
  by_cases hk0 : k = 0
  · subst k
    rw [hL.1 x 0 (by omega)]
    simp [positiveValue, pLevel]
  · simp only [positiveValue, dif_pos (show 1 ≤ k ∧ k ≤ L.K from ⟨by omega, hk⟩),
      eta0Bin]

-- @node: population_binary_success_value
/-- For [a baseline index at most the final level](hyp:hk), [the population binary
treated-success value equals the population treated-success probability at that
level and covariate value](goal). -/
lemma population_binary_success_value (L : LevelData Z X) (k : ℕ)
    (hk : k ≤ L.K) (x : X) :
    positiveValue (eta0Bin M L).P1 k x = treatedSuccess M L k x := by
  by_cases hk0 : k = 0
  · subst k
    simp [positiveValue, treatedSuccess]
  · simp only [positiveValue, dif_pos (show 1 ≤ k ∧ k ≤ L.K from ⟨by omega, hk⟩),
      eta0Bin]

-- @node: population_binary_full_contrast_eq_Jfull
/-- Under [the structural model assumptions](hyp:h), [known outcome endpoints](hyp:he),
and [a finite instrument reduction](hyp:hf), if [baseline and policy levels have
covariate-invariant ordering](hyp:hL) and [the baseline interval lies below the final
level](hyp:hk), [the population binary treated-success contrast equals the full-interval
outcome contribution for almost every covariate value](goal). -/
lemma population_binary_full_contrast_eq_Jfull (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) (hf : InstrumentFiniteReduction Z)
    (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (k : ℕ) (hk : k < L.K) :
    ∀ᵐ x ∂xLaw M, binFullJ L (eta0Bin M L) k x = Jfull M L k x := by
  filter_upwards [discrete_Jfull_eq_treatedSuccess_increment M h he hf q L hL k hk]
    with x hx
  rw [binFullJ, population_binary_success_value M L (k+1) (by omega),
    population_binary_success_value M L k hk.le, hx]

-- @node: ordered_policy_level_nonempty
/-- If [baseline and policy levels have covariate-invariant ordering](hyp:hL),
[the baseline index is at most the final level](hyp:hk), [the policy-level index
is positive](hyp:hj0), and [it does not exceed the number of policy levels in that
baseline interval](hyp:hj), [at least one instrument value belongs to that policy-level set](goal). -/
lemma ordered_policy_level_nonempty (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (k j : ℕ)
    (hk : k ≤ L.K) (hj0 : 1 ≤ j) (hj : j ≤ L.l k) :
    (L.T k j).Nonempty := by
  let x : X := Classical.choice (inferInstance : Nonempty X)
  have hidx : j - 1 < (policyLevelsAt M.prop q x k).length := by
    rw [hL.2.2.2.2.1 x k hk]
    omega
  have hm : L.qLev k j x ∈ policyLevelsAt M.prop q x k := by
    rw [hL.2.1 x k j hk (by omega), if_neg (by omega), if_pos hj,
      List.getD_eq_getElem _ _ hidx]
    exact List.getElem_mem hidx
  simp only [policyLevelsAt, Finset.mem_sort, Finset.mem_filter] at hm
  obtain ⟨z, _, hz⟩ := Finset.mem_image.mp hm.1
  exact ⟨z, (hL.2.2.2.2.2.2.1 x k j z hk hj0 hj).mpr hz⟩

-- @node: population_policy_level_shares_sum_one
/-- Under [covariate-invariant ordering of baseline and policy levels](hyp:hL) and
[policy-level overlap with the specified positive lower bound](hyp:hov), for
[a baseline index at most the final level](hyp:hk) and a policy-level index
[that is positive](hyp:hj0) and [within the interval's range](hyp:hj), [the normalized
instrument shares in that policy-level set sum to one at every covariate value](goal). -/
lemma population_policy_level_shares_sum_one (q : Z → X → ℝ)
    (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (cpi : ℝ) (hov : PolicyOverlap M L cpi) (k j : ℕ)
    (hk : k ≤ L.K) (hj0 : 1 ≤ j) (hj : j ≤ L.l k) (x : X) :
    ∑ z ∈ L.T k j, levelShares M L k j z x = 1 := by
  have hp : 0 < (levelSetProb M L).2 k j x := hov.1.trans_le
    (hov.2 x k j hk hj0 hj (ordered_policy_level_nonempty M q L hL k j hk hj0 hj))
  calc
    _ = ∑ z ∈ L.T k j, instProb M z x / (levelSetProb M L).2 k j x := by
      apply Finset.sum_congr rfl
      intro z hz
      simp only [levelShares, if_pos hz]
    _ = (∑ z ∈ L.T k j, instProb M z x) / (levelSetProb M L).2 k j x :=
      (Finset.sum_div _ _ _).symm
    _ = 1 := div_self hp.ne'

-- @node: population_pooledQBin_eq_ordered_level
/-- Under [covariate-invariant ordering of baseline and policy levels](hyp:hL) and
[policy-level overlap with the specified positive lower bound](hyp:hov), if
[the baseline index is at most the final level](hyp:hk) and [the policy-level index
is within the interval's range, including zero](hyp:hj), [the pooled population
binary policy propensity equals the recorded ordered policy level at every covariate value](goal). -/
lemma population_pooledQBin_eq_ordered_level (phi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : PolicyOverlap M L cpi) (k j : ℕ)
    (hk : k ≤ L.K) (hj : j ≤ L.l k) (x : X) :
    pooledQBin phi L (eta0Bin M L) k j x = L.qLev k j x := by
  by_cases hj0 : j = 0
  · subst j
    rw [pooledQBin, if_pos rfl, population_binary_baseline_value M _ L hL k hk,
      hL.2.1 x k 0 hk (by omega), if_pos rfl]
  · have ha : k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k := ⟨hk, by omega, hj⟩
    simp only [pooledQBin, if_neg hj0, if_neg (not_lt.mpr hj), dif_pos ha, eta0Bin]
    calc
      _ = ∑ z ∈ L.T k j, levelShares M L k j z x * L.qLev k j x := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [show phi z x (M.prop z x) = L.qLev k j x from
          (hL.2.2.2.2.2.2.1 x k j z hk ha.2.1 hj).mp hz]
      _ = (∑ z ∈ L.T k j, levelShares M L k j z x) * L.qLev k j x :=
        (Finset.sum_mul _ _ _).symm
      _ = L.qLev k j x := by
        rw [population_policy_level_shares_sum_one M _ L hL cpi hov k j hk ha.2.1 hj,
          one_mul]

-- @node: population_hMinus_eq_Jband
/-- Under [the structural model assumptions](hyp:h), [known outcome endpoints](hyp:he),
[a finite instrument reduction](hyp:hf), and [binary outcomes](hyp:hb), suppose
[baseline and policy levels have covariate-invariant ordering](hyp:hL) and
[policy-level overlap holds with the specified positive lower bound](hyp:hov).
For [a baseline interval below the final level](hyp:hk) and a policy-level index
[that is positive](hyp:hj0) and [within the interval's range](hyp:hj), [the population
binary lower-band expression equals the lower quantile-band outcome contribution
between the preceding and current policy levels, almost surely over covariates](goal). -/
lemma population_hMinus_eq_Jband (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) (hf : InstrumentFiniteReduction Z)
    (hb : OutcomeBinary M) (phi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : PolicyOverlap M L cpi) (k j : ℕ)
    (hk : k < L.K) (hj0 : 1 ≤ j) (hj : j ≤ L.l k) :
    ∀ᵐ x ∂xLaw M, hMinus phi L (eta0Bin M L) k j x = Jband M false L k (j-1) x := by
  filter_upwards [population_binary_full_contrast_eq_Jfull M h he hf _ L hL k hk,
    binary_discrete_Jband M h hf hb _ L hL k j hk hj0 hj] with x hx hband
  rw [hMinus, population_pooledQBin_eq_ordered_level M phi L hL cpi hov k j hk.le hj,
    population_pooledQBin_eq_ordered_level M phi L hL cpi hov k (j-1) hk.le
      (by omega), population_binary_baseline_value M _ L hL (k+1) (by omega),
    hx, hband]

-- @node: population_mBin_integral_eq_discreteTarget
/-- Under [the structural model assumptions](hyp:h), [known outcome endpoints](hyp:he),
[a finite instrument reduction](hyp:hf), [binary outcomes](hyp:hb), [covariate-invariant
ordering of baseline and policy levels](hyp:hL), and [policy-level overlap with the
specified positive lower bound](hyp:hov), [the covariate average of the population
binary plug-in expression equals the discrete lower target for the policy propensity](goal). -/
lemma population_mBin_integral_eq_discreteTarget (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) (hf : InstrumentFiniteReduction Z)
    (hb : OutcomeBinary M) (phi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : PolicyOverlap M L cpi) :
    (∫ x, mBin M phi L (eta0Bin M L) x ∂xLaw M) =
      discreteTarget M false L (policyProp phi M.prop) := by
  have hfull : ∀ᵐ x ∂xLaw M, ∀ k, k < L.K →
      binFullJ L (eta0Bin M L) k x = Jfull M L k x := by
    simp only [ae_all_iff]
    intro k hk
    exact population_binary_full_contrast_eq_Jfull M h he hf _ L hL k hk
  have hband : ∀ᵐ x ∂xLaw M, ∀ k, k < L.K → ∀ j, 1 ≤ j → j ≤ L.l k →
      hMinus phi L (eta0Bin M L) k j x = Jband M false L k (j-1) x := by
    simp only [ae_all_iff]
    intro k hk j hj0 hj
    exact population_hMinus_eq_Jband M h he hf hb phi L hL cpi hov k j hk hj0 hj
  unfold discreteTarget
  apply integral_congr_ae
  filter_upwards [hfull, hband] with x hx hbnd
  simp only [mBin]
  congr 1
  · apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have hw : fullValue (eta0Bin M L).gammaFull k x = gammaFull M L k x := by
      simp only [fullValue, dif_pos hk', eta0Bin]
    rw [hw, hx k hk']
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have ha : k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k :=
      ⟨hk'.le, (Finset.mem_Icc.mp hj).1, (Finset.mem_Icc.mp hj).2⟩
    have hw : regularValue (eta0Bin M L).gamma k j x = gamma M L k j x := by
      simp only [regularValue, dif_pos ha, eta0Bin]
    rw [hw, hbnd k hk' j ha.2.1 ha.2.2]
  · rw [population_binary_baseline_value M _ L hL L.K le_rfl]
    rfl

end Papers.TbsPrteOptimalTransport

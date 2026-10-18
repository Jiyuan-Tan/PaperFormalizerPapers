module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLRearrangedVariance
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationBinaryAdmissibility
/-! Variance consistency for the fitted binary regime on exact level recovery.
Training measurability and clipping are obtained from the repaired oracle
construction. Population monotonicity follows from binary gap support;
branch margins remain explicit intermediate inputs for theorem assembly. -/
public section
set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

universe u v
variable {Ω : Type u} {X Z : Type v}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]
  [Fintype Z] [DecidableEq Z]

-- @node: binAdmissible_component_measurable
/-- If [a binary nuisance collection is admissible](hyp:he), then [each of its
encoded component functions is measurable](goal). -/
@[fun_prop] lemma binAdmissible_component_measurable
    (M : LatentIVModel Ω X Z) (L : LevelData Z X) (e : NuisanceBin L)
    (he : BinAdmissible M L e) (c : ℕ × ℕ × ℕ × Z) :
    Measurable (binComponent L e c) := by
  try fun_prop
  rcases he with ⟨_, hp, _, hl, _, ht, _, hs, _, _, hf, _, htail⟩
  rcases c with ⟨code, k, j, z⟩
  unfold binComponent
  dsimp only
  split <;> try dsimp only
  all_goals try simp only [positiveValue, regularValue, fullValue]
  all_goals repeat' first
    | fun_prop
    | split
    | exact hp _
    | exact (hl _).1
    | exact (hl _).2.1
    | exact (hl _).2.2
    | exact (ht _).1
    | exact (ht _).2

-- @node: training_measurable_binary_score_difference
/-- If [the policy map is valid](hyp:hphi) and [has the specified derivative](hyp:hd),
[the level count is positive](hyp:hK), [the fixed reference binary nuisances are
admissible](hyp:he0), [their propensity values lie between zero and one](hyp:hp0),
and [a score is measurable using the training information](hyp:hm), then [subtracting
the binary score evaluated at those reference nuisances preserves training
measurability](goal). -/
lemma training_measurable_binary_score_difference
    (M : LatentIVModel Ω X Z) {A : Type*} [MeasurableSpace A]
    {μ : Measure A} [IsProbabilityMeasure μ] (S : ObservedSample M μ)
    (I₁ : SampleSplit A) (phi dphi : Z → X → ℝ → ℝ)
    (hphi : IsPolicyMap phi) (hd : PolicyDifferentiable phi dphi)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (e0 : NuisanceBin L) (he0 : BinAdmissible M L e0)
    (hp0 : ∀ z x, e0.prop z x ∈ Icc (0 : ℝ) 1)
    (score : ℕ → A → Obs X Z → ℝ)
    (hm : TrainingPredictorMeasurable M S I₁ score) :
    TrainingPredictorMeasurable M S I₁
      (fun n a o => score n a o - psiBin M phi dphi L hK o e0) := by
  have hconst : ∀ c, TrainingPredictorMeasurable M S I₁
      (fun (_ : ℕ) (_ : A) => binComponent L e0 c) := by
    intro c n
    let : MeasurableSpace A :=
      MeasurableSpace.comap (trainingView M S I₁ n) inferInstance
    exact (binAdmissible_component_measurable M L e0 he0 c).comp measurable_snd
  have htruth := training_measurable_binary_score_of_components M S I₁
    phi dphi hphi hd L hK (fun _ _ => e0) hconst (fun _ _ => hp0)
  intro n
  exact (hm n).sub (htruth n)

-- @node: population_binary_Jfull_nonneg
/-- Under [the structural model assumptions](hyp:h), [finite instrument
reduction](hyp:hf), [an almost surely binary outcome](hyp:hy), and [a covariate-invariant
ordering of baseline and policy levels](hyp:hOrder), [every full-gap outcome integral
below the last baseline level is nonnegative for almost every covariate value](goal). -/
lemma population_binary_Jfull_nonneg (M : LatentIVModel Ω X Z) (h : StructuralAssumptions M)
    (hf : InstrumentFiniteReduction Z) (hy : OutcomeBinaryAE M)
    (q : Z → X → ℝ) (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop q L) :
    ∀ᵐ x ∂xLaw M, ∀ k < L.K, 0 ≤ Jfull M L k x := by
  filter_upwards [discrete_gap_law_binary_supported M h hf hy q L hOrder] with x hx
  intro k hk
  have hae : ∀ᵐ y ∂discreteGapLaw M L k x, y = 0 ∨ y = 1 := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
      (ae_iff.mpr (hx k hk) : ∀ᵐ y ∂discreteGapLaw M L k x,
        y ∈ ({0, 1} : Set ℝ))
  have hm : 0 ≤ ∫ y, y ∂discreteGapLaw M L k x := by
    apply integral_nonneg_of_ae
    filter_upwards [hae] with y hy
    rcases hy with rfl | rfl <;> norm_num
  exact mul_nonneg
    (sub_nonneg.mpr (hOrder.2.2.2.2.2.2.2.1 x k (k+1) (by omega) (by omega)).le) hm

-- @node: population_binary_success_increment_nonneg
/-- Under [the structural model assumptions](hyp:h), [known outcome endpoints](hyp:he),
[finite instrument reduction](hyp:hf), [an almost surely binary outcome](hyp:hy), and
[a covariate-invariant ordering of baseline and policy levels](hyp:hOrder), [treated
success probabilities weakly increase between consecutive baseline levels for
almost every covariate value](goal). -/
lemma population_binary_success_increment_nonneg (M : LatentIVModel Ω X Z) (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) (hf : InstrumentFiniteReduction Z)
    (hy : OutcomeBinaryAE M) (q : Z → X → ℝ) (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop q L) :
    ∀ᵐ x ∂xLaw M, ∀ k < L.K,
      treatedSuccess M L k x ≤ treatedSuccess M L (k+1) x := by
  have hid : ∀ᵐ x ∂xLaw M, ∀ k < L.K,
      Jfull M L k x = treatedSuccess M L (k+1) x - treatedSuccess M L k x := by
    simp only [ae_all_iff]
    intro k hk
    exact discrete_Jfull_eq_treatedSuccess_increment M h he hf q L hOrder k hk
  filter_upwards [population_binary_Jfull_nonneg M h hf hy q L hOrder, hid]
    with x hn hi
  intro k hk
  exact sub_nonneg.mp (hi k hk ▸ hn k hk)

-- @node: population_binary_P1_monotone
/-- Under [the structural model assumptions](hyp:h), [known outcome endpoints](hyp:he),
[finite instrument reduction](hyp:hf), [an almost surely binary outcome](hyp:hy), and
[a covariate-invariant ordering of baseline and policy levels](hyp:hOrder), [the
population binary nuisance's treated success probabilities are weakly increasing
over all positive baseline indices for almost every covariate value](goal). -/
lemma population_binary_P1_monotone (M : LatentIVModel Ω X Z) (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) (hf : InstrumentFiniteReduction Z)
    (hy : OutcomeBinaryAE M) (q : Z → X → ℝ) (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop q L) :
    ∀ᵐ x ∂xLaw M, ∀ i j : PositiveIndex L.K,
      i.val ≤ j.val → (eta0Bin M L).P1 i x ≤ (eta0Bin M L).P1 j x := by
  filter_upwards [population_binary_success_increment_nonneg M h he hf hy q L hOrder]
    with x hx
  have hm : ∀ j ≤ L.K, ∀ i ≤ j, treatedSuccess M L i x ≤ treatedSuccess M L j x := by
    intro j
    induction j with
    | zero =>
      intro _ i hi
      have hi0 : i = 0 := by omega
      subst i
      exact le_rfl
    | succ j ih =>
      intro hj i hi
      by_cases hij : i ≤ j
      · exact (ih (by omega) i hij).trans (hx j (by omega))
      · have hij : i = j+1 := by omega
        subst i
        exact le_rfl
  intro i j hij
  exact hm j.val j.property.2 i.val hij


-- @node: binDMLRegime_mean_variance_consistent_on_recovery
/-- For [binary nuisance records fitted on the recovered levels](hyp:eHat), suppose [the sample uses an equal half split](hyp:hSplit), [the policy map is
valid](hyp:hphi), [has the specified derivative](hyp:hd), and [that derivative is
bounded and Lipschitz](hyp:hDerivative); assume [the structural model conditions](hyp:hStruct),
[known outcome endpoints](hyp:hEndpoints), [finite instrument reduction](hyp:hFinite),
and [an almost surely binary outcome](hyp:hy). If [the level count is positive](hyp:hK),
[the baseline level functions are measurable](hyp:hlev), [the baseline and policy
level ordering is invariant across covariates](hyp:hOrder), [policy overlap holds](hyp:hov),
[baseline overlap holds](hyp:hbase), [the fitted nuisances satisfy the finite binary
DML regime](hyp:hr), [the complements of the recovery sets have probabilities tending
to zero](hyp:hG), [the recovered level data equal the population data on those
sets at even sample sizes](hyp:hLevels), and [a positive separation margin](hyp:hsep)
[bounds below every policy-level gap and both distances from the binary branch
threshold, almost surely](hyp:hgap), then [the fitted DML mean converges in probability
to the discrete target and its variance estimator converges in probability to the
population variance of the true binary score, along even sample sizes starting at
two](goal). -/
lemma binDMLRegime_mean_variance_consistent_on_recovery
    (M : LatentIVModel Ω X Z)
    {A : Type*} [MeasurableSpace A] (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (hStruct : StructuralAssumptions M) (hEndpoints : OutcomeEndpointsKnown M)
    (hFinite : InstrumentFiniteReduction Z) (hy : OutcomeBinaryAE M)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hlev : ∀ k, Measurable (L.pLev k))
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : PolicyOverlap M L cpi)
    (hbase : BaselineOverlapWitness M L cpi)
    (pHat : ℕ → A → Z → X → ℝ) (rho : ℕ → ℝ) (gap ch : ℝ)
    (eHat : ∀ n a, NuisanceBin (recoveredData M S I₁ I₂ pHat phi rho gap n a))
    (hr : FiniteBinDMLRegime M μ S I₁ I₂ pHat phi rho gap cpi L ch eHat)
    (G : ℕ → Set A) (hG : Tendsto (fun n => μ (G n)ᶜ) atTop (𝓝 0))
    (hLevels : ∀ n a, a ∈ G n →
      recoveredData M S I₁ I₂ pHat phi rho gap (2 * (n + 1)) a = L)
    (sep : ℝ) (hsep : 0 < sep)
    (hgap : ∀ k ∈ Finset.range L.K, ∀ j ∈ Finset.Icc 1 (L.l k), ∀ᵐ x ∂xLaw M,
      sep ≤ pooledQBin phi L (eta0Bin M L) k j x -
        pooledQBin phi L (eta0Bin M L) k (j - 1) x ∧
      sep ≤ |positiveValue (eta0Bin M L).pLev (k + 1) x -
        binFullJ L (eta0Bin M L) k x -
        pooledQBin phi L (eta0Bin M L) k (j - 1) x| ∧
      sep ≤ |positiveValue (eta0Bin M L).pLev (k + 1) x -
        binFullJ L (eta0Bin M L) k x -
        pooledQBin phi L (eta0Bin M L) k j x|)
 :
    let score := fittedBinScore M S I₁ I₂ pHat phi dphi rho gap eHat
    let truth := fun o => psiBin M phi dphi L hK o (eta0Bin M L)
    let theta := discreteTarget M false L (policyProp phi M.prop)
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => dmlRV M S I₂ score (2 * (n + 1)) a - theta)
      atTop (fun _ _ => 0) ∧
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => varianceRV M S I₂ score (2 * (n + 1)) a) atTop
      (fun _ _ => populationVariance M truth theta) := by
  have he0 := population_binary_nuisance_admissible M hStruct.2.2.2.1 hy
    (policyProp phi M.prop) L hOrder hlev cpi hov
  have hmono := population_binary_P1_monotone M hStruct hEndpoints hFinite hy
    (policyProp phi M.prop) L hOrder
  obtain ⟨oracle, hm, hc, ha, hrate, hscore, hsorted, heq⟩ :=
    binDMLRegime_rearranged_oracle_score_records M μ S I₁ I₂ pHat phi dphi
      hphi hd rho gap cpi L ch hK eHat hr G hG hLevels
  have hdiff := training_measurable_binary_score_difference M S I₁ phi dphi
    hphi hd L hK (eta0Bin M L) he0 M.rangeProp _ hscore
  have hpi (n : ℕ) (a : A) (i : PositiveIndex L.K) :
      ∀ᵐ x ∂xLaw M, cpi / 2 ≤ (rearrangeP1 L (oracle n a)).piLev i x :=
    Eventually.of_forall
      ((rearrangeP1_clipped_denominator_lower_bounds L hK (oracle n a) cpi
        (hc n a).2.2 (hc n a).2.1).1 i)
  have htau (n : ℕ) (a : A) (t : RegularIndex L) :
      ∀ᵐ x ∂xLaw M, cpi / 2 ≤ (rearrangeP1 L (oracle n a)).tauLev t x :=
    Eventually.of_forall
      ((rearrangeP1_clipped_denominator_lower_bounds L hK (oracle n a) cpi
        (hc n a).2.2 (hc n a).2.1).2 t)
  exact binary_encoded_rearranged_mean_variance_on_recovery M μ S I₁ I₂ hSplit
    phi dphi hphi hd hDerivative hStruct hEndpoints hFinite hy L hK hlev hOrder
    cpi hov hbase he0 oracle ha (cpi / 2) sep (by linarith [hbase.1]) hsep
    hpi htau hrate hmono hgap hdiff _ G hG
    (fun n a hna i hi => heq n a hna (S.Z i a))

end Papers.TbsPrteOptimalTransport

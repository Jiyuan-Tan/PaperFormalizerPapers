module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLRecoveryGraphMeasurability
public import Papers.TbsPrteOptimalTransport.Helpers.DMLRecoveryLabelDomains
public import Papers.TbsPrteOptimalTransport.Helpers.DMLBinaryFiniteLabelClipping
public import Papers.TbsPrteOptimalTransport.Helpers.DMLRearrangedOracle
public import Papers.TbsPrteOptimalTransport.Helpers.DMLBinaryPopulationNormality
/-! Countable encodings of finite score labels and measurable selection of
fixed-label functions. Only the finite index domains enter the encoding;
no countability of the covariate or observation space is needed. The resulting
measurable feasible binary statistic inherits its CLT from the population oracle. -/
@[expose] public section
set_option linter.style.haveILetI false
set_option linter.style.openClassical false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Set Filter
open scoped Classical Topology
universe v

-- @node: FiniteScoreLabelCode
/-- For [an instrument category space](hyp:Z), a [finite score-label code](goal)
records the number of levels, the number of sublevels at each level, and the
finite instrument sets attached to those levels and sublevels. -/
abbrev FiniteScoreLabelCode (Z : Type v) :=
  Σ K : ℕ, Σ l : Fin (K + 1) → ℕ,
    (Fin (K + 1) → Finset Z) × ((k : Fin (K + 1)) → Fin (l k + 1) → Finset Z)

-- @node: finiteScoreLabelData
/-- The [level data reconstructed](goal) from [a finite score-label code](hyp:c)
use [the encoded level count](step:1), [the encoded sublevel counts, extended by
zero outside the level range](step:2), [the encoded level instrument sets, extended
by empty sets](step:3), [the encoded sublevel instrument sets, extended by empty
sets outside either index range](step:4), [zero baseline propensity levels](step:5),
and [zero policy propensity levels](step:6). -/
def finiteScoreLabelData {Z X : Type v} (c : FiniteScoreLabelCode Z) : LevelData Z X where
  K := c.1
  l := fun k => if hk : k ≤ c.1 then c.2.1 ⟨k, by omega⟩ else 0
  S := fun k => if hk : k ≤ c.1 then c.2.2.1 ⟨k, by omega⟩ else ∅
  T := fun k j => if hk : k ≤ c.1 then
    if hj : j ≤ c.2.1 ⟨k, by omega⟩ then c.2.2.2 ⟨k, by omega⟩ ⟨j, by omega⟩ else ∅
    else ∅
  pLev := fun _ _ => 0
  qLev := fun _ _ _ => 0

-- @node: finiteScoreLabelCode_of_levelData
/-- The [finite score-label code](goal) of [level data](hyp:L) retains the level
count and the sublevel counts and instrument sets on their finite index domains,
discarding the numerical propensity levels. -/
def finiteScoreLabelCode_of_levelData {Z X : Type v} (L : LevelData Z X) :
    FiniteScoreLabelCode Z :=
  ⟨L.K, (fun k => L.l k), (fun k => L.S k), (fun k j => L.T k j)⟩

-- @node: scoreRecoveryLabels_finiteScoreLabelData
/-- [Encoding level data and reconstructing them leaves their score-recovery
labels unchanged](goal). -/
lemma scoreRecoveryLabels_finiteScoreLabelData {Z X : Type v} (L : LevelData Z X) :
    scoreRecoveryLabels (finiteScoreLabelData (X := X) (finiteScoreLabelCode_of_levelData L)) =
      scoreRecoveryLabels L := by
  apply (scoreRecoveryLabels_eq_iff _ _).mpr
  refine ⟨rfl, ?_⟩
  intro k hk
  refine ⟨?_, ?_, ?_⟩
  · simp [finiteScoreLabelData, finiteScoreLabelCode_of_levelData, hk]
  · simp [finiteScoreLabelData, finiteScoreLabelCode_of_levelData, hk]
  · intro j hj
    simp [finiteScoreLabelData, finiteScoreLabelCode_of_levelData, hk, hj]

-- @node: countable_range_scoreRecoveryLabels
/-- When the instrument category space is countable, [the set of score-recovery
labels attainable by level data is countable](goal). -/
lemma countable_range_scoreRecoveryLabels {Z X : Type v} [Countable Z] :
    (Set.range (scoreRecoveryLabels (Z := Z) (X := X))).Countable := by
  have hc := Set.countable_range (fun c : FiniteScoreLabelCode Z =>
    scoreRecoveryLabels (finiteScoreLabelData (X := X) c))
  apply hc.mono
  rintro _ ⟨L, rfl⟩
  exact ⟨finiteScoreLabelCode_of_levelData L, scoreRecoveryLabels_finiteScoreLabelData L⟩

-- @node: measurable_scoreLabel_selection
/-- If [every event on which the selected level data have given score labels is
measurable](hyp:hlabel), [each fixed-label function is measurable](hyp:hg), and
[the selected function agrees with that fixed-label function whenever their score
labels agree](hyp:heq), then [the selected function is measurable](goal). -/
lemma measurable_scoreLabel_selection {Z X : Type v} [Countable Z]
    {B E : Type*} [MeasurableSpace B] [MeasurableSpace E]
    (L : B → LevelData Z X) (f : B → E)
    (hlabel : ∀ H : LevelData Z X,
      MeasurableSet {b | scoreRecoveryLabels (L b) = scoreRecoveryLabels H})
    (g : LevelData Z X → B → E) (hg : ∀ H, Measurable (g H))
    (heq : ∀ b H, scoreRecoveryLabels (L b) = scoreRecoveryLabels H → f b = g H b) :
    Measurable f := by
  let C := FiniteScoreLabelCode Z
  let t := fun c : C => {b | scoreRecoveryLabels (L b) =
    scoreRecoveryLabels (finiteScoreLabelData (X := X) c)}
  let g' := fun c : C => g (finiteScoreLabelData (X := X) c)
  letI : Nonempty C := ⟨⟨0, (fun _ => 0), (fun _ => ∅), (fun _ _ => ∅)⟩⟩
  obtain ⟨h, hh, hhg⟩ := exists_measurable_piecewise t
    (fun c => hlabel _) g' (fun c => hg _) (fun c d hcd b hb =>
      (heq b _ hb.1).symm.trans (heq b _ hb.2))
  have hfh : f = h := by
    funext b
    let c := finiteScoreLabelCode_of_levelData (L b)
    have hb : b ∈ t c := (scoreRecoveryLabels_finiteScoreLabelData (L b)).symm
    exact (heq b _ hb).trans (hhg c hb).symm
  rw [hfh]
  exact hh

universe u w
variable {Ω : Type u} {X Z : Type v} {B : Type w}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace B]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]
  [Fintype Z] [DecidableEq Z]

-- @node: measurable_rearrangeP1_components
/-- If [every nuisance component is jointly measurable in the fitting input and
covariates](hyp:hm), then [each component remains jointly measurable after clipping
and sorting the positive first-outcome levels](goal). -/
@[fun_prop] lemma measurable_rearrangeP1_components
    (L : LevelData Z X) (e : B → NuisanceBin L)
    (hm : ∀ c, Measurable (fun bx : B × X => binComponent L (e bx.1) c bx.2))
    (c : ℕ × ℕ × ℕ × Z) :
    Measurable (fun bx : B × X => binComponent L (rearrangeP1 L (e bx.1)) c bx.2) := by
  have hP (i : ℕ) : Measurable (fun bx : B × X =>
      min 1 (max 0 (positiveValue (e bx.1).P1 (i + 1) bx.2))) := by
    have hi := hm (2, i + 1, 0, Classical.choice inferInstance)
    change Measurable (fun bx : B × X => positiveValue (e bx.1).P1 (i+1) bx.2) at hi
    fun_prop
  have hsort (k : ℕ) := measurable_mergeSort_getD
    ((List.range L.K).map (fun i (bx : B × X) =>
      min 1 (max 0 (positiveValue (e bx.1).P1 (i + 1) bx.2))))
    (by
      intro f hf
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hf
      exact hP i) (k - 1)
  rcases c with ⟨tag, k, j, z⟩
  match tag with
  | 0 => exact hm (0, k, j, z)
  | 1 => exact hm (1, k, j, z)
  | 2 =>
    by_cases hk : 1 ≤ k ∧ k ≤ L.K
    · simpa only [binComponent, positiveValue, dif_pos hk, rearrangeP1,
        List.map_map, Function.comp_def] using hsort k
    · simp only [binComponent, positiveValue, dif_neg hk]
      fun_prop
  | 3 => exact hm (3, k, j, z)
  | 4 => exact hm (4, k, j, z)
  | 5 => exact hm (5, k, j, z)
  | 6 => exact hm (6, k, j, z)
  | 7 => exact hm (7, k, j, z)
  | t + 8 => exact hm (t + 8, k, j, z)

-- @node: measurable_rearranged_binary_score_of_components
/-- If [the policy is a valid policy map](hyp:hphi) and [has the specified
derivative](hyp:hd), [the number of positive levels is positive](hyp:hK),
[all nuisance components are jointly measurable](hyp:hm), and [fitted propensities
lie between zero and one](hyp:hr), then [the binary score after rearranging the
positive first-outcome levels is jointly measurable in fitting input and observation](goal). -/
@[fun_prop] lemma measurable_rearranged_binary_score_of_components
    (M : LatentIVModel Ω X Z) (phi dphi : Z → X → ℝ → ℝ)
    (hphi : IsPolicyMap phi) (hd : PolicyDifferentiable phi dphi)
    (L : LevelData Z X) (hK : LevelCountPos L.K) (e : B → NuisanceBin L)
    (hm : ∀ c, Measurable (fun bx : B × X => binComponent L (e bx.1) c bx.2))
    (hr : ∀ b z x, (e b).prop z x ∈ Icc (0 : ℝ) 1) :
    Measurable (fun bo : B × Obs X Z =>
      psiBin M phi dphi L hK bo.2 (rearrangeP1 L (e bo.1))) := by
  have hf := measurable_decoded_binary_score M phi dphi hphi hd L hK
    (fun b => binComponent L (rearrangeP1 L (e b)))
    (measurable_rearrangeP1_components L e hm) hr
  simpa only [psiBin_decodeBinComponents_binComponent] using hf

-- @node: measurable_zero_level_binary_tail
/-- If [the policy is a valid policy map](hyp:hphi) and [has the specified
derivative](hyp:hd), [there are no positive levels](hyp:hK), [all nuisance components
are jointly measurable](hyp:hm), and [fitted propensities lie between zero and
one](hyp:hr), then [the common binary tail score is jointly measurable in fitting
input and observation](goal). -/
@[fun_prop] lemma measurable_zero_level_binary_tail
    (M : LatentIVModel Ω X Z) (phi dphi : Z → X → ℝ → ℝ)
    (hphi : IsPolicyMap phi) (hd : PolicyDifferentiable phi dphi)
    (L : LevelData Z X) (hK : L.K = 0) (e : B → NuisanceBin L)
    (hm : ∀ c, Measurable (fun bx : B × X => binComponent L (e bx.1) c bx.2))
    (hr : ∀ b z x, (e b).prop z x ∈ Icc (0 : ℝ) 1) :
    Measurable (fun bo : B × Obs X Z => commonTailScore M phi dphi L
      (e bo.1).prop (e bo.1).pLev (e bo.1).piLev (e bo.1).gammaTail bo.2) := by
  have hp : Measurable (fun bzx : B × Z × X => (e bzx.1).prop bzx.2.1 bzx.2.2) := by
    have hh : Measurable (fun zbx : Z × B × X => (e zbx.2.1).prop zbx.1 zbx.2.2) :=
      measurable_from_prod_countable_right (fun z => hm (0, 0, 0, z))
    exact hh.comp (measurable_snd.fst.prodMk (measurable_fst.prodMk measurable_snd.snd))
  have hq := measurable_fitted_policy_graph phi hphi (fun b => (e b).prop) hp hr
  have hdq := measurable_fitted_policy_derivative_graph phi dphi hphi hd
    (fun b => (e b).prop) hp hr
  have hpo : Measurable (fun bo : B × Obs X Z => (e bo.1).prop bo.2.2.1 bo.2.1) :=
    hp.comp (measurable_fst.prodMk (measurable_snd.snd.fst.prodMk measurable_snd.fst))
  have hqo : Measurable (fun bo : B × Obs X Z =>
      phi bo.2.2.1 bo.2.1 ((e bo.1).prop bo.2.2.1 bo.2.1)) :=
    hq.comp (measurable_fst.prodMk (measurable_snd.snd.fst.prodMk measurable_snd.fst))
  have hdqo : Measurable (fun bo : B × Obs X Z =>
      dphi bo.2.2.1 bo.2.1 ((e bo.1).prop bo.2.2.1 bo.2.1)) :=
    hdq.comp (measurable_fst.prodMk (measurable_snd.snd.fst.prodMk measurable_snd.fst))
  have hind : Measurable (fun bo : B × Obs X Z => indicator (bo.2.2.1 ∈ policyUnion L 0 1)) := by
    unfold indicator
    apply Measurable.ite _ measurable_const measurable_const
    exact (Finset.measurableSet _).preimage measurable_snd.snd.fst
  simp only [commonTailScore, hK, positiveValue, show ¬ (1 ≤ (0 : ℕ) ∧ 0 ≤ 0) by omega,
    ↓reduceDIte, ↓reduceIte, sub_zero]
  exact (((measurable_const.mul hind).mul hqo).add
    (((measurable_const.mul hind).mul hdqo).mul
      (measurable_snd.snd.snd.fst.sub hpo)))

-- @node: measurable_binary_score_random_labels
/-- For [binary nuisance records on the random level structures](hyp:e), if [the policy is a valid policy map](hyp:hphi) and [has the specified
derivative](hyp:hd), [the random score labels are measurable](hyp:hlabels),
[all nuisance components are jointly measurable](hyp:hm), and [fitted propensities
lie between zero and one](hyp:hr), then [the score using the rearranged binary
formula when positive levels exist and the common tail formula otherwise is
jointly measurable in fitting input and observation](goal). -/
@[fun_prop] lemma measurable_binary_score_random_labels
    (M : LatentIVModel Ω X Z) (phi dphi : Z → X → ℝ → ℝ)
    (hphi : IsPolicyMap phi) (hd : PolicyDifferentiable phi dphi)
    (L : B → LevelData Z X) (e : ∀ b, NuisanceBin (L b))
    (hlabels : Measurable (fun b => scoreRecoveryLabels (L b)))
    (hm : ∀ c, Measurable (fun bx : B × X => binComponent (L bx.1) (e bx.1) c bx.2))
    (hr : ∀ b z x, (e b).prop z x ∈ Icc (0 : ℝ) 1) :
    Measurable (fun bo : B × Obs X Z =>
      if h : LevelCountPos (L bo.1).K then
        psiBin M phi dphi (L bo.1) h bo.2 (rearrangeP1 (L bo.1) (e bo.1))
      else commonTailScore M phi dphi (L bo.1)
        (e bo.1).prop (e bo.1).pLev (e bo.1).piLev (e bo.1).gammaTail bo.2) := by
  let F := fun b => binComponent (L b) (e b)
  let g := fun H : LevelData Z X => fun bo : B × Obs X Z =>
    if h : LevelCountPos H.K then
      psiBin M phi dphi H h bo.2 (rearrangeP1 H (decodeBinComponents H (F bo.1)))
    else commonTailScore M phi dphi H
      (decodeBinComponents H (F bo.1)).prop (decodeBinComponents H (F bo.1)).pLev
      (decodeBinComponents H (F bo.1)).piLev (decodeBinComponents H (F bo.1)).gammaTail bo.2
  apply measurable_scoreLabel_selection (fun bo : B × Obs X Z => L bo.1) _
    (fun H => ((hlabels.comp measurable_fst).eq_const _).setOf) g
  · intro H
    have hdcomp := decodeBinComponents_measurable H F hm
    by_cases hk : LevelCountPos H.K
    · simp only [g, dif_pos hk]
      exact measurable_rearranged_binary_score_of_components M phi dphi hphi hd H hk
        (fun b => decodeBinComponents H (F b)) hdcomp hr
    · simp only [g, dif_neg hk]
      exact measurable_zero_level_binary_tail M phi dphi hphi hd H
        (by unfold LevelCountPos at hk; omega)
        (fun b => decodeBinComponents H (F b)) hdcomp hr
  · intro bo H heq
    have hK := (scoreRecoveryLabels_eq_iff _ _).mp heq |>.1
    by_cases hk : LevelCountPos H.K
    · have hk' : LevelCountPos (L bo.1).K := hK.symm ▸ hk
      simp only [dif_pos hk', g, dif_pos hk]
      rw [← psiBin_rearranged_decodeBinComponents_binComponent M phi dphi (L bo.1)
        hk' (e bo.1) bo.2]
      exact psiBin_rearranged_decode_eq_of_scoreLabels_eq M phi dphi (L bo.1) H
        heq hk' hk (F bo.1) bo.2
    · have hk' : ¬ LevelCountPos (L bo.1).K := by simpa only [hK] using hk
      have hzero : H.K = 0 := by unfold LevelCountPos at hk; omega
      have hzero' : (L bo.1).K = 0 := hK.trans hzero
      have hu := policyUnion_eq_of_scoreLabels_eq (L bo.1) H heq 0 1 (by omega)
      simp only [dif_neg hk', g, dif_neg hk, commonTailScore, hzero, hzero',
        positiveValue, show ¬ (1 ≤ (0 : ℕ) ∧ 0 ≤ 0) by omega, ↓reduceDIte,
        ↓reduceIte, sub_zero, hu]
      rfl

-- @node: dynamicBinFit_measurable_fittedBinScore
/-- If [the policy is a valid policy map](hyp:hphi) and [has the specified
derivative](hyp:hd), [the binary nuisance estimates on recovered levels](hyp:eHat)
[satisfy the dynamic binary fitting
conditions](hyp:hfit), and [the sample size is at least two](hyp:hn) and
[even](hyp:heven), then [the fitted binary score is jointly measurable in the
sample realization and observation](goal). -/
@[fun_prop] lemma dynamicBinFit_measurable_fittedBinScore
    (M : LatentIVModel Ω X Z) {μ : Measure B} [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit B)
    (pHat : ℕ → B → Z → X → ℝ) (phi dphi : Z → X → ℝ → ℝ)
    (hphi : IsPolicyMap phi) (hd : PolicyDifferentiable phi dphi)
    (rho : ℕ → ℝ) (gap cpi : ℝ)
    (eHat : ∀ n b, NuisanceBin (recoveredData M S I₁ I₂ pHat phi rho gap n b))
    (hfit : DynamicBinFit M S I₁ I₂ pHat phi rho gap eHat cpi)
    (n : ℕ) (hn : 2 ≤ n) (heven : Even n) :
    Measurable (fun bo : B × Obs X Z =>
      fittedBinScore M S I₁ I₂ pHat phi dphi rho gap eHat n bo.1 bo.2) := by
  rcases hfit with ⟨hSplit, hthreshold, htrain, hrange, hclip, hcoord, hjoint⟩
  have hlabels := equalHalfSplit_measurable_recoveredData_labels M S I₁ I₂ hSplit
    pHat htrain hrange phi hphi rho gap n hn heven
  have hs := measurable_scoreRecoveryLabels_of_measurable_recoveryLabels _ hlabels
  have hc (c) := (measurable_pi_apply c).comp (hjoint n)
  apply measurable_binary_score_random_labels M phi dphi hphi hd _ _ hs hc
  intro b z x
  rw [(hclip n b).1]
  exact hrange n b z x

-- @node: dynamicBinFit_aemeasurable_fittedBinScore_evaluation
/-- If [the policy is a valid policy map](hyp:hphi) and [has the specified
derivative](hyp:hd), and [the binary nuisance estimates on recovered levels](hyp:eHat)
[satisfy the dynamic binary fitting
conditions](hyp:hfit), then [the fitted binary score evaluated at any selected
evaluation-half observation is almost everywhere measurable under the sample law](goal). -/
lemma dynamicBinFit_aemeasurable_fittedBinScore_evaluation
    (M : LatentIVModel Ω X Z) {μ : Measure B} [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit B)
    (pHat : ℕ → B → Z → X → ℝ) (phi dphi : Z → X → ℝ → ℝ)
    (hphi : IsPolicyMap phi) (hd : PolicyDifferentiable phi dphi)
    (rho : ℕ → ℝ) (gap cpi : ℝ)
    (eHat : ∀ n b, NuisanceBin (recoveredData M S I₁ I₂ pHat phi rho gap n b))
    (hfit : DynamicBinFit M S I₁ I₂ pHat phi rho gap eHat cpi)
    (n : ℕ) (i : Fin (n + 1)) :
    AEMeasurable (fun b => fittedBinScore M S I₁ I₂ pHat phi dphi rho gap eHat
      (2 * (n + 1)) b (S.Z (dmlEvaluationIndex n (I₂ (2 * (n + 1)) b) i) b)) μ := by
  have hm := dynamicBinFit_measurable_fittedBinScore M S I₁ I₂ pHat phi dphi hphi hd
    rho gap cpi eHat hfit (2 * (n + 1)) (by omega) (even_two_mul _)
  have hl := equalHalfSplit_evaluationIndex_laws M μ S I₁ I₂ hfit.1 n
  exact (hm.comp (measurable_id.prodMk (hl.2.2.1 i))).aemeasurable

-- @node: binDMLRegime_population_clt_on_recovery
/-- Suppose [the sample is split into equal halves](hyp:hSplit), [the policy is
valid](hyp:hphi), [has the specified derivative](hyp:hd), and [that derivative is
bounded and Lipschitz](hyp:hDerivative). Under [the structural model assumptions](hyp:hStruct),
[known outcome endpoints](hyp:hEndpoints), [finite instrument reduction](hyp:hFinite),
[almost surely binary outcomes](hyp:hy), [a positive level count](hyp:hK),
[measurable baseline levels](hyp:hlev), [invariant level ordering](hyp:hOrder),
[policy overlap](hyp:hov), [baseline overlap](hyp:hbase), and [the finite binary
DML regime](hyp:hr) for [binary nuisance estimates on the recovered levels](hyp:eHat), if [the complements of the recovery events have probabilities
tending to zero](hyp:hG), [score labels agree with the population labels on those
events](hyp:hLabels), [policy levels avoid the boundary](hyp:hOff), and [propensity
gaps have the specified separation](hyp:hGap), then [the fitted evaluation-half
mean, centered at the discrete population target and scaled by the square root
of the half-sample size, converges in distribution to a centered Gaussian with
the population binary-score variance](goal). -/
lemma binDMLRegime_population_clt_on_recovery
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
    (hLabels : ∀ n a, a ∈ G n →
      scoreRecoveryLabels (recoveredData M S I₁ I₂ pHat phi rho gap (2 * (n + 1)) a) =
        scoreRecoveryLabels L)
    (hOff : PolicyLevelOffBoundary L)
    (hGap : PropensityGapSeparationWitness M.prop (policyProp phi M.prop) gap)
 :
    let score := fittedBinScore M S I₁ I₂ pHat phi dphi rho gap eHat
    let truth := fun o => psiBin M phi dphi L hK o (eta0Bin M L)
    let theta := discreteTarget M false L (policyProp phi M.prop)
    Causalean.Stat.Modes.TendstoInLaw (fun _ => μ)
      (fun n a => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (dmlRV M S I₂ score (2 * (n + 1)) a - theta)) atTop
      (ProbabilityTheory.gaussianReal 0
        (Real.toNNReal (populationVariance M truth theta))) := by
  have he0 := population_binary_nuisance_admissible M hStruct.2.2.2.1 hy
    (policyProp phi M.prop) L hOrder hlev cpi hov
  have hmono := population_binary_P1_monotone M hStruct hEndpoints hFinite hy
    (policyProp phi M.prop) L hOrder
  obtain ⟨oracle, hm, hc, ha, hrate, hscore, hsorted, heq⟩ :=
    binDMLRegime_rearranged_oracle_score_records_of_scoreLabels_eq M μ S I₁ I₂ pHat phi dphi
      hphi hd rho gap cpi L ch hK eHat hr G hG hLabels
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
  obtain ⟨hp, hl, hP, hpi', ht, hs, hf, hg, htail⟩ :=
    binary_component_rates_rearranged_oracle_rates M μ L oracle (eta0Bin M L)
      ha he0 hmono hrate
  obtain ⟨ch0, hch0⟩ := hr.2.2.2
  have ho := nuisanceRates_training_population_binary_clt M μ S I₁ I₂
    hSplit phi dphi hphi hd hDerivative hStruct hEndpoints hFinite hy L hK hlev hOrder
    cpi hov hbase he0 (fun n a => rearrangeP1 L (oracle n a)) hsorted
    hOff gap hGap ch0 hch0 (cpi / 2) (by linarith [hbase.1]) hpi htau
    hp hl hP hpi' hs ht hg hf htail hdiff
  dsimp only at ho ⊢
  have hrow := dynamicBinFit_aemeasurable_fittedBinScore_evaluation M S I₁ I₂
    pHat phi dphi hphi hd rho gap cpi eHat hr.1
  have hmeas := equalHalfSplit_dmlRV_aemeasurable_of_evaluation_rows M μ S I₁ I₂
    hSplit (fittedBinScore M S I₁ I₂ pHat phi dphi rho gap eHat) hrow
  apply law_limit_transfer_on_recovery μ _ G _ _ hG
  · intro n a ha
    rw [dmlRV_eq_of_score_eq_on_sample M S I₂ _
      (fun n a o => psiBin M phi dphi L hK o (rearrangeP1 L (oracle n a)))
      (2 * (n + 1)) a (fun i hi => heq n a ha (S.Z i a))]
  · exact fun n => ((hmeas n).sub_const _).const_mul _
  · exact ho

-- @node: binDMLRegime_lower_bound_clt_on_recovery_of_scoreLabels_eq
/-- Suppose [the sample is split into equal halves](hyp:hSplit), [the policy is
valid](hyp:hphi), [has the specified derivative](hyp:hd), and [that derivative is
bounded and Lipschitz](hyp:hDerivative). Under [the structural model assumptions](hyp:hStruct),
[known outcome endpoints](hyp:hend), [separated propensity gaps](hyp:hGap),
[finite instrument reduction](hyp:hFinite), [a positive level count at the reference
covariate](hyp:hK), [invariant level ordering](hyp:hOrder), [baseline overlap](hyp:hov),
[policy overlap](hyp:hpol), [binary nuisance estimates on the recovered levels](hyp:eHat), [the finite binary DML regime](hyp:hr), [policy levels
away from the boundary](hyp:hOff), and [the specified propensity-gap separation](hyp:hgap),
if [recovery-event complements have probabilities tending to zero](hyp:hG) and
[score labels agree with the reference population labels on those events](hyp:hLabels),
then [the fitted evaluation-half mean, centered at the sharp lower transport bound
and scaled by the square root of the half-sample size, converges in distribution
to a centered Gaussian with the population binary-score variance](goal). -/
lemma binDMLRegime_lower_bound_clt_on_recovery_of_scoreLabels_eq
    (M : LatentIVModel Ω X Z) {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] (S : ObservedSample M μ)
    (I₁ I₂ : SampleSplit A) (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (hStruct : StructuralAssumptions M) (hend : OutcomeEndpointsKnown M)
    (x0 : X) (hGap : PropensityGapSeparation M.prop (policyProp phi M.prop))
    (hFinite : InstrumentFiniteReduction Z)
    (hK : LevelCountPos (LevelStructure M.prop (policyProp phi M.prop) x0).K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop)
      (LevelStructure M.prop (policyProp phi M.prop) x0))
    (cpi : ℝ)
    (hov : BaselineOverlapWitness M (LevelStructure M.prop (policyProp phi M.prop) x0) cpi)
    (hpol : PolicyOverlap M (LevelStructure M.prop (policyProp phi M.prop) x0) cpi)
    (pHat : ℕ → A → Z → X → ℝ) (rho : ℕ → ℝ) (gap ch : ℝ)
    (eHat : ∀ n a, NuisanceBin (recoveredData M S I₁ I₂ pHat phi rho gap n a))
    (hr : FiniteBinDMLRegime M μ S I₁ I₂ pHat phi rho gap cpi
      (LevelStructure M.prop (policyProp phi M.prop) x0) ch eHat)
    (hOff : PolicyLevelOffBoundary (LevelStructure M.prop (policyProp phi M.prop) x0))
    (hgap : PropensityGapSeparationWitness M.prop (policyProp phi M.prop) gap)
    (G : ℕ → Set A) (hG : Tendsto (fun n => μ (G n)ᶜ) atTop (𝓝 0))
    (hLabels : ∀ n a, a ∈ G n → scoreRecoveryLabels (recoveredData M S I₁ I₂ pHat phi rho gap
      (2 * (n + 1)) a) = scoreRecoveryLabels (LevelStructure M.prop (policyProp phi M.prop) x0)) :
    let L := LevelStructure M.prop (policyProp phi M.prop) x0
    let score := fittedBinScore M S I₁ I₂ pHat phi dphi rho gap eHat
    let truth := fun o => psiBin M phi dphi L hK o (eta0Bin M L)
    let theta := thetaLower1 (transportData M) (policyWeight M (policyProp phi M.prop))
    Causalean.Stat.Modes.TendstoInLaw (fun _ => μ)
      (fun n a => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (dmlRV M S I₂ score (2 * (n + 1)) a - theta)) atTop
      (ProbabilityTheory.gaussianReal 0
        (Real.toNNReal (populationVariance M truth theta))) := by
  cases Subsingleton.elim ‹DecidableEq Z› (fun a b => Classical.propDecidable (a = b))
  have hlev := population_LevelStructure_baseline_measurable M hStruct.2.2.2.1
    (policyProp phi M.prop) x0 hOrder
  have htarget := (discrete_reduction M hStruct.2.2.2.2.2.2 hend hStruct.1
    hStruct.2.1 hStruct.2.2.1 hStruct.2.2.2.1 hStruct.2.2.2.2.1
    hStruct.2.2.2.2.2.1 phi hphi x0 hGap hOrder hFinite).2.2.1
  dsimp only
  rw [htarget]
  exact binDMLRegime_population_clt_on_recovery M μ S I₁ I₂ hSplit
    phi dphi hphi hd hDerivative hStruct hend hFinite hr.2.2.1 _ hK hlev hOrder
    cpi hpol hov pHat rho gap ch eHat hr G hG hLabels hOff hgap

-- @node: binDMLRegime_clt
/-- Suppose [the sample is split into equal halves](hyp:hSplit), [the policy is
valid](hyp:hphi), [has the specified derivative](hyp:hd), and [that derivative is
bounded and Lipschitz](hyp:hDerivative). Under [the structural model assumptions](hyp:hStruct),
[known outcome endpoints](hyp:hend), [separated propensity gaps](hyp:hGap),
[finite instrument reduction](hyp:hFinite), [a positive level count at the reference
covariate](hyp:hK), [invariant level ordering](hyp:hOrder), [baseline overlap](hyp:hov),
[policy overlap](hyp:hpol), [the finite first-stage convergence rate](hyp:hRate),
[policy levels away from the boundary](hyp:hOff), [the specified propensity-gap
separation](hyp:hgap), and [the finite binary DML regime](hyp:hr) for
[binary nuisance estimates on the recovered levels](hyp:eHat), [the fitted
evaluation-half mean, centered at the sharp lower transport bound and scaled by
the square root of the half-sample size, converges in distribution to a centered
Gaussian with the population binary-score variance](goal). -/
lemma binDMLRegime_clt
    (M : LatentIVModel Ω X Z) {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] (S : ObservedSample M μ)
    (I₁ I₂ : SampleSplit A) (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (hStruct : StructuralAssumptions M) (hend : OutcomeEndpointsKnown M)
    (x0 : X) (hGap : PropensityGapSeparation M.prop (policyProp phi M.prop))
    (hFinite : InstrumentFiniteReduction Z)
    (hK : LevelCountPos (LevelStructure M.prop (policyProp phi M.prop) x0).K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop)
      (LevelStructure M.prop (policyProp phi M.prop) x0))
    (cpi : ℝ)
    (hov : BaselineOverlapWitness M (LevelStructure M.prop (policyProp phi M.prop) x0) cpi)
    (hpol : PolicyOverlap M (LevelStructure M.prop (policyProp phi M.prop) x0) cpi)
    (pHat : ℕ → A → Z → X → ℝ) (hRate : FiniteFirstStageRate M μ pHat)
    (rho : ℕ → ℝ) (gap ch : ℝ)
    (hOff : PolicyLevelOffBoundary (LevelStructure M.prop (policyProp phi M.prop) x0))
    (hgap : PropensityGapSeparationWitness M.prop (policyProp phi M.prop) gap)
    (eHat : ∀ n a, NuisanceBin (recoveredData M S I₁ I₂ pHat phi rho gap n a))
    (hr : FiniteBinDMLRegime M μ S I₁ I₂ pHat phi rho gap cpi
      (LevelStructure M.prop (policyProp phi M.prop) x0) ch eHat) :
    let L := LevelStructure M.prop (policyProp phi M.prop) x0
    let score := fittedBinScore M S I₁ I₂ pHat phi dphi rho gap eHat
    let truth := fun o => psiBin M phi dphi L hK o (eta0Bin M L)
    let theta := thetaLower1 (transportData M) (policyWeight M (policyProp phi M.prop))
    Causalean.Stat.Modes.TendstoInLaw (fun _ => μ)
      (fun n a => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (dmlRV M S I₂ score (2 * (n + 1)) a - theta)) atTop
      (ProbabilityTheory.gaussianReal 0
        (Real.toNNReal (populationVariance M truth theta))) := by
  have hG := binDMLRegime_recoveryEvent_compl_tendsto_zero M μ S I₁ I₂ hStruct.2.2.2.1
    pHat hRate phi dphi hphi hd hDerivative x0 gap cpi rho hOrder hOff hgap hK ch eHat hr
  exact binDMLRegime_lower_bound_clt_on_recovery_of_scoreLabels_eq
    M μ S I₁ I₂ hSplit phi dphi hphi hd hDerivative hStruct hend x0 hGap hFinite hK
    hOrder cpi hov hpol pHat rho gap ch eHat hr hOff hgap
    (fun n => recoveryEvent M S I₁ I₂ pHat phi rho gap
      (LevelStructure M.prop (policyProp phi M.prop) x0) (2 * (n + 1))) hG
    (fun n a ha => (mem_recoveryEvent_iff_scoreRecoveryLabels_eq
      M S I₁ I₂ pHat phi rho gap _ _ a).mp ha)

end Papers.TbsPrteOptimalTransport

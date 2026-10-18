module
public import Papers.TbsPrteOptimalTransport.Helpers.RecoveryExactEvent
/-! Recovery labels restricted to the finite index domains used by the score.
The recovery event identifies these labels, without making any assertion about
the arbitrary extensions of population labels beyond their index domains. -/
@[expose] public section
set_option linter.style.openClassical false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Set Filter
open scoped Classical Topology

universe u v

-- @node: scoreRecoveryLabels
/-- For [a level structure](hyp:L), its [score-relevant recovery labels](goal) consist
of [the number of baseline levels](step:1), [the policy-level counts, set to zero
beyond the baseline index domain](step:2), [the baseline instrument groups, set to
empty beyond that domain](step:3), and [the policy instrument groups, set to empty
outside both valid index domains](step:4). -/
def scoreRecoveryLabels {Z X : Type v} (L : LevelData Z X) :=
  (L.K, (fun k => if k ≤ L.K then L.l k else 0),
    (fun k => if k ≤ L.K then L.S k else ∅),
    (fun k j => if k ≤ L.K ∧ j ≤ L.l k then L.T k j else ∅))

-- @node: scoreRecoveryLabels_eq_iff
/-- [Two level structures have equal score-relevant recovery labels exactly when
their baseline level counts agree and, at every valid baseline index, their
policy-level counts and baseline groups agree and their policy groups agree at
every valid policy index](goal). -/
lemma scoreRecoveryLabels_eq_iff {Z X : Type v} (H L : LevelData Z X) :
    scoreRecoveryLabels H = scoreRecoveryLabels L ↔
      H.K = L.K ∧ ∀ k ≤ L.K, H.l k = L.l k ∧ H.S k = L.S k ∧
        ∀ j ≤ L.l k, H.T k j = L.T k j := by
  constructor
  · intro h
    have hk := congrArg Prod.fst h
    have hl := congrArg (fun t => t.2.1) h
    have hs := congrArg (fun t => t.2.2.1) h
    have ht := congrArg (fun t => t.2.2.2) h
    change H.K = L.K at hk
    refine ⟨hk, ?_⟩
    intro k hkle
    have hkH : k ≤ H.K := hk.symm ▸ hkle
    have hlk : H.l k = L.l k := by
      simpa only [scoreRecoveryLabels, if_pos hkle, if_pos hkH] using congrFun hl k
    refine ⟨hlk, ?_, ?_⟩
    · simpa only [scoreRecoveryLabels, if_pos hkle, if_pos hkH] using congrFun hs k
    · intro j hj
      have hjH : j ≤ H.l k := hlk.symm ▸ hj
      simpa only [scoreRecoveryLabels, if_pos (And.intro hkle hj),
        if_pos (And.intro hkH hjH)] using congrFun (congrFun ht k) j
  · rintro ⟨hk, h⟩
    unfold scoreRecoveryLabels
    apply Prod.ext hk
    apply Prod.ext
    · funext k
      by_cases hkle : k ≤ L.K
      · simp only [hk, if_pos hkle, (h k hkle).1]
      · simp only [hk, if_neg hkle]
    · apply Prod.ext
      · funext k
        by_cases hkle : k ≤ L.K
        · simp only [hk, if_pos hkle, (h k hkle).2.1]
        · simp only [hk, if_neg hkle]
      · funext k j
        dsimp only
        by_cases hkle : k ≤ L.K
        · rw [hk, (h k hkle).1]
          by_cases hj : j ≤ L.l k
          · simp only [if_pos (And.intro hkle hj), (h k hkle).2.2 j hj]
          · simp only [and_false, hj, if_false]
        · simp only [hk, hkle, false_and, if_false]

variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]

-- @node: measurable_scoreRecoveryLabels_of_measurable_recoveryLabels
/-- If [the unrestricted recovery labels of a varying level structure are
measurable](hyp:hm), then [its score-relevant recovery labels are measurable](goal). -/
@[fun_prop] lemma measurable_scoreRecoveryLabels_of_measurable_recoveryLabels
    {B : Type*} [MeasurableSpace B] (L : B → LevelData Z X)
    (hm : Measurable (fun b => recoveryLabels (L b))) :
    Measurable (fun b => scoreRecoveryLabels (L b)) := by
  try fun_prop
  have hk : Measurable (fun b => (L b).K) := hm.fst
  have hl : Measurable (fun b => (L b).l) := hm.snd.fst
  have hs : Measurable (fun b => (L b).S) := hm.snd.snd.fst
  have ht : Measurable (fun b => (L b).T) := hm.snd.snd.snd
  unfold scoreRecoveryLabels
  refine hk.prodMk ((measurable_pi_lambda _ (fun k => ?_)).prodMk
    ((measurable_pi_lambda _ (fun k => ?_)).prodMk
      (measurable_pi_lambda _ (fun k => measurable_pi_lambda _ (fun j => ?_)))))
  · exact Measurable.ite (measurableSet_le measurable_const hk)
      ((measurable_pi_apply k).comp hl) measurable_const
  · exact Measurable.ite (measurableSet_le measurable_const hk)
      ((measurable_pi_apply k).comp hs) measurable_const
  · exact Measurable.ite ((measurableSet_le measurable_const hk).inter
      (measurableSet_le measurable_const ((measurable_pi_apply k).comp hl)))
      ((measurable_pi_apply j).comp ((measurable_pi_apply k).comp ht)) measurable_const

-- @node: mem_recoveryEvent_iff_scoreRecoveryLabels_eq
/-- [A sample realization belongs to the exact recovery event if and only if the
recovered structure and the specified population structure have identical
score-relevant recovery labels](goal). -/
lemma mem_recoveryEvent_iff_scoreRecoveryLabels_eq
    (M : LatentIVModel Ω X Z) {A : Type*} [MeasurableSpace A]
    {μ : Measure A} [IsProbabilityMeasure μ] (S : ObservedSample M μ)
    (I₁ I₂ : SampleSplit A) (pHat : ℕ → A → Z → X → ℝ)
    (phi : Z → X → ℝ → ℝ) (rho : ℕ → ℝ) (gap : ℝ)
    (L : LevelData Z X) (n : ℕ) (a : A) :
    a ∈ recoveryEvent M S I₁ I₂ pHat phi rho gap L n ↔
      scoreRecoveryLabels (recoveredData M S I₁ I₂ pHat phi rho gap n a) =
        scoreRecoveryLabels L := by
  exact (scoreRecoveryLabels_eq_iff _ _).symm

-- @node: contDMLRegime_scoreRecoveryLabels_failure_tendsto_zero
/-- For [continuous nuisance records fitted on the recovered levels](hyp:eHat), suppose [the model satisfies threshold crossing](hyp:h), [the first-stage
estimator satisfies the finite first-stage rate](hyp:hRate), [the policy map is
valid](hyp:hphi), [has the specified derivative](hyp:hd), and [that derivative is
bounded and Lipschitz](hyp:hDerivative). If [the population level ordering is
invariant across covariates](hyp:hL), [policy levels avoid the boundary](hyp:hOff),
[the propensity levels have the specified gap separation](hyp:hgap), [there is a
positive number of baseline levels](hyp:hK), and [the fitted continuous nuisances
and recovery procedure satisfy the finite continuous DML regime](hyp:hr), then
[the probability that the score-relevant recovered labels differ from the population
labels tends to zero along the even sample sizes starting at two](goal). -/
lemma contDMLRegime_scoreRecoveryLabels_failure_tendsto_zero
    (M : LatentIVModel Ω X Z) {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] (S : ObservedSample M μ)
    (I₁ I₂ : SampleSplit A) (h : ThresholdCrossing M)
    (pHat : ℕ → A → Z → X → ℝ) (hRate : FiniteFirstStageRate M μ pHat)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (x0 : X) (gap cpi : ℝ) (rho : ℕ → ℝ)
    (hL : LevelOrderInvariant M.prop (policyProp phi M.prop)
      (LevelStructure M.prop (policyProp phi M.prop) x0))
    (hOff : PolicyLevelOffBoundary (LevelStructure M.prop (policyProp phi M.prop) x0))
    (hgap : PropensityGapSeparationWitness M.prop (policyProp phi M.prop) gap)
    (hK : LevelCountPos' (LevelStructure M.prop (policyProp phi M.prop) x0).K)
    (ch : ℝ)
    (eHat : ∀ n a, NuisanceCont (recoveredData M S I₁ I₂ pHat phi rho gap n a))
    (hr : FiniteContDMLRegime M μ S I₁ I₂ pHat phi rho gap cpi
      (LevelStructure M.prop (policyProp phi M.prop) x0) ch eHat) :
    Tendsto (fun n => μ {a | scoreRecoveryLabels
      (recoveredData M S I₁ I₂ pHat phi rho gap (2 * (n + 1)) a) ≠
        scoreRecoveryLabels (LevelStructure M.prop (policyProp phi M.prop) x0)})
      atTop (𝓝 0) := by
  have hrec := contDMLRegime_recoveryEvent_compl_tendsto_zero M μ S I₁ I₂ h
    pHat hRate phi dphi hphi hd hDerivative x0 gap cpi rho hL hOff hgap hK ch eHat hr
  simpa only [Set.compl_def, mem_recoveryEvent_iff_scoreRecoveryLabels_eq] using hrec

-- @node: binDMLRegime_scoreRecoveryLabels_failure_tendsto_zero
/-- For [binary nuisance records fitted on the recovered levels](hyp:eHat), suppose [the model satisfies threshold crossing](hyp:h), [the first-stage
estimator satisfies the finite first-stage rate](hyp:hRate), [the policy map is
valid](hyp:hphi), [has the specified derivative](hyp:hd), and [that derivative is
bounded and Lipschitz](hyp:hDerivative). If [the population level ordering is
invariant across covariates](hyp:hL), [policy levels avoid the boundary](hyp:hOff),
[the propensity levels have the specified gap separation](hyp:hgap), [there is a
positive number of baseline levels](hyp:hK), and [the fitted binary nuisances and
recovery procedure satisfy the finite binary DML regime](hyp:hr), then [the
probability that the score-relevant recovered labels differ from the population
labels tends to zero along the even sample sizes starting at two](goal). -/
lemma binDMLRegime_scoreRecoveryLabels_failure_tendsto_zero
    (M : LatentIVModel Ω X Z) {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] (S : ObservedSample M μ)
    (I₁ I₂ : SampleSplit A) (h : ThresholdCrossing M)
    (pHat : ℕ → A → Z → X → ℝ) (hRate : FiniteFirstStageRate M μ pHat)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (x0 : X) (gap cpi : ℝ) (rho : ℕ → ℝ)
    (hL : LevelOrderInvariant M.prop (policyProp phi M.prop)
      (LevelStructure M.prop (policyProp phi M.prop) x0))
    (hOff : PolicyLevelOffBoundary (LevelStructure M.prop (policyProp phi M.prop) x0))
    (hgap : PropensityGapSeparationWitness M.prop (policyProp phi M.prop) gap)
    (hK : LevelCountPos' (LevelStructure M.prop (policyProp phi M.prop) x0).K)
    (ch : ℝ)
    (eHat : ∀ n a, NuisanceBin (recoveredData M S I₁ I₂ pHat phi rho gap n a))
    (hr : FiniteBinDMLRegime M μ S I₁ I₂ pHat phi rho gap cpi
      (LevelStructure M.prop (policyProp phi M.prop) x0) ch eHat) :
    Tendsto (fun n => μ {a | scoreRecoveryLabels
      (recoveredData M S I₁ I₂ pHat phi rho gap (2 * (n + 1)) a) ≠
        scoreRecoveryLabels (LevelStructure M.prop (policyProp phi M.prop) x0)})
      atTop (𝓝 0) := by
  have hrec := binDMLRegime_recoveryEvent_compl_tendsto_zero M μ S I₁ I₂ h
    pHat hRate phi dphi hphi hd hDerivative x0 gap cpi rho hL hOff hgap hK ch eHat hr
  simpa only [Set.compl_def, mem_recoveryEvent_iff_scoreRecoveryLabels_eq] using hrec

end Papers.TbsPrteOptimalTransport

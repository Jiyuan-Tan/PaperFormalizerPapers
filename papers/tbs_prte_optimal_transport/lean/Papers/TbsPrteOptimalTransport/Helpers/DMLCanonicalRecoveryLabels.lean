module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLRecoveryLabelDomains
public import Papers.TbsPrteOptimalTransport.Helpers.DMLBoundedFixedLabels
/-! Canonical extensions of the recovered finite label domains.
The recovery construction sets every unused label to zero or the empty set.
Thus finite-domain recovery fixes the entire label input to the training fit,
even when the population labels have arbitrary unused extensions. -/
public section
set_option linter.style.openClassical false
set_option linter.unusedSectionVars false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Set Filter
open scoped Classical Topology
universe u v
variable {X Z : Type v} [Fintype Z] [DecidableEq Z]

-- @node: recoverLevelsAt_policy_count_zero_of_gt
/-- If [a level index exceeds the number of recovered baseline levels](hyp:hk),
[its recovered policy-level count is zero](goal). -/
lemma recoverLevelsAt_policy_count_zero_of_gt
    (pb qb : Z → ℝ) (rho gap : ℝ) (k : ℕ)
    (hk : (recoverLevelsAt pb qb rho gap : LevelData Z X).K < k) :
    (recoverLevelsAt pb qb rho gap : LevelData Z X).l k = 0 := by
  dsimp only [recoverLevelsAt] at hk ⊢
  have hk0 : k ≠ 0 := by omega
  have hk1 : ¬ k ≤ ((recoveryComponents pb qb rho gap).filter
      (fun C => ∃ z, (false, z) ∈ C)).length := by omega
  have hk2 : ¬ k + 1 ≤ ((recoveryComponents pb qb rho gap).filter
      (fun C => ∃ z, (false, z) ∈ C)).length := by omega
  simp [hk0, hk1, hk2, show k ≠
    ((recoveryComponents pb qb rho gap).filter (fun C => ∃ z, (false, z) ∈ C)).length
      by omega]

-- @node: recoverLevelsAt_baseline_label_empty_of_gt
/-- If [a level index exceeds the number of recovered baseline levels](hyp:hk),
[its recovered baseline instrument label is empty](goal). -/
lemma recoverLevelsAt_baseline_label_empty_of_gt
    (pb qb : Z → ℝ) (rho gap : ℝ) (k : ℕ)
    (hk : (recoverLevelsAt pb qb rho gap : LevelData Z X).K < k) :
    (recoverLevelsAt pb qb rho gap : LevelData Z X).S k = ∅ := by
  dsimp only [recoverLevelsAt] at hk ⊢
  have hk0 : k ≠ 0 := by omega
  have hlen : ((recoveryComponents pb qb rho gap).filter
    (fun C => ∃ z, (false, z) ∈ C)).length ≤ k - 1 := by omega
  simp [hk0, hlen]

-- @node: recoverLevelsAt_policy_label_empty_of_gt
/-- If [a policy-level index exceeds the recovered policy-level count at a baseline level](hyp:hj),
[the corresponding recovered policy instrument label is empty](goal). -/
lemma recoverLevelsAt_policy_label_empty_of_gt
    (pb qb : Z → ℝ) (rho gap : ℝ) (k j : ℕ)
    (hj : (recoverLevelsAt pb qb rho gap : LevelData Z X).l k < j) :
    (recoverLevelsAt pb qb rho gap : LevelData Z X).T k j = ∅ := by
  simp only [recoverLevelsAt] at hj ⊢
  rw [if_pos (Or.inr hj)]

-- @node: recoveryLabels_recoverLevelsAt_eq_scoreRecoveryLabels
/-- [The full labels produced by level recovery equal their canonical score labels,
with zero counts and empty labels outside the score domain](goal). -/
lemma recoveryLabels_recoverLevelsAt_eq_scoreRecoveryLabels
    (pb qb : Z → ℝ) (rho gap : ℝ) :
    recoveryLabels (recoverLevelsAt pb qb rho gap : LevelData Z X) =
      scoreRecoveryLabels (recoverLevelsAt pb qb rho gap : LevelData Z X) := by
  let H : LevelData Z X := recoverLevelsAt pb qb rho gap
  change (H.K, H.l, H.S, H.T) =
    (H.K, (fun k => if k ≤ H.K then H.l k else 0),
      (fun k => if k ≤ H.K then H.S k else ∅),
      (fun k j => if k ≤ H.K ∧ j ≤ H.l k then H.T k j else ∅))
  apply Prod.ext
  · rfl
  apply Prod.ext
  · funext k
    dsimp only
    by_cases hk : k ≤ H.K
    · rw [if_pos hk]
    · rw [if_neg hk]
      exact recoverLevelsAt_policy_count_zero_of_gt pb qb rho gap k (by change H.K < k; omega)
  · apply Prod.ext
    · funext k
      dsimp only
      by_cases hk : k ≤ H.K
      · rw [if_pos hk]
      · rw [if_neg hk]
        exact recoverLevelsAt_baseline_label_empty_of_gt pb qb rho gap k (by change H.K < k; omega)
    · funext k j
      dsimp only
      by_cases hk : k ≤ H.K
      · by_cases hj : j ≤ H.l k
        · rw [if_pos ⟨hk, hj⟩]
        · rw [if_neg (by simp only [hj, and_false, not_false_eq_true])]
          exact recoverLevelsAt_policy_label_empty_of_gt pb qb rho gap k j
            (by change H.l k < j; omega)
      · rw [if_neg (by simp only [hk, false_and, not_false_eq_true])]
        have hl : H.l k = 0 :=
          recoverLevelsAt_policy_count_zero_of_gt pb qb rho gap k (by change H.K < k; omega)
        by_cases hj : j = 0
        · subst j
          simp only [H, recoverLevelsAt, true_or, if_true]
        · exact recoverLevelsAt_policy_label_empty_of_gt pb qb rho gap k j
            (by change H.l k < j; omega)

variable {Ω : Type u} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z]

-- @node: recoveryLabels_recoveredData_eq_scoreRecoveryLabels
/-- [At every sample size and sample realization, the recovered data's full labels
equal their canonical score labels](goal). -/
lemma recoveryLabels_recoveredData_eq_scoreRecoveryLabels
    (M : LatentIVModel Ω X Z) {A : Type*} [MeasurableSpace A]
    {μ : Measure A} [IsProbabilityMeasure μ] (S : ObservedSample M μ)
    (I₁ I₂ : SampleSplit A) (pHat : ℕ → A → Z → X → ℝ)
    (phi : Z → X → ℝ → ℝ) (rho : ℕ → ℝ) (gap : ℝ) (n : ℕ) (a : A) :
    recoveryLabels (recoveredData M S I₁ I₂ pHat phi rho gap n a) =
      scoreRecoveryLabels (recoveredData M S I₁ I₂ pHat phi rho gap n a) := by
  exact recoveryLabels_recoverLevelsAt_eq_scoreRecoveryLabels _ _ _ _

-- @node: mem_recoveryEvent_iff_canonical_recoveryLabels_eq
/-- [A sample realization belongs to the recovery event exactly when the recovered
data's full labels equal the population level data's canonical score labels](goal). -/
lemma mem_recoveryEvent_iff_canonical_recoveryLabels_eq
    (M : LatentIVModel Ω X Z) {A : Type*} [MeasurableSpace A]
    {μ : Measure A} [IsProbabilityMeasure μ] (S : ObservedSample M μ)
    (I₁ I₂ : SampleSplit A) (pHat : ℕ → A → Z → X → ℝ)
    (phi : Z → X → ℝ → ℝ) (rho : ℕ → ℝ) (gap : ℝ)
    (L : LevelData Z X) (n : ℕ) (a : A) :
    a ∈ recoveryEvent M S I₁ I₂ pHat phi rho gap L n ↔
      recoveryLabels (recoveredData M S I₁ I₂ pHat phi rho gap n a) =
        scoreRecoveryLabels L := by
  rw [recoveryLabels_recoveredData_eq_scoreRecoveryLabels]
  exact mem_recoveryEvent_iff_scoreRecoveryLabels_eq M S I₁ I₂ pHat phi rho gap L n a

variable {A : Type*} [MeasurableSpace A]

-- @node: binDMLRegime_oracle_component_predictors_of_scoreLabels_eq
/-- For [binary nuisance estimates on the recovered levels](hyp:eHat), under [the finite binary-outcome DML regime](hyp:hr), if [the complements of the
events under consideration have probabilities tending to zero](hyp:hG) and
[recovered and population score labels agree on those events at even sample sizes](hyp:hlabels),
[there exist predictors measurable from the training sample, bounded in absolute value
by one, agreeing with the fitted binary nuisance components on those events, and
satisfying the finite nuisance rates relative to the true components](goal). -/
lemma binDMLRegime_oracle_component_predictors_of_scoreLabels_eq
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (pHat : ℕ → A → Z → X → ℝ) (phi : Z → X → ℝ → ℝ)
    (rho : ℕ → ℝ) (gap cpi : ℝ) (L : LevelData Z X) (ch : ℝ)
    (eHat : ∀ n a, NuisanceBin (recoveredData M S I₁ I₂ pHat phi rho gap n a))
    (hr : FiniteBinDMLRegime M μ S I₁ I₂ pHat phi rho gap cpi L ch eHat)
    (G : ℕ → Set A)
    (hG : Tendsto (fun n => μ (G n)ᶜ) atTop (𝓝 0))
    (hlabels : ∀ n a, a ∈ G n →
      scoreRecoveryLabels (recoveredData M S I₁ I₂ pHat phi rho gap (2 * (n + 1)) a) =
        scoreRecoveryLabels L) :
    ∃ oracle : ℕ → A → (ℕ × ℕ × ℕ × Z) → X → ℝ,
      (∀ c, TrainingPredictorMeasurable M S I₁ (fun n a => oracle n a c)) ∧
      (∀ n a c x, |oracle n a c x| ≤ 1) ∧
      (∀ n a, a ∈ G n → ∀ c x,
        oracle (2 * (n + 1)) a c x = binComponent _ (eHat (2 * (n + 1)) a) c x) ∧
      FiniteNuisanceRates M μ oracle (binComponent L (eta0Bin M L)) := by
  have hcanonical : ∀ n a, a ∈ G n →
      recoveryLabels (recoveredData M S I₁ I₂ pHat phi rho gap (2 * (n + 1)) a) =
        scoreRecoveryLabels L := by
    intro n a ha
    rw [recoveryLabels_recoveredData_eq_scoreRecoveryLabels]
    exact hlabels n a ha
  obtain ⟨F, hm, hb, heq, ht⟩ :=
    binDMLRegime_bounded_fixed_label_components M μ S I₁ I₂ pHat phi rho gap cpi L ch eHat hr
  refine ⟨fun n a => F n (trainingView M S I₁ n a) (scoreRecoveryLabels L),
    ht (scoreRecoveryLabels L), (fun n a c x => hb n _ _ c x), ?_, ?_⟩
  · intro n a ha c x
    rw [heq, hcanonical n a ha]
  · exact fixed_label_component_rates_on_recovery M μ
      (trainingView M S I₁) _ _ _ F heq (scoreRecoveryLabels L) G hG hcanonical hr.2.1


-- @node: contDMLRegime_oracle_component_predictors_of_scoreLabels_eq
/-- For [continuous-outcome nuisance estimates on the recovered levels](hyp:eHat), under [the finite continuous-outcome DML regime](hyp:hr), if [the complements of
the events under consideration have probabilities tending to zero](hyp:hG) and
[recovered and population score labels agree on those events at even sample sizes](hyp:hlabels),
[there exist predictors measurable from the training sample, bounded in absolute value
by one plus the absolute outcome bounds, agreeing with the fitted continuous nuisance
components on those events, and satisfying the finite nuisance rates relative to truth](goal). -/
lemma contDMLRegime_oracle_component_predictors_of_scoreLabels_eq
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (pHat : ℕ → A → Z → X → ℝ) (phi : Z → X → ℝ → ℝ)
    (rho : ℕ → ℝ) (gap cpi : ℝ) (L : LevelData Z X) (ch : ℝ)
    (eHat : ∀ n a, NuisanceCont (recoveredData M S I₁ I₂ pHat phi rho gap n a))
    (hr : FiniteContDMLRegime M μ S I₁ I₂ pHat phi rho gap cpi L ch eHat)
    (G : ℕ → Set A)
    (hG : Tendsto (fun n => μ (G n)ᶜ) atTop (𝓝 0))
    (hlabels : ∀ n a, a ∈ G n →
      scoreRecoveryLabels (recoveredData M S I₁ I₂ pHat phi rho gap (2 * (n + 1)) a) =
        scoreRecoveryLabels L) :
    ∃ oracle : ℕ → A → (ℕ × ℕ × ℕ × Z) → X → ℝ,
      (∀ c, TrainingPredictorMeasurable M S I₁ (fun n a => oracle n a c)) ∧
      (∀ n a c x, |oracle n a c x| ≤ 1 + |M.yMin| + |M.yMax|) ∧
      (∀ n a, a ∈ G n → ∀ c x,
        oracle (2 * (n + 1)) a c x = contComponent M _ (eHat (2 * (n + 1)) a) c x) ∧
      FiniteNuisanceRates M μ oracle (contComponent M L (trueNuisance M L)) := by
  have hcanonical : ∀ n a, a ∈ G n →
      recoveryLabels (recoveredData M S I₁ I₂ pHat phi rho gap (2 * (n + 1)) a) =
        scoreRecoveryLabels L := by
    intro n a ha
    rw [recoveryLabels_recoveredData_eq_scoreRecoveryLabels]
    exact hlabels n a ha
  obtain ⟨F, hm, hb, heq, ht⟩ :=
    contDMLRegime_bounded_fixed_label_components M μ S I₁ I₂ pHat phi rho gap cpi L ch eHat hr
  refine ⟨fun n a => F n (trainingView M S I₁ n a) (scoreRecoveryLabels L),
    ht (scoreRecoveryLabels L), (fun n a c x => hb n _ _ c x), ?_, ?_⟩
  · intro n a ha c x
    rw [heq, hcanonical n a ha]
  · exact fixed_label_component_rates_on_recovery M μ
      (trainingView M S I₁) _ _ _ F heq (scoreRecoveryLabels L) G hG hcanonical hr.2.1


-- @node: contDMLRegime_canonical_oracle_component_predictors
/-- Given [a threshold-crossing model](hyp:h), [a first stage satisfying the finite
first-stage rate](hyp:hRate), [a valid policy map](hyp:hphi) with [the specified
derivative](hyp:hd) that is [bounded and Lipschitz](hyp:hDerivative), assume
[the population level ordering is invariant across covariates](hyp:hL),
[policy levels avoid the boundary](hyp:hOff), [distinct propensity levels have the
specified gap separation](hyp:hgap), [the baseline level count is positive](hyp:hK),
and [the finite continuous-outcome DML regime holds](hyp:hr) for
[continuous-outcome nuisance estimates on the recovered levels](hyp:eHat).
[There exist training-sample-measurable oracle component predictors, bounded by one
plus the absolute outcome bounds, agreeing with the fitted components on the recovery
event at even sample sizes, and satisfying the finite nuisance rates relative to truth](goal). -/
lemma contDMLRegime_canonical_oracle_component_predictors
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
    let L := LevelStructure M.prop (policyProp phi M.prop) x0
    ∃ oracle : ℕ → A → (ℕ × ℕ × ℕ × Z) → X → ℝ,
      (∀ c, TrainingPredictorMeasurable M S I₁ (fun n a => oracle n a c)) ∧
      (∀ n a c x, |oracle n a c x| ≤ 1 + |M.yMin| + |M.yMax|) ∧
      (∀ n a, a ∈ recoveryEvent M S I₁ I₂ pHat phi rho gap L (2 * (n + 1)) →
        ∀ c x, oracle (2 * (n + 1)) a c x =
          contComponent M _ (eHat (2 * (n + 1)) a) c x) ∧
      FiniteNuisanceRates M μ oracle (contComponent M L (trueNuisance M L)) := by
  have hG := contDMLRegime_recoveryEvent_compl_tendsto_zero M μ S I₁ I₂ h
    pHat hRate phi dphi hphi hd hDerivative x0 gap cpi rho hL hOff hgap hK ch eHat hr
  exact contDMLRegime_oracle_component_predictors_of_scoreLabels_eq M μ S I₁ I₂
    pHat phi rho gap cpi _ ch eHat hr
    (fun n => recoveryEvent M S I₁ I₂ pHat phi rho gap
      (LevelStructure M.prop (policyProp phi M.prop) x0) (2 * (n + 1))) hG
    (fun n a ha => (mem_recoveryEvent_iff_scoreRecoveryLabels_eq
      M S I₁ I₂ pHat phi rho gap _ _ a).mp ha)

-- @node: binDMLRegime_canonical_oracle_component_predictors
/-- Given [a threshold-crossing model](hyp:h), [a first stage satisfying the finite
first-stage rate](hyp:hRate), [a valid policy map](hyp:hphi) with [the specified
derivative](hyp:hd) that is [bounded and Lipschitz](hyp:hDerivative), assume
[the population level ordering is invariant across covariates](hyp:hL),
[policy levels avoid the boundary](hyp:hOff), [distinct propensity levels have the
specified gap separation](hyp:hgap), [the baseline level count is positive](hyp:hK),
and [the finite binary-outcome DML regime holds](hyp:hr) for
[binary nuisance estimates on the recovered levels](hyp:eHat).
[There exist training-sample-measurable oracle component predictors bounded in absolute
value by one, agreeing with the fitted components on the recovery event at even sample
sizes, and satisfying the finite nuisance rates relative to truth](goal). -/
lemma binDMLRegime_canonical_oracle_component_predictors
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
    let L := LevelStructure M.prop (policyProp phi M.prop) x0
    ∃ oracle : ℕ → A → (ℕ × ℕ × ℕ × Z) → X → ℝ,
      (∀ c, TrainingPredictorMeasurable M S I₁ (fun n a => oracle n a c)) ∧
      (∀ n a c x, |oracle n a c x| ≤ 1) ∧
      (∀ n a, a ∈ recoveryEvent M S I₁ I₂ pHat phi rho gap L (2 * (n + 1)) →
        ∀ c x, oracle (2 * (n + 1)) a c x =
          binComponent _ (eHat (2 * (n + 1)) a) c x) ∧
      FiniteNuisanceRates M μ oracle (binComponent L (eta0Bin M L)) := by
  have hG := binDMLRegime_recoveryEvent_compl_tendsto_zero M μ S I₁ I₂ h
    pHat hRate phi dphi hphi hd hDerivative x0 gap cpi rho hL hOff hgap hK ch eHat hr
  exact binDMLRegime_oracle_component_predictors_of_scoreLabels_eq M μ S I₁ I₂
    pHat phi rho gap cpi _ ch eHat hr
    (fun n => recoveryEvent M S I₁ I₂ pHat phi rho gap
      (LevelStructure M.prop (policyProp phi M.prop) x0) (2 * (n + 1))) hG
    (fun n a ha => (mem_recoveryEvent_iff_scoreRecoveryLabels_eq
      M S I₁ I₂ pHat phi rho gap _ _ a).mp ha)

end Papers.TbsPrteOptimalTransport

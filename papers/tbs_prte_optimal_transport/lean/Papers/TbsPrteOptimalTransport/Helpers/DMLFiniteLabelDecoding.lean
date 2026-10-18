module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLCanonicalRecoveryLabels
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousLabelTransport
/-! Continuous nuisance decoding on the finite recovered label domains.
Only labels used by the score are transported; unused population extensions
need not agree with the canonical extensions of the recovery procedure. -/
public section
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Set Filter
open scoped Classical Topology
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]

-- @node: contComponent_decodeContComponents_of_scoreLabels_eq
/-- If [two level systems have the same labels used by the score](hyp:hLabels),
[decoding the continuous nuisance components from the second system into the first preserves
every component at every covariate value](goal). -/
lemma contComponent_decodeContComponents_of_scoreLabels_eq
    (M : LatentIVModel Ω X Z) (L H : LevelData Z X)
    (hLabels : scoreRecoveryLabels H = scoreRecoveryLabels L)
    (e : NuisanceCont H) (c : ℕ × ℕ × ℕ × Z) (x : X) :
    contComponent M L (decodeContComponents L (contComponent M H e)) c x =
      contComponent M H e c x := by
  obtain ⟨hK, hdom⟩ := (scoreRecoveryLabels_eq_iff H L).mp hLabels
  rcases c with ⟨code, k, j, z⟩
  unfold contComponent
  dsimp only
  split
  all_goals by_cases hk : k ≤ L.K
  all_goals try
    have hl := (hdom k hk).1
    have ht := (hdom k hk).2.2
    simp [decodeContComponents, contComponent, positiveValue, regularValue,
      shareValue, fullValue, nuValue, boundaryValue, minusBoundaryValue,
      meanValue, minusMeanValue, minusFullValue, hK, hl]
  all_goals try
    have hlt : ¬ k < L.K := by omega
    simp [decodeContComponents, contComponent, positiveValue, regularValue,
      shareValue, fullValue, nuValue, boundaryValue, minusBoundaryValue,
      meanValue, minusMeanValue, minusFullValue, hK, hk, hlt]
  all_goals repeat' (split <;> simp_all)
  all_goals
    intro hz hp hq
    have ht := (hdom k hk).2.2 j hq
    simp_all

-- @node: contComponent_decodeContComponents_of_scoreLabels_eq_of_factor
/-- If [two level systems have the same score labels](hyp:hLabels) and
[the component predictor equals every continuous nuisance component of the second system](hyp:hF),
[decoding that predictor into the first system reproduces the second system's components
at the specified index and covariate value](goal). -/
lemma contComponent_decodeContComponents_of_scoreLabels_eq_of_factor
    (M : LatentIVModel Ω X Z) (L H : LevelData Z X)
    (hLabels : scoreRecoveryLabels H = scoreRecoveryLabels L)
    (e : NuisanceCont H) (F : (ℕ × ℕ × ℕ × Z) → X → ℝ)
    (hF : ∀ c x, F c x = contComponent M H e c x)
    (c : ℕ × ℕ × ℕ × Z) (x : X) :
    contComponent M L (decodeContComponents L F) c x = contComponent M H e c x := by
  have heq : F = contComponent M H e := funext fun c => funext (hF c)
  rw [heq]
  exact contComponent_decodeContComponents_of_scoreLabels_eq M L H hLabels e c x

-- @node: contDMLRegime_oracle_nuisance_records_of_scoreLabels_eq
/-- For [continuous nuisance records fitted on the recovered levels at each sample size and realization](hyp:eHat), under [the finite continuous double machine learning regime](hyp:hr), if
[the probabilities of the complements of the recovery events tend to zero](hyp:hG) and
[the recovered score labels equal the population labels on those events at even sample sizes](hyp:hLabels),
[there exist nuisance records on the population level system whose components are training
measurable, agree with the fitted components on those events, and satisfy the finite nuisance
rates relative to the true components](goal). -/
lemma contDMLRegime_oracle_nuisance_records_of_scoreLabels_eq
    (M : LatentIVModel Ω X Z) {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] (S : ObservedSample M μ)
    (I₁ I₂ : SampleSplit A) (pHat : ℕ → A → Z → X → ℝ)
    (phi : Z → X → ℝ → ℝ) (rho : ℕ → ℝ) (gap cpi : ℝ)
    (L : LevelData Z X) (ch : ℝ)
    (eHat : ∀ n a, NuisanceCont (recoveredData M S I₁ I₂ pHat phi rho gap n a))
    (hr : FiniteContDMLRegime M μ S I₁ I₂ pHat phi rho gap cpi L ch eHat)
    (G : ℕ → Set A) (hG : Tendsto (fun n => μ (G n)ᶜ) atTop (𝓝 0))
    (hLabels : ∀ n a, a ∈ G n →
      scoreRecoveryLabels (recoveredData M S I₁ I₂ pHat phi rho gap (2 * (n + 1)) a) =
        scoreRecoveryLabels L) :
    ∃ oracle : ℕ → A → NuisanceCont L,
      (∀ c, TrainingPredictorMeasurable M S I₁
        (fun n a => contComponent M L (oracle n a) c)) ∧
      (∀ n a, a ∈ G n → ∀ c x,
        contComponent M L (oracle (2 * (n + 1)) a) c x =
          contComponent M _ (eHat (2 * (n + 1)) a) c x) ∧
      FiniteNuisanceRates M μ (fun n a => contComponent M L (oracle n a))
        (contComponent M L (trueNuisance M L)) := by
  obtain ⟨F, hm, hb, heq, hrate⟩ :=
    contDMLRegime_oracle_component_predictors_of_scoreLabels_eq
      M μ S I₁ I₂ pHat phi rho gap cpi L ch eHat hr G hG hLabels
  have heq' : ∀ n a, a ∈ G n → ∀ c x,
      contComponent M L (decodeContComponents L (F (2 * (n + 1)) a)) c x =
        contComponent M _ (eHat (2 * (n + 1)) a) c x := by
    intro n a ha c x
    exact contComponent_decodeContComponents_of_scoreLabels_eq_of_factor M L _
      (hLabels n a ha) (eHat (2 * (n + 1)) a) _ (heq n a ha) c x
  refine ⟨fun n a => decodeContComponents L (F n a), ?_, heq', ?_⟩
  · intro c n
    let : MeasurableSpace A :=
      MeasurableSpace.comap (trainingView M S I₁ n) inferInstance
    exact decodeContComponents_measurable M L (F n) (fun d => hm d n) c
  · exact nuisanceRates_transfer_on_recovery M μ
      (fun n a => contComponent M _ (eHat n a))
      (fun n a => contComponent M L (decodeContComponents L (F n a)))
      (contComponent M L (trueNuisance M L)) G hG heq' hr.2.1

-- @node: contDMLRegime_canonical_oracle_nuisance_records
/-- For [continuous nuisance records fitted on the recovered levels](hyp:eHat), suppose [the model satisfies threshold crossing](hyp:h),
[the first stage satisfies the finite rate condition](hyp:hRate),
[the policy map is valid](hyp:hphi), [its derivative is the specified function](hyp:hd), and
[that derivative is bounded and Lipschitz](hyp:hDerivative).
If [the canonical levels have invariant order](hyp:hL),
[policy levels avoid the boundary](hyp:hOff), [the specified gap separates propensity levels](hyp:hgap),
[the canonical level count is positive](hyp:hK), and
[the finite continuous double machine learning regime holds](hyp:hr),
[there exist training-measurable nuisance records on the canonical population levels that
match the fitted components on the canonical recovery events at even sample sizes and satisfy
the finite nuisance rates relative to truth](goal). -/
lemma contDMLRegime_canonical_oracle_nuisance_records
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
    ∃ oracle : ℕ → A → NuisanceCont L,
      (∀ c, TrainingPredictorMeasurable M S I₁
        (fun n a => contComponent M L (oracle n a) c)) ∧
      (∀ n a, a ∈ recoveryEvent M S I₁ I₂ pHat phi rho gap L (2 * (n + 1)) →
        ∀ c x, contComponent M L (oracle (2 * (n + 1)) a) c x =
          contComponent M _ (eHat (2 * (n + 1)) a) c x) ∧
      FiniteNuisanceRates M μ (fun n a => contComponent M L (oracle n a))
        (contComponent M L (trueNuisance M L)) := by
  have hG := contDMLRegime_recoveryEvent_compl_tendsto_zero M μ S I₁ I₂ h
    pHat hRate phi dphi hphi hd hDerivative x0 gap cpi rho hL hOff hgap hK ch eHat hr
  exact contDMLRegime_oracle_nuisance_records_of_scoreLabels_eq M μ S I₁ I₂
    pHat phi rho gap cpi _ ch eHat hr
    (fun n => recoveryEvent M S I₁ I₂ pHat phi rho gap
      (LevelStructure M.prop (policyProp phi M.prop) x0) (2 * (n + 1))) hG
    (fun n a ha => (mem_recoveryEvent_iff_scoreRecoveryLabels_eq
      M S I₁ I₂ pHat phi rho gap _ _ a).mp ha)

end Papers.TbsPrteOptimalTransport

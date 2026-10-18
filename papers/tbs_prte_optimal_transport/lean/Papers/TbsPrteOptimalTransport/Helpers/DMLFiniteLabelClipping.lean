module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLFiniteLabelDecoding
/-! Clipping and simplex transport on the finite recovered score domains.
This supplies bounded training-only oracle nuisances without requiring equality
of unused population label extensions. -/
public section
set_option linter.style.longLine false
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

-- @node: decodeContComponents_regular_of_scoreLabels_eq
/-- If [the recovered and target level structures have identical score recovery labels](hyp:hLabels), and the recovered continuous-outcome nuisances [satisfy clipping bounds](hyp:hc), [have shares forming a simplex](hyp:hs), and [have denominators clipped at the specified threshold](hyp:hd), then [decoding their components on the target structure preserves all three properties](goal). -/
lemma decodeContComponents_regular_of_scoreLabels_eq
    (M : LatentIVModel Ω X Z) (L H : LevelData Z X)
    (hLabels : scoreRecoveryLabels H = scoreRecoveryLabels L)
    (e : NuisanceCont H) (cpi : ℝ)
    (hc : ContClipping M H e) (hs : ContFittedSharesSimplex H e)
    (hd : ContDenominatorsClipped H e cpi) :
    let decoded := decodeContComponents L (contComponent M H e)
    ContClipping M L decoded ∧ ContFittedSharesSimplex L decoded ∧
      ContDenominatorsClipped L decoded cpi := by
  obtain ⟨hK, hdom⟩ := (scoreRecoveryLabels_eq_iff H L).mp hLabels
  obtain ⟨hp, hl, hr, ha, hf, ht, hn, hmp, hmm, hjp, hjm, hjfp, hjfm, _hprob⟩ := hc
  dsimp only
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · exact hp
  · intro k x
    have hk : 1 ≤ k.val ∧ k.val ≤ H.K := by simpa only [hK] using k.property
    simpa [decodeContComponents, contComponent, positiveValue, regularValue, shareValue, fullValue, nuValue, boundaryValue, minusBoundaryValue, meanValue, minusMeanValue, minusFullValue, hk] using hl ⟨k.val, hk⟩ x
  · intro a x
    have hk : a.val.1 ≤ L.K := by omega
    have hi : a.val.1 ≤ H.K ∧ 1 ≤ a.val.2 ∧ a.val.2 ≤ H.l a.val.1 := by
      rw [hK, (hdom a.val.1 hk).1]
      exact a.property
    simpa [decodeContComponents, contComponent, positiveValue, regularValue, shareValue, fullValue, nuValue, boundaryValue, minusBoundaryValue, meanValue, minusMeanValue, minusFullValue, hi] using hr ⟨a.val, hi⟩ x
  · intro a z x
    have hk : a.val.1 ≤ L.K := a.property.1
    have hi : a.val.1 ≤ H.K ∧ 1 ≤ a.val.2 ∧ a.val.2 ≤ H.l a.val.1 := by
      rw [hK, (hdom a.val.1 hk).1]
      exact a.property
    by_cases hz : z ∈ H.T a.val.1 a.val.2
    · simpa [decodeContComponents, contComponent, positiveValue, regularValue, shareValue, fullValue, nuValue, boundaryValue, minusBoundaryValue, meanValue, minusMeanValue, minusFullValue, hz, hi] using ha ⟨a.val, hi⟩ z x
    · simp [decodeContComponents, contComponent, positiveValue, regularValue, shareValue, fullValue, nuValue, boundaryValue, minusBoundaryValue, meanValue, minusMeanValue, minusFullValue, hz]
  · intro k x
    have hk : k.val < H.K := by simpa only [hK] using k.isLt
    simpa [decodeContComponents, contComponent, positiveValue, regularValue, shareValue, fullValue, nuValue, boundaryValue, minusBoundaryValue, meanValue, minusMeanValue, minusFullValue, hk] using hf ⟨k.val, hk⟩ x
  · exact ht
  · intro a x
    have hk : a.val.1 ≤ L.K := by omega
    have hi : a.val.1 < H.K ∧ 1 ≤ a.val.2 ∧ a.val.2 ≤ H.l a.val.1 := by
      rw [hK, (hdom a.val.1 hk).1]
      exact a.property
    have hj : a.val.2 ≠ 0 := by omega
    simpa [decodeContComponents, contComponent, positiveValue, regularValue, shareValue, fullValue, nuValue, boundaryValue, minusBoundaryValue, meanValue, minusMeanValue, minusFullValue, hi, hj] using hn ⟨a.val, hi⟩ x
  · intro a x
    have hk : a.val.1 ≤ L.K := by omega
    have hi : a.val.1 < H.K ∧ a.val.2 ≤ H.l a.val.1 := by
      rw [hK, (hdom a.val.1 hk).1]
      exact a.property
    simpa [decodeContComponents, contComponent, positiveValue, regularValue, shareValue, fullValue, nuValue, boundaryValue, minusBoundaryValue, meanValue, minusMeanValue, minusFullValue, hi] using hmp ⟨a.val, hi⟩ x
  · intro a x
    have hk : a.val.1 ≤ L.K := by omega
    have hi : 1 ≤ a.val.1 ∧ a.val.1 < H.K ∧ a.val.2 ≤ H.l a.val.1 := by
      rw [hK, (hdom a.val.1 hk).1]
      exact a.property
    simpa [decodeContComponents, contComponent, positiveValue, regularValue, shareValue, fullValue, nuValue, boundaryValue, minusBoundaryValue, meanValue, minusMeanValue, minusFullValue, hi] using hmm ⟨a.val, hi⟩ x
  · intro a x
    have hk : a.val.1 ≤ L.K := by omega
    have hi : a.val.1 < H.K ∧ a.val.2 ≤ H.l a.val.1 := by
      rw [hK, (hdom a.val.1 hk).1]
      exact a.property
    simpa [decodeContComponents, contComponent, positiveValue, regularValue, shareValue, fullValue, nuValue, boundaryValue, minusBoundaryValue, meanValue, minusMeanValue, minusFullValue, hi] using hjp ⟨a.val, hi⟩ x
  · intro a x
    have hk : a.val.1 ≤ L.K := by omega
    have hi : 1 ≤ a.val.1 ∧ a.val.1 < H.K ∧ a.val.2 ≤ H.l a.val.1 := by
      rw [hK, (hdom a.val.1 hk).1]
      exact a.property
    simpa [decodeContComponents, contComponent, positiveValue, regularValue, shareValue, fullValue, nuValue, boundaryValue, minusBoundaryValue, meanValue, minusMeanValue, minusFullValue, hi] using hjm ⟨a.val, hi⟩ x
  · intro k x
    have hk : k.val < H.K := by simpa only [hK] using k.isLt
    simpa [decodeContComponents, contComponent, positiveValue, regularValue, shareValue, fullValue, nuValue, boundaryValue, minusBoundaryValue, meanValue, minusMeanValue, minusFullValue, hk] using hjfp ⟨k.val, hk⟩ x
  · intro k x
    have hk : 1 ≤ k.val ∧ k.val < H.K := by simpa only [hK] using k.property
    simpa [decodeContComponents, contComponent, positiveValue, regularValue, shareValue, fullValue, nuValue, boundaryValue, minusBoundaryValue, meanValue, minusMeanValue, minusFullValue, hk] using hjfm ⟨k.val, hk⟩ x
  · intro k x
    exact ⟨⟨le_rfl, zero_le_one⟩, ⟨le_rfl, zero_le_one⟩⟩
  · intro a x
    have hk : a.val.1 ≤ L.K := a.property.1
    have hi : a.val.1 ≤ H.K ∧ 1 ≤ a.val.2 ∧ a.val.2 ≤ H.l a.val.1 := by
      rw [hK, (hdom a.val.1 hk).1]
      exact a.property
    have hT := (hdom a.val.1 hk).2.2 a.val.2 a.property.2.2
    refine ⟨?_, ?_⟩
    · intro z
      by_cases hz : z ∈ H.T a.val.1 a.val.2
      · simpa [decodeContComponents, contComponent, positiveValue, regularValue, shareValue, fullValue, nuValue, boundaryValue, minusBoundaryValue, meanValue, minusMeanValue, minusFullValue, hz, hi] using (hs ⟨a.val, hi⟩ x).1 z
      · simp [decodeContComponents, contComponent, positiveValue, regularValue, shareValue, fullValue, nuValue, boundaryValue, minusBoundaryValue, meanValue, minusMeanValue, minusFullValue, hz]
    · simpa [decodeContComponents, contComponent, positiveValue, regularValue, shareValue, fullValue, nuValue, boundaryValue, minusBoundaryValue, meanValue, minusMeanValue, minusFullValue, hi, ← hT] using (hs ⟨a.val, hi⟩ x).2
  · intro k x
    have hk : 1 ≤ k.val ∧ k.val ≤ H.K := by simpa only [hK] using k.property
    simpa [decodeContComponents, contComponent, positiveValue, regularValue, shareValue, fullValue, nuValue, boundaryValue, minusBoundaryValue, meanValue, minusMeanValue, minusFullValue, hk] using hd.1 ⟨k.val, hk⟩ x
  · intro a x hne
    have hk : a.val.1 ≤ L.K := a.property.1
    have hi : a.val.1 ≤ H.K ∧ 1 ≤ a.val.2 ∧ a.val.2 ≤ H.l a.val.1 := by
      rw [hK, (hdom a.val.1 hk).1]
      exact a.property
    have hT := (hdom a.val.1 hk).2.2 a.val.2 a.property.2.2
    simpa [decodeContComponents, contComponent, positiveValue, regularValue, shareValue, fullValue, nuValue, boundaryValue, minusBoundaryValue, meanValue, minusMeanValue, minusFullValue, hi] using hd.2 ⟨a.val, hi⟩ x (hT.symm ▸ hne)

-- @node: repairContNuisance_component_eq_of_scoreLabels_eq
/-- If [the recovered and target structures have identical score recovery labels](hyp:hLabels), [every target regular instrument set is nonempty](hyp:hne), and [a component array agrees everywhere with the recovered nuisance components](hyp:heq), whose nuisances [satisfy clipping bounds](hyp:hc), [have simplex shares](hyp:hs), and [have denominators clipped at the specified threshold](hyp:hd), then [decoding and repairing that array on the target structure leaves the selected component unchanged at the chosen covariate value](goal). -/
lemma repairContNuisance_component_eq_of_scoreLabels_eq
    (M : LatentIVModel Ω X Z) (L H : LevelData Z X)
    (hLabels : scoreRecoveryLabels H = scoreRecoveryLabels L) (cpi : ℝ)
    (hne : ∀ a : RegularIndex L, (L.T a.val.1 a.val.2).Nonempty)
    (F : (ℕ × ℕ × ℕ × Z) → X → ℝ) (e : NuisanceCont H)
    (heq : ∀ c x, F c x = contComponent M H e c x)
    (hc : ContClipping M H e) (hs : ContFittedSharesSimplex H e)
    (hd : ContDenominatorsClipped H e cpi) (c : ℕ × ℕ × ℕ × Z) (x : X) :
    contComponent M L (repairContNuisance M L cpi hne (decodeContComponents L F)) c x =
      contComponent M H e c x := by
  have hF : F = contComponent M H e := funext fun c => funext (heq c)
  rw [hF]
  have hr := decodeContComponents_regular_of_scoreLabels_eq M L H hLabels e cpi hc hs hd
  rw [repairContNuisance_eq_of_regular M L cpi hne _ hr.1 hr.2.1 hr.2.2,
    contComponent_normalizeContAuxiliaryFits]
  exact contComponent_decodeContComponents_of_scoreLabels_eq M L H hLabels e c x

-- @node: contDMLRegime_regular_oracle_nuisance_records_of_scoreLabels_eq
/-- Assume [the target structure has a positive number of levels](hyp:hK), [the outcome endpoints are known](hyp:hend), and [the continuous-outcome nuisance estimators on recovered levels](hyp:eHat) [satisfy the finite continuous-outcome double machine learning regime](hyp:hr). If [the complements of a sequence of recovery events have probability tending to zero](hyp:hG) and [score recovery labels agree with the target structure on those events at even sample sizes](hyp:hLabels), then [there exist target-structure oracle nuisances whose components use only training data, satisfy clipping, simplex and denominator bounds, are admissible, agree componentwise with the recovered estimates on those events, and satisfy the finite nuisance rate conditions](goal). -/
lemma contDMLRegime_regular_oracle_nuisance_records_of_scoreLabels_eq
    (M : LatentIVModel Ω X Z) {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (pHat : ℕ → A → Z → X → ℝ) (phi : Z → X → ℝ → ℝ)
    (rho : ℕ → ℝ) (gap cpi : ℝ) (L : LevelData Z X) (ch : ℝ)
    (hK : LevelCountPos L.K) (hend : OutcomeEndpointsKnown M)
    (eHat : ∀ n a, NuisanceCont (recoveredData M S I₁ I₂ pHat phi rho gap n a))
    (hr : FiniteContDMLRegime M μ S I₁ I₂ pHat phi rho gap cpi L ch eHat)
    (G : ℕ → Set A)
    (hG : Tendsto (fun n => μ (G n)ᶜ) atTop (𝓝 0))
    (hLabels : ∀ n a, a ∈ G n →
      scoreRecoveryLabels (recoveredData M S I₁ I₂ pHat phi rho gap (2 * (n + 1)) a) =
        scoreRecoveryLabels L) :
    ∃ oracle : ℕ → A → NuisanceCont L,
      (∀ c, TrainingPredictorMeasurable M S I₁
        (fun n a => contComponent M L (oracle n a) c)) ∧
      (∀ n a, ContClipping M L (oracle n a) ∧
        ContFittedSharesSimplex L (oracle n a) ∧
        ContDenominatorsClipped L (oracle n a) cpi) ∧
      (∀ n a, ContAdmissible M L (oracle n a)) ∧
      (∀ n a, a ∈ G n → ∀ c x,
        contComponent M L (oracle (2 * (n + 1)) a) c x =
          contComponent M _ (eHat (2 * (n + 1)) a) c x) ∧
      FiniteNuisanceRates M μ (fun n a => contComponent M L (oracle n a))
        (contComponent M L (trueNuisance M L)) := by
  obtain ⟨n, hn⟩ := (hG.eventually
    (gt_mem_nhds (by norm_num : (0 : ENNReal) < 1))).exists
  have hnG : (G n).Nonempty := by
    by_contra h
    have hz := Set.not_nonempty_iff_eq_empty.mp h
    simp only [hz, Set.compl_empty, measure_univ, lt_self_iff_false] at hn
  obtain ⟨a, ha⟩ := hnG
  have hL := hLabels n a ha
  have hfit := hr.1.2.2.1.2.2.2.1 (2 * (n + 1)) a
  have hdecoded := decodeContComponents_regular_of_scoreLabels_eq M L _ hL
    (eHat (2 * (n + 1)) a) cpi hfit.1 hfit.2.2.2 hfit.2.2.1
  have hgeometry' := continuous_clipping_simplex_geometry L cpi hK
    (decodeContComponents L (contComponent M _ (eHat (2 * (n + 1)) a)))
    hdecoded.2.2 hdecoded.2.1
  obtain ⟨hcpi, hne⟩ := hgeometry'
  obtain ⟨F, hm, hb, heq, hrate⟩ := contDMLRegime_oracle_component_predictors_of_scoreLabels_eq
    M μ S I₁ I₂ pHat phi rho gap cpi L ch eHat hr G hG hLabels
  let raw := fun n a => repairContNuisance M L cpi hne (decodeContComponents L (F n a))
  let oracle := fun n a => normalizeContAuxiliaryFits L (raw n a)
  have hreg (n : ℕ) (a : A) : ContClipping M L (oracle n a) ∧
      ContFittedSharesSimplex L (oracle n a) ∧
      ContDenominatorsClipped L (oracle n a) cpi := by
    have h := repairContNuisance_regular M L cpi hcpi (hend.1.2 hend.2.1)
      hne (decodeContComponents L (F n a))
    exact normalizeContAuxiliaryFits_regular M L _ cpi h.1 h.2.1 h.2.2
  have hmeas (c) : TrainingPredictorMeasurable M S I₁
      (fun n a => contComponent M L (oracle n a) c) := by
    intro n
    let : MeasurableSpace A :=
      MeasurableSpace.comap (trainingView M S I₁ n) inferInstance
    have hh := repairContNuisance_decoded_measurable M L cpi hne (F n)
      (fun c => hm c n) c
    change Measurable (fun ax : A × X => contComponent M L (oracle n ax.1) c ax.2)
    simpa only [oracle, raw, contComponent_normalizeContAuxiliaryFits] using hh
  have heq' : ∀ n a, a ∈ G n → ∀ c x,
      contComponent M L (oracle (2 * (n + 1)) a) c x =
        contComponent M _ (eHat (2 * (n + 1)) a) c x := by
    intro n a ha c x
    have hf := hr.1.2.2.1.2.2.2.1 (2 * (n + 1)) a
    simp only [oracle, contComponent_normalizeContAuxiliaryFits, raw]
    exact repairContNuisance_component_eq_of_scoreLabels_eq M L _ (hLabels n a ha)
      cpi hne _ _ (heq n a ha) hf.1 hf.2.2.2 hf.2.2.1 c x
  have hadm (n : ℕ) (a : A) : ContAdmissible M L (oracle n a) := by
    have hmsection (c) : Measurable (contComponent M L (raw n a) c) := by
      let : MeasurableSpace A :=
        MeasurableSpace.comap (trainingView M S I₁ n) inferInstance
      have hh := repairContNuisance_decoded_measurable M L cpi hne (F n)
        (fun c => hm c n) c
      exact hh.comp (measurable_const.prodMk measurable_id)
    have h := repairContNuisance_regular M L cpi hcpi (hend.1.2 hend.2.1)
      hne (decodeContComponents L (F n a))
    exact restrictContShares_admissible_of_encoded_clipping M L (raw n a)
      h.1 h.2.1 hmsection
  refine ⟨oracle, hmeas, hreg, hadm, heq', ?_⟩
  exact nuisanceRates_transfer_on_recovery M μ
      (fun n a => contComponent M _ (eHat n a))
      (fun n a => contComponent M L (oracle n a))
      (contComponent M L (trueNuisance M L)) G hG heq' hr.2.1

-- @node: contDMLRegime_canonical_regular_oracle_nuisance_records
/-- Assume [the model satisfies threshold crossing](hyp:h), [the first-stage estimates satisfy the finite rate condition](hyp:hRate), [the policy transformation is measurable and preserves the unit interval](hyp:hphi), [its specified derivative is valid](hyp:hd) and [bounded and Lipschitz](hyp:hDerivative), [the canonical level structure preserves the ordering of baseline and policy propensities](hyp:hL), [policy levels avoid the boundary](hyp:hOff), [distinct propensity levels are separated by the specified gap](hyp:hgap), [there is a positive number of levels](hyp:hK), [outcome endpoints are known](hyp:hend), and [the continuous-outcome nuisance estimates on recovered levels](hyp:eHat) [satisfy the finite continuous-outcome double machine learning regime](hyp:hr). Then [there exist admissible oracle nuisances on the canonical structure, with training-only measurable components, clipping, simplex and denominator bounds, the finite nuisance rates, and componentwise agreement with the recovered estimates on the canonical recovery events at even sample sizes](goal). -/
lemma contDMLRegime_canonical_regular_oracle_nuisance_records
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
    (ch : ℝ) (hend : OutcomeEndpointsKnown M)
    (eHat : ∀ n a, NuisanceCont (recoveredData M S I₁ I₂ pHat phi rho gap n a))
    (hr : FiniteContDMLRegime M μ S I₁ I₂ pHat phi rho gap cpi
      (LevelStructure M.prop (policyProp phi M.prop) x0) ch eHat) :
    let L := LevelStructure M.prop (policyProp phi M.prop) x0
    ∃ oracle : ℕ → A → NuisanceCont L,
      (∀ c, TrainingPredictorMeasurable M S I₁
        (fun n a => contComponent M L (oracle n a) c)) ∧
      (∀ n a, ContClipping M L (oracle n a) ∧
        ContFittedSharesSimplex L (oracle n a) ∧
        ContDenominatorsClipped L (oracle n a) cpi) ∧
      (∀ n a, ContAdmissible M L (oracle n a)) ∧
      (∀ n a, a ∈ recoveryEvent M S I₁ I₂ pHat phi rho gap L (2 * (n + 1)) →
        ∀ c x, contComponent M L (oracle (2 * (n + 1)) a) c x =
          contComponent M _ (eHat (2 * (n + 1)) a) c x) ∧
      FiniteNuisanceRates M μ (fun n a => contComponent M L (oracle n a))
        (contComponent M L (trueNuisance M L)) := by
  have hG := contDMLRegime_recoveryEvent_compl_tendsto_zero M μ S I₁ I₂ h
    pHat hRate phi dphi hphi hd hDerivative x0 gap cpi rho hL hOff hgap hK ch eHat hr
  exact contDMLRegime_regular_oracle_nuisance_records_of_scoreLabels_eq M μ S I₁ I₂
    pHat phi rho gap cpi _ ch hK hend eHat hr
    (fun n => recoveryEvent M S I₁ I₂ pHat phi rho gap
      (LevelStructure M.prop (policyProp phi M.prop) x0) (2 * (n + 1))) hG
    (fun n a ha => (mem_recoveryEvent_iff_scoreRecoveryLabels_eq
      M S I₁ I₂ pHat phi rho gap _ _ a).mp ha)

-- @node: contDMLRegime_oracle_score_convergence_of_scoreLabels_eq
/-- Assume [the policy transformation is measurable and preserves the unit interval](hyp:hphi), [its specified derivative is valid](hyp:hd) and [bounded and Lipschitz](hyp:hDerivative), [the model satisfies the structural assumptions](hyp:hStruct), [outcome endpoints are known](hyp:hend), [the target structure has a positive number of levels](hyp:hK) and [preserves baseline and policy propensity ordering](hyp:hOrder), [the population nuisances are admissible](hyp:he0), and [baseline overlap](hyp:hov) and [policy overlap](hyp:hpol) hold at the clipping threshold. If [the continuous-outcome nuisance estimates on recovered levels](hyp:eHat) [satisfy the finite continuous-outcome double machine learning regime](hyp:hr), [recovery-event complements have probability tending to zero](hyp:hG), and [the recovered score labels match the target labels on those events at even sample sizes](hyp:hLabels), then [there exist admissible oracle nuisances with clipping, simplex and denominator bounds, a training-only measurable score difference whose population integrated square tends to zero in probability along even sample sizes, and componentwise agreement with the recovered estimates on the recovery events](goal). -/
lemma contDMLRegime_oracle_score_convergence_of_scoreLabels_eq
    (M : LatentIVModel Ω X Z) {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] (S : ObservedSample M μ)
    (I₁ I₂ : SampleSplit A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (hStruct : StructuralAssumptions M) (hend : OutcomeEndpointsKnown M)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (hpol : PolicyOverlap M L cpi)
    (pHat : ℕ → A → Z → X → ℝ) (rho : ℕ → ℝ) (gap ch : ℝ)
    (eHat : ∀ n a, NuisanceCont (recoveredData M S I₁ I₂ pHat phi rho gap n a))
    (hr : FiniteContDMLRegime M μ S I₁ I₂ pHat phi rho gap cpi L ch eHat)
    (G : ℕ → Set A) (hG : Tendsto (fun n => μ (G n)ᶜ) atTop (𝓝 0))
    (hLabels : ∀ n a, a ∈ G n →
      scoreRecoveryLabels (recoveredData M S I₁ I₂ pHat phi rho gap (2 * (n + 1)) a) =
        scoreRecoveryLabels L) :
    ∃ oracle : ℕ → A → NuisanceCont L,
      (∀ n a, ContClipping M L (oracle n a) ∧
        ContFittedSharesSimplex L (oracle n a) ∧
        ContDenominatorsClipped L (oracle n a) cpi) ∧
      (∀ n a, ContAdmissible M L (oracle n a)) ∧
      TrainingPredictorMeasurable M S I₁ (fun n a o =>
        psiCont M phi dphi L hK o (oracle n a) -
          psiCont M phi dphi L hK o (trueNuisance M L)) ∧
      Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
        (fun n a => ∫ o,
          (psiCont M phi dphi L hK o (oracle (2 * (n + 1)) a) -
            psiCont M phi dphi L hK o (trueNuisance M L)) ^ 2 ∂observationLaw M)
        atTop (fun _ _ => 0) ∧
      (∀ n a, a ∈ G n → ∀ c x,
        contComponent M L (oracle (2 * (n + 1)) a) c x =
          contComponent M _ (eHat (2 * (n + 1)) a) c x) := by
  cases Subsingleton.elim ‹DecidableEq Z› (fun a b => Classical.propDecidable (a = b))
  obtain ⟨oracle, hm, hc, ha, heq, hrate⟩ :=
    contDMLRegime_regular_oracle_nuisance_records_of_scoreLabels_eq M μ S I₁ I₂ pHat phi
      rho gap cpi L ch hK hend eHat hr G hG hLabels
  have hscore := training_measurable_continuous_score_of_components M S I₁
    phi dphi hphi hd L hK oracle hm (fun n a => (hc n a).1.1)
  have hdiff := training_measurable_continuous_score_difference M S I₁
    phi dphi hphi hd L hK he0 _ hscore
  have hsection (n : ℕ) (a : A) (c) :
      Measurable (contComponent M L (oracle n a) c) := by
    let : MeasurableSpace A :=
      MeasurableSpace.comap (trainingView M S I₁ n) inferInstance
    exact (hm c n).comp (measurable_const.prodMk measurable_id)
  have hconv := encoded_continuous_total_score_sq_tendsto_probability_zero
    M μ hStruct.2.2.2.1 phi dphi hphi hd hDerivative L hK hOrder
    hStruct.1 hStruct.2.1 hend he0 oracle (fun n a => (hc n a).1)
    (fun n a => (hc n a).2.1) hsection hrate hr.2.2.1 cpi hov hpol
    (fun n a => (hc n a).2.2)
  exact ⟨oracle, hc, ha, hdiff, hconv, heq⟩

end Papers.TbsPrteOptimalTransport

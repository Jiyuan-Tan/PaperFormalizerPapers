module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLCanonicalRecoveryLabels
public import Papers.TbsPrteOptimalTransport.Helpers.DMLBinaryOracleClipping
public import Papers.TbsPrteOptimalTransport.Helpers.DMLFiniteLabelVariance
public import Papers.TbsPrteOptimalTransport.Helpers.DMLRegimeVariance
/-! Binary oracle reconstruction on finite recovered score labels.
Decoding preserves clipping and simplex constraints. Training-only reconstruction
transfers nuisance rates, and coherent sorting preserves exact score equality. -/
public section
set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Set Filter
open scoped Classical Topology
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]

-- @node: binComponent_decodeBinComponents_of_scoreLabels_eq
/-- If [two level structures have identical score-recovery labels](hyp:hLabels), then
[encoding a nuisance record after decoding its components under the other structure
preserves the selected component at the selected covariate value](goal). -/
lemma binComponent_decodeBinComponents_of_scoreLabels_eq
    (L H : LevelData Z X)
    (hLabels : scoreRecoveryLabels H = scoreRecoveryLabels L)
    (e : NuisanceBin H) (c : ℕ × ℕ × ℕ × Z) (x : X) :
    binComponent L (decodeBinComponents L (binComponent H e)) c x =
      binComponent H e c x := by
  obtain ⟨hK, hdom⟩ := (scoreRecoveryLabels_eq_iff H L).mp hLabels
  rcases c with ⟨code, k, j, z⟩
  unfold binComponent
  dsimp only
  split
  all_goals by_cases hk : k ≤ L.K
  all_goals try
    have hl := (hdom k hk).1
    have ht := (hdom k hk).2.2
    simp [decodeBinComponents, positiveValue, regularValue,
      fullValue, hK, hl]
  all_goals try
    have hlt : ¬ k < L.K := by omega
    simp [decodeBinComponents, positiveValue, regularValue,
      fullValue, hK, hk, hlt]
  all_goals repeat' (split <;> simp_all)

-- @node: binComponent_decodeBinComponents_of_scoreLabels_eq_of_factor
/-- If [two level structures have identical score-recovery labels](hyp:hLabels) and
[the encoded functions equal every component of a nuisance record on the first structure](hyp:hF),
then [decoding under the second structure reproduces the selected original component](goal). -/
lemma binComponent_decodeBinComponents_of_scoreLabels_eq_of_factor
    (L H : LevelData Z X)
    (hLabels : scoreRecoveryLabels H = scoreRecoveryLabels L)
    (e : NuisanceBin H) (F : (ℕ × ℕ × ℕ × Z) → X → ℝ)
    (hF : ∀ c x, F c x = binComponent H e c x)
    (c : ℕ × ℕ × ℕ × Z) (x : X) :
    binComponent L (decodeBinComponents L F) c x = binComponent H e c x := by
  have heq : F = binComponent H e := funext fun c => funext (hF c)
  rw [heq]
  exact binComponent_decodeBinComponents_of_scoreLabels_eq L H hLabels e c x


-- @node: decodeBinComponents_regular_of_scoreLabels_eq
/-- If [two level structures have identical score-recovery labels](hyp:hLabels), and
the original record has [binary clipping](hyp:hc), [simplex shares](hyp:hs), and
[denominator clipping at the chosen constant](hyp:hd), then
[decoding its components under the reference structure preserves all three properties](goal). -/
lemma decodeBinComponents_regular_of_scoreLabels_eq
    (L H : LevelData Z X)
    (hLabels : scoreRecoveryLabels H = scoreRecoveryLabels L)
    (e : NuisanceBin H) (cpi : ℝ)
    (hc : BinClipping H e) (hs : BinFittedSharesSimplex H e)
    (hd : BinDenominatorsClipped H e cpi) :
    let decoded := decodeBinComponents L (binComponent H e)
    BinClipping L decoded ∧ BinFittedSharesSimplex L decoded ∧
      BinDenominatorsClipped L decoded cpi := by
  obtain ⟨hK, hdom⟩ := (scoreRecoveryLabels_eq_iff H L).mp hLabels
  have hfull := binClipping_full_range H e hc
  obtain ⟨hp, hl, hr, ha, ht, hop⟩ := hc
  dsimp only
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · exact hp
  · intro k x
    have hk : 1 ≤ k.val ∧ k.val ≤ H.K := by simpa only [hK] using k.property
    simpa [decodeBinComponents, binComponent, positiveValue, regularValue, fullValue, hk]
      using hl ⟨k.val, hk⟩ x
  · intro a x
    have hi : a.val.1 ≤ H.K ∧ 1 ≤ a.val.2 ∧ a.val.2 ≤ H.l a.val.1 := by
      rw [hK, (hdom a.val.1 a.property.1).1]
      exact a.property
    simpa [decodeBinComponents, binComponent, positiveValue, regularValue, fullValue, hi]
      using hr ⟨a.val, hi⟩ x
  · intro a z x
    have hi : a.val.1 ≤ H.K ∧ 1 ≤ a.val.2 ∧ a.val.2 ≤ H.l a.val.1 := by
      rw [hK, (hdom a.val.1 a.property.1).1]
      exact a.property
    by_cases hz : z ∈ H.T a.val.1 a.val.2
    · simpa [decodeBinComponents, binComponent, hi, hz] using ha ⟨a.val, hi⟩ z x
    · simp [decodeBinComponents, binComponent, hz]
  · exact ht
  · obtain ⟨policyFit, baselineFit, hrange, hdiff⟩ := hop
    refine ⟨(fun k x => policyFit ⟨k.val, by simpa only [hK] using k.isLt⟩ x),
      (fun k x => baselineFit ⟨k.val, by simpa only [hK] using k.isLt⟩ x), ?_, ?_⟩
    · intro k x
      exact hrange _ x
    · intro k x
      have hk : k.val < H.K := by simpa only [hK] using k.isLt
      simpa [decodeBinComponents, binComponent, fullValue, hk] using hdiff ⟨k.val, hk⟩ x
  · intro a x
    have hi : a.val.1 ≤ H.K ∧ 1 ≤ a.val.2 ∧ a.val.2 ≤ H.l a.val.1 := by
      rw [hK, (hdom a.val.1 a.property.1).1]
      exact a.property
    have hT := (hdom a.val.1 a.property.1).2.2 a.val.2 a.property.2.2
    refine ⟨?_, ?_⟩
    · intro z
      by_cases hz : z ∈ H.T a.val.1 a.val.2
      · simpa [decodeBinComponents, binComponent, hi, hz] using (hs ⟨a.val, hi⟩ x).1 z
      · simp [decodeBinComponents, binComponent, hz]
    · simpa [decodeBinComponents, binComponent, hi, ← hT] using (hs ⟨a.val, hi⟩ x).2
  · intro k x
    have hk : 1 ≤ k.val ∧ k.val ≤ H.K := by simpa only [hK] using k.property
    simpa [decodeBinComponents, binComponent, positiveValue, hk] using hd.1 ⟨k.val, hk⟩ x
  · intro a x hne
    have hi : a.val.1 ≤ H.K ∧ 1 ≤ a.val.2 ∧ a.val.2 ≤ H.l a.val.1 := by
      rw [hK, (hdom a.val.1 a.property.1).1]
      exact a.property
    have hT := (hdom a.val.1 a.property.1).2.2 a.val.2 a.property.2.2
    simpa [decodeBinComponents, binComponent, regularValue, hi]
      using hd.2 ⟨a.val, hi⟩ x (hT.symm ▸ hne)

-- @node: repairBinNuisance_component_eq_of_scoreLabels_eq
/-- If [the two structures have identical score-recovery labels](hyp:hLabels),
[every reference regular instrument group is nonempty](hyp:hne), and
[the encoded functions reproduce the original nuisance components](hyp:heq), with
[binary clipping](hyp:hc), [simplex shares](hyp:hs), and [clipped denominators](hyp:hd),
then [decoding and repairing under the reference structure preserves the selected component](goal). -/
lemma repairBinNuisance_component_eq_of_scoreLabels_eq
    (L H : LevelData Z X)
    (hLabels : scoreRecoveryLabels H = scoreRecoveryLabels L) (cpi : ℝ)
    (hne : ∀ a : RegularIndex L, (L.T a.val.1 a.val.2).Nonempty)
    (F : (ℕ × ℕ × ℕ × Z) → X → ℝ) (e : NuisanceBin H)
    (heq : ∀ c x, F c x = binComponent H e c x)
    (hc : BinClipping H e) (hs : BinFittedSharesSimplex H e)
    (hd : BinDenominatorsClipped H e cpi) (c : ℕ × ℕ × ℕ × Z) (x : X) :
    binComponent L (repairBinNuisance L cpi hne (decodeBinComponents L F)) c x =
      binComponent H e c x := by
  have hF : F = binComponent H e := funext fun c => funext (heq c)
  rw [hF]
  have hr := decodeBinComponents_regular_of_scoreLabels_eq L H hLabels e cpi hc hs hd
  rw [repairBinNuisance_eq_of_regular L cpi hne _ hr.1 hr.2.1 hr.2.2,
    binComponent_restrictBinShares]
  exact binComponent_decodeBinComponents_of_scoreLabels_eq L H hLabels e c x

-- @node: binDMLRegime_regular_oracle_nuisance_records_of_scoreLabels_eq
/-- Suppose [the reference level count is positive](hyp:hK),
[the fitted binary nuisance records on the recovered level structures](hyp:eHat)
[satisfy the finite binary double machine learning regime](hyp:hr),
[the recovery-event complements have probabilities tending to zero](hyp:hG), and
[the recovered and reference score labels agree on those events at even sample sizes](hyp:hLabels).
Then [there exist reference-level oracle records with training-measurable components,
binary clipping, simplex shares, clipped denominators, admissibility, and finite nuisance rates,
agreeing componentwise with the fitted records on the recovery events](goal). -/
lemma binDMLRegime_regular_oracle_nuisance_records_of_scoreLabels_eq
    (M : LatentIVModel Ω X Z) {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (pHat : ℕ → A → Z → X → ℝ) (phi : Z → X → ℝ → ℝ)
    (rho : ℕ → ℝ) (gap cpi : ℝ) (L : LevelData Z X) (ch : ℝ)
    (hK : LevelCountPos L.K)
    (eHat : ∀ n a, NuisanceBin (recoveredData M S I₁ I₂ pHat phi rho gap n a))
    (hr : FiniteBinDMLRegime M μ S I₁ I₂ pHat phi rho gap cpi L ch eHat)
    (G : ℕ → Set A)
    (hG : Tendsto (fun n => μ (G n)ᶜ) atTop (𝓝 0))
    (hLabels : ∀ n a, a ∈ G n →
      scoreRecoveryLabels (recoveredData M S I₁ I₂ pHat phi rho gap (2 * (n + 1)) a) =
        scoreRecoveryLabels L) :
    ∃ oracle : ℕ → A → NuisanceBin L,
      (∀ c, TrainingPredictorMeasurable M S I₁
        (fun n a => binComponent L (oracle n a) c)) ∧
      (∀ n a, BinClipping L (oracle n a) ∧
        BinFittedSharesSimplex L (oracle n a) ∧
        BinDenominatorsClipped L (oracle n a) cpi) ∧
      (∀ n a, BinAdmissible M L (oracle n a)) ∧
      (∀ n a, a ∈ G n → ∀ c x,
        binComponent L (oracle (2 * (n + 1)) a) c x =
          binComponent _ (eHat (2 * (n + 1)) a) c x) ∧
      FiniteNuisanceRates M μ (fun n a => binComponent L (oracle n a))
        (binComponent L (eta0Bin M L)) := by
  obtain ⟨n, hn⟩ := (hG.eventually
    (gt_mem_nhds (by norm_num : (0 : ENNReal) < 1))).exists
  have hnG : (G n).Nonempty := by
    by_contra h
    have hz := Set.not_nonempty_iff_eq_empty.mp h
    simp only [hz, Set.compl_empty, measure_univ, lt_self_iff_false] at hn
  obtain ⟨a, ha⟩ := hnG
  have hL := hLabels n a ha
  have hfit := hr.1.2.2.2.2.1 (2 * (n + 1)) a
  have hdecoded := decodeBinComponents_regular_of_scoreLabels_eq L _ hL
    (eHat (2 * (n + 1)) a) cpi hfit.2.1 hfit.2.2.2 hfit.2.2.1
  obtain ⟨hcpi, hne⟩ := binary_clipping_simplex_geometry L cpi hK
    (decodeBinComponents L (binComponent _ (eHat (2 * (n + 1)) a)))
    hdecoded.2.2 hdecoded.2.1
  obtain ⟨F, hm, hb, heq, hrate⟩ := binDMLRegime_oracle_component_predictors_of_scoreLabels_eq
    M μ S I₁ I₂ pHat phi rho gap cpi L ch eHat hr G hG hLabels
  let raw := fun n a => repairBinNuisance L cpi hne (decodeBinComponents L (F n a))
  let oracle := fun n a => restrictBinShares L (raw n a)
  have hreg (n : ℕ) (a : A) : BinClipping L (oracle n a) ∧
      BinFittedSharesSimplex L (oracle n a) ∧
      BinDenominatorsClipped L (oracle n a) cpi := by
    have h := repairBinNuisance_regular L cpi hcpi hne (decodeBinComponents L (F n a))
    exact restrictBinShares_regular L _ cpi h.1 h.2.1 h.2.2
  have hmeas (c) : TrainingPredictorMeasurable M S I₁
      (fun n a => binComponent L (oracle n a) c) := by
    intro n
    let : MeasurableSpace A :=
      MeasurableSpace.comap (trainingView M S I₁ n) inferInstance
    have hh := repairBinNuisance_decoded_measurable L cpi hne (F n)
      (fun c => hm c n) c
    change Measurable (fun ax : A × X => binComponent L (oracle n ax.1) c ax.2)
    simpa only [oracle, raw, binComponent_restrictBinShares] using hh
  have heq' : ∀ n a, a ∈ G n → ∀ c x,
      binComponent L (oracle (2 * (n + 1)) a) c x =
        binComponent _ (eHat (2 * (n + 1)) a) c x := by
    intro n a ha c x
    have hf := hr.1.2.2.2.2.1 (2 * (n + 1)) a
    simp only [oracle, binComponent_restrictBinShares, raw]
    exact repairBinNuisance_component_eq_of_scoreLabels_eq L _ (hLabels n a ha)
      cpi hne _ _ (heq n a ha) hf.2.1 hf.2.2.2 hf.2.2.1 c x
  refine ⟨oracle, hmeas, hreg, ?_, heq', ?_⟩
  · intro n a
    have hmsection (c) : Measurable (binComponent L (raw n a) c) := by
      let : MeasurableSpace A :=
        MeasurableSpace.comap (trainingView M S I₁ n) inferInstance
      have hh := repairBinNuisance_decoded_measurable L cpi hne (F n)
        (fun c => hm c n) c
      exact hh.comp (measurable_const.prodMk measurable_id)
    have h := repairBinNuisance_regular L cpi hcpi hne (decodeBinComponents L (F n a))
    exact restrictBinShares_admissible_of_encoded_clipping M L (raw n a)
      h.1 h.2.1 hmsection
  · exact nuisanceRates_transfer_on_recovery M μ
      (fun n a => binComponent _ (eHat n a))
      (fun n a => binComponent L (oracle n a))
      (binComponent L (eta0Bin M L)) G hG heq' hr.2.1

-- @node: rearranged_decode_positiveValue_eq_of_count_eq
/-- If [two structures have the same number of levels](hyp:hK), then
[decoding the same components and rearranging the treated-success regressions
gives the same extended positive-level value under either structure](goal). -/
lemma rearranged_decode_positiveValue_eq_of_count_eq (H L : LevelData Z X)
    (hK : H.K = L.K) (F : (ℕ × ℕ × ℕ × Z) → X → ℝ) (k : ℕ) (x : X) :
    positiveValue (rearrangeP1 H (decodeBinComponents H F)).P1 k x =
      positiveValue (rearrangeP1 L (decodeBinComponents L F)).P1 k x := by
  simp [positiveValue, rearrangeP1, decodeBinComponents, hK]

-- @node: pooledQBin_rearranged_decode_eq_of_scoreLabels_eq
/-- If [two structures have identical score-recovery labels](hyp:hLabels) and
[the baseline level index does not exceed the reference level count](hyp:hk), then
[decoding the same components and rearranging yields equal pooled policy values
under the two structures at the selected indices and covariate value](goal). -/
lemma pooledQBin_rearranged_decode_eq_of_scoreLabels_eq
    (phi : Z → X → ℝ → ℝ) (H L : LevelData Z X)
    (hLabels : scoreRecoveryLabels H = scoreRecoveryLabels L)
    (F : (ℕ × ℕ × ℕ × Z) → X → ℝ) (k j : ℕ) (hk : k ≤ L.K) (x : X) :
    pooledQBin phi H (rearrangeP1 H (decodeBinComponents H F)) k j x =
      pooledQBin phi L (rearrangeP1 L (decodeBinComponents L F)) k j x := by
  obtain ⟨hK, hdom⟩ := (scoreRecoveryLabels_eq_iff H L).mp hLabels
  have hl := (hdom k hk).1
  unfold pooledQBin
  split
  · simp [rearrangeP1, decodeBinComponents, positiveValue, hK]
  · split
    · simp_all [rearrangeP1, decodeBinComponents, positiveValue]
    · have hj : j ≤ L.l k := by omega
      simp_all [rearrangeP1, decodeBinComponents, (hdom k hk).2.2 j hj]

-- @node: psiBin_rearranged_decode_eq_of_scoreLabels_eq
/-- If [the score-recovery labels agree](hyp:hLabels) and
[both structures have positive level counts](hyp:hH,hL), then
[decoding the same components and rearranging the treated-success regressions
gives identical binary scores for every observation under either structure](goal). -/
lemma psiBin_rearranged_decode_eq_of_scoreLabels_eq
    (M : LatentIVModel Ω X Z) (phi dphi : Z → X → ℝ → ℝ)
    (H L : LevelData Z X) (hLabels : scoreRecoveryLabels H = scoreRecoveryLabels L)
    (hH : LevelCountPos H.K) (hL : LevelCountPos L.K)
    (F : (ℕ × ℕ × ℕ × Z) → X → ℝ) (o : Obs X Z) :
    psiBin M phi dphi H hH o (rearrangeP1 H (decodeBinComponents H F)) =
      psiBin M phi dphi L hL o (rearrangeP1 L (decodeBinComponents L F)) := by
  obtain ⟨hK, hdom⟩ := (scoreRecoveryLabels_eq_iff H L).mp hLabels
  simp only [psiBin]
  apply congrArg₂ (· + ·)
  · rw [hK]
    apply Finset.sum_congr rfl
    intro k hk
    have hklt := Finset.mem_range.mp hk
    have hl := (hdom k hklt.le).1
    have hs := (hdom k hklt.le).2.1
    have hs1 := (hdom (k+1) hklt).2.1
    have hP := rearranged_decode_positiveValue_eq_of_count_eq H L hK F
    apply congrArg₂ (· + ·)
    · simp only [psiFullProdBin, binFullJ, hP,
        higherPolicy_eq_of_scoreLabels_eq H L hLabels,
        higherBaseline_eq_of_scoreLabels_eq H L hLabels]
      simp [RP, rearrangeP1, decodeBinComponents, positiveValue, fullValue, hK, hs, hs1]
    · rw [hl]
      apply Finset.sum_congr rfl
      intro j hj
      have hq := pooledQBin_rearranged_decode_eq_of_scoreLabels_eq phi H L hLabels F k
      have hqj := hq j hklt.le
      have hqprev := hq (j-1) hklt.le
      have hu := policyUnion_eq_of_scoreLabels_eq H L hLabels k j hklt.le
      have ht0 := (hdom k hklt.le).2.2 (j-1)
        (by have := (Finset.mem_Icc.mp hj).2; omega)
      have ht1 := (hdom k hklt.le).2.2 j (Finset.mem_Icc.mp hj).2
      simp only [psiProdBin, binScoreComponents, hMinus, Dbd, Edom, Iact,
        binFullJ, hP, hqj, hqprev, hu]
      simp [RP, Rp, RqBin, rearrangeP1, decodeBinComponents,
        positiveValue, regularValue, hK, hl, hs, hs1, ht0, ht1]
  · have hu := policyUnion_eq_of_scoreLabels_eq H L hLabels L.K 1 le_rfl
    have hs := (hdom L.K le_rfl).2.1
    simp [commonTailScore, rearrangeP1, decodeBinComponents, positiveValue, hK, hu, hs]

-- @node: psiBin_rearranged_decodeBinComponents_binComponent
/-- With [a positive level count](hyp:hK),
[encoding and decoding a nuisance record before rearranging leaves its binary score unchanged](goal). -/
lemma psiBin_rearranged_decodeBinComponents_binComponent
    (M : LatentIVModel Ω X Z) (phi dphi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (hK : LevelCountPos L.K) (e : NuisanceBin L) (o : Obs X Z) :
    psiBin M phi dphi L hK o (rearrangeP1 L (decodeBinComponents L (binComponent L e))) =
      psiBin M phi dphi L hK o (rearrangeP1 L e) := by
  rw [decodeBinComponents_binComponent, rearrangeP1_restrictBinShares]
  exact psiBin_restrictBinShares M phi dphi L hK o _

-- @node: psiBin_rearrangeP1_eq_of_component_eq_of_scoreLabels_eq
/-- If [the structures have identical score-recovery labels](hyp:hLabels),
[both level counts are positive](hyp:hH,hL), and
[the nuisance records agree in every encoded component at every covariate value](hyp:heq), then
[their binary scores agree after rearranging the treated-success regressions](goal). -/
lemma psiBin_rearrangeP1_eq_of_component_eq_of_scoreLabels_eq
    (M : LatentIVModel Ω X Z) (phi dphi : Z → X → ℝ → ℝ)
    (H L : LevelData Z X) (hLabels : scoreRecoveryLabels H = scoreRecoveryLabels L)
    (hH : LevelCountPos H.K) (hL : LevelCountPos L.K)
    (e : NuisanceBin H) (f : NuisanceBin L)
    (heq : ∀ c x, binComponent H e c x = binComponent L f c x) (o : Obs X Z) :
    psiBin M phi dphi H hH o (rearrangeP1 H e) =
      psiBin M phi dphi L hL o (rearrangeP1 L f) := by
  have hfun : binComponent H e = binComponent L f := funext fun c => funext (heq c)
  rw [← psiBin_rearranged_decodeBinComponents_binComponent M phi dphi H hH e o,
    psiBin_rearranged_decode_eq_of_scoreLabels_eq M phi dphi H L hLabels hH hL,
    hfun, psiBin_rearranged_decodeBinComponents_binComponent]

-- @node: fittedBinScore_eq_oracle_of_scoreLabels_eq
/-- For [fitted binary nuisance records on the recovered level structures](hyp:eHat),
if [the reference level count is positive](hyp:hK),
[the recovered score labels equal the reference labels at the selected sample size and realization](hyp:hLabels),
and [the oracle and fitted records agree componentwise there](hyp:heq), then
[the fitted binary score equals the reference oracle score after rearrangement](goal). -/
lemma fittedBinScore_eq_oracle_of_scoreLabels_eq
    (M : LatentIVModel Ω X Z) {A : Type*} [MeasurableSpace A]
    {μ : Measure A} [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (pHat : ℕ → A → Z → X → ℝ) (phi dphi : Z → X → ℝ → ℝ)
    (rho : ℕ → ℝ) (gap : ℝ) (L : LevelData Z X) (hK : LevelCountPos L.K)
    (eHat : ∀ n a, NuisanceBin (recoveredData M S I₁ I₂ pHat phi rho gap n a))
    (oracle : ℕ → A → NuisanceBin L) (n : ℕ) (a : A)
    (hLabels : scoreRecoveryLabels (recoveredData M S I₁ I₂ pHat phi rho gap n a) =
      scoreRecoveryLabels L)
    (heq : ∀ c x, binComponent L (oracle n a) c x =
      binComponent _ (eHat n a) c x) (o : Obs X Z) :
    fittedBinScore M S I₁ I₂ pHat phi dphi rho gap eHat n a o =
      psiBin M phi dphi L hK o (rearrangeP1 L (oracle n a)) := by
  have hk := (scoreRecoveryLabels_eq_iff _ _).mp hLabels |>.1
  have hK' : LevelCountPos (recoveredData M S I₁ I₂ pHat phi rho gap n a).K := hk.symm ▸ hK
  simp only [fittedBinScore, dif_pos hK']
  exact psiBin_rearrangeP1_eq_of_component_eq_of_scoreLabels_eq M phi dphi _ L hLabels
    hK' hK (eHat n a) (oracle n a) (fun c x => (heq c x).symm) o

-- @node: binDMLRegime_rearranged_oracle_score_records_of_scoreLabels_eq
/-- Suppose [the policy is a valid policy map](hyp:hphi),
[its specified derivative is correct](hyp:hd), [the reference level count is positive](hyp:hK),
[the fitted binary nuisance records on the recovered level structures](hyp:eHat)
[satisfy the finite binary double machine learning regime](hyp:hr),
[the recovery-event complements have probability tending to zero](hyp:hG), and
[score labels agree with the reference labels on those events at even sample sizes](hyp:hLabels).
Then [there exist training-measurable, clipped, simplex-valued, admissible oracle records
with finite nuisance rates, training-measurable rearranged scores, admissible rearrangements,
and exact equality between fitted and rearranged oracle scores on the recovery events](goal). -/
lemma binDMLRegime_rearranged_oracle_score_records_of_scoreLabels_eq
    (M : LatentIVModel Ω X Z) {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (pHat : ℕ → A → Z → X → ℝ) (phi dphi : Z → X → ℝ → ℝ)
    (hphi : IsPolicyMap phi) (hd : PolicyDifferentiable phi dphi)
    (rho : ℕ → ℝ) (gap cpi : ℝ) (L : LevelData Z X) (ch : ℝ)
    (hK : LevelCountPos L.K)
    (eHat : ∀ n a, NuisanceBin (recoveredData M S I₁ I₂ pHat phi rho gap n a))
    (hr : FiniteBinDMLRegime M μ S I₁ I₂ pHat phi rho gap cpi L ch eHat)
    (G : ℕ → Set A) (hG : Tendsto (fun n => μ (G n)ᶜ) atTop (𝓝 0))
    (hLabels : ∀ n a, a ∈ G n →
      scoreRecoveryLabels (recoveredData M S I₁ I₂ pHat phi rho gap (2 * (n + 1)) a) =
        scoreRecoveryLabels L) :
    ∃ oracle : ℕ → A → NuisanceBin L,
      (∀ c, TrainingPredictorMeasurable M S I₁
        (fun n a => binComponent L (oracle n a) c)) ∧
      (∀ n a, BinClipping L (oracle n a) ∧ BinFittedSharesSimplex L (oracle n a) ∧
        BinDenominatorsClipped L (oracle n a) cpi) ∧
      (∀ n a, BinAdmissible M L (oracle n a)) ∧
      FiniteNuisanceRates M μ (fun n a => binComponent L (oracle n a))
        (binComponent L (eta0Bin M L)) ∧
      TrainingPredictorMeasurable M S I₁
        (fun n a o => psiBin M phi dphi L hK o (rearrangeP1 L (oracle n a))) ∧
      (∀ n a, BinAdmissible M L (rearrangeP1 L (oracle n a))) ∧
      (∀ n a, a ∈ G n → ∀ o,
        fittedBinScore M S I₁ I₂ pHat phi dphi rho gap eHat (2 * (n + 1)) a o =
          psiBin M phi dphi L hK o (rearrangeP1 L (oracle (2 * (n + 1)) a))) := by
  obtain ⟨oracle, hm, hc, ha, heq, hrate⟩ :=
    binDMLRegime_regular_oracle_nuisance_records_of_scoreLabels_eq M μ S I₁ I₂ pHat phi rho gap
      cpi L ch hK eHat hr G hG hLabels
  refine ⟨oracle, hm, hc, ha, hrate, ?_, ?_, ?_⟩
  · exact training_measurable_rearranged_binary_score M S I₁ phi dphi hphi hd
      L hK oracle hm (fun n a => (hc n a).1)
  · intro n a
    exact rearrangeP1_admissible M L (oracle n a) (ha n a)
  · intro n a hna o
    exact fittedBinScore_eq_oracle_of_scoreLabels_eq M S I₁ I₂ pHat phi dphi rho
      gap L hK eHat oracle _ a (hLabels n a hna) (heq n a hna) o

-- @node: binDMLRegime_canonical_rearranged_oracle_score_records
/-- Under [threshold crossing](hyp:h), [a finite first-stage estimation rate](hyp:hRate),
[a valid policy map](hyp:hphi), [its specified derivative](hyp:hd), and
[a bounded Lipschitz policy derivative](hyp:hDerivative), suppose
[the canonical level ordering is covariate invariant](hyp:hL),
[policy levels avoid the boundary](hyp:hOff),
[the chosen gap separates distinct baseline and policy propensities](hyp:hgap),
[the canonical level count is positive](hyp:hK), and
[the fitted binary nuisance records on the recovered level structures](hyp:eHat)
[satisfy the finite binary double machine learning regime](hyp:hr).
Then [there exist canonical oracle records with training-measurable components,
clipping, simplex shares, denominator clipping, admissibility, and finite nuisance rates,
whose rearranged scores are training measurable and admissible and equal the fitted scores
on the canonical recovery events at even sample sizes](goal). -/
lemma binDMLRegime_canonical_rearranged_oracle_score_records
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
    ∃ oracle : ℕ → A → NuisanceBin L,
      (∀ c, TrainingPredictorMeasurable M S I₁
        (fun n a => binComponent L (oracle n a) c)) ∧
      (∀ n a, BinClipping L (oracle n a) ∧ BinFittedSharesSimplex L (oracle n a) ∧
        BinDenominatorsClipped L (oracle n a) cpi) ∧
      (∀ n a, BinAdmissible M L (oracle n a)) ∧
      FiniteNuisanceRates M μ (fun n a => binComponent L (oracle n a))
        (binComponent L (eta0Bin M L)) ∧
      TrainingPredictorMeasurable M S I₁
        (fun n a o => psiBin M phi dphi L hK o (rearrangeP1 L (oracle n a))) ∧
      (∀ n a, BinAdmissible M L (rearrangeP1 L (oracle n a))) ∧
      (∀ n a, a ∈ recoveryEvent M S I₁ I₂ pHat phi rho gap L (2 * (n + 1)) → ∀ o,
        fittedBinScore M S I₁ I₂ pHat phi dphi rho gap eHat (2 * (n + 1)) a o =
          psiBin M phi dphi L hK o (rearrangeP1 L (oracle (2 * (n + 1)) a))) := by
  have hG := binDMLRegime_recoveryEvent_compl_tendsto_zero M μ S I₁ I₂ h
    pHat hRate phi dphi hphi hd hDerivative x0 gap cpi rho hL hOff hgap hK ch eHat hr
  exact binDMLRegime_rearranged_oracle_score_records_of_scoreLabels_eq M μ S I₁ I₂
    pHat phi dphi hphi hd rho gap cpi _ ch hK eHat hr
    (fun n => recoveryEvent M S I₁ I₂ pHat phi rho gap
      (LevelStructure M.prop (policyProp phi M.prop) x0) (2 * (n + 1))) hG
    (fun n a ha => (mem_recoveryEvent_iff_scoreRecoveryLabels_eq
      M S I₁ I₂ pHat phi rho gap _ _ a).mp ha)

end Papers.TbsPrteOptimalTransport

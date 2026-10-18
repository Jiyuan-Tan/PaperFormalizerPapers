module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLFixedLabelPredictors
/-! Uniformly bounded nuisance coordinates with fixed recovery labels.
Clipping the measurable factor outside the image of the recovered training view
keeps every fixed-label predictor bounded, while preserving all feasible fits.
The nuisance rates consequently transfer to the population-label predictors on
any exact-recovery event whose probability tends to one. -/
public section
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Set Filter
open scoped Classical Topology

universe u v
variable {Ω : Type u} {X Z : Type v} {A : Type*}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]
  [Fintype Z] [DecidableEq Z]

-- @node: binComponent_abs_le_one_of_clipping
/-- If [binary nuisance coordinates obey their clipping restrictions](hyp:hc),
[every encoded binary component has absolute value at most one at every covariate
value](goal). -/
lemma binComponent_abs_le_one_of_clipping
    (L : LevelData Z X) (e : NuisanceBin L) (hc : BinClipping L e)
    (c : ℕ × ℕ × ℕ × Z) (x : X) : |binComponent L e c x| ≤ 1 := by
  have hfull := binClipping_full_range L e hc
  obtain ⟨hp, hl, hr, hs, ht, hop⟩ := hc
  have hunit (r : ℝ) (h : r ∈ Icc (0 : ℝ) 1) : |r| ≤ 1 := by
    rw [abs_of_nonneg h.1]
    exact h.2
  rcases c with ⟨code, k, j, z⟩
  unfold binComponent
  dsimp only
  split
  · exact hunit _ (hp z x)
  · unfold positiveValue
    split
    · exact hunit _ (hl _ x).1
    · norm_num
  · unfold positiveValue
    split
    · exact hunit _ (hl _ x).2.1
    · norm_num
  · unfold positiveValue
    split
    · exact hunit _ (hl _ x).2.2
    · norm_num
  · unfold regularValue
    split
    · exact hunit _ (hr _ x).1
    · norm_num
  · split
    · split
      · exact hunit _ (hs _ z x)
      · norm_num
    · norm_num
  · unfold fullValue
    split
    · exact abs_le.mpr (hfull _ x)
    · norm_num
  · unfold regularValue
    split
    · exact hunit _ (hr _ x).2
    · norm_num
  · exact hunit _ (ht x)

-- @node: contComponent_abs_le_of_clipping
/-- If [continuous-outcome nuisance coordinates obey their clipping
restrictions](hyp:hc), [every encoded component has absolute value at most one
plus the absolute lower and upper outcome endpoints at every covariate value](goal). -/
lemma contComponent_abs_le_of_clipping
    (M : LatentIVModel Ω X Z) (L : LevelData Z X) (e : NuisanceCont L)
    (hc : ContClipping M L e) (c : ℕ × ℕ × ℕ × Z) (x : X) :
    |contComponent M L e c x| ≤ 1 + |M.yMin| + |M.yMax| := by
  obtain ⟨hp, hl, hr, hs, hf, ht, hn, hmp, hmm, hjp, hjm, hjfp, hjfm, _hprob⟩ := hc
  let C := 1 + |M.yMin| + |M.yMax|
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have h1 : 1 ≤ C := by dsimp [C]; linarith [abs_nonneg M.yMin, abs_nonneg M.yMax]
  have hlo : -C ≤ M.yMin := by
    dsimp [C]; linarith [neg_abs_le M.yMin, abs_nonneg M.yMax]
  have hhi : M.yMax ≤ C := by
    dsimp [C]; linarith [le_abs_self M.yMax, abs_nonneg M.yMin]
  have hsmall (r : ℝ) (h : r ∈ Icc (0 : ℝ) 1) : |r| ≤ C := by
    rw [abs_of_nonneg h.1]
    exact h.2.trans h1
  have hout (r : ℝ) (h : r ∈ Icc M.yMin M.yMax) : |r| ≤ C :=
    abs_le.mpr ⟨hlo.trans h.1, h.2.trans hhi⟩
  have htrunc (r : ℝ) (h : r ∈ Icc (min 0 M.yMin) (max 0 M.yMax)) : |r| ≤ C := by
    apply abs_le.mpr
    exact ⟨(le_min (neg_nonpos.mpr hC) hlo).trans h.1,
      h.2.trans (max_le hC hhi)⟩
  rcases c with ⟨code, k, j, z⟩
  change |contComponent M L e (code, k, j, z) x| ≤ C
  unfold contComponent
  dsimp only
  split
  · exact hsmall _ (hp z x)
  · unfold positiveValue
    split
    · exact hsmall _ (hl _ x).1
    · simpa using hC
  · unfold positiveValue
    split
    · exact hsmall _ (hl _ x).2
    · simpa using hC
  · unfold regularValue
    split
    · exact hsmall _ (hr _ x).1
    · simpa using hC
  · split
    · unfold shareValue
      split
      · exact hsmall _ (hs _ z x)
      · simpa using hC
    · simpa using hC
  · unfold fullValue
    split
    · exact (abs_le.mpr (hf _ x)).trans h1
    · simpa using hC
  · unfold regularValue
    split
    · exact hsmall _ (hr _ x).2
    · simpa using hC
  · exact hsmall _ (ht x)
  · unfold nuValue
    split
    · dsimp [C]; linarith [abs_nonneg M.yMax]
    · split
      · exact hout _ (hn _ x)
      · dsimp [C]; linarith [abs_nonneg M.yMin]
  · unfold boundaryValue
    split
    · exact hsmall _ (hmp _ x)
    · split
      · simpa using h1
      · simpa using hC
  · unfold minusBoundaryValue
    split
    · exact hsmall _ (hmm _ x)
    · split
      · simpa using h1
      · simpa using hC
  · unfold meanValue
    split
    · exact htrunc _ (hjp _ x)
    · simpa using hC
  · unfold minusMeanValue
    split
    · exact htrunc _ (hjm _ x)
    · simpa using hC
  · unfold fullValue
    split
    · exact hout _ (hjfp _ x)
    · simpa using hC
  · unfold minusFullValue
    split
    · exact hout _ (hjfm _ x)
    · simpa using hC

-- @node: binDMLRegime_bounded_fixed_label_components
/-- For [binary nuisance estimates on the recovered levels](hyp:eHat), under [the finite binary DML regime](hyp:hr), [there exist component
predictors jointly measurable in the training view, recovery labels, and
covariates, bounded in absolute value by one, reproducing all fitted binary
components at the recovered labels, and measurable from training data and
covariates whenever the labels and component are fixed](goal). -/
lemma binDMLRegime_bounded_fixed_label_components
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (pHat : ℕ → A → Z → X → ℝ) (phi : Z → X → ℝ → ℝ)
    (rho : ℕ → ℝ) (gap cpi : ℝ) (L : LevelData Z X) (ch : ℝ)
    (eHat : ∀ n a, NuisanceBin (recoveredData M S I₁ I₂ pHat phi rho gap n a))
    (hr : FiniteBinDMLRegime M μ S I₁ I₂ pHat phi rho gap cpi L ch eHat) :
    ∃ F : ∀ n, (Finset ℕ × (Fin n → Unit ⊕ Obs X Z)) →
        (ℕ × (ℕ → ℕ) × (ℕ → Finset Z) × (ℕ → ℕ → Finset Z)) →
        (ℕ × ℕ × ℕ × Z) → X → ℝ,
      (∀ n c, Measurable (fun tb :
        ((Finset ℕ × (Fin n → Unit ⊕ Obs X Z)) ×
          (ℕ × (ℕ → ℕ) × (ℕ → Finset Z) × (ℕ → ℕ → Finset Z))) × X =>
        F n tb.1.1 tb.1.2 c tb.2)) ∧
      (∀ n t d c x, |F n t d c x| ≤ 1) ∧
      (∀ n a c x, binComponent _ (eHat n a) c x =
        F n (trainingView M S I₁ n a)
          (recoveryLabels (recoveredData M S I₁ I₂ pHat phi rho gap n a)) c x) ∧
      (∀ d c, TrainingPredictorMeasurable M S I₁
        (fun n a x => F n (trainingView M S I₁ n a) d c x)) := by
  have hex (n : ℕ) (c : ℕ × ℕ × ℕ × Z) :=
    bounded_fixed_label_predictor_factorization
      (trainingView M S I₁ n)
      (fun a => recoveryLabels (recoveredData M S I₁ I₂ pHat phi rho gap n a))
      (fun a x => binComponent _ (eHat n a) c x)
      (hr.1.2.2.2.2.2.1 n c) 1 zero_le_one
      (fun a x => binComponent_abs_le_one_of_clipping _ _
        (hr.1.2.2.2.2.1 n a).2.1 c x)
  choose F hm hb heq hfixed using hex
  refine ⟨fun n t d c x => F n c t d x, hm,
    (fun n t d c x => hb n c t d x), (fun n a c x => heq n c a x), ?_⟩
  intro d c n
  exact hfixed n c d

-- @node: contDMLRegime_bounded_fixed_label_components
/-- For [continuous-outcome nuisance estimates on the recovered levels](hyp:eHat), under [the finite continuous-outcome DML regime](hyp:hr), [there exist
component predictors jointly measurable in the training view, recovery labels,
and covariates, bounded in absolute value by one plus the absolute outcome
endpoints, reproducing all fitted continuous components at the recovered labels,
and measurable from training data and covariates for fixed labels and component](goal). -/
lemma contDMLRegime_bounded_fixed_label_components
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (pHat : ℕ → A → Z → X → ℝ) (phi : Z → X → ℝ → ℝ)
    (rho : ℕ → ℝ) (gap cpi : ℝ) (L : LevelData Z X) (ch : ℝ)
    (eHat : ∀ n a, NuisanceCont (recoveredData M S I₁ I₂ pHat phi rho gap n a))
    (hr : FiniteContDMLRegime M μ S I₁ I₂ pHat phi rho gap cpi L ch eHat) :
    ∃ F : ∀ n, (Finset ℕ × (Fin n → Unit ⊕ Obs X Z)) →
        (ℕ × (ℕ → ℕ) × (ℕ → Finset Z) × (ℕ → ℕ → Finset Z)) →
        (ℕ × ℕ × ℕ × Z) → X → ℝ,
      (∀ n c, Measurable (fun tb :
        ((Finset ℕ × (Fin n → Unit ⊕ Obs X Z)) ×
          (ℕ × (ℕ → ℕ) × (ℕ → Finset Z) × (ℕ → ℕ → Finset Z))) × X =>
        F n tb.1.1 tb.1.2 c tb.2)) ∧
      (∀ n t d c x, |F n t d c x| ≤ 1 + |M.yMin| + |M.yMax|) ∧
      (∀ n a c x, contComponent M _ (eHat n a) c x =
        F n (trainingView M S I₁ n a)
          (recoveryLabels (recoveredData M S I₁ I₂ pHat phi rho gap n a)) c x) ∧
      (∀ d c, TrainingPredictorMeasurable M S I₁
        (fun n a x => F n (trainingView M S I₁ n a) d c x)) := by
  have hex (n : ℕ) (c : ℕ × ℕ × ℕ × Z) :=
    bounded_fixed_label_predictor_factorization
      (trainingView M S I₁ n)
      (fun a => recoveryLabels (recoveredData M S I₁ I₂ pHat phi rho gap n a))
      (fun a x => contComponent M _ (eHat n a) c x)
      (hr.1.2.2.2.1 n c) (1 + |M.yMin| + |M.yMax|) (by positivity)
      (fun a x => contComponent_abs_le_of_clipping M _ _
        (hr.1.2.2.1.2.2.2.1 n a).1 c x)
  choose F hm hb heq hfixed using hex
  refine ⟨fun n t d c x => F n c t d x, hm,
    (fun n t d c x => hb n c t d x), (fun n a c x => heq n c a x), ?_⟩
  intro d c n
  exact hfixed n c d

-- @node: fixed_label_component_rates_on_recovery
/-- Given [a training summary for each sample size and realization](hyp:view) and
[component predictors indexed by that summary, labels, and covariates](hyp:F),
suppose [fitted components factor through the training summary and estimated
labels using these predictors](hyp:heq), [the recovery events have probability tending to one](hyp:hG),
[the labels equal a fixed label on those events at even sample sizes](hyp:hlabels),
and [the fitted components satisfy finite nuisance quarter-rate bounds](hyp:hr).
Then [the predictors evaluated at that fixed label satisfy the same rates relative
to the reference components](goal). -/
lemma fixed_label_component_rates_on_recovery
    (M : LatentIVModel Ω X Z) (μ : Measure A)
    {D C : Type*} {T : ℕ → Type*} (view : ∀ n, A → T n) (labels : ℕ → A → D)
    (fit : ℕ → A → C → X → ℝ) (truth : C → X → ℝ)
    (F : ∀ n, T n → D → C → X → ℝ)
    (heq : ∀ n a c x, fit n a c x = F n (view n a) (labels n a) c x)
    (d : D) (G : ℕ → Set A)
    (hG : Tendsto (fun n => μ (G n)ᶜ) atTop (𝓝 0))
    (hlabels : ∀ n a, a ∈ G n → labels (2 * (n + 1)) a = d)
    (hr : FiniteNuisanceRates M μ fit truth) :
    FiniteNuisanceRates M μ (fun n a => F n (view n a) d) truth := by
  apply nuisanceRates_transfer_on_recovery M μ fit _ truth G hG _ hr
  intro n a ha c x
  rw [heq, hlabels n a ha]

-- @node: binDMLRegime_oracle_component_predictors
/-- For [binary nuisance estimates on the recovered levels](hyp:eHat), under [the finite binary DML regime](hyp:hr), if [recovery events have
probability tending to one](hyp:hG) and [recovered labels equal the population
labels on those events at even sample sizes](hyp:hlabels), [there exist oracle
component predictors measurable from training data and covariates, bounded by one
in absolute value, equal to the fitted binary components on recovery events, and
satisfying finite nuisance quarter-rate bounds relative to the population binary
components](goal). -/
lemma binDMLRegime_oracle_component_predictors
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (pHat : ℕ → A → Z → X → ℝ) (phi : Z → X → ℝ → ℝ)
    (rho : ℕ → ℝ) (gap cpi : ℝ) (L : LevelData Z X) (ch : ℝ)
    (eHat : ∀ n a, NuisanceBin (recoveredData M S I₁ I₂ pHat phi rho gap n a))
    (hr : FiniteBinDMLRegime M μ S I₁ I₂ pHat phi rho gap cpi L ch eHat)
    (G : ℕ → Set A)
    (hG : Tendsto (fun n => μ (G n)ᶜ) atTop (𝓝 0))
    (hlabels : ∀ n a, a ∈ G n →
      recoveryLabels (recoveredData M S I₁ I₂ pHat phi rho gap (2 * (n + 1)) a) =
        recoveryLabels L) :
    ∃ oracle : ℕ → A → (ℕ × ℕ × ℕ × Z) → X → ℝ,
      (∀ c, TrainingPredictorMeasurable M S I₁ (fun n a => oracle n a c)) ∧
      (∀ n a c x, |oracle n a c x| ≤ 1) ∧
      (∀ n a, a ∈ G n → ∀ c x,
        oracle (2 * (n + 1)) a c x = binComponent _ (eHat (2 * (n + 1)) a) c x) ∧
      FiniteNuisanceRates M μ oracle (binComponent L (eta0Bin M L)) := by
  obtain ⟨F, hm, hb, heq, ht⟩ :=
    binDMLRegime_bounded_fixed_label_components M μ S I₁ I₂ pHat phi rho gap cpi L ch eHat hr
  refine ⟨fun n a => F n (trainingView M S I₁ n a) (recoveryLabels L),
    ht (recoveryLabels L), (fun n a c x => hb n _ _ c x), ?_, ?_⟩
  · intro n a ha c x
    rw [heq, hlabels n a ha]
  · exact fixed_label_component_rates_on_recovery M μ
      (trainingView M S I₁) _ _ _ F heq (recoveryLabels L) G hG hlabels hr.2.1

-- @node: contDMLRegime_oracle_component_predictors
/-- For [continuous-outcome nuisance estimates on the recovered levels](hyp:eHat), under [the finite continuous-outcome DML regime](hyp:hr), if [recovery
events have probability tending to one](hyp:hG) and [the recovered labels equal
the population labels on those events at even sample sizes](hyp:hlabels), [there
exist oracle component predictors measurable from training data and covariates,
bounded in absolute value by one plus the absolute outcome endpoints, equal to
the fitted continuous components on recovery events, and satisfying finite
nuisance quarter-rate bounds relative to the population continuous components](goal). -/
lemma contDMLRegime_oracle_component_predictors
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (pHat : ℕ → A → Z → X → ℝ) (phi : Z → X → ℝ → ℝ)
    (rho : ℕ → ℝ) (gap cpi : ℝ) (L : LevelData Z X) (ch : ℝ)
    (eHat : ∀ n a, NuisanceCont (recoveredData M S I₁ I₂ pHat phi rho gap n a))
    (hr : FiniteContDMLRegime M μ S I₁ I₂ pHat phi rho gap cpi L ch eHat)
    (G : ℕ → Set A)
    (hG : Tendsto (fun n => μ (G n)ᶜ) atTop (𝓝 0))
    (hlabels : ∀ n a, a ∈ G n →
      recoveryLabels (recoveredData M S I₁ I₂ pHat phi rho gap (2 * (n + 1)) a) =
        recoveryLabels L) :
    ∃ oracle : ℕ → A → (ℕ × ℕ × ℕ × Z) → X → ℝ,
      (∀ c, TrainingPredictorMeasurable M S I₁ (fun n a => oracle n a c)) ∧
      (∀ n a c x, |oracle n a c x| ≤ 1 + |M.yMin| + |M.yMax|) ∧
      (∀ n a, a ∈ G n → ∀ c x,
        oracle (2 * (n + 1)) a c x = contComponent M _ (eHat (2 * (n + 1)) a) c x) ∧
      FiniteNuisanceRates M μ oracle (contComponent M L (trueNuisance M L)) := by
  obtain ⟨F, hm, hb, heq, ht⟩ :=
    contDMLRegime_bounded_fixed_label_components M μ S I₁ I₂ pHat phi rho gap cpi L ch eHat hr
  refine ⟨fun n a => F n (trainingView M S I₁ n a) (recoveryLabels L),
    ht (recoveryLabels L), (fun n a c x => hb n _ _ c x), ?_, ?_⟩
  · intro n a ha c x
    rw [heq, hlabels n a ha]
  · exact fixed_label_component_rates_on_recovery M μ
      (trainingView M S I₁) _ _ _ F heq (recoveryLabels L) G hG hlabels hr.2.1

end Papers.TbsPrteOptimalTransport

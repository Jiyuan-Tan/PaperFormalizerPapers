module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLTrainingFactorization
public import Causalean.Stat.Limit.ProbabilityTransfer
/-! Oracle predictors with the recovered labels held fixed.
Factorization through the training summary and labels gives a measurable family
of training-only predictors. Clipping the factor preserves its bound even for
label configurations outside the image of the feasible recovery procedure.
Nuisance rates transfer on events where the fixed-label and feasible fits agree. -/
public section
set_option linter.unusedSectionVars false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Set Filter
open scoped Topology

-- @node: bounded_fixed_label_predictor_factorization
/-- If [a fitted predictor is jointly measurable using only the training view,
recovered labels, and prediction argument](hyp:hm), [the bound is nonnegative](hyp:hC),
and [the predictor is uniformly bounded in absolute value by that bound](hyp:hb),
then [it factors through a jointly measurable function of the training view,
labels, and prediction argument with the same uniform bound; fixing any label
leaves a predictor measurable using only the training view and prediction argument](goal). -/
lemma bounded_fixed_label_predictor_factorization
    {A T D B : Type*} [MeasurableSpace T] [MeasurableSpace D] [MeasurableSpace B]
    (view : A → T) (labels : A → D) (fit : A → B → ℝ)
    (hm : Measurable[(MeasurableSpace.comap
      (fun a => (view a, labels a)) inferInstance).prod inferInstance]
      (Function.uncurry fit))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ a b, |fit a b| ≤ C) :
    ∃ F : T → D → B → ℝ,
      Measurable (fun tb : (T × D) × B => F tb.1.1 tb.1.2 tb.2) ∧
      (∀ t d b, |F t d b| ≤ C) ∧
      (∀ a b, fit a b = F (view a) (labels a) b) ∧
      (∀ d, Measurable[(MeasurableSpace.comap view inferInstance).prod inferInstance]
        (fun ab : A × B => F (view ab.1) d ab.2)) := by
  obtain ⟨G, hG, hGb, heq⟩ := bounded_training_predictor_factorization
    (fun a => (view a, labels a)) fit hm C hC hb
  refine ⟨fun t d b => G (t, d) b, hG, ?_, heq, ?_⟩
  · intro t d b
    exact hGb (t, d) b
  · intro d
    have hv : Measurable[MeasurableSpace.comap view inferInstance] view :=
      Measurable.of_comap_le le_rfl
    exact hG.comp (((hv.comp measurable_fst).prodMk measurable_const).prodMk
      measurable_snd)

-- @node: measurable_fixed_label_predictor_factorization
/-- If [a fitted predictor is jointly measurable using only the training view,
recovered labels, and prediction argument](hyp:hm), then [it factors through a
jointly measurable function of those three objects, and fixing any label leaves
a predictor measurable using only the training view and prediction argument](goal). -/
lemma measurable_fixed_label_predictor_factorization
    {A T D B : Type*} [MeasurableSpace T] [MeasurableSpace D] [MeasurableSpace B]
    (view : A → T) (labels : A → D) (fit : A → B → ℝ)
    (hm : Measurable[(MeasurableSpace.comap
      (fun a => (view a, labels a)) inferInstance).prod inferInstance]
      (Function.uncurry fit)) :
    ∃ F : T → D → B → ℝ,
      Measurable (fun tb : (T × D) × B => F tb.1.1 tb.1.2 tb.2) ∧
      (∀ a b, fit a b = F (view a) (labels a) b) ∧
      (∀ d, Measurable[(MeasurableSpace.comap view inferInstance).prod inferInstance]
        (fun ab : A × B => F (view ab.1) d ab.2)) := by
  obtain ⟨G, hG, heq⟩ := measurable_training_predictor_factorization
    (fun a => (view a, labels a)) fit hm
  refine ⟨fun t d b => G (t, d) b, hG, heq, ?_⟩
  intro d
  have hv : Measurable[MeasurableSpace.comap view inferInstance] view :=
    Measurable.of_comap_le le_rfl
  exact hG.comp (((hv.comp measurable_fst).prodMk measurable_const).prodMk
    measurable_snd)

universe u v

-- @node: nuisanceRates_transfer_on_recovery
/-- If [the probability of recovery failure tends to zero](hyp:hG), [the oracle
and feasible predictors agree for every component and covariate on recovery
events at sample sizes twice one more than the index](hyp:heq), and [each feasible
predictor's L2 error relative to the truth is of smaller order in probability than
the inverse fourth root of sample size along those sample sizes](hyp:hr),
then [the oracle predictors satisfy those same componentwise L2 rate conditions](goal). -/
lemma nuisanceRates_transfer_on_recovery
    {Ω : Type u} {X Z : Type v} {A C : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [MeasurableSpace Z] [MeasurableSpace A] [TopologicalSpace X] [TopologicalSpace Z]
    [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
    [Nonempty X] [Nonempty Z]
    (M : LatentIVModel Ω X Z) (μ : Measure A)
    (feasible oracle : ℕ → A → C → X → ℝ) (truth : C → X → ℝ)
    (G : ℕ → Set A)
    (hG : Tendsto (fun n => μ (G n)ᶜ) atTop (𝓝 0))
    (heq : ∀ n a, a ∈ G n → ∀ c x,
      oracle (2 * (n + 1)) a c x = feasible (2 * (n + 1)) a c x)
    (hr : FiniteNuisanceRates M μ feasible truth) :
    FiniteNuisanceRates M μ oracle truth := by
  intro c
  apply Causalean.Stat.isLittleOp_of_isLittleOp_on_highProbEvent
    G (fun n => μ (G n)ᶜ) hG (fun _ => le_rfl) _ (hr c)
  intro n a ha
  have hf : oracle (2 * (n + 1)) a c = feasible (2 * (n + 1)) a c :=
    funext (heq n a ha c)
  rw [hf]

variable {Ω : Type u} {X Z : Type v} {A : Type*}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]
  [Fintype Z] [DecidableEq Z]

-- @node: contDMLRegime_fixed_label_component_factorization
/-- For [continuous nuisance records fitted on the recovered levels](hyp:eHat), under [the finite continuous-outcome double machine learning regime](hyp:hr),
[every fitted nuisance component can be represented by a jointly measurable
function of the training view, recovered labels, and covariates; fixing the
labels and component gives a predictor measurable with respect to the first
training split](goal). -/
lemma contDMLRegime_fixed_label_component_factorization
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
      (∀ n a c x, contComponent M _ (eHat n a) c x =
        F n (trainingView M S I₁ n a)
          (recoveryLabels (recoveredData M S I₁ I₂ pHat phi rho gap n a)) c x) ∧
      (∀ d c, TrainingPredictorMeasurable M S I₁
        (fun n a x => F n (trainingView M S I₁ n a) d c x)) := by
  have hex (n : ℕ) (c : ℕ × ℕ × ℕ × Z) :=
    measurable_fixed_label_predictor_factorization
      (trainingView M S I₁ n)
      (fun a => recoveryLabels (recoveredData M S I₁ I₂ pHat phi rho gap n a))
      (fun a x => contComponent M _ (eHat n a) c x)
      (hr.1.2.2.2.1 n c)
  choose F hm heq hfixed using hex
  refine ⟨fun n t d c x => F n c t d x, hm, (fun n a c x => heq n c a x), ?_⟩
  intro d c n
  exact hfixed n c d

-- @node: binDMLRegime_fixed_label_component_factorization
/-- For [binary nuisance records fitted on the recovered levels](hyp:eHat), under [the finite binary-outcome double machine learning regime](hyp:hr),
[every fitted nuisance component can be represented by a jointly measurable
function of the training view, recovered labels, and covariates; fixing the
labels and component gives a predictor measurable with respect to the first
training split](goal). -/
lemma binDMLRegime_fixed_label_component_factorization
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
      (∀ n a c x, binComponent _ (eHat n a) c x =
        F n (trainingView M S I₁ n a)
          (recoveryLabels (recoveredData M S I₁ I₂ pHat phi rho gap n a)) c x) ∧
      (∀ d c, TrainingPredictorMeasurable M S I₁
        (fun n a x => F n (trainingView M S I₁ n a) d c x)) := by
  have hex (n : ℕ) (c : ℕ × ℕ × ℕ × Z) :=
    measurable_fixed_label_predictor_factorization
      (trainingView M S I₁ n)
      (fun a => recoveryLabels (recoveredData M S I₁ I₂ pHat phi rho gap n a))
      (fun a x => binComponent _ (eHat n a) c x)
      (hr.1.2.2.2.2.2.1 n c)
  choose F hm heq hfixed using hex
  refine ⟨fun n t d c x => F n c t d x, hm, (fun n a c x => heq n c a x), ?_⟩
  intro d c n
  exact hfixed n c d

end Papers.TbsPrteOptimalTransport

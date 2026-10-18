module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLBinaryComponentBridge
public import Papers.TbsPrteOptimalTransport.Helpers.DMLBoundedFixedLabels
/-! Reconstruction of binary nuisance records from fixed-label component predictors.
The encoding omits shares outside their policy set; decoding therefore returns
the supported record, which has exactly the same evaluation score. -/
@[expose] public section
set_option linter.style.openClassical false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Set Filter
open scoped Classical Topology

universe u v
variable {Ω : Type u} {X Z : Type v}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]
  [Fintype Z] [DecidableEq Z]

-- @node: decodeBinComponents
/-- Given [policy level data](hyp:L) and [a family of component predictions
indexed by component code, level, policy index, and instrument](hyp:F), the
[decoded binary nuisance record](goal) first [chooses a reference instrument](step:1)
and then [reads codes zero through eight into the propensity, positive baseline
level, success regression, baseline set probability, policy set probability,
share, full-interval weight, policy weight, and tail weight components, using the reference
instrument for components without an instrument index](step:2). -/
noncomputable def decodeBinComponents (L : LevelData Z X)
    (F : (ℕ × ℕ × ℕ × Z) → X → ℝ) : NuisanceBin L :=
  let z₀ : Z := Classical.choice inferInstance
  { prop := fun z => F (0, 0, 0, z)
    pLev := fun k => F (1, k, 0, z₀)
    P1 := fun k => F (2, k, 0, z₀)
    piLev := fun k => F (3, k, 0, z₀)
    tauLev := fun a => F (4, a.val.1, a.val.2, z₀)
    share := fun a z => F (5, a.val.1, a.val.2, z)
    gammaFull := fun k => F (6, k, 0, z₀)
    gamma := fun a => F (7, a.val.1, a.val.2, z₀)
    gammaTail := F (8, 0, 0, z₀) }

-- @node: decodeBinComponents_binComponent
/-- [Decoding the encoded components of a binary nuisance record recovers that
record with its shares set to zero outside their policy sets](goal). -/
lemma decodeBinComponents_binComponent (L : LevelData Z X) (e : NuisanceBin L) :
    decodeBinComponents L (binComponent L e) = restrictBinShares L e := by
  cases e
  unfold decodeBinComponents restrictBinShares
  dsimp only
  congr 1
  · funext k x
    simp [binComponent, positiveValue, k.property]
  · funext k x
    simp [binComponent, positiveValue, k.property]
  · funext k x
    simp [binComponent, positiveValue, k.property]
  · funext a x
    simp [binComponent, regularValue, a.property]
  · funext a z x
    simp [binComponent, a.property]
  · funext k x
    simp [binComponent, fullValue, k.isLt]
  · funext a x
    simp [binComponent, regularValue, a.property]

-- @node: psiBin_decodeBinComponents_binComponent
/-- With [a positive number of policy levels](hyp:hK), [encoding and then
decoding a binary nuisance record leaves its binary score unchanged at each
observation](goal). -/
lemma psiBin_decodeBinComponents_binComponent (M : LatentIVModel Ω X Z)
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (hK : LevelCountPos L.K) (o : Obs X Z) (e : NuisanceBin L) :
    psiBin M phi dphi L hK o (decodeBinComponents L (binComponent L e)) =
      psiBin M phi dphi L hK o e := by
  rw [decodeBinComponents_binComponent]
  exact psiBin_restrictBinShares M phi dphi L hK o e

-- @node: binComponent_decodeBinComponents_of_level_eq
/-- If [two sets of policy level data are equal](hyp:hL) and [the prediction
family agrees with every encoded component of a nuisance record for the second
set](hyp:hF), then [decoding with the first set and encoding again reproduces
each original component at every covariate value](goal). -/
lemma binComponent_decodeBinComponents_of_level_eq
    (L L' : LevelData Z X) (hL : L' = L) (e : NuisanceBin L')
    (F : (ℕ × ℕ × ℕ × Z) → X → ℝ)
    (hF : ∀ c x, F c x = binComponent L' e c x) (c : ℕ × ℕ × ℕ × Z) (x : X) :
    binComponent L (decodeBinComponents L F) c x = binComponent L' e c x := by
  subst L'
  have hfun : F = binComponent L e := funext fun c => funext (hF c)
  rw [hfun, decodeBinComponents_binComponent]
  exact binComponent_restrictBinShares L e c x

-- @node: decodeBinComponents_measurable
/-- If [every component prediction is jointly measurable in the training
realization and covariates](hyp:hm), then [every component obtained by decoding
and encoding again is jointly measurable in those same variables](goal). -/
@[fun_prop] lemma decodeBinComponents_measurable
    {A : Type*} [MeasurableSpace A]
    (L : LevelData Z X) (F : A → (ℕ × ℕ × ℕ × Z) → X → ℝ)
    (hm : ∀ c, Measurable (fun ax : A × X => F ax.1 c ax.2))
    (c : ℕ × ℕ × ℕ × Z) :
    Measurable (fun ax : A × X =>
      binComponent L (decodeBinComponents L (F ax.1)) c ax.2) := by
  rcases c with ⟨code, k, j, z⟩
  unfold binComponent decodeBinComponents
  dsimp only
  split <;> try dsimp only
  all_goals try simp only [positiveValue, regularValue, fullValue]
  all_goals repeat' first | fun_prop | split

-- @node: binDMLRegime_oracle_nuisance_records
/-- Consider [fitted binary nuisance records indexed by the recovered policy
level data](hyp:eHat) and suppose [they satisfy the finite binary double machine
learning regime](hyp:hr). If [the probability of leaving the recovery events
tends to zero](hyp:hG) and [the recovered level data at twice the sample index
plus two equal the fixed level data on those events](hyp:hLevels), then [there
exists a sequence of nuisance records on the fixed level data whose encoded
components are measurable with respect to the first training split, agree with
the fitted encoded components on the recovery events at those indices, and
have root integrated squared errors relative to the true binary nuisance record,
at twice the sample index plus two, of smaller order in probability than the
inverse fourth root of that index](goal). -/
lemma binDMLRegime_oracle_nuisance_records
    (M : LatentIVModel Ω X Z) {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (pHat : ℕ → A → Z → X → ℝ) (phi : Z → X → ℝ → ℝ)
    (rho : ℕ → ℝ) (gap cpi : ℝ) (L : LevelData Z X) (ch : ℝ)
    (eHat : ∀ n a, NuisanceBin (recoveredData M S I₁ I₂ pHat phi rho gap n a))
    (hr : FiniteBinDMLRegime M μ S I₁ I₂ pHat phi rho gap cpi L ch eHat)
    (G : ℕ → Set A)
    (hG : Tendsto (fun n => μ (G n)ᶜ) atTop (𝓝 0))
    (hLevels : ∀ n a, a ∈ G n →
      recoveredData M S I₁ I₂ pHat phi rho gap (2 * (n + 1)) a = L) :
    ∃ oracle : ℕ → A → NuisanceBin L,
      (∀ c, TrainingPredictorMeasurable M S I₁
        (fun n a => binComponent L (oracle n a) c)) ∧
      (∀ n a, a ∈ G n → ∀ c x,
        binComponent L (oracle (2 * (n + 1)) a) c x =
          binComponent _ (eHat (2 * (n + 1)) a) c x) ∧
      FiniteNuisanceRates M μ (fun n a => binComponent L (oracle n a))
        (binComponent L (eta0Bin M L)) := by
  have hlabels : ∀ n a, a ∈ G n →
      recoveryLabels (recoveredData M S I₁ I₂ pHat phi rho gap (2 * (n + 1)) a) =
        recoveryLabels L := fun n a ha => congrArg recoveryLabels (hLevels n a ha)
  obtain ⟨F, hm, hb, heq, hrate⟩ := binDMLRegime_oracle_component_predictors
    M μ S I₁ I₂ pHat phi rho gap cpi L ch eHat hr G hG hlabels
  have heq' : ∀ n a, a ∈ G n → ∀ c x,
      binComponent L (decodeBinComponents L (F (2 * (n + 1)) a)) c x =
        binComponent _ (eHat (2 * (n + 1)) a) c x := by
    intro n a ha c x
    exact binComponent_decodeBinComponents_of_level_eq L _ (hLevels n a ha)
      (eHat (2 * (n + 1)) a) _ (heq n a ha) c x
  refine ⟨fun n a => decodeBinComponents L (F n a), ?_, heq', ?_⟩
  · intro c n
    let : MeasurableSpace A :=
      MeasurableSpace.comap (trainingView M S I₁ n) inferInstance
    exact decodeBinComponents_measurable L (F n) (fun d => hm d n) c
  · exact nuisanceRates_transfer_on_recovery M μ
      (fun n a => binComponent _ (eHat n a))
      (fun n a => binComponent L (decodeBinComponents L (F n a)))
      (binComponent L (eta0Bin M L)) G hG heq' hr.2.1

-- The rearranged oracle uses the same single success-probability vector as the
-- feasible score. Equality of encodings preserves that entire vector.
-- @node: psiBin_rearrangeP1_eq_of_binComponent_eq
/-- With [a positive number of policy levels](hyp:hK), if [two binary nuisance
records have identical encoded components at every covariate value](hyp:heq),
then [rearranging their success probabilities yields identical binary scores at
each observation](goal). -/
lemma psiBin_rearrangeP1_eq_of_binComponent_eq (M : LatentIVModel Ω X Z)
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (hK : LevelCountPos L.K) (e f : NuisanceBin L)
    (heq : ∀ c x, binComponent L e c x = binComponent L f c x) (o : Obs X Z) :
    psiBin M phi dphi L hK o (rearrangeP1 L e) =
      psiBin M phi dphi L hK o (rearrangeP1 L f) := by
  have hfun : binComponent L e = binComponent L f :=
    funext fun c => funext (heq c)
  have hrecords : restrictBinShares L e = restrictBinShares L f := by
    rw [← decodeBinComponents_binComponent L e,
      ← decodeBinComponents_binComponent L f, hfun]
  calc
    _ = psiBin M phi dphi L hK o (restrictBinShares L (rearrangeP1 L e)) :=
      (psiBin_restrictBinShares M phi dphi L hK o _).symm
    _ = psiBin M phi dphi L hK o (restrictBinShares L (rearrangeP1 L f)) := by
      rw [← rearrangeP1_restrictBinShares, ← rearrangeP1_restrictBinShares, hrecords]
    _ = _ := psiBin_restrictBinShares M phi dphi L hK o _

end Papers.TbsPrteOptimalTransport

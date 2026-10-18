module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousComponentBridge
public import Papers.TbsPrteOptimalTransport.Helpers.DMLBoundedFixedLabels
/-! Continuous nuisance records reconstructed from fixed-label training predictors.
The encoding retains every score coordinate. Auxiliary higher-set fits are
unused by the score and are normalized to zero in the reconstructed record. -/
@[expose] public section
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.unusedSimpArgs false
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

-- @node: normalizeContAuxiliaryFits
/-- For [a system of treatment levels and policy sets](hyp:L) and [a continuous nuisance record](hyp:e),
[the normalized continuous nuisance record](goal) restricts shares to their policy sets and sets the auxiliary higher-policy and higher-baseline fits to zero. -/
noncomputable def normalizeContAuxiliaryFits (L : LevelData Z X)
    (e : NuisanceCont L) : NuisanceCont L :=
  { restrictContShares L e with
    higherPolicyFit := fun _ _ => 0
    higherBaselineFit := fun _ _ => 0 }

-- @node: decodeContComponents
/-- For [a system of treatment levels and policy sets](hyp:L) and [a family of numerically indexed covariate predictors](hyp:F),
[the decoded continuous nuisance record](goal) is obtained by [choosing a reference instrument value](step:1) and
[reading the propensity, probability, share, weight, boundary, indicator, and mean coordinates from their respective codes, with both auxiliary higher-set fits set to zero](step:2). -/
noncomputable def decodeContComponents (L : LevelData Z X)
    (F : (ℕ × ℕ × ℕ × Z) → X → ℝ) : NuisanceCont L :=
  let z₀ : Z := Classical.choice inferInstance
  { prop := fun z => F (0, 0, 0, z)
    pLev := fun k => F (1, k, 0, z₀)
    piLev := fun k => F (2, k, 0, z₀)
    tauLev := fun a => F (3, a.val.1, a.val.2, z₀)
    share := fun a z => F (4, a.val.1, a.val.2, z)
    higherPolicyFit := fun _ _ => 0
    higherBaselineFit := fun _ _ => 0
    gammaFull := fun k => F (5, k, 0, z₀)
    gamma := fun a => F (6, a.val.1, a.val.2, z₀)
    gammaTail := F (7, 0, 0, z₀)
    nu := fun a => F (8, a.val.1, a.val.2, z₀)
    Mplus := fun a => F (9, a.val.1, a.val.2, z₀)
    Mminus := fun a => F (10, a.val.1, a.val.2, z₀)
    Jplus := fun a => F (11, a.val.1, a.val.2, z₀)
    Jminus := fun a => F (12, a.val.1, a.val.2, z₀)
    JfullPlus := fun k => F (13, k, 0, z₀)
    JfullMinus := fun k => F (14, k, 0, z₀) }

-- @node: decodeContComponents_contComponent
/-- [Decoding the encoded coordinates of a continuous nuisance record returns that record with shares restricted to policy sets and auxiliary higher-set fits set to zero](goal). -/
lemma decodeContComponents_contComponent (M : LatentIVModel Ω X Z)
    (L : LevelData Z X) (e : NuisanceCont L) :
    decodeContComponents L (contComponent M L e) = normalizeContAuxiliaryFits L e := by
  cases e
  unfold decodeContComponents normalizeContAuxiliaryFits restrictContShares
  dsimp only
  congr 1
  all_goals funext a
  all_goals try funext z
  all_goals try funext x
  all_goals first
    | simp [contComponent, fullValue, a.isLt]
    | simp [contComponent, positiveValue, regularValue, shareValue,
        fullValue, nuValue, boundaryValue, minusBoundaryValue, meanValue,
        minusMeanValue, minusFullValue, a.property]
  have ha := a.property
  intro hz
  omega

-- @node: contComponent_normalizeContAuxiliaryFits
/-- [Restricting shares to policy sets and zeroing auxiliary higher-set fits preserves every encoded continuous nuisance coordinate at every covariate value](goal). -/
lemma contComponent_normalizeContAuxiliaryFits (M : LatentIVModel Ω X Z)
    (L : LevelData Z X) (e : NuisanceCont L) (c : ℕ × ℕ × ℕ × Z) (x : X) :
    contComponent M L (normalizeContAuxiliaryFits L e) c x =
      contComponent M L e c x := by
  change contComponent M L (restrictContShares L e) c x = _
  exact contComponent_restrictContShares M L e c x

-- @node: psiCont_decodeContComponents_contComponent
/-- If [the number of treatment levels is positive](hyp:hK), then
[encoding and then decoding a continuous nuisance record preserves its orthogonal score at every observation](goal). -/
lemma psiCont_decodeContComponents_contComponent (M : LatentIVModel Ω X Z)
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (hK : LevelCountPos L.K) (o : Obs X Z) (e : NuisanceCont L) :
    psiCont M phi dphi L hK o (decodeContComponents L (contComponent M L e)) =
      psiCont M phi dphi L hK o e := by
  rw [decodeContComponents_contComponent]
  change psiCont M phi dphi L hK o (restrictContShares L e) = _
  exact psiCont_restrictContShares M phi dphi L hK o e

-- @node: contComponent_decodeContComponents_of_level_eq
/-- If [two systems of treatment levels and policy sets coincide](hyp:hL) and
[the predictor family equals every encoded coordinate of a nuisance record on the second system](hyp:hF), then
[decoding those predictors on the first system reproduces every encoded coordinate of that record](goal). -/
lemma contComponent_decodeContComponents_of_level_eq (M : LatentIVModel Ω X Z)
    (L L' : LevelData Z X) (hL : L' = L) (e : NuisanceCont L')
    (F : (ℕ × ℕ × ℕ × Z) → X → ℝ)
    (hF : ∀ c x, F c x = contComponent M L' e c x) (c : ℕ × ℕ × ℕ × Z) (x : X) :
    contComponent M L (decodeContComponents L F) c x = contComponent M L' e c x := by
  subst L'
  have hfun : F = contComponent M L e := funext fun c => funext (hF c)
  rw [hfun, decodeContComponents_contComponent]
  exact contComponent_normalizeContAuxiliaryFits M L e c x

-- @node: decodeContComponents_measurable
/-- If [each predictor coordinate is jointly measurable in the training outcome and covariates](hyp:hm), then
[every encoded coordinate of the decoded nuisance record is jointly measurable in those arguments](goal). -/
@[fun_prop] lemma decodeContComponents_measurable (M : LatentIVModel Ω X Z)
    {A : Type*} [MeasurableSpace A]
    (L : LevelData Z X) (F : A → (ℕ × ℕ × ℕ × Z) → X → ℝ)
    (hm : ∀ c, Measurable (fun ax : A × X => F ax.1 c ax.2))
    (c : ℕ × ℕ × ℕ × Z) :
    Measurable (fun ax : A × X =>
      contComponent M L (decodeContComponents L (F ax.1)) c ax.2) := by
  rcases c with ⟨code, k, j, z⟩
  unfold contComponent decodeContComponents
  dsimp only
  split <;> try dsimp only
  all_goals try simp only [positiveValue, regularValue, shareValue, fullValue,
    nuValue, boundaryValue, minusBoundaryValue, meanValue, minusMeanValue, minusFullValue]
  all_goals repeat' first | fun_prop | split

-- @node: psiCont_eq_of_contComponent_eq
/-- If [the number of treatment levels is positive](hyp:hK) and
[two continuous nuisance records agree in every encoded coordinate at every covariate value](hyp:heq), then
[their orthogonal scores agree at every observation](goal). -/
lemma psiCont_eq_of_contComponent_eq (M : LatentIVModel Ω X Z)
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (hK : LevelCountPos L.K) (e f : NuisanceCont L)
    (heq : ∀ c x, contComponent M L e c x = contComponent M L f c x)
    (o : Obs X Z) :
    psiCont M phi dphi L hK o e = psiCont M phi dphi L hK o f := by
  have hfun : contComponent M L e = contComponent M L f :=
    funext fun c => funext (heq c)
  rw [← psiCont_decodeContComponents_contComponent M phi dphi L hK o e,
    hfun, psiCont_decodeContComponents_contComponent]

-- @node: contDMLRegime_oracle_nuisance_records
/-- For [continuous-outcome nuisance estimates on the recovered levels](hyp:eHat), under [the finite continuous DML regime for the fitted nuisance records](hyp:hr), if
[the probability of leaving the recovery events tends to zero](hyp:hG) and
[the recovered level system equals the fixed level system on those events at sample sizes twice a positive integer](hyp:hLevels), then
[there exist nuisance records on the fixed system whose encoded coordinates are measurable from the first training split, coincide with the fitted coordinates on the recovery events, and satisfy the finite nuisance convergence rates relative to the true record](goal). -/
lemma contDMLRegime_oracle_nuisance_records
    (M : LatentIVModel Ω X Z) {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (pHat : ℕ → A → Z → X → ℝ) (phi : Z → X → ℝ → ℝ)
    (rho : ℕ → ℝ) (gap cpi : ℝ) (L : LevelData Z X) (ch : ℝ)
    (eHat : ∀ n a, NuisanceCont (recoveredData M S I₁ I₂ pHat phi rho gap n a))
    (hr : FiniteContDMLRegime M μ S I₁ I₂ pHat phi rho gap cpi L ch eHat)
    (G : ℕ → Set A)
    (hG : Tendsto (fun n => μ (G n)ᶜ) atTop (𝓝 0))
    (hLevels : ∀ n a, a ∈ G n →
      recoveredData M S I₁ I₂ pHat phi rho gap (2 * (n + 1)) a = L) :
    ∃ oracle : ℕ → A → NuisanceCont L,
      (∀ c, TrainingPredictorMeasurable M S I₁
        (fun n a => contComponent M L (oracle n a) c)) ∧
      (∀ n a, a ∈ G n → ∀ c x,
        contComponent M L (oracle (2 * (n + 1)) a) c x =
          contComponent M _ (eHat (2 * (n + 1)) a) c x) ∧
      FiniteNuisanceRates M μ (fun n a => contComponent M L (oracle n a))
        (contComponent M L (trueNuisance M L)) := by
  have hlabels : ∀ n a, a ∈ G n →
      recoveryLabels (recoveredData M S I₁ I₂ pHat phi rho gap (2 * (n + 1)) a) =
        recoveryLabels L := fun n a ha => congrArg recoveryLabels (hLevels n a ha)
  obtain ⟨F, hm, hb, heq, hrate⟩ := contDMLRegime_oracle_component_predictors
    M μ S I₁ I₂ pHat phi rho gap cpi L ch eHat hr G hG hlabels
  have heq' : ∀ n a, a ∈ G n → ∀ c x,
      contComponent M L (decodeContComponents L (F (2 * (n + 1)) a)) c x =
        contComponent M _ (eHat (2 * (n + 1)) a) c x := by
    intro n a ha c x
    exact contComponent_decodeContComponents_of_level_eq M L _ (hLevels n a ha)
      (eHat (2 * (n + 1)) a) _ (heq n a ha) c x
  refine ⟨fun n a => decodeContComponents L (F n a), ?_, heq', ?_⟩
  · intro c n
    let : MeasurableSpace A :=
      MeasurableSpace.comap (trainingView M S I₁ n) inferInstance
    exact decodeContComponents_measurable M L (F n) (fun d => hm d n) c
  · exact nuisanceRates_transfer_on_recovery M μ
      (fun n a => contComponent M _ (eHat n a))
      (fun n a => contComponent M L (decodeContComponents L (F n a)))
      (contComponent M L (trueNuisance M L)) G hG heq' hr.2.1

-- @node: psiCont_eq_of_contComponent_eq_of_level_eq
/-- If [two level systems coincide](hyp:hL), [both have positive level counts](hyp:hK,hK'), and
[their nuisance records agree in every encoded coordinate](hyp:heq), then
[the continuous orthogonal scores computed from the two systems agree at every observation](goal). -/
lemma psiCont_eq_of_contComponent_eq_of_level_eq (M : LatentIVModel Ω X Z)
    (phi dphi : Z → X → ℝ → ℝ) (L L' : LevelData Z X) (hL : L' = L)
    (hK : LevelCountPos L.K) (hK' : LevelCountPos L'.K)
    (e : NuisanceCont L) (f : NuisanceCont L')
    (heq : ∀ c x, contComponent M L e c x = contComponent M L' f c x)
    (o : Obs X Z) :
    psiCont M phi dphi L hK o e = psiCont M phi dphi L' hK' o f := by
  subst L'
  exact psiCont_eq_of_contComponent_eq M phi dphi L hK e f heq o

-- @node: fittedContScore_eq_oracle_of_component_eq
/-- For [continuous-outcome nuisance estimates on the recovered levels](hyp:eHat), if [the fixed level count is positive](hyp:hK), [the recovered level system equals the fixed system at the given sample size and training outcome](hyp:hLevels), and
[the oracle and fitted nuisance records agree in every encoded coordinate there](hyp:heq), then
[the fitted continuous score equals the score computed with the fixed levels and oracle nuisance record at every observation](goal). -/
lemma fittedContScore_eq_oracle_of_component_eq
    (M : LatentIVModel Ω X Z) {A : Type*} [MeasurableSpace A]
    {μ : Measure A} [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (pHat : ℕ → A → Z → X → ℝ) (phi dphi : Z → X → ℝ → ℝ)
    (rho : ℕ → ℝ) (gap : ℝ) (L : LevelData Z X) (hK : LevelCountPos L.K)
    (eHat : ∀ n a, NuisanceCont (recoveredData M S I₁ I₂ pHat phi rho gap n a))
    (oracle : ℕ → A → NuisanceCont L) (n : ℕ) (a : A)
    (hLevels : recoveredData M S I₁ I₂ pHat phi rho gap n a = L)
    (heq : ∀ c x, contComponent M L (oracle n a) c x =
      contComponent M _ (eHat n a) c x) (o : Obs X Z) :
    fittedContScore M S I₁ I₂ pHat phi dphi rho gap eHat n a o =
      psiCont M phi dphi L hK o (oracle n a) := by
  have hK' : LevelCountPos (recoveredData M S I₁ I₂ pHat phi rho gap n a).K := by
    rw [hLevels]
    exact hK
  simp only [fittedContScore, dif_pos hK']
  exact (psiCont_eq_of_contComponent_eq_of_level_eq M phi dphi L _ hLevels
    hK hK' (oracle n a) (eHat n a) heq o).symm

end Papers.TbsPrteOptimalTransport

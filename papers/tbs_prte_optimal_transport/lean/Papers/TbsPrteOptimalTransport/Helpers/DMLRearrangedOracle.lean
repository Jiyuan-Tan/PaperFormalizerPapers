module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLBinaryOracleClipping
public import Papers.TbsPrteOptimalTransport.Helpers.DMLScoreMeasurability
public import Papers.TbsPrteOptimalTransport.Helpers.DMLRearrangementRegularity
public import Papers.TbsPrteOptimalTransport.Helpers.DMLBinaryOracleMoments
/-! Training measurability and recovery equality for the rearranged binary oracle.
Sorting acts only on the nonboundary outcome probabilities. The resulting score
uses the same coherent sorted vector as the feasible estimation procedure. -/
public section
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v
variable {Ω : Type u} {X Z : Type v}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]
  [Fintype Z] [DecidableEq Z]

-- @node: rearrangeP1_clipping
/-- If [a binary nuisance record satisfies clipping](hyp:he), then
[clipping and sorting its positive-level success probabilities preserves
all binary clipping conditions](goal). -/
lemma rearrangeP1_clipping (L : LevelData Z X) (e : NuisanceBin L)
    (he : BinClipping L e) : BinClipping L (rearrangeP1 L e) := by
  refine ⟨he.1, ?_, he.2.2.1, he.2.2.2.1, he.2.2.2.2.1, he.2.2.2.2.2⟩
  intro k x
  exact ⟨(he.2.1 k x).1, rearrangeP1_range L e k x, (he.2.1 k x).2.2⟩

-- @node: training_measurable_rearrangeP1_components
/-- If [every encoded component of a binary nuisance estimator is measurable
from the training view and covariates](hyp:hm), then [every encoded component
remains training measurable after clipping and sorting the positive-level
success probabilities](goal). -/
lemma training_measurable_rearrangeP1_components
    (M : LatentIVModel Ω X Z) {A : Type*} [MeasurableSpace A]
    {μ : Measure A} [IsProbabilityMeasure μ] (S : ObservedSample M μ)
    (I₁ : SampleSplit A) (L : LevelData Z X) (eh : ℕ → A → NuisanceBin L)
    (hm : ∀ c, TrainingPredictorMeasurable M S I₁
      (fun n a => binComponent L (eh n a) c)) :
    ∀ c, TrainingPredictorMeasurable M S I₁
      (fun n a => binComponent L (rearrangeP1 L (eh n a)) c) := by
  intro c n
  let : MeasurableSpace A :=
    MeasurableSpace.comap (trainingView M S I₁ n) inferInstance
  change Measurable (fun ax : A × X =>
    binComponent L (rearrangeP1 L (eh n ax.1)) c ax.2)
  have hP (i : ℕ) : Measurable (fun ax : A × X =>
      min 1 (max 0 (positiveValue (eh n ax.1).P1 (i + 1) ax.2))) := by
    have hi := hm (2, i + 1, 0, Classical.choice inferInstance) n
    change Measurable (fun ax : A × X =>
      positiveValue (eh n ax.1).P1 (i + 1) ax.2) at hi
    fun_prop
  have hsort (k : ℕ) := measurable_mergeSort_getD
    ((List.range L.K).map (fun i (ax : A × X) =>
      min 1 (max 0 (positiveValue (eh n ax.1).P1 (i + 1) ax.2))))
    (by
      intro f hf
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hf
      exact hP i) (k - 1)
  rcases c with ⟨tag, k, j, z⟩
  match tag with
  | 0 => exact hm (0, k, j, z) n
  | 1 => exact hm (1, k, j, z) n
  | 2 =>
    by_cases hk : 1 ≤ k ∧ k ≤ L.K
    · simpa only [binComponent, positiveValue, dif_pos hk, rearrangeP1,
        List.map_map, Function.comp_def] using hsort k
    · simp only [binComponent, positiveValue, dif_neg hk]
      fun_prop
  | 3 => exact hm (3, k, j, z) n
  | 4 => exact hm (4, k, j, z) n
  | 5 => exact hm (5, k, j, z) n
  | 6 => exact hm (6, k, j, z) n
  | 7 => exact hm (7, k, j, z) n
  | t + 8 => exact hm (t + 8, k, j, z) n

-- @node: training_measurable_rearranged_binary_score
/-- For [a valid policy map](hyp:hphi) with [the specified derivative](hyp:hd)
and [a positive number of levels](hyp:hK), if [all encoded nuisance components
are training measurable](hyp:hm) and [every fitted record satisfies binary
clipping](hyp:hc), then [the binary score computed from the rearranged nuisance
record is measurable from the training view and the observation](goal). -/
lemma training_measurable_rearranged_binary_score
    (M : LatentIVModel Ω X Z) {A : Type*} [MeasurableSpace A]
    {μ : Measure A} [IsProbabilityMeasure μ] (S : ObservedSample M μ)
    (I₁ : SampleSplit A) (phi dphi : Z → X → ℝ → ℝ)
    (hphi : IsPolicyMap phi) (hd : PolicyDifferentiable phi dphi)
    (L : LevelData Z X) (hK : LevelCountPos L.K) (eh : ℕ → A → NuisanceBin L)
    (hm : ∀ c, TrainingPredictorMeasurable M S I₁
      (fun n a => binComponent L (eh n a) c))
    (hc : ∀ n a, BinClipping L (eh n a)) :
    TrainingPredictorMeasurable M S I₁
      (fun n a o => psiBin M phi dphi L hK o (rearrangeP1 L (eh n a))) := by
  exact training_measurable_binary_score_of_components M S I₁ phi dphi hphi hd
    L hK (fun n a => rearrangeP1 L (eh n a))
    (training_measurable_rearrangeP1_components M S I₁ L eh hm)
    (fun n a => (hc n a).1)

-- @node: binDMLRegime_rearranged_oracle_score_records
/-- For [binary nuisance records fitted on the recovered levels](hyp:eHat) and [a valid policy map](hyp:hphi) with [the specified derivative](hyp:hd)
and [a positive number of levels](hyp:hK), suppose [the fitted records satisfy
the finite binary DML regime](hyp:hr), [the recovery events have probability
tending to one](hyp:hG), and [the recovered level data equal the fixed level
data on those events at even sample sizes](hyp:hLevels). Then [there exists
a fixed-level oracle with training-measurable components, clipping, simplex
shares, clipped denominators, admissibility, and the required component rates;
its rearranged score is training measurable, its rearranged records are
admissible, and its score equals the feasible score on recovery events](goal). -/
lemma binDMLRegime_rearranged_oracle_score_records
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
    (hLevels : ∀ n a, a ∈ G n →
      recoveredData M S I₁ I₂ pHat phi rho gap (2 * (n + 1)) a = L) :
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
    binDMLRegime_regular_oracle_nuisance_records M μ S I₁ I₂ pHat phi rho gap
      cpi L ch hK eHat hr G hG hLevels
  refine ⟨oracle, hm, hc, ha, hrate, ?_, ?_, ?_⟩
  · exact training_measurable_rearranged_binary_score M S I₁ phi dphi hphi hd
      L hK oracle hm (fun n a => (hc n a).1)
  · intro n a
    exact rearrangeP1_admissible M L (oracle n a) (ha n a)
  · intro n a hna o
    exact fittedBinScore_eq_oracle_of_component_eq M S I₁ I₂ pHat phi dphi rho
      gap L hK eHat oracle _ a (hLevels n a hna) (heq n a hna) o

-- @node: rearrangeP1_clipped_denominator_lower_bounds
/-- With [a positive number of levels](hyp:hK), if [the binary nuisance
denominators satisfy clipping at the given threshold](hyp:hd) and
[the fitted shares form simplices](hyp:hs), then [all positive-level and
regular-cell denominators of the rearranged record are bounded below by half
that threshold, at every covariate value](goal). -/
lemma rearrangeP1_clipped_denominator_lower_bounds
    (L : LevelData Z X) (hK : LevelCountPos L.K) (e : NuisanceBin L)
    (cpi : ℝ) (hd : BinDenominatorsClipped L e cpi)
    (hs : BinFittedSharesSimplex L e) :
    (∀ i : PositiveIndex L.K, ∀ x, cpi / 2 ≤ (rearrangeP1 L e).piLev i x) ∧
    (∀ r : RegularIndex L, ∀ x, cpi / 2 ≤ (rearrangeP1 L e).tauLev r x) := by
  have hne := (binary_clipping_simplex_geometry L cpi hK e hd hs).2
  exact ⟨fun i x => (hd.1 i x).1, fun r x => (hd.2 r x (hne r)).1⟩

-- @node: rearranged_binary_oracle_score_and_square_memLp
/-- For [a valid policy map](hyp:hphi) with [the specified derivative](hyp:hd)
and [a bounded Lipschitz derivative](hyp:hDerivative), assume [a positive
number of levels](hyp:hK), [an admissible binary nuisance record](hyp:he),
[an almost surely binary outcome](hyp:hy), [a positive clipping threshold](hyp:hcpi),
[denominators clipped at that threshold](hyp:hden), and [simplex fitted
shares](hyp:hs). Then [the rearranged binary score and its squared deviation
from any real centering constant are both square integrable under the
population observation law](goal). -/
lemma rearranged_binary_oracle_score_and_square_memLp
    (M : LatentIVModel Ω X Z) (phi dphi : Z → X → ℝ → ℝ)
    (hphi : IsPolicyMap phi) (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hK : LevelCountPos L.K) (e : NuisanceBin L)
    (he : BinAdmissible M L e) (hy : OutcomeBinaryAE M)
    (cpi : ℝ) (hcpi : 0 < cpi)
    (hden : BinDenominatorsClipped L e cpi) (hs : BinFittedSharesSimplex L e)
    (theta : ℝ) :
    MemLp (fun o => psiBin M phi dphi L hK o (rearrangeP1 L e)) 2
      (observationLaw M) ∧
    MemLp (fun o => (psiBin M phi dphi L hK o (rearrangeP1 L e) - theta)^2) 2
      (observationLaw M) := by
  have ha := rearrangeP1_admissible M L e he
  have hl := rearrangeP1_clipped_denominator_lower_bounds L hK e cpi hden hs
  have hpi (i : PositiveIndex L.K) :
      ∀ᵐ x ∂xLaw M, cpi / 2 ≤ (rearrangeP1 L e).piLev i x :=
    Eventually.of_forall (hl.1 i)
  have htau (r : RegularIndex L) :
      ∀ᵐ x ∂xLaw M, cpi / 2 ≤ (rearrangeP1 L e).tauLev r x :=
    Eventually.of_forall (hl.2 r)
  exact ⟨fitted_binary_score_memLp M phi dphi hphi hd hDerivative L hK
      (rearrangeP1 L e) ha hy (cpi / 2) (by positivity) hpi htau,
    fitted_binary_centered_square_memLp M phi dphi hphi hd hDerivative L hK
      (rearrangeP1 L e) ha hy (cpi / 2) (by positivity) hpi htau theta⟩

end Papers.TbsPrteOptimalTransport

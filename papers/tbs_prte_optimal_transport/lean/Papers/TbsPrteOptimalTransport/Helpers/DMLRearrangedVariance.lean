module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLRearrangedOracle
public import Papers.TbsPrteOptimalTransport.Helpers.DMLBinaryTrainingVariance
/-! Component rates for the coherent sorted binary oracle and its variance.
The aggregate sorting contraction preserves the outcome-probability rates.
The admissible support convention removes the encoded share restriction. -/
public section
set_option linter.style.openClassical false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

universe u v
variable {Ω : Type u} {X Z : Type v}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]
  [Fintype Z] [DecidableEq Z]

-- @node: nuisanceRates_congr_ae_sections
/-- If [two fitted component families agree almost everywhere in covariates
for each sample size, realization, and component](hyp:hf), [their target
components agree almost everywhere](hyp:ht), and [the first family satisfies
the required nuisance rates toward its target](hyp:hr), then [the second
family satisfies the same rates toward its target](goal). -/
lemma nuisanceRates_congr_ae_sections
    (M : LatentIVModel Ω X Z) {A C : Type*} [MeasurableSpace A]
    (μ : Measure A) (f g : ℕ → A → C → X → ℝ) (t s : C → X → ℝ)
    (hf : ∀ n a c, f n a c =ᵐ[xLaw M] g n a c)
    (ht : ∀ c, t c =ᵐ[xLaw M] s c)
    (hr : FiniteNuisanceRates M μ f t) : FiniteNuisanceRates M μ g s := by
  have heq (n : ℕ) (a : A) (c : C) :
      finiteL2Error M (f n a c) (t c) = finiteL2Error M (g n a c) (s c) := by
    unfold finiteL2Error
    congr 1
    apply integral_congr_ae
    filter_upwards [hf n a c, ht c] with x hx hy
    rw [hx, hy]
  intro c
  simpa only [heq] using hr c

-- @node: binary_component_rates_admissible_shares
/-- If [all fitted binary nuisance records are admissible](hyp:hh),
[the target record is admissible](hyp:h0), and [the encoded components
satisfy the required nuisance rates toward the target components](hyp:hr),
then [the unrestricted instrument-share functions satisfy those rates for
every share cell](goal). -/
lemma binary_component_rates_admissible_shares
    (M : LatentIVModel Ω X Z) {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (L : LevelData Z X) (eh : ℕ → A → NuisanceBin L)
    (e0 : NuisanceBin L) (hh : ∀ n a, BinAdmissible M L (eh n a))
    (h0 : BinAdmissible M L e0)
    (hr : FiniteNuisanceRates M μ (fun n a => binComponent L (eh n a))
      (binComponent L e0)) :
    ∀ t, FiniteNuisanceRates M μ (fun n a => (eh n a).share t) (e0.share t) := by
  have hs := (binary_component_rates_to_oracle_rates M μ L eh e0 hr).2.2.2.2.2.1
  intro t
  apply nuisanceRates_congr_ae_sections M μ _ _ _ _ _ _ (hs t)
  · intro n a z
    exact (restrictBinShares_eq_of_admissible M L (eh n a) (hh n a)).mono
      (fun x hx => hx t z)
  · intro z
    exact (restrictBinShares_eq_of_admissible M L e0 h0).mono
      (fun x hx => hx t z)

-- @node: binary_component_rates_rearranged_oracle_rates
/-- If [all fitted binary records are admissible](hyp:hh), [the target record
is admissible](hyp:h0), [the target success probabilities are nondecreasing
across positive levels almost everywhere](hyp:hmono), and [the encoded
components satisfy the required nuisance rates](hyp:hr), then [the rearranged
records satisfy those rates for the propensity, level propensities, success
probabilities, level and regular-cell denominators, every instrument-share
cell, and the full, regular, and tail gamma components](goal). -/
lemma binary_component_rates_rearranged_oracle_rates
    (M : LatentIVModel Ω X Z) {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (L : LevelData Z X) (eh : ℕ → A → NuisanceBin L)
    (e0 : NuisanceBin L) (hh : ∀ n a, BinAdmissible M L (eh n a))
    (h0 : BinAdmissible M L e0)
    (hmono : ∀ᵐ x ∂xLaw M, ∀ i j : PositiveIndex L.K,
      i.val ≤ j.val → e0.P1 i x ≤ e0.P1 j x)
    (hr : FiniteNuisanceRates M μ (fun n a => binComponent L (eh n a))
      (binComponent L e0)) :
    FiniteNuisanceRates M μ (fun n a => (rearrangeP1 L (eh n a)).prop) e0.prop ∧
    FiniteNuisanceRates M μ (fun n a => (rearrangeP1 L (eh n a)).pLev) e0.pLev ∧
    FiniteNuisanceRates M μ (fun n a => (rearrangeP1 L (eh n a)).P1) e0.P1 ∧
    FiniteNuisanceRates M μ (fun n a => (rearrangeP1 L (eh n a)).piLev) e0.piLev ∧
    FiniteNuisanceRates M μ (fun n a => (rearrangeP1 L (eh n a)).tauLev) e0.tauLev ∧
    (∀ t, FiniteNuisanceRates M μ (fun n a => (rearrangeP1 L (eh n a)).share t)
      (e0.share t)) ∧
    FiniteNuisanceRates M μ (fun n a => (rearrangeP1 L (eh n a)).gammaFull)
      e0.gammaFull ∧
    FiniteNuisanceRates M μ (fun n a => (rearrangeP1 L (eh n a)).gamma) e0.gamma ∧
    FiniteNuisanceRates M μ (fun n a (_ : Unit) => (rearrangeP1 L (eh n a)).gammaTail)
      (fun _ => e0.gammaTail) := by
  obtain ⟨hp, hl, hP, hpi, ht, hs, hf, hg, htail⟩ :=
    binary_component_rates_to_oracle_rates M μ L eh e0 hr
  exact ⟨hp, hl, nuisanceRates_rearrangeP1 M μ L eh e0 hh h0 hmono hP,
    hpi, ht, binary_component_rates_admissible_shares M μ L eh e0 hh h0 hr,
    hf, hg, htail⟩

-- @node: binary_encoded_rearranged_mean_variance_consistent
/-- Under [an equal half split independent of the sample](hyp:hSplit), take
[a valid policy map](hyp:hphi) with [the specified derivative](hyp:hd) and
[a bounded Lipschitz derivative](hyp:hDerivative). Assume [the model's
structural conditions](hyp:hStruct), [known outcome endpoints](hyp:hEndpoints),
[a finite instrument reduction](hyp:hFinite), [an almost surely binary
outcome](hyp:hy), [a positive number of levels](hyp:hK), [measurable level
propensities](hyp:hlev), [policy-invariant level ordering](hyp:hOrder),
[policy overlap](hyp:hov), [a baseline overlap witness](hyp:hbase),
[admissibility of the true nuisance record](hyp:he0), [admissibility of every
fitted record](hyp:heh), [a positive denominator bound](hyp:hc), [a positive
separation bound](hyp:hsep), [the denominator bound for all rearranged
positive-level denominators almost everywhere](hyp:hpi), [the same bound
for all rearranged regular-cell denominators almost everywhere](hyp:htau),
[the required encoded-component nuisance rates](hyp:hr), [almost everywhere
nondecreasing true success probabilities across positive levels](hyp:hmono),
[uniform separation of adjacent pooled quantities and of each residual
level propensity from both adjacent pooled quantities](hyp:hgap), and
[training measurability of the rearranged score minus the true score](hyp:hm).
Then [along increasing even sample sizes the evaluation mean of the
rearranged score converges in probability to the discrete policy target,
and its empirical variance converges in probability to the population
variance of the true score centered at that target](goal). -/
lemma binary_encoded_rearranged_mean_variance_consistent
    (M : LatentIVModel Ω X Z)
    {A : Type*} [MeasurableSpace A] (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (hStruct : StructuralAssumptions M) (hEndpoints : OutcomeEndpointsKnown M)
    (hFinite : InstrumentFiniteReduction Z) (hy : OutcomeBinaryAE M)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hlev : ∀ k, Measurable (L.pLev k))
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : PolicyOverlap M L cpi)
    (hbase : BaselineOverlapWitness M L cpi)
    (he0 : BinAdmissible M L (eta0Bin M L)) (eh : ℕ → A → NuisanceBin L)
    (heh : ∀ n a, BinAdmissible M L (eh n a))
    (c sep : ℝ) (hc : 0 < c) (hsep : 0 < sep)
    (hpi : ∀ n a i, ∀ᵐ x ∂xLaw M, c ≤ (rearrangeP1 L (eh n a)).piLev i x)
    (htau : ∀ n a t, ∀ᵐ x ∂xLaw M, c ≤ (rearrangeP1 L (eh n a)).tauLev t x)
    (hr : FiniteNuisanceRates M μ (fun n a => binComponent L (eh n a))
      (binComponent L (eta0Bin M L)))
    (hmono : ∀ᵐ x ∂xLaw M, ∀ i j : PositiveIndex L.K,
      i.val ≤ j.val → (eta0Bin M L).P1 i x ≤ (eta0Bin M L).P1 j x)
    (hgap : ∀ k ∈ Finset.range L.K, ∀ j ∈ Finset.Icc 1 (L.l k), ∀ᵐ x ∂xLaw M,
      sep ≤ pooledQBin phi L (eta0Bin M L) k j x -
        pooledQBin phi L (eta0Bin M L) k (j - 1) x ∧
      sep ≤ |positiveValue (eta0Bin M L).pLev (k + 1) x -
        binFullJ L (eta0Bin M L) k x -
        pooledQBin phi L (eta0Bin M L) k (j - 1) x| ∧
      sep ≤ |positiveValue (eta0Bin M L).pLev (k + 1) x -
        binFullJ L (eta0Bin M L) k x -
        pooledQBin phi L (eta0Bin M L) k j x|)
    (hm : TrainingPredictorMeasurable M S I₁ (fun n a o =>
      psiBin M phi dphi L hK o (rearrangeP1 L (eh n a)) -
        psiBin M phi dphi L hK o (eta0Bin M L))) :
    let score := fun n a o => psiBin M phi dphi L hK o (rearrangeP1 L (eh n a))
    let truth := fun o => psiBin M phi dphi L hK o (eta0Bin M L)
    let theta := discreteTarget M false L (policyProp phi M.prop)
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => dmlRV M S I₂ score (2 * (n + 1)) a - theta)
      atTop (fun _ _ => 0) ∧
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => varianceRV M S I₂ score (2 * (n + 1)) a) atTop
      (fun _ _ => populationVariance M truth theta) := by
  obtain ⟨hp, hl, hP, hpi', ht, hs, hf, hg, htail⟩ :=
    binary_component_rates_rearranged_oracle_rates M μ L eh (eta0Bin M L)
      heh he0 hmono hr
  exact nuisanceRates_training_binary_oracle_mean_variance_consistent M μ S I₁ I₂
    hSplit phi dphi hphi hd hDerivative hStruct hEndpoints hFinite hy L hK
    hlev hOrder cpi hov hbase he0 (fun n a => rearrangeP1 L (eh n a))
    (fun n a => rearrangeP1_admissible M L (eh n a) (heh n a))
    c sep hc hsep hpi htau hp hl hP hpi' hs ht hg hf htail hgap hm

-- @node: binary_encoded_rearranged_mean_variance_on_recovery
/-- Under [an equal half split independent of the sample](hyp:hSplit), take
[a valid policy map](hyp:hphi) with [the specified derivative](hyp:hd) and
[a bounded Lipschitz derivative](hyp:hDerivative). Assume [the structural
model conditions](hyp:hStruct), [known outcome endpoints](hyp:hEndpoints),
[a finite instrument reduction](hyp:hFinite), [an almost surely binary
outcome](hyp:hy), [a positive number of levels](hyp:hK), [measurable level
propensities](hyp:hlev), [policy-invariant level ordering](hyp:hOrder),
[policy overlap](hyp:hov), [a baseline overlap witness](hyp:hbase),
[an admissible true nuisance record](hyp:he0), [admissible fitted records](hyp:heh),
[a positive denominator bound](hyp:hc), [a positive separation bound](hyp:hsep),
[this denominator bound for the rearranged positive-level denominators
almost everywhere](hyp:hpi), [the same bound for the rearranged regular-cell
denominators almost everywhere](hyp:htau), [the required encoded-component
nuisance rates](hyp:hr), [almost everywhere nondecreasing true success
probabilities across positive levels](hyp:hmono), [uniform separation of
adjacent pooled quantities and of each residual level propensity from both
adjacent pooled quantities](hyp:hgap), and [training measurability of the
rearranged score minus the true score](hyp:hm). If [the recovery events have
probability tending to one](hyp:hG) and [the feasible score agrees with the
rearranged score on every evaluation record on those events at even sample
sizes](hyp:heq), then [the feasible evaluation mean converges in probability
to the discrete policy target and its empirical variance converges in
probability to the population variance of the true score centered at that
target, along increasing even sample sizes](goal). -/
lemma binary_encoded_rearranged_mean_variance_on_recovery
    (M : LatentIVModel Ω X Z)
    {A : Type*} [MeasurableSpace A] (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (hStruct : StructuralAssumptions M) (hEndpoints : OutcomeEndpointsKnown M)
    (hFinite : InstrumentFiniteReduction Z) (hy : OutcomeBinaryAE M)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hlev : ∀ k, Measurable (L.pLev k))
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : PolicyOverlap M L cpi)
    (hbase : BaselineOverlapWitness M L cpi)
    (he0 : BinAdmissible M L (eta0Bin M L)) (eh : ℕ → A → NuisanceBin L)
    (heh : ∀ n a, BinAdmissible M L (eh n a))
    (c sep : ℝ) (hc : 0 < c) (hsep : 0 < sep)
    (hpi : ∀ n a i, ∀ᵐ x ∂xLaw M, c ≤ (rearrangeP1 L (eh n a)).piLev i x)
    (htau : ∀ n a t, ∀ᵐ x ∂xLaw M, c ≤ (rearrangeP1 L (eh n a)).tauLev t x)
    (hr : FiniteNuisanceRates M μ (fun n a => binComponent L (eh n a))
      (binComponent L (eta0Bin M L)))
    (hmono : ∀ᵐ x ∂xLaw M, ∀ i j : PositiveIndex L.K,
      i.val ≤ j.val → (eta0Bin M L).P1 i x ≤ (eta0Bin M L).P1 j x)
    (hgap : ∀ k ∈ Finset.range L.K, ∀ j ∈ Finset.Icc 1 (L.l k), ∀ᵐ x ∂xLaw M,
      sep ≤ pooledQBin phi L (eta0Bin M L) k j x -
        pooledQBin phi L (eta0Bin M L) k (j - 1) x ∧
      sep ≤ |positiveValue (eta0Bin M L).pLev (k + 1) x -
        binFullJ L (eta0Bin M L) k x -
        pooledQBin phi L (eta0Bin M L) k (j - 1) x| ∧
      sep ≤ |positiveValue (eta0Bin M L).pLev (k + 1) x -
        binFullJ L (eta0Bin M L) k x -
        pooledQBin phi L (eta0Bin M L) k j x|)
    (hm : TrainingPredictorMeasurable M S I₁ (fun n a o =>
      psiBin M phi dphi L hK o (rearrangeP1 L (eh n a)) -
        psiBin M phi dphi L hK o (eta0Bin M L)))
    (feasible : ℕ → A → Obs X Z → ℝ) (G : ℕ → Set A)
    (hG : Tendsto (fun n => μ (G n)ᶜ) atTop (𝓝 0))
    (heq : ∀ n a, a ∈ G n → ∀ i ∈ I₂ (2 * (n + 1)) a,
      feasible (2 * (n + 1)) a (S.Z i a) =
        psiBin M phi dphi L hK (S.Z i a)
          (rearrangeP1 L (eh (2 * (n + 1)) a))) :
    let score := fun n a o => psiBin M phi dphi L hK o (rearrangeP1 L (eh n a))
    let truth := fun o => psiBin M phi dphi L hK o (eta0Bin M L)
    let theta := discreteTarget M false L (policyProp phi M.prop)
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => dmlRV M S I₂ feasible (2 * (n + 1)) a - theta)
      atTop (fun _ _ => 0) ∧
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => varianceRV M S I₂ feasible (2 * (n + 1)) a) atTop
      (fun _ _ => populationVariance M truth theta) := by
  have ho := binary_encoded_rearranged_mean_variance_consistent M μ S I₁ I₂
    hSplit phi dphi hphi hd hDerivative hStruct hEndpoints hFinite hy L hK
    hlev hOrder cpi hov hbase he0 eh heh c sep hc hsep hpi htau hr hmono hgap hm
  dsimp only at ho ⊢
  exact dml_mean_variance_transfer_on_recovery M S I₂ feasible
    (fun n a o => psiBin M phi dphi L hK o (rearrangeP1 L (eh n a)))
    (fun n => 2 * (n + 1)) G (discreteTarget M false L (policyProp phi M.prop))
    (populationVariance M (fun o => psiBin M phi dphi L hK o (eta0Bin M L))
      (discreteTarget M false L (policyProp phi M.prop))) hG heq ho.1 ho.2

end Papers.TbsPrteOptimalTransport

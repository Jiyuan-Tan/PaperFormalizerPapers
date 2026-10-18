module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLIntegrableEvaluationLLN
public import Papers.TbsPrteOptimalTransport.Helpers.DMLOracleNormality
public import Papers.TbsPrteOptimalTransport.Helpers.DMLBinaryOracleMoments
/-! Binary oracle mean and variance consistency before normality.
Componentwise nuisance convergence supplies population squared score convergence;
conditional Markov transfers it to the evaluation sample. The integrable oracle
LLN and empirical score comparison then give both consistency conclusions. -/
public section
set_option linter.style.openClassical false

set_option linter.style.longLine false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: nuisanceRates_binary_oracle_mean_variance_consistent
/-- Under [equal training and evaluation halves](hyp:hSplit), assume [a valid
policy map](hyp:hphi), [its specified derivative](hyp:hd), [a bounded Lipschitz
derivative](hyp:hDerivative), [the structural model assumptions](hyp:hStruct),
[known outcome endpoints](hyp:hEndpoints), [finite instrument reduction](hyp:hFinite),
[binary outcomes almost surely](hyp:hy), [a positive number of levels](hyp:hK),
[measurable level propensities](hyp:hlev), [policy-invariant level ordering](hyp:hOrder),
[policy overlap](hyp:hov), [baseline overlap](hyp:hbase), [admissible population
nuisances](hyp:he0), and [admissible fitted nuisances](hyp:heh). If [the denominator
bound is positive](hyp:hc), [the separation margin is positive](hyp:hsep),
[fitted assignment probabilities are bounded below almost everywhere](hyp:hpi),
[fitted regular-cell probabilities are bounded below almost everywhere](hyp:htau),
[instrument propensities satisfy quarter-rate control](hyp:hrp),
[level propensities satisfy quarter-rate control](hyp:hrlev),
[success regressions satisfy quarter-rate control](hyp:hrP),
[assignment probabilities satisfy quarter-rate control](hyp:hrpi),
[all regular cell shares satisfy quarter-rate control](hyp:hrs),
[regular-cell probabilities satisfy quarter-rate control](hyp:hrt),
[regular weights satisfy quarter-rate control](hyp:hrg),
[full-cell weights satisfy quarter-rate control](hyp:hrfull),
[the tail weight satisfies quarter-rate control](hyp:hrtail), [population pooled
thresholds are separated from each other and the boundary](hyp:hgap), and [the
score error factors through the training view](hyp:hscore) via
[a sample-size-indexed function of the training view and a new observation](hyp:f) with [measurable
factors](hyp:hf) having [finite second moments on every evaluation row](hyp:hfit),
then [the held-out binary score mean converges in probability to the discrete
target and its empirical variance converges to the population score variance](goal). -/
lemma nuisanceRates_binary_oracle_mean_variance_consistent
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
    (hpi : ∀ n a i, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).piLev i x)
    (htau : ∀ n a t, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).tauLev t x)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) M.prop)
    (hrlev : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) (eta0Bin M L).pLev)
    (hrP : FiniteNuisanceRates M μ (fun n a => (eh n a).P1) (eta0Bin M L).P1)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) (eta0Bin M L).piLev)
    (hrs : ∀ t, FiniteNuisanceRates M μ (fun n a => (eh n a).share t) ((eta0Bin M L).share t))
    (hrt : FiniteNuisanceRates M μ (fun n a => (eh n a).tauLev) (eta0Bin M L).tauLev)
    (hrg : FiniteNuisanceRates M μ (fun n a => (eh n a).gamma) (eta0Bin M L).gamma)
    (hrfull : FiniteNuisanceRates M μ (fun n a => (eh n a).gammaFull) (eta0Bin M L).gammaFull)
    (hrtail : FiniteNuisanceRates M μ (fun n a (_ : Unit) => (eh n a).gammaTail)
      (fun _ => (eta0Bin M L).gammaTail))
    (hgap : ∀ k ∈ Finset.range L.K, ∀ j ∈ Finset.Icc 1 (L.l k), ∀ᵐ x ∂xLaw M,
      sep ≤ pooledQBin phi L (eta0Bin M L) k j x -
        pooledQBin phi L (eta0Bin M L) k (j - 1) x ∧
      sep ≤ |positiveValue (eta0Bin M L).pLev (k + 1) x -
        binFullJ L (eta0Bin M L) k x -
        pooledQBin phi L (eta0Bin M L) k (j - 1) x| ∧
      sep ≤ |positiveValue (eta0Bin M L).pLev (k + 1) x -
        binFullJ L (eta0Bin M L) k x -
        pooledQBin phi L (eta0Bin M L) k j x|)
    (f : ∀ n, (Finset ℕ × (Fin (2 * (n + 1)) → Unit ⊕ Obs X Z)) × Obs X Z → ℝ)
    (hscore : ∀ n a o,
      psiBin M phi dphi L hK o (eh (2 * (n + 1)) a) -
        psiBin M phi dphi L hK o (eta0Bin M L) =
      f n (trainingView M S I₁ (2 * (n + 1)) a, o))
    (hf : ∀ n, Measurable (f n))
    (hfit : ∀ n i, MemLp (fun a => f n
      (trainingView M S I₁ (2 * (n + 1)) a,
        S.Z (dmlEvaluationIndex n (I₂ (2 * (n + 1)) a) i) a)) 2 μ) :
    let score := fun n a o => psiBin M phi dphi L hK o (eh n a)
    let truth := fun o => psiBin M phi dphi L hK o (eta0Bin M L)
    let theta := discreteTarget M false L (policyProp phi M.prop)
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => dmlRV M S I₂ score (2 * (n + 1)) a - theta)
      atTop (fun _ _ => 0) ∧
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => varianceRV M S I₂ score (2 * (n + 1)) a) atTop
      (fun _ _ => populationVariance M truth theta) := by
  have : IsProbabilityMeasure (observationLaw M) := by
    rw [← S.map_eq 0]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  have hpi0 (i : PositiveIndex L.K) :
      ∀ᵐ x ∂xLaw M, cpi ≤ (eta0Bin M L).piLev i x :=
    Eventually.of_forall (fun x => hbase.2 x i i.property.1 i.property.2)
  have htau0 (r : RegularIndex L) :
      ∀ᵐ x ∂xLaw M, cpi ≤ (eta0Bin M L).tauLev r x :=
    Eventually.of_forall (fun x => hov.2 x r.val.1 r.val.2 r.property.1 r.property.2.1 r.property.2.2
      (ordered_policy_level_nonempty M _ L hOrder _ _ r.property.1
        r.property.2.1 r.property.2.2))
  have hc' : 0 < min c cpi := lt_min hc hbase.1
  have hpiboth (n : ℕ) (a : A) (i : PositiveIndex L.K) :
      ∀ᵐ x ∂xLaw M, min c cpi ≤ (eta0Bin M L).piLev i x ∧
        min c cpi ≤ (eh n a).piLev i x := by
    filter_upwards [hpi0 i, hpi n a i] with x h0 hh
    exact ⟨(min_le_right _ _).trans h0, (min_le_left _ _).trans hh⟩
  have htauboth (n : ℕ) (a : A) (r : RegularIndex L) :
      ∀ᵐ x ∂xLaw M, min c cpi ≤ (eta0Bin M L).tauLev r x ∧
        min c cpi ≤ (eh n a).tauLev r x := by
    filter_upwards [htau0 r, htau n a r] with x h0 hh
    exact ⟨(min_le_right _ _).trans h0, (min_le_left _ _).trans hh⟩
  have hr := nuisanceRates_binary_score_sq_tendsto_probability_zero M μ phi dphi
    hphi hd hDerivative L hK (eta0Bin M L) eh he0 heh hy (min c cpi) hc'
    hpiboth htauboth hrp hrlev hrP hrpi hrt hrs hrg hrfull hrtail sep hsep
    (fun k hk j hj => hgap k (Finset.mem_range.mpr hk) j (Finset.mem_Icc.mpr hj))
  have hdphi := policy_derivative_graph_measurable phi dphi hphi hd M.prop
    hStruct.2.2.2.1.2.1 M.rangeProp
  have hmean := (population_binary_score_mean_eq_target M hStruct hEndpoints hFinite
    phi dphi hphi hdphi hDerivative L hK hOrder hlev cpi hbase hov hy he0).2
  have hLp := fitted_binary_score_memLp M phi dphi hphi hd hDerivative L hK
    (eta0Bin M L) he0 hy cpi hbase.1 hpi0 htau0
  have hrate : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o, f n (trainingView M S I₁ (2 * (n + 1)) a, o) ^ 2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
    simpa only [← hscore] using hr
  have hE := equalHalfSplit_empirical_fitted_score_energy M μ S I₁ I₂
    hSplit f hf hfit hrate
  simp only [← hscore] at hE
  dsimp only
  exact ⟨equalHalfSplit_dmlRV_consistent_of_empirical_score_error M μ S I₁ I₂
      hSplit _ _ (hLp.integrable (by norm_num)) _ hmean hE,
    equalHalfSplit_varianceRV_consistent_of_empirical_score_error_memLp M μ S I₁ I₂
      hSplit _ _ hLp _ hmean hE⟩

end Papers.TbsPrteOptimalTransport

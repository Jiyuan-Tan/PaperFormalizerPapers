module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLBranchProductBridge
/-! Binary total score convergence under the paper's population margins.
Finite sums combine full, fractional, and tail scores. The structural-zero
branch uses outcome separation without policy spacing from zero. -/
public section
set_option linter.style.openClassical false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
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

-- @node: nuisanceRates_regular_score_block_sq_tendsto_probability_zero_of_branch_convergence
/-- For [a valid policy](hyp:hphi) with [the specified derivative](hyp:hd)
that is [uniformly bounded and Lipschitz](hyp:hDerivative), suppose [reference](hyp:he0)
and [fitted nuisances](hyp:heh) are admissible, [outcomes are binary almost surely](hyp:hy),
[c is positive](hyp:hc), and [reference and fitted baseline assignment masses](hyp:hpi)
and [reference and fitted policy masses](hyp:htau) are almost surely at least c.
Assume quarter-rate conditions for [propensities](hyp:hrp), [treatment-level
propensities](hyp:hrlev), [treated-success probabilities](hyp:hrP), [baseline
assignment masses](hyp:hrpi), [policy masses](hyp:hrt), [pooling shares](hyp:hrs),
and [regular regression weights](hyp:hrg), together with [convergence to zero
in probability of the integrated sum of squared errors in the activation,
boundary, and dominance indicators at every interior regular level](hyp:hbranch).
Then [the integrated squared error of the entire regular product score block
converges to zero in probability along sample sizes twice n plus two](goal). -/
lemma nuisanceRates_regular_score_block_sq_tendsto_probability_zero_of_branch_convergence
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e0 : NuisanceBin L) (eh : ℕ → A → NuisanceBin L)
    (he0 : BinAdmissible M L e0) (heh : ∀ n a, BinAdmissible M L (eh n a))
    (hy : OutcomeBinaryAE M) (c : ℝ) (hc : 0 < c)
    (hpi : ∀ n a (i : PositiveIndex L.K), ∀ᵐ x ∂xLaw M,
      c ≤ e0.piLev i x ∧ c ≤ (eh n a).piLev i x)
    (htau : ∀ n a (r : RegularIndex L), ∀ᵐ x ∂xLaw M,
      c ≤ e0.tauLev r x ∧ c ≤ (eh n a).tauLev r x)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) e0.prop)
    (hrlev : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrP : FiniteNuisanceRates M μ (fun n a => (eh n a).P1) e0.P1)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) e0.piLev)
    (hrt : FiniteNuisanceRates M μ (fun n a => (eh n a).tauLev) e0.tauLev)
    (hrs : ∀ r : RegularIndex L,
      FiniteNuisanceRates M μ (fun n a => (eh n a).share r) (e0.share r))
    (hrg : FiniteNuisanceRates M μ (fun n a => (eh n a).gamma) e0.gamma)
    (hbranch : ∀ k, k < L.K → ∀ j, 1 ≤ j ∧ j ≤ L.l k →
      Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o : Obs X Z,
        (Iact phi L (eh (2*(n+1)) a) k j o.1 - Iact phi L e0 k j o.1)^2 +
        (Dbd phi L (eh (2*(n+1)) a) k j o.1 - Dbd phi L e0 k j o.1)^2 +
        (Edom phi L (eh (2*(n+1)) a) k j o.1 - Edom phi L e0 k j o.1)^2
        ∂observationLaw M) atTop (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o : Obs X Z,
        ((∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
            psiProdBin phi dphi L (eh (2*(n+1)) a) k j o) -
          ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
            psiProdBin phi dphi L e0 k j o)^2 ∂observationLaw M)
      atTop (fun _ _ => 0) := by
  let F := fun (k j n : ℕ) (a : A) (o : Obs X Z) =>
    psiProdBin phi dphi L (eh (2*(n+1)) a) k j o - psiProdBin phi dphi L e0 k j o
  have hF (k j n : ℕ) (a : A) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k) :
      MemLp (F k j n a) 2 (observationLaw M) :=
    (fitted_regular_product_memLp M phi dphi hphi hd hDerivative L _ (heh _ a) hy c hc
      (fun i => (hpi _ a i).mono (fun _ hx => hx.2))
      (fun r => (htau _ a r).mono (fun _ hx => hx.2)) k j hk hj).sub
      (fitted_regular_product_memLp M phi dphi hphi hd hDerivative L e0 he0 hy c hc
        (fun i => (hpi (2*(n+1)) a i).mono (fun _ hx => hx.1))
        (fun r => (htau (2*(n+1)) a r).mono (fun _ hx => hx.1)) k j hk hj)
  have hs := dml_finset_sum_sq_tendsto_probability_zero μ (observationLaw M)
    (Finset.range L.K) (fun k n a o => ∑ j ∈ Finset.Icc 1 (L.l k), F k j n a o)
    (fun k hk n a => memLp_finsetSum _
      (fun j hj => hF k j n a (Finset.mem_range.mp hk) (Finset.mem_Icc.mp hj))) (by
      intro k hk
      apply dml_finset_sum_sq_tendsto_probability_zero μ (observationLaw M)
        (Finset.Icc 1 (L.l k)) (F k)
        (fun j hj n a => hF k j n a (Finset.mem_range.mp hk) (Finset.mem_Icc.mp hj))
      intro j hj
      exact nuisanceRates_regular_product_sq_tendsto_probability_zero_of_branch_convergence M μ phi dphi hphi hd
        hDerivative L e0 eh he0 heh hy c hc hpi htau hrp hrlev hrP hrpi hrt hrs hrg
        k j (Finset.mem_range.mp hk) (Finset.mem_Icc.mp hj) (hbranch k (Finset.mem_range.mp hk) j (Finset.mem_Icc.mp hj)))
  simpa only [F, Finset.sum_sub_distrib] using hs

-- @node: nuisanceRates_binary_score_sq_tendsto_probability_zero_of_branch_convergence
/-- Assume [a valid policy](hyp:hphi) with [the specified derivative](hyp:hd)
that is [uniformly bounded and Lipschitz](hyp:hDerivative), [a positive number
of treatment levels](hyp:hK), [admissible reference](hyp:he0) and [fitted
nuisances](hyp:heh), [almost surely binary outcomes](hyp:hy), [positive c](hyp:hc),
and [reference and fitted baseline assignment masses](hyp:hpi) and [policy
masses](hyp:htau) almost surely at least c. If quarter-rate conditions hold
for [propensities](hyp:hrp), [treatment-level propensities](hyp:hrlev),
[treated-success probabilities](hyp:hrP), [baseline assignment masses](hyp:hrpi),
[policy masses](hyp:hrt), [pooling shares](hyp:hrs), [regular regression weights](hyp:hrg),
[full-level regression weights](hyp:hrfull), and [the tail regression weight](hyp:hrtail),
and [the integrated sum of squared errors in the three branch indicators tends
to zero in probability at every interior regular level](hyp:hbranch), then
[the integrated squared error of the complete binary score tends to zero in
probability along sample sizes twice n plus two](goal). -/
lemma nuisanceRates_binary_score_sq_tendsto_probability_zero_of_branch_convergence
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (e0 : NuisanceBin L) (eh : ℕ → A → NuisanceBin L)
    (he0 : BinAdmissible M L e0) (heh : ∀ n a, BinAdmissible M L (eh n a))
    (hy : OutcomeBinaryAE M) (c : ℝ) (hc : 0 < c)
    (hpi : ∀ n a (i : PositiveIndex L.K), ∀ᵐ x ∂xLaw M,
      c ≤ e0.piLev i x ∧ c ≤ (eh n a).piLev i x)
    (htau : ∀ n a (r : RegularIndex L), ∀ᵐ x ∂xLaw M,
      c ≤ e0.tauLev r x ∧ c ≤ (eh n a).tauLev r x)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) e0.prop)
    (hrlev : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrP : FiniteNuisanceRates M μ (fun n a => (eh n a).P1) e0.P1)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) e0.piLev)
    (hrt : FiniteNuisanceRates M μ (fun n a => (eh n a).tauLev) e0.tauLev)
    (hrs : ∀ r : RegularIndex L,
      FiniteNuisanceRates M μ (fun n a => (eh n a).share r) (e0.share r))
    (hrg : FiniteNuisanceRates M μ (fun n a => (eh n a).gamma) e0.gamma)
    (hrfull : FiniteNuisanceRates M μ (fun n a => (eh n a).gammaFull) e0.gammaFull)
    (hrtail : FiniteNuisanceRates M μ (fun n a (_ : Unit) => (eh n a).gammaTail)
      (fun _ => e0.gammaTail))
    (hbranch : ∀ k, k < L.K → ∀ j, 1 ≤ j ∧ j ≤ L.l k →
      Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o : Obs X Z,
        (Iact phi L (eh (2*(n+1)) a) k j o.1 - Iact phi L e0 k j o.1)^2 +
        (Dbd phi L (eh (2*(n+1)) a) k j o.1 - Dbd phi L e0 k j o.1)^2 +
        (Edom phi L (eh (2*(n+1)) a) k j o.1 - Edom phi L e0 k j o.1)^2
        ∂observationLaw M) atTop (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o : Obs X Z,
        (psiBin M phi dphi L hK o (eh (2*(n+1)) a) -
          psiBin M phi dphi L hK o e0)^2 ∂observationLaw M)
      atTop (fun _ _ => 0) := by
  let F := fun (e : NuisanceBin L) (o : Obs X Z) =>
    ∑ k ∈ Finset.range L.K, psiFullProdBin L e k o
  let R := fun (e : NuisanceBin L) (o : Obs X Z) =>
    ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k), psiProdBin phi dphi L e k j o
  let T := fun (e : NuisanceBin L) => commonTailScore M phi dphi L e.prop e.pLev e.piLev e.gammaTail
  have hF (e : NuisanceBin L) (he : BinAdmissible M L e)
      (hcl : ∀ i, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x) :=
    fitted_full_score_block_memLp M L e he hy c hc hcl
  have hR (e : NuisanceBin L) (he : BinAdmissible M L e)
      (hcl : ∀ i, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
      (hct : ∀ r, ∀ᵐ x ∂xLaw M, c ≤ e.tauLev r x) :=
    fitted_regular_score_block_memLp M phi dphi hphi hd hDerivative L e he hy c hc hcl hct
  have hT (e : NuisanceBin L) (he : BinAdmissible M L e)
      (hcl : ∀ i, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x) :=
    fitted_commonTailScore_memLp M phi dphi hphi hd hDerivative L e he c hc hcl
  have hrF := nuisanceRates_full_score_block_sq_tendsto_probability_zero M μ L e0 eh
    he0 heh hy c hc hpi hrP hrpi hrfull
  have hsum (e : NuisanceBin L) (o : Obs X Z) :
      (∑ k : Fin L.K, psiFullProdBin L e k o) = F e o :=
    Fin.sum_univ_eq_sum_range (fun k => psiFullProdBin L e k o) L.K
  simp only [hsum] at hrF
  have hrR := nuisanceRates_regular_score_block_sq_tendsto_probability_zero_of_branch_convergence M μ phi dphi hphi
    hd hDerivative L e0 eh he0 heh hy c hc hpi htau hrp hrlev hrP hrpi hrt hrs hrg hbranch
  have hrT := nuisanceRates_commonTailScore_sq_tendsto_probability_zero M μ phi dphi hphi hd
    hDerivative L e0 eh he0 heh c hc hpi hrp hrlev hrpi hrtail
  have hs := dml_three_term_sq_tendsto_probability_zero μ (observationLaw M)
    (fun n a o => F (eh (2*(n+1)) a) o - F e0 o)
    (fun n a o => R (eh (2*(n+1)) a) o - R e0 o)
    (fun n a o => -(T (eh (2*(n+1)) a) o - T e0 o))
    (fun n a => (hF _ (heh _ a) (fun i => (hpi _ a i).mono (fun _ hx => hx.2))).sub
      (hF e0 he0 (fun i => (hpi (2*(n+1)) a i).mono (fun _ hx => hx.1))))
    (fun n a => (hR _ (heh _ a) (fun i => (hpi _ a i).mono (fun _ hx => hx.2))
      (fun r => (htau _ a r).mono (fun _ hx => hx.2))).sub
      (hR e0 he0 (fun i => (hpi (2*(n+1)) a i).mono (fun _ hx => hx.1))
        (fun r => (htau (2*(n+1)) a r).mono (fun _ hx => hx.1))))
    (fun n a => ((hT _ (heh _ a) (fun i => (hpi _ a i).mono (fun _ hx => hx.2))).sub
      (hT e0 he0 (fun i => (hpi (2*(n+1)) a i).mono (fun _ hx => hx.1)))).neg)
    hrF hrR (by simpa only [T, neg_sq] using hrT)
  have hid (n : ℕ) (a : A) (o : Obs X Z) :
      psiBin M phi dphi L hK o (eh (2*(n+1)) a) - psiBin M phi dphi L hK o e0 =
      (F (eh (2*(n+1)) a) o - F e0 o) + (R (eh (2*(n+1)) a) o - R e0 o) -
        -(T (eh (2*(n+1)) a) o - T e0 o) := by
    simp only [psiBin, Finset.sum_add_distrib, F, R, T]
    ring
  simpa only [hid] using hs

-- @node: nuisanceRates_binary_score_l2_tendsto_probability_zero_of_branch_convergence
/-- Suppose [the policy is valid](hyp:hphi), [its derivative is as specified](hyp:hd)
and [uniformly bounded and Lipschitz](hyp:hDerivative), [there is at least one
treatment level](hyp:hK), [reference nuisances](hyp:he0) and [all fits](hyp:heh)
are admissible, [outcomes are binary almost surely](hyp:hy), [c is positive](hyp:hc),
and [reference and fitted baseline assignment masses](hyp:hpi) and [policy
masses](hyp:htau) are almost surely at least c. Under quarter-rate conditions
for [propensities](hyp:hrp), [treatment-level propensities](hyp:hrlev),
[treated-success probabilities](hyp:hrP), [baseline assignment masses](hyp:hrpi),
[policy masses](hyp:hrt), [pooling shares](hyp:hrs), [regular regression weights](hyp:hrg),
[full-level regression weights](hyp:hrfull), and [the tail regression weight](hyp:hrtail),
and [convergence to zero in probability of the integrated sum of squared errors
in the three branch indicators at every interior regular level](hyp:hbranch),
[the complete binary score's L2 error converges to zero in probability along
sample sizes twice n plus two](goal). -/
lemma nuisanceRates_binary_score_l2_tendsto_probability_zero_of_branch_convergence
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (e0 : NuisanceBin L) (eh : ℕ → A → NuisanceBin L)
    (he0 : BinAdmissible M L e0) (heh : ∀ n a, BinAdmissible M L (eh n a))
    (hy : OutcomeBinaryAE M) (c : ℝ) (hc : 0 < c)
    (hpi : ∀ n a (i : PositiveIndex L.K), ∀ᵐ x ∂xLaw M,
      c ≤ e0.piLev i x ∧ c ≤ (eh n a).piLev i x)
    (htau : ∀ n a (r : RegularIndex L), ∀ᵐ x ∂xLaw M,
      c ≤ e0.tauLev r x ∧ c ≤ (eh n a).tauLev r x)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) e0.prop)
    (hrlev : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrP : FiniteNuisanceRates M μ (fun n a => (eh n a).P1) e0.P1)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) e0.piLev)
    (hrt : FiniteNuisanceRates M μ (fun n a => (eh n a).tauLev) e0.tauLev)
    (hrs : ∀ r : RegularIndex L,
      FiniteNuisanceRates M μ (fun n a => (eh n a).share r) (e0.share r))
    (hrg : FiniteNuisanceRates M μ (fun n a => (eh n a).gamma) e0.gamma)
    (hrfull : FiniteNuisanceRates M μ (fun n a => (eh n a).gammaFull) e0.gammaFull)
    (hrtail : FiniteNuisanceRates M μ (fun n a (_ : Unit) => (eh n a).gammaTail)
      (fun _ => e0.gammaTail))
    (hbranch : ∀ k, k < L.K → ∀ j, 1 ≤ j ∧ j ≤ L.l k →
      Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o : Obs X Z,
        (Iact phi L (eh (2*(n+1)) a) k j o.1 - Iact phi L e0 k j o.1)^2 +
        (Dbd phi L (eh (2*(n+1)) a) k j o.1 - Dbd phi L e0 k j o.1)^2 +
        (Edom phi L (eh (2*(n+1)) a) k j o.1 - Edom phi L e0 k j o.1)^2
        ∂observationLaw M) atTop (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt (∫ o : Obs X Z,
        (psiBin M phi dphi L hK o (eh (2*(n+1)) a) -
          psiBin M phi dphi L hK o e0)^2 ∂observationLaw M))
      atTop (fun _ _ => 0) := by
  have hs := nuisanceRates_binary_score_sq_tendsto_probability_zero_of_branch_convergence M μ phi dphi hphi hd
    hDerivative L hK e0 eh he0 heh hy c hc hpi htau hrp hrlev hrP hrpi hrt hrs hrg
    hrfull hrtail hbranch
  have hcont : Continuous (fun t : ℝ => Real.sqrt t) := by fun_prop
  simpa only [Real.sqrt_zero] using
    Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt hcont.continuousAt hs

-- @node: nuisanceRates_population_binary_score_l2_tendsto_probability_zero
/-- Assume [a valid policy](hyp:hphi) with [the specified derivative](hyp:hd)
that is [uniformly bounded and Lipschitz](hyp:hDerivative), [the structural model
assumptions](hyp:hStruct), [known outcome endpoints](hyp:hend), [finite instrument
reduction](hyp:hf), [a positive number of treatment levels](hyp:hK), [invariant
level ordering under the policy](hyp:hOrder), [policy levels off the boundary](hyp:hOff),
[separated propensity gaps](hyp:hGap), [policy overlap](hyp:hpol), and [separated
outcome gaps](hyp:hOutcome). Suppose [population nuisances](hyp:he0) and [all
fits](hyp:heh) are admissible, [outcomes are binary almost surely](hyp:hy),
[c is positive](hyp:hc), and [population and fitted baseline assignment masses](hyp:hpi)
and [policy masses](hyp:htau) are almost surely at least c. If quarter-rate
conditions hold for [propensities](hyp:hrp), [treatment-level propensities](hyp:hrlev),
[treated-success probabilities](hyp:hrP), [baseline assignment masses](hyp:hrpi),
[policy masses](hyp:hrt), [pooling shares](hyp:hrs), [regular regression weights](hyp:hrg),
[full-level regression weights](hyp:hrfull), and [the tail regression weight](hyp:hrtail),
then [the L2 distance between the fitted binary score and its population-nuisance
version converges to zero in probability along sample sizes twice n plus two](goal). -/
lemma nuisanceRates_population_binary_score_l2_tendsto_probability_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (hStruct : StructuralAssumptions M) (hend : OutcomeEndpointsKnown M)
    (hf : InstrumentFiniteReduction Z)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (hOff : PolicyLevelOffBoundary L) (gap : ℝ)
    (hGap : PropensityGapSeparationWitness M.prop (policyProp phi M.prop) gap)
    (cpi : ℝ) (hpol : PolicyOverlap M L cpi) (ch : ℝ)
    (hOutcome : DiscreteOutcomeGapWitness M L ch) (eh : ℕ → A → NuisanceBin L)
    (he0 : BinAdmissible M L (eta0Bin M L)) (heh : ∀ n a, BinAdmissible M L (eh n a))
    (hy : OutcomeBinaryAE M) (c : ℝ) (hc : 0 < c)
    (hpi : ∀ n a (i : PositiveIndex L.K), ∀ᵐ x ∂xLaw M,
      c ≤ (eta0Bin M L).piLev i x ∧ c ≤ (eh n a).piLev i x)
    (htau : ∀ n a (r : RegularIndex L), ∀ᵐ x ∂xLaw M,
      c ≤ (eta0Bin M L).tauLev r x ∧ c ≤ (eh n a).tauLev r x)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) (eta0Bin M L).prop)
    (hrlev : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) (eta0Bin M L).pLev)
    (hrP : FiniteNuisanceRates M μ (fun n a => (eh n a).P1) (eta0Bin M L).P1)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) (eta0Bin M L).piLev)
    (hrt : FiniteNuisanceRates M μ (fun n a => (eh n a).tauLev) (eta0Bin M L).tauLev)
    (hrs : ∀ r : RegularIndex L,
      FiniteNuisanceRates M μ (fun n a => (eh n a).share r) ((eta0Bin M L).share r))
    (hrg : FiniteNuisanceRates M μ (fun n a => (eh n a).gamma) (eta0Bin M L).gamma)
    (hrfull : FiniteNuisanceRates M μ (fun n a => (eh n a).gammaFull) (eta0Bin M L).gammaFull)
    (hrtail : FiniteNuisanceRates M μ (fun n a (_ : Unit) => (eh n a).gammaTail)
      (fun _ => (eta0Bin M L).gammaTail))
    :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt (∫ o : Obs X Z,
        (psiBin M phi dphi L hK o (eh (2*(n+1)) a) -
          psiBin M phi dphi L hK o (eta0Bin M L))^2 ∂observationLaw M))
      atTop (fun _ _ => 0) := by
  apply nuisanceRates_binary_score_l2_tendsto_probability_zero_of_branch_convergence M μ
    phi dphi hphi hd hDerivative L hK (eta0Bin M L) eh he0 heh hy c hc hpi htau
    hrp hrlev hrP hrpi hrt hrs hrg hrfull hrtail
  intro k hk j hj
  exact nuisanceRates_population_binary_branch_observation_sq_tendsto_probability_zero M μ
    phi dphi hphi hd hDerivative hStruct hend hf hy L hOrder hOff gap hGap
    cpi hpol ch hOutcome eh he0 heh hrp hrlev hrP hrs k j hk hj

end Papers.TbsPrteOptimalTransport

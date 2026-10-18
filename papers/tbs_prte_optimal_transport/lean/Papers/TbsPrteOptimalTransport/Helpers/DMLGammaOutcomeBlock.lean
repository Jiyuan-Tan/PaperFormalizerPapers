module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLGammaBandBlock
/-! Assembly of the outcome portion of the nonterminal continuous score.
The fitted band mean and the paired outcome residual use the same gamma;
their component energies give L2 convergence of the combined block. -/
@[expose] public section
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]

-- @node: continuousGammaOutcomeBlock
/-- For [a latent instrumental-variable model](hyp:M), [its population-level and band specification](hyp:L), [continuous nuisance functions](hyp:e), and [an observation](hyp:o), [the continuous gamma-weighted outcome block](goal) sums, over nonterminal levels and regular bands, gamma times the sum of the preceding band's conditional outcome-mean contrast and its upper-minus-lower outcome residual. -/
noncomputable def continuousGammaOutcomeBlock (M : LatentIVModel Ω X Z)
    (L : LevelData Z X) (e : NuisanceCont L) (o : Obs X Z) : ℝ :=
  ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
    regularValue e.gamma k j o.1 * (contJ L e k (j-1) o.1 +
      (IFJ M L e true k (j-1) o - IFJ M L e false k (j-1) o))

-- @node: continuousGammaOutcomeBlock_decomposition
/-- [The continuous gamma-weighted outcome block equals the sum of its gamma-weighted conditional band-mean block and its gamma-weighted upper-minus-lower outcome-residual block](goal), with both sums running over nonterminal levels and regular bands and using the preceding outcome-band coordinate. -/
lemma continuousGammaOutcomeBlock_decomposition (M : LatentIVModel Ω X Z)
    (L : LevelData Z X) (e : NuisanceCont L) (o : Obs X Z) :
    continuousGammaOutcomeBlock M L e o =
      (∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
        regularValue e.gamma k j o.1 * contJ L e k (j-1) o.1) +
      ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
        regularValue e.gamma k j o.1 *
          (IFJ M L e true k (j-1) o - IFJ M L e false k (j-1) o) := by
  simp only [continuousGammaOutcomeBlock, mul_add, Finset.sum_add_distrib]

-- @node: fitted_continuous_gamma_outcome_block_memLp
/-- If [the continuous nuisances are admissible](hyp:he), [the denominator bound is positive](hyp:hc), and [every positive-level baseline probability is at least that bound almost everywhere](hyp:hden), then [the continuous gamma-weighted outcome block is square integrable under the observation law](goal). -/
lemma fitted_continuous_gamma_outcome_block_memLp [Fintype Z]
    (M : LatentIVModel Ω X Z) (L : LevelData Z X) (e : NuisanceCont L)
    (he : ContAdmissible M L e) (c : ℝ) (hc : 0 < c)
    (hden : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x) :
    MemLp (continuousGammaOutcomeBlock M L e) 2 (observationLaw M) := by
  convert
    (fitted_continuous_gamma_contJ_block_memLp M L e he).add
      (fitted_continuous_gamma_IFJ_block_memLp M L e he c hc hden) using 1
  funext o
  exact continuousGammaOutcomeBlock_decomposition M L e o

-- @node: encoded_continuous_gamma_outcome_block_sq_tendsto_probability_zero
/-- Suppose [the true continuous nuisances are admissible](hyp:he0), [fitted nuisances obey clipping](hyp:hclip), [fitted shares are nonnegative and sum to one](hyp:hshares), [encoded fitted components are measurable](hyp:hm), [treated-outcome densities are bounded near band boundaries](hyp:hd), and [componentwise L2 errors are of smaller order in probability than the inverse fourth root of sample size](hyp:hr). Under [baseline overlap](hyp:hov) and [overlap-based fitted denominator clipping](hyp:hden), [the observation-integrated squared difference between the fitted and true continuous gamma-weighted outcome blocks converges in probability to zero along sample sizes twice one plus the index](goal). -/
lemma encoded_continuous_gamma_outcome_block_sq_tendsto_probability_zero [Fintype Z]
    (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n t, ContClipping M L (eh n t))
    (hshares : ∀ n t, ContFittedSharesSimplex L (eh n t))
    (hm : ∀ n t d, Measurable (contComponent M L (eh n t) d))
    (hd : BoundaryDensitiesBounded M L)
    (hr : FiniteNuisanceRates M μ (fun n t => contComponent M L (eh n t))
      (contComponent M L (trueNuisance M L)))
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (hden : ∀ n t, ContDenominatorsClipped L (eh n t) cpi) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ o : Obs X Z,
        (continuousGammaOutcomeBlock M L (eh (2*(n+1)) t) o -
          continuousGammaOutcomeBlock M L (trueNuisance M L) o)^2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  let er := fun n t => restrictContShares L (eh n t)
  have her n t : ContAdmissible M L (er n t) :=
    restrictContShares_admissible_of_encoded_clipping M L (eh n t)
      (hclip n t) (hshares n t) (hm n t)
  let J := fun (e : NuisanceCont L) (o : Obs X Z) =>
    ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
      regularValue e.gamma k j o.1 * contJ L e k (j-1) o.1
  let R := fun (e : NuisanceCont L) (o : Obs X Z) =>
    ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
      regularValue e.gamma k j o.1 *
        (IFJ M L e true k (j-1) o - IFJ M L e false k (j-1) o)
  let F := fun n t o => J (er (2*(n+1)) t) o - J (trueNuisance M L) o
  let G := fun n t o => R (er (2*(n+1)) t) o - R (trueNuisance M L) o
  have hc : 0 < cpi / 2 := by linarith [hov.1]
  have hden0 (i : PositiveIndex L.K) :
      ∀ᵐ x ∂xLaw M, cpi / 2 ≤ (trueNuisance M L).piLev i x := by
    apply Eventually.of_forall
    intro x
    have hx := hov.2 x i.val i.property.1 i.property.2
    change cpi / 2 ≤ (levelSetProb M L).1 i.val x
    linarith [hov.1]
  have hF n t : MemLp (F n t) 2 (observationLaw M) :=
    (fitted_continuous_gamma_contJ_block_memLp M L _ (her _ t)).sub
      (fitted_continuous_gamma_contJ_block_memLp M L _ he0)
  have hG n t : MemLp (G n t) 2 (observationLaw M) :=
    (fitted_continuous_gamma_IFJ_block_memLp M L _ (her _ t) (cpi / 2) hc
      (fun i => Eventually.of_forall (fun x => (hden _ t).1 i x |>.1))).sub
      (fitted_continuous_gamma_IFJ_block_memLp M L _ he0 (cpi / 2) hc hden0)
  have hrF : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ o, (F n t o)^2 ∂observationLaw M) atTop (fun _ _ => 0) := by
    simpa only [F, J, er, restrictContShares, regularValue, contJ] using
      encoded_continuous_gamma_contJ_block_sq_tendsto_probability_zero
        M μ L he0 eh hclip hshares hm hr
  have hrG : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ o, (G n t o)^2 ∂observationLaw M) atTop (fun _ _ => 0) := by
    simpa only [G, R, er, restrictContShares, regularValue, IFJ, nuValue] using
      encoded_continuous_gamma_IFJ_block_sq_tendsto_probability_zero
        M μ L he0 eh hclip hshares hm hd hr cpi hov hden
  have hz : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun (_ : ℕ) (_ : A) => (0 : ℝ)) atTop (fun _ _ => 0) := by
    rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm]
    intro eps heps
    simpa only [sub_self, norm_zero, not_le.mpr heps, Set.ofPred_false,
      measure_empty] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (𝓝 0))
  have hs := dml_three_term_sq_tendsto_probability_zero μ (observationLaw M)
    F G (fun _ _ _ => 0) hF hG (fun _ _ => MemLp.zero') hrF hrG (by simpa using hz)
  have hid n t o : continuousGammaOutcomeBlock M L (eh (2*(n+1)) t) o -
      continuousGammaOutcomeBlock M L (trueNuisance M L) o = F n t o + G n t o - 0 := by
    simp only [continuousGammaOutcomeBlock_decomposition, F, G, J, R, er,
      restrictContShares, regularValue, contJ, IFJ, nuValue]
    ring
  simpa only [← hid] using hs

-- @node: encoded_continuous_gamma_outcome_block_l2_tendsto_probability_zero
/-- Given [admissible true nuisances](hyp:he0), [clipped fitted nuisances](hyp:hclip), [nonnegative fitted shares summing to one](hyp:hshares), [measurable encoded fitted components](hyp:hm), [bounded treated-outcome densities near band boundaries](hyp:hd), and [componentwise L2 errors of smaller order in probability than the inverse fourth root of sample size](hyp:hr), assume [baseline overlap](hyp:hov) and [overlap-based fitted denominator clipping](hyp:hden). Then [the L2 distance between the fitted and true continuous gamma-weighted outcome blocks converges in probability to zero along sample sizes twice one plus the index](goal). -/
lemma encoded_continuous_gamma_outcome_block_l2_tendsto_probability_zero [Fintype Z]
    (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n t, ContClipping M L (eh n t))
    (hshares : ∀ n t, ContFittedSharesSimplex L (eh n t))
    (hm : ∀ n t d, Measurable (contComponent M L (eh n t) d))
    (hd : BoundaryDensitiesBounded M L)
    (hr : FiniteNuisanceRates M μ (fun n t => contComponent M L (eh n t))
      (contComponent M L (trueNuisance M L)))
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (hden : ∀ n t, ContDenominatorsClipped L (eh n t) cpi) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => Real.sqrt (∫ o : Obs X Z,
        (continuousGammaOutcomeBlock M L (eh (2*(n+1)) t) o -
          continuousGammaOutcomeBlock M L (trueNuisance M L) o)^2
        ∂observationLaw M)) atTop (fun _ _ => 0) := by
  have hs := encoded_continuous_gamma_outcome_block_sq_tendsto_probability_zero
    M μ L he0 eh hclip hshares hm hd hr cpi hov hden
  have hcont : Continuous (fun t : ℝ => Real.sqrt t) := by fun_prop
  simpa only [Real.sqrt_zero] using
    Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt hcont.continuousAt hs

end Papers.TbsPrteOptimalTransport

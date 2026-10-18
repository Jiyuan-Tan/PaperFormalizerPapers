module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLQuantileWeightedIndicator
public import Papers.TbsPrteOptimalTransport.Helpers.DMLGammaOutcomeBlock
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousBandCorrection
/-! Finite assembly of both quantile boundaries in the continuous score.
The lower and upper boundary corrections share the band's gamma multiplier;
their componentwise energies control the full nonterminal boundary block. -/
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

-- @node: continuousGammaBoundaryBlock
/-- For [a latent instrumental-variable model](hyp:M), [a level and band specification](hyp:L),
[continuous nuisance functions](hyp:e), and [an observation](hyp:o), the
[gamma-weighted boundary block](goal) sums, over nonterminal levels and their bands,
the lower-endpoint quantile times its boundary influence contrast minus the corresponding
upper-endpoint product, both multiplied by the band's gamma weight. -/
noncomputable def continuousGammaBoundaryBlock (M : LatentIVModel Ω X Z)
    (L : LevelData Z X) (e : NuisanceCont L) (o : Obs X Z) : ℝ :=
  ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
    (nuValue M e k (j-1) o.1 * (regularValue e.gamma k j o.1 *
      (IFM M L e true k (j-1) o - IFM M L e false k (j-1) o)) -
    nuValue M e k j o.1 * (regularValue e.gamma k j o.1 *
      (IFM M L e true k j o - IFM M L e false k j o)))

-- @node: fitted_continuous_gamma_boundary_block_memLp
/-- If [the fitted continuous nuisances are admissible](hyp:he),
[the denominator floor is positive](hyp:hc), and [every positive-level propensity is at
least that floor almost everywhere under the covariate law](hyp:hden), then
[the gamma-weighted boundary block has a finite second moment under the observation law](goal). -/
lemma fitted_continuous_gamma_boundary_block_memLp [Fintype Z]
    (M : LatentIVModel Ω X Z) (L : LevelData Z X) (e : NuisanceCont L)
    (he : ContAdmissible M L e) (c : ℝ) (hc : 0 < c)
    (hden : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x) :
    MemLp (continuousGammaBoundaryBlock M L e) 2 (observationLaw M) := by
  unfold continuousGammaBoundaryBlock
  apply memLp_finsetSum
  intro k hk
  apply memLp_finsetSum
  intro j hj
  have hk' := Finset.mem_range.mp hk
  have hg : k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k :=
    ⟨hk'.le, Finset.mem_Icc.mp hj⟩
  simpa only [regularValue, dif_pos hg, Pi.sub_def] using
    (fitted_continuous_quantile_gamma_IFM_contrast_memLp
      M L e he c hc hden ⟨(k,j), hg⟩ k (j-1) hk').sub
    (fitted_continuous_quantile_gamma_IFM_contrast_memLp
      M L e he c hc hden ⟨(k,j), hg⟩ k j hk')

-- @node: encoded_continuous_gamma_boundary_block_sq_tendsto_probability_zero
/-- Suppose [the true continuous nuisances are admissible](hyp:he0), and
[a sequence of fitted continuous nuisances](hyp:eh) satisfies [clipping at every sample
index and realization](hyp:hclip), [the fitted-share simplex restrictions](hyp:hshares),
[measurability of every encoded coordinate](hyp:hm), and [the finite nuisance rate
conditions relative to truth](hyp:hr). If [boundary densities are bounded](hyp:hd),
[baseline overlap holds with the given constant](hyp:hov), and [all fitted denominators
are clipped using that constant](hyp:hden), then [the integrated squared error of the
gamma-weighted boundary block, evaluated at sample indices twice one plus the sequence
index, converges to zero in probability under the fitting measure](goal). -/
lemma encoded_continuous_gamma_boundary_block_sq_tendsto_probability_zero [Fintype Z]
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
        (continuousGammaBoundaryBlock M L (eh (2*(n+1)) t) o -
          continuousGammaBoundaryBlock M L (trueNuisance M L) o)^2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  let er := fun n t => restrictContShares L (eh n t)
  have her n t : ContAdmissible M L (er n t) :=
    restrictContShares_admissible_of_encoded_clipping M L (eh n t)
      (hclip n t) (hshares n t) (hm n t)
  have hc : 0 < cpi / 2 := by linarith [hov.1]
  have hden0 (i : PositiveIndex L.K) :
      ∀ᵐ x ∂xLaw M, cpi / 2 ≤ (trueNuisance M L).piLev i x := by
    apply Eventually.of_forall
    intro x
    have hx := hov.2 x i.val i.property.1 i.property.2
    change cpi / 2 ≤ (levelSetProb M L).1 i.val x
    linarith [hov.1]
  let Q := fun (e : NuisanceCont L) (k j b : ℕ) (o : Obs X Z) =>
    nuValue M e k b o.1 * (regularValue e.gamma k j o.1 *
      (IFM M L e true k b o - IFM M L e false k b o))
  let F := fun (b : ℕ → ℕ) (k j n : ℕ) (t : A) (o : Obs X Z) =>
    Q (er (2*(n+1)) t) k j (b j) o - Q (trueNuisance M L) k j (b j) o
  have hF b k j n t (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k) :
      MemLp (F b k j n t) 2 (observationLaw M) := by
    have hg : k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k := ⟨hk.le, hj⟩
    simpa only [F, Q, regularValue, dif_pos hg, Pi.sub_def] using
      (fitted_continuous_quantile_gamma_IFM_contrast_memLp
        M L _ (her _ t) (cpi/2) hc
        (fun i => Eventually.of_forall (fun x => (hden _ t).1 i x |>.1))
        ⟨(k,j), hg⟩ k (b j) hk).sub
      (fitted_continuous_quantile_gamma_IFM_contrast_memLp
        M L _ he0 (cpi/2) hc hden0 ⟨(k,j), hg⟩ k (b j) hk)
  let B := fun (b : ℕ → ℕ) n t o =>
    ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k), F b k j n t o
  have hB b n t : MemLp (B b n t) 2 (observationLaw M) := by
    apply memLp_finsetSum
    intro k hk
    exact memLp_finsetSum _ (fun j hj =>
      hF b k j n t (Finset.mem_range.mp hk) (Finset.mem_Icc.mp hj))
  have hrB b : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ o, (B b n t o)^2 ∂observationLaw M) atTop (fun _ _ => 0) := by
    apply dml_finset_sum_sq_tendsto_probability_zero μ (observationLaw M)
      (Finset.range L.K)
      (fun k n t o => ∑ j ∈ Finset.Icc 1 (L.l k), F b k j n t o)
      (fun k hk n t => memLp_finsetSum _ (fun j hj =>
        hF b k j n t (Finset.mem_range.mp hk) (Finset.mem_Icc.mp hj)))
    intro k hk
    apply dml_finset_sum_sq_tendsto_probability_zero μ (observationLaw M)
      (Finset.Icc 1 (L.l k)) (F b k)
      (fun j hj n t => hF b k j n t (Finset.mem_range.mp hk) (Finset.mem_Icc.mp hj))
    intro j hj
    have hg : k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k :=
      ⟨(Finset.mem_range.mp hk).le, Finset.mem_Icc.mp hj⟩
    simpa only [F, Q, regularValue, dif_pos hg, er, restrictContShares, IFM, nuValue] using
      encoded_continuous_quantile_gamma_IFM_contrast_sq_tendsto_probability_zero
        M μ L he0 eh hclip hshares hm hd hr cpi hov hden
        ⟨(k,j), hg⟩ k (b j) (Finset.mem_range.mp hk)
  have hz : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun (_ : ℕ) (_ : A) => (0 : ℝ)) atTop (fun _ _ => 0) := by
    rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm]
    intro eps heps
    simpa only [sub_self, norm_zero, not_le.mpr heps, Set.ofPred_false,
      measure_empty] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (𝓝 0))
  have hs := dml_three_term_sq_tendsto_probability_zero μ (observationLaw M)
    (fun _ _ _ => 0) (B (fun j => j-1)) (B id)
    (fun _ _ => MemLp.zero') (hB _) (hB _) (by simpa using hz) (hrB _) (hrB _)
  have hid n t o : continuousGammaBoundaryBlock M L (eh (2*(n+1)) t) o -
      continuousGammaBoundaryBlock M L (trueNuisance M L) o =
      0 + B (fun j => j-1) n t o - B id n t o := by
    simp only [continuousGammaBoundaryBlock, B, F, Q, er, restrictContShares,
      regularValue, IFM, nuValue, id_eq, Finset.sum_sub_distrib]
    ring
  simpa only [← hid] using hs

-- @node: encoded_continuous_gamma_boundary_block_l2_tendsto_probability_zero
/-- Under [admissibility of the true nuisances](hyp:he0), let [the fitted nuisance
sequence](hyp:eh) obey [clipping](hyp:hclip), [the share simplex restrictions](hyp:hshares),
[measurability of all encoded coordinates](hyp:hm), and [the finite nuisance rate
conditions relative to truth](hyp:hr). With [bounded boundary densities](hyp:hd),
[baseline overlap at the given constant](hyp:hov), and [denominators clipped using that
constant](hyp:hden), [the square root of the observation-law integrated squared error
of the gamma-weighted boundary block at sample indices twice one plus the sequence
index converges to zero in probability under the fitting measure](goal). -/
lemma encoded_continuous_gamma_boundary_block_l2_tendsto_probability_zero [Fintype Z]
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
        (continuousGammaBoundaryBlock M L (eh (2*(n+1)) t) o -
          continuousGammaBoundaryBlock M L (trueNuisance M L) o)^2
        ∂observationLaw M)) atTop (fun _ _ => 0) := by
  have hs := encoded_continuous_gamma_boundary_block_sq_tendsto_probability_zero
    M μ L he0 eh hclip hshares hm hd hr cpi hov hden
  have hcont : Continuous (fun t : ℝ => Real.sqrt t) := by fun_prop
  simpa only [Real.sqrt_zero] using
    Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt hcont.continuousAt hs

-- This identifies the assembled blocks with the regression part of psiProd,
-- including its j-1 band index and the fixed lower endpoint.
-- @node: continuous_gamma_regression_block_decomposition
/-- [The sum over nonterminal levels and bands of the gamma weight times the band
moment plus its regression correction equals the gamma-weighted outcome block plus
the gamma-weighted boundary block, at each observation](goal). -/
lemma continuous_gamma_regression_block_decomposition (M : LatentIVModel Ω X Z)
    (L : LevelData Z X) (e : NuisanceCont L) (o : Obs X Z) :
    (∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
      regularValue e.gamma k j o.1 * (contJ L e k (j-1) o.1 +
        continuousBandRegressionCorrection M L e k (j-1) o)) =
      continuousGammaOutcomeBlock M L e o + continuousGammaBoundaryBlock M L e o := by
  unfold continuousGammaOutcomeBlock continuousGammaBoundaryBlock
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hj1 : j-1+1 = j := by have := (Finset.mem_Icc.mp hj).1; omega
  simp only [continuousBandRegressionCorrection, hj1]
  ring

-- @node: fitted_continuous_gamma_regression_block_memLp
/-- If [the continuous nuisances are admissible](hyp:he), [the propensity floor is
positive](hyp:hc), and [all positive-level propensities exceed or equal that floor
almost everywhere under the covariate law](hyp:hden), then [the sum of the gamma-weighted
band moments and regression corrections over nonterminal levels and bands has a finite
second moment under the observation law](goal). -/
lemma fitted_continuous_gamma_regression_block_memLp [Fintype Z]
    (M : LatentIVModel Ω X Z) (L : LevelData Z X) (e : NuisanceCont L)
    (he : ContAdmissible M L e) (c : ℝ) (hc : 0 < c)
    (hden : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x) :
    MemLp (fun o : Obs X Z => ∑ k ∈ Finset.range L.K,
      ∑ j ∈ Finset.Icc 1 (L.l k), regularValue e.gamma k j o.1 *
        (contJ L e k (j-1) o.1 + continuousBandRegressionCorrection M L e k (j-1) o))
      2 (observationLaw M) := by
  convert (fitted_continuous_gamma_outcome_block_memLp M L e he c hc hden).add
    (fitted_continuous_gamma_boundary_block_memLp M L e he c hc hden) using 1
  funext o
  exact continuous_gamma_regression_block_decomposition M L e o

-- @node: encoded_continuous_gamma_regression_block_sq_tendsto_probability_zero
/-- Suppose [the true nuisances are admissible](hyp:he0) and [the fitted nuisance
sequence](hyp:eh) satisfies [clipping](hyp:hclip), [the fitted-share simplex
restrictions](hyp:hshares), [measurability of every encoded coordinate](hyp:hm), and
[the finite nuisance rate conditions relative to truth](hyp:hr). With [bounded boundary
densities](hyp:hd), [baseline overlap at the given constant](hyp:hov), and [fitted
denominators clipped using that constant](hyp:hden), [the observation-law integrated
squared error of the full gamma-weighted regression block at sample indices twice
one plus the sequence index converges to zero in probability under the fitting measure](goal). -/
lemma encoded_continuous_gamma_regression_block_sq_tendsto_probability_zero [Fintype Z]
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
        ((∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
          regularValue (eh (2*(n+1)) t).gamma k j o.1 *
            (contJ L (eh (2*(n+1)) t) k (j-1) o.1 +
              continuousBandRegressionCorrection M L (eh (2*(n+1)) t) k (j-1) o)) -
          ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
            regularValue (trueNuisance M L).gamma k j o.1 *
              (contJ L (trueNuisance M L) k (j-1) o.1 +
                continuousBandRegressionCorrection M L (trueNuisance M L) k (j-1) o))^2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  let er := fun n t => restrictContShares L (eh n t)
  have her n t : ContAdmissible M L (er n t) :=
    restrictContShares_admissible_of_encoded_clipping M L (eh n t)
      (hclip n t) (hshares n t) (hm n t)
  have hc : 0 < cpi / 2 := by linarith [hov.1]
  have hden0 (i : PositiveIndex L.K) :
      ∀ᵐ x ∂xLaw M, cpi / 2 ≤ (trueNuisance M L).piLev i x := by
    apply Eventually.of_forall
    intro x
    have hx := hov.2 x i.val i.property.1 i.property.2
    change cpi / 2 ≤ (levelSetProb M L).1 i.val x
    linarith [hov.1]
  let F := fun n t o => continuousGammaOutcomeBlock M L (er (2*(n+1)) t) o -
    continuousGammaOutcomeBlock M L (trueNuisance M L) o
  let G := fun n t o => continuousGammaBoundaryBlock M L (er (2*(n+1)) t) o -
    continuousGammaBoundaryBlock M L (trueNuisance M L) o
  have hF n t : MemLp (F n t) 2 (observationLaw M) :=
    (fitted_continuous_gamma_outcome_block_memLp M L _ (her _ t) (cpi/2) hc
      (fun i => Eventually.of_forall (fun x => (hden _ t).1 i x |>.1))).sub
    (fitted_continuous_gamma_outcome_block_memLp M L _ he0 (cpi/2) hc hden0)
  have hG n t : MemLp (G n t) 2 (observationLaw M) :=
    (fitted_continuous_gamma_boundary_block_memLp M L _ (her _ t) (cpi/2) hc
      (fun i => Eventually.of_forall (fun x => (hden _ t).1 i x |>.1))).sub
    (fitted_continuous_gamma_boundary_block_memLp M L _ he0 (cpi/2) hc hden0)
  have hrF : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ o, (F n t o)^2 ∂observationLaw M) atTop (fun _ _ => 0) := by
    simpa only [F, er, continuousGammaOutcomeBlock, restrictContShares,
      regularValue, contJ, IFJ, nuValue] using
      encoded_continuous_gamma_outcome_block_sq_tendsto_probability_zero
        M μ L he0 eh hclip hshares hm hd hr cpi hov hden
  have hrG : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ o, (G n t o)^2 ∂observationLaw M) atTop (fun _ _ => 0) := by
    simpa only [G, er, continuousGammaBoundaryBlock, restrictContShares,
      regularValue, IFM, nuValue] using
      encoded_continuous_gamma_boundary_block_sq_tendsto_probability_zero
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
  simp only [continuous_gamma_regression_block_decomposition]
  have hid n t o :
      continuousGammaOutcomeBlock M L (eh (2*(n+1)) t) o +
        continuousGammaBoundaryBlock M L (eh (2*(n+1)) t) o -
      (continuousGammaOutcomeBlock M L (trueNuisance M L) o +
        continuousGammaBoundaryBlock M L (trueNuisance M L) o) = F n t o + G n t o - 0 := by
    simp only [F, G, er, continuousGammaOutcomeBlock, continuousGammaBoundaryBlock,
      restrictContShares, regularValue, contJ, IFJ, IFM, nuValue]
    ring
  simpa only [← hid] using hs

end Papers.TbsPrteOptimalTransport

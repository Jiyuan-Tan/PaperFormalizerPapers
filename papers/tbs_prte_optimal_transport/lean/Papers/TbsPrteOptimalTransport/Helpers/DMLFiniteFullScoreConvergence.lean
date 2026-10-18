module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLFullScoreConvergence
/-! Finite assembly of the full-interval binary score convergence.
The moments and energies of the actual product scores are derived from clipping
and component nuisance rates before summing over the population levels. -/
public section
set_option linter.style.haveILetI false
set_option linter.style.openClassical false
set_option linter.unusedFintypeInType false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

-- Finite sums preserve vanishing squared L2 error. The induction invokes the
-- three-term energy bound, rather than requiring a rate for the sum itself.
-- @node: dml_finset_sum_sq_tendsto_probability_zero
/-- If [each function in a finite collection is square integrable for every sample size and realization](hyp:hf) and [each function's integrated square converges to zero in probability](hyp:hr), then [the integrated square of their sum also converges to zero in probability](goal). -/
lemma dml_finset_sum_sq_tendsto_probability_zero {A B ι : Type*}
    [MeasurableSpace A] [MeasurableSpace B] (μ : Measure A) (ν : Measure B)
    (s : Finset ι) (f : ι → ℕ → A → B → ℝ)
    (hf : ∀ i ∈ s, ∀ n a, MemLp (f i n a) 2 ν)
    (hr : ∀ i ∈ s, Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ x, (f i n a x) ^ 2 ∂ν) atTop (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ x, (∑ i ∈ s, f i n a x) ^ 2 ∂ν) atTop (fun _ _ => 0) := by
  classical
  have hz : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun (_ : ℕ) (_ : A) => (0 : ℝ)) atTop (fun _ _ => 0) := by
    rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm]
    intro eps heps
    simpa only [sub_self, norm_zero, not_le.mpr heps, Set.ofPred_false,
      measure_empty] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (𝓝 0))
  induction s using Finset.induction_on with
  | empty => simpa using hz
  | @insert i s hi ih =>
    have hfs : ∀ j ∈ s, ∀ n a, MemLp (f j n a) 2 ν :=
      fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hrs := ih hfs (fun j hj => hr j (Finset.mem_insert_of_mem hj))
    have hs := dml_three_term_sq_tendsto_probability_zero μ ν (f i)
      (fun n a x => ∑ j ∈ s, f j n a x) (fun _ _ _ => 0)
      (hf i (Finset.mem_insert_self i s))
      (fun n a => memLp_finsetSum s (fun j hj => hfs j hj n a))
      (fun _ _ => MemLp.zero')
      (hr i (Finset.mem_insert_self i s)) hrs (by simpa using hz)
    simpa only [Finset.sum_insert hi, sub_zero] using hs

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- The event contrast cancels the plug-in product weight. Its magnitude is at
-- most one, and overlap bounds the two remaining weighted residuals.
-- @node: fitted_full_product_memLp
/-- If [the binary-outcome nuisances are admissible](hyp:he), [outcomes are binary almost surely](hyp:hy), [the overlap bound is strictly positive](hyp:hc), and [every fitted positive-level instrument probability is almost surely at least that bound](hyp:hclip), then [the full-interval product score at the chosen level is square integrable under the observation distribution](goal). -/
lemma fitted_full_product_memLp (L : LevelData Z X) (e : NuisanceBin L)
    (he : BinAdmissible M L e) (hy : OutcomeBinaryAE M)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (k : Fin L.K) : MemLp (psiFullProdBin L e k) 2 (observationLaw M) := by
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  let ev := fun o : Obs X Z => indicator (o.2.1 ∈ higherPolicy L k) -
    indicator (o.2.1 ∈ higherBaseline L k)
  have hev : Measurable ev := by dsimp only [ev]; fun_prop
  have hj := fitted_binFullJ_measurable M L e he k
  have hplug : MemLp (fun o : Obs X Z => ev o * binFullJ L e k o.1)
      2 (observationLaw M) := by
    apply MemLp.of_bound (by fun_prop) 1
    filter_upwards [observationLaw_covariate_ae M _
      (fitted_binFullJ_norm_bound M L e he k)] with o ho
    have hb : |ev o| ≤ 1 := by
      dsimp only [ev, indicator]
      split_ifs <;> norm_num
    rw [norm_mul, Real.norm_eq_abs (ev o)]
    exact (mul_le_mul hb ho (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hrp := fitted_gammaFull_RP_memLp M L e he hy c hc hclip k (k+1) (by omega)
  have hrm := fitted_gammaFull_RP_memLp M L e he hy c hc hclip k k k.isLt.le
  convert (hplug.add hrp).sub hrm using 1
  funext o
  simp only [Pi.sub_apply, Pi.add_apply, psiFullProdBin, fullValue, dif_pos k.isLt, ev]
  ring

-- No score-level convergence hypothesis: each summand's energy is supplied
-- by the proved full-product convergence from P1, pi and gammaFull rates.
-- @node: nuisanceRates_full_score_block_sq_tendsto_probability_zero
/-- If [the reference binary nuisances are admissible](hyp:he0), [all fitted binary nuisances are admissible](hyp:heh), [outcomes are binary almost surely](hyp:hy), [the overlap bound is positive](hyp:hc), and [reference and fitted positive-level instrument probabilities are almost surely bounded below by it](hyp:hclip), and if [the fitted success probabilities satisfy the finite nuisance rate conditions](hyp:hrP), [the fitted level instrument probabilities satisfy those rate conditions](hyp:hrpi), and [the fitted full-interval weights satisfy those rate conditions](hyp:hrg), then [the integrated squared difference between the fitted and reference sums of full-interval product scores converges to zero in probability along even sample sizes](goal). -/
lemma nuisanceRates_full_score_block_sq_tendsto_probability_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (L : LevelData Z X) (e0 : NuisanceBin L) (eh : ℕ → A → NuisanceBin L)
    (he0 : BinAdmissible M L e0) (heh : ∀ n a, BinAdmissible M L (eh n a))
    (hy : OutcomeBinaryAE M) (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a (i : PositiveIndex L.K), ∀ᵐ x ∂xLaw M,
      c ≤ e0.piLev i x ∧ c ≤ (eh n a).piLev i x)
    (hrP : FiniteNuisanceRates M μ (fun n a => (eh n a).P1) e0.P1)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) e0.piLev)
    (hrg : FiniteNuisanceRates M μ (fun n a => (eh n a).gammaFull) e0.gammaFull) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o,
        ((∑ k : Fin L.K, psiFullProdBin L (eh (2*(n+1)) a) k o) -
          ∑ k : Fin L.K, psiFullProdBin L e0 k o)^2 ∂observationLaw M)
      atTop (fun _ _ => 0) := by
  have hs := dml_finset_sum_sq_tendsto_probability_zero μ (observationLaw M)
    Finset.univ (fun (k : Fin L.K) n a o =>
      psiFullProdBin L (eh (2*(n+1)) a) k o - psiFullProdBin L e0 k o)
    (fun k _ n a =>
      (fitted_full_product_memLp M L _ (heh _ a) hy c hc
        (fun i => (hclip _ a i).mono (fun _ hx => hx.2)) k).sub
      (fitted_full_product_memLp M L e0 he0 hy c hc
        (fun i => (hclip (2*(n+1)) a i).mono (fun _ hx => hx.1)) k))
    (fun k _ => nuisanceRates_full_product_sq_tendsto_probability_zero M μ L e0 eh
      he0 heh hy c hc hclip hrP hrpi hrg k)
  simpa only [Finset.sum_sub_distrib] using hs

-- The same indexing used in psiBin supplies a second moment for the full
-- block, so the centered evaluation-sample argument can use this construction.
-- @node: fitted_full_score_block_memLp
/-- If [the binary-outcome nuisances are admissible](hyp:he), [outcomes are binary almost surely](hyp:hy), [the overlap bound is positive](hyp:hc), and [all fitted positive-level instrument probabilities are almost surely at least that bound](hyp:hclip), then [the sum of full-interval product scores over all population levels is square integrable under the observation distribution](goal). -/
lemma fitted_full_score_block_memLp (L : LevelData Z X) (e : NuisanceBin L)
    (he : BinAdmissible M L e) (hy : OutcomeBinaryAE M)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x) :
    MemLp (fun o => ∑ k ∈ Finset.range L.K, psiFullProdBin L e k o)
      2 (observationLaw M) := by
  apply memLp_finsetSum
  intro k hk
  exact fitted_full_product_memLp M L e he hy c hc hclip
    ⟨k, Finset.mem_range.mp hk⟩

-- Convert the assembled energy to the observation-law L2 norm, in the
-- natural-number indexing of the total binary score.
-- @node: nuisanceRates_full_score_block_l2_tendsto_probability_zero
/-- If [the reference binary nuisances are admissible](hyp:he0), [every fitted binary nuisance record is admissible](hyp:heh), [outcomes are binary almost surely](hyp:hy), [the overlap bound is positive](hyp:hc), and [reference and fitted positive-level instrument probabilities are almost surely bounded below by it](hyp:hclip), and if [the fitted success probabilities satisfy the finite nuisance rate conditions](hyp:hrP), [the fitted level instrument probabilities satisfy those rate conditions](hyp:hrpi), and [the fitted full-interval weights satisfy those rate conditions](hyp:hrg), then [the population root mean squared difference between the fitted and reference full score blocks converges to zero in probability along even sample sizes](goal). -/
lemma nuisanceRates_full_score_block_l2_tendsto_probability_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (L : LevelData Z X) (e0 : NuisanceBin L) (eh : ℕ → A → NuisanceBin L)
    (he0 : BinAdmissible M L e0) (heh : ∀ n a, BinAdmissible M L (eh n a))
    (hy : OutcomeBinaryAE M) (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a (i : PositiveIndex L.K), ∀ᵐ x ∂xLaw M,
      c ≤ e0.piLev i x ∧ c ≤ (eh n a).piLev i x)
    (hrP : FiniteNuisanceRates M μ (fun n a => (eh n a).P1) e0.P1)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) e0.piLev)
    (hrg : FiniteNuisanceRates M μ (fun n a => (eh n a).gammaFull) e0.gammaFull) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt (∫ o,
        ((∑ k ∈ Finset.range L.K, psiFullProdBin L (eh (2*(n+1)) a) k o) -
          ∑ k ∈ Finset.range L.K, psiFullProdBin L e0 k o) ^ 2 ∂observationLaw M))
      atTop (fun _ _ => 0) := by
  have hs := nuisanceRates_full_score_block_sq_tendsto_probability_zero M μ L e0 eh
    he0 heh hy c hc hclip hrP hrpi hrg
  have hcont : Continuous (fun t : ℝ => Real.sqrt t) := by fun_prop
  have hl := Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt
    hcont.continuousAt hs
  have hsum (e : NuisanceBin L) (o : Obs X Z) :
      (∑ k : Fin L.K, psiFullProdBin L e k o) =
        ∑ k ∈ Finset.range L.K, psiFullProdBin L e k o :=
    Fin.sum_univ_eq_sum_range (fun k => psiFullProdBin L e k o) L.K
  simpa only [Real.sqrt_zero, hsum] using hl

end Papers.TbsPrteOptimalTransport

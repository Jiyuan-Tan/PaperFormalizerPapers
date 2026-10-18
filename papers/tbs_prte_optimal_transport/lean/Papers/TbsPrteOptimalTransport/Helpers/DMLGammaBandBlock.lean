module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLGammaBandMeans
/-! Finite assembly of the gamma-weighted plug-in outcome bands in continuous DML.
Componentwise band convergence gives vanishing energy and L2 norm for the
nonterminal block in the total orthogonal score. -/
public section
set_option linter.unusedFintypeInType false
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]

-- @node: fitted_continuous_gamma_contJ_block_memLp
/-- If [the continuous-outcome nuisance vector is admissible](hyp:he), then
[the sum of its gamma-weighted outcome-band contrasts over all nonterminal intervals and their regular bands is square-integrable under the observation law](goal). -/
lemma fitted_continuous_gamma_contJ_block_memLp [Fintype Z]
    (M : LatentIVModel Ω X Z) (L : LevelData Z X) (e : NuisanceCont L)
    (he : ContAdmissible M L e) :
    MemLp (fun o : Obs X Z => ∑ k ∈ Finset.range L.K,
      ∑ j ∈ Finset.Icc 1 (L.l k), regularValue e.gamma k j o.1 *
        contJ L e k (j-1) o.1) 2 (observationLaw M) := by
  apply memLp_finsetSum
  intro k hk
  apply memLp_finsetSum
  intro j hj
  have hg : k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k :=
    ⟨(Finset.mem_range.mp hk).le, Finset.mem_Icc.mp hj⟩
  simpa only [regularValue, dif_pos hg] using
    fitted_continuous_gamma_contJ_memLp M L e he ⟨(k,j), hg⟩ k (j-1)

-- @node: encoded_continuous_gamma_contJ_block_sq_tendsto_probability_zero
/-- Suppose [the true continuous-outcome nuisance vector is admissible](hyp:he0),
[every fitted nuisance vector satisfies the clipping restrictions](hyp:hclip),
[every fitted share vector lies in the simplex](hyp:hshares), and
[every encoded fitted component is measurable](hyp:hm).
If [the encoded components satisfy the finite nuisance rates relative to truth](hyp:hr), then
[the observation-law integrated squared error of the entire gamma-weighted outcome-band block, summed over nonterminal intervals and regular bands and evaluated at sample sizes twice n plus two, converges in probability to zero](goal). -/
lemma encoded_continuous_gamma_contJ_block_sq_tendsto_probability_zero [Fintype Z]
    (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n t, ContClipping M L (eh n t))
    (hshares : ∀ n t, ContFittedSharesSimplex L (eh n t))
    (hm : ∀ n t d, Measurable (contComponent M L (eh n t) d))
    (hr : FiniteNuisanceRates M μ (fun n t => contComponent M L (eh n t))
      (contComponent M L (trueNuisance M L))) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ o : Obs X Z,
        ((∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
          regularValue (eh (2*(n+1)) t).gamma k j o.1 *
            contJ L (eh (2*(n+1)) t) k (j-1) o.1) -
          ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
            regularValue (trueNuisance M L).gamma k j o.1 *
              contJ L (trueNuisance M L) k (j-1) o.1) ^ 2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  let er := fun n t => restrictContShares L (eh n t)
  have her n t : ContAdmissible M L (er n t) :=
    restrictContShares_admissible_of_encoded_clipping M L (eh n t)
      (hclip n t) (hshares n t) (hm n t)
  let F := fun (k j n : ℕ) (t : A) (o : Obs X Z) =>
    regularValue (er (2*(n+1)) t).gamma k j o.1 *
      contJ L (er (2*(n+1)) t) k (j-1) o.1 -
    regularValue (trueNuisance M L).gamma k j o.1 *
      contJ L (trueNuisance M L) k (j-1) o.1
  have hF k j n t (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k) :
      MemLp (F k j n t) 2 (observationLaw M) := by
    have hg : k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k := ⟨hk.le, hj⟩
    convert
      (fitted_continuous_gamma_contJ_memLp M L (er (2*(n+1)) t) (her (2*(n+1)) t)
        ⟨(k,j), hg⟩ k (j-1)).sub
      (fitted_continuous_gamma_contJ_memLp M L _ he0 ⟨(k,j), hg⟩ k (j-1)) using 1
    funext o
    simp only [F, regularValue, dif_pos hg, Pi.sub_apply]
  have hs := dml_finset_sum_sq_tendsto_probability_zero μ (observationLaw M)
    (Finset.range L.K) (fun k n t o => ∑ j ∈ Finset.Icc 1 (L.l k), F k j n t o)
    (fun k hk n t => memLp_finsetSum _
      (fun j hj => hF k j n t (Finset.mem_range.mp hk) (Finset.mem_Icc.mp hj))) (by
      intro k hk
      apply dml_finset_sum_sq_tendsto_probability_zero μ (observationLaw M)
        (Finset.Icc 1 (L.l k)) (F k)
        (fun j hj n t => hF k j n t (Finset.mem_range.mp hk) (Finset.mem_Icc.mp hj))
      intro j hj
      have hg : k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k :=
        ⟨(Finset.mem_range.mp hk).le, Finset.mem_Icc.mp hj⟩
      simpa only [F, regularValue, dif_pos hg, er, restrictContShares, contJ] using
        encoded_continuous_gamma_contJ_sq_tendsto_probability_zero
          M μ L he0 eh hclip hshares hm hr ⟨(k,j), hg⟩ k (j-1))
  simpa only [F, er, restrictContShares, regularValue, contJ,
    Finset.sum_sub_distrib] using hs

-- The L2 norm is the square root of the assembled nonnegative energy.
-- @node: encoded_continuous_gamma_contJ_block_l2_tendsto_probability_zero
/-- Suppose [the true continuous-outcome nuisance vector is admissible](hyp:he0),
[every fitted nuisance vector satisfies the clipping restrictions](hyp:hclip),
[every fitted share vector lies in the simplex](hyp:hshares), and
[every encoded fitted component is measurable](hyp:hm).
If [the encoded components satisfy the finite nuisance rates relative to truth](hyp:hr), then
[the observation-law L2 error of the entire gamma-weighted outcome-band block, summed over nonterminal intervals and regular bands and evaluated at sample sizes twice n plus two, converges in probability to zero](goal). -/
lemma encoded_continuous_gamma_contJ_block_l2_tendsto_probability_zero [Fintype Z]
    (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n t, ContClipping M L (eh n t))
    (hshares : ∀ n t, ContFittedSharesSimplex L (eh n t))
    (hm : ∀ n t d, Measurable (contComponent M L (eh n t) d))
    (hr : FiniteNuisanceRates M μ (fun n t => contComponent M L (eh n t))
      (contComponent M L (trueNuisance M L))) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => Real.sqrt (∫ o : Obs X Z,
        ((∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
          regularValue (eh (2*(n+1)) t).gamma k j o.1 *
            contJ L (eh (2*(n+1)) t) k (j-1) o.1) -
          ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
            regularValue (trueNuisance M L).gamma k j o.1 *
              contJ L (trueNuisance M L) k (j-1) o.1) ^ 2
        ∂observationLaw M)) atTop (fun _ _ => 0) := by
  have hs := encoded_continuous_gamma_contJ_block_sq_tendsto_probability_zero
    M μ L he0 eh hclip hshares hm hr
  have hcont : Continuous (fun t : ℝ => Real.sqrt t) := by fun_prop
  simpa only [Real.sqrt_zero] using
    Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt hcont.continuousAt hs

end Papers.TbsPrteOptimalTransport

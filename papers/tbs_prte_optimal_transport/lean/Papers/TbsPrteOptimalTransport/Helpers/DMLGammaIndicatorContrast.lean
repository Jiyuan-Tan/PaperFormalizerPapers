module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLChangingIndicatorRegressions
/-! L2 regularity and convergence of the paired boundary indicator residual in continuous DML.
The two sides use the same fitted gamma and retain the structural zero baseline. -/
public section
set_option linter.unnecessarySimpa false
set_option linter.unreachableTactic false
set_option linter.unusedFintypeInType false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]

-- @node: fitted_continuous_gamma_IFM_memLp
/-- If [the continuous nuisances are admissible](hyp:he), [the denominator bound is positive](hyp:hc), [all positive-level baseline probabilities are at least that bound almost everywhere](hyp:hden), and [the population level is nonterminal](hyp:hk), then [the gamma-weighted upper or lower inverse-probability-weighted outcome-threshold indicator residual is square integrable under the observation law](goal). -/
lemma fitted_continuous_gamma_IFM_memLp [Fintype Z]
    (M : LatentIVModel Ω X Z) (L : LevelData Z X) (e : NuisanceCont L)
    (he : ContAdmissible M L e) (c : ℝ) (hc : 0 < c)
    (hden : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (g : RegularIndex L) (plus : Bool) (k j : ℕ) (hk : k < L.K) :
    MemLp (fun o : Obs X Z => e.gamma g o.1 * IFM M L e plus k j o)
      2 (observationLaw M) := by
  classical
  have hg : Measurable (e.gamma g) := by
    rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hm, _⟩
    exact hm g
  have hgb : ∀ᵐ x ∂xLaw M, |e.gamma g x| ≤ 1 := by
    rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hb, _⟩
    filter_upwards [hb g] with x hx
    simpa only [abs_of_nonneg hx.1] using hx.2
  have hJ : (Measurable (boundaryValue e.Mplus k j) ∧
      ∀ᵐ x ∂xLaw M, |boundaryValue e.Mplus k j x| ≤ 1) ∧
      (Measurable (minusBoundaryValue e.Mminus k j) ∧
      ∀ᵐ x ∂xLaw M, |minusBoundaryValue e.Mminus k j x| ≤ 1) := by
    rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hp, hpm, hn, hnm, _⟩
    constructor
    · unfold boundaryValue
      split_ifs with hj hlast
      · refine ⟨by first | fun_prop | exact hpm _, ?_⟩
        filter_upwards [hp ⟨(k,j), hj⟩] with x hx
        simpa only [abs_of_nonneg hx.1] using hx.2
      · exact ⟨measurable_const, Eventually.of_forall (by simp)⟩
      · exact ⟨measurable_const, Eventually.of_forall (by simp)⟩
    · unfold minusBoundaryValue
      split_ifs with hj hlast
      · refine ⟨by first | fun_prop | exact hnm _, ?_⟩
        filter_upwards [hn ⟨(k,j), hj⟩] with x hx
        simpa only [abs_of_nonneg hx.1] using hx.2
      · exact ⟨measurable_const, Eventually.of_forall (by simp)⟩
      · exact ⟨measurable_const, Eventually.of_forall (by simp)⟩
  have hside (i : PositiveIndex L.K) (J : X → ℝ) (hJ : Measurable J)
      (hJb : ∀ᵐ x ∂xLaw M, |J x| ≤ 1) :
      MemLp (fun o : Obs X Z => e.gamma g o.1 *
        (indicator (o.2.1 ∈ L.S i.val) * o.2.2.1 / e.piLev i o.1 *
          (indicator (o.2.2.2 ≤ nuValue M e k j o.1) - J o.1)))
        2 (observationLaw M) := by
    let f : X × ℝ → ℝ := fun p => e.gamma g p.1 *
      (indicator (p.2 ≤ nuValue M e k j p.1) - J p.1)
    have hf : Measurable f := by fun_prop
    have hp : Measurable (e.piLev i) := by
      rcases he with ⟨_, _, _, _, _, hm, _⟩
      exact hm i
    have hbound : ∀ᵐ x ∂xLaw M, ∀ y, |f (x,y)| ≤ 2 := by
      filter_upwards [hgb, hJb] with x hg hJ
      intro y
      have hy : |indicator (y ≤ nuValue M e k j x)| ≤ 1 := by
        unfold indicator
        split_ifs <;> norm_num
      dsimp only [f]
      rw [abs_mul]
      exact (mul_le_mul hg ((abs_sub _ _).trans (add_le_add hy hJ))
        (abs_nonneg _) zero_le_one).trans (by norm_num)
    have hs := observationLaw_selected_memLp M L i.val f hf (e.piLev i) hp
      c 2 hc (hden i) hbound
    convert hs using 1
    funext o
    dsimp only [f]
    ring
  cases plus with
  | true =>
    have hi : 1 ≤ k+1 ∧ k+1 ≤ L.K := by omega
    simpa only [IFM, Bool.not_true, Bool.false_and, Bool.false_eq_true, false_and,
      if_false, if_true, positiveValue, dif_pos hi] using
      hside ⟨k+1, hi⟩ (boundaryValue e.Mplus k j) hJ.1.1 hJ.1.2
  | false =>
    by_cases hk0 : k = 0
    · subst k
      simp only [IFM, Bool.not_false, beq_self_eq_true, Bool.and_self, and_self, if_true, mul_zero]
      exact MemLp.zero
    · have hi : 1 ≤ k ∧ k ≤ L.K := by omega
      simpa only [IFM, Bool.not_false, Bool.true_and, true_and, beq_iff_eq, hk0,
        if_false, Bool.false_eq_true, positiveValue, dif_pos hi] using
        hside ⟨k, hi⟩ (minusBoundaryValue e.Mminus k j) hJ.2.1 hJ.2.2

-- @node: encoded_continuous_gamma_minus_IFM_all_levels_sq_tendsto_probability_zero
/-- Assume [admissibility of the true nuisances](hyp:he0), [clipping of fitted nuisances](hyp:hclip), [nonnegative fitted shares summing to one](hyp:hshares), [measurability of encoded fitted components](hyp:hm), [bounded treated-outcome densities near the band boundaries](hyp:hd), and [componentwise L2 errors of smaller order in probability than the inverse fourth root of sample size](hyp:hr). Under [baseline overlap](hyp:hov) and [overlap-based fitted denominator clipping](hyp:hden), for [any nonterminal population level, including zero](hyp:hk), [the observation-integrated squared error of the gamma-weighted lower indicator residual converges in probability to zero along sample sizes twice one plus the index](goal). -/
lemma encoded_continuous_gamma_minus_IFM_all_levels_sq_tendsto_probability_zero
    [Fintype Z]
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
    (hden : ∀ n t, ContDenominatorsClipped L (eh n t) cpi)
    (g : RegularIndex L) (k j : ℕ) (hk : k < L.K) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ o : Obs X Z,
        ((eh (2 * (n + 1)) t).gamma g o.1 *
            IFM M L (eh (2 * (n + 1)) t) false k j o -
          (trueNuisance M L).gamma g o.1 *
            IFM M L (trueNuisance M L) false k j o) ^ 2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  by_cases hk0 : k = 0
  · subst k
    -- The baseline minus residual is structurally absent from the score.
    simp only [IFM, Bool.not_false, beq_self_eq_true, Bool.and_self,
      if_true, mul_zero, sub_self, zero_pow (by norm_num : 2 ≠ 0), integral_zero]
    rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm]
    intro eps heps
    simpa [not_le_of_gt heps] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (𝓝 0))
  · exact encoded_continuous_gamma_minus_IFM_sq_tendsto_probability_zero
      M μ L he0 eh hclip hshares hm hd hr cpi hov hden g k j (by omega) hk

-- @node: encoded_continuous_gamma_IFM_contrast_sq_tendsto_probability_zero
/-- Suppose [the true nuisances are admissible](hyp:he0), [the fitted nuisances are clipped](hyp:hclip), [fitted shares are nonnegative and sum to one](hyp:hshares), [encoded fitted components are measurable](hyp:hm), [treated-outcome densities are bounded near band boundaries](hyp:hd), and [componentwise L2 errors are of smaller order in probability than the inverse fourth root of sample size](hyp:hr). Given [baseline overlap](hyp:hov), [overlap-based fitted denominator clipping](hyp:hden), and [a nonterminal population level](hyp:hk), [the observation-integrated squared error of gamma times the upper-minus-lower indicator residual converges in probability to zero along sample sizes twice one plus the index](goal). -/
lemma encoded_continuous_gamma_IFM_contrast_sq_tendsto_probability_zero
    [Fintype Z]
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
    (hden : ∀ n t, ContDenominatorsClipped L (eh n t) cpi)
    (g : RegularIndex L) (k j : ℕ) (hk : k < L.K) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ o : Obs X Z,
        ((eh (2 * (n + 1)) t).gamma g o.1 *
            (IFM M L (eh (2 * (n + 1)) t) true k j o -
              IFM M L (eh (2 * (n + 1)) t) false k j o) -
          (trueNuisance M L).gamma g o.1 *
            (IFM M L (trueNuisance M L) true k j o -
              IFM M L (trueNuisance M L) false k j o)) ^ 2
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
    have hi := hov.2 x i.val i.property.1 i.property.2
    change cpi / 2 ≤ (levelSetProb M L).1 i.val x
    linarith [hov.1]
  let r := fun (plus : Bool) n t (o : Obs X Z) =>
    (er (2 * (n + 1)) t).gamma g o.1 *
      IFM M L (er (2 * (n + 1)) t) plus k j o -
    (trueNuisance M L).gamma g o.1 * IFM M L (trueNuisance M L) plus k j o
  have hmem plus n t : MemLp (r plus n t) 2 (observationLaw M) :=
    (fitted_continuous_gamma_IFM_memLp M L _ (her _ t) (cpi / 2) hc
      (fun i => Eventually.of_forall (fun x => (hden _ t).1 i x |>.1)) g plus k j hk).sub
    (fitted_continuous_gamma_IFM_memLp M L _ he0 (cpi / 2) hc hden0 g plus k j hk)
  have hz : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun _ : ℕ => fun _ : A => (0 : ℝ)) atTop (fun _ _ => 0) := by
    rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm]
    intro eps heps
    simpa [not_le_of_gt heps] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (𝓝 0))
  have hs := dml_three_term_sq_tendsto_probability_zero μ (observationLaw M)
    (r true) (fun _ _ _ => 0) (r false) (hmem true)
    (fun _ _ => MemLp.zero) (hmem false)
    (encoded_continuous_gamma_plus_IFM_sq_tendsto_probability_zero
      M μ L he0 eh hclip hshares hm hd hr cpi hov hden g k j hk)
    (by simpa using hz)
    (encoded_continuous_gamma_minus_IFM_all_levels_sq_tendsto_probability_zero
      M μ L he0 eh hclip hshares hm hd hr cpi hov hden g k j hk)
  convert hs using 1
  funext n t
  congr 1
  funext o
  simp only [r, er, IFM, nuValue, restrictContShares]
  ring

-- Sum the paired boundary residuals over nonterminal population levels.
-- @node: fitted_continuous_gamma_IFM_block_memLp
/-- With [admissible continuous nuisances](hyp:he), [a positive denominator bound](hyp:hc), and [positive-level baseline probabilities bounded below by it almost everywhere](hyp:hden), [the sum over nonterminal levels and regular boundaries of gamma times the upper-minus-lower indicator residual is square integrable](goal). -/
lemma fitted_continuous_gamma_IFM_block_memLp [Fintype Z]
    (M : LatentIVModel Ω X Z) (L : LevelData Z X) (e : NuisanceCont L)
    (he : ContAdmissible M L e) (c : ℝ) (hc : 0 < c)
    (hden : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x) :
    MemLp (fun o : Obs X Z => ∑ k ∈ Finset.range L.K,
      ∑ j ∈ Finset.Icc 1 (L.l k), regularValue e.gamma k j o.1 *
        (IFM M L e true k j o - IFM M L e false k j o))
      2 (observationLaw M) := by
  apply memLp_finsetSum
  intro k hk
  apply memLp_finsetSum
  intro j hj
  have hk' := Finset.mem_range.mp hk
  have hg : k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k :=
    ⟨hk'.le, Finset.mem_Icc.mp hj⟩
  have hplus := fitted_continuous_gamma_IFM_memLp M L e he c hc hden
    ⟨(k,j), hg⟩ true k j hk'
  have hminus := fitted_continuous_gamma_IFM_memLp M L e he c hc hden
    ⟨(k,j), hg⟩ false k j hk'
  convert hplus.sub hminus using 1
  funext o
  simp only [regularValue, dif_pos hg, Pi.sub_apply]
  ring

-- @node: encoded_continuous_gamma_IFM_block_sq_tendsto_probability_zero
/-- Under [admissible true nuisances](hyp:he0), [clipped fitted nuisances](hyp:hclip), [nonnegative fitted shares summing to one](hyp:hshares), [measurable encoded fitted components](hyp:hm), [bounded treated-outcome densities near band boundaries](hyp:hd), and [componentwise L2 errors of smaller order in probability than the inverse fourth root of sample size](hyp:hr), assume [baseline overlap](hyp:hov) and [overlap-based fitted denominator clipping](hyp:hden). Then [the observation-integrated squared error of the gamma-weighted upper-minus-lower indicator-residual block, summed over nonterminal levels and regular boundaries, converges in probability to zero along sample sizes twice one plus the index](goal). -/
lemma encoded_continuous_gamma_IFM_block_sq_tendsto_probability_zero [Fintype Z]
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
            (IFM M L (eh (2*(n+1)) t) true k j o -
              IFM M L (eh (2*(n+1)) t) false k j o)) -
          ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
            regularValue (trueNuisance M L).gamma k j o.1 *
              (IFM M L (trueNuisance M L) true k j o -
                IFM M L (trueNuisance M L) false k j o)) ^ 2
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
  let F := fun (k j n : ℕ) (t : A) (o : Obs X Z) =>
    regularValue (er (2*(n+1)) t).gamma k j o.1 *
      (IFM M L (er (2*(n+1)) t) true k j o -
        IFM M L (er (2*(n+1)) t) false k j o) -
    regularValue (trueNuisance M L).gamma k j o.1 *
      (IFM M L (trueNuisance M L) true k j o -
        IFM M L (trueNuisance M L) false k j o)
  have hF k j n t (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k) :
      MemLp (F k j n t) 2 (observationLaw M) := by
    have hg : k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k := ⟨hk.le, hj⟩
    have hs (e : NuisanceCont L) (he : ContAdmissible M L e)
        (hde : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, cpi / 2 ≤ e.piLev i x) :=
      (fitted_continuous_gamma_IFM_memLp M L e he (cpi / 2) hc hde
        ⟨(k,j), hg⟩ true k j hk).sub
      (fitted_continuous_gamma_IFM_memLp M L e he (cpi / 2) hc hde
        ⟨(k,j), hg⟩ false k j hk)
    convert (hs (er (2*(n+1)) t) (her (2*(n+1)) t)
      (fun i => Eventually.of_forall
        (fun x => (hden (2*(n+1)) t).1 i x |>.1))).sub
      (hs (trueNuisance M L) he0 hden0) using 1
    funext o
    simp only [F, regularValue, dif_pos hg, Pi.sub_apply]
    ring
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
      simpa only [F, regularValue, dif_pos hg, er, restrictContShares, IFM, nuValue] using
        encoded_continuous_gamma_IFM_contrast_sq_tendsto_probability_zero
          M μ L he0 eh hclip hshares hm hd hr cpi hov hden
          ⟨(k,j), hg⟩ k j (Finset.mem_range.mp hk))
  simpa only [F, er, restrictContShares, regularValue, IFM, nuValue,
    Finset.sum_sub_distrib] using hs

-- @node: encoded_continuous_gamma_IFM_block_l2_tendsto_probability_zero
/-- If [the true nuisances are admissible](hyp:he0), [fitted nuisances obey clipping](hyp:hclip), [their shares are nonnegative and sum to one](hyp:hshares), [their encoded components are measurable](hyp:hm), [treated-outcome densities are bounded near band boundaries](hyp:hd), and [componentwise L2 errors are of smaller order in probability than the inverse fourth root of sample size](hyp:hr), then, with [baseline overlap](hyp:hov) and [overlap-based fitted denominator clipping](hyp:hden), [the L2 distance between fitted and true gamma-weighted indicator-residual blocks converges in probability to zero along sample sizes twice one plus the index](goal). -/
lemma encoded_continuous_gamma_IFM_block_l2_tendsto_probability_zero [Fintype Z]
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
        ((∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
          regularValue (eh (2*(n+1)) t).gamma k j o.1 *
            (IFM M L (eh (2*(n+1)) t) true k j o -
              IFM M L (eh (2*(n+1)) t) false k j o)) -
          ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
            regularValue (trueNuisance M L).gamma k j o.1 *
              (IFM M L (trueNuisance M L) true k j o -
                IFM M L (trueNuisance M L) false k j o)) ^ 2
        ∂observationLaw M)) atTop (fun _ _ => 0) := by
  have hs := encoded_continuous_gamma_IFM_block_sq_tendsto_probability_zero
    M μ L he0 eh hclip hshares hm hd hr cpi hov hden
  have hcont : Continuous (fun t : ℝ => Real.sqrt t) := by fun_prop
  simpa only [Real.sqrt_zero] using
    Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt hcont.continuousAt hs

end Papers.TbsPrteOptimalTransport

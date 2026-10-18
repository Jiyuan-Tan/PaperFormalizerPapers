module
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousBandJointDerivative
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousBandDirectionRegularity
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousFullAdmissibleDerivative
/-! Boundary-indicator regression telescopes with all other continuous nuisances moving jointly. -/
public section
set_option linter.unusedSectionVars false
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

-- Selection outside the estimated coordinates is the fixed zero direction.
-- @node: continuous_band_indicator_selected_direction_regular
/-- If [a continuous nuisance direction is admissible](hyp:hd), then [the upper- and
lower-level indicator-regression directions, extended by zero outside their estimated
coordinates, are measurable at every pair of indices and share a nonnegative finite
almost-sure absolute bound under the covariate law](goal). -/
lemma continuous_band_indicator_selected_direction_regular (L : LevelData Z X)
    (eta del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl eta) (.inl del)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ k j,
      Measurable (meanValue del.Mplus k j) ∧
      Measurable (minusMeanValue del.Mminus k j) ∧
      (∀ᵐ x ∂xLaw M, |meanValue del.Mplus k j x| ≤ D) ∧
      (∀ᵐ x ∂xLaw M, |minusMeanValue del.Mminus k j x| ≤ D) := by
  obtain ⟨P, hP, hp⟩ := continuous_band_plus_indicator_direction_regular M L eta del hd
  obtain ⟨N, hN, hn⟩ := continuous_band_minus_indicator_direction_regular M L eta del hd
  refine ⟨P + N, by positivity, ?_⟩
  intro k j
  have hpm : Measurable (meanValue del.Mplus k j) := by
    unfold meanValue
    split_ifs with ha
    · exact (hp _).1
    · fun_prop
  have hnm : Measurable (minusMeanValue del.Mminus k j) := by
    unfold minusMeanValue
    split_ifs with ha
    · exact (hn _).1
    · fun_prop
  refine ⟨hpm, hnm, ?_, ?_⟩
  · unfold meanValue
    split_ifs with ha
    · filter_upwards [(hp ⟨(k,j),ha⟩).2] with x hx
      simp only [Real.norm_eq_abs] at hx
      linarith
    · exact Eventually.of_forall fun _ => by simp; positivity
  · unfold minusMeanValue
    split_ifs with ha
    · filter_upwards [(hn ⟨(k,j),ha⟩).2] with x hx
      simp only [Real.norm_eq_abs] at hx
      linarith
    · exact Eventually.of_forall fun _ => by simp; positivity

-- The quantile coefficients retain their moving values in both paths.
-- @node: continuous_band_indicator_coefficient_difference
/-- When only the two boundary-indicator regressions receive affine perturbations,
[the upper propensity coefficient changes by time times the lower quantile-weighted
upper-level indicator direction minus its upper-boundary counterpart, the lower
propensity coefficient changes by the negative of the analogous lower-level expression,
and the band outcome contrast is unchanged](goal). -/
lemma continuous_band_indicator_coefficient_difference (L : LevelData Z X)
    (e : NuisanceCont L) (dp : IndicatorIndex L → X → ℝ)
    (dm : MinusIndicatorIndex L → X → ℝ) (t : ℝ) (k j : ℕ) (x : X) :
    let et := {e with
      Mplus := fun a x => e.Mplus a x + t * dp a x
      Mminus := fun a x => e.Mminus a x + t * dm a x}
    alphaHigh M L et k j x - alphaHigh M L e k j x =
      t * (nuValue M e k j x * meanValue dp k j x -
        nuValue M e k (j+1) x * meanValue dp k (j+1) x) ∧
    alphaLow M L et k j x - alphaLow M L e k j x =
      -t * (nuValue M e k j x * minusMeanValue dm k j x -
        nuValue M e k (j+1) x * minusMeanValue dm k (j+1) x) ∧
    contJ L et k j x = contJ L e k j x := by
  dsimp only
  refine ⟨?_, ?_, rfl⟩ <;>
    simp only [alphaHigh, alphaLow, boundaryValue_affine_path,
      minusBoundaryValue_affine_path, nuValue] <;> split_ifs <;> ring

-- @node: continuous_admissible_nuValue_measurable
/-- If [the continuous nuisance functions are admissible](hyp:he), then
[the selected quantile boundary is measurable at every pair of indices, including
fixed endpoints and indices outside the estimated family](goal). -/
@[fun_prop] lemma continuous_admissible_nuValue_measurable (L : LevelData Z X)
    (e : NuisanceCont L) (he : ContAdmissible M L e) (k j : ℕ) :
    Measurable (nuValue M e k j) := by
  first | fun_prop | skip
  rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hn, _⟩
  unfold nuValue
  split_ifs
  · fun_prop
  · exact hn _
  · fun_prop

-- Includes both fixed endpoints and coordinates outside the estimated family.
-- @node: continuous_admissible_nuValue_abs_bound
/-- If [the continuous nuisance functions are admissible](hyp:he), then
[the absolute value of the selected quantile boundary is at most the sum of the
absolute outcome endpoints almost surely under the covariate law, at every pair of indices](goal). -/
lemma continuous_admissible_nuValue_abs_bound (L : LevelData Z X)
    (e : NuisanceCont L) (he : ContAdmissible M L e) (k j : ℕ) :
    ∀ᵐ x ∂xLaw M, |nuValue M e k j x| ≤ |M.yMin| + |M.yMax| := by
  rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hn, _⟩
  unfold nuValue
  split_ifs with hj ha
  · exact Eventually.of_forall fun _ => le_add_of_nonneg_right (abs_nonneg _)
  · filter_upwards [hn ⟨(k,j),ha⟩] with x hx
    apply (abs_le.mpr ⟨?_, ?_⟩)
    · have := neg_abs_le M.yMin
      have := abs_nonneg M.yMax
      linarith [hx.1]
    · have := le_abs_self M.yMax
      have := abs_nonneg M.yMin
      linarith [hx.2]
  · exact Eventually.of_forall fun _ => le_add_of_nonneg_left (abs_nonneg _)

-- This is a difference of actual product scores, rather than an isolated
-- coordinate derivative. All other coordinates retain their full affine path.
-- @node: population_continuous_band_indicator_joint_telescope_orthogonality
/-- With [baseline assignment overlap at the specified constant](hyp:hov),
[an admissible nuisance direction at the truth](hyp:hd), and [a band index below the
level's band count](hyp:hj), [the difference between the band product score on the full
affine path and the score with only indicator regressions held at their true values
has population derivative zero at time zero and is integrable throughout some
neighborhood of zero](goal). -/
lemma population_continuous_band_indicator_joint_telescope_orthogonality
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del))
    (k : Fin L.K) (j : ℕ) (hj : j < L.l k) :
    let e := fun t : ℝ => trueNuisance M L + t • del
    let b := fun t => {e t with
      Mplus := (trueNuisance M L).Mplus
      Mminus := (trueNuisance M L).Mminus}
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z,
      psiProd M phi dphi L (e t) k (j+1) o - psiProd M phi dphi L (b t) k (j+1) o
        ∂observationLaw M) 0 0 ∧
    (∀ᶠ t : ℝ in 𝓝 0, Integrable (fun o : Obs X Z =>
      psiProd M phi dphi L (e t) k (j+1) o - psiProd M phi dphi L (b t) k (j+1) o)
        (observationLaw M)) := by
  dsimp only
  let e := fun t : ℝ => trueNuisance M L + t • del
  let b := fun t => {e t with
      Mplus := (trueNuisance M L).Mplus
      Mminus := (trueNuisance M L).Mminus}
  obtain ⟨D, hD, hdir⟩ := continuous_band_indicator_selected_direction_regular M L _ del hd
  obtain ⟨C, hC, hpi⟩ := continuous_assignment_direction_regular M L _ del hd
  obtain ⟨G, hG, hg⟩ := continuous_regular_weight_direction_regular M L _ del hd
  obtain ⟨r, hr, hpath⟩ := hd.admissible
  have hi : 1 ≤ k.val+1 ∧ k.val+1 ≤ L.K := by omega
  have ha : k.val ≤ L.K ∧ 1 ≤ j+1 ∧ j+1 ≤ L.l k := by omega
  let a : RegularIndex L := ⟨(k,j+1),ha⟩
  let vp : ℝ → X → ℝ := fun t x => regularValue (e t).gamma k (j+1) x *
    (positiveValue (e t).pLev (k+1) x * (t * (nuValue M (e t) k j x * meanValue del.Mplus k j x -
      nuValue M (e t) k (j+1) x * meanValue del.Mplus k (j+1) x)))
  let vm : ℝ → X → ℝ := fun t x => regularValue (e t).gamma k (j+1) x *
    (if k.val = 0 then 0 else positiveValue (e t).pLev k x *
      (t * (nuValue M (e t) k j x * minusMeanValue del.Mminus k j x -
      nuValue M (e t) k (j+1) x * minusMeanValue del.Mminus k (j+1) x)))
  let B := |M.yMin| + |M.yMax|
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  let v : ℝ → X → ℝ := fun _ _ => 0
  have hcoef (t : ℝ) (x : X) :=
    continuous_band_indicator_coefficient_difference M L (b t) del.Mplus del.Mminus t k j x
  have het (t : ℝ) : {b t with
      Mplus := fun a x => (b t).Mplus a x + t * del.Mplus a x
      Mminus := fun a x => (b t).Mminus a x + t * del.Mminus a x} = e t := rfl
  simp only [het] at hcoef
  have hlocal : ∀ᶠ t : ℝ in 𝓝 0,
      Integrable (fun o : Obs X Z => psiProd M phi dphi L (e t) k (j+1) o -
        psiProd M phi dphi L (b t) k (j+1) o) (observationLaw M) ∧
      |∫ o : Obs X Z, psiProd M phi dphi L (e t) k (j+1) o -
        psiProd M phi dphi L (b t) k (j+1) o ∂observationLaw M| ≤
        (2 * ((2*B*D) * C / (cpi/2)) + 0 * G) * t^2 := by
    filter_upwards [continuous_assignment_path_uniform_lower_bound M L cpi hov del hd,
      continuousAt_id.abs.eventually_lt_const (by simpa using hr)] with t hclip ht
    have had := hpath t ht
    have hpm := had.2.2.2.1
    have hpim := had.2.2.2.2.2.1
    have hgm := had.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hgb := had.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hpb (i : ℕ) : ∀ᵐ x ∂xLaw M, |positiveValue (e t).pLev i x| ≤ 1 := by
      unfold positiveValue
      split_ifs with hh
      · filter_upwards [had.2.2.1 ⟨i,hh⟩] with x hx
        rw [abs_of_nonneg hx.1]; exact hx.2
      · exact Eventually.of_forall fun _ => by norm_num
    have hps (i : ℕ) : Measurable (positiveValue (e t).pLev i) := by
      unfold positiveValue
      split_ifs
      · exact hpm _
      · fun_prop
    have hgs : Measurable (regularValue (e t).gamma k (j+1)) := by
      change Measurable (fun x => regularValue (e t).gamma k (j+1) x)
      simpa only [regularValue, dif_pos ha] using hgm a
    have hgw : ∀ᵐ x ∂xLaw M, |regularValue (e t).gamma k (j+1) x| ≤ 1 := by
      filter_upwards [hgb a] with x hx
      simp only [regularValue, dif_pos ha]
      rw [abs_of_nonneg hx.1]; exact hx.2
    have hdpm := (hdir k j).1
    have hdnm := (hdir k j).2.1
    have hdpnm := (hdir k (j+1)).1
    have hdmnm := (hdir k (j+1)).2.1
    have hnmeas i := continuous_admissible_nuValue_measurable M L (e t) had k i
    have hvm : Measurable (vm t) := by
      dsimp only [vm]
      split_ifs <;> fun_prop
    have hvpm : Measurable (vp t) := by dsimp only [vp]; fun_prop
    have hvmeas : Measurable (v t) := by dsimp only [v]; fun_prop
    have hnu i : ∀ᵐ x ∂xLaw M, |nuValue M (e t) k i x| ≤ B :=
      continuous_admissible_nuValue_abs_bound M L (e t) had k i
    have hdiffp : ∀ᵐ x ∂xLaw M,
        |nuValue M (e t) k j x * meanValue del.Mplus k j x -
          nuValue M (e t) k (j+1) x * meanValue del.Mplus k (j+1) x| ≤ 2*B*D := by
      filter_upwards [hnu j, hnu (j+1), (hdir k j).2.2.1,
        (hdir k (j+1)).2.2.1] with x ha hb hdp hdq
      calc
        _ ≤ |nuValue M (e t) k j x| * |meanValue del.Mplus k j x| +
          |nuValue M (e t) k (j+1) x| * |meanValue del.Mplus k (j+1) x| := by
          simpa only [abs_mul] using abs_sub
            (nuValue M (e t) k j x * meanValue del.Mplus k j x)
            (nuValue M (e t) k (j+1) x * meanValue del.Mplus k (j+1) x)
        _ ≤ B*D + B*D := by gcongr
        _ = _ := by ring
    have hdiffm : ∀ᵐ x ∂xLaw M,
        |nuValue M (e t) k j x * minusMeanValue del.Mminus k j x -
          nuValue M (e t) k (j+1) x * minusMeanValue del.Mminus k (j+1) x| ≤ 2*B*D := by
      filter_upwards [hnu j, hnu (j+1), (hdir k j).2.2.2,
        (hdir k (j+1)).2.2.2] with x ha hb hdp hdq
      calc
        _ ≤ |nuValue M (e t) k j x| * |minusMeanValue del.Mminus k j x| +
          |nuValue M (e t) k (j+1) x| * |minusMeanValue del.Mminus k (j+1) x| := by
          simpa only [abs_mul] using abs_sub
            (nuValue M (e t) k j x * minusMeanValue del.Mminus k j x)
            (nuValue M (e t) k (j+1) x * minusMeanValue del.Mminus k (j+1) x)
        _ ≤ B*D + B*D := by gcongr
        _ = _ := by ring
    have hBp : ∀ᵐ x ∂xLaw M, |vp t x| ≤ (2*B*D) * |t| := by
      filter_upwards [hgw, hpb (k+1), hdiffp] with x hx hp hdj
      simp only [vp, abs_mul]
      calc
        _ ≤ 1 * (1 * (|t| * (2*B*D))) := by gcongr
        _ = _ := by ring
    have hBm : ∀ᵐ x ∂xLaw M, |vm t x| ≤ (2*B*D) * |t| := by
      by_cases hk : k.val = 0
      · simp only [vm, hk, if_true, mul_zero, abs_zero]
        exact Eventually.of_forall fun _ => by positivity
      · filter_upwards [hgw, hpb k, hdiffm] with x hx hp hdj
        simp only [vm, if_neg hk, abs_mul]
        calc
          _ ≤ 1 * (1 * (|t| * (2*B*D))) := by gcongr
          _ = _ := by ring
    have hvb : ∀ᵐ x ∂xLaw M, |v t x| ≤ 0 * |t| := by
      exact Eventually.of_forall fun _ => by simp only [v, abs_zero, zero_mul, le_refl]
    apply population_continuous_band_joint_product_difference_bound M phi dphi L
      (e t) (b t) rfl rfl rfl rfl rfl rfl k j (vp t) (vm t)
      (c := cpi/2) (D := 2*B*D) (C := C) (t := t) (v := v t) (E := 0) (G := G)
    · intro x; simp only [vp, (hcoef t x).1]; rfl
    · intro x
      simp only [vm, (hcoef t x).2.1]
      change _ = regularValue (e t).gamma k (j+1) x *
        (if k.val = 0 then 0 else -positiveValue (e t).pLev k x *
          (-t * (nuValue M (e t) k j x * minusMeanValue del.Mminus k j x -
            nuValue M (e t) k (j+1) x * minusMeanValue del.Mminus k (j+1) x)))
      split_ifs <;> ring
    · exact hpim
    · exact hvpm
    · exact hvm
    · exact div_pos hov.1 (by norm_num)
    · positivity
    · exact hC
    · exact hclip
    · exact hBp
    · exact hBm
    · intro i hi1 hi2
      filter_upwards [(hpi ⟨i,hi1,hi2⟩).2] with x hx
      change |positiveValue (e t).piLev i x - _| ≤ C * |t|
      have hii : 1 ≤ i ∧ i ≤ L.K := ⟨hi1,hi2⟩
      simp only [positiveValue, dif_pos hii]
      change |((∑ z ∈ L.S i, instProb M z x) + t * del.piLev ⟨i,hi1,hi2⟩ x) - _| ≤ _
      simpa only [add_sub_cancel_left, abs_mul, mul_comm, Real.norm_eq_abs] using
        mul_le_mul_of_nonneg_left hx (abs_nonneg t)
    · rfl
    · intro x; simp only [v, (hcoef t x).2.2, sub_self]
    · exact hvmeas
    · exact hgs
    · positivity
    · exact hG
    · exact hvb
    · filter_upwards [(hg a).2] with x hx
      simp only [regularValue, dif_pos ha]
      change |gamma M L k (j+1) x - (gamma M L k (j+1) x + t * del.gamma a x)| ≤ _
      simpa only [sub_add_cancel_left, abs_neg, abs_mul, mul_comm, Real.norm_eq_abs] using
        mul_le_mul_of_nonneg_left hx (abs_nonneg t)
  refine ⟨?_, hlocal.mono fun _ ht => ht.1⟩
  let f : ℝ → ℝ := fun t => ∫ o : Obs X Z,
    psiProd M phi dphi L (e t) k (j+1) o - psiProd M phi dphi L (b t) k (j+1) o
      ∂observationLaw M
  have hb0 : b 0 = e 0 := by
    dsimp only [b, e]
    rw [continuous_nuisance_path_zero]
  have hf0 : f 0 = 0 := by simp only [f, hb0, sub_self, integral_zero]
  have ho : (fun t => f t - f 0) =O[𝓝 0] (fun t : ℝ => t^2) := by
    apply Asymptotics.IsBigO.of_bound (2 * ((2*B*D) * C / (cpi/2)) + 0 * G)
    filter_upwards [hlocal] with t ht
    simpa only [hf0, sub_zero, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)] using ht.2
  apply HasDerivAt.of_isLittleO
  simpa only [smul_zero, sub_zero] using
    ho.trans_isLittleO (Asymptotics.isLittleO_pow_id (𝕜 := ℝ) (by norm_num : 1 < 2))

-- Full-interval and tail scores do not use boundary-indicator regressions.
-- @node: continuous_total_indicator_regression_difference
/-- For [a positive number of treatment levels](hyp:hK), [replacing the upper- and
lower-level indicator regressions changes the total continuous score by exactly the
sum of the corresponding regular-band product-score changes over all levels and bands](goal). -/
lemma continuous_total_indicator_regression_difference
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X) (hK : LevelCountPos L.K)
    (eta : NuisanceCont L) (jp : IndicatorIndex L → X → ℝ)
    (jm : MinusIndicatorIndex L → X → ℝ) (o : Obs X Z) :
    psiCont M phi dphi L hK o eta -
      psiCont M phi dphi L hK o {eta with Mplus := jp, Mminus := jm} =
      ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
        (psiProd M phi dphi L eta k j o -
          psiProd M phi dphi L {eta with Mplus := jp, Mminus := jm} k j o) := by
  have hf : ∀ k, psiFullProd L {eta with Mplus := jp, Mminus := jm} k o =
      psiFullProd L eta k o := fun _ => rfl
  simp only [psiCont, hf, add_sub_add_right_eq_sub, ← Finset.sum_sub_distrib,
    add_sub_add_left_eq_sub]

-- @node: continuous_total_indicator_regression_difference_integral
/-- For [a positive number of treatment levels](hyp:hK), if [each regular-band
product-score difference induced by replacing the indicator regressions is integrable](hyp:hi),
then [the resulting total continuous-score difference is integrable, and its population
mean is the sum of the population means of those band differences](goal). -/
lemma continuous_total_indicator_regression_difference_integral
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X) (hK : LevelCountPos L.K)
    (eta : NuisanceCont L) (jp : IndicatorIndex L → X → ℝ)
    (jm : MinusIndicatorIndex L → X → ℝ)
    (hi : ∀ k ∈ Finset.range L.K, ∀ j ∈ Finset.Icc 1 (L.l k),
      Integrable (fun o : Obs X Z => psiProd M phi dphi L eta k j o -
        psiProd M phi dphi L {eta with Mplus := jp, Mminus := jm} k j o)
          (observationLaw M)) :
    Integrable (fun o => psiCont M phi dphi L hK o eta -
      psiCont M phi dphi L hK o {eta with Mplus := jp, Mminus := jm}) (observationLaw M) ∧
    (∫ o, psiCont M phi dphi L hK o eta -
      psiCont M phi dphi L hK o {eta with Mplus := jp, Mminus := jm} ∂observationLaw M) =
      ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
        ∫ o, psiProd M phi dphi L eta k j o -
          psiProd M phi dphi L {eta with Mplus := jp, Mminus := jm} k j o
            ∂observationLaw M := by
  simp_rw [continuous_total_indicator_regression_difference]
  refine ⟨integrable_finsetSum _ (fun k hk => integrable_finsetSum _ (hi k hk)), ?_⟩
  rw [integral_finsetSum _ (fun k hk => integrable_finsetSum _ (hi k hk))]
  apply Finset.sum_congr rfl
  intro k hk
  exact integral_finsetSum _ (hi k hk)

-- Finiteness supplies a common neighborhood for all band differences.
-- @node: population_continuous_total_indicator_regression_telescope_orthogonality
/-- For [a positive number of treatment levels](hyp:hK), under [baseline assignment
overlap at the specified constant](hyp:hov) and [an admissible nuisance direction at
the truth](hyp:hd), [the difference between the total continuous score on the full affine
path and the score with indicator regressions held at their true values has population
derivative zero at time zero and is integrable throughout some neighborhood of zero](goal). -/
lemma population_continuous_total_indicator_regression_telescope_orthogonality
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X) (hK : LevelCountPos L.K)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del)) :
    let e := fun t : ℝ => trueNuisance M L + t • del
    let b := fun t => {e t with
      Mplus := (trueNuisance M L).Mplus
      Mminus := (trueNuisance M L).Mminus}
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z,
      psiCont M phi dphi L hK o (e t) - psiCont M phi dphi L hK o (b t)
        ∂observationLaw M) 0 0 ∧
    (∀ᶠ t : ℝ in 𝓝 0, Integrable (fun o : Obs X Z =>
      psiCont M phi dphi L hK o (e t) - psiCont M phi dphi L hK o (b t))
        (observationLaw M)) := by
  dsimp only
  let e := fun t : ℝ => trueNuisance M L + t • del
  let b := fun t => {e t with
    Mplus := (trueNuisance M L).Mplus
    Mminus := (trueNuisance M L).Mminus}
  have hband : ∀ k ∈ Finset.range L.K, ∀ j ∈ Finset.Icc 1 (L.l k),
      HasDerivAt (fun t : ℝ => ∫ o : Obs X Z,
        psiProd M phi dphi L (e t) k j o - psiProd M phi dphi L (b t) k j o
          ∂observationLaw M) 0 0 ∧
      (∀ᶠ t : ℝ in 𝓝 0, Integrable (fun o : Obs X Z =>
        psiProd M phi dphi L (e t) k j o - psiProd M phi dphi L (b t) k j o)
          (observationLaw M)) := by
    intro k hk j hj
    have hk' := Finset.mem_range.mp hk
    obtain ⟨hj1, hjl⟩ := Finset.mem_Icc.mp hj
    simpa only [Nat.sub_add_cancel hj1] using
      population_continuous_band_indicator_joint_telescope_orthogonality M phi dphi L
        cpi hov del hd ⟨k,hk'⟩ (j-1) (by change j-1 < L.l k; omega)
  have hi : ∀ᶠ t : ℝ in 𝓝 0, ∀ k ∈ Finset.range L.K,
      ∀ j ∈ Finset.Icc 1 (L.l k), Integrable (fun o : Obs X Z =>
        psiProd M phi dphi L (e t) k j o - psiProd M phi dphi L (b t) k j o)
          (observationLaw M) := by
    apply (Finset.eventually_all _).mpr
    intro k hk
    apply (Finset.eventually_all _).mpr
    intro j hj
    exact (hband k hk j hj).2
  have hmean : ∀ᶠ t : ℝ in 𝓝 0,
      Integrable (fun o : Obs X Z => psiCont M phi dphi L hK o (e t) -
        psiCont M phi dphi L hK o (b t)) (observationLaw M) ∧
      (∫ o : Obs X Z, psiCont M phi dphi L hK o (e t) -
        psiCont M phi dphi L hK o (b t) ∂observationLaw M) =
        ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
          ∫ o : Obs X Z, psiProd M phi dphi L (e t) k j o -
            psiProd M phi dphi L (b t) k j o ∂observationLaw M := by
    filter_upwards [hi] with t ht
    exact continuous_total_indicator_regression_difference_integral M phi dphi L hK
      (e t) (trueNuisance M L).Mplus (trueNuisance M L).Mminus ht
  have hsum : HasDerivAt (fun t : ℝ =>
      ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
        ∫ o : Obs X Z, psiProd M phi dphi L (e t) k j o -
          psiProd M phi dphi L (b t) k j o ∂observationLaw M) 0 0 := by
    have hk : ∀ k ∈ Finset.range L.K, HasDerivAt (fun t : ℝ =>
        ∑ j ∈ Finset.Icc 1 (L.l k), ∫ o : Obs X Z,
          psiProd M phi dphi L (e t) k j o - psiProd M phi dphi L (b t) k j o
            ∂observationLaw M) 0 0 := by
      intro k hk
      simpa only [Finset.sum_const_zero] using
        HasDerivAt.fun_sum (fun j hj => (hband k hk j hj).1)
    simpa only [Finset.sum_const_zero] using HasDerivAt.fun_sum hk
  exact ⟨hsum.congr_of_eventuallyEq (hmean.mono fun _ ht => ht.2),
    hmean.mono fun _ ht => ht.1⟩

end Papers.TbsPrteOptimalTransport

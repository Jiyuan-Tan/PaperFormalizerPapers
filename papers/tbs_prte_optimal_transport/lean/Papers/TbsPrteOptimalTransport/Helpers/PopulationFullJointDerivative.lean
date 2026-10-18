module
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationFullJointMean
/-! Integrated quadratic cancellation for simultaneous full-interval nuisance paths. -/
public section
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unreachableTactic false
set_option linter.unusedFintypeInType false
set_option linter.unusedTactic false
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

-- A local quadratic population remainder suffices; no interchange of derivatives
-- and integrals is needed.
-- @node: integral_local_quadratic_orthogonality
/-- If [the baseline function is integrable under a probability law](hyp:h0) and
[for all sufficiently small perturbations the function is almost everywhere
strongly measurable and its change from baseline is almost surely bounded by a
fixed constant times the squared perturbation](hyp:hlocal), [its population
integral has derivative zero at zero](goal). -/
lemma integral_local_quadratic_orthogonality {B : Type*} [MeasurableSpace B]
    (ν : Measure B) [IsProbabilityMeasure ν] (F : ℝ → B → ℝ) (C : ℝ)
    (h0 : Integrable (F 0) ν)
    (hlocal : ∀ᶠ t : ℝ in nhds 0, AEStronglyMeasurable (F t) ν ∧
      ∀ᵐ b ∂ν, |F t b - F 0 b| ≤ C * t ^ 2) :
    HasDerivAt (fun t : ℝ => ∫ b, F t b ∂ν) 0 0 := by
  have hbound : ∀ᶠ t : ℝ in nhds 0,
      |(∫ b, F t b ∂ν) - ∫ b, F 0 b ∂ν| ≤ C * t ^ 2 := by
    filter_upwards [hlocal] with t ht
    have hr : Integrable (fun b => F t b - F 0 b) ν :=
      Integrable.of_bound (ht.1.sub h0.aestronglyMeasurable) (C * t^2)
        (by simpa only [Real.norm_eq_abs] using ht.2)
    have hi : Integrable (F t) ν := by
      convert! hr.fun_add h0 using 1
      funext b
      ring
    rw [← integral_sub hi h0]
    have hb : ∀ᵐ b ∂ν, ‖F t b - F 0 b‖ ≤ C * t^2 := by
      simpa only [Real.norm_eq_abs] using ht.2
    simpa using norm_integral_le_of_norm_le_const hb
  have ho : (fun t : ℝ => (∫ b, F t b ∂ν) - ∫ b, F 0 b ∂ν)
      =O[nhds 0] (fun t : ℝ => t^2) := by
    apply Asymptotics.IsBigO.of_bound C
    filter_upwards [hbound] with t ht
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)] using ht
  apply HasDerivAt.of_isLittleO
  simpa only [smul_zero, sub_zero] using
    ho.trans_isLittleO (Asymptotics.isLittleO_pow_id (𝕜 := ℝ) (by norm_num : 1 < 2))

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- Each positive-level contribution retains the regression/denominator/weight
-- interaction; the structural zero contributes identically zero.
-- @node: population_binary_full_level_joint_remainder_bound
/-- Under [baseline overlap with the given positive lower bound](hyp:hov) and
[admissibility of the true binary nuisance](hyp:he), suppose [the outcome,
assignment, and instrument-weight direction bounds are nonnegative](hyp:hR,hC,hG)
and [bound every outcome regression direction](hyp:hr), [every assignment
probability direction](hyp:hc), and [every full instrument-weight
direction](hyp:hg) almost surely. If [the absolute perturbation is less than the
overlap bound divided by twice one plus the assignment direction bound](hyp:ht),
[almost surely, the perturbed outcome regression times the true instrument
weight, plus its fitted inverse-assignment residual correction, differs from the
true product by at most the squared perturbation times the outcome direction
bound times the sum of the other two bounds, divided by half the overlap
bound](goal). -/
lemma population_binary_full_level_joint_remainder_bound
    (L : LevelData Z X) (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (del : NuisanceBin L) (he : BinAdmissible M L (eta0Bin M L))
    (R C G : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C) (hG : 0 ≤ G)
    (hr : ∀ a, ∀ᵐ x ∂xLaw M, ‖del.P1 a x‖ ≤ R)
    (hc : ∀ a, ∀ᵐ x ∂xLaw M, ‖del.piLev a x‖ ≤ C)
    (hg : ∀ a, ∀ᵐ x ∂xLaw M, ‖del.gammaFull a x‖ ≤ G)
    (k : Fin L.K) (i : ℕ) (t : ℝ) (ht : |t| < cpi / (2*(C+1))) :
    ∀ᵐ x ∂xLaw M,
      |positiveValue (eta0Bin M L + t • del).P1 i x * (eta0Bin M L).gammaFull k x +
        (eta0Bin M L + t • del).gammaFull k x * positiveValue (eta0Bin M L).piLev i x *
          (positiveValue (eta0Bin M L).P1 i x - positiveValue (eta0Bin M L + t • del).P1 i x) /
            positiveValue (eta0Bin M L + t • del).piLev i x -
        positiveValue (eta0Bin M L).P1 i x * (eta0Bin M L).gammaFull k x| ≤
      (R * (C+G) / (cpi/2)) * t^2 := by
  by_cases hi : 1 ≤ i ∧ i ≤ L.K
  · let a : PositiveIndex L.K := ⟨i,hi⟩
    filter_upwards [hr a, hc a, hg k, he.2.2.1 a,
      he.2.2.2.2.2.2.2.2.2.1 k] with x hxR hxC hxG hx hxg
    have hpi : cpi ≤ (eta0Bin M L).piLev a x := hov.2 x i hi.1 hi.2
    have hclip : cpi/2 ≤ (eta0Bin M L).piLev a x + t * del.piLev a x := by
      have hmul : |t * del.piLev a x| ≤ |t| * C := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using hxC) (abs_nonneg t)
      have hsmall := (lt_div_iff₀ (by positivity : 0 < 2*(C+1))).mp ht
      nlinarith [neg_abs_le (t * del.piLev a x), abs_nonneg t]
    have hgb : |(eta0Bin M L).gammaFull k x| ≤ 1 := abs_le.mpr hxg
    have hpib : |(eta0Bin M L).piLev a x| ≤ 1 := by
      rw [abs_of_nonneg hx.2.2.1]
      exact hx.2.2.2
    simp only [positiveValue, dif_pos hi]
    change |((eta0Bin M L).P1 a x + t * del.P1 a x) * (eta0Bin M L).gammaFull k x +
      ((eta0Bin M L).gammaFull k x + t * del.gammaFull k x) * (eta0Bin M L).piLev a x *
        ((eta0Bin M L).P1 a x - ((eta0Bin M L).P1 a x + t * del.P1 a x)) /
          ((eta0Bin M L).piLev a x + t * del.piLev a x) -
      (eta0Bin M L).P1 a x * (eta0Bin M L).gammaFull k x| ≤ _
    have hb := binary_full_joint_scalar_remainder_bound
      ((eta0Bin M L).P1 a x) ((eta0Bin M L).gammaFull k x) ((eta0Bin M L).piLev a x)
      (del.P1 a x) (del.gammaFull k x) (del.piLev a x) t (cpi/2) (by linarith [hov.1]) hclip
    have hcoef : |del.P1 a x| * (|(eta0Bin M L).gammaFull k x| * |del.piLev a x| +
        |del.gammaFull k x| * |(eta0Bin M L).piLev a x|) / (cpi/2) ≤ R*(C+G)/(cpi/2) := by
      apply div_le_div_of_nonneg_right _ (by linarith [hov.1])
      calc
        _ ≤ R * (1*C + G*1) := by
          gcongr
          · simpa only [Real.norm_eq_abs] using hxR
          · simpa only [Real.norm_eq_abs] using hxC
          · simpa only [Real.norm_eq_abs] using hxG
        _ = _ := by ring
    exact hb.trans (by nlinarith [sq_nonneg t])
  · simp only [positiveValue, dif_neg hi, zero_mul, sub_self, mul_zero, zero_div, add_zero,
      abs_zero]
    have hcpi := hov.1
    exact Eventually.of_forall (fun _ => by positivity)

-- The conditional mean formula is integrated before taking the derivative.
-- Admissibility supplies bounded directions, and overlap bounds reciprocals.
-- @node: population_binary_full_joint_orthogonality_of_admissible
/-- Under [baseline overlap](hyp:hov) and [an almost surely binary
outcome](hyp:hy), for [an admissible joint binary nuisance direction at the
truth](hyp:hd), [the population mean of the full product score at the given level
has derivative zero at zero along the linear nuisance path](goal). -/
lemma population_binary_full_joint_orthogonality_of_admissible
    (L : LevelData Z X) (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (hy : OutcomeBinaryAE M) (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del)) (k : Fin L.K) :
    HasDerivAt (fun t : ℝ => ∫ o, psiFullProdBin L (eta0Bin M L + t • del) k o
      ∂observationLaw M) 0 0 := by
  haveI : IsProbabilityMeasure (observationLaw M) := by
    unfold observationLaw
    exact Measure.isProbabilityMeasure_map (M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY))).aemeasurable
  have he := binary_admissible_direction_origin M L (eta0Bin M L) del hd
  obtain ⟨R, hR, hr⟩ := binary_regression_direction_regular M L (eta0Bin M L) del hd
  obtain ⟨C, hC, hc⟩ := binary_assignment_denominator_direction_regular M L (eta0Bin M L) del hd
  obtain ⟨G, hG, hg⟩ := binary_full_weight_direction_regular M L (eta0Bin M L) del hd
  let F : ℝ → Obs X Z → ℝ := fun t o =>
    binFullJ L (eta0Bin M L + t • del) k o.1 * (eta0Bin M L).gammaFull k o.1 +
    (eta0Bin M L + t • del).gammaFull k o.1 * positiveValue (eta0Bin M L).piLev (k+1) o.1 *
      (positiveValue (eta0Bin M L).P1 (k+1) o.1 -
        positiveValue (eta0Bin M L + t • del).P1 (k+1) o.1) /
          positiveValue (eta0Bin M L + t • del).piLev (k+1) o.1 -
    (eta0Bin M L + t • del).gammaFull k o.1 * positiveValue (eta0Bin M L).piLev k o.1 *
      (positiveValue (eta0Bin M L).P1 k o.1 -
        positiveValue (eta0Bin M L + t • del).P1 k o.1) /
          positiveValue (eta0Bin M L + t • del).piLev k o.1
  have hz : eta0Bin M L + (0 : ℝ) • del = eta0Bin M L := by
    change (⟨(eta0Bin M L).prop + 0 • del.prop, (eta0Bin M L).pLev + 0 • del.pLev,
      (eta0Bin M L).P1 + 0 • del.P1, (eta0Bin M L).piLev + 0 • del.piLev,
      (eta0Bin M L).tauLev + 0 • del.tauLev, (eta0Bin M L).share + 0 • del.share,
      (eta0Bin M L).gammaFull + 0 • del.gammaFull, (eta0Bin M L).gamma + 0 • del.gamma,
      (eta0Bin M L).gammaTail + 0 • del.gammaTail⟩ : NuisanceBin L) = eta0Bin M L
    simp only [zero_smul, add_zero]
    rfl
  have hF0 : F 0 = fun o => binFullJ L (eta0Bin M L) k o.1 * (eta0Bin M L).gammaFull k o.1 := by
    funext o
    simp only [F, hz, sub_self, mul_zero, zero_div, add_zero, sub_zero]
  have hg0 : Measurable ((eta0Bin M L).gammaFull k) := he.2.2.2.2.2.2.2.2.2.2.1 k
  have hg0B : ∀ᵐ x ∂xLaw M, ‖(eta0Bin M L).gammaFull k x‖ ≤ 1 := by
    filter_upwards [he.2.2.2.2.2.2.2.2.2.1 k] with x hx
    simpa only [Real.norm_eq_abs, abs_le, mem_Icc] using hx
  have i0 : Integrable (F 0) (observationLaw M) := by
    rw [hF0]
    exact (population_binary_full_contrast_integrable M L he k).mul_bdd
      (hg0.comp measurable_fst).aestronglyMeasurable (observationLaw_covariate_ae M _ hg0B)
  have hPm (t : ℝ) (i : ℕ) : Measurable (positiveValue (eta0Bin M L + t • del).P1 i) := by
    change Measurable (fun x => positiveValue (eta0Bin M L + t • del).P1 i x)
    by_cases hi : 1 ≤ i ∧ i ≤ L.K
    · simp only [positiveValue, dif_pos hi]
      exact ((he.2.2.2.1 ⟨i,hi⟩).2.1).add ((hr ⟨i,hi⟩).1.const_mul t)
    · simp only [positiveValue, dif_neg hi]
      fun_prop
  have hpim (t : ℝ) (i : ℕ) : Measurable (positiveValue (eta0Bin M L + t • del).piLev i) := by
    change Measurable (fun x => positiveValue (eta0Bin M L + t • del).piLev i x)
    by_cases hi : 1 ≤ i ∧ i ≤ L.K
    · simp only [positiveValue, dif_pos hi]
      exact ((he.2.2.2.1 ⟨i,hi⟩).2.2).add ((hc ⟨i,hi⟩).1.const_mul t)
    · simp only [positiveValue, dif_neg hi]
      fun_prop
  have hFm (t : ℝ) : Measurable (F t) := by
    have hP0 (i : ℕ) : Measurable (positiveValue (eta0Bin M L).P1 i) := by
      simpa only [hz] using hPm 0 i
    have hpi0 (i : ℕ) : Measurable (positiveValue (eta0Bin M L).piLev i) := by
      simpa only [hz] using hpim 0 i
    have hgt : Measurable ((eta0Bin M L + t • del).gammaFull k) :=
      hg0.add ((hg k).1.const_mul t)
    dsimp only [F]
    unfold binFullJ
    first
    | fun_prop
    | exact (((((hPm t (k+1)).sub (hPm t k)).comp measurable_fst).mul
        (hg0.comp measurable_fst)).add
        ((((hgt.comp measurable_fst).mul ((hpi0 (k+1)).comp measurable_fst)).mul
          (((hP0 (k+1)).comp measurable_fst).sub ((hPm t (k+1)).comp measurable_fst))).div
            ((hpim t (k+1)).comp measurable_fst))).sub
        ((((hgt.comp measurable_fst).mul ((hpi0 k).comp measurable_fst)).mul
          (((hP0 k).comp measurable_fst).sub ((hPm t k).comp measurable_fst))).div
            ((hpim t k).comp measurable_fst))
  have radius : 0 < cpi / (2*(C+1)) := by have hcpi := hov.1; positivity
  have hloc : ∀ᶠ t : ℝ in nhds 0, AEStronglyMeasurable (F t) (observationLaw M) ∧
      ∀ᵐ o ∂observationLaw M, |F t o - F 0 o| ≤ (2*(R*(C+G)/(cpi/2))) * t^2 := by
    filter_upwards [continuousAt_id.abs.eventually_lt_const (by simpa using radius)] with t ht
    refine ⟨(hFm t).aestronglyMeasurable, ?_⟩
    have hp := population_binary_full_level_joint_remainder_bound M L cpi hov del he R C G
      hR hC hG (fun a => (hr a).2) (fun a => (hc a).2) (fun a => (hg a).2) k (k+1) t ht
    have hm := population_binary_full_level_joint_remainder_bound M L cpi hov del he R C G
      hR hC hG (fun a => (hr a).2) (fun a => (hc a).2) (fun a => (hg a).2) k k t ht
    filter_upwards [observationLaw_covariate_ae M _ hp, observationLaw_covariate_ae M _ hm] with o hp hm
    rw [hF0]
    dsimp only [F]
    unfold binFullJ
    -- Pair the plus and minus scalar remainders before bounding their sum.
    have heq : ∀ a b c d e f g : ℝ,
        (a-b)*c+d-e-(f-g)*c = (a*c+d-f*c)-(b*c+e-g*c) := by intros; ring
    rw [heq]
    apply (abs_sub_le _ (0 : ℝ) _).trans
    simp only [sub_zero, zero_sub, abs_neg]
    linarith [hp, hm]
  have hder := integral_local_quadratic_orthogonality (observationLaw M) F
    (2*(R*(C+G)/(cpi/2))) i0 hloc
  apply hder.congr_of_eventuallyEq
  filter_upwards [population_binary_full_joint_path_local_mean_of_admissible M L cpi hov hy del hd k]
    with t ht
  exact ht.2

-- @node: population_binary_full_sum_joint_orthogonality_of_admissible
/-- Under [baseline overlap](hyp:hov) and [an almost surely binary
outcome](hyp:hy), for [an admissible joint binary nuisance direction at the
truth](hyp:hd), [the population mean of the sum of full product scores over all
levels has derivative zero at zero along the linear nuisance path](goal). -/
lemma population_binary_full_sum_joint_orthogonality_of_admissible
    (L : LevelData Z X) (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (hy : OutcomeBinaryAE M) (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del)) :
    HasDerivAt (fun t : ℝ => ∫ o, ∑ k ∈ Finset.range L.K,
      psiFullProdBin L (eta0Bin M L + t • del) k o ∂observationLaw M) 0 0 := by
  have hder : ∀ k ∈ Finset.range L.K, HasDerivAt (fun t : ℝ =>
      ∫ o, psiFullProdBin L (eta0Bin M L + t • del) k o ∂observationLaw M) 0 0 := by
    intro k hk
    exact population_binary_full_joint_orthogonality_of_admissible M L cpi hov hy del hd
      ⟨k, Finset.mem_range.mp hk⟩
  have hsum := HasDerivAt.fun_sum hder
  have hi : ∀ᶠ t : ℝ in nhds 0, ∀ k ∈ Finset.range L.K,
      Integrable (psiFullProdBin L (eta0Bin M L + t • del) k) (observationLaw M) := by
    apply (eventually_all_finset _).2
    intro k hk
    exact (population_binary_full_joint_path_local_mean_of_admissible M L cpi hov hy del hd
      ⟨k, Finset.mem_range.mp hk⟩).mono (fun _ h => h.1)
  have hsum' : HasDerivAt (fun t : ℝ => ∑ k ∈ Finset.range L.K,
      ∫ o, psiFullProdBin L (eta0Bin M L + t • del) k o ∂observationLaw M) 0 0 := by
    simpa only [Finset.sum_const_zero] using hsum
  apply hsum'.congr_of_eventuallyEq
  filter_upwards [hi] with t ht
  exact integral_finsetSum _ ht

end Papers.TbsPrteOptimalTransport

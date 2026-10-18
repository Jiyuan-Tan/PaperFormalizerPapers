module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousFullEvaluation
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousTailEvaluation
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousBandTreatmentEvaluation
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationContinuousAdmissibility
/-! Uniform bounds for the continuous orthogonal score. Clipped band outcomes,
quantiles and probabilities, together with overlap, control every residual
correction uniformly over the training sample. -/
public section
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option maxHeartbeats 800000

set_option linter.style.longLine false
set_option linter.unreachableTactic false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedTactic false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v
variable {Ω : Type u} {X Z : Type v}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]
  [Fintype Z] [DecidableEq Z]

-- @node: fitted_continuous_gamma_IFJ_abs_bound
/-- Write $R$ for the sum of the absolute outcome endpoints. If [the nuisance record is admissible](hyp:he), [the denominator bound $c$ is positive](hyp:hc), [all positive-level probabilities are at least $c$ almost everywhere](hyp:hden), and [the level is below the level count](hyp:hk), then [the absolute gamma-weighted band-mean influence correction, for either sign, is at most $2R/c$ almost everywhere under the observation law](goal). -/
lemma fitted_continuous_gamma_IFJ_abs_bound
    (M : LatentIVModel Ω X Z) (L : LevelData Z X) (e : NuisanceCont L)
    (he : ContAdmissible M L e) (c : ℝ) (hc : 0 < c)
    (hden : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (g : RegularIndex L) (plus : Bool) (k j : ℕ) (hk : k < L.K) :
    ∀ᵐ o ∂observationLaw M, |e.gamma g o.1 * IFJ M L e plus k j o| ≤
      2 * (|M.yMin| + |M.yMax|) / c := by
  let B := |M.yMin| + |M.yMax|
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hgb : ∀ᵐ x ∂xLaw M, |e.gamma g x| ≤ 1 := by
    rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hb, _⟩
    filter_upwards [hb g] with x hx
    simpa only [abs_of_nonneg hx.1] using hx.2
  have hside (i : PositiveIndex L.K) (J : X → ℝ)
      (hJb : ∀ᵐ x ∂xLaw M, |J x| ≤ B) :
      ∀ᵐ o ∂observationLaw M, |e.gamma g o.1 *
        (indicator (o.2.1 ∈ L.S i.val) * o.2.2.1 / e.piLev i o.1 *
          (o.2.2.2 * indicator (nuValue M e k j o.1 < o.2.2.2 ∧
            o.2.2.2 ≤ nuValue M e k (j+1) o.1) - J o.1))| ≤ 2 * B / c := by
    filter_upwards [observationLaw_covariate_ae M _ hgb,
      observationLaw_covariate_ae M _ hJb,
      observationLaw_covariate_ae M _ (hden i), observationLaw_treatment_range M,
      observationLaw_covariate_ae M _ (continuous_admissible_nuValue_abs_bound M L e he k j),
      observationLaw_covariate_ae M _ (continuous_admissible_nuValue_abs_bound M L e he k (j+1))]
      with o hg hJ hd hW ha hb
    have hy := outcome_weighted_band_abs_bound (nuValue M e k j o.1)
      (nuValue M e k (j+1) o.1) 1 o.2.2.2 B 1 ha hb (by norm_num)
      (by dsimp [B]; positivity) zero_le_one
    simp only [one_mul, mul_one] at hy
    have hs : |indicator (o.2.1 ∈ L.S i.val)| ≤ 1 := by
      unfold indicator; split_ifs <;> norm_num
    have hw : |o.2.2.1| ≤ 1 := by rw [abs_of_nonneg hW.1]; exact hW.2
    have herr : |o.2.2.2 * indicator (nuValue M e k j o.1 < o.2.2.2 ∧
        o.2.2.2 ≤ nuValue M e k (j+1) o.1) - J o.1| ≤ 2 * B :=
      (abs_sub _ _).trans (by linarith)
    have hpi0 : 0 < e.piLev i o.1 := hc.trans_le hd
    rw [abs_mul, abs_mul, abs_div, abs_mul, abs_of_pos hpi0]
    calc
      _ ≤ 1 * ((1 * 1) / e.piLev i o.1 * (2 * B)) := by
        gcongr <;> first | fun_prop | assumption | positivity
      _ = 2 * B / e.piLev i o.1 := by ring
      _ ≤ 2 * B / c := div_le_div_of_nonneg_left (by dsimp [B]; positivity) hc hd
  cases plus with
  | true =>
    have hi : 1 ≤ k+1 ∧ k+1 ≤ L.K := by omega
    simpa only [IFJ, Bool.not_true, Bool.false_and, Bool.false_eq_true,
      if_false, if_true, positiveValue, dif_pos hi] using
      hside ⟨k+1, hi⟩ _ (continuous_admissible_band_means_abs_bound M L e he k j).1
  | false =>
    by_cases hk0 : k = 0
    · subst k
      simp only [IFJ, Bool.not_false, beq_self_eq_true, Bool.and_self, if_true, mul_zero, abs_zero]
      exact Eventually.of_forall (fun _ => by positivity)
    · have hi : 1 ≤ k ∧ k ≤ L.K := by omega
      simpa only [IFJ, Bool.not_false, Bool.true_and, beq_iff_eq, hk0,
        if_false, Bool.false_eq_true, positiveValue, dif_pos hi] using
        hside ⟨k, hi⟩ _ (continuous_admissible_band_means_abs_bound M L e he k j).2

-- @node: fitted_contJ_abs_bound
/-- If [the nuisance record is admissible](hyp:he), then [the absolute continuous band-mean contrast is at most twice the sum of the absolute outcome endpoints, almost everywhere under the covariate law](goal). -/
lemma fitted_contJ_abs_bound
    (M : LatentIVModel Ω X Z) (L : LevelData Z X) (e : NuisanceCont L)
    (he : ContAdmissible M L e) (k j : ℕ) :
    ∀ᵐ x ∂xLaw M, |contJ L e k j x| ≤ 2 * (|M.yMin| + |M.yMax|) := by
  have hp := (fitted_continuous_full_coordinates M L e he (k+1)).1.2
  have hm := (fitted_continuous_full_coordinates M L e he k).1.2
  have hj := continuous_admissible_band_means_abs_bound M L e he k j
  filter_upwards [hp, hm, hj.1, hj.2] with x hp hm hj hl
  unfold contJ
  apply (abs_sub _ _).trans
  rw [abs_mul, abs_mul]
  have hplus := mul_le_mul hp hj (abs_nonneg _) zero_le_one
  have hminus := mul_le_mul hm hl (abs_nonneg _) zero_le_one
  norm_num at hplus hminus
  linarith

-- @node: fitted_continuous_gamma_quantile_correction_abs_bound
/-- Write $R$ for the sum of the absolute outcome endpoints. If [the policy is valid](hyp:hphi), [the nuisance record is admissible](hyp:he), [the denominator bound $c$ is positive](hyp:hc), [positive-level probabilities are at least $c$ almost everywhere](hyp:hden), [the level is below the level count](hyp:hk), and [the boundary index does not exceed the number of bands](hyp:hj), then [the absolute gamma-weighted quantile correction, including the boundary, policy-width, and influence terms, is at most $R(4+4/c)$ almost everywhere under the observation law](goal). -/
lemma fitted_continuous_gamma_quantile_correction_abs_bound
    (M : LatentIVModel Ω X Z) (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (L : LevelData Z X) (e : NuisanceCont L) (he : ContAdmissible M L e)
    (c : ℝ) (hc : 0 < c)
    (hden : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (g : RegularIndex L) (k j : ℕ) (hk : k < L.K) (hj : j ≤ L.l k) :
    ∀ᵐ o ∂observationLaw M, |e.gamma g o.1 * nuValue M e k j o.1 *
      (positiveValue e.pLev (k+1) o.1 * boundaryValue e.Mplus k j o.1 -
        positiveValue e.pLev k o.1 * minusBoundaryValue e.Mminus k j o.1 -
        (pooledQ phi L e k j o.1 - positiveValue e.pLev k o.1) +
        IFM M L e true k j o - IFM M L e false k j o)| ≤
      (|M.yMin| + |M.yMax|) * (4 + 4 / c) := by
  have hgb : ∀ᵐ x ∂xLaw M, |e.gamma g x| ≤ 1 := by
    rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hb, _⟩
    filter_upwards [hb g] with x hx
    simpa only [abs_of_nonneg hx.1] using hx.2
  filter_upwards [observationLaw_covariate_ae M _ hgb,
    observationLaw_covariate_ae M _ (continuous_admissible_nuValue_abs_bound M L e he k j),
    observationLaw_covariate_ae M _ (fitted_continuous_boundary_contrast_abs_bound M L e he k j),
    observationLaw_covariate_ae M _ (fitted_continuous_policy_width_abs_bound M phi hphi L e he k j hk hj),
    fitted_continuous_gamma_IFM_abs_bound M L e he c hc hden g true k j hk,
    fitted_continuous_gamma_IFM_abs_bound M L e he c hc hden g false k j hk]
    with o hg hn hb hw hp hm
  let D := positiveValue e.pLev (k+1) o.1 * boundaryValue e.Mplus k j o.1 -
    positiveValue e.pLev k o.1 * minusBoundaryValue e.Mminus k j o.1
  let W := pooledQ phi L e k j o.1 - positiveValue e.pLev k o.1
  let P := e.gamma g o.1 * IFM M L e true k j o
  let N := e.gamma g o.1 * IFM M L e false k j o
  have hbase : |e.gamma g o.1 * (D - W)| ≤ 4 := by
    rw [abs_mul]
    exact (mul_le_mul hg ((abs_sub _ _).trans (add_le_add hb hw))
      (abs_nonneg _) zero_le_one).trans (by norm_num)
  have hcor : |e.gamma g o.1 * (D - W) + P - N| ≤ 4 + 4 / c := by
    have ht : |e.gamma g o.1 * (D - W) + P - N| ≤
        |e.gamma g o.1 * (D - W)| + |P| + |N| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    dsimp only [P, N] at ht ⊢
    exact (ht.trans (add_le_add (add_le_add hbase hp) hm)).trans_eq (by ring)
  calc
    _ = |nuValue M e k j o.1 * (e.gamma g o.1 * (D - W) + P - N)| := by
      congr 1; dsimp [D, W, P, N]; ring
    _ ≤ (|M.yMin| + |M.yMax|) * (4 + 4 / c) := by
      rw [abs_mul]
      exact mul_le_mul hn hcor (abs_nonneg _) (by positivity)

-- @node: fitted_continuous_fractional_product_abs_bound
/-- Write $R$ for the sum of the absolute outcome endpoints and $m$ for the sum of the instrument-set sizes at the two boundaries of the band. Suppose [the policy is valid](hyp:hphi), [the derivative bound $B$ is nonnegative](hyp:hB), [the absolute derivative is at most $B$ at all probabilities between zero and one](hyp:hb), [the nuisance record is admissible](hyp:he), [the denominator bound $c$ is positive](hyp:hc), [positive-level probabilities are at least $c$ almost everywhere](hyp:hpi), and [regular-band probabilities are at least $c$ almost everywhere](hyp:htau). If [the level is below the level count](hyp:hk) and [the band index lies between one and the number of bands](hyp:hj), then [the absolute fractional-band score product is at most $10R+22R/c+RmB/c$ almost everywhere under the observation law](goal). -/
lemma fitted_continuous_fractional_product_abs_bound
    (M : LatentIVModel Ω X Z) (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ z x p, p ∈ Icc (0 : ℝ) 1 → |dphi z x p| ≤ B)
    (L : LevelData Z X) (e : NuisanceCont L) (he : ContAdmissible M L e)
    (c : ℝ) (hc : 0 < c)
    (hpi : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (htau : ∀ r : RegularIndex L, ∀ᵐ x ∂xLaw M, c ≤ e.tauLev r x)
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k) :
    ∀ᵐ o ∂observationLaw M, |psiProd M phi dphi L e k j o| ≤
      10 * (|M.yMin| + |M.yMax|) + 22 * (|M.yMin| + |M.yMax|) / c +
        (|M.yMin| + |M.yMax|) *
          (((L.T k (j-1)).card : ℝ) + (L.T k j).card) * B / c := by
  have hg : k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k := ⟨hk.le, hj⟩
  let g : RegularIndex L := ⟨(k,j), hg⟩
  have hgb : ∀ᵐ x ∂xLaw M, |e.gamma g x| ≤ 1 := by
    rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hb, _⟩
    filter_upwards [hb g] with x hx
    simpa only [abs_of_nonneg hx.1] using hx.2
  have hlow : ∀ᵐ o ∂observationLaw M,
      |e.gamma g o.1 * (if k = 0 then 0 else
        alphaLow M L e k (j-1) o.1 * RpCont L e k o)| ≤
          5 * (|M.yMin| + |M.yMax|) / c := by
    have h := fitted_continuous_gamma_alpha_treatment_abs_bound M L e he c hc hpi
      g false k (j-1) hk
    by_cases hk0 : k = 0
    · simp only [hk0, if_true, mul_zero, abs_zero]
      exact Eventually.of_forall (fun _ => by positivity)
    · simpa only [Bool.false_eq_true, if_false, hk0, div_eq_mul_inv, one_mul] using h
  filter_upwards [observationLaw_covariate_ae M _ hgb,
    observationLaw_covariate_ae M _ (fitted_contJ_abs_bound M L e he k (j-1)),
    fitted_continuous_gamma_IFJ_abs_bound M L e he c hc hpi g true k (j-1) hk,
    fitted_continuous_gamma_IFJ_abs_bound M L e he c hc hpi g false k (j-1) hk,
    fitted_continuous_gamma_quantile_correction_abs_bound M phi hphi L e he c hc hpi
      g k (j-1) hk (by omega),
    fitted_continuous_gamma_quantile_correction_abs_bound M phi hphi L e he c hc hpi
      g k j hk hj.2, hlow,
    fitted_continuous_gamma_alpha_treatment_abs_bound M L e he c hc hpi g true k (j-1) hk,
    fitted_continuous_quantile_policy_residual_abs_bound M dphi B hB hb L e he c hc htau k (j-1) hk.le,
    fitted_continuous_quantile_policy_residual_abs_bound M dphi B hB hb L e he c hc htau k j hk.le]
    with o hgam hJ hIp hIm hQp hQm hTl hTh hRl hRh
  have hshift : j-1+1 = j := by omega
  let Y := |M.yMin| + |M.yMax|
  let moment := fun b => positiveValue e.pLev (k+1) o.1 * boundaryValue e.Mplus k b o.1 -
    positiveValue e.pLev k o.1 * minusBoundaryValue e.Mminus k b o.1 -
    (pooledQ phi L e k b o.1 - positiveValue e.pLev k o.1) +
    IFM M L e true k b o - IFM M L e false k b o
  let A := indicator (o.2.1 ∈ policyUnion L k j) * contJ L e k (j-1) o.1
  let P := e.gamma g o.1 * IFJ M L e true k (j-1) o
  let N := e.gamma g o.1 * IFJ M L e false k (j-1) o
  let Q := e.gamma g o.1 * nuValue M e k (j-1) o.1 * moment (j-1)
  let R := e.gamma g o.1 * nuValue M e k j o.1 * moment j
  let T := e.gamma g o.1 * (if k = 0 then 0 else alphaLow M L e k (j-1) o.1 * RpCont L e k o)
  let U := e.gamma g o.1 * (alphaHigh M L e k (j-1) o.1 * RpCont L e (k+1) o)
  let V := e.gamma g o.1 * (nuValue M e k (j-1) o.1 * RqCont dphi L e k (j-1) o)
  let W := e.gamma g o.1 * (nuValue M e k j o.1 * RqCont dphi L e k j o)
  have hA : |A| ≤ 2 * Y := by
    have hi : |indicator (o.2.1 ∈ policyUnion L k j)| ≤ 1 := by
      unfold indicator; split_ifs <;> norm_num
    dsimp only [A]
    rw [abs_mul]
    exact (mul_le_mul hi hJ (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hV : |V| ≤ Y * ((L.T k (j-1)).card * B / c) := by
    dsimp only [V]
    rw [abs_mul]
    exact (mul_le_mul hgam hRl (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hW : |W| ≤ Y * ((L.T k j).card * B / c) := by
    dsimp only [W]
    rw [abs_mul]
    exact (mul_le_mul hgam hRh (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have heq : psiProd M phi dphi L e k j o = A + P - N + Q - R + T + U - V + W := by
    simp only [psiProd, contScoreComponents, hshift, regularValue, dif_pos hg]
    dsimp [A, P, N, Q, R, T, U, V, W, moment, g]
    ring
  have htriangle : |A + P - N + Q - R + T + U - V + W| ≤
      |A| + |P| + |N| + |Q| + |R| + |T| + |U| + |V| + |W| := by
    linarith only [abs_add_le A P, abs_sub (A+P) N, abs_add_le (A+P-N) Q,
      abs_sub (A+P-N+Q) R, abs_add_le (A+P-N+Q-R) T,
      abs_add_le (A+P-N+Q-R+T) U, abs_sub (A+P-N+Q-R+T+U) V,
      abs_add_le (A+P-N+Q-R+T+U-V) W]
  simp only [if_true] at hTh
  rw [heq]
  apply htriangle.trans
  change |A| + |P| + |N| + |Q| + |R| + |T| + |U| + |V| + |W| ≤ _
  have hU : |U| ≤ 5 * Y / c := by
    simpa only [U, Y, div_eq_mul_inv, one_mul] using hTh
  change |P| ≤ 2 * Y / c at hIp
  change |N| ≤ 2 * Y / c at hIm
  change |Q| ≤ Y * (4 + 4 / c) at hQp
  change |R| ≤ Y * (4 + 4 / c) at hQm
  change |T| ≤ 5 * Y / c at hTl
  calc
    _ ≤ 2*Y + 2*Y/c + 2*Y/c + Y*(4+4/c) + Y*(4+4/c) +
        5*Y/c + 5*Y/c + Y*((L.T k (j-1)).card*B/c) + Y*((L.T k j).card*B/c) := by
      linarith only [hA, hIp, hIm, hQp, hQm, hTl, hU, hV, hW]
    _ = _ := by dsimp [Y]; ring

-- @node: fitted_continuous_total_score_uniform_bound
/-- If [the policy is valid](hyp:hphi), [its derivative map is bounded and Lipschitz](hyp:hDerivative), [the level count is positive](hyp:hK), [potential outcomes satisfy the support restriction](hyp:hp), [observed outcomes satisfy consistency](hyp:hcons), [outcome endpoints are known](hyp:hend), and [the common denominator bound is positive](hyp:hc), then [one finite constant bounds the absolute continuous total score almost everywhere for every admissible nuisance record whose positive-level and regular-band probabilities exceed that common bound](goal). -/
lemma fitted_continuous_total_score_uniform_bound
    (M : LatentIVModel Ω X Z) (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hp : PotentialSupport M) (hcons : Consistency M) (hend : OutcomeEndpointsKnown M)
    (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, ∀ e : NuisanceCont L, ContAdmissible M L e →
      (∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x) →
      (∀ r : RegularIndex L, ∀ᵐ x ∂xLaw M, c ≤ e.tauLev r x) →
      ∀ᵐ o ∂observationLaw M, |psiCont M phi dphi L hK o e| ≤ C := by
  cases Subsingleton.elim ‹DecidableEq Z› (fun a b => Classical.propDecidable (a = b))
  obtain ⟨B, D, hB, hD, hder⟩ := hDerivative
  have hb z x p (hp : p ∈ Icc (0 : ℝ) 1) : |dphi z x p| ≤ B :=
    (hder z x p p hp hp).1
  let Y := |M.yMin| + |M.yMax|
  let F := (L.K : ℝ) * (2 * max |M.yMin| |M.yMax| + 6 * max |M.yMin| |M.yMax| / c)
  let G := ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
    (10 * Y + 22 * Y / c + Y * (((L.T k (j-1)).card : ℝ) + (L.T k j).card) * B / c)
  let T := |M.yMin| * (2 + B + 1 / c)
  refine ⟨F + G + T, ?_⟩
  intro e he hpi htau
  have hband : ∀ᵐ o ∂observationLaw M, ∀ k j : ℕ,
      k < L.K → (1 ≤ j ∧ j ≤ L.l k) →
      |psiProd M phi dphi L e k j o| ≤
        10 * Y + 22 * Y / c + Y * (((L.T k (j-1)).card : ℝ) + (L.T k j).card) * B / c := by
    simp only [ae_all_iff]
    intro k j hk hj
    exact fitted_continuous_fractional_product_abs_bound M phi dphi hphi B hB hb
      L e he c hc hpi htau k j hk hj
  have hG : ∀ᵐ o ∂observationLaw M,
      |∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
        psiProd M phi dphi L e k j o| ≤ G := by
    filter_upwards [hband] with o ho
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro k hk
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro j hj
    exact ho k j (Finset.mem_range.mp hk) (Finset.mem_Icc.mp hj)
  filter_upwards [fitted_continuous_full_score_block_abs_bound M L e he hp hcons hend
    c hc hpi, hG, fitted_continuous_tail_abs_bound M phi dphi hphi B hB hb L e he c hc hpi]
    with o hF hG hT
  rw [continuous_total_score_block_decomposition]
  exact ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
    (add_le_add (add_le_add hF hG) hT)

-- @node: contDMLRegime_mean_variance_consistent_on_recovery
/-- Suppose [the sample is split into equal halves with the required independence](hyp:hSplit), [the policy is valid](hyp:hphi), [the specified derivative differentiates it](hyp:hd), [the derivative is bounded and Lipschitz](hyp:hDerivative), [the structural assumptions hold](hyp:hStruct), [outcome endpoints are known](hyp:hend), [the level count is positive](hyp:hK), [level ordering is policy invariant](hyp:hOrder), [level probabilities are measurable](hyp:hlev), [band boundaries are measurable](hyp:hb), [baseline overlap has the specified witness](hyp:hov), and [policy overlap holds at the same bound](hyp:hpol). For [continuous-outcome nuisance estimates on the recovered levels](hyp:eHat), under [the finite continuous DML regime](hyp:hr), [recovery events with vanishing complement probabilities](hyp:hG), and [exact recovery of the fixed level data on those events at even sample sizes](hyp:hLevels), [the evaluation-half score mean converges in probability to the discrete target, and its variance estimator converges in probability to the population variance of the true continuous score centered at that target](goal). -/
lemma contDMLRegime_mean_variance_consistent_on_recovery
    (M : LatentIVModel Ω X Z) {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] (S : ObservedSample M μ)
    (I₁ I₂ : SampleSplit A) (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (hStruct : StructuralAssumptions M) (hend : OutcomeEndpointsKnown M)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (hlev : ∀ k, Measurable (L.pLev k))
    (hb : ∀ k < L.K, ∀ j ≤ L.l k, Measurable (bandBoundary M L k j))
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (pHat : ℕ → A → Z → X → ℝ) (rho : ℕ → ℝ) (gap ch : ℝ)
    (eHat : ∀ n a, NuisanceCont (recoveredData M S I₁ I₂ pHat phi rho gap n a))
    (hr : FiniteContDMLRegime M μ S I₁ I₂ pHat phi rho gap cpi L ch eHat)
    (G : ℕ → Set A) (hG : Tendsto (fun n => μ (G n)ᶜ) atTop (𝓝 0))
    (hLevels : ∀ n a, a ∈ G n →
      recoveredData M S I₁ I₂ pHat phi rho gap (2 * (n + 1)) a = L) :
    let score := fittedContScore M S I₁ I₂ pHat phi dphi rho gap eHat
    let truth := fun o => psiCont M phi dphi L hK o (trueNuisance M L)
    let theta := discreteTarget M false L (policyProp phi M.prop)
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => dmlRV M S I₂ score (2 * (n + 1)) a - theta)
      atTop (fun _ _ => 0) ∧
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => varianceRV M S I₂ score (2 * (n + 1)) a)
      atTop (fun _ _ => populationVariance M truth theta) := by
  cases Subsingleton.elim ‹DecidableEq Z› (fun a b => Classical.propDecidable (a = b))
  have hq := population_policyProp_measurable M hStruct.2.2.2.1 phi hphi
  have he0 := population_continuous_nuisance_admissible M hStruct hend
    (policyProp phi M.prop) hq L hOrder hlev cpi hov hpol
  obtain ⟨oracle, hc, ha, hm, hrate, heq⟩ :=
    contDMLRegime_oracle_score_convergence_on_recovery M μ S I₁ I₂ phi dphi hphi hd
      hDerivative hStruct hend L hK hOrder he0 cpi hov hpol pHat rho gap ch eHat hr G hG hLevels
  have hpos : 0 < cpi / 2 := by linarith [hov.1]
  have hp0 (i : PositiveIndex L.K) :
      ∀ᵐ x ∂xLaw M, cpi / 2 ≤ (trueNuisance M L).piLev i x := by
    apply Eventually.of_forall
    intro x
    have hx := hov.2 x i.val i.property.1 i.property.2
    change cpi / 2 ≤ (levelSetProb M L).1 i.val x
    linarith [hov.1]
  have ht0 (r : RegularIndex L) :
      ∀ᵐ x ∂xLaw M, cpi / 2 ≤ (trueNuisance M L).tauLev r x := by
    have hne := continuous_admissible_policy_nonempty M L _ he0 r
    apply Eventually.of_forall
    intro x
    have hx : cpi ≤ (trueNuisance M L).tauLev r x :=
      hpol.2 x r.val.1 r.val.2 r.property.1 r.property.2.1 r.property.2.2 hne
    linarith [hpol.1]
  have hpf n a (i : PositiveIndex L.K) :
      ∀ᵐ x ∂xLaw M, cpi / 2 ≤ (oracle n a).piLev i x :=
    Eventually.of_forall (fun x => (hc n a).2.2.1 i x |>.1)
  have htf n a (r : RegularIndex L) :
      ∀ᵐ x ∂xLaw M, cpi / 2 ≤ (oracle n a).tauLev r x :=
    Eventually.of_forall (fun x => ((hc n a).2.2.2 r x
      (contFittedSharesSimplex_policy_nonempty L _ (hc n a).2.1 r)).1)
  obtain ⟨C, hbound⟩ := fitted_continuous_total_score_uniform_bound M phi dphi hphi
    hDerivative L hK hStruct.1 hStruct.2.1 hend (cpi / 2) hpos
  have hdiff n a : ∀ᵐ o ∂observationLaw M,
      |psiCont M phi dphi L hK o (oracle n a) -
        psiCont M phi dphi L hK o (trueNuisance M L)| ≤ C + C := by
    filter_upwards [hbound _ (ha n a) (hpf n a) (htf n a),
      hbound _ he0 hp0 ht0] with o hf ht
    exact (abs_sub _ _).trans (add_le_add hf ht)
  have hdphi := policy_derivative_graph_measurable phi dphi hphi hd M.prop
    hStruct.2.2.2.1.2.1 M.rangeProp
  have hmean := (population_continuous_score_mean_eq_target M hStruct hend phi dphi
    hphi hdphi hDerivative L hK hOrder hlev cpi hov hpol hb hr.2.2.1 hr.2.2.2).2
  have hLp := true_continuous_total_score_memLp_of_overlap M phi dphi hphi hd hDerivative
    L hK he0 hStruct.1 hStruct.2.1 hend cpi hov hpol
  dsimp only
  exact equalHalfSplit_ae_bounded_training_feasible_mean_variance_consistent M μ S I₁ I₂
    hSplit (fun n a o => psiCont M phi dphi L hK o (oracle n a)) _ _ hmean hLp hm
    (C+C) hdiff hrate _ G hG (fun n a hna i hi => heq n a hna (S.Z i a))

-- @node: contDMLRegime_lower_bound_variance_consistent_on_recovery
/-- Suppose [the sample is split into equal halves with the required independence](hyp:hSplit), [the policy is valid](hyp:hphi), [the specified derivative differentiates it](hyp:hd), [the derivative is bounded and Lipschitz](hyp:hDerivative), [the structural assumptions hold](hyp:hStruct), [outcome endpoints are known](hyp:hend), [baseline and policy propensities satisfy gap separation](hyp:hGap), and [the instrument admits a finite reduction](hyp:hFinite). For [continuous-outcome nuisance estimates on the recovered levels](hyp:eHat), if [the level structure at the reference covariate has positive level count](hyp:hK), [its ordering is invariant under the policy](hyp:hOrder), [baseline overlap has the specified witness](hyp:hov), [policy overlap holds at the same bound](hyp:hpol), [the finite continuous DML regime holds](hyp:hr), [the recovery events have vanishing complement probabilities](hyp:hG), and [the level structure is recovered exactly on those events at even sample sizes](hyp:hLevels), then [the evaluation-half variance estimator converges in probability to the population variance of the true continuous score centered at the transport lower-bound target](goal). -/
lemma contDMLRegime_lower_bound_variance_consistent_on_recovery
    (M : LatentIVModel Ω X Z) {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] (S : ObservedSample M μ)
    (I₁ I₂ : SampleSplit A) (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (hStruct : StructuralAssumptions M) (hend : OutcomeEndpointsKnown M)
    (x0 : X) (hGap : PropensityGapSeparation M.prop (policyProp phi M.prop))
    (hFinite : InstrumentFiniteReduction Z)
    (hK : LevelCountPos (LevelStructure M.prop (policyProp phi M.prop) x0).K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop)
      (LevelStructure M.prop (policyProp phi M.prop) x0))
    (cpi : ℝ)
    (hov : BaselineOverlapWitness M (LevelStructure M.prop (policyProp phi M.prop) x0) cpi)
    (hpol : PolicyOverlap M (LevelStructure M.prop (policyProp phi M.prop) x0) cpi)
    (pHat : ℕ → A → Z → X → ℝ) (rho : ℕ → ℝ) (gap ch : ℝ)
    (eHat : ∀ n a, NuisanceCont (recoveredData M S I₁ I₂ pHat phi rho gap n a))
    (hr : FiniteContDMLRegime M μ S I₁ I₂ pHat phi rho gap cpi
      (LevelStructure M.prop (policyProp phi M.prop) x0) ch eHat)
    (G : ℕ → Set A) (hG : Tendsto (fun n => μ (G n)ᶜ) atTop (𝓝 0))
    (hLevels : ∀ n a, a ∈ G n → recoveredData M S I₁ I₂ pHat phi rho gap
      (2 * (n + 1)) a = LevelStructure M.prop (policyProp phi M.prop) x0) :
    let L := LevelStructure M.prop (policyProp phi M.prop) x0
    let score := fittedContScore M S I₁ I₂ pHat phi dphi rho gap eHat
    let truth := fun o => psiCont M phi dphi L hK o (trueNuisance M L)
    let theta := thetaLower1 (transportData M) (policyWeight M (policyProp phi M.prop))
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => varianceRV M S I₂ score (2 * (n + 1)) a)
      atTop (fun _ _ => populationVariance M truth theta) := by
  cases Subsingleton.elim ‹DecidableEq Z› (fun a b => Classical.propDecidable (a = b))
  have hlev := population_LevelStructure_baseline_measurable M hStruct.2.2.2.1
    (policyProp phi M.prop) x0 hOrder
  have hq := population_policyProp_measurable M hStruct.2.2.2.1 phi hphi
  have hb := population_bandBoundary_measurable M (policyProp phi M.prop) hq
    _ hOrder hlev
  have htarget := (discrete_reduction M hStruct.2.2.2.2.2.2 hend hStruct.1
    hStruct.2.1 hStruct.2.2.1 hStruct.2.2.2.1 hStruct.2.2.2.2.1
    hStruct.2.2.2.2.2.1 phi hphi x0 hGap hOrder hFinite).2.2.1
  dsimp only
  rw [htarget]
  exact (contDMLRegime_mean_variance_consistent_on_recovery M μ S I₁ I₂ hSplit
    phi dphi hphi hd hDerivative hStruct hend _ hK hOrder hlev
    (fun k hk j hj => hb k j hk hj) cpi hov hpol pHat rho gap ch eHat hr
    G hG hLevels).2

end Papers.TbsPrteOptimalTransport

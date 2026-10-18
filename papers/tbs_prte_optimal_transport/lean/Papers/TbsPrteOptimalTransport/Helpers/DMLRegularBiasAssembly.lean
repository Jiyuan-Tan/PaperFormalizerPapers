module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLRegularProductAssembly
/-! Assembly of the fractional binary product bias from the branch and residual envelopes.
These bounds retain the fitted instrument-event correction and its product of errors. -/
public section
set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- Expose the integrated residual cancellation used by the envelope lemma.
-- @node: fitted_regular_component_bias_integral_eq
/-- Assume [threshold crossing](hyp:h), [a valid policy map](hyp:hphi) [with the
specified derivative](hyp:hDiff), [a bounded Lipschitz policy derivative](hyp:hDerivative),
[covariate-invariant level ordering](hyp:hOrder), [baseline overlap](hyp:hov),
[an almost surely binary outcome](hyp:hy), and [admissible population and fitted
binary nuisances](hyp:he0,he). For [a positive denominator bound](hyp:hc) that
[bounds all fitted baseline event probabilities below almost surely](hyp:hpi) and
[all fitted policy event probabilities below almost surely](hyp:htau), and indices
with [the baseline index below the last level](hyp:hk) and [the policy index between
one and its level count](hyp:hj), [the expected fitted-weighted hinge difference plus
regression and policy mean corrections equals the expected fitted-weighted regular
score component minus the expected fitted-weighted population hinge](goal). -/
lemma fitted_regular_component_bias_integral_eq
    (h : ThresholdCrossing M) (phi dphi : Z → X → ℝ → ℝ)
    (hphi : IsPolicyMap phi) (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hy : OutcomeBinaryAE M)
    (he0 : BinAdmissible M L (eta0Bin M L)) (e : NuisanceBin L)
    (he : BinAdmissible M L e) (c : ℝ) (hc : 0 < c)
    (hpi : ∀ a, ∀ᵐ x ∂xLaw M, c ≤ e.piLev a x)
    (htau : ∀ a, ∀ᵐ x ∂xLaw M, c ≤ e.tauLev a x)
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k) :
    (∫ o : Obs X Z, regularValue e.gamma k j o.1 *
      (hMinus phi L e k j o.1 +
        binaryRegularRegressionMean phi L (eta0Bin M L) e k j o.1 +
        binaryRegularPolicyMean M phi dphi L e k j o.1 -
        hMinus phi L (eta0Bin M L) k j o.1) ∂observationLaw M) =
    (∫ o : Obs X Z, regularValue e.gamma k j o.1 *
      binScoreComponents phi dphi L e k j o ∂observationLaw M) -
    (∫ o : Obs X Z, regularValue e.gamma k j o.1 *
      hMinus phi L (eta0Bin M L) k j o.1 ∂observationLaw M) := by
  let a : RegularIndex L := ⟨(k,j), hk.le, hj⟩
  have hw : Measurable (regularValue e.gamma k j) := by
    change Measurable (fun x => regularValue e.gamma k j x)
    simpa only [regularValue, dif_pos (show k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k from
      ⟨hk.le, hj⟩)] using (he.2.2.2.2.2.1 a).2
  have hb : ∀ᵐ x ∂xLaw M, ‖regularValue e.gamma k j x‖ ≤ 1 := by
    filter_upwards [he.2.2.2.2.1 a] with x hx
    simp only [regularValue, dif_pos (show k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k from
      ⟨hk.le, hj⟩)]
    rw [Real.norm_eq_abs, abs_of_nonneg hx.2.1]
    exact hx.2.2
  have ht := population_binary_regular_component_correction_fitted_mean M h phi dphi
    hphi hDiff hDerivative L hOrder cpi hov hy he0 e he c hc hpi htau k j hk.le
    (regularValue e.gamma k j) hw 1 hb
  have iPlug := binary_weighted_hMinus_integrable_of_admissible M phi hphi L e he
    k j hk hj (regularValue e.gamma k j) hw 1 hb
  have iTrue := binary_weighted_hMinus_integrable_of_admissible M phi hphi L
    (eta0Bin M L) he0 k j hk hj (regularValue e.gamma k j) hw 1 hb
  have hs : (fun o : Obs X Z => regularValue e.gamma k j o.1 *
      binScoreComponents phi dphi L e k j o) =
      (fun o => regularValue e.gamma k j o.1 * hMinus phi L e k j o.1 +
        regularValue e.gamma k j o.1 *
          (binScoreComponents phi dphi L e k j o - hMinus phi L e k j o.1)) := by
    funext o
    ring
  rw [hs, integral_add iPlug ht.1, ht.2.2, ← integral_add iPlug ht.2.1,
    ← integral_sub (iPlug.fun_add ht.2.1) iTrue]
  apply integral_congr_ae
  exact Eventually.of_forall (fun o => by ring)

-- The event correction contributes only a product of fitted errors.
-- @node: fitted_regular_product_bias_envelope
/-- Assume [threshold crossing](hyp:h), [a valid policy map](hyp:hphi) [with the
specified derivative](hyp:hDiff), [a bounded Lipschitz policy derivative](hyp:hDerivative),
[covariate-invariant level ordering](hyp:hOrder), [baseline overlap](hyp:hov),
[an almost surely binary outcome](hyp:hy), and [admissible population and fitted
binary nuisances](hyp:he0,he). Suppose [the denominator bound is positive](hyp:hc),
[all fitted baseline event probabilities are at least that bound almost surely](hyp:hpi),
[all fitted policy event probabilities are at least that bound almost surely](hyp:htau), [the
baseline index is below the last level](hyp:hk), [the policy index lies between one
and its level count](hyp:hj), [the branch separation margin is positive](hyp:hsep),
[the common approximation-error envelope is square integrable under the observation
law](hyp:herr), and [the boundary, upper-policy, and lower-policy residual envelopes
are integrable](hyp:hEB,hEQ,hEL). If [the population policy gap and both branch
distances are at least the separation margin almost surely](hyp:hgap), [the common
envelope bounds both pooled-policy errors and the binary branch-threshold error
almost surely](hyp:herrors), and [the three residual envelopes bound the centered
boundary correction and the upper and lower pooled-policy corrections, including
the first-policy-index boundary term, almost surely](hyp:hres), then [the fitted
regular product score is integrable and its absolute mean bias relative to the
population gamma-weighted hinge is at most 26 divided by the separation margin
times the integrated squared approximation error, plus the three integrated
residual envelopes and the product of the gamma and hinge L2 errors](goal). -/
lemma fitted_regular_product_bias_envelope
    (h : ThresholdCrossing M) (phi dphi : Z → X → ℝ → ℝ)
    (hphi : IsPolicyMap phi) (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hy : OutcomeBinaryAE M)
    (he0 : BinAdmissible M L (eta0Bin M L)) (e : NuisanceBin L)
    (he : BinAdmissible M L e) (c : ℝ) (hc : 0 < c)
    (hpi : ∀ a, ∀ᵐ x ∂xLaw M, c ≤ e.piLev a x)
    (htau : ∀ a, ∀ᵐ x ∂xLaw M, c ≤ e.tauLev a x)
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k)
    (err EB EQ EL : X → ℝ) (sep : ℝ) (hsep : 0 < sep)
    (herr : MemLp (fun o : Obs X Z => err o.1) 2 (observationLaw M))
    (hEB : Integrable (fun o : Obs X Z => EB o.1) (observationLaw M))
    (hEQ : Integrable (fun o : Obs X Z => EQ o.1) (observationLaw M))
    (hEL : Integrable (fun o : Obs X Z => EL o.1) (observationLaw M))
    (hgap : ∀ᵐ x ∂xLaw M,
      sep ≤ pooledQBin phi L (eta0Bin M L) k j x - pooledQBin phi L (eta0Bin M L) k (j-1) x ∧
      sep ≤ |positiveValue (eta0Bin M L).pLev (k+1) x - binFullJ L (eta0Bin M L) k x -
        pooledQBin phi L (eta0Bin M L) k (j-1) x| ∧
      sep ≤ |positiveValue (eta0Bin M L).pLev (k+1) x - binFullJ L (eta0Bin M L) k x -
        pooledQBin phi L (eta0Bin M L) k j x|)
    (herrors : ∀ᵐ x ∂xLaw M,
      |pooledQBin phi L e k j x - pooledQBin phi L (eta0Bin M L) k j x| ≤ err x ∧
      |pooledQBin phi L e k (j-1) x - pooledQBin phi L (eta0Bin M L) k (j-1) x| ≤ err x ∧
      |(positiveValue e.pLev (k+1) x - binFullJ L e k x) -
        (positiveValue (eta0Bin M L).pLev (k+1) x - binFullJ L (eta0Bin M L) k x)| ≤ err x)
    (hres : ∀ᵐ x ∂xLaw M,
      let rP := fun i => positiveValue (eta0Bin M L).piLev i x *
        (positiveValue (eta0Bin M L).P1 i x - positiveValue e.P1 i x) / positiveValue e.piLev i x
      let rp := fun i => positiveValue (eta0Bin M L).piLev i x *
        (positiveValue (eta0Bin M L).pLev i x - positiveValue e.pLev i x) / positiveValue e.piLev i x
      let Q := fun i => ∑ z, instProb M z x * RqBin dphi L e k i (x,z,M.prop z x,0)
      |(rP (k+1) - rP k - rp (k+1)) -
        ((positiveValue e.pLev (k+1) x - binFullJ L e k x) -
          (positiveValue (eta0Bin M L).pLev (k+1) x - binFullJ L (eta0Bin M L) k x))| ≤ EB x ∧
      |Q j + (pooledQBin phi L e k j x - pooledQBin phi L (eta0Bin M L) k j x)| ≤ EQ x ∧
      |(if j = 1 then rp k else 0) + Q (j-1) +
        (pooledQBin phi L e k (j-1) x - pooledQBin phi L (eta0Bin M L) k (j-1) x)| ≤ EL x) :
    Integrable (psiProdBin phi dphi L e k j) (observationLaw M) ∧
    |(∫ o, psiProdBin phi dphi L e k j o ∂observationLaw M) -
      (∫ o : Obs X Z, gamma M L k j o.1 *
        hMinus phi L (eta0Bin M L) k j o.1 ∂observationLaw M)| ≤
      (26 / sep) * (∫ o : Obs X Z, err o.1 ^ 2 ∂observationLaw M) +
        (∫ o : Obs X Z, EB o.1 ∂observationLaw M) +
        (∫ o : Obs X Z, EQ o.1 ∂observationLaw M) +
        (∫ o : Obs X Z, EL o.1 ∂observationLaw M) +
        finiteL2Error M (regularValue e.gamma k j) (regularValue (eta0Bin M L).gamma k j) *
          finiteL2Error M (hMinus phi L e k j) (hMinus phi L (eta0Bin M L) k j) := by
  let a : RegularIndex L := ⟨(k,j), hk.le, hj⟩
  have hw : Measurable (regularValue e.gamma k j) := by
    change Measurable (fun x => regularValue e.gamma k j x)
    simpa only [regularValue, dif_pos (show k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k from
      ⟨hk.le, hj⟩)] using (he.2.2.2.2.2.1 a).2
  have hb : ∀ᵐ x ∂xLaw M, ‖regularValue e.gamma k j x‖ ≤ 1 := by
    filter_upwards [he.2.2.2.2.1 a] with x hx
    simp only [regularValue, dif_pos (show k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k from
      ⟨hk.le, hj⟩)]
    rw [Real.norm_eq_abs, abs_of_nonneg hx.2.1]
    exact hx.2.2
  have henv := (population_binary_regular_component_bias_envelope M h phi dphi
    hphi hDiff hDerivative L hOrder cpi hov hy he0 e he c hc hpi htau k j hk hj
    (regularValue e.gamma k j) hw 1 zero_le_one hb err EB EQ EL sep hsep
    herr hEB hEQ hEL hgap herrors hres).2
  rw [one_mul] at henv
  refine ⟨(fitted_regular_product_exact_bias M h phi dphi hphi hDiff hDerivative L hOrder
    cpi hov hy he0 e he c hc hpi htau k j hk hj).1, ?_⟩
  apply (fitted_regular_product_bias_L2_decomposition M h phi dphi hphi hDiff hDerivative
    L hOrder cpi hov hy he0 e he c hc hpi htau k j hk hj).trans
  rw [fitted_regular_component_bias_integral_eq M h phi dphi hphi hDiff hDerivative
    L hOrder cpi hov hy he0 e he c hc hpi htau k j hk hj]
  exact add_le_add henv le_rfl


-- Invalid indices and the structural zero have zero residual and zero error.
-- @node: fitted_positive_ipw_residual_centering_error
/-- If [the denominator bound is positive](hyp:hc) and [every fitted positive-index
weight at the chosen covariate value is at least that bound](hyp:hp), then [the
absolute difference between the inverse-probability-weighted reference-minus-fitted
value error and the unweighted reference-minus-fitted error is bounded by the
product of the absolute weight and value errors divided by the denominator bound,
including at indices whose extended values are zero](goal). -/
lemma fitted_positive_ipw_residual_centering_error {K : ℕ}
    (p0 p v0 v : PositiveIndex K → X → ℝ) (x : X) (c : ℝ) (hc : 0 < c)
    (hp : ∀ i, c ≤ p i x) (i : ℕ) :
    |positiveValue p0 i x * (positiveValue v0 i x - positiveValue v i x) /
        positiveValue p i x + (positiveValue v i x - positiveValue v0 i x)| ≤
      |positiveValue p i x - positiveValue p0 i x| *
        |positiveValue v i x - positiveValue v0 i x| / c := by
  by_cases hi : 1 ≤ i ∧ i ≤ K
  · simp only [positiveValue, dif_pos hi]
    exact fitted_ipw_residual_centering_error hc (hp ⟨i, hi⟩)
  · simp only [positiveValue, dif_neg hi]
    simp

-- This supplies EB in the regular-score envelope from actual nuisance errors.
-- All fitted residual corrections, including the k=0 boundary, are retained.
-- @node: fitted_regular_boundary_residual_error_bound
/-- If [the denominator bound is positive](hyp:hc) and [all fitted baseline event
probabilities at the chosen covariate value are at least that bound](hyp:hp), then
[the absolute discrepancy between the inverse-probability-weighted boundary residual
correction and the fitted-minus-reference binary branch threshold is bounded by
the next-level event-probability error times the sum of its success-probability and
propensity errors, plus the current-level event-probability error times its
success-probability error, all divided by the denominator bound](goal). -/
lemma fitted_regular_boundary_residual_error_bound (L : LevelData Z X)
    (e0 e : NuisanceBin L) (x : X) (c : ℝ) (hc : 0 < c)
    (hp : ∀ i, c ≤ e.piLev i x) (k : ℕ) :
    let rP := fun i => positiveValue e0.piLev i x *
      (positiveValue e0.P1 i x - positiveValue e.P1 i x) / positiveValue e.piLev i x
    let rp := fun i => positiveValue e0.piLev i x *
      (positiveValue e0.pLev i x - positiveValue e.pLev i x) / positiveValue e.piLev i x
    |(rP (k+1) - rP k - rp (k+1)) -
      ((positiveValue e.pLev (k+1) x - binFullJ L e k x) -
        (positiveValue e0.pLev (k+1) x - binFullJ L e0 k x))| ≤
      |positiveValue e.piLev (k+1) x - positiveValue e0.piLev (k+1) x| *
        (|positiveValue e.P1 (k+1) x - positiveValue e0.P1 (k+1) x| +
          |positiveValue e.pLev (k+1) x - positiveValue e0.pLev (k+1) x|) / c +
      |positiveValue e.piLev k x - positiveValue e0.piLev k x| *
        |positiveValue e.P1 k x - positiveValue e0.P1 k x| / c := by
  dsimp only
  have hPnext := fitted_positive_ipw_residual_centering_error
    e0.piLev e.piLev e0.P1 e.P1 x c hc hp (k+1)
  have hPprev := fitted_positive_ipw_residual_centering_error
    e0.piLev e.piLev e0.P1 e.P1 x c hc hp k
  have hpnext := fitted_positive_ipw_residual_centering_error
    e0.piLev e.piLev e0.pLev e.pLev x c hc hp (k+1)
  let E := fun (v0 v : PositiveIndex L.K → X → ℝ) i =>
    positiveValue e0.piLev i x * (positiveValue v0 i x - positiveValue v i x) /
      positiveValue e.piLev i x + (positiveValue v i x - positiveValue v0 i x)
  have hid :
      (positiveValue e0.piLev (k+1) x *
          (positiveValue e0.P1 (k+1) x - positiveValue e.P1 (k+1) x) /
            positiveValue e.piLev (k+1) x -
        positiveValue e0.piLev k x * (positiveValue e0.P1 k x - positiveValue e.P1 k x) /
          positiveValue e.piLev k x -
        positiveValue e0.piLev (k+1) x *
          (positiveValue e0.pLev (k+1) x - positiveValue e.pLev (k+1) x) /
            positiveValue e.piLev (k+1) x) -
        ((positiveValue e.pLev (k+1) x - binFullJ L e k x) -
          (positiveValue e0.pLev (k+1) x - binFullJ L e0 k x)) =
      E e0.P1 e.P1 (k+1) - E e0.P1 e.P1 k - E e0.pLev e.pLev (k+1) := by
    dsimp only [E, binFullJ]
    ring
  rw [hid]
  calc
    _ ≤ |E e0.P1 e.P1 (k+1)| + |E e0.P1 e.P1 k| + |E e0.pLev e.pLev (k+1)| :=
      (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ _ := by
      have ht := add_le_add (add_le_add hPnext hPprev) hpnext
      exact ht.trans_eq (by ring)

end Papers.TbsPrteOptimalTransport

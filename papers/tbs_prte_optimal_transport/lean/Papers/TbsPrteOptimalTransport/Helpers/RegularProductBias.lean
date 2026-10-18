module
public import Papers.TbsPrteOptimalTransport.Helpers.RegularComponentBias
/-! Fitted binary product scores: event centering and the remaining error product. -/
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

-- Center the event with the true probability even when the hinge is fitted.
-- No conditional identity or integrability of the fitted hinge is assumed.
-- @node: population_binary_fitted_hinge_event_centering
/-- For [an admissible policy](hyp:hphi), [an admissible fitted binary nuisance](hyp:he),
and [an admissible true binary nuisance](hyp:he0), with [k below the last treatment
level](hyp:hk) and [j a positive policy index in that interval](hyp:hj), [the fitted
negative hinge times the policy-union event indicator minus its true conditional
probability is integrable and has zero mean under the observation law](goal). -/
lemma population_binary_fitted_hinge_event_centering
    (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (L : LevelData Z X) (e : NuisanceBin L)
    (he : BinAdmissible M L e) (he0 : BinAdmissible M L (eta0Bin M L))
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k) :
    Integrable (fun o : Obs X Z => hMinus phi L e k j o.1 *
      (indicator (o.2.1 ∈ policyUnion L k j) - gamma M L k j o.1)) (observationLaw M) ∧
    (∫ o : Obs X Z, hMinus phi L e k j o.1 *
      (indicator (o.2.1 ∈ policyUnion L k j) - gamma M L k j o.1)
      ∂observationLaw M) = 0 := by
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  let a : RegularIndex L := ⟨(k,j), hk.le, hj⟩
  have hg : Measurable (gamma M L k j) := (he0.2.2.2.2.2.1 a).2
  have hgb : ∀ᵐ x ∂xLaw M, ‖gamma M L k j x‖ ≤ 1 := by
    filter_upwards [he0.2.2.2.2.1 a] with x hx
    have hr : gamma M L k j x ∈ Icc (0 : ℝ) 1 := hx.2
    rw [Real.norm_eq_abs, abs_of_nonneg hr.1]
    exact hr.2
  obtain ⟨H, hH, hHe⟩ := binary_hMinus_measurable_version M phi hphi L e he k j
  have ho := observationLaw_covariate_ae M _ hHe
  have ih : Integrable (fun o : Obs X Z => H o.1) (observationLaw M) := by
    apply Integrable.of_bound (hH.comp measurable_fst).aestronglyMeasurable 1
    filter_upwards [ho, observationLaw_covariate_ae M _
      (binary_auxiliary_ranges M phi L e hphi he k hk j hj.1 hj.2)] with o hEq hr
    change ‖H o.1‖ ≤ 1
    rw [hEq, Real.norm_eq_abs, abs_of_nonneg hr.1.1]
    exact hr.1.2
  have hi : Measurable (fun o : Obs X Z => indicator (o.2.1 ∈ policyUnion L k j)) := by
    first | fun_prop
          | unfold indicator
            exact Measurable.ite ((policyUnion L k j).finite_toSet.measurableSet.preimage
              measurable_snd.fst) measurable_const measurable_const
  have hib : ∀ᵐ o : Obs X Z ∂observationLaw M,
      ‖indicator (o.2.1 ∈ policyUnion L k j)‖ ≤ 1 := by
    apply Eventually.of_forall
    intro o
    unfold indicator
    split_ifs <;> norm_num
  have ie := ih.mul_bdd hi.aestronglyMeasurable hib
  have ig := ih.mul_bdd (hg.comp measurable_fst).aestronglyMeasurable
    (observationLaw_covariate_ae M _ hgb)
  have hz := population_instrument_event_residual_zero M (policyUnion L k j) H hH ie ig
  change (∫ o : Obs X Z, H o.1 *
    (indicator (o.2.1 ∈ policyUnion L k j) - gamma M L k j o.1)
    ∂observationLaw M) = 0 at hz
  have hEq : (fun o : Obs X Z => H o.1 *
      (indicator (o.2.1 ∈ policyUnion L k j) - gamma M L k j o.1)) =ᵐ[observationLaw M]
      (fun o : Obs X Z => hMinus phi L e k j o.1 *
      (indicator (o.2.1 ∈ policyUnion L k j) - gamma M L k j o.1)) := by
    filter_upwards [ho] with o hx
    rw [hx]
  refine ⟨?_, ?_⟩
  · have ir : Integrable (fun o : Obs X Z => H o.1 *
        (indicator (o.2.1 ∈ policyUnion L k j) - gamma M L k j o.1))
        (observationLaw M) := by
      simpa only [mul_sub, Function.comp_apply] using ie.sub' ig
    exact ir.congr hEq
  · rw [← integral_congr_ae hEq]
    exact hz

-- @node: binary_regular_product_bias_decomposition
/-- [The binary product score minus the true product of the policy-union probability
and negative hinge equals the fitted product weight times the component score error,
plus the fitted hinge times the centered policy-union indicator, minus the product of
the weight error and hinge error](goal). -/
lemma binary_regular_product_bias_decomposition
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X) (e : NuisanceBin L)
    (k j : ℕ) (o : Obs X Z) :
    psiProdBin phi dphi L e k j o - gamma M L k j o.1 * hMinus phi L (eta0Bin M L) k j o.1 =
    regularValue e.gamma k j o.1 *
      (binScoreComponents phi dphi L e k j o - hMinus phi L (eta0Bin M L) k j o.1) +
    hMinus phi L e k j o.1 *
      (indicator (o.2.1 ∈ policyUnion L k j) - gamma M L k j o.1) -
    (regularValue e.gamma k j o.1 - gamma M L k j o.1) *
      (hMinus phi L e k j o.1 - hMinus phi L (eta0Bin M L) k j o.1) := by
  unfold psiProdBin
  ring

-- A component bias estimate now propagates to the actual fitted product score.
-- The additional term is a product of two L2 errors, as in the paper roadmap.
-- @node: population_binary_regular_product_bias_bound
/-- For [an admissible policy](hyp:hphi), [an admissible fitted binary nuisance](hyp:he),
and [an admissible true binary nuisance](hyp:he0), with [k below the last treatment
level](hyp:hk) and [j a positive policy index in that interval](hyp:hj), suppose
[the fitted-weighted component score is integrable](hyp:hcomp), [the product-weight
error is square integrable](hyp:heg), and [the fitted hinge error is square integrable](hyp:heh).
Then [the binary product score is integrable and its absolute mean bias is bounded by
the absolute fitted-weighted component mean bias plus the product of the two error L2 norms](goal). -/
lemma population_binary_regular_product_bias_bound
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (L : LevelData Z X) (e : NuisanceBin L)
    (he : BinAdmissible M L e) (he0 : BinAdmissible M L (eta0Bin M L))
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k)
    (hcomp : Integrable (fun o : Obs X Z => regularValue e.gamma k j o.1 *
      binScoreComponents phi dphi L e k j o) (observationLaw M))
    (heg : MemLp (fun o : Obs X Z => regularValue e.gamma k j o.1 - gamma M L k j o.1)
      2 (observationLaw M))
    (heh : MemLp (fun o : Obs X Z => hMinus phi L e k j o.1 -
      hMinus phi L (eta0Bin M L) k j o.1) 2 (observationLaw M)) :
    Integrable (psiProdBin phi dphi L e k j) (observationLaw M) ∧
    |(∫ o, psiProdBin phi dphi L e k j o ∂observationLaw M) -
      (∫ o : Obs X Z, gamma M L k j o.1 * hMinus phi L (eta0Bin M L) k j o.1
        ∂observationLaw M)| ≤
    |(∫ o : Obs X Z, regularValue e.gamma k j o.1 * binScoreComponents phi dphi L e k j o
        ∂observationLaw M) -
      (∫ o : Obs X Z, regularValue e.gamma k j o.1 * hMinus phi L (eta0Bin M L) k j o.1
        ∂observationLaw M)| +
    (eLpNorm (fun o : Obs X Z => regularValue e.gamma k j o.1 - gamma M L k j o.1)
      2 (observationLaw M)).toReal *
    (eLpNorm (fun o : Obs X Z => hMinus phi L e k j o.1 -
      hMinus phi L (eta0Bin M L) k j o.1) 2 (observationLaw M)).toReal := by
  let a : RegularIndex L := ⟨(k,j), hk.le, hj⟩
  have hval : regularValue e.gamma k j = e.gamma a := by
    funext x
    simp only [regularValue, dif_pos (show k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k from ⟨hk.le, hj⟩)]
    rfl
  have hg : Measurable (regularValue e.gamma k j) := by
    rw [hval]
    exact (he.2.2.2.2.2.1 a).2
  have hgb : ∀ᵐ x ∂xLaw M, ‖regularValue e.gamma k j x‖ ≤ 1 := by
    rw [hval]
    filter_upwards [he.2.2.2.2.1 a] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg hx.2.1]
    exact hx.2.2
  have igh := binary_weighted_hMinus_integrable_of_admissible M phi hphi L (eta0Bin M L)
    he0 k j hk hj _ hg 1 hgb
  have hg0 : Measurable (gamma M L k j) := (he0.2.2.2.2.2.1 a).2
  have hgb0 : ∀ᵐ x ∂xLaw M, ‖gamma M L k j x‖ ≤ 1 := by
    filter_upwards [he0.2.2.2.2.1 a] with x hx
    have hr : gamma M L k j x ∈ Icc (0 : ℝ) 1 := hx.2
    rw [Real.norm_eq_abs, abs_of_nonneg hr.1]
    exact hr.2
  have itarget := binary_weighted_hMinus_integrable_of_admissible M phi hphi L (eta0Bin M L)
    he0 k j hk hj _ hg0 1 hgb0
  obtain ⟨icenter, zcenter⟩ := population_binary_fitted_hinge_event_centering M phi hphi
    L e he he0 k j hk hj
  have icross : Integrable (fun o : Obs X Z =>
      (regularValue e.gamma k j o.1 - gamma M L k j o.1) *
      (hMinus phi L e k j o.1 - hMinus phi L (eta0Bin M L) k j o.1))
      (observationLaw M) := by
    convert! heg.integrable_mul heh using 1
  have idiff := hcomp.sub' igh
  have hid : (fun o => psiProdBin phi dphi L e k j o -
      gamma M L k j o.1 * hMinus phi L (eta0Bin M L) k j o.1) =
      (fun o => regularValue e.gamma k j o.1 *
        (binScoreComponents phi dphi L e k j o - hMinus phi L (eta0Bin M L) k j o.1) +
        hMinus phi L e k j o.1 *
          (indicator (o.2.1 ∈ policyUnion L k j) - gamma M L k j o.1) -
        (regularValue e.gamma k j o.1 - gamma M L k j o.1) *
          (hMinus phi L e k j o.1 - hMinus phi L (eta0Bin M L) k j o.1)) :=
    funext (binary_regular_product_bias_decomposition M phi dphi L e k j)
  have id : Integrable (fun o : Obs X Z => regularValue e.gamma k j o.1 *
      (binScoreComponents phi dphi L e k j o - hMinus phi L (eta0Bin M L) k j o.1))
      (observationLaw M) := by simpa only [mul_sub] using idiff
  have ibias : Integrable (fun o => psiProdBin phi dphi L e k j o -
      gamma M L k j o.1 * hMinus phi L (eta0Bin M L) k j o.1) (observationLaw M) := by
    rw [hid]
    exact (id.fun_add icenter).sub' icross
  have iscore : Integrable (psiProdBin phi dphi L e k j) (observationLaw M) := by
    convert! ibias.fun_add itarget using 1
    funext o
    ring
  refine ⟨iscore, ?_⟩
  rw [← integral_sub iscore itarget, hid, integral_sub (id.fun_add icenter) icross,
    integral_add id icenter, zcenter, add_zero]
  have hc : |∫ o : Obs X Z, (regularValue e.gamma k j o.1 - gamma M L k j o.1) *
      (hMinus phi L e k j o.1 - hMinus phi L (eta0Bin M L) k j o.1)
      ∂observationLaw M| ≤ _ :=
    (show |∫ o : Obs X Z, (regularValue e.gamma k j o.1 - gamma M L k j o.1) *
      (hMinus phi L e k j o.1 - hMinus phi L (eta0Bin M L) k j o.1)
      ∂observationLaw M| ≤ ∫ o : Obs X Z,
      |(regularValue e.gamma k j o.1 - gamma M L k j o.1) *
      (hMinus phi L e k j o.1 - hMinus phi L (eta0Bin M L) k j o.1)|
      ∂observationLaw M from by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := observationLaw M)
          (fun o : Obs X Z => (regularValue e.gamma k j o.1 - gamma M L k j o.1) *
            (hMinus phi L e k j o.1 - hMinus phi L (eta0Bin M L) k j o.1))).trans
      (Causalean.Stat.integral_abs_mul_le_eLpNorm_mul_eLpNorm heg heh)
  have hm : (∫ o : Obs X Z, regularValue e.gamma k j o.1 *
      (binScoreComponents phi dphi L e k j o - hMinus phi L (eta0Bin M L) k j o.1)
      ∂observationLaw M) =
      (∫ o : Obs X Z, regularValue e.gamma k j o.1 * binScoreComponents phi dphi L e k j o
      ∂observationLaw M) - (∫ o : Obs X Z, regularValue e.gamma k j o.1 *
      hMinus phi L (eta0Bin M L) k j o.1 ∂observationLaw M) := by
    simp_rw [mul_sub]
    exact integral_sub hcomp igh
  rw [hm]
  exact (abs_sub _ _).trans (add_le_add le_rfl hc)

-- @node: population_binary_regular_product_bias_envelope
/-- Under [threshold crossing](hyp:h), [an admissible policy](hyp:hphi), [policy
differentiability with derivative dphi](hyp:hDiff), [a bounded Lipschitz derivative](hyp:hDerivative),
[invariant level ordering](hyp:hOrder), [baseline overlap with constant cpi](hyp:hov),
[binary outcomes almost surely](hyp:hy), and [admissible true](hyp:he0) and [fitted
binary nuisances](hyp:he), suppose [c is positive](hyp:hc), [fitted assignment masses](hyp:hpi)
and [pooling denominators](hyp:htau) are at least c almost everywhere, [k is below the
last treatment level](hyp:hk), and [j is a positive policy index in that interval](hyp:hj).
Assume [sep is positive](hyp:hsep), [err is square integrable](hyp:herr), [EB](hyp:hEB),
[EQ](hyp:hEQ), and [EL](hyp:hEL) are integrable, [the true endpoint gap and both boundary
distances are at least sep almost everywhere](hyp:hgap), [both pooled endpoint errors
and the boundary error are bounded by err almost everywhere](hyp:herrors), and [the
regression and two policy residual centering errors are bounded by EB, EQ, and EL almost
everywhere](hyp:hres). If [the product-weight error](hyp:heg) and [hinge error](hyp:heh)
are square integrable, [the binary product score is integrable and its absolute mean
bias is at most 26 divided by sep times the integrated squared error, plus the three
envelope integrals and the product of the weight-error and hinge-error L2 norms](goal). -/
lemma population_binary_regular_product_bias_envelope
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
        (pooledQBin phi L e k (j-1) x - pooledQBin phi L (eta0Bin M L) k (j-1) x)| ≤ EL x)
    (heg : MemLp (fun o : Obs X Z => regularValue e.gamma k j o.1 - gamma M L k j o.1)
      2 (observationLaw M))
    (heh : MemLp (fun o : Obs X Z => hMinus phi L e k j o.1 -
      hMinus phi L (eta0Bin M L) k j o.1) 2 (observationLaw M)) :
    Integrable (psiProdBin phi dphi L e k j) (observationLaw M) ∧
    |(∫ o, psiProdBin phi dphi L e k j o ∂observationLaw M) -
      (∫ o : Obs X Z, gamma M L k j o.1 * hMinus phi L (eta0Bin M L) k j o.1
        ∂observationLaw M)| ≤
    ((26 / sep) * (∫ o : Obs X Z, err o.1 ^ 2 ∂observationLaw M) +
      (∫ o : Obs X Z, EB o.1 ∂observationLaw M) +
      (∫ o : Obs X Z, EQ o.1 ∂observationLaw M) +
      (∫ o : Obs X Z, EL o.1 ∂observationLaw M)) +
    (eLpNorm (fun o : Obs X Z => regularValue e.gamma k j o.1 - gamma M L k j o.1)
      2 (observationLaw M)).toReal *
    (eLpNorm (fun o : Obs X Z => hMinus phi L e k j o.1 -
      hMinus phi L (eta0Bin M L) k j o.1) 2 (observationLaw M)).toReal := by
  let a : RegularIndex L := ⟨(k,j), hk.le, hj⟩
  have hval : regularValue e.gamma k j = e.gamma a := by
    funext x
    simp only [regularValue, dif_pos (show k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k from ⟨hk.le, hj⟩)]
    rfl
  have hg : Measurable (regularValue e.gamma k j) := by
    rw [hval]
    exact (he.2.2.2.2.2.1 a).2
  have hgb : ∀ᵐ x ∂xLaw M, ‖regularValue e.gamma k j x‖ ≤ 1 := by
    rw [hval]
    filter_upwards [he.2.2.2.2.1 a] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg hx.2.1]
    exact hx.2.2
  have hcpt := population_binary_regular_component_bias_envelope M h phi dphi hphi hDiff
    hDerivative L hOrder cpi hov hy he0 e he c hc hpi htau k j hk hj
    (regularValue e.gamma k j) hg 1 (by norm_num) hgb err EB EQ EL sep hsep
    herr hEB hEQ hEL hgap herrors hres
  have hprod := population_binary_regular_product_bias_bound M phi dphi hphi L e he he0
    k j hk hj hcpt.1 heg heh
  refine ⟨hprod.1, hprod.2.trans ?_⟩
  exact add_le_add (by simpa only [one_mul] using hcpt.2) le_rfl

end Papers.TbsPrteOptimalTransport

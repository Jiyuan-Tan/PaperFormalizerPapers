module
public import Papers.TbsPrteOptimalTransport.Helpers.RegularComponentBias
/-! Exact fitted fractional binary product bias, with the instrument-event
correction and all regression and policy residual corrections retained. -/
public section
set_option linter.style.openClassical false
set_option linter.unusedFintypeInType false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- A measurable version suffices: the original fitted propensity is clipped
-- almost everywhere, and the policy is only specified on the unit interval.
-- @node: fitted_regular_product_event_mean
/-- For [a valid policy map](hyp:hphi) and
[admissible true and fitted binary nuisance records](hyp:he0,he), if
[the baseline index is below the level count](hyp:hk) and
[the policy index is positive and within its level's policy count](hyp:hj),
[the fitted regular contrast times the policy-union indicator minus fitted union probability,
and the same contrast times true minus fitted union probability, are both integrable and
have equal means under the observation law](goal). -/
lemma fitted_regular_product_event_mean
    (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (L : LevelData Z X) (e : NuisanceBin L)
    (he0 : BinAdmissible M L (eta0Bin M L)) (he : BinAdmissible M L e)
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k) :
    Integrable (fun o : Obs X Z => hMinus phi L e k j o.1 *
      (indicator (o.2.1 ∈ policyUnion L k j) - regularValue e.gamma k j o.1))
      (observationLaw M) ∧
    Integrable (fun o : Obs X Z => hMinus phi L e k j o.1 *
      (gamma M L k j o.1 - regularValue e.gamma k j o.1)) (observationLaw M) ∧
    (∫ o : Obs X Z, hMinus phi L e k j o.1 *
      (indicator (o.2.1 ∈ policyUnion L k j) - regularValue e.gamma k j o.1)
      ∂observationLaw M) =
      ∫ o : Obs X Z, hMinus phi L e k j o.1 *
        (gamma M L k j o.1 - regularValue e.gamma k j o.1) ∂observationLaw M := by
  let a : RegularIndex L := ⟨(k,j), hk.le, hj⟩
  have hw : Measurable (regularValue e.gamma k j) := by
    change Measurable (fun x => regularValue e.gamma k j x)
    simpa only [regularValue, dif_pos (show k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k from
      ⟨hk.le, hj⟩)] using (he.2.2.2.2.2.1 a).2
  have hg : Measurable (gamma M L k j) := (he0.2.2.2.2.2.1 a).2
  have hb : ∀ᵐ x ∂xLaw M, ‖regularValue e.gamma k j x‖ ≤ 1 := by
    filter_upwards [he.2.2.2.2.1 a] with x hx
    simp only [regularValue, dif_pos (show k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k from
      ⟨hk.le, hj⟩)]
    rw [Real.norm_eq_abs, abs_of_nonneg hx.2.1]
    exact hx.2.2
  have hgb : ∀ᵐ x ∂xLaw M, ‖gamma M L k j x‖ ≤ 1 := by
    filter_upwards [he0.2.2.2.2.1 a] with x hx
    have hxg : gamma M L k j x ∈ Icc (0 : ℝ) 1 := hx.2
    rw [Real.norm_eq_abs, abs_of_nonneg hxg.1]
    exact hxg.2
  obtain ⟨H, hH, hHe⟩ := binary_hMinus_measurable_version M phi hphi L e he k j
  have hHo := observationLaw_covariate_ae M _ hHe
  have iH : Integrable (fun o : Obs X Z => H o.1) (observationLaw M) := by
    have hi := binary_weighted_hMinus_integrable_of_admissible M phi hphi L e he
      k j hk hj (fun _ => 1) measurable_const 1
      (Eventually.of_forall (fun _ => by norm_num))
    have hi' : Integrable (fun o : Obs X Z => hMinus phi L e k j o.1)
        (observationLaw M) := by simpa only [one_mul] using hi
    exact hi'.congr (hHo.mono (fun _ ho => ho.symm))
  have hi : Measurable (fun o : Obs X Z => indicator (o.2.1 ∈ policyUnion L k j)) := by
    fun_prop
  have hib : ∀ᵐ o : Obs X Z ∂observationLaw M,
      ‖indicator (o.2.1 ∈ policyUnion L k j)‖ ≤ 1 := by
    apply Eventually.of_forall
    intro o
    unfold indicator
    split_ifs <;> norm_num
  have iE := iH.mul_bdd hi.aestronglyMeasurable hib
  have iG : Integrable (fun o : Obs X Z => H o.1 * gamma M L k j o.1)
      (observationLaw M) := iH.mul_bdd (hg.comp measurable_fst).aestronglyMeasurable
    (observationLaw_covariate_ae M _ hgb)
  have iW : Integrable (fun o : Obs X Z => H o.1 * regularValue e.gamma k j o.1)
      (observationLaw M) := iH.mul_bdd (hw.comp measurable_fst).aestronglyMeasurable
    (observationLaw_covariate_ae M _ hb)
  have hz := population_instrument_event_residual_zero M (policyUnion L k j) H hH iE iG
  change (∫ o : Obs X Z, H o.1 *
    (indicator (o.2.1 ∈ policyUnion L k j) - gamma M L k j o.1)
    ∂observationLaw M) = 0 at hz
  simp_rw [mul_sub] at hz
  rw [integral_sub iE iG] at hz
  have hE : (fun o : Obs X Z => H o.1 *
      (indicator (o.2.1 ∈ policyUnion L k j) - regularValue e.gamma k j o.1)) =ᵐ[observationLaw M]
      (fun o => hMinus phi L e k j o.1 *
        (indicator (o.2.1 ∈ policyUnion L k j) - regularValue e.gamma k j o.1)) :=
    hHo.mono (fun _ ho => by dsimp only; rw [ho])
  have hG : (fun o : Obs X Z => H o.1 *
      (gamma M L k j o.1 - regularValue e.gamma k j o.1)) =ᵐ[observationLaw M]
      (fun o => hMinus phi L e k j o.1 *
        (gamma M L k j o.1 - regularValue e.gamma k j o.1)) :=
    hHo.mono (fun _ ho => by dsimp only; rw [ho])
  have iEc : Integrable (fun o : Obs X Z => H o.1 *
      (indicator (o.2.1 ∈ policyUnion L k j) - regularValue e.gamma k j o.1))
      (observationLaw M) := by simpa only [mul_sub] using iE.sub' iW
  have iGc : Integrable (fun o : Obs X Z => H o.1 *
      (gamma M L k j o.1 - regularValue e.gamma k j o.1))
      (observationLaw M) := by simpa only [mul_sub] using iG.sub' iW
  refine ⟨iEc.congr hE, iGc.congr hG, ?_⟩
  rw [← integral_congr_ae hE, ← integral_congr_ae hG]
  simp_rw [mul_sub]
  rw [integral_sub iE iW, integral_sub iG iW, sub_eq_zero.mp hz]

-- Both nuisance corrections are computed by the structural tower lemmas.
-- The fitted gamma error appears only multiplied by the fitted hinge error.
-- @node: fitted_regular_product_exact_bias
/-- Under [threshold crossing](hyp:h), [a valid policy map](hyp:hphi),
[the specified policy derivative](hyp:hDiff), [a bounded Lipschitz derivative](hyp:hDerivative),
[invariant level order](hyp:hOrder), [baseline overlap](hyp:hov),
[an almost surely binary outcome](hyp:hy), and
[admissible true and fitted binary nuisance records](hyp:he0,he), suppose
[the clipping threshold is positive](hyp:hc), [all fitted baseline-set probabilities](hyp:hpi)
and [all fitted policy-set probabilities](hyp:htau) are almost surely at least that threshold,
[the baseline index is below the level count](hyp:hk), and
[the policy index is positive and within its level's policy count](hyp:hj).
Then [the fitted regular product score is integrable and its bias relative to the true union
probability times the true regular contrast equals the mean of fitted union probability times
the fitted contrast plus its regression and policy residual means minus the true contrast,
less the product of the union-probability error and the regular-contrast error](goal). -/
lemma fitted_regular_product_exact_bias
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
    Integrable (psiProdBin phi dphi L e k j) (observationLaw M) ∧
    (∫ o, psiProdBin phi dphi L e k j o ∂observationLaw M) -
      (∫ o : Obs X Z, gamma M L k j o.1 *
        hMinus phi L (eta0Bin M L) k j o.1 ∂observationLaw M) =
      ∫ o : Obs X Z,
        regularValue e.gamma k j o.1 *
          (hMinus phi L e k j o.1 +
            binaryRegularRegressionMean phi L (eta0Bin M L) e k j o.1 +
            binaryRegularPolicyMean M phi dphi L e k j o.1 -
            hMinus phi L (eta0Bin M L) k j o.1) -
        (regularValue e.gamma k j o.1 - gamma M L k j o.1) *
          (hMinus phi L e k j o.1 - hMinus phi L (eta0Bin M L) k j o.1)
        ∂observationLaw M := by
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
  have hg : Measurable (gamma M L k j) := (he0.2.2.2.2.2.1 a).2
  have hgb : ∀ᵐ x ∂xLaw M, ‖gamma M L k j x‖ ≤ 1 := by
    filter_upwards [he0.2.2.2.2.1 a] with x hx
    have hxg : gamma M L k j x ∈ Icc (0 : ℝ) 1 := hx.2
    rw [Real.norm_eq_abs, abs_of_nonneg hxg.1]
    exact hxg.2
  have ht := population_binary_regular_component_correction_fitted_mean M h phi dphi
    hphi hDiff hDerivative L hOrder cpi hov hy he0 e he c hc hpi htau k j hk.le
    (regularValue e.gamma k j) hw 1 hb
  have iPlug := binary_weighted_hMinus_integrable_of_admissible M phi hphi L e he
    k j hk hj (regularValue e.gamma k j) hw 1 hb
  have iTarget := binary_weighted_hMinus_integrable_of_admissible M phi hphi L
    (eta0Bin M L) he0 k j hk hj (gamma M L k j) hg 1 hgb
  obtain ⟨iEvent, iMean, hEvent⟩ :=
    fitted_regular_product_event_mean M phi hphi L e he0 he k j hk hj
  have hsplit (o : Obs X Z) : regularValue e.gamma k j o.1 *
      binScoreComponents phi dphi L e k j o =
      regularValue e.gamma k j o.1 * hMinus phi L e k j o.1 +
      regularValue e.gamma k j o.1 *
        (binScoreComponents phi dphi L e k j o - hMinus phi L e k j o.1) := by ring
  have iScore : Integrable (fun o : Obs X Z => regularValue e.gamma k j o.1 *
      binScoreComponents phi dphi L e k j o) (observationLaw M) := by
    simp_rw [hsplit]
    exact iPlug.fun_add ht.1
  refine ⟨iScore.fun_add iEvent, ?_⟩
  simp only [psiProdBin]
  rw [integral_add iScore iEvent, hEvent]
  simp_rw [hsplit]
  rw [integral_add iPlug ht.1, ht.2.2, ← integral_add iPlug ht.2.1,
    ← integral_add (iPlug.fun_add ht.2.1) iMean,
    ← integral_sub ((iPlug.fun_add ht.2.1).fun_add iMean) iTarget]
  apply integral_congr_ae
  filter_upwards [] with o
  ring

end Papers.TbsPrteOptimalTransport

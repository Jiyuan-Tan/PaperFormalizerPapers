module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLBranchResidualBridge
public import Papers.TbsPrteOptimalTransport.Helpers.DMLRegularScoreConvergence
/-! Binary fractional product score convergence from branch energy.
Gamma nuisance rates control changing product weights; the regression and
policy correction bounds control their residual factors. -/
public section
set_option linter.style.openClassical false
set_option linter.unusedTactic false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
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

-- @node: nuisanceRates_weighted_regular_regression_correction_sq_tendsto_probability_zero_of_branch_convergence
/-- Assume [a valid policy map](hyp:hphi), [its specified derivative](hyp:hd),
[a bounded Lipschitz derivative](hyp:hDerivative), [admissible reference
nuisances](hyp:he0), [admissible fitted nuisances](hyp:heh), [binary outcomes
almost surely](hyp:hy), [a positive denominator bound](hyp:hc), and [reference
and fitted assignment probabilities bounded below almost everywhere](hyp:hclip).
With [quarter-rate control of instrument propensities](hyp:hrp),
[quarter-rate control of level propensities](hyp:hrlev),
[quarter-rate control of success regressions](hyp:hrP),
[quarter-rate control of assignment probabilities](hyp:hrpi),
[quarter-rate control of all regular cell shares](hyp:hrs),
[quarter-rate control of regular weights](hyp:hrg),
[a level below the level count](hyp:hk), [a valid positive
policy-cell index](hyp:hj), and [vanishing integrated squared errors of the
three branch indicators in probability](hyp:hbranch), [the regular regression
correction multiplied by its fitted regular weight has integrated squared error
tending to zero in probability along even sample sizes](goal). -/
lemma nuisanceRates_weighted_regular_regression_correction_sq_tendsto_probability_zero_of_branch_convergence
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e0 : NuisanceBin L) (eh : ℕ → A → NuisanceBin L)
    (he0 : BinAdmissible M L e0) (heh : ∀ n a, BinAdmissible M L (eh n a))
    (hy : OutcomeBinaryAE M) (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a (i : PositiveIndex L.K), ∀ᵐ x ∂xLaw M,
      c ≤ e0.piLev i x ∧ c ≤ (eh n a).piLev i x)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) e0.prop)
    (hrlev : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrP : FiniteNuisanceRates M μ (fun n a => (eh n a).P1) e0.P1)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) e0.piLev)
    (hrs : ∀ a : RegularIndex L,
      FiniteNuisanceRates M μ (fun n t => (eh n t).share a) (e0.share a))
    (hrg : FiniteNuisanceRates M μ (fun n a => (eh n a).gamma) e0.gamma)
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k)
    (hbranch : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o : Obs X Z,
        (Iact phi L (eh (2*(n+1)) a) k j o.1 - Iact phi L e0 k j o.1)^2 +
        (Dbd phi L (eh (2*(n+1)) a) k j o.1 - Dbd phi L e0 k j o.1)^2 +
        (Edom phi L (eh (2*(n+1)) a) k j o.1 - Edom phi L e0 k j o.1)^2
        ∂observationLaw M) atTop (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o : Obs X Z,
        (regularValue (eh (2*(n+1)) a).gamma k j o.1 *
            binaryRegularRegressionCorrection phi L (eh (2*(n+1)) a) k j o -
          regularValue e0.gamma k j o.1 *
            binaryRegularRegressionCorrection phi L e0 k j o)^2 ∂observationLaw M)
      atTop (fun _ _ => 0) := by
  let r : RegularIndex L := ⟨(k,j), hk.le, hj⟩
  have hg (e : NuisanceBin L) : regularValue e.gamma k j = e.gamma r := by
    funext x
    simp only [regularValue, dif_pos r.property, r]
  have hmp := observationLaw_fst_measurePreserving M
  have hw (e : NuisanceBin L) (he : BinAdmissible M L e) :=
    (fitted_regular_gamma_memLp M L e he k j).comp_measurePreserving hmp
  have hR (e : NuisanceBin L) (he : BinAdmissible M L e)
      (hpi : ∀ i, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x) :=
    fitted_regular_regression_correction_memLp M phi hphi L e he hy c hc hpi k j hk
  have hRm : AEStronglyMeasurable (binaryRegularRegressionCorrection phi L e0 k j)
      (observationLaw M) := by
    first | fun_prop | skip
    obtain ⟨hI, hD, hE⟩ := fitted_fractional_branches_memLp M phi hphi L e0 he0 k j
    have hi := (hI.comp_measurePreserving hmp).1
    have hd := (hD.comp_measurePreserving hmp).1
    have he := (hE.comp_measurePreserving hmp).1
    have hp := (fitted_RP_measurable M L e0 he0 (k+1)).aestronglyMeasurable (μ := observationLaw M)
    have hm := (fitted_RP_measurable M L e0 he0 k).aestronglyMeasurable (μ := observationLaw M)
    have ht := (fitted_Rp_measurable M L e0 he0 (k+1)).aestronglyMeasurable (μ := observationLaw M)
    have hb := (fitted_Rp_measurable M L e0 he0 k).aestronglyMeasurable (μ := observationLaw M)
    unfold binaryRegularRegressionCorrection
    by_cases hj : j = 1
    · simp only [if_pos hj]
      exact ((hd.mul (hp.sub hm)).sub (hd.mul ht)).sub ((he.mul hi).mul hb)
    · simp only [if_neg hj, sub_zero]
      exact (hd.mul (hp.sub hm)).sub (hd.mul ht)
  apply dml_ae_weighted_residual_sq_tendsto_probability_zero μ (observationLaw M)
    (fun o => regularValue e0.gamma k j o.1) (binaryRegularRegressionCorrection phi L e0 k j)
    (fun n a o => regularValue (eh (2*(n+1)) a).gamma k j o.1)
    (fun n a => binaryRegularRegressionCorrection phi L (eh (2*(n+1)) a) k j) 1 (4/c)
    (hw e0 he0).1
    hRm
    (fun n a => (hw _ (heh _ a)).1)
    (fun n a => (hR _ (heh _ a) (fun i => (hclip _ a i).mono (fun _ hx => hx.2))).1)
  · exact fun n a => (hw _ (heh _ a)).sub (hw e0 he0)
  · intro n a
    exact (hR _ (heh _ a) (fun i => (hclip _ a i).mono (fun _ hx => hx.2))).sub
      (hR e0 he0 (fun i => (hclip (2*(n+1)) a i).mono (fun _ hx => hx.1)))
  · exact fun n a => observationLaw_covariate_ae M _
      (fitted_regular_gamma_abs_bound M L _ (heh _ a) k j)
  · exact fun n a => fitted_regular_regression_correction_abs_bound M phi L e0 he0 hy c hc
      (fun i => (hclip n a i).mono (fun _ hx => hx.1)) k j hk
  · simpa only [hg] using nuisanceRates_covariate_sq_tendsto_probability_zero M μ e0.gamma
      (fun n a => (eh n a).gamma) (fun i => (he0.2.2.2.2.2.1 i).2)
      (fun n a i => ((heh n a).2.2.2.2.2.1 i).2) hrg r
  · exact nuisanceRates_regular_regression_correction_sq_tendsto_probability_zero_of_branch_convergence M μ
      phi dphi hphi hd hDerivative L e0 eh he0 heh hy c hc hclip
      hrp hrlev hrP hrpi hrs k j hk hbranch

-- @node: nuisanceRates_weighted_regular_policy_correction_sq_tendsto_probability_zero_of_branch_convergence
/-- For [a valid policy map](hyp:hphi) with [its specified derivative](hyp:hd)
and [a bounded Lipschitz derivative](hyp:hDerivative), assume [admissible
reference nuisances](hyp:he0), [admissible fitted nuisances](hyp:heh), [a
positive denominator bound](hyp:hc), and [reference and fitted regular-cell
probabilities bounded below almost everywhere](hyp:hclip). With
[quarter-rate control of instrument propensities](hyp:hrp),
[quarter-rate control of level propensities](hyp:hrlev),
[quarter-rate control of success regressions](hyp:hrP),
[quarter-rate control of regular-cell probabilities](hyp:hrt),
[quarter-rate control of all regular cell shares](hyp:hrs),
[quarter-rate control of regular weights](hyp:hrg),
[a level below the level count](hyp:hk), [a valid positive
policy-cell index](hyp:hj), and [vanishing integrated squared branch indicator
errors in probability](hyp:hbranch), [the regular policy correction multiplied
by its fitted regular weight has integrated squared error tending to zero in
probability along even sample sizes](goal). -/
lemma nuisanceRates_weighted_regular_policy_correction_sq_tendsto_probability_zero_of_branch_convergence
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e0 : NuisanceBin L) (eh : ℕ → A → NuisanceBin L)
    (he0 : BinAdmissible M L e0) (heh : ∀ n a, BinAdmissible M L (eh n a))
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a (r : RegularIndex L), ∀ᵐ x ∂xLaw M,
      c ≤ e0.tauLev r x ∧ c ≤ (eh n a).tauLev r x)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) e0.prop)
    (hrlev : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrP : FiniteNuisanceRates M μ (fun n a => (eh n a).P1) e0.P1)
    (hrt : FiniteNuisanceRates M μ (fun n a => (eh n a).tauLev) e0.tauLev)
    (hrs : ∀ r : RegularIndex L,
      FiniteNuisanceRates M μ (fun n a => (eh n a).share r) (e0.share r))
    (hrg : FiniteNuisanceRates M μ (fun n a => (eh n a).gamma) e0.gamma)
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k)
    (hbranch : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o : Obs X Z,
        (Iact phi L (eh (2*(n+1)) a) k j o.1 - Iact phi L e0 k j o.1)^2 +
        (Dbd phi L (eh (2*(n+1)) a) k j o.1 - Dbd phi L e0 k j o.1)^2 +
        (Edom phi L (eh (2*(n+1)) a) k j o.1 - Edom phi L e0 k j o.1)^2
        ∂observationLaw M) atTop (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o : Obs X Z,
        (regularValue (eh (2*(n+1)) a).gamma k j o.1 *
            binaryRegularPolicyCorrection phi dphi L (eh (2*(n+1)) a) k j o -
          regularValue e0.gamma k j o.1 *
            binaryRegularPolicyCorrection phi dphi L e0 k j o)^2 ∂observationLaw M)
      atTop (fun _ _ => 0) := by
  obtain ⟨B, D, hB, hD, hb⟩ := hDerivative
  have hDerivative : PolicyDerivativeBoundedLipschitz dphi := ⟨B, D, hB, hD, hb⟩
  let r : RegularIndex L := ⟨(k,j), hk.le, hj⟩
  have hg (e : NuisanceBin L) : regularValue e.gamma k j = e.gamma r := by
    funext x
    simp only [regularValue, dif_pos r.property, r]
  have hmp := observationLaw_fst_measurePreserving M
  have hw (e : NuisanceBin L) (he : BinAdmissible M L e) :=
    (fitted_regular_gamma_memLp M L e he k j).comp_measurePreserving hmp
  have hR (e : NuisanceBin L) (he : BinAdmissible M L e)
      (ht : ∀ r, ∀ᵐ x ∂xLaw M, c ≤ e.tauLev r x) :=
    fitted_regular_policy_correction_memLp M phi dphi hphi hd hDerivative L e he c hc ht k j hk.le
  have hRm : AEStronglyMeasurable (binaryRegularPolicyCorrection phi dphi L e0 k j)
      (observationLaw M) := by
    first | fun_prop | exact (fitted_regular_policy_correction_aestronglyMeasurable
      M phi dphi hphi hd hDerivative L e0 he0 k j hk.le)
  apply dml_ae_weighted_residual_sq_tendsto_probability_zero μ (observationLaw M)
    (fun o => regularValue e0.gamma k j o.1) (binaryRegularPolicyCorrection phi dphi L e0 k j)
    (fun n a o => regularValue (eh (2*(n+1)) a).gamma k j o.1)
    (fun n a => binaryRegularPolicyCorrection phi dphi L (eh (2*(n+1)) a) k j)
    1 (((L.T k j).card + (L.T k (j-1)).card) * B / c)
    (hw e0 he0).1 hRm (fun n a => (hw _ (heh _ a)).1)
    (fun n a => (hR _ (heh _ a) (fun r => (hclip _ a r).mono (fun _ hx => hx.2))).1)
  · exact fun n a => (hw _ (heh _ a)).sub (hw e0 he0)
  · intro n a
    exact (hR _ (heh _ a) (fun r => (hclip _ a r).mono (fun _ hx => hx.2))).sub
      (hR e0 he0 (fun r => (hclip (2*(n+1)) a r).mono (fun _ hx => hx.1)))
  · exact fun n a => observationLaw_covariate_ae M _
      (fitted_regular_gamma_abs_bound M L _ (heh _ a) k j)
  · exact fun n a => fitted_regular_policy_correction_abs_bound M phi dphi B hB
      (fun z x p hp => (hb z x p p hp hp).1) L e0 he0 c hc
      (fun r => (hclip n a r).mono (fun _ hx => hx.1)) k j hk.le
  · simpa only [hg] using nuisanceRates_covariate_sq_tendsto_probability_zero M μ e0.gamma
      (fun n a => (eh n a).gamma) (fun i => (he0.2.2.2.2.2.1 i).2)
      (fun n a i => ((heh n a).2.2.2.2.2.1 i).2) hrg r
  · exact nuisanceRates_regular_policy_correction_sq_tendsto_probability_zero_of_branch_convergence M μ
      phi dphi hphi hd hDerivative L e0 eh he0 heh c hc hclip
      hrp hrlev hrP hrt hrs k j hk.le hbranch

-- @node: nuisanceRates_regular_product_sq_tendsto_probability_zero_of_branch_convergence
/-- Under [a valid policy map](hyp:hphi), [its specified derivative](hyp:hd),
[a bounded Lipschitz derivative](hyp:hDerivative), [admissible reference
nuisances](hyp:he0), [admissible fitted nuisances](hyp:heh), and [binary outcomes
almost surely](hyp:hy), assume [a positive denominator bound](hyp:hc) with
[reference and fitted assignment probabilities bounded below almost everywhere](hyp:hpi)
and [reference and fitted regular-cell probabilities bounded below almost everywhere](hyp:htau).
If [instrument propensities satisfy quarter-rate control](hyp:hrp),
[level propensities satisfy quarter-rate control](hyp:hrlev),
[success regressions satisfy quarter-rate control](hyp:hrP),
[assignment probabilities satisfy quarter-rate control](hyp:hrpi),
[regular-cell probabilities satisfy quarter-rate control](hyp:hrt),
[all regular cell shares satisfy quarter-rate control](hyp:hrs),
[regular weights satisfy quarter-rate control](hyp:hrg), [the level is below the
level count](hyp:hk), [the policy-cell index is positive and valid](hyp:hj), and
[the integrated squared errors of the three branch indicators vanish in
probability](hyp:hbranch), [the binary regular product score has integrated
squared error tending to zero in probability along even sample sizes](goal). -/
lemma nuisanceRates_regular_product_sq_tendsto_probability_zero_of_branch_convergence
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e0 : NuisanceBin L) (eh : ℕ → A → NuisanceBin L)
    (he0 : BinAdmissible M L e0) (heh : ∀ n a, BinAdmissible M L (eh n a))
    (hy : OutcomeBinaryAE M) (c : ℝ) (hc : 0 < c)
    (hpi : ∀ n a (i : PositiveIndex L.K), ∀ᵐ x ∂xLaw M,
      c ≤ e0.piLev i x ∧ c ≤ (eh n a).piLev i x)
    (htau : ∀ n a (r : RegularIndex L), ∀ᵐ x ∂xLaw M,
      c ≤ e0.tauLev r x ∧ c ≤ (eh n a).tauLev r x)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) e0.prop)
    (hrlev : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrP : FiniteNuisanceRates M μ (fun n a => (eh n a).P1) e0.P1)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) e0.piLev)
    (hrt : FiniteNuisanceRates M μ (fun n a => (eh n a).tauLev) e0.tauLev)
    (hrs : ∀ r : RegularIndex L,
      FiniteNuisanceRates M μ (fun n a => (eh n a).share r) (e0.share r))
    (hrg : FiniteNuisanceRates M μ (fun n a => (eh n a).gamma) e0.gamma)
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k)
    (hbranch : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o : Obs X Z,
        (Iact phi L (eh (2*(n+1)) a) k j o.1 - Iact phi L e0 k j o.1)^2 +
        (Dbd phi L (eh (2*(n+1)) a) k j o.1 - Dbd phi L e0 k j o.1)^2 +
        (Edom phi L (eh (2*(n+1)) a) k j o.1 - Edom phi L e0 k j o.1)^2
        ∂observationLaw M) atTop (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o : Obs X Z,
        (psiProdBin phi dphi L (eh (2*(n+1)) a) k j o -
          psiProdBin phi dphi L e0 k j o)^2 ∂observationLaw M)
      atTop (fun _ _ => 0) := by
  let H := fun (e : NuisanceBin L) (o : Obs X Z) =>
    indicator (o.2.1 ∈ policyUnion L k j) * hMinus phi L e k j o.1
  let R := fun (e : NuisanceBin L) (o : Obs X Z) =>
    regularValue e.gamma k j o.1 * binaryRegularRegressionCorrection phi L e k j o
  let P := fun (e : NuisanceBin L) (o : Obs X Z) =>
    regularValue e.gamma k j o.1 * binaryRegularPolicyCorrection phi dphi L e k j o
  have hH (e : NuisanceBin L) (he : BinAdmissible M L e) :=
    fitted_event_hinge_memLp M phi hphi L e he k j hk hj
  have hR (e : NuisanceBin L) (he : BinAdmissible M L e)
      (hcl : ∀ i, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x) :=
    fitted_weighted_regular_regression_correction_memLp M phi hphi L e he hy c hc hcl k j hk
  have hP (e : NuisanceBin L) (he : BinAdmissible M L e)
      (hcl : ∀ r, ∀ᵐ x ∂xLaw M, c ≤ e.tauLev r x) :=
    fitted_weighted_regular_policy_correction_memLp M phi dphi hphi hd hDerivative
      L e he c hc hcl k j hk.le
  have hrH := nuisanceRates_event_hinge_sq_tendsto_probability_zero M μ phi dphi hphi hd
    hDerivative L e0 eh he0 heh hrp hrlev hrP hrs k j hk hj
  have hrR := nuisanceRates_weighted_regular_regression_correction_sq_tendsto_probability_zero_of_branch_convergence
    M μ phi dphi hphi hd hDerivative L e0 eh he0 heh hy c hc hpi
    hrp hrlev hrP hrpi hrs hrg k j hk hj hbranch
  have hrP' := nuisanceRates_weighted_regular_policy_correction_sq_tendsto_probability_zero_of_branch_convergence
    M μ phi dphi hphi hd hDerivative L e0 eh he0 heh c hc htau
    hrp hrlev hrP hrt hrs hrg k j hk hj hbranch
  have hs := dml_three_term_sq_tendsto_probability_zero μ (observationLaw M)
    (fun n a o => H (eh (2*(n+1)) a) o - H e0 o)
    (fun n a o => R (eh (2*(n+1)) a) o - R e0 o)
    (fun n a o => -(P (eh (2*(n+1)) a) o - P e0 o))
    (fun n a => (hH _ (heh _ a)).sub (hH e0 he0))
    (fun n a => (hR _ (heh _ a) (fun i => (hpi _ a i).mono (fun _ hx => hx.2))).sub
      (hR e0 he0 (fun i => (hpi (2*(n+1)) a i).mono (fun _ hx => hx.1))))
    (fun n a => ((hP _ (heh _ a) (fun r => (htau _ a r).mono (fun _ hx => hx.2))).sub
      (hP e0 he0 (fun r => (htau (2*(n+1)) a r).mono (fun _ hx => hx.1)))).neg)
    hrH hrR (by simpa only [P, neg_sq] using hrP')
  have hid (n : ℕ) (a : A) (o : Obs X Z) :
      psiProdBin phi dphi L (eh (2*(n+1)) a) k j o - psiProdBin phi dphi L e0 k j o =
      (H (eh (2*(n+1)) a) o - H e0 o) + (R (eh (2*(n+1)) a) o - R e0 o) -
        -(P (eh (2*(n+1)) a) o - P e0 o) := by
    simp only [psiProdBin_correction_split, H, R, P]
    ring
  simpa only [hid] using hs

end Papers.TbsPrteOptimalTransport

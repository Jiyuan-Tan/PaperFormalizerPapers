module
public import Papers.TbsPrteOptimalTransport.Helpers.PooledTreated
public import Papers.TbsPrteOptimalTransport.Helpers.JQuantileBands
public import Papers.TbsPrteOptimalTransport.Helpers.JBinaryBands
public import Papers.TbsPrteOptimalTransport.TDiscreteReduction
/-! TJSpecialization statements. -/
public section
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z]
variable (M : LatentIVModel Ω X Z)
variable [Fintype Z] [DecidableEq Z]
/-- Under [the structural model assumptions](hyp:h) and [known outcome endpoints](hyp:he),
if [the lower resistance threshold is nonnegative](hyp:ha), [the thresholds are ordered](hyp:hab),
and [both cumulative treated submeasures are supported on the outcome set](hyp:hsa,hsb), then
[the first moment of their difference equals the difference of the two canonical cumulative treated regressions](goal).

The compact outcome support supplies integrability for both summands. -/
-- @node: canonical_treated_increment_mean
lemma canonical_treated_increment_mean (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) (x : X) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hsa : canonSubmeasure M true x a M.Ysetᶜ = 0)
    (hsb : canonSubmeasure M true x b M.Ysetᶜ = 0) :
    (∫ y, y ∂(canonSubmeasure M true x b - canonSubmeasure M true x a)) =
      g1Canon M b x - g1Canon M a x := by
  let K := (outcomeKernel (latentMarginal M true)).comap
    (fun u : ℝ => (u, x)) (by fun_prop)
  letI := outcomeKernel_isMarkov (latentMarginal M true)
  let mu := (volume.restrict (Ioc 0 a)).bind K
  let nu := (volume.restrict (Ioc a b)).bind K
  letI : IsFiniteMeasure mu := ⟨(interval_kernel_finite K 0 a).lt_top⟩
  letI : IsFiniteMeasure nu := ⟨(interval_kernel_finite K a b).lt_top⟩
  have hadd : canonSubmeasure M true x b = mu + nu :=
    interval_kernel_add K 0 a b ha hab
  have hsnu : nu M.Ysetᶜ = 0 := by
    apply le_zero_iff.mp
    calc
      nu M.Ysetᶜ ≤ (mu + nu) M.Ysetᶜ := Measure.le_add_left le_rfl _
      _ = 0 := by rw [← hadd]; exact hsb
  have himu : Integrable (fun y : ℝ => y) mu := by
    exact Integrable.of_bound (by fun_prop) (outcomeMagnitude M)
      (supported_outcome_norm_bound M h he mu hsa)
  have hinu : Integrable (fun y : ℝ => y) nu := by
    exact Integrable.of_bound (by fun_prop) (outcomeMagnitude M)
      (supported_outcome_norm_bound M h he nu hsnu)
  rw [canonical_treated_increment M x a b ha hab]
  change (∫ y, y ∂nu) = (∫ y, y ∂canonSubmeasure M true x b) - ∫ y, y ∂mu
  rw [hadd, integral_add_measure himu hinu, add_sub_cancel_left]


/-- If [adjacent baseline propensity levels are strictly ordered at the given covariate value](hyp:hab),
then [the full-bin contribution equals the first moment of the difference between the cumulative treated submeasures at those levels](goal).

The baseline interval length cancels the normalization of its complier law. -/
-- @node: discrete_Jfull_eq_increment_mean
lemma discrete_Jfull_eq_increment_mean (L : LevelData Z X) (k : ℕ) (x : X)
    (hab : L.pLev k x < L.pLev (k+1) x) :
    Jfull M L k x =
      ∫ y, y ∂(canonSubmeasure M true x (L.pLev (k+1) x) -
        canonSubmeasure M true x (L.pLev k x)) := by
  have hw : 0 < L.pLev (k+1) x - L.pLev k x := sub_pos.mpr hab
  rw [Jfull, discreteGapLaw, integral_smul_measure, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hw.le, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hw.ne', one_mul]

/-- Under [the structural model assumptions](hyp:h), [known outcome endpoints](hyp:he), and
[a covariate-invariant ordering of baseline and policy propensity levels](hyp:hL),
[almost surely in covariates, every baseline interval's full-bin contribution equals the increment in the canonical treated regression between its endpoints](goal). -/
-- @node: discrete_Jfull_eq_regression_increment
lemma discrete_Jfull_eq_regression_increment (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) :
    ∀ᵐ x ∂xLaw M, ∀ k < L.K,
      Jfull M L k x = g1Canon M (L.pLev (k+1) x) x - g1Canon M (L.pLev k x) x := by
  filter_upwards [canonical_submeasure_supported M h true] with x hx
  intro k hk
  have ha := hL.2.2.2.2.2.2.2.2.2.2.1 x k (by omega)
  have hb := hL.2.2.2.2.2.2.2.2.2.2.1 x (k+1) (by omega)
  have hab := hL.2.2.2.2.2.2.2.1 x k (k+1) (by omega) (by omega)
  rw [discrete_Jfull_eq_increment_mean M L k x hab]
  exact canonical_treated_increment_mean M h he x _ _ ha.1 hab.le (hx _ ha) (hx _ hb)


/-- Under [the structural model assumptions](hyp:h), [known outcome endpoints](hyp:he),
[the finite-instrument reduction conditions](hyp:hFinite), and
[a covariate-invariant ordering of baseline and policy propensity levels](hyp:hL),
[each baseline interval's full-bin contribution almost surely equals the difference between the pooled observed treated moments at its upper and lower levels](goal). -/
-- @node: discrete_Jfull_eq_treatedSuccess_increment
lemma discrete_Jfull_eq_treatedSuccess_increment (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) (hFinite : InstrumentFiniteReduction Z)
    (q : Z → X → ℝ) (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L) :
    ∀ k < L.K, ∀ᵐ x ∂xLaw M,
      Jfull M L k x = treatedSuccess M L (k+1) x - treatedSuccess M L k x := by
  intro k hk
  filter_upwards [discrete_Jfull_eq_regression_increment M h he q L hL,
    treatedSuccess_eq_canonical_regression M h hFinite q L hL] with x hx hpool
  rw [hx k hk, hpool (k+1) (by omega), hpool k (by omega)]

-- @node: prop:j-specialization
/-- Assume [compact Borel domains](hyp:hDomains), [known outcome endpoints](hyp:hEndpoints),
[supported potential outcomes](hyp:hPotential), [consistency](hyp:hConsistency),
[instrument exogeneity](hyp:hExogeneity), [threshold crossing](hyp:hThreshold),
[uniform resistance](hyp:hUniform), and [common instrument support](hyp:hSupport).
For [an admissible policy](hyp:hPolicy), suppose [distinct baseline and policy propensity levels are separated](hyp:hGap),
[the reference level ordering is invariant across covariates](hyp:hOrder), and
[the finite-instrument reduction conditions hold](hyp:hFinite).
Then [each lower-bound band contribution is its baseline interval length times the outcome first moment between its quantile boundaries whenever the gap law is continuous there; for binary outcomes, full-bin contributions are pooled treated-moment increments, band contributions are positive-part overlap lengths, and substituting those lengths in the discrete formula gives the sharp lower bound](goal). -/
theorem J_specialization
    (hDomains : DomainsCompactBorel M) (hEndpoints : OutcomeEndpointsKnown M)
    (hPotential : PotentialSupport M) (hConsistency : Consistency M)
    (hExogeneity : InstrumentExogeneity M) (hThreshold : ThresholdCrossing M)
    (hUniform : UniformResistance M) (hSupport : CommonInstrumentSupport M)

    (phi : Z → X → ℝ → ℝ) (hPolicy : IsPolicyMap phi) (x0 : X)
    (hGap : PropensityGapSeparation M.prop (policyProp phi M.prop))
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop)
      (LevelStructure M.prop (policyProp phi M.prop) x0))
    (hFinite : InstrumentFiniteReduction Z) :
    let L := LevelStructure M.prop (policyProp phi M.prop) x0
    (∀ k < L.K, ∀ j < L.l k, GapLawContinuousAtBoundaries M L k j →
      ∀ᵐ x ∂xLaw M, Jband M false L k j x = (L.pLev (k+1) x - L.pLev k x) *
        ∫ y in Ioc (bandBoundary M L k j x) (bandBoundary M L k (j+1) x), y ∂discreteGapLaw M L k x) ∧
    (OutcomeBinary M →
      (∀ k < L.K, ∀ᵐ x ∂xLaw M, Jfull M L k x = treatedSuccess M L (k+1) x - treatedSuccess M L k x) ∧
      (∀ k < L.K, ∀ j, 1 ≤ j → j ≤ L.l k → ∀ᵐ x ∂xLaw M,
        Jband M false L k (j-1) x = max 0 (L.qLev k j x -
          max (L.qLev k (j-1) x) (L.pLev (k+1) x - Jfull M L k x))) ∧
      thetaLower1 (transportData M) (policyWeight M (policyProp phi M.prop)) =
        ∫ x, ((∑ k ∈ Finset.range L.K, (gammaFull M L k x * Jfull M L k x +
          ∑ j ∈ Finset.Icc 1 (L.l k), gamma M L k j x *
            max 0 (L.qLev k j x -
              max (L.qLev k (j-1) x) (L.pLev (k+1) x - Jfull M L k x)))) +
          tailContribution M false L (policyProp phi M.prop) x) ∂xLaw M) := by
  dsimp only
  constructor
  · intro k hk j hj hn
    exact continuous_discrete_Jband M
      ⟨hPotential, hConsistency, hExogeneity, hThreshold, hUniform, hSupport, hDomains⟩
      hEndpoints M.prop (policyProp phi M.prop) _ hOrder k j hk hj hn
  · intro hBinary
    let L := LevelStructure M.prop (policyProp phi M.prop) x0
    have hStructural : StructuralAssumptions M :=
      ⟨hPotential, hConsistency, hExogeneity, hThreshold, hUniform, hSupport, hDomains⟩
    have hMean : ∀ k < L.K, ∀ᵐ x ∂xLaw M,
        Jfull M L k x = treatedSuccess M L (k+1) x - treatedSuccess M L k x := by
      exact discrete_Jfull_eq_treatedSuccess_increment M hStructural hEndpoints hFinite
        (policyProp phi M.prop) L hOrder
    have hBand : ∀ k < L.K, ∀ j, 1 ≤ j → j ≤ L.l k → ∀ᵐ x ∂xLaw M,
        Jband M false L k (j-1) x = max 0 (L.qLev k j x -
          max (L.qLev k (j-1) x) (L.pLev (k+1) x - Jfull M L k x)) := by
      intro k hk j hj0 hj
      exact binary_discrete_Jband M hStructural hFinite hBinary
        (policyProp phi M.prop) L hOrder k j hk hj0 hj
    refine ⟨hMean, hBand, ?_⟩
    have hReduction := (discrete_reduction M hDomains hEndpoints hPotential hConsistency
      hExogeneity hThreshold hUniform hSupport phi hPolicy x0 hGap hOrder hFinite).2.2.1
    rw [hReduction]
    unfold discreteTarget
    have hAll : ∀ᵐ x ∂xLaw M, ∀ k < L.K, ∀ j, 1 ≤ j → j ≤ L.l k →
        Jband M false L k (j-1) x = max 0 (L.qLev k j x -
          max (L.qLev k (j-1) x) (L.pLev (k+1) x - Jfull M L k x)) := by
      simp only [ae_all_iff]
      exact hBand
    apply integral_congr_ae
    filter_upwards [hAll] with x hx
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [hx k (Finset.mem_range.mp hk) j (Finset.mem_Icc.mp hj).1
      (Finset.mem_Icc.mp hj).2]

end Papers.TbsPrteOptimalTransport

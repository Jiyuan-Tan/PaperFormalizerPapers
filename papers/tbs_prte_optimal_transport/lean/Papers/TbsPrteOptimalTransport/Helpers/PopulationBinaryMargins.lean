module
public import Papers.TbsPrteOptimalTransport.Helpers.JointResidualEnvelopes
public import Papers.TbsPrteOptimalTransport.Helpers.FittedBranchRegression
/-! Population separation supplies the margins for simultaneous binary product paths. -/
public section
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Set Filter
open scoped Classical Topology
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- The structural zero is excluded: zero need not be a realized propensity.
-- @node: population_binary_policy_spacing
/-- Suppose [baseline and policy levels have an invariant ordering](hyp:hOrder), [interior
policy levels avoid their bin's lower baseline boundary](hyp:hOff), [distinct combined
baseline and policy propensities are uniformly separated by more than the positive
gap](hyp:hGap), and [policy overlap holds](hyp:hpol). For [a bin before the final bin](hyp:hk)
and [a policy index between one and that bin's policy count](hyp:hj), [excluding the
first policy interval in the initial bin](hyp:hzero), [the upper pooled policy level
minus its predecessor exceeds the gap at every covariate value](goal). -/
lemma population_binary_policy_spacing
    (phi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (hOff : PolicyLevelOffBoundary L) (gap : ℝ)
    (hGap : PropensityGapSeparationWitness M.prop (policyProp phi M.prop) gap)
    (cpi : ℝ) (hpol : PolicyOverlap M L cpi)
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k)
    (hzero : k ≠ 0 ∨ j ≠ 1) (x : X) :
    gap < pooledQBin phi L (eta0Bin M L) k j x -
      pooledQBin phi L (eta0Bin M L) k (j-1) x := by
  rw [population_pooledQBin_eq_ordered_level M phi L hOrder cpi hpol k j hk.le hj.2,
    population_pooledQBin_eq_ordered_level M phi L hOrder cpi hpol k (j-1) hk.le (by omega)]
  obtain ⟨z, hz⟩ := ordered_policy_level_nonempty M _ L hOrder k j hk.le hj.1 hj.2
  have hqz := (hOrder.2.2.2.2.2.2.1 x k j z hk.le hj.1 hj.2).mp hz
  have hqmem : L.qLev k j x ∈ combinedPropensityRange M.prop (policyProp phi M.prop) x :=
    Or.inr ⟨z, hqz⟩
  have hlmem : L.qLev k (j-1) x ∈ combinedPropensityRange M.prop (policyProp phi M.prop) x := by
    by_cases hj1 : j = 1
    · subst j
      have hkpos : 1 ≤ k := by omega
      obtain ⟨w, hw⟩ := ordered_baseline_level_nonempty M _ L hOrder k ⟨hkpos, hk.le⟩
      have hpw := (hOrder.2.2.2.2.2.1 x k w hk.le).mp hw
      rw [hOrder.2.1 x k 0 hk.le (by omega), if_pos rfl]
      exact Or.inl ⟨w, hpw⟩
    · obtain ⟨w, hw⟩ := ordered_policy_level_nonempty M _ L hOrder k (j-1) hk.le
        (by omega) (by omega)
      exact Or.inr ⟨w, (hOrder.2.2.2.2.2.2.1 x k (j-1) w hk.le (by omega) (by omega)).mp hw⟩
  have hlt : L.qLev k (j-1) x < L.qLev k j x := by
    by_cases hj1 : j = 1
    · subst j
      have hidx : 0 < (policyLevelsAt M.prop (policyProp phi M.prop) x k).length := by
        rw [hOrder.2.2.2.2.1 x k hk.le]
        exact hj.2
      have hmem : L.qLev k 1 x ∈ policyLevelsAt M.prop (policyProp phi M.prop) x k := by
        rw [hOrder.2.1 x k 1 hk.le (by omega), if_neg (by omega), if_pos hj.2,
          List.getD_eq_getElem _ _ hidx]
        exact List.getElem_mem hidx
      have hb := (policyLevelsAt_mem_bounds M.prop (policyProp phi M.prop) x k hmem).1
      rw [← hOrder.1 x k (by omega)] at hb
      have hne := hOff k hk 1 le_rfl hj.2 ⟨z, hz⟩ x
      rw [hOrder.2.1 x k 0 hk.le (by omega), if_pos rfl]
      exact lt_of_le_of_ne hb (Ne.symm hne)
    · exact hOrder.2.2.2.2.2.2.2.2.1 x k (j-1) j hk.le (by omega) (by omega) hj.2
  rcases hGap.2 x _ hqmem _ hlmem with heq | hsep
  · exact False.elim (hlt.ne heq)
  · simpa only [abs_of_pos (sub_pos.mpr hlt)] using hsep

-- @node: population_binary_regular_joint_margins
/-- Under [the structural model assumptions](hyp:h), [known outcome endpoints](hyp:he),
and [finite discrete instrument reduction](hyp:hf), suppose [level ordering is invariant](hyp:hOrder),
[interior policy levels avoid lower baseline boundaries](hyp:hOff), [distinct combined
propensities are separated by more than the positive propensity gap](hyp:hGap), [policy
overlap holds](hyp:hpol), and [a positive outcome margin separates the regression
boundary from policy levels almost surely](hyp:hOutcome). For [a bin before the final
bin](hyp:hk) and [an interior policy index](hyp:hj), [excluding the first interval in
the initial bin](hyp:hzero), [the spacing between the two pooled policy endpoints
and the absolute distance of each endpoint from the upper baseline propensity
minus the treated-success increment are all at least the smaller of the propensity
gap and the outcome margin, almost surely in covariates](goal). -/
lemma population_binary_regular_joint_margins
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (hf : InstrumentFiniteReduction Z) (phi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (hOff : PolicyLevelOffBoundary L) (gap : ℝ)
    (hGap : PropensityGapSeparationWitness M.prop (policyProp phi M.prop) gap)
    (cpi : ℝ) (hpol : PolicyOverlap M L cpi) (ch : ℝ)
    (hOutcome : DiscreteOutcomeGapWitness M L ch)
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k)
    (hzero : k ≠ 0 ∨ j ≠ 1) :
    ∀ᵐ x ∂xLaw M,
      min gap ch ≤ pooledQBin phi L (eta0Bin M L) k j x -
        pooledQBin phi L (eta0Bin M L) k (j-1) x ∧
      min gap ch ≤ |positiveValue (eta0Bin M L).pLev (k+1) x -
        binFullJ L (eta0Bin M L) k x - pooledQBin phi L (eta0Bin M L) k (j-1) x| ∧
      min gap ch ≤ |positiveValue (eta0Bin M L).pLev (k+1) x -
        binFullJ L (eta0Bin M L) k x - pooledQBin phi L (eta0Bin M L) k j x| := by
  filter_upwards [population_binary_regression_endpoint_margins M h he hf phi L hOrder
    cpi hpol ch hOutcome k j hk hj] with x hx
  exact ⟨(min_le_left _ _).trans
    (population_binary_policy_spacing M phi L hOrder hOff gap hGap cpi hpol k j hk hj hzero x).le,
    (min_le_right _ _).trans hx.1, (min_le_right _ _).trans hx.2⟩

-- @node: population_binary_regular_product_joint_orthogonality_of_gap
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he), [finite
discrete instrument reduction](hyp:hf), and [an almost surely binary outcome](hyp:hy),
suppose [the policy map satisfies its policy restrictions](hyp:hphi), [its derivative
is the given derivative function](hyp:hDiff), [that derivative is bounded and Lipschitz](hyp:hDerivative),
[level ordering is invariant](hyp:hOrder), [interior policy levels avoid lower baseline
boundaries](hyp:hOff), and [a positive uniform gap separates distinct combined propensities](hyp:hGap).
With [baseline overlap](hyp:hov), [policy overlap](hyp:hpol), [a positive discrete outcome
gap](hyp:hOutcome), and [an admissible nuisance direction at the population truth](hyp:hd),
for [a bin before the final bin](hyp:hk) and [an interior policy index](hyp:hj), [excluding
the initial bin's first interval](hyp:hzero), [the regular product score is integrable
for all sufficiently small path values and its population mean has derivative zero
at zero along the simultaneous linear nuisance path](goal). -/
lemma population_binary_regular_product_joint_orthogonality_of_gap
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (hf : InstrumentFiniteReduction Z) (hy : OutcomeBinaryAE M)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi) (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (hOff : PolicyLevelOffBoundary L) (gap : ℝ)
    (hGap : PropensityGapSeparationWitness M.prop (policyProp phi M.prop) gap)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (hOutcome : DiscreteOutcomeGap M L) (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del))
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k)
    (hzero : k ≠ 0 ∨ j ≠ 1) :
    (∀ᶠ t : ℝ in nhds 0, Integrable
      (psiProdBin phi dphi L (eta0Bin M L + t • del) k j) (observationLaw M)) ∧
    HasDerivAt (fun t : ℝ => ∫ o, psiProdBin phi dphi L
      (eta0Bin M L + t • del) k j o ∂observationLaw M) 0 0 := by
  obtain ⟨ch, hch, hmargin⟩ := hOutcome
  exact population_binary_regular_product_joint_orthogonality_of_margins M h.2.2.2.1 hy
    phi dphi hphi hDiff hDerivative L hOrder cpi hov hpol del hd k j hk hj
    (min gap ch) (lt_min hGap.1 hch)
    (population_binary_regular_joint_margins M h he hf phi L hOrder hOff gap hGap cpi hpol
      ch ⟨hch, hmargin⟩ k j hk hj hzero)
end Papers.TbsPrteOptimalTransport

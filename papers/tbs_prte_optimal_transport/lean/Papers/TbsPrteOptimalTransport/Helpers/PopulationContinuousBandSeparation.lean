module
public import Papers.TbsPrteOptimalTransport.Helpers.BoundaryAtomFreedom
/-! Uniform separation of interior outcome boundaries from the population
propensity gap and the local density bound. The quantile moment is kept
unnormalized, so no lower bound on the latent stratum width is needed. -/
public section
set_option linter.style.openClassical false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

-- @node: local_interval_mass_gap_separates_endpoints
/-- If [the neighborhood radius is positive](hyp:hr), [the mass gap is positive](hyp:_hg),
[the lower endpoint does not exceed the upper endpoint](hyp:hab),
[their intervening interval has mass at least the gap](hyp:hm), and
[every interval in the radius-neighborhood of the upper endpoint has mass bounded
by the constant times its length](hyp:hd), [the endpoint distance is at least the
minimum of the radius and the gap divided by one plus the nonnegative part of the constant](goal). -/
lemma local_interval_mass_gap_separates_endpoints
    (μ : Measure ℝ) (a b r C gap : ℝ)
    (hr : 0 < r) (_hg : 0 < gap) (hab : a ≤ b)
    (hm : gap ≤ (μ (Ioc a b)).toReal)
    (hd : ∀ u v, b - r ≤ u → u ≤ v → v ≤ b + r →
      (μ (Ioc u v)).toReal ≤ C * (v - u)) :
    min r (gap / (max C 0 + 1)) ≤ b - a := by
  by_cases hnear : b - a ≤ r
  · have hmass := hd a b (by linarith) hab (by linarith)
    have hC : C ≤ max C 0 + 1 := by linarith [le_max_left C 0]
    have hlen : 0 ≤ b - a := sub_nonneg.mpr hab
    have hbound : gap ≤ (max C 0 + 1) * (b - a) :=
      hm.trans (hmass.trans (mul_le_mul_of_nonneg_right hC hlen))
    exact (min_le_right _ _).trans ((div_le_iff₀ (by positivity)).mpr (by
      simpa only [mul_comm] using hbound))
  · exact (min_le_left _ _).trans (le_of_not_ge hnear)

-- @node: weighted_cumulative_contrast_interval_bound
/-- For two finite measures, if [the lower endpoint is at most the upper endpoint](hyp:hab),
[the first cumulative-mass weight lies between zero and one](hyp:ha), and
[the second weight is nonnegative](hyp:hb), [the increase in the first weighted
cumulative mass minus the second is at most the first measure's mass between
the endpoints, excluding the lower and including the upper](goal). -/
lemma weighted_cumulative_contrast_interval_bound
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (a b alpha beta : ℝ) (hab : a ≤ b)
    (ha : alpha ∈ Icc (0 : ℝ) 1) (hb : 0 ≤ beta) :
    (alpha * μ.real (Iic b) - beta * ν.real (Iic b)) -
      (alpha * μ.real (Iic a) - beta * ν.real (Iic a)) ≤ μ.real (Ioc a b) := by
  have hdiff : μ.real (Ioc a b) = μ.real (Iic b) - μ.real (Iic a) := by
    rw [← Iic_sdiff_Iic, measureReal_sdiff (Iic_subset_Iic.mpr hab) measurableSet_Iic]
  have hn := measureReal_mono (μ := ν) (Iic_subset_Iic.mpr hab)
  have hnn : 0 ≤ μ.real (Iic b) - μ.real (Iic a) := by
    rw [← hdiff]
    exact measureReal_nonneg
  have hmul := mul_le_mul_of_nonneg_right ha.2 hnn
  have hminus := mul_nonneg hb (sub_nonneg.mpr hn)
  rw [hdiff]
  nlinarith

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: ordered_population_policy_pointwise_gap
/-- Under [covariate-invariant level ordering](hyp:hL) and [uniform separation of
distinct combined baseline and policy propensity values](hyp:hg), for
[a bin at or before the final bin](hyp:hk) and policy indices with
[the first at least one](hyp:hi), [the first strictly below the second](hyp:hij),
and [the second no larger than the policy-level count](hyp:hj),
[the higher policy level minus the lower is at least the separation constant at every fixed covariate](goal). -/
lemma ordered_population_policy_pointwise_gap
    (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (gap : ℝ)
    (hg : PropensityGapSeparationWitness M.prop q gap)
    (x : X) (k i j : ℕ) (hk : k ≤ L.K)
    (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ L.l k) :
    gap ≤ L.qLev k j x - L.qLev k i x := by
  obtain ⟨z, hz⟩ := ordered_policy_level_nonempty M q L hL k i hk hi (by omega)
  obtain ⟨w, hw⟩ := ordered_policy_level_nonempty M q L hL k j hk (by omega) hj
  have hz' := (hL.2.2.2.2.2.2.1 x k i z hk hi (by omega)).mp hz
  have hw' := (hL.2.2.2.2.2.2.1 x k j w hk (by omega) hj).mp hw
  have hs := hL.2.2.2.2.2.2.2.2.1 x k i j hk hi hij hj
  have hsep := hg.2 x (q z x) (Or.inr ⟨z, rfl⟩) (q w x) (Or.inr ⟨w, rfl⟩)
  rw [hz', hw'] at hsep
  rcases hsep with he | he
  · exact False.elim (hs.ne he.symm)
  · rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hs)] at he
    exact he.le

-- @node: population_continuous_interior_boundaries_uniformly_separated
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
[covariate-invariant level ordering](hyp:hL), [baseline overlap](hyp:hov),
[uniform propensity-gap separation](hyp:hg), [locally bounded treated-outcome
densities near band boundaries](hyp:hd), and [no treated-outcome atom at the lower
endpoint](hyp:h0), [there is a common positive distance separating every ordered
pair of interior policy boundaries in every nonfinal bin for almost every covariate](goal). -/
lemma population_continuous_interior_boundaries_uniformly_separated
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (cpi gap : ℝ)
    (hov : BaselineOverlapWitness M L cpi)
    (hg : PropensityGapSeparationWitness M.prop q gap)
    (hd : BoundaryDensitiesBounded M L) (h0 : NoAtomAtLowerEndpoint M L) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ k < L.K, ∀ i j : ℕ,
      1 ≤ i → i < j → j ≤ L.l k → ∀ᵐ x ∂xLaw M,
        delta ≤ bandBoundary M L k j x - bandBoundary M L k i x := by
  obtain ⟨r, C, hr, hden⟩ := hd
  let delta := min r (gap / (max C 0 + 1))
  refine ⟨delta, lt_min hr (div_pos hg.1 (by positivity)), ?_⟩
  intro k hk i j hi hij hj
  have hno := population_discrete_gap_boundaries_noAtom M h q L hL cpi hov
    ⟨r, C, hr, hden⟩ h0
  filter_upwards [discrete_band_boundary_cdf M h he M.prop q L hL,
    population_boundary_indicator_unnormalized_moment M h he q L hL cpi hov,
    hno, hden k hk j (by omega) hj (k+1) (Or.inl rfl)] with x hc hm hn hdx
  let a := bandBoundary M L k i x
  let b := bandBoundary M L k j x
  let := discrete_gap_law_probability M M.prop q L hL k hk x
  let := treatedLaw_isFiniteMeasure M L (k+1) x
  let := treatedLaw_isFiniteMeasure M L k x
  have hwidth := hL.2.2.2.2.2.2.2.1 x k (k+1) (by omega) (by omega)
  have hqgap := ordered_population_policy_pointwise_gap M q L hL gap hg x k i j hk.le hi hij hj
  have hrank : kappa L k i x < kappa L k j x := by
    unfold kappa
    exact div_lt_div_of_pos_right (by linarith [hg.1]) (sub_pos.mpr hwidth)
  have hab : a ≤ b := by
    by_contra hba
    have hcmono := monotone_cdf (discreteGapLaw M L k x) (le_of_not_ge hba)
    rw [hc k hk i (by omega) (hn k hk i (by omega)),
      hc k hk j hj (hn k hk j hj)] at hcmono
    exact (not_le_of_gt hrank) hcmono
  have hmoment (t : ℕ) (ht : t ≤ L.l k) :
      L.pLev (k+1) x * (treatedLaw M L (k+1) x).real
        (Iic (bandBoundary M L k t x)) -
      L.pLev k x * (treatedLaw M L k x).real
        (Iic (bandBoundary M L k t x)) = L.qLev k t x - L.pLev k x := by
    have hh := hm k hk t ht (hn k hk t ht)
    simp only [boundaryIndicatorMean, Bool.not_true, Bool.false_and,
      Bool.false_eq_true, if_false, if_true, Bool.not_false, Bool.true_and,
      beq_iff_eq] at hh
    by_cases hk0 : k = 0
    · have hp0 : L.pLev k x = 0 := by
        rw [hk0, hL.1 x 0 (by omega)]
        simp [pLevel]
      simpa only [measureReal_def, hp0, zero_mul, sub_zero] using (sub_eq_zero.mp hh)
    · simpa only [measureReal_def, hk0, if_false] using (sub_eq_zero.mp hh)
  have hmass : gap ≤ (treatedLaw M L (k+1) x (Ioc a b)).toReal := by
    have hbnd := weighted_cumulative_contrast_interval_bound
      (treatedLaw M L (k+1) x) (treatedLaw M L k x) a b
      (L.pLev (k+1) x) (L.pLev k x) hab
      (hL.2.2.2.2.2.2.2.2.2.2.1 x (k+1) (by omega))
      (hL.2.2.2.2.2.2.2.2.2.2.1 x k (by omega)).1
    dsimp only [a, b] at hbnd
    rw [hmoment j hj, hmoment i (by omega)] at hbnd
    exact hqgap.trans (by
      simpa only [measureReal_def, sub_sub_sub_cancel_right, a, b] using hbnd)
  exact local_interval_mass_gap_separates_endpoints _ a b r C gap hr hg.1 hab hmass hdx

end Papers.TbsPrteOptimalTransport

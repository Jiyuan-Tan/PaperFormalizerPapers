module
public import Papers.TbsPrteOptimalTransport.Helpers.AdmissibleBandBoundary
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationBinaryMargins
public import Papers.TbsPrteOptimalTransport.Helpers.BoundaryAtomFreedom
/-! Uniform interior quantile spacing and ordering along admissible paths. -/
public section
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

-- A rank increment dominated by a locally bounded-density measure cannot
-- occur over an arbitrarily short interval.
-- @node: quantile_spacing_of_dominated_rank_increment
/-- For a probability distribution and a finite dominating measure, suppose
[the distribution's weight is positive](hyp:hw), [the proposed rank gap is
positive](hyp:hgap), [the neighborhood radius is positive](hyp:hr), [the weighted
increase in the distribution function between two endpoints exceeds that
gap](hyp:hrank), [the weighted probability of every measurable set is bounded
by its dominating measure](hyp:hdom), and [the dominating measure of every
interval in the radius-neighborhood of the first endpoint is at most a common
constant times its length](hyp:hden). Then [the distance from the first endpoint
to the second is at least the smaller of the radius and the gap divided by one
plus the absolute value of that constant](goal). -/
lemma quantile_spacing_of_dominated_rank_increment
    (ν μ : Measure ℝ) [IsProbabilityMeasure ν] [IsFiniteMeasure μ]
    (a b w gap r C : ℝ) (hw : 0 < w) (hgap : 0 < gap) (hr : 0 < r)
    (hrank : gap < w * (cdf ν b - cdf ν a))
    (hdom : ∀ B : Set ℝ, MeasurableSet B → w * (ν B).toReal ≤ (μ B).toReal)
    (hden : ∀ u v, a - r ≤ u → u ≤ v → v ≤ a + r →
      (μ (Ioc u v)).toReal ≤ C * (v-u)) :
    min r (gap / (|C| + 1)) ≤ b-a := by
  have hab : a < b := by
    by_contra h
    have hba : b ≤ a := le_of_not_gt h
    have hm : cdf ν b ≤ cdf ν a := by
      rw [cdf_eq_real, cdf_eq_real]
      exact measureReal_mono (Iic_subset_Iic.mpr hba)
    have hz := mul_nonpos_of_nonneg_of_nonpos hw.le (sub_nonpos.mpr hm)
    linarith
  have hid : (ν (Ioc a b)).toReal = cdf ν b - cdf ν a := by
    rw [cdf_eq_real, cdf_eq_real]
    have hs : Iic b \ Iic a = Ioc a b := by
      ext y
      simp only [Set.mem_sdiff, mem_Iic, mem_Ioc, not_le]
      tauto
    rw [← hs]
    exact measureReal_sdiff (Iic_subset_Iic.mpr hab.le) measurableSet_Iic
  by_cases hlarge : r ≤ b-a
  · exact (min_le_left _ _).trans hlarge
  · have hb : b ≤ a+r := by linarith
    have hd := (hdom (Ioc a b) measurableSet_Ioc).trans (hden a b (by linarith) hab.le hb)
    rw [hid] at hd
    have hc := mul_le_mul_of_nonneg_right (le_abs_self C) (sub_nonneg.mpr hab.le)
    have hsmall : gap / (|C|+1) ≤ b-a := by
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith
    exact (min_le_right _ _).trans hsmall

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- The normalization cancellation holds for every measurable set, not only CDFs.
-- @node: discrete_gap_measure_unnormalized
/-- If [baseline and policy propensities respect the level ordering](hyp:hL) and
[the gap index is below the number of levels](hyp:hk), then [the probability of
any outcome set under the normalized gap distribution, multiplied by the
baseline propensity gap, equals its mass under the difference of the upper and
lower treated canonical submeasures](goal), at every covariate value. -/
lemma discrete_gap_measure_unnormalized (prop q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant prop q L) (k : ℕ) (hk : k < L.K) (x : X) (B : Set ℝ) :
    (L.pLev (k+1) x - L.pLev k x) * (discreteGapLaw M L k x B).toReal =
      ((canonSubmeasure M true x (L.pLev (k+1) x) -
        canonSubmeasure M true x (L.pLev k x)) B).toReal := by
  have hwidth := hL.2.2.2.2.2.2.2.1 x k (k+1) (by omega) (by omega)
  have hp : 0 < L.pLev (k+1) x - L.pLev k x := sub_pos.mpr hwidth
  rw [discreteGapLaw, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal hp.le]
  rw [← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul]

-- Interior policy levels are separated; their quantiles inherit a uniform
-- separation from the upper selected law's local density bound.
-- @node: population_continuous_interior_quantile_spacing
/-- Assume [the structural model conditions](hyp:h), [known outcome
endpoints](hyp:he), [ordering-compatible baseline and policy propensities](hyp:hL),
[nonempty policy levels distinct from their lower baseline boundary](hyp:hOff), [a positive uniform
separation of distinct baseline and policy propensity levels](hyp:hGap),
[baseline overlap](hyp:hov), [policy overlap](hyp:hpol), and [bounded boundary
densities](hyp:hd). For [a baseline gap below the number of levels](hyp:hk) and
[a policy boundary index at least one](hyp:hj0) and [strictly below the number
of policy levels in that gap](hyp:hj), [there is a positive constant that almost
surely bounds from below the distance between this band boundary and the next
one](goal). -/
lemma population_continuous_interior_quantile_spacing
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (phi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (hOff : PolicyLevelOffBoundary L) (gap : ℝ)
    (hGap : PropensityGapSeparationWitness M.prop (policyProp phi M.prop) gap)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (hd : BoundaryDensitiesBounded M L)
    (k j : ℕ) (hk : k < L.K) (hj0 : 1 ≤ j) (hj : j < L.l k) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᵐ x ∂xLaw M,
      ε ≤ bandBoundary M L k (j+1) x - bandBoundary M L k j x := by
  obtain ⟨r, C, hr, hden⟩ := hd
  have hd' : BoundaryDensitiesBounded M L := ⟨r, C, hr, hden⟩
  have hna := population_discrete_gap_noAtom_of_treated_upper M h _ L hL cpi hov k hk
    (bandBoundary M L k j)
    (population_treated_boundary_noAtom_of_density M L hd' k j hk hj0 (by omega)
      (k+1) (Or.inl rfl))
  have hnb := population_discrete_gap_noAtom_of_treated_upper M h _ L hL cpi hov k hk
    (bandBoundary M L k (j+1))
    (population_treated_boundary_noAtom_of_density M L hd' k (j+1) hk (by omega) hj
      (k+1) (Or.inl rfl))
  refine ⟨min r (gap / (|C|+1)), lt_min hr (div_pos hGap.1 (by positivity)), ?_⟩
  filter_upwards [hna, hnb, discrete_band_boundary_cdf M h he M.prop _ L hL,
    population_treated_cdf_unnormalized M h _ L hL,
    hden k hk j hj0 (by omega) (k+1) (Or.inl rfl)] with x hax hbx hc ht hdx
  letI := discrete_gap_law_probability M M.prop _ L hL k hk x
  letI := treatedLaw_isFiniteMeasure M L (k+1) x
  have hwidth := hL.2.2.2.2.2.2.2.1 x k (k+1) (by omega) (by omega)
  have hp := hL.2.2.2.2.2.2.2.2.2.2.1 x (k+1) (by omega)
  have hmass : M.instKernel x (L.S (k+1) : Set Z) ≠ 0 := by
    haveI := M.instKernel_markov
    have hs := sum_measureReal_singleton (μ := M.instKernel x) (L.S (k+1))
    have ho := hov.2 x (k+1) (by omega) (by omega)
    change cpi ≤ ∑ z ∈ L.S (k+1), (M.instKernel x {z}).toReal at ho
    change (∑ z ∈ L.S (k+1), (M.instKernel x {z}).toReal) =
      (M.instKernel x (L.S (k+1) : Set Z)).toReal at hs
    rw [hs] at ho
    exact fun hz => by simpa [hz] using hov.1.trans_le ho
  apply quantile_spacing_of_dominated_rank_increment (discreteGapLaw M L k x)
    (treatedLaw M L (k+1) x) _ _ (L.pLev (k+1) x - L.pLev k x)
    gap r C (sub_pos.mpr hwidth) hGap.1 hr
  · rw [hc k hk (j+1) hj hbx, hc k hk j (by omega) hax]
    have hs := population_binary_policy_spacing M phi L hL hOff gap hGap cpi hpol
      k (j+1) hk ⟨by omega, hj⟩ (Or.inr (by omega)) x
    simp only [Nat.add_sub_cancel] at hs
    rw [population_pooledQBin_eq_ordered_level M phi L hL cpi hpol k (j+1) hk.le hj,
      population_pooledQBin_eq_ordered_level M phi L hL cpi hpol k j hk.le (by omega)] at hs
    have hid : (L.pLev (k+1) x - L.pLev k x) *
        (kappa L k (j+1) x - kappa L k j x) = L.qLev k (j+1) x - L.qLev k j x := by
      unfold kappa
      field_simp [(sub_pos.mpr hwidth).ne']
      <;> ring
    rwa [hid]
  · intro B hB
    rw [discrete_gap_measure_unnormalized M M.prop _ L hL k hk x B]
    have hu := ht (k+1) (by omega) hmass B
    have hfinite : canonSubmeasure M true x (L.pLev (k+1) x) B ≠ ⊤ := by
      letI := outcomeKernel_isMarkov (latentMarginal M true)
      exact ne_top_of_le_ne_top
        (interval_kernel_finite ((outcomeKernel (latentMarginal M true)).comap
          (fun u : ℝ => (u,x)) (by fun_prop)) 0 (L.pLev (k+1) x))
        (measure_mono (subset_univ B))
    have hm := ENNReal.toReal_mono hfinite (Measure.sub_le (μ := canonSubmeasure M true x (L.pLev (k+1) x))
      (ν := canonSubmeasure M true x (L.pLev k x)) B)
    rw [← hu hB] at hm
    exact hm.trans (mul_le_of_le_one_left ENNReal.toReal_nonneg hp.2)
  · exact hdx

-- Uniformly bounded directions cannot cross the uniformly separated true endpoints.
-- @node: continuous_admissible_interior_band_ordered_path
/-- Assume [the structural model conditions](hyp:h), [known outcome
endpoints](hyp:he), [ordering-compatible baseline and policy propensities](hyp:hL),
[nonempty policy levels distinct from their lower baseline boundary](hyp:hOff), [a positive uniform
separation of distinct baseline and policy propensity levels](hyp:hGap),
[baseline overlap](hyp:hov), [policy overlap](hyp:hpol), [bounded boundary
densities](hyp:hden), and [an admissible nuisance direction at the truth](hyp:hd).
For [a baseline gap below the number of levels](hyp:hk) and [a policy boundary
index at least one](hyp:hj0) and [strictly below the number of policy levels in
that gap](hyp:hj), [the perturbed boundary remains almost surely no larger than
the next perturbed boundary for every sufficiently small step](goal). -/
lemma continuous_admissible_interior_band_ordered_path
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (phi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (hOff : PolicyLevelOffBoundary L) (gap : ℝ)
    (hGap : PropensityGapSeparationWitness M.prop (policyProp phi M.prop) gap)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (hden : BoundaryDensitiesBounded M L) (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del))
    (k j : ℕ) (hk : k < L.K) (hj0 : 1 ≤ j) (hj : j < L.l k) :
    ∀ᶠ t : ℝ in 𝓝 0, ∀ᵐ x ∂xLaw M,
      nuValue M (trueNuisance M L + t • del) k j x ≤
        nuValue M (trueNuisance M L + t • del) k (j+1) x := by
  obtain ⟨ε, hε, hspace⟩ := population_continuous_interior_quantile_spacing
    M h he phi L hL hOff gap hGap cpi hov hpol hden k j hk hj0 hj
  obtain ⟨C, hC, hdir⟩ := continuous_quantile_direction_regular M L _ del hd
  let a : BoundaryIndex L := ⟨(k,j), hk, hj0, Nat.le_of_lt hj⟩
  let b : BoundaryIndex L := ⟨(k,j+1), hk, by omega, hj⟩
  have hr : 0 < ε / (2 * (C+1)) := div_pos hε (by positivity)
  filter_upwards [continuousAt_id.abs.eventually_lt_const (by simpa using hr)] with t ht
  change |t| < ε / (2 * (C+1)) at ht
  filter_upwards [hspace, (hdir a).2, (hdir b).2] with x hs ha hb
  have hva : k < L.K ∧ 1 ≤ j ∧ j ≤ L.l k := ⟨hk, hj0, by omega⟩
  have hvb : k < L.K ∧ 1 ≤ j+1 ∧ j+1 ≤ L.l k := ⟨hk, by omega, hj⟩
  simp only [nuValue, show j ≠ 0 by omega, Nat.add_one_ne_zero, if_false,
    dif_pos hva, dif_pos hvb]
  change bandBoundary M L k j x + t * del.nu a x ≤
    bandBoundary M L k (j+1) x + t * del.nu b x
  have hma : |t * del.nu a x| ≤ |t| * C := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using ha)
      (abs_nonneg t)
  have hmb : |t * del.nu b x| ≤ |t| * C := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using hb)
      (abs_nonneg t)
  have hsmall := (lt_div_iff₀ (by positivity : 0 < 2 * (C+1))).mp ht
  nlinarith [le_abs_self (t * del.nu a x), neg_abs_le (t * del.nu b x), abs_nonneg t]

-- The previous signed boundary cancellation now applies to every admissible
-- direction under the paper's assumptions, without a separate ordering gate.
-- @node: population_continuous_interior_band_signed_quantile_block_orthogonality_of_gap
/-- Assume [the structural model conditions](hyp:h), [known outcome
endpoints](hyp:he), [ordering-compatible baseline and policy propensities](hyp:hL),
[nonempty policy levels distinct from their lower baseline boundary](hyp:hOff), [a positive uniform
separation of distinct baseline and policy propensity levels](hyp:hGap),
[baseline overlap](hyp:hov), [policy overlap](hyp:hpol), [bounded boundary
densities](hyp:hden), and [an admissible nuisance direction at the truth](hyp:hd).
For [a baseline gap below the number of levels](hyp:hk) and [a policy boundary
index at least one](hyp:hj0) and [strictly below the number of policy levels in
that gap](hyp:hj), suppose [the lower band boundary is measurable](hyp:ha) and
[the upper band boundary is measurable](hyp:hb). Then [the population mean of
the upper-minus-lower quantile influence-block change from moving both
boundaries rather than holding them at truth, with assignment probabilities
moving in both terms and weighted by a moving regular-component weight, has
derivative zero at step zero](goal). -/
lemma population_continuous_interior_band_signed_quantile_block_orthogonality_of_gap
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (phi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (hOff : PolicyLevelOffBoundary L) (gap : ℝ)
    (hGap : PropensityGapSeparationWitness M.prop (policyProp phi M.prop) gap)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (hden : BoundaryDensitiesBounded M L) (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del))
    (k : ℕ) (hk : k < L.K) (j : ℕ) (hj0 : 1 ≤ j) (hj : j < L.l k)
    (g : RegularIndex L) (ha : Measurable (bandBoundary M L k j))
    (hb : Measurable (bandBoundary M L k (j+1))) :
    let path := fun t : ℝ => trueNuisance M L + t • del
    let e := fun t => {trueNuisance M L with piLev := (path t).piLev, nu := (path t).nu}
    let b := fun t => {trueNuisance M L with piLev := (path t).piLev}
    let block := fun plus t (o : Obs X Z) =>
      (IFJ M L (e t) plus k j o + nuValue M (e t) k j o.1 * IFM M L (e t) plus k j o -
        nuValue M (e t) k (j+1) o.1 * IFM M L (e t) plus k (j+1) o) -
      (IFJ M L (b t) plus k j o + bandBoundary M L k j o.1 * IFM M L (b t) plus k j o -
        bandBoundary M L k (j+1) o.1 * IFM M L (b t) plus k (j+1) o)
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z, (path t).gamma g o.1 *
      (block true t o - block false t o) ∂observationLaw M) 0 0 := by
  exact population_continuous_interior_band_admissible_signed_quantile_block_orthogonality
    M L hden cpi hov del hd k hk j hj0 hj g ha hb
    (continuous_admissible_interior_band_ordered_path M h he phi L hL hOff gap hGap
      cpi hov hpol hden del hd k j hk hj0 hj)

end Papers.TbsPrteOptimalTransport

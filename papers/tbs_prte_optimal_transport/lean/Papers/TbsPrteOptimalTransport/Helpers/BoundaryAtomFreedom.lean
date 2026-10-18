module
public import Papers.TbsPrteOptimalTransport.Helpers.GapQuantileMoments
public import Papers.TbsPrteOptimalTransport.Helpers.QuantileScoreRemainder
/-! Atom-free score boundaries derived from the continuous DML regime. -/
public section
set_option linter.unusedSectionVars false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical

-- Shrinking a left interval to its right endpoint rules out an atom there.
-- @node: singleton_null_of_local_interval_bound
/-- For a finite measure, if [a neighborhood radius is positive](hyp:hr) and
[every left-open, right-closed interval within that neighborhood of v has
mass at most C times its length](hyp:h), then [the singleton containing v
has measure zero](goal). -/
lemma singleton_null_of_local_interval_bound (μ : Measure ℝ) [IsFiniteMeasure μ]
    (v r C : ℝ) (hr : 0 < r)
    (h : ∀ a b, v - r ≤ a → a ≤ b → b ≤ v + r →
      (μ (Ioc a b)).toReal ≤ C * (b - a)) : μ {v} = 0 := by
  have hz : (μ {v}).toReal ≤ 0 := by
    apply le_of_forall_pos_le_add
    intro ε hε
    let d := min r (ε / (|C| + 1))
    have hd : 0 < d := lt_min hr (div_pos hε (by positivity))
    have hdr : d ≤ r := min_le_left _ _
    have hde : d * (|C| + 1) ≤ ε := by
      exact (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    have hs : ({v} : Set ℝ) ⊆ Ioc (v - d) v := by
      intro y hy
      rcases mem_singleton_iff.mp hy with rfl
      exact ⟨by linarith, le_rfl⟩
    have hm := measureReal_mono (μ := μ) hs
    have hb := h (v - d) v (by linarith) (by linarith) (by linarith)
    change (μ {v}).toReal ≤ (μ (Ioc (v - d) v)).toReal at hm
    have hc := le_abs_self C
    have hcd : C * d ≤ |C| * d := mul_le_mul_of_nonneg_right hc hd.le
    have hdd : 0 ≤ d := hd.le
    nlinarith
  have hz' : (μ {v}).toReal = 0 := le_antisymm hz ENNReal.toReal_nonneg
  exact ((ENNReal.toReal_eq_zero_iff _).mp hz').resolve_right (measure_ne_top _ _)

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: population_treated_boundary_noAtom_of_density
/-- If [treated boundary densities satisfy the local boundedness condition](hyp:h),
[the level index is below the level count](hyp:hk), [the band index is at
least one](hyp:hj) and [at most that level's band count](hyp:hjl), and [the
treated-law index is the upper adjacent level or the positive lower adjacent
level](hyp:hi), then [the treated law places zero mass at that band boundary
for almost every covariate value](goal). -/
lemma population_treated_boundary_noAtom_of_density
    (L : LevelData Z X) (h : BoundaryDensitiesBounded M L)
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j) (hjl : j ≤ L.l k)
    (i : ℕ) (hi : i = k + 1 ∨ (1 ≤ k ∧ i = k)) :
    ∀ᵐ x ∂xLaw M, treatedLaw M L i x {bandBoundary M L k j x} = 0 := by
  obtain ⟨r, C, hr, hd⟩ := h
  filter_upwards [hd k hk j hj hjl i hi] with x hx
  letI := treatedLaw_isFiniteMeasure M L i x
  exact singleton_null_of_local_interval_bound _ _ r C hr hx

-- The gap submeasure is the nonnegative increment of two treated
-- submeasures. An atom absent in the upper one is absent in the increment.
-- @node: population_discrete_gap_noAtom_of_treated_upper
/-- Under [the structural assumptions](hyp:h), [invariant ordering of the
baseline and comparison propensity levels](hyp:hL), and [baseline
overlap](hyp:hov), if [the level index is below the level count](hyp:hk) and
[the upper adjacent treated law has no atom at the covariate-dependent
value almost everywhere](hyp:hn), then [the discrete gap law also has no
atom at that value almost everywhere](goal). -/
lemma population_discrete_gap_noAtom_of_treated_upper
    (h : StructuralAssumptions M) (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (cpi : ℝ)
    (hov : BaselineOverlapWitness M L cpi) (k : ℕ) (hk : k < L.K)
    (v : X → ℝ) (hn : ∀ᵐ x ∂xLaw M, treatedLaw M L (k + 1) x {v x} = 0) :
    ∀ᵐ x ∂xLaw M, discreteGapLaw M L k x {v x} = 0 := by
  haveI := M.instKernel_markov
  filter_upwards [population_treated_cdf_unnormalized M h q L hL, hn] with x hx hnx
  have hmass : M.instKernel x (L.S (k + 1) : Set Z) ≠ 0 := by
    have hp := hov.2 x (k + 1) (by omega) (by omega)
    have hs := sum_measureReal_singleton (μ := M.instKernel x) (L.S (k + 1))
    change (∑ z ∈ L.S (k + 1), (M.instKernel x {z}).toReal) =
      (M.instKernel x (L.S (k + 1) : Set Z)).toReal at hs
    change cpi ≤ ∑ z ∈ L.S (k + 1), (M.instKernel x {z}).toReal at hp
    rw [hs] at hp
    have hpos := hov.1.trans_le hp
    exact fun hz => by simpa [hz] using hpos
  have hu := hx (k + 1) (by omega) hmass {v x} (measurableSet_singleton _)
  rw [hnx, ENNReal.toReal_zero, mul_zero] at hu
  have ha := hL.2.2.2.2.2.2.2.2.2.2.1 x k (by omega)
  have hab := hL.2.2.2.2.2.2.2.1 x k (k + 1) (by omega) (by omega)
  have hz : ((canonSubmeasure M true x (L.pLev (k + 1) x) -
      canonSubmeasure M true x (L.pLev k x)) {v x}).toReal = 0 := by
    rw [canonical_treated_increment_real M x _ _ ha.1 hab.le, ← hu, zero_sub]
    have hn := ENNReal.toReal_nonneg (a := canonSubmeasure M true x (L.pLev k x) {v x})
    have hp := ENNReal.toReal_nonneg
      (a := (canonSubmeasure M true x (L.pLev (k + 1) x) -
        canonSubmeasure M true x (L.pLev k x)) {v x})
    rw [canonical_treated_increment_real M x _ _ ha.1 hab.le, ← hu, zero_sub] at hp
    linarith
  letI := discrete_gap_law_probability M M.prop q L hL k hk x
  have hg : (discreteGapLaw M L k x {v x}).toReal = 0 := by
    rw [discreteGapLaw, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, hz, mul_zero]
  exact ((ENNReal.toReal_eq_zero_iff _).mp hg).resolve_right (measure_ne_top _ _)

-- This includes the fixed j = 0 endpoint and every estimated interior
-- boundary, using exactly the two conditions in the continuous regime.
-- @node: population_discrete_gap_boundaries_noAtom
/-- Under [the structural assumptions](hyp:h), [invariant ordering of baseline
and comparison propensity levels](hyp:hL), [baseline overlap](hyp:hov),
[bounded local densities at the treated band boundaries](hyp:hd), and
[absence of atoms at the lower outcome endpoint](hyp:h0), [almost every
covariate value has zero discrete-gap-law mass at every band boundary in
every level below the level count, including band zero](goal). -/
lemma population_discrete_gap_boundaries_noAtom
    (h : StructuralAssumptions M) (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (cpi : ℝ)
    (hov : BaselineOverlapWitness M L cpi)
    (hd : BoundaryDensitiesBounded M L) (h0 : NoAtomAtLowerEndpoint M L) :
    ∀ᵐ x ∂xLaw M, ∀ k < L.K, ∀ j ≤ L.l k,
      discreteGapLaw M L k x {bandBoundary M L k j x} = 0 := by
  have hn (k : ℕ) (hk : k < L.K) (j : ℕ) (hj : j ≤ L.l k) :
      ∀ᵐ x ∂xLaw M, discreteGapLaw M L k x {bandBoundary M L k j x} = 0 := by
    apply population_discrete_gap_noAtom_of_treated_upper M h q L hL cpi hov k hk
    by_cases hj0 : j = 0
    · subst j
      simpa only [bandBoundary, true_or, if_true] using h0 k hk (k + 1) (Or.inl rfl)
    · exact population_treated_boundary_noAtom_of_density M L hd k j hk
        (by omega) hj (k + 1) (Or.inl rfl)
  exact ae_all_iff.mpr fun k => ae_all_iff.mpr fun hk =>
    ae_all_iff.mpr fun j => ae_all_iff.mpr fun hj => hn k hk j hj

-- @node: population_continuous_score_quantile_moment_of_density
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
[invariant ordering of baseline and policy propensity levels](hyp:hL),
[baseline](hyp:hov) and [policy overlap](hyp:hpol), [bounded local densities
at treated band boundaries](hyp:hd), and [no atoms at the lower outcome
endpoint](hyp:h0), [for almost every covariate value and every valid level
and band, the upper propensity times the upper treated boundary moment
minus the lower propensity times the lower treated boundary moment equals
the pooled policy value minus the lower propensity](goal). -/
lemma population_continuous_score_quantile_moment_of_density
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (phi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L) (cpi : ℝ)
    (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (hd : BoundaryDensitiesBounded M L) (h0 : NoAtomAtLowerEndpoint M L) :
    ∀ᵐ x ∂xLaw M, ∀ k < L.K, ∀ j ≤ L.l k,
      positiveValue (trueNuisance M L).pLev (k + 1) x *
          boundaryValue (trueNuisance M L).Mplus k j x -
        positiveValue (trueNuisance M L).pLev k x *
          minusBoundaryValue (trueNuisance M L).Mminus k j x -
        (pooledQ phi L (trueNuisance M L) k j x -
          positiveValue (trueNuisance M L).pLev k x) = 0 := by
  filter_upwards [population_continuous_score_quantile_moment M h he phi L hL cpi hov hpol,
    population_discrete_gap_boundaries_noAtom M h (policyProp phi M.prop) L hL cpi hov hd h0]
    with x hm hn
  intro k hk j hj
  exact hm k hk j hj (hn k hk j hj)

end Papers.TbsPrteOptimalTransport

module
public import Papers.TbsPrteOptimalTransport.Helpers.LevelMarginalSeparation
public import Papers.TbsPrteOptimalTransport.Helpers.DiscretePolicyInterior
/-! Identification of baseline equality classes by their marginal means.
The zero level is included in the ordering, without imposing a uniform gap
between a positive baseline level and zero. -/
public section
set_option linter.style.openClassical false
set_option linter.unusedDecidableInType false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Set
open scoped Classical

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: population_baseline_marginal_strict_order
/-- Under [the threshold-crossing model](hyp:h), [a covariate-invariant ordering and
classification of baseline and policy levels](hyp:hL), and [a positive uniform gap
separating distinct propensity values](hyp:hgap), if [the first level index is smaller
than the second](hyp:hij) and [the second is at most the number of positive baseline
levels](hyp:hj), then [the first baseline level has a strictly smaller covariate-averaged
value than the second](goal). -/
lemma population_baseline_marginal_strict_order (h : ThresholdCrossing M)
    (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (gap : ℝ)
    (hgap : PropensityGapSeparationWitness M.prop q gap)
    (i j : ℕ) (hij : i < j) (hj : j ≤ L.K) :
    (∫ x, L.pLev i x ∂xLaw M) < ∫ x, L.pLev j x ∂xLaw M := by
  by_cases hi : i = 0
  · subst i
    have hz : L.pLev 0 = fun _ => (0 : ℝ) := by
      funext x
      rw [hL.1 x 0 (by omega)]
      simp [pLevel]
    rw [hz, integral_zero]
    exact population_baseline_marginal_pos M h q L hL j ⟨by omega, hj⟩
  · have hg := population_baseline_marginal_gap M h q L hL gap hgap
      i j (by omega) hij hj
    linarith [hgap.1]

-- @node: population_baseline_marginal_order_iff
/-- Under [the threshold-crossing model](hyp:h), [a covariate-invariant ordering and
classification of baseline and policy levels](hyp:hL), and [a positive uniform gap
separating distinct propensity values](hyp:hgap), for [a first index at most the number
of positive baseline levels](hyp:hi) and [a second index within the same bound](hyp:hj),
[the first baseline marginal mean is strictly smaller than the second exactly when its
index is smaller](goal). -/
lemma population_baseline_marginal_order_iff (h : ThresholdCrossing M)
    (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (gap : ℝ)
    (hgap : PropensityGapSeparationWitness M.prop q gap)
    (i j : ℕ) (hi : i ≤ L.K) (hj : j ≤ L.K) :
    (∫ x, L.pLev i x ∂xLaw M) < (∫ x, L.pLev j x ∂xLaw M) ↔ i < j := by
  constructor
  · intro hlt
    by_contra hn
    rcases (Nat.le_of_not_gt hn).eq_or_lt with heq | hji
    · subst j
      exact lt_irrefl _ hlt
    · exact lt_asymm hlt
        (population_baseline_marginal_strict_order M h q L hL gap hgap j i hji hi)
  · exact fun hij => population_baseline_marginal_strict_order M h q L hL gap hgap i j hij hj

-- @node: population_baseline_marginal_index_iff
/-- Under [the threshold-crossing model](hyp:h), [a covariate-invariant ordering and
classification of baseline and policy levels](hyp:hL), and [a positive uniform gap
separating distinct propensity values](hyp:hgap), for [a first index at most the number
of positive baseline levels](hyp:hi) and [a second index within the same bound](hyp:hj),
[the baseline levels have equal marginal means exactly when their indices are equal](goal). -/
lemma population_baseline_marginal_index_iff (h : ThresholdCrossing M)
    (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (gap : ℝ)
    (hgap : PropensityGapSeparationWitness M.prop q gap)
    (i j : ℕ) (hi : i ≤ L.K) (hj : j ≤ L.K) :
    (∫ x, L.pLev i x ∂xLaw M) = (∫ x, L.pLev j x ∂xLaw M) ↔ i = j := by
  constructor
  · intro heq
    rcases lt_trichotomy i j with hij | hij | hij
    · exact False.elim ((population_baseline_marginal_strict_order
        M h q L hL gap hgap i j hij hj).ne heq)
    · exact hij
    · exact False.elim ((population_baseline_marginal_strict_order
        M h q L hL gap hgap j i hij hi).ne heq.symm)
  · rintro rfl
    rfl

-- @node: population_baseline_class_eq_marginal_fiber
/-- Under [the threshold-crossing model](hyp:h), [a covariate-invariant ordering and
classification of baseline and policy levels](hyp:hL), and [a positive uniform gap
separating distinct propensity values](hyp:hgap), for [an index from zero through the
number of positive baseline levels](hyp:hk), [the corresponding baseline class consists
exactly of the instrument values whose baseline marginal mean equals that level's
marginal mean](goal). -/
lemma population_baseline_class_eq_marginal_fiber (h : ThresholdCrossing M)
    (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (gap : ℝ)
    (hgap : PropensityGapSeparationWitness M.prop q gap)
    (k : ℕ) (hk : k ≤ L.K) :
    L.S k = Finset.univ.filter (fun z =>
      (∫ x, M.prop z x ∂xLaw M) = ∫ x, L.pLev k x ∂xLaw M) := by
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hz
    have heq : M.prop z = L.pLev k := by
      funext x
      exact (hL.2.2.2.2.2.1 x k z hk).mp hz
    rw [heq]
  · intro hz
    let x₀ : X := Classical.choice inferInstance
    obtain ⟨i, hi, hzi⟩ := finite_baseline_level_exists M q L hL x₀ z
    have hmem : z ∈ L.S i := (hL.2.2.2.2.2.1 x₀ i z hi).mpr hzi
    have heq : M.prop z = L.pLev i := by
      funext x
      exact (hL.2.2.2.2.2.1 x i z hi).mp hmem
    rw [heq] at hz
    have hik := (population_baseline_marginal_index_iff M h q L hL gap hgap i k hi hk).mp hz
    simpa only [hik] using hmem

-- @node: population_baseline_marginal_eq_iff_pointwise
/-- Under [the threshold-crossing model](hyp:h), [a covariate-invariant ordering and
classification of baseline and policy levels](hyp:hL), and [a positive uniform gap
separating distinct propensity values](hyp:hgap), [two instrument values have equal
baseline marginal means exactly when their baseline propensities agree at any specified
covariate value](goal). -/
lemma population_baseline_marginal_eq_iff_pointwise (h : ThresholdCrossing M)
    (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (gap : ℝ)
    (hgap : PropensityGapSeparationWitness M.prop q gap)
    (x : X) (z w : Z) :
    (∫ t, M.prop z t ∂xLaw M) = (∫ t, M.prop w t ∂xLaw M) ↔
      M.prop z x = M.prop w x := by
  obtain ⟨k, hk, hzk⟩ := finite_baseline_level_exists M q L hL x w
  have hw : w ∈ L.S k := (hL.2.2.2.2.2.1 x k w hk).mpr hzk
  have heq : M.prop w = L.pLev k := by
    funext t
    exact (hL.2.2.2.2.2.1 t k w hk).mp hw
  rw [heq]
  have hfiber := population_baseline_class_eq_marginal_fiber M h q L hL gap hgap k hk
  have hz : z ∈ L.S k ↔ (∫ t, M.prop z t ∂xLaw M) =
      ∫ t, L.pLev k t ∂xLaw M := by
    rw [hfiber]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact hz.symm.trans (hL.2.2.2.2.2.1 x k z hk)

-- @node: population_baseline_marginal_lt_iff_pointwise
/-- Under [the threshold-crossing model](hyp:h), [a covariate-invariant ordering and
classification of baseline and policy levels](hyp:hL), and [a positive uniform gap
separating distinct propensity values](hyp:hgap), [the first of two instrument values
has a strictly smaller baseline marginal mean exactly when its baseline propensity is
strictly smaller at any specified covariate value](goal). -/
lemma population_baseline_marginal_lt_iff_pointwise (h : ThresholdCrossing M)
    (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (gap : ℝ)
    (hgap : PropensityGapSeparationWitness M.prop q gap)
    (x : X) (z w : Z) :
    (∫ t, M.prop z t ∂xLaw M) < (∫ t, M.prop w t ∂xLaw M) ↔
      M.prop z x < M.prop w x := by
  obtain ⟨i, hi, hzi⟩ := finite_baseline_level_exists M q L hL x z
  obtain ⟨j, hj, hwj⟩ := finite_baseline_level_exists M q L hL x w
  have hz : M.prop z = L.pLev i := by
    have hm := (hL.2.2.2.2.2.1 x i z hi).mpr hzi
    exact funext (fun t => (hL.2.2.2.2.2.1 t i z hi).mp hm)
  have hw : M.prop w = L.pLev j := by
    have hm := (hL.2.2.2.2.2.1 x j w hj).mpr hwj
    exact funext (fun t => (hL.2.2.2.2.2.1 t j w hj).mp hm)
  rw [hz, hw, population_baseline_marginal_order_iff M h q L hL gap hgap i j hi hj]
  constructor
  · exact fun hij => hL.2.2.2.2.2.2.2.1 x i j hij hj
  · intro hlt
    by_contra hn
    have hle := canonical_baseline_levels_monotone M q L hL x j i
      (Nat.le_of_not_gt hn) (by omega)
    exact (not_lt_of_ge hle) hlt

end Papers.TbsPrteOptimalTransport

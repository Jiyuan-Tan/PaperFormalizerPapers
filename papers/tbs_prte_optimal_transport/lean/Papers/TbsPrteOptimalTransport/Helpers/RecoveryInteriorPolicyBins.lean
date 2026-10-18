module
public import Papers.TbsPrteOptimalTransport.Helpers.RecoveryBaselineIndexing
public import Papers.TbsPrteOptimalTransport.Helpers.RecoveryInteriorPolicyProjection
/-! Numerical bin location of recovered interior policy components.
The indexed baseline list supplies the fitted endpoints. Strict component
ordering then puts each interior policy class in exactly its population bin. -/
public section
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Set Filter
open scoped Classical Topology

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z) (h : ThresholdCrossing M)
  (q : Z → X → ℝ) (hq : Measurable (Function.uncurry q))
  (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
  (hOff : PolicyLevelOffBoundary L) (hlev : ∀ k, Measurable (L.pLev k))
  (gap : ℝ) (hgap : PropensityGapSeparationWitness M.prop q gap)
  (pb qb : Z → ℝ) (rho : ℝ)
  (hactive : ∀ z, rho < pb z ↔ z ∉ L.S 0)
  (hp : ∀ z, |pb z - ∫ x, M.prop z x ∂xLaw M| < gap / 4)
  (hqr : ∀ z, |qb z - ∫ x, q z x ∂xLaw M| < gap / 4)

include M h q hq L hL hOff hlev hgap hactive hp hqr

-- @node: recoveryComponents_baseline_getD_eq_component
/-- Suppose threshold crossing holds, policy propensities are jointly
measurable, the population level structure is invariant across
covariates, policy classes before the final bin avoid their lower
boundaries, baseline levels are measurable, there is a
positive uniform propensity gap, active baseline vertices are exactly
those outside the zero class, baseline marginal errors are below
a quarter-gap, and policy marginal errors are below a quarter-gap.
For [a positive baseline index i within the population range](hyp:hi) and [z in
its baseline class](hyp:hz), [entry i minus one in the ordered list of components
containing a baseline vertex, with the empty set as fallback, equals the
component of z's baseline vertex](goal). -/
lemma recoveryComponents_baseline_getD_eq_component
    (i : ℕ) (hi : 1 ≤ i ∧ i ≤ L.K) (z : Z) (hz : z ∈ L.S i) :
    ((recoveryComponents pb qb rho gap).filter (fun C =>
      ∃ w, (false, w) ∈ C)).getD (i - 1) ∅ =
        recoveryComponent pb qb rho gap (false, z) := by
  let rep : ℕ → Z := fun k => if hk : 1 ≤ k ∧ k ≤ L.K then
    Classical.choose (ordered_baseline_level_nonempty M q L hL k hk)
    else Classical.choice inferInstance
  have hrep : ∀ k, (1 ≤ k ∧ k ≤ L.K) → rep k ∈ L.S k := by
    intro k hk
    simpa only [rep, dif_pos hk] using
      Classical.choose_spec (ordered_baseline_level_nonempty M q L hL k hk)
  rw [recoveryComponents_baseline_list_eq M h q hq L hL hOff hlev
    gap hgap pb qb rho hactive hp hqr rep hrep]
  have hget : ((List.range L.K).map (fun k =>
      recoveryComponent pb qb rho gap (false, rep (k + 1)))).getD (i - 1) ∅ =
      recoveryComponent pb qb rho gap (false, rep i) := by
    simp [List.getD, List.getElem?_map,
      List.getElem?_range (show i - 1 < L.K by omega), Nat.sub_add_cancel hi.1]
  rw [hget]
  have hself := recoveryComponent_positive_baseline_self_mem M q L hL
    gap pb qb rho hactive i hi z hz
  have hproj := recoveryComponent_baseline_projection_eq M h q hq L hL hOff
    hlev gap hgap pb qb rho hactive hp hqr i hi z hz
  have hr : (false, rep i) ∈ recoveryComponent pb qb rho gap (false, z) := by
    have hm := hproj.symm ▸ hrep i hi
    exact (Finset.mem_filter.mp hm).2
  exact recoveryComponents_eq_component_of_mem pb qb rho gap
    (by
      simp only [recoveryComponents, List.mem_mergeSort, Finset.mem_toList, Finset.mem_image]
      exact ⟨(false, z), (Finset.mem_filter.mp hself).1, rfl⟩) hr

-- @node: recoverLevelsAt_positive_baseline_endpoint_eq
/-- Under threshold crossing, joint measurability of policy
propensities, an invariant population level structure, policy
classes off their lower boundaries before the final bin, measurable
baseline levels, positive uniform propensity separation,
correct activity classification outside the zero baseline class,
baseline marginal errors below a quarter-gap, and policy marginal
errors below a quarter-gap, let [i be a positive baseline index within
the population range](hyp:hi) and [z belong to that baseline class](hyp:hz).
Then [at any covariate value, recovered baseline endpoint i equals the average
fitted value of the component of z's baseline vertex](goal). -/
lemma recoverLevelsAt_positive_baseline_endpoint_eq
    (i : ℕ) (hi : 1 ≤ i ∧ i ≤ L.K) (z : Z) (hz : z ∈ L.S i) (x : X) :
    (recoverLevelsAt pb qb rho gap : LevelData Z X).pLev i x =
      componentAverage pb qb (recoveryComponent pb qb rho gap (false, z)) := by
  have hK := recoverLevelsAt_baseline_count_eq M h q hq L hL hOff hlev
    gap hgap pb qb rho hactive hp hqr
  have hlen : ((recoveryComponents pb qb rho gap).filter
      (fun C => ∃ w, (false, w) ∈ C)).length = L.K := hK
  change (if i = 0 then 0 else if i ≤ _ then _ else 1) = _
  rw [if_neg (by omega), if_pos (by omega),
    recoveryComponents_baseline_getD_eq_component M h q hq L hL hOff hlev
      gap hgap pb qb rho hactive hp hqr i hi z hz]

-- @node: recoverLevelsAt_endpoint_interior_policy_order
/-- Suppose threshold crossing holds, policy propensities are jointly
measurable, population levels and classes are invariant across
covariates, policy classes before the final bin avoid their lower
boundaries, baseline levels are measurable, there is a
positive uniform propensity gap, baseline activity identifies exactly
the complement of the zero class, baseline marginal errors are
below a quarter-gap, and policy marginal errors are below a quarter-gap.
For [a positive baseline index i within range](hyp:hi), [a bin r before the final
bin](hyp:hr), [a valid positive policy index j in r](hyp:hj), and [w in that policy
class](hyp:hw), [at any covariates the recovered endpoint i is strictly below
the policy component average exactly when i is at most r, and the reverse strict
inequality holds exactly when r is less than i](goal). -/
lemma recoverLevelsAt_endpoint_interior_policy_order
    (i r j : ℕ) (hi : 1 ≤ i ∧ i ≤ L.K)
    (hr : r < L.K) (hj : 1 ≤ j ∧ j ≤ L.l r)
    (w : Z) (hw : w ∈ L.T r j) (x : X) :
    ((recoverLevelsAt pb qb rho gap : LevelData Z X).pLev i x <
      componentAverage pb qb (recoveryComponent pb qb rho gap (true, w)) ↔ i ≤ r) ∧
    (componentAverage pb qb (recoveryComponent pb qb rho gap (true, w)) <
      (recoverLevelsAt pb qb rho gap : LevelData Z X).pLev i x ↔ r < i) := by
  obtain ⟨z, hz⟩ := ordered_baseline_level_nonempty M q L hL i hi
  rw [recoverLevelsAt_positive_baseline_endpoint_eq M h q hq L hL hOff hlev
    gap hgap pb qb rho hactive hp hqr i hi z hz x]
  exact recoveryComponent_baseline_interior_policy_average_order M h q hq L hL
    hOff hlev gap hgap pb qb rho hactive hp hqr i r j hi hr hj z w hz hw

-- @node: recoverLevelsAt_endpoint_le_interior_policy_iff
/-- Under threshold crossing, jointly measurable policy propensities,
an invariant population level structure, policy classes off their
lower boundaries before the final bin, measurable baseline levels,
positive uniform propensity separation, correct activity classification
outside the zero baseline class, baseline marginal errors below
a quarter-gap, and policy marginal errors below a quarter-gap,
suppose [i is a positive baseline index within range](hyp:hi), [r precedes the
final bin](hyp:hr), [j is a valid positive policy index in r](hyp:hj), and [w belongs
to that policy class](hyp:hw). Then [at any covariates the recovered endpoint i
is no larger than w's policy component average if and only if i is at most r](goal). -/
lemma recoverLevelsAt_endpoint_le_interior_policy_iff
    (i r j : ℕ) (hi : 1 ≤ i ∧ i ≤ L.K)
    (hr : r < L.K) (hj : 1 ≤ j ∧ j ≤ L.l r)
    (w : Z) (hw : w ∈ L.T r j) (x : X) :
    (recoverLevelsAt pb qb rho gap : LevelData Z X).pLev i x ≤
      componentAverage pb qb (recoveryComponent pb qb rho gap (true, w)) ↔ i ≤ r := by
  have ho := recoverLevelsAt_endpoint_interior_policy_order M h q hq L hL
    hOff hlev gap hgap pb qb rho hactive hp hqr i r j hi hr hj w hw x
  constructor
  · intro hle
    by_contra hn
    exact (not_lt_of_ge hle) (ho.2.mpr (Nat.lt_of_not_ge hn))
  · intro hir
    exact (ho.1.mpr hir).le

-- @node: recoverLevelsAt_interior_policy_numeric_bin_iff
/-- Suppose threshold crossing holds, policy propensities are jointly
measurable, population levels and classes are invariant across
covariates, policy classes before the final bin avoid their lower
boundaries, baseline levels are measurable, there is a
positive uniform propensity gap, active baseline vertices are exactly
those outside the zero class, baseline marginal errors are below
a quarter-gap, and policy marginal errors are below a quarter-gap.
For [a positive bin k before the final bin](hyp:hk), [a bin r before the final
bin](hyp:hr), [a valid positive policy index j in r](hyp:hj), and [w in that policy
class](hyp:hw), [at any covariates w's policy component average lies at or above
recovered endpoint k and strictly below endpoint k plus one if and only if
k equals r](goal). -/
lemma recoverLevelsAt_interior_policy_numeric_bin_iff
    (k r j : ℕ) (hk : 1 ≤ k ∧ k < L.K)
    (hr : r < L.K) (hj : 1 ≤ j ∧ j ≤ L.l r)
    (w : Z) (hw : w ∈ L.T r j) (x : X) :
    ((recoverLevelsAt pb qb rho gap : LevelData Z X).pLev k x ≤
      componentAverage pb qb (recoveryComponent pb qb rho gap (true, w)) ∧
      componentAverage pb qb (recoveryComponent pb qb rho gap (true, w)) <
        (recoverLevelsAt pb qb rho gap : LevelData Z X).pLev (k + 1) x) ↔ k = r := by
  rw [recoverLevelsAt_endpoint_le_interior_policy_iff M h q hq L hL hOff hlev
    gap hgap pb qb rho hactive hp hqr k r j ⟨hk.1, hk.2.le⟩ hr hj w hw x,
    (recoverLevelsAt_endpoint_interior_policy_order M h q hq L hL hOff hlev
      gap hgap pb qb rho hactive hp hqr (k + 1) r j
        ⟨by omega, by omega⟩ hr hj w hw x).2]
  omega

-- @node: recoveryComponents_interior_policy_numeric_filter_mem_iff
/-- Under threshold crossing, joint measurability of policy
propensities, an invariant population level structure, policy
classes off their lower boundaries before the final bin, measurable
baseline levels, positive uniform propensity separation,
correct activity classification outside the zero baseline class,
baseline marginal errors below a quarter-gap, and policy marginal
errors below a quarter-gap, suppose [k is a positive bin before the
final bin](hyp:hk), [r precedes the final bin](hyp:hr), [j is a valid positive policy
index in r](hyp:hj), and [w is in that policy class](hyp:hw). Then [at any
covariates w's policy component belongs to the recovered list filtered for policy
vertices and the numerical bounds of bin k if and only if k equals r](goal). -/
lemma recoveryComponents_interior_policy_numeric_filter_mem_iff
    (k r j : ℕ) (hk : 1 ≤ k ∧ k < L.K)
    (hr : r < L.K) (hj : 1 ≤ j ∧ j ≤ L.l r)
    (w : Z) (hw : w ∈ L.T r j) (x : X) :
    recoveryComponent pb qb rho gap (true, w) ∈
      (recoveryComponents pb qb rho gap).filter (fun C =>
        (∃ z, (true, z) ∈ C) ∧
        (recoverLevelsAt pb qb rho gap : LevelData Z X).pLev k x ≤
          componentAverage pb qb C ∧
        (if k = (recoverLevelsAt pb qb rho gap : LevelData Z X).K then
          componentAverage pb qb C ≤ 1 else
          componentAverage pb qb C <
            (recoverLevelsAt pb qb rho gap : LevelData Z X).pLev (k + 1) x)) ↔ k = r := by
  have hK := recoverLevelsAt_baseline_count_eq M h q hq L hL hOff hlev
    gap hgap pb qb rho hactive hp hqr
  have hmem := recoveryComponent_policy_mem_components gap pb qb rho w
  have hpolicy : ∃ z, (true, z) ∈ recoveryComponent pb qb rho gap (true, w) :=
    ⟨w, recoveryComponent_policy_self_mem gap pb qb rho w⟩
  simp only [List.mem_filter, decide_eq_true_eq, hmem, true_and, hpolicy, hK,
    if_neg (show k ≠ L.K by omega)]
  exact recoverLevelsAt_interior_policy_numeric_bin_iff M h q hq L hL hOff hlev
    gap hgap pb qb rho hactive hp hqr k r j hk hr hj w hw x

omit hactive hp hqr in
-- @node: recovery_interior_numeric_bins_failure_tendsto_zero
/-- Suppose threshold crossing holds, policy propensities are jointly
measurable, population levels and classes are invariant across
covariates, policy classes before the final bin avoid their lower
boundaries, baseline levels are measurable, and there is
a positive uniform propensity gap. If [the activity threshold tends
to zero](hyp:hrho), [baseline marginal estimates converge in probability to their
population means](hyp:hpconv), [policy marginal estimates converge in probability
to their population means](hyp:hqconv), and [threshold exceedance at each zero
baseline marginal has measure tending to zero](hyp:hzero), then [the measure of
failure of the following simultaneous characterization tends to zero: for every
positive bin k before the final bin and every policy class in a bin r before the
final bin, its component average lies between recovered endpoints k inclusive
and k plus one exclusive, at every covariate value, exactly when k equals r](goal). -/
lemma recovery_interior_numeric_bins_failure_tendsto_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (pb qb : ℕ → A → Z → ℝ) (rho : ℕ → ℝ)
    (hrho : Tendsto rho atTop (𝓝 0))
    (hpconv : ∀ z, Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => pb n a z) atTop (fun _ _ => ∫ x, M.prop z x ∂xLaw M))
    (hqconv : ∀ z, Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => qb n a z) atTop (fun _ _ => ∫ x, q z x ∂xLaw M))
    (hzero : ∀ z, (∫ x, M.prop z x ∂xLaw M) = 0 →
      Tendsto (fun n => μ {a | rho n < pb n a z}) atTop (𝓝 0)) :
    Tendsto (fun n => μ {a | ¬ (∀ k r j, (1 ≤ k ∧ k < L.K) →
      r < L.K → (1 ≤ j ∧ j ≤ L.l r) → ∀ w ∈ L.T r j, ∀ x,
        ((recoverLevelsAt (pb n a) (qb n a) (rho n) gap : LevelData Z X).pLev k x ≤
          componentAverage (pb n a) (qb n a)
            (recoveryComponent (pb n a) (qb n a) (rho n) gap (true, w)) ∧
          componentAverage (pb n a) (qb n a)
            (recoveryComponent (pb n a) (qb n a) (rho n) gap (true, w)) <
            (recoverLevelsAt (pb n a) (qb n a) (rho n) gap : LevelData Z X).pLev
              (k + 1) x) ↔ k = r)}) atTop (𝓝 0) := by
  have hz := recovery_zero_class_failure_tendsto_zero μ pb
    (fun z => ∫ x, M.prop z x ∂xLaw M)
    (fun z => integral_nonneg (fun x => (M.rangeProp z x).1))
    rho hrho hpconv hzero
  have hconv : ∀ v : RecoveryVertex Z,
      Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
        (fun n a => vertexValue (pb n a) (qb n a) v) atTop
        (fun _ _ => vertexValue (fun z => ∫ x, M.prop z x ∂xLaw M)
          (fun z => ∫ x, q z x ∂xLaw M) v) := by
    rintro ⟨b, z⟩
    cases b
    · exact hpconv z
    · exact hqconv z
  have herr := finite_marginal_errors_tendsto_zero μ
    (fun n a => vertexValue (pb n a) (qb n a))
    (vertexValue (fun z => ∫ x, M.prop z x ∂xLaw M)
      (fun z => ∫ x, q z x ∂xLaw M)) hconv (gap / 4) (by linarith [hgap.1])
  have hs := hz.add herr
  simp only [add_zero] at hs
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs
    (fun _ => zero_le)
  intro n
  refine (measure_mono ?_).trans (measure_union_le _ _)
  intro a hbad
  by_contra hn
  have hg :
      Finset.univ.filter (fun z => pb n a z ≤ rho n) =
        Finset.univ.filter (fun z => (∫ x, M.prop z x ∂xLaw M) = 0) ∧
      ¬ ∃ v, gap / 4 ≤ |vertexValue (pb n a) (qb n a) v -
        vertexValue (fun z => ∫ x, M.prop z x ∂xLaw M)
          (fun z => ∫ x, q z x ∂xLaw M) v| := by
    simpa only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] using hn
  have ha (z : Z) : rho n < pb n a z ↔ z ∉ L.S 0 := by
    have he := Finset.ext_iff.mp hg.1 z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    rw [population_baseline_marginal_zero_iff M h q L hL z] at he
    exact (not_le).symm.trans (not_congr he)
  have he (v : RecoveryVertex Z) :
      |vertexValue (pb n a) (qb n a) v -
        vertexValue (fun z => ∫ x, M.prop z x ∂xLaw M)
          (fun z => ∫ x, q z x ∂xLaw M) v| < gap / 4 :=
    lt_of_not_ge (fun hh => hg.2 ⟨v, hh⟩)
  apply hbad
  intro k r j hk hr hj w hw x
  exact recoverLevelsAt_interior_policy_numeric_bin_iff M h q hq L hL hOff hlev
    gap hgap (pb n a) (qb n a) (rho n) ha
    (fun z => he (false, z)) (fun z => he (true, z)) k r j hk hr hj w hw x

end Papers.TbsPrteOptimalTransport

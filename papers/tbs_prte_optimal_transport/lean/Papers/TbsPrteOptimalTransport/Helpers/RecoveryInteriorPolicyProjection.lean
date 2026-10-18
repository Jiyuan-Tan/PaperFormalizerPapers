module
public import Papers.TbsPrteOptimalTransport.Helpers.RecoveryInteriorPolicyOrder
public import Papers.TbsPrteOptimalTransport.Helpers.RecoveryComponentIndexing
/-! Projection and canonical ordering of interior policy components.
Each population policy class is a full recovery component. Its policy projection
recovers the class, and representatives give a strictly ordered, duplicate-free
list of the components in each interior bin. -/
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
variable (M : LatentIVModel Ω X Z)
  (q : Z → X → ℝ) (hq : Measurable (Function.uncurry q))
  (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
  (hOff : PolicyLevelOffBoundary L) (hlev : ∀ k, Measurable (L.pLev k))
  (gap : ℝ) (hgap : PropensityGapSeparationWitness M.prop q gap)
  (pb qb : Z → ℝ) (rho : ℝ)
  (hactive : ∀ z, rho < pb z ↔ z ∉ L.S 0)
  (hp : ∀ z, |pb z - ∫ x, M.prop z x ∂xLaw M| < gap / 4)
  (hqr : ∀ z, |qb z - ∫ x, q z x ∂xLaw M| < gap / 4)

-- @node: recoveryComponent_policy_self_mem
/-- [Every policy vertex belongs to its own recovery component](goal). -/
lemma recoveryComponent_policy_self_mem (z : Z) :
    (true, z) ∈ recoveryComponent pb qb rho gap (true, z) := by
  exact Finset.mem_filter.mpr ⟨by simp [recoveryActive], Relation.ReflTransGen.refl⟩

-- @node: recoveryComponent_policy_mem_components
/-- [The recovery component of any policy vertex occurs in the ordered list of recovery components](goal). -/
lemma recoveryComponent_policy_mem_components (z : Z) :
    recoveryComponent pb qb rho gap (true, z) ∈ recoveryComponents pb qb rho gap := by
  simp only [recoveryComponents, List.mem_mergeSort, Finset.mem_toList, Finset.mem_image]
  exact ⟨(true, z), (Finset.mem_filter.mp
    (recoveryComponent_policy_self_mem gap pb qb rho z)).1, rfl⟩

include M q hq L hL hOff hlev hgap hactive hp hqr

-- @node: recoveryComponent_interior_policy_projection_eq
/-- Suppose the policy propensity is measurable, the population levels have an invariant ordering, policy levels avoid their bins' lower baseline boundaries before the terminal bin, baseline levels are measurable, and distinct population propensities satisfy the positive gap separation condition. If the activity threshold selects exactly the nonzero baseline classes, baseline marginal errors are less than one quarter of the gap, policy marginal errors satisfy the same bound, [the bin is below the terminal bin](hyp:hk), [the policy index runs from one to the number of levels in that bin](hyp:hj), and [the chosen instrument belongs to that policy class](hyp:hz), then [the policy instruments in its recovery component are exactly that population policy class](goal). -/
lemma recoveryComponent_interior_policy_projection_eq
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k)
    (z : Z) (hz : z ∈ L.T k j) :
    Finset.univ.filter (fun w =>
      (true, w) ∈ recoveryComponent pb qb rho gap (true, z)) = L.T k j := by
  rw [recoveryComponent_interior_policy_class_eq M q hq L hL hOff hlev
    gap hgap pb qb rho hactive hp hqr k j hk hj z hz]
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
    Prod.mk.injEq, true_and, exists_eq_right]

-- @node: recoveryComponent_interior_policy_eq_iff_indices
/-- Assume measurable policy propensities, invariant population level ordering, policy levels avoiding their bins' lower baseline boundaries before the terminal bin, measurable baseline levels, positive gap separation of distinct population propensities, correct selection of nonzero baseline classes by the activity threshold, baseline marginal errors smaller than one quarter of the gap, and policy marginal errors smaller than one quarter of the gap. For [two bins below the terminal bin](hyp:hk,hr), [valid positive policy indices in the respective bins](hyp:hi,hj), and [instruments belonging to the respective policy classes](hyp:hz,hw), [their policy recovery components coincide if and only if both their bin indices and their policy indices coincide](goal). -/
lemma recoveryComponent_interior_policy_eq_iff_indices
    (k r i j : ℕ) (hk : k < L.K) (hr : r < L.K)
    (hi : 1 ≤ i ∧ i ≤ L.l k) (hj : 1 ≤ j ∧ j ≤ L.l r)
    (z w : Z) (hz : z ∈ L.T k i) (hw : w ∈ L.T r j) :
    recoveryComponent pb qb rho gap (true, z) =
      recoveryComponent pb qb rho gap (true, w) ↔ k = r ∧ i = j := by
  constructor
  · intro he
    have ho := recoveryComponent_interior_policy_average_order_iff M q hq L hL
      hOff hlev gap hgap pb qb rho hactive hp hqr k r i j hk hr hi hj z w hz hw
    have hor := recoveryComponent_interior_policy_average_order_iff M q hq L hL
      hOff hlev gap hgap pb qb rho hactive hp hqr r k j i hr hk hj hi w z hw hz
    have hn : ¬ (k < r ∨ k = r ∧ i < j) := by
      intro hh
      have ht := ho.mpr hh
      rw [he] at ht
      exact lt_irrefl _ ht
    have hnr : ¬ (r < k ∨ r = k ∧ j < i) := by
      intro hh
      have ht := hor.mpr hh
      rw [he] at ht
      exact lt_irrefl _ ht
    omega
  · rintro ⟨rfl, rfl⟩
    rw [recoveryComponent_interior_policy_class_eq M q hq L hL hOff hlev
      gap hgap pb qb rho hactive hp hqr k i hk hi z hz,
      recoveryComponent_interior_policy_class_eq M q hq L hL hOff hlev
      gap hgap pb qb rho hactive hp hqr k i hk hi w hw]

-- @node: recovery_interior_policy_representative_list_pairwise
/-- Under measurability of the policy propensity, invariant population level ordering, policy levels avoiding their bins' lower baseline boundaries before the terminal bin, measurable baseline levels, positive gap separation, correct activity classification of nonzero baseline classes, baseline marginal errors below one quarter of the gap, and policy marginal errors below one quarter of the gap, consider [a bin below the terminal bin](hyp:hk) and [a representative in every positive policy class of that bin](hyp:hrep). [The recovery components of these representatives, listed in policy-index order, have strictly increasing fitted averages](goal). -/
lemma recovery_interior_policy_representative_list_pairwise
    (k : ℕ) (hk : k < L.K) (rep : ℕ → Z)
    (hrep : ∀ j, (1 ≤ j ∧ j ≤ L.l k) → rep j ∈ L.T k j) :
    ((List.range (L.l k)).map (fun j =>
      recoveryComponent pb qb rho gap (true, rep (j + 1)))).Pairwise
      (fun C D => componentAverage pb qb C < componentAverage pb qb D) := by
  rw [List.pairwise_map]
  apply List.Pairwise.imp_of_mem _ List.pairwise_lt_range
  intro i j hi hj hij
  have hi' : 1 ≤ i + 1 ∧ i + 1 ≤ L.l k := by
    have := List.mem_range.mp hi
    omega
  have hj' : 1 ≤ j + 1 ∧ j + 1 ≤ L.l k := by
    have := List.mem_range.mp hj
    omega
  exact recoveryComponent_interior_policy_average_strict_order M q hq L hL hOff
    hlev gap hgap pb qb rho hactive hp hqr k k (i + 1) (j + 1) hk hk hi' hj'
    _ _ (hrep _ hi') (hrep _ hj') (Or.inr ⟨rfl, by omega⟩)

-- @node: recovery_interior_policy_representative_list_nodup
/-- Suppose the policy propensity is measurable, population levels have an invariant ordering, policy levels avoid their bins' lower baseline boundaries before the terminal bin, baseline levels are measurable, positive gap separation holds, the activity threshold identifies the nonzero baseline classes, baseline marginal errors are below one quarter of the gap, and policy marginal errors are below one quarter of the gap. For [a bin below the terminal bin](hyp:hk) and [representatives belonging to each of its positive policy classes](hyp:hrep), [the list of representative recovery components contains no duplicates](goal). -/
lemma recovery_interior_policy_representative_list_nodup
    (k : ℕ) (hk : k < L.K) (rep : ℕ → Z)
    (hrep : ∀ j, (1 ≤ j ∧ j ≤ L.l k) → rep j ∈ L.T k j) :
    ((List.range (L.l k)).map (fun j =>
      recoveryComponent pb qb rho gap (true, rep (j + 1)))).Nodup := by
  exact (recovery_interior_policy_representative_list_pairwise M q hq L hL hOff
    hlev gap hgap pb qb rho hactive hp hqr k hk rep hrep).nodup

-- Selecting the components that touch a population bin already gives the
-- correctly indexed list. Relating this selection to fitted numerical bin
-- endpoints is the remaining step for recoverLevelsAt.
-- @node: recoveryComponents_interior_policy_class_list_eq
/-- Assume measurable policy propensities, invariant population level ordering, policy levels avoiding their bins' lower baseline boundaries before the terminal bin, measurable baseline levels, positive gap separation, correct threshold classification of nonzero baseline classes, baseline marginal errors smaller than one quarter of the gap, and policy marginal errors smaller than one quarter of the gap. For [a bin below the terminal bin](hyp:hk) and [one representative belonging to each positive policy class in that bin](hyp:hrep), [filtering the ordered recovery components for those containing a policy instrument from the bin gives exactly the representatives' components in policy-index order](goal). -/
lemma recoveryComponents_interior_policy_class_list_eq
    (k : ℕ) (hk : k < L.K) (rep : ℕ → Z)
    (hrep : ∀ j, (1 ≤ j ∧ j ≤ L.l k) → rep j ∈ L.T k j) :
    (recoveryComponents pb qb rho gap).filter (fun C =>
      ∃ j, (1 ≤ j ∧ j ≤ L.l k) ∧ ∃ z ∈ L.T k j, (true, z) ∈ C) =
    (List.range (L.l k)).map (fun j =>
      recoveryComponent pb qb rho gap (true, rep (j + 1))) := by
  let Qs := (recoveryComponents pb qb rho gap).filter (fun C =>
    ∃ j, (1 ≤ j ∧ j ≤ L.l k) ∧ ∃ z ∈ L.T k j, (true, z) ∈ C)
  let f := fun j => recoveryComponent pb qb rho gap (true, rep (j + 1))
  have hfmem (i : ℕ) (hi : i < L.l k) : f i ∈ Qs := by
    have hi' : 1 ≤ i + 1 ∧ i + 1 ≤ L.l k := by omega
    apply List.mem_filter.mpr
    refine ⟨recoveryComponent_policy_mem_components gap pb qb rho _, ?_⟩
    simpa only [decide_eq_true_eq] using
      (show ∃ j, (1 ≤ j ∧ j ≤ L.l k) ∧ ∃ z ∈ L.T k j, (true, z) ∈ f i from
        ⟨i + 1, hi', rep (i + 1), hrep _ hi',
          recoveryComponent_policy_self_mem gap pb qb rho _⟩)
  have hcover (C : Finset (RecoveryVertex Z)) (hC : C ∈ Qs) :
      ∃ i < L.l k, f i = C := by
    have hC' : C ∈ recoveryComponents pb qb rho gap ∧
        ∃ j, (1 ≤ j ∧ j ≤ L.l k) ∧ ∃ z ∈ L.T k j, (true, z) ∈ C := by
      simpa only [Qs, List.mem_filter, decide_eq_true_eq] using hC
    obtain ⟨j, hj, z, hz, hzc⟩ := hC'.2
    have he := recoveryComponents_eq_component_of_mem pb qb rho gap hC'.1 hzc
    have hc := (recoveryComponent_interior_policy_eq_iff_indices M q hq L hL
      hOff hlev gap hgap pb qb rho hactive hp hqr k k j j hk hk hj hj
      (rep j) z (hrep j hj) hz).mpr ⟨rfl, rfl⟩
    refine ⟨j - 1, by omega, ?_⟩
    simpa only [f, Nat.sub_add_cancel hj.1] using hc.trans he
  have hstrict := recovery_interior_policy_representative_list_pairwise
    M q hq L hL hOff hlev gap hgap pb qb rho hactive hp hqr k hk rep hrep
  have hn : Qs.Nodup := by
    apply List.Nodup.filter
    unfold recoveryComponents
    exact (List.mergeSort_perm _ _).nodup_iff.mpr (Finset.nodup_toList _)
  have hperm : Qs.Perm ((List.range (L.l k)).map f) := by
    apply (List.perm_ext_iff_of_nodup hn hstrict.nodup).mpr
    intro C
    constructor
    · intro hC
      obtain ⟨i, hi, he⟩ := hcover C hC
      exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, he⟩
    · intro hC
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hC
      exact hfmem i (List.mem_range.mp hi)
  apply List.Perm.eq_of_pairwise (le := fun C D =>
    componentAverage pb qb C ≤ componentAverage pb qb D) _
    ((recoveryComponents_pairwise_average_le pb qb rho gap).filter _) _ hperm
  · intro C D hC hD hCD hDC
    obtain ⟨i, hi, rfl⟩ := hcover C hC
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hD
    have hi' : 1 ≤ i + 1 ∧ i + 1 ≤ L.l k := by omega
    have hj' : 1 ≤ j + 1 ∧ j + 1 ≤ L.l k := by
      have := List.mem_range.mp hj
      omega
    have ho := recoveryComponent_interior_policy_average_order_iff M q hq L hL
      hOff hlev gap hgap pb qb rho hactive hp hqr k k (i + 1) (j + 1)
      hk hk hi' hj' _ _ (hrep _ hi') (hrep _ hj')
    have hor := recoveryComponent_interior_policy_average_order_iff M q hq L hL
      hOff hlev gap hgap pb qb rho hactive hp hqr k k (j + 1) (i + 1)
      hk hk hj' hi' _ _ (hrep _ hj') (hrep _ hi')
    have hij : ¬ i + 1 < j + 1 := fun ht =>
      (not_lt_of_ge hDC) (ho.mpr (Or.inr ⟨rfl, ht⟩))
    have hji : ¬ j + 1 < i + 1 := fun ht =>
      (not_lt_of_ge hCD) (hor.mpr (Or.inr ⟨rfl, ht⟩))
    exact congrArg f (show i = j by omega)
  · exact hstrict.imp (fun hh => hh.le)

-- @node: recoveryComponents_interior_policy_indexed_projection_eq
/-- Under measurable policy propensities, invariant population level ordering, policy levels avoiding their bins' lower baseline boundaries before the terminal bin, measurable baseline levels, positive gap separation, correct activity classification of nonzero baseline classes, baseline marginal errors below one quarter of the gap, and policy marginal errors below one quarter of the gap, take [a bin below the terminal bin](hyp:hk) and [a valid positive policy index in that bin](hyp:hj). [Selecting that entry, with counting starting at one, from the ordered components touching the bin and retaining its policy instruments recovers exactly the indexed population policy class](goal). -/
lemma recoveryComponents_interior_policy_indexed_projection_eq
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k) :
    Finset.univ.filter (fun z => (true, z) ∈
      ((recoveryComponents pb qb rho gap).filter (fun C =>
        ∃ i, (1 ≤ i ∧ i ≤ L.l k) ∧ ∃ w ∈ L.T k i, (true, w) ∈ C)).getD
          (j - 1) ∅) = L.T k j := by
  let rep : ℕ → Z := fun i => if hi : 1 ≤ i ∧ i ≤ L.l k then
    Classical.choose (ordered_policy_level_nonempty M q L hL k i hk.le hi.1 hi.2)
    else Classical.choice inferInstance
  have hrep : ∀ i, (1 ≤ i ∧ i ≤ L.l k) → rep i ∈ L.T k i := by
    intro i hi
    simpa only [rep, dif_pos hi] using
      Classical.choose_spec (ordered_policy_level_nonempty M q L hL k i hk.le hi.1 hi.2)
  rw [recoveryComponents_interior_policy_class_list_eq M q hq L hL hOff hlev
    gap hgap pb qb rho hactive hp hqr k hk rep hrep]
  have hget : ((List.range (L.l k)).map (fun i =>
      recoveryComponent pb qb rho gap (true, rep (i + 1)))).getD (j - 1) ∅ =
      recoveryComponent pb qb rho gap (true, rep j) := by
    simp [List.getD, List.getElem?_map,
      List.getElem?_range (show j - 1 < L.l k by omega), Nat.sub_add_cancel hj.1]
  rw [hget]
  exact recoveryComponent_interior_policy_projection_eq M q hq L hL hOff hlev
    gap hgap pb qb rho hactive hp hqr k j hk hj _ (hrep j hj)

end Papers.TbsPrteOptimalTransport

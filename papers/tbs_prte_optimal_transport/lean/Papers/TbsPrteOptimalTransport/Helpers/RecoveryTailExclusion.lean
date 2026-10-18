module
public import Papers.TbsPrteOptimalTransport.Helpers.RecoveryInteriorPolicyBins
public import Papers.TbsPrteOptimalTransport.Helpers.RecoveryComponentValueOrder
/-! Tail components lie above every positive recovered baseline endpoint.
Reversing paths and marginal gaps exclude them from interior bins; threshold
graph ordering handles the terminal endpoint and completes recovery there. -/
public section
set_option linter.unusedDecidableInType false
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

-- @node: recoveryComponent_tail_vertex_marginal_ge
/-- Assume threshold crossing, measurable policy propensities, invariant population level ordering, policy levels avoiding their bins' lower baseline boundaries before the terminal bin, measurable baseline levels, positive gap separation, activity exactly outside the zero baseline class, and baseline and policy marginal errors below one quarter of the gap. For [a valid positive policy index in the terminal bin](hyp:hj) and [an instrument in that policy class](hyp:hz), [any vertex in its policy recovery component](hyp:hv) has [population marginal at least the population average of the highest baseline level](goal). -/
lemma recoveryComponent_tail_vertex_marginal_ge
    (j : ℕ) (hj : 1 ≤ j ∧ j ≤ L.l L.K) (z : Z) (hz : z ∈ L.T L.K j)
    (v : RecoveryVertex Z) (hv : v ∈ recoveryComponent pb qb rho gap (true, z)) :
    (∫ x, L.pLev L.K x ∂xLaw M) ≤
      vertexValue (fun w => ∫ x, M.prop w x ∂xLaw M)
        (fun w => ∫ x, q w x ∂xLaw M) v := by
  have : IsProbabilityMeasure (xLaw M) :=
    Measure.isProbabilityMeasure_map M.measX.aemeasurable
  let x : X := Classical.choice inferInstance
  rcases v with ⟨b, w⟩
  cases b
  · obtain ⟨i, hi, hwi⟩ := finite_baseline_level_exists M q L hL x w
    have hwm := (hL.2.2.2.2.2.1 x i w hi).mpr hwi
    have hn : w ∉ L.S 0 := by
      apply (hactive w).mp
      simpa only [recoveryActive, Finset.mem_filter, Finset.mem_univ,
        Bool.false_eq_true, false_or, true_and] using (Finset.mem_filter.mp hv).1
    have hi0 : 1 ≤ i := by
      by_contra hh
      have he : i = 0 := by omega
      exact hn (he ▸ hwm)
    have hiK : i = L.K := by
      by_contra hh
      have hc := recovery_path_nonterminal_baseline_class_closed M h q hq L hL hOff
        hlev gap hgap pb qb rho hactive hp hqr i ⟨hi0, by omega⟩ w hwm
        (true, z) (recovery_path_reverse pb qb rho gap (Finset.mem_filter.mp hv).2)
      exact Bool.noConfusion hc.1
    have he : M.prop w = L.pLev L.K := by
      funext y
      exact (hL.2.2.2.2.2.1 y L.K w le_rfl).mp (hiK ▸ hwm)
    simp only [vertexValue, Bool.false_eq_true, if_false, he, le_refl]
  · obtain ⟨r, hr, i, hi0, hi, hwm, _, _⟩ := finite_policy_level_cover M q L hL x w
    have hrK : r = L.K := by
      by_contra hh
      have hc := recovery_path_interior_policy_class_closed M q hq L hL hOff
        hlev gap hgap pb qb rho hactive hp hqr r i (by omega) ⟨hi0, hi⟩ w hwm
        (true, z) (recovery_path_reverse pb qb rho gap (Finset.mem_filter.mp hv).2)
      have he1 := (hL.2.2.2.2.2.2.1 x r i z hr hi0 hi).mp hc.2
      have he2 := (hL.2.2.2.2.2.2.1 x L.K j z le_rfl hj.1 hj.2).mp hz
      have hs := population_policy_level_lex_strict_order M q L hL x r L.K i j
        hr le_rfl ⟨hi0, hi⟩ hj (Or.inl (by omega))
      rw [← he1, ← he2] at hs
      exact lt_irrefl _ hs
    subst r
    have hqm : Measurable (q w) := by fun_prop
    have hqi := (recovery_unit_interval_memLp M (q w) hqm
      (fun y => (hL.2.2.2.2.2.2.2.2.2.1 w y).2)).integrable (by norm_num)
    have hpi := (recovery_unit_interval_memLp M (L.pLev L.K) (hlev L.K)
      (fun y => hL.2.2.2.2.2.2.2.2.2.2.1 y L.K (by omega))).integrable (by norm_num)
    change (∫ y, L.pLev L.K y ∂xLaw M) ≤ ∫ y, q w y ∂xLaw M
    apply integral_mono hpi hqi
    intro y
    rw [(hL.2.2.2.2.2.2.1 y L.K i w le_rfl hi0 hi).mp hwm]
    exact (policy_level_bin_bounds M q L hL y L.K i le_rfl (by omega)).1

-- @node: recoveryComponent_tail_average_gt
/-- Under threshold crossing, measurable policy propensities, invariant population level ordering, policy levels avoiding their bins' lower baseline boundaries before the terminal bin, measurable baseline levels, positive gap separation, correct activity classification outside the zero baseline class, and baseline and policy marginal errors below one quarter of the gap, take [a valid positive terminal-bin policy index](hyp:hj) and [an instrument in its policy class](hyp:hz). [The fitted average of its policy recovery component is strictly greater than the population average of the highest baseline level minus one quarter of the gap](goal). -/
lemma recoveryComponent_tail_average_gt
    (j : ℕ) (hj : 1 ≤ j ∧ j ≤ L.l L.K) (z : Z) (hz : z ∈ L.T L.K j) :
    (∫ x, L.pLev L.K x ∂xLaw M) - gap / 4 <
      componentAverage pb qb (recoveryComponent pb qb rho gap (true, z)) := by
  apply componentAverage_gt_of_pointwise_gt pb qb _
    ⟨(true, z), recoveryComponent_policy_self_mem gap pb qb rho z⟩
  intro v hv
  have hlo := recoveryComponent_tail_vertex_marginal_ge M h q hq L hL hOff hlev
    gap hgap pb qb rho hactive hp hqr j hj z hz v hv
  have he : |vertexValue pb qb v -
      vertexValue (fun w => ∫ x, M.prop w x ∂xLaw M)
        (fun w => ∫ x, q w x ∂xLaw M) v| < gap / 4 := by
    rcases v with ⟨b, w⟩
    cases b
    · exact hp w
    · exact hqr w
  linarith [(abs_lt.mp he).1]

-- @node: recoverLevelsAt_nonterminal_endpoint_lt_tail_component
/-- Suppose threshold crossing, measurable policy propensities, invariant population level ordering, policy levels avoiding their bins' lower baseline boundaries before the terminal bin, measurable baseline levels, positive gap separation, activity exactly outside the zero baseline class, and baseline and policy marginal errors below one quarter of the gap. For [a positive nonterminal baseline index](hyp:hi), [a valid positive terminal-bin policy index](hyp:hj), and [an instrument in that terminal policy class](hyp:hz), [the recovered baseline endpoint at any covariate value is strictly below the fitted average of that instrument's policy recovery component](goal). -/
lemma recoverLevelsAt_nonterminal_endpoint_lt_tail_component
    (i j : ℕ) (hi : 1 ≤ i ∧ i < L.K) (hj : 1 ≤ j ∧ j ≤ L.l L.K)
    (z : Z) (hz : z ∈ L.T L.K j) (x : X) :
    (recoverLevelsAt pb qb rho gap : LevelData Z X).pLev i x <
      componentAverage pb qb (recoveryComponent pb qb rho gap (true, z)) := by
  obtain ⟨w, hw⟩ := ordered_baseline_level_nonempty M q L hL i ⟨hi.1, hi.2.le⟩
  rw [recoverLevelsAt_positive_baseline_endpoint_eq M h q hq L hL hOff hlev
    gap hgap pb qb rho hactive hp hqr i ⟨hi.1, hi.2.le⟩ w hw x]
  have ha := abs_lt.mp (recoveryComponent_nonterminal_baseline_average_close
    M h q hq L hL hOff hlev gap hgap pb qb rho hactive hp hqr i hi w hw)
  have hb := recoveryComponent_tail_average_gt M h q hq L hL hOff hlev
    gap hgap pb qb rho hactive hp hqr j hj z hz
  have hg := population_baseline_marginal_gap M h q L hL gap hgap
    i L.K hi.1 hi.2 le_rfl
  linarith [hgap.1]

-- @node: recoverLevelsAt_positive_endpoint_le_tail_component
/-- Assume threshold crossing, measurable policy propensities, invariant population level ordering, policy levels avoiding their bins' lower baseline boundaries before the terminal bin, measurable baseline levels, positive gap separation, correct activity classification outside the zero baseline class, and baseline and policy marginal errors below one quarter of the gap. For [any positive baseline index up to the highest baseline](hyp:hi), [a valid positive terminal-bin policy index](hyp:hj), and [an instrument belonging to that terminal policy class](hyp:hz), [the recovered baseline endpoint at any covariate value is no greater than the fitted average of that instrument's policy recovery component](goal). -/
lemma recoverLevelsAt_positive_endpoint_le_tail_component
    (i j : ℕ) (hi : 1 ≤ i ∧ i ≤ L.K) (hj : 1 ≤ j ∧ j ≤ L.l L.K)
    (z : Z) (hz : z ∈ L.T L.K j) (x : X) :
    (recoverLevelsAt pb qb rho gap : LevelData Z X).pLev i x ≤
      componentAverage pb qb (recoveryComponent pb qb rho gap (true, z)) := by
  by_cases hiK : i < L.K
  · exact (recoverLevelsAt_nonterminal_endpoint_lt_tail_component
      M h q hq L hL hOff hlev gap hgap pb qb rho hactive hp hqr
      i j ⟨hi.1, hiK⟩ hj z hz x).le
  · have he : i = L.K := by omega
    subst i
    obtain ⟨w, hw⟩ := ordered_baseline_level_nonempty M q L hL L.K hi
    rw [recoverLevelsAt_positive_baseline_endpoint_eq M h q hq L hL hOff hlev
      gap hgap pb qb rho hactive hp hqr L.K hi w hw x]
    have hselfw := recoveryComponent_positive_baseline_self_mem M q L hL
      gap pb qb rho hactive L.K hi w hw
    have hselfz := recoveryComponent_policy_self_mem gap pb qb rho z
    have hwm : M.prop w = L.pLev L.K :=
      funext (fun y => (hL.2.2.2.2.2.1 y L.K w le_rfl).mp hw)
    have hlo := recoveryComponent_tail_vertex_marginal_ge M h q hq L hL hOff hlev
      gap hgap pb qb rho hactive hp hqr j hj z hz (true, z) hselfz
    apply recoveryComponent_average_le_of_marginal_le pb qb rho gap hgap.1
      (Finset.mem_filter.mp hselfw).1 (Finset.mem_filter.mp hselfz).1
      (∫ y, M.prop w y ∂xLaw M) (∫ y, q z y ∂xLaw M)
      (hp w) (hqr z)
    simpa only [hwm, vertexValue, if_true] using hlo

-- @node: recoveryComponents_lower_policy_numeric_filter_eq
/-- Under threshold crossing, measurable policy propensities, invariant population level ordering, policy levels avoiding their bins' lower baseline boundaries before the terminal bin, measurable baseline levels, positive gap separation, activity exactly outside the zero baseline class, and baseline and policy marginal errors below one quarter of the gap, consider [a positive bin below the terminal bin](hyp:hk). [At any covariate value, filtering the ordered components for policy vertices with fitted averages between that bin's recovered lower endpoint, inclusive, and upper endpoint, exclusive, gives exactly the ordered components containing a population policy class from that bin](goal). -/
lemma recoveryComponents_lower_policy_numeric_filter_eq
    (k : ℕ) (hk : 1 ≤ k ∧ k < L.K) (x : X) :
    (recoveryComponents pb qb rho gap).filter (fun C =>
      (∃ z, (true, z) ∈ C) ∧
      (recoverLevelsAt pb qb rho gap : LevelData Z X).pLev k x ≤ componentAverage pb qb C ∧
      (if k = (recoverLevelsAt pb qb rho gap : LevelData Z X).K then
        componentAverage pb qb C ≤ 1 else componentAverage pb qb C <
          (recoverLevelsAt pb qb rho gap : LevelData Z X).pLev (k + 1) x)) =
    (recoveryComponents pb qb rho gap).filter (fun C =>
      ∃ j, (1 ≤ j ∧ j ≤ L.l k) ∧ ∃ z ∈ L.T k j, (true, z) ∈ C) := by
  have hK := recoverLevelsAt_baseline_count_eq M h q hq L hL hOff hlev
    gap hgap pb qb rho hactive hp hqr
  apply List.filter_congr
  intro C hC
  simp only [decide_eq_decide]
  constructor
  · rintro ⟨⟨w, hw⟩, hlo, hhi⟩
    obtain ⟨r, hr, j, hj0, hj, hwm, _, _⟩ := finite_policy_level_cover M q L hL x w
    have he := recoveryComponents_eq_component_of_mem pb qb rho gap hC hw
    have hrK : r < L.K := by
      by_contra hh
      have hrK : r = L.K := by omega
      subst r
      have ht := recoverLevelsAt_positive_endpoint_le_tail_component
        M h q hq L hL hOff hlev gap hgap pb qb rho hactive hp hqr
        (k + 1) j ⟨by omega, by omega⟩ ⟨hj0, hj⟩ w hwm x
      rw [he] at ht
      rw [hK, if_neg (show k ≠ L.K by omega)] at hhi
      exact (not_lt_of_ge ht) hhi
    have hm : recoveryComponent pb qb rho gap (true, w) ∈
        (recoveryComponents pb qb rho gap).filter (fun D =>
          (∃ z, (true, z) ∈ D) ∧
          (recoverLevelsAt pb qb rho gap : LevelData Z X).pLev k x ≤ componentAverage pb qb D ∧
          (if k = (recoverLevelsAt pb qb rho gap : LevelData Z X).K then
            componentAverage pb qb D ≤ 1 else componentAverage pb qb D <
              (recoverLevelsAt pb qb rho gap : LevelData Z X).pLev (k + 1) x)) := by
      rw [he]
      exact List.mem_filter.mpr ⟨hC, by simpa using And.intro ⟨w, hw⟩ ⟨hlo, hhi⟩⟩
    have hkr := (recoveryComponents_interior_policy_numeric_filter_mem_iff M h q hq L hL
      hOff hlev gap hgap pb qb rho hactive hp hqr k r j ⟨hk.1, by omega⟩
      hrK ⟨hj0, hj⟩ w hwm x).mp hm
    subst r
    exact ⟨j, ⟨hj0, hj⟩, w, hwm, hw⟩
  · rintro ⟨j, hj, w, hwm, hw⟩
    have hm := (recoveryComponents_interior_policy_numeric_filter_mem_iff M h q hq L hL
      hOff hlev gap hgap pb qb rho hactive hp hqr k k j ⟨hk.1, by omega⟩
      (by omega) hj w hwm x).mpr rfl
    have he := recoveryComponents_eq_component_of_mem pb qb rho gap hC hw
    rw [he] at hm
    simpa only [decide_eq_true_eq] using (List.mem_filter.mp hm).2

-- @node: recoveryComponents_lower_policy_numeric_list_eq
/-- Suppose threshold crossing, measurable policy propensities, invariant population level ordering, policy levels avoiding their bins' lower baseline boundaries before the terminal bin, measurable baseline levels, positive gap separation, correct activity classification outside the zero baseline class, and baseline and policy marginal errors below one quarter of the gap. For [a positive bin below the terminal bin](hyp:hk) and [representatives belonging to each positive policy class in that bin](hyp:hrep), [the ordered components containing policy vertices whose fitted averages lie between the recovered bin endpoints, including the lower and excluding the upper, are exactly the representatives' policy components in policy-index order, at every covariate value](goal). -/
lemma recoveryComponents_lower_policy_numeric_list_eq
    (k : ℕ) (hk : 1 ≤ k ∧ k < L.K) (x : X) (rep : ℕ → Z)
    (hrep : ∀ j, (1 ≤ j ∧ j ≤ L.l k) → rep j ∈ L.T k j) :
    (recoveryComponents pb qb rho gap).filter (fun C =>
      (∃ z, (true, z) ∈ C) ∧
      (recoverLevelsAt pb qb rho gap : LevelData Z X).pLev k x ≤ componentAverage pb qb C ∧
      (if k = (recoverLevelsAt pb qb rho gap : LevelData Z X).K then
        componentAverage pb qb C ≤ 1 else componentAverage pb qb C <
          (recoverLevelsAt pb qb rho gap : LevelData Z X).pLev (k + 1) x)) =
    (List.range (L.l k)).map (fun j => recoveryComponent pb qb rho gap (true, rep (j + 1))) := by
  rw [recoveryComponents_lower_policy_numeric_filter_eq M h q hq L hL hOff hlev
    gap hgap pb qb rho hactive hp hqr k hk x]
  exact recoveryComponents_interior_policy_class_list_eq M q hq L hL hOff hlev
    gap hgap pb qb rho hactive hp hqr k (by omega) rep hrep

-- @node: recoverLevelsAt_lower_policy_count_eq
/-- Assume threshold crossing, measurable policy propensities, invariant population level ordering, policy levels avoiding their bins' lower baseline boundaries before the terminal bin, measurable baseline levels, positive gap separation, activity exactly outside the zero baseline class, and baseline and policy marginal errors below one quarter of the gap. In [any positive bin below the terminal bin](hyp:hk), [the recovered number of policy levels equals the population number](goal). -/
lemma recoverLevelsAt_lower_policy_count_eq
    (k : ℕ) (hk : 1 ≤ k ∧ k < L.K) :
    (recoverLevelsAt pb qb rho gap : LevelData Z X).l k = L.l k := by
  let rep : ℕ → Z := fun j => if hj : 1 ≤ j ∧ j ≤ L.l k then
    Classical.choose (ordered_policy_level_nonempty M q L hL k j (by omega) hj.1 hj.2)
    else Classical.choice inferInstance
  have hrep : ∀ j, (1 ≤ j ∧ j ≤ L.l k) → rep j ∈ L.T k j := by
    intro j hj
    simpa only [rep, dif_pos hj] using
      Classical.choose_spec (ordered_policy_level_nonempty M q L hL k j (by omega) hj.1 hj.2)
  have he := congrArg List.length (recoveryComponents_lower_policy_numeric_list_eq
    M h q hq L hL hOff hlev gap hgap pb qb rho hactive hp hqr k hk
    (Classical.choice inferInstance) rep hrep)
  simpa only [recoverLevelsAt, List.length_map, List.length_range] using he

-- @node: recoverLevelsAt_lower_policy_label_eq
/-- Under threshold crossing, measurable policy propensities, invariant population level ordering, policy levels avoiding their bins' lower baseline boundaries before the terminal bin, measurable baseline levels, positive gap separation, correct activity classification outside the zero baseline class, and baseline and policy marginal errors below one quarter of the gap, take [a positive bin below the terminal bin](hyp:hk) and [a valid positive policy index in that bin](hyp:hj). [The recovered instrument class at that bin and policy index equals the corresponding population policy class](goal). -/
lemma recoverLevelsAt_lower_policy_label_eq
    (k j : ℕ) (hk : 1 ≤ k ∧ k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k) :
    (recoverLevelsAt pb qb rho gap : LevelData Z X).T k j = L.T k j := by
  have hl := recoverLevelsAt_lower_policy_count_eq M h q hq L hL hOff hlev
    gap hgap pb qb rho hactive hp hqr k hk
  have hf := recoveryComponents_lower_policy_numeric_filter_eq M h q hq L hL hOff hlev
    gap hgap pb qb rho hactive hp hqr k hk (Classical.choice inferInstance)
  have hvalid : ¬ (j = 0 ∨
      (recoverLevelsAt pb qb rho gap : LevelData Z X).l k < j) := by omega
  let Qs := (recoveryComponents pb qb rho gap).filter (fun C =>
    (∃ z, (true, z) ∈ C) ∧
    (recoverLevelsAt pb qb rho gap : LevelData Z X).pLev k
      (Classical.choice inferInstance) ≤ componentAverage pb qb C ∧
    (if k = (recoverLevelsAt pb qb rho gap : LevelData Z X).K then
      componentAverage pb qb C ≤ 1 else componentAverage pb qb C <
        (recoverLevelsAt pb qb rho gap : LevelData Z X).pLev (k + 1)
          (Classical.choice inferInstance)))
  change ¬ (j = 0 ∨ Qs.length < j) at hvalid
  change Qs = _ at hf
  change (if j = 0 ∨ Qs.length < j then ∅ else
    Finset.univ.filter (fun z => (true, z) ∈ Qs.getD (j - 1) ∅)) = _
  rw [if_neg hvalid, hf]
  exact recoveryComponents_interior_policy_indexed_projection_eq M q hq L hL hOff hlev
    gap hgap pb qb rho hactive hp hqr k j (by omega) hj

omit hactive hp hqr in
-- @node: recovery_lower_policy_labels_failure_tendsto_zero
/-- In a threshold-crossing model with measurable policy propensities, invariant population level ordering, policy levels avoiding their bins' lower baseline boundaries before the terminal bin, measurable baseline levels, and positive gap separation, suppose [the activity threshold tends to zero](hyp:hrho), [each fitted baseline marginal converges in probability to its population value](hyp:hpconv), [each fitted policy marginal converges in probability to its population value](hyp:hqconv), and [threshold exceedance at every zero baseline marginal has measure tending to zero](hyp:hzero). [The measure of samples on which any positive bin below the terminal bin has an incorrect policy-level count or an incorrect class at a valid positive policy index tends to zero](goal). -/
lemma recovery_lower_policy_labels_failure_tendsto_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (pb qb : ℕ → A → Z → ℝ) (rho : ℕ → ℝ)
    (hrho : Tendsto rho atTop (𝓝 0))
    (hpconv : ∀ z, Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => pb n a z) atTop (fun _ _ => ∫ x, M.prop z x ∂xLaw M))
    (hqconv : ∀ z, Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => qb n a z) atTop (fun _ _ => ∫ x, q z x ∂xLaw M))
    (hzero : ∀ z, (∫ x, M.prop z x ∂xLaw M) = 0 →
      Tendsto (fun n => μ {a | rho n < pb n a z}) atTop (𝓝 0)) :
    Tendsto (fun n => μ {a | ¬ (∀ k, (1 ≤ k ∧ k < L.K) →
      (recoverLevelsAt (pb n a) (qb n a) (rho n) gap : LevelData Z X).l k = L.l k ∧
      ∀ j, (1 ≤ j ∧ j ≤ L.l k) →
        (recoverLevelsAt (pb n a) (qb n a) (rho n) gap : LevelData Z X).T k j = L.T k j)})
      atTop (𝓝 0) := by
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
  intro k hk
  constructor
  · exact recoverLevelsAt_lower_policy_count_eq M h q hq L hL hOff hlev
      gap hgap (pb n a) (qb n a) (rho n) ha
      (fun z => he (false, z)) (fun z => he (true, z)) k hk
  · intro j hj
    exact recoverLevelsAt_lower_policy_label_eq M h q hq L hL hOff hlev
      gap hgap (pb n a) (qb n a) (rho n) ha
      (fun z => he (false, z)) (fun z => he (true, z)) k j hk hj

omit q hq hL hgap hactive hp hqr in
-- @node: firstStageRate_lower_policy_labels_failure_tendsto_zero
/-- Assume threshold crossing, policy levels avoiding their bins' lower baseline boundaries before the terminal bin, measurable baseline levels, [an equal half split of the observed sample](hyp:hSplit), and [a predictor measurable using the training half](hyp:hTrain), [taking values between zero and one](hyp:hrange), and [having maximum population L2 error across instruments negligible in probability relative to sample size to the negative one-quarter power](hyp:hRate). If [the policy map preserves admissible propensities](hyp:hphi), [is differentiable with the specified derivative](hyp:hd), [has a bounded Lipschitz derivative](hyp:hDerivative), [the transformed population propensities have the specified invariant level ordering](hyp:hLphi), [they satisfy positive gap separation jointly with the baseline](hyp:hgapPhi), [the threshold tends to zero](hyp:hrho), and [the threshold times the fourth root of sample size tends to infinity](hyp:hgrowth), then [along even sample sizes the probability of an incorrect policy count or any incorrect valid positive indexed policy class in any positive nonterminal bin tends to zero](goal). -/
lemma firstStageRate_lower_policy_labels_failure_tendsto_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (pHat : ℕ → A → Z → X → ℝ)
    (hTrain : TrainingPredictorMeasurable M S I₁
      (fun n a (zx : Z × X) => pHat n a zx.1 zx.2))
    (hrange : ∀ n a z x, pHat n a z x ∈ Icc (0 : ℝ) 1)
    (hRate : FiniteFirstStageRate M μ pHat)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (hLphi : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (hgapPhi : PropensityGapSeparationWitness M.prop (policyProp phi M.prop) gap)
    (rho : ℕ → ℝ) (hrho : Tendsto rho atTop (𝓝 0))
    (hgrowth : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 4 : ℝ) * rho n) atTop atTop) :
    Tendsto (fun n => μ {a | ¬ (∀ k, (1 ≤ k ∧ k < L.K) →
      (recoveredData M S I₁ I₂ pHat phi rho gap (2 * (n + 1)) a).l k = L.l k ∧
      ∀ j, (1 ≤ j ∧ j ≤ L.l k) →
        (recoveredData M S I₁ I₂ pHat phi rho gap (2 * (n + 1)) a).T k j = L.T k j)})
      atTop (𝓝 0) := by
  have hindex : Tendsto (fun n : ℕ => 2 * (n + 1)) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    exact eventually_atTop.2 ⟨b, fun n hn => by omega⟩
  have hqphi : Measurable (Function.uncurry (policyProp phi M.prop)) := by fun_prop
  have hconv := firstStageRate_pBar_marginals_consistent M μ S I₁ I₂ hSplit h
    pHat hTrain hrange hRate phi dphi hphi hd hDerivative
  apply recovery_lower_policy_labels_failure_tendsto_zero M h
    (policyProp phi M.prop) hqphi L hLphi hOff hlev gap hgapPhi μ
    (fun n a => pBar M S I₂ pHat (2 * (n + 1)) a)
    (fun n a => pBar M S I₂ (fun n a => policyProp phi (pHat n a)) (2 * (n + 1)) a)
    (fun n => rho (2 * (n + 1))) (hrho.comp hindex) hconv.1 hconv.2
  intro z hz
  have he := firstStageRate_pBar_baseline_quarter_rate M μ S I₁ I₂ hSplit h
    pHat hTrain hrange hRate z
  simp only [hz, sub_zero] at he
  exact littleOp_threshold_exceedance_tendsto_zero μ _ _ _ he
    (recovery_threshold_dominates_quarter_rate rho hgrowth)

end Papers.TbsPrteOptimalTransport

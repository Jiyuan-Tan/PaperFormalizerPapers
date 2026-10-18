module
public import Papers.TbsPrteOptimalTransport.Helpers.RecoveryPolicyIndexing
public import Papers.TbsPrteOptimalTransport.Helpers.LevelZeroRecovery
/-! Exact recovery of indexed policy labels in baseline bins.
The component ordering identifies both baseline endpoints; stability of the
interval filter then identifies its length and every indexed policy set. -/
public section
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Filter Set
open scoped Classical Topology
universe v
variable {Z : Type v} [Fintype Z] [DecidableEq Z]

-- @node: recoverLevelsAt_interior_policy_labels_stable
/-- Suppose [two fitted systems have the same active vertices](hyp:hactive), [the first system's active values are within one quarter of the gap of common population values](hyp:herror), [the second satisfies the same bound](hyp:herror'), and [active population values are equal or at least the gap apart](hyp:hsep). For [a positive bin index](hyp:hk) [strictly below the first system's recovered baseline count](hyp:hkK), [the two systems recover the same number of policy levels in that bin and the same instrument class at every policy index](goal). -/
lemma recoverLevelsAt_interior_policy_labels_stable {X : Type v}
    (pb qb pb' qb' : Z → ℝ) (rho rho' gap : ℝ)
    (truth : RecoveryVertex Z → ℝ)
    (hactive : recoveryActive pb rho = recoveryActive pb' rho')
    (herror : ∀ v ∈ recoveryActive pb rho,
      |vertexValue pb qb v - truth v| < gap / 4)
    (herror' : ∀ v ∈ recoveryActive pb' rho',
      |vertexValue pb' qb' v - truth v| < gap / 4)
    (hsep : ∀ a ∈ recoveryActive pb rho, ∀ b ∈ recoveryActive pb rho,
      truth a = truth b ∨ gap ≤ |truth a - truth b|)
    (k : ℕ) (hk : 0 < k)
    (hkK : k < (recoverLevelsAt pb qb rho gap : LevelData Z X).K) :
    (recoverLevelsAt pb qb rho gap : LevelData Z X).l k =
      (recoverLevelsAt pb' qb' rho' gap : LevelData Z X).l k ∧
    ∀ j, (recoverLevelsAt pb qb rho gap : LevelData Z X).T k j =
      (recoverLevelsAt pb' qb' rho' gap : LevelData Z X).T k j := by
  let Cs := recoveryComponents pb qb rho gap
  let Bs := Cs.filter (fun C => ∃ z, (false, z) ∈ C)
  have hCs := recoveryComponents_eq_of_common_population_classes
    pb qb pb' qb' rho rho' gap truth hactive herror herror' hsep
  have hklen : k < Bs.length := hkK
  have hB : Bs.getD (k - 1) ∅ ∈ Cs := by
    have hi : k - 1 < Bs.length := by omega
    rw [← List.getElem_eq_getD (h := hi) ∅]
    exact List.mem_of_mem_filter (List.getElem_mem hi)
  have hD : Bs.getD k ∅ ∈ Cs := by
    rw [← List.getElem_eq_getD (h := hklen) ∅]
    exact List.mem_of_mem_filter (List.getElem_mem hklen)
  have hfilter := recoveryComponents_policy_interval_filter_stable
    pb qb pb' qb' rho rho' gap truth hactive herror herror' hsep hB hD
  have hk0 : k ≠ 0 := by omega
  have hk1 : k + 1 ≠ 0 := by omega
  have hkle : k ≤ Bs.length := by omega
  have hk1le : k + 1 ≤ Bs.length := by omega
  have hkne : k ≠ Bs.length := by omega
  have hQs :
      (Cs.filter (fun C => (∃ z, (true, z) ∈ C) ∧
        componentAverage pb qb (Bs.getD (k - 1) ∅) ≤ componentAverage pb qb C ∧
        componentAverage pb qb C < componentAverage pb qb (Bs.getD k ∅))) =
      (Cs.filter (fun C => (∃ z, (true, z) ∈ C) ∧
        componentAverage pb' qb' (Bs.getD (k - 1) ∅) ≤ componentAverage pb' qb' C ∧
        componentAverage pb' qb' C < componentAverage pb' qb' (Bs.getD k ∅))) := by
    simpa only [← hCs] using hfilter
  constructor
  · simpa only [recoverLevelsAt, ← hCs, ← show Cs = recoveryComponents pb qb rho gap from rfl,
      ← show Bs = Cs.filter (fun C => ∃ z, (false, z) ∈ C) from rfl,
      if_neg hk0, if_pos hkle, if_neg hkne, if_neg hk1, if_pos hk1le,
      Nat.add_sub_cancel] using congrArg List.length hQs
  · intro j
    simp only [recoverLevelsAt, ← hCs, ← show Cs = recoveryComponents pb qb rho gap from rfl,
      ← show Bs = Cs.filter (fun C => ∃ z, (false, z) ∈ C) from rfl,
      if_neg hk0, if_pos hkle, if_neg hkne, if_neg hk1, if_pos hk1le,
      Nat.add_sub_cancel, hQs]

-- All interior bins are identified on one good event. No union over the
-- policy indices is needed: the ordered filtered list agrees in its entirety.
-- @node: recovery_interior_policy_labels_failure_tendsto_zero
/-- Assume [nonnegative population baseline marginals](hyp:hp), [an activity threshold tending to zero](hyp:hrho), [a positive gap](hyp:hgap), [population vertex values equal or separated by at least that gap](hyp:hsep), [convergence in probability of each fitted vertex value to its population value](hyp:hconv), and [vanishing measure of threshold exceedance at every zero baseline marginal](hyp:hzero). [The measure of samples where any positive bin below the population marginal graph's baseline count has an incorrect policy-level count or any incorrect indexed policy class tends to zero](goal). -/
lemma recovery_interior_policy_labels_failure_tendsto_zero
    {A : Type*} {X : Type v} [MeasurableSpace A]
    (μ : Measure A) (pb qb : ℕ → A → Z → ℝ) (p q : Z → ℝ)
    (hp : ∀ z, 0 ≤ p z) (rho : ℕ → ℝ)
    (hrho : Tendsto rho atTop (𝓝 0)) (gap : ℝ) (hgap : 0 < gap)
    (hsep : ∀ v w, vertexValue p q v = vertexValue p q w ∨
      gap ≤ |vertexValue p q v - vertexValue p q w|)
    (hconv : ∀ v, Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => vertexValue (pb n a) (qb n a) v) atTop
      (fun _ _ => vertexValue p q v))
    (hzero : ∀ z, p z = 0 →
      Tendsto (fun n => μ {a | rho n < pb n a z}) atTop (𝓝 0)) :
    Tendsto (fun n => μ {a | ¬ (
      ∀ k, 0 < k → k < (recoverLevelsAt p q 0 gap : LevelData Z X).K →
        (recoverLevelsAt (pb n a) (qb n a) (rho n) gap : LevelData Z X).l k =
          (recoverLevelsAt p q 0 gap : LevelData Z X).l k ∧
        ∀ j, (recoverLevelsAt (pb n a) (qb n a) (rho n) gap : LevelData Z X).T k j =
          (recoverLevelsAt p q 0 gap : LevelData Z X).T k j)}) atTop (𝓝 0) := by
  have hgood := marginal_recovery_good_event_failure_tendsto_zero
    μ pb qb p q hp rho hrho gap hgap hconv hzero
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hgood
    (fun _ => zero_le)
  intro n
  apply measure_mono
  intro a hbad hnot
  change recoveryActive (pb n a) (rho n) = recoveryActive p 0 ∧
    ∀ v ∈ recoveryActive (pb n a) (rho n),
      |vertexValue (pb n a) (qb n a) v - vertexValue p q v| < gap / 4 at hnot
  have hreference : ∀ v ∈ recoveryActive p 0,
      |vertexValue p q v - vertexValue p q v| < gap / 4 := by
    intro v _
    simp only [sub_self, abs_zero]
    positivity
  have hs : ∀ v ∈ recoveryActive (pb n a) (rho n),
      ∀ w ∈ recoveryActive (pb n a) (rho n),
      vertexValue p q v = vertexValue p q w ∨
        gap ≤ |vertexValue p q v - vertexValue p q w| := fun v _ w _ => hsep v w
  have hK := (recoverLevelsAt_baseline_labels_stable (X := X)
    (pb n a) (qb n a) p q (rho n) 0 gap (vertexValue p q)
    hnot.1 hnot.2 hreference hs).1
  apply hbad
  intro k hk hkK
  exact recoverLevelsAt_interior_policy_labels_stable
    (pb n a) (qb n a) p q (rho n) 0 gap (vertexValue p q)
    hnot.1 hnot.2 hreference hs k hk (hK.symm ▸ hkK)

omit [Fintype Z] [DecidableEq Z] in
-- @node: recovery_componentAverage_unit_range
/-- If [every fitted baseline and policy marginal lies between zero and one](hyp:hrange), then [the fitted average over any finite collection of baseline and policy vertices also lies between zero and one](goal). -/
lemma recovery_componentAverage_unit_range (pb qb : Z → ℝ)
    (hrange : ∀ z, pb z ∈ Icc (0 : ℝ) 1 ∧ qb z ∈ Icc (0 : ℝ) 1)
    (C : Finset (RecoveryVertex Z)) :
    componentAverage pb qb C ∈ Icc (0 : ℝ) 1 := by
  apply finite_unit_average_range
  intro v _
  rcases v with ⟨b, z⟩
  cases b
  · exact (hrange z).1
  · exact (hrange z).2

-- @node: recoverLevelsAt_boundary_policy_labels_stable
/-- If [two fitted systems have the same active vertices](hyp:hactive), [the first system approximates common population values within one quarter of the gap on active vertices](hyp:herror), [the second obeys the same bound](hyp:herror'), [active population values are equal or at least the gap apart](hyp:hsep), and [both systems' baseline and policy marginals lie between zero and one](hyp:hrange,hrange'), then for [the initial bin or the first system's terminal bin](hyp:hk), [the recovered policy-level counts and all indexed policy classes agree across systems](goal). -/
lemma recoverLevelsAt_boundary_policy_labels_stable {X : Type v}
    (pb qb pb' qb' : Z → ℝ) (rho rho' gap : ℝ)
    (truth : RecoveryVertex Z → ℝ)
    (hactive : recoveryActive pb rho = recoveryActive pb' rho')
    (herror : ∀ v ∈ recoveryActive pb rho,
      |vertexValue pb qb v - truth v| < gap / 4)
    (herror' : ∀ v ∈ recoveryActive pb' rho',
      |vertexValue pb' qb' v - truth v| < gap / 4)
    (hsep : ∀ a ∈ recoveryActive pb rho, ∀ b ∈ recoveryActive pb rho,
      truth a = truth b ∨ gap ≤ |truth a - truth b|)
    (hrange : ∀ z, pb z ∈ Icc (0 : ℝ) 1 ∧ qb z ∈ Icc (0 : ℝ) 1)
    (hrange' : ∀ z, pb' z ∈ Icc (0 : ℝ) 1 ∧ qb' z ∈ Icc (0 : ℝ) 1)
    (k : ℕ)
    (hk : k = 0 ∨ k = (recoverLevelsAt pb qb rho gap : LevelData Z X).K) :
    (recoverLevelsAt pb qb rho gap : LevelData Z X).l k =
      (recoverLevelsAt pb' qb' rho' gap : LevelData Z X).l k ∧
    ∀ j, (recoverLevelsAt pb qb rho gap : LevelData Z X).T k j =
      (recoverLevelsAt pb' qb' rho' gap : LevelData Z X).T k j := by
  let Cs := recoveryComponents pb qb rho gap
  let Bs := Cs.filter (fun C => ∃ z, (false, z) ∈ C)
  have hCs := recoveryComponents_eq_of_common_population_classes
    pb qb pb' qb' rho rho' gap truth hactive herror herror' hsep
  have hbounds (C : Finset (RecoveryVertex Z)) :=
    recovery_componentAverage_unit_range pb qb hrange C
  have hbounds' (C : Finset (RecoveryVertex Z)) :=
    recovery_componentAverage_unit_range pb' qb' hrange' C
  let p := fun i => if i = 0 then (0 : ℝ) else if i ≤ Bs.length then
    componentAverage pb qb (Bs.getD (i - 1) ∅) else 1
  let p' := fun i => if i = 0 then (0 : ℝ) else if i ≤ Bs.length then
    componentAverage pb' qb' (Bs.getD (i - 1) ∅) else 1
  have hQs :
      Cs.filter (fun C => (∃ z, (true, z) ∈ C) ∧ p k ≤ componentAverage pb qb C ∧
        (if k = Bs.length then componentAverage pb qb C ≤ 1
          else componentAverage pb qb C < p (k + 1))) =
      Cs.filter (fun C => (∃ z, (true, z) ∈ C) ∧ p' k ≤ componentAverage pb' qb' C ∧
        (if k = Bs.length then componentAverage pb' qb' C ≤ 1
          else componentAverage pb' qb' C < p' (k + 1))) := by
    apply List.filter_congr
    intro C hC
    rcases hk with rfl | hk
    · by_cases hK : Bs.length = 0
      · simp only [p, p', if_pos rfl, hK,
          (hbounds C).1, (hbounds C).2, (hbounds' C).1, (hbounds' C).2,
          if_true, and_true]
      · have hi : 0 < Bs.length := Nat.pos_of_ne_zero hK
        have hD : Bs.getD 0 ∅ ∈ Cs := by
          rw [← List.getElem_eq_getD (h := hi) ∅]
          exact List.mem_of_mem_filter (List.getElem_mem hi)
        have hlt := recoveryComponents_member_average_lt_stable
          pb qb pb' qb' rho rho' gap truth hactive herror herror' hsep hC hD
        simp only [p, p', if_pos rfl, if_neg (Ne.symm hK),
          show (0 + 1 : ℕ) ≠ 0 by omega, if_false,
          show 0 + 1 ≤ Bs.length by omega, if_true, Nat.add_sub_cancel,
          (hbounds C).1, (hbounds' C).1, true_and, hlt]
    · have hklen : k = Bs.length := hk
      by_cases hk0 : k = 0
      · have hK : Bs.length = 0 := hklen.symm.trans hk0
        simp only [hk0, hK, p, p', if_pos rfl,
          (hbounds C).1, (hbounds C).2, (hbounds' C).1, (hbounds' C).2,
          if_true, and_true]
      · have hi : k - 1 < Bs.length := by omega
        have hB : Bs.getD (k - 1) ∅ ∈ Cs := by
          rw [← List.getElem_eq_getD (h := hi) ∅]
          exact List.mem_of_mem_filter (List.getElem_mem hi)
        have hle := recoveryComponents_member_average_le_stable
          pb qb pb' qb' rho rho' gap truth hactive herror herror' hsep hB hC
        simp only [p, p', if_neg hk0, if_pos (show k ≤ Bs.length by omega),
          if_pos hklen, (hbounds C).2, (hbounds' C).2, and_true, hle]
  dsimp only [p, p'] at hQs
  constructor
  · simpa only [recoverLevelsAt, ← hCs, ← show Cs = recoveryComponents pb qb rho gap from rfl,
      ← show Bs = Cs.filter (fun C => ∃ z, (false, z) ∈ C) from rfl] using
      congrArg List.length hQs
  · intro j
    simp only [recoverLevelsAt, ← hCs, ← show Cs = recoveryComponents pb qb rho gap from rfl,
      ← show Bs = Cs.filter (fun C => ∃ z, (false, z) ∈ C) from rfl, hQs]

-- @node: recoverLevelsAt_all_labels_stable
/-- Suppose [two fitted systems have identical active vertices](hyp:hactive), [the first system's active values approximate common population values within one quarter of the gap](hyp:herror), [the second has the same accuracy](hyp:herror'), [active population values are equal or separated by at least the gap](hyp:hsep), and [all baseline and policy marginals in both systems lie between zero and one](hyp:hrange,hrange'). [The recovered baseline counts and every baseline class agree, and in every bin up to the first system's baseline count the policy-level counts and all indexed policy classes agree](goal). -/
lemma recoverLevelsAt_all_labels_stable {X : Type v}
    (pb qb pb' qb' : Z → ℝ) (rho rho' gap : ℝ)
    (truth : RecoveryVertex Z → ℝ)
    (hactive : recoveryActive pb rho = recoveryActive pb' rho')
    (herror : ∀ v ∈ recoveryActive pb rho,
      |vertexValue pb qb v - truth v| < gap / 4)
    (herror' : ∀ v ∈ recoveryActive pb' rho',
      |vertexValue pb' qb' v - truth v| < gap / 4)
    (hsep : ∀ a ∈ recoveryActive pb rho, ∀ b ∈ recoveryActive pb rho,
      truth a = truth b ∨ gap ≤ |truth a - truth b|)
    (hrange : ∀ z, pb z ∈ Icc (0 : ℝ) 1 ∧ qb z ∈ Icc (0 : ℝ) 1)
    (hrange' : ∀ z, pb' z ∈ Icc (0 : ℝ) 1 ∧ qb' z ∈ Icc (0 : ℝ) 1) :
    (recoverLevelsAt pb qb rho gap : LevelData Z X).K =
      (recoverLevelsAt pb' qb' rho' gap : LevelData Z X).K ∧
    (∀ k, (recoverLevelsAt pb qb rho gap : LevelData Z X).S k =
      (recoverLevelsAt pb' qb' rho' gap : LevelData Z X).S k) ∧
    ∀ k, k ≤ (recoverLevelsAt pb qb rho gap : LevelData Z X).K →
      (recoverLevelsAt pb qb rho gap : LevelData Z X).l k =
        (recoverLevelsAt pb' qb' rho' gap : LevelData Z X).l k ∧
      ∀ j, (recoverLevelsAt pb qb rho gap : LevelData Z X).T k j =
        (recoverLevelsAt pb' qb' rho' gap : LevelData Z X).T k j := by
  have hb := recoverLevelsAt_baseline_labels_stable (X := X)
    pb qb pb' qb' rho rho' gap truth hactive herror herror' hsep
  refine ⟨hb.1, hb.2, ?_⟩
  intro k hk
  by_cases hboundary : k = 0 ∨ k = (recoverLevelsAt pb qb rho gap : LevelData Z X).K
  · exact recoverLevelsAt_boundary_policy_labels_stable
      pb qb pb' qb' rho rho' gap truth hactive herror herror' hsep hrange hrange' k hboundary
  · have hk0 : 0 < k := by omega
    have hkK : k < (recoverLevelsAt pb qb rho gap : LevelData Z X).K := by omega
    exact recoverLevelsAt_interior_policy_labels_stable
      pb qb pb' qb' rho rho' gap truth hactive herror herror' hsep k hk0 hkK

-- @node: recovery_all_labels_failure_tendsto_zero
/-- Suppose [all fitted baseline and policy marginals lie between zero and one](hyp:hrange), [their population counterparts also lie between zero and one](hyp:hrange'), [the activity threshold tends to zero](hyp:hrho), [the gap is positive](hyp:hgap), [population vertex values are equal or at least the gap apart](hyp:hsep), [fitted vertex values converge in probability to their population counterparts](hyp:hconv), and [threshold exceedance at each zero baseline marginal has measure tending to zero](hyp:hzero). [The measure of samples where the recovered baseline count, any baseline class, or any policy count or indexed policy class in a population bin differs from recovery using the population marginals tends to zero](goal). -/
lemma recovery_all_labels_failure_tendsto_zero
    {A : Type*} {X : Type v} [MeasurableSpace A]
    (μ : Measure A) (pb qb : ℕ → A → Z → ℝ) (p q : Z → ℝ)
    (hrange : ∀ n a z, pb n a z ∈ Icc (0 : ℝ) 1 ∧ qb n a z ∈ Icc (0 : ℝ) 1)
    (hrange' : ∀ z, p z ∈ Icc (0 : ℝ) 1 ∧ q z ∈ Icc (0 : ℝ) 1)
    (rho : ℕ → ℝ) (hrho : Tendsto rho atTop (𝓝 0)) (gap : ℝ) (hgap : 0 < gap)
    (hsep : ∀ v w, vertexValue p q v = vertexValue p q w ∨
      gap ≤ |vertexValue p q v - vertexValue p q w|)
    (hconv : ∀ v, Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => vertexValue (pb n a) (qb n a) v) atTop
      (fun _ _ => vertexValue p q v))
    (hzero : ∀ z, p z = 0 →
      Tendsto (fun n => μ {a | rho n < pb n a z}) atTop (𝓝 0)) :
    Tendsto (fun n => μ {a | ¬ (
      (recoverLevelsAt (pb n a) (qb n a) (rho n) gap : LevelData Z X).K =
        (recoverLevelsAt p q 0 gap : LevelData Z X).K ∧
      (∀ k, (recoverLevelsAt (pb n a) (qb n a) (rho n) gap : LevelData Z X).S k =
        (recoverLevelsAt p q 0 gap : LevelData Z X).S k) ∧
      ∀ k, k ≤ (recoverLevelsAt p q 0 gap : LevelData Z X).K →
        (recoverLevelsAt (pb n a) (qb n a) (rho n) gap : LevelData Z X).l k =
          (recoverLevelsAt p q 0 gap : LevelData Z X).l k ∧
        ∀ j, (recoverLevelsAt (pb n a) (qb n a) (rho n) gap : LevelData Z X).T k j =
          (recoverLevelsAt p q 0 gap : LevelData Z X).T k j)}) atTop (𝓝 0) := by
  have hgood := marginal_recovery_good_event_failure_tendsto_zero
    μ pb qb p q (fun z => (hrange' z).1.1) rho hrho gap hgap hconv hzero
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hgood
    (fun _ => zero_le)
  intro n
  apply measure_mono
  intro a hbad hnot
  change recoveryActive (pb n a) (rho n) = recoveryActive p 0 ∧
    ∀ v ∈ recoveryActive (pb n a) (rho n),
      |vertexValue (pb n a) (qb n a) v - vertexValue p q v| < gap / 4 at hnot
  have hreference : ∀ v ∈ recoveryActive p 0,
      |vertexValue p q v - vertexValue p q v| < gap / 4 := by
    intro v _
    simp only [sub_self, abs_zero]
    positivity
  have hs : ∀ v ∈ recoveryActive (pb n a) (rho n),
      ∀ w ∈ recoveryActive (pb n a) (rho n),
      vertexValue p q v = vertexValue p q w ∨
        gap ≤ |vertexValue p q v - vertexValue p q w| := fun v _ w _ => hsep v w
  have hlabels := recoverLevelsAt_all_labels_stable (X := X)
    (pb n a) (qb n a) p q (rho n) 0 gap (vertexValue p q)
    hnot.1 hnot.2 hreference hs (hrange n a) hrange'
  apply hbad
  exact ⟨hlabels.1, hlabels.2.1, fun k hk => hlabels.2.2 k (hlabels.1.symm ▸ hk)⟩

universe u s
variable {Ω : Type u} {X : Type v} {A : Type s}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]

-- This assembles concentration, the first-stage rate, threshold domination,
-- and deterministic label stability. The reference is the population
-- marginal graph; identifying it with LevelStructure is a separate step.
-- @node: firstStageRate_recovered_marginal_labels_failure_tendsto_zero
/-- Under [an equal half split of the observed sample](hyp:hSplit) and [threshold crossing](hyp:h), assume [the first-stage predictor is measurable using the training half](hyp:hTrain), [takes values between zero and one](hyp:hrange), and [has maximum population L2 error across instruments negligible in probability relative to sample size to the negative one-quarter power](hyp:hRate). If [the policy map preserves admissible propensities](hyp:hphi), [is differentiable with the specified derivative](hyp:hd), [has a bounded Lipschitz derivative](hyp:hDerivative), [the threshold tends to zero](hyp:hrho), [the threshold times the fourth root of sample size tends to infinity](hyp:hgrowth), [the gap is positive](hyp:hgap), and [population baseline and transformed-policy marginals are equal or at least the gap apart](hyp:hsep), then [along even sample sizes the probability of any disagreement with population-marginal recovery in the baseline count, any baseline class, or any policy count or indexed policy class in a population bin tends to zero](goal). -/
lemma firstStageRate_recovered_marginal_labels_failure_tendsto_zero
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂) (h : ThresholdCrossing M)
    (pHat : ℕ → A → Z → X → ℝ)
    (hTrain : TrainingPredictorMeasurable M S I₁
      (fun n a (zx : Z × X) => pHat n a zx.1 zx.2))
    (hrange : ∀ n a z x, pHat n a z x ∈ Icc (0 : ℝ) 1)
    (hRate : FiniteFirstStageRate M μ pHat)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (rho : ℕ → ℝ) (hrho : Tendsto rho atTop (𝓝 0))
    (hgrowth : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 4 : ℝ) * rho n) atTop atTop)
    (gap : ℝ) (hgap : 0 < gap)
    (hsep : ∀ v w,
      vertexValue (fun z => ∫ x, M.prop z x ∂xLaw M)
        (fun z => ∫ x, policyProp phi M.prop z x ∂xLaw M) v =
      vertexValue (fun z => ∫ x, M.prop z x ∂xLaw M)
        (fun z => ∫ x, policyProp phi M.prop z x ∂xLaw M) w ∨
      gap ≤ |vertexValue (fun z => ∫ x, M.prop z x ∂xLaw M)
        (fun z => ∫ x, policyProp phi M.prop z x ∂xLaw M) v -
        vertexValue (fun z => ∫ x, M.prop z x ∂xLaw M)
          (fun z => ∫ x, policyProp phi M.prop z x ∂xLaw M) w|) :
    let L : LevelData Z X := recoverLevelsAt
      (fun z => ∫ x, M.prop z x ∂xLaw M)
      (fun z => ∫ x, policyProp phi M.prop z x ∂xLaw M) 0 gap
    Tendsto (fun n => μ {a | ¬ (
      (recoveredData M S I₁ I₂ pHat phi rho gap (2 * (n + 1)) a).K = L.K ∧
      (∀ k, (recoveredData M S I₁ I₂ pHat phi rho gap (2 * (n + 1)) a).S k = L.S k) ∧
      ∀ k, k ≤ L.K →
        (recoveredData M S I₁ I₂ pHat phi rho gap (2 * (n + 1)) a).l k = L.l k ∧
        ∀ j, (recoveredData M S I₁ I₂ pHat phi rho gap (2 * (n + 1)) a).T k j = L.T k j)})
      atTop (𝓝 0) := by
  have : IsProbabilityMeasure (xLaw M) :=
    Measure.isProbabilityMeasure_map M.measX.aemeasurable
  have hindex : Tendsto (fun n : ℕ => 2 * (n + 1)) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    exact eventually_atTop.2 ⟨b, fun n hn => by omega⟩
  have hconv := firstStageRate_pBar_marginals_consistent M μ S I₁ I₂ hSplit h
    pHat hTrain hrange hRate phi dphi hphi hd hDerivative
  have hint_range (f : X → ℝ) (hf : Measurable f) (hr : ∀ x, f x ∈ Icc (0 : ℝ) 1) :
      (∫ x, f x ∂xLaw M) ∈ Icc (0 : ℝ) 1 := by
    have hi := (recovery_unit_interval_memLp M f hf hr).integrable (by norm_num)
    refine ⟨integral_nonneg (fun x => (hr x).1), ?_⟩
    have hu := integral_mono hi (integrable_const (1 : ℝ)) (fun x => (hr x).2)
    simpa only [integral_const, probReal_univ, one_smul] using hu
  have hpopulation (z : Z) :
      (∫ x, M.prop z x ∂xLaw M) ∈ Icc (0 : ℝ) 1 ∧
      (∫ x, policyProp phi M.prop z x ∂xLaw M) ∈ Icc (0 : ℝ) 1 := by
    have hp : Measurable (M.prop z) := by
      first | fun_prop | exact h.2.1.comp (measurable_const.prodMk measurable_id)
    have hq : Measurable (policyProp phi M.prop z) := by
      fun_prop
    exact ⟨hint_range _ hp (M.rangeProp z),
      hint_range _ hq (fun x => hphi.2 z x _ (M.rangeProp z x))⟩
  apply recovery_all_labels_failure_tendsto_zero (X := X) μ
    (fun n a => pBar M S I₂ pHat (2 * (n + 1)) a)
    (fun n a => pBar M S I₂ (fun n a => policyProp phi (pHat n a)) (2 * (n + 1)) a)
    (fun z => ∫ x, M.prop z x ∂xLaw M)
    (fun z => ∫ x, policyProp phi M.prop z x ∂xLaw M)
    (fun n a z => recovery_averages_range M S I₂ pHat phi hrange hphi _ a z)
    hpopulation (fun n => rho (2 * (n + 1))) (hrho.comp hindex) gap hgap hsep
  · rintro ⟨b, z⟩
    cases b
    · exact hconv.1 z
    · exact hconv.2 z
  · intro z hz
    have he := firstStageRate_pBar_baseline_quarter_rate M μ S I₁ I₂ hSplit h
      pHat hTrain hrange hRate z
    simp only [hz, sub_zero] at he
    exact littleOp_threshold_exceedance_tendsto_zero μ _ _ _ he
      (recovery_threshold_dominates_quarter_rate rho hgrowth)

end Papers.TbsPrteOptimalTransport

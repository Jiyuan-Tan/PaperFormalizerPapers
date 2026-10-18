module
public import Papers.TbsPrteOptimalTransport.Helpers.RecoveryComponentIndexing
public import Papers.TbsPrteOptimalTransport.Helpers.LevelRecoveryProbability
/-! Stability of policy-component interval filters under exact graph recovery.
The endpoints here are recovered baseline components. Their numerical averages
may change, while all comparisons and the ordered policy lists remain fixed. -/
public section
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Filter Set
open scoped Classical Topology
universe v
variable {Z : Type v} [Fintype Z] [DecidableEq Z]

-- @node: recoveryComponents_member_average_le_stable
/-- If [two fitted systems have the same active vertices](hyp:hactive), [the first system's active-vertex values are within one quarter of the gap of a common population value](hyp:herror), [the second system satisfies the same error bound](hyp:herror'), and [any two active population values are equal or separated by at least the gap](hyp:hsep), then for [two components in the first system's recovery list](hyp:hC,hD), [the first component's fitted average is at most the second's in one system if and only if it is in the other](goal). -/
lemma recoveryComponents_member_average_le_stable
    (pb qb pb' qb' : Z → ℝ) (rho rho' gap : ℝ)
    (truth : RecoveryVertex Z → ℝ)
    (hactive : recoveryActive pb rho = recoveryActive pb' rho')
    (herror : ∀ v ∈ recoveryActive pb rho,
      |vertexValue pb qb v - truth v| < gap / 4)
    (herror' : ∀ v ∈ recoveryActive pb' rho',
      |vertexValue pb' qb' v - truth v| < gap / 4)
    (hsep : ∀ a ∈ recoveryActive pb rho, ∀ b ∈ recoveryActive pb rho,
      truth a = truth b ∨ gap ≤ |truth a - truth b|)
    {C D : Finset (RecoveryVertex Z)}
    (hC : C ∈ recoveryComponents pb qb rho gap)
    (hD : D ∈ recoveryComponents pb qb rho gap) :
    componentAverage pb qb C ≤ componentAverage pb qb D ↔
      componentAverage pb' qb' C ≤ componentAverage pb' qb' D := by
  have hs' : ∀ a ∈ recoveryActive pb' rho', ∀ b ∈ recoveryActive pb' rho',
      truth a = truth b ∨ gap ≤ |truth a - truth b| := by
    simpa only [← hactive] using hsep
  obtain ⟨a, ha, hCa⟩ :=
    (mem_recoveryComponents_iff_population_class pb qb rho gap truth herror hsep C).mp hC
  obtain ⟨b, hb, hDb⟩ :=
    (mem_recoveryComponents_iff_population_class pb qb rho gap truth herror hsep D).mp hD
  have hCa' : recoveryComponent pb qb rho gap a = C :=
    (recoveryComponent_eq_population_class pb qb rho gap truth herror hsep ha).trans hCa
  have hDb' : recoveryComponent pb qb rho gap b = D :=
    (recoveryComponent_eq_population_class pb qb rho gap truth herror hsep hb).trans hDb
  have hCa'' : recoveryComponent pb' qb' rho' gap a = C := by
    rw [recoveryComponent_eq_population_class pb' qb' rho' gap truth herror' hs'
      (hactive ▸ ha), ← hactive]
    exact hCa
  have hDb'' : recoveryComponent pb' qb' rho' gap b = D := by
    rw [recoveryComponent_eq_population_class pb' qb' rho' gap truth herror' hs'
      (hactive ▸ hb), ← hactive]
    exact hDb
  calc
    _ ↔ truth a ≤ truth b := by
      rw [← hCa', ← hDb']
      exact recoveryComponent_average_le_iff pb qb rho gap truth herror hsep ha hb
    _ ↔ _ := by
      rw [← hCa'', ← hDb'']
      exact (recoveryComponent_average_le_iff pb' qb' rho' gap truth herror' hs'
        (hactive ▸ ha) (hactive ▸ hb)).symm

-- @node: recoveryComponents_member_average_lt_stable
/-- Suppose [the active vertices agree across two fitted systems](hyp:hactive), [the first system approximates common population values within one quarter of the gap on active vertices](hyp:herror), [the second system has the same approximation bound](hyp:herror'), and [active population values are equal or at least the gap apart](hyp:hsep). For [a first component belonging to the first recovery list](hyp:hC) and [a second component belonging to that list](hyp:hD), [strict ordering of their fitted averages holds in the first system if and only if it holds in the second](goal). -/
lemma recoveryComponents_member_average_lt_stable
    (pb qb pb' qb' : Z → ℝ) (rho rho' gap : ℝ)
    (truth : RecoveryVertex Z → ℝ)
    (hactive : recoveryActive pb rho = recoveryActive pb' rho')
    (herror : ∀ v ∈ recoveryActive pb rho,
      |vertexValue pb qb v - truth v| < gap / 4)
    (herror' : ∀ v ∈ recoveryActive pb' rho',
      |vertexValue pb' qb' v - truth v| < gap / 4)
    (hsep : ∀ a ∈ recoveryActive pb rho, ∀ b ∈ recoveryActive pb rho,
      truth a = truth b ∨ gap ≤ |truth a - truth b|)
    {C D : Finset (RecoveryVertex Z)}
    (hC : C ∈ recoveryComponents pb qb rho gap)
    (hD : D ∈ recoveryComponents pb qb rho gap) :
    componentAverage pb qb C < componentAverage pb qb D ↔
      componentAverage pb' qb' C < componentAverage pb' qb' D := by
  simpa only [not_le] using not_congr
    (recoveryComponents_member_average_le_stable pb qb pb' qb' rho rho' gap
      truth hactive herror herror' hsep hD hC)

-- This is the interior-bin Qs filter in recoverLevelsAt. Policy membership
-- is preserved by the component list; the two numerical comparisons are
-- preserved by the population ordering, including coincident components.
-- @node: recoveryComponents_policy_interval_filter_stable
/-- Assume [two fitted systems have identical active vertices](hyp:hactive), [the first system's values approximate common population values within one quarter of the gap](hyp:herror), [the second system obeys that bound as well](hyp:herror'), and [active population values are equal or separated by at least the gap](hyp:hsep). Given [a lower endpoint component](hyp:hB) and [an upper endpoint component](hyp:hD) from the first recovery list, [the ordered list of components containing policy vertices with averages at least the lower endpoint's and strictly below the upper endpoint's is identical across the two systems](goal). -/
lemma recoveryComponents_policy_interval_filter_stable
    (pb qb pb' qb' : Z → ℝ) (rho rho' gap : ℝ)
    (truth : RecoveryVertex Z → ℝ)
    (hactive : recoveryActive pb rho = recoveryActive pb' rho')
    (herror : ∀ v ∈ recoveryActive pb rho,
      |vertexValue pb qb v - truth v| < gap / 4)
    (herror' : ∀ v ∈ recoveryActive pb' rho',
      |vertexValue pb' qb' v - truth v| < gap / 4)
    (hsep : ∀ a ∈ recoveryActive pb rho, ∀ b ∈ recoveryActive pb rho,
      truth a = truth b ∨ gap ≤ |truth a - truth b|)
    {B D : Finset (RecoveryVertex Z)}
    (hB : B ∈ recoveryComponents pb qb rho gap)
    (hD : D ∈ recoveryComponents pb qb rho gap) :
    (recoveryComponents pb qb rho gap).filter (fun C =>
      (∃ z, (true, z) ∈ C) ∧ componentAverage pb qb B ≤ componentAverage pb qb C ∧
        componentAverage pb qb C < componentAverage pb qb D) =
    (recoveryComponents pb' qb' rho' gap).filter (fun C =>
      (∃ z, (true, z) ∈ C) ∧ componentAverage pb' qb' B ≤ componentAverage pb' qb' C ∧
        componentAverage pb' qb' C < componentAverage pb' qb' D) := by
  have hCs := recoveryComponents_eq_of_common_population_classes
    pb qb pb' qb' rho rho' gap truth hactive herror herror' hsep
  rw [← hCs]
  apply List.filter_congr
  intro C hC
  have hlo := recoveryComponents_member_average_le_stable
    pb qb pb' qb' rho rho' gap truth hactive herror herror' hsep hB hC
  have hhi := recoveryComponents_member_average_lt_stable
    pb qb pb' qb' rho rho' gap truth hactive herror herror' hsep hC hD
  simp only [hlo, hhi]

-- @node: recovery_policy_interval_filter_failure_tendsto_zero
/-- Suppose [population baseline marginals are nonnegative](hyp:hp), [the activity threshold tends to zero](hyp:hrho), [the gap is positive](hyp:hgap), [population vertex values are equal or separated by at least the gap](hyp:hsep), [all fitted vertex values converge in probability to their population values](hyp:hconv), and [threshold exceedance at every zero baseline marginal has measure tending to zero](hyp:hzero). For [lower and upper endpoint components in the population recovery list](hyp:hB,hD), [the measure of samples where the ordered policy-component list between their fitted averages, including the lower bound and excluding the upper bound, differs from its population counterpart tends to zero](goal). -/
lemma recovery_policy_interval_filter_failure_tendsto_zero
    {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (pb qb : ℕ → A → Z → ℝ) (p q : Z → ℝ)
    (hp : ∀ z, 0 ≤ p z) (rho : ℕ → ℝ)
    (hrho : Tendsto rho atTop (𝓝 0)) (gap : ℝ) (hgap : 0 < gap)
    (hsep : ∀ v w, vertexValue p q v = vertexValue p q w ∨
      gap ≤ |vertexValue p q v - vertexValue p q w|)
    (hconv : ∀ v, Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => vertexValue (pb n a) (qb n a) v) atTop
      (fun _ _ => vertexValue p q v))
    (hzero : ∀ z, p z = 0 →
      Tendsto (fun n => μ {a | rho n < pb n a z}) atTop (𝓝 0))
    {B D : Finset (RecoveryVertex Z)}
    (hB : B ∈ recoveryComponents p q 0 gap)
    (hD : D ∈ recoveryComponents p q 0 gap) :
    Tendsto (fun n => μ {a |
      (recoveryComponents (pb n a) (qb n a) (rho n) gap).filter (fun C =>
        (∃ z, (true, z) ∈ C) ∧
          componentAverage (pb n a) (qb n a) B ≤ componentAverage (pb n a) (qb n a) C ∧
          componentAverage (pb n a) (qb n a) C < componentAverage (pb n a) (qb n a) D) ≠
      (recoveryComponents p q 0 gap).filter (fun C =>
        (∃ z, (true, z) ∈ C) ∧ componentAverage p q B ≤ componentAverage p q C ∧
          componentAverage p q C < componentAverage p q D)}) atTop (𝓝 0) := by
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
  have hCs := recoveryComponents_eq_of_common_population_classes
    (pb n a) (qb n a) p q (rho n) 0 gap (vertexValue p q)
    hnot.1 hnot.2 hreference hs
  exact hbad (recoveryComponents_policy_interval_filter_stable
    (pb n a) (qb n a) p q (rho n) 0 gap (vertexValue p q)
    hnot.1 hnot.2 hreference hs (hCs.symm ▸ hB) (hCs.symm ▸ hD))

end Papers.TbsPrteOptimalTransport

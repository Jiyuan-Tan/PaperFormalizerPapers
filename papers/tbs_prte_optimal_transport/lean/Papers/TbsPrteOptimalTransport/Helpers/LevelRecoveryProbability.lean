module
public import Papers.TbsPrteOptimalTransport.Helpers.LevelGraphRecovery
public import Papers.TbsPrteOptimalTransport.Helpers.RecoveryComponentIndexing
public import Papers.TbsPrteOptimalTransport.Helpers.DMLOracleTransfer
/-! Simultaneous marginal consistency and high-probability recovery of the
finite level graph. A finite union bound upgrades componentwise convergence;
the deterministic gap lemmas then identify components and their ordering. -/
public section
set_option linter.style.openClassical false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Filter Set
open scoped Classical Topology
universe v

-- @node: finite_bad_events_tendsto_zero
/-- If [each of finitely many bad events has measure tending to zero](hyp:hbad),
[the measure of their union tends to zero](goal). -/
lemma finite_bad_events_tendsto_zero {A ι : Type*} [MeasurableSpace A] [Fintype ι]
    (μ : Measure A) (bad : ℕ → ι → Set A)
    (hbad : ∀ i, Tendsto (fun n => μ (bad n i)) atTop (𝓝 0)) :
    Tendsto (fun n => μ (⋃ i, bad n i)) atTop (𝓝 0) := by
  have hs : Tendsto (fun n => ∑ i, μ (bad n i)) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ (fun i _ => hbad i)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs
    (fun _ => zero_le) (fun n => measure_iUnion_fintype_le μ (bad n))

-- @node: finite_marginal_errors_tendsto_zero
/-- If [each of finitely many marginal estimates converges in probability to its true value](hyp:hconv),
then, for [any positive error tolerance](hyp:heps), [the measure of the event that at least one
absolute estimation error reaches that tolerance tends to zero](goal). -/
lemma finite_marginal_errors_tendsto_zero {A ι : Type*}
    [MeasurableSpace A] [Fintype ι]
    (μ : Measure A) (estimate : ℕ → A → ι → ℝ) (truth : ι → ℝ)
    (hconv : ∀ i, Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => estimate n a i) atTop (fun _ _ => truth i))
    (eps : ℝ) (heps : 0 < eps) :
    Tendsto (fun n => μ {a | ∃ i, eps ≤ |estimate n a i - truth i|})
      atTop (𝓝 0) := by
  have hc (i : ι) : Tendsto
      (fun n => μ {a | eps ≤ ‖estimate n a i - truth i‖}) atTop (𝓝 0) := by
    have hh := hconv i
    rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm] at hh
    exact hh eps heps
  have hu := finite_bad_events_tendsto_zero μ
    (fun n i => {a | eps ≤ |estimate n a i - truth i|})
    (fun i => by simpa only [Real.norm_eq_abs] using hc i)
  simpa only [Set.iUnion_ofPred] using hu

-- A positive marginal mean is eventually above the shrinking threshold;
-- no additional separation of positive levels from zero is needed.
-- @node: positive_marginal_threshold_failure_tendsto_zero
/-- For [a strictly positive marginal value](hyp:hp), if [the threshold tends to zero](hyp:hrho)
and [the estimate converges in probability to that value](hyp:hconv), [the measure of the event
that the estimate is at or below the threshold tends to zero](goal). -/
lemma positive_marginal_threshold_failure_tendsto_zero {A : Type*}
    [MeasurableSpace A] (μ : Measure A) (estimate : ℕ → A → ℝ)
    (p : ℝ) (hp : 0 < p) (rho : ℕ → ℝ)
    (hrho : Tendsto rho atTop (𝓝 0))
    (hconv : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      estimate atTop (fun _ _ => p)) :
    Tendsto (fun n => μ {a | estimate n a ≤ rho n}) atTop (𝓝 0) := by
  rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm] at hconv
  have hc := hconv (p / 2) (by positivity)
  have ht : ∀ᶠ n in atTop, rho n < p / 2 :=
    (tendsto_order.mp hrho).2 (p / 2) (by positivity)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hc
    (Eventually.of_forall (fun _ => zero_le))
  filter_upwards [ht] with n hn
  apply measure_mono
  intro a ha
  change p / 2 ≤ ‖estimate n a - p‖
  rw [Real.norm_eq_abs]
  have he := (neg_le_abs (estimate n a - p))
  change estimate n a ≤ rho n at ha
  linarith

-- @node: recoveryActive_failure_tendsto_zero
/-- If [population baseline marginals are nonnegative](hyp:hp), [the threshold tends to zero](hyp:hrho),
[each marginal estimate is consistent in probability](hyp:hconv), and [threshold exceedances
at every zero marginal have vanishing measure](hyp:hzero), [the measure of failing to recover
exactly all policy vertices and the nonzero baseline vertices tends to zero](goal). -/
lemma recoveryActive_failure_tendsto_zero {A Z : Type*}
    [MeasurableSpace A] [Fintype Z] [DecidableEq Z]
    (μ : Measure A) (pb : ℕ → A → Z → ℝ) (p : Z → ℝ)
    (hp : ∀ z, 0 ≤ p z) (rho : ℕ → ℝ)
    (hrho : Tendsto rho atTop (𝓝 0))
    (hconv : ∀ z, Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => pb n a z) atTop (fun _ _ => p z))
    (hzero : ∀ z, p z = 0 →
      Tendsto (fun n => μ {a | rho n < pb n a z}) atTop (𝓝 0)) :
    Tendsto (fun n => μ {a | recoveryActive (pb n a) (rho n) ≠
      Finset.univ.filter (fun v : RecoveryVertex Z => v.1 = true ∨ p v.2 ≠ 0)})
      atTop (𝓝 0) := by
  let bad := fun n z => if p z = 0 then {a | rho n < pb n a z}
    else {a | pb n a z ≤ rho n}
  have hb : ∀ z, Tendsto (fun n => μ (bad n z)) atTop (𝓝 0) := by
    intro z
    by_cases hz : p z = 0
    · simpa only [bad, if_pos hz] using hzero z hz
    · simpa only [bad, if_neg hz] using
        positive_marginal_threshold_failure_tendsto_zero μ (fun n a => pb n a z)
          (p z) (lt_of_le_of_ne (hp z) (Ne.symm hz)) rho hrho (hconv z)
  have hu := finite_bad_events_tendsto_zero μ bad hb
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
    (fun _ => zero_le)
  intro n
  apply measure_mono
  intro a ha
  by_contra hn
  have hn' : ∀ z, a ∉ bad n z := by simpa only [Set.mem_iUnion, not_exists] using hn
  apply ha
  apply recoveryActive_eq_population_nonzero
  · intro z hz
    have hh := hn' z
    simpa only [bad, if_pos hz, Set.mem_ofPred_eq, not_lt] using hh
  · intro z hz
    have hh := hn' z
    simpa only [bad, if_neg hz, Set.mem_ofPred_eq, not_le] using hh

-- @node: recovery_components_and_order_failure_tendsto_zero
/-- If [the separation gap is positive](hyp:hgap), [any two population vertex values are equal
or separated by at least that gap](hyp:hsep), and [all vertex estimates converge in probability
to their population values](hyp:hconv), [the measure of failing either to recover every active
vertex's population equality class as its graph component or to order component averages
strictly for population values separated by the gap tends to zero](goal). -/
lemma recovery_components_and_order_failure_tendsto_zero
    {A Z : Type*} [MeasurableSpace A] [Fintype Z] [DecidableEq Z]
    (μ : Measure A) (pb qb : ℕ → A → Z → ℝ) (rho : ℕ → ℝ)
    (truth : RecoveryVertex Z → ℝ) (gap : ℝ) (hgap : 0 < gap)
    (hsep : ∀ a b, truth a = truth b ∨ gap ≤ |truth a - truth b|)
    (hconv : ∀ v, Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => vertexValue (pb n a) (qb n a) v)
      atTop (fun _ _ => truth v)) :
    Tendsto (fun n => μ {a | ¬ (
      (∀ v ∈ recoveryActive (pb n a) (rho n),
        recoveryComponent (pb n a) (qb n a) (rho n) gap v =
          (recoveryActive (pb n a) (rho n)).filter (fun w => truth v = truth w)) ∧
      (∀ v ∈ recoveryActive (pb n a) (rho n),
        ∀ w ∈ recoveryActive (pb n a) (rho n), truth v + gap ≤ truth w →
          componentAverage (pb n a) (qb n a)
              (recoveryComponent (pb n a) (qb n a) (rho n) gap v) <
            componentAverage (pb n a) (qb n a)
              (recoveryComponent (pb n a) (qb n a) (rho n) gap w)))})
      atTop (𝓝 0) := by
  have herr := finite_marginal_errors_tendsto_zero μ
    (fun n a v => vertexValue (pb n a) (qb n a) v) truth hconv
    (gap / 4) (by positivity)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds herr
    (fun _ => zero_le)
  intro n
  apply measure_mono
  intro a ha
  by_contra hn
  have he : ∀ v ∈ recoveryActive (pb n a) (rho n),
      |vertexValue (pb n a) (qb n a) v - truth v| < gap / 4 := by
    intro v _
    exact lt_of_not_ge (fun hv => hn ⟨v, hv⟩)
  have hs : ∀ v ∈ recoveryActive (pb n a) (rho n),
      ∀ w ∈ recoveryActive (pb n a) (rho n),
      truth v = truth w ∨ gap ≤ |truth v - truth w| := fun v _ w _ => hsep v w
  apply ha
  constructor
  · intro v hv
    exact recoveryComponent_eq_population_class (pb n a) (qb n a) (rho n)
      gap truth he hs hv
  · intro v hv w hw hvw
    exact recoveryComponent_average_order (pb n a) (qb n a) (rho n)
      gap truth he hs hv hw hvw

-- A single event supplies both the structural-zero removal and the ordered
-- population classes. This is the graph input to the oracle-equivalence step.
-- @node: recovery_population_graph_failure_tendsto_zero
/-- Suppose [baseline population marginals are nonnegative](hyp:hp), [the threshold tends to zero](hyp:hrho),
[the gap is positive](hyp:hgap), [distinct population vertex values are separated by at least
the gap](hyp:hsep), [all vertex estimates are consistent in probability](hyp:hconv), and
[false positive threshold exceedances at zero baseline marginals have vanishing measure](hyp:hzero).
Then [the measure of failing to recover the population active set, its equality-class components,
and the exact strict ordering of population values through component averages tends to zero](goal). -/
lemma recovery_population_graph_failure_tendsto_zero
    {A Z : Type*} [MeasurableSpace A] [Fintype Z] [DecidableEq Z]
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
    let P := Finset.univ.filter (fun v : RecoveryVertex Z => v.1 = true ∨ p v.2 ≠ 0)
    Tendsto (fun n => μ {a | ¬ (
      recoveryActive (pb n a) (rho n) = P ∧
      (∀ v ∈ P, recoveryComponent (pb n a) (qb n a) (rho n) gap v =
        P.filter (fun w => vertexValue p q v = vertexValue p q w)) ∧
      (∀ v ∈ P, ∀ w ∈ P,
        componentAverage (pb n a) (qb n a)
            (recoveryComponent (pb n a) (qb n a) (rho n) gap v) <
          componentAverage (pb n a) (qb n a)
            (recoveryComponent (pb n a) (qb n a) (rho n) gap w) ↔
          vertexValue p q v < vertexValue p q w))}) atTop (𝓝 0) := by
  let P := Finset.univ.filter (fun v : RecoveryVertex Z => v.1 = true ∨ p v.2 ≠ 0)
  have hpconv : ∀ z, Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => pb n a z) atTop (fun _ _ => p z) := by
    intro z
    simpa only [vertexValue, Bool.false_eq_true, if_false] using hconv (false, z)
  have hactive := recoveryActive_failure_tendsto_zero μ pb p hp rho hrho hpconv hzero
  have herrors := finite_marginal_errors_tendsto_zero μ
    (fun n a v => vertexValue (pb n a) (qb n a) v) (vertexValue p q)
    hconv (gap / 4) (by positivity)
  have hsum : Tendsto (fun n =>
      μ {a | recoveryActive (pb n a) (rho n) ≠ P} +
      μ {a | ∃ v, gap / 4 ≤ |vertexValue (pb n a) (qb n a) v - vertexValue p q v|})
      atTop (𝓝 0) := by
    simpa only [add_zero] using hactive.add herrors
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le)
  intro n
  refine (measure_mono ?_).trans (measure_union_le _ _)
  intro a hbad
  by_contra hnot
  have hgood : recoveryActive (pb n a) (rho n) = P ∧
      ¬ ∃ v, gap / 4 ≤ |vertexValue (pb n a) (qb n a) v - vertexValue p q v| := by
    simpa only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] using hnot
  have he : ∀ v ∈ recoveryActive (pb n a) (rho n),
      |vertexValue (pb n a) (qb n a) v - vertexValue p q v| < gap / 4 := by
    intro v _
    exact lt_of_not_ge (fun hv => hgood.2 ⟨v, hv⟩)
  have hs : ∀ v ∈ recoveryActive (pb n a) (rho n),
      ∀ w ∈ recoveryActive (pb n a) (rho n),
      vertexValue p q v = vertexValue p q w ∨
        gap ≤ |vertexValue p q v - vertexValue p q w| := fun v _ w _ => hsep v w
  apply hbad
  refine ⟨hgood.1, ?_, ?_⟩
  · intro v hv
    have hv' : v ∈ recoveryActive (pb n a) (rho n) := hgood.1.symm ▸ hv
    simpa only [hgood.1] using recoveryComponent_eq_population_class
      (pb n a) (qb n a) (rho n) gap (vertexValue p q) he hs hv'
  · intro v hv w hw
    exact recoveryComponent_average_order_iff (pb n a) (qb n a) (rho n) gap
      (vertexValue p q) he hs (hgood.1.symm ▸ hv) (hgood.1.symm ▸ hw)

-- The simultaneous good event is independent of any choice of representative
-- for a component. It supplies the hypotheses of the deterministic indexing
-- lemmas, including the structural-zero class.
-- @node: marginal_recovery_good_event_failure_tendsto_zero
/-- If [baseline population marginals are nonnegative](hyp:hp), [the threshold tends to zero](hyp:hrho),
[the gap is positive](hyp:hgap), [all vertex estimates are consistent in probability](hyp:hconv),
and [threshold exceedances at zero baseline marginals have vanishing measure](hyp:hzero),
[the measure of failing either to recover the population active set at threshold zero or to
keep every active vertex's absolute error below one quarter of the gap tends to zero](goal). -/
lemma marginal_recovery_good_event_failure_tendsto_zero
    {A Z : Type*} [MeasurableSpace A] [Fintype Z] [DecidableEq Z]
    (μ : Measure A) (pb qb : ℕ → A → Z → ℝ) (p q : Z → ℝ)
    (hp : ∀ z, 0 ≤ p z) (rho : ℕ → ℝ)
    (hrho : Tendsto rho atTop (𝓝 0)) (gap : ℝ) (hgap : 0 < gap)
    (hconv : ∀ v, Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => vertexValue (pb n a) (qb n a) v) atTop
      (fun _ _ => vertexValue p q v))
    (hzero : ∀ z, p z = 0 →
      Tendsto (fun n => μ {a | rho n < pb n a z}) atTop (𝓝 0)) :
    Tendsto (fun n => μ {a | ¬ (
      recoveryActive (pb n a) (rho n) = recoveryActive p 0 ∧
      ∀ v ∈ recoveryActive (pb n a) (rho n),
        |vertexValue (pb n a) (qb n a) v - vertexValue p q v| < gap / 4)})
      atTop (𝓝 0) := by
  have hpconv : ∀ z, Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => pb n a z) atTop (fun _ _ => p z) := by
    intro z
    simpa only [vertexValue, Bool.false_eq_true, if_false] using hconv (false, z)
  have hpopulation : recoveryActive p 0 =
      Finset.univ.filter (fun v : RecoveryVertex Z => v.1 = true ∨ p v.2 ≠ 0) :=
    recoveryActive_eq_population_nonzero p p 0
      (fun z hz => hz.le) (fun z hz => lt_of_le_of_ne (hp z) (Ne.symm hz))
  have hactive := recoveryActive_failure_tendsto_zero μ pb p hp rho hrho hpconv hzero
  rw [← hpopulation] at hactive
  have herrors := finite_marginal_errors_tendsto_zero μ
    (fun n a v => vertexValue (pb n a) (qb n a) v) (vertexValue p q)
    hconv (gap / 4) (by positivity)
  have hsum := hactive.add herrors
  simp only [add_zero] at hsum
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le)
  intro n
  refine (measure_mono ?_).trans (measure_union_le _ _)
  intro a hbad
  by_contra hnot
  have hgood : recoveryActive (pb n a) (rho n) = recoveryActive p 0 ∧
      ¬ ∃ v, gap / 4 ≤ |vertexValue (pb n a) (qb n a) v - vertexValue p q v| := by
    simpa only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] using hnot
  apply hbad
  refine ⟨hgood.1, ?_⟩
  intro v _
  exact lt_of_not_ge (fun hv => hgood.2 ⟨v, hv⟩)

-- With true marginal values and threshold zero as the reference, the sorted
-- list and all indexed baseline labels agree on the simultaneous good event.
-- Numerical component averages themselves are allowed to differ.
-- @node: recovery_ordered_baseline_labels_failure_tendsto_zero
/-- Suppose [baseline population marginals are nonnegative](hyp:hp), [the threshold tends to zero](hyp:hrho),
[the gap is positive](hyp:hgap), [distinct population vertex values are separated by the gap](hyp:hsep),
[all vertex estimates are consistent in probability](hyp:hconv), and [threshold exceedances at
zero baseline marginals have vanishing measure](hyp:hzero). Then [the measure of disagreement
with population recovery at threshold zero in the ordered component list, the number of levels,
or any indexed baseline membership set tends to zero](goal). -/
lemma recovery_ordered_baseline_labels_failure_tendsto_zero
    {A : Type*} {Z X : Type v} [MeasurableSpace A] [Fintype Z] [DecidableEq Z]
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
      recoveryComponents (pb n a) (qb n a) (rho n) gap = recoveryComponents p q 0 gap ∧
      (recoverLevelsAt (pb n a) (qb n a) (rho n) gap : LevelData Z X).K =
        (recoverLevelsAt p q 0 gap : LevelData Z X).K ∧
      ∀ k, (recoverLevelsAt (pb n a) (qb n a) (rho n) gap : LevelData Z X).S k =
        (recoverLevelsAt p q 0 gap : LevelData Z X).S k)}) atTop (𝓝 0) := by
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
  apply hbad
  exact ⟨recoveryComponents_eq_of_common_population_classes
    (pb n a) (qb n a) p q (rho n) 0 gap (vertexValue p q)
    hnot.1 hnot.2 hreference hs,
    recoverLevelsAt_baseline_labels_stable (X := X)
      (pb n a) (qb n a) p q (rho n) 0 gap (vertexValue p q)
      hnot.1 hnot.2 hreference hs⟩

end Papers.TbsPrteOptimalTransport

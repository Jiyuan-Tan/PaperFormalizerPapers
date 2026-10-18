module
public import Papers.TbsPrteOptimalTransport.Helpers.RecoveryZeroPolicyBins
/-! Numerical identification of the terminal policy bin.
Bounded fitted probabilities keep component averages below one. Endpoint
ordering then selects exactly the components touching population tail classes,
including components shared with the terminal baseline class. -/
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

omit [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]
  [Fintype Z] [DecidableEq Z] in
-- @node: componentAverage_le_one
/-- If [all fitted baseline values are at most one](hyp:hpb) and [all fitted policy
values are at most one](hyp:hqb), then [the average value over any finite collection
of recovery vertices is at most one, including the empty collection](goal). -/
lemma componentAverage_le_one
    (hpb : ∀ z, pb z ≤ 1) (hqb : ∀ z, qb z ≤ 1)
    (C : Finset (RecoveryVertex Z)) :
    componentAverage pb qb C ≤ 1 := by
  by_cases hc : C.card = 0
  · simp [componentAverage, hc]
  · have hs : ∑ v ∈ C, vertexValue pb qb v ≤ ∑ _v ∈ C, (1 : ℝ) := by
      apply Finset.sum_le_sum
      rintro ⟨b, z⟩ _
      cases b
      · exact hpb z
      · exact hqb z
    have hm := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr (Nat.cast_nonneg C.card))
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_one, inv_mul_cancel₀
      (show (C.card : ℝ) ≠ 0 by exact_mod_cast hc), componentAverage] using hm

omit [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X]
  [Nonempty X] [Fintype Z] [DecidableEq Z] in
-- @node: pBar_le_one
/-- If [every fitted propensity is at most one](hyp:hrange), then [its average over
the evaluation subsample, at any sample size, realization, and instrument value,
is at most one](goal). -/
lemma pBar_le_one
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (S : ObservedSample M μ) (I₂ : SampleSplit A)
    (pHat : ℕ → A → Z → X → ℝ)
    (hrange : ∀ n a z x, pHat n a z x ≤ 1) (n : ℕ) (a : A) (z : Z) :
    pBar M S I₂ pHat n a z ≤ 1 := by
  by_cases hc : (I₂ n a).card = 0
  · simp [pBar, hc]
  · have hs : ∑ i ∈ I₂ n a, pHat n a z (S.Z i a).1 ≤ ∑ _i ∈ I₂ n a, (1 : ℝ) :=
      Finset.sum_le_sum (fun i _ => hrange n a z (S.Z i a).1)
    have hm := mul_le_mul_of_nonneg_left hs
      (inv_nonneg.mpr (Nat.cast_nonneg (I₂ n a).card))
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_one, inv_mul_cancel₀
      (show ((I₂ n a).card : ℝ) ≠ 0 by exact_mod_cast hc), pBar] using hm

include M h q hq L hL hOff hlev hgap hactive hp hqr

-- @node: recoverLevelsAt_tail_policy_numeric_bin_iff
/-- Under threshold crossing, measurability of the policy propensity,
invariant ordering of the population levels, nonterminal policy levels
distinct from their lower baseline endpoints, measurable baseline levels, and a positive
separation gap between distinct propensities, suppose the activity
threshold excludes exactly the zero baseline class and all baseline
and policy marginal estimation errors are less than one quarter of the gap.
If [there is a positive baseline level](hyp:hK), [baseline fitted values
are at most one](hyp:hpb), [policy fitted values are at most one](hyp:hqb),
[the baseline bin index does not exceed the terminal index](hyp:hr), [the policy
class index is valid in that bin](hyp:hj), and [the instrument belongs to that
policy class](hyp:hw), then [its recovery component average lies between the
recovered terminal baseline endpoint at the chosen covariate value and one,
inclusive, exactly when its bin is terminal](goal). -/
lemma recoverLevelsAt_tail_policy_numeric_bin_iff
    (hK : 0 < L.K) (hpb : ∀ z, pb z ≤ 1) (hqb : ∀ z, qb z ≤ 1)
    (r j : ℕ) (hr : r ≤ L.K) (hj : 1 ≤ j ∧ j ≤ L.l r)
    (w : Z) (hw : w ∈ L.T r j) (x : X) :
    ((recoverLevelsAt pb qb rho gap : LevelData Z X).pLev L.K x ≤
      componentAverage pb qb (recoveryComponent pb qb rho gap (true, w)) ∧
      componentAverage pb qb (recoveryComponent pb qb rho gap (true, w)) ≤ 1) ↔
      r = L.K := by
  constructor
  · rintro ⟨hlo, _⟩
    by_contra hn
    have hr' : r < L.K := by omega
    have ht := (recoverLevelsAt_endpoint_interior_policy_order M h q hq L hL hOff hlev
      gap hgap pb qb rho hactive hp hqr L.K r j ⟨hK, le_rfl⟩ hr' hj w hw x).2.mpr hr'
    exact (not_lt_of_ge hlo) ht
  · intro he
    subst r
    exact ⟨recoverLevelsAt_positive_endpoint_le_tail_component M h q hq L hL hOff hlev
      gap hgap pb qb rho hactive hp hqr L.K j ⟨hK, le_rfl⟩ hj w hw x,
      componentAverage_le_one pb qb hpb hqb _⟩

-- @node: recoveryComponents_tail_policy_numeric_filter_eq
/-- Assume threshold crossing, a measurable policy propensity,
invariant population level ordering, nonterminal policy levels distinct
from their lower baseline endpoints,
measurable baseline levels, positive propensity gap separation,
correct exclusion of the zero baseline class by the activity threshold,
and all baseline and policy marginal errors below one quarter of the gap.
With [a positive baseline level](hyp:hK), [baseline fitted values at most
one](hyp:hpb), and [policy fitted values at most one](hyp:hqb), [the ordered list
of components containing a policy vertex whose averages lie between the recovered
terminal baseline endpoint at the chosen covariate value and one, inclusive,
equals the list of components meeting a
population terminal policy class](goal). -/
lemma recoveryComponents_tail_policy_numeric_filter_eq
    (hK : 0 < L.K) (hpb : ∀ z, pb z ≤ 1) (hqb : ∀ z, qb z ≤ 1) (x : X) :
    (recoveryComponents pb qb rho gap).filter (fun C =>
      (∃ z, (true, z) ∈ C) ∧
      (recoverLevelsAt pb qb rho gap : LevelData Z X).pLev L.K x ≤ componentAverage pb qb C ∧
      (if L.K = (recoverLevelsAt pb qb rho gap : LevelData Z X).K then
        componentAverage pb qb C ≤ 1 else componentAverage pb qb C <
          (recoverLevelsAt pb qb rho gap : LevelData Z X).pLev (L.K + 1) x)) =
    (recoveryComponents pb qb rho gap).filter (fun C =>
      ∃ j, (1 ≤ j ∧ j ≤ L.l L.K) ∧ ∃ z ∈ L.T L.K j, (true, z) ∈ C) := by
  have hcount := recoverLevelsAt_baseline_count_eq M h q hq L hL hOff hlev
    gap hgap pb qb rho hactive hp hqr
  apply List.filter_congr
  intro C hC
  simp only [decide_eq_decide, hcount, ite_true]
  constructor
  · rintro ⟨⟨w, hw⟩, hlo, hhi⟩
    obtain ⟨r, hr, j, hj0, hj, hwm, _, _⟩ := finite_policy_level_cover M q L hL x w
    have he := recoveryComponents_eq_component_of_mem pb qb rho gap hC hw
    have hrK := (recoverLevelsAt_tail_policy_numeric_bin_iff M h q hq L hL hOff hlev
      gap hgap pb qb rho hactive hp hqr hK hpb hqb r j hr ⟨hj0, hj⟩ w hwm x).mp
        (by simpa only [he] using And.intro hlo hhi)
    subst r
    exact ⟨j, ⟨hj0, hj⟩, w, hwm, hw⟩
  · rintro ⟨j, hj, w, hwm, hw⟩
    have hm := (recoverLevelsAt_tail_policy_numeric_bin_iff M h q hq L hL hOff hlev
      gap hgap pb qb rho hactive hp hqr hK hpb hqb L.K j le_rfl hj w hwm x).mpr rfl
    have he := recoveryComponents_eq_component_of_mem pb qb rho gap hC hw
    exact ⟨⟨w, hw⟩, by simpa only [he] using hm⟩

-- @node: recoveryComponent_tail_policy_mem_numeric_bin
/-- Under threshold crossing, policy propensity measurability,
invariant level ordering, nonterminal policy levels distinct from their
lower baseline endpoints,
baseline level measurability, positive gap separation,
an activity threshold excluding exactly the zero baseline class, and
all baseline and policy marginal errors below one quarter of the gap, suppose
[a positive baseline level exists](hyp:hK), [baseline fitted values are at most
one](hyp:hpb), and [policy fitted values are at most one](hyp:hqb).
For [a valid terminal policy class index](hyp:hj) and [an instrument in that
class](hyp:hz), [the instrument's policy recovery component belongs to the list
of components containing a policy vertex with average between the recovered
terminal baseline endpoint at the chosen covariate value and one, inclusive](goal). -/
lemma recoveryComponent_tail_policy_mem_numeric_bin
    (hK : 0 < L.K) (hpb : ∀ z, pb z ≤ 1) (hqb : ∀ z, qb z ≤ 1)
    (j : ℕ) (hj : 1 ≤ j ∧ j ≤ L.l L.K) (z : Z) (hz : z ∈ L.T L.K j) (x : X) :
    recoveryComponent pb qb rho gap (true, z) ∈
      (recoveryComponents pb qb rho gap).filter (fun C =>
        (∃ w, (true, w) ∈ C) ∧
        (recoverLevelsAt pb qb rho gap : LevelData Z X).pLev L.K x ≤ componentAverage pb qb C ∧
        (if L.K = (recoverLevelsAt pb qb rho gap : LevelData Z X).K then
          componentAverage pb qb C ≤ 1 else componentAverage pb qb C <
            (recoverLevelsAt pb qb rho gap : LevelData Z X).pLev (L.K + 1) x)) := by
  rw [recoveryComponents_tail_policy_numeric_filter_eq M h q hq L hL hOff hlev
    gap hgap pb qb rho hactive hp hqr hK hpb hqb x]
  apply List.mem_filter.mpr
  refine ⟨recoveryComponent_policy_mem_components gap pb qb rho z, ?_⟩
  simpa only [decide_eq_true_eq] using
    (show ∃ i, (1 ≤ i ∧ i ≤ L.l L.K) ∧ ∃ w ∈ L.T L.K i,
      (true, w) ∈ recoveryComponent pb qb rho gap (true, z) from
      ⟨j, hj, z, hz, recoveryComponent_policy_self_mem gap pb qb rho z⟩)

-- Policy levels after the first tail level are separated even from the
-- terminal baseline. Only the first tail level can share a baseline component.
-- @node: population_terminal_baseline_higher_tail_marginal_gap
/-- Assume threshold crossing, a measurable policy propensity,
invariant level ordering, nonterminal policy levels distinct from their
lower baseline endpoints,
measurable baseline levels, positive propensity gap separation,
an activity threshold excluding exactly the zero baseline class, and
all baseline and policy marginal errors below one quarter of the gap.
If [the terminal
policy class index is valid and exceeds one](hyp:hj), [the baseline instrument
belongs to the terminal baseline class](hyp:hz), and [the policy instrument
belongs to that higher terminal policy class](hyp:hw), then [the policy population
marginal exceeds the baseline population marginal by at least the gap](goal). -/
lemma population_terminal_baseline_higher_tail_marginal_gap
    (j : ℕ) (hj : 1 < j ∧ j ≤ L.l L.K)
    (z w : Z) (hz : z ∈ L.S L.K) (hw : w ∈ L.T L.K j) :
    gap ≤ (∫ x, q w x ∂xLaw M) - ∫ x, M.prop z x ∂xLaw M := by
  obtain ⟨v, hv⟩ := ordered_policy_level_nonempty M q L hL L.K 1 le_rfl
    (by omega) (by omega)
  have hlo := recoveryComponent_tail_vertex_marginal_ge M h q hq L hL hOff hlev
    gap hgap pb qb rho hactive hp hqr 1 ⟨by omega, by omega⟩ v hv (true, v)
    (recoveryComponent_policy_self_mem gap pb qb rho v)
  have hez : M.prop z = L.pLev L.K :=
    funext (fun x => (hL.2.2.2.2.2.1 x L.K z le_rfl).mp hz)
  have hev : q v = L.qLev L.K 1 :=
    funext (fun x => (hL.2.2.2.2.2.2.1 x L.K 1 v le_rfl (by omega) (by omega)).mp hv)
  have hew : q w = L.qLev L.K j :=
    funext (fun x => (hL.2.2.2.2.2.2.1 x L.K j w le_rfl (by omega) hj.2).mp hw)
  have hg := population_policy_marginal_lex_gap M q hq L hL hlev gap hgap
    L.K L.K 1 j le_rfl le_rfl ⟨by omega, by omega⟩ ⟨by omega, hj.2⟩
    (Or.inr ⟨rfl, hj.1⟩)
  simp only [vertexValue, if_true, hev] at hlo
  rw [hez, hew]
  linarith

-- @node: baseline_higher_tail_policy_recovery_no_cross_edge
/-- With threshold crossing, a measurable policy propensity,
invariant population level ordering, nonterminal policy levels distinct
from their lower baseline endpoints,
measurable baseline levels, positive gap separation,
an activity threshold excluding exactly the zero baseline class, and
all baseline and policy marginal errors below one quarter of the gap, take
[a valid positive baseline class index](hyp:hi) and [a valid terminal policy class
index greater than one](hyp:hj). If [the baseline instrument is in the baseline
class](hyp:hz) and [the policy instrument is in the specified terminal class](hyp:hw),
then [their fitted marginal values cannot be less than half the gap apart](goal). -/
lemma baseline_higher_tail_policy_recovery_no_cross_edge
    (i j : ℕ) (hi : 1 ≤ i ∧ i ≤ L.K) (hj : 1 < j ∧ j ≤ L.l L.K)
    (z w : Z) (hz : z ∈ L.S i) (hw : w ∈ L.T L.K j) :
    ¬ |pb z - qb w| < gap / 2 := by
  by_cases hiK : i < L.K
  · exact nonterminal_baseline_policy_recovery_no_cross_edge M h q hq L hL hOff hlev
      gap hgap i ⟨hi.1, hiK⟩ z w hz pb qb (hp z) (hqr w)
  · have hei : i = L.K := by omega
    subst i
    have hg := population_terminal_baseline_higher_tail_marginal_gap M h q hq L hL
      hOff hlev gap hgap pb qb rho hactive hp hqr j hj z w hz hw
    have hs : gap ≤ |(∫ x, M.prop z x ∂xLaw M) - ∫ x, q w x ∂xLaw M| := by
      rw [abs_sub_comm]
      exact hg.trans (le_abs_self _)
    intro hc
    have he := (separated_values_close_iff_equal _ _ _ _ gap
      (hp z) (hqr w) (Or.inr hs)).mp hc
    rw [he, sub_self] at hg
    exact (not_le_of_gt hgap.1) hg

-- @node: recoveryEdge_higher_tail_policy_class_closed
/-- Assume threshold crossing, policy propensity measurability,
invariant level ordering, nonterminal policy levels distinct from their
lower baseline endpoints,
baseline level measurability, positive propensity gap separation,
an activity threshold excluding exactly the zero baseline class, and
all baseline and policy marginal errors below one quarter of the gap.
For [a valid
terminal policy class index greater than one](hyp:hj), if [an instrument belongs
to that class](hyp:hz) and [a recovery edge joins its policy vertex to another
vertex](hyp:he), then [the other vertex is a policy vertex in the same class](goal). -/
lemma recoveryEdge_higher_tail_policy_class_closed
    (j : ℕ) (hj : 1 < j ∧ j ≤ L.l L.K)
    (z : Z) (hz : z ∈ L.T L.K j) (v : RecoveryVertex Z)
    (he : recoveryEdge pb qb rho gap (true, z) v) :
    v.1 = true ∧ v.2 ∈ L.T L.K j := by
  let x : X := Classical.choice inferInstance
  rcases v with ⟨b, w⟩
  cases b
  · have hw : w ∉ L.S 0 := by
      apply (hactive w).mp
      simpa only [recoveryActive, Finset.mem_filter, Finset.mem_univ,
        Bool.false_eq_true, false_or, true_and] using he.2.1
    obtain ⟨i, hi, hwi⟩ := finite_baseline_level_exists M q L hL x w
    have hwm := (hL.2.2.2.2.2.1 x i w hi).mpr hwi
    have hi0 : 1 ≤ i := by
      by_contra hn
      have hi0 : i = 0 := by omega
      exact hw (hi0 ▸ hwm)
    have hn := baseline_higher_tail_policy_recovery_no_cross_edge M h q hq L hL
      hOff hlev gap hgap pb qb rho hactive hp hqr i j ⟨hi0, hi⟩ hj w z hwm hz
    have hc : |qb z - pb w| < gap / 2 := he.2.2.2
    exact False.elim (hn (by simpa only [abs_sub_comm] using hc))
  · have heq := ((policy_recoveryEdge_iff_pointwise_equal M q hq L hL hlev
      gap hgap pb qb rho x z w (hqr z) (hqr w)).mp he).2
    have hzq := (hL.2.2.2.2.2.2.1 x L.K j z le_rfl (by omega) hj.2).mp hz
    exact ⟨rfl, (hL.2.2.2.2.2.2.1 x L.K j w le_rfl (by omega) hj.2).mpr
      (heq.symm.trans hzq)⟩

-- @node: recovery_path_higher_tail_policy_class_closed
/-- Under threshold crossing, a measurable policy propensity,
invariant population level ordering, nonterminal policy levels distinct
from their lower baseline endpoints,
measurable baseline levels, positive gap separation,
an activity threshold excluding exactly the zero baseline class, and
all baseline and policy marginal errors below one quarter of the gap, let [the
terminal policy class index be valid and greater than one](hyp:hj). If [the
starting instrument belongs to this class](hyp:hz) and [a finite recovery path,
possibly of length zero, reaches another vertex from its policy vertex](hyp:he),
then [the reached vertex is a policy vertex in the same class](goal). -/
lemma recovery_path_higher_tail_policy_class_closed
    (j : ℕ) (hj : 1 < j ∧ j ≤ L.l L.K)
    (z : Z) (hz : z ∈ L.T L.K j) (v : RecoveryVertex Z)
    (he : Relation.ReflTransGen (recoveryEdge pb qb rho gap) (true, z) v) :
    v.1 = true ∧ v.2 ∈ L.T L.K j := by
  induction he with
  | refl => exact ⟨rfl, hz⟩
  | @tail a b _ hab ih =>
    have ha : a = (true, a.2) := by
      ext <;> simp only [ih.1]
    rw [ha] at hab
    exact recoveryEdge_higher_tail_policy_class_closed M h q hq L hL hOff hlev
      gap hgap pb qb rho hactive hp hqr j hj a.2 ih.2 b hab

-- @node: recoveryComponent_higher_tail_policy_class_eq
/-- Given threshold crossing, a measurable policy propensity,
invariant level ordering, nonterminal policy levels distinct from their
lower baseline endpoints,
measurable baseline levels, positive gap separation,
an activity threshold excluding exactly the zero baseline class, and
all baseline and policy marginal errors below one quarter of the gap, if [the
terminal policy class index is valid and greater than one](hyp:hj) and [the
instrument belongs to that class](hyp:hz), then [its policy recovery component
consists exactly of the policy vertices of instruments in that class](goal). -/
lemma recoveryComponent_higher_tail_policy_class_eq
    (j : ℕ) (hj : 1 < j ∧ j ≤ L.l L.K)
    (z : Z) (hz : z ∈ L.T L.K j) :
    recoveryComponent pb qb rho gap (true, z) =
      (L.T L.K j).image (fun w => (true, w)) := by
  let x : X := Classical.choice inferInstance
  ext v
  constructor
  · intro hv
    have hc := recovery_path_higher_tail_policy_class_closed M h q hq L hL hOff hlev
      gap hgap pb qb rho hactive hp hqr j hj z hz v (Finset.mem_filter.mp hv).2
    apply Finset.mem_image.mpr
    refine ⟨v.2, hc.2, ?_⟩
    ext <;> simp only [hc.1]
  · intro hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    apply Finset.mem_filter.mpr
    refine ⟨by simp [recoveryActive], ?_⟩
    by_cases he : z = w
    · subst w
      exact Relation.ReflTransGen.refl
    · apply Relation.ReflTransGen.single
      apply (policy_recoveryEdge_iff_pointwise_equal M q hq L hL hlev
        gap hgap pb qb rho x z w (hqr z) (hqr w)).mpr
      exact ⟨he, ((hL.2.2.2.2.2.2.1 x L.K j z le_rfl (by omega) hj.2).mp hz).trans
        ((hL.2.2.2.2.2.2.1 x L.K j w le_rfl (by omega) hj.2).mp hw).symm⟩

-- @node: recoveryComponent_tail_policy_projection_eq
/-- Assume threshold crossing, policy propensity measurability,
invariant population level ordering, nonterminal policy levels distinct
from their lower baseline endpoints,
baseline level measurability, positive propensity gap separation,
an activity threshold excluding exactly the zero baseline class, and
all baseline and policy marginal errors below one quarter of the gap.
For [a valid
terminal policy class index](hyp:hj) and [an instrument in that class](hyp:hz),
[the instruments whose policy vertices lie in its recovery component are exactly
the instruments in that population class](goal). -/
lemma recoveryComponent_tail_policy_projection_eq
    (j : ℕ) (hj : 1 ≤ j ∧ j ≤ L.l L.K) (z : Z) (hz : z ∈ L.T L.K j) :
    Finset.univ.filter (fun w =>
      (true, w) ∈ recoveryComponent pb qb rho gap (true, z)) = L.T L.K j := by
  by_cases hj' : 1 < j
  · rw [recoveryComponent_higher_tail_policy_class_eq M h q hq L hL hOff hlev
      gap hgap pb qb rho hactive hp hqr j ⟨hj', hj.2⟩ z hz]
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Prod.mk.injEq, true_and, exists_eq_right]
  · have hj1 : j = 1 := by omega
    subst j
    let x : X := Classical.choice inferInstance
    have hzq := (hL.2.2.2.2.2.2.1 x L.K 1 z le_rfl hj.1 hj.2).mp hz
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hw
      have hpath := recovery_path_reverse pb qb rho gap (Finset.mem_filter.mp hw).2
      obtain ⟨r, hr, i, hi0, hi, hwm, _, _⟩ := finite_policy_level_cover M q L hL x w
      have hrK : r = L.K := by
        by_contra hn
        have hzc := (recovery_path_interior_policy_class_closed M q hq L hL hOff hlev
          gap hgap pb qb rho hactive hp hqr r i (by omega) ⟨hi0, hi⟩ w hwm
          (true, z) hpath).2
        have hzq' := (hL.2.2.2.2.2.2.1 x r i z hr hi0 hi).mp hzc
        have hs := population_policy_level_lex_strict_order M q L hL x r L.K i 1
          hr le_rfl ⟨hi0, hi⟩ hj (Or.inl (by omega))
        rw [← hzq', ← hzq] at hs
        exact lt_irrefl _ hs
      subst r
      have hi1 : i = 1 := by
        by_contra hn
        have hzc := (recovery_path_higher_tail_policy_class_closed M h q hq L hL
          hOff hlev gap hgap pb qb rho hactive hp hqr i ⟨by omega, hi⟩ w hwm
          (true, z) hpath).2
        have hzq' := (hL.2.2.2.2.2.2.1 x L.K i z le_rfl hi0 hi).mp hzc
        have hs := population_policy_level_lex_strict_order M q L hL x L.K L.K 1 i
          le_rfl le_rfl hj ⟨hi0, hi⟩ (Or.inr ⟨rfl, by omega⟩)
        rw [← hzq, ← hzq'] at hs
        exact lt_irrefl _ hs
      exact hi1 ▸ hwm
    · intro hw
      apply Finset.mem_filter.mpr
      refine ⟨by simp [recoveryActive], ?_⟩
      by_cases he : z = w
      · subst w
        exact Relation.ReflTransGen.refl
      · apply Relation.ReflTransGen.single
        apply (policy_recoveryEdge_iff_pointwise_equal M q hq L hL hlev
          gap hgap pb qb rho x z w (hqr z) (hqr w)).mpr
        exact ⟨he, hzq.trans
          ((hL.2.2.2.2.2.2.1 x L.K 1 w le_rfl hj.1 hj.2).mp hw).symm⟩

end Papers.TbsPrteOptimalTransport

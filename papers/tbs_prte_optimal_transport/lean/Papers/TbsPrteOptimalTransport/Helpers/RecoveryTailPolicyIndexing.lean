module
public import Papers.TbsPrteOptimalTransport.Helpers.RecoveryTailPolicyBins
/-! Exact counts and indexed labels for the terminal policy bin.
Policy projections distinguish all tail classes even when the lowest one
shares the terminal baseline component. Marginal gaps order their components. -/
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

-- @node: recoveryComponent_same_tail_policy_class_eq
/-- Under threshold crossing, a measurable policy propensity,
invariant population level ordering, nonterminal policy levels distinct
from their lower baseline endpoints,
measurable baseline levels, positive propensity gap separation,
an activity threshold excluding exactly the zero baseline class, and
all baseline and policy marginal errors below one quarter of the gap, take [a valid
terminal policy class index](hyp:hj). If [the first instrument belongs to that
class](hyp:hz) and [the second instrument also belongs to that class](hyp:hw),
then [their policy vertices have the same recovery component](goal). -/
lemma recoveryComponent_same_tail_policy_class_eq
    (j : ℕ) (hj : 1 ≤ j ∧ j ≤ L.l L.K)
    (z w : Z) (hz : z ∈ L.T L.K j) (hw : w ∈ L.T L.K j) :
    recoveryComponent pb qb rho gap (true, z) =
      recoveryComponent pb qb rho gap (true, w) := by
  have hpj := recoveryComponent_tail_policy_projection_eq M h q hq L hL hOff hlev
    gap hgap pb qb rho hactive hp hqr j hj w hw
  have hm : (true, z) ∈ recoveryComponent pb qb rho gap (true, w) := by
    have hz' : z ∈ Finset.univ.filter (fun v =>
        (true, v) ∈ recoveryComponent pb qb rho gap (true, w)) := hpj.symm ▸ hz
    exact (Finset.mem_filter.mp hz').2
  exact recoveryComponent_eq_of_mem pb qb rho gap hm

-- @node: recoveryComponent_tail_policy_average_strict_order
/-- Assume threshold crossing, policy propensity measurability,
invariant level ordering, nonterminal policy levels distinct from their
lower baseline endpoints,
baseline level measurability, positive gap separation,
an activity threshold excluding exactly the zero baseline class, and
all baseline and policy marginal errors below one quarter of the gap.
For [a valid
first terminal policy class index](hyp:hi), [a valid second terminal policy class
index](hyp:hj), [an instrument in the first class](hyp:hz), and [an instrument in
the second class](hyp:hw), if [the first index is smaller](hyp:hij), then [the
average of the first policy recovery component is strictly below the average
of the second](goal). -/
lemma recoveryComponent_tail_policy_average_strict_order
    (i j : ℕ) (hi : 1 ≤ i ∧ i ≤ L.l L.K) (hj : 1 ≤ j ∧ j ≤ L.l L.K)
    (z w : Z) (hz : z ∈ L.T L.K i) (hw : w ∈ L.T L.K j) (hij : i < j) :
    componentAverage pb qb (recoveryComponent pb qb rho gap (true, z)) <
      componentAverage pb qb (recoveryComponent pb qb rho gap (true, w)) := by
  have hg := population_policy_marginal_lex_gap M q hq L hL hlev gap hgap
    L.K L.K i j le_rfl le_rfl hi hj (Or.inr ⟨rfl, hij⟩)
  have hez : q z = L.qLev L.K i :=
    funext (fun x => (hL.2.2.2.2.2.2.1 x L.K i z le_rfl hi.1 hi.2).mp hz)
  have hew : q w = L.qLev L.K j :=
    funext (fun x => (hL.2.2.2.2.2.2.1 x L.K j w le_rfl hj.1 hj.2).mp hw)
  have hne : recoveryComponent pb qb rho gap (true, z) ≠
      recoveryComponent pb qb rho gap (true, w) := by
    intro he
    have hpz := recoveryComponent_tail_policy_projection_eq M h q hq L hL hOff hlev
      gap hgap pb qb rho hactive hp hqr i hi z hz
    have hpw := recoveryComponent_tail_policy_projection_eq M h q hq L hL hOff hlev
      gap hgap pb qb rho hactive hp hqr j hj w hw
    rw [he, hpw] at hpz
    have hzj : z ∈ L.T L.K j := hpz.symm ▸ hz
    let x : X := Classical.choice inferInstance
    have hezj := (hL.2.2.2.2.2.2.1 x L.K j z le_rfl hj.1 hj.2).mp hzj
    have hs := population_policy_level_lex_strict_order M q L hL x L.K L.K i j
      le_rfl le_rfl hi hj (Or.inr ⟨rfl, hij⟩)
    rw [← hezj, ← hez] at hs
    exact lt_irrefl _ hs
  apply recoveryComponent_average_lt_of_disconnected_value_le pb qb rho gap hgap.1
    (Finset.mem_filter.mp (recoveryComponent_policy_self_mem gap pb qb rho z)).1
    (Finset.mem_filter.mp (recoveryComponent_policy_self_mem gap pb qb rho w)).1 hne
  change qb z ≤ qb w
  have hpz := (abs_lt.mp (hqr z)).2
  have hpw := (abs_lt.mp (hqr w)).1
  rw [hez] at hpz
  rw [hew] at hpw
  linarith [hgap.1]

-- @node: recoveryComponent_tail_policy_average_order_iff
/-- With threshold crossing, a measurable policy propensity,
invariant population level ordering, nonterminal policy levels distinct
from their lower baseline endpoints,
measurable baseline levels, positive gap separation,
an activity threshold excluding exactly the zero baseline class, and
all baseline and policy marginal errors below one quarter of the gap, consider
[a valid first terminal policy class index](hyp:hi) and [a valid second terminal
policy class index](hyp:hj), with [an instrument from the first class](hyp:hz)
and [an instrument from the second](hyp:hw). Then [the first policy recovery
component has a strictly smaller average exactly when its class index is
smaller](goal). -/
lemma recoveryComponent_tail_policy_average_order_iff
    (i j : ℕ) (hi : 1 ≤ i ∧ i ≤ L.l L.K) (hj : 1 ≤ j ∧ j ≤ L.l L.K)
    (z w : Z) (hz : z ∈ L.T L.K i) (hw : w ∈ L.T L.K j) :
    componentAverage pb qb (recoveryComponent pb qb rho gap (true, z)) <
      componentAverage pb qb (recoveryComponent pb qb rho gap (true, w)) ↔ i < j := by
  constructor
  · intro ht
    by_contra hn
    rcases (le_of_not_gt hn).eq_or_lt with he | he
    · subst j
      rw [recoveryComponent_same_tail_policy_class_eq M h q hq L hL hOff hlev
        gap hgap pb qb rho hactive hp hqr i hi z w hz hw] at ht
      exact lt_irrefl _ ht
    · exact lt_asymm ht (recoveryComponent_tail_policy_average_strict_order M h q hq
        L hL hOff hlev gap hgap pb qb rho hactive hp hqr j i hj hi w z hw hz he)
  · exact recoveryComponent_tail_policy_average_strict_order M h q hq L hL hOff hlev
      gap hgap pb qb rho hactive hp hqr i j hi hj z w hz hw

-- @node: recovery_tail_policy_representative_list_pairwise
/-- Under threshold crossing, a measurable policy propensity,
invariant level ordering, nonterminal policy levels distinct from their
lower baseline endpoints,
measurable baseline levels, positive propensity gap separation,
an activity threshold excluding exactly the zero baseline class, and
all baseline and policy marginal errors below one quarter of the gap, suppose
[the representative rule selects an instrument in each valid terminal policy
class](hyp:hrep). Then [the recovery components of these policy representatives,
listed in class order starting with class one, have strictly increasing
averages](goal). -/
lemma recovery_tail_policy_representative_list_pairwise
    (rep : ℕ → Z)
    (hrep : ∀ j, (1 ≤ j ∧ j ≤ L.l L.K) → rep j ∈ L.T L.K j) :
    ((List.range (L.l L.K)).map (fun j =>
      recoveryComponent pb qb rho gap (true, rep (j + 1)))).Pairwise
      (fun C D => componentAverage pb qb C < componentAverage pb qb D) := by
  rw [List.pairwise_map]
  apply List.Pairwise.imp_of_mem _ List.pairwise_lt_range
  intro i j hi hj hij
  have hi' : 1 ≤ i + 1 ∧ i + 1 ≤ L.l L.K := by
    have := List.mem_range.mp hi
    omega
  have hj' : 1 ≤ j + 1 ∧ j + 1 ≤ L.l L.K := by
    have := List.mem_range.mp hj
    omega
  exact recoveryComponent_tail_policy_average_strict_order M h q hq L hL hOff
    hlev gap hgap pb qb rho hactive hp hqr (i + 1) (j + 1) hi' hj'
    _ _ (hrep _ hi') (hrep _ hj') (by omega)

-- @node: recovery_tail_policy_representative_list_nodup
/-- Assume threshold crossing, policy propensity measurability,
invariant population level ordering, nonterminal policy levels distinct
from their lower baseline endpoints,
baseline level measurability, positive gap separation,
an activity threshold excluding exactly the zero baseline class, and
all baseline and policy marginal errors below one quarter of the gap.
If [the
representative rule chooses an instrument in each valid terminal policy class](hyp:hrep),
then [the list of their policy recovery components in class order contains no
duplicates](goal). -/
lemma recovery_tail_policy_representative_list_nodup
    (rep : ℕ → Z)
    (hrep : ∀ j, (1 ≤ j ∧ j ≤ L.l L.K) → rep j ∈ L.T L.K j) :
    ((List.range (L.l L.K)).map (fun j =>
      recoveryComponent pb qb rho gap (true, rep (j + 1)))).Nodup := by
  exact (recovery_tail_policy_representative_list_pairwise M h q hq L hL hOff
    hlev gap hgap pb qb rho hactive hp hqr rep hrep).nodup

-- The population tail selection has the same order as its numerical bin.
-- @node: recoveryComponents_tail_policy_class_list_eq
/-- Given threshold crossing, a measurable policy propensity,
invariant level ordering, nonterminal policy levels distinct from their
lower baseline endpoints,
measurable baseline levels, positive propensity gap separation,
an activity threshold excluding exactly the zero baseline class, and
all baseline and policy marginal errors below one quarter of the gap, suppose
[the representative rule chooses an instrument from each valid terminal policy
class](hyp:hrep). Then [filtering the ordered recovery component list for
components meeting a terminal policy class gives exactly the list of the
representatives' policy components in increasing class order](goal). -/
lemma recoveryComponents_tail_policy_class_list_eq
    (rep : ℕ → Z)
    (hrep : ∀ j, (1 ≤ j ∧ j ≤ L.l L.K) → rep j ∈ L.T L.K j) :
    (recoveryComponents pb qb rho gap).filter (fun C =>
      ∃ j, (1 ≤ j ∧ j ≤ L.l L.K) ∧ ∃ z ∈ L.T L.K j, (true, z) ∈ C) =
    (List.range (L.l L.K)).map (fun j =>
      recoveryComponent pb qb rho gap (true, rep (j + 1))) := by
  let Qs := (recoveryComponents pb qb rho gap).filter (fun C =>
    ∃ j, (1 ≤ j ∧ j ≤ L.l L.K) ∧ ∃ z ∈ L.T L.K j, (true, z) ∈ C)
  let f := fun j => recoveryComponent pb qb rho gap (true, rep (j + 1))
  have hfmem (i : ℕ) (hi : i < L.l L.K) : f i ∈ Qs := by
    have hi' : 1 ≤ i + 1 ∧ i + 1 ≤ L.l L.K := by omega
    apply List.mem_filter.mpr
    refine ⟨recoveryComponent_policy_mem_components gap pb qb rho _, ?_⟩
    simpa only [decide_eq_true_eq] using
      (show ∃ j, (1 ≤ j ∧ j ≤ L.l L.K) ∧ ∃ z ∈ L.T L.K j, (true, z) ∈ f i from
        ⟨i + 1, hi', rep (i + 1), hrep _ hi',
          recoveryComponent_policy_self_mem gap pb qb rho _⟩)
  have hcover (C : Finset (RecoveryVertex Z)) (hC : C ∈ Qs) :
      ∃ i < L.l L.K, f i = C := by
    have hC' : C ∈ recoveryComponents pb qb rho gap ∧
        ∃ j, (1 ≤ j ∧ j ≤ L.l L.K) ∧ ∃ z ∈ L.T L.K j, (true, z) ∈ C := by
      simpa only [Qs, List.mem_filter, decide_eq_true_eq] using hC
    obtain ⟨j, hj, z, hz, hzc⟩ := hC'.2
    have he := recoveryComponents_eq_component_of_mem pb qb rho gap hC'.1 hzc
    have hc := recoveryComponent_same_tail_policy_class_eq M h q hq L hL
      hOff hlev gap hgap pb qb rho hactive hp hqr j hj (rep j) z (hrep j hj) hz
    refine ⟨j - 1, by omega, ?_⟩
    simpa only [f, Nat.sub_add_cancel hj.1] using hc.trans he
  have hstrict := recovery_tail_policy_representative_list_pairwise
    M h q hq L hL hOff hlev gap hgap pb qb rho hactive hp hqr rep hrep
  have hn : Qs.Nodup := by
    apply List.Nodup.filter
    unfold recoveryComponents
    exact (List.mergeSort_perm _ _).nodup_iff.mpr (Finset.nodup_toList _)
  have hperm : Qs.Perm ((List.range (L.l L.K)).map f) := by
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
    have hi' : 1 ≤ i + 1 ∧ i + 1 ≤ L.l L.K := by omega
    have hj' : 1 ≤ j + 1 ∧ j + 1 ≤ L.l L.K := by
      have := List.mem_range.mp hj
      omega
    have ho := recoveryComponent_tail_policy_average_order_iff M h q hq L hL
      hOff hlev gap hgap pb qb rho hactive hp hqr (i + 1) (j + 1)
      hi' hj' _ _ (hrep _ hi') (hrep _ hj')
    have hor := recoveryComponent_tail_policy_average_order_iff M h q hq L hL
      hOff hlev gap hgap pb qb rho hactive hp hqr (j + 1) (i + 1)
      hj' hi' _ _ (hrep _ hj') (hrep _ hi')
    have hij : ¬ i + 1 < j + 1 := fun ht =>
      (not_lt_of_ge hDC) (ho.mpr ht)
    have hji : ¬ j + 1 < i + 1 := fun ht =>
      (not_lt_of_ge hCD) (hor.mpr ht)
    exact congrArg f (show i = j by omega)
  · exact hstrict.imp (fun hh => hh.le)

-- @node: recoveryComponents_tail_policy_indexed_projection_eq
/-- Under threshold crossing, policy propensity measurability,
invariant population level ordering, nonterminal policy levels distinct
from their lower baseline endpoints,
baseline level measurability, positive gap separation,
an activity threshold excluding exactly the zero baseline class, and
all baseline and policy marginal errors below one quarter of the gap, let [the
terminal policy class index be valid](hyp:hj). Then [the instruments whose policy
vertices occur in the component at that one-based position in the ordered list
of components meeting terminal policy classes are exactly the instruments in
the corresponding population class](goal). -/
lemma recoveryComponents_tail_policy_indexed_projection_eq
    (j : ℕ) (hj : 1 ≤ j ∧ j ≤ L.l L.K) :
    Finset.univ.filter (fun z => (true, z) ∈
      ((recoveryComponents pb qb rho gap).filter (fun C =>
        ∃ i, (1 ≤ i ∧ i ≤ L.l L.K) ∧ ∃ w ∈ L.T L.K i, (true, w) ∈ C)).getD
          (j - 1) ∅) = L.T L.K j := by
  let rep : ℕ → Z := fun i => if hi : 1 ≤ i ∧ i ≤ L.l L.K then
    Classical.choose (ordered_policy_level_nonempty M q L hL L.K i le_rfl hi.1 hi.2)
    else Classical.choice inferInstance
  have hrep : ∀ i, (1 ≤ i ∧ i ≤ L.l L.K) → rep i ∈ L.T L.K i := by
    intro i hi
    simpa only [rep, dif_pos hi] using
      Classical.choose_spec (ordered_policy_level_nonempty M q L hL L.K i le_rfl hi.1 hi.2)
  rw [recoveryComponents_tail_policy_class_list_eq M h q hq L hL hOff hlev
    gap hgap pb qb rho hactive hp hqr rep hrep]
  have hget : ((List.range (L.l L.K)).map (fun i =>
      recoveryComponent pb qb rho gap (true, rep (i + 1)))).getD (j - 1) ∅ =
      recoveryComponent pb qb rho gap (true, rep j) := by
    simp [List.getD, List.getElem?_map,
      List.getElem?_range (show j - 1 < L.l L.K by omega), Nat.sub_add_cancel hj.1]
  rw [hget]
  exact recoveryComponent_tail_policy_projection_eq M h q hq L hL hOff hlev
    gap hgap pb qb rho hactive hp hqr j hj _ (hrep j hj)

-- @node: recoveryComponents_tail_policy_numeric_list_eq
/-- Assume threshold crossing, a measurable policy propensity,
invariant level ordering, nonterminal policy levels distinct from their
lower baseline endpoints,
measurable baseline levels, positive gap separation,
an activity threshold excluding exactly the zero baseline class, and
all baseline and policy marginal errors below one quarter of the gap.
If [a positive
baseline level exists](hyp:hK), [baseline fitted values are at most one](hyp:hpb),
[policy fitted values are at most one](hyp:hqb), and [the representative rule
selects an instrument in each valid terminal policy class](hyp:hrep), then
[the ordered components containing a policy vertex whose averages lie between
the recovered terminal baseline endpoint at the chosen covariate value and one,
inclusive, are exactly the representatives'
policy components in increasing class order](goal). -/
lemma recoveryComponents_tail_policy_numeric_list_eq
    (hK : 0 < L.K) (hpb : ∀ z, pb z ≤ 1) (hqb : ∀ z, qb z ≤ 1)
    (x : X) (rep : ℕ → Z)
    (hrep : ∀ j, (1 ≤ j ∧ j ≤ L.l L.K) → rep j ∈ L.T L.K j) :
    (recoveryComponents pb qb rho gap).filter (fun C =>
      (∃ z, (true, z) ∈ C) ∧
      (recoverLevelsAt pb qb rho gap : LevelData Z X).pLev L.K x ≤ componentAverage pb qb C ∧
      (if L.K = (recoverLevelsAt pb qb rho gap : LevelData Z X).K then
        componentAverage pb qb C ≤ 1 else componentAverage pb qb C <
          (recoverLevelsAt pb qb rho gap : LevelData Z X).pLev (L.K + 1) x)) =
    (List.range (L.l L.K)).map (fun j => recoveryComponent pb qb rho gap (true, rep (j + 1))) := by
  rw [recoveryComponents_tail_policy_numeric_filter_eq M h q hq L hL hOff hlev
    gap hgap pb qb rho hactive hp hqr hK hpb hqb x]
  exact recoveryComponents_tail_policy_class_list_eq M h q hq L hL hOff hlev
    gap hgap pb qb rho hactive hp hqr rep hrep

-- @node: recoverLevelsAt_tail_policy_count_eq
/-- With threshold crossing, a measurable policy propensity,
invariant population level ordering, nonterminal policy levels distinct
from their lower baseline endpoints,
measurable baseline levels, positive propensity gap separation,
an activity threshold excluding exactly the zero baseline class, and
all baseline and policy marginal errors below one quarter of the gap, if [there is
a positive baseline level](hyp:hK), [baseline fitted values are at most one](hyp:hpb),
and [policy fitted values are at most one](hyp:hqb), then [the recovered number
of policy classes in the population terminal bin equals its population count](goal). -/
lemma recoverLevelsAt_tail_policy_count_eq
    (hK : 0 < L.K) (hpb : ∀ z, pb z ≤ 1) (hqb : ∀ z, qb z ≤ 1) :
    (recoverLevelsAt pb qb rho gap : LevelData Z X).l L.K = L.l L.K := by
  let rep : ℕ → Z := fun j => if hj : 1 ≤ j ∧ j ≤ L.l L.K then
    Classical.choose (ordered_policy_level_nonempty M q L hL L.K j le_rfl hj.1 hj.2)
    else Classical.choice inferInstance
  have hrep : ∀ j, (1 ≤ j ∧ j ≤ L.l L.K) → rep j ∈ L.T L.K j := by
    intro j hj
    simpa only [rep, dif_pos hj] using
      Classical.choose_spec (ordered_policy_level_nonempty M q L hL L.K j le_rfl hj.1 hj.2)
  have he := congrArg List.length (recoveryComponents_tail_policy_numeric_list_eq
    M h q hq L hL hOff hlev gap hgap pb qb rho hactive hp hqr hK hpb hqb
    (Classical.choice inferInstance) rep hrep)
  simpa only [recoverLevelsAt, List.length_map, List.length_range] using he

-- @node: recoverLevelsAt_tail_policy_label_eq
/-- Assume threshold crossing, policy propensity measurability,
invariant level ordering, nonterminal policy levels distinct from their
lower baseline endpoints,
baseline level measurability, positive gap separation,
an activity threshold excluding exactly the zero baseline class, and
all baseline and policy marginal errors below one quarter of the gap.
With [a
positive baseline level](hyp:hK), [baseline fitted values at most one](hyp:hpb),
[policy fitted values at most one](hyp:hqb), and [a valid terminal policy class
index](hyp:hj), [the recovered instrument set for that class equals its population
instrument set](goal). -/
lemma recoverLevelsAt_tail_policy_label_eq
    (hK : 0 < L.K) (hpb : ∀ z, pb z ≤ 1) (hqb : ∀ z, qb z ≤ 1)
    (j : ℕ) (hj : 1 ≤ j ∧ j ≤ L.l L.K) :
    (recoverLevelsAt pb qb rho gap : LevelData Z X).T L.K j = L.T L.K j := by
  have hl := recoverLevelsAt_tail_policy_count_eq M h q hq L hL hOff hlev
    gap hgap pb qb rho hactive hp hqr hK hpb hqb
  have hf := recoveryComponents_tail_policy_numeric_filter_eq M h q hq L hL hOff hlev
    gap hgap pb qb rho hactive hp hqr hK hpb hqb (Classical.choice inferInstance)
  have hvalid : ¬ (j = 0 ∨
      (recoverLevelsAt pb qb rho gap : LevelData Z X).l L.K < j) := by omega
  let Qs := (recoveryComponents pb qb rho gap).filter (fun C =>
    (∃ z, (true, z) ∈ C) ∧
    (recoverLevelsAt pb qb rho gap : LevelData Z X).pLev L.K
      (Classical.choice inferInstance) ≤ componentAverage pb qb C ∧
    (if L.K = (recoverLevelsAt pb qb rho gap : LevelData Z X).K then
      componentAverage pb qb C ≤ 1 else componentAverage pb qb C <
        (recoverLevelsAt pb qb rho gap : LevelData Z X).pLev (L.K + 1)
          (Classical.choice inferInstance)))
  change ¬ (j = 0 ∨ Qs.length < j) at hvalid
  change Qs = _ at hf
  change (if j = 0 ∨ Qs.length < j then ∅ else
    Finset.univ.filter (fun z => (true, z) ∈ Qs.getD (j - 1) ∅)) = _
  rw [if_neg hvalid, hf]
  exact recoveryComponents_tail_policy_indexed_projection_eq M h q hq L hL hOff hlev
    gap hgap pb qb rho hactive hp hqr j hj

omit hactive hp hqr in
-- @node: recovery_tail_policy_labels_failure_tendsto_zero
/-- Under threshold crossing, a measurable policy propensity,
invariant population level ordering, nonterminal policy levels distinct
from their lower baseline endpoints,
measurable baseline levels, and positive propensity gap separation,
suppose [the activity thresholds converge to zero](hyp:hrho), [a positive baseline
level exists](hyp:hK), [all baseline estimates are at most one](hyp:hpb), and [all
policy estimates are at most one](hyp:hqb). If [baseline marginal estimates
converge in probability to their population marginals for every instrument](hyp:hpconv),
[policy marginal estimates do likewise](hyp:hqconv), and [the measure of threshold
exceedance tends to zero for every instrument with zero baseline marginal](hyp:hzero),
then [the measure of failure to recover both the terminal policy class count
and every valid terminal policy class instrument set tends to zero](goal). -/
lemma recovery_tail_policy_labels_failure_tendsto_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (pb qb : ℕ → A → Z → ℝ) (rho : ℕ → ℝ)
    (hrho : Tendsto rho atTop (𝓝 0))
    (hK : 0 < L.K)
    (hpb : ∀ n a z, pb n a z ≤ 1) (hqb : ∀ n a z, qb n a z ≤ 1)
    (hpconv : ∀ z, Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => pb n a z) atTop (fun _ _ => ∫ x, M.prop z x ∂xLaw M))
    (hqconv : ∀ z, Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => qb n a z) atTop (fun _ _ => ∫ x, q z x ∂xLaw M))
    (hzero : ∀ z, (∫ x, M.prop z x ∂xLaw M) = 0 →
      Tendsto (fun n => μ {a | rho n < pb n a z}) atTop (𝓝 0)) :
    Tendsto (fun n => μ {a | ¬ (
      (recoverLevelsAt (pb n a) (qb n a) (rho n) gap : LevelData Z X).l L.K = L.l L.K ∧
      ∀ j, (1 ≤ j ∧ j ≤ L.l L.K) →
        (recoverLevelsAt (pb n a) (qb n a) (rho n) gap : LevelData Z X).T L.K j = L.T L.K j)})
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
  constructor
  · exact recoverLevelsAt_tail_policy_count_eq M h q hq L hL hOff hlev
      gap hgap (pb n a) (qb n a) (rho n) ha
      (fun z => he (false, z)) (fun z => he (true, z)) hK (hpb n a) (hqb n a)
  · intro j hj
    exact recoverLevelsAt_tail_policy_label_eq M h q hq L hL hOff hlev
      gap hgap (pb n a) (qb n a) (rho n) ha
      (fun z => he (false, z)) (fun z => he (true, z)) hK (hpb n a) (hqb n a) j hj

omit q hq hL hgap hactive hp hqr in
-- @node: firstStageRate_tail_policy_labels_failure_tendsto_zero
/-- Assume threshold crossing, nonterminal policy levels distinct from
their lower baseline endpoints,
measurable baseline levels, [an equal half split of the observed
sample](hyp:hSplit), [a predictor measurable with respect to its training
sample](hyp:hTrain), [fitted propensities between zero and one](hyp:hrange), and
[maximum finite population L2 error across instruments vanishing in probability
faster than sample size to the negative one-quarter power along even sample
sizes](hyp:hRate). For [a policy map preserving the unit interval](hyp:hphi)
that [is differentiable with the specified derivative](hyp:hd), with [a bounded
Lipschitz derivative](hyp:hDerivative), suppose [baseline and transformed policy
propensities have the specified invariant level ordering](hyp:hLphi) and [positive
gap separation](hyp:hgapPhi), and [a positive baseline level exists](hyp:hK).
If [the activity threshold tends to zero](hyp:hrho) and [its product with the
fourth root of sample size tends to infinity](hyp:hgrowth), then [along even
sample sizes starting at two, the probability of failing to recover the terminal
policy class count and all its valid class instrument sets tends to zero](goal). -/
lemma firstStageRate_tail_policy_labels_failure_tendsto_zero
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
    (hK : 0 < L.K)
    (rho : ℕ → ℝ) (hrho : Tendsto rho atTop (𝓝 0))
    (hgrowth : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 4 : ℝ) * rho n) atTop atTop) :
    Tendsto (fun n => μ {a | ¬ (
      (recoveredData M S I₁ I₂ pHat phi rho gap (2 * (n + 1)) a).l L.K = L.l L.K ∧
      ∀ j, (1 ≤ j ∧ j ≤ L.l L.K) →
        (recoveredData M S I₁ I₂ pHat phi rho gap (2 * (n + 1)) a).T L.K j = L.T L.K j)})
      atTop (𝓝 0) := by
  have hindex : Tendsto (fun n : ℕ => 2 * (n + 1)) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    exact eventually_atTop.2 ⟨b, fun n hn => by omega⟩
  have hqphi : Measurable (Function.uncurry (policyProp phi M.prop)) := by fun_prop
  have hconv := firstStageRate_pBar_marginals_consistent M μ S I₁ I₂ hSplit h
    pHat hTrain hrange hRate phi dphi hphi hd hDerivative
  apply recovery_tail_policy_labels_failure_tendsto_zero M h
    (policyProp phi M.prop) hqphi L hLphi hOff hlev gap hgapPhi μ
    (fun n a => pBar M S I₂ pHat (2 * (n + 1)) a)
    (fun n a => pBar M S I₂ (fun n a => policyProp phi (pHat n a)) (2 * (n + 1)) a)
    (fun n => rho (2 * (n + 1))) (hrho.comp hindex) hK
    (fun n a z => pBar_le_one M μ S I₂ pHat
      (fun n a z x => (hrange n a z x).2) _ a z)
    (fun n a z => pBar_le_one M μ S I₂
      (fun n a => policyProp phi (pHat n a))
      (fun n a z x => (hphi.2 z x _ (hrange n a z x)).2) _ a z)
    hconv.1 hconv.2
  intro z hz
  have he := firstStageRate_pBar_baseline_quarter_rate M μ S I₁ I₂ hSplit h
    pHat hTrain hrange hRate z
  simp only [hz, sub_zero] at he
  exact littleOp_threshold_exceedance_tendsto_zero μ _ _ _ he
    (recovery_threshold_dominates_quarter_rate rho hgrowth)

end Papers.TbsPrteOptimalTransport

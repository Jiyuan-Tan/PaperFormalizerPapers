module
public import Papers.TbsPrteOptimalTransport.Helpers.RecoveryBaselineOrder
/-! Order of components of the real-valued threshold graph.
Paths cannot cross a vertex in a different component. Thus weak ordering of
population marginal values persists in component averages under small errors,
even when the terminal baseline and a policy level share a component. -/
public section
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open scoped Classical
variable {Z : Type*} [Fintype Z] [DecidableEq Z]

-- @node: recoveryComponent_external_value_gap
/-- If [a vertex b is active](hyp:hb), [b lies outside the component of a](hyp:houtside),
and [u belongs to that component](hyp:hu), then [the fitted values at u and b differ
by at least half the graph's gap threshold](goal). -/
lemma recoveryComponent_external_value_gap
    (pb qb : Z → ℝ) (rho gap : ℝ) {a b u : RecoveryVertex Z}
    (hb : b ∈ recoveryActive pb rho)
    (houtside : b ∉ recoveryComponent pb qb rho gap a)
    (hu : u ∈ recoveryComponent pb qb rho gap a) :
    gap / 2 ≤ |vertexValue pb qb u - vertexValue pb qb b| := by
  apply le_of_not_gt
  intro hclose
  have hne : u ≠ b := fun he => houtside (he ▸ hu)
  have hedge : recoveryEdge pb qb rho gap u b :=
    ⟨(Finset.mem_filter.mp hu).1, hb, hne, hclose⟩
  exact houtside (Finset.mem_filter.mpr
    ⟨hb, (Finset.mem_filter.mp hu).2.tail hedge⟩)

-- @node: recoveryComponent_values_lt_external
/-- If [the gap is positive](hyp:hgap), [a is active](hyp:ha), [b is active](hyp:hb),
[b lies outside a's component](hyp:houtside), and [a's fitted value is no larger
than b's](hyp:hab), then [every fitted value in a's component is strictly below
b's fitted value](goal). -/
lemma recoveryComponent_values_lt_external
    (pb qb : Z → ℝ) (rho gap : ℝ) (hgap : 0 < gap)
    {a b : RecoveryVertex Z} (ha : a ∈ recoveryActive pb rho)
    (hb : b ∈ recoveryActive pb rho)
    (houtside : b ∉ recoveryComponent pb qb rho gap a)
    (hab : vertexValue pb qb a ≤ vertexValue pb qb b) :
    ∀ u ∈ recoveryComponent pb qb rho gap a,
      vertexValue pb qb u < vertexValue pb qb b := by
  have hself : a ∈ recoveryComponent pb qb rho gap a :=
    Finset.mem_filter.mpr ⟨ha, Relation.ReflTransGen.refl⟩
  have hbase := recoveryComponent_external_value_gap pb qb rho gap hb houtside hself
  rw [abs_of_nonpos (sub_nonpos.mpr hab)] at hbase
  intro u hu
  have hpath := (Finset.mem_filter.mp hu).2
  induction hpath with
  | refl => linarith
  | @tail v w hav hvw ih =>
    have hv : v ∈ recoveryComponent pb qb rho gap a :=
      Finset.mem_filter.mpr ⟨hvw.1, hav⟩
    have hsep := recoveryComponent_external_value_gap pb qb rho gap hb houtside hv
    rw [abs_of_neg (sub_neg.mpr (ih hv))] at hsep
    have hstep := (abs_lt.mp hvw.2.2.2).1
    linarith

-- @node: recoveryComponent_cross_value_strict_order
/-- If [the gap is positive](hyp:hgap), [a is active](hyp:ha), [b is active](hyp:hb),
[their components are distinct](hyp:hne), and [a's fitted value is no larger than
b's](hyp:hab), then [every fitted value in a's component is strictly below every
fitted value in b's component](goal). -/
lemma recoveryComponent_cross_value_strict_order
    (pb qb : Z → ℝ) (rho gap : ℝ) (hgap : 0 < gap)
    {a b : RecoveryVertex Z} (ha : a ∈ recoveryActive pb rho)
    (hb : b ∈ recoveryActive pb rho)
    (hne : recoveryComponent pb qb rho gap a ≠ recoveryComponent pb qb rho gap b)
    (hab : vertexValue pb qb a ≤ vertexValue pb qb b) :
    ∀ u ∈ recoveryComponent pb qb rho gap a,
      ∀ v ∈ recoveryComponent pb qb rho gap b,
        vertexValue pb qb u < vertexValue pb qb v := by
  have hout : b ∉ recoveryComponent pb qb rho gap a := by
    intro hm
    exact hne (recoveryComponent_eq_of_mem pb qb rho gap hm).symm
  intro u hu v hv
  have hub := recoveryComponent_values_lt_external pb qb rho gap hgap ha hb hout hab u hu
  by_contra hn
  have hout' : u ∉ recoveryComponent pb qb rho gap v := by
    intro hm
    have he := recoveryComponent_eq_of_mem pb qb rho gap hm
    have he' := recoveryComponent_eq_of_mem pb qb rho gap hv
    have heu := recoveryComponent_eq_of_mem pb qb rho gap hu
    exact hne (heu.symm.trans (he.trans he'))
  have hbu : vertexValue pb qb b < vertexValue pb qb u := by
    apply recoveryComponent_values_lt_external pb qb rho gap hgap
      (Finset.mem_filter.mp hv).1 (Finset.mem_filter.mp hu).1 hout' (le_of_not_gt hn)
    rw [recoveryComponent_eq_of_mem pb qb rho gap hv]
    exact Finset.mem_filter.mpr ⟨hb, Relation.ReflTransGen.refl⟩
  exact lt_asymm hub hbu

-- @node: componentAverage_lt_of_pointwise_lt
/-- If [a finite set of vertices is nonempty](hyp:hC) and [each of its fitted
values is strictly below t](hyp:hlt), then [its average fitted value is strictly
below t](goal). -/
lemma componentAverage_lt_of_pointwise_lt
    (pb qb : Z → ℝ) (C : Finset (RecoveryVertex Z)) (hC : C.Nonempty)
    (t : ℝ) (hlt : ∀ v ∈ C, vertexValue pb qb v < t) :
    componentAverage pb qb C < t := by
  have hc : (0 : ℝ) < C.card := by exact_mod_cast hC.card_pos
  obtain ⟨v, hv⟩ := hC
  have hs := Finset.sum_lt_sum (fun w hw => (hlt w hw).le) ⟨v, hv, hlt v hv⟩
  have hm := mul_lt_mul_of_pos_left hs (inv_pos.mpr hc)
  simpa only [Finset.sum_const, nsmul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ hc.ne', one_mul, componentAverage] using hm

-- @node: recoveryComponent_average_lt_of_disconnected_value_le
/-- If [the gap is positive](hyp:hgap), [a is active](hyp:ha), [b is active](hyp:hb),
[their components differ](hyp:hne), and [a's fitted value is no larger than
b's](hyp:hab), then [the average fitted value of a's component is strictly below
that of b's component](goal). -/
lemma recoveryComponent_average_lt_of_disconnected_value_le
    (pb qb : Z → ℝ) (rho gap : ℝ) (hgap : 0 < gap)
    {a b : RecoveryVertex Z} (ha : a ∈ recoveryActive pb rho)
    (hb : b ∈ recoveryActive pb rho)
    (hne : recoveryComponent pb qb rho gap a ≠ recoveryComponent pb qb rho gap b)
    (hab : vertexValue pb qb a ≤ vertexValue pb qb b) :
    componentAverage pb qb (recoveryComponent pb qb rho gap a) <
      componentAverage pb qb (recoveryComponent pb qb rho gap b) := by
  have hselfa : a ∈ recoveryComponent pb qb rho gap a :=
    Finset.mem_filter.mpr ⟨ha, Relation.ReflTransGen.refl⟩
  have hselfb : b ∈ recoveryComponent pb qb rho gap b :=
    Finset.mem_filter.mpr ⟨hb, Relation.ReflTransGen.refl⟩
  apply componentAverage_gt_of_pointwise_gt pb qb _ ⟨b, hselfb⟩
  intro v hv
  apply componentAverage_lt_of_pointwise_lt pb qb _ ⟨a, hselfa⟩
  intro u hu
  exact recoveryComponent_cross_value_strict_order pb qb rho gap hgap ha hb hne hab u hu v hv

-- @node: recoveryComponent_average_le_of_marginal_le
/-- If [the gap is positive](hyp:hgap), [a is active](hyp:ha), [b is active](hyp:hb),
[a's fitted value is within a quarter-gap of s](hyp:hs), [b's fitted value is within
a quarter-gap of t](hyp:ht), and [s is no larger than t](hyp:hst), then [the average
fitted value of a's component is no larger than that of b's component](goal). -/
lemma recoveryComponent_average_le_of_marginal_le
    (pb qb : Z → ℝ) (rho gap : ℝ) (hgap : 0 < gap)
    {a b : RecoveryVertex Z} (ha : a ∈ recoveryActive pb rho)
    (hb : b ∈ recoveryActive pb rho) (s t : ℝ)
    (hs : |vertexValue pb qb a - s| < gap / 4)
    (ht : |vertexValue pb qb b - t| < gap / 4) (hst : s ≤ t) :
    componentAverage pb qb (recoveryComponent pb qb rho gap a) ≤
      componentAverage pb qb (recoveryComponent pb qb rho gap b) := by
  by_cases he : recoveryComponent pb qb rho gap a = recoveryComponent pb qb rho gap b
  · rw [he]
  · have hout : b ∉ recoveryComponent pb qb rho gap a := by
      intro hm
      exact he (recoveryComponent_eq_of_mem pb qb rho gap hm).symm
    have hself : a ∈ recoveryComponent pb qb rho gap a :=
      Finset.mem_filter.mpr ⟨ha, Relation.ReflTransGen.refl⟩
    have hsep := recoveryComponent_external_value_gap pb qb rho gap hb hout hself
    have hab : vertexValue pb qb a ≤ vertexValue pb qb b := by
      by_contra hn
      rw [abs_of_pos (sub_pos.mpr (lt_of_not_ge hn))] at hsep
      linarith [(abs_lt.mp hs).2, (abs_lt.mp ht).1]
    exact (recoveryComponent_average_lt_of_disconnected_value_le
      pb qb rho gap hgap ha hb he hab).le

end Papers.TbsPrteOptimalTransport

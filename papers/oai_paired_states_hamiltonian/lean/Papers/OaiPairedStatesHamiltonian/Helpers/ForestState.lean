module

public import Papers.OaiPairedStatesHamiltonian.Helpers.Pairs
public import Papers.OaiPairedStatesHamiltonian.Helpers.Cancel
public import Papers.OaiPairedStatesHamiltonian.Helpers.Circulation
public import Papers.OaiPairedStatesHamiltonian.Helpers.PairCycleLift
public import Papers.OaiPairedStatesHamiltonian.Helpers.ForestAsymptotics
public import Papers.OaiPairedStatesHamiltonian.Helpers.PairGroupProducts

/-! A pair with an acyclic opposite-edge graph, and its fixed choice. -/

@[expose] public section

namespace OaiPairedStatesHamiltonian

set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.unusedVariables false
open Classical
attribute [local instance] propDecidable




-- @node: clockwiseCycleWeight_lt_counterclockwise
/-- On a [sphere triangulation](hyp:hT) with [oppositely colored faces across every edge](hyp:hcol),
suppose [every counterclockwise cycle in the bounded spoke graph has positive signed weight](hyp:hpos).
For a pair and a cycle [whose edges all belong to that pair's undirected paired-edge set](hyp:hC),
[the clockwise cycle weight is strictly less than the counterclockwise cycle weight](goal). -/
lemma clockwiseCycleWeight_lt_counterclockwise (T : SphereMap) (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (hcol : PartitionColoring T col) (t0 : T.Face)
    (a : IncidenceWeights T col t0)
    (hpos : ∀ C : (spokeGraphBounded T col t0 hT hcol).Cycle,
      (spokeGraphBounded T col t0 hT hcol).IsCounterclockwise (spokeOuter T col t0 hT hcol) C →
        0 < signedSpokeWeight T col t0 hT hcol a C)
    (p : Pair T col t0) (C : T.Cycle)
    (hC : ∀ d ∈ C.val, T.edgeOf d ∈ undirectedPairedEdges T col t0 hT p) :
    clockwiseCycleWeight T col t0 hT hcol a p C hC < counterclockwiseCycleWeight T col t0 hT hcol a p C hC := by
  exact pairedCycle_weight_comparison T col t0 hT hcol a hpos p C hC

/-- For a [sphere triangulation](hyp:hT), [the partition sum equals the sum over occurring
undirected paired-edge sets of the sum over all pairs with that edge set, retaining each pair's
phase factor and exponential weight](goal). -/
-- @node: Z_eq_sum_undirected_groups
lemma Z_eq_sum_undirected_groups (T : SphereMap) (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (t0 : T.Face)
    (a : IncidenceWeights T col t0) (x : ℝ) :
    Z T col t0 hT a x =
      ∑ D ∈ Finset.univ.image (groupKey T col t0 hT),
        ∑ p ∈ Finset.univ.filter (fun p => groupKey T col t0 hT p = D),
          Complex.I ^ J T col t0 hT p.val.1 p.val.2 p.property *
            Complex.exp ((x * omega T col t0 a p.val.2 : ℝ) : ℂ) := by
  unfold Z
  symm
  apply Finset.sum_fiberwise_of_maps_to
  intro p hp
  exact Finset.mem_image.mpr ⟨p, hp, rfl⟩

/-- For a [sphere triangulation](hyp:hT) with [oppositely colored faces across each edge](hyp:hcol),
assume [at least one pair exists](hyp:hpairs) and [every counterclockwise spoke cycle has positive
signed weight](hyp:hpos). Then [the component counts of the occurring undirected paired-edge
graphs restricted to nonroot vertices have an attained minimum, and the partition sum is nonzero
at some real argument](goal). -/
-- @node: exists_Z_ne_zero_with_positive_weights
lemma exists_Z_ne_zero_with_positive_weights (T : SphereMap) (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (hcol : PartitionColoring T col) (t0 : T.Face)
    (hpairs : PairExists T col t0) (a : IncidenceWeights T col t0)
    (hpos : ∀ C : (spokeGraphBounded T col t0 hT hcol).Cycle,
      (spokeGraphBounded T col t0 hT hcol).IsCounterclockwise (spokeOuter T col t0 hT hcol) C →
        0 < signedSpokeWeight T col t0 hT hcol a C) :
    let groups := Finset.univ.image (groupKey T col t0 hT)
    let c := fun D : Finset T.Edge => Nat.card
      ((T.spanningGraph {e | e ∈ D}).induce {v | v ∈ nonRoot T t0}).ConnectedComponent
      -- @realizes c(number of cycles of an occurring undirected paired edge set)
    ∃ c_min : ℕ, -- @realizes c_{\min}(smallest number of cycles among the occurring groups)
      c_min ∈ groups.image c ∧ (∀ D ∈ groups, c_min ≤ c D) ∧
      ∃ x : ℝ, Z T col t0 hT a x ≠ 0 := by
  let groups := Finset.univ.image (groupKey T col t0 hT)
  let c := fun D : Finset T.Edge => Nat.card
    ((T.spanningGraph {e | e ∈ D}).induce {v | v ∈ nonRoot T t0}).ConnectedComponent
  have hgroups : groups.Nonempty := by
    obtain ⟨r, s, hp⟩ := hpairs
    exact ⟨_, Finset.mem_image.mpr ⟨⟨(r, s), hp⟩, Finset.mem_univ _, rfl⟩⟩
  obtain ⟨D, hD, hminimal⟩ := Finset.exists_min_image groups c hgroups
  refine ⟨c D, Finset.mem_image.mpr ⟨D, hD, rfl⟩, hminimal, ?_⟩
  have hleading (D : groups) :
      ∃ (n : ℕ) (f : ℝ → ℝ) (k : ℝ), 0 < k ∧
        Filter.Tendsto (fun x => f x / x ^ n) (nhdsWithin 0 {0}ᶜ) (nhds k) ∧
        ∀ x, (∑ q ∈ Finset.univ.filter (fun q => groupKey T col t0 hT q = D.val),
          Complex.I ^ J T col t0 hT q.val.1 q.val.2 q.property *
            Complex.exp ((x * omega T col t0 a q.val.2 : ℝ) : ℂ)) =
          (-Complex.I) ^ n * (f x : ℂ) := by
    obtain ⟨p, hp, he⟩ := Finset.mem_image.mp D.property
    simpa only [he] using pair_group_positive_leading_term T col t0 hT hcol p a hpos
  choose n f k hk hlim hprod using hleading
  have hnonempty : (Finset.univ : Finset groups).Nonempty :=
    ⟨⟨D, hD⟩, Finset.mem_univ _⟩
  obtain ⟨x, hx⟩ := exists_nonzero_minimum_order_phase_sum Finset.univ hnonempty
    (-Complex.I) (neg_ne_zero.mpr Complex.I_ne_zero) n f k
    (fun D hD => hk D) (fun D hD => hlim D)
  refine ⟨x, ?_⟩
  have he : Z T col t0 hT a x = ∑ D : groups, (-Complex.I) ^ n D * (f D x : ℂ) := by
    rw [Z_eq_sum_undirected_groups]
    change (∑ D ∈ groups, _) = _
    rw [Finset.sum_subtype (F := inferInstance) (p := fun D => D ∈ groups)
      groups (fun D => Iff.rfl)]
    apply Finset.sum_congr rfl
    intro D hD
    exact hprod D x
  rwa [he]


/-- For a [sphere triangulation](hyp:hT), [the partition sum equals the sum over second states
of the sum over all first states paired with them, with the same phase factors and exponential
weights](goal). -/
-- @node: Z_eq_sum_second_state
lemma Z_eq_sum_second_state (T : SphereMap) (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (t0 : T.Face)
    (a : IncidenceWeights T col t0) (x : ℝ) :
    Z T col t0 hT a x = ∑ s : State T col t0,
      ∑ r : {r : State T col t0 // IsPair T col t0 r s},
        Complex.I ^ J T col t0 hT r.val s r.property *
          Complex.exp ((x * omega T col t0 a s : ℝ) : ℂ) := by
  let e : Pair T col t0 ≃
      Σ s : State T col t0, {r : State T col t0 // IsPair T col t0 r s} :=
    { toFun := fun p => ⟨p.val.2, ⟨p.val.1, p.property⟩⟩
      invFun := fun p => ⟨(p.2.val, p.1), p.2.property⟩
      left_inv := by intro p; rfl
      right_inv := by intro p; rfl }
  unfold Z
  calc
    _ = ∑ p : (Σ s : State T col t0, {r : State T col t0 // IsPair T col t0 r s}),
        Complex.I ^ J T col t0 hT p.2.val p.1 p.2.property *
          Complex.exp ((x * omega T col t0 a p.1 : ℝ) : ℂ) :=
      Fintype.sum_equiv e _ _ (fun p => rfl)
    _ = _ := Fintype.sum_sigma _

/-- If [a state's opposite-edge graph is not acyclic](hyp:h), then
[that graph contains a simple cycle](goal). -/
-- @node: qsHasSimpleCycle_of_cyclic
lemma qsHasSimpleCycle_of_cyclic (T : SphereMap) (col : T.Face → Bool)
    (t0 : T.Face) (s : State T col t0) (h : QsCyclic T col t0 s) :
    QsHasSimpleCycle T col t0 s := by
  change ¬ (∀ ⦃v : T.Vertex⦄ (C : (Qs T col t0 s).Walk v v), ¬ C.IsCycle) at h
  push Not at h
  exact h

/-- For a [sphere triangulation](hyp:hT) with [oppositely colored faces across each edge](hyp:hcol),
if [every pair has a cyclic opposite-edge graph for its second state](hyp:hcyclic), then
[the partition sum is zero for any incidence weights and real argument](goal). -/
-- @node: Z_eq_zero_of_all_pairs_cyclic
lemma Z_eq_zero_of_all_pairs_cyclic (T : SphereMap) (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (hcol : PartitionColoring T col) (t0 : T.Face)
    (hcyclic : ∀ r s : State T col t0, IsPair T col t0 r s → QsCyclic T col t0 s)
    (a : IncidenceWeights T col t0) (x : ℝ) : Z T col t0 hT a x = 0 := by
  rw [Z_eq_sum_second_state]
  apply Finset.sum_eq_zero
  intro s hs
  by_cases hp : ∃ r : State T col t0, IsPair T col t0 r s
  · obtain ⟨r, hr⟩ := hp
    have hc := hcyclic r s hr
    exact sum_Z_terms_eq_zero_of_cyclic T hT col hcol t0 s hc
      (qsHasSimpleCycle_of_cyclic T col t0 s hc) a x
  · let hempty : IsEmpty {r : State T col t0 // IsPair T col t0 r s} :=
      ⟨fun r => hp ⟨r.val, r.property⟩⟩
    simp only [Finset.univ_eq_empty, Finset.sum_empty]

-- @node: prop:forest-state
/-- For a [sphere triangulation](hyp:hT) with [oppositely colored faces across each edge](hyp:hcol),
assume [a pair exists](hyp:hpairs) and [two pairs have the same grouping key exactly when their
undirected paired-edge sets agree](hyp:hpin). Then [there are two paired states whose second
state has an acyclic opposite-edge graph](goal). -/
lemma exists_pair_qs_forest (T : SphereMap) (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (hcol : PartitionColoring T col) (t0 : T.Face)
    (hpairs : PairExists T col t0) (hpin : PairedEdgesReading T col t0 hT) :
    ∃ r s : State T col t0, IsPair T col t0 r s ∧ QsForest T col t0 s := by
  obtain ⟨a, hpositive⟩ := exists_positive_spoke_weights T hT col hcol t0
  obtain ⟨c, hc, hminimal, x, hx⟩ :=
    exists_Z_ne_zero_with_positive_weights T hT col hcol t0 hpairs a hpositive
  by_contra hforest
  have hcyclic (r s : State T col t0) (hp : IsPair T col t0 r s) :
      QsCyclic T col t0 s := by
    intro hf
    exact hforest ⟨r, s, hp, hf⟩
  exact hx (Z_eq_zero_of_all_pairs_cyclic T hT col hcol t0 hcyclic a x)

-- @node: exists_forest_pair_of_noSeparatingTriangle
/-- For a [sphere triangulation](hyp:hT) with [oppositely colored faces across each edge](hyp:hcol)
and [no separating triangle](hyp:hsep), [there is an ordered pair of states satisfying the pairing
condition whose second state's opposite-edge graph is a forest](goal). -/
lemma exists_forest_pair_of_noSeparatingTriangle (T : SphereMap) (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (hcol : PartitionColoring T col)
    (hsep : TreesNoSeparatingTriangle T) (t0 : T.Face) :
    ∃ p : State T col t0 × State T col t0, IsPair T col t0 p.1 p.2 ∧ QsForest T col t0 p.2 := by
  have hpairs : PairExists T col t0 :=
    exists_pair_of_noSeparatingTriangle T hT col hcol hsep singletonTreeEdgeless_of_mathlib t0
  have hreading : PairedEdgesReading T col t0 hT := fun p q => Iff.rfl
  obtain ⟨r, s, hp, hf⟩ := exists_pair_qs_forest T hT col hcol t0 hpairs hreading
  exact ⟨(r, s), hp, hf⟩

-- @node: def:forest-pair
/-- Given a [sphere map](hyp:T), [its triangulation property](hyp:hT), a [face coloring](hyp:col)
that [assigns opposite colors across each edge](hyp:hcol), [absence of separating triangles](hyp:hsep),
and a [root face](hyp:t0), the [chosen forest pair](goal) is an ordered pair of states satisfying
the pairing condition whose second state's opposite-edge graph is acyclic. -/
noncomputable def forestPair (T : SphereMap) (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (hcol : PartitionColoring T col)
    (hsep : TreesNoSeparatingTriangle T) (t0 : T.Face) : State T col t0 × State T col t0 :=
  Classical.choose (exists_forest_pair_of_noSeparatingTriangle T hT col hcol hsep t0)

-- @node: forestPair_isPair
/-- For a [sphere triangulation](hyp:hT) with [oppositely colored faces across each edge](hyp:hcol)
and [no separating triangle](hyp:hsep), [the two states of the chosen forest pair satisfy the
pairing condition](goal). -/
lemma forestPair_isPair (T : SphereMap) (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (hcol : PartitionColoring T col)
    (hsep : TreesNoSeparatingTriangle T) (t0 : T.Face) :
    IsPair T col t0 (forestPair T hT col hcol hsep t0).1 (forestPair T hT col hcol hsep t0).2 := by
  exact (Classical.choose_spec
    (exists_forest_pair_of_noSeparatingTriangle T hT col hcol hsep t0)).1
-- @node: forestPair_qsForest
/-- For a [sphere triangulation](hyp:hT) with [oppositely colored faces across each edge](hyp:hcol)
and [no separating triangle](hyp:hsep), [the second state of the chosen forest pair has an
acyclic opposite-edge graph](goal). -/
lemma forestPair_qsForest (T : SphereMap) (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (hcol : PartitionColoring T col)
    (hsep : TreesNoSeparatingTriangle T) (t0 : T.Face) :
    QsForest T col t0 (forestPair T hT col hcol hsep t0).2 := by
  exact (Classical.choose_spec
    (exists_forest_pair_of_noSeparatingTriangle T hT col hcol hsep t0)).2


end OaiPairedStatesHamiltonian

module
public import Papers.OaiGeometricErdosSimilarity.Helpers.Windows
public import Causalean.Experimentation.DesignBased.Designs.BernoulliMoments
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.MeasurableSpace.Basic

/-! # Independent finite tables, routing, and center exposure -/

@[expose] public section

namespace Papers.OaiGeometricErdosSimilarity

open Causalean.Experimentation.DesignBased
open scoped BigOperators
open MeasureTheory
attribute [local instance] Classical.propDecidable

-- @env: S3
variable {q : ℝ} {M d g r0 n0 : ℕ} {p : ℝ}

/-- For [geometric ratio q](hyp:q), [branching number M](hyp:M), [tree depth d](hyp:d),
[window gap g](hyp:g), [base length r0](hyp:r0), [starting index n0](hyp:n0), and
[leaf L](hyp:L), the [leaf endpoint](goal) is the endpoint of its incoming-edge
window when its depth is positive, and zero otherwise. -/
noncomputable def leafEndpoint (q : ℝ) (M d g r0 n0 : ℕ) (L : Leaf M d) : ℕ :=
  -- @realizes b(L)(incoming-edge endpoint; positive range via leafEndpoint_positive)
  if hL : 1 ≤ L.val.1.val then windowEnd q M d g r0 n0 ⟨L.val, hL⟩ else 0

/-- If [the tree depth is at least one](hyp:hd), [the base window length is positive](hyp:hr),
and [the starting index is at least one](hyp:hn0), then [leaf L](hyp:L)
has [an incoming-window endpoint of at least one](goal). -/
-- @node: leafEndpoint_positive
lemma leafEndpoint_positive
    (hd : DepthDomain d) -- @realizes b(L)(positive-depth domain excludes depth zero)
    (hr : BaseLengthDomain r0) -- @realizes b(L)(positive base-length domain)
    (hn0 : 1 ≤ n0) -- @realizes b(L)(positive starting-index domain)
    (L : Leaf M d) :
    1 ≤ leafEndpoint q M d g r0 n0 L := by
  have hL : 1 ≤ L.val.1.val := L.property.symm ▸ hd
  rw [leafEndpoint, dif_pos hL]
  exact windowEnd_positive q g r0 hr hn0 ⟨L.val, hL⟩

/-- With [geometric ratio q](hyp:q), [branching number M](hyp:M), [tree depth d](hyp:d),
[window gap g](hyp:g), [base length r0](hyp:r0), and [starting index n0](hyp:n0),
a [selector address](goal) pairs a nondefault edge with a grid-cell index at
the resolution determined by that edge's window endpoint. -/
abbrev SelAddr (q : ℝ) (M d g r0 n0 : ℕ) :=
  Σ e : NondefaultEdge M d, Fin (gridResolution q (windowEnd q M d g r0 n0 e.val))

/-- With [geometric ratio q](hyp:q), [branching number M](hyp:M), [tree depth d](hyp:d),
[window gap g](hyp:g), [base length r0](hyp:r0), and [starting index n0](hyp:n0),
a [terminal address](goal) pairs a leaf with a grid-cell index at the resolution
determined by that leaf's incoming-window endpoint. -/
abbrev TermAddr (q : ℝ) (M d g r0 n0 : ℕ) :=
  Σ L : Leaf M d, Fin (gridResolution q (leafEndpoint q M d g r0 n0 L))

/-- For [geometric ratio q](hyp:q), [branching number M](hyp:M), [tree depth d](hyp:d),
[window gap g](hyp:g), [base length r0](hyp:r0), and [starting index n0](hyp:n0),
a [table address](goal) is either a selector address or a terminal address,
with the two kinds distinguished. -/
abbrev TableAddr (q : ℝ) (M d g r0 n0 : ℕ) := SelAddr q M d g r0 n0 ⊕ TermAddr q M d g r0 n0

/-- For [geometric ratio q](hyp:q), [branching number M](hyp:M), [tree depth d](hyp:d),
[window gap g](hyp:g), [base length r0](hyp:r0), and [starting index n0](hyp:n0),
an [outcome](goal) assigns a Boolean value to every selector and terminal address. -/
abbrev Outcome (q : ℝ) (M d g r0 n0 : ℕ) := TableAddr q M d g r0 n0 → Bool
  -- @realizes \Omega(all finite Boolean table assignments)

/-- For tables with [geometric ratio q](hyp:q), [branching number M](hyp:M),
[depth d](hyp:d), [gap g](hyp:g), [base length r0](hyp:r0), and [starting index n0](hyp:n0),
the [coordinate success probability](goal) is one half at selector addresses and
[the terminal parameter p](hyp:p) clipped to the interval from zero to one at terminal addresses. -/
noncomputable def tableParameter (p : ℝ) : TableAddr q M d g r0 n0 → ℝ :=
  Sum.elim (fun _ => 1 / 2) (fun _ => max 0 (min p 1))

-- @node: tableParameter_nonneg
/-- For [terminal parameter p](hyp:p) and [table address a](hyp:a),
[the coordinate success probability is nonnegative](goal). -/
lemma tableParameter_nonneg (p : ℝ) (a : TableAddr q M d g r0 n0) :
    0 ≤ tableParameter p a := by
  cases a <;> simp [tableParameter]

-- @node: tableParameter_le_one
/-- For [terminal parameter p](hyp:p) and [table address a](hyp:a),
[the coordinate success probability is at most one](goal). -/
lemma tableParameter_le_one (p : ℝ) (a : TableAddr q M d g r0 n0) :
    tableParameter p a ≤ 1 := by
  cases a <;> norm_num [tableParameter]

-- @node: def:random-tables
/-- For [geometric ratio q](hyp:q), [branching number M](hyp:M), [tree depth d](hyp:d),
[window gap g](hyp:g), [base length r0](hyp:r0), [starting index n0](hyp:n0), and
[terminal parameter p](hyp:p), the [table probability law](goal) makes all
coordinates independent, with fair selector bits and terminal success probability
equal to p clipped to the interval from zero to one. -/
noncomputable def tableLaw (q : ℝ) (M d g r0 n0 : ℕ) (p : ℝ) :
    FiniteDesign (Outcome q M d g r0 n0) :=
  -- @realizes \Prob(independent fair selector and Bernoulli-p terminal product law)
  -- @realizes \E(FiniteDesign.E for this law)
  bernoulliDesign (tableParameter p) (tableParameter_nonneg p) (tableParameter_le_one p)

/-- In tables with [geometric ratio q](hyp:q), [branching number M](hyp:M), [depth d](hyp:d),
[gap g](hyp:g), [base length r0](hyp:r0), and [starting index n0](hyp:n0),
the [selector entry](goal) reads [outcome ω](hyp:ω) at [nondefault edge e](hyp:e)
and [grid-cell index j](hyp:j). -/
noncomputable def selectorEntry (ω : Outcome q M d g r0 n0) (e : NondefaultEdge M d)
    (j : Fin (gridResolution q (windowEnd q M d g r0 n0 e.val))) : Bool := ω (Sum.inl ⟨e, j⟩)
      -- @realizes S_e(selector table coordinates)

/-- In tables with [geometric ratio q](hyp:q), [branching number M](hyp:M), [depth d](hyp:d),
[gap g](hyp:g), [base length r0](hyp:r0), and [starting index n0](hyp:n0),
the [terminal entry](goal) reads [outcome ω](hyp:ω) at [leaf L](hyp:L)
and [grid-cell index j](hyp:j). -/
noncomputable def terminalEntry (ω : Outcome q M d g r0 n0) (L : Leaf M d)
    (j : Fin (gridResolution q (leafEndpoint q M d g r0 n0 L))) : Bool := ω (Sum.inr ⟨L, j⟩)
      -- @realizes T_L(terminal table coordinates)

-- @node: defaultChild_lt
/-- If [M is at least two](hyp:hM), then
[the default child's zero-based index M minus one is less than M](goal). -/
lemma defaultChild_lt (hM : BranchingDomain M) : M - 1 < M := by
  unfold BranchingDomain at hM
  omega

/-- For [branching number M](hyp:M) [at least two](hyp:hM),
the [default child](goal) is the last child, with zero-based index M minus one. -/
def defaultChild (hM : BranchingDomain M) : Fin M := ⟨M - 1, defaultChild_lt hM⟩

-- @node: nondefaultChildEdge_property
/-- For [internal vertex U](hyp:U) and [child index i](hyp:i), if
[i plus one is less than M](hyp:hi), then [the edge to that child also has
child index plus one less than M](goal). -/
lemma nondefaultChildEdge_property (U : InternalVertex M d) (i : Fin M) (hi : i.val + 1 < M) :
    (childIndex (childEdge U i)).val + 1 < M := by
  have hindex : childIndex (childEdge U i) = i := by
    change Fin.lastCases i U.val.2 ⟨U.val.1.val + 1 - 1, _⟩ = i
    have hlast : (⟨U.val.1.val + 1 - 1, lastIndex_lt (childEdge U i)⟩ :
        Fin (U.val.1.val + 1)) = Fin.last U.val.1.val := by
      apply Fin.ext
      simp
    rw [hlast, Fin.lastCases_last]
  rwa [hindex]

/-- In a tree with [branching number M](hyp:M) and [depth d](hyp:d), for
[internal vertex U](hyp:U) and [child index i](hyp:i) with
[i plus one less than M](hyp:hi), the [nondefault child edge](goal) is the edge
from U to child i, recorded as a nondefault edge. -/
def nondefaultChildEdge (U : InternalVertex M d) (i : Fin M) (hi : i.val + 1 < M) :
  NondefaultEdge M d :=
  ⟨childEdge U i, nondefaultChildEdge_property U i hi⟩

/-- In a tree with [branching number M](hyp:M) and [depth d](hyp:d), assuming
[M is at least two](hyp:hM), the [chosen child](goal) of
[internal vertex U](hyp:U) is the first nondefault child whose edge is true in
[the Boolean edge assignment ξ](hyp:ξ), or the default child if no such child exists. -/
noncomputable def chooseChild (hM : BranchingDomain M) (ξ : NondefaultEdge M d → Bool)
    (U : InternalVertex M d) : Fin M :=
  ((List.finRange M).find? (fun i => if hi : i.val + 1 < M then ξ (nondefaultChildEdge U i hi)
    else false)).getD
    (defaultChild hM)

/-- In a tree with [branching number M](hyp:M) and [depth d](hyp:d), assuming
[M is at least two](hyp:hM) and using [Boolean edge assignment ξ](hyp:ξ),
the [list of visited vertices](goal) [contains only the starting vertex when
the step budget is zero](step:1); [with a positive budget it follows the chosen
child and continues with one fewer step, or stops at a leaf](step:2). -/
noncomputable def walkVertices (hM : BranchingDomain M) (ξ : NondefaultEdge M d → Bool) :
    ℕ → TreeVertex M d → List (TreeVertex M d)
  | 0, v => [v]
  | fuel + 1, v =>
    if hv : v.1.val < d then
      v :: walkVertices hM ξ fuel (child ⟨v, hv⟩ (chooseChild hM ξ ⟨v, hv⟩))
    else [v]

-- @node: walkVertices_ne_nil
/-- Assuming [M is at least two](hyp:hM), for [Boolean edge assignment ξ](hyp:ξ),
[step budget fuel](hyp:fuel), and [starting vertex v](hyp:v),
[the list of visited vertices is nonempty](goal). -/
lemma walkVertices_ne_nil (hM : BranchingDomain M) (ξ : NondefaultEdge M d → Bool)
    (fuel : ℕ) (v : TreeVertex M d) : walkVertices hM ξ fuel v ≠ [] := by
  cases fuel <;> simp [walkVertices]
  split <;> simp

-- @node: walkVertices_last_depth_of_fuel
/-- Assuming [M is at least two](hyp:hM), take [Boolean edge assignment ξ](hyp:ξ),
[step budget fuel](hyp:fuel), and [starting vertex v](hyp:v). If [the budget is at least
the remaining depth below v](hyp:hfuel), then [the last visited vertex has depth d](goal). -/
lemma walkVertices_last_depth_of_fuel (hM : BranchingDomain M)
    (ξ : NondefaultEdge M d → Bool) (fuel : ℕ) (v : TreeVertex M d)
    (hfuel : d - v.1.val ≤ fuel) :
    ((walkVertices hM ξ fuel v).getLast (walkVertices_ne_nil hM ξ fuel v)).1.val = d := by
  induction fuel generalizing v with
  | zero =>
      have hv := v.1.isLt
      simpa [walkVertices] using (show v.1.val = d by omega)
  | succ fuel ih =>
      by_cases hv : v.1.val < d
      · simp only [walkVertices, dif_pos hv]
        rw [List.getLast_cons (walkVertices_ne_nil hM ξ fuel _)]
        apply ih
        change d - (v.1.val + 1) ≤ fuel
        omega
      · have hvbound := v.1.isLt
        simpa [walkVertices, hv] using (show v.1.val = d by omega)

-- @node: walkVertices_last_depth
/-- Assuming [M is at least two](hyp:hM), for [Boolean edge assignment ξ](hyp:ξ)
and [starting vertex v](hyp:v), [a walk with a budget of d steps ends at depth d](goal). -/
lemma walkVertices_last_depth (hM : BranchingDomain M) (ξ : NondefaultEdge M d → Bool)
    (v : TreeVertex M d) : ((walkVertices hM ξ d v).getLast (walkVertices_ne_nil hM ξ d
      v)).1.val = d := by
  exact walkVertices_last_depth_of_fuel hM ξ d v (Nat.sub_le _ _)

/-- For [geometric ratio q](hyp:q), [branching number M](hyp:M), [tree depth d](hyp:d),
[window gap g](hyp:g), [base length r0](hyp:r0), and [starting index n0](hyp:n0),
the [exposed selector address](goal) pairs [nondefault edge e](hyp:e) with
the grid cell containing [point x](hyp:x), at the resolution of the edge's window endpoint. -/
noncomputable def exposedAddr (q : ℝ) (M d g r0 n0 : ℕ) (x : ℝ) (e : NondefaultEdge M d) : SelAddr
  q M d g r0 n0 :=
  ⟨e, gridKeyFin q (windowEnd q M d g r0 n0 e.val) x⟩

/-- For tables with [geometric ratio q](hyp:q), [branching number M](hyp:M), [depth d](hyp:d),
[gap g](hyp:g), [base length r0](hyp:r0), and [starting index n0](hyp:n0),
the [exposed Boolean vector](goal) reads [outcome ω](hyp:ω) at the selector address
of [point z](hyp:z) in every nondefault-edge table. -/
noncomputable def exposedValues (ω : Outcome q M d g r0 n0) (z : ℝ) : NondefaultEdge M d → Bool :=
  fun e => ω (Sum.inl (exposedAddr q M d g r0 n0 z e))

/-- With [geometric ratio q](hyp:q), [branching number M](hyp:M), [tree depth d](hyp:d),
[window gap g](hyp:g), [base length r0](hyp:r0), and [starting index n0](hyp:n0), assuming
[M is at least two](hyp:hM), the [routed leaf from a vertex](goal)
is reached from [starting vertex v](hyp:v) by following the selector values exposed
by [point z](hyp:z) in [outcome ω](hyp:ω), with a budget of d steps. -/
noncomputable def routeFrom (hM : BranchingDomain M) (ω : Outcome q M d g r0 n0) (z : ℝ)
    (v : TreeVertex M d) : Leaf M d :=
  ⟨(walkVertices hM (exposedValues ω z) d v).getLast (walkVertices_ne_nil hM (exposedValues ω z)
    d v),
    walkVertices_last_depth hM (exposedValues ω z) v⟩

/-- With [geometric ratio q](hyp:q), [branching number M](hyp:M), [tree depth d](hyp:d),
[window gap g](hyp:g), [base length r0](hyp:r0), and [starting index n0](hyp:n0), assuming
[M is at least two](hyp:hM), the [routed leaf](goal) is reached from
the root using the selector values exposed by [point z](hyp:z) in [outcome ω](hyp:ω). -/
noncomputable def route (hM : BranchingDomain M) (ω : Outcome q M d g r0 n0) (z : ℝ) : Leaf M d :=
  -- @realizes L(z)(selector-dependent routed leaf)
  routeFrom hM ω z (root M d)

-- @node: def:random-set
/-- With [geometric ratio q](hyp:q), [branching number M](hyp:M), [tree depth d](hyp:d),
[window gap g](hyp:g), [base length r0](hyp:r0), and [starting index n0](hyp:n0), assuming
[M is at least two](hyp:hM), the [random set](goal) associated with
[outcome ω](hyp:ω) consists of real points whose grid cell at their routed leaf
has terminal value true. -/
noncomputable def randomSet (hM : BranchingDomain M) (ω : Outcome q M d g r0 n0) : Set ℝ :=
  -- @realizes B(periodic random set from terminal entry at the routed leaf)
  {z | terminalEntry ω (route hM ω z) (gridKeyFin q (leafEndpoint q M d g r0 n0 (route hM ω z)) z)
    = true}

/-- For [geometric ratio q](hyp:q), [branching number M](hyp:M), [tree depth d](hyp:d),
[window gap g](hyp:g), [base length r0](hyp:r0), and [starting index n0](hyp:n0),
the [exposure atom condition](goal) says that [outcome ω](hyp:ω) agrees with
[Boolean edge vector ξ](hyp:ξ) at every selector address exposed by [point x](hyp:x). -/
def atomEvent (q : ℝ) (M d g r0 n0 : ℕ) (x : ℝ) (ξ : NondefaultEdge M d → Bool)
    (ω : Outcome q M d g r0 n0) : Prop :=
      -- @realizes \xi(atom specified by a finite Boolean value vector)
  ∀ e, ω (Sum.inl (exposedAddr q M d g r0 n0 x e)) = ξ e

/-- For [geometric ratio q](hyp:q), [branching number M](hyp:M), [tree depth d](hyp:d),
[window gap g](hyp:g), [base length r0](hyp:r0), and [starting index n0](hyp:n0),
the [selector sigma-algebra](goal) is generated by the full vector of selector bits,
so its events can depend on all selector coordinates. -/
@[instance_reducible]
def selectorSigmaAlgebra (q : ℝ) (M d g r0 n0 : ℕ) :
    MeasurableSpace (Outcome q M d g r0 n0) :=
  -- @realizes \mathcal A(sigma-field generated by all selector entries)
  MeasurableSpace.comap (fun ω => fun a : SelAddr q M d g r0 n0 => ω (Sum.inl a)) ⊤

/-- For [geometric ratio q](hyp:q), [branching number M](hyp:M), [tree depth d](hyp:d),
[window gap g](hyp:g), [base length r0](hyp:r0), and [starting index n0](hyp:n0),
the [center-exposure sigma-algebra](goal) is generated by the vector of selector bits
addressed by [point x](hyp:x), one in every nondefault-edge table, including those outside the route. -/
-- @node: def:center-exposure
@[instance_reducible]
noncomputable def centerExposure (q : ℝ) (M d g r0 n0 : ℕ) (x : ℝ) :
    MeasurableSpace (Outcome q M d g r0 n0) :=
  -- @realizes \mathcal F_x(sigma-field generated by every addressed selector coordinate)
  MeasurableSpace.comap (fun ω => exposedValues ω x) ⊤

/-- For [center x](hyp:x), [the center-exposure sigma-algebra is contained in
the sigma-algebra generated by all selector coordinates](goal). -/
-- keep: Proves the explicit inclusion F_x ⊆ A in eq:center-exposure; a paper-facing fidelity result even though atomwise probability proofs do not invoke it.
lemma centerExposure_le_selectorSigmaAlgebra (x : ℝ) :
    centerExposure q M d g r0 n0 x ≤ selectorSigmaAlgebra q M d g r0 n0 := by
  intro s hs
  obtain ⟨t, _, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
  exact ⟨{σ | (fun e => σ (exposedAddr q M d g r0 n0 x e)) ∈ t}, trivial, rfl⟩

/-- For [center x](hyp:x) and [Boolean edge vector ξ](hyp:ξ), [the exposure atom
is exactly the set of outcomes whose exposed vector at x equals ξ](goal). -/
lemma atomEvent_eq_fiber (x : ℝ) (ξ : NondefaultEdge M d → Bool) :
    {ω | atomEvent q M d g r0 n0 x ξ ω} = {ω | exposedValues ω x = ξ} := by
  ext ω
  exact ⟨fun h => funext h, fun h => congrFun h⟩

/-- For [center x](hyp:x), [every Boolean edge vector is the exposed vector
of some table outcome at x](goal). -/
lemma exposedValues_surjective (x : ℝ) :
    Function.Surjective (fun ω : Outcome q M d g r0 n0 => exposedValues ω x) := by
  intro ξ
  exact ⟨Sum.elim (fun a => ξ a.1) (fun _ => false), rfl⟩

-- keep: Proves every exposure vector defines a nonempty atom, as stated immediately after eq:center-exposure; needed to justify the atom interpretation of xi.
/-- For [center x](hyp:x) and [Boolean edge vector ξ](hyp:ξ),
[the exposure atom specified by ξ contains at least one outcome](goal). -/
lemma atomEvent_nonempty (x : ℝ) (ξ : NondefaultEdge M d → Bool) :
    Set.Nonempty {ω | atomEvent q M d g r0 n0 x ξ ω} := by
  obtain ⟨ω, hω⟩ := exposedValues_surjective (q := q) (g := g) (r0 := r0) (n0 := n0) x ξ
  exact ⟨ω, fun e => congrFun hω e⟩

/-- For [center x](hyp:x) and [Boolean edge vector ξ](hyp:ξ),
[the exposure atom specified by ξ is measurable in the center-exposure sigma-algebra](goal). -/
lemma measurableSet_atomEvent (x : ℝ) (ξ : NondefaultEdge M d → Bool) :
    MeasurableSet[centerExposure q M d g r0 n0 x]
      {ω | atomEvent q M d g r0 n0 x ξ ω} := by
  rw [atomEvent_eq_fiber]
  exact ⟨{ξ}, trivial, rfl⟩

/-- For [center x](hyp:x) and [a set s of table outcomes](hyp:s), [s is measurable
in the center-exposure sigma-algebra if and only if it is a union of exposure atoms](goal). -/
-- keep: Identifies the exposure sigma-field exactly with unions of the fibers used for conditioning; certifies the paper-to-Lean representation of def:center-exposure.
lemma measurableSet_centerExposure_iff (x : ℝ) (s : Set (Outcome q M d g r0 n0)) :
    MeasurableSet[centerExposure q M d g r0 n0 x] s ↔
      ∃ vectors : Set (NondefaultEdge M d → Bool),
        s = ⋃ ξ ∈ vectors, {ω | atomEvent q M d g r0 n0 x ξ ω} := by
  constructor
  · intro hs
    obtain ⟨vectors, _, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
    refine ⟨vectors, ?_⟩
    ext ω
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨fun h => ⟨exposedValues ω x, h, fun _ => rfl⟩,
      fun ⟨ξ, hξ, hω⟩ => by
        have heq : exposedValues ω x = ξ := funext hω
        rwa [heq]⟩
  · rintro ⟨vectors, rfl⟩
    exact MeasurableSet.iUnion (fun ξ =>
      MeasurableSet.iUnion (fun _ => measurableSet_atomEvent x ξ))

/-- For [center x](hyp:x), [Boolean edge vector ξ](hyp:ξ), and [a set s of table outcomes](hyp:s),
if [s is measurable in the center-exposure sigma-algebra](hyp:hs), [s is nonempty](hyp:hne),
and [s is contained in the exposure atom specified by ξ](hyp:hsub), then
[s equals that entire exposure atom](goal). -/
-- keep: Proves the fibers used for conditioning are sigma-field atoms, as the paper requires after eq:center-exposure; retained as representation evidence.
lemma atomEvent_minimal (x : ℝ) (ξ : NondefaultEdge M d → Bool)
    (s : Set (Outcome q M d g r0 n0))
    (hs : MeasurableSet[centerExposure q M d g r0 n0 x] s)
    (hne : s.Nonempty) (hsub : s ⊆ {ω | atomEvent q M d g r0 n0 x ξ ω}) :
    s = {ω | atomEvent q M d g r0 n0 x ξ ω} := by
  obtain ⟨ω, hω⟩ := hne
  obtain ⟨t, _, ht⟩ := MeasurableSpace.measurableSet_comap.mp hs
  apply Set.Subset.antisymm hsub
  intro ω' hω'
  have heq : exposedValues ω' x = exposedValues ω x :=
    (funext hω').trans (funext (hsub hω)).symm
  rw [← ht] at hω ⊢
  change exposedValues ω' x ∈ t
  rw [heq]
  exact hω

/-- Under [finite probability design D](hyp:D), the [conditional probability](goal)
of [event A](hyp:A) given [event B](hyp:B) is the probability of their intersection
divided by the probability of B, with value zero when B has probability zero. -/
noncomputable def condPr {Ω : Type*} [Fintype Ω] (D : FiniteDesign Ω) (A B : Ω → Prop) : ℝ :=
  D.Pr (fun ω => A ω ∧ B ω) / D.Pr B

-- @node: atomEvent_probability
/-- For [center x](hyp:x) and [Boolean edge vector ξ](hyp:ξ), [the probability
of the exposure atom specified by ξ under the table law is one half raised
to the number of nondefault edges](goal). -/
lemma atomEvent_probability (x : ℝ) (ξ : NondefaultEdge M d → Bool) :
    (tableLaw q M d g r0 n0 p).Pr (atomEvent q M d g r0 n0 x ξ) = (1 / 2 : ℝ) ^ Fintype.card
      (NondefaultEdge M d) := by
  classical
  -- Each exposed selector contributes one indicator; all other coordinates contribute one.
  let F : TableAddr q M d g r0 n0 → Bool → ℝ := Sum.elim
    (fun a b => if a.2 = gridKeyFin q (windowEnd q M d g r0 n0 a.1.val) x then
      if b = ξ a.1 then 1 else 0 else 1)
    (fun _ _ => 1)
  have hprod (ω : Outcome q M d g r0 n0) :
      (∏ a, F a (ω a)) = ∏ e, if ω (Sum.inl (exposedAddr q M d g r0 n0 x e)) = ξ e
        then (1 : ℝ) else 0 := by
    simp only [Fintype.prod_sum_type, Fintype.prod_sigma, F, Sum.elim_inl,
      Sum.elim_inr, Finset.prod_const_one, mul_one]
    apply Finset.prod_congr rfl
    intro e _
    rw [Finset.prod_eq_single (gridKeyFin q (windowEnd q M d g r0 n0 e.val) x)]
    · simp [exposedAddr]
      rfl
    · intro j _ hj
      simp [hj]
    · simp
  have hind : FiniteDesign.ind (atomEvent q M d g r0 n0 x ξ) =
      fun ω => ∏ a, F a (ω a) := by
    funext ω
    rw [hprod]
    by_cases hω : atomEvent q M d g r0 n0 x ξ ω
    · simp only [FiniteDesign.ind, if_pos hω]
      symm
      exact Finset.prod_eq_one fun e _ => if_pos (hω e)
    · obtain ⟨e, he⟩ := not_forall.mp hω
      rw [FiniteDesign.ind, if_neg hω]
      exact (Finset.prod_eq_zero (Finset.mem_univ e) (if_neg he)).symm
  unfold tableLaw FiniteDesign.Pr
  rw [hind, bernoulliDesign_E_prod]
  rw [Fintype.prod_sum_type]
  have hterm : (∏ a : TermAddr q M d g r0 n0,
      (tableParameter p (Sum.inr a) * F (Sum.inr a) true +
        (1 - tableParameter p (Sum.inr a)) * F (Sum.inr a) false)) = 1 := by
    simp [F]
  rw [hterm, mul_one, Fintype.prod_sigma]
  have hfactor (e : NondefaultEdge M d) :
      (∏ j : Fin (gridResolution q (windowEnd q M d g r0 n0 e.val)),
        (tableParameter p (Sum.inl ⟨e, j⟩) * F (Sum.inl ⟨e, j⟩) true +
          (1 - tableParameter p (Sum.inl ⟨e, j⟩)) * F (Sum.inl ⟨e, j⟩) false)) = 1 / 2 := by
    rw [Finset.prod_eq_single (gridKeyFin q (windowEnd q M d g r0 n0 e.val) x)]
    · cases hξ : ξ e <;> norm_num [F, tableParameter, hξ]
    · intro j _ hj
      norm_num [F, tableParameter, hj]
    · simp
  simp_rw [hfactor]
  simp


-- @node: atomEvent_probability_pos
/-- For [center x](hyp:x) and [Boolean edge vector ξ](hyp:ξ),
[the exposure atom specified by ξ has strictly positive probability under the table law](goal). -/
lemma atomEvent_probability_pos (x : ℝ) (ξ : NondefaultEdge M d → Bool) :
    0 < (tableLaw q M d g r0 n0 p).Pr (atomEvent q M d g r0 n0 x ξ) := by
  rw [atomEvent_probability]
  positivity

-- @node: def:first-default
/-- In a tree with [branching number M](hyp:M) and [depth d](hyp:d), assuming
[M is at least two](hyp:hM), the [first default-choice vertex](goal)
is the first internal vertex along the root walk using [Boolean edge assignment ξ](hyp:ξ)
where the default child is chosen, or no vertex if that never occurs.
The [ratio argument](hyp:_q), [gap argument](hyp:_g), [base-length argument](hyp:_r0),
and [center argument](hyp:_x) do not affect this walk once ξ is fixed. -/
noncomputable def firstDefault (_q : ℝ) (M d _g _r0 : ℕ) (hM : BranchingDomain M) (_x : ℝ)
    (ξ : NondefaultEdge M d → Bool) : Option (InternalVertex M d) :=
      -- @realizes U(first internal vertex choosing the default child)
  (walkVertices hM ξ d (root M d)).findSome? (fun v =>
    if hv : v.1.val < d then
      if chooseChild hM ξ ⟨v, hv⟩ = defaultChild hM then some ⟨v, hv⟩ else none
    else none)

-- @node: route_eq_of_atomEvent
/-- Assuming [the branching number is at least two](hyp:hM), for [center x](hyp:x),
[Boolean edge assignment ξ](hyp:ξ), and [table outcome ω](hyp:ω), if
[the selector bits exposed at x in ω agree with ξ](hyp:hω), then
[the leaf reached by routing x through ω is the last vertex of the depth-d walk
from the root using ξ](goal). -/
lemma route_eq_of_atomEvent (hM : BranchingDomain M) (x : ℝ) (ξ : NondefaultEdge M d → Bool)
    (ω : Outcome q M d g r0 n0) (hω : atomEvent q M d g r0 n0 x ξ ω) :
    (route hM ω x).val = (walkVertices hM ξ d (root M d)).getLast (walkVertices_ne_nil hM ξ d
      (root M d)) := by
  have hvalues : exposedValues ω x = ξ := funext hω
  simp only [route, routeFrom, hvalues]

/-- For [geometric ratio q](hyp:q), [branching number M](hyp:M), [tree depth d](hyp:d),
[window gap g](hyp:g), [base length r0](hyp:r0), and [starting index n0](hyp:n0), assuming
[M is at least two](hyp:hM), the [no-default event](goal) holds for [table outcome ω](hyp:ω)
when the root walk determined by the selector bits exposed at [center x](hyp:x)
never chooses a default child. -/
noncomputable def noDefaultEvent (q : ℝ) (M d g r0 n0 : ℕ) (hM : BranchingDomain M) (x : ℝ)
    (ω : Outcome q M d g r0 n0) : Prop := firstDefault q M d g r0 hM x (exposedValues ω x) = none

-- @node: def:no-default
/-- For [geometric ratio q](hyp:q), [branching number M](hyp:M), [tree depth d](hyp:d),
[window gap g](hyp:g), [base length r0](hyp:r0), [starting index n0](hyp:n0), and
[terminal-entry probability p](hyp:p), assuming [M is at least two](hyp:hM), the
[no-default probability identity](goal) asserts that the table-law probability of
never choosing a default child at [center x](hyp:x) equals the d-th power of
one minus two raised to the power one minus M. -/
def NoDefaultProbability (q : ℝ) (M d g r0 n0 : ℕ) (p : ℝ)
    (hM : BranchingDomain M) (x : ℝ) : Prop :=
  (tableLaw q M d g r0 n0 p).Pr (noDefaultEvent q M d g r0 n0 hM x) =
    (1 - (2 : ℝ) ^ (1 - (M : ℤ))) ^ d

end Papers.OaiGeometricErdosSimilarity

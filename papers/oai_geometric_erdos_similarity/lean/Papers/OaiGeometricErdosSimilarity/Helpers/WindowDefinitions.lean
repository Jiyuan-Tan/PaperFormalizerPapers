module
public import Papers.OaiGeometricErdosSimilarity.Basic
public import Mathlib.Data.List.Lex
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Finset.Lattice.Fold

/-! # The complete ordered tree and its preorder windows -/

@[expose] public section

namespace Papers.OaiGeometricErdosSimilarity

open scoped BigOperators
attribute [local instance] Classical.propDecidable

-- @env: S2
variable {M d : ℕ} (q : ℝ) (g r0 : ℕ) {n0 : ℕ}

-- @node: def:ordered-tree
/-- For [a branching count M](hyp:M) and [maximum depth d](hyp:d), [the tree's
vertices](goal) are finite paths of length at most d, with each entry choosing
one of M children. -/
abbrev TreeVertex (M d : ℕ) := Σ k : Fin (d + 1), Fin k.val → Fin M
  -- @realizes P(vertices are bounded finite paths)

/-- In the tree with [M children per vertex](hyp:M) and [maximum depth d](hyp:d),
[the internal vertices](goal) are the vertices whose depth is strictly below d. -/
abbrev InternalVertex (M d : ℕ) := {v : TreeVertex M d // v.1.val < d}
  -- @realizes P(internal vertices have depth below d)

/-- In the tree with [branching count M](hyp:M) and [maximum depth d](hyp:d),
[an edge](goal) is represented by its child vertex, whose path is nonempty. -/
abbrev TreeEdge (M d : ℕ) := {v : TreeVertex M d // 1 ≤ v.1.val}
  -- @realizes e(edge represented by its nonempty child path)

/-- In the tree with [branching count M](hyp:M) and [maximum depth d](hyp:d),
[the leaves](goal) are the vertices at depth exactly d. -/
abbrev Leaf (M d : ℕ) := {v : TreeVertex M d // v.1.val = d} -- @realizes L(leaf paths of depth d)

/-- For [a vertex v](hyp:v) in the tree with [branching count M](hyp:M) and
[maximum depth d](hyp:d), [its height](goal) is d minus its depth. -/
def vertexHeight (v : TreeVertex M d) : ℕ := d - v.1.val -- @realizes h(height is d minus depth)

/-- For [branching count M](hyp:M) and [maximum depth d](hyp:d), [the root](goal)
is the vertex represented by the empty path. -/
def root (M d : ℕ) : TreeVertex M d := ⟨⟨0, Nat.zero_lt_succ d⟩, Fin.elim0⟩

-- @node: child_depth_lt
/-- For an internal vertex U, [its depth plus one is strictly less than the
maximum depth plus one](goal). -/
lemma child_depth_lt (U : InternalVertex M d) : U.val.1.val + 1 < d + 1 := by
  exact Nat.succ_lt_succ U.property

/-- In the tree with [branching count M](hyp:M) and [maximum depth d](hyp:d),
for [an internal vertex U](hyp:U) and [a child index i](hyp:i), [the selected
child](goal) is obtained by appending i to U's path. -/
def child (U : InternalVertex M d) (i : Fin M) : TreeVertex M d :=
  -- @realizes P_i(append child index to parent path)
  -- @realizes i(Fin M uses zero-based encoding of children 1 through M)
  ⟨⟨U.val.1.val + 1, child_depth_lt U⟩, Fin.lastCases i U.val.2⟩

/-- In the tree with [branching count M](hyp:M) and [maximum depth d](hyp:d),
for [an internal vertex U](hyp:U) and [a child index i](hyp:i), [the corresponding
edge](goal) joins U to its child indexed by i. -/
def childEdge (U : InternalVertex M d) (i : Fin M) : TreeEdge M d :=
  ⟨child U i, Nat.succ_le_succ (Nat.zero_le _)⟩

-- @node: lastIndex_lt
/-- For any edge e, [the depth of its child vertex minus one is strictly less
than that child's depth](goal). -/
lemma lastIndex_lt (e : TreeEdge M d) : e.val.1.val - 1 < e.val.1.val := by
  exact Nat.sub_lt e.property (by decide)

/-- For [an edge e](hyp:e) in the tree with [branching count M](hyp:M) and
[maximum depth d](hyp:d), [its child index](goal) is the last entry in the path
of its child vertex, using indices starting at zero. -/
def childIndex (e : TreeEdge M d) : Fin M := e.val.2 ⟨e.val.1.val - 1, lastIndex_lt e⟩

/-- For [an edge e](hyp:e) in the tree with [branching count M](hyp:M) and
[maximum depth d](hyp:d), [its source height](goal) is d plus one minus the
depth of its child vertex. -/
def sourceHeight (e : TreeEdge M d) : ℕ := d + 1 - e.val.1.val

/-- For [branching count M](hyp:M) and [maximum depth d](hyp:d), [the nondefault
edges](goal) are those whose child index is not the last of the M choices. -/
abbrev NondefaultEdge (M d : ℕ) := {e : TreeEdge M d // (childIndex e).val + 1 < M}

/-- For [a vertex v](hyp:v) in the tree with [branching count M](hyp:M) and
[maximum depth d](hyp:d), [its path list](goal) lists its child choices in
order from the root. -/
def vertexPath (v : TreeVertex M d) : List (Fin M) := List.ofFn v.2

-- @node: vertexPath_injective
/-- [Two vertices with the same path list are equal](goal). -/
lemma vertexPath_injective : Function.Injective (vertexPath (M := M) (d := d)) := by
  rintro ⟨⟨k, hk⟩, f⟩ ⟨⟨l, hl⟩, g⟩ h
  have hkl : k = l := by
    have := congrArg List.length h
    simpa [vertexPath] using this
  subst l
  have hfg : f = g := List.ofFn_injective h
  subst g
  rfl

/-- For [edges e](hyp:e) and [f](hyp:f) in the tree with [branching count M](hyp:M)
and [maximum depth d](hyp:d), [e precedes f in preorder](goal) when e's path
comes before f's in lexicographic order, with a proper prefix coming first. -/
def preorderLt (e f : TreeEdge M d) : Prop := List.Lex (· < ·) (vertexPath e.val) (vertexPath f.val)

/-- For [edges f](hyp:f) and [e](hyp:e) in the tree with [branching count M](hyp:M)
and [maximum depth d](hyp:d), [f is the immediate predecessor of e](goal) when
[f precedes e in preorder](step:1) and [no edge lies strictly between them in
that order](step:2). -/
def IsPredecessor (f e : TreeEdge M d) : Prop :=
  preorderLt f e ∧ ¬ ∃ a : TreeEdge M d, preorderLt f a ∧ preorderLt a e

/-- For [edges e](hyp:e) and [f](hyp:f) in the tree with [branching count M](hyp:M)
and [maximum depth d](hyp:d), [f is a descendant of e or e itself](goal) when
the path of e is a prefix of the path of f. -/
def IsDescendantOrSelf (e f : TreeEdge M d) : Prop := (vertexPath e.val).IsPrefix (vertexPath f.val)

/-- For [branching count M](hyp:M) and [maximum depth d](hyp:d), [the edge
count](goal) is the total number of edges in the finite tree. -/
noncomputable def edgeCount (M d : ℕ) : ℕ := Fintype.card (TreeEdge M d)
  -- @realizes K(total edge count)

/-- For [branching count M](hyp:M), [gap g](hyp:g), and [base length r0](hyp:r0),
[the window-length and subtree-span pair at each height](goal) is defined by
[the pair (r0, 0) at height zero](step:1), [the pair (r0, M times r0 plus
(M minus one) times g) at height one](step:2), and [at each later height, a
length equal to the larger of r0 and g plus the previous span, and a span
equal to M times the sum of this length, g, and the previous span, plus
(M minus one) times g](step:3). -/
def windowData (M g r0 : ℕ) : ℕ → ℕ × ℕ
  | 0 => (r0, 0)
  | 1 => (r0, M * r0 + (M - 1) * g)
  | h + 2 =>
    let σ := (windowData M g r0 (h + 1)).2
    let r := max r0 (g + σ)
    (r, M * (r + g + σ) + (M - 1) * g)

/-- For [branching count M](hyp:M), [gap g](hyp:g), [base length r0](hyp:r0),
and [height h](hyp:h), [the window length](goal) is the length component of
the recursive window data at height h. -/
def windowLength (M g r0 h : ℕ) : ℕ := (windowData M g r0 h).1
  -- @realizes r_h(recursive length from height h)

/-- For [branching count M](hyp:M), [gap g](hyp:g), [base length r0](hyp:r0),
and [height h](hyp:h), [the subtree span](goal) is the span component of the
recursive window data at height h. -/
def subtreeSpan (M g r0 h : ℕ) : ℕ := (windowData M g r0 h).2
  -- @realizes \sigma_h(recursive span of subtree windows and gaps)

-- @node: baseLength_le_windowLength
/-- [The window length at every height is at least the base length](goal). -/
lemma baseLength_le_windowLength (M g r0 h : ℕ) : r0 ≤ windowLength M g r0 h := by
  rcases h with _ | h
  · exact Nat.le_refl _
  rcases h with _ | h
  · exact Nat.le_refl _
  · exact le_max_left _ _

-- @node: windowLength_pos
/-- If [the base length is at least one](hyp:hr), then [the window length at
every height is at least one](goal). -/
lemma windowLength_pos (M g r0 h : ℕ) (hr : BaseLengthDomain r0) :
    1 ≤ windowLength M g r0 h := by
  exact le_trans hr (baseLength_le_windowLength M g r0 h)


-- @node: gap_add_subtreeSpan_le_windowLength
/-- If [h is at least two](hyp:hh), then [the gap plus the subtree span at
height h minus one is at most the window length at height h](goal). -/
lemma gap_add_subtreeSpan_le_windowLength (M g r0 h : ℕ) (hh : 2 ≤ h) :
    g + subtreeSpan M g r0 (h - 1) ≤ windowLength M g r0 h := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hh
  simpa [windowLength, subtreeSpan, windowData, Nat.add_comm] using
    (le_max_right r0 (g + (windowData M g r0 (k + 1)).2))

/-- For [a real scaling factor q](hyp:q), [the chosen initial index](goal) is
one plus the nonnegative integer ceiling of the ratio of the logarithm of
one eighth to the logarithm of q. -/
noncomputable def firstIndex (q : ℝ) : ℕ := ⌈Real.log (1 / 8) / Real.log q⌉₊ + 1
  -- A witness for the internal choice in the periodic construction.

-- @node: firstIndex_spec
/-- If [q lies strictly between zero and one](hyp:hq), then [the chosen initial
index is at least one and twice q raised to that index is at most one
quarter](goal). -/
lemma firstIndex_spec (hq : QDomain q) : 1 ≤ firstIndex q ∧ 2 * q ^ firstIndex q ≤ 1 / 4 := by
  have hn : 1 ≤ firstIndex q := by
    unfold firstIndex
    omega
  have hceil : Real.log (1 / 8) / Real.log q ≤ (firstIndex q : ℝ) := by
    exact le_trans (Nat.le_ceil _) (by
      simp only [firstIndex, Nat.cast_add, Nat.cast_one]
      linarith)
  have hlogq : Real.log q < 0 := Real.log_neg hq.1 hq.2
  have hlog := (div_le_iff_of_neg hlogq).mp hceil
  have hpow : q ^ firstIndex q ≤ (1 / 8 : ℝ) := by
    apply (Real.log_le_log_iff (pow_pos hq.1 _) (by norm_num)).mp
    rw [Real.log_pow]
    exact hlog
  exact ⟨hn, by linarith⟩

/-- For [an initial index n0](hyp:n0), [the window-start domain condition](goal)
requires n0 to be at least one.

The window formulas extend to zero only for internal constructions. -/
def WindowStartDomain (n0 : ℕ) : Prop :=
  1 ≤ n0 -- @realizes a_e(positive-start domain; every window start is at least n0)
    -- @realizes n_0(positive initial index)

-- @node: def:windows
/-- For [a real scaling parameter q](hyp:_q), [branching count M](hyp:M),
[maximum depth d](hyp:d), [gap g](hyp:g), [base length r0](hyp:r0),
[initial index n0](hyp:n0), and [edge e](hyp:e), [the window start](goal) is
n0 plus the sum of each preceding edge's window length and gap g in preorder. -/
noncomputable def windowStart (_q : ℝ) (M d g r0 : ℕ)
    (n0 : ℕ) -- @realizes n_0(natural carrier; positive range via WindowStartDomain)
    (e : TreeEdge M d) : ℕ :=
  -- @realizes a_e(natural carrier; positive range via WindowStartDomain)
  n0 + ∑ f ∈ Finset.univ.filter (fun f : TreeEdge M d => preorderLt f e),
    (windowLength M g r0 (sourceHeight f) + g)

-- @node: windowStart_positive
/-- If [the initial index is at least one](hyp:hn0), then [every edge's window
start is at least one](goal). -/
lemma windowStart_positive (hn0 : WindowStartDomain n0) (e : TreeEdge M d) :
    1 ≤ windowStart q M d g r0 n0 e := by
  change 1 ≤ n0 at hn0
  unfold windowStart
  exact hn0.trans (Nat.le_add_right _ _)

-- @realizes b_e(inclusive endpoint; positive under windowEnd_positive domains)
/-- For [scaling parameter q](hyp:q), [branching count M](hyp:M),
[maximum depth d](hyp:d), [gap g](hyp:g), [base length r0](hyp:r0),
[initial index n0](hyp:n0), and [edge e](hyp:e), [the inclusive window
endpoint](goal) is its start plus its length minus one, with subtraction
truncated at zero. -/
noncomputable def windowEnd (q : ℝ)
    (M d g r0 n0 : ℕ) (e : TreeEdge M d) : ℕ :=
  -- @realizes b_f(natural carrier; positive range via windowEnd_positive)
  windowStart q M d g r0 n0 e + windowLength M g r0 (sourceHeight e) - 1

-- @node: windowEnd_positive
/-- If [the base length is at least one](hyp:hr) and [the initial index is at
least one](hyp:hn0), then [every edge's inclusive window endpoint is at least
one](goal).

The endpoint formula extends to other parameters solely for internal constructions. -/
lemma windowEnd_positive
    (hr : BaseLengthDomain r0) -- @realizes b_e(positive base-length domain)
      -- @realizes b_f(positive base-length domain)
    (hn0 : 1 ≤ n0) -- @realizes b_e(positive starting-index domain)
      -- @realizes b_f(positive starting-index domain)
    (e : TreeEdge M d) :
    1 ≤ windowEnd q M d g r0 n0 e := by
  have hlen := windowLength_pos M g r0 (sourceHeight e) hr
  have hstart : n0 ≤ windowStart q M d g r0 n0 e := by
    unfold windowStart
    exact Nat.le_add_right _ _
  unfold windowEnd
  omega

/-- For [scaling parameter q](hyp:q), [branching count M](hyp:M),
[maximum depth d](hyp:d), [gap g](hyp:g), [base length r0](hyp:r0),
[initial index n0](hyp:n0), and [edge e](hyp:e), [the edge's window set](goal)
contains all natural-number indices from its start to its endpoint, inclusive. -/
noncomputable def windowSet (q : ℝ) (M d g r0 n0 : ℕ) (e : TreeEdge M d) : Finset ℕ :=
  -- @realizes W_e(finite inclusive integer interval)
  Finset.Icc (windowStart q M d g r0 n0 e) (windowEnd q M d g r0 n0 e)

/-- For [scaling parameter q](hyp:q), [branching count M](hyp:M),
[maximum depth d](hyp:d), [gap g](hyp:g), [base length r0](hyp:r0), and
[initial index n0](hyp:n0), [the index set](goal) is the union of the windows
of all edges in the tree. -/
noncomputable def indexSet (q : ℝ) (M d g r0 n0 : ℕ) : Finset ℕ :=
  -- @realizes \mathcal N(finite union of all edge windows)
  Finset.univ.biUnion (windowSet q M d g r0 n0)

-- @node: def:block-endpoint
/-- For [scaling parameter q](hyp:q), [branching count M](hyp:M),
[maximum depth d](hyp:d), [gap g](hyp:g), [base length r0](hyp:r0),
[initial index n0](hyp:n0), and [edge e](hyp:e), [the block endpoint](goal) is
the largest window endpoint among e and all its descendant edges. -/
noncomputable def blockEndpoint (q : ℝ) (M d g r0 n0 : ℕ) (e : TreeEdge M d) : ℕ :=
  -- @realizes b_e^*(largest endpoint; positive range via blockEndpoint_positive)
  (Finset.univ.filter (IsDescendantOrSelf e)).sup (windowEnd q M d g r0 n0)

-- @node: blockEndpoint_positive
/-- If [the base length is at least one](hyp:hr) and [the initial index is at
least one](hyp:hn0), then [every edge's block endpoint is at least one](goal).

The edge itself belongs to its block. Values outside this domain are internal extensions. -/
lemma blockEndpoint_positive
    (hr : BaseLengthDomain r0) -- @realizes b_e^*(positive base-length domain)
    (hn0 : 1 ≤ n0) -- @realizes b_e^*(positive starting-index domain)
    (e : TreeEdge M d) :
    1 ≤ blockEndpoint q M d g r0 n0 e := by
  apply (windowEnd_positive q g r0 hr hn0 e).trans
  apply Finset.le_sup
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ e, by simp [IsDescendantOrSelf]⟩

-- @node: ass:stable-center-condition
/-- For [scaling parameter q](hyp:q), [branching count M](hyp:M),
[maximum depth d](hyp:d), [gap g](hyp:g), [base length r0](hyp:r0),
[initial index n0](hyp:n0), and [a real center x](hyp:x), [the stable-center
condition](goal) requires [the base length to be at least one](step:1),
[the initial index to be at least one](step:2), and [for each edge with an
immediate preorder predecessor, the interval open at x and closed at x plus
twice q raised to the edge's window start to contain no point of the grid
lattice at the predecessor's window endpoint](step:3). -/
def StableCenterCondition (q : ℝ) (M d g r0 n0 : ℕ) (x : ℝ) : Prop :=
  BaseLengthDomain r0 ∧ -- @realizes b'(positive base-length domain of predecessor endpoint)
  WindowStartDomain n0 ∧ -- @realizes a_e(positive-start domain in the standing window setup)
    -- @realizes b'(positive starting-index domain of predecessor endpoint)
  ∀ e f : TreeEdge M d, IsPredecessor f e → -- @realizes f(preorder predecessor)
    Set.Ioc x (x + 2 * q ^ windowStart q M d g r0 n0 e) ∩
      gridLattice q (windowEnd q M d g r0 n0 f) = ∅ -- @realizes b'(predecessor endpoint)

-- @node: ass:window-span-height
/-- In the tree with [branching count M](hyp:M) and [maximum depth d](hyp:d),
for [an edge e](hyp:e) and [a height h](hyp:h), [the window-span height
condition](goal) says that e's source height equals h. -/
def WindowSpanHeight (e : TreeEdge M d) (h : ℕ) : Prop := sourceHeight e = h

-- @node: ass:separation-parameters
/-- For [a real dilation t](hyp:t), [the separation-parameter condition](goal)
requires t to lie between one and two, inclusive. -/
def SeparationParameters (t : ℝ) : Prop := t ∈ Set.Icc (1 : ℝ) 2
  -- @realizes t(normalized dilation in [1,2])

-- @node: def:stable-centers
/-- For [scaling parameter q](hyp:q), [branching count M](hyp:M),
[maximum depth d](hyp:d), [gap g](hyp:g), [base length r0](hyp:r0),
[initial index n0](hyp:n0), and [a real center x](hyp:x), [being a stable
center](goal) means that [x satisfies the stable-center condition for these
parameters](hyp:stable). -/
structure IsStableCenter (q : ℝ) (M d g r0 n0 : ℕ) (x : ℝ) : Prop where
  stable : StableCenterCondition q M d g r0 n0 x -- @realizes x(stable center condition)

/-- For [scaling parameter q](hyp:q), [branching count M](hyp:M),
[maximum depth d](hyp:d), [gap g](hyp:g), [base length r0](hyp:r0), and
[initial index n0](hyp:n0), [the stable set](goal) consists of all real centers
that satisfy the stable-center condition for these parameters. -/
def stableSet (q : ℝ) (M d g r0 n0 : ℕ) : Set ℝ := {x | IsStableCenter q M d g r0 n0 x}
  -- @realizes \mathcal S(set of stable centers)

end Papers.OaiGeometricErdosSimilarity

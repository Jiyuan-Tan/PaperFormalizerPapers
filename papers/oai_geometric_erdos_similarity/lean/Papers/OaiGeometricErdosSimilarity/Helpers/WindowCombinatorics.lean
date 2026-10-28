module
public import Papers.OaiGeometricErdosSimilarity.Helpers.WindowDefinitions

/-! # Weighted preorder blocks and complete subtrees -/

@[expose] public section

namespace Papers.OaiGeometricErdosSimilarity

open scoped BigOperators
attribute [local instance] Classical.propDecidable

-- @node: appendSubtreeVertex
/-- For [an edge e](hyp:e) and [a vertex v in the tree of remaining depth below e](hyp:v),
[the extended edge](goal) is obtained by appending the path of v to the path of e. -/
def appendSubtreeVertex {M d : ℕ} (e : TreeEdge M d)
    (v : TreeVertex M (d - e.val.1.val)) : TreeEdge M d :=
  ⟨⟨⟨e.val.1.val + v.1.val, by have := v.1.isLt; omega⟩,
    Fin.append e.val.2 v.2⟩, by exact e.property.trans (Nat.le_add_right _ _)⟩

-- @node: vertexPath_appendSubtreeVertex
/-- [The path of the edge obtained by extending e with v is the path of e followed by
the path of v](goal). -/
lemma vertexPath_appendSubtreeVertex {M d : ℕ} (e : TreeEdge M d)
    (v : TreeVertex M (d - e.val.1.val)) :
    vertexPath (appendSubtreeVertex e v).val = vertexPath e.val ++ vertexPath v := by
  exact List.ofFn_fin_append _ _

-- @node: appendSubtreeVertex_injective
/-- [Appending vertices below a fixed edge gives distinct edges for distinct vertices](goal). -/
lemma appendSubtreeVertex_injective {M d : ℕ} (e : TreeEdge M d) :
    Function.Injective (appendSubtreeVertex e) := by
  intro v w h
  apply vertexPath_injective
  have hp := congrArg (fun f => vertexPath f.val) h
  simpa only [vertexPath_appendSubtreeVertex, List.append_cancel_left_eq] using hp

-- @node: appendSubtreeVertex_range
/-- [An edge f is a descendant of e, including e itself, exactly when it is obtained
by appending some vertex of the remaining-depth tree to e](goal). -/
lemma appendSubtreeVertex_range {M d : ℕ} (e f : TreeEdge M d) :
    IsDescendantOrSelf e f ↔ ∃ v, appendSubtreeVertex e v = f := by
  constructor
  · rintro ⟨s, hs⟩
    have hlen : e.val.1.val + s.length = f.val.1.val := by
      have := congrArg List.length hs
      simpa only [List.length_append, vertexPath, List.length_ofFn] using this
    let v : TreeVertex M (d - e.val.1.val) :=
      ⟨⟨s.length, by have := f.val.1.isLt; omega⟩, s.get⟩
    refine ⟨v, ?_⟩
    apply Subtype.ext
    apply vertexPath_injective
    rw [vertexPath_appendSubtreeVertex]
    simpa only [vertexPath, v, List.ofFn_get] using hs
  · rintro ⟨v, rfl⟩
    exact ⟨vertexPath v, (vertexPath_appendSubtreeVertex e v).symm⟩

-- @node: subtreeLevelSum
/-- For [branching number M](hyp:M), [gap g](hyp:g), [base window length r0](hyp:r0),
and [remaining depth k](hyp:k), [the subtree level sum](goal) adds, over levels j from
zero through k, M to the power j times the sum of the height k + 1 − j window length
and the gap. -/
def subtreeLevelSum (M g r0 k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (k + 1), M ^ j * (windowLength M g r0 (k + 1 - j) + g)

-- @node: subtreeLevelSum_succ
/-- [The subtree level sum at remaining depth k + 1 equals the height k + 2 window
length plus the gap, plus M times the subtree level sum at remaining depth k](goal). -/
lemma subtreeLevelSum_succ (M g r0 k : ℕ) :
    subtreeLevelSum M g r0 (k + 1) =
      windowLength M g r0 (k + 2) + g + M * subtreeLevelSum M g r0 k := by
  unfold subtreeLevelSum
  rw [Finset.sum_range_succ']
  simp only [pow_zero, one_mul, Nat.sub_zero, pow_succ', Nat.add_sub_add_right]
  rw [Finset.mul_sum]
  simp only [mul_assoc]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  omega

-- @node: subtreeLevelSum_span
/-- If [the branching number is at least one](hyp:hM), then [M times the subtree
level sum at remaining depth k equals the height k + 1 subtree span plus the gap](goal). -/
lemma subtreeLevelSum_span (M g r0 k : ℕ) (hM : 1 ≤ M) :
    M * subtreeLevelSum M g r0 k = subtreeSpan M g r0 (k + 1) + g := by
  induction k with
  | zero =>
      have hMg : (M - 1) * g + g = M * g := by
        rw [← Nat.add_one_mul, Nat.sub_add_cancel hM]
      simp only [subtreeLevelSum, Nat.zero_add, Finset.sum_range_one, Nat.sub_zero,
        pow_zero, one_mul, windowLength, windowData, subtreeSpan, Nat.mul_add]
      omega
  | succ k ih =>
      rw [subtreeLevelSum_succ]
      rw [ih]
      have hMg : (M - 1) * g + g = M * g := by
        rw [← Nat.add_one_mul, Nat.sub_add_cancel hM]
      simp only [subtreeSpan, windowLength, windowData] at *
      nlinarith

-- @node: subtreeLevelSum_le_span
/-- If [the branching number is at least one](hyp:hM), then [the subtree level sum
at remaining depth k is at most the height k + 1 window length plus the height k
subtree span plus two gaps](goal). -/
lemma subtreeLevelSum_le_span (M g r0 k : ℕ) (hM : 1 ≤ M) :
    subtreeLevelSum M g r0 k ≤
      windowLength M g r0 (k + 1) + g + subtreeSpan M g r0 k + g := by
  cases k with
  | zero => simp [subtreeLevelSum, subtreeSpan, windowData]
  | succ k =>
      rw [subtreeLevelSum_succ, subtreeLevelSum_span M g r0 k hM]
      simp [Nat.add_assoc]

-- @node: descendant_weight_sum
/-- [Summing window length plus gap over an edge and all its descendants gives the
subtree level sum at remaining depth equal to tree depth minus the edge's child depth](goal). -/
lemma descendant_weight_sum {M d : ℕ} (g r0 : ℕ) (e : TreeEdge M d) :
    ∑ f ∈ Finset.univ.filter (IsDescendantOrSelf e),
        (windowLength M g r0 (sourceHeight f) + g) =
      subtreeLevelSum M g r0 (d - e.val.1.val) := by
  classical
  have he := e.val.1.isLt
  have hsum : (∑ v : TreeVertex M (d - e.val.1.val),
      (windowLength M g r0 (sourceHeight (appendSubtreeVertex e v)) + g)) =
      ∑ f ∈ Finset.univ.filter (IsDescendantOrSelf e),
        (windowLength M g r0 (sourceHeight f) + g) := by
    apply Finset.sum_bij (fun v _ => appendSubtreeVertex e v)
    · intro v _
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (appendSubtreeVertex_range e _).mpr ⟨v, rfl⟩⟩
    · intro v _ w _ h
      exact appendSubtreeVertex_injective e h
    · intro f hf
      obtain ⟨v, hv⟩ := (appendSubtreeVertex_range e f).mp (Finset.mem_filter.mp hf).2
      exact ⟨v, Finset.mem_univ _, hv⟩
    · intro v _
      rfl
  rw [← hsum]
  simp only [TreeVertex, Fintype.sum_sigma]
  have hheight (j : Fin (d - e.val.1.val + 1)) (v : Fin j.val → Fin M) :
      sourceHeight (appendSubtreeVertex e ⟨j, v⟩) = d - e.val.1.val + 1 - j.val := by
    change d + 1 - (e.val.1.val + j.val) = d - e.val.1.val + 1 - j.val
    have := j.isLt
    omega
  simp_rw [hheight]
  simp only [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
  exact Fin.sum_univ_eq_sum_range
    (fun j => M ^ j * (windowLength M g r0 (d - e.val.1.val + 1 - j) + g)) _

-- @node: lex_before_append_or_prefix
/-- If [a list a precedes the concatenation of b and s in lexicographic order](hyp:h),
then [a precedes b in that order or b is a prefix of a](goal). -/
lemma lex_before_append_or_prefix {α : Type*} [LinearOrder α]
    (a b s : List α) (h : List.Lex (· < ·) a (b ++ s)) :
    List.Lex (· < ·) a b ∨ b.IsPrefix a := by
  induction b generalizing a with
  | nil => exact Or.inr List.nil_prefix
  | cons c b ih =>
      cases a with
      | nil => exact Or.inl .nil
      | cons x a =>
          cases h with
          | rel h => exact Or.inl (.rel h)
          | cons h =>
              rcases ih a h with h | h
              · exact Or.inl (.cons h)
              · obtain ⟨t, rfl⟩ := h
                exact Or.inr ⟨t, rfl⟩

-- @node: prefix_not_lex_before
/-- If [a is a prefix of b](hyp:h), then [b does not strictly precede a in
lexicographic order](goal). -/
lemma prefix_not_lex_before {α : Type*} [LinearOrder α] {a b : List α}
    (h : a.IsPrefix b) : ¬ List.Lex (· < ·) b a := by
  obtain ⟨s, rfl⟩ := h
  intro h
  induction a with
  | nil => cases h
  | cons x a ih =>
      cases h with
      | rel h => exact lt_irrefl x h
      | cons h => exact ih h

-- @node: descendant_windowEnd_le_weight_sum
/-- If [the base window length is at least one](hyp:hr) and [f is a descendant of e,
possibly e itself](hyp:hf), then [the window endpoint of f plus the gap plus one is
at most the window start of e plus the sum of window length and gap over e and all
its descendants](goal). -/
lemma descendant_windowEnd_le_weight_sum {M d g r0 n0 : ℕ} (q : ℝ)
    (hr : BaseLengthDomain r0) (e f : TreeEdge M d) (hf : IsDescendantOrSelf e f) :
    windowEnd q M d g r0 n0 f + g + 1 ≤ windowStart q M d g r0 n0 e +
      ∑ a ∈ Finset.univ.filter (IsDescendantOrSelf e),
        (windowLength M g r0 (sourceHeight a) + g) := by
  classical
  let A := Finset.univ.filter (fun a : TreeEdge M d => preorderLt a e)
  let B := Finset.univ.filter (IsDescendantOrSelf e)
  let C := Finset.univ.filter (fun a : TreeEdge M d => preorderLt a f)
  let w := fun a : TreeEdge M d => windowLength M g r0 (sourceHeight a) + g
  have hdisj : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    exact prefix_not_lex_before (Finset.mem_filter.mp hb).2 (Finset.mem_filter.mp ha).2
  have hfC : f ∉ C := by
    intro hf
    exact List.lex_irrefl (fun a : Fin M => lt_irrefl a) _ (Finset.mem_filter.mp hf).2
  have hsub : insert f C ⊆ A ∪ B := by
    intro a ha
    apply Finset.mem_union.mpr
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf⟩)
    · obtain ⟨s, hs⟩ := hf
      have hlt := (Finset.mem_filter.mp ha).2
      change List.Lex (· < ·) (vertexPath a.val) (vertexPath f.val) at hlt
      rw [← hs] at hlt
      exact (lex_before_append_or_prefix _ _ _ hlt).imp
        (fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
        (fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  have hsum := Finset.sum_le_sum_of_subset hsub (f := w)
  rw [Finset.sum_insert hfC, Finset.sum_union hdisj] at hsum
  have hlen := windowLength_pos M g r0 (sourceHeight f) hr
  change windowStart q M d g r0 n0 f + windowLength M g r0 (sourceHeight f) - 1 + g + 1 ≤ _
  change n0 + ∑ a ∈ C, w a + windowLength M g r0 (sourceHeight f) - 1 + g + 1 ≤
    n0 + ∑ a ∈ A, w a + ∑ a ∈ B, w a
  change windowLength M g r0 (sourceHeight f) + g + ∑ a ∈ C, w a ≤
    ∑ a ∈ A, w a + ∑ a ∈ B, w a at hsum
  omega

-- @node: blockEndpoint_le_weight_sum
/-- If [the base window length is at least one](hyp:hr), then [the largest window
endpoint among an edge and its descendants, plus the gap plus one, is at most the
edge's window start plus the subtree level sum at its remaining depth](goal). -/
lemma blockEndpoint_le_weight_sum {M d g r0 n0 : ℕ} (q : ℝ)
    (hr : BaseLengthDomain r0) (e : TreeEdge M d) :
    blockEndpoint q M d g r0 n0 e + g + 1 ≤ windowStart q M d g r0 n0 e +
      subtreeLevelSum M g r0 (d - e.val.1.val) := by
  classical
  let S := Finset.univ.filter (IsDescendantOrSelf e)
  have he : e ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨[], by simp⟩⟩
  obtain ⟨f, hf, hmax⟩ := Finset.exists_mem_eq_sup S ⟨e, he⟩ (windowEnd q M d g r0 n0)
  have hbound := descendant_windowEnd_le_weight_sum (g := g) (n0 := n0) q hr e f
    (Finset.mem_filter.mp hf).2
  rw [descendant_weight_sum] at hbound
  change S.sup (windowEnd q M d g r0 n0) + g + 1 ≤ _
  rw [hmax]
  exact hbound

-- @node: appendBelowVertex
/-- For [an internal vertex U](hyp:U) and [a nonempty extension path v whose length
does not exceed the remaining height of U](hyp:v), [the edge below U](goal) has the
path of U followed by v. -/
def appendBelowVertex {M d : ℕ} (U : InternalVertex M d)
    (v : Σ j : Fin (vertexHeight U.val), Fin (j.val + 1) → Fin M) : TreeEdge M d :=
  ⟨⟨⟨U.val.1.val + (v.1.val + 1), by
      have hv := v.1.isLt
      have hu := U.property
      unfold vertexHeight at *
      omega⟩, Fin.append U.val.2 v.2⟩, by
      change 1 ≤ U.val.1.val + (v.1.val + 1)
      omega⟩

-- @node: vertexPath_appendBelowVertex
/-- [The path of the edge obtained by a nonempty extension below U is the path of U
followed by the extension's sequence of child indices](goal). -/
lemma vertexPath_appendBelowVertex {M d : ℕ} (U : InternalVertex M d)
    (v : Σ j : Fin (vertexHeight U.val), Fin (j.val + 1) → Fin M) :
    vertexPath (appendBelowVertex U v).val = vertexPath U.val ++ List.ofFn v.2 := by
  exact List.ofFn_fin_append _ _

-- @node: appendBelowVertex_injective
/-- [Distinct nonempty extension paths below a fixed internal vertex give distinct
edges](goal). -/
lemma appendBelowVertex_injective {M d : ℕ} (U : InternalVertex M d) :
    Function.Injective (appendBelowVertex U) := by
  rintro ⟨j, v⟩ ⟨k, w⟩ h
  have hp := congrArg (fun e => vertexPath e.val) h
  simp only [vertexPath_appendBelowVertex, List.append_cancel_left_eq] at hp
  have hjk : j = k := by
    apply Fin.ext
    have := congrArg List.length hp
    simp only [List.length_ofFn] at this
    omega
  subst k
  have hvw : v = w := List.ofFn_injective hp
  subst w
  rfl

-- @node: appendBelowVertex_range
/-- [An edge has child depth strictly greater than the depth of U and a path
extending that of U exactly when it is obtained by a nonempty extension below U](goal). -/
lemma appendBelowVertex_range {M d : ℕ} (U : InternalVertex M d) (e : TreeEdge M d) :
    (U.val.1.val < e.val.1.val ∧ (vertexPath U.val).IsPrefix (vertexPath e.val)) ↔
      ∃ v, appendBelowVertex U v = e := by
  constructor
  · rintro ⟨hdepth, s, hs⟩
    have hlen : U.val.1.val + s.length = e.val.1.val := by
      have := congrArg List.length hs
      simpa only [List.length_append, vertexPath, List.length_ofFn] using this
    have hspos : 0 < s.length := by omega
    let j : Fin (vertexHeight U.val) := ⟨s.length - 1, by
      have := e.val.1.isLt
      unfold vertexHeight
      omega⟩
    have hj : j.val + 1 = s.length := by dsimp [j]; omega
    let v : Fin (j.val + 1) → Fin M := fun i => s.get (Fin.cast hj i)
    refine ⟨⟨j, v⟩, ?_⟩
    apply Subtype.ext
    apply vertexPath_injective
    rw [vertexPath_appendBelowVertex]
    have hv : List.ofFn v = s := by
      dsimp [v]
      rw [List.ofFn_congr hj]
      simp
    rw [hv]
    exact hs
  · rintro ⟨v, rfl⟩
    refine ⟨by change U.val.1.val < U.val.1.val + (v.1.val + 1); omega, ?_⟩
    exact ⟨List.ofFn v.2, (vertexPath_appendBelowVertex U v).symm⟩

-- @node: properDescendant_weight_sum
/-- If [the branching number is at least one](hyp:hM), then [the sum of window length
plus gap over edges whose child vertices are proper descendants of U equals the
subtree span at the height of U plus one gap](goal). -/
lemma properDescendant_weight_sum {M d : ℕ} (g r0 : ℕ) (hM : 1 ≤ M)
    (U : InternalVertex M d) :
    ∑ e ∈ Finset.univ.filter (fun e : TreeEdge M d => U.val.1.val < e.val.1.val ∧
        (vertexPath U.val).IsPrefix (vertexPath e.val)),
        (windowLength M g r0 (sourceHeight e) + g) =
      subtreeSpan M g r0 (vertexHeight U.val) + g := by
  classical
  let H := vertexHeight U.val
  have hH : 1 ≤ H := by dsimp [H, vertexHeight]; omega
  have hsum : (∑ v : Σ j : Fin H, Fin (j.val + 1) → Fin M,
      (windowLength M g r0 (sourceHeight (appendBelowVertex U v)) + g)) =
      ∑ e ∈ Finset.univ.filter (fun e : TreeEdge M d => U.val.1.val < e.val.1.val ∧
        (vertexPath U.val).IsPrefix (vertexPath e.val)),
        (windowLength M g r0 (sourceHeight e) + g) := by
    apply Finset.sum_bij (fun v _ => appendBelowVertex U v)
    · intro v _
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (appendBelowVertex_range U _).mpr ⟨v, rfl⟩⟩
    · intro v _ w _ h
      exact appendBelowVertex_injective U h
    · intro e he
      obtain ⟨v, hv⟩ := (appendBelowVertex_range U e).mp (Finset.mem_filter.mp he).2
      exact ⟨v, Finset.mem_univ _, hv⟩
    · intro v _
      rfl
  rw [← hsum]
  have hheight (j : Fin H) (v : Fin (j.val + 1) → Fin M) :
      sourceHeight (appendBelowVertex U ⟨j, v⟩) = H - j.val := by
    change d + 1 - (U.val.1.val + (j.val + 1)) = d - U.val.1.val - j.val
    omega
  simp only [Fintype.sum_sigma]
  simp_rw [hheight]
  simp only [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range
    (fun j => M ^ (j + 1) * (windowLength M g r0 (H - j) + g)) H]
  have hcount : (∑ j ∈ Finset.range H,
      M ^ (j + 1) * (windowLength M g r0 (H - j) + g)) =
      M * subtreeLevelSum M g r0 (H - 1) := by
    unfold subtreeLevelSum
    rw [Nat.sub_add_cancel hH, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [pow_succ']
    exact mul_assoc _ _ _
  rw [hcount, subtreeLevelSum_span M g r0 (H - 1) hM, Nat.sub_add_cancel hH]

-- @node: strictPrefix_lex
/-- If [a is a prefix of b](hyp:hp) and [a is shorter than b](hyp:hl), then [a
strictly precedes b in lexicographic order](goal). -/
lemma strictPrefix_lex {α : Type*} [LinearOrder α] {a b : List α}
    (hp : a.IsPrefix b) (hl : a.length < b.length) : List.Lex (· < ·) a b := by
  obtain ⟨s, rfl⟩ := hp
  have hs : s ≠ [] := by intro h; simp [h] at hl
  cases s with
  | nil => contradiction
  | cons c s => simpa only [List.append_nil] using
      (List.Lex.append_left (· < ·) (List.Lex.nil (a := c) (l := s)) a)

-- @node: properDescendant_preorder_convex
/-- If [the child vertex of e is a proper descendant of U](hyp:he) and [the child
vertex of f is a proper descendant of U](hyp:hf), and [the path of e is no later
than that of a](hyp:hea) while [the path of a is no later than that of f](hyp:haf)
in lexicographic order, then [the child vertex of a is also a proper descendant of U](goal). -/
lemma properDescendant_preorder_convex {M d : ℕ} (U : InternalVertex M d)
    (e f a : TreeEdge M d)
    (he : U.val.1.val < e.val.1.val ∧ (vertexPath U.val).IsPrefix (vertexPath e.val))
    (hf : U.val.1.val < f.val.1.val ∧ (vertexPath U.val).IsPrefix (vertexPath f.val))
    (hea : vertexPath e.val ≤ vertexPath a.val)
    (haf : vertexPath a.val ≤ vertexPath f.val) :
    U.val.1.val < a.val.1.val ∧ (vertexPath U.val).IsPrefix (vertexPath a.val) := by
  rcases eq_or_lt_of_le haf with haf | haf
  · have h : a = f := Subtype.ext (vertexPath_injective haf)
    simpa [h] using hf
  obtain ⟨s, hs⟩ := hf.2
  change List.Lex (· < ·) (vertexPath a.val) (vertexPath f.val) at haf
  rw [← hs] at haf
  rcases lex_before_append_or_prefix _ _ _ haf with ha | ha
  · have hue : vertexPath U.val < vertexPath e.val :=
      strictPrefix_lex he.2 (by simpa [vertexPath] using he.1)
    have hau : vertexPath a.val < vertexPath U.val := ha
    exact False.elim (not_lt_of_ge hea (hau.trans hue))
  · refine ⟨?_, ha⟩
    have hlen := ha.length_le
    simp only [vertexPath, List.length_ofFn] at hlen
    by_contra h
    have heq : vertexPath U.val = vertexPath a.val := ha.eq_of_length (by
      simp only [vertexPath, List.length_ofFn]; omega)
    have hue : vertexPath U.val < vertexPath e.val :=
      strictPrefix_lex he.2 (by simpa [vertexPath] using he.1)
    rw [heq] at hue
    exact not_lt_of_ge hea hue

-- @node: preorder_windowEnd_mono
/-- If [the base window length is at least one](hyp:hr) and [the path of e is no
later than the path of f in lexicographic order](hyp:hef), then [the window endpoint
of e is no greater than that of f](goal). -/
lemma preorder_windowEnd_mono {M d g r0 n0 : ℕ} (q : ℝ)
    (hr : BaseLengthDomain r0) (e f : TreeEdge M d)
    (hef : vertexPath e.val ≤ vertexPath f.val) :
    windowEnd q M d g r0 n0 e ≤ windowEnd q M d g r0 n0 f := by
  classical
  rcases eq_or_lt_of_le hef with heq | hef
  · have h : e = f := Subtype.ext (vertexPath_injective heq)
    rw [h]
  let A := Finset.univ.filter (fun a : TreeEdge M d => preorderLt a e)
  let B := Finset.univ.filter (fun a : TreeEdge M d => preorderLt a f)
  let w := fun a : TreeEdge M d => windowLength M g r0 (sourceHeight a) + g
  have heA : e ∉ A := by
    intro h
    exact lt_irrefl (vertexPath e.val) (Finset.mem_filter.mp h).2
  have hsub : insert e A ⊆ B := by
    intro a ha
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact hef
    · exact lt_trans (show vertexPath a.val < vertexPath e.val from
        (Finset.mem_filter.mp ha).2) hef
  have hsum := Finset.sum_le_sum_of_subset hsub (f := w)
  rw [Finset.sum_insert heA] at hsum
  have hepos := windowLength_pos M g r0 (sourceHeight e) hr
  have hfpos := windowLength_pos M g r0 (sourceHeight f) hr
  change windowLength M g r0 (sourceHeight e) + g + ∑ a ∈ A, w a ≤ ∑ a ∈ B, w a at hsum
  change n0 + ∑ a ∈ A, w a + windowLength M g r0 (sourceHeight e) - 1 ≤
    n0 + ∑ a ∈ B, w a + windowLength M g r0 (sourceHeight f) - 1
  omega

-- @node: preorder_convex_weight_span
/-- Suppose [the base window length is at least one](hyp:hr), [S is nonempty](hyp:hS),
and [every edge lying between two members of S in lexicographic path order also
belongs to S](hyp:hconv). Then [there is an edge e in S whose window start, plus the
sum of window length and gap over S, equals the largest window endpoint in S plus
the gap plus one](goal). -/
lemma preorder_convex_weight_span {M d g r0 n0 : ℕ} (q : ℝ)
    (hr : BaseLengthDomain r0) (S : Finset (TreeEdge M d)) (hS : S.Nonempty)
    (hconv : ∀ e ∈ S, ∀ f ∈ S, ∀ a : TreeEdge M d,
      vertexPath e.val ≤ vertexPath a.val → vertexPath a.val ≤ vertexPath f.val → a ∈ S) :
    ∃ e ∈ S, S.sup (windowEnd q M d g r0 n0) + g + 1 =
      windowStart q M d g r0 n0 e +
        ∑ a ∈ S, (windowLength M g r0 (sourceHeight a) + g) := by
  classical
  obtain ⟨e, he, hemin⟩ := S.exists_min_image (fun a => vertexPath a.val) hS
  obtain ⟨f, hf, hfmax⟩ := S.exists_max_image (fun a => vertexPath a.val) hS
  let A := Finset.univ.filter (fun a : TreeEdge M d => preorderLt a e)
  let B := Finset.univ.filter (fun a : TreeEdge M d => preorderLt a f)
  let w := fun a : TreeEdge M d => windowLength M g r0 (sourceHeight a) + g
  have hfB : f ∉ B := by
    intro h
    exact lt_irrefl (vertexPath f.val) (Finset.mem_filter.mp h).2
  have hdisj : Disjoint A S := by
    apply Finset.disjoint_left.mpr
    intro a ha haS
    exact not_lt_of_ge (hemin a haS) (Finset.mem_filter.mp ha).2
  have hsets : insert f B = A ∪ S := by
    ext a
    constructor
    · intro ha
      apply Finset.mem_union.mpr
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact Or.inr hf
      have haf : vertexPath a.val < vertexPath f.val := (Finset.mem_filter.mp ha).2
      rcases lt_or_ge (vertexPath a.val) (vertexPath e.val) with hae | hea
      · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hae⟩)
      · exact Or.inr (hconv e he f hf a hea haf.le)
    · intro ha
      rcases Finset.mem_union.mp ha with ha | ha
      · apply Finset.mem_insert_of_mem
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          lt_of_lt_of_le (show vertexPath a.val < vertexPath e.val from
            (Finset.mem_filter.mp ha).2) (hfmax e he)⟩
      · rcases eq_or_lt_of_le (hfmax a ha) with haf | haf
        · have h : a = f := Subtype.ext (vertexPath_injective haf)
          exact Finset.mem_insert.mpr (Or.inl h)
        · exact Finset.mem_insert_of_mem
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _, haf⟩)
  have hsum := congrArg (fun T => ∑ a ∈ T, w a) hsets
  rw [Finset.sum_insert hfB, Finset.sum_union hdisj] at hsum
  have hsup : S.sup (windowEnd q M d g r0 n0) = windowEnd q M d g r0 n0 f := by
    apply le_antisymm
    · exact Finset.sup_le (fun a ha => preorder_windowEnd_mono q hr a f (hfmax a ha))
    · exact Finset.le_sup hf
  refine ⟨e, he, ?_⟩
  rw [hsup]
  have hlen := windowLength_pos M g r0 (sourceHeight f) hr
  change windowLength M g r0 (sourceHeight f) + g + ∑ a ∈ B, w a =
    ∑ a ∈ A, w a + ∑ a ∈ S, w a at hsum
  change n0 + ∑ a ∈ B, w a + windowLength M g r0 (sourceHeight f) - 1 + g + 1 =
    n0 + ∑ a ∈ A, w a + ∑ a ∈ S, w a
  omega

end Papers.OaiGeometricErdosSimilarity

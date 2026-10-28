module
public import Papers.OaiGeometricErdosSimilarity.Helpers.WindowCombinatorics

/-! # Window spans and separation of geometric points -/

@[expose] public section

namespace Papers.OaiGeometricErdosSimilarity

open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {M d : ℕ} (q : ℝ) (g r0 : ℕ) {n0 : ℕ}

-- @node: subtree_windows_span
/-- Suppose [q lies strictly between zero and one](hyp:hq), [the branching number
is at least two](hyp:hM), [the tree depth is positive](hyp:hd), [the gap is
positive](hyp:hg), and [the base window length is positive](hyp:hr). Then [among
edges whose child vertices are proper descendants of U, some window starts at an
index a such that the largest window endpoint plus one equals a plus the subtree
span at the height of U](goal). -/
lemma subtree_windows_span (hq : QDomain q) (hM : BranchingDomain M) (hd : DepthDomain d)
    (hg : GapDomain g) (hr : BaseLengthDomain r0) (U : InternalVertex M d) :
    let S := Finset.univ.filter (fun e : TreeEdge M d => (U.val.1.val < e.val.1.val ∧
      (vertexPath U.val).IsPrefix (vertexPath e.val)))
    ∃ a : ℕ, (∃ e ∈ S, windowStart q M d g r0 n0 e = a) ∧
      S.sup (windowEnd q M d g r0 n0) + 1 = a + subtreeSpan M g r0 (vertexHeight U.val) := by
  classical
  let S := Finset.univ.filter (fun e : TreeEdge M d => U.val.1.val < e.val.1.val ∧
    (vertexPath U.val).IsPrefix (vertexPath e.val))
  have hnonempty : S.Nonempty := by
    let i : Fin M := ⟨0, by unfold BranchingDomain at hM; omega⟩
    refine ⟨childEdge U i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    refine ⟨by change U.val.1.val < U.val.1.val + 1; omega, ?_⟩
    change (List.ofFn U.val.2).IsPrefix (List.ofFn (Fin.lastCases i U.val.2))
    rw [List.ofFn_succ_last]
    simp only [Fin.lastCases_castSucc, Fin.lastCases_last]
    exact ⟨[i], rfl⟩
  have hconv : ∀ e ∈ S, ∀ f ∈ S, ∀ a : TreeEdge M d,
      vertexPath e.val ≤ vertexPath a.val → vertexPath a.val ≤ vertexPath f.val → a ∈ S := by
    intro e he f hf a hea haf
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, properDescendant_preorder_convex U e f a
      (Finset.mem_filter.mp he).2 (Finset.mem_filter.mp hf).2 hea haf⟩
  obtain ⟨e, he, hspan⟩ := preorder_convex_weight_span (g := g) (n0 := n0)
    q hr S hnonempty hconv
  have hweight := properDescendant_weight_sum g r0
    (show 1 ≤ M by unfold BranchingDomain at hM; omega) U
  change (∑ a ∈ S, (windowLength M g r0 (sourceHeight a) + g)) =
    subtreeSpan M g r0 (vertexHeight U.val) + g at hweight
  rw [hweight] at hspan
  refine ⟨windowStart q M d g r0 n0 e, ⟨e, he, rfl⟩, ?_⟩
  change S.sup (windowEnd q M d g r0 n0) + 1 =
    windowStart q M d g r0 n0 e + subtreeSpan M g r0 (vertexHeight U.val)
  omega

-- @node: windowSet_card
/-- If [q lies strictly between zero and one](hyp:hq), [the branching number is at
least two](hyp:hM), [the tree depth is positive](hyp:hd), [the gap is positive](hyp:hg),
and [the base window length is positive](hyp:hr), then [the number of integer indices
in an edge's window equals the window length at that edge's source height](goal). -/
lemma windowSet_card (hq : QDomain q) (hM : BranchingDomain M) (hd : DepthDomain d)
    (hg : GapDomain g) (hr : BaseLengthDomain r0) (e : TreeEdge M d) :
    (windowSet q M d g r0 n0 e).card = windowLength M g r0 (sourceHeight e) := by
  have hlen := windowLength_pos M g r0 (sourceHeight e) hr
  simp only [windowSet, Nat.card_Icc, windowEnd]
  omega

-- @node: windowSet_positive
/-- Suppose [q lies strictly between zero and one](hyp:hq), [the branching number
is at least two](hyp:hM), [the tree depth is positive](hyp:hd), [the gap is
positive](hyp:hg), [the base window length is positive](hyp:hr), and [the initial
index is at least one](hyp:hn0). If [n belongs to the window of e](hyp:hn), then
[n is at least one](goal). -/
lemma windowSet_positive (hq : QDomain q) (hM : BranchingDomain M) (hd : DepthDomain d)
    (hg : GapDomain g) (hr : BaseLengthDomain r0)
    (hn0 : 1 ≤ n0) -- @realizes n_0(positive starting index)
    (e : TreeEdge M d) (n : ℕ)
    (hn : n ∈ windowSet q M d g r0 n0 e) : 1 ≤ n := by
  have hstart : windowStart q M d g r0 n0 e ≤ n := (Finset.mem_Icc.mp hn).1
  have hn0start : n0 ≤ windowStart q M d g r0 n0 e := by
    unfold windowStart
    exact Nat.le_add_right _ _
  exact le_trans hn0 (le_trans hn0start hstart)

-- @node: sourceHeight_pos
/-- [Every edge has source height at least one](goal). -/
lemma sourceHeight_pos (e : TreeEdge M d) : 1 ≤ sourceHeight e := by
  have := e.val.1.isLt
  unfold sourceHeight
  omega

-- @node: descendant_eq_of_sourceHeight_one
/-- If [e has source height one](hyp:he) and [f is a descendant of e, possibly e
itself](hyp:hf), then [f equals e](goal). -/
lemma descendant_eq_of_sourceHeight_one (e f : TreeEdge M d)
    (he : sourceHeight e = 1) (hf : IsDescendantOrSelf e f) : f = e := by
  have hed : e.val.1.val = d := by
    have := e.val.1.isLt
    unfold sourceHeight at he
    omega
  have hlen : (vertexPath e.val).length = (vertexPath f.val).length := by
    have hle := hf.length_le
    simp only [vertexPath, List.length_ofFn] at hle ⊢
    have := f.val.1.isLt
    omega
  apply Subtype.ext
  exact vertexPath_injective (hf.eq_of_length hlen).symm

-- @node: blockEndpoint_eq_windowEnd_of_sourceHeight_one
/-- If [an edge has source height one](hyp:he), then [the largest window endpoint
in its descendant block equals its own window endpoint](goal). -/
lemma blockEndpoint_eq_windowEnd_of_sourceHeight_one (e : TreeEdge M d)
    (he : sourceHeight e = 1) :
    blockEndpoint q M d g r0 n0 e = windowEnd q M d g r0 n0 e := by
  have hfilter : Finset.univ.filter (IsDescendantOrSelf e) = {e} := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · exact descendant_eq_of_sourceHeight_one e f he
    · rintro rfl
      exact ⟨[], by simp⟩
  simp only [blockEndpoint, hfilter, Finset.sup_singleton]

-- @node: blockEndpoint_span_of_sourceHeight_one
/-- If [the base window length is positive](hyp:hr) and [an edge has source height
one](hyp:he), then [its block endpoint plus one equals its window start plus the
base window length](goal). -/
lemma blockEndpoint_span_of_sourceHeight_one (hr : BaseLengthDomain r0)
    (e : TreeEdge M d) (he : sourceHeight e = 1) :
    blockEndpoint q M d g r0 n0 e + 1 = windowStart q M d g r0 n0 e + r0 := by
  rw [blockEndpoint_eq_windowEnd_of_sourceHeight_one q g r0 e he]
  have hlen : windowLength M g r0 (sourceHeight e) = r0 := by
    simp [he, windowLength, windowData]
  unfold windowEnd
  rw [hlen]
  unfold BaseLengthDomain at hr
  omega

-- @node: lem:window-span
/-- Suppose [q lies strictly between zero and one](hyp:hq), [the branching number
is at least two](hyp:hM), [the tree depth is positive](hyp:hd), [the gap is
positive](hyp:hg), and [the base window length is positive](hyp:hr). For [a height
h](hyp:h), if [the source height of e equals h](hyp:he), then [the block endpoint of
e plus one is at most its window start plus twice the window length at height h](goal). -/
lemma blockEndpoint_sub_windowStart_le (hq : QDomain q) (hM : BranchingDomain M)
    (hd : DepthDomain d) (hg : GapDomain g) (hr : BaseLengthDomain r0)
    (e : TreeEdge M d) (h : ℕ) (he : WindowSpanHeight e h) :
    blockEndpoint q M d g r0 n0 e + 1 ≤
      windowStart q M d g r0 n0 e + 2 * windowLength M g r0 h := by
  by_cases hh : h = 1
  · have he1 : sourceHeight e = 1 := he.trans hh
    rw [blockEndpoint_span_of_sourceHeight_one q g r0 hr e he1, hh]
    simp only [windowLength, windowData]
    omega
  · have hh2 : 2 ≤ h := by
      have hp := sourceHeight_pos e
      unfold WindowSpanHeight at he
      omega
    have hlength := gap_add_subtreeSpan_le_windowLength M g r0 h hh2
    suffices hspan : blockEndpoint q M d g r0 n0 e + 1 ≤
        windowStart q M d g r0 n0 e + windowLength M g r0 h +
          g + subtreeSpan M g r0 (h - 1) by
      omega
    -- Prefix convexity bounds the block by its full subtree weight;
    -- the recursive level sum is r_h + g + σ_(h-1), with one final gap removed.
    have hblock := blockEndpoint_le_weight_sum (g := g) (n0 := n0) q hr e
    have hweight := subtreeLevelSum_le_span M g r0 (d - e.val.1.val)
      (show 1 ≤ M by unfold BranchingDomain at hM; omega)
    have hsource : d - e.val.1.val + 1 = h := by
      have := e.val.1.isLt
      unfold WindowSpanHeight sourceHeight at he
      omega
    have hchildheight : d - e.val.1.val = h - 1 := by omega
    rw [hsource, hchildheight] at hweight
    rw [hchildheight] at hblock
    omega

/-- For [a center x](hyp:x), [a scale t](hyp:t), and [a geometric ratio q](hyp:q),
[the point associated with an optional index from W](goal) is [x when no index is
chosen](step:1), and [x plus t times q to the power n when index n is chosen](step:2). -/
noncomputable def sepPoint (x t q : ℝ) {W : Finset ℕ} : Option {n // n ∈ W} → ℝ
  | none => x
  | some n => x + t * q ^ n.val

-- @node: gridKey_ne_of_separated
/-- If [q lies strictly between zero and one](hyp:hq), [y minus x is at least
(1 − q) times q to the power b](hyp:hsep), and [y minus x is at most one
quarter](hyp:hshort), then [x and y have different grid keys at level b](goal). -/
lemma gridKey_ne_of_separated (hq : QDomain q) (b : ℕ) (x y : ℝ)
    (hsep : (1 - q) * q ^ b ≤ y - x) (hshort : y - x ≤ 1 / 4) :
    gridKey q b x ≠ gridKey q b y := by
  have hp := pow_pos hq.1 b
  have hq1 : 0 < 1 - q := sub_pos.mpr hq.2
  have hdelta : 0 < y - x := lt_of_lt_of_le (mul_pos hq1 hp) hsep
  have hsize := (gridSizeComparison_of_qDomain q hq b).1
  have hfour : 4 ≤ (gridResolution q b : ℝ) * ((1 - q) * q ^ b) := by
    have h := mul_le_mul_of_nonneg_right hsize (mul_pos hq1 hp).le
    rw [zpow_neg, zpow_natCast] at h
    have hid : gridConst q * (q ^ b)⁻¹ * ((1 - q) * q ^ b) = 4 := by
      unfold gridConst
      field_simp
    rwa [hid] at h
  have hN : (0 : ℝ) < gridResolution q b := by exact_mod_cast gridResolution_pos q b
  have hdist : 4 ≤ (gridResolution q b : ℝ) * (y - x) :=
    hfour.trans (mul_le_mul_of_nonneg_left hsep hN.le)
  have hNlarge : 4 ≤ (gridResolution q b : ℝ) := by nlinarith
  intro heq
  have hxlo := Nat.floor_le (mul_nonneg hN.le (Int.fract_nonneg x))
  have hylo := Nat.floor_le (mul_nonneg hN.le (Int.fract_nonneg y))
  have hxhi := Nat.lt_floor_add_one ((gridResolution q b : ℝ) * Int.fract x)
  have hyhi := Nat.lt_floor_add_one ((gridResolution q b : ℝ) * Int.fract y)
  change ⌊(gridResolution q b : ℝ) * Int.fract x⌋₊ =
    ⌊(gridResolution q b : ℝ) * Int.fract y⌋₊ at heq
  rw [heq] at hxlo hxhi
  have hfraclo : -1 < (gridResolution q b : ℝ) * (Int.fract y - Int.fract x) := by
    nlinarith
  have hfrachi : (gridResolution q b : ℝ) * (Int.fract y - Int.fract x) < 1 := by
    nlinarith
  have hxn := Int.fract_nonneg x
  have hyn := Int.fract_nonneg y
  have hxl := Int.fract_lt_one x
  have hyl := Int.fract_lt_one y
  let k : ℤ := ⌊y⌋ - ⌊x⌋
  have hk0 : 0 ≤ k := sub_nonneg.mpr (Int.floor_mono (by linarith))
  have hkcast : (k : ℝ) = y - x - (Int.fract y - Int.fract x) := by
    dsimp only [k, Int.fract]
    push_cast
    ring
  have hklt : (k : ℝ) < 2 := by linarith
  have hk1 : k ≤ 1 := by
    have : k < 2 := by exact_mod_cast hklt
    omega
  have hk : k = 0 ∨ k = 1 := by omega
  rcases hk with hk | hk
  · have : (k : ℝ) = 0 := by rw [hk]; norm_num
    nlinarith
  · have : (k : ℝ) = 1 := by rw [hk]; norm_num
    nlinarith

-- @node: lem:separation
/-- Suppose [q lies strictly between zero and one](hyp:hq), [the branching number
is at least two](hyp:hM), [the tree depth is positive](hyp:hd), [the gap is
positive](hyp:hg), [the base window length is positive](hyp:hr), [the initial index
is at least one](hyp:hn0), [twice q to the power of the initial index is at most
one quarter](hyp:hn0q), and [t lies between one and two, inclusive](hyp:ht). Then
[at every grid level b at least as large as the window endpoint of e, the center x
and the points x plus t times q to the power n for indices n in that window all
have distinct grid keys](goal). -/
lemma gridKey_injective_on_translated_window (hq : QDomain q) (hM : BranchingDomain M)
    (hd : DepthDomain d) (hg : GapDomain g) (hr : BaseLengthDomain r0)
    (hn0 : 1 ≤ n0) -- @realizes n_0(positive starting index)
    (hn0q : 2 * q ^ n0 ≤ 1 / 4) -- @realizes n_0(smallness at the supplied index)
    (e : TreeEdge M d) (x t : ℝ) (ht : SeparationParameters t) :
    ∀ b : ℕ, windowEnd q M d g r0 n0 e ≤ b →
      Function.Injective (fun u : Option {n // n ∈ windowSet q M d g r0 n0 e} =>
        gridKey q b (sepPoint x t q u)) := by
  intro b hb
  have ht1 : 1 ≤ t := ht.1
  have ht2 : t ≤ 2 := ht.2
  have hpow (n : ℕ) (hn : n ∈ windowSet q M d g r0 n0 e) :
      q ^ b ≤ q ^ n ∧ 2 * q ^ n ≤ 1 / 4 := by
    have hnI := Finset.mem_Icc.mp hn
    have hstart : n0 ≤ windowStart q M d g r0 n0 e := by
      unfold windowStart
      exact Nat.le_add_right _ _
    have hnb : n ≤ b := hnI.2.trans hb
    have hn0n : n0 ≤ n := hstart.trans hnI.1
    exact ⟨pow_le_pow_of_le_one hq.1.le hq.2.le hnb,
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one hq.1.le hq.2.le hn0n) (by norm_num)).trans hn0q⟩
  have hcenter (n : ℕ) (hn : n ∈ windowSet q M d g r0 n0 e) :
      gridKey q b x ≠ gridKey q b (x + t * q ^ n) := by
    have hp := hpow n hn
    have hpn := pow_pos hq.1 n
    apply gridKey_ne_of_separated q hq b x (x + t * q ^ n)
    · have hsmall : (1 - q) * q ^ b ≤ q ^ b := by
        nlinarith [hq.1, pow_pos hq.1 b]
      nlinarith
    · nlinarith
  have hpair (n m : ℕ) (hn : n ∈ windowSet q M d g r0 n0 e)
      (hm : m ∈ windowSet q M d g r0 n0 e) (hnm : n < m) :
      gridKey q b (x + t * q ^ m) ≠ gridKey q b (x + t * q ^ n) := by
    have hpn := pow_pos hq.1 n
    have hpm := pow_pos hq.1 m
    have hpb := pow_pos hq.1 b
    have hnp := hpow n hn
    have hmp := hpow m hm
    have hstep : q ^ m ≤ q ^ n * q := by
      simpa only [pow_succ] using
        pow_le_pow_of_le_one hq.1.le hq.2.le (Nat.succ_le_of_lt hnm)
    have hbase : (1 - q) * q ^ b ≤ (1 - q) * q ^ n :=
      mul_le_mul_of_nonneg_left hnp.1 (by linarith [hq.2])
    have hgap : (1 - q) * q ^ b ≤ q ^ n - q ^ m := by nlinarith
    have hnonneg : 0 ≤ q ^ n - q ^ m := by
      exact le_trans (mul_nonneg (sub_pos.mpr hq.2).le hpb.le) hgap
    have hscale : q ^ n - q ^ m ≤ t * (q ^ n - q ^ m) := by nlinarith
    apply gridKey_ne_of_separated q hq b (x + t * q ^ m) (x + t * q ^ n)
    · nlinarith
    · have htpos : 0 ≤ t := by linarith
      nlinarith
  intro u v huv
  cases u with
  | none =>
    cases v with
    | none => rfl
    | some m => exact False.elim (hcenter m.val m.property huv)
  | some n =>
    cases v with
    | none => exact False.elim (hcenter n.val n.property huv.symm)
    | some m =>
      have hnm : n.val = m.val := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact hpair n.val m.val n.property m.property hlt huv.symm
        · exact hpair m.val n.val m.property n.property hgt huv
      exact congrArg some (Subtype.ext hnm)

end Papers.OaiGeometricErdosSimilarity

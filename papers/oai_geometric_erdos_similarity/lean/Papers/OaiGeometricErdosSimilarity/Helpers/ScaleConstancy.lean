module
public import Papers.OaiGeometricErdosSimilarity.Helpers.ScaleDefinitions
public import Papers.OaiGeometricErdosSimilarity.Helpers.ScalePartition

/-! # Constancy of local table tests between scale boundaries -/

public section

namespace Papers.OaiGeometricErdosSimilarity

attribute [local instance] Classical.propDecidable
variable {q : ℝ} {M d g r0 n0 : ℕ}

-- @node: scaleEndpoints_mem_Icc
/-- If [q lies strictly between zero and one](hyp:hq) and [t is a scale endpoint
for U and x](hyp:ht), then [t lies between one and two, inclusive](goal). -/
lemma scaleEndpoints_mem_Icc (hq : QDomain q) (U : InternalVertex M d) (x t : ℝ)
    (ht : t ∈ scaleEndpoints (g := g) (r0 := r0) (n0 := n0) hq U x) :
    t ∈ Set.Icc (1 : ℝ) 2 := by
  rcases Finset.mem_union.mp ht with ht | ht
  · rcases Finset.mem_insert.mp ht with ht | ht
    · subst t; norm_num
    · have : t = 2 := Finset.mem_singleton.mp ht
      subst t; norm_num
  · exact ((Set.Finite.mem_toFinset _).mp ht).1

-- @node: scaleRepresentatives_mem_Icc
/-- If [q lies strictly between zero and one](hyp:hq) and [t is a representative
scale for U and x](hyp:ht), then [t lies between one and two, inclusive](goal). -/
lemma scaleRepresentatives_mem_Icc (hq : QDomain q) (U : InternalVertex M d) (x t : ℝ)
    (ht : t ∈ scaleRepresentatives (g := g) (r0 := r0) (n0 := n0) hq U x) :
    t ∈ Set.Icc (1 : ℝ) 2 :=
  endpoint_midpoints_mem_Icc _ (scaleEndpoints_mem_Icc hq U x) t ht

-- @node: subtree_walk_eq_of_fine_key_eq
/-- Assume [q lies strictly between zero and one](hyp:hq), [M is at least two](hyp:hM),
[y and z have the same grid cell at edge e's block endpoint resolution](hyp:hkey),
and [v is in the subtree rooted at e's destination](hyp:hp). Then [routing from v
for any given number of steps follows the same vertex sequence at y and z, for any
fixed table outcome](goal). -/
lemma subtree_walk_eq_of_fine_key_eq (hq : QDomain q) (hM : BranchingDomain M)
    (ω : Outcome q M d g r0 n0) (e : TreeEdge M d) (y z : ℝ)
    (hkey : gridKeyFin q (blockEndpoint q M d g r0 n0 e) y =
      gridKeyFin q (blockEndpoint q M d g r0 n0 e) z)
    (fuel : ℕ) (v : TreeVertex M d) (hp : (vertexPath e.val).IsPrefix (vertexPath v)) :
    walkVertices hM (exposedValues ω y) fuel v = walkVertices hM (exposedValues ω z) fuel v := by
  induction fuel generalizing v with
  | zero => rfl
  | succ fuel ih =>
      by_cases hv : v.1.val < d
      · have hprefix (j : Fin M) : (vertexPath e.val).IsPrefix
            (vertexPath (child ⟨v, hv⟩ j)) := by
          rw [vertexPath_child]
          exact hp.trans (List.prefix_append _ _)
        have hpred : (fun j : Fin M => if hj : j.val + 1 < M then
            exposedValues ω y (nondefaultChildEdge ⟨v, hv⟩ j hj) else false) =
            (fun j : Fin M => if hj : j.val + 1 < M then
            exposedValues ω z (nondefaultChildEdge ⟨v, hv⟩ j hj) else false) := by
          funext j
          split
          · rename_i hj
            have hb : windowEnd q M d g r0 n0 (childEdge ⟨v, hv⟩ j) ≤
                blockEndpoint q M d g r0 n0 e :=
              Finset.le_sup (f := windowEnd q M d g r0 n0)
                (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hprefix j⟩)
            have hk := gridKeyFin_eq_of_finer_eq hq hb hkey
            simp only [exposedValues, exposedAddr, nondefaultChildEdge]
            rw [hk]
          · rfl
        have hchoose : chooseChild hM (exposedValues ω y) ⟨v, hv⟩ =
            chooseChild hM (exposedValues ω z) ⟨v, hv⟩ := by
          unfold chooseChild
          rw [hpred]
        simp only [walkVertices, dif_pos hv, hchoose]
        congr 1
        exact ih _ (hprefix _)
      · simp only [walkVertices, dif_neg hv]

-- @node: subtree_leafEndpoint_le
/-- If [leaf L is in the subtree rooted at edge e's destination](hyp:hp), then
[L's endpoint is at most e's block endpoint](goal). -/
lemma subtree_leafEndpoint_le (e : TreeEdge M d) (L : Leaf M d)
    (hp : (vertexPath e.val).IsPrefix (vertexPath L.val)) :
    leafEndpoint q M d g r0 n0 L ≤ blockEndpoint q M d g r0 n0 e := by
  unfold leafEndpoint
  split
  · exact Finset.le_sup (f := windowEnd q M d g r0 n0)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩)
  · exact Nat.zero_le _

-- @node: localTest_eq_of_block_key_eq
/-- If [q lies strictly between zero and one](hyp:hq), [M is at least two](hyp:hM),
[i is a nondefault child of U](hyp:hi), and [y and z have the same grid cell at
that child's block endpoint resolution](hyp:hkey), then [the local tests at y and z
give the same result for any fixed table outcome](goal). -/
lemma localTest_eq_of_block_key_eq (hq : QDomain q) (hM : BranchingDomain M)
    (ω : Outcome q M d g r0 n0) (U : InternalVertex M d) (i : Fin M)
    (hi : i.val + 1 < M) (y z : ℝ)
    (hkey : gridKeyFin q (blockEndpoint q M d g r0 n0 (localEdge U i)) y =
      gridKeyFin q (blockEndpoint q M d g r0 n0 (localEdge U i)) z) :
    localTest hM ω U i hi y = localTest hM ω U i hi z := by
  have hwalk := subtree_walk_eq_of_fine_key_eq hq hM ω (localEdge U i) y z hkey d
    (child U i) (List.prefix_refl _)
  have hleaf : localLeaf hM ω U i y = localLeaf hM ω U i z := by
    apply Subtype.ext
    change (walkVertices hM (exposedValues ω y) d (child U i)).getLast _ =
      (walkVertices hM (exposedValues ω z) d (child U i)).getLast _
    simp only [hwalk]
  have hb : windowEnd q M d g r0 n0 (localEdge U i) ≤
      blockEndpoint q M d g r0 n0 (localEdge U i) :=
    Finset.le_sup (f := windowEnd q M d g r0 n0)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, List.prefix_refl _⟩)
  have ht := subtree_leafEndpoint_le (q := q) (g := g) (r0 := r0) (n0 := n0)
    (localEdge U i) (localLeaf hM ω U i z) (localLeaf_prefix hM ω U i z)
  unfold localTest
  rw [hleaf, gridKeyFin_eq_of_finer_eq hq ht hkey,
    gridKeyFin_eq_of_finer_eq hq hb hkey]

-- @node: scale_gap_key_eq_of_le
/-- Suppose [q lies strictly between zero and one](hyp:hq), [a is a scale endpoint
for U and x](hyp:ha), [b is also such an endpoint](hyp:hb), and [no scale endpoint lies strictly between them](hyp:hgap).
If [a is less than t](hyp:hat), [t is at most s](hyp:hts), [s is less than b](hyp:hsb),
[i is a nondefault child](hyp:hi), and [n lies in that child's local window](hyp:hn),
then [x + tqⁿ and x + sqⁿ have the same grid cell at that child's block endpoint resolution](goal). -/
lemma scale_gap_key_eq_of_le (hq : QDomain q) (U : InternalVertex M d) (x : ℝ)
    (a b : ℝ)
    (ha : a ∈ scaleEndpoints (g := g) (r0 := r0) (n0 := n0) hq U x)
    (hb : b ∈ scaleEndpoints (g := g) (r0 := r0) (n0 := n0) hq U x)
    (hgap : ¬ ∃ c ∈ scaleEndpoints (g := g) (r0 := r0) (n0 := n0) hq U x,
      a < c ∧ c < b)
    (t s : ℝ) (hat : a < t) (hts : t ≤ s) (hsb : s < b)
    (i : Fin M) (hi : i.val + 1 < M) (n : ℕ)
    (hn : n ∈ windowSet q M d g r0 n0 (localEdge U i)) :
    gridKeyFin q (blockEndpoint q M d g r0 n0 (localEdge U i)) (localPoint x t q n) =
      gridKeyFin q (blockEndpoint q M d g r0 n0 (localEdge U i)) (localPoint x s q n) := by
  have hv := pow_pos hq.1 n
  apply Fin.ext
  symm
  apply gridKey_eq_of_no_boundary q
  · dsimp [localPoint]
    nlinarith
  · apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    let c := (z - x) / q ^ n
    have htc : t < c := by
      apply (lt_div_iff₀ hv).mpr
      dsimp [localPoint] at hz
      linarith [hz.1.1]
    have hcs : c ≤ s := by
      apply (div_le_iff₀ hv).mpr
      dsimp [localPoint] at hz
      linarith [hz.1.2]
    have hac : a < c := lt_trans hat htc
    have hcb : c < b := lt_of_le_of_lt hcs hsb
    have ha' := scaleEndpoints_mem_Icc hq U x a ha
    have hb' := scaleEndpoints_mem_Icc hq U x b hb
    have hc : c ∈ scaleBreakpoints q M d g r0 n0 U x := by
      refine ⟨⟨by linarith [ha'.1], by linarith [hb'.2]⟩, (i, n),
        (mem_localIndexPairs_iff U (i, n)).mpr ⟨hi, hn⟩, ?_⟩
      have heq : localPoint x c q n = z := by dsimp [localPoint, c]; field_simp; ring
      rw [heq]
      exact hz.2
    exact hgap ⟨c, Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).mpr hc), hac, hcb⟩

-- @node: scale_gap_localTest_eq
/-- Assume [q lies strictly between zero and one](hyp:hq), [M is at least two](hyp:hM),
[a is a scale endpoint for U and x](hyp:ha), [b is also such an endpoint](hyp:hb), and [no scale endpoint
lies strictly between them](hyp:hgap). If [a is less than t](hyp:hat), [t is less
than b](hyp:htb), [a is less than s](hyp:has), [s is less than b](hyp:hsb),
[i is a nondefault child](hyp:hi), and [n lies in that child's local window](hyp:hn),
then [the local tests at x + tqⁿ and x + sqⁿ agree for any fixed table outcome](goal). -/
lemma scale_gap_localTest_eq (hq : QDomain q) (hM : BranchingDomain M)
    (U : InternalVertex M d) (x a b : ℝ)
    (ha : a ∈ scaleEndpoints (g := g) (r0 := r0) (n0 := n0) hq U x)
    (hb : b ∈ scaleEndpoints (g := g) (r0 := r0) (n0 := n0) hq U x)
    (hgap : ¬ ∃ c ∈ scaleEndpoints (g := g) (r0 := r0) (n0 := n0) hq U x,
      a < c ∧ c < b)
    (t s : ℝ) (hat : a < t) (htb : t < b) (has : a < s) (hsb : s < b)
    (ω : Outcome q M d g r0 n0) (i : Fin M) (hi : i.val + 1 < M) (n : ℕ)
    (hn : n ∈ windowSet q M d g r0 n0 (localEdge U i)) :
    localTest hM ω U i hi (localPoint x t q n) = localTest hM ω U i hi (localPoint x s q n) := by
  apply localTest_eq_of_block_key_eq hq hM
  rcases le_total t s with hts | hst
  · exact scale_gap_key_eq_of_le hq U x a b ha hb hgap t s hat hts hsb i hi n hn
  · exact (scale_gap_key_eq_of_le hq U x a b ha hb hgap s t has hst htb i hi n hn).symm

-- @node: scaleRepresentatives_cover_localTests
/-- If [q lies strictly between zero and one](hyp:hq), [M is at least two](hyp:hM),
and [t lies between one and two, inclusive](hyp:ht), then [there is a representative
scale for U and x whose local tests agree with those at t for every table outcome,
every nondefault child, and every index in that child's window](goal). -/
lemma scaleRepresentatives_cover_localTests (hq : QDomain q) (hM : BranchingDomain M)
    (U : InternalVertex M d) (x t : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) 2) :
    ∃ t' ∈ scaleRepresentatives (g := g) (r0 := r0) (n0 := n0) hq U x,
      ∀ ω : Outcome q M d g r0 n0, ∀ (i : Fin M) (hi : i.val + 1 < M),
        ∀ n ∈ windowSet q M d g r0 n0 (localEdge U i),
          localTest hM ω U i hi (localPoint x t q n) =
            localTest hM ω U i hi (localPoint x t' q n) := by
  have h1 : 1 ∈ scaleEndpoints (g := g) (r0 := r0) (n0 := n0) hq U x := by
    simp [scaleEndpoints]
  have h2 : 2 ∈ scaleEndpoints (g := g) (r0 := r0) (n0 := n0) hq U x := by
    simp [scaleEndpoints]
  obtain ⟨t', ht', heq | ⟨a, ha, b, hb, hat, htb, hat', ht'b, hgap⟩⟩ :=
    endpoint_midpoints_cover _ h1 h2 t ht
  · exact ⟨t', ht', by subst t'; intros; rfl⟩
  · exact ⟨t', ht', fun ω i hi n hn =>
      scale_gap_localTest_eq hq hM U x a b ha hb hgap t t' hat htb hat' ht'b ω i hi n hn⟩

end Papers.OaiGeometricErdosSimilarity

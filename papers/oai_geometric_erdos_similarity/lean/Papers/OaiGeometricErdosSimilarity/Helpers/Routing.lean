module
public import Papers.OaiGeometricErdosSimilarity.Helpers.LocalRouting

/-! # Stable routing and the two-stage conditional test calculation

First fix every selector, making terminal addresses deterministic and distinct. Evaluate the
terminal failure product, then average the remaining fair selector entries conditional on the
center atom. Selector-dependent terminal addresses are never treated as independent coordinates.
-/

@[expose] public section

namespace Papers.OaiGeometricErdosSimilarity

open Causalean.Experimentation.DesignBased
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {q p : ℝ} {M d g r0 n0 : ℕ}

/-- For [contraction ratio q](hyp:q), [branching number M](hyp:M), [tree depth d](hyp:d),
[gap g](hyp:g), [base length r0](hyp:r0), [starting index n0](hyp:n0), and
[internal vertex U](hyp:U), the [local pairs](goal) are the child-index and window-index
pairs belonging to U's local index set. -/
abbrev LocalPair (q : ℝ) (M d g r0 n0 : ℕ) (U : InternalVertex M d) :=
  {a // a ∈ localIndexPairs q M d g r0 n0 U}

-- @node: mem_localIndexPairs_iff
/-- [A child-index and integer-index pair belongs to U's local index set exactly when
the child is nondefault and the integer lies in that child's window](goal). -/
lemma mem_localIndexPairs_iff (U : InternalVertex M d) (a : Fin M × ℕ) :
    a ∈ localIndexPairs q M d g r0 n0 U ↔
      a.1.val + 1 < M ∧ a.2 ∈ windowSet q M d g r0 n0 (localEdge U a.1) := by
  rcases a with ⟨i, n⟩
  simp [localIndexPairs]

-- @node: localPair_nondefault
/-- [The child index of every local pair at U is strictly before the default child](goal). -/
lemma localPair_nondefault (U : InternalVertex M d) (a : LocalPair q M d g r0 n0 U) :
    a.val.1.val + 1 < M := by
  exact ((mem_localIndexPairs_iff U a.val).mp a.property).1

/-- With [ratio q](hyp:q), [branching number M](hyp:M), [depth d](hyp:d), [gap g](hyp:g),
[base length r0](hyp:r0), and [starting index n0](hyp:n0), the [selector address](goal)
for [local pair a](hyp:a) at [vertex U](hyp:U), [center x](hyp:x), and [scale t](hyp:t)
combines its nondefault child edge with the grid cell of x + t qⁿ at that edge's window end. -/
noncomputable def localSelectorAddr (U : InternalVertex M d) (x t : ℝ)
    (a : LocalPair q M d g r0 n0 U) : SelAddr q M d g r0 n0 :=
  ⟨nondefaultChildEdge U a.val.1 (localPair_nondefault U a),
    gridKeyFin q (windowEnd q M d g r0 n0 (localEdge U a.val.1)) (localPoint x t q a.val.2)⟩

/-- With [ratio q](hyp:q), [branching M](hyp:M), [depth d](hyp:d), [gap g](hyp:g),
[base length r0](hyp:r0), and [starting index n0](hyp:n0), the [local selector bit](goal)
reads [outcome ω](hyp:ω) at the selector address of [pair a](hyp:a) at [vertex U](hyp:U),
[center x](hyp:x), and [scale t](hyp:t). -/
noncomputable def localSelectorBit (ω : Outcome q M d g r0 n0) (U : InternalVertex M d)
    (x t : ℝ) (a : LocalPair q M d g r0 n0 U) : Bool :=
  ω (Sum.inl (localSelectorAddr U x t a)) -- @realizes A_{i,n}(fixed addressed selector bit)

/-- For the table with [ratio q](hyp:q), [branching M](hyp:M), [depth d](hyp:d),
[gap g](hyp:g), [base length r0](hyp:r0), and [starting index n0](hyp:n0), the
[assembled outcome](goal) uses [selector assignment σ](hyp:σ) on selector addresses
and [terminal assignment τ](hyp:τ) on terminal addresses. -/
def assembleOutcome (σ : SelAddr q M d g r0 n0 → Bool) (τ : TermAddr q M d g r0 n0 → Bool) :
    Outcome q M d g r0 n0 := Sum.elim σ τ

/-- For [ratio q](hyp:q), [branching M](hyp:M), [depth d](hyp:d), [gap g](hyp:g),
[base length r0](hyp:r0), and [starting index n0](hyp:n0), the [selector atom condition](goal)
says that [outcome ω](hyp:ω) agrees with [assignment σ](hyp:σ) at every selector address. -/
def selectorAtom (σ : SelAddr q M d g r0 n0 → Bool) (ω : Outcome q M d g r0 n0) : Prop :=
  ∀ a, ω (Sum.inl a) = σ a

/-- For [ratio q](hyp:q), [branching M](hyp:M), [depth d](hyp:d), [gap g](hyp:g),
[base length r0](hyp:r0), and [starting index n0](hyp:n0), with [M at least two](hyp:hM),
the [leaf for local pair a](goal) is reached using [selector assignment σ](hyp:σ)
from the child specified by [a](hyp:a) at [vertex U](hyp:U), evaluated at
[center x](hyp:x) plus [scale t](hyp:t) times q to the pair's window index. -/
noncomputable def localPairLeaf (hM : BranchingDomain M) (σ : SelAddr q M d g r0 n0 → Bool)
    (U : InternalVertex M d) (x t : ℝ) (a : LocalPair q M d g r0 n0 U) : Leaf M d :=
  localLeaf hM (assembleOutcome σ (fun _ => false)) U a.val.1 (localPoint x t q a.val.2)
  -- @realizes L_{i,n}(leaf fixed after all selectors are revealed)

/-- For [ratio q](hyp:q), [branching M](hyp:M), [depth d](hyp:d), [gap g](hyp:g),
[base length r0](hyp:r0), and [starting index n0](hyp:n0), with [M at least two](hyp:hM),
the [terminal address](goal) for [pair a](hyp:a) at [vertex U](hyp:U), [center x](hyp:x),
and [scale t](hyp:t) combines the leaf determined by [selector assignment σ](hyp:σ)
with the translated point's grid cell at that leaf's endpoint resolution. -/
noncomputable def localTerminalAddr (hM : BranchingDomain M) (σ : SelAddr q M d g r0 n0 → Bool)
    (U : InternalVertex M d) (x t : ℝ) (a : LocalPair q M d g r0 n0 U) : TermAddr q M d g r0 n0 :=
  ⟨localPairLeaf hM σ U x t a,
    gridKeyFin q (leafEndpoint q M d g r0 n0 (localPairLeaf hM σ U x t a))
      (localPoint x t q a.val.2)⟩
  -- @realizes \kappa_{i,n}(terminal address fixed conditional on all selectors)

/-- For [ratio q](hyp:q), [branching M](hyp:M), [depth d](hyp:d), [gap g](hyp:g),
[base length r0](hyp:r0), and [starting index n0](hyp:n0), assuming [M is at least two](hyp:hM),
the [all-tests-fail event](goal) requires [outcome ω](hyp:ω) to return false for every
nondefault child test at [vertex U](hyp:U) and every index in that child's window,
at the points given by [center x](hyp:x) and [scale t](hyp:t). -/
noncomputable def allLocalTestsFail (hM : BranchingDomain M) (U : InternalVertex M d)
    (x t : ℝ) (ω : Outcome q M d g r0 n0) : Prop :=
  ∀ (i : Fin M) (hi : i.val + 1 < M), ∀ n ∈ windowSet q M d g r0 n0 (localEdge U i),
    localTest hM ω U i hi (localPoint x t q n) = false

/-- For [ratio q](hyp:q), [branching M](hyp:M), [depth d](hyp:d), [gap g](hyp:g),
[base length r0](hyp:r0), and [starting index n0](hyp:n0), the [selector failure weight](goal)
at [vertex U](hyp:U), [center x](hyp:x), and [scale t](hyp:t) multiplies over local pairs:
each true selector bit in [outcome ω](hyp:ω) contributes one minus [terminal probability p](hyp:p),
and each false bit contributes one. -/
noncomputable def selectorFailureWeight (p : ℝ) (U : InternalVertex M d) (x t : ℝ)
    (ω : Outcome q M d g r0 n0) : ℝ :=
  ∏ a : LocalPair q M d g r0 n0 U, if localSelectorBit ω U x t a then 1 - p else 1

/-- Under [finite probability design D](hyp:D), the [conditional mean](goal) of
[real-valued quantity f](hyp:f) given [event B](hyp:B) is the mean of f restricted to B,
divided by B's probability; it is zero when B has probability zero. -/
noncomputable def condE {Ω : Type*} [Fintype Ω] (D : FiniteDesign Ω) (f : Ω → ℝ)
    (B : Ω → Prop) : ℝ := D.E (fun ω => if B ω then f ω else 0) / D.Pr B

-- @node: localEdge_sourceHeight
/-- [The source height of child i's local edge at U equals the height of U](goal). -/
lemma localEdge_sourceHeight (U : InternalVertex M d) (i : Fin M) :
    sourceHeight (localEdge U i) = vertexHeight U.val := by
  change d + 1 - (U.val.1.val + 1) = d - U.val.1.val
  omega

-- @node: nondefaultIndices_card
/-- [There are M minus one nondefault child indices among M children, with subtraction
truncated at zero](goal). -/
lemma nondefaultIndices_card (M : ℕ) :
    (Finset.univ.filter (fun i : Fin M => i.val + 1 < M)).card = M - 1 := by
  calc
    _ = (Finset.univ : Finset (Fin (M - 1))).card := by
      apply Finset.card_bij (fun i hi =>
        (⟨i.val, by have := (Finset.mem_filter.mp hi).2; omega⟩ : Fin (M - 1)))
      · intro i hi
        exact Finset.mem_univ _
      · intro i hi j hj hij
        exact Fin.ext (congrArg (fun k : Fin (M - 1) => k.val) hij)
      · intro j hj
        have hjM : j.val < M := lt_of_lt_of_le j.isLt (Nat.sub_le _ _)
        refine ⟨⟨j.val, hjM⟩, ?_, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have := j.isLt
        change j.val + 1 < M
        omega
    _ = M - 1 := Finset.card_fin _

-- @node: localIndexPairs_card
/-- If [q lies strictly between zero and one](hyp:hq), [M is at least two](hyp:hM),
[the depth is positive](hyp:hd), [the gap is positive](hyp:hg), and [the base length
is positive](hyp:hr), then [the number of local pairs at U is M minus one times U's
local window length](goal). -/
lemma localIndexPairs_card (hq : QDomain q) (hM : BranchingDomain M) (hd : DepthDomain d)
    (hg : GapDomain g) (hr : BaseLengthDomain r0) (U : InternalVertex M d) :
    (localIndexPairs q M d g r0 n0 U).card = (M - 1) * localLength M g r0 U := by
  unfold localIndexPairs
  rw [Finset.card_biUnion]
  · simp_rw [Finset.card_image_of_injective _ (fun n m h => (Prod.mk.inj h).2),
      windowSet_card q g r0 hq hM hd hg hr, localEdge_sourceHeight]
    simp [nondefaultIndices_card, localLength]
  · intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro a hai haj
    obtain ⟨n, hn, hin⟩ := Finset.mem_image.mp hai
    obtain ⟨m, hm, hjm⟩ := Finset.mem_image.mp haj
    exact hij (congrArg Prod.fst (hin.trans hjm.symm))

-- @node: childIndex_childEdge
/-- [The child index recovered from U's edge to child i is i](goal). -/
lemma childIndex_childEdge (U : InternalVertex M d) (i : Fin M) :
    childIndex (childEdge U i) = i := by
  change Fin.lastCases i U.val.2 ⟨U.val.1.val + 1 - 1, _⟩ = i
  have hlast : (⟨U.val.1.val + 1 - 1, lastIndex_lt (childEdge U i)⟩ :
      Fin (U.val.1.val + 1)) = Fin.last U.val.1.val := by
    apply Fin.ext
    simp
  rw [hlast, Fin.lastCases_last]

-- @node: localSelectorAddr_injective_and_unexposed
/-- Suppose [q is strictly between zero and one](hyp:hq), [M is at least two](hyp:hM),
[the depth is positive](hyp:hd), [the gap is positive](hyp:hg), and [the base length is positive](hyp:hr),
[n0 is at least one](hyp:hn0), [2 qⁿ⁰ is at most one quarter](hyp:hn0q),
[x satisfies the stable center condition, keeping translated windows clear of predecessor
grid boundaries](hyp:hx), and [t lies between one and two](hyp:ht).
Then [distinct local pairs at U have distinct selector addresses, and none of these
addresses is exposed at x](goal). -/
lemma localSelectorAddr_injective_and_unexposed (hq : QDomain q) (hM : BranchingDomain M)
    (hd : DepthDomain d) (hg : GapDomain g) (hr : BaseLengthDomain r0)
    (hn0 : 1 ≤ n0) -- @realizes n_0(positive starting index)
    (hn0q : 2 * q ^ n0 ≤ 1 / 4) -- @realizes n_0(smallness at the supplied index)
    (x : ℝ) (hx : StableCenterCondition q M d g r0 n0 x)
    (U : InternalVertex M d) (t : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) 2) :
    Function.Injective (localSelectorAddr (q := q) (g := g) (r0 := r0) (n0 := n0) U x t) ∧
    ∀ a : LocalPair q M d g r0 n0 U, ∀ e : NondefaultEdge M d,
      localSelectorAddr U x t a ≠ exposedAddr q M d g r0 n0 x e := by
  have hsep (i : Fin M) :=
    gridKey_injective_on_translated_window q g r0 hq hM hd hg hr hn0 hn0q
      (localEdge U i) x t ht (windowEnd q M d g r0 n0 (localEdge U i)) le_rfl
  constructor
  · rintro ⟨⟨i, n⟩, ha⟩ ⟨⟨j, m⟩, hb⟩ hab
    have hij : i = j := by
      have h := congrArg (fun a : SelAddr q M d g r0 n0 => childIndex a.1.val) hab
      simpa only [localSelectorAddr, nondefaultChildEdge, childIndex_childEdge] using h
    subst j
    have hn := ((mem_localIndexPairs_iff U (i, n)).mp ha).2
    have hm := ((mem_localIndexPairs_iff U (i, m)).mp hb).2
    have hkey := congrArg (fun a : SelAddr q M d g r0 n0 => a.2.val) hab
    have hnm : (some ⟨n, hn⟩ : Option {k // k ∈ windowSet q M d g r0 n0 (localEdge U i)}) =
        some ⟨m, hm⟩ := hsep i hkey
    apply Subtype.ext
    exact Prod.ext rfl (congrArg Subtype.val (Option.some.inj hnm))
  · intro a e hae
    have he := congrArg (fun b : SelAddr q M d g r0 n0 => b.1) hae
    change nondefaultChildEdge U a.val.1 (localPair_nondefault U a) = e at he
    subst e
    have hn := ((mem_localIndexPairs_iff U a.val).mp a.property).2
    have hkey := congrArg (fun b : SelAddr q M d g r0 n0 => b.2.val) hae
    have hbad : (some ⟨a.val.2, hn⟩ :
        Option {k // k ∈ windowSet q M d g r0 n0 (localEdge U a.val.1)}) = none :=
      hsep a.val.1 hkey
    cases hbad

-- @node: localTerminalAddr_injective
/-- Suppose [q lies strictly between zero and one](hyp:hq), [M is at least two](hyp:hM),
[the depth is positive](hyp:hd), [the gap is positive](hyp:hg), and [the base length is positive](hyp:hr),
[n0 is at least one](hyp:hn0), [2 qⁿ⁰ is at most one quarter](hyp:hn0q),
[x satisfies the stable center condition excluding predecessor grid boundaries](hyp:hx),
and [t lies between one and two](hyp:ht). For any fixed selector assignment,
[distinct local pairs at U have distinct terminal addresses](goal). -/
lemma localTerminalAddr_injective (hq : QDomain q) (hM : BranchingDomain M)
    (hd : DepthDomain d) (hg : GapDomain g) (hr : BaseLengthDomain r0)
    (hn0 : 1 ≤ n0) -- @realizes n_0(positive starting index)
    (hn0q : 2 * q ^ n0 ≤ 1 / 4) -- @realizes n_0(smallness at the supplied index)
    (x : ℝ) (hx : StableCenterCondition q M d g r0 n0 x) (U : InternalVertex M d)
    (t : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) 2) (σ : SelAddr q M d g r0 n0 → Bool) :
    Function.Injective (localTerminalAddr hM σ U x t) := by
  intro a b hab
  have hleaf : localPairLeaf hM σ U x t a = localPairLeaf hM σ U x t b :=
    congrArg Sigma.fst hab
  have hprefix (a : LocalPair q M d g r0 n0 U) :
      (vertexPath (child U a.val.1)).IsPrefix (vertexPath (localPairLeaf hM σ U x t a).val) :=
    localLeaf_prefix hM _ U a.val.1 _
  have hij : a.val.1 = b.val.1 := by
    apply child_indices_eq_of_common_leaf U a.val.1 b.val.1 (localPairLeaf hM σ U x t a)
      (hprefix a)
    rw [hleaf]
    exact hprefix b
  have hn := ((mem_localIndexPairs_iff U a.val).mp a.property).2
  have hm := ((mem_localIndexPairs_iff U b.val).mp b.property).2
  rw [← hij] at hm
  have hend : windowEnd q M d g r0 n0 (localEdge U a.val.1) ≤
      leafEndpoint q M d g r0 n0 (localPairLeaf hM σ U x t a) :=
    windowEnd_le_leafEndpoint_of_prefix hr _ _ (hprefix a)
  have hkey := congrArg (fun c : TermAddr q M d g r0 n0 => c.2.val) hab
  change gridKey q (leafEndpoint q M d g r0 n0 (localPairLeaf hM σ U x t a))
      (localPoint x t q a.val.2) =
    gridKey q (leafEndpoint q M d g r0 n0 (localPairLeaf hM σ U x t b))
      (localPoint x t q b.val.2) at hkey
  rw [← hleaf] at hkey
  have hsep := gridKey_injective_on_translated_window q g r0 hq hM hd hg hr hn0 hn0q
    (localEdge U a.val.1) x t ht _ hend
  have hnm : (some ⟨a.val.2, hn⟩ :
      Option {n // n ∈ windowSet q M d g r0 n0 (localEdge U a.val.1)}) =
      some ⟨b.val.2, hm⟩ := hsep hkey
  exact Subtype.ext (Prod.ext hij (congrArg Subtype.val (Option.some.inj hnm)))

/-- If [each Bernoulli success probability is nonnegative](hyp:hπ0) and
[at most one](hyp:hπ1), and [the selected coordinate addresses are distinct](hyp:hf),
then [the expected product of coordinate payoffs is the product of their Bernoulli
means, each success payoff weighted by its success probability and each failure payoff
by the complementary probability](goal). -/
-- @node: bernoulli_product_at_injective_addresses
lemma bernoulli_product_at_injective_addresses {C I : Type*} [Fintype C] [DecidableEq C]
    [Fintype I] (π : C → ℝ) (hπ0 : ∀ c, 0 ≤ π c) (hπ1 : ∀ c, π c ≤ 1)
    (f : I → C) (hf : Function.Injective f) (G : I → Bool → ℝ) :
    (bernoulliDesign π hπ0 hπ1).E (fun ω => ∏ i, G i (ω (f i))) =
      ∏ i, (π (f i) * G i true + (1 - π (f i)) * G i false) := by
  classical
  let F : C → Bool → ℝ := fun c b => ∏ i, if f i = c then G i b else 1
  have hF (i : I) (b : Bool) : F (f i) b = G i b := by
    dsimp only [F]
    rw [Finset.prod_eq_single i]
    · simp
    · intro j _ hji
      exact if_neg (fun h => hji (hf h))
    · simp
  have hprod (ω : C → Bool) :
      (∏ i, G i (ω (f i))) = ∏ c ∈ Finset.univ.image f, F c (ω c) := by
    rw [Finset.prod_image hf.injOn]
    exact Finset.prod_congr rfl fun i _ => (hF i _).symm
  simp_rw [hprod]
  rw [bernoulliDesign_E_prod_finset, Finset.prod_image hf.injOn]
  simp_rw [hF]

set_option maxHeartbeats 400000 in
/-- Assume [q lies strictly between zero and one](hyp:hq), [M is at least two](hyp:hM),
[the depth is positive](hyp:hd), [the gap is positive](hyp:hg), and [the base length is positive](hyp:hr),
[n0 is at least one](hyp:hn0), [2 qⁿ⁰ is at most one quarter](hyp:hn0q),
[p lies strictly between zero and one](hyp:hp), [x satisfies the stable center condition
excluding predecessor grid boundaries](hyp:hx), and [t lies between one and two](hyp:ht).
Then [conditional on all selectors equaling σ, the probability that all local tests at U
fail is the product over local pairs of 1 − p for a true selector and one for a false
selector](goal). -/
-- @node: allSelectors_failure_product
lemma allSelectors_failure_product (hq : QDomain q) (hM : BranchingDomain M)
    (hd : DepthDomain d) (hg : GapDomain g) (hr : BaseLengthDomain r0)
    (hn0 : 1 ≤ n0) -- @realizes n_0(positive starting index)
    (hn0q : 2 * q ^ n0 ≤ 1 / 4) -- @realizes n_0(smallness at the supplied index)
    (hp : TerminalProbabilityDomain p) (x : ℝ) (hx : StableCenterCondition q M d g r0 n0 x)
    (U : InternalVertex M d) (t : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) 2)
    (σ : SelAddr q M d g r0 n0 → Bool) :
    condPr (tableLaw q M d g r0 n0 p) (allLocalTestsFail hM U x t) (selectorAtom σ) =
      ∏ a : LocalPair q M d g r0 n0 U,
        if σ (localSelectorAddr U x t a) then 1 - p else 1 := by
  classical
  letI : Fintype (SelAddr q M d g r0 n0) := inferInstance
  let f : SelAddr q M d g r0 n0 ⊕ LocalPair q M d g r0 n0 U → TableAddr q M d g r0 n0 :=
    Sum.elim Sum.inl (fun a => Sum.inr (localTerminalAddr hM σ U x t a))
  have hf : Function.Injective f := by
    intro a b hab
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (Sum.inl.inj hab)
      | inr b => cases hab
    | inr a =>
      cases b with
      | inl b => cases hab
      | inr b =>
        exact congrArg Sum.inr (localTerminalAddr_injective hq hM hd hg hr hn0 hn0q x hx U t ht σ (Sum.inr.inj hab))
  let G : SelAddr q M d g r0 n0 ⊕ LocalPair q M d g r0 n0 U → Bool → ℝ :=
    Sum.elim (fun j b => if b = σ j then 1 else 0)
      (fun a b => if (σ (localSelectorAddr U x t a) && b) = false then 1 else 0)
  have hsel (ω : Outcome q M d g r0 n0) :
      (∏ j : SelAddr q M d g r0 n0, if ω (Sum.inl j) = σ j then (1 : ℝ) else 0) =
        if selectorAtom σ ω then 1 else 0 := by
    by_cases hω : selectorAtom σ ω
    · rw [if_pos hω]
      exact Finset.prod_eq_one fun j _ => if_pos (hω j)
    · rw [if_neg hω]
      obtain ⟨j, hj⟩ := not_forall.mp hω
      exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)
  have htest (ω : Outcome q M d g r0 n0) (hω : selectorAtom σ ω)
      (a : LocalPair q M d g r0 n0 U) :
      localTest hM ω U a.val.1 (localPair_nondefault U a) (localPoint x t q a.val.2) =
        (σ (localSelectorAddr U x t a) && ω (Sum.inr (localTerminalAddr hM σ U x t a))) := by
    have hvalues : exposedValues ω (localPoint x t q a.val.2) =
        exposedValues (assembleOutcome σ (fun _ => false)) (localPoint x t q a.val.2) := by
      funext e
      exact hω _
    have hleaf : localLeaf hM ω U a.val.1 (localPoint x t q a.val.2) =
        localPairLeaf hM σ U x t a := by
      simp only [localLeaf, localPairLeaf, routeFrom, hvalues]
    unfold localTest
    rw [hleaf]
    exact congrArg (fun b => b && ω (Sum.inr (localTerminalAddr hM σ U x t a))) (hω _)
  have hfail (ω : Outcome q M d g r0 n0) (hω : selectorAtom σ ω) :
      allLocalTestsFail hM U x t ω ↔ ∀ a : LocalPair q M d g r0 n0 U,
        (σ (localSelectorAddr U x t a) && ω (Sum.inr (localTerminalAddr hM σ U x t a))) = false := by
    constructor
    · intro h a
      rw [← htest ω hω a]
      exact h a.val.1 (localPair_nondefault U a) a.val.2
        ((mem_localIndexPairs_iff U a.val).mp a.property).2
    · intro h i hi n hn
      let a : LocalPair q M d g r0 n0 U := ⟨(i, n), (mem_localIndexPairs_iff U (i, n)).mpr ⟨hi, hn⟩⟩
      exact (htest ω hω a).trans (h a)
  have hind : FiniteDesign.ind (fun ω => allLocalTestsFail hM U x t ω ∧ selectorAtom σ ω) =
      fun ω => ∏ k, G k (ω (f k)) := by
    funext ω
    rw [Fintype.prod_sum_type]
    change (if allLocalTestsFail hM U x t ω ∧ selectorAtom σ ω then (1 : ℝ) else 0) =
      (∏ j, if ω (Sum.inl j) = σ j then 1 else 0) * _
    rw [hsel]
    by_cases hω : selectorAtom σ ω
    · simp only [hω, and_true, if_true, one_mul]
      rw [hfail ω hω]
      simp only [G, f, Sum.elim_inr]
      by_cases h : ∀ a : LocalPair q M d g r0 n0 U,
        (σ (localSelectorAddr U x t a) && ω (Sum.inr (localTerminalAddr hM σ U x t a))) = false
      · rw [if_pos h]
        exact (Finset.prod_eq_one fun a _ => if_pos (h a)).symm
      · rw [if_neg h]
        obtain ⟨a, ha⟩ := not_forall.mp h
        exact (Finset.prod_eq_zero (Finset.mem_univ a) (if_neg ha)).symm
    · simp [hω]
  have hfair (j : SelAddr q M d g r0 n0) :
      tableParameter p (Sum.inl j) * (if true = σ j then (1 : ℝ) else 0) +
        (1 - tableParameter p (Sum.inl j)) * (if false = σ j then 1 else 0) = 1 / 2 := by
    cases σ j <;> norm_num [tableParameter]
  have hden : (tableLaw q M d g r0 n0 p).Pr (selectorAtom σ) =
      (1 / 2 : ℝ) ^ Fintype.card (SelAddr q M d g r0 n0) := by
    have hindsel : FiniteDesign.ind (selectorAtom σ) = fun ω =>
        ∏ j : SelAddr q M d g r0 n0, if ω (Sum.inl j) = σ j then (1 : ℝ) else 0 := by
      funext ω
      exact (hsel ω).symm
    unfold tableLaw FiniteDesign.Pr
    rw [hindsel, bernoulli_product_at_injective_addresses (tableParameter p)
      (tableParameter_nonneg p) (tableParameter_le_one p)
      (fun j : SelAddr q M d g r0 n0 => (Sum.inl j : TableAddr q M d g r0 n0))
      Sum.inl_injective (fun j b => if b = σ j then 1 else 0)]
    simp_rw [hfair]
    simp
  have hterm (a : LocalPair q M d g r0 n0 U) :
      tableParameter p (f (Sum.inr a)) * G (Sum.inr a) true +
        (1 - tableParameter p (f (Sum.inr a))) * G (Sum.inr a) false =
      if σ (localSelectorAddr U x t a) then 1 - p else 1 := by
    have hclamp : max 0 (min p 1) = p := by
      rw [min_eq_left hp.2.le, max_eq_right hp.1.le]
    cases hbit : σ (localSelectorAddr U x t a) <;>
      simp [f, G, tableParameter, hclamp, hbit]
  unfold condPr
  unfold FiniteDesign.Pr
  rw [hind]
  change (bernoulliDesign (tableParameter p) (tableParameter_nonneg p)
    (tableParameter_le_one p)).E _ / _ = _
  rw [bernoulli_product_at_injective_addresses (tableParameter p)
    (tableParameter_nonneg p) (tableParameter_le_one p) f hf G, Fintype.prod_sum_type]
  simp_rw [hterm]
  have hleft : (∏ j : SelAddr q M d g r0 n0,
      (tableParameter p (f (Sum.inl j)) * G (Sum.inl j) true +
        (1 - tableParameter p (f (Sum.inl j))) * G (Sum.inl j) false)) =
        (1 / 2 : ℝ) ^ Fintype.card (SelAddr q M d g r0 n0) := by
    change (∏ j : SelAddr q M d g r0 n0,
      (tableParameter p (Sum.inl j) * (if true = σ j then (1 : ℝ) else 0) +
        (1 - tableParameter p (Sum.inl j)) * (if false = σ j then 1 else 0))) = _
    simp_rw [hfair]
    simp
  rw [hleft]
  change _ / (tableLaw q M d g r0 n0 p).Pr (selectorAtom σ) = _
  rw [hden]
  exact mul_div_cancel_left₀ _ (ne_of_gt (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) _))

/-- If [the conditional probability of A in every classifier cell i equals F at i](hyp:hF),
then [the probability of A conditional on the classifier satisfying B equals the
conditional mean of F evaluated at the classifier, given the same event](goal).

The identity also includes cells and conditioning events of probability zero. -/
-- @node: condPr_eq_condE_of_finite_fibers
lemma condPr_eq_condE_of_finite_fibers {Ω I : Type*} [Fintype Ω] [Fintype I]
    (D : FiniteDesign Ω) (A : Ω → Prop) (c : Ω → I) (B : I → Prop) (F : I → ℝ)
    (hF : ∀ i, condPr D A (fun ω => c ω = i) = F i) :
    condPr D A (fun ω => B (c ω)) = condE D (fun ω => F (c ω)) (fun ω => B (c ω)) := by
  classical
  have hcell (i : I) :
      D.Pr (fun ω => A ω ∧ c ω = i) = F i * D.Pr (fun ω => c ω = i) := by
    by_cases hi : D.Pr (fun ω => c ω = i) = 0
    · have hle := D.Pr_mono (fun ω => A ω ∧ c ω = i) (fun ω => c ω = i)
        (fun _ h => h.2)
      have hnonneg := D.Pr_nonneg (fun ω => A ω ∧ c ω = i)
      rw [hi] at hle
      rw [hi, mul_zero]
      exact le_antisymm hle hnonneg
    · exact (div_eq_iff hi).mp (hF i)
  have partition (X : Ω → ℝ) :
      D.E X = ∑ i, D.E (fun ω => if c ω = i then X ω else 0) := by
    rw [← D.E_sum]
    apply D.E_congr
    intro ω
    simp
  unfold condPr condE FiniteDesign.Pr
  congr 1
  rw [partition, partition]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hb : B i
  · calc
      _ = D.Pr (fun ω => A ω ∧ c ω = i) := by
        apply D.E_congr
        intro ω
        by_cases hc : c ω = i <;> simp [FiniteDesign.ind, hc, hb]
      _ = F i * D.Pr (fun ω => c ω = i) := hcell i
      _ = D.E (fun ω => if c ω = i then (if B (c ω) then F (c ω) else 0) else 0) := by
        rw [FiniteDesign.Pr, ← D.E_const_mul]
        apply D.E_congr
        intro ω
        by_cases hc : c ω = i <;> simp [FiniteDesign.ind, hc, hb]
  · have hleft : D.E (fun ω => if c ω = i then
          FiniteDesign.ind (fun ω => A ω ∧ B (c ω)) ω else 0) = 0 := by
        convert D.E_const 0 using 1
        apply D.E_congr
        intro ω
        by_cases hc : c ω = i <;> simp [FiniteDesign.ind, hc, hb]
    rw [hleft]
    symm
    convert D.E_const 0 using 1
    apply D.E_congr
    intro ω
    by_cases hc : c ω = i <;> simp [hc, hb]

/-- Assume [q lies strictly between zero and one](hyp:hq), [M is at least two](hyp:hM),
[the depth is positive](hyp:hd), [the gap is positive](hyp:hg), and [the base length is positive](hyp:hr),
[n0 is at least one](hyp:hn0), [2 qⁿ⁰ is at most one quarter](hyp:hn0q),
[p lies strictly between zero and one](hyp:hp), [x satisfies the stable center condition
excluding predecessor grid boundaries](hyp:hx), and [t lies between one and two](hyp:ht).
Then [conditional on the exposed bits at x equaling ξ, the probability that all local
tests at U fail equals the conditional mean of the selector failure weight](goal). -/
-- @node: failure_condPr_eq_selector_condE
lemma failure_condPr_eq_selector_condE (hq : QDomain q) (hM : BranchingDomain M)
    (hd : DepthDomain d) (hg : GapDomain g) (hr : BaseLengthDomain r0)
    (hn0 : 1 ≤ n0) -- @realizes n_0(positive starting index)
    (hn0q : 2 * q ^ n0 ≤ 1 / 4) -- @realizes n_0(smallness at the supplied index)
    (hp : TerminalProbabilityDomain p) (x : ℝ) (hx : StableCenterCondition q M d g r0 n0 x)
    (ξ : NondefaultEdge M d → Bool) (U : InternalVertex M d)
    (t : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) 2) :
    condPr (tableLaw q M d g r0 n0 p) (allLocalTestsFail hM U x t) (atomEvent q M d g r0 n0 x ξ) =
      condE (tableLaw q M d g r0 n0 p) (selectorFailureWeight p U x t) (atomEvent q M d g r0 n0 x ξ)
        := by
  classical
  letI : Fintype (SelAddr q M d g r0 n0) := inferInstance
  letI : Fintype (SelAddr q M d g r0 n0 → Bool) := inferInstance
  let c (ω : Outcome q M d g r0 n0) := fun a : SelAddr q M d g r0 n0 => ω (Sum.inl a)
  let B (σ : SelAddr q M d g r0 n0 → Bool) :=
    ∀ e, σ (exposedAddr q M d g r0 n0 x e) = ξ e
  let F (σ : SelAddr q M d g r0 n0 → Bool) :=
    ∏ a : LocalPair q M d g r0 n0 U, if σ (localSelectorAddr U x t a) then 1 - p else 1
  have hF (σ : SelAddr q M d g r0 n0 → Bool) :
      condPr (tableLaw q M d g r0 n0 p) (allLocalTestsFail hM U x t)
        (fun ω => c ω = σ) = F σ := by
    have hevent : (fun ω => c ω = σ) = selectorAtom σ := by
      funext ω
      exact propext funext_iff
    rw [hevent]
    exact allSelectors_failure_product hq hM hd hg hr hn0 hn0q hp x hx U t ht σ
  exact condPr_eq_condE_of_finite_fibers (tableLaw q M d g r0 n0 p)
    (allLocalTestsFail hM U x t) c B F hF

/-- Assume [q lies strictly between zero and one](hyp:hq), [M is at least two](hyp:hM),
[the depth is positive](hyp:hd), [the gap is positive](hyp:hg), and [the base length is positive](hyp:hr),
[n0 is at least one](hyp:hn0), [2 qⁿ⁰ is at most one quarter](hyp:hn0q),
[p lies strictly between zero and one](hyp:hp), [x satisfies the stable center condition
excluding predecessor grid boundaries](hyp:hx), and [t lies between one and two](hyp:ht).
Then [the mean selector failure weight conditional on exposed bits ξ at x is
(1 − p/2) raised to M minus one times U's local window length](goal). -/
-- @node: selector_failure_average
lemma selector_failure_average (hq : QDomain q) (hM : BranchingDomain M)
    (hd : DepthDomain d) (hg : GapDomain g) (hr : BaseLengthDomain r0)
    (hn0 : 1 ≤ n0) -- @realizes n_0(positive starting index)
    (hn0q : 2 * q ^ n0 ≤ 1 / 4) -- @realizes n_0(smallness at the supplied index)
    (hp : TerminalProbabilityDomain p) (x : ℝ) (hx : StableCenterCondition q M d g r0 n0 x)
    (ξ : NondefaultEdge M d → Bool) (U : InternalVertex M d)
    (t : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) 2) :
    condE (tableLaw q M d g r0 n0 p) (selectorFailureWeight p U x t) (atomEvent q M d g r0 n0 x ξ) =
      (1 - p / 2) ^ ((M - 1) * localLength M g r0 U) := by
  classical
  obtain ⟨hinj, hunexposed⟩ :=
    localSelectorAddr_injective_and_unexposed hq hM hd hg hr hn0 hn0q x hx U t ht
  let f : NondefaultEdge M d ⊕ LocalPair q M d g r0 n0 U → TableAddr q M d g r0 n0 :=
    Sum.elim (fun e => Sum.inl (exposedAddr q M d g r0 n0 x e))
      (fun a => Sum.inl (localSelectorAddr U x t a))
  have hf : Function.Injective f := by
    intro a b hab
    cases a with
    | inl e =>
      cases b with
      | inl e' =>
        have he := congrArg (fun c : SelAddr q M d g r0 n0 => c.1) (Sum.inl.inj hab)
        exact congrArg Sum.inl he
      | inr b => exact False.elim (hunexposed b e (Sum.inl.inj hab).symm)
    | inr a =>
      cases b with
      | inl e => exact False.elim (hunexposed a e (Sum.inl.inj hab))
      | inr b => exact congrArg Sum.inr (hinj (Sum.inl.inj hab))
  let G : NondefaultEdge M d ⊕ LocalPair q M d g r0 n0 U → Bool → ℝ :=
    Sum.elim (fun e b => if b = ξ e then 1 else 0)
      (fun _ b => if b then 1 - p else 1)
  have hind (ω : Outcome q M d g r0 n0) :
      (∏ e : NondefaultEdge M d,
        if ω (Sum.inl (exposedAddr q M d g r0 n0 x e)) = ξ e then (1 : ℝ) else 0) =
      if atomEvent q M d g r0 n0 x ξ ω then 1 else 0 := by
    by_cases hω : atomEvent q M d g r0 n0 x ξ ω
    · rw [if_pos hω]
      exact Finset.prod_eq_one fun e _ => if_pos (hω e)
    · rw [if_neg hω]
      obtain ⟨e, he⟩ := not_forall.mp hω
      exact Finset.prod_eq_zero (Finset.mem_univ e) (if_neg he)
  have hfun : (fun ω : Outcome q M d g r0 n0 =>
      if atomEvent q M d g r0 n0 x ξ ω then selectorFailureWeight p U x t ω else 0) =
      (fun ω => ∏ i, G i (ω (f i))) := by
    funext ω
    rw [Fintype.prod_sum_type]
    change _ = (∏ e, if ω (Sum.inl (exposedAddr q M d g r0 n0 x e)) = ξ e
      then (1 : ℝ) else 0) * selectorFailureWeight p U x t ω
    rw [hind]
    split <;> simp
  have hE := bernoulli_product_at_injective_addresses
    (tableParameter (q := q) (M := M) (d := d) (g := g) (r0 := r0) (n0 := n0) p)
    (tableParameter_nonneg p) (tableParameter_le_one p) f hf G
  have hfactor (i : NondefaultEdge M d ⊕ LocalPair q M d g r0 n0 U) :
      tableParameter p (f i) * G i true + (1 - tableParameter p (f i)) * G i false =
      Sum.elim (fun _ => (1 / 2 : ℝ)) (fun _ => 1 - p / 2) i := by
    cases i with
    | inl e => cases hξ : ξ e <;> norm_num [f, G, tableParameter, hξ]
    | inr a => simp [f, G, tableParameter]; ring
  simp_rw [hfactor] at hE
  rw [Fintype.prod_sum_type] at hE
  simp only [Sum.elim_inl, Sum.elim_inr, Finset.prod_const, Finset.card_univ] at hE
  have hcard : Fintype.card (LocalPair q M d g r0 n0 U) =
      (M - 1) * localLength M g r0 U := by
    exact (Fintype.card_coe _).trans (localIndexPairs_card hq hM hd hg hr U)
  rw [hcard] at hE
  unfold condE
  rw [hfun]
  change (bernoulliDesign (tableParameter p) (tableParameter_nonneg p)
    (tableParameter_le_one p)).E _ / _ = _
  rw [hE, atomEvent_probability]
  exact mul_div_cancel_left₀ _ (ne_of_gt (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) _))

-- @node: lem:independent-tests
/-- Assume [q lies strictly between zero and one](hyp:hq), [M is at least two](hyp:hM),
[the depth is positive](hyp:hd), [the gap is positive](hyp:hg), and [the base length is positive](hyp:hr),
[n0 is at least one](hyp:hn0), [2 qⁿ⁰ is at most one quarter](hyp:hn0q),
[p lies strictly between zero and one](hyp:hp), and [x satisfies the stable center condition
excluding predecessor grid boundaries](hyp:hx). If [the exposed assignment ξ has a first
default vertex](hyp:hξ), [that vertex is U](hyp:hU), [its height equals](hyp:hh)
[the integer h](hyp:h), and
[t lies between one and two](hyp:ht), then [conditional on ξ at x, the probability that
all local tests fail is (1 − p/2) raised to M minus one times the window length at height h](goal). -/
lemma condPr_forall_localTest_false_eq (hq : QDomain q) (hM : BranchingDomain M)
    (hd : DepthDomain d) (hg : GapDomain g) (hr : BaseLengthDomain r0)
    (hn0 : 1 ≤ n0) -- @realizes n_0(positive starting index)
    (hn0q : 2 * q ^ n0 ≤ 1 / 4) -- @realizes n_0(smallness at the supplied index)
    (hp : TerminalProbabilityDomain p) (x : ℝ) (hx : StableCenterCondition q M d g r0 n0 x)
    (ξ : NondefaultEdge M d → Bool) (hξ : IndependentTestsDefaultAtom q M d g r0 hM x ξ)
    (U : InternalVertex M d) (h : ℕ) (hU : firstDefault q M d g r0 hM x ξ = some U)
    (hh : vertexHeight U.val = h) (t : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) 2) :
    condPr (tableLaw q M d g r0 n0 p) (allLocalTestsFail hM U x t) (atomEvent q M d g r0 n0 x ξ) =
      (1 - p / 2) ^ ((M - 1) * windowLength M g r0 h) := by
  rw [failure_condPr_eq_selector_condE hq hM hd hg hr hn0 hn0q hp x hx ξ U t ht,
    selector_failure_average hq hM hd hg hr hn0 hn0q hp x hx ξ U t ht]
  simp only [localLength, hh]

end Papers.OaiGeometricErdosSimilarity

module
public import Papers.OaiGeometricErdosSimilarity.Helpers.DefaultProbability

/-! # Local tests and measurable periodic random sets -/

@[expose] public section

namespace Papers.OaiGeometricErdosSimilarity

open Causalean.Experimentation.DesignBased
open scoped BigOperators
open MeasureTheory
attribute [local instance] Classical.propDecidable

variable {q : ℝ} {M d g r0 n0 : ℕ} {p : ℝ}

-- @node: ass:routing-default-atom
/-- For [ratio q](hyp:q), [branching number M](hyp:M), [tree depth d](hyp:d),
[window gap g](hyp:g), [base length r0](hyp:r0), and [center x](hyp:x), assuming
[M is at least two](hyp:hM), the [routing default-atom condition](goal) says that
the root walk specified by [Boolean edge assignment ξ](hyp:ξ) chooses the default
child at some internal vertex. -/
noncomputable def RoutingDefaultAtom (q : ℝ) (M d g r0 : ℕ) (hM : BranchingDomain M) (x : ℝ)
    (ξ : NondefaultEdge M d → Bool) : Prop := (firstDefault q M d g r0 hM x ξ).isSome

-- @node: ass:independent-tests-default-atom
/-- For [ratio q](hyp:q), [branching number M](hyp:M), [tree depth d](hyp:d),
[window gap g](hyp:g), [base length r0](hyp:r0), and [center x](hyp:x), with
[M at least two](hyp:hM) and [Boolean edge assignment ξ](hyp:ξ), the
[default-atom condition for independent tests](goal) requires a default-child
choice somewhere along the root walk. -/
noncomputable def IndependentTestsDefaultAtom (q : ℝ) (M d g r0 : ℕ) (hM : BranchingDomain M) (x
  : ℝ)
    (ξ : NondefaultEdge M d → Bool) : Prop := (firstDefault q M d g r0 hM x ξ).isSome

-- @node: ass:conditional-scales-default-atom
/-- With [ratio q](hyp:q), [branching number M](hyp:M), [depth d](hyp:d),
[gap g](hyp:g), [base length r0](hyp:r0), [center x](hyp:x), and
[Boolean edge assignment ξ](hyp:ξ), assuming [M is at least two](hyp:hM), the
[default-atom condition for conditional scales](goal) requires the root walk
to choose a default child at least once. -/
noncomputable def ConditionalScalesDefaultAtom (q : ℝ) (M d g r0 : ℕ) (hM : BranchingDomain M)
  (x : ℝ)
    (ξ : NondefaultEdge M d → Bool) : Prop := (firstDefault q M d g r0 hM x ξ).isSome

-- @node: ass:conditional-scales-height
/-- For [ratio q](hyp:q), [branching number M](hyp:M), [depth d](hyp:d),
[gap g](hyp:g), [base length r0](hyp:r0), [center x](hyp:x), and
[Boolean edge assignment ξ](hyp:ξ), with [M at least two](hyp:hM), the
[conditional-scale height condition](goal) requires that [the first default
choice occurs at internal vertex U](step:1), for [the specified vertex U](hyp:U),
and that [this vertex has height h](step:2), for [height h](hyp:h). -/
noncomputable def ConditionalScalesHeight (q : ℝ) (M d g r0 : ℕ) (hM : BranchingDomain M) (x : ℝ)
    (ξ : NondefaultEdge M d → Bool) (U : InternalVertex M d) (h : ℕ) : Prop :=
  firstDefault q M d g r0 hM x ξ = some U ∧ vertexHeight U.val = h

/-- For [center x](hyp:x), [dilation t](hyp:t), [geometric ratio q](hyp:q), and
[scale index n](hyp:n), the [local point](goal) is x plus t times the nth power of q. -/
def localPoint (x t q : ℝ) (n : ℕ) : ℝ := x + t * q ^ n -- @realizes y_n(t)(translated local point)

/-- In a tree with [branching number M](hyp:M) and [depth d](hyp:d), the
[local edge](goal) from [internal vertex U](hyp:U) with [child index i](hyp:i)
is the edge leading to that child. -/
def localEdge (U : InternalVertex M d) -- @realizes e_i(outgoing edge of the first default vertex)
    (i : Fin M) : TreeEdge M d :=
  childEdge U i

/-- For [branching number M](hyp:M), [window gap g](hyp:g), and
[base length r0](hyp:r0), the [local length](goal) at [internal vertex U](hyp:U)
in a tree of [depth d](hyp:d) is the window length assigned to its height. -/
def localLength (M g r0 : ℕ) -- @realizes r(window length at the first default height)
    {d : ℕ} (U : InternalVertex M d) : ℕ :=
  windowLength M g r0 (vertexHeight U.val)

-- @node: def:local-indices
/-- For [ratio q](hyp:q), [branching number M](hyp:M), [depth d](hyp:d),
[gap g](hyp:g), [base length r0](hyp:r0), [starting index n0](hyp:n0), and
[center x](hyp:x), assuming [M is at least two](hyp:hM) and
[x satisfies the stable-center condition for these windows](hyp:_hx), fix
[Boolean edge assignment ξ](hyp:ξ) and [internal vertex U](hyp:U) such that
[U is the first vertex choosing the default child](hyp:_hU). The
[local assignments](goal) consist of [the window length at U's height](step:1),
[the outgoing edge for each nondefault child](step:2), and
[the point x plus t times the nth power of q for each dilation t between one
and two and positive index n](step:3). -/
def localIndices (q : ℝ) (M d g r0 n0 : ℕ) (hM : BranchingDomain M) (x : ℝ)
    (_hx : StableCenterCondition q M d g r0 n0 x) (ξ : NondefaultEdge M d → Bool)
    (U : InternalVertex M d) (_hU : firstDefault q M d g r0 hM x ξ = some U) :
    ℕ × ({i : Fin M // i.val + 1 < M} → TreeEdge M d) ×
      ({t : ℝ // t ∈ Set.Icc (1 : ℝ) 2} → {n : ℕ // 1 ≤ n} → ℝ) :=
  (localLength M g r0 U, (fun i => localEdge U i.val),
    fun t n => localPoint x t.val q n.val)

/-- With [ratio q](hyp:q), [branching number M](hyp:M), [depth d](hyp:d),
[gap g](hyp:g), [base length r0](hyp:r0), and [starting index n0](hyp:n0), the
[local index pairs](goal) at [internal vertex U](hyp:U) are all pairs of a
nondefault child index and an integer in that child's edge window. -/
noncomputable def localIndexPairs (q : ℝ) (M d g r0 n0 : ℕ) (U : InternalVertex M d) : Finset (Fin
  M × ℕ) := -- @realizes \mathcal I(nondefault child and window-index pairs)
  (Finset.univ.filter (fun i : Fin M => i.val + 1 < M)).biUnion (fun i =>
    (windowSet q M d g r0 n0 (localEdge U i)).image (fun n => (i, n)))

/-- With [ratio q](hyp:q), [branching number M](hyp:M), [depth d](hyp:d),
[gap g](hyp:g), [base length r0](hyp:r0), and [starting index n0](hyp:n0), assuming
[M is at least two](hyp:hM), the [local leaf](goal) is reached by routing
[point z](hyp:z) under [table outcome ω](hyp:ω), starting at [child i](hyp:i)
of [internal vertex U](hyp:U). -/
noncomputable def localLeaf (hM : BranchingDomain M) (ω : Outcome q M d g r0 n0)
    (U : InternalVertex M d) (i : Fin M) (z : ℝ) : Leaf M d :=
      -- @realizes L_i(z)(route beginning at the chosen child)
  routeFrom hM ω z (child U i)

-- @node: def:local-test
/-- With [ratio q](hyp:q), [branching number M](hyp:M), [depth d](hyp:d),
[gap g](hyp:g), [base length r0](hyp:r0), and [starting index n0](hyp:n0), assume
[M is at least two](hyp:hM). For [table outcome ω](hyp:ω), [internal vertex U](hyp:U),
[child index i](hyp:i) that [is nondefault](hyp:hi), and [point z](hyp:z), the
[local test](goal) is true exactly when both [the selector bit for the child
edge at z's window-end grid cell is true](step:1) and [the terminal bit at
the locally routed leaf and z's leaf-endpoint grid cell is true](step:2). -/
noncomputable def localTest (hM : BranchingDomain M) (ω : Outcome q M d g r0 n0)
    (U : InternalVertex M d) (i : Fin M) (hi : i.val + 1 < M) (z : ℝ) : Bool :=
      -- @realizes Q_i(Boolean product of selector and terminal bits)
  selectorEntry ω (nondefaultChildEdge U i hi) (gridKeyFin q (windowEnd q M d g r0 n0 (localEdge U
    i)) z) &&
    terminalEntry ω (localLeaf hM ω U i z) (gridKeyFin q (leafEndpoint q M d g r0 n0 (localLeaf hM
      ω U i z)) z)

-- @node: gridKeyFin_add_one
/-- For [ratio q](hyp:q), [grid level b](hyp:b), and [point z](hyp:z),
[adding one to z leaves its grid-cell index unchanged](goal). -/
lemma gridKeyFin_add_one (q : ℝ) (b : ℕ) (z : ℝ) :
    gridKeyFin q b (z + 1) = gridKeyFin q b z := by
  apply Fin.ext
  simp [gridKeyFin, gridKey, Int.fract_add_one]

-- @node: randomSet_isOnePeriodic
/-- Assuming [the branching number is at least two](hyp:hM), for
[any table outcome ω](hyp:ω), [membership in the resulting random set is
unchanged by translating a point by one](goal). -/
lemma randomSet_isOnePeriodic (hM : BranchingDomain M) (ω : Outcome q M d g r0 n0) :
    IsOnePeriodic (randomSet hM ω) := by
  intro z
  have hvalues : exposedValues ω (z + 1) = exposedValues ω z := by
    funext e
    simp only [exposedValues, exposedAddr, gridKeyFin_add_one]
  have hroute : route hM ω (z + 1) = route hM ω z := by
    simp only [route, routeFrom, hvalues]
  change terminalEntry ω (route hM ω z) _ = true ↔
    terminalEntry ω (route hM ω (z + 1)) _ = true
  rw [hroute, gridKeyFin_add_one]

-- @node: measurableSet_randomSet
/-- Assuming [the branching number is at least two](hyp:hM), for
[any table outcome ω](hyp:ω), [the resulting random set is measurable](goal). -/
lemma measurableSet_randomSet (hM : BranchingDomain M) (ω : Outcome q M d g r0 n0) :
    MeasurableSet (randomSet hM ω) := by
  let L (ξ : NondefaultEdge M d → Bool) : Leaf M d :=
    ⟨(walkVertices hM ξ d (root M d)).getLast (walkVertices_ne_nil hM ξ d (root M d)),
      walkVertices_last_depth hM ξ (root M d)⟩
  have hkey (b : ℕ) : Measurable (gridKeyFin q b) := by
    apply measurable_to_countable'
    intro j
    have hk : Measurable (gridKey q b) := by
      unfold gridKey
      fun_prop
    convert measurableSet_eq_fun hk (measurable_const (a := j.val)) using 1
    ext z
    simp [gridKeyFin, Fin.ext_iff]
  have hexposed : Measurable (fun z : ℝ => exposedValues ω z) := by
    apply measurable_pi_lambda
    intro e
    exact (measurable_of_countable
      (fun j => ω (Sum.inl (⟨e, j⟩ : SelAddr q M d g r0 n0)))).comp (hkey _)
  have hset : randomSet hM ω =
      ⋃ ξ : NondefaultEdge M d → Bool,
        {z | exposedValues ω z = ξ} ∩
        {z | terminalEntry ω (L ξ) (gridKeyFin q (leafEndpoint q M d g r0 n0 (L ξ)) z) = true} := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro hz
      exact ⟨exposedValues ω z, rfl, hz⟩
    · rintro ⟨ξ, hξ, hz⟩
      change terminalEntry ω (L (exposedValues ω z))
        (gridKeyFin q (leafEndpoint q M d g r0 n0 (L (exposedValues ω z))) z) = true
      rw [hξ]
      exact hz
  rw [hset]
  apply MeasurableSet.iUnion
  intro ξ
  apply MeasurableSet.inter
  · exact measurableSet_eq_fun hexposed measurable_const
  · exact ((measurable_of_countable (terminalEntry ω (L ξ))).comp
      (hkey _)) (measurableSet_singleton true)

-- @node: gridKeyFin_eq_of_finer_eq
/-- If [q lies strictly between zero and one](hyp:hq), [grid level b is at most
B](hyp:hb), and [x and y have the same grid-cell index at level B](hyp:hxy),
then [they have the same grid-cell index at level b](goal). -/
lemma gridKeyFin_eq_of_finer_eq (hq : QDomain q) {b B : ℕ} (hb : b ≤ B)
    {x y : ℝ} (hxy : gridKeyFin q B x = gridKeyFin q B y) :
    gridKeyFin q b x = gridKeyFin q b y := by
  obtain ⟨j, hj⟩ := (gridNesting_of_qDomain q hq).1 b
  obtain ⟨k, hk⟩ := (gridNesting_of_qDomain q hq).1 B
  have hmono := (gridNesting_of_qDomain q hq).2.1 hb
  rw [hj, hk] at hmono
  have hjk : j ≤ k := (pow_le_pow_iff_right₀ (by norm_num : 1 < (2 : ℕ))).mp hmono
  have hdvd : gridResolution q b ∣ gridResolution q B := by
    rw [hj, hk]
    exact pow_dvd_pow 2 hjk
  have hratio : gridResolution q B / gridResolution q b ≠ 0 := by
    have hmul := Nat.div_mul_cancel hdvd
    have hp := gridResolution_pos q B
    intro hz
    rw [hz, Nat.zero_mul] at hmul
    omega
  have hmul : (gridResolution q B : ℝ) =
      (gridResolution q b : ℝ) * (gridResolution q B / gridResolution q b : ℕ) := by
    exact_mod_cast (Nat.mul_div_cancel' hdvd).symm
  have hkey (z : ℝ) : gridKey q b z =
      gridKey q B z / (gridResolution q B / gridResolution q b) := by
    unfold gridKey
    rw [hmul, mul_right_comm]
    exact (Nat.mul_cast_floor_div_cancel hratio _).symm
  apply Fin.ext
  change gridKey q b x = gridKey q b y
  rw [hkey x, hkey y]
  exact congrArg (fun j : ℕ => j / (gridResolution q B / gridResolution q b))
    (congrArg Fin.val hxy)

-- @node: randomSet_mem_iff_of_gridKeyFin_eq
/-- If [q lies strictly between zero and one](hyp:hq) and [the branching number
is at least two](hyp:hM), then for [table outcome ω](hyp:ω), whenever
[x and y have the same grid-cell index at the largest edge-window endpoint](hyp:hxy),
[x belongs to the random set exactly when y does](goal). -/
lemma randomSet_mem_iff_of_gridKeyFin_eq (hq : QDomain q) (hM : BranchingDomain M)
    (ω : Outcome q M d g r0 n0) {x y : ℝ}
    (hxy : gridKeyFin q (Finset.univ.sup (windowEnd q M d g r0 n0)) x =
      gridKeyFin q (Finset.univ.sup (windowEnd q M d g r0 n0)) y) :
    x ∈ randomSet hM ω ↔ y ∈ randomSet hM ω := by
  have hbound (e : TreeEdge M d) : windowEnd q M d g r0 n0 e ≤
      Finset.univ.sup (windowEnd q M d g r0 n0) :=
    Finset.le_sup (f := windowEnd q M d g r0 n0) (Finset.mem_univ e)
  have hvalues : exposedValues ω x = exposedValues ω y := by
    funext e
    simp only [exposedValues, exposedAddr,
      gridKeyFin_eq_of_finer_eq hq (hbound e.val) hxy]
  have hroute : route hM ω x = route hM ω y := by
    simp only [route, routeFrom, hvalues]
  have hleaf (L : Leaf M d) : leafEndpoint q M d g r0 n0 L ≤
      Finset.univ.sup (windowEnd q M d g r0 n0) := by
    unfold leafEndpoint
    split
    · exact hbound _
    · exact Nat.zero_le _
  change terminalEntry ω (route hM ω x) _ = true ↔
    terminalEntry ω (route hM ω y) _ = true
  rw [hroute, gridKeyFin_eq_of_finer_eq hq (hleaf _) hxy]

-- @node: randomSet_finite_cells
/-- If [q lies strictly between zero and one](hyp:hq), [the branching number
is at least two](hyp:hM), [the tree depth is positive](hyp:hd), [the window gap
is positive](hyp:hg), and [the base length is positive](hyp:hr), then for
[table outcome ω](hyp:ω), [there is a finite collection of grid-cell indices
at the largest edge-window endpoint such that a point belongs to the random
set exactly when its index belongs to that collection](goal). -/
lemma randomSet_finite_cells (hq : QDomain q) (hM : BranchingDomain M)
    (hd : DepthDomain d) (hg : GapDomain g) (hr : BaseLengthDomain r0)
    (ω : Outcome q M d g r0 n0) :
    let bmax := Finset.univ.sup (windowEnd q M d g r0 n0)
    ∃ cells : Finset (Fin (gridResolution q bmax)),
      ∀ z : ℝ, z ∈ randomSet hM ω ↔ gridKeyFin q bmax z ∈ cells := by
  classical
  dsimp only
  refine ⟨Finset.univ.filter (fun j => ∃ z ∈ randomSet hM ω,
    gridKeyFin q (Finset.univ.sup (windowEnd q M d g r0 n0)) z = j), ?_⟩
  intro z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hz
    exact ⟨z, hz, rfl⟩
  · rintro ⟨y, hy, hyz⟩
    exact (randomSet_mem_iff_of_gridKeyFin_eq hq hM ω hyz).mp hy

-- @node: terminalEntry_mean_of_selector_address
/-- If [the terminal success probability p lies strictly between zero and one](hyp:hp),
and [a rule a selects a terminal-table address from each outcome](hyp:a) such that
[outcomes agreeing on all selector bits select the same address](hyp:ha), then
[the expected indicator of the selected terminal bit under the table law is p](goal). -/
lemma terminalEntry_mean_of_selector_address (hp : TerminalProbabilityDomain p)
    (a : Outcome q M d g r0 n0 → TermAddr q M d g r0 n0)
    (ha : ∀ ω ω', (∀ j : SelAddr q M d g r0 n0,
      ω (Sum.inl j) = ω' (Sum.inl j)) → a ω = a ω') :
    (tableLaw q M d g r0 n0 p).E (fun ω => if ω (Sum.inr (a ω)) then 1 else 0) = p := by
  classical
  let D := tableLaw q M d g r0 n0 p
  let A : Finset (TableAddr q M d g r0 n0) := Finset.univ.filter (fun j => j.isLeft)
  have hfactor (j : TermAddr q M d g r0 n0) :
      D.E (fun ω => (if a ω = j then (1 : ℝ) else 0) *
        (if ω (Sum.inr j) then 1 else 0)) =
      D.E (fun ω => if a ω = j then 1 else 0) * p := by
    have hf := FiniteDesign.E_prod_block_mul
      (fun k : TableAddr q M d g r0 n0 =>
        coinDesign (tableParameter p k) (tableParameter_nonneg p k) (tableParameter_le_one p k))
      A (fun ω => if a ω = j then (1 : ℝ) else 0)
      (fun ω => if ω (Sum.inr j) then (1 : ℝ) else 0)
      (by
        intro ω ω' hω
        rw [ha ω ω' (fun k => hω (Sum.inl k) (by simp [A]))])
      (by
        intro ω ω' hω
        rw [hω (Sum.inr j) (by simp [A])])
    have hmean : D.E (fun ω => if ω (Sum.inr j) then (1 : ℝ) else 0) = p := by
      change (bernoulliDesign _ _ _).E _ = p
      rw [bernoulliDesign_E_treat]
      simp [tableParameter, max_eq_right hp.1.le, min_eq_left hp.2.le]
    exact hf.trans (congrArg (D.E (fun ω => if a ω = j then 1 else 0) * ·) hmean)
  calc
    D.E (fun ω => if ω (Sum.inr (a ω)) then 1 else 0) =
        D.E (fun ω => ∑ j : TermAddr q M d g r0 n0,
          (if a ω = j then (1 : ℝ) else 0) * (if ω (Sum.inr j) then 1 else 0)) := by
      apply D.E_congr
      intro ω
      simp only [ite_mul, zero_mul, one_mul]
      rw [Finset.sum_ite_eq]
      simp
    _ = ∑ j : TermAddr q M d g r0 n0,
        D.E (fun ω => if a ω = j then 1 else 0) * p := by
      rw [D.E_sum]
      exact Finset.sum_congr rfl (fun j _ => hfactor j)
    _ = D.E (fun ω => ∑ j : TermAddr q M d g r0 n0,
        if a ω = j then (1 : ℝ) else 0) * p := by rw [D.E_sum, Finset.sum_mul]
    _ = p := by simp

-- @node: pr_mem_randomSet
/-- If [the branching number is at least two](hyp:hM) and [the terminal success
probability p lies strictly between zero and one](hyp:hp), then for [any point z](hyp:z),
[the probability that z belongs to the random set under the table law equals p](goal). -/
lemma pr_mem_randomSet (hM : BranchingDomain M) (hp : TerminalProbabilityDomain p) (z : ℝ) :
    (tableLaw q M d g r0 n0 p).Pr (fun ω => z ∈ randomSet hM ω) = p := by
  let a (ω : Outcome q M d g r0 n0) : TermAddr q M d g r0 n0 :=
    ⟨route hM ω z, gridKeyFin q (leafEndpoint q M d g r0 n0 (route hM ω z)) z⟩
  have ha : ∀ ω ω', (∀ j : SelAddr q M d g r0 n0,
      ω (Sum.inl j) = ω' (Sum.inl j)) → a ω = a ω' := by
    intro ω ω' hω
    have hv : exposedValues ω z = exposedValues ω' z :=
      funext (fun e => hω (exposedAddr q M d g r0 n0 z e))
    have hr : route hM ω z = route hM ω' z := by simp only [route, routeFrom, hv]
    exact congrArg (fun L : Leaf M d => (⟨L,
      gridKeyFin q (leafEndpoint q M d g r0 n0 L) z⟩ : TermAddr q M d g r0 n0)) hr
  convert terminalEntry_mean_of_selector_address hp a ha using 1
  apply FiniteDesign.E_congr
  intro ω
  unfold FiniteDesign.ind
  by_cases h : z ∈ randomSet hM ω
  · rw [if_pos h, if_pos (show ω (Sum.inr (a ω)) = true from h)]
  · rw [if_neg h, if_neg (show ¬ ω (Sum.inr (a ω)) = true from h)]

-- @node: lem:density
/-- If [q lies strictly between zero and one](hyp:hq), [the branching number
is at least two](hyp:hM), [the tree depth is positive](hyp:hd), [the window gap
is positive](hyp:hg), [the base length is positive](hyp:hr), and [the terminal
success probability p lies strictly between zero and one](hyp:hp), then
[the expected density of the random set over one period under the table law equals p](goal). -/
lemma expected_periodicDensity_randomSet_eq (hq : QDomain q) (hM : BranchingDomain M)
    (hd : DepthDomain d) (hg : GapDomain g) (hr : BaseLengthDomain r0) (hp :
      TerminalProbabilityDomain p) :
    (tableLaw q M d g r0 n0 p).E (fun ω => periodicDensity (randomSet hM ω)) = p := by
  classical
  let μ := MeasureTheory.volume.restrict (Set.Ico (0 : ℝ) 1)
  let D := tableLaw q M d g r0 n0 p
  have hmeas (ω : Outcome q M d g r0 n0) := measurableSet_randomSet hM ω
  have hint (ω : Outcome q M d g r0 n0) :
      MeasureTheory.Integrable ((randomSet hM ω).indicator (fun _ => (1 : ℝ))) μ := by
    exact MeasureTheory.integrable_const (1 : ℝ) |>.indicator (hmeas ω)
  have hden (ω : Outcome q M d g r0 n0) : periodicDensity (randomSet hM ω) =
      ∫ z, (randomSet hM ω).indicator (fun _ => (1 : ℝ)) z ∂μ := by
    rw [MeasureTheory.integral_indicator (hmeas ω)]
    simp [μ, periodicDensity, lebesgueMeasure, MeasureTheory.integral_const,
      MeasureTheory.Measure.real, MeasureTheory.Measure.restrict_apply (hmeas ω)]
  calc
    D.E (fun ω => periodicDensity (randomSet hM ω)) =
        ∫ z, D.E (fun ω => (randomSet hM ω).indicator (fun _ => (1 : ℝ)) z) ∂μ := by
      simp only [FiniteDesign.E, hden, ← MeasureTheory.integral_const_mul]
      rw [MeasureTheory.integral_finsetSum]
      intro ω _
      exact (hint ω).const_mul _
    _ = ∫ _z, p ∂μ := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with z
      exact pr_mem_randomSet hM hp z
    _ = p := by simp [μ]

end Papers.OaiGeometricErdosSimilarity

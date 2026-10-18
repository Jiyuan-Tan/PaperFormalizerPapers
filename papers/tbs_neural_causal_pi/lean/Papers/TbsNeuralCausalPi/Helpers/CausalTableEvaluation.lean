module
public import Papers.TbsNeuralCausalPi.Helpers.FixedLabelPrefixCausality
/-! # Deterministic evaluation of causal finite categorical tables

The table is evaluated in the actual topological order, including empty slots.
Prefix causality proves that its terminal labels solve the local selector
equations uniquely. No fixed point or circular choice of a stratum is used.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
open scoped NNReal ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
  {C : Fin b → Set (Fin n)}

-- @node: causalLabelSteps
/-- For [node ranks](hyp:rank) and [a rule selecting labels from a complete label vector](hyp:select),
[the sequence of partial label vectors](goal) [starts with every label zero](step:1)
and [at each subsequent slot updates exactly the nodes whose rank equals that slot, using the previous vector](step:2). -/
def causalLabelSteps (rank : Fin n → ℕ)
    (select : CategoricalStratum kind → CategoricalStratum kind) :
    ℕ → CategoricalStratum kind
  | 0 => fun _ => ⟨0, by omega⟩
  | r + 1 => fun i => if rank i = r then select (causalLabelSteps rank select r) i
      else causalLabelSteps rank select r i

-- @node: causalLabelSteps_stable
/-- If [a node's rank is below an evaluation horizon](hyp:hi) and [a later horizon is at least as large](hyp:hrt),
[the node has the same label at both horizons](goal). -/
lemma causalLabelSteps_stable (rank : Fin n → ℕ)
    (select : CategoricalStratum kind → CategoricalStratum kind)
    (i : Fin n) {r t : ℕ} (hi : rank i < r) (hrt : r ≤ t) :
    causalLabelSteps rank select t i = causalLabelSteps rank select r i := by
  induction t, hrt using Nat.le_induction with
  | base => rfl
  | succ t hrt ih =>
    simpa only [causalLabelSteps, if_neg (show rank i ≠ t by omega)] using ih

-- @node: causalLabelSteps_eq_solution
/-- If [each node's selector depends only on labels at lower ranks](hyp:hcausal)
and [a complete label vector satisfies the selector equations](hyp:hc),
[the recursive evaluation agrees with that vector at every node visited before any given horizon](goal). -/
lemma causalLabelSteps_eq_solution (rank : Fin n → ℕ)
    (select : CategoricalStratum kind → CategoricalStratum kind)
    (hcausal : ∀ c c' i, (∀ j, rank j < rank i → c j = c' j) →
      select c i = select c' i)
    (c : CategoricalStratum kind) (hc : select c = c) (r : ℕ) :
    ∀ i, rank i < r → causalLabelSteps rank select r i = c i := by
  induction r with
  | zero => intro i hi; omega
  | succ r ih =>
    intro i hi
    by_cases he : rank i = r
    · simp only [causalLabelSteps, if_pos he]
      rw [hcausal _ c i (fun j hj => ih j (by omega)), hc]
    · simpa only [causalLabelSteps, if_neg he] using ih i (by omega)

-- @node: causalLabelSteps_selector_equations
/-- If [each selector depends only on labels at lower ranks](hyp:hcausal)
and [every node's rank is below the evaluation horizon](hyp:hN),
[the label vector computed at that horizon satisfies all selector equations](goal). -/
lemma causalLabelSteps_selector_equations (rank : Fin n → ℕ)
    (select : CategoricalStratum kind → CategoricalStratum kind)
    (hcausal : ∀ c c' i, (∀ j, rank j < rank i → c j = c' j) →
      select c i = select c' i)
    (N : ℕ) (hN : ∀ i, rank i < N) :
    select (causalLabelSteps rank select N) = causalLabelSteps rank select N := by
  funext i
  have hprefix : ∀ j, rank j < rank i →
      causalLabelSteps rank select N j = causalLabelSteps rank select (rank i) j := by
    intro j hj
    exact causalLabelSteps_stable rank select j hj (Nat.le_of_lt (hN i))
  rw [hcausal _ _ i hprefix]
  have hi := causalLabelSteps_stable rank select i (Nat.lt_succ_self _)
    (Nat.succ_le_of_lt (hN i))
  simpa only [causalLabelSteps, if_true] using hi.symm

-- @node: causalLabelSteps_unique_solution
/-- If [each selector depends only on labels at lower ranks](hyp:hcausal)
and [all ranks lie below a common finite horizon](hyp:hN),
[exactly one complete label vector satisfies the selector equations](goal). -/
lemma causalLabelSteps_unique_solution (rank : Fin n → ℕ)
    (select : CategoricalStratum kind → CategoricalStratum kind)
    (hcausal : ∀ c c' i, (∀ j, rank j < rank i → c j = c' j) →
      select c i = select c' i)
    (N : ℕ) (hN : ∀ i, rank i < N) :
    ∃! c, select c = c := by
  refine ⟨causalLabelSteps rank select N,
    causalLabelSteps_selector_equations rank select hcausal N hN, ?_⟩
  intro c hc
  funext i
  exact (causalLabelSteps_eq_solution rank select hcausal c hc N i (hN i)).symm

-- @node: causalLabelSteps_measurable
/-- If [the selected label vector is measurable in the input for each fixed current vector](hyp:hselect),
[the recursively computed label vector at any fixed horizon is measurable in the input](goal). -/
@[fun_prop] lemma causalLabelSteps_measurable
    {X : Type*} [MeasurableSpace X] (rank : Fin n → ℕ)
    (select : X → CategoricalStratum kind → CategoricalStratum kind)
    (hselect : ∀ c, Measurable (fun x => select x c)) (r : ℕ) :
    Measurable (fun x => causalLabelSteps rank (select x) r) := by
  induction r with
  | zero => exact measurable_const
  | succ r ih =>
    have hm : Measurable (fun z : X × CategoricalStratum kind => select z.1 z.2) :=
      measurable_from_prod_countable_left hselect
    have hs := hm.comp (measurable_id.prodMk ih)
    apply measurable_pi_lambda
    intro i
    by_cases hi : rank i = r
    · simpa only [causalLabelSteps, hi, if_true, Function.comp_def, id_eq] using (measurable_pi_apply i).comp hs
    · simpa only [causalLabelSteps, hi, if_false, Function.comp_def] using (measurable_pi_apply i).comp ih

-- @node: causalTableSelector
/-- For [a canonical causal model](hyp:M), [a categorical probability table indexed by complete labels and grid cells](hyp:table),
[a grid cell](hyp:a), [an exogenous noise realization](hyp:u), and [a current complete label vector](hyp:c),
[the table selector](goal) assigns zero to continuous nodes and applies the model's categorical selector
to the table probabilities and private categorical noise at categorical nodes. -/
def causalTableSelector (M : CanonicalSCM kind dims dag G C) {s : ℕ}
    (table : ∀ i k, kind i = Sum.inr k →
      CategoricalStratum kind → Fin s → probabilitySimplex k)
    (a : Fin s) (u : Exogenous kind dims) (c : CategoricalStratum kind) :
    CategoricalStratum kind := fun i =>
  ⟨match hi : kind i with
    | .inl _ => 0
    | .inr k =>
      (canonicalSelector (.inr k)
        (fun m hm => M.categoricalPositive i m (hi.trans hm))
        (WithLp.toLp 1 (table i k hi c a).val)
        (WithLp.toLp 1 (fun l => (categoricalNoise i u).ofLp
          (Fin.cast (congrArg noiseDim hi).symm l)))).val,
    by
      split
      · omega
      · rename_i k hi
        exact lt_of_lt_of_le (Fin.isLt _) (by simp [hi, noiseDim])⟩

-- @node: causalTableSelector_categorical
/-- Given [a categorical probability table](hyp:table), if [the chosen node has the specified number of categories](hyp:hi),
[its table-selected label equals the canonical categorical choice using the table probabilities at the current labels and cell and the node's private noise](goal). -/
lemma causalTableSelector_categorical (M : CanonicalSCM kind dims dag G C) {s : ℕ}
    (table : ∀ i k, kind i = Sum.inr k →
      CategoricalStratum kind → Fin s → probabilitySimplex k)
    (a : Fin s) (u : Exogenous kind dims) (c : CategoricalStratum kind)
    (i : Fin n) (k : ℕ) (hi : kind i = Sum.inr k) :
    (causalTableSelector M table a u c i).val =
      (canonicalSelector (.inr k)
        (fun m hm => M.categoricalPositive i m (hi.trans hm))
        (WithLp.toLp 1 (table i k hi c a).val)
        (WithLp.toLp 1 (fun l => (categoricalNoise i u).ofLp
          (Fin.cast (congrArg noiseDim hi).symm l)))).val := by
  unfold causalTableSelector
  dsimp only
  split
  · rename_i d hd
    have h := hi.symm.trans hd
    cases h
  · rename_i k' hk'
    have he : k = k' := Sum.inr.inj (hi.symm.trans hk')
    subst k'
    rfl

-- @node: causalTableSelector_prefix_causal
/-- Given [a categorical probability table](hyp:table) that [depends only on labels earlier in topological order](hyp:hcausal),
if [two label vectors agree at every node earlier than the chosen node](hyp:hc),
[their table-selected labels at that node coincide](goal). -/
lemma causalTableSelector_prefix_causal (M : CanonicalSCM kind dims dag G C) {s : ℕ}
    (table : ∀ i k, kind i = Sum.inr k →
      CategoricalStratum kind → Fin s → probabilitySimplex k)
    (hcausal : ∀ i k hi c c',
      (∀ j, dag.topoOrder j < dag.topoOrder i → c j = c' j) →
        table i k hi c = table i k hi c')
    (a : Fin s) (u : Exogenous kind dims) (c c' : CategoricalStratum kind)
    (i : Fin n) (hc : ∀ j, dag.topoOrder j < dag.topoOrder i → c j = c' j) :
    causalTableSelector M table a u c i = causalTableSelector M table a u c' i := by
  apply Fin.ext
  have hcases : (∃ d, kind i = Sum.inl d) ∨ (∃ k, kind i = Sum.inr k) := by
    cases kind i with
    | inl d => exact Or.inl ⟨d, rfl⟩
    | inr k => exact Or.inr ⟨k, rfl⟩
  rcases hcases with ⟨d, hi⟩ | ⟨k, hi⟩
  · have hsize : max 1 (noiseDim (kind i)) = 1 := by simp [hi, noiseDim]
    have h1 := (causalTableSelector M table a u c i).isLt
    have h2 := (causalTableSelector M table a u c' i).isLt
    omega
  · rw [causalTableSelector_categorical M table a u c i k hi,
      causalTableSelector_categorical M table a u c' i k hi, hcausal i k hi c c' hc]

-- @node: causalTableEvaluation
/-- For [a canonical causal model](hyp:M), [a categorical probability table](hyp:table),
[a grid cell](hyp:a), and [an exogenous noise realization](hyp:u),
[the table's complete label vector](goal) is computed by applying its selector recursively in topological order for the square of the node count plus the node count slots. -/
def causalTableEvaluation (M : CanonicalSCM kind dims dag G C) {s : ℕ}
    (table : ∀ i k, kind i = Sum.inr k →
      CategoricalStratum kind → Fin s → probabilitySimplex k)
    (a : Fin s) (u : Exogenous kind dims) : CategoricalStratum kind :=
  causalLabelSteps dag.topoOrder (causalTableSelector M table a u) (n*n+n)

-- @node: causalTableEvaluation_selector_equations
/-- Given [a categorical probability table](hyp:table) that [depends only on earlier labels in topological order](hyp:hcausal),
[the computed complete label vector satisfies the table's selector equations](goal). -/
lemma causalTableEvaluation_selector_equations
    (M : CanonicalSCM kind dims dag G C) {s : ℕ}
    (table : ∀ i k, kind i = Sum.inr k →
      CategoricalStratum kind → Fin s → probabilitySimplex k)
    (hcausal : ∀ i k hi c c',
      (∀ j, dag.topoOrder j < dag.topoOrder i → c j = c' j) →
        table i k hi c = table i k hi c')
    (a : Fin s) (u : Exogenous kind dims) :
    causalTableSelector M table a u (causalTableEvaluation M table a u) =
      causalTableEvaluation M table a u := by
  exact causalLabelSteps_selector_equations dag.topoOrder _
    (causalTableSelector_prefix_causal M table hcausal a u) _
    (scm_topoOrder_lt_horizon M.toEuclideanSCM)

-- @node: causalTableSelector_measurable
/-- For [a categorical probability table](hyp:table), if [the grid cell varies measurably with the input](hyp:ha)
and [the exogenous noise varies measurably with the input](hyp:hu),
[the table-selected label vector for any fixed current label vector is measurable](goal). -/
@[fun_prop] lemma causalTableSelector_measurable
    {X : Type*} [MeasurableSpace X]
    (M : CanonicalSCM kind dims dag G C) {s : ℕ}
    (table : ∀ i k, kind i = Sum.inr k →
      CategoricalStratum kind → Fin s → probabilitySimplex k)
    (a : X → Fin s) (u : X → Exogenous kind dims)
    (ha : Measurable a) (hu : Measurable u) (c : CategoricalStratum kind) :
    Measurable (fun x => causalTableSelector M table (a x) (u x) c) := by
  first | fun_prop | skip
  apply measurable_pi_lambda
  intro i
  have hcases : (∃ d, kind i = Sum.inl d) ∨ (∃ k, kind i = Sum.inr k) := by
    cases kind i with
    | inl d => exact Or.inl ⟨d, rfl⟩
    | inr k => exact Or.inr ⟨k, rfl⟩
  rcases hcases with ⟨d, hi⟩ | ⟨k, hi⟩
  · have hsize : max 1 (noiseDim (kind i)) = 1 := by simp [hi, noiseDim]
    convert (measurable_const : Measurable (fun _ : X =>
      (⟨0, by omega⟩ : Fin (max 1 (noiseDim (kind i)))))) using 1
    funext x
    apply Fin.ext
    have h := (causalTableSelector M table (a x) (u x) c i).isLt
    omega
  · let label := fun x => canonicalSelector (.inr k)
        (fun m hm => M.categoricalPositive i m (hi.trans hm))
        (WithLp.toLp 1 (table i k hi c (a x)).val)
        (WithLp.toLp 1 (fun l => (categoricalNoise i (u x)).ofLp
          (Fin.cast (congrArg noiseDim hi).symm l)))
    have hm : Measurable label := by
      apply firstArgmax_getD_measurable
      intro j
      change Measurable (fun x => extendedLog ((table i k hi c (a x)).val j) +
        ((categoricalNoise i (u x)).ofLp (Fin.cast (congrArg noiseDim hi).symm j) : EReal))
      have ht : Measurable (fun x => (table i k hi c (a x)).val j) :=
        (measurable_of_finite (fun t => (table i k hi c t).val j)).comp ha
      exact (extendedLog_measurable.comp ht).add (by fun_prop [categoricalNoise])
    let embed : Fin k → Fin (max 1 (noiseDim (kind i))) := fun j =>
      ⟨j.val, j.isLt.trans_le (by simp [hi, noiseDim])⟩
    convert (measurable_of_finite embed).comp hm using 1
    funext x
    apply Fin.ext
    exact causalTableSelector_categorical M table (a x) (u x) c i k hi

-- @node: causalTableEvaluation_measurable
/-- For [a categorical probability table](hyp:table), if [the grid cell is measurable in the input](hyp:ha)
and [the exogenous noise is measurable in the input](hyp:hu),
[the complete label vector obtained by table evaluation is measurable in the input](goal). -/
@[fun_prop] lemma causalTableEvaluation_measurable
    {X : Type*} [MeasurableSpace X]
    (M : CanonicalSCM kind dims dag G C) {s : ℕ}
    (table : ∀ i k, kind i = Sum.inr k →
      CategoricalStratum kind → Fin s → probabilitySimplex k)
    (a : X → Fin s) (u : X → Exogenous kind dims)
    (ha : Measurable a) (hu : Measurable u) :
    Measurable (fun x => causalTableEvaluation M table (a x) (u x)) := by
  exact causalLabelSteps_measurable dag.topoOrder _
    (causalTableSelector_measurable M table a u ha hu) _

-- @node: causalTableEvaluation_eq_of_categoricalNoise
/-- For [a categorical probability table](hyp:table), if [two exogenous realizations have identical private categorical noise at every node](hyp:hu),
[table evaluation at the same grid cell produces identical complete label vectors](goal). -/
lemma causalTableEvaluation_eq_of_categoricalNoise
    (M : CanonicalSCM kind dims dag G C) {s : ℕ}
    (table : ∀ i k, kind i = Sum.inr k →
      CategoricalStratum kind → Fin s → probabilitySimplex k)
    (a : Fin s) (u u' : Exogenous kind dims)
    (hu : ∀ i, categoricalNoise i u = categoricalNoise i u') :
    causalTableEvaluation M table a u = causalTableEvaluation M table a u' := by
  have he : causalTableSelector M table a u = causalTableSelector M table a u' := by
    funext c i
    apply Fin.ext
    unfold causalTableSelector
    dsimp only
    split
    · rfl
    · rename_i k hi
      rw [hu i]
  unfold causalTableEvaluation
  rw [he]

end
end Papers.TbsNeuralCausalPi

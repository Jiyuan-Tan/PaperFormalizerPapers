module
public import Papers.TbsNeuralCausalPi.Helpers.CausalTableSampling
public import Papers.TbsNeuralCausalPi.Helpers.SimulationShattering
/-! # Joint type-subset and ambiguity patterns for actual causal tables

A fixed table uses only the latent code and the original private Gumbels.
Both kinds of scalar indicator therefore share one generator-pattern budget.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
  {C : Fin b → Set (Fin n)}

-- @node: causalTableNodeAmbiguity_eq_of_categoricalNoise
/-- For [a table of categorical probability vectors indexed by label strata
and cells](hyp:table), if [two exogenous inputs have identical categorical
noise at every node](hyp:hnoise), then [their table-ambiguity conditions at
any given node, tolerance, and cell are equal](goal). -/
lemma causalTableNodeAmbiguity_eq_of_categoricalNoise {s : ℕ}
    (table : ∀ i k, kind i = Sum.inr k →
      CategoricalStratum kind → Fin s → probabilitySimplex k)
    (a : ℝ) (j : Fin s) (u u' : Exogenous kind dims)
    (hnoise : ∀ i, categoricalNoise i u = categoricalNoise i u') (i : Fin n) :
    causalTableNodeAmbiguity table a j u i = causalTableNodeAmbiguity table a j u' i := by
  cases hi : kind i with
  | inl d => rw [causalTableNodeAmbiguity_continuous table a j u i d hi,
      causalTableNodeAmbiguity_continuous table a j u' i d hi]
  | inr k => rw [causalTableNodeAmbiguity_categorical table a j u i k hi,
      causalTableNodeAmbiguity_categorical table a j u' i k hi, hnoise i]

/-- For [a categorical probability table over label strata and cells](hyp:table),
[ambiguity of a simulation input under a model is equivalent to ambiguity at
some node using that model's latent cell code and the exogenous categorical
noise from any fixed reference model](goal). -/
-- @node: ncmCausalTableAmbiguity_reference
lemma ncmCausalTableAmbiguity_reference {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C} {F1 : GeneratorClass dims counts}
    {bound : Option (ℝ × ℝ)} (R R0 : NCMIn kind dims dag G C counts F0 F1 bound)
    {s : ℕ} (code : Latent dims → Fin s)
    (table : ∀ i k, kind i = Sum.inr k →
      CategoricalStratum kind → Fin s → probabilitySimplex k)
    (a : ℝ) (z : SimulationInput kind counts) :
    (z ∈ ncmCausalTableAmbiguity R code table a) =
      (∃ i, causalTableNodeAmbiguity table a
        (code (jointNonGumbel (ncmSimulationExogenous R z)))
        (ncmSimulationExogenous R0 z) i) := by
  unfold ncmCausalTableAmbiguity
  simp only [Set.mem_setOf_eq]
  exact congrArg (fun p : Fin n → Prop => ∃ i, p i)
    (funext fun i => causalTableNodeAmbiguity_eq_of_categoricalNoise table a _ _ _
      (fun i => by rw [categoricalNoise_ncmSimulationExogenous,
        categoricalNoise_ncmSimulationExogenous]) i)

/-- For [a neural causal model](hyp:R), [a finite latent cell code](hyp:code),
[a categorical probability table over strata and cells](hyp:table), and
[an ambiguity tolerance](hyp:a), the [joint Boolean table indicator](goal)
reports [whether a simulation input is ambiguous when no type subset is
selected](step:1), or [whether its cell-and-label type belongs to the
selected subset when a subset is selected](step:2). -/
-- @node: ncmCausalTableIndicator
def ncmCausalTableIndicator {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C} {F1 : GeneratorClass dims counts}
    {bound : Option (ℝ × ℝ)} (R : NCMIn kind dims dag G C counts F0 F1 bound)
    {s : ℕ} (code : Latent dims → Fin s)
    (table : ∀ i k, kind i = Sum.inr k →
      CategoricalStratum kind → Fin s → probabilitySimplex k) (a : ℝ) :
    Option (Finset (Fin s × CategoricalStratum kind)) → SimulationInput kind counts → Bool
  | none, z => decide (z ∈ ncmCausalTableAmbiguity R code table a)
  | some t, z => decide (ncmCausalTableType R code table z ∈ t)

-- @node: ncmCausalTableIndicator_measurable
/-- For [a categorical probability table](hyp:table), if [the latent cell
code is measurable](hyp:hcode), then [the Boolean indicator of table
ambiguity or membership in a selected subset of cell-and-label types is a
measurable function of the simulation input](goal). -/
@[fun_prop] lemma ncmCausalTableIndicator_measurable {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C} {F1 : GeneratorClass dims counts}
    {bound : Option (ℝ × ℝ)} (R : NCMIn kind dims dag G C counts F0 F1 bound)
    {s : ℕ} (code : Latent dims → Fin s) (hcode : Measurable code)
    (table : ∀ i k, kind i = Sum.inr k →
      CategoricalStratum kind → Fin s → probabilitySimplex k) (a : ℝ)
    (t : Option (Finset (Fin s × CategoricalStratum kind))) :
    Measurable (ncmCausalTableIndicator R code table a t) := by
  first | fun_prop | skip
  cases t with
  | none =>
    change Measurable (fun z => if z ∈ ncmCausalTableAmbiguity R code table a
      then true else false)
    exact measurable_const.ite (ncmCausalTableAmbiguity_measurable R code hcode table a)
      measurable_const
  | some t =>
    exact (measurable_of_finite (fun x => decide (x ∈ t))).comp
      (ncmCausalTableType_measurable R code hcode table)

/-- For [a finite collection of categorical probability tables](hyp:tables),
if [every representation's vector of latent cell codes on the fixed draws
belongs to a given finite pattern collection](hyp:hpatterns), then [the
number of joint indicator patterns is at most the table count times the
pattern count times one plus the number of subsets of cell-and-label types](goal). -/
-- @node: ncmCausalTableIndicator_growth_card_le
lemma ncmCausalTableIndicator_growth_card_le {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C} {F1 : GeneratorClass dims counts}
    {bound : Option (ℝ × ℝ)} {A : Type*}
    (repr : A → NCMIn kind dims dag G C counts F0 F1 bound)
    (R0 : NCMIn kind dims dag G C counts F0 F1 bound)
    {s m : ℕ} (code : Latent dims → Fin s)
    (tables : Finset (∀ i k, kind i = Sum.inr k →
      CategoricalStratum kind → Fin s → probabilitySimplex k))
    (a : ℝ) (draws : Fin m → SimulationInput kind counts)
    (patterns : Finset (Fin m → Fin s))
    (hpatterns : ∀ r, (fun j =>
      code (jointNonGumbel (ncmSimulationExogenous (repr r) (draws j)))) ∈ patterns) :
    (Causalean.Stat.Concentration.growthFamily
      (fun idx : A × tables × Option (Finset (Fin s × CategoricalStratum kind)) =>
        ncmCausalTableIndicator (repr idx.1) code idx.2.1.val a idx.2.2) draws).card ≤
      tables.card * patterns.card * (2 ^ Fintype.card (Fin s × CategoricalStratum kind) + 1) := by
  classical
  let indicator := fun table (p : Fin m → Fin s)
      (t : Finset (Fin s × CategoricalStratum kind)) =>
    Finset.univ.filter (fun j =>
      (p j, causalTableEvaluation R0.canonical table (p j)
        (ncmSimulationExogenous R0 (draws j))) ∈ t)
  let ambiguity := fun table (p : Fin m → Fin s) =>
    Finset.univ.filter (fun j => ∃ i, causalTableNodeAmbiguity table a (p j)
      (ncmSimulationExogenous R0 (draws j)) i)
  apply simulation_table_patterns_card_le tables patterns _ indicator ambiguity
  intro p hp
  obtain ⟨⟨r, table, t⟩, rfl⟩ := Causalean.Stat.Concentration.mem_growthFamily_iff.mp hp
  refine ⟨table.val, table.property, _, hpatterns r, ?_⟩
  cases t with
  | none =>
    right
    ext j
    simp only [ambiguity, Finset.mem_filter, Finset.mem_univ, true_and,
      Causalean.Stat.Concentration.restrictionPattern_mem_iff,
      ncmCausalTableIndicator, decide_eq_true_eq,
      ncmCausalTableAmbiguity_reference (repr r) R0]
  | some t =>
    left
    refine ⟨t, ?_⟩
    ext j
    simp only [indicator, Finset.mem_filter, Finset.mem_univ, true_and,
      Causalean.Stat.Concentration.restrictionPattern_mem_iff,
      ncmCausalTableIndicator, decide_eq_true_eq,
      ncmCausalTableType_reference (repr r) R0]

/-- For [a finite categorical probability-table alphabet](hyp:tables), if
[the number of distinct latent cell-code vectors produced by the
representations on the fixed draws is at most P](hyp:hpatterns), then [the
joint indicator pattern count is at most the table count times P times one
plus the number of subsets of cell-and-label types](goal). -/
-- @node: ncmCausalTableIndicator_growth_card_le_of_grid_encard
lemma ncmCausalTableIndicator_growth_card_le_of_grid_encard {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C} {F1 : GeneratorClass dims counts}
    {bound : Option (ℝ × ℝ)} {A : Type*}
    (repr : A → NCMIn kind dims dag G C counts F0 F1 bound)
    (R0 : NCMIn kind dims dag G C counts F0 F1 bound)
    {s m : ℕ} (code : Latent dims → Fin s)
    (tables : Finset (∀ i k, kind i = Sum.inr k →
      CategoricalStratum kind → Fin s → probabilitySimplex k))
    (a : ℝ) (draws : Fin m → SimulationInput kind counts) (P : ℕ)
    (hpatterns : (Set.range (fun r j =>
      code (jointNonGumbel (ncmSimulationExogenous (repr r) (draws j))))).encard ≤ P) :
    (Causalean.Stat.Concentration.growthFamily
      (fun idx : A × tables × Option (Finset (Fin s × CategoricalStratum kind)) =>
        ncmCausalTableIndicator (repr idx.1) code idx.2.1.val a idx.2.2) draws).card ≤
      tables.card * P * (2 ^ Fintype.card (Fin s × CategoricalStratum kind) + 1) := by
  classical
  let patterns := Set.range (fun r j =>
    code (jointNonGumbel (ncmSimulationExogenous (repr r) (draws j))))
  have hfinite : patterns.Finite := Set.toFinite _
  have hcard : hfinite.toFinset.card ≤ P := by
    exact_mod_cast (hfinite.encard_eq_coe_toFinset_card ▸ hpatterns)
  exact (ncmCausalTableIndicator_growth_card_le repr R0 code tables a draws
    hfinite.toFinset (fun r => hfinite.mem_toFinset.mpr ⟨r, rfl⟩)).trans
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hcard))

/-- For [a finite categorical probability-table alphabet](hyp:tables), if
[the representations produce at most P latent cell-code patterns on the
simulation components of the fixed input-and-threshold pairs](hyp:hpatterns),
then [the subgraph pattern count of the zero-or-one table indicators is at
most the table count times P times one plus the number of subsets of
cell-and-label types](goal). -/
-- @node: ncmCausalTableIndicator_subgraph_card_le
lemma ncmCausalTableIndicator_subgraph_card_le {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C} {F1 : GeneratorClass dims counts}
    {bound : Option (ℝ × ℝ)} {A : Type*}
    (repr : A → NCMIn kind dims dag G C counts F0 F1 bound)
    (R0 : NCMIn kind dims dag G C counts F0 F1 bound)
    {s m : ℕ} (code : Latent dims → Fin s)
    (tables : Finset (∀ i k, kind i = Sum.inr k →
      CategoricalStratum kind → Fin s → probabilitySimplex k))
    (a : ℝ) (draws : Fin m → SimulationInput kind counts × ℝ) (P : ℕ)
    (hpatterns : (Set.range (fun r j =>
      code (jointNonGumbel (ncmSimulationExogenous (repr r) (draws j).1)))).encard ≤ P) :
    (Causalean.Stat.Concentration.growthFamily
      (Causalean.Stat.Concentration.subgraphClassifier
        (fun (idx : A × tables × Option (Finset (Fin s × CategoricalStratum kind))) z =>
          if ncmCausalTableIndicator (repr idx.1) code idx.2.1.val a idx.2.2 z
          then (1 : ℝ) else 0)) draws).card ≤
      tables.card * P * (2 ^ Fintype.card (Fin s × CategoricalStratum kind) + 1) := by
  exact (simulation_indicator_subgraph_card_le _ m draws).trans
    (ncmCausalTableIndicator_growth_card_le_of_grid_encard
      repr R0 code tables a (fun j => (draws j).1) P hpatterns)

end
end Papers.TbsNeuralCausalPi

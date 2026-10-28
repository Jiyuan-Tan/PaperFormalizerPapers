module
public import Papers.OaiGraphDecompositionsIntegral.Helpers.DegreeLayers
public import Papers.OaiGraphDecompositionsIntegral.Helpers.Compression
public import Papers.OaiGraphDecompositionsIntegral.Helpers.BernoulliTests

/-! # Disjoint requirements and the probabilistic Hall obstruction

Intersecting requirements are separated by an independent set in their conflict
graph. The resulting Bernoulli failure estimate uses only disjoint coordinates;
in particular an empty requirement makes the obstruction impossible.
-/

public section

open Causalean.Experimentation.DesignBased
open scoped BigOperators

namespace Papers.OaiGraphDecompositionsIntegral

attribute [local instance] Classical.propDecidable

/-- If [each requirement has at most k coordinates](hyp:hsize) and [each
coordinate belongs to at most Δ requirements](hyp:hload), then [there is a
subfamily I of pairwise disjoint requirements whose size times 1 + kΔ is
at least the total number of requirements](goal). -/
-- @node: degree_disjoint_requirements
lemma degree_disjoint_requirements {V X : Type} [Fintype V]
    [DecidableEq X] (R : V → Finset X) (k Δ : ℕ)
    (hsize : ∀ v, (R v).card ≤ k)
    (hload : ∀ x, (Finset.univ.filter (fun v => x ∈ R v)).card ≤ Δ) :
    ∃ I : Finset V, (I : Set V).Pairwise (fun v w => Disjoint (R v) (R w)) ∧
      Fintype.card V ≤ (1 + k * Δ) * I.card := by
  classical
  let G : SimpleGraph V := {
    Adj := fun v w => v ≠ w ∧ ¬ Disjoint (R v) (R w)
    symm := ⟨by intro v w h; exact ⟨h.1.symm, fun hd => h.2 hd.symm⟩⟩
    loopless := ⟨by intro v h; exact h.1 rfl⟩ }
  have hdeg (v : V) : G.degree v ≤ k * Δ := by
    have hsub : G.neighborFinset v ⊆
        (R v).biUnion (fun x => Finset.univ.filter (fun w => x ∈ R w)) := by
      intro w hw
      have hadj := (G.mem_neighborFinset v w).mp hw
      obtain ⟨x, hxv, hxw⟩ := Finset.not_disjoint_iff.mp hadj.2
      exact Finset.mem_biUnion.mpr ⟨x, hxv, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxw⟩⟩
    calc
      G.degree v = (G.neighborFinset v).card := (G.card_neighborFinset_eq_degree v).symm
      _ ≤ _ := Finset.card_le_card hsub
      _ ≤ ∑ x ∈ R v, (Finset.univ.filter (fun w => x ∈ R w)).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _x ∈ R v, Δ := Finset.sum_le_sum (fun x _ => hload x)
      _ = (R v).card * Δ := by simp
      _ ≤ k * Δ := Nat.mul_le_mul_right Δ (hsize v)
  obtain ⟨I, hI, hcard⟩ := degree_independent_set_size G (k * Δ) hdeg
  refine ⟨I, ?_, by simpa only [Nat.add_comm] using hcard⟩
  intro v hv w hw hne
  by_contra hd
  exact hI hv hw hne ⟨hne, hd⟩

/-- If [0 < r < 1](hyp:hr), then [under independent coordinate inclusion with
probability r, the probability that T is not entirely included is one minus
r raised to the number of coordinates in T](goal). -/
-- @node: degree_requirement_failure_probability
lemma degree_requirement_failure_probability {X : Type} [Fintype X] [DecidableEq X]
    (r : ℝ) (hr : CompressionDensity r) (T : Finset X) :
    (productMeasure X r).Pr (fun z => ¬ T ⊆ toFinset' z) = 1 - r ^ T.card := by
  have h := (productMeasure X r).Pr_split (fun _ => True) (fun z => T ⊆ toFinset' z)
  have hone : (productMeasure X r).Pr (fun _ => True) = 1 :=
    (productMeasure X r).E_const 1
  have hyes : (productMeasure X r).Pr (fun z => True ∧ T ⊆ toFinset' z) = r ^ T.card := by
    calc
      _ = (productMeasure X r).Pr (fun z => T ⊆ toFinset' z) :=
        (productMeasure X r).Pr_congr _ _ (fun _ => by simp)
      _ = _ := compression_inclusion_probability r hr T
  have hno : (productMeasure X r).Pr (fun z => True ∧ ¬ T ⊆ toFinset' z) =
      (productMeasure X r).Pr (fun z => ¬ T ⊆ toFinset' z) :=
    (productMeasure X r).Pr_congr _ _ (fun _ => by simp)
  rw [hone, hyes, hno] at h
  linarith

/-- If [0 < r < 1](hyp:hr) and [the requirements indexed by I are pairwise
disjoint](hyp:hI), then [under independent coordinate inclusion with probability
r, the probability that every requirement in I fails is the product over I
of one minus r raised to each requirement's size](goal). -/
-- @node: degree_disjoint_failure_product
lemma degree_disjoint_failure_product {V X : Type}
    [Fintype X] [DecidableEq X] (r : ℝ) (hr : CompressionDensity r)
    (R : V → Finset X) (I : Finset V)
    (hI : (I : Set V).Pairwise (fun v w => Disjoint (R v) (R w))) :
    (productMeasure X r).Pr (fun z => ∀ v ∈ I, ¬ R v ⊆ toFinset' z) =
      ∏ v ∈ I, (1 - r ^ (R v).card) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    rw [(productMeasure X r).Pr_congr _ (fun _ => True) (by
      intro z
      simp only [Finset.notMem_empty, false_implies, implies_true])]
    exact (productMeasure X r).E_const 1
  | @insert v I hv ih =>
    have htail : (I : Set V).Pairwise (fun v w => Disjoint (R v) (R w)) :=
      hI.mono (by intro w hw; exact Finset.mem_insert_of_mem hw)
    have hsep : ∀ w ∈ I, Disjoint (R v) (R w) := by
      intro w hw
      exact hI (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hw)
        (fun heq => hv (heq ▸ hw))
    let f := FiniteDesign.ind (fun z : X → Bool => ¬ R v ⊆ toFinset' z)
    let g := FiniteDesign.ind (fun z : X → Bool => ∀ w ∈ I, ¬ R w ⊆ toFinset' z)
    have hpoint (z : X → Bool) :
        FiniteDesign.ind (fun z => ∀ w ∈ insert v I, ¬ R w ⊆ toFinset' z) z = f z * g z := by
      simp only [Finset.mem_insert, forall_eq_or_imp]
      by_cases hf : ¬ R v ⊆ toFinset' z <;>
        by_cases hg : ∀ w ∈ I, ¬ R w ⊆ toFinset' z <;>
          simp [f, g, FiniteDesign.ind, hf, hg]
    have hfactor : (productMeasure X r).E (fun z => f z * g z) =
        (productMeasure X r).E f * (productMeasure X r).E g := by
      dsimp [productMeasure]
      rw [Toolkit.Foundations.Probability.bernoulliCube_eq r hr.1.le hr.2.le]
      apply FiniteDesign.E_prod_block_mul _ (R v)
      · intro z z' hz
        have heq : R v ⊆ toFinset' z ↔ R v ⊆ toFinset' z' := by
          simp only [compression_subset_bits]
          exact forall₂_congr fun x hx => by rw [hz x hx]
        simp only [f, FiniteDesign.ind, heq]
      · intro z z' hz
        have heq : (∀ w ∈ I, ¬ R w ⊆ toFinset' z) ↔
            ∀ w ∈ I, ¬ R w ⊆ toFinset' z' := by
          apply forall₂_congr
          intro w hw
          apply not_congr
          simp only [compression_subset_bits]
          apply forall₂_congr
          intro x hx
          rw [hz x (fun hxv => Finset.disjoint_left.mp (hsep w hw) hxv hx)]
        simp only [g, FiniteDesign.ind, heq]
    change (productMeasure X r).E _ = _
    rw [FiniteDesign.E_congr _ hpoint, hfactor]
    change (productMeasure X r).Pr _ * (productMeasure X r).Pr _ = _
    rw [degree_requirement_failure_probability r hr, ih htail, Finset.prod_insert hv]

/-- If [0 < r < 1](hyp:hr), [the requirements indexed by I are pairwise
disjoint](hyp:hI), and [each has size at most k](hyp:hsize), then [under
independent coordinate inclusion with probability r, the probability that
all of them fail is at most exp(−|I| rᵏ)](goal). -/
-- @node: degree_disjoint_failure_exp
lemma degree_disjoint_failure_exp {V X : Type}
    [Fintype X] [DecidableEq X] (r : ℝ) (hr : CompressionDensity r)
    (R : V → Finset X) (I : Finset V) (k : ℕ)
    (hI : (I : Set V).Pairwise (fun v w => Disjoint (R v) (R w)))
    (hsize : ∀ v ∈ I, (R v).card ≤ k) :
    (productMeasure X r).Pr (fun z => ∀ v ∈ I, ¬ R v ⊆ toFinset' z) ≤
      Real.exp (-(I.card : ℝ) * r ^ k) := by
  rw [degree_disjoint_failure_product r hr R I hI]
  calc
    _ ≤ ∏ _v ∈ I, Real.exp (-(r ^ k)) := by
      apply Finset.prod_le_prod
      · intro v hv
        have := pow_le_one₀ hr.1.le hr.2.le (n := (R v).card)
        linarith
      · intro v hv
        have hp : r ^ k ≤ r ^ (R v).card :=
          pow_le_pow_of_le_one hr.1.le hr.2.le (hsize v hv)
        have he := Real.add_one_le_exp (-(r ^ k))
        linarith
    _ = Real.exp (-(I.card : ℝ) * r ^ k) := by
      rw [Finset.prod_const, ← Real.exp_nat_mul]
      congr 1
      ring

/-- If [0 < r < 1](hyp:hr), [the requirements indexed by I are pairwise
disjoint](hyp:hI), and [each has at most k coordinates](hyp:hsize), then [in
an array of independent Bernoulli trials with success probability r, the
probability that no candidate in B satisfies any requirement in I is at most
exp(−|B| |I| rᵏ)](goal). -/
-- @node: degree_candidate_failure_exp
lemma degree_candidate_failure_exp {V X C : Type}
    [Fintype X] [DecidableEq X] [Fintype C] [DecidableEq C]
    (r : ℝ) (hr : CompressionDensity r) (R : V → Finset X)
    (I : Finset V) (B : Finset C) (k : ℕ)
    (hI : (I : Set V).Pairwise (fun v w => Disjoint (R v) (R w)))
    (hsize : ∀ v ∈ I, (R v).card ≤ k) :
    (productMeasure (X × C) r).Pr
      (fun z => ∀ v ∈ I, ∀ c ∈ B, ¬ ∀ x ∈ R v, z (x, c) = true) ≤
        Real.exp (-(B.card : ℝ) * I.card * r ^ k) := by
  classical
  let T : V × C → Finset (X × C) := fun a => (R a.1).product {a.2}
  have hT : (↑(I.product B) : Set (V × C)).Pairwise
      (fun a b => Disjoint (T a) (T b)) := by
    intro a ha b hb hne
    obtain ⟨haI, haB⟩ := Finset.mem_product.mp ha
    obtain ⟨hbI, hbB⟩ := Finset.mem_product.mp hb
    apply Finset.disjoint_left.mpr
    intro p hpa hpb
    obtain ⟨hxa, hca⟩ := Finset.mem_product.mp hpa
    obtain ⟨hxb, hcb⟩ := Finset.mem_product.mp hpb
    have hab : a.1 ≠ b.1 := by
      intro hab
      apply hne
      exact Prod.ext hab ((Finset.mem_singleton.mp hca).symm.trans
        (Finset.mem_singleton.mp hcb))
    exact Finset.disjoint_left.mp (hI haI hbI hab) hxa hxb
  have hcard (a : V × C) (ha : a ∈ I.product B) : (T a).card ≤ k := by
    simpa [T] using hsize a.1 (Finset.mem_product.mp ha).1
  have heq (z : X × C → Bool) :
      (∀ a ∈ I.product B, ¬ T a ⊆ toFinset' z) ↔
        ∀ v ∈ I, ∀ c ∈ B, ¬ ∀ x ∈ R v, z (x, c) = true := by
    have hrow (v : V) (c : C) :
        T (v, c) ⊆ toFinset' z ↔ ∀ x ∈ R v, z (x, c) = true := by
      simp [T, compression_subset_bits]
    constructor
    · intro h v hv c hc
      exact fun hs => h (v, c) (Finset.mem_product.mpr ⟨hv, hc⟩) ((hrow v c).mpr hs)
    · intro h a ha hs
      exact h a.1 (Finset.mem_product.mp ha).1 a.2 (Finset.mem_product.mp ha).2
        ((hrow a.1 a.2).mp hs)
  rw [← (productMeasure (X × C) r).Pr_congr _ _ heq]
  have h := degree_disjoint_failure_exp r hr T (I.product B) k hT hcard
  rw [Finset.product_eq_sprod, Finset.card_product, Nat.cast_mul] at h
  convert h using 1
  · congr 1
  · congr 1; ring

/-- If [0 < r < 1](hyp:hr), [each requirement has at most k coordinates](hyp:hsize),
and [each coordinate occurs in at most Δ requirements](hyp:hload), then [in
an independent Bernoulli array with success probability r, the probability
that no candidate in B satisfies any requirement is at most
exp(−|B| |V| rᵏ/(1 + kΔ))](goal). -/
-- @node: degree_hall_failure_probability
lemma degree_hall_failure_probability {V X C : Type} [Fintype V]
    [Fintype X] [DecidableEq X] [Fintype C] [DecidableEq C]
    (r : ℝ) (hr : CompressionDensity r) (R : V → Finset X)
    (B : Finset C) (k Δ : ℕ)
    (hsize : ∀ v, (R v).card ≤ k)
    (hload : ∀ x, (Finset.univ.filter (fun v => x ∈ R v)).card ≤ Δ) :
    (productMeasure (X × C) r).Pr
      (fun z => ∀ v, ∀ c ∈ B, ¬ ∀ x ∈ R v, z (x, c) = true) ≤
        Real.exp (-(B.card : ℝ) * Fintype.card V * r ^ k / (1 + (k : ℝ) * Δ)) := by
  classical
  obtain ⟨I, hI, hcard⟩ := degree_disjoint_requirements R k Δ hsize hload
  calc
    _ ≤ (productMeasure (X × C) r).Pr
        (fun z => ∀ v ∈ I, ∀ c ∈ B, ¬ ∀ x ∈ R v, z (x, c) = true) :=
      FiniteDesign.Pr_mono _ _ _ (fun z hz v _ c hc => hz v c hc)
    _ ≤ Real.exp (-(B.card : ℝ) * I.card * r ^ k) :=
      by
        convert degree_candidate_failure_exp r hr R I B k hI (fun v _ => hsize v) using 1
        congr 1
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hc : (Fintype.card V : ℝ) ≤ (1 + (k : ℝ) * Δ) * I.card := by
        exact_mod_cast hcard
      have hp : 0 ≤ (B.card : ℝ) * r ^ k :=
        mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hr.1.le _)
      apply (le_div_iff₀ (by positivity : 0 < 1 + (k : ℝ) * Δ)).mpr
      nlinarith [mul_le_mul_of_nonneg_left hc hp]

/-- Suppose [0 < r < 1](hyp:hr), [the old host set Y and candidate bin B are
disjoint](hyp:hYB), [each requirement on Y has at most k vertices](hyp:hsize),
and [each vertex of Y occurs in at most Δ requirements](hyp:hload). Then
[in the random host with edge probability r, the probability that no vertex
of B is adjacent to every vertex of any requirement is at most
exp(−|B| |V| rᵏ/(1 + kΔ))](goal). -/
-- @node: degree_host_hall_failure
lemma degree_host_hall_failure {V : Type} [Fintype V] {n : ℕ}
    (r : ℝ) (hr : CompressionDensity r) (Y B : Finset (Fin n))
    (hYB : Disjoint Y B) (R : V → Finset ↥Y) (k Δ : ℕ)
    (hsize : ∀ v, (R v).card ≤ k)
    (hload : ∀ y, (Finset.univ.filter (fun v => y ∈ R v)).card ≤ Δ) :
    (randomHost n r ⟨hr.1.le, hr.2.le⟩).Pr (fun z => ∀ v, ∀ c ∈ B,
      ¬ ∀ y ∈ R v, (hostGraph z).Adj c y.val) ≤
        Real.exp (-(B.card : ℝ) * Fintype.card V * r ^ k / (1 + (k : ℝ) * Δ)) := by
  classical
  have hc (c : ↥B) : c.val ∉ Y := by
    intro hy
    exact Finset.disjoint_left.mp hYB hy c.property
  let e : ↥Y × ↥B → KEdge n := fun a => neighborhoodEdge Y a.2.val (hc a.2) a.1
  have hinj : Function.Injective e := by
    intro a b hab
    have he := congrArg Subtype.val hab
    simp only [e, neighborhoodEdge, Sym2.eq_iff] at he
    rcases he with he | he
    · exact Prod.ext (Subtype.ext he.2) (Subtype.ext he.1)
    · exact (hc a.2 (he.1 ▸ b.1.property)).elim
  have hadj (z : KEdge n → Bool) (c : ↥B) (y : ↥Y) :
      (hostGraph z).Adj c.val y.val ↔ z (e (y, c)) = true := by
    have hne : c.val ≠ y.val := fun h => hc c (h ▸ y.property)
    simp [hostGraph, SimpleGraph.fromEdgeSet_adj, e, neighborhoodEdge, hne]
  let P := fun z : (↥Y × ↥B) → Bool =>
    ∀ v, ∀ c ∈ (Finset.univ : Finset ↥B), ¬ ∀ y ∈ R v, z (y, c) = true
  have hevent (z : KEdge n → Bool) :
      (∀ v, ∀ c ∈ B, ¬ ∀ y ∈ R v, (hostGraph z).Adj c y.val) ↔
        P (fun a => z (e a)) := by
    constructor
    · intro h v c _ hs
      exact h v c.val c.property (fun y hy => (hadj z c y).mpr (hs y hy))
    · intro h v c hcB hs
      exact h v ⟨c, hcB⟩ (Finset.mem_univ _) (fun y hy => (hadj z ⟨c, hcB⟩ y).mp (hs y hy))
  have hprob : (randomHost n r ⟨hr.1.le, hr.2.le⟩).Pr
      (fun z => ∀ v, ∀ c ∈ B, ¬ ∀ y ∈ R v, (hostGraph z).Adj c y.val) =
        (productMeasure (↥Y × ↥B) r).Pr P := by
    rw [(randomHost n r ⟨hr.1.le, hr.2.le⟩).Pr_congr _ _ hevent]
    exact productMeasure_E_comp_injective r e hinj (FiniteDesign.ind P)
  rw [hprob]
  have h := degree_hall_failure_probability r hr R (Finset.univ : Finset ↥B) k Δ hsize hload
  simpa only [Finset.card_univ, Fintype.card_coe] using h

end Papers.OaiGraphDecompositionsIntegral

module
public import Papers.OaiGraphDecompositionsIntegral.Helpers.DegreeHallLayer

/-! # Adaptive requirements and accumulated layer losses

Partitioning the past by the chosen requirement family lets the fixed-family
fresh-edge estimate apply to an embedding chosen from the earlier exposures.
The resulting losses add over the deterministic sequence of layers.
-/

public section

open Causalean.Experimentation.DesignBased
open scoped BigOperators

namespace Papers.OaiGraphDecompositionsIntegral

attribute [local instance] Classical.propDecidable

/-- [The probability of event A equals the sum, over all possible choices, of the
probability that A occurs and that choice is selected](goal). -/
-- @node: degree_probability_choice_partition
lemma degree_probability_choice_partition {Ω I : Type} [Fintype Ω] [Fintype I]
    (D : FiniteDesign Ω) (choose : Ω → I) (A : Ω → Prop) :
    D.Pr A = ∑ i, D.Pr (fun z => A z ∧ choose z = i) := by
  classical
  unfold FiniteDesign.Pr
  rw [← FiniteDesign.E_sum]
  apply D.E_congr
  intro z
  by_cases hz : A z <;> simp [FiniteDesign.ind, hz]

/-- If [for each choice, the joint probability of A, that choice, and its failure
is at most ε times the probability of A and that choice](hyp:hfiber), then
[the probability of A and failure of the selected choice is at most ε times
the probability of A](goal). -/
-- @node: degree_adaptive_failure_of_fibers
lemma degree_adaptive_failure_of_fibers {Ω I : Type} [Fintype Ω] [Fintype I]
    (D : FiniteDesign Ω) (choose : Ω → I) (A : Ω → Prop)
    (F : I → Ω → Prop) (ε : ℝ)
    (hfiber : ∀ i, D.Pr (fun z => (A z ∧ choose z = i) ∧ F i z) ≤
      D.Pr (fun z => A z ∧ choose z = i) * ε) :
    D.Pr (fun z => A z ∧ F (choose z) z) ≤ D.Pr A * ε := by
  classical
  calc
    _ = ∑ i, D.Pr (fun z => (A z ∧ F (choose z) z) ∧ choose z = i) := by
      convert degree_probability_choice_partition D choose (fun z => A z ∧ F (choose z) z)
        using 1
      · congr!
      · apply Finset.sum_congr rfl
        intro i hi
        congr!
    _ = ∑ i, D.Pr (fun z => (A z ∧ choose z = i) ∧ F i z) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply D.Pr_congr
      intro z
      constructor
      · rintro ⟨⟨ha, hf⟩, hc⟩
        exact ⟨⟨ha, hc⟩, hc ▸ hf⟩
      · rintro ⟨⟨ha, hc⟩, hf⟩
        exact ⟨⟨ha, hc.symm ▸ hf⟩, hc⟩
    _ ≤ ∑ i, D.Pr (fun z => A z ∧ choose z = i) * ε :=
      Finset.sum_le_sum (fun i _ => hfiber i)
    _ = D.Pr A * ε := by
      rw [← Finset.sum_mul, ← degree_probability_choice_partition D choose A]

/-- Suppose [the edge probability r lies strictly between zero and one](hyp:hr),
[the old vertex set Y and fresh bin B are disjoint](hyp:hYB), [n is at least
two](hyp:hn), and [there are at most n source vertices](hyp:hV). If [every
requirement has at most k vertices](hyp:hsize), [each old vertex occurs in at
most Δ requirements for each choice](hyp:hload), [B has at least b more vertices
than the source set](hyp:hB), [b rᵏ/(1 + kΔ) is at least 5 log n](hyp:hexp),
and [event A depends only on edges within Y](hyp:hA) and [the requirement-family
choice depends only on edges within Y](hyp:hchoose), then [the probability of A and failure to assign distinct
vertices in B satisfying the chosen adjacency requirements is at most the
probability of A times 2/n³](goal). -/
-- @node: degree_adaptive_layer_failure_bound
lemma degree_adaptive_layer_failure_bound {V I : Type} [Fintype V] [Fintype I]
    (n : ℕ) (r : ℝ) (hr : CompressionDensity r) (Y B : Finset (Fin n))
    (hYB : Disjoint Y B) (R : I → V → Finset ↥Y) (k Δ b : ℕ) (hn : 2 ≤ n)
    (hV : Fintype.card V ≤ n) (hsize : ∀ i v, (R i v).card ≤ k)
    (hload : ∀ i y, (Finset.univ.filter (fun v => y ∈ R i v)).card ≤ Δ)
    (hB : Fintype.card V + b ≤ B.card)
    (hexp : 5 * naturalLog n ≤ (b : ℝ) * r ^ k / (1 + (k : ℝ) * Δ))
    (A : (KEdge n → Bool) → Prop) (choose : (KEdge n → Bool) → I)
    (hA : ∀ z z', (∀ a ∈ Y, ∀ c ∈ Y,
      (hostGraph z).Adj a c ↔ (hostGraph z').Adj a c) → (A z ↔ A z'))
    (hchoose : ∀ z z', (∀ a ∈ Y, ∀ c ∈ Y,
      (hostGraph z).Adj a c ↔ (hostGraph z').Adj a c) → choose z = choose z') :
    (randomHost n r ⟨hr.1.le, hr.2.le⟩).Pr (fun z => A z ∧
      ¬ ∃ f : V → Fin n, Function.Injective f ∧
        ∀ v, f v ∈ B ∧ ∀ y ∈ R (choose z) v, (hostGraph z).Adj (f v) y.val) ≤
      (randomHost n r ⟨hr.1.le, hr.2.le⟩).Pr A * (2 / (n : ℝ) ^ 3) := by
  classical
  have hfiber (i : I) := degree_fresh_layer_failure_bound n r hr Y B hYB (R i)
    k Δ b hn hV (hsize i) (hload i) hB hexp (fun z => A z ∧ choose z = i)
    (by
      intro z z' hz
      rw [hchoose z z' hz]
      exact and_congr (hA z z' hz) Iff.rfl)
  convert degree_adaptive_failure_of_fibers (randomHost n r ⟨hr.1.le, hr.2.le⟩) choose A
    (fun i z => ¬ ∃ f : V → Fin n, Function.Injective f ∧
      ∀ v, f v ∈ B ∧ ∀ y ∈ R i v, (hostGraph z).Adj (f v) y.val)
    (2 / (n : ℝ) ^ 3) (by
      intro i
      convert hfiber i using 1 <;> congr!)
    using 1 <;> congr!

/-- If [the probability of A occurring without M is at most ε times the
probability of A](hyp:hfail), then [the probability of A and M is at least
(1 − ε) times the probability of A](goal). -/
-- @node: degree_adaptive_layer_success_of_failure
lemma degree_adaptive_layer_success_of_failure {Ω : Type} [Fintype Ω]
    (D : FiniteDesign Ω) (A M : Ω → Prop) (ε : ℝ)
    (hfail : D.Pr (fun z => A z ∧ ¬ M z) ≤ D.Pr A * ε) :
    (1 - ε) * D.Pr A ≤ D.Pr (fun z => A z ∧ M z) := by
  have hsplit := D.Pr_split A M
  linarith

/-- Suppose [ε is nonnegative](hyp:hε), [the initial event always occurs](hyp:hzero),
[each event through stage t implies the preceding event](hyp:hnested), and
[the probability of losing success at each stage is at most ε times the
probability of success before that stage](hyp:hloss). Then [the probability
of success at stage t is at least 1 − tε](goal). -/
-- @node: degree_layer_iteration_probability
lemma degree_layer_iteration_probability {Ω : Type} [Fintype Ω]
    (D : FiniteDesign Ω) (A : ℕ → Ω → Prop) (t : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (hzero : ∀ z, A 0 z)
    (hnested : ∀ j < t, ∀ z, A (j + 1) z → A j z)
    (hloss : ∀ j < t, D.Pr (fun z => A j z ∧ ¬ A (j + 1) z) ≤ D.Pr (A j) * ε) :
    1 - (t : ℝ) * ε ≤ D.Pr (A t) := by
  have hstep (j : ℕ) (hj : j < t) : D.Pr (A j) - ε ≤ D.Pr (A (j + 1)) := by
    have hsplit := D.Pr_split (A j) (A (j + 1))
    have heq : D.Pr (fun z => A j z ∧ A (j + 1) z) = D.Pr (A (j + 1)) :=
      D.Pr_congr _ _ (fun z => ⟨fun h => h.2, fun h => ⟨hnested j hj z h, h⟩⟩)
    rw [heq] at hsplit
    have hbound := (hloss j hj).trans
      (mul_le_of_le_one_left hε (D.Pr_le_one (A j)))
    linarith
  have hind : ∀ j, j ≤ t → 1 - (j : ℝ) * ε ≤ D.Pr (A j) := by
    intro j
    induction j with
    | zero =>
      intro hj
      have heq : D.Pr (A 0) = 1 := by
        calc
          _ = D.Pr (fun _ => True) := D.Pr_congr _ _ (fun z => iff_true_intro (hzero z))
          _ = 1 := D.E_const 1
      simp [heq]
    | succ j ih =>
      intro hj
      have hprev := ih (by omega)
      have hs := hstep j (by omega)
      push_cast
      linarith
  exact hind t le_rfl

/-- If [f is injective on the old vertex set S](hyp:hf), [f maps S into Y](hyp:hfY),
and [every vertex in layer I has at most k neighbors in S](hyp:hdeg), then
[there is a requirement family on Y for I whose members are exactly the
images of old neighbors, whose sizes are at most k, and in which each vertex
of Y occurs at most as often as the maximum degree of G](goal). -/
-- @node: degree_layer_requirements_exists
lemma degree_layer_requirements_exists {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S I : Finset V)
    (n k : ℕ) (Y : Finset (Fin n)) (f : V → Fin n)
    (hf : Set.InjOn f (S : Set V)) (hfY : ∀ w ∈ S, f w ∈ Y)
    (hdeg : ∀ v ∈ I, (G.neighborFinset v ∩ S).card ≤ k) :
    ∃ R : ↥I → Finset ↥Y,
      (∀ v y, y ∈ R v ↔ ∃ w ∈ S, G.Adj v.val w ∧ f w = y.val) ∧
      (∀ v, (R v).card ≤ k) ∧
      ∀ y, (Finset.univ.filter (fun v => y ∈ R v)).card ≤ G.maxDegree := by
  classical
  let e : ↥S ↪ ↥Y := ⟨fun w => ⟨f w.val, hfY w.val w.property⟩, by
    intro a b hab
    exact Subtype.ext (hf a.property b.property (congrArg Subtype.val hab))⟩
  let T : ↥I → Finset ↥S := fun v =>
    Finset.univ.filter (fun w => G.Adj v.val w.val)
  let R : ↥I → Finset ↥Y := fun v => (T v).map e
  have hmem (v : ↥I) (y : ↥Y) :
      y ∈ R v ↔ ∃ w ∈ S, G.Adj v.val w ∧ f w = y.val := by
    constructor
    · intro hy
      obtain ⟨w, hw, heq⟩ := Finset.mem_map.mp hy
      exact ⟨w.val, w.property, (Finset.mem_filter.mp hw).2,
        congrArg Subtype.val heq⟩
    · rintro ⟨w, hw, hvw, heq⟩
      exact Finset.mem_map.mpr ⟨⟨w, hw⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvw⟩, Subtype.ext heq⟩
  refine ⟨R, hmem, ?_, ?_⟩
  · intro v
    have himg : (T v).image Subtype.val = G.neighborFinset v.val ∩ S := by
      ext w
      constructor
      · rintro hw
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw
        exact Finset.mem_inter.mpr
          ⟨(G.mem_neighborFinset v.val a.val).mpr (Finset.mem_filter.mp ha).2, a.property⟩
      · intro hw
        obtain ⟨hadj, hwS⟩ := Finset.mem_inter.mp hw
        exact Finset.mem_image.mpr ⟨⟨w, hwS⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, (G.mem_neighborFinset v.val w).mp hadj⟩, rfl⟩
    have hc := congrArg Finset.card himg
    rw [Finset.card_image_of_injective _ Subtype.val_injective] at hc
    simpa only [R, Finset.card_map, hc] using hdeg v.val v.property
  · intro y
    let U := Finset.univ.filter (fun v : ↥I => y ∈ R v)
    by_cases hy : ∃ w ∈ S, f w = y.val
    · obtain ⟨w, hwS, hwy⟩ := hy
      have hsub : U.image Subtype.val ⊆ G.neighborFinset w := by
        intro v hv
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
        obtain ⟨b, hbS, hab, hby⟩ := (hmem a y).mp (Finset.mem_filter.mp ha).2
        have hbw : b = w := hf hbS hwS (hby.trans hwy.symm)
        subst b
        exact (G.mem_neighborFinset w a.val).mpr hab.symm
      have hc := Finset.card_le_card hsub
      rw [Finset.card_image_of_injective _ Subtype.val_injective,
        SimpleGraph.card_neighborFinset_eq_degree] at hc
      exact hc.trans (G.degree_le_maxDegree w)
    · have hU : U = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro v hv
        obtain ⟨w, hw, _, heq⟩ := (hmem v y).mp (Finset.mem_filter.mp hv).2
        exact hy ⟨w, hw, heq⟩
      change U.card ≤ G.maxDegree
      rw [hU]
      exact Nat.zero_le _

/-- Suppose [S and I are disjoint](hyp:hSI), [Y and B are disjoint](hyp:hYB),
[I is independent in G](hyp:hi), [f is injective on S](hyp:hf), and [g is
injective on I](hyp:hg). If [f maps S into Y](hyp:hfY), [g maps I into B](hyp:hgB),
[f preserves edges within S](hyp:hprev), and [g and f preserve edges from I
to S](hyp:hnew), then [there is an injective, edge-preserving map on S ∪ I
into Y ∪ B agreeing with f on S and g on I](goal). -/
-- @node: degree_extend_layer_embedding
lemma degree_extend_layer_embedding {V W : Type}
    (G : SimpleGraph V) (H : SimpleGraph W) (S I : Finset V) (Y B : Finset W)
    (hSI : Disjoint S I) (hYB : Disjoint Y B)
    (hi : G.IsIndepSet (I : Set V)) (f g : V → W)
    (hf : Set.InjOn f (S : Set V)) (hg : Set.InjOn g (I : Set V))
    (hfY : ∀ v ∈ S, f v ∈ Y) (hgB : ∀ v ∈ I, g v ∈ B)
    (hprev : ∀ v ∈ S, ∀ w ∈ S, G.Adj v w → H.Adj (f v) (f w))
    (hnew : ∀ v ∈ I, ∀ w ∈ S, G.Adj v w → H.Adj (g v) (f w)) :
    ∃ F : V → W, Set.InjOn F ((S ∪ I : Finset V) : Set V) ∧
      (∀ v ∈ S ∪ I, F v ∈ Y ∪ B) ∧
      (∀ v ∈ S ∪ I, ∀ w ∈ S ∪ I, G.Adj v w → H.Adj (F v) (F w)) ∧
      (∀ v ∈ S, F v = f v) ∧ (∀ v ∈ I, F v = g v) := by
  classical
  let F : V → W := fun v => if v ∈ I then g v else f v
  have hnot (v : V) (hv : v ∈ S) : v ∉ I :=
    fun hvI => Finset.disjoint_left.mp hSI hv hvI
  have hcross (v : V) (hv : v ∈ I) (w : V) (hw : w ∈ S) : g v ≠ f w := by
    intro heq
    exact Finset.disjoint_left.mp hYB (hfY w hw) (heq ▸ hgB v hv)
  have hfold (v : V) (hv : v ∈ S) : F v = f v := by simp [F, hnot v hv]
  have hfnew (v : V) (hv : v ∈ I) : F v = g v := by simp [F, hv]
  refine ⟨F, ?_, ?_, ?_, hfold, hfnew⟩
  · intro v hv w hw heq
    have hv' : v ∈ S ∨ v ∈ I := Finset.mem_union.mp hv
    have hw' : w ∈ S ∨ w ∈ I := Finset.mem_union.mp hw
    by_cases hvI : v ∈ I
    · rw [hfnew v hvI] at heq
      by_cases hwI : w ∈ I
      · rw [hfnew w hwI] at heq
        exact hg hvI hwI heq
      · have hwS := hw'.resolve_right hwI
        rw [hfold w hwS] at heq
        exact (hcross v hvI w hwS heq).elim
    · have hvS := hv'.resolve_right hvI
      rw [hfold v hvS] at heq
      by_cases hwI : w ∈ I
      · rw [hfnew w hwI] at heq
        exact (hcross w hwI v hvS heq.symm).elim
      · have hwS := hw'.resolve_right hwI
        rw [hfold w hwS] at heq
        exact hf hvS hwS heq
  · intro v hv
    by_cases hvI : v ∈ I
    · rw [hfnew v hvI]
      exact Finset.mem_union_right _ (hgB v hvI)
    · have hvS := (Finset.mem_union.mp hv).resolve_right hvI
      rw [hfold v hvS]
      exact Finset.mem_union_left _ (hfY v hvS)
  · intro v hv w hw hvw
    by_cases hvI : v ∈ I
    · by_cases hwI : w ∈ I
      · exact (hi hvI hwI hvw.ne hvw).elim
      · have hwS := (Finset.mem_union.mp hw).resolve_right hwI
        rw [hfnew v hvI, hfold w hwS]
        exact hnew v hvI w hwS hvw
    · have hvS := (Finset.mem_union.mp hv).resolve_right hvI
      by_cases hwI : w ∈ I
      · rw [hfold v hvS, hfnew w hwI]
        exact (hnew w hwI v hvS hvw.symm).symm
      · have hwS := (Finset.mem_union.mp hw).resolve_right hwI
        rw [hfold v hvS, hfold w hwS]
        exact hprev v hvS w hwS hvw

end Papers.OaiGraphDecompositionsIntegral

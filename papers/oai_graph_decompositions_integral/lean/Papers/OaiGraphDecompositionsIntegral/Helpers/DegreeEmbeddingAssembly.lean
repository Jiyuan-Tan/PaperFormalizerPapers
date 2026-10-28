module
public import Papers.OaiGraphDecompositionsIntegral.Helpers.DegreeAdaptiveLayers
public import Papers.OaiGraphDecompositionsIntegral.Helpers.DegreeLayerSetup
public import Mathlib.Data.Fintype.Sum

/-! # Assembling the fresh-bin layer embeddings

A partial embedding is selected solely from the induced host on the old bins.
The adaptive Hall estimate therefore applies without paying for its selection.
-/

@[expose] public section

open Causalean.Experimentation.DesignBased

namespace Papers.OaiGraphDecompositionsIntegral

attribute [local instance] Classical.propDecidable

variable {V : Type} [Fintype V] [DecidableEq V]

/-- For [a vertex population V](hyp:V), [a graph G on V](hyp:G), [an old vertex set S](hyp:S), [a host vertex set
Y](hyp:Y), [a configuration z of host edges](hyp:z), and [a vertex map f](hyp:f),
[being a partial embedding](goal) means that [f is injective on S](step:1),
[f maps S into Y](step:2), and [f preserves every edge of G within S in the
host graph determined by z](step:3). -/
-- @node: DegreePartialEmbedding
def DegreePartialEmbedding (G : SimpleGraph V) (S : Finset V)
    {n : ℕ} (Y : Finset (Fin n)) (z : KEdge n → Bool) (f : V → Fin n) : Prop :=
  Set.InjOn f (S : Set V) ∧ (∀ v ∈ S, f v ∈ Y) ∧
    ∀ v ∈ S, ∀ w ∈ S, G.Adj v w → (hostGraph z).Adj (f v) (f w)

omit [Fintype V] [DecidableEq V] in
/-- If [two host configurations have the same adjacencies within Y](hyp:hz),
then [f is a partial embedding of S into Y for one configuration exactly
when it is a partial embedding for the other](goal). -/
-- @node: degree_partial_embedding_past
lemma degree_partial_embedding_past (G : SimpleGraph V) (S : Finset V)
    {n : ℕ} (Y : Finset (Fin n)) (z z' : KEdge n → Bool)
    (hz : ∀ a ∈ Y, ∀ c ∈ Y, (hostGraph z).Adj a c ↔ (hostGraph z').Adj a c)
    (f : V → Fin n) :
    DegreePartialEmbedding G S Y z f ↔ DegreePartialEmbedding G S Y z' f := by
  constructor <;> rintro ⟨hinj, hY, hadj⟩
  · exact ⟨hinj, hY, fun v hv w hw he =>
      (hz _ (hY v hv) _ (hY w hw)).mp (hadj v hv w hw he)⟩
  · exact ⟨hinj, hY, fun v hv w hw he =>
      (hz _ (hY v hv) _ (hY w hw)).mpr (hadj v hv w hw he)⟩

/-- Suppose [the old set S and new layer I are disjoint](hyp:hSI), [I is
independent in G](hyp:hi), [0 < r < 1](hyp:hr), [the old host set Y and fresh
bin B are disjoint](hyp:hYB), [n is at least two](hyp:hn), and [G has at most
n vertices](hyp:hV). If [each vertex of I has at most k neighbors in S](hyp:hdeg),
[B has at least b more vertices than I](hyp:hB), and [b rᵏ divided by one plus
k times the maximum degree of G is at least 5 log n](hyp:hexp), then [the
probability of embedding S ∪ I into Y ∪ B is at least the probability of
embedding S into Y minus 2/n³](goal). -/
-- @node: degree_partial_embedding_step
lemma degree_partial_embedding_step (G : SimpleGraph V) [DecidableRel G.Adj]
    (S I : Finset V) (hSI : Disjoint S I) (hi : G.IsIndepSet (I : Set V))
    (n : ℕ) (r : ℝ) (hr : CompressionDensity r) (Y B : Finset (Fin n))
    (hYB : Disjoint Y B) (k b : ℕ) (hn : 2 ≤ n)
    (hV : Fintype.card V ≤ n)
    (hdeg : ∀ v ∈ I, (G.neighborFinset v ∩ S).card ≤ k)
    (hB : I.card + b ≤ B.card)
    (hexp : 5 * naturalLog n ≤ (b : ℝ) * r ^ k / (1 + (k : ℝ) * G.maxDegree)) :
    (randomHost n r ⟨hr.1.le, hr.2.le⟩).Pr (fun z => ∃ f, DegreePartialEmbedding G S Y z f) -
      2 / (n : ℝ) ^ 3 ≤
    (randomHost n r ⟨hr.1.le, hr.2.le⟩).Pr (fun z => ∃ f,
      DegreePartialEmbedding G (S ∪ I) (Y ∪ B) z f) := by
  classical
  let : Inhabited (Fin n) := ⟨⟨0, by omega⟩⟩
  let A := fun z => ∃ f, DegreePartialEmbedding G S Y z f
  let choose := fun z => Classical.epsilon (DegreePartialEmbedding G S Y z)
  let valid := fun f : V → Fin n => Set.InjOn f (S : Set V) ∧ ∀ w ∈ S, f w ∈ Y
  have hreq (f : V → Fin n) (hf : valid f) :=
    degree_layer_requirements_exists G S I n k Y f hf.1 hf.2 hdeg
  let R : (V → Fin n) → ↥I → Finset ↥Y := fun f =>
    if hf : valid f then Classical.choose (hreq f hf) else fun _ => ∅
  have hR (f : V → Fin n) (hf : valid f) :
      (∀ v y, y ∈ R f v ↔ ∃ w ∈ S, G.Adj v.val w ∧ f w = y.val) ∧
      (∀ v, (R f v).card ≤ k) ∧
      ∀ y, (Finset.univ.filter (fun v => y ∈ R f v)).card ≤ G.maxDegree := by
    simpa only [R, dif_pos hf] using Classical.choose_spec (hreq f hf)
  have hsize : ∀ f v, (R f v).card ≤ k := by
    intro f v
    by_cases hf : valid f
    · exact (hR f hf).2.1 v
    · simp [R, hf]
  have hload : ∀ f y, (Finset.univ.filter (fun v => y ∈ R f v)).card ≤ G.maxDegree := by
    intro f y
    by_cases hf : valid f
    · exact (hR f hf).2.2 y
    · simp [R, hf]
  have hchoose : ∀ z z', (∀ a ∈ Y, ∀ c ∈ Y,
      (hostGraph z).Adj a c ↔ (hostGraph z').Adj a c) → choose z = choose z' := by
    intro z z' hz
    have heq : DegreePartialEmbedding G S Y z = DegreePartialEmbedding G S Y z' := by
      funext f
      exact propext (degree_partial_embedding_past G S Y z z' hz f)
    exact congrArg Classical.epsilon heq
  let M := fun z => ∃ g : ↥I → Fin n, Function.Injective g ∧
    ∀ v, g v ∈ B ∧ ∀ y ∈ R (choose z) v, (hostGraph z).Adj (g v) y.val
  have hfail := degree_adaptive_layer_failure_bound n r hr Y B hYB R k G.maxDegree b hn
    (by simpa using (Finset.card_le_univ I).trans hV) hsize hload (by simpa using hB)
    hexp A choose (by
      intro z z' hz
      exact exists_congr (degree_partial_embedding_past G S Y z z' hz)) hchoose
  have hfailM : (randomHost n r ⟨hr.1.le, hr.2.le⟩).Pr (fun z => A z ∧ ¬ M z) ≤
      (randomHost n r ⟨hr.1.le, hr.2.le⟩).Pr A * (2 / (n : ℝ) ^ 3) := by
    convert hfail using 1 <;> congr!
  have hsplit := (randomHost n r ⟨hr.1.le, hr.2.le⟩).Pr_split A M
  have hmono : (randomHost n r ⟨hr.1.le, hr.2.le⟩).Pr (fun z => A z ∧ M z) ≤
      (randomHost n r ⟨hr.1.le, hr.2.le⟩).Pr (fun z => ∃ f,
        DegreePartialEmbedding G (S ∪ I) (Y ∪ B) z f) := by
    apply FiniteDesign.Pr_mono
    rintro z ⟨ha, g, hginj, hg⟩
    have hf : DegreePartialEmbedding G S Y z (choose z) := Classical.epsilon_spec ha
    have hvalid : valid (choose z) := ⟨hf.1, hf.2.1⟩
    let g' : V → Fin n := fun v => if h : v ∈ I then g ⟨v, h⟩ else default
    have hg'eq (v : V) (hv : v ∈ I) : g' v = g ⟨v, hv⟩ := by simp [g', hv]
    obtain ⟨F, hFinj, hFY, hFadj, _⟩ := degree_extend_layer_embedding G (hostGraph z)
      S I Y B hSI hYB hi (choose z) g' hf.1
      (by
        intro v hv w hw heq
        rw [hg'eq v hv, hg'eq w hw] at heq
        exact congrArg Subtype.val (hginj heq)) hf.2.1
      (by intro v hv; rw [hg'eq v hv]; exact (hg ⟨v, hv⟩).1) hf.2.2
      (by
        intro v hv w hw hvw
        rw [hg'eq v hv]
        exact (hg ⟨v, hv⟩).2 ⟨(choose z) w, hf.2.1 w hw⟩
          ((hR (choose z) hvalid).1 _ _ |>.mpr ⟨w, hw, hvw, rfl⟩))
    refine ⟨F, ?_, ?_, ?_⟩
    · simpa only [Finset.coe_union] using hFinj
    · simpa only [Finset.mem_union] using hFY
    · simpa only [Finset.mem_union] using hFadj
  have hε : 0 ≤ 2 / (n : ℝ) ^ 3 := by positivity
  have hmass := mul_le_of_le_one_left hε ((randomHost n r ⟨hr.1.le, hr.2.le⟩).Pr_le_one A)
  have hbound : (randomHost n r ⟨hr.1.le, hr.2.le⟩).Pr A - 2 / (n : ℝ) ^ 3 ≤
      (randomHost n r ⟨hr.1.le, hr.2.le⟩).Pr (fun z => A z ∧ M z) := by
    nlinarith only [hsplit, hfailM, hmass]
  exact hbound.trans hmono

/-- Given [a sequence L of independent-layer removals covering S with residual
degrees at most 4s](hyp:h), suppose [0 < r < 1](hyp:hr), [n is at least two](hyp:hn),
[G has at most n vertices](hyp:hV), and [b r⁴ˢ divided by one plus 4s times
the maximum degree of G is at least 5 log n](hyp:hexp). If [each assigned bin
has at least b more vertices than its layer](hyp:hbin) and [distinct bins are
disjoint](hyp:hdisj), then [the probability of a partial embedding of S into
the union of the bins is at least one minus the number of layers times
2/n³](goal). -/
-- @node: degree_layer_sequence_embedding_probability
lemma degree_layer_sequence_embedding_probability
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : ℕ)
    {S : Finset V} {L : List (Finset V)} (h : DegreeLayerSequence G s S L)
    (n : ℕ) (r : ℝ) (hr : CompressionDensity r) (hn : 2 ≤ n)
    (hV : Fintype.card V ≤ n) (b : ℕ)
    (hexp : 5 * naturalLog n ≤ (b : ℝ) * r ^ (4 * s) /
      (1 + ((4 * s : ℕ) : ℝ) * G.maxDegree))
    (bin : Fin L.length → Finset (Fin n))
    (hbin : ∀ i, (L.get i).card + b ≤ (bin i).card)
    (hdisj : Pairwise (fun i j => Disjoint (bin i) (bin j))) :
    1 - (L.length : ℝ) * (2 / (n : ℝ) ^ 3) ≤
      (randomHost n r ⟨hr.1.le, hr.2.le⟩).Pr (fun z => ∃ f,
        DegreePartialEmbedding G S (Finset.univ.biUnion bin) z f) := by
  classical
  let : Inhabited (Fin n) := ⟨⟨0, by omega⟩⟩
  induction h with
  | nil =>
    have heq : (randomHost n r ⟨hr.1.le, hr.2.le⟩).Pr (fun z => ∃ f,
        DegreePartialEmbedding G ∅ (Finset.univ.biUnion bin) z f) = 1 := by
      calc
        _ = (randomHost n r ⟨hr.1.le, hr.2.le⟩).Pr (fun _ => True) := by
          apply FiniteDesign.Pr_congr
          intro z
          exact iff_true_intro ⟨fun _ => default, by simp [DegreePartialEmbedding]⟩
        _ = 1 := (randomHost n r ⟨hr.1.le, hr.2.le⟩).E_const 1
    simpa using heq.ge
  | @cons S I L hIS hne hi hdeg htail ih =>
    let bins : Fin L.length → Finset (Fin n) := fun i => bin i.succ
    let Y := Finset.univ.biUnion bins
    let B := bin 0
    have hYB : Disjoint Y B := by
      apply Finset.disjoint_left.mpr
      intro x hxY hxB
      obtain ⟨j, _, hxj⟩ := Finset.mem_biUnion.mp hxY
      exact Finset.disjoint_left.mp (hdisj (by simp : j.succ ≠ 0)) hxj hxB
    have htailprob := ih bins (fun i => by simpa [bins] using hbin i.succ)
      (fun i j hij => hdisj (fun heq => hij (Fin.succ_inj.mp heq)))
    have hdegtail : ∀ v ∈ I, (G.neighborFinset v ∩ (S \ I)).card ≤ 4 * s := by
      intro v hv
      exact (Finset.card_le_card (Finset.inter_subset_inter_left
        Finset.sdiff_subset)).trans (hdeg v hv)
    have hstep := degree_partial_embedding_step G (S \ I) I
      Finset.sdiff_disjoint hi n r hr Y B hYB (4 * s) b hn hV hdegtail
      (by simpa [B] using hbin 0) hexp
    have hS : S \ I ∪ I = S := Finset.sdiff_union_of_subset hIS
    have hY : Y ∪ B = Finset.univ.biUnion bin := by
      ext x
      simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and,
        Y, bins, B]
      constructor
      · rintro (⟨i, hi⟩ | hi)
        · exact ⟨i.succ, hi⟩
        · exact ⟨0, hi⟩
      · rintro ⟨i, hi⟩
        refine Fin.cases ?_ (fun j => ?_) i hi
        · exact fun hx => Or.inr hx
        · exact fun hx => Or.inl ⟨j, hx⟩
    rw [hS, hY] at hstep
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    change 1 - ((L.length : ℝ) + 1) * (2 / (n : ℝ) ^ 3) ≤ _
    change 1 - (L.length : ℝ) * (2 / (n : ℝ) ^ 3) ≤
      (randomHost n r ⟨hr.1.le, hr.2.le⟩).Pr (fun z => ∃ f,
        DegreePartialEmbedding G (S \ I) Y z f) at htailprob
    linarith

omit [DecidableEq V] in
/-- If [G has at most n vertices](hyp:hV) and [f partially embeds all
nonisolated vertices of G into Y in the host configuration z](hyp:hf), then
[the host graph contains a copy of G](goal). -/
-- @node: degree_partial_embedding_containsCopy
lemma degree_partial_embedding_containsCopy (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} (hV : Fintype.card V ≤ n) (Y : Finset (Fin n))
    (z : KEdge n → Bool) (f : V → Fin n)
    (hf : DegreePartialEmbedding G (nonisolated G) Y z f) :
    ContainsCopy G (hostGraph z) := by
  classical
  obtain ⟨T, hT, hcard⟩ := Finset.exists_superset_card_eq
    ((Finset.card_image_le.trans (Finset.card_le_univ (nonisolated G))) :
      ((nonisolated G).image f).card ≤ Fintype.card V)
    (by simpa using hV)
  obtain ⟨g, hg⟩ := Finset.exists_equiv_extend_of_card_eq hcard.symm hT hf.1
  refine ⟨⟨⟨fun v => (g v).val, ?_⟩, ?_⟩⟩
  · intro v w hvw
    have hv : v ∈ nonisolated G := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hvw.degree_pos_left⟩
    have hw : w ∈ nonisolated G := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hvw.symm.degree_pos_left⟩
    rw [hg v hv, hg w hw]
    exact hf.2.2 v hv w hw hvw
  · intro v w heq
    exact g.injective (Subtype.ext heq)

/-- [There is a threshold N such that, whenever n is at least N, 0 < r < 1,
s is at most 10 log n, and rˢ is at least n⁻¹ᐟ¹⁰⁰, every finite graph G with
at most n vertices, at most n/4 nonisolated vertices, degeneracy at most s,
maximum degree at most n²ᐟ³, and at least one edge is contained in the random
host with edge probability r with probability at least one half](goal). -/
-- @node: degree_embedding_probability
lemma degree_embedding_probability :
    ∃ N : ℕ, ∀ (n : ℕ) (r : ℝ) (s : ℕ),
      N ≤ n → TransferParameters n r s →
      ∀ (V : Type) [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj],
        Fintype.card V ≤ n → DegreeEmbeddingBounds G n s → G.edgeSet.Nonempty →
        (1 / 2 : ℝ) ≤ containmentProb G n r := by
  obtain ⟨N, hNtwo, hN⟩ := degree_layer_setup_exists
  refine ⟨N, ?_⟩
  intro n r s hn hp V _ _ G _ hsize hb hedge
  classical
  obtain ⟨L, hL, ht, hlen, hexp, hloss⟩ := hN n r s hn hp V G hsize hb hedge
  obtain ⟨bin, hbin, hdisj, _⟩ := degree_layer_bins G s hL n hb.1 ht
  have hprob := degree_layer_sequence_embedding_probability G s hL n r
    ⟨hp.1, hp.2.1⟩ (by omega) hsize (layerSlack n L.length ht)
    (by simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using hexp)
    bin (fun i => (hbin i).ge) hdisj
  have hcopy : (randomHost n r ⟨hp.1.le, hp.2.1.le⟩).Pr (fun z => ∃ f,
      DegreePartialEmbedding G (nonisolated G) (Finset.univ.biUnion bin) z f) ≤
      containmentProb G n r := by
    apply FiniteDesign.Pr_mono
    rintro z ⟨f, hf⟩
    exact degree_partial_embedding_containsCopy G hsize _ z f hf
  linarith

end Papers.OaiGraphDecompositionsIntegral

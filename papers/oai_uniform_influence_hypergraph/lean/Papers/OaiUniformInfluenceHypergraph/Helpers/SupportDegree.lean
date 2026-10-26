module
public import Papers.OaiUniformInfluenceHypergraph.Basic
public import Mathlib.Data.Nat.Choose.Bounds

/-! # A low-degree vertex in a finite edge support

The vertex is chosen from the support before a random block is sampled.
-/

@[expose] public section

open scoped BigOperators

namespace Papers.OaiUniformInfluenceHypergraph

variable {n r : ℕ}

/-- The [support size](goal) of [a finite set of edges](hyp:S), each containing
[r vertices](hyp:r) from [n available vertices](hyp:n), is its number of edges. -/
def supportSize (S : Finset (Edge n r)) : ℕ := S.card -- @realizes s(number of edges in S)

/-- The [support vertices](goal) of [a finite set of edges](hyp:S), each containing
[r vertices](hyp:r) from [n available vertices](hyp:n), are all vertices belonging
to at least one of those edges. -/
def supportVertices (S : Finset (Edge n r)) : Finset (Fin n) :=
  S.biUnion (fun e => e.val) -- @realizes V(union of the support edges)

-- @realizes v(number of support vertices)
/-- The [support vertex count](goal) of [a finite set of edges](hyp:S), each
containing [r vertices](hyp:r) from [n available vertices](hyp:n), is the number
of distinct vertices occurring in those edges. -/
def supportVertexCount (S : Finset (Edge n r)) : ℕ := (supportVertices S).card

/-- The [support degree](goal) of [a vertex](hyp:u) in [a finite set of edges](hyp:S),
each containing [r vertices](hyp:r) from [n available vertices](hyp:n), is the
number of those edges containing that vertex. -/
def supportDegree (S : Finset (Edge n r)) (u : Fin n) : ℕ :=
  (S.filter (fun e => u ∈ e.val)).card -- @realizes d_S(u)(number of incident edges)

-- @node: support_card_le_choose
/-- [The number of edges in a finite support is at most the number of ways
to choose r vertices from the vertices occurring in that support](goal). -/
lemma support_card_le_choose (S : Finset (Edge n r)) :
    S.card ≤ (supportVertices S).card.choose r := by
  classical
  have hsub : S.image Subtype.val ⊆ (supportVertices S).powersetCard r := by
    intro e he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    exact Finset.mem_powersetCard.mpr ⟨fun u hu =>
      Finset.mem_biUnion.mpr ⟨a, ha, hu⟩, a.property⟩
  calc
    S.card = (S.image Subtype.val).card :=
      (Finset.card_image_of_injective S Subtype.val_injective).symm
    _ ≤ ((supportVertices S).powersetCard r).card := Finset.card_le_card hsub
    _ = _ := Finset.card_powersetCard r _

-- @node: supportVertices_card_le
/-- [The number of distinct vertices occurring in a finite support of edges
of size r is at most r times the number of edges](goal). -/
lemma supportVertices_card_le (S : Finset (Edge n r)) :
    (supportVertices S).card ≤ r * S.card := by
  calc
    (supportVertices S).card ≤ ∑ e ∈ S, e.val.card := Finset.card_biUnion_le
    _ = r * S.card := by
      calc
        (∑ e ∈ S, e.val.card) = ∑ _e ∈ S, r :=
          Finset.sum_congr rfl (fun e _ => e.property)
        _ = _ := by simp [Nat.mul_comm]

-- @node: sum_supportDegree
/-- [The sum of support degrees over all vertices occurring in a finite
edge support equals r times the number of edges](goal). -/
lemma sum_supportDegree (S : Finset (Edge n r)) :
    ∑ u ∈ supportVertices S, supportDegree S u = r * S.card := by
  classical
  simp only [supportDegree, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  have he : ∀ e ∈ S, ∑ u ∈ supportVertices S, (if u ∈ e.val then 1 else 0) = r := by
    intro e he
    rw [← Finset.sum_filter]
    have hf : (supportVertices S).filter (fun u => u ∈ e.val) = e.val := by
      ext u
      simp only [Finset.mem_filter, and_iff_right_iff_imp]
      exact fun hu => Finset.mem_biUnion.mpr ⟨e, he, hu⟩
    rw [hf]
    simpa using e.property
  calc
    (∑ e ∈ S, ∑ u ∈ supportVertices S, if u ∈ e.val then 1 else 0) = ∑ _e ∈ S, r :=
      Finset.sum_congr rfl he
    _ = _ := by simp [Nat.mul_comm]

-- @node: exists_support_vertex_degree_le
/-- Suppose [each edge has at least three vertices](hyp:hr), [the edge size is
at most the available vertex count](hyp:hrn), [the degree cutoff k is positive](hyp:hk),
and [the edge support is nonempty and has at most (k/r) raised to r/(r − 1)
edges](hyp:hS). Then [some vertex in the support has degree at least one, at
most the number of support edges, and at most k](goal). -/
lemma exists_support_vertex_degree_le (r n : ℕ) (hr : 3 ≤ r) (hrn : r ≤ n)
    (k : ℝ) (hk : CapturePositiveCutoff k) (S : Finset (Edge n r))
    (hS : CaptureSupport S (supportCutoff r k)) :
    ∃ u ∈ supportVertices S, -- @realizes u(support vertex chosen from S before sampling B)
      1 ≤ supportDegree S u ∧ supportDegree S u ≤ S.card ∧ (supportDegree S u : ℝ) ≤ k := by
  classical
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hrone : (1 : ℝ) < r := by exact_mod_cast (show 1 < r by omega)
  have hspos : (0 : ℝ) < S.card := by
    exact_mod_cast (show 0 < S.card from hS.1)
  have hV : (supportVertices S).Nonempty := by
    obtain ⟨e, he⟩ := Finset.card_pos.mp (show 0 < S.card from hS.1)
    obtain ⟨u, hu⟩ := Finset.card_pos.mp (show 0 < e.val.card by rw [e.property]; omega)
    exact ⟨u, Finset.mem_biUnion.mpr ⟨e, he, hu⟩⟩
  have hcount : (S.card : ℝ) ≤ ((supportVertices S).card : ℝ) ^ r := by
    exact_mod_cast (support_card_le_choose S).trans
      (Nat.choose_le_pow (supportVertices S).card r)
  have hroot : (S.card : ℝ) ^ (1 / (r : ℝ)) ≤ (supportVertices S).card := by
    have h := Real.rpow_le_rpow (Nat.cast_nonneg S.card) hcount
      (show 0 ≤ 1 / (r : ℝ) by positivity)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _),
      mul_one_div_cancel hrpos.ne', Real.rpow_one] at h
    exact h
  have hpower : (S.card : ℝ) ^ (((r : ℝ) - 1) / r) ≤ k / r := by
    have h := Real.rpow_le_rpow (Nat.cast_nonneg S.card) hS.2
      (show 0 ≤ ((r : ℝ) - 1) / r by positivity)
    change (S.card : ℝ) ^ (((r : ℝ) - 1) / r) ≤
      ((k / r) ^ ((r : ℝ) / ((r : ℝ) - 1))) ^ (((r : ℝ) - 1) / r) at h
    rw [← Real.rpow_mul (show 0 ≤ k / (r : ℝ) by exact (div_pos hk hrpos).le)] at h
    have hexp : (r : ℝ) / ((r : ℝ) - 1) * (((r : ℝ) - 1) / r) = 1 := by
      field_simp [hrpos.ne', (sub_pos.mpr hrone).ne']
    rw [hexp, Real.rpow_one] at h
    exact h
  have hmass : (r : ℝ) * S.card ≤ k * (supportVertices S).card := by
    have hsplit : (S.card : ℝ) =
        (S.card : ℝ) ^ (((r : ℝ) - 1) / r) * (S.card : ℝ) ^ (1 / (r : ℝ)) := by
      rw [← Real.rpow_add hspos]
      have hexp : ((r : ℝ) - 1) / r + 1 / (r : ℝ) = 1 := by field_simp; ring
      rw [hexp, Real.rpow_one]
    have hmul := mul_le_mul hpower hroot (Real.rpow_nonneg hspos.le _)
      (show 0 ≤ k / (r : ℝ) from (div_pos hk hrpos).le)
    rw [← hsplit] at hmul
    have := mul_le_mul_of_nonneg_left hmul hrpos.le
    nlinarith [div_mul_cancel₀ k hrpos.ne']
  have hexists : ∃ u ∈ supportVertices S, (supportDegree S u : ℝ) ≤ k := by
    by_contra h
    push Not at h
    have hsum := Finset.sum_lt_sum_of_nonempty hV h
    have hsumdeg : (∑ u ∈ supportVertices S, (supportDegree S u : ℝ)) =
        (r : ℝ) * S.card := by exact_mod_cast sum_supportDegree S
    simp only [Finset.sum_const, nsmul_eq_mul] at hsum
    rw [hsumdeg] at hsum
    nlinarith
  obtain ⟨u, hu, hku⟩ := hexists
  refine ⟨u, hu, ?_, ?_, hku⟩
  · obtain ⟨e, he, hue⟩ := Finset.mem_biUnion.mp hu
    exact Finset.one_le_card.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hue⟩⟩
  · exact Finset.card_filter_le _ _

-- @node: captured_edges_eq_incident
/-- If [a vertex belongs to the edge support](hyp:hu) and [the block intersects
the support vertices in exactly that vertex](hyp:hB), [the support edges meeting
the block are exactly the support edges containing that vertex](goal). -/
lemma captured_edges_eq_incident (S : Finset (Edge n r)) (B : Finset (Fin n))
    (u : Fin n) (hu : u ∈ supportVertices S) (hB : B ∩ supportVertices S = {u}) :
    S ∩ freeEdges B = S.filter (fun e => u ∈ e.val) := by
  classical
  have huB : u ∈ B := by
    have : u ∈ B ∩ supportVertices S := by rw [hB]; simp
    exact (Finset.mem_inter.mp this).1
  ext e
  simp only [Finset.mem_inter, freeEdges, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨he, v, hv⟩
    obtain ⟨hve, hvB⟩ := Finset.mem_inter.mp hv
    have hvV : v ∈ supportVertices S := Finset.mem_biUnion.mpr ⟨e, he, hve⟩
    have hvu : v = u := by
      have : v ∈ B ∩ supportVertices S := Finset.mem_inter.mpr ⟨hvB, hvV⟩
      simpa [hB] using this
    exact ⟨he, hvu ▸ hve⟩
  · rintro ⟨he, hue⟩
    exact ⟨he, u, Finset.mem_inter.mpr ⟨hue, huB⟩⟩

end Papers.OaiUniformInfluenceHypergraph

module
public import Papers.OaiUniformInfluenceHypergraph.Helpers.SupportDegree

/-! # Probability that a block captures a support at one vertex -/

public section

open scoped BigOperators
open Causalean.Experimentation.DesignBased

namespace Papers.OaiUniformInfluenceHypergraph

/-- If [there are at least two vertices](hyp:hn), [the block size is at least one](hyp:hm),
[the block size does not exceed the vertex count](hyp:hmn), and [u belongs to the
vertex set V](hyp:hu), then [the probability that a uniform m-vertex block meets V
exactly at u is at least m/n times one minus (the size of V minus one) times
(m − 1)/(n − 1)](goal). -/
-- @node: block_single_support_vertex_probability_ge
lemma block_single_support_vertex_probability_ge (n m : ℕ) (hn : 2 ≤ n)
    (hm : 1 ≤ m) (hmn : m ≤ n) (V : Finset (Fin n)) (u : Fin n) (hu : u ∈ V) :
    (m : ℝ) / n * (1 - ((V.card : ℝ) - 1) * (((m : ℝ) - 1) / ((n : ℝ) - 1))) ≤
      (blockLaw n m hmn).Pr (fun B => B.val ∩ V = {u}) := by
  classical
  let D := blockLaw n m hmn
  have hpoint (B : {B : Finset (Fin n) // B.card = m}) :
      FiniteDesign.ind (fun B => u ∈ B.val) B -
        ∑ v ∈ V.erase u, FiniteDesign.ind (fun B => u ∈ B.val ∧ v ∈ B.val) B ≤
      FiniteDesign.ind (fun B => B.val ∩ V = {u}) B := by
    have hnonneg : 0 ≤ ∑ v ∈ V.erase u,
        FiniteDesign.ind (fun B => u ∈ B.val ∧ v ∈ B.val) B :=
      Finset.sum_nonneg (fun _ _ => FiniteDesign.ind_nonneg _ _)
    by_cases hgood : B.val ∩ V = {u}
    · have huB : u ∈ B.val := by
        have : u ∈ B.val ∩ V := by rw [hgood]; simp
        exact (Finset.mem_inter.mp this).1
      simp only [FiniteDesign.ind, huB, hgood, if_true] at *
      linarith
    · by_cases huB : u ∈ B.val
      · have hex : ∃ v ∈ V.erase u, v ∈ B.val := by
          by_contra h
          apply hgood
          ext v
          simp only [Finset.mem_inter, Finset.mem_singleton]
          constructor
          · rintro ⟨hvB, hvV⟩
            by_contra hvu
            exact h ⟨v, Finset.mem_erase.mpr ⟨hvu, hvV⟩, hvB⟩
          · rintro rfl
            exact ⟨huB, hu⟩
        obtain ⟨v, hv, hvB⟩ := hex
        have hone : (1 : ℝ) ≤ ∑ v ∈ V.erase u,
            FiniteDesign.ind (fun B => u ∈ B.val ∧ v ∈ B.val) B := by
          calc
            (1 : ℝ) = FiniteDesign.ind (fun B => u ∈ B.val ∧ v ∈ B.val) B := by
              simp [FiniteDesign.ind, huB, hvB]
            _ ≤ _ := Finset.single_le_sum (f := fun v => FiniteDesign.ind
              (fun B => u ∈ B.val ∧ v ∈ B.val) B)
              (fun _ _ => FiniteDesign.ind_nonneg _ _) hv
        simp only [FiniteDesign.ind, huB, hgood, if_true, if_false] at *
        linarith
      · simp [FiniteDesign.ind, huB, hgood]
  have hE : D.Pr (fun B => u ∈ B.val) -
      ∑ v ∈ V.erase u, D.Pr (fun B => u ∈ B.val ∧ v ∈ B.val) ≤
        D.Pr (fun B => B.val ∩ V = {u}) := by
    unfold FiniteDesign.Pr
    rw [← D.E_sum, ← D.E_sub]
    exact Finset.sum_le_sum (fun B _ => mul_le_mul_of_nonneg_left (hpoint B) (D.p_nonneg B))
  have hfirst : D.Pr (fun B => u ∈ B.val) = (m : ℝ) / n := by
    simpa [D, blockLaw] using completeRandomization_incl m
      (by simpa using hmn) u
  have hpair (v : Fin n) (hv : v ∈ V.erase u) :
      D.Pr (fun B => u ∈ B.val ∧ v ∈ B.val) =
        ((m : ℝ) * ((m : ℝ) - 1)) / ((n : ℝ) * ((n : ℝ) - 1)) := by
    simpa [D, blockLaw] using completeRandomization_incl_pair m
      (by simpa using hmn) (Finset.ne_of_mem_erase hv).symm
  rw [hfirst, Finset.sum_congr rfl hpair] at hE
  have hcard : ((V.erase u).card : ℝ) = (V.card : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem hu, Nat.cast_sub (Finset.one_le_card.mpr ⟨u, hu⟩)]
    simp
  simp only [Finset.sum_const, nsmul_eq_mul, hcard] at hE
  simp only [div_mul_eq_div_div] at hE
  convert hE using 1 <;> ring

-- @node: block_single_support_vertex_probability_ge_half
/-- Assume [3 ≤ r ≤ n and 1 ≤ m ≤ n](hyp:hd), [the capture cutoff k is positive](hyp:hk),
[r times the support cutoff times (m − 1)/(n − 1) is at most one half](hyp:hc),
[the edge support is nonempty and has size at most the support cutoff](hyp:hS),
and [u is a vertex of that support](hyp:hu). Then [a uniform m-vertex block meets
the support's vertices exactly at u with probability at least m/(2n)](goal). -/
lemma block_single_support_vertex_probability_ge_half (n r m : ℕ) (k : ℝ)
    (hd : CaptureDomain n r m) (hk : CapturePositiveCutoff k)
    (hc : CaptureCondition r n m k) (S : Finset (Edge n r))
    (hS : CaptureSupport S (supportCutoff r k)) (u : Fin n) (hu : u ∈ supportVertices S) :
    (m : ℝ) / (2 * n) ≤
      (blockLaw n m hd.2.2.2).Pr (fun B => B.val ∩ supportVertices S = {u}) := by
  have hn : 2 ≤ n := by have := hd.1; have := hd.2.1; omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hratio : 0 ≤ ((m : ℝ) - 1) / ((n : ℝ) - 1) :=
    div_nonneg (by
      have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast hd.2.2.1
      linarith) (by
      have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
      linarith)
  have hv : ((supportVertices S).card : ℝ) ≤ (r : ℝ) * supportCutoff r k := by
    calc
      ((supportVertices S).card : ℝ) ≤ (r : ℝ) * S.card := by
        exact_mod_cast supportVertices_card_le S
      _ ≤ _ := mul_le_mul_of_nonneg_left hS.2 (Nat.cast_nonneg r)
  have hbad : (((supportVertices S).card : ℝ) - 1) *
      (((m : ℝ) - 1) / ((n : ℝ) - 1)) ≤ 1 / 2 := by
    exact (mul_le_mul_of_nonneg_right (by linarith :
      ((supportVertices S).card : ℝ) - 1 ≤ (r : ℝ) * supportCutoff r k) hratio).trans hc
  calc
    (m : ℝ) / (2 * n) = ((m : ℝ) / n) * (1 / 2) := by ring
    _ ≤ ((m : ℝ) / n) * (1 - (((supportVertices S).card : ℝ) - 1) *
        (((m : ℝ) - 1) / ((n : ℝ) - 1))) :=
      mul_le_mul_of_nonneg_left (by linarith) (div_nonneg (Nat.cast_nonneg m) hnpos.le)
    _ ≤ _ := block_single_support_vertex_probability_ge n m hn hd.2.2.1 hd.2.2.2
      (supportVertices S) u hu

-- @node: lem:capture
/-- Assume [3 ≤ r ≤ n and 1 ≤ m ≤ n](hyp:hd), [the capture cutoff k is positive](hyp:hk),
[r times the support cutoff times (m − 1)/(n − 1) is at most one half](hyp:hc), and
[the edge support is nonempty and has size at most the support cutoff](hyp:hS).
Then [a uniform m-vertex block meets between one and k support edges with
probability at least m/(2n)](goal). -/
lemma blockProb_capture_ge (n r m : ℕ) (k : ℝ) (hd : CaptureDomain n r m)
    (hk : CapturePositiveCutoff k) (hc : CaptureCondition r n m k)
    (S : Finset (Edge n r)) (hS : CaptureSupport S (supportCutoff r k)) :
    (m : ℝ) / (2 * n) ≤ blockCaptureProb n r m hd.2.2.2 k S := by
  classical
  obtain ⟨u, hu, hdegree, _, hkdegree⟩ :=
    exists_support_vertex_degree_le r n hd.1 hd.2.1 k hk S hS
  refine (block_single_support_vertex_probability_ge_half n r m k hd hk hc S hS u hu).trans ?_
  apply (blockLaw n m hd.2.2.2).Pr_mono
  intro B hB
  rw [captured_edges_eq_incident S B.val u hu hB]
  exact ⟨hdegree, hkdegree⟩

end Papers.OaiUniformInfluenceHypergraph

module
public import Papers.OaiSharpThresholdMonotone.Helpers.SupportDegree
public import Papers.OaiSharpThresholdMonotone.Helpers.BlockAverage
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Uniform-block capture of each small support -/

public section

open scoped BigOperators
open Causalean.Experimentation.DesignBased

namespace Papers.OaiSharpThresholdMonotone

-- @node: sqrtBlockSize_le
/-- [The integer part of the square root of the vertex count never exceeds the
vertex count itself](goal). -/
lemma sqrtBlockSize_le (n : ℕ) : sqrtBlockSize n ≤ n := by
  exact Nat.sqrt_le_self n

-- @node: capture_block_parameters
/-- If [the natural logarithm of the vertex count n is at least 16](hyp:hn), then
[the block size floor √n lies between 3 and n, and its natural logarithm is at least
one third of log n](goal). -/
lemma capture_block_parameters (n : ℕ) (hn : CaptureLogSize n) :
    BlockSize (sqrtBlockSize n) n ∧
      Real.log (n : ℝ) / 3 ≤ Real.log (sqrtBlockSize n : ℝ) := by
  have ht : 16 ≤ Real.log (n : ℝ) := hn
  have hn0 : 0 < n := by
    by_contra h
    have : n = 0 := by omega
    norm_num [this] at ht
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
  have hnlarge : 9 ≤ n := by
    have := Real.log_le_sub_one_of_pos hnpos
    have : (9 : ℝ) ≤ n := by linarith
    exact_mod_cast this
  have hm : 3 ≤ sqrtBlockSize n := Nat.le_sqrt.mpr hnlarge
  have hmpos : (0 : ℝ) < sqrtBlockSize n := by exact_mod_cast (by omega : 0 < sqrtBlockSize n)
  have hupper : (n : ℝ) < (2 * (sqrtBlockSize n : ℝ)) ^ 2 := by
    have h := Nat.lt_succ_sqrt' n
    have h' : (n : ℝ) < ((sqrtBlockSize n : ℝ) + 1) ^ 2 := by
      exact_mod_cast h
    have hm1 : (1 : ℝ) ≤ sqrtBlockSize n := by exact_mod_cast (by omega : 1 ≤ sqrtBlockSize n)
    nlinarith
  have hlog := Real.log_le_log hnpos hupper.le
  rw [Real.log_pow, Real.log_mul (by norm_num) hmpos.ne'] at hlog
  norm_num at hlog
  have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  exact ⟨⟨hm, sqrtBlockSize_le n⟩, by linarith⟩

-- @node: block_single_support_vertex_probability_ge
/-- Suppose [there are at least two vertices](hyp:hn),
[the block size m is at least one](hyp:hm),
[m does not exceed the vertex count n](hyp:hmn), and
[the designated vertex u belongs to the vertex set V](hyp:hu). Then
[a uniformly sampled m-vertex block intersects V in exactly u with probability at
least m/n times one minus (the size of V minus one) times (m−1)/(n−1)](goal). -/
lemma block_single_support_vertex_probability_ge (n m : ℕ) (hn : 2 ≤ n)
    (hm : 1 ≤ m) (hmn : m ≤ n) (V : Finset (Fin n)) (u : Fin n) (hu : u ∈ V) :
    (m : ℝ) / n * (1 - ((V.card : ℝ) - 1) * (((m : ℝ) - 1) / ((n : ℝ) - 1))) ≤
      (blockLaw n m hmn).Pr (fun B => B.val ∩ V = {u}) := by
  classical
  let π := blockLaw n m hmn
  have hi : π.Pr (fun B => u ∈ B.val) = (m : ℝ) / n := by
    simpa [π, blockLaw] using completeRandomization_incl m
      ((Fintype.card_fin n).symm ▸ hmn) u
  have hij (v : Fin n) (hv : v ∈ V.erase u) :
      π.Pr (fun B => u ∈ B.val ∧ v ∈ B.val) =
        (m : ℝ) * ((m : ℝ) - 1) / ((n : ℝ) * ((n : ℝ) - 1)) := by
    simpa [π, blockLaw] using completeRandomization_incl_pair m
      ((Fintype.card_fin n).symm ▸ hmn) (Finset.mem_erase.mp hv).1.symm
  have hpoint (B : {B : Finset (Fin n) // B.card = m}) :
      FiniteDesign.ind (fun B => u ∈ B.val) B -
        ∑ v ∈ V.erase u, FiniteDesign.ind (fun B => u ∈ B.val ∧ v ∈ B.val) B ≤
      FiniteDesign.ind (fun B => B.val ∩ V = {u}) B := by
    by_cases huB : u ∈ B.val
    · by_cases hBV : B.val ∩ V = {u}
      · have hnonneg : 0 ≤ ∑ v ∈ V.erase u,
            FiniteDesign.ind (fun B => u ∈ B.val ∧ v ∈ B.val) B :=
          Finset.sum_nonneg (fun v _ => FiniteDesign.ind_nonneg _ _)
        simp only [FiniteDesign.ind, huB, hBV, if_true] at *
        linarith
      · have hex : ∃ v ∈ V.erase u, v ∈ B.val := by
          by_contra h
          apply hBV
          ext v
          simp only [Finset.mem_inter, Finset.mem_singleton]
          constructor
          · rintro ⟨hvB, hvV⟩
            by_contra hvu
            exact h ⟨v, Finset.mem_erase.mpr ⟨hvu, hvV⟩, hvB⟩
          · rintro rfl
            exact ⟨huB, hu⟩
        obtain ⟨v, hv, hvB⟩ := hex
        have hone := Finset.single_le_sum
          (fun w (_ : w ∈ V.erase u) => FiniteDesign.ind_nonneg
            (fun B : {B : Finset (Fin n) // B.card = m} => u ∈ B.val ∧ w ∈ B.val) B) hv
        simp only [FiniteDesign.ind, huB, hvB, and_self, hBV, if_true, if_false] at *
        linarith
    · have hBV : B.val ∩ V ≠ {u} := by
        intro h
        have : u ∈ B.val ∩ V := by rw [h]; simp
        exact huB (Finset.mem_inter.mp this).1
      simp [FiniteDesign.ind, huB, hBV]
  have hbound : π.Pr (fun B => u ∈ B.val) -
      ∑ v ∈ V.erase u, π.Pr (fun B => u ∈ B.val ∧ v ∈ B.val) ≤
      π.Pr (fun B => B.val ∩ V = {u}) := by
    unfold FiniteDesign.Pr
    rw [← π.E_sum, ← π.E_sub]
    exact Finset.sum_le_sum (fun B _ =>
      mul_le_mul_of_nonneg_left (hpoint B) (π.p_nonneg B))
  have hcard : ((V.erase u).card : ℝ) = (V.card : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem hu, Nat.cast_sub (Finset.one_le_card.mpr ⟨u, hu⟩)]
    norm_num
  rw [hi] at hbound
  have hsum : (∑ v ∈ V.erase u, π.Pr (fun B => u ∈ B.val ∧ v ∈ B.val)) =
      ∑ _v ∈ V.erase u, (m : ℝ) * ((m : ℝ) - 1) / ((n : ℝ) * ((n : ℝ) - 1)) :=
    Finset.sum_congr rfl hij
  rw [hsum] at hbound
  rw [Finset.sum_const, nsmul_eq_mul, hcard] at hbound
  convert hbound using 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring


-- @node: capture_exponential_overlap_le
/-- If [t is at least 16](hyp:ht), then
[t squared times exp(−t/2) is at most one half](goal). -/
lemma capture_exponential_overlap_le (t : ℝ) (ht : 16 ≤ t) :
    t ^ 2 * Real.exp (-t / 2) ≤ 1 / 2 := by
  have hanti : AntitoneOn (fun x : ℝ => x ^ 2 * Real.exp (-x / 2)) (Set.Ici 16) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici (16 : ℝ))
      (f' := fun x => (2 * x - x ^ 2 / 2) * Real.exp (-x / 2))
    · fun_prop
    · intro x hx
      have hd := ((hasDerivAt_id x).pow 2).mul
        ((((hasDerivAt_id x).neg).div_const 2).exp)
      convert hd.hasDerivWithinAt using 1 <;> first | rfl | (dsimp; ring)
    · intro x hx
      have hx16 : 16 ≤ x := (interior_subset hx : x ∈ Set.Ici (16 : ℝ))
      apply mul_nonpos_of_nonpos_of_nonneg _ (Real.exp_nonneg _)
      nlinarith
  have hmono := hanti (by norm_num : (16 : ℝ) ∈ Set.Ici 16) ht ht
  have he : (512 : ℝ) ≤ Real.exp 8 := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 8) 6
    norm_num [Finset.sum_range_succ] at h
    linarith
  have hcancel : Real.exp 8 * Real.exp (-8) = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hmul := mul_le_mul_of_nonneg_right he (Real.exp_nonneg (-8))
  norm_num at hmono
  nlinarith

-- @node: capture_support_overlap_le
/-- Suppose [the natural logarithm of the vertex count n is at least 16](hyp:hn),
[the edge probability lies strictly between zero and one](hyp:hp), and
[the edge set S is nonempty and has size at most half the square of the low-degree
cutoff for blocks of size floor √n](hyp:hS). Then
[the number of vertices incident to S, minus one, times (floor √n minus one)/(n−1)
is at most one half](goal). -/
lemma capture_support_overlap_le (n : ℕ) (hn : CaptureLogSize n)
    (p : ℝ) (hp : BiasInterior p) (S : Finset (GraphEdge n))
    (hS : 1 ≤ S.card ∧ (S.card : ℝ) ≤ lowCutoff p (sqrtBlockSize n) ^ 2 / 2) :
    (((supportVertices S).card : ℝ) - 1) *
      (((sqrtBlockSize n : ℝ) - 1) / ((n : ℝ) - 1)) ≤ 1 / 2 := by
  obtain ⟨⟨hm3, hmn⟩, hlog⟩ := capture_block_parameters n hn
  have ht : 16 ≤ Real.log (n : ℝ) := hn
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast (hm3.trans hmn)
  have hnpos : (0 : ℝ) < n := by linarith
  have hn1 : 0 < (n : ℝ) - 1 := by linarith
  have hmR : (3 : ℝ) ≤ sqrtBlockSize n := by exact_mod_cast hm3
  have hmlog0 : 0 ≤ Real.log (sqrtBlockSize n : ℝ) :=
    Real.log_nonneg (by linarith)
  have hmlog : Real.log (sqrtBlockSize n : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by linarith) (by exact_mod_cast hmn)
  have hk0 : 0 ≤ lowCutoff p (sqrtBlockSize n) := by
    unfold lowCutoff
    exact div_nonneg (mul_nonneg (biasScale_pos_le_half p hp).1.le hmlog0) (by norm_num)
  have hk : lowCutoff p (sqrtBlockSize n) ≤ Real.log (n : ℝ) := by
    unfold lowCutoff
    have hσ := (biasScale_pos_le_half p hp).2
    have hmul := mul_le_mul_of_nonneg_right hσ hmlog0
    linarith
  have hv : ((supportVertices S).card : ℝ) - 1 ≤ Real.log (n : ℝ) ^ 2 := by
    have hV : ((supportVertices S).card : ℝ) ≤ 2 * (S.card : ℝ) := by
      exact_mod_cast supportVertices_card_le S
    nlinarith [hS.2]
  have he : Real.exp (Real.log (n : ℝ) / 2) ^ 2 = n := by
    rw [← Real.exp_nat_mul]
    convert Real.exp_log hnpos using 1 <;> ring
  have hepos := Real.exp_pos (Real.log (n : ℝ) / 2)
  have hmsq : (sqrtBlockSize n : ℝ) ^ 2 ≤ n := by
    exact_mod_cast Nat.sqrt_le' n
  have hmexp : (sqrtBlockSize n : ℝ) ≤ Real.exp (Real.log (n : ℝ) / 2) := by
    nlinarith
  have hcancel : Real.exp (Real.log (n : ℝ) / 2) *
      Real.exp (-Real.log (n : ℝ) / 2) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  have hN : (n : ℝ) * Real.exp (-Real.log (n : ℝ) / 2) =
      Real.exp (Real.log (n : ℝ) / 2) := by
    nth_rw 1 [← he]
    rw [pow_two, mul_assoc, hcancel, mul_one]
  have hneg : Real.exp (-Real.log (n : ℝ) / 2) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have hratio : ((sqrtBlockSize n : ℝ) - 1) / ((n : ℝ) - 1) ≤
      Real.exp (-Real.log (n : ℝ) / 2) := by
    apply (div_le_iff₀ hn1).mpr
    nlinarith [hN]
  calc
    _ ≤ Real.log (n : ℝ) ^ 2 *
        (((sqrtBlockSize n : ℝ) - 1) / ((n : ℝ) - 1)) :=
      mul_le_mul_of_nonneg_right hv (div_nonneg (by linarith) hn1.le)
    _ ≤ Real.log (n : ℝ) ^ 2 * Real.exp (-Real.log (n : ℝ) / 2) :=
      mul_le_mul_of_nonneg_left hratio (sq_nonneg _)
    _ ≤ _ := capture_exponential_overlap_le _ ht

-- @node: block_capture_probability_ge
/-- Suppose [the natural logarithm of the vertex count n is at least 16](hyp:hn),
[the edge probability lies strictly between zero and one](hyp:hp), and
[S is a nonempty edge set of size at most half the square of the low-degree cutoff
for blocks of size floor √n](hyp:hS). Then
[a uniformly sampled block of that size meets S in between one and the low-degree
cutoff many edges with probability at least floor √n divided by 2n](goal).

The capturing event may depend on `S`; no common block is asserted. -/
lemma block_capture_probability_ge (n : ℕ) (hn : CaptureLogSize n)
    (p : ℝ) (hp : BiasInterior p)
    (S : Finset (GraphEdge n))
    (hS : 1 ≤ S.card ∧ (S.card : ℝ) ≤ lowCutoff p (sqrtBlockSize n) ^ 2 / 2) :
    (sqrtBlockSize n : ℝ) / (2 * n) ≤
      (blockLaw n (sqrtBlockSize n) (sqrtBlockSize_le n)).Pr (fun B =>
        1 ≤ (S ∩ freeEdges B.val).card ∧
        ((S ∩ freeEdges B.val).card : ℝ) ≤ lowCutoff p (sqrtBlockSize n)) := by
  classical
  obtain ⟨hm, hlog⟩ := capture_block_parameters n hn
  obtain ⟨hm3, hmn⟩ := hm
  have hn2 : 2 ≤ n := by omega
  have hmpos : (0 : ℝ) < sqrtBlockSize n := by exact_mod_cast (by omega : 0 < sqrtBlockSize n)
  have hk : 0 ≤ lowCutoff p (sqrtBlockSize n) := by
    unfold lowCutoff
    exact div_nonneg (mul_nonneg (biasScale_pos_le_half p hp).1.le
      (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ sqrtBlockSize n)))) (by norm_num)
  obtain ⟨u, hu, hdpos, _, hdsqrt⟩ := exists_support_vertex_degree_le S hS.1
  have hdk : (supportDegree S u : ℝ) ≤ lowCutoff p (sqrtBlockSize n) := by
    apply hdsqrt.trans
    apply (Real.sqrt_le_iff).mpr
    exact ⟨hk, by linarith [hS.2]⟩
  have hprob := block_single_support_vertex_probability_ge n (sqrtBlockSize n)
    hn2 (by omega) (sqrtBlockSize_le n) (supportVertices S) u hu
  have hover := capture_support_overlap_le n hn p hp S hS
  calc
    _ = (sqrtBlockSize n : ℝ) / n * (1 / 2) := by ring
    _ ≤ (sqrtBlockSize n : ℝ) / n *
        (1 - (((supportVertices S).card : ℝ) - 1) *
          (((sqrtBlockSize n : ℝ) - 1) / ((n : ℝ) - 1))) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ ≤ _ := hprob
    _ ≤ _ := by
      apply FiniteDesign.Pr_mono
      intro B hB
      rw [captured_edges_eq_incident S B.val u hu hB]
      exact ⟨hdpos, hdk⟩

end Papers.OaiSharpThresholdMonotone

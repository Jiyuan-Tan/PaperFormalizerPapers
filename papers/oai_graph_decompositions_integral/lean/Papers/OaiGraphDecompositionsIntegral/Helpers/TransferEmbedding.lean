module
public import Papers.OaiGraphDecompositionsIntegral.Helpers.TransferConcentration
public import Papers.OaiGraphDecompositionsIntegral.Helpers.TransferAmplification
public import Papers.OaiGraphDecompositionsIntegral.Helpers.Hall
public import Mathlib.Data.Fintype.Sum

/-! # Compression and Hall verification for the transfer embedding -/

public section

open Causalean.Experimentation.DesignBased
open scoped BigOperators

namespace Papers.OaiGraphDecompositionsIntegral

attribute [local instance] Classical.propDecidable

-- @node: transfer_mem_neighborhoodIn
/-- [A vertex y in Y belongs to the neighborhood of w restricted to Y exactly when
w and y are adjacent in J](goal). -/
lemma transfer_mem_neighborhoodIn {n : ℕ} (Y : Finset (Fin n))
    (J : SimpleGraph (Fin n)) (w : Fin n) (y : ↥Y) :
    y ∈ neighborhoodIn Y J w ↔ J.Adj w y.val := by
  classical
  simp [neighborhoodIn]

-- @node: transfer_neighborhood_card
/-- If [every edge of J joins Y to its complement](hyp:hcross) and
[w lies outside Y](hyp:hw), then [the number of neighbors of w within Y equals
the degree of w in J](goal). -/
lemma transfer_neighborhood_card {n : ℕ} (Y : Finset (Fin n))
    (J : SimpleGraph (Fin n)) [DecidableRel J.Adj]
    (hcross : ∀ u v, J.Adj u v → (u ∈ Y ∧ v ∉ Y) ∨ (v ∈ Y ∧ u ∉ Y))
    (w : Fin n) (hw : w ∉ Y) : (neighborhoodIn Y J w).card = J.degree w := by
  classical
  have himage : (neighborhoodIn Y J w).image Subtype.val = J.neighborFinset w := by
    ext y
    simp only [Finset.mem_image, neighborhoodIn, Finset.mem_filter, Finset.mem_univ,
      true_and, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨v, hv, rfl⟩; exact hv
    · intro hy
      have hyY : y ∈ Y := (hcross w y hy).resolve_left (fun h => hw h.1) |>.1
      exact ⟨⟨y, hyY⟩, hy, rfl⟩
  have hcard := congrArg Finset.card himage
  simpa only [Finset.card_image_of_injective _ Subtype.coe_injective,
    SimpleGraph.card_neighborFinset_eq_degree] using hcard

-- @node: transfer_matching
/-- Suppose [r lies strictly between zero and one, s ≤ 10 log n, and r raised to s ≥
n to the power −1/100](hyp:hp); [Y has at most n to the power 2/3 vertices, J has only
edges across Y, J is contained in a source-test edge set, at most n/8 vertices outside Y
have positive degree, and their degrees are at most s](hyp:hconfiguration);
[Y has at most n/2 vertices](hyp:hhalf); and [Gstar passes all target tests](hyp:htarget).
Then [there is a map of the n vertices that is injective on the positive-degree vertices
outside Y and sends each of them outside Y to a vertex whose neighbors in Y in Gstar
include all its original neighbors in J](goal). -/
lemma transfer_matching {n s : ℕ} {r : ℝ} (hp : TransferParameters n r s)
    (Y : Finset (Fin n)) (J : SimpleGraph (Fin n)) [DecidableRel J.Adj]
    (hconfiguration : TransferConfiguration n s (sourceTestFamily n r s) Y J)
    (hhalf : 2 * Y.card ≤ n) (Gstar : SimpleGraph (Fin n))
    (htarget : TargetTests n r s Gstar) :
    ∃ f : Fin n → Fin n,
      Set.InjOn f ((Finset.univ \ Y).filter (fun w => 0 < J.degree w)) ∧
      ∀ w ∈ (Finset.univ \ Y).filter (fun w => 0 < J.degree w),
        f w ∉ Y ∧ neighborhoodIn Y J w ⊆ neighborhoodIn Y Gstar (f w) := by
  classical
  let U := (Finset.univ \ Y).filter (fun w => 0 < J.degree w)
  let cand := fun w => (Finset.univ \ Y).filter
    (fun a => neighborhoodIn Y J w ⊆ neighborhoodIn Y Gstar a)
  have hdata := hconfiguration
  obtain ⟨hY, hcross, ⟨G, hG, hJG⟩, hsize, hdeg⟩ := hdata
  have hcand : ∀ w ∈ U, cand w ⊆ Finset.univ \ Y :=
    fun _ _ => Finset.filter_subset _ _
  have hHall : ∀ V ⊆ U, V.card ≤ (V.biUnion cand).card := by
    intro V hVU
    by_cases hV : V.Nonempty
    · have hout : ∀ w ∈ V, w ∉ Y ∧ 0 < J.degree w := by
        intro w hw
        have hw := Finset.mem_filter.mp (hVU hw)
        exact ⟨(Finset.mem_sdiff.mp hw.1).2, hw.2⟩
      let R := V.image (neighborhoodIn Y J)
      have hR : CompressionFamily R s := by
        refine ⟨hV.image _, ?_⟩
        intro T hT
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hT
        rw [transfer_neighborhood_card Y J hcross w (hout w hw).1]
        exact ⟨(hout w hw).2, hdeg w (hout w hw).1⟩
      have hs : CompressionSize s := by
        obtain ⟨T, hT⟩ := hR.1
        exact (hR.2 T hT).1.trans (hR.2 T hT).2
      obtain ⟨Q, hQR, hQne, hQcard, hcompress⟩ :=
        compression r s R (show Finite ↥Y from inferInstance) ⟨hp.1, hp.2.1⟩ hs hR
      have hQ : AdmissibleTest r s Q :=
        ⟨⟨hQne, fun T hT => hR.2 T (hQR hT)⟩, hQcard⟩
      have hmpos : 0 < (n : ℝ) - Y.card := by
        obtain ⟨w, hw⟩ := hV
        have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le w.val) w.isLt
        have hlt : Y.card < n := by omega
        exact sub_pos.mpr (by exact_mod_cast hlt)
      have hsource := hG Y hY Q hQ
      have hsatisfy (w : Fin n) (hw : w ∈ V) :
          Satisfies R (neighborhoodIn Y (graphOfEdges G) w) := by
        refine ⟨neighborhoodIn Y J w, Finset.mem_image.mpr ⟨w, hw, rfl⟩, ?_⟩
        intro y hy
        have hy : J.Adj w y.val := (transfer_mem_neighborhoodIn Y J w y).mp hy
        exact (transfer_mem_neighborhoodIn Y (graphOfEdges G) w y).mpr (hJG hy)
      have hsum : (V.card : ℝ) / 2 ≤
          ∑ w ∈ Finset.univ \ Y, smoothedTest ↥Y r Q
            (neighborhoodIn Y (graphOfEdges G) w) := by
        calc
          _ = ∑ _w ∈ V, (1 / 2 : ℝ) := by simp; ring
          _ ≤ ∑ w ∈ V, smoothedTest ↥Y r Q
              (neighborhoodIn Y (graphOfEdges G) w) :=
            Finset.sum_le_sum (fun w hw => hcompress _ (hsatisfy w hw))
          _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
            (hVU.trans (Finset.filter_subset _ _)) (fun w _ _ => FiniteDesign.Pr_nonneg _ _)
      have hupper : (V.card : ℝ) ≤ 4 * xQ r Q * ((n : ℝ) - Y.card) := by
        change (1 / ((n : ℝ) - Y.card)) * _ ≤ 2 * xQ r Q at hsource
        have h := (div_le_iff₀ hmpos).mp
          (show (∑ w ∈ Finset.univ \ Y, smoothedTest ↥Y r Q
            (neighborhoodIn Y (graphOfEdges G) w)) / ((n : ℝ) - Y.card) ≤
              2 * xQ r Q by simpa only [div_eq_inv_mul, one_div, mul_one] using hsource)
        nlinarith
      let B := (Finset.univ \ Y).filter
        (fun a => Satisfies Q (neighborhoodIn Y Gstar a))
      have hBsub : B ⊆ V.biUnion cand := by
        intro a ha
        obtain ⟨haout, T, hT, hTa⟩ := Finset.mem_filter.mp ha
        obtain ⟨w, hw, hwT⟩ := Finset.mem_image.mp (hQR hT)
        apply Finset.mem_biUnion.mpr
        refine ⟨w, hw, Finset.mem_filter.mpr ⟨haout, ?_⟩⟩
        simpa only [hwT] using hTa
      have htarget' := htarget Y hY Q hQ
      have hlower : (3 / 4 : ℝ) * xStarQ r Q * ((n : ℝ) - Y.card) ≤ B.card := by
        apply (le_div_iff₀ hmpos).mp
        simpa only [B, div_eq_inv_mul, one_div, mul_one] using htarget'
      have hBcard : (V.card : ℝ) ≤ B.card := by
        obtain ⟨hsmall, hlarge⟩ := transfer_amplification_cases hp.1.le hp.2.1.le Q
        by_cases hx : xQ r Q ≤ 1 / 16
        · have h := mul_le_mul_of_nonneg_right (hsmall hx) hmpos.le
          have hx0 : 0 ≤ xQ r Q := FiniteDesign.Pr_nonneg _ _
          nlinarith [mul_nonneg hx0 hmpos.le]
        · have hx := hlarge (lt_of_not_ge hx)
          have h := mul_le_mul_of_nonneg_right hx hmpos.le
          have hU : (V.card : ℝ) ≤ (n : ℝ) / 8 :=
            (show (V.card : ℝ) ≤ U.card by exact_mod_cast Finset.card_le_card hVU).trans hsize
          have hh : 2 * (Y.card : ℝ) ≤ n := by exact_mod_cast hhalf
          nlinarith
      exact (by exact_mod_cast hBcard : V.card ≤ B.card).trans (Finset.card_le_card hBsub)
    · simp [Finset.not_nonempty_iff_eq_empty.mp hV]
  obtain ⟨f, hf, hmem⟩ := transfer_hall (sourceTestFamily n r s) Y J hconfiguration
    U cand (Finset.Subset.refl _) hcand hHall
  refine ⟨f, hf, ?_⟩
  intro w hw
  obtain ⟨ha, hsub⟩ := Finset.mem_filter.mp (hmem w hw)
  exact ⟨(Finset.mem_sdiff.mp ha).2, hsub⟩

-- @node: transfer_containsCopy
/-- Suppose [r lies strictly between zero and one, s ≤ 10 log n, and r raised to s ≥
n to the power −1/100](hyp:hp); [Y has at most n to the power 2/3 vertices, every edge
of J crosses Y, J is contained in a source-test edge set, at most n/8 vertices outside Y
have positive degree, and each has degree at most s](hyp:hconfiguration);
[Y has at most n/2 vertices](hyp:hhalf); and [Gstar passes all target tests](hyp:htarget).
Then [Gstar contains a copy of J](goal). -/
lemma transfer_containsCopy {n s : ℕ} {r : ℝ} (hp : TransferParameters n r s)
    (Y : Finset (Fin n)) (J : SimpleGraph (Fin n)) [DecidableRel J.Adj]
    (hconfiguration : TransferConfiguration n s (sourceTestFamily n r s) Y J)
    (hhalf : 2 * Y.card ≤ n) (Gstar : SimpleGraph (Fin n))
    (htarget : TargetTests n r s Gstar) : ContainsCopy J Gstar := by
  classical
  let U := (Finset.univ \ Y).filter (fun w => 0 < J.degree w)
  obtain ⟨f, hf, hsub⟩ := transfer_matching hp Y J hconfiguration hhalf Gstar htarget
  let F : Fin n → Fin n := fun w => if w ∈ Y then w else f w
  have hFinj : Set.InjOn F (↑(Y ∪ U) : Set (Fin n)) := by
    intro v hv w hw heq
    change v ∈ Y ∪ U at hv
    change w ∈ Y ∪ U at hw
    by_cases hvY : v ∈ Y <;> by_cases hwY : w ∈ Y
    · simpa [F, hvY, hwY] using heq
    · have hwU : w ∈ U := (Finset.mem_union.mp hw).resolve_left hwY
      have h := (hsub w hwU).1
      simp only [F, if_pos hvY, if_neg hwY] at heq
      exact False.elim (h (heq ▸ hvY))
    · have hvU : v ∈ U := (Finset.mem_union.mp hv).resolve_left hvY
      have h := (hsub v hvU).1
      simp only [F, if_neg hvY, if_pos hwY] at heq
      exact False.elim (h (heq.symm ▸ hwY))
    · have hvU : v ∈ U := (Finset.mem_union.mp hv).resolve_left hvY
      have hwU : w ∈ U := (Finset.mem_union.mp hw).resolve_left hwY
      apply hf hvU hwU
      simpa [F, hvY, hwY] using heq
  obtain ⟨g, hg⟩ := Finset.exists_equiv_extend_of_card_eq
    (t := (Finset.univ : Finset (Fin n))) (by simp)
    (Finset.subset_univ ((Y ∪ U).image F)) hFinj
  have hfix (w : Fin n) (hw : w ∈ Y) : (g w).val = w := by
    rw [hg w (Finset.mem_union_left _ hw)]
    simp [F, hw]
  have hmove (w : Fin n) (hw : w ∈ U) : (g w).val = f w := by
    rw [hg w (Finset.mem_union_right _ hw)]
    have hout : w ∉ Y := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hw).1).2
    simp [F, hout]
  have hcross := hconfiguration.2.1
  have hedge {w y : Fin n} (hwy : J.Adj w y) (hw : w ∉ Y) (hy : y ∈ Y) :
      Gstar.Adj (g w).val (g y).val := by
    have hwU : w ∈ U := Finset.mem_filter.mpr
      ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hw⟩, hwy.degree_pos_left⟩
    rw [hmove w hwU, hfix y hy]
    have hyJ : (⟨y, hy⟩ : ↥Y) ∈ neighborhoodIn Y J w := by
      exact (transfer_mem_neighborhoodIn Y J w ⟨y, hy⟩).mpr hwy
    exact (transfer_mem_neighborhoodIn Y Gstar (f w) ⟨y, hy⟩).mp ((hsub w hwU).2 hyJ)
  refine ⟨⟨⟨(fun w => (g w).val), ?_⟩, ?_⟩⟩
  · intro v w hvw
    rcases hcross v w hvw with ⟨hv, hw⟩ | ⟨hw, hv⟩
    · exact (hedge hvw.symm hw hv).symm
    · exact hedge hvw hv hw
  · intro v w heq
    exact g.injective (Subtype.ext heq)

end Papers.OaiGraphDecompositionsIntegral

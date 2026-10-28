module
public import Papers.OaiGeometricErdosSimilarity.Helpers.ScaleBounds
public import Papers.OaiGeometricErdosSimilarity.Helpers.ScaleConstancy

/-! # Boundary representatives for scales and the conditional union bound -/

public section

namespace Papers.OaiGeometricErdosSimilarity

open Causalean.Experimentation.DesignBased
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {q p : ℝ} {M d g r0 n0 : ℕ}

-- @node: scaleRepresentatives_spec
/-- Assume [q lies strictly between zero and one](hyp:hq), [M is at least
two](hyp:hM), [the depth is positive](hyp:hd), [the gap is positive](hyp:hg),
[the base length is positive](hyp:hr), [the starting index is at least
one](hyp:hn0), [twice q to that starting index is at most one quarter](hyp:hn0q),
and [x is a stable center](hyp:hx). Then [the representative scales at U all
lie between one and two, their number is bounded by the scale-count bound
for U's local window length, and every scale between one and two has a
representative giving identical local tests for every outcome, nonfinal
child, and index in that child's window](goal). -/
lemma scaleRepresentatives_spec (hq : QDomain q) (hM : BranchingDomain M)
    (hd : DepthDomain d) (hg : GapDomain g) (hr : BaseLengthDomain r0)
    (hn0 : 1 ≤ n0) -- @realizes n_0(positive starting index)
    (hn0q : 2 * q ^ n0 ≤ 1 / 4) -- @realizes n_0(smallness at the supplied index)
    (x : ℝ) (hx : StableCenterCondition q M d g r0 n0 x) (U : InternalVertex M d) :
    (∀ t ∈ scaleRepresentatives (g := g) (r0 := r0) (n0 := n0) hq U x, t ∈ Set.Icc (1 : ℝ) 2) ∧
    ((scaleRepresentatives (g := g) (r0 := r0) (n0 := n0) hq U x).card : ℝ) ≤
      scaleCount M q (localLength M g r0 U) ∧
    ∀ t ∈ Set.Icc (1 : ℝ) 2, ∃ t' ∈ scaleRepresentatives (g := g) (r0 := r0) (n0 := n0) hq U x,
      ∀ ω : Outcome q M d g r0 n0, ∀ (i : Fin M) (hi : i.val + 1 < M),
        ∀ n ∈ windowSet q M d g r0 n0 (localEdge U i),
          localTest hM ω U i hi (localPoint x t q n) =
            localTest hM ω U i hi (localPoint x t' q n) := by
  refine ⟨scaleRepresentatives_mem_Icc hq U x,
    scaleRepresentatives_card_le hq hM hd hg hr U x, ?_⟩
  exact scaleRepresentatives_cover_localTests hq hM U x

-- @node: condPr_le_sum_of_cover
/-- If [every outcome satisfying both B and A belongs to at least one event
in the family F indexed by T](hyp:hcover), then [the probability of A
conditional on B is at most the sum, over T, of the probabilities of those
events conditional on B](goal). -/
lemma condPr_le_sum_of_cover {Ω ι : Type*} [Fintype Ω]
    (D : FiniteDesign Ω) (A B : Ω → Prop) (T : Finset ι) (F : ι → Ω → Prop)
    (hcover : ∀ ω, B ω → A ω → ∃ t ∈ T, F t ω) :
    condPr D A B ≤ ∑ t ∈ T, condPr D (F t) B := by
  classical
  have hind (ω : Ω) : FiniteDesign.ind (fun ω => A ω ∧ B ω) ω ≤
      ∑ t ∈ T, FiniteDesign.ind (fun ω => F t ω ∧ B ω) ω := by
    by_cases h : A ω ∧ B ω
    · obtain ⟨t, ht, hFt⟩ := hcover ω h.2 h.1
      calc
        _ = 1 := by simp [FiniteDesign.ind, h]
        _ = FiniteDesign.ind (fun ω => F t ω ∧ B ω) ω := by
          simp [FiniteDesign.ind, hFt, h.2]
        _ ≤ _ := Finset.single_le_sum
          (fun j _ => FiniteDesign.ind_nonneg (fun ω => F j ω ∧ B ω) ω) ht
    · simp only [FiniteDesign.ind, if_neg h]
      exact Finset.sum_nonneg (fun j _ =>
        FiniteDesign.ind_nonneg (fun ω => F j ω ∧ B ω) ω)
  have hprob : D.Pr (fun ω => A ω ∧ B ω) ≤
      ∑ t ∈ T, D.Pr (fun ω => F t ω ∧ B ω) := by
    calc
      _ ≤ D.E (fun ω => ∑ t ∈ T, FiniteDesign.ind (fun ω => F t ω ∧ B ω) ω) :=
        Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (hind ω) (D.p_nonneg ω))
      _ = _ := D.E_sum T _
  unfold condPr
  rw [← Finset.sum_div]
  exact div_le_div_of_nonneg_right hprob (D.Pr_nonneg B)

-- @node: lem:conditional-scales
/-- Assume [q lies strictly between zero and one](hyp:hq), [M is at least
two](hyp:hM), [the depth is positive](hyp:hd), [the gap is positive](hyp:hg),
[the base length is positive](hyp:hr), [the starting index is at least
one](hyp:hn0), [twice q to that index is at most one quarter](hyp:hn0q),
[p lies strictly between zero and one](hyp:hp), and [jointly, p lies strictly
between zero and one, M is at least two, and d, g, and r0 are positive](hyp:hpar).
If [x is stable](hyp:hx), [the assignment ξ has a first
default vertex](hyp:hξ), and, for [height h](hyp:h), [that vertex is U with
height h](hyp:hUh), then
[conditional on the atom specified by x and ξ, the probability that some
scale between one and two makes every indexed local point miss the random
set is at most the scale-count bound at height h times the exponential of
minus p times (M minus 1) times the window length at height h divided by
two](goal). -/
lemma condPr_exists_scale_miss_le (hq : QDomain q) (hM : BranchingDomain M)
    (hd : DepthDomain d) (hg : GapDomain g) (hr : BaseLengthDomain r0)
    (hn0 : 1 ≤ n0) -- @realizes n_0(positive starting index)
    (hn0q : 2 * q ^ n0 ≤ 1 / 4) -- @realizes n_0(smallness at the supplied index)
    (hp : TerminalProbabilityDomain p) (hpar : ConditionalScalesParameters p M d g r0)
    (x : ℝ) (hx : StableCenterCondition q M d g r0 n0 x)
    (ξ : NondefaultEdge M d → Bool) (hξ : ConditionalScalesDefaultAtom q M d g r0 hM x ξ)
    (U : InternalVertex M d) (h : ℕ) (hUh : ConditionalScalesHeight q M d g r0 hM x ξ U h) :
    condPr (tableLaw q M d g r0 n0 p)
      (fun ω => ∃ t ∈ Set.Icc (1 : ℝ) 2,
        ∀ n ∈ indexSet q M d g r0 n0, localPoint x t q n ∉ randomSet hM ω)
      (atomEvent q M d g r0 n0 x ξ) ≤
        scaleCount M q (windowLength M g r0 h) *
          Real.exp (-(p * ((M : ℝ) - 1) * windowLength M g r0 h / 2)) := by
  classical
  obtain ⟨hT, hcard, hrep⟩ := scaleRepresentatives_spec hq hM hd hg hr hn0 hn0q x hx U
  let T := scaleRepresentatives (g := g) (r0 := r0) (n0 := n0) hq U x
  have hcover (ω : Outcome q M d g r0 n0)
      (hω : atomEvent q M d g r0 n0 x ξ ω)
      (hmiss : ∃ t ∈ Set.Icc (1 : ℝ) 2,
        ∀ n ∈ indexSet q M d g r0 n0, localPoint x t q n ∉ randomSet hM ω) :
      ∃ t' ∈ T, allLocalTestsFail hM U x t' ω := by
    obtain ⟨t, ht, hmiss⟩ := hmiss
    obtain ⟨t', ht', heq⟩ := hrep t ht
    refine ⟨t', ht', ?_⟩
    intro i hi n hn
    rw [← heq ω i hi n hn]
    apply Bool.eq_false_iff.mpr
    intro htest
    have hnN : n ∈ indexSet q M d g r0 n0 :=
      Finset.mem_biUnion.mpr ⟨localEdge U i, Finset.mem_univ _, hn⟩
    exact hmiss n hnN ((localTest_imp_mem_randomSet hq hM hd hg hr hp x hx ξ hξ
      U hUh.1 ω hω i hi n hn t ht).2 htest)
  have hunion := condPr_le_sum_of_cover (tableLaw q M d g r0 n0 p)
    (fun ω => ∃ t ∈ Set.Icc (1 : ℝ) 2,
      ∀ n ∈ indexSet q M d g r0 n0, localPoint x t q n ∉ randomSet hM ω)
    (atomEvent q M d g r0 n0 x ξ) T (allLocalTestsFail hM U x) hcover
  have hsum : (∑ t ∈ T, condPr (tableLaw q M d g r0 n0 p)
      (allLocalTestsFail hM U x t) (atomEvent q M d g r0 n0 x ξ)) =
      (T.card : ℝ) * (1 - p / 2) ^ ((M - 1) * windowLength M g r0 h) := by
    calc
      _ = ∑ _t ∈ T, (1 - p / 2) ^ ((M - 1) * windowLength M g r0 h) := by
        apply Finset.sum_congr rfl
        intro t ht
        exact condPr_forall_localTest_false_eq hq hM hd hg hr hn0 hn0q hp x hx ξ hξ
          U h hUh.1 hUh.2 t (hT t ht)
      _ = _ := by simp
  have hcard' : (T.card : ℝ) ≤ scaleCount M q (windowLength M g r0 h) := by
    simpa only [T, localLength, hUh.2] using hcard
  have hexp : (1 - p / 2) ^ ((M - 1) * windowLength M g r0 h) ≤
      Real.exp (-(p * ((M : ℝ) - 1) * windowLength M g r0 h / 2)) := by
    calc
      _ ≤ (Real.exp (-(p / 2))) ^ ((M - 1) * windowLength M g r0 h) :=
        pow_le_pow_left₀ (by have := hp.2; linarith) (Real.one_sub_le_exp_neg _) _
      _ = _ := by
        rw [← Real.exp_nat_mul]
        congr 1
        rw [Nat.cast_mul, Nat.cast_sub (by have := hM; unfold BranchingDomain at hM; omega),
          Nat.cast_one]
        ring
  rw [hsum] at hunion
  exact hunion.trans ((mul_le_mul_of_nonneg_right hcard' (pow_nonneg
    (by have := hp.2; linarith) _)).trans (mul_le_mul_of_nonneg_left hexp
      ((Nat.cast_nonneg T.card).trans hcard')))

end Papers.OaiGeometricErdosSimilarity

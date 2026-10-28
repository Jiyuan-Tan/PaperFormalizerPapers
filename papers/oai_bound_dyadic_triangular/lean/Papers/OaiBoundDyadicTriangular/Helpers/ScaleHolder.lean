module

public import Papers.OaiBoundDyadicTriangular.Helpers.LocalProduct
public import Papers.OaiBoundDyadicTriangular.Helpers.AtomIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! # Discrete three-factor Hölder and the disjoint edge boxes at one scale -/

public section

open MeasureTheory
open scoped BigOperators

namespace Papers.OaiBoundDyadicTriangular

-- @node: eLpNorm_count_cube
/-- [For a real function on a finite set with counting measure, the cube of its
L³ norm equals the sum of the cubes of its absolute values](goal). -/
lemma eLpNorm_count_cube {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (f : ι → ℝ) :
    (eLpNorm f 3 Measure.count).toReal ^ 3 = ∑ i, |f i| ^ 3 := by
  rw [eLpNorm_toReal_cube, lintegral_count, tsum_fintype,
    ENNReal.toReal_sum (fun i _ => by finiteness)]
  simp only [ENNReal.toReal_pow, toReal_enorm, Real.norm_eq_abs]

-- @node: finite_holder_three
/-- If [f is nonnegative](hyp:hf), [g is nonnegative](hyp:hg), and [h is
nonnegative](hyp:hh) on a finite set, [A is nonnegative](hyp:hA), [B is
nonnegative](hyp:hB), and [C is nonnegative](hyp:hC), and
[the sum of the cubes of f is at most A cubed](hyp:hfA), [the sum of the cubes of
g is at most B cubed](hyp:hgB), and [the sum of the cubes of h is at most C
cubed](hyp:hhC), then [the sum of the pointwise triple products is at most
A times B times C](goal). -/
lemma finite_holder_three {ι : Type*} [Fintype ι]
    (f g h : ι → ℝ) (A B C : ℝ)
    (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i) (hh : ∀ i, 0 ≤ h i)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hfA : ∑ i, f i ^ 3 ≤ A ^ 3) (hgB : ∑ i, g i ^ 3 ≤ B ^ 3)
    (hhC : ∑ i, h i ^ 3 ≤ C ^ 3) :
    ∑ i, f i * g i * h i ≤ A * B * C := by
  let : MeasurableSpace ι := ⊤
  have hn (u : ι → ℝ) (D : ℝ) (hu : ∀ i, 0 ≤ u i) (hD : 0 ≤ D)
      (hb : ∑ i, u i ^ 3 ≤ D ^ 3) : (eLpNorm u 3 Measure.count).toReal ≤ D := by
    apply (pow_le_pow_iff_left₀ ENNReal.toReal_nonneg hD (by decide : 3 ≠ 0)).mp
    simpa only [eLpNorm_count_cube, abs_of_nonneg (hu _)] using hb
  have hbound := abs_integral_mul_three_le
    (MemLp.of_discrete (f := f) (p := 3) (μ := Measure.count))
    (MemLp.of_discrete (f := g) (p := 3) (μ := Measure.count))
    (MemLp.of_discrete (f := h) (p := 3) (μ := Measure.count))
  rw [integral_count, abs_of_nonneg
    (Finset.sum_nonneg (fun i _ => mul_nonneg (mul_nonneg (hf i) (hg i)) (hh i)))] at hbound
  exact hbound.trans (mul_le_mul
    (mul_le_mul (hn f A hf hA hfA) (hn g B hg hB hgB) ENNReal.toReal_nonneg hA)
    (hn h C hh hC hhC) ENNReal.toReal_nonneg (mul_nonneg hA hB))

-- @node: localEdge_cube_sum_le
/-- If [each of the three edge functions belongs to L³ on the nonnegative
quadrant](hyp:hF), then [for any fixed edge and finite collection of admissible
index triples at one scale, the sum of the cubed local edge L³ norms is bounded
by that edge function's cubed L³ norm on the whole quadrant](goal). -/
lemma localEdge_cube_sum_le (k : ℤ) (F : Fin 3 → ℝ × ℝ → ℝ)
    (hF : ContinuityInputs F) (v : Fin 3) (T : Finset admissibleSet) :
    (∑ n ∈ T, (eLpNorm (F v) 3 (localEdgeMeasure k n.val v)).toReal ^ 3) ≤
      (eLpNorm (F v) 3 quadrantMeasure).toReal ^ 3 := by
  classical
  have hd : Set.PairwiseDisjoint (↑T : Set admissibleSet)
      (fun n => dyadicInterval k (n.val v) ×ˢ dyadicInterval k (n.val (v + 1))) := by
    intro a _ b _ hab
    exact dyadicRect_pairwiseDisjoint k
      (show (a.val v, a.val (v + 1)) ≠ (b.val v, b.val (v + 1)) from
        fun he => hab (admissible_edge_pair_injective v he))
  have hm (n : admissibleSet) :
      MeasurableSet (dyadicInterval k (n.val v) ×ˢ dyadicInterval k (n.val (v + 1))) :=
    measurableSet_Ico.prod measurableSet_Ico
  have hs : (⋃ n ∈ T, dyadicInterval k (n.val v) ×ˢ
      dyadicInterval k (n.val (v + 1))) ⊆ Rplus ×ˢ Rplus := by
    intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨n, hx⟩
    rcases Set.mem_iUnion.mp hx with ⟨_, hx⟩
    exact ⟨dyadicInterval_subset_Rplus k _ hx.1, dyadicInterval_subset_Rplus k _ hx.2⟩
  have hb := lintegral_mono_set (μ := volume) (f := fun x => ‖F v x‖ₑ ^ (3 : ℕ)) hs
  rw [lintegral_biUnion_finset hd (fun n _ => hm n)] at hb
  have ht : (∫⁻ x, ‖F v x‖ₑ ^ (3 : ℕ) ∂quadrantMeasure) ≠ ⊤ := by
    have he := eLpNorm_nnreal_pow_eq_lintegral
      (f := F v) (μ := quadrantMeasure) (p := (3 : NNReal)) (by norm_num)
    norm_num only [NNReal.coe_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_ofNat] at he
    rw [← he]
    exact ENNReal.pow_ne_top (hF v).eLpNorm_ne_top
  have hr := ENNReal.toReal_mono ht hb
  rw [ENNReal.toReal_sum (fun n _ => ne_top_of_le_ne_top ht
    ((Finset.single_le_sum (fun _ _ => zero_le) (by assumption)).trans hb))] at hr
  simpa only [eLpNorm_toReal_cube, localEdgeMeasure, quadrantMeasure] using hr

-- @node: localForm_one_scale_sum_bound
/-- If [the three edge functions belong to L³ on the nonnegative quadrant](hyp:hF),
then [the sum of the absolute local triangular forms over any finite collection
of admissible index triples at one scale is at most the product of the three
global quadrant L³ norms](goal). -/
lemma localForm_one_scale_sum_bound (k : ℤ) (F : Fin 3 → ℝ × ℝ → ℝ)
    (hF : ContinuityInputs F) (T : Finset admissibleSet) :
    ∑ n ∈ T, |localForm k n.val F| ≤
      ∏ v : Fin 3, (eLpNorm (F v) 3 quadrantMeasure).toReal := by
  classical
  apply (Finset.sum_le_sum (fun n _ => localForm_le_edge_L3 k n.val F hF)).trans
  simp only [Fin.prod_univ_three]
  rw [← Finset.sum_coe_sort T]
  apply finite_holder_three
  · intro n; exact ENNReal.toReal_nonneg
  · intro n; exact ENNReal.toReal_nonneg
  · intro n; exact ENNReal.toReal_nonneg
  · exact ENNReal.toReal_nonneg
  · exact ENNReal.toReal_nonneg
  · exact ENNReal.toReal_nonneg
  · rw [Finset.sum_coe_sort T (fun n : admissibleSet =>
      (eLpNorm (F 0) 3 (localEdgeMeasure k n.val 0)).toReal ^ 3)]
    exact localEdge_cube_sum_le k F hF 0 T
  · rw [Finset.sum_coe_sort T (fun n : admissibleSet =>
      (eLpNorm (F 1) 3 (localEdgeMeasure k n.val 1)).toReal ^ 3)]
    exact localEdge_cube_sum_le k F hF 1 T
  · rw [Finset.sum_coe_sort T (fun n : admissibleSet =>
      (eLpNorm (F 2) 3 (localEdgeMeasure k n.val 2)).toReal ^ 3)]
    exact localEdge_cube_sum_le k F hF 2 T

end Papers.OaiBoundDyadicTriangular

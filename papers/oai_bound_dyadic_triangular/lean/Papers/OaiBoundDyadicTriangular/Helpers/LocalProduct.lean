module

public import Papers.OaiBoundDyadicTriangular.Helpers.LocalHolder
public import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

/-! # Lifting edge functions to the local product box -/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace Papers.OaiBoundDyadicTriangular

-- @node: memLp_pair_first
/-- If [a function of the first two coordinates belongs to L³ for their product
measure](hyp:hf), then [its extension to three coordinates, independent of the
third coordinate, belongs to L³ when the third measure is finite](goal). -/
lemma memLp_pair_first {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {μ : Measure α} {ν : Measure β} {ξ : Measure γ}
    [SFinite ν] [IsFiniteMeasure ξ] {f : α × β → ℝ}
    (hf : MemLp f 3 (μ.prod ν)) :
    MemLp (fun x : α × (β × γ) => f (x.1, x.2.1)) 3 (μ.prod (ν.prod ξ)) := by
  exact
    (hf.comp_fst ξ).comp_measurePreserving
      ((measurePreserving_prodAssoc μ ν ξ).symm MeasurableEquiv.prodAssoc)

-- @node: memLp_pair_last
/-- If [a function of the last two coordinates belongs to L³ for their product
measure](hyp:hf), then [its extension to three coordinates, independent of the
first coordinate, belongs to L³ when the first measure is finite](goal). -/
lemma memLp_pair_last {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {μ : Measure α} {ν : Measure β} {ξ : Measure γ}
    [IsFiniteMeasure μ] [SFinite ν] [SFinite ξ] {f : β × γ → ℝ}
    (hf : MemLp f 3 (ν.prod ξ)) :
    MemLp (fun x : α × (β × γ) => f (x.2.1, x.2.2)) 3 (μ.prod (ν.prod ξ)) := by
  exact hf.comp_snd μ

-- @node: memLp_pair_cyclic
/-- If [a function of the third and first coordinates, in that order, belongs to
L³ for their product measure](hyp:hf), then [its extension to three coordinates
belongs to L³ when the unused second measure is finite](goal). -/
lemma memLp_pair_cyclic {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {μ : Measure α} {ν : Measure β} {ξ : Measure γ}
    [SFinite μ] [IsFiniteMeasure ν] [SFinite ξ] {f : γ × α → ℝ}
    (hf : MemLp f 3 (ξ.prod μ)) :
    MemLp (fun x : α × (β × γ) => f (x.2.2, x.1)) 3 (μ.prod (ν.prod ξ)) := by
  exact
    (hf.comp_snd ν).comp_measurePreserving
      ((measurePreserving_prodAssoc ν ξ μ).comp (Measure.measurePreserving_swap))

-- @node: lintegral_cube_pair_first
/-- If [a function of the first two coordinates belongs to L³](hyp:hf), then
[the integral of its absolute value cubed over the three-coordinate product
equals its two-coordinate integral times the total mass of the third measure](goal). -/
lemma lintegral_cube_pair_first {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {μ : Measure α} {ν : Measure β} {ξ : Measure γ}
    [SFinite ν] [IsFiniteMeasure ξ] {f : α × β → ℝ}
    (hf : MemLp f 3 (μ.prod ν)) :
    (∫⁻ x : α × (β × γ), ‖f (x.1, x.2.1)‖ₑ ^ (3 : ℕ) ∂μ.prod (ν.prod ξ)) =
      (∫⁻ x, ‖f x‖ₑ ^ (3 : ℕ) ∂μ.prod ν) * ξ Set.univ := by
  have he := ((measurePreserving_prodAssoc μ ν ξ).symm MeasurableEquiv.prodAssoc).lintegral_comp_emb
    MeasurableEquiv.prodAssoc.symm.measurableEmbedding
      (fun x : (α × β) × γ => ‖f x.1‖ₑ ^ (3 : ℕ))
  change (∫⁻ x, ‖f (x.1, x.2.1)‖ₑ ^ (3 : ℕ) ∂μ.prod (ν.prod ξ)) =
    (∫⁻ x : (α × β) × γ, ‖f x.1‖ₑ ^ (3 : ℕ) ∂(μ.prod ν).prod ξ) at he
  rw [he, lintegral_prod _ ((hf.comp_fst ξ).1.enorm.pow_const 3)]
  simp only [lintegral_const, ← lintegral_mul_const'' _ (hf.1.enorm.pow_const 3)]

-- @node: lintegral_cube_pair_last
/-- If [a function of the last two coordinates belongs to L³](hyp:hf), then
[the integral of its absolute value cubed over the three-coordinate product
equals its two-coordinate integral times the total mass of the first measure](goal). -/
lemma lintegral_cube_pair_last {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {μ : Measure α} {ν : Measure β} {ξ : Measure γ}
    [IsFiniteMeasure μ] [SFinite ν] [SFinite ξ] {f : β × γ → ℝ}
    (hf : MemLp f 3 (ν.prod ξ)) :
    (∫⁻ x : α × (β × γ), ‖f (x.2.1, x.2.2)‖ₑ ^ (3 : ℕ) ∂μ.prod (ν.prod ξ)) =
      (∫⁻ x, ‖f x‖ₑ ^ (3 : ℕ) ∂ν.prod ξ) * μ Set.univ := by
  rw [lintegral_prod _ ((hf.comp_snd μ).1.enorm.pow_const 3)]
  simp only [lintegral_const]

-- @node: lintegral_cube_pair_cyclic
/-- If [a function of the third and first coordinates, in that order, belongs to
L³](hyp:hf), then [the integral of its absolute value cubed over the three-coordinate
product equals its two-coordinate integral times the total mass of the second
measure](goal). -/
lemma lintegral_cube_pair_cyclic {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {μ : Measure α} {ν : Measure β} {ξ : Measure γ}
    [SFinite μ] [IsFiniteMeasure ν] [SFinite ξ] {f : γ × α → ℝ}
    (hf : MemLp f 3 (ξ.prod μ)) :
    (∫⁻ x : α × (β × γ), ‖f (x.2.2, x.1)‖ₑ ^ (3 : ℕ) ∂μ.prod (ν.prod ξ)) =
      (∫⁻ x, ‖f x‖ₑ ^ (3 : ℕ) ∂ξ.prod μ) * ν Set.univ := by
  have he := (Measure.measurePreserving_swap (μ := μ) (ν := ν.prod ξ)).lintegral_comp_emb
    MeasurableEquiv.prodComm.measurableEmbedding
      (fun x : (β × γ) × α => ‖f (x.1.2, x.2)‖ₑ ^ (3 : ℕ))
  change (∫⁻ x, ‖f (x.2.2, x.1)‖ₑ ^ (3 : ℕ) ∂μ.prod (ν.prod ξ)) =
    (∫⁻ x : (β × γ) × α, ‖f (x.1.2, x.2)‖ₑ ^ (3 : ℕ) ∂(ν.prod ξ).prod μ) at he
  rw [he]
  have ha := (measurePreserving_prodAssoc ν ξ μ).lintegral_comp_emb
    MeasurableEquiv.prodAssoc.measurableEmbedding
      (fun x : β × (γ × α) => ‖f x.2‖ₑ ^ (3 : ℕ))
  change (∫⁻ x : (β × γ) × α, ‖f (x.1.2, x.2)‖ₑ ^ (3 : ℕ) ∂(ν.prod ξ).prod μ) =
    (∫⁻ x : β × (γ × α), ‖f x.2‖ₑ ^ (3 : ℕ) ∂ν.prod (ξ.prod μ)) at ha
  rw [ha]
  exact lintegral_cube_pair_last hf

-- @node: localCubeMeasure
/-- For [an integer scale](hyp:k) and [three nonnegative integer interval
indices](hyp:n), [the local cube measure is Lebesgue measure restricted to the
product of the three indexed dyadic intervals at that scale](goal). -/
noncomputable def localCubeMeasure (k : ℤ) (n : Fin 3 → ℕ) : Measure (ℝ × (ℝ × ℝ)) :=
  volume.restrict (dyadicInterval k (n 0) ×ˢ
    (dyadicInterval k (n 1) ×ˢ dyadicInterval k (n 2)))

-- @node: localEdgeMeasure
/-- For [an integer scale](hyp:k), [three nonnegative integer interval
indices](hyp:n), and [a cyclic edge index](hyp:v), [the local edge measure is
Lebesgue measure restricted to the rectangle formed by that edge's interval and
the next interval in cyclic order](goal). -/
noncomputable def localEdgeMeasure (k : ℤ) (n : Fin 3 → ℕ) (v : Fin 3) :
    Measure (ℝ × ℝ) :=
  volume.restrict (dyadicInterval k (n v) ×ˢ dyadicInterval k (n (v + 1)))

-- @node: cubeEdgeMap
/-- For [a cyclic edge index](hyp:v) and [a point with three real coordinates](hyp:x),
[the edge projection returns the coordinate at that index followed by the next
coordinate in cyclic order](goal). -/
def cubeEdgeMap (v : Fin 3) (x : ℝ × (ℝ × ℝ)) : ℝ × ℝ :=
  (![x.1, x.2.1, x.2.2] v, ![x.1, x.2.1, x.2.2] (v + 1))

-- @node: localCubeMeasure_eq_prod
/-- [Lebesgue measure restricted to a local dyadic cube equals the product of
Lebesgue measures restricted to its three coordinate intervals](goal). -/
lemma localCubeMeasure_eq_prod (k : ℤ) (n : Fin 3 → ℕ) :
    localCubeMeasure k n = (volume.restrict (dyadicInterval k (n 0))).prod
      ((volume.restrict (dyadicInterval k (n 1))).prod
        (volume.restrict (dyadicInterval k (n 2)))) := by
  simp only [localCubeMeasure, Measure.prod_restrict, ← Measure.volume_eq_prod]

-- @node: localEdgeMeasure_eq_prod
/-- [Lebesgue measure restricted to a local dyadic edge rectangle equals the
product of Lebesgue measures restricted to its two coordinate intervals](goal). -/
lemma localEdgeMeasure_eq_prod (k : ℤ) (n : Fin 3 → ℕ) (v : Fin 3) :
    localEdgeMeasure k n v = (volume.restrict (dyadicInterval k (n v))).prod
      (volume.restrict (dyadicInterval k (n (v + 1)))) := by
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  rfl

-- @node: dyadicInterval_subset_Rplus
/-- [Every dyadic interval with a nonnegative integer index lies in the
nonnegative real half-line](goal). -/
lemma dyadicInterval_subset_Rplus (k : ℤ) (a : ℕ) : dyadicInterval k a ⊆ Rplus := by
  intro x hx
  exact (by positivity : 0 ≤ (2 : ℝ) ^ k * a).trans hx.1

-- @node: memLp_localEdge
/-- If [a function belongs to L³ on the nonnegative quadrant](hyp:hf), then
[it belongs to L³ on every local dyadic edge rectangle](goal). -/
lemma memLp_localEdge (k : ℤ) (n : Fin 3 → ℕ) (v : Fin 3) {f : ℝ × ℝ → ℝ}
    (hf : MemLp f 3 quadrantMeasure) : MemLp f 3 (localEdgeMeasure k n v) := by
  apply hf.mono_measure
  exact Measure.restrict_mono
    (Set.prod_mono (dyadicInterval_subset_Rplus k _) (dyadicInterval_subset_Rplus k _))
    le_rfl

-- @node: memLp_localCube_edges
/-- If [each of three edge functions belongs to L³ on the nonnegative
quadrant](hyp:hF), then [any one of them, evaluated on its cyclic pair of cube
coordinates, belongs to L³ on the local dyadic cube](goal). -/
lemma memLp_localCube_edges (k : ℤ) (n : Fin 3 → ℕ)
    (F : Fin 3 → ℝ × ℝ → ℝ) (hF : ContinuityInputs F) (v : Fin 3) :
    MemLp (fun x => F v (cubeEdgeMap v x)) 3 (localCubeMeasure k n) := by
  have hf := memLp_localEdge k n v (hF v)
  rw [localEdgeMeasure_eq_prod] at hf
  rw [localCubeMeasure_eq_prod]
  unfold dyadicInterval at hf ⊢
  fin_cases v
  · exact memLp_pair_first hf
  · exact memLp_pair_last hf
  · exact memLp_pair_cyclic hf

-- @node: volume_dyadicInterval
/-- [The Lebesgue measure of any indexed dyadic interval at integer scale k
is two raised to k](goal). -/
lemma volume_dyadicInterval (k : ℤ) (a : ℕ) :
    volume (dyadicInterval k a) = ENNReal.ofReal ((2 : ℝ) ^ k) := by
  rw [dyadicInterval, Real.volume_Ico]
  congr 1
  ring

-- @node: lintegral_cube_localCube_edge
/-- If [the three edge functions belong to L³ on the nonnegative quadrant](hyp:hF),
then [the integral of the absolute cube of an edge function lifted to the local
cube equals its integral on the local edge rectangle times the dyadic side
length, two raised to the scale](goal). -/
lemma lintegral_cube_localCube_edge (k : ℤ) (n : Fin 3 → ℕ)
    (F : Fin 3 → ℝ × ℝ → ℝ) (hF : ContinuityInputs F) (v : Fin 3) :
    (∫⁻ x, ‖F v (cubeEdgeMap v x)‖ₑ ^ (3 : ℕ) ∂localCubeMeasure k n) =
      (∫⁻ x, ‖F v x‖ₑ ^ (3 : ℕ) ∂localEdgeMeasure k n v) *
        ENNReal.ofReal ((2 : ℝ) ^ k) := by
  have hf := memLp_localEdge k n v (hF v)
  rw [localEdgeMeasure_eq_prod] at hf
  rw [localCubeMeasure_eq_prod, localEdgeMeasure_eq_prod]
  have hm (a : ℕ) : (volume.restrict (dyadicInterval k a)) Set.univ =
      ENNReal.ofReal ((2 : ℝ) ^ k) := by
    rw [Measure.restrict_apply_univ, volume_dyadicInterval]
  unfold dyadicInterval at hf ⊢
  fin_cases v
  · exact (lintegral_cube_pair_first hf).trans (congrArg _ (hm (n 2)))
  · exact (lintegral_cube_pair_last hf).trans (congrArg _ (hm (n 0)))
  · exact (lintegral_cube_pair_cyclic hf).trans (congrArg _ (hm (n 1)))

-- @node: eLpNorm_toReal_cube
/-- [The cube of the real-valued L³ seminorm of a real function equals the real
value of the integral of its absolute value cubed](goal).

The conversion from extended nonnegative reals to reals sends infinity to zero. -/
lemma eLpNorm_toReal_cube {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) :
    (eLpNorm f 3 μ).toReal ^ 3 = (∫⁻ x, ‖f x‖ₑ ^ (3 : ℕ) ∂μ).toReal := by
  have h := eLpNorm_nnreal_pow_eq_lintegral
    (f := f) (μ := μ) (p := (3 : NNReal)) (by norm_num)
  norm_num only [NNReal.coe_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_ofNat] at h
  simpa only [ENNReal.toReal_pow] using congrArg ENNReal.toReal h

-- @node: localCube_edge_norm_cube
/-- If [the three edge functions belong to L³ on the nonnegative quadrant](hyp:hF),
then [the cubed L³ norm of an edge function lifted to the local cube equals its
cubed local edge L³ norm times the dyadic side length](goal). -/
lemma localCube_edge_norm_cube (k : ℤ) (n : Fin 3 → ℕ)
    (F : Fin 3 → ℝ × ℝ → ℝ) (hF : ContinuityInputs F) (v : Fin 3) :
    (eLpNorm (fun x => F v (cubeEdgeMap v x)) 3 (localCubeMeasure k n)).toReal ^ 3 =
      (eLpNorm (F v) 3 (localEdgeMeasure k n v)).toReal ^ 3 * (2 : ℝ) ^ k := by
  rw [eLpNorm_toReal_cube, lintegral_cube_localCube_edge k n F hF v,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), eLpNorm_toReal_cube]

-- @node: localForm_le_edge_L3
/-- If [the three edge functions belong to L³ on the nonnegative quadrant](hyp:hF),
then [the absolute local triangular form is bounded by the product of their
L³ norms on the corresponding local edge rectangles](goal). -/
lemma localForm_le_edge_L3 (k : ℤ) (n : Fin 3 → ℕ)
    (F : Fin 3 → ℝ × ℝ → ℝ) (hF : ContinuityInputs F) :
    |localForm k n F| ≤ ∏ v : Fin 3, (eLpNorm (F v) 3 (localEdgeMeasure k n v)).toReal := by
  have h₀ := memLp_localCube_edges k n F hF 0
  have h₁ := memLp_localCube_edges k n F hF 1
  have h₂ := memLp_localCube_edges k n F hF 2
  have h := localForm_le_local_L3 k n F h₀ h₁ h₂
  have hc : ((2 : ℝ) ^ (-k) *
      ((eLpNorm (fun x => F 0 (cubeEdgeMap 0 x)) 3 (localCubeMeasure k n)).toReal *
        (eLpNorm (fun x => F 1 (cubeEdgeMap 1 x)) 3 (localCubeMeasure k n)).toReal *
        (eLpNorm (fun x => F 2 (cubeEdgeMap 2 x)) 3 (localCubeMeasure k n)).toReal)) ^ 3 =
      (∏ v : Fin 3, (eLpNorm (F v) 3 (localEdgeMeasure k n v)).toReal) ^ 3 := by
    rw [mul_pow, mul_pow, mul_pow,
      localCube_edge_norm_cube k n F hF 0, localCube_edge_norm_cube k n F hF 1,
      localCube_edge_norm_cube k n F hF 2, Fin.prod_univ_three, mul_pow, mul_pow,
      zpow_neg]
    have hp : (2 : ℝ) ^ k ≠ 0 := by positivity
    field_simp
  apply (pow_le_pow_iff_left₀ (abs_nonneg _) (by positivity) (by decide : 3 ≠ 0)).mp
  rw [← hc]
  exact pow_le_pow_left₀ (abs_nonneg _) h 3

-- @node: localForm_sub_expansion
/-- If [each function in the first triple belongs to L³ on the nonnegative
quadrant](hyp:hF) and [the same holds for the second triple](hyp:hG), then
[the difference of their local triangular forms is the sum of three local forms,
replacing the first, second, and third inputs successively by their differences,
with earlier inputs from the second triple and later inputs from the first](goal). -/
lemma localForm_sub_expansion (k : ℤ) (n : Fin 3 → ℕ)
    (F G : Fin 3 → ℝ × ℝ → ℝ) (hF : ContinuityInputs F) (hG : ContinuityInputs G) :
    localForm k n F - localForm k n G =
      localForm k n ![fun x => F 0 x - G 0 x, F 1, F 2] +
        localForm k n ![G 0, fun x => F 1 x - G 1 x, F 2] +
        localForm k n ![G 0, G 1, fun x => F 2 x - G 2 x] := by
  have hw : AEStronglyMeasurable (fun x : ℝ × (ℝ × ℝ) =>
      haarSign k (n 0) x.1 * haarSign k (n 1) x.2.1 * haarSign k (n 2) x.2.2)
      (localCubeMeasure k n) := by
    fun_prop
  have hb : ∀ᵐ x ∂localCubeMeasure k n,
      ‖haarSign k (n 0) x.1 * haarSign k (n 1) x.2.1 *
        haarSign k (n 2) x.2.2‖ ≤ 1 :=
    Filter.Eventually.of_forall (fun x => by
      simpa only [Real.norm_eq_abs] using abs_haarSign_product_le_one k n x)
  have hi := integral_mul_three_weight_sub
    (memLp_localCube_edges k n F hF 0) (memLp_localCube_edges k n F hF 1)
    (memLp_localCube_edges k n F hF 2) (memLp_localCube_edges k n G hG 0)
    (memLp_localCube_edges k n G hG 1) (memLp_localCube_edges k n G hG 2) hw hb
  simpa [localForm, cubeEdgeMap, localCubeMeasure, mul_assoc, mul_add, mul_sub] using
    congrArg (fun r : ℝ => (2 : ℝ) ^ (-k) * r) hi

end Papers.OaiBoundDyadicTriangular

module

public import Papers.OaiBoundDyadicTriangular.Basic

/-! # Hölder estimates for the signed local trilinear integrals -/

public section

open MeasureTheory
open scoped BigOperators

namespace Papers.OaiBoundDyadicTriangular

-- @node: measurable_haarSign
/-- [The Haar sign function at any integer scale k and location n is
measurable](goal). -/
@[fun_prop] lemma measurable_haarSign (k : ℤ) (n : ℕ) : Measurable (haarSign k n) := by
  unfold haarSign dyadicInterval
  exact (measurable_const.indicator measurableSet_Ico).sub
    (measurable_const.indicator measurableSet_Ico)

-- @node: abs_haarSign_le_one
/-- [The absolute value of the Haar sign function at any scale, location, and
real argument is at most one](goal). -/
lemma abs_haarSign_le_one (k : ℤ) (n : ℕ) (x : ℝ) : |haarSign k n x| ≤ 1 := by
  unfold haarSign
  by_cases h₀ : x ∈ dyadicInterval (k - 1) (2 * n) <;>
    by_cases h₁ : x ∈ dyadicInterval (k - 1) (2 * n + 1) <;>
      simp [h₀, h₁]

-- @node: memLp_mul_three
/-- If [f, g, and h each have finite L³ norm and are almost everywhere strongly
measurable under μ](hyp:hf,hg,hh), then [their pointwise
product belongs to L¹ under μ](goal). -/
lemma memLp_mul_three {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g h : α → ℝ} (hf : MemLp f 3 μ) (hg : MemLp g 3 μ)
    (hh : MemLp h 3 μ) : MemLp (fun x => f x * g x * h x) 1 μ := by
  have : ENNReal.HolderTriple 3 3 (3 / 2) := ⟨by
    apply (ENNReal.toReal_eq_toReal_iff'
      (by norm_num [ENNReal.add_ne_top, ENNReal.inv_ne_top, ENNReal.div_eq_zero_iff])
      (by norm_num [ENNReal.add_ne_top, ENNReal.inv_ne_top, ENNReal.div_eq_zero_iff])).mp
    norm_num [ENNReal.toReal_add, ENNReal.toReal_inv, ENNReal.toReal_div]⟩
  have : ENNReal.HolderTriple (3 / 2) 3 1 := ⟨by
    apply (ENNReal.toReal_eq_toReal_iff'
      (by norm_num [ENNReal.add_ne_top, ENNReal.inv_ne_top, ENNReal.div_eq_zero_iff])
      (by norm_num [ENNReal.add_ne_top, ENNReal.inv_ne_top, ENNReal.div_eq_zero_iff])).mp
    norm_num [ENNReal.toReal_add, ENNReal.toReal_inv, ENNReal.toReal_div]⟩
  exact hh.mul' (hg.mul' hf : MemLp (fun x => f x * g x) (3 / 2) μ)

-- @node: eLpNorm_mul_three_le
/-- If [f, g, and h are each almost everywhere strongly measurable under
μ](hyp:hf,hg,hh), then [the extended L¹ norm of their pointwise
product is at most the product of their extended L³ norms](goal). -/
lemma eLpNorm_mul_three_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g h : α → ℝ} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (hh : AEStronglyMeasurable h μ) :
    eLpNorm (fun x => f x * g x * h x) 1 μ ≤
      eLpNorm f 3 μ * eLpNorm g 3 μ * eLpNorm h 3 μ := by
  have : ENNReal.HolderTriple 3 3 (3 / 2) := ⟨by
    apply (ENNReal.toReal_eq_toReal_iff'
      (by norm_num [ENNReal.add_ne_top, ENNReal.inv_ne_top, ENNReal.div_eq_zero_iff])
      (by norm_num [ENNReal.add_ne_top, ENNReal.inv_ne_top, ENNReal.div_eq_zero_iff])).mp
    norm_num [ENNReal.toReal_add, ENNReal.toReal_inv, ENNReal.toReal_div]⟩
  have : ENNReal.HolderTriple (3 / 2) 3 1 := ⟨by
    apply (ENNReal.toReal_eq_toReal_iff'
      (by norm_num [ENNReal.add_ne_top, ENNReal.inv_ne_top, ENNReal.div_eq_zero_iff])
      (by norm_num [ENNReal.add_ne_top, ENNReal.inv_ne_top, ENNReal.div_eq_zero_iff])).mp
    norm_num [ENNReal.toReal_add, ENNReal.toReal_inv, ENNReal.toReal_div]⟩
  have hfg : eLpNorm (fun x => f x * g x) (3 / 2) μ ≤
      eLpNorm f 3 μ * eLpNorm g 3 μ := by
    simpa only [ENNReal.coe_one, one_mul, Pi.mul_apply, Pi.mul_def] using
      (eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm (p := 3) (q := 3) (r := 3 / 2)
        hf hg (fun a b : ℝ => a * b) 1
        (Filter.Eventually.of_forall (fun x => by simp [norm_mul])))
  have hAll : eLpNorm (fun x => f x * g x * h x) 1 μ ≤
      eLpNorm (fun x => f x * g x) (3 / 2) μ * eLpNorm h 3 μ := by
    simpa only [ENNReal.coe_one, one_mul, Pi.mul_apply, Pi.mul_def] using
      (eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm (p := 3 / 2) (q := 3) (r := 1)
        (hf.mul hg) hh (fun a b : ℝ => a * b) 1
        (Filter.Eventually.of_forall (fun x => by simp [norm_mul])))
  exact hAll.trans (mul_le_mul' hfg le_rfl)

-- @node: abs_integral_mul_three_le
/-- If [f, g, and h each belong to L³ under μ](hyp:hf,hg,hh),
then [the absolute integral of their pointwise product is at most the product
of their L³ norms](goal). -/
lemma abs_integral_mul_three_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g h : α → ℝ} (hf : MemLp f 3 μ) (hg : MemLp g 3 μ)
    (hh : MemLp h 3 μ) :
    |∫ x, f x * g x * h x ∂μ| ≤
      (eLpNorm f 3 μ).toReal * (eLpNorm g 3 μ).toReal * (eLpNorm h 3 μ).toReal := by
  have hi := (memLp_mul_three hf hg hh).eLpNorm_ne_top
  have he := enorm_integral_le_lintegral_enorm (μ := μ) (fun x => f x * g x * h x)
  rw [← eLpNorm_one_eq_lintegral_enorm] at he
  have hbound := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top hf.eLpNorm_ne_top hg.eLpNorm_ne_top)
      hh.eLpNorm_ne_top) (eLpNorm_mul_three_le hf.1 hg.1 hh.1)
  have hIntegral := ENNReal.toReal_mono hi he
  simpa only [ENNReal.toReal_mul, toReal_enorm, Real.norm_eq_abs] using
    hIntegral.trans hbound

-- @node: memLp_mul_bounded_weight
/-- If [f belongs to Lᵖ under μ](hyp:hf), [w is almost everywhere strongly
measurable under μ](hyp:hw), and [|w| ≤ 1 almost everywhere](hyp:hwBound), then
[the pointwise product fw also belongs to Lᵖ under μ](goal). -/
lemma memLp_mul_bounded_weight {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f w : α → ℝ} {p : ENNReal} (hf : MemLp f p μ)
    (hw : AEStronglyMeasurable w μ) (hwBound : ∀ᵐ x ∂μ, ‖w x‖ ≤ 1) :
    MemLp (fun x => f x * w x) p μ := by
  apply hf.of_le (hf.1.mul hw)
  filter_upwards [hwBound] with x hx
  simpa only [Pi.mul_apply, norm_mul, mul_one] using
    mul_le_mul_of_nonneg_left hx (norm_nonneg (f x))

-- @node: abs_integral_mul_three_weight_le
/-- If [f, g, and h each belong to L³ under μ](hyp:hf,hg,hh),
[w is almost everywhere strongly measurable](hyp:hw), and [|w| ≤ 1 almost
everywhere](hyp:hwBound), then [the absolute integral of fghw is at most the
product of the L³ norms of f, g, and h](goal). -/
lemma abs_integral_mul_three_weight_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g h w : α → ℝ} (hf : MemLp f 3 μ) (hg : MemLp g 3 μ)
    (hh : MemLp h 3 μ) (hw : AEStronglyMeasurable w μ)
    (hwBound : ∀ᵐ x ∂μ, ‖w x‖ ≤ 1) :
    |∫ x, f x * g x * h x * w x ∂μ| ≤
      (eLpNorm f 3 μ).toReal * (eLpNorm g 3 μ).toReal * (eLpNorm h 3 μ).toReal := by
  have hfw := memLp_mul_bounded_weight hf hw hwBound
  have hnorm : eLpNorm (fun x => f x * w x) 3 μ ≤ eLpNorm f 3 μ := by
    apply eLpNorm_mono_ae
    filter_upwards [hwBound] with x hx
    simpa only [Pi.mul_apply, norm_mul, mul_one] using
      mul_le_mul_of_nonneg_left hx (norm_nonneg (f x))
  calc
    _ = |∫ x, (f x * w x) * g x * h x ∂μ| := by
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by ring)
    _ ≤ (eLpNorm (fun x => f x * w x) 3 μ).toReal *
        (eLpNorm g 3 μ).toReal * (eLpNorm h 3 μ).toReal :=
      abs_integral_mul_three_le hfw hg hh
    _ ≤ _ := by
      gcongr
      exact hf.eLpNorm_ne_top

-- @node: integrable_mul_three_weight
/-- If [f, g, and h each belong to L³ under μ](hyp:hf,hg,hh),
[w is almost everywhere strongly measurable](hyp:hw), and [|w| ≤ 1 almost
everywhere](hyp:hwBound), then [fghw is integrable under μ](goal). -/
lemma integrable_mul_three_weight {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g h w : α → ℝ} (hf : MemLp f 3 μ) (hg : MemLp g 3 μ)
    (hh : MemLp h 3 μ) (hw : AEStronglyMeasurable w μ)
    (hwBound : ∀ᵐ x ∂μ, ‖w x‖ ≤ 1) :
    Integrable (fun x => f x * g x * h x * w x) μ := by
  exact memLp_one_iff_integrable.mp
    (memLp_mul_bounded_weight (memLp_mul_three hf hg hh) hw hwBound)

-- @node: integral_mul_three_weight_sub
/-- Suppose [f₀, f₁, f₂, g₀, g₁, and g₂ each belong to L³ under
μ](hyp:hf₀,hf₁,hf₂,hg₀,hg₁,hg₂), [w is almost
everywhere strongly measurable](hyp:hw), and [|w| ≤ 1 almost
everywhere](hyp:hwBound). Then [the integral of f₀f₁f₂w minus the integral of
g₀g₁g₂w equals the sum of the integrals of (f₀ − g₀)f₁f₂w,
g₀(f₁ − g₁)f₂w, and g₀g₁(f₂ − g₂)w](goal). -/
lemma integral_mul_three_weight_sub {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f₀ f₁ f₂ g₀ g₁ g₂ w : α → ℝ}
    (hf₀ : MemLp f₀ 3 μ) (hf₁ : MemLp f₁ 3 μ) (hf₂ : MemLp f₂ 3 μ)
    (hg₀ : MemLp g₀ 3 μ) (hg₁ : MemLp g₁ 3 μ) (hg₂ : MemLp g₂ 3 μ)
    (hw : AEStronglyMeasurable w μ) (hwBound : ∀ᵐ x ∂μ, ‖w x‖ ≤ 1) :
    (∫ x, f₀ x * f₁ x * f₂ x * w x ∂μ) -
        (∫ x, g₀ x * g₁ x * g₂ x * w x ∂μ) =
      (∫ x, (f₀ x - g₀ x) * f₁ x * f₂ x * w x ∂μ) +
        (∫ x, g₀ x * (f₁ x - g₁ x) * f₂ x * w x ∂μ) +
        (∫ x, g₀ x * g₁ x * (f₂ x - g₂ x) * w x ∂μ) := by
  have hF := integrable_mul_three_weight hf₀ hf₁ hf₂ hw hwBound
  have hG := integrable_mul_three_weight hg₀ hg₁ hg₂ hw hwBound
  have h₀ := integrable_mul_three_weight (hf₀.sub hg₀) hf₁ hf₂ hw hwBound
  have h₁ := integrable_mul_three_weight hg₀ (hf₁.sub hg₁) hf₂ hw hwBound
  have h₂ := integrable_mul_three_weight hg₀ hg₁ (hf₂.sub hg₂) hw hwBound
  simp only [Pi.sub_apply] at h₀ h₁ h₂
  have h₀₁ := h₀.add h₁
  simp only [Pi.add_def] at h₀₁
  rw [← integral_sub hF hG, ← integral_add h₀ h₁, ← integral_add h₀₁ h₂]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by ring)

-- @node: abs_integral_mul_three_weight_sub_le
/-- Suppose [f₀, f₁, f₂, g₀, g₁, and g₂ each belong to L³ under
μ](hyp:hf₀,hf₁,hf₂,hg₀,hg₁,hg₂), [w is almost
everywhere strongly measurable](hyp:hw), and [|w| ≤ 1 almost
everywhere](hyp:hwBound). Then [the absolute difference between the integrals
of f₀f₁f₂w and g₀g₁g₂w is at most the sum of three products of L³ norms:
those of (f₀ − g₀), f₁, f₂; those of g₀, (f₁ − g₁), f₂; and those of
g₀, g₁, (f₂ − g₂)](goal). -/
lemma abs_integral_mul_three_weight_sub_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f₀ f₁ f₂ g₀ g₁ g₂ w : α → ℝ}
    (hf₀ : MemLp f₀ 3 μ) (hf₁ : MemLp f₁ 3 μ) (hf₂ : MemLp f₂ 3 μ)
    (hg₀ : MemLp g₀ 3 μ) (hg₁ : MemLp g₁ 3 μ) (hg₂ : MemLp g₂ 3 μ)
    (hw : AEStronglyMeasurable w μ) (hwBound : ∀ᵐ x ∂μ, ‖w x‖ ≤ 1) :
    |(∫ x, f₀ x * f₁ x * f₂ x * w x ∂μ) -
        (∫ x, g₀ x * g₁ x * g₂ x * w x ∂μ)| ≤
      (eLpNorm (fun x => f₀ x - g₀ x) 3 μ).toReal *
          (eLpNorm f₁ 3 μ).toReal * (eLpNorm f₂ 3 μ).toReal +
        (eLpNorm g₀ 3 μ).toReal * (eLpNorm (fun x => f₁ x - g₁ x) 3 μ).toReal *
          (eLpNorm f₂ 3 μ).toReal +
        (eLpNorm g₀ 3 μ).toReal * (eLpNorm g₁ 3 μ).toReal *
          (eLpNorm (fun x => f₂ x - g₂ x) 3 μ).toReal := by
  rw [integral_mul_three_weight_sub hf₀ hf₁ hf₂ hg₀ hg₁ hg₂ hw hwBound]
  apply (abs_add_le _ _).trans
  apply add_le_add
  · apply (abs_add_le _ _).trans
    simpa only [Pi.sub_apply, Pi.sub_def] using add_le_add
      (abs_integral_mul_three_weight_le (hf₀.sub hg₀) hf₁ hf₂ hw hwBound)
      (abs_integral_mul_three_weight_le hg₀ (hf₁.sub hg₁) hf₂ hw hwBound)
  · simpa only [Pi.sub_apply, Pi.sub_def] using
      abs_integral_mul_three_weight_le hg₀ hg₁ (hf₂.sub hg₂) hw hwBound

-- @node: abs_haarSign_product_le_one
/-- [The absolute product of three Haar sign functions at a common scale,
each evaluated at its own location and coordinate of a real triple, is at
most one](goal). -/
lemma abs_haarSign_product_le_one (k : ℤ) (n : Fin 3 → ℕ)
    (x : ℝ × (ℝ × ℝ)) :
    |haarSign k (n 0) x.1 * haarSign k (n 1) x.2.1 *
      haarSign k (n 2) x.2.2| ≤ 1 := by
  calc
    _ = |haarSign k (n 0) x.1| * |haarSign k (n 1) x.2.1| *
        |haarSign k (n 2) x.2.2| := by simp only [abs_mul]
    _ ≤ 1 * 1 * 1 := by
      gcongr <;> apply abs_haarSign_le_one
    _ = 1 := by norm_num

-- @node: localForm_le_local_L3
/-- If [F₀ on the first and second coordinates belongs to L³ on the dyadic box
at scale k and locations n](hyp:h₀), [F₁ on the second and third coordinates
belongs to L³ on that box](hyp:h₁), and [F₂ on the third and first coordinates
belongs to L³ on that box](hyp:h₂), then [the absolute local
trilinear form is at most 2 to the power −k times the product of these three
L³ norms on that box](goal). -/
lemma localForm_le_local_L3 (k : ℤ) (n : Fin 3 → ℕ)
    (F : Fin 3 → ℝ × ℝ → ℝ)
    (h₀ : MemLp (fun x : ℝ × (ℝ × ℝ) => F 0 (x.1, x.2.1)) 3
      (volume.restrict (dyadicInterval k (n 0) ×ˢ
        (dyadicInterval k (n 1) ×ˢ dyadicInterval k (n 2)))))
    (h₁ : MemLp (fun x : ℝ × (ℝ × ℝ) => F 1 (x.2.1, x.2.2)) 3
      (volume.restrict (dyadicInterval k (n 0) ×ˢ
        (dyadicInterval k (n 1) ×ˢ dyadicInterval k (n 2)))))
    (h₂ : MemLp (fun x : ℝ × (ℝ × ℝ) => F 2 (x.2.2, x.1)) 3
      (volume.restrict (dyadicInterval k (n 0) ×ˢ
        (dyadicInterval k (n 1) ×ˢ dyadicInterval k (n 2))))) :
    let μ := volume.restrict (dyadicInterval k (n 0) ×ˢ
      (dyadicInterval k (n 1) ×ˢ dyadicInterval k (n 2)))
    |localForm k n F| ≤ (2 : ℝ) ^ (-k) *
      ((eLpNorm (fun x : ℝ × (ℝ × ℝ) => F 0 (x.1, x.2.1)) 3 μ).toReal *
        (eLpNorm (fun x : ℝ × (ℝ × ℝ) => F 1 (x.2.1, x.2.2)) 3 μ).toReal *
        (eLpNorm (fun x : ℝ × (ℝ × ℝ) => F 2 (x.2.2, x.1)) 3 μ).toReal) := by
  dsimp only
  have hw : AEStronglyMeasurable (fun x : ℝ × (ℝ × ℝ) =>
      haarSign k (n 0) x.1 * haarSign k (n 1) x.2.1 * haarSign k (n 2) x.2.2)
      (volume.restrict (dyadicInterval k (n 0) ×ˢ
        (dyadicInterval k (n 1) ×ˢ dyadicInterval k (n 2)))) := by
    fun_prop
  have h := abs_integral_mul_three_weight_le h₀ h₁ h₂ hw
    (Filter.Eventually.of_forall (fun x => by
      simpa only [Real.norm_eq_abs] using abs_haarSign_product_le_one k n x))
  unfold localForm
  rw [abs_mul, abs_of_pos (by positivity : 0 < (2 : ℝ) ^ (-k))]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [mul_assoc] using h

end Papers.OaiBoundDyadicTriangular

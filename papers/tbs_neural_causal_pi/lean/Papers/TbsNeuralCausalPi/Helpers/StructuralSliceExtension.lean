module
public import Papers.TbsNeuralCausalPi.Helpers.StructuralScalarExtension
public import Mathlib.Analysis.Normed.Lp.ProdLp
public import Mathlib.Analysis.Normed.Affine.AddTorsor
/-! # Convex-range extension between categorical parent slices

Interpolation between adjacent labels, followed by endpoint gluing, preserves
the exact Lipschitz constant for the input one-norm. This construction retains
any convex output constraint in every dimension. The carrying-set version
allows the other categorical coordinates to remain restricted during extension.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open scoped NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {X E : Type*} [PseudoMetricSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- [The distance between two input pairs is the distance between their first
coordinates plus the absolute difference between their real coordinates](goal). -/
-- @node: structural_slice_prod_dist
lemma structural_slice_prod_dist (z w : WithLp 1 (X × ℝ)) :
    dist z w = dist z.fst w.fst + dist z.snd w.snd := by
  rw [WithLp.prod_dist_eq_add (by norm_num : 0 < (1 : ENNReal).toReal)]
  norm_num

-- @node: structuralSliceWeight
/-- For [a real interpolation coordinate t](hyp:t), the [clipped interpolation
weight](goal) is t truncated to the interval from zero to one. -/
def structuralSliceWeight (t : ℝ) : ℝ := max 0 (min t 1)

-- @node: structuralSliceWeight_mem
/-- [The clipped interpolation weight lies between zero and one, inclusive,
for every real input](goal). -/
lemma structuralSliceWeight_mem (t : ℝ) : structuralSliceWeight t ∈ Set.Icc 0 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩

-- @node: structuralSliceWeight_lipschitz
/-- [Clipping a real interpolation coordinate to the interval from zero to one
is Lipschitz with constant one](goal). -/
lemma structuralSliceWeight_lipschitz : LipschitzWith 1 structuralSliceWeight :=
  (LipschitzWith.id.min_const 1).const_max 0

-- @node: structuralSliceWeight_eq_zero
/-- If [the interpolation coordinate is at most zero](hyp:ht), then
[its clipped weight equals zero](goal). -/
lemma structuralSliceWeight_eq_zero {t : ℝ} (ht : t ≤ 0) :
    structuralSliceWeight t = 0 := by
  exact max_eq_left ((min_le_left t 1).trans ht)

-- @node: structuralSliceWeight_eq_one
/-- If [the interpolation coordinate is at least one](hyp:ht), then
[its clipped weight equals one](goal). -/
lemma structuralSliceWeight_eq_one {t : ℝ} (ht : 1 ≤ t) :
    structuralSliceWeight t = 1 := by
  simp [structuralSliceWeight, min_eq_right ht]

-- @node: structuralSliceBlend
/-- Given [an input space X](hyp:X), [an output vector space E](hyp:E),
[a lower slice function](hyp:f₀), [an upper slice function](hyp:f₁),
[an input x](hyp:x), and [a real interpolation coordinate t](hyp:t), the
[slice blend](goal) is the weighted average of the two slice values at x,
using the clipped value of t as the upper slice's weight. -/
def structuralSliceBlend (f₀ f₁ : X → E) (x : X) (t : ℝ) : E :=
  (1 - structuralSliceWeight t) • f₀ x + structuralSliceWeight t • f₁ x

-- @node: structuralSliceBlend_zero
/-- [At interpolation coordinate zero, the slice blend equals the lower
slice value](goal). -/
@[simp] lemma structuralSliceBlend_zero (f₀ f₁ : X → E) (x : X) :
    structuralSliceBlend f₀ f₁ x 0 = f₀ x := by
  simp [structuralSliceBlend, structuralSliceWeight]

-- @node: structuralSliceBlend_one
/-- [At interpolation coordinate one, the slice blend equals the upper
slice value](goal). -/
@[simp] lemma structuralSliceBlend_one (f₀ f₁ : X → E) (x : X) :
    structuralSliceBlend f₀ f₁ x 1 = f₁ x := by
  simp [structuralSliceBlend, structuralSliceWeight]

-- @node: structuralSliceBlend_mem_convex
/-- If [the output constraint set is convex](hyp:hS), [every lower slice value
belongs to it](hyp:h₀), and [every upper slice value belongs to it](hyp:h₁),
then [every slice blend belongs to the same set](goal). -/
lemma structuralSliceBlend_mem_convex (f₀ f₁ : X → E) {S : Set E}
    (hS : Convex ℝ S) (h₀ : ∀ x, f₀ x ∈ S) (h₁ : ∀ x, f₁ x ∈ S)
    (x : X) (t : ℝ) : structuralSliceBlend f₀ f₁ x t ∈ S := by
  have ht := structuralSliceWeight_mem t
  exact hS (h₀ x) (h₁ x) (sub_nonneg.mpr ht.2) ht.1 (by ring)

-- @node: structuralSliceBlend_horizontal
/-- If [the lower slice is Lipschitz with constant L](hyp:h₀) and
[the upper slice is Lipschitz with constant L](hyp:h₁), then
[the blend at any fixed interpolation coordinate is Lipschitz in the remaining
input with the same constant L](goal). -/
lemma structuralSliceBlend_horizontal (f₀ f₁ : X → E) {L : ℝ≥0}
    (h₀ : LipschitzWith L f₀) (h₁ : LipschitzWith L f₁) (t : ℝ) :
    LipschitzWith L (fun x => structuralSliceBlend f₀ f₁ x t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have ht := structuralSliceWeight_mem t
  have heq : structuralSliceBlend f₀ f₁ x t - structuralSliceBlend f₀ f₁ y t =
      (1 - structuralSliceWeight t) • (f₀ x - f₀ y) +
        structuralSliceWeight t • (f₁ x - f₁ y) := by
    simp only [structuralSliceBlend, smul_sub]
    abel
  rw [dist_eq_norm, heq]
  calc
    _ ≤ ‖(1 - structuralSliceWeight t) • (f₀ x - f₀ y)‖ +
        ‖structuralSliceWeight t • (f₁ x - f₁ y)‖ := norm_add_le _ _
    _ = (1 - structuralSliceWeight t) * dist (f₀ x) (f₀ y) +
        structuralSliceWeight t * dist (f₁ x) (f₁ y) := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1,
        abs_of_nonneg (sub_nonneg.mpr ht.2), dist_eq_norm]
    _ ≤ (1 - structuralSliceWeight t) * (L * dist x y) +
        structuralSliceWeight t * (L * dist x y) :=
      add_le_add (mul_le_mul_of_nonneg_left (h₀.dist_le_mul x y) (sub_nonneg.mpr ht.2))
        (mul_le_mul_of_nonneg_left (h₁.dist_le_mul x y) ht.1)
    _ = L * dist x y := by ring

-- @node: structuralSliceBlend_vertical
/-- If [the two slice values are at distance at most L at every input](hyp:hstep),
then [their blend at a fixed input is Lipschitz in the interpolation coordinate
with constant L](goal). -/
lemma structuralSliceBlend_vertical (f₀ f₁ : X → E) {L : ℝ≥0}
    (hstep : ∀ x, dist (f₀ x) (f₁ x) ≤ L) (x : X) :
    LipschitzWith L (structuralSliceBlend f₀ f₁ x) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  have heq (r : ℝ) : structuralSliceBlend f₀ f₁ x r =
      AffineMap.lineMap (f₀ x) (f₁ x) (structuralSliceWeight r) :=
    (AffineMap.lineMap_apply_module _ _ _).symm
  rw [heq s, heq t, dist_lineMap_lineMap]
  calc
    _ ≤ dist s t * (L : ℝ) :=
      mul_le_mul (structuralSliceWeight_lipschitz.dist_le_mul s t |>.trans_eq (one_mul _))
        (hstep x) dist_nonneg dist_nonneg
    _ = L * dist s t := mul_comm _ _

/-- If [the lower slice is Lipschitz with constant L](hyp:h₀),
[the upper slice is Lipschitz with constant L](hyp:h₁), and
[their values at each common input differ by at most L](hyp:hstep), then
[the blend is jointly Lipschitz with constant L for the sum of the distances
in the remaining input and interpolation coordinate](goal). -/
-- @node: structuralSliceBlend_lipschitz
lemma structuralSliceBlend_lipschitz (f₀ f₁ : X → E) {L : ℝ≥0}
    (h₀ : LipschitzWith L f₀) (h₁ : LipschitzWith L f₁)
    (hstep : ∀ x, dist (f₀ x) (f₁ x) ≤ L) :
    LipschitzWith L (fun z : WithLp 1 (X × ℝ) =>
      structuralSliceBlend f₀ f₁ z.fst z.snd) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  calc
    _ ≤ dist (structuralSliceBlend f₀ f₁ z.fst z.snd)
        (structuralSliceBlend f₀ f₁ w.fst z.snd) +
        dist (structuralSliceBlend f₀ f₁ w.fst z.snd)
          (structuralSliceBlend f₀ f₁ w.fst w.snd) := dist_triangle _ _ _
    _ ≤ L * dist z.fst w.fst + L * dist z.snd w.snd :=
      add_le_add ((structuralSliceBlend_horizontal f₀ f₁ h₀ h₁ z.snd).dist_le_mul _ _)
        ((structuralSliceBlend_vertical f₀ f₁ hstep w.fst).dist_le_mul _ _)
    _ = L * dist z w := by rw [structural_slice_prod_dist]; ring

/-- If [the output constraint set is convex](hyp:hS), [a mechanism is Lipschitz
with constant L on the union of the slices at labels zero and one](hyp:hf), and
[its values on those slices belong to the constraint set](hyp:hrange), then
[it has an extension to all real labels that is Lipschitz with constant L for
the input one-norm, takes values in that set everywhere, and agrees with the
original mechanism on both slices](goal). -/
-- @node: structural_two_slice_extension
lemma structural_two_slice_extension (f : WithLp 1 (X × ℝ) → E)
    {L : ℝ≥0} {S : Set E} (hS : Convex ℝ S)
    (hf : LipschitzOnWith L f {z | z.snd = 0 ∨ z.snd = 1})
    (hrange : ∀ z, z.snd = 0 ∨ z.snd = 1 → f z ∈ S) :
    ∃ g : WithLp 1 (X × ℝ) → E, LipschitzWith L g ∧
      (∀ z, g z ∈ S) ∧ Set.EqOn g f {z | z.snd = 0 ∨ z.snd = 1} := by
  let f₀ := fun x => f (WithLp.toLp 1 (x, (0 : ℝ)))
  let f₁ := fun x => f (WithLp.toLp 1 (x, (1 : ℝ)))
  have hs₀ : LipschitzWith L f₀ := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa [f₀, structural_slice_prod_dist] using
      hf.dist_le_mul (WithLp.toLp 1 (x, 0)) (Or.inl rfl)
        (WithLp.toLp 1 (y, 0)) (Or.inl rfl)
  have hs₁ : LipschitzWith L f₁ := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa [f₁, structural_slice_prod_dist] using
      hf.dist_le_mul (WithLp.toLp 1 (x, 1)) (Or.inr rfl)
        (WithLp.toLp 1 (y, 1)) (Or.inr rfl)
  have hstep (x : X) : dist (f₀ x) (f₁ x) ≤ L := by
    simpa [f₀, f₁, structural_slice_prod_dist, Real.dist_eq] using
      hf.dist_le_mul (WithLp.toLp 1 (x, 0)) (Or.inl rfl)
        (WithLp.toLp 1 (x, 1)) (Or.inr rfl)
  refine ⟨fun z => structuralSliceBlend f₀ f₁ z.fst z.snd,
    structuralSliceBlend_lipschitz f₀ f₁ hs₀ hs₁ hstep, ?_, ?_⟩
  · intro z
    exact structuralSliceBlend_mem_convex f₀ f₁ hS
      (fun x => hrange _ (Or.inl rfl)) (fun x => hrange _ (Or.inr rfl)) _ _
  · intro z hz
    rcases hz with hz | hz
    · change structuralSliceBlend f₀ f₁ z.fst z.snd = f z
      rw [hz, structuralSliceBlend_zero]
      exact congrArg f (WithLp.ofLp_injective 1 (Prod.ext rfl hz.symm))
    · change structuralSliceBlend f₀ f₁ z.fst z.snd = f z
      rw [hz, structuralSliceBlend_one]
      exact congrArg f (WithLp.ofLp_injective 1 (Prod.ext rfl hz.symm))

/-- If [one curve is Lipschitz with constant L](hyp:hf), [a second curve is
Lipschitz with constant L](hyp:hg), and [the curves agree at a](hyp:ha), then
[the curve that uses the first up to a and the second after a is Lipschitz
with constant L](goal). -/
-- @node: structural_paste_lipschitz
lemma structural_paste_lipschitz {F : Type*} [PseudoMetricSpace F]
    {f g : ℝ → F} {L : ℝ≥0} (hf : LipschitzWith L f) (hg : LipschitzWith L g)
    (a : ℝ) (ha : f a = g a) :
    LipschitzWith L (fun t => if t ≤ a then f t else g t) := by
  have hcross (s t : ℝ) (hs : s ≤ a) (ht : a ≤ t) :
      dist (f s) (g t) ≤ L * dist s t := by
    calc
      _ ≤ dist (f s) (f a) + dist (f a) (g t) := dist_triangle _ _ _
      _ = dist (f s) (f a) + dist (g a) (g t) := by rw [ha]
      _ ≤ L * dist s a + L * dist a t :=
        add_le_add (hf.dist_le_mul _ _) (hg.dist_le_mul _ _)
      _ = L * dist s t := by
        rw [Real.dist_eq, Real.dist_eq, Real.dist_eq,
          abs_of_nonpos (sub_nonpos.mpr hs), abs_of_nonpos (sub_nonpos.mpr ht),
          abs_of_nonpos (sub_nonpos.mpr (hs.trans ht))]
        ring
  apply LipschitzWith.of_dist_le_mul
  intro s t
  by_cases hs : s ≤ a <;> by_cases ht : t ≤ a
  · simp only [if_pos hs, if_pos ht]
    exact hf.dist_le_mul _ _
  · simp only [if_pos hs, if_neg ht]
    exact hcross s t hs (le_of_not_ge ht)
  · simp only [if_neg hs, if_pos ht]
    rw [dist_comm (g s) (f t), dist_comm s t]
    exact hcross t s ht (le_of_not_ge hs)
  · simp only [if_neg hs, if_neg ht]
    exact hg.dist_le_mul _ _

-- @node: structuralFiniteSlice
/-- For [an input space X](hyp:X), [an output vector space E](hyp:E),
[a largest categorical label k](hyp:k), [a family of slice functions f](hyp:f),
[an input x](hyp:x), and [a real label t](hyp:t), the [finite-slice
interpolant](goal) is defined recursively: [with largest label zero it returns
the value of slice zero at x](step:1); [with largest label k + 1 it uses the
interpolant through k when t is at most k, and otherwise blends slices k and
k + 1 with clipped weight t minus k](step:2). -/
def structuralFiniteSlice : ℕ → (ℕ → X → E) → X → ℝ → E
  | 0, f, x, _ => f 0 x
  | k + 1, f, x, t => if t ≤ (k : ℝ) then structuralFiniteSlice k f x t
      else structuralSliceBlend (f k) (f (k + 1)) x (t - k)

-- @node: structuralFiniteSlice_right
/-- If [the real label is at least the largest categorical label k](hyp:ht),
then [the finite-slice interpolant equals the value of slice k](goal). -/
lemma structuralFiniteSlice_right (k : ℕ) (f : ℕ → X → E) (x : X)
    {t : ℝ} (ht : (k : ℝ) ≤ t) : structuralFiniteSlice k f x t = f k x := by
  cases k with
  | zero => rfl
  | succ k =>
    have hk : ¬ t ≤ (k : ℝ) := by push_cast at ht; linarith
    simp only [structuralFiniteSlice, if_neg hk, structuralSliceBlend,
      structuralSliceWeight_eq_one (show 1 ≤ t - k by push_cast at ht; linarith)]
    simp

-- @node: structuralFiniteSlice_left
/-- If [the real label is at most zero](hyp:ht), then [the finite-slice
interpolant equals the value of slice zero](goal). -/
lemma structuralFiniteSlice_left (k : ℕ) (f : ℕ → X → E) (x : X)
    {t : ℝ} (ht : t ≤ 0) : structuralFiniteSlice k f x t = f 0 x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk : t ≤ (k : ℝ) := ht.trans (Nat.cast_nonneg k)
    simpa only [structuralFiniteSlice, if_pos hk] using ih

-- @node: structuralFiniteSlice_label
/-- If [the categorical label j is at most the largest label k](hyp:hj), then
[the finite-slice interpolant at j equals the original value of slice j](goal). -/
lemma structuralFiniteSlice_label (k : ℕ) (f : ℕ → X → E) (x : X)
    (j : ℕ) (hj : j ≤ k) : structuralFiniteSlice k f x j = f j x := by
  induction k with
  | zero => have : j = 0 := by omega
            subst j
            rfl
  | succ k ih =>
    by_cases h : j ≤ k
    · simpa only [structuralFiniteSlice, if_pos (show (j : ℝ) ≤ k by exact_mod_cast h)]
        using ih h
    · have he : j = k + 1 := by omega
      subst j
      exact structuralFiniteSlice_right (k + 1) f x le_rfl

-- @node: structuralFiniteSlice_mem_convex
/-- If [the output constraint set is convex](hyp:hS) and [every slice with
label from zero through k takes values in that set](hyp:hf), then
[the finite-slice interpolant belongs to that set at every input and real
label](goal). -/
lemma structuralFiniteSlice_mem_convex (k : ℕ) (f : ℕ → X → E) {S : Set E}
    (hS : Convex ℝ S) (hf : ∀ j ≤ k, ∀ x, f j x ∈ S) (x : X) (t : ℝ) :
    structuralFiniteSlice k f x t ∈ S := by
  induction k with
  | zero => exact hf 0 le_rfl x
  | succ k ih =>
    dsimp only [structuralFiniteSlice]
    split
    · exact ih (fun j hj => hf j (hj.trans (Nat.le_succ k)))
    · exact structuralSliceBlend_mem_convex (f k) (f (k + 1)) hS
        (hf k (Nat.le_succ k)) (hf (k + 1) le_rfl) x (t - k)

-- @node: structuralFiniteSlice_horizontal
/-- If [every slice with label from zero through k is Lipschitz with constant
L](hyp:hf), then [the finite-slice interpolant at any fixed real label is
Lipschitz in the remaining input with constant L](goal). -/
lemma structuralFiniteSlice_horizontal (k : ℕ) (f : ℕ → X → E) {L : ℝ≥0}
    (hf : ∀ j ≤ k, LipschitzWith L (f j)) (t : ℝ) :
    LipschitzWith L (fun x => structuralFiniteSlice k f x t) := by
  induction k with
  | zero => exact hf 0 le_rfl
  | succ k ih =>
    by_cases ht : t ≤ (k : ℝ)
    · simpa only [structuralFiniteSlice, if_pos ht] using
        ih (fun j hj => hf j (hj.trans (Nat.le_succ k)))
    · simpa only [structuralFiniteSlice, if_neg ht] using
        structuralSliceBlend_horizontal (f k) (f (k + 1))
          (hf k (Nat.le_succ k)) (hf (k + 1) le_rfl) (t - k)

-- @node: structuralFiniteSlice_vertical
/-- If [successive slices from zero through k have values at distance at most
L at each common input](hyp:hstep), then [the finite-slice interpolant at any
fixed input is Lipschitz in the real label with constant L](goal). -/
lemma structuralFiniteSlice_vertical (k : ℕ) (f : ℕ → X → E) {L : ℝ≥0}
    (hstep : ∀ j < k, ∀ x, dist (f j x) (f (j + 1) x) ≤ L) (x : X) :
    LipschitzWith L (structuralFiniteSlice k f x) := by
  induction k with
  | zero =>
    change LipschitzWith L (fun _ : ℝ => f 0 x)
    apply LipschitzWith.of_dist_le_mul
    intro s t
    simp only [dist_self]
    positivity
  | succ k ih =>
    have hprev := ih (fun j hj => hstep j (hj.trans (Nat.lt_succ_self k)))
    have hshift : LipschitzWith 1 (fun t : ℝ => t - (k : ℝ)) := by
      apply LipschitzWith.of_dist_le_mul
      intro s t
      simp
    have hnext : LipschitzWith L (fun t =>
        structuralSliceBlend (f k) (f (k + 1)) x (t - k)) := by
      simpa only [mul_one, Function.comp_def] using
        (structuralSliceBlend_vertical (f k) (f (k + 1))
          (hstep k (Nat.lt_succ_self k)) x).comp hshift
    apply structural_paste_lipschitz hprev hnext (k : ℝ)
    rw [structuralFiniteSlice_right k f x le_rfl, sub_self, structuralSliceBlend_zero]

-- @node: structuralFiniteSlice_lipschitz
/-- If [every slice from zero through k is Lipschitz with constant L](hyp:hf)
and [successive slices have values at distance at most L at every common
input](hyp:hstep), then [the finite-slice interpolant is jointly Lipschitz
with constant L for the sum of the distances in the remaining input and
real label](goal). -/
lemma structuralFiniteSlice_lipschitz (k : ℕ) (f : ℕ → X → E) {L : ℝ≥0}
    (hf : ∀ j ≤ k, LipschitzWith L (f j))
    (hstep : ∀ j < k, ∀ x, dist (f j x) (f (j + 1) x) ≤ L) :
    LipschitzWith L (fun z : WithLp 1 (X × ℝ) => structuralFiniteSlice k f z.fst z.snd) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  calc
    _ ≤ dist (structuralFiniteSlice k f z.fst z.snd)
        (structuralFiniteSlice k f w.fst z.snd) +
        dist (structuralFiniteSlice k f w.fst z.snd)
          (structuralFiniteSlice k f w.fst w.snd) := dist_triangle _ _ _
    _ ≤ L * dist z.fst w.fst + L * dist z.snd w.snd :=
      add_le_add ((structuralFiniteSlice_horizontal k f hf z.snd).dist_le_mul _ _)
        ((structuralFiniteSlice_vertical k f hstep w.fst).dist_le_mul _ _)
    _ = L * dist z w := by rw [structural_slice_prod_dist]; ring

/-- If [the output constraint set is convex](hyp:hS), [a mechanism is Lipschitz
with constant L on the categorical slices labeled zero through k](hyp:hf),
and [its values on those slices belong to the constraint set](hyp:hrange),
then [it has an extension to all real labels that is Lipschitz with constant
L for the input one-norm, takes values in that set everywhere, and agrees
with the mechanism on all the original slices](goal). -/
-- @node: structural_finite_slice_extension
lemma structural_finite_slice_extension (k : ℕ) (f : WithLp 1 (X × ℝ) → E)
    {L : ℝ≥0} {S : Set E} (hS : Convex ℝ S)
    (hf : LipschitzOnWith L f {z : WithLp 1 (X × ℝ) | ∃ j : ℕ, j ≤ k ∧ z.snd = j})
    (hrange : ∀ z : WithLp 1 (X × ℝ), (∃ j : ℕ, j ≤ k ∧ z.snd = j) → f z ∈ S) :
    ∃ g : WithLp 1 (X × ℝ) → E, LipschitzWith L g ∧
      (∀ z, g z ∈ S) ∧ Set.EqOn g f {z : WithLp 1 (X × ℝ) | ∃ j : ℕ, j ≤ k ∧ z.snd = j} := by
  let F := fun (j : ℕ) (x : X) => f (WithLp.toLp 1 (x, (j : ℝ)))
  have hs (j : ℕ) (hj : j ≤ k) : LipschitzWith L (F j) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa [F, structural_slice_prod_dist] using
      hf.dist_le_mul (WithLp.toLp 1 (x, (j : ℝ))) ⟨j, hj, rfl⟩
        (WithLp.toLp 1 (y, (j : ℝ))) ⟨j, hj, rfl⟩
  have hstep (j : ℕ) (hj : j < k) (x : X) : dist (F j x) (F (j + 1) x) ≤ L := by
    simpa [F, structural_slice_prod_dist, Real.dist_eq, Nat.cast_add,
      show (j : ℝ) - ((j : ℝ) + 1) = -1 by ring] using
      hf.dist_le_mul (WithLp.toLp 1 (x, (j : ℝ))) ⟨j, hj.le, rfl⟩
        (WithLp.toLp 1 (x, ((j + 1 : ℕ) : ℝ))) ⟨j + 1, hj, rfl⟩
  refine ⟨fun z => structuralFiniteSlice k F z.fst z.snd,
    structuralFiniteSlice_lipschitz k F hs hstep, ?_, ?_⟩
  · intro z
    exact structuralFiniteSlice_mem_convex k F hS
      (fun j hj x => hrange _ ⟨j, hj, rfl⟩) _ _
  · intro z hz
    obtain ⟨j, hj, hz⟩ := hz
    change structuralFiniteSlice k F z.fst z.snd = f z
    rw [hz, structuralFiniteSlice_label k F z.fst j hj]
    exact congrArg f (WithLp.ofLp_injective 1 (Prod.ext rfl hz.symm))

/-- If [the output constraint set is convex](hyp:hS), [a mechanism is Lipschitz
with constant L when its remaining input lies in s and its label is an integer
from zero through k](hyp:hf), and [its values on that domain belong to the
constraint set](hyp:hrange), then [there is a function on all inputs that is
Lipschitz with constant L for the input one-norm and takes values in the
constraint set whenever the remaining input lies in s, and agrees with the
original mechanism on that domain](goal). -/
-- @node: structural_finite_slice_extension_on
lemma structural_finite_slice_extension_on (k : ℕ) (s : Set X)
    (f : WithLp 1 (X × ℝ) → E) {L : ℝ≥0} {S : Set E} (hS : Convex ℝ S)
    (hf : LipschitzOnWith L f
      {z : WithLp 1 (X × ℝ) | z.fst ∈ s ∧ ∃ j : ℕ, j ≤ k ∧ z.snd = j})
    (hrange : ∀ z : WithLp 1 (X × ℝ),
      z.fst ∈ s → (∃ j : ℕ, j ≤ k ∧ z.snd = j) → f z ∈ S) :
    ∃ g : WithLp 1 (X × ℝ) → E,
      LipschitzOnWith L g {z | z.fst ∈ s} ∧
      (∀ z, z.fst ∈ s → g z ∈ S) ∧
      Set.EqOn g f {z : WithLp 1 (X × ℝ) |
        z.fst ∈ s ∧ ∃ j : ℕ, j ≤ k ∧ z.snd = j} := by
  classical
  let lift : WithLp 1 (s × ℝ) → WithLp 1 (X × ℝ) :=
    fun z => WithLp.toLp 1 (z.fst.val, z.snd)
  have hdist (z w : WithLp 1 (s × ℝ)) : dist (lift z) (lift w) = dist z w := by
    simp [lift, structural_slice_prod_dist, Subtype.dist_eq]
  have hf' : LipschitzOnWith L (f ∘ lift)
      {z : WithLp 1 (s × ℝ) | ∃ j : ℕ, j ≤ k ∧ z.snd = j} := by
    apply LipschitzOnWith.of_dist_le_mul
    intro z hz w hw
    simpa only [hdist, Function.comp_apply] using
      hf.dist_le_mul (lift z) ⟨z.fst.property, hz⟩ (lift w) ⟨w.fst.property, hw⟩
  obtain ⟨g, hg, hgS, heq⟩ := structural_finite_slice_extension k (f ∘ lift) hS hf'
    (fun z hz => hrange (lift z) z.fst.property hz)
  let G : WithLp 1 (X × ℝ) → E := fun z =>
    if hz : z.fst ∈ s then g (WithLp.toLp 1 (⟨z.fst, hz⟩, z.snd)) else 0
  refine ⟨G, ?_, ?_, ?_⟩
  · apply LipschitzOnWith.of_dist_le_mul
    intro z hz w hw
    change z.fst ∈ s at hz
    change w.fst ∈ s at hw
    dsimp only [G]
    rw [dif_pos hz, dif_pos hw]
    simpa [structural_slice_prod_dist, Subtype.dist_eq] using
      hg.dist_le_mul (WithLp.toLp 1 (⟨z.fst, hz⟩, z.snd))
        (WithLp.toLp 1 (⟨w.fst, hw⟩, w.snd))
  · intro z hz
    dsimp only [G]
    rw [dif_pos hz]
    exact hgS _
  · intro z hz
    dsimp only [G]
    rw [dif_pos hz.1]
    have h := heq (x := WithLp.toLp 1 (⟨z.fst, hz.1⟩, z.snd)) hz.2
    exact h.trans (congrArg f (WithLp.ofLp_injective 1 (Prod.ext rfl rfl)))

end
end Papers.TbsNeuralCausalPi

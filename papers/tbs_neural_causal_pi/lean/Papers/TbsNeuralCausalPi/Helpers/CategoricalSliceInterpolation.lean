module
public import Mathlib.Analysis.Normed.Lp.ProdLp
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.Convex.StdSimplex
/-! # Interpolation between adjacent categorical input slices

Linear interpolation in a label coordinate preserves convex output constraints.
With the one-norm product metric it also preserves the exact common Lipschitz
constant, provided the two adjacent slices have that same separation bound.
Clamping the label coordinate gives a globally defined extension agreeing at
both labels. This is a geometric step towards categorical-parent representatives;
it does not assert agreement with arbitrary off-domain canonical values.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open scoped NNReal

-- @node: categoricalSliceWeight
/-- For [a real label coordinate t](hyp:t), the [interpolation weight](goal) is t clamped to the interval from zero to one. -/
def categoricalSliceWeight (t : ℝ) : ℝ := max 0 (min t 1)

-- @node: categoricalSliceWeight_mem
/-- [The clamped interpolation weight lies between zero and one, inclusive, for every real input](goal). -/
lemma categoricalSliceWeight_mem (t : ℝ) :
    categoricalSliceWeight t ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩

-- @node: categoricalSliceWeight_lipschitz
/-- [Clamping the label coordinate to the interval from zero to one is Lipschitz with constant one](goal). -/
lemma categoricalSliceWeight_lipschitz : LipschitzWith 1 categoricalSliceWeight := by
  exact (LipschitzWith.id.min_const 1).const_max 0

-- @node: categoricalSliceWeight_endpoints
/-- [The interpolation weight is zero at zero and one at one](goal). -/
lemma categoricalSliceWeight_endpoints :
    categoricalSliceWeight 0 = 0 ∧ categoricalSliceWeight 1 = 1 := by
  norm_num [categoricalSliceWeight]

variable {X E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

-- @node: categoricalSliceBlend
/-- Given [two slice functions](hyp:f₀,f₁) and [an input consisting of the other coordinates and a real label coordinate](hyp:z), the [slice blend](goal) is the weighted average of the two functions at those other coordinates, with the second function's weight equal to the clamped label coordinate. -/
def categoricalSliceBlend (f₀ f₁ : X → E) (z : WithLp 1 (X × ℝ)) : E :=
  (1 - categoricalSliceWeight z.snd) • f₀ z.fst +
    categoricalSliceWeight z.snd • f₁ z.fst

/-- If [the output set is convex](hyp:hS), [the first slice takes values in that set](hyp:h₀), and [the second slice also takes values in that set](hyp:h₁), [their blend belongs to the same set at every input](goal). -/
-- @node: categoricalSliceBlend_mem_convex
lemma categoricalSliceBlend_mem_convex (f₀ f₁ : X → E)
    {S : Set E} (hS : Convex ℝ S) (h₀ : ∀ x, f₀ x ∈ S) (h₁ : ∀ x, f₁ x ∈ S)
    (z : WithLp 1 (X × ℝ)) : categoricalSliceBlend f₀ f₁ z ∈ S := by
  exact hS (h₀ z.fst) (h₁ z.fst)
    (sub_nonneg.mpr (categoricalSliceWeight_mem z.snd).2)
    (categoricalSliceWeight_mem z.snd).1 (sub_add_cancel 1 _)

/-- [The slice blend equals the first function at label zero and the second function at label one, at every value of the other coordinates](goal). -/
-- @node: categoricalSliceBlend_endpoints
lemma categoricalSliceBlend_endpoints (f₀ f₁ : X → E) (x : X) :
    categoricalSliceBlend f₀ f₁ (WithLp.toLp 1 (x, (0 : ℝ))) = f₀ x ∧
    categoricalSliceBlend f₀ f₁ (WithLp.toLp 1 (x, (1 : ℝ))) = f₁ x := by
  simp [categoricalSliceBlend, categoricalSliceWeight]

variable [PseudoMetricSpace X]

/-- For [a nonnegative bound L](hyp:L), if [the first slice is L-Lipschitz](hyp:h₀), [the second slice is L-Lipschitz](hyp:h₁), and [their values at each common input are at distance at most L](hyp:hsep), [their blend is L-Lipschitz for the sum metric on the other inputs and the label coordinate](goal). -/
-- @node: categoricalSliceBlend_lipschitz
lemma categoricalSliceBlend_lipschitz (f₀ f₁ : X → E) (L : ℝ≥0)
    (h₀ : LipschitzWith L f₀) (h₁ : LipschitzWith L f₁)
    (hsep : ∀ x, dist (f₀ x) (f₁ x) ≤ L) :
    LipschitzWith L (categoricalSliceBlend f₀ f₁) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  let a := categoricalSliceWeight z.snd
  let b := categoricalSliceWeight w.snd
  have ha : 0 ≤ a := (categoricalSliceWeight_mem z.snd).1
  have ha' : 0 ≤ 1 - a := sub_nonneg.mpr (categoricalSliceWeight_mem z.snd).2
  have hhorizontal :
      dist ((1 - a) • f₀ z.fst + a • f₁ z.fst)
        ((1 - a) • f₀ w.fst + a • f₁ w.fst) ≤ L * dist z.fst w.fst := by
    calc
      _ ≤ dist ((1 - a) • f₀ z.fst) ((1 - a) • f₀ w.fst) +
          dist (a • f₁ z.fst) (a • f₁ w.fst) := dist_add_add_le _ _ _ _
      _ = (1 - a) * dist (f₀ z.fst) (f₀ w.fst) +
          a * dist (f₁ z.fst) (f₁ w.fst) := by
        simp only [dist_smul₀, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg ha']
      _ ≤ (1 - a) * (L * dist z.fst w.fst) + a * (L * dist z.fst w.fst) :=
        add_le_add (mul_le_mul_of_nonneg_left (h₀.dist_le_mul _ _) ha')
          (mul_le_mul_of_nonneg_left (h₁.dist_le_mul _ _) ha)
      _ = L * dist z.fst w.fst := by ring
  have hvertical :
      dist ((1 - a) • f₀ w.fst + a • f₁ w.fst)
        ((1 - b) • f₀ w.fst + b • f₁ w.fst) ≤ L * dist z.snd w.snd := by
    have hline := dist_lineMap_lineMap (f₀ w.fst) (f₁ w.fst) a b
    rw [AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module] at hline
    rw [hline]
    calc
      dist a b * dist (f₀ w.fst) (f₁ w.fst) ≤ dist z.snd w.snd * (L : ℝ) :=
        mul_le_mul (categoricalSliceWeight_lipschitz.dist_le_mul _ _ |>.trans_eq
          (one_mul _)) (hsep w.fst) dist_nonneg (by positivity)
      _ = L * dist z.snd w.snd := mul_comm _ _
  calc
    _ ≤ dist ((1 - a) • f₀ z.fst + a • f₁ z.fst)
          ((1 - a) • f₀ w.fst + a • f₁ w.fst) +
        dist ((1 - a) • f₀ w.fst + a • f₁ w.fst)
          ((1 - b) • f₀ w.fst + b • f₁ w.fst) := dist_triangle _ _ _
    _ ≤ L * dist z.fst w.fst + L * dist z.snd w.snd :=
      add_le_add hhorizontal hvertical
    _ = L * dist z w := by
      rw [WithLp.prod_dist_eq_add (by norm_num : (0 : ℝ) < (1 : ENNReal).toReal)]
      simp only [ENNReal.toReal_one, Real.rpow_one, one_div_one]
      ring

omit [PseudoMetricSpace X] in
-- @node: categoricalSliceBlend_norm_le
/-- If [the first slice has norm at most K everywhere](hyp:h₀) and [the second slice has norm at most K everywhere](hyp:h₁), [their blend also has norm at most K at every input](goal). -/
lemma categoricalSliceBlend_norm_le (f₀ f₁ : X → E) (K : ℝ)
    (h₀ : ∀ x, ‖f₀ x‖ ≤ K) (h₁ : ∀ x, ‖f₁ x‖ ≤ K)
    (z : WithLp 1 (X × ℝ)) : ‖categoricalSliceBlend f₀ f₁ z‖ ≤ K := by
  have h := categoricalSliceBlend_mem_convex f₀ f₁ (convex_closedBall (0 : E) K)
    (fun x => by simpa using h₀ x) (fun x => by simpa using h₁ x) z
  simpa using h

/-- If [the label coordinate of z is at most a](hyp:hz) and [a is at most the label coordinate of w](hyp:hw), [the distance from z to w equals the sum of the distances through the intermediate point with w's other coordinates and label a](goal), using the sum metric. -/
-- @node: categoricalSlice_bridge_dist
lemma categoricalSlice_bridge_dist (z w : WithLp 1 (X × ℝ)) (a : ℝ)
    (hz : z.snd ≤ a) (hw : a ≤ w.snd) :
    dist z (WithLp.toLp 1 (w.fst, a)) +
      dist (WithLp.toLp 1 (w.fst, a)) w = dist z w := by
  simp only [WithLp.prod_dist_eq_add (by norm_num : (0 : ℝ) < (1 : ENNReal).toReal),
    ENNReal.toReal_one, Real.rpow_one, one_div_one]
  change (dist z.fst w.fst + dist z.snd a) +
    (dist w.fst w.fst + dist a w.snd) = dist z.fst w.fst + dist z.snd w.snd
  rw [dist_self, zero_add, Real.dist_eq, Real.dist_eq, Real.dist_eq,
    abs_of_nonpos (sub_nonpos.mpr hz), abs_of_nonpos (sub_nonpos.mpr hw),
    abs_of_nonpos (sub_nonpos.mpr (hz.trans hw))]
  ring

omit [NormedSpace ℝ E] in
/-- For [a nonnegative bound L](hyp:L), if [the first function is L-Lipschitz](hyp:h₀), [the second function is L-Lipschitz](hyp:h₁), and [they agree at every input with label coordinate a](hyp:heq), [the function that uses the first below or at a and the second above a is L-Lipschitz for the sum metric](goal). -/
-- @node: categoricalSlice_glue_lipschitz
lemma categoricalSlice_glue_lipschitz
    (g₀ g₁ : WithLp 1 (X × ℝ) → E) (a : ℝ) (L : ℝ≥0)
    (h₀ : LipschitzWith L g₀) (h₁ : LipschitzWith L g₁)
    (heq : ∀ x, g₀ (WithLp.toLp 1 (x, a)) = g₁ (WithLp.toLp 1 (x, a))) :
    LipschitzWith L (fun z => if z.snd ≤ a then g₀ z else g₁ z) := by
  have hcross : ∀ z w : WithLp 1 (X × ℝ), z.snd ≤ a → a ≤ w.snd →
      dist (g₀ z) (g₁ w) ≤ L * dist z w := by
    intro z w hz hw
    let v := WithLp.toLp 1 (w.fst, a)
    calc
      _ ≤ dist (g₀ z) (g₀ v) + dist (g₀ v) (g₁ w) := dist_triangle _ _ _
      _ = dist (g₀ z) (g₀ v) + dist (g₁ v) (g₁ w) := by rw [heq w.fst]
      _ ≤ L * dist z v + L * dist v w :=
        add_le_add (h₀.dist_le_mul _ _) (h₁.dist_le_mul _ _)
      _ = L * dist z w := by rw [← mul_add, categoricalSlice_bridge_dist z w a hz hw]
  apply LipschitzWith.of_dist_le_mul
  intro z w
  split_ifs with hz hw hw
  · exact h₀.dist_le_mul _ _
  · exact hcross z w hz (le_of_not_ge hw)
  · rw [dist_comm (g₁ z), dist_comm z]
    exact hcross w z hw (le_of_not_ge hz)
  · exact h₁.dist_le_mul _ _

/-- [Subtracting a fixed real number from the label coordinate while keeping all other coordinates fixed preserves distances in the sum metric](goal). -/
-- @node: categoricalSlice_label_translate_isometry
lemma categoricalSlice_label_translate_isometry (a : ℝ) :
    Isometry (fun z : WithLp 1 (X × ℝ) => WithLp.toLp 1 (z.fst, z.snd - a)) := by
  apply Isometry.of_dist_eq
  intro z w
  simp only [WithLp.prod_dist_eq_add (by norm_num : (0 : ℝ) < (1 : ENNReal).toReal),
    ENNReal.toReal_one, Real.rpow_one, one_div_one]
  change (dist z.fst w.fst + dist (z.snd - a) (w.snd - a)) =
    dist z.fst w.fst + dist z.snd w.snd
  rw [dist_sub_right]

/-- For [a nonnegative bound L](hyp:L) and [a convex output set](hyp:hS), suppose [each of the k plus one slices is L-Lipschitz](hyp:hf), [adjacent slices differ by distance at most L at each common input](hyp:hsep), and [all slice values belong to the output set](hyp:hmem). Then [there is a globally L-Lipschitz function for the sum metric that agrees with every slice at its integer label from zero through k and takes values in that set everywhere](goal). -/
-- @node: categoricalFiniteSlices_extension
lemma categoricalFiniteSlices_extension (k : ℕ) (f : Fin (k + 1) → X → E)
    (L : ℝ≥0) {S : Set E} (hS : Convex ℝ S)
    (hf : ∀ i, LipschitzWith L (f i))
    (hsep : ∀ j : Fin k, ∀ x, dist (f j.castSucc x) (f j.succ x) ≤ L)
    (hmem : ∀ i x, f i x ∈ S) :
    ∃ g : WithLp 1 (X × ℝ) → E, LipschitzWith L g ∧
      (∀ i x, g (WithLp.toLp 1 (x, (i.val : ℝ))) = f i x) ∧
      (∀ z, g z ∈ S) := by
  induction k with
  | zero =>
    refine ⟨fun z => f 0 z.fst, ?_, ?_, fun z => hmem 0 z.fst⟩
    · apply LipschitzWith.of_dist_le_mul
      intro z w
      apply (hf 0).dist_le_mul _ _ |>.trans
      apply mul_le_mul_of_nonneg_left _ L.coe_nonneg
      rw [WithLp.prod_dist_eq_add (by norm_num : (0 : ℝ) < (1 : ENNReal).toReal)]
      simp only [ENNReal.toReal_one, Real.rpow_one, one_div_one]
      exact le_add_of_nonneg_right dist_nonneg
    · intro i x
      have hi : i = 0 := by apply Fin.ext; have := i.isLt; simp only [Fin.val_zero]; omega
      subst i
      rfl
  | succ k ih =>
    obtain ⟨g₀, hg₀, heq₀, hmem₀⟩ := ih (fun i => f i.castSucc)
      (fun i => hf i.castSucc)
      (fun j x => by simpa using hsep j.castSucc x)
      (fun i x => hmem i.castSucc x)
    let g₁ : WithLp 1 (X × ℝ) → E := fun z =>
      categoricalSliceBlend (f (Fin.last k).castSucc) (f (Fin.last (k + 1)))
        (WithLp.toLp 1 (z.fst, z.snd - k))
    have hg₁ : LipschitzWith L g₁ := by
      simpa only [mul_one, Function.comp_def, g₁] using
        (categoricalSliceBlend_lipschitz (f (Fin.last k).castSucc)
          (f (Fin.last (k + 1))) L (hf _) (hf _)
          (fun x => by simpa using hsep (Fin.last k) x)).comp
        (categoricalSlice_label_translate_isometry (X := X) k).lipschitz
    have hagree : ∀ x,
        g₀ (WithLp.toLp 1 (x, (k : ℝ))) = g₁ (WithLp.toLp 1 (x, (k : ℝ))) := by
      intro x
      have h := heq₀ (Fin.last k) x
      simpa [g₁, categoricalSliceBlend, categoricalSliceWeight] using h
    refine ⟨fun z => if z.snd ≤ (k : ℝ) then g₀ z else g₁ z,
      categoricalSlice_glue_lipschitz g₀ g₁ k L hg₀ hg₁ hagree, ?_, ?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · intro x
        change (if ((Fin.last (k + 1)).val : ℝ) ≤ k then _ else _) = _
        have hk : ¬ ((Fin.last (k + 1)).val : ℝ) ≤ k := by
          simp only [Fin.val_last, Nat.cast_add, Nat.cast_one]
          linarith
        rw [if_neg hk]
        simp [g₁, categoricalSliceBlend, categoricalSliceWeight, Nat.cast_add]
      · intro x
        change (if ((j.castSucc).val : ℝ) ≤ k then _ else _) = _
        have hj : ((j.castSucc).val : ℝ) ≤ k := by
          exact_mod_cast (Nat.le_of_lt_succ j.isLt)
        rw [if_pos hj]
        exact heq₀ j x
    · intro z
      change (if z.snd ≤ (k : ℝ) then g₀ z else g₁ z) ∈ S
      split_ifs
      · exact hmem₀ z
      · exact categoricalSliceBlend_mem_convex _ _ hS
          (hmem (Fin.last k).castSucc) (hmem (Fin.last (k + 1))) _

/-- For [a nonnegative bound L](hyp:L) and [a convex output set](hyp:hS), if [a function is L-Lipschitz on inputs with integer labels from zero through k](hyp:hf) and [its values there belong to the output set](hyp:hmem), [it has a globally L-Lipschitz extension for the sum metric agreeing on those inputs and taking values in that set everywhere](goal). -/
-- @node: categorical_label_slices_extension
lemma categorical_label_slices_extension (k : ℕ)
    (f : WithLp 1 (X × ℝ) → E) (L : ℝ≥0) {S : Set E} (hS : Convex ℝ S)
    (hf : LipschitzOnWith L f
      {z | ∃ j : Fin (k + 1), z.snd = (j.val : ℝ)})
    (hmem : ∀ z, (∃ j : Fin (k + 1), z.snd = (j.val : ℝ)) → f z ∈ S) :
    ∃ g : WithLp 1 (X × ℝ) → E, LipschitzWith L g ∧
      Set.EqOn g f {z | ∃ j : Fin (k + 1), z.snd = (j.val : ℝ)} ∧
      (∀ z, g z ∈ S) := by
  have hslice : ∀ j : Fin (k + 1),
      LipschitzWith L (fun x => f (WithLp.toLp 1 (x, (j.val : ℝ)))) := by
    intro j
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have h := hf.dist_le_mul (WithLp.toLp 1 (x, (j.val : ℝ))) ⟨j, rfl⟩
      (WithLp.toLp 1 (y, (j.val : ℝ))) ⟨j, rfl⟩
    simpa [WithLp.prod_dist_eq_add (by norm_num : (0 : ℝ) < (1 : ENNReal).toReal)] using h
  have hsep : ∀ j : Fin k, ∀ x,
      dist (f (WithLp.toLp 1 (x, (j.castSucc.val : ℝ))))
        (f (WithLp.toLp 1 (x, (j.succ.val : ℝ)))) ≤ L := by
    intro j x
    have h := hf.dist_le_mul (WithLp.toLp 1 (x, (j.castSucc.val : ℝ))) ⟨j.castSucc, rfl⟩
      (WithLp.toLp 1 (x, (j.succ.val : ℝ))) ⟨j.succ, rfl⟩
    simpa [WithLp.prod_dist_eq_add (by norm_num : (0 : ℝ) < (1 : ENNReal).toReal),
      Fin.val_succ, Real.dist_eq] using h
  obtain ⟨g, hg, heq, hgmem⟩ := categoricalFiniteSlices_extension k
    (fun j x => f (WithLp.toLp 1 (x, (j.val : ℝ)))) L hS hslice hsep
    (fun j x => hmem _ ⟨j, rfl⟩)
  refine ⟨g, hg, ?_, hgmem⟩
  intro z hz
  obtain ⟨j, hj⟩ := hz
  have hz : WithLp.toLp 1 (z.fst, (j.val : ℝ)) = z := by
    apply WithLp.ofLp_injective 1
    exact Prod.ext rfl hj.symm
  simpa only [hz] using heq j z.fst

/-- For [a nonnegative bound L](hyp:L), if [a function is L-Lipschitz on inputs with integer labels from zero through k](hyp:hf) and [its norm there is at most K](hyp:hb), [it has a globally L-Lipschitz extension for the sum metric agreeing on those inputs and having norm at most K everywhere](goal). -/
-- @node: categorical_label_slices_bounded_extension
lemma categorical_label_slices_bounded_extension (k : ℕ)
    (f : WithLp 1 (X × ℝ) → E) (L : ℝ≥0) (K : ℝ)
    (hf : LipschitzOnWith L f
      {z | ∃ j : Fin (k + 1), z.snd = (j.val : ℝ)})
    (hb : ∀ z, (∃ j : Fin (k + 1), z.snd = (j.val : ℝ)) → ‖f z‖ ≤ K) :
    ∃ g : WithLp 1 (X × ℝ) → E, LipschitzWith L g ∧
      Set.EqOn g f {z | ∃ j : Fin (k + 1), z.snd = (j.val : ℝ)} ∧
      (∀ z, ‖g z‖ ≤ K) := by
  obtain ⟨g, hg, heq, hb⟩ := categorical_label_slices_extension k f L
    (convex_closedBall (0 : E) K) hf (fun z hz => by simpa using hb z hz)
  exact ⟨g, hg, heq, fun z => by simpa using hb z⟩

/-- For [a nonnegative bound L](hyp:L), if [a vector-valued function is L-Lipschitz on inputs with integer labels from zero through k](hyp:hf) and [its values there are nonnegative vectors with coordinates summing to one](hyp:hs), [it has a globally L-Lipschitz extension for the sum metric agreeing on those inputs and taking values in the same probability simplex everywhere](goal). -/
-- @node: categorical_label_slices_simplex_extension
lemma categorical_label_slices_simplex_extension (k d : ℕ)
    (f : WithLp 1 (X × ℝ) → WithLp 1 (Fin d → ℝ)) (L : ℝ≥0)
    (hf : LipschitzOnWith L f
      {z | ∃ j : Fin (k + 1), z.snd = (j.val : ℝ)})
    (hs : ∀ z, (∃ j : Fin (k + 1), z.snd = (j.val : ℝ)) →
      (f z).ofLp ∈ stdSimplex ℝ (Fin d)) :
    ∃ g : WithLp 1 (X × ℝ) → WithLp 1 (Fin d → ℝ), LipschitzWith L g ∧
      Set.EqOn g f {z | ∃ j : Fin (k + 1), z.snd = (j.val : ℝ)} ∧
      (∀ z, (g z).ofLp ∈ stdSimplex ℝ (Fin d)) := by
  have hc : Convex ℝ {v : WithLp 1 (Fin d → ℝ) | v.ofLp ∈ stdSimplex ℝ (Fin d)} :=
    (convex_stdSimplex ℝ (Fin d)).linear_preimage
      (WithLp.linearEquiv 1 ℝ (Fin d → ℝ)).toLinearMap
  exact categorical_label_slices_extension k f L hc hf hs

end Papers.TbsNeuralCausalPi

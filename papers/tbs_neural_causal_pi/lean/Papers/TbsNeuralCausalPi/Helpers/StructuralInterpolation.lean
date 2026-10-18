module
public import Papers.TbsNeuralCausalPi.Setup.Notation
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Algebra.BigOperators.Fin
/-! # Convex, Lipschitz interpolation on ordered cube simplices

The affine interpolant on a Kuhn simplex has one derivative column for each
successive vertex difference. In the one-norm, bounding these differences
preserves the original Lipschitz constant, independently of output dimension.
The barycentric formula also preserves convex output constraints.
-/
@[expose] public section

namespace Papers.TbsNeuralCausalPi
open scoped BigOperators NNReal
noncomputable section

-- @node: orderedSimplexWeights
/-- For [a coordinate vector](hyp:t) and [a vertex index](hyp:i), the
[barycentric weight](goal) is the difference between the corresponding entries
of the vector with a leading one and the vector with a trailing zero. -/
def orderedSimplexWeights {d : ℕ} (t : Fin d → ℝ) (i : Fin (d + 1)) : ℝ :=
  Fin.cons (α := fun _ => ℝ) 1 t i - Fin.snoc (α := fun _ => ℝ) t 0 i

-- @node: orderedSimplexWeights_sum
/-- [The barycentric weights of any coordinate vector sum to one](goal),
including in dimension zero. -/
lemma orderedSimplexWeights_sum {d : ℕ} (t : Fin d → ℝ) :
    ∑ i, orderedSimplexWeights t i = 1 := by
  simp only [orderedSimplexWeights, Finset.sum_sub_distrib]
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  simp

-- @node: orderedSimplexWeights_nonneg
/-- If [every coordinate lies between zero and one](hyp:ht) and
[the coordinates are nonincreasing](hyp:horder), then
[every barycentric weight is nonnegative](goal). -/
lemma orderedSimplexWeights_nonneg {d : ℕ} (t : Fin d → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc 0 1) (horder : Antitone t) :
    ∀ i, 0 ≤ orderedSimplexWeights t i := by
  cases d with
  | zero => intro i; fin_cases i; norm_num [orderedSimplexWeights, Fin.snoc]
  | succ d =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [orderedSimplexWeights, Fin.snoc_castSucc] using sub_nonneg.mpr (ht 0).2
    · by_cases hj : j = Fin.last d
      · subst j
        simpa [orderedSimplexWeights] using (ht (Fin.last d)).1
      · obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hj
        simp only [orderedSimplexWeights, ← Fin.castSucc_succ,
          Fin.snoc_castSucc]
        exact sub_nonneg.mpr (horder (show j.castSucc ≤ j.succ from Nat.le_succ _))

-- @node: orderedSimplexInterpolant
/-- Given [output values along a chain of simplex vertices](hyp:y) and
[a coordinate vector](hyp:t), the [affine interpolant](goal) is the first
output value plus the sum of successive output differences weighted by the
corresponding coordinates. -/
def orderedSimplexInterpolant {d k : ℕ} (y : Fin (d + 1) → L1Vec k)
    (t : Fin d → ℝ) : L1Vec k :=
  y 0 + ∑ j, t j • (y j.succ - y j.castSucc)

-- @node: orderedSimplexInterpolant_apply
/-- [Each output coordinate of the affine interpolant equals that coordinate
of the first vertex value plus the sum of successive vertex differences in
that coordinate, weighted by the input coordinates](goal). -/
lemma orderedSimplexInterpolant_apply {d k : ℕ}
    (y : Fin (d + 1) → L1Vec k) (t : Fin d → ℝ) (j : Fin k) :
    (orderedSimplexInterpolant y t).ofLp j =
      (y 0).ofLp j + ∑ i, t i * (y i.succ - y i.castSucc).ofLp j := by
  simp [orderedSimplexInterpolant]

-- @node: orderedSimplexInterpolant_eq_sum
/-- [The affine interpolant equals the sum of vertex output values multiplied
by their barycentric weights](goal). -/
lemma orderedSimplexInterpolant_eq_sum {d k : ℕ}
    (y : Fin (d + 1) → L1Vec k) (t : Fin d → ℝ) :
    orderedSimplexInterpolant y t = ∑ i, orderedSimplexWeights t i • y i := by
  simp only [orderedSimplexWeights, sub_smul, Finset.sum_sub_distrib]
  rw [Fin.sum_univ_succ (fun i => Fin.cons (α := fun _ => ℝ) 1 t i • y i),
    Fin.sum_univ_castSucc (fun i => Fin.snoc (α := fun _ => ℝ) t 0 i • y i)]
  simp only [Fin.cons_zero, one_smul, Fin.cons_succ, Fin.snoc_castSucc,
    Fin.snoc_last, zero_smul, add_zero]
  simp only [orderedSimplexInterpolant, smul_sub, Finset.sum_sub_distrib]
  abel

-- @node: orderedSimplexInterpolant_mem_convex
/-- If [the coordinates lie between zero and one](hyp:ht),
[they are nonincreasing](hyp:horder), [the output constraint set is convex](hyp:hS),
and [every vertex output belongs to that set](hyp:hy), then
[the interpolated output belongs to the same set](goal). -/
lemma orderedSimplexInterpolant_mem_convex {d k : ℕ}
    (y : Fin (d + 1) → L1Vec k) (t : Fin d → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc 0 1) (horder : Antitone t)
    {S : Set (L1Vec k)} (hS : Convex ℝ S) (hy : ∀ i, y i ∈ S) :
    orderedSimplexInterpolant y t ∈ S := by
  rw [orderedSimplexInterpolant_eq_sum]
  exact hS.sum_mem (fun i _ => orderedSimplexWeights_nonneg t ht horder i)
    (orderedSimplexWeights_sum t) (fun i _ => hy i)

-- @node: orderedSimplexInterpolant_mem_convexHull
/-- If [the coordinates lie between zero and one](hyp:ht) and
[are nonincreasing](hyp:horder), then [the interpolated output belongs to the
convex hull of the vertex output values](goal). -/
lemma orderedSimplexInterpolant_mem_convexHull {d k : ℕ}
    (y : Fin (d + 1) → L1Vec k) (t : Fin d → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc 0 1) (horder : Antitone t) :
    orderedSimplexInterpolant y t ∈ convexHull ℝ (Set.range y) := by
  exact orderedSimplexInterpolant_mem_convex y t ht horder (convex_convexHull _ _)
    (fun i => subset_convexHull ℝ _ (Set.mem_range_self i))

-- @node: orderedSimplexInterpolant_sub
/-- [The difference between interpolated outputs at two coordinate vectors
equals the sum of successive vertex output differences weighted by the
differences between the corresponding input coordinates](goal). -/
lemma orderedSimplexInterpolant_sub {d k : ℕ}
    (y : Fin (d + 1) → L1Vec k) (t s : Fin d → ℝ) :
    orderedSimplexInterpolant y t - orderedSimplexInterpolant y s =
      ∑ j, (t j - s j) • (y j.succ - y j.castSucc) := by
  simp only [orderedSimplexInterpolant, sub_smul, Finset.sum_sub_distrib]
  abel

-- @node: orderedSimplexInterpolant_lipschitz
/-- For [a nonnegative bound L](hyp:L), if [each successive vertex output
difference has one-norm at most L](hyp:hy), then [the affine interpolant is
Lipschitz with constant L on the entire input space, using one-norm
distances](goal). -/
lemma orderedSimplexInterpolant_lipschitz {d k : ℕ}
    (y : Fin (d + 1) → L1Vec k) (L : ℝ≥0)
    (hy : ∀ j : Fin d, ‖y j.succ - y j.castSucc‖ ≤ L) :
    LipschitzWith L (fun x : L1Vec d => orderedSimplexInterpolant y x.ofLp) := by
  apply LipschitzWith.of_dist_le_mul
  intro x z
  rw [dist_eq_norm, orderedSimplexInterpolant_sub]
  calc
    ‖∑ j, (x.ofLp j - z.ofLp j) • (y j.succ - y j.castSucc)‖ ≤
        ∑ j, ‖(x.ofLp j - z.ofLp j) • (y j.succ - y j.castSucc)‖ := norm_sum_le _ _
    _ ≤ ∑ j, |x.ofLp j - z.ofLp j| * (L : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hy j) (abs_nonneg _)
    _ = L * dist x z := by
      simp only [dist_eq_norm, PiLp.norm_eq_of_L1, PiLp.sub_apply, Real.norm_eq_abs]
      rw [← Finset.sum_mul, mul_comm]

-- @node: orderedSimplexInterpolant_error
/-- If [the coordinates lie between zero and one](hyp:ht),
[they are nonincreasing](hyp:horder), and [every vertex output is within
one-norm error e of a reference output](hyp:hy), then [the interpolated
output is within one-norm error e of that reference output](goal). -/
lemma orderedSimplexInterpolant_error {d k : ℕ}
    (y : Fin (d + 1) → L1Vec k) (t : Fin d → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc 0 1) (horder : Antitone t)
    (v : L1Vec k) (e : ℝ) (hy : ∀ i, ‖y i - v‖ ≤ e) :
    ‖orderedSimplexInterpolant y t - v‖ ≤ e := by
  have hw := orderedSimplexWeights_nonneg t ht horder
  have hsum := orderedSimplexWeights_sum t
  have hid : orderedSimplexInterpolant y t - v =
      ∑ i, orderedSimplexWeights t i • (y i - v) := by
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hsum, one_smul]
    rw [orderedSimplexInterpolant_eq_sum]
  rw [hid]
  calc
    _ ≤ ∑ i, ‖orderedSimplexWeights t i • (y i - v)‖ := norm_sum_le _ _
    _ ≤ ∑ i, orderedSimplexWeights t i * e := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw i)]
      exact mul_le_mul_of_nonneg_left (hy i) (hw i)
    _ = e := by rw [← Finset.sum_mul, hsum, one_mul]

-- @node: orderedSimplexInterpolant_norm_le
/-- If [the coordinates lie between zero and one](hyp:ht),
[they are nonincreasing](hyp:horder), and [every vertex output has one-norm
at most K](hyp:hy), then [the interpolated output has one-norm at most K](goal). -/
lemma orderedSimplexInterpolant_norm_le {d k : ℕ}
    (y : Fin (d + 1) → L1Vec k) (t : Fin d → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc 0 1) (horder : Antitone t)
    (K : ℝ) (hy : ∀ i, ‖y i‖ ≤ K) :
    ‖orderedSimplexInterpolant y t‖ ≤ K := by
  simpa only [sub_zero] using
    orderedSimplexInterpolant_error y t ht horder (0 : L1Vec k) K
      (by simpa only [sub_zero] using hy)

-- @node: orderedSimplexInterpolant_simplex
/-- If [the coordinates lie between zero and one](hyp:ht),
[they are nonincreasing](hyp:horder), [all vertex output coordinates are
nonnegative](hyp:hy0), and [each vertex output sums to one](hyp:hy1), then
[the interpolated output has nonnegative coordinates summing to one](goal). -/
lemma orderedSimplexInterpolant_simplex {d k : ℕ}
    (y : Fin (d + 1) → L1Vec k) (t : Fin d → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc 0 1) (horder : Antitone t)
    (hy0 : ∀ i j, 0 ≤ (y i).ofLp j) (hy1 : ∀ i, ∑ j, (y i).ofLp j = 1) :
    (∀ j, 0 ≤ (orderedSimplexInterpolant y t).ofLp j) ∧
      ∑ j, (orderedSimplexInterpolant y t).ofLp j = 1 := by
  rw [orderedSimplexInterpolant_eq_sum]
  have hcoord (j : Fin k) :
      (∑ i, orderedSimplexWeights t i • y i).ofLp j =
        ∑ i, orderedSimplexWeights t i * (y i).ofLp j := by
    simp
  constructor
  · intro j
    rw [hcoord]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg
      (orderedSimplexWeights_nonneg t ht horder i) (hy0 i j))
  · simp_rw [hcoord]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hy1, mul_one, orderedSimplexWeights_sum]

-- @node: kuhnVertex
/-- For [a permutation specifying the order of coordinates](hyp:p) and
[a vertex index i](hyp:i), the [Kuhn simplex vertex](goal) has ones in the
first i coordinates in that order and zeros in the remaining coordinates. -/
def kuhnVertex {d : ℕ} (p : Equiv.Perm (Fin d)) (i : Fin (d + 1)) : L1Vec d :=
  WithLp.toLp 1 (fun j => if (p.symm j).val < i.val then 1 else 0)

-- @node: kuhnVertex_mem_unitCube
/-- [Every Kuhn simplex vertex belongs to the unit cube](goal). -/
lemma kuhnVertex_mem_unitCube {d : ℕ} (p : Equiv.Perm (Fin d)) (i : Fin (d + 1)) :
    kuhnVertex p i ∈ unitCube d := by
  intro j
  simp only [kuhnVertex, WithLp.ofLp_toLp]
  split_ifs <;> norm_num

-- @node: orderedSimplexWeights_vertex
/-- [At the chain vertex with its first i coordinates equal to one and the
rest zero, the barycentric weight at index j is one when j equals i and
zero otherwise](goal). -/
lemma orderedSimplexWeights_vertex {d : ℕ} (i j : Fin (d + 1)) :
    orderedSimplexWeights (fun k : Fin d => if k.val < i.val then 1 else 0) j =
      if j = i then 1 else 0 := by
  classical
  cases d with
  | zero => fin_cases i; fin_cases j; norm_num [orderedSimplexWeights, Fin.snoc]
  | succ d =>
    refine Fin.cases ?_ (fun k => ?_) j
    · change 1 - (if 0 < i.val then (1 : ℝ) else 0) =
        if (0 : Fin (d + 2)) = i then 1 else 0
      by_cases hi : i = 0
      · subst i; norm_num
      · have hne : i.val ≠ 0 := fun h => hi (Fin.ext h)
        have hv : 0 < i.val := by omega
        simp [hv, Ne.symm hi]
    · simp only [orderedSimplexWeights, Fin.cons_succ]
      by_cases hk : k = Fin.last d
      · subst k
        simp only [Fin.succ_last, Fin.snoc_last, sub_zero, Fin.val_last]
        have hi : d < i.val ↔ Fin.last (d + 1) = i := by
          constructor
          · intro hi; apply Fin.ext; simp only [Fin.val_last]; omega
          · intro hi; subst i; simp
        simp only [hi]
      · obtain ⟨k, rfl⟩ := Fin.eq_castSucc_of_ne_last hk
        rw [← Fin.castSucc_succ, Fin.snoc_castSucc]
        simp only [Fin.val_castSucc, Fin.val_succ]
        by_cases hi : k.succ.castSucc = i
        · subst i; simp
        · have he : k.val < i.val ↔ k.val + 1 < i.val := by
            have hne : k.val + 1 ≠ i.val := by
              intro he; exact hi (Fin.ext he)
            omega
          simp only [he, if_neg hi, sub_self]

-- @node: orderedSimplexInterpolant_vertex
/-- [At the chain vertex whose first i coordinates are one and whose
remaining coordinates are zero, the affine interpolant equals the vertex
output value indexed by i](goal). -/
lemma orderedSimplexInterpolant_vertex {d k : ℕ}
    (y : Fin (d + 1) → L1Vec k) (i : Fin (d + 1)) :
    orderedSimplexInterpolant y (fun j => if j.val < i.val then 1 else 0) = y i := by
  classical
  rw [orderedSimplexInterpolant_eq_sum]
  simp_rw [orderedSimplexWeights_vertex]
  simp

-- @node: kuhnVertex_sub_apply
/-- [The difference between chain vertices i + 1 and i has coordinate j
equal to one if j is the coordinate selected at position i by the
permutation, and zero otherwise](goal). -/
lemma kuhnVertex_sub_apply {d : ℕ} (p : Equiv.Perm (Fin d)) (i j : Fin d) :
    (kuhnVertex p i.succ - kuhnVertex p i.castSucc).ofLp j =
      if j = p i then 1 else 0 := by
  simp only [kuhnVertex, PiLp.sub_apply,
    Fin.val_succ, Fin.val_castSucc]
  by_cases hj : j = p i
  · subst j
    simp
  · have hne : (p.symm j).val ≠ i.val := by
      intro h
      have he : p.symm j = i := Fin.ext h
      exact hj (by simpa using congrArg p he)
    have he : ((p.symm j).val < i.val + 1) ↔ (p.symm j).val < i.val := by omega
    simp only [he, if_neg hj]
    split_ifs <;> norm_num

-- @node: kuhnVertex_dist_succ
/-- [The one-norm distance between each pair of successive Kuhn simplex
vertices is one](goal). -/
lemma kuhnVertex_dist_succ {d : ℕ} (p : Equiv.Perm (Fin d)) (i : Fin d) :
    dist (kuhnVertex p i.succ) (kuhnVertex p i.castSucc) = 1 := by
  classical
  simp only [dist_eq_norm, PiLp.norm_eq_of_L1, kuhnVertex_sub_apply, Real.norm_eq_abs]
  simp_rw [abs_ite, abs_one, abs_zero]
  simp

-- @node: structural_unitCube_dist_le
/-- If [x belongs to the unit cube](hyp:hx) and [z belongs to the unit
cube](hyp:hz), then [their one-norm distance is at most the dimension](goal). -/
lemma structural_unitCube_dist_le {d : ℕ} {x z : L1Vec d}
    (hx : x ∈ unitCube d) (hz : z ∈ unitCube d) : dist x z ≤ d := by
  rw [dist_eq_norm, PiLp.norm_eq_of_L1]
  calc
    ∑ j, ‖(x - z).ofLp j‖ ≤ ∑ _j : Fin d, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      simp only [PiLp.sub_apply, Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [(hx j).1, (hz j).2],
        by linarith [(hx j).2, (hz j).1]⟩
    _ = d := by simp

-- @node: structural_permute_isometry
/-- [Reordering coordinates by any permutation preserves all one-norm
distances](goal). -/
lemma structural_permute_isometry {d : ℕ} (p : Equiv.Perm (Fin d)) :
    Isometry (fun x : L1Vec d => WithLp.toLp 1 (fun j => x.ofLp (p j))) := by
  apply Isometry.of_dist_eq
  intro x z
  simp only [dist_eq_norm, PiLp.norm_eq_of_L1, PiLp.sub_apply]
  exact Equiv.sum_comp p (fun j => ‖x.ofLp j - z.ofLp j‖)

-- @node: kuhnInterpolant
/-- Given [a structural function](hyp:f), [a permutation specifying the
simplex coordinate order](hyp:p), and [an input point](hyp:x), the
[Kuhn interpolant](goal) affinely interpolates the function's values at the
Kuhn simplex vertices using the input coordinates in that order. -/
def kuhnInterpolant {d k : ℕ} (f : L1Vec d → L1Vec k)
    (p : Equiv.Perm (Fin d)) (x : L1Vec d) : L1Vec k :=
  orderedSimplexInterpolant (fun i => f (kuhnVertex p i)) (fun j => x.ofLp (p j))

-- @node: kuhnInterpolant_vertex
/-- [The Kuhn interpolant agrees with the original function at every vertex
of its simplex](goal). -/
lemma kuhnInterpolant_vertex {d k : ℕ} (f : L1Vec d → L1Vec k)
    (p : Equiv.Perm (Fin d)) (i : Fin (d + 1)) :
    kuhnInterpolant f p (kuhnVertex p i) = f (kuhnVertex p i) := by
  simp only [kuhnInterpolant, kuhnVertex, WithLp.ofLp_toLp, Equiv.symm_apply_apply]
  exact orderedSimplexInterpolant_vertex _ i

-- @node: kuhnInterpolant_id
/-- [The Kuhn interpolant of the identity function returns the input point
for every permutation and every input](goal). -/
lemma kuhnInterpolant_id {d : ℕ} (p : Equiv.Perm (Fin d)) (x : L1Vec d) :
    kuhnInterpolant id p x = x := by
  classical
  apply PiLp.ext
  intro j
  change (orderedSimplexInterpolant (kuhnVertex p) (fun i => x.ofLp (p i))).ofLp j = _
  rw [orderedSimplexInterpolant_apply]
  have hzero : (kuhnVertex p 0).ofLp j = 0 := by simp [kuhnVertex]
  simp only [hzero, zero_add, kuhnVertex_sub_apply]
  have he (i : Fin d) : j = p i ↔ i = p.symm j := by
    constructor
    · intro h; simpa using (congrArg p.symm h).symm
    · intro h; subst i; simp
  simp only [he, mul_ite, mul_one, mul_zero]
  simp

-- @node: mem_kuhnSimplex_convexHull
/-- If [a point belongs to the unit cube](hyp:hx) and [its coordinates are
nonincreasing in the permutation's order](hyp:horder), then [the point
belongs to the convex hull of the corresponding Kuhn simplex vertices](goal). -/
lemma mem_kuhnSimplex_convexHull {d : ℕ} (p : Equiv.Perm (Fin d))
    {x : L1Vec d} (hx : x ∈ unitCube d)
    (horder : Antitone (fun j => x.ofLp (p j))) :
    x ∈ convexHull ℝ (Set.range (kuhnVertex p)) := by
  have h := orderedSimplexInterpolant_mem_convexHull (kuhnVertex p)
    (fun j => x.ofLp (p j)) (fun j => hx (p j)) horder
  change kuhnInterpolant id p x ∈ _ at h
  rwa [kuhnInterpolant_id] at h

-- @node: kuhnInterpolant_lipschitz
/-- For [a nonnegative constant L](hyp:L), if [the structural function is
Lipschitz with constant L on the unit cube](hyp:hf), then [its Kuhn
interpolant is Lipschitz with constant L on the entire input space, using
one-norm distances](goal). -/
lemma kuhnInterpolant_lipschitz {d k : ℕ} (f : L1Vec d → L1Vec k)
    (p : Equiv.Perm (Fin d)) (L : ℝ≥0)
    (hf : LipschitzOnWith L f (unitCube d)) :
    LipschitzWith L (kuhnInterpolant f p) := by
  have hcolumns : ∀ j : Fin d,
      ‖f (kuhnVertex p j.succ) - f (kuhnVertex p j.castSucc)‖ ≤ L := by
    intro j
    have h := hf.dist_le_mul _ (kuhnVertex_mem_unitCube p j.succ)
      _ (kuhnVertex_mem_unitCube p j.castSucc)
    rw [kuhnVertex_dist_succ, mul_one, dist_eq_norm] at h
    exact h
  have hLip := orderedSimplexInterpolant_lipschitz
    (fun i => f (kuhnVertex p i)) L hcolumns
  apply LipschitzWith.of_dist_le_mul
  intro x z
  have h := hLip.dist_le_mul
    (WithLp.toLp 1 (fun j => x.ofLp (p j)))
    (WithLp.toLp 1 (fun j => z.ofLp (p j)))
  rw [(structural_permute_isometry p).dist_eq] at h
  exact h

-- @node: kuhnInterpolant_mem_convexHull
/-- If [the input belongs to the unit cube](hyp:hx) and [its coordinates
are nonincreasing in the permutation's order](hyp:horder), then [the Kuhn
interpolated output belongs to the convex hull of the function's image of
the unit cube](goal). -/
lemma kuhnInterpolant_mem_convexHull {d k : ℕ} (f : L1Vec d → L1Vec k)
    (p : Equiv.Perm (Fin d)) {x : L1Vec d} (hx : x ∈ unitCube d)
    (horder : Antitone (fun j => x.ofLp (p j))) :
    kuhnInterpolant f p x ∈ convexHull ℝ (f '' unitCube d) := by
  apply orderedSimplexInterpolant_mem_convex _ _ (fun j => hx (p j)) horder
    (convex_convexHull _ _)
  intro i
  exact subset_convexHull ℝ _ ⟨kuhnVertex p i, kuhnVertex_mem_unitCube p i, rfl⟩

-- @node: kuhnInterpolant_error
/-- For [a nonnegative constant L](hyp:L), if [the function is Lipschitz
with constant L on the unit cube](hyp:hf), [the input belongs to the unit
cube](hyp:hx), and [its coordinates are nonincreasing in the permutation's
order](hyp:horder), then [the one-norm error of the Kuhn interpolant at
that input is at most L times the input dimension](goal). -/
lemma kuhnInterpolant_error {d k : ℕ} (f : L1Vec d → L1Vec k)
    (p : Equiv.Perm (Fin d)) (L : ℝ≥0)
    (hf : LipschitzOnWith L f (unitCube d))
    {x : L1Vec d} (hx : x ∈ unitCube d)
    (horder : Antitone (fun j => x.ofLp (p j))) :
    ‖kuhnInterpolant f p x - f x‖ ≤ L * d := by
  apply orderedSimplexInterpolant_error _ _ (fun j => hx (p j)) horder
  intro i
  rw [← dist_eq_norm]
  exact (hf.dist_le_mul _ (kuhnVertex_mem_unitCube p i) _ hx).trans
    (mul_le_mul_of_nonneg_left (structural_unitCube_dist_le
      (kuhnVertex_mem_unitCube p i) hx) L.coe_nonneg)

-- @node: structuralCellMap
/-- Given [a cell's base point](hyp:base), [a nonnegative side length](hyp:h),
and [an input vector](hyp:x), the [cell map](goal) scales the vector by the
side length and adds the base point. -/
def structuralCellMap {d : ℕ} (base : L1Vec d) (h : ℝ≥0) (x : L1Vec d) : L1Vec d :=
  base + (h : ℝ) • x

-- @node: structuralCell
/-- For [a base point](hyp:base) and [a nonnegative side length](hyp:h), the
[physical cell](goal) is the image of the unit cube under scaling by that
side length and translation by that base point. -/
def structuralCell {d : ℕ} (base : L1Vec d) (h : ℝ≥0) : Set (L1Vec d) :=
  structuralCellMap base h '' unitCube d

-- @node: structuralCellNormalize
/-- Given [a cell's base point](hyp:base), [a nonnegative side length](hyp:h),
and [a point in the ambient space](hyp:x), the [normalized cell
coordinates](goal) are the point minus the base point, scaled by the
reciprocal of the side length, with reciprocal zero taken to be zero. -/
def structuralCellNormalize {d : ℕ} (base : L1Vec d) (h : ℝ≥0)
    (x : L1Vec d) : L1Vec d := (h : ℝ)⁻¹ • (x - base)

-- @node: structuralCellMap_lipschitz
/-- For [a nonnegative side length h](hyp:h), [the cell map is Lipschitz
with constant h in the one-norm distance](goal). -/
lemma structuralCellMap_lipschitz {d : ℕ} (base : L1Vec d) (h : ℝ≥0) :
    LipschitzWith h (structuralCellMap base h) := by
  apply LipschitzWith.of_dist_le_mul
  intro x z
  simp only [structuralCellMap, dist_eq_norm, add_sub_add_left_eq_sub,
    ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg h.coe_nonneg, le_refl]

-- @node: structuralCellNormalize_lipschitz
/-- For [a nonnegative side length h](hyp:h), [cell normalization is
Lipschitz with constant equal to the reciprocal of h in the one-norm
distance](goal), with reciprocal zero taken to be zero. -/
lemma structuralCellNormalize_lipschitz {d : ℕ} (base : L1Vec d) (h : ℝ≥0) :
    LipschitzWith h⁻¹ (structuralCellNormalize base h) := by
  apply LipschitzWith.of_dist_le_mul
  intro x z
  simp only [structuralCellNormalize, dist_eq_norm, ← smul_sub,
    sub_sub_sub_cancel_right, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr h.coe_nonneg), NNReal.coe_inv, le_refl]

-- @node: structuralCellNormalize_map
/-- For [a nonnegative cell side length h](hyp:h), if [h is strictly
positive](hyp:hh), then [mapping any vector into the physical cell's
coordinates and then normalizing returns the original vector](goal). -/
lemma structuralCellNormalize_map {d : ℕ} (base : L1Vec d) (h : ℝ≥0)
    (hh : 0 < h) (x : L1Vec d) :
    structuralCellNormalize base h (structuralCellMap base h x) = x := by
  simp only [structuralCellNormalize, structuralCellMap, add_sub_cancel_left, smul_smul]
  rw [inv_mul_cancel₀ (show (h : ℝ) ≠ 0 from ne_of_gt hh), one_smul]

-- @node: structuralCellMap_lipschitzOn_comp
/-- For [a nonnegative cell side length h and a nonnegative constant L](hyp:h,L),
if [the function is Lipschitz with constant L on the physical cell](hyp:hf),
then [composing it with the cell map gives a function that is Lipschitz
with constant L times h on the unit cube, using one-norm distances](goal). -/
lemma structuralCellMap_lipschitzOn_comp {d k : ℕ} (base : L1Vec d) (h L : ℝ≥0)
    (f : L1Vec d → L1Vec k) (hf : LipschitzOnWith L f (structuralCell base h)) :
    LipschitzOnWith (L * h) (f ∘ structuralCellMap base h) (unitCube d) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx z hz
  calc
    dist (f (structuralCellMap base h x)) (f (structuralCellMap base h z)) ≤
        L * dist (structuralCellMap base h x) (structuralCellMap base h z) :=
      hf.dist_le_mul _ ⟨x, hx, rfl⟩ _ ⟨z, hz, rfl⟩
    _ ≤ L * (h * dist x z) := mul_le_mul_of_nonneg_left
      ((structuralCellMap_lipschitz base h).dist_le_mul x z) L.coe_nonneg
    _ = (L * h : ℝ≥0) * dist x z := by simp only [NNReal.coe_mul]; ring

-- @node: cellKuhnInterpolant
/-- Given [a structural function](hyp:f), [a cell base point](hyp:base),
[a nonnegative cell side length](hyp:h), [a permutation specifying the
simplex coordinate order](hyp:p), and [an input point](hyp:x), the
[physical-cell Kuhn interpolant](goal) evaluates the Kuhn interpolant of
the function composed with the cell map at the normalized input point. -/
def cellKuhnInterpolant {d k : ℕ} (f : L1Vec d → L1Vec k)
    (base : L1Vec d) (h : ℝ≥0) (p : Equiv.Perm (Fin d)) (x : L1Vec d) : L1Vec k :=
  kuhnInterpolant (f ∘ structuralCellMap base h) p (structuralCellNormalize base h x)

-- @node: cellKuhnInterpolant_lipschitz
/-- For [a nonnegative cell side length h and a nonnegative constant L](hyp:h,L),
if [h is strictly positive](hyp:hh) and [the function is Lipschitz with
constant L on the physical cell](hyp:hf), then [the physical-cell Kuhn
interpolant is Lipschitz with constant L on the entire input space, using
one-norm distances](goal). -/
lemma cellKuhnInterpolant_lipschitz {d k : ℕ} (f : L1Vec d → L1Vec k)
    (base : L1Vec d) (h L : ℝ≥0) (hh : 0 < h) (p : Equiv.Perm (Fin d))
    (hf : LipschitzOnWith L f (structuralCell base h)) :
    LipschitzWith L (cellKuhnInterpolant f base h p) := by
  have hlocal := kuhnInterpolant_lipschitz (f ∘ structuralCellMap base h) p (L * h)
    (structuralCellMap_lipschitzOn_comp base h L f hf)
  have hcomp := hlocal.comp (structuralCellNormalize_lipschitz base h)
  change LipschitzWith L
    (kuhnInterpolant (f ∘ structuralCellMap base h) p ∘ structuralCellNormalize base h)
  simpa only [mul_assoc, mul_inv_cancel₀ (ne_of_gt hh), mul_one] using hcomp

-- @node: cellKuhnInterpolant_error
/-- For [a nonnegative cell side length h and a nonnegative constant L](hyp:h,L),
if [h is strictly positive](hyp:hh), [the function is Lipschitz with
constant L on the physical cell](hyp:hf), [the normalized input z belongs
to the unit cube](hyp:hz), and [its coordinates are nonincreasing in the
permutation's order](hyp:horder), then [the one-norm interpolation error
at the physical point corresponding to z is at most L times the input
dimension times h](goal). -/
lemma cellKuhnInterpolant_error {d k : ℕ} (f : L1Vec d → L1Vec k)
    (base : L1Vec d) (h L : ℝ≥0) (hh : 0 < h) (p : Equiv.Perm (Fin d))
    (hf : LipschitzOnWith L f (structuralCell base h))
    {z : L1Vec d} (hz : z ∈ unitCube d)
    (horder : Antitone (fun j => z.ofLp (p j))) :
    ‖cellKuhnInterpolant f base h p (structuralCellMap base h z) -
      f (structuralCellMap base h z)‖ ≤ L * d * h := by
  rw [cellKuhnInterpolant, structuralCellNormalize_map base h hh]
  have he := kuhnInterpolant_error (f ∘ structuralCellMap base h) p (L * h)
    (structuralCellMap_lipschitzOn_comp base h L f hf) hz horder
  convert he using 1 <;> simp only [NNReal.coe_mul, Function.comp_apply]
  ring

-- @node: cellKuhnInterpolant_mem_convex
/-- For [a nonnegative cell side length h](hyp:h), if [h is strictly
positive](hyp:hh), [the normalized input z belongs to the unit cube](hyp:hz),
[its coordinates are nonincreasing in the permutation's order](hyp:horder),
[the output constraint set is convex](hyp:hS), and [every function value
on the physical cell belongs to that set](hyp:hf), then [the interpolated
output at the physical point corresponding to z belongs to the same set](goal). -/
lemma cellKuhnInterpolant_mem_convex {d k : ℕ} (f : L1Vec d → L1Vec k)
    (base : L1Vec d) (h : ℝ≥0) (hh : 0 < h) (p : Equiv.Perm (Fin d))
    {z : L1Vec d} (hz : z ∈ unitCube d)
    (horder : Antitone (fun j => z.ofLp (p j)))
    {S : Set (L1Vec k)} (hS : Convex ℝ S)
    (hf : ∀ x ∈ structuralCell base h, f x ∈ S) :
    cellKuhnInterpolant f base h p (structuralCellMap base h z) ∈ S := by
  rw [cellKuhnInterpolant, structuralCellNormalize_map base h hh]
  apply orderedSimplexInterpolant_mem_convex _ _ (fun j => hz (p j)) horder hS
  intro i
  exact hf _ ⟨kuhnVertex p i, kuhnVertex_mem_unitCube p i, rfl⟩

-- @node: cellKuhnInterpolant_mem_convexHull
/-- For [a nonnegative cell side length h](hyp:h), if [h is strictly
positive](hyp:hh), [the normalized input z belongs to the unit cube](hyp:hz),
and [its coordinates are nonincreasing in the permutation's order](hyp:horder),
then [the interpolated output at the physical point corresponding to z
belongs to the convex hull of the function's image of the physical cell](goal). -/
lemma cellKuhnInterpolant_mem_convexHull {d k : ℕ} (f : L1Vec d → L1Vec k)
    (base : L1Vec d) (h : ℝ≥0) (hh : 0 < h) (p : Equiv.Perm (Fin d))
    {z : L1Vec d} (hz : z ∈ unitCube d)
    (horder : Antitone (fun j => z.ofLp (p j))) :
    cellKuhnInterpolant f base h p (structuralCellMap base h z) ∈
      convexHull ℝ (f '' structuralCell base h) := by
  exact cellKuhnInterpolant_mem_convex f base h hh p hz horder (convex_convexHull _ _)
    (fun x hx => subset_convexHull ℝ _ ⟨x, hx, rfl⟩)

-- @node: cellKuhnInterpolant_norm_le
/-- For [a nonnegative cell side length h](hyp:h), if [h is strictly
positive](hyp:hh), [the normalized input z belongs to the unit cube](hyp:hz),
[its coordinates are nonincreasing in the permutation's order](hyp:horder),
and [the one-norm of every function value on the physical cell is at most
K](hyp:hf), then [the one-norm of the interpolated output at the physical
point corresponding to z is also at most K](goal). -/
lemma cellKuhnInterpolant_norm_le {d k : ℕ} (f : L1Vec d → L1Vec k)
    (base : L1Vec d) (h : ℝ≥0) (hh : 0 < h) (p : Equiv.Perm (Fin d))
    {z : L1Vec d} (hz : z ∈ unitCube d)
    (horder : Antitone (fun j => z.ofLp (p j))) (K : ℝ)
    (hf : ∀ x ∈ structuralCell base h, ‖f x‖ ≤ K) :
    ‖cellKuhnInterpolant f base h p (structuralCellMap base h z)‖ ≤ K := by
  rw [cellKuhnInterpolant, structuralCellNormalize_map base h hh]
  apply orderedSimplexInterpolant_norm_le _ _ (fun j => hz (p j)) horder K
  intro i
  exact hf _ ⟨kuhnVertex p i, kuhnVertex_mem_unitCube p i, rfl⟩

-- @node: cellKuhnInterpolant_simplex
/-- For [a nonnegative cell side length h](hyp:h), if [h is strictly
positive](hyp:hh), [the normalized input z belongs to the unit cube](hyp:hz),
[its coordinates are nonincreasing in the permutation's order](hyp:horder),
[every function value on the physical cell has nonnegative coordinates](hyp:hf0),
and [those coordinates sum to one at every point of the physical cell](hyp:hf1),
then [the interpolated output at the physical point corresponding to z
has nonnegative coordinates that sum to one](goal). -/
lemma cellKuhnInterpolant_simplex {d k : ℕ} (f : L1Vec d → L1Vec k)
    (base : L1Vec d) (h : ℝ≥0) (hh : 0 < h) (p : Equiv.Perm (Fin d))
    {z : L1Vec d} (hz : z ∈ unitCube d)
    (horder : Antitone (fun j => z.ofLp (p j)))
    (hf0 : ∀ x ∈ structuralCell base h, ∀ j, 0 ≤ (f x).ofLp j)
    (hf1 : ∀ x ∈ structuralCell base h, ∑ j, (f x).ofLp j = 1) :
    (∀ j, 0 ≤ (cellKuhnInterpolant f base h p (structuralCellMap base h z)).ofLp j) ∧
      ∑ j, (cellKuhnInterpolant f base h p (structuralCellMap base h z)).ofLp j = 1 := by
  rw [cellKuhnInterpolant, structuralCellNormalize_map base h hh]
  apply orderedSimplexInterpolant_simplex _ _ (fun j => hz (p j)) horder
  · intro i j
    exact hf0 _ ⟨kuhnVertex p i, kuhnVertex_mem_unitCube p i, rfl⟩ j
  · intro i
    exact hf1 _ ⟨kuhnVertex p i, kuhnVertex_mem_unitCube p i, rfl⟩

-- @node: cellKuhnInterpolant_vertex
/-- For [a nonnegative cell side length h](hyp:h), if [h is strictly
positive](hyp:hh), then [the physical-cell Kuhn interpolant agrees exactly
with the original function at every vertex of the simplex specified by
the permutation](goal). -/
lemma cellKuhnInterpolant_vertex {d k : ℕ} (f : L1Vec d → L1Vec k)
    (base : L1Vec d) (h : ℝ≥0) (hh : 0 < h) (p : Equiv.Perm (Fin d))
    (i : Fin (d + 1)) :
    cellKuhnInterpolant f base h p (structuralCellMap base h (kuhnVertex p i)) =
      f (structuralCellMap base h (kuhnVertex p i)) := by
  rw [cellKuhnInterpolant, structuralCellNormalize_map base h hh, kuhnInterpolant_vertex]
  rfl

end
end Papers.TbsNeuralCausalPi

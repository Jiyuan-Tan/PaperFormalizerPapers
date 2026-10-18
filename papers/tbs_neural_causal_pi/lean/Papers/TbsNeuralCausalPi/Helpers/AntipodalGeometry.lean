module
public import Papers.TbsNeuralCausalPi.Helpers.AntipodalFaces
public import Mathlib.Analysis.Convex.Combination
/-! # Geometric coordinates of signed faces

The no-opposite face condition isolates each vertex coefficient in its own coordinate.
These identities provide the affine independence and barycentric coordinates of
the cross-polytope faces used in the local antipodal sphere model.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi.Antipodal
open Finset

-- @node: noOpposite_fst_injOn
/-- If [a finite set of signed vertices contains no opposite pair](hyp:hs), then
[no two distinct vertices in the set share a coordinate index](goal). -/
lemma noOpposite_fst_injOn {n : ℕ} {s : Finset (SignedVertex n)}
    (hs : NoOpposite s) : Set.InjOn Prod.fst (s : Set (SignedVertex n)) := by
  rintro ⟨i, b⟩ hb ⟨j, c⟩ hc hij
  change i = j at hij
  subst j
  by_cases hbc : b = c
  · exact congrArg (fun t => (i, t)) hbc
  · have hneg : signedAntipode (i, b) = (i, c) := by
      cases b <;> cases c <;> simp_all [signedAntipode]
    exact False.elim (hs _ hb (hneg.symm ▸ hc))

-- @node: signedFace_sum_coordinate
/-- If [a finite set of signed vertices contains no opposite pair](hyp:hs) and
[a vertex belongs to that set](hyp:hv), then, for [real weights on signed vertices](hyp:w),
[the weighted vector sum at that vertex's coordinate equals its weight times its sign](goal). -/
lemma signedFace_sum_coordinate {n : ℕ} {s : Finset (SignedVertex n)}
    (hs : NoOpposite s) (w : SignedVertex n → ℝ) {v : SignedVertex n} (hv : v ∈ s) :
    (∑ u ∈ s, w u • signedVertexVector u) v.1 =
      w v * (if v.2 then 1 else -1) := by
  classical
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single v]
  · simp [signedVertexVector]
  · intro u hu huv
    have hcoord : v.1 ≠ u.1 := fun h => huv ((noOpposite_fst_injOn hs hu hv h.symm))
    simp [signedVertexVector, hcoord]
  · exact fun h => (h hv).elim

-- @node: signedFace_sum_abs_coordinate
/-- If [a finite set of signed vertices contains no opposite pair](hyp:hs),
[real vertex weights](hyp:w) are [nonnegative on the set](hyp:hw), and
[a vertex belongs to the set](hyp:hv), then [the absolute value of the weighted
vector sum at that vertex's coordinate equals its weight](goal). -/
lemma signedFace_sum_abs_coordinate {n : ℕ} {s : Finset (SignedVertex n)}
    (hs : NoOpposite s) (w : SignedVertex n → ℝ) (hw : ∀ v ∈ s, 0 ≤ w v)
    {v : SignedVertex n} (hv : v ∈ s) :
    |(∑ u ∈ s, w u • signedVertexVector u) v.1| = w v := by
  rw [signedFace_sum_coordinate hs w hv, abs_mul]
  cases v.2 <;> simp [abs_of_nonneg (hw v hv)]

-- @node: signedFace_linearIndependent
/-- If [a finite set of signed vertices contains no opposite pair](hyp:hs), then
[their coordinate vectors are linearly independent over the real numbers](goal). -/
lemma signedFace_linearIndependent {n : ℕ} {s : Finset (SignedVertex n)}
    (hs : NoOpposite s) :
    LinearIndependent ℝ (fun v : s => signedVertexVector v.val) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro w hw v
  have he := congrFun hw v.val.1
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at he
  have hsum : (∑ u : s, w u * signedVertexVector u.val v.val.1) =
      w v * (if v.val.2 then 1 else -1) := by
    rw [Finset.sum_eq_single v]
    · simp [signedVertexVector]
    · intro u _ huv
      have hcoord : v.val.1 ≠ u.val.1 := by
        intro h
        exact huv (Subtype.ext (noOpposite_fst_injOn hs u.property v.property h.symm))
      simp [signedVertexVector, hcoord]
    · simp
  rw [hsum] at he
  cases hb : v.val.2 <;> simpa [hb] using he

-- @node: signedFace_affineIndependent
/-- If [a finite set of signed vertices contains no opposite pair](hyp:hs), then
[their coordinate vectors are affinely independent over the real numbers](goal). -/
lemma signedFace_affineIndependent {n : ℕ} {s : Finset (SignedVertex n)}
    (hs : NoOpposite s) :
    AffineIndependent ℝ (fun v : s => signedVertexVector v.val) :=
  (signedFace_linearIndependent hs).affineIndependent

-- @node: signedVertexVector_sign_nonpos_of_ne
/-- If [two signed vertices are distinct](hyp:huv), then [the first vertex's vector,
evaluated at the second vertex's coordinate and multiplied by the second vertex's sign,
is nonpositive](goal). -/
lemma signedVertexVector_sign_nonpos_of_ne {n : ℕ} {u v : SignedVertex n}
    (huv : u ≠ v) : signedVertexVector u v.1 * (if v.2 then 1 else -1) ≤ 0 := by
  rcases u with ⟨i, b⟩
  rcases v with ⟨j, c⟩
  by_cases hij : j = i
  · subst j
    cases b <;> cases c <;> simp_all [signedVertexVector]
  · simp [signedVertexVector, hij]

-- @node: signedFace_sum_sign_nonpos_of_notMem
/-- For [real weights on signed vertices](hyp:w) that are [nonnegative on a finite
vertex set](hyp:hw), if [a vertex lies outside the set](hyp:hv), then [the weighted
vector sum at that vertex's coordinate, multiplied by its sign, is nonpositive](goal). -/
lemma signedFace_sum_sign_nonpos_of_notMem {n : ℕ} {s : Finset (SignedVertex n)}
    (w : SignedVertex n → ℝ) (hw : ∀ u ∈ s, 0 ≤ w u)
    {v : SignedVertex n} (hv : v ∉ s) :
    (∑ u ∈ s, w u • signedVertexVector u) v.1 * (if v.2 then 1 else -1) ≤ 0 := by
  classical
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  apply Finset.sum_nonpos
  intro u hu
  rw [mul_assoc]
  exact mul_nonpos_of_nonneg_of_nonpos (hw u hu)
    (signedVertexVector_sign_nonpos_of_ne (fun h => hv (h ▸ hu)))

-- @node: signedFace_sum_coefficient_zero
/-- Suppose [the first of two finite vertex sets contains no opposite pair](hyp:hs),
with [two systems of real vertex weights](hyp:w,z) that are [nonnegative on the
first set](hyp:hw) and [nonnegative on the second set, respectively](hyp:hz).
If [their weighted vector sums agree](hyp:heq) and [a vertex belongs to the first
set](hyp:hv) but [not the second](hyp:hvt), then [its weight in the first sum is zero](goal). -/
lemma signedFace_sum_coefficient_zero {n : ℕ} {s t : Finset (SignedVertex n)}
    (hs : NoOpposite s) (w z : SignedVertex n → ℝ)
    (hw : ∀ u ∈ s, 0 ≤ w u) (hz : ∀ u ∈ t, 0 ≤ z u)
    (heq : ∑ u ∈ s, w u • signedVertexVector u = ∑ u ∈ t, z u • signedVertexVector u)
    {v : SignedVertex n} (hv : v ∈ s) (hvt : v ∉ t) : w v = 0 := by
  have hnonpos := signedFace_sum_sign_nonpos_of_notMem z hz hvt
  rw [← heq, signedFace_sum_coordinate hs w hv] at hnonpos
  have hle : w v ≤ 0 := by
    cases hb : v.2 <;> simpa [hb] using hnonpos
  exact le_antisymm hle (hw v hv)

-- @node: signedFace_mem_convexHull_iff
/-- For [a finite set of signed vertices](hyp:s) and [a real coordinate vector](hyp:x),
[the vector lies in the convex hull of the corresponding vertex vectors if and only
if it is their weighted sum with weights nonnegative on the set and summing to one](goal). -/
lemma signedFace_mem_convexHull_iff {n : ℕ} (s : Finset (SignedVertex n))
    (x : Fin n → ℝ) :
    x ∈ convexHull ℝ (s.image signedVertexVector : Set (Fin n → ℝ)) ↔
      ∃ w : SignedVertex n → ℝ, (∀ v ∈ s, 0 ≤ w v) ∧
        ∑ v ∈ s, w v = 1 ∧ ∑ v ∈ s, w v • signedVertexVector v = x := by
  classical
  have hinj := signedVertexVector_injective (n := n)
  constructor
  · intro hx
    obtain ⟨w, hw, hw1, hwx⟩ := Finset.mem_convexHull'.mp hx
    refine ⟨fun v => w (signedVertexVector v), fun v hv => hw _ (mem_image_of_mem _ hv), ?_, ?_⟩
    · simpa only [Finset.sum_image hinj.injOn] using hw1
    · simpa only [Finset.sum_image hinj.injOn] using hwx
  · rintro ⟨w, hw, hw1, hwx⟩
    let z := Function.extend signedVertexVector w (fun _ => 0)
    have hz : ∀ v, z (signedVertexVector v) = w v := hinj.extend_apply _ _
    apply Finset.mem_convexHull'.mpr
    refine ⟨z, ?_, ?_, ?_⟩
    · intro y hy
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
      rw [hz]
      exact hw v hv
    · simpa only [Finset.sum_image hinj.injOn, hz] using hw1
    · simpa only [Finset.sum_image hinj.injOn, hz] using hwx

-- @node: signedFace_convexHull_inter
/-- If [the first of two finite sets of signed vertices contains no opposite pair](hyp:hs),
then [the intersection of their vector convex hulls equals the convex hull of the
vectors of their common vertices](goal). -/
lemma signedFace_convexHull_inter {n : ℕ} {s t : Finset (SignedVertex n)}
    (hs : NoOpposite s) :
    convexHull ℝ (s.image signedVertexVector : Set (Fin n → ℝ)) ∩
      convexHull ℝ (t.image signedVertexVector : Set (Fin n → ℝ)) =
    convexHull ℝ ((s ∩ t).image signedVertexVector : Set (Fin n → ℝ)) := by
  classical
  apply Set.Subset.antisymm
  · rintro x ⟨hxs, hxt⟩
    obtain ⟨w, hw, hw1, hwx⟩ := (signedFace_mem_convexHull_iff s x).mp hxs
    obtain ⟨z, hz, _, hzx⟩ := (signedFace_mem_convexHull_iff t x).mp hxt
    have hzero : ∀ v ∈ s, v ∉ t → w v = 0 := by
      intro v hv hvt
      exact signedFace_sum_coefficient_zero hs w z hw hz (hwx.trans hzx.symm) hv hvt
    apply (signedFace_mem_convexHull_iff (s ∩ t) x).mpr
    refine ⟨w, fun v hv => hw v (mem_inter.mp hv).1, ?_, ?_⟩
    · calc
        ∑ v ∈ s ∩ t, w v = ∑ v ∈ s, w v := by
          apply Finset.sum_subset Finset.inter_subset_left
          intro v hv hvt
          exact hzero v hv (fun ht => hvt (mem_inter.mpr ⟨hv, ht⟩))
        _ = 1 := hw1
    · calc
        ∑ v ∈ s ∩ t, w v • signedVertexVector v = ∑ v ∈ s, w v • signedVertexVector v := by
          apply Finset.sum_subset Finset.inter_subset_left
          intro v hv hvt
          rw [hzero v hv (fun ht => hvt (mem_inter.mpr ⟨hv, ht⟩)), zero_smul]
        _ = x := hwx
  · exact Set.subset_inter
      (convexHull_mono (by
        intro y hy
        obtain ⟨v, hv, rfl⟩ := mem_image.mp hy
        exact mem_image_of_mem _ (mem_inter.mp hv).1))
      (convexHull_mono (by
        intro y hy
        obtain ⟨v, hv, rfl⟩ := mem_image.mp hy
        exact mem_image_of_mem _ (mem_inter.mp hv).2))

-- @node: signedFace_image_affineIndependent
/-- If [a finite set of signed vertices contains no opposite pair](hyp:hs), then
[the distinct points obtained as their coordinate vectors are affinely independent
over the real numbers](goal). -/
lemma signedFace_image_affineIndependent {n : ℕ} {s : Finset (SignedVertex n)}
    (hs : NoOpposite s) :
    AffineIndependent ℝ (fun v : (s.image signedVertexVector : Set (Fin n → ℝ)) => v.val) := by
  classical
  have h := (signedFace_linearIndependent hs)
  have hi : LinearIndepOn ℝ signedVertexVector (s : Set (SignedVertex n)) := h
  have him := (linearIndepOn_iff_image signedVertexVector_injective.injOn).mp hi
  have him' : LinearIndependent ℝ
      (fun v : (s.image signedVertexVector : Set (Fin n → ℝ)) => v.val) := by
    rw [Finset.coe_image]
    exact him
  exact him'.affineIndependent

-- @node: signedGeometricComplex
/-- In [n coordinate directions](hyp:n), the [geometric signed-face complex](goal)
has as its faces the coordinate-vector images of nonempty finite sets of signed
vertices containing no opposite pair. -/
noncomputable def signedGeometricComplex (n : ℕ) : Geometry.SimplicialComplex ℝ (Fin n → ℝ) := by
  classical
  refine { (signedFaceComplex n).map signedVertexVector with
    indep := ?_, inter_subset_convexHull := ?_ }
  · rintro s ⟨t, ht, rfl⟩
    exact signedFace_image_affineIndependent ht.2
  · rintro s t ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    rw [signedFace_convexHull_inter ha.2]
    exact convexHull_mono (by
      rw [← Finset.coe_inter, ← Finset.image_inter _ _ signedVertexVector_injective])

-- @node: signedGeometricComplex_faces_finite
/-- [The geometric signed-face complex has finitely many faces](goal). -/
lemma signedGeometricComplex_faces_finite (n : ℕ) :
    (signedGeometricComplex n).faces.Finite := by
  classical
  exact (signedFaceComplex_faces_finite n).image _

-- @node: signedFace_sum_abs
/-- If [a finite set of signed vertices contains no opposite pair](hyp:hs) and
[real vertex weights](hyp:w) are [nonnegative on that set](hyp:hw), then [the sum
of absolute coordinates of their weighted vector sum equals the sum of the weights](goal). -/
lemma signedFace_sum_abs {n : ℕ} {s : Finset (SignedVertex n)}
    (hs : NoOpposite s) (w : SignedVertex n → ℝ) (hw : ∀ v ∈ s, 0 ≤ w v) :
    ∑ i, |(∑ v ∈ s, w v • signedVertexVector v) i| = ∑ v ∈ s, w v := by
  classical
  calc
    ∑ i, |(∑ v ∈ s, w v • signedVertexVector v) i| =
        ∑ i ∈ s.image Prod.fst, |(∑ v ∈ s, w v • signedVertexVector v) i| := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      have hzero : (∑ v ∈ s, w v • signedVertexVector v) i = 0 := by
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        apply Finset.sum_eq_zero
        intro v hv
        have hne : i ≠ v.1 := fun h => hi (h ▸ mem_image_of_mem Prod.fst hv)
        simp [signedVertexVector, hne]
      simp [hzero]
    _ = ∑ v ∈ s, |(∑ u ∈ s, w u • signedVertexVector u) v.1| :=
      Finset.sum_image (noOpposite_fst_injOn hs)
    _ = ∑ v ∈ s, w v := Finset.sum_congr rfl (fun v hv =>
      signedFace_sum_abs_coordinate hs w hw hv)

-- @node: signedGeometricComplex_sum_abs_eq_one
/-- If [a vector belongs to the space of the geometric signed-face complex](hyp:hx),
then [the sum of its absolute coordinates is one](goal). -/
lemma signedGeometricComplex_sum_abs_eq_one {n : ℕ} {x : Fin n → ℝ}
    (hx : x ∈ (signedGeometricComplex n).space) : ∑ i, |x i| = 1 := by
  classical
  obtain ⟨_, ⟨s, hs, rfl⟩, hx⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
  obtain ⟨w, hw, hw1, rfl⟩ := (signedFace_mem_convexHull_iff s x).mp hx
  exact (signedFace_sum_abs hs.2 w hw).trans hw1

-- @node: noOpposite_coordinateFace
/-- For [any choice of a Boolean sign for each coordinate](hyp:b), [the set
containing the chosen signed vertex in every coordinate has no opposite pair](goal). -/
lemma noOpposite_coordinateFace {n : ℕ} (b : Fin n → Bool) :
    NoOpposite (Finset.univ.image (fun i => (i, b i))) := by
  classical
  intro v hv hneg
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hneg
  have hji : j = i := congrArg Prod.fst hj
  subst j
  exact signedAntipode_ne (i, b i) hj.symm

-- @node: signedGeometricComplex_mem_of_sum_abs_eq_one
/-- If [the sum of a vector's absolute coordinates is one](hyp:hx), then [the vector
belongs to the space of the geometric signed-face complex](goal). -/
lemma signedGeometricComplex_mem_of_sum_abs_eq_one {n : ℕ} {x : Fin n → ℝ}
    (hx : ∑ i, |x i| = 1) : x ∈ (signedGeometricComplex n).space := by
  classical
  let b : Fin n → Bool := fun i => decide (0 ≤ x i)
  let s : Finset (SignedVertex n) := Finset.univ.image (fun i => (i, b i))
  let w : SignedVertex n → ℝ := fun v => |x v.1|
  have hs : NoOpposite s := noOpposite_coordinateFace b
  have hw : ∀ v ∈ s, 0 ≤ w v := fun _ _ => abs_nonneg _
  have hw1 : ∑ v ∈ s, w v = 1 := by
    calc
      ∑ v ∈ s, w v = ∑ i, |x i| := by
        dsimp [s, w]
        rw [Finset.sum_image]
        intro i _ j _ h
        exact congrArg Prod.fst h
      _ = 1 := hx
  have hsne : s.Nonempty := by
    by_contra he
    have he' : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    simp [he'] at hw1
  have hwx : ∑ v ∈ s, w v • signedVertexVector v = x := by
    funext i
    have hi : (i, b i) ∈ s := Finset.mem_image_of_mem _ (Finset.mem_univ i)
    have he := signedFace_sum_coordinate hs w hi
    change (∑ v ∈ s, w v • signedVertexVector v) i = x i
    rw [he]
    change |x i| * (if decide (0 ≤ x i) then 1 else -1) = x i
    by_cases h : 0 ≤ x i
    · simp [h, abs_of_nonneg h]
    · simp [h, abs_of_neg (lt_of_not_ge h)]
  apply Geometry.SimplicialComplex.mem_space_iff.mpr
  refine ⟨s.image signedVertexVector, ⟨s, ⟨hsne, hs⟩, rfl⟩, ?_⟩
  exact (signedFace_mem_convexHull_iff s x).mpr ⟨w, hw, hw1, hwx⟩

-- @node: signedGeometricComplex_space
/-- [The space of the geometric signed-face complex consists exactly of the real
coordinate vectors whose absolute coordinates sum to one](goal). -/
lemma signedGeometricComplex_space (n : ℕ) :
    (signedGeometricComplex n).space = {x : Fin n → ℝ | ∑ i, |x i| = 1} := by
  ext x
  exact ⟨signedGeometricComplex_sum_abs_eq_one, signedGeometricComplex_mem_of_sum_abs_eq_one⟩

-- @node: signedGeometricComplex_neg_face
/-- If [a finite set of vectors is a face of the geometric signed-face complex](hyp:hs),
then [negating all of its vectors gives another face](goal). -/
lemma signedGeometricComplex_neg_face {n : ℕ} {s : Finset (Fin n → ℝ)}
    (hs : s ∈ (signedGeometricComplex n).faces) :
    s.image Neg.neg ∈ (signedGeometricComplex n).faces := by
  classical
  obtain ⟨t, ht, rfl⟩ := hs
  refine ⟨t.image signedAntipode, signedFaceComplex_antipode ht, ?_⟩
  simp only [Finset.image_image, Function.comp_def, signedVertexVector_antipode]

-- @node: signedGeometricComplex_neg_mem
/-- If [a vector belongs to the space of the geometric signed-face complex](hyp:hx),
then [its negative also belongs to that space](goal). -/
lemma signedGeometricComplex_neg_mem {n : ℕ} {x : Fin n → ℝ}
    (hx : x ∈ (signedGeometricComplex n).space) :
    -x ∈ (signedGeometricComplex n).space := by
  apply signedGeometricComplex_mem_of_sum_abs_eq_one
  simpa only [Pi.neg_apply, abs_neg] using signedGeometricComplex_sum_abs_eq_one hx

-- @node: signedGeometricComplex_ne_zero
/-- If [a vector belongs to the space of the geometric signed-face complex](hyp:hx),
then [it is nonzero](goal). -/
lemma signedGeometricComplex_ne_zero {n : ℕ} {x : Fin n → ℝ}
    (hx : x ∈ (signedGeometricComplex n).space) : x ≠ 0 := by
  intro hz
  have hsum := signedGeometricComplex_sum_abs_eq_one hx
  simp [hz] at hsum

-- @node: signedGeometricComplex_ne_antipode
/-- If [a vector belongs to the space of the geometric signed-face complex](hyp:hx),
then [it differs from its negative](goal). -/
lemma signedGeometricComplex_ne_antipode {n : ℕ} {x : Fin n → ℝ}
    (hx : x ∈ (signedGeometricComplex n).space) : x ≠ -x := by
  intro heq
  apply signedGeometricComplex_ne_zero hx
  funext i
  have hi := congrFun heq i
  change x i = -x i at hi
  change x i = 0
  linarith

end Papers.TbsNeuralCausalPi.Antipodal

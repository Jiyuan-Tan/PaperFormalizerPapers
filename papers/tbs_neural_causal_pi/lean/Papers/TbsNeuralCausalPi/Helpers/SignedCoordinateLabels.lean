module
public import Papers.TbsNeuralCausalPi.Helpers.SignedChainObstruction
public import Toolkit.Foundations.Topology.PiecewiseAffineApproximation
/-! # Signed coordinate labels for zero-free continuous maps

Choose a coordinate of largest absolute value, with ties resolved using only
the absolute values. Negation then reverses the sign of the label. Uniform
continuity and subdivision mesh decay exclude opposite labels on fine faces.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi.Antipodal
noncomputable section
open Toolkit.Foundations.Topology

-- @node: largestCoordinate
/-- Given [a positive number of coordinates](hyp:hd) and [a real value at
each coordinate](hyp:a), the [selected largest coordinate](goal) is an index
where those values attain their maximum. -/
def largestCoordinate {d : ℕ} (hd : 0 < d) (a : Fin d → ℝ) : Fin d :=
  (Finset.exists_max_image Finset.univ a ⟨⟨0, hd⟩, Finset.mem_univ _⟩).choose

-- @node: largestCoordinate_le
/-- With [a positive number of coordinates](hyp:hd), [the value at any
coordinate is at most the value at the selected largest coordinate](goal). -/
lemma largestCoordinate_le {d : ℕ} (hd : 0 < d) (a : Fin d → ℝ) (i : Fin d) :
    a i ≤ a (largestCoordinate hd a) :=
  (Finset.exists_max_image Finset.univ a ⟨⟨0, hd⟩, Finset.mem_univ _⟩).choose_spec.2
    i (Finset.mem_univ _)

-- @node: signedCoordinateLabel
/-- Given [a positive dimension](hyp:hd) and [a real vector](hyp:x), its
[signed coordinate label](goal) is formed by [selecting a coordinate of
largest absolute value](step:1) and [pairing its index with whether its value
is strictly positive](step:2). -/
def signedCoordinateLabel {d : ℕ} (hd : 0 < d) (x : Fin d → ℝ) : SignedVertex d :=
  let i := largestCoordinate hd (fun j => |x j|)
  (i, decide (0 < x i))

-- @node: largestCoordinate_abs_eq_norm
/-- In [a positive dimension](hyp:hd), [the absolute value at the selected
largest absolute coordinate equals the vector's maximum-coordinate norm](goal). -/
lemma largestCoordinate_abs_eq_norm {d : ℕ} (hd : 0 < d) (x : Fin d → ℝ) :
    |x (largestCoordinate hd (fun j => |x j|))| = ‖x‖ := by
  apply le_antisymm
  · simpa only [Real.norm_eq_abs] using norm_le_pi_norm x
      (largestCoordinate hd (fun j => |x j|))
  · apply (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr
    intro i
    simpa only [Real.norm_eq_abs] using largestCoordinate_le hd (fun j => |x j|) i

-- @node: signedCoordinateLabel_neg
/-- In [a positive dimension](hyp:hd), if [a vector is nonzero](hyp:hx),
then [negating it reverses its signed coordinate label](goal). -/
lemma signedCoordinateLabel_neg {d : ℕ} (hd : 0 < d) (x : Fin d → ℝ) (hx : x ≠ 0) :
    signedCoordinateLabel hd (-x) = signedAntipode (signedCoordinateLabel hd x) := by
  have hn : x (largestCoordinate hd (fun j => |x j|)) ≠ 0 := by
    intro h
    have he := largestCoordinate_abs_eq_norm hd x
    rw [h, abs_zero] at he
    exact hx (norm_eq_zero.mp he.symm)
  simp only [signedCoordinateLabel, Pi.neg_apply, abs_neg, signedAntipode]
  congr 1
  by_cases hp : 0 < x (largestCoordinate hd (fun j => |x j|))
  · simp [hp, not_lt.mpr (le_of_lt hp)]
  · have hm : x (largestCoordinate hd (fun j => |x j|)) < 0 := lt_of_le_of_ne
      (le_of_not_gt hp) hn
    simp [hp, hm]

-- @node: norm_le_dist_of_opposite_coordinate_labels
/-- In [a positive dimension](hyp:hd), if [two vectors have opposite signed
coordinate labels](hyp:h), then [their distance in the maximum-coordinate
norm is at least the norm of the first vector](goal).

This estimate requires no continuity of the label selection. -/
lemma norm_le_dist_of_opposite_coordinate_labels {d : ℕ} (hd : 0 < d)
    (x y : Fin d → ℝ)
    (h : signedCoordinateLabel hd y = signedAntipode (signedCoordinateLabel hd x)) :
    ‖x‖ ≤ dist x y := by
  let i := largestCoordinate hd (fun j => |x j|)
  let j := largestCoordinate hd (fun j => |y j|)
  have hij : j = i := congrArg Prod.fst h
  have hs : decide (0 < y i) = !decide (0 < x i) := by
    have hh := congrArg Prod.snd h
    change decide (0 < y j) = !decide (0 < x i) at hh
    rw [hij] at hh
    exact hh
  have hcoord : |x i| ≤ |x i - y i| := by
    by_cases hx : 0 < x i
    · have hy : y i ≤ 0 := by
        have : ¬ (0 < y i) := by simpa [hx] using hs
        exact le_of_not_gt this
      rw [abs_of_pos hx, abs_of_nonneg (by linarith)]
      linarith
    · have hy : 0 < y i := by simpa [hx] using hs
      rw [abs_of_nonpos (le_of_not_gt hx), abs_of_nonpos (by linarith)]
      linarith
  calc
    ‖x‖ = |x i| := (largestCoordinate_abs_eq_norm hd x).symm
    _ ≤ |x i - y i| := hcoord
    _ ≤ dist x y := by
      simpa only [dist_eq_norm, Pi.sub_apply, Real.norm_eq_abs] using
        norm_le_pi_norm (x - y) i

-- @node: coordinateLabelOn
/-- Given [a simplicial complex](hyp:Q), [a positive target dimension](hyp:hd),
[a vector-valued map on its underlying space](hyp:f), and [an ambient point](hyp:x),
the [extended coordinate label](goal) is the signed coordinate label of the
map's value if the point belongs to the complex, and the label of the zero
vector otherwise. -/
def coordinateLabelOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : Geometry.SimplicialComplex ℝ E) {d : ℕ} (hd : 0 < d)
    (f : Q.space → (Fin d → ℝ)) (x : E) : SignedVertex d := by
  classical
  exact signedCoordinateLabel hd (if hx : x ∈ Q.space then f ⟨x, hx⟩ else 0)

-- @node: coordinateLabelOn_mem
/-- For [a positive target dimension](hyp:hd), if [a point belongs to the
underlying space of the complex](hyp:hx), then [its extended coordinate label
equals the signed coordinate label of the map's value there](goal). -/
lemma coordinateLabelOn_mem {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : Geometry.SimplicialComplex ℝ E) {d : ℕ} (hd : 0 < d)
    (f : Q.space → (Fin d → ℝ)) {x : E} (hx : x ∈ Q.space) :
    coordinateLabelOn Q hd f x = signedCoordinateLabel hd (f ⟨x, hx⟩) := by
  classical
  simp only [coordinateLabelOn, dif_pos hx]

-- @node: exists_subdivision_no_opposite_coordinate_labels
/-- If [a simplicial complex has finitely many faces](hyp:hQ), [the target
dimension is positive](hyp:hd), and a map on its underlying space is
[continuous](hyp:hf) and [nowhere zero](hyp:hz), then [some iterated
barycentric subdivision has no opposite coordinate labels on any face](goal). -/
lemma exists_subdivision_no_opposite_coordinate_labels
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {Q : Geometry.SimplicialComplex ℝ E} (hQ : Q.faces.Finite)
    {d : ℕ} (hd : 0 < d) (f : Q.space → (Fin d → ℝ))
    (hf : Continuous f) (hz : ∀ x, f x ≠ 0) :
    ∃ r, ∀ s ∈ (sdIterate Q r).faces, NoOpposite (s.image (coordinateLabelOn Q hd f)) := by
  classical
  let : CompactSpace Q.space := isCompact_iff_compactSpace.mp (isCompact_space hQ)
  obtain ⟨ε, hε, hlower⟩ := isCompact_univ.exists_forall_le' hf.norm.continuousOn
    (fun x _ => norm_pos_iff.mpr (hz x))
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hf) ε hε
  obtain ⟨r, hr⟩ := ((mesh_sdIterate_tendsto_zero hQ).eventually
    (gt_mem_nhds hδ)).exists
  refine ⟨r, ?_⟩
  intro s hs v hv hneg
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨y, hy, hylabel⟩ := Finset.mem_image.mp hneg
  have hxQ : x ∈ Q.space := by
    rw [← sdIterate_space Q r]
    exact (sdIterate Q r).subset_space hs hx
  have hyQ : y ∈ Q.space := by
    rw [← sdIterate_space Q r]
    exact (sdIterate Q r).subset_space hs hy
  rw [coordinateLabelOn_mem Q hd f hyQ, coordinateLabelOn_mem Q hd f hxQ] at hylabel
  have hsep := norm_le_dist_of_opposite_coordinate_labels hd (f ⟨x, hxQ⟩)
    (f ⟨y, hyQ⟩) hylabel
  have hxy : dist x y < δ := by
    have hdia := Metric.dist_le_diam_of_mem
      (isBounded_convexHull.mpr s.finite_toSet.isBounded)
      (subset_convexHull ℝ (s : Set E) hx) (subset_convexHull ℝ (s : Set E) hy)
    have hm : Metric.diam (convexHull ℝ (s : Set E)) ≤ mesh (sdIterate Q r) :=
      le_csSup (((sdIterate_finite hQ r).image _).insert 0).bddAbove
        (Set.mem_insert_of_mem _ ⟨s, hs, rfl⟩)
    exact (hdia.trans hm).trans_lt hr
  exact (not_lt_of_ge ((hlower ⟨x, hxQ⟩ (Set.mem_univ _)).trans hsep))
    (hclose hxy)

-- @node: signedSphere_odd_exists_zero
/-- For [a positive dimension](hyp:hd), if a map from the signed sphere of
that dimension into the real vector space of the same dimension is
[continuous](hyp:hf) and [sends antipodal points to negative vectors](hyp:hodd),
then [it vanishes at some point](goal).

The finite labeling obstruction supplies the parity argument through its
chain ladder. -/
lemma signedSphere_odd_exists_zero {d : ℕ} (hd : 0 < d)
    (f : (signedGeometricComplex (d + 1)).space → (Fin d → ℝ))
    (hf : Continuous f)
    (hodd : ∀ x, f ⟨-x.val, signedGeometricComplex_neg_mem x.property⟩ = -f x) :
    ∃ x, f x = 0 := by
  classical
  by_contra hz
  have hnonzero : ∀ x, f x ≠ 0 := by simpa only [not_exists] using hz
  obtain ⟨r, hr⟩ := exists_subdivision_no_opposite_coordinate_labels
    (signedGeometricComplex_faces_finite (d + 1)) hd f hf hnonzero
  apply signedSubdivision_no_antipodal_labeling
    (coordinateLabelOn (signedGeometricComplex (d + 1)) hd f) r ?_ hr
  intro s hs x hx
  have hxQ : x ∈ (signedGeometricComplex (d + 1)).space := by
    rw [← sdIterate_space (signedGeometricComplex (d + 1)) r]
    exact (sdIterate _ r).subset_space hs hx
  rw [coordinateLabelOn_mem _ hd f hxQ,
    coordinateLabelOn_mem _ hd f (signedGeometricComplex_neg_mem hxQ), hodd ⟨x, hxQ⟩]
  exact signedCoordinateLabel_neg hd (f ⟨x, hxQ⟩) (hnonzero _)

end
end Papers.TbsNeuralCausalPi.Antipodal

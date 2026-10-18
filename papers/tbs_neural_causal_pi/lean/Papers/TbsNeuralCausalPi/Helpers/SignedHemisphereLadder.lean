module
public import Papers.TbsNeuralCausalPi.Helpers.SimplicialModTwo
/-! # Concrete hemisphere chain ladder on the signed sphere

The ladder successively cones antipodal sums to the next positive coordinate
vertex. Every term is supported on actual nonempty no-opposite signed faces.
Its successive boundaries are the antipodal sums of the preceding terms.
This constructs the ladder on the original sphere; subdivision transport and
the chain map induced by a zero-free PL map are still required.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi.Antipodal
noncomputable section
open Finset
attribute [local instance] Classical.propDecidable

-- @node: signedFaceNorm
/-- The [antipodal sum operator](goal) adds a signed-face chain to its antipodal
image, with coefficients computed modulo two. -/
def signedFaceNorm {n : ℕ} :
    ModTwoFaceChain (SignedVertex n) →ₗ[ZMod 2] ModTwoFaceChain (SignedVertex n) :=
  LinearMap.id + modTwoFaceMap signedAntipode

-- @node: signedFaceNorm_apply
/-- For any signed-face chain, [its antipodal sum is the chain plus its
antipodal image](goal), with coefficients modulo two. -/
lemma signedFaceNorm_apply {n : ℕ} (c : ModTwoFaceChain (SignedVertex n)) :
    signedFaceNorm c = c + modTwoFaceMap signedAntipode c := rfl

-- @node: signedFaceNorm_sq
/-- For any signed-face chain, [applying the antipodal sum operator twice
gives the zero chain](goal). -/
lemma signedFaceNorm_sq {n : ℕ} (c : ModTwoFaceChain (SignedVertex n)) :
    signedFaceNorm (signedFaceNorm c) = 0 := by
  have hinv : modTwoFaceMap signedAntipode (modTwoFaceMap signedAntipode c) = c := by
    rw [modTwoFaceMap_comp]
    have he : (signedAntipode ∘ signedAntipode : SignedVertex n → SignedVertex n) = id :=
      funext signedAntipode_involutive
    rw [he, modTwoFaceMap_id]
  simp only [signedFaceNorm_apply, map_add, hinv]
  calc
    (c + modTwoFaceMap signedAntipode c) + (modTwoFaceMap signedAntipode c + c) =
        (c + c) + (modTwoFaceMap signedAntipode c + modTwoFaceMap signedAntipode c) := by
          abel
    _ = 0 := by rw [ZModModule.add_self, ZModModule.add_self, add_zero]

-- @node: signedFaceNorm_boundary
/-- For any signed-face chain, [the boundary of its antipodal sum equals the
antipodal sum of its boundary](goal). -/
lemma signedFaceNorm_boundary {n : ℕ} (c : ModTwoFaceChain (SignedVertex n)) :
    modTwoBoundary (signedFaceNorm c) = signedFaceNorm (modTwoBoundary c) := by
  simp only [signedFaceNorm_apply, map_add,
    modTwoBoundary_faceMap signedAntipode signedAntipode_injective]

-- @node: signedFaceNorm_augmentation
/-- For any signed-face chain, [the augmentation of its antipodal sum is
zero](goal). -/
lemma signedFaceNorm_augmentation {n : ℕ} (c : ModTwoFaceChain (SignedVertex n)) :
    modTwoAugmentation (signedFaceNorm c) = 0 := by
  rw [signedFaceNorm_apply, map_add,
    modTwoAugmentation_faceMap signedAntipode signedAntipode_injective, ZModModule.add_self]

-- @node: signedFaceNorm_empty
/-- For any coefficient modulo two, [the antipodal sum of the chain supported
only on the empty face with that coefficient is zero](goal). -/
@[simp] lemma signedFaceNorm_empty {n : ℕ} (r : ZMod 2) :
    signedFaceNorm (Finsupp.single (∅ : Finset (SignedVertex n)) r) = 0 := by
  simp only [signedFaceNorm_apply, modTwoFaceMap_single, image_empty]
  exact ZModModule.add_self _

-- @node: signedFaceNorm_support
/-- If [a face has a nonzero coefficient in the antipodal sum of a chain](hyp:hs),
then [it is either a face with a nonzero coefficient in the original chain or
the antipodal image of such a face](goal). -/
lemma signedFaceNorm_support {n : ℕ} (c : ModTwoFaceChain (SignedVertex n))
    {s : Finset (SignedVertex n)} (hs : s ∈ (signedFaceNorm c).support) :
    ∃ t ∈ c.support, s = t ∨ s = t.image signedAntipode := by
  rw [signedFaceNorm_apply] at hs
  rcases mem_union.mp (Finsupp.support_add hs) with h | h
  · exact ⟨s, h, Or.inl rfl⟩
  · obtain ⟨t, ht, he⟩ := modTwoFaceMap_support signedAntipode c h
    exact ⟨t, ht, Or.inr he⟩

-- @node: noOpposite_insert_fresh_coordinate
/-- If [a set of signed vertices contains no antipodal pair](hyp:hs) and
[none of its vertices uses a given coordinate](hyp:hfresh), then [adjoining
either sign of that coordinate still leaves no antipodal pair](goal). -/
lemma noOpposite_insert_fresh_coordinate {n : ℕ} {s : Finset (SignedVertex n)}
    (hs : NoOpposite s) (i : Fin n) (b : Bool)
    (hfresh : ∀ v ∈ s, v.1 ≠ i) : NoOpposite (insert (i, b) s) := by
  intro v hv hneg
  rcases mem_insert.mp hv with rfl | hv
  · rcases mem_insert.mp hneg with he | he
    · exact signedAntipode_ne (i, b) he
    · exact hfresh _ he rfl
  · rcases mem_insert.mp hneg with he | he
    · exact hfresh v hv (congrArg Prod.fst he)
    · exact hs v hv he

-- @node: signedHemisphereChain
/-- For [a number of coordinates](hyp:n), the [hemisphere chain ladder](goal)
[starts at the positive vertex of coordinate zero, or at zero if there are no
coordinates](step:1), and [forms each subsequent chain by coning the preceding
chain's antipodal sum to the next positive coordinate vertex, returning zero
when that coordinate is out of range](step:2). -/
def signedHemisphereChain (n : ℕ) : ℕ → ModTwoFaceChain (SignedVertex n)
  | 0 => if h : 0 < n then Finsupp.single {(⟨0, h⟩, true)} 1 else 0
  | k + 1 => if h : k + 1 < n then
      modTwoCone (⟨k + 1, h⟩, true) (signedFaceNorm (signedHemisphereChain n k)) else 0

-- @node: signedHemisphereChain_norm_cycle
/-- At every level of the hemisphere ladder, [the antipodal sum of the chain
has zero boundary](goal). -/
lemma signedHemisphereChain_norm_cycle (n k : ℕ) :
    modTwoBoundary (signedFaceNorm (signedHemisphereChain n k)) = 0 := by
  induction k with
  | zero =>
      by_cases hn : 0 < n
      · rw [signedHemisphereChain, dif_pos hn, signedFaceNorm_boundary,
          modTwoBoundary_vertex, signedFaceNorm_empty]
      · simp [signedHemisphereChain, hn]
  | succ k ih =>
      by_cases hk : k + 1 < n
      · rw [signedHemisphereChain, dif_pos hk, signedFaceNorm_boundary,
          modTwoBoundary_cone_cycle _ _ ih, signedFaceNorm_sq]
      · simp [signedHemisphereChain, hk]

-- @node: signedHemisphereChain_boundary
/-- If [the next level is below the number of coordinates](hyp:hk), then
[the boundary of that hemisphere chain is the antipodal sum of the preceding
hemisphere chain](goal). -/
lemma signedHemisphereChain_boundary (n k : ℕ) (hk : k + 1 < n) :
    modTwoBoundary (signedHemisphereChain n (k + 1)) =
      signedFaceNorm (signedHemisphereChain n k) := by
  rw [signedHemisphereChain, dif_pos hk]
  exact modTwoBoundary_cone_cycle _ _ (signedHemisphereChain_norm_cycle n k)

-- @node: signedHemisphereChain_bottom_augmentation
/-- If [there is at least one coordinate](hyp:hn), then [the bottom hemisphere
chain has augmentation one](goal). -/
lemma signedHemisphereChain_bottom_augmentation {n : ℕ} (hn : 0 < n) :
    modTwoAugmentation (signedHemisphereChain n 0) = 1 := by
  simp [signedHemisphereChain, hn]

-- @node: signedHemisphereChain_support
/-- At level k of the hemisphere ladder, [every face with a nonzero coefficient
contains no antipodal pair, has exactly k plus one vertices, and uses only
coordinates with index at most k](goal). -/
lemma signedHemisphereChain_support (n k : ℕ) :
    ∀ s ∈ (signedHemisphereChain n k).support,
      NoOpposite s ∧ s.card = k + 1 ∧ ∀ v ∈ s, v.1.val ≤ k := by
  induction k with
  | zero =>
      intro s hs
      by_cases hn : 0 < n
      · rw [signedHemisphereChain, dif_pos hn] at hs
        obtain ⟨rfl, _⟩ := (Finsupp.mem_support_single _ _ _).mp hs
        refine ⟨noOpposite_singleton _, by simp, ?_⟩
        intro v hv
        rw [mem_singleton.mp hv]
      · simp [signedHemisphereChain, hn] at hs
  | succ k ih =>
      intro s hs
      by_cases hk : k + 1 < n
      · rw [signedHemisphereChain, dif_pos hk] at hs
        obtain ⟨t, ht, hv, rfl⟩ := modTwoCone_support _ _ hs
        obtain ⟨u, hu, he⟩ := signedFaceNorm_support _ ht
        have htu : NoOpposite t ∧ t.card = k + 1 ∧ ∀ v ∈ t, v.1.val ≤ k := by
          rcases ih u hu with ⟨hno, hcard, hcoord⟩
          rcases he with rfl | rfl
          · exact ⟨hno, hcard, hcoord⟩
          · refine ⟨noOpposite_image_antipode hno, ?_, ?_⟩
            · rw [card_image_of_injective _ signedAntipode_injective, hcard]
            · intro v hv
              obtain ⟨w, hw, rfl⟩ := mem_image.mp hv
              exact hcoord w hw
        refine ⟨noOpposite_insert_fresh_coordinate htu.1 _ _ ?_, ?_, ?_⟩
        · intro v hv heq
          have hval := congrArg Fin.val heq
          have hle := htu.2.2 v hv
          simp only at hval
          omega
        · rw [card_insert_of_notMem hv, htu.2.1]
        · intro v hv'
          rcases mem_insert.mp hv' with rfl | hv'
          · exact le_refl _
          · exact (htu.2.2 v hv').trans (Nat.le_succ _)
      · simp [signedHemisphereChain, hk] at hs

-- @node: signedHemisphereChain_faces
/-- If [a face has a nonzero coefficient in a hemisphere chain](hyp:hs), then
[it belongs to the signed-sphere complex](goal). -/
lemma signedHemisphereChain_faces (n k : ℕ) {s : Finset (SignedVertex n)}
    (hs : s ∈ (signedHemisphereChain n k).support) :
    s ∈ (signedFaceComplex n).faces := by
  obtain ⟨hno, hc, _⟩ := signedHemisphereChain_support n k s hs
  exact ⟨card_pos.mp (by omega), hno⟩

-- @node: signedHemisphereChain_top_support
/-- If [there is at least one coordinate](hyp:hn) and [a face has a nonzero
coefficient in the top hemisphere chain](hyp:hs), then [that face is a full
signed facet, obtained by choosing one sign for each coordinate](goal). -/
lemma signedHemisphereChain_top_support {n : ℕ} (hn : 0 < n)
    {s : Finset (SignedVertex n)} (hs : s ∈ (signedHemisphereChain n (n - 1)).support) :
    ∃ σ : Fin n → Bool, s = signedFacet σ := by
  obtain ⟨hno, hc, _⟩ := signedHemisphereChain_support n (n - 1) s hs
  exact noOpposite_top_face_iff.mp ⟨hno, by omega⟩

-- @node: signedGeometricHemisphereChain
/-- For [a number of coordinates](hyp:n) and [a ladder level](hyp:k), the
[geometric hemisphere chain](goal) is the corresponding signed hemisphere
chain with each signed vertex replaced by its real coordinate vector. -/
def signedGeometricHemisphereChain (n k : ℕ) : ModTwoFaceChain (Fin n → ℝ) :=
  modTwoFaceMap signedVertexVector (signedHemisphereChain n k)

-- @node: signedVertexVector_chainNorm
/-- For any signed-face chain, [mapping its antipodal sum to coordinate vectors
gives the mapped chain plus its image under vector negation](goal). -/
lemma signedVertexVector_chainNorm {n : ℕ} (c : ModTwoFaceChain (SignedVertex n)) :
    modTwoFaceMap signedVertexVector (signedFaceNorm c) =
      modTwoFaceMap signedVertexVector c +
        modTwoFaceMap (fun x : Fin n → ℝ => -x) (modTwoFaceMap signedVertexVector c) := by
  rw [signedFaceNorm_apply, map_add, modTwoFaceMap_comp, modTwoFaceMap_comp]
  congr 1
  congr 1
  exact congrArg modTwoFaceMap (funext signedVertexVector_antipode)

-- @node: signedGeometricHemisphereChain_boundary
/-- If [the next level is below the number of coordinates](hyp:hk), then
[the boundary of that geometric hemisphere chain equals the preceding
geometric hemisphere chain plus its image under vector negation](goal). -/
lemma signedGeometricHemisphereChain_boundary (n k : ℕ) (hk : k + 1 < n) :
    modTwoBoundary (signedGeometricHemisphereChain n (k + 1)) =
      signedGeometricHemisphereChain n k +
        modTwoFaceMap (fun x : Fin n → ℝ => -x) (signedGeometricHemisphereChain n k) := by
  unfold signedGeometricHemisphereChain
  rw [modTwoBoundary_faceMap signedVertexVector signedVertexVector_injective,
    signedHemisphereChain_boundary n k hk, signedVertexVector_chainNorm]

-- @node: signedGeometricHemisphereChain_bottom_augmentation
/-- If [there is at least one coordinate](hyp:hn), then [the bottom geometric
hemisphere chain has augmentation one](goal). -/
lemma signedGeometricHemisphereChain_bottom_augmentation {n : ℕ} (hn : 0 < n) :
    modTwoAugmentation (signedGeometricHemisphereChain n 0) = 1 := by
  rw [signedGeometricHemisphereChain,
    modTwoAugmentation_faceMap signedVertexVector signedVertexVector_injective,
    signedHemisphereChain_bottom_augmentation hn]

-- @node: signedGeometricHemisphereChain_support
/-- If [a set of vectors has a nonzero coefficient in the geometric hemisphere
chain at level k](hyp:hs), then [it is a face of the geometric signed-sphere
complex and has exactly k plus one vertices](goal). -/
lemma signedGeometricHemisphereChain_support (n k : ℕ)
    {s : Finset (Fin n → ℝ)} (hs : s ∈ (signedGeometricHemisphereChain n k).support) :
    s ∈ (signedGeometricComplex n).faces ∧ s.card = k + 1 := by
  obtain ⟨t, ht, rfl⟩ := modTwoFaceMap_support signedVertexVector _ hs
  constructor
  · exact ⟨t, signedHemisphereChain_faces n k ht, rfl⟩
  · rw [card_image_of_injective _ signedVertexVector_injective]
    exact (signedHemisphereChain_support n k t ht).2.1

end
end Papers.TbsNeuralCausalPi.Antipodal

module
public import Papers.TbsNeuralCausalPi.Helpers.SignedHemisphereLadder
/-! # Barycentric subdivision of mod-two chains

A face subdivides by coning the subdivision of its boundary to its own
barycentric vertex. Vertices at this stage are nonempty original faces;
the geometric barycenter map is a separate realization step.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi.Antipodal
noncomputable section
open Finset

-- @node: modTwoSubdivisionFace
/-- For [a finite face](hyp:s), its [barycentric subdivision with coefficients
modulo two](goal) is [the empty face with coefficient one when the original face
is empty](step:1); otherwise it is [the cone, with apex the original face, over
the sum of the recursively subdivided faces obtained by deleting one vertex](step:2). -/
def modTwoSubdivisionFace {V : Type*} [DecidableEq V]
    (s : Finset V) : ModTwoFaceChain (Finset V) :=
  if _h : s = ∅ then Finsupp.single ∅ 1 else
    modTwoCone s (∑ v : s, modTwoSubdivisionFace (s.erase v.val))
termination_by s.card
decreasing_by exact card_erase_lt_of_mem v.property

-- @node: modTwoSubdivisionFace_empty
/-- [Subdividing the empty face gives the empty face with coefficient one](goal). -/
@[simp] lemma modTwoSubdivisionFace_empty {V : Type*} [DecidableEq V] :
    modTwoSubdivisionFace (∅ : Finset V) = Finsupp.single ∅ 1 := by
  rw [modTwoSubdivisionFace, dif_pos rfl]

-- @node: modTwoSubdivisionFace_nonempty
/-- If [a face is nonempty](hyp:hs), then [its subdivision is the cone with apex
that face over the sum of the subdivisions of all faces obtained by deleting
one vertex](goal). -/
lemma modTwoSubdivisionFace_nonempty {V : Type*} [DecidableEq V]
    {s : Finset V} (hs : s.Nonempty) :
    modTwoSubdivisionFace s = modTwoCone s (∑ v ∈ s, modTwoSubdivisionFace (s.erase v)) := by
  rw [modTwoSubdivisionFace, dif_neg hs.ne_empty]
  congr 1
  exact Finset.sum_coe_sort s (fun v => modTwoSubdivisionFace (s.erase v))

-- @node: modTwoSubdivision
/-- The [barycentric subdivision operator on chains with coefficients modulo
two](goal) extends the subdivision of individual faces by linearity, using finite
sets of original vertices as the new vertices. -/
def modTwoSubdivision {V : Type*} [DecidableEq V] :
    ModTwoFaceChain V →ₗ[ZMod 2] ModTwoFaceChain (Finset V) :=
  Finsupp.linearCombination (ZMod 2) modTwoSubdivisionFace

-- @node: modTwoSubdivision_single
/-- [Subdividing a chain consisting of one face with a given coefficient gives
that coefficient times the subdivision of the face](goal). -/
@[simp] lemma modTwoSubdivision_single {V : Type*} [DecidableEq V]
    (s : Finset V) (r : ZMod 2) :
    modTwoSubdivision (Finsupp.single s r) = r • modTwoSubdivisionFace s := by
  simp [modTwoSubdivision]

-- @node: modTwoSubdivisionFace_boundary
/-- [The boundary of a subdivided face is the sum of the subdivisions of its
faces obtained by deleting one vertex](goal). -/
lemma modTwoSubdivisionFace_boundary {V : Type*} [DecidableEq V] (s : Finset V) :
    modTwoBoundary (modTwoSubdivisionFace s) =
      ∑ v ∈ s, modTwoSubdivisionFace (s.erase v) := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases hs : s = ∅
    · subst s
      simp
    · rw [modTwoSubdivisionFace_nonempty (nonempty_iff_ne_empty.mpr hs)]
      apply modTwoBoundary_cone_cycle
      rw [map_sum]
      have he : (∑ v ∈ s, modTwoBoundary (modTwoSubdivisionFace (s.erase v))) =
          ∑ v ∈ s, ∑ w ∈ s.erase v, modTwoSubdivisionFace ((s.erase v).erase w) := by
        apply sum_congr rfl
        intro v hv
        exact ih _ (erase_ssubset hv)
      rw [he]
      exact modTwo_sum_erase_symmetric s
        (fun v w => modTwoSubdivisionFace ((s.erase v).erase w))
        (fun v w => by rw [erase_right_comm])

-- @node: modTwoBoundary_subdivision
/-- [Taking the boundary of a subdivided chain gives the same chain as
subdividing its boundary](goal). -/
lemma modTwoBoundary_subdivision {V : Type*} [DecidableEq V] (c : ModTwoFaceChain V) :
    modTwoBoundary (modTwoSubdivision c) = modTwoSubdivision (modTwoBoundary c) := by
  have h : (modTwoBoundary (V := Finset V)).comp modTwoSubdivision =
      (modTwoSubdivision (V := V)).comp modTwoBoundary := by
    apply Finsupp.lhom_ext
    intro s r
    simp only [LinearMap.comp_apply, modTwoSubdivision_single, map_smul,
      modTwoSubdivisionFace_boundary, modTwoBoundary_single, map_sum,
      modTwoSubdivision_single, one_smul]
  exact LinearMap.congr_fun h c

-- @node: modTwoSubdivisionFace_support
/-- If [a simplex occurs with nonzero coefficient in the subdivision of a face](hyp:ht),
then [it has as many vertices as the original face, all its vertices are nonempty
subfaces of the original face, and any two of these subfaces are comparable by
inclusion](goal). -/
lemma modTwoSubdivisionFace_support {V : Type*} [DecidableEq V] (s : Finset V)
    {t : Finset (Finset V)} (ht : t ∈ (modTwoSubdivisionFace s).support) :
    t.card = s.card ∧ (∀ u ∈ t, u.Nonempty ∧ u ⊆ s) ∧
      ∀ u ∈ t, ∀ w ∈ t, u ⊆ w ∨ w ⊆ u := by
  induction s using Finset.strongInductionOn generalizing t with
  | _ s ih =>
    by_cases hs : s = ∅
    · subst s
      rw [modTwoSubdivisionFace_empty] at ht
      obtain ⟨rfl, _⟩ := (Finsupp.mem_support_single _ _ _).mp ht
      simp
    · rw [modTwoSubdivisionFace_nonempty (nonempty_iff_ne_empty.mpr hs)] at ht
      obtain ⟨t, htb, hst, rfl⟩ := modTwoCone_support _ _ ht
      obtain ⟨v, hv, hvt⟩ := Finsupp.mem_support_finsetSum t htb
      obtain ⟨hcard, hsub, hchain⟩ := ih _ (erase_ssubset hv) hvt
      have hsubs : ∀ u ∈ t, u.Nonempty ∧ u ⊆ s := fun u hu =>
        ⟨(hsub u hu).1, (hsub u hu).2.trans (erase_subset _ _)⟩
      refine ⟨?_, ?_, ?_⟩
      · rw [card_insert_of_notMem hst, hcard, card_erase_of_mem hv]
        have := card_pos.mpr ⟨v, hv⟩
        omega
      · intro u hu
        rcases mem_insert.mp hu with rfl | hu
        · exact ⟨nonempty_iff_ne_empty.mpr hs, Subset.rfl⟩
        · exact hsubs u hu
      · intro u hu w hw
        rcases mem_insert.mp hu with rfl | hu
        · rcases mem_insert.mp hw with rfl | hw
          · exact Or.inl Subset.rfl
          · exact Or.inr (hsubs w hw).2
        · rcases mem_insert.mp hw with hw | hw
          · exact Or.inl (hw ▸ (hsubs u hu).2)
          · exact hchain u hu w hw

-- @node: modTwoSubdivisionFace_vertex
/-- [The subdivision of a one-vertex face consists of a single vertex, labeled
by that original face, with coefficient one](goal). -/
@[simp] lemma modTwoSubdivisionFace_vertex {V : Type*} [DecidableEq V] (v : V) :
    modTwoSubdivisionFace {v} = Finsupp.single {{v}} 1 := by
  rw [modTwoSubdivisionFace_nonempty (singleton_nonempty v)]
  simp

-- @node: modTwoAugmentation_eq_zero_of_support
/-- If [no face occurring with nonzero coefficient in a chain has exactly one
vertex](hyp:hc), then [the chain's augmentation is zero](goal). -/
lemma modTwoAugmentation_eq_zero_of_support {V : Type*}
    (c : ModTwoFaceChain V) (hc : ∀ s ∈ c.support, s.card ≠ 1) :
    modTwoAugmentation c = 0 := by
  classical
  conv_lhs => rw [← c.sum_single]
  simp only [Finsupp.sum, map_sum, modTwoAugmentation_single]
  exact sum_eq_zero (fun s hs => if_neg (hc s hs))

-- @node: modTwoSubdivisionFace_augmentation
/-- [The augmentation of a subdivided face is one when the original face has
exactly one vertex, and zero otherwise](goal). -/
lemma modTwoSubdivisionFace_augmentation {V : Type*} [DecidableEq V] (s : Finset V) :
    modTwoAugmentation (modTwoSubdivisionFace s) = if s.card = 1 then 1 else 0 := by
  by_cases hs : s.card = 1
  · obtain ⟨v, rfl⟩ := card_eq_one.mp hs
    simp
  · rw [if_neg hs]
    apply modTwoAugmentation_eq_zero_of_support
    intro t ht
    rw [(modTwoSubdivisionFace_support s ht).1]
    exact hs

-- @node: modTwoAugmentation_subdivision
/-- [Subdivision preserves the augmentation of a chain](goal). -/
lemma modTwoAugmentation_subdivision {V : Type*} [DecidableEq V] (c : ModTwoFaceChain V) :
    modTwoAugmentation (modTwoSubdivision c) = modTwoAugmentation c := by
  have h : (modTwoAugmentation (V := Finset V)).comp modTwoSubdivision =
      (modTwoAugmentation (V := V)) := by
    apply Finsupp.lhom_ext
    intro s r
    simp only [LinearMap.comp_apply, modTwoSubdivision_single, map_smul,
      modTwoSubdivisionFace_augmentation, modTwoAugmentation_single]
    split_ifs <;> simp
  exact LinearMap.congr_fun h c

-- @node: modTwoSubdivision_homogeneous
/-- If [every face occurring with nonzero coefficient in a chain has the given
number of vertices](hyp:hc) and [a simplex occurs with nonzero coefficient in the
subdivided chain](hyp:ht), then [that simplex has the same given number of vertices](goal). -/
lemma modTwoSubdivision_homogeneous {V : Type*} [DecidableEq V]
    (c : ModTwoFaceChain V) (k : ℕ) (hc : ∀ s ∈ c.support, s.card = k)
    {t : Finset (Finset V)} (ht : t ∈ (modTwoSubdivision c).support) : t.card = k := by
  obtain ⟨s, hs, hst⟩ := modTwoLinearMap_support modTwoSubdivision c ht
  simp only [modTwoSubdivision_single, one_smul] at hst
  exact (modTwoSubdivisionFace_support s hst).1.trans (hc s hs)

-- @node: modTwoFaceMap_cone
/-- If [a relabeling of vertices is injective](hyp:hf), then [relabeling a cone
gives the cone over the relabeled chain with the relabeled apex](goal). -/
lemma modTwoFaceMap_cone {V W : Type*} [DecidableEq V] [DecidableEq W]
    (f : V → W) (hf : Function.Injective f) (v : V) (c : ModTwoFaceChain V) :
    modTwoFaceMap f (modTwoCone v c) = modTwoCone (f v) (modTwoFaceMap f c) := by
  have h : (modTwoFaceMap f).comp (modTwoCone v) =
      (modTwoCone (f v)).comp (modTwoFaceMap f) := by
    apply Finsupp.lhom_ext
    intro s r
    simp only [LinearMap.comp_apply, modTwoCone_single, modTwoFaceMap_single]
    by_cases hv : v ∈ s
    · simp [hv, mem_image_of_mem f hv]
    · have hfv : f v ∉ s.image f := by simpa [hf.eq_iff] using hv
      simp [hv, hfv, image_insert]
  exact LinearMap.congr_fun h c

-- @node: modTwoSubdivisionFace_image
/-- If [a relabeling of vertices is injective](hyp:hf), then [subdividing the
relabeled face gives the same chain as subdividing the original face and relabeling
each new vertex by the image of its corresponding subface](goal). -/
lemma modTwoSubdivisionFace_image {V W : Type*} [DecidableEq V] [DecidableEq W]
    (f : V → W) (hf : Function.Injective f) (s : Finset V) :
    modTwoSubdivisionFace (s.image f) =
      modTwoFaceMap (fun t : Finset V => t.image f) (modTwoSubdivisionFace s) := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases hs : s = ∅
    · subst s
      simp
    · have hs' : s.Nonempty := nonempty_iff_ne_empty.mpr hs
      rw [modTwoSubdivisionFace_nonempty (hs'.image f),
        modTwoSubdivisionFace_nonempty hs', modTwoFaceMap_cone _
          (Finset.image_injective hf)]
      simp only [map_sum]
      rw [sum_image]
      · apply sum_congr rfl
        intro v hv
        rw [← Finset.image_erase hf, ih _ (erase_ssubset hv)]
      · exact fun _ _ _ _ h => hf h

-- @node: modTwoSubdivision_faceMap
/-- If [a relabeling of vertices is injective](hyp:hf), then [subdividing a
relabeled chain gives the same chain as subdividing first and then relabeling each
new vertex by the image of its corresponding face](goal). -/
lemma modTwoSubdivision_faceMap {V W : Type*} [DecidableEq V] [DecidableEq W]
    (f : V → W) (hf : Function.Injective f) (c : ModTwoFaceChain V) :
    modTwoSubdivision (modTwoFaceMap f c) =
      modTwoFaceMap (fun t : Finset V => t.image f) (modTwoSubdivision c) := by
  have h : (modTwoSubdivision (V := W)).comp (modTwoFaceMap f) =
      (modTwoFaceMap (fun t : Finset V => t.image f)).comp modTwoSubdivision := by
    apply Finsupp.lhom_ext
    intro s r
    simp only [LinearMap.comp_apply, modTwoFaceMap_single, modTwoSubdivision_single,
      map_smul, modTwoSubdivisionFace_image f hf]
  exact LinearMap.congr_fun h c

-- @node: modTwoSubdivision_ladder_step
/-- If [a vertex map is injective](hyp:ha) and [the boundary of the second chain
is the first chain plus its image under that map](hyp:hstep), then [the boundary
of the subdivided second chain is the subdivided first chain plus its image under
the induced map sending each face to its image](goal). -/
lemma modTwoSubdivision_ladder_step {V : Type*} [DecidableEq V]
    (a : V → V) (ha : Function.Injective a) (c c' : ModTwoFaceChain V)
    (hstep : modTwoBoundary c' = c + modTwoFaceMap a c) :
    modTwoBoundary (modTwoSubdivision c') = modTwoSubdivision c +
      modTwoFaceMap (fun s : Finset V => s.image a) (modTwoSubdivision c) := by
  rw [modTwoBoundary_subdivision, hstep, map_add, modTwoSubdivision_faceMap a ha]

-- @node: signedHemisphereChain_subdivision_boundary
/-- If [the next hemisphere index is less than the number of signed coordinate
directions](hyp:hk), then [the boundary of the subdivided next hemisphere chain is
the subdivided current hemisphere chain plus its image under the map taking each
face to its antipodal image](goal). -/
lemma signedHemisphereChain_subdivision_boundary (n k : ℕ) (hk : k + 1 < n) :
    modTwoBoundary (modTwoSubdivision (signedHemisphereChain n (k + 1))) =
      modTwoSubdivision (signedHemisphereChain n k) +
        modTwoFaceMap (fun s : Finset (SignedVertex n) => s.image signedAntipode)
          (modTwoSubdivision (signedHemisphereChain n k)) := by
  apply modTwoSubdivision_ladder_step signedAntipode signedAntipode_injective
  exact signedHemisphereChain_boundary n k hk

-- @node: signedHemisphereChain_subdivision_bottom
/-- If [there is at least one signed coordinate direction](hyp:hn), then [the
subdivided bottom hemisphere chain has augmentation one](goal). -/
lemma signedHemisphereChain_subdivision_bottom {n : ℕ} (hn : 0 < n) :
    modTwoAugmentation (modTwoSubdivision (signedHemisphereChain n 0)) = 1 := by
  rw [modTwoAugmentation_subdivision, signedHemisphereChain_bottom_augmentation hn]

end
end Papers.TbsNeuralCausalPi.Antipodal

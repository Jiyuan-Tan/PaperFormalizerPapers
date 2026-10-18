module
public import Papers.TbsNeuralCausalPi.Helpers.NormalizedModTwoMap
/-! # The finite signed-target chain obstruction

Discard the augmented empty face to obtain the ordinary boundary on the
nonempty signed faces of the target. The antipodal action is free on this finite basis,
so the chain-ladder parity theorem applies to this actual target complex.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi.Antipodal
noncomputable section
open Finset

-- @node: signedChainSubmodule
/-- For [a number of signed coordinate axes](hyp:n), the [signed-face chain
space](goal) consists of finite sums, with coefficients modulo two, supported
on nonempty faces containing no pair of opposite signed vertices. -/
def signedChainSubmodule (n : ℕ) : Submodule (ZMod 2) (ModTwoFaceChain (SignedVertex n)) where
  carrier := {c | ∀ s, s ∉ (signedFaceComplex n).faces → c s = 0}
  zero_mem' := by simp
  add_mem' := by intro c b hc hb s hs; simp [hc s hs, hb s hs]
  smul_mem' := by intro r c hc s hs; simp [hc s hs]

-- @node: signedChain_mem_face
/-- If [a face has a nonzero coefficient in a signed-face chain](hyp:hs),
then [it is a nonempty face containing no opposite signed vertices](goal). -/
lemma signedChain_mem_face {n : ℕ} (c : signedChainSubmodule n)
    {s : Finset (SignedVertex n)} (hs : s ∈ c.val.support) :
    s ∈ (signedFaceComplex n).faces := by
  by_contra hn
  exact (Finsupp.mem_support_iff.mp hs) (c.property s hn)

-- @node: signedChain_empty
/-- [The coefficient of the empty face in any signed-face chain is zero](goal). -/
@[simp] lemma signedChain_empty {n : ℕ} (c : signedChainSubmodule n) : c.val ∅ = 0 :=
  c.property ∅ (by simp [signedFaceComplex])

-- @node: signedChainBoundary
/-- For [a number of signed coordinate axes](hyp:n), the [ordinary boundary
operator](goal) takes the augmented boundary of a signed-face chain and deletes
its empty-face coefficient. -/
def signedChainBoundary (n : ℕ) : signedChainSubmodule n →ₗ[ZMod 2] signedChainSubmodule n where
  toFun c := ⟨modTwoBoundary c.val - Finsupp.single ∅ (modTwoBoundary c.val ∅), by
    intro s hs
    by_cases he : s = ∅
    · subst s; simp
    · have hz : modTwoBoundary c.val s = 0 := by
        by_contra hz
        obtain ⟨t, ht, v, hv, hst⟩ := modTwoBoundary_support c.val (Finsupp.mem_support_iff.mpr hz)
        have hface := signedChain_mem_face c ht
        apply hs
        exact ⟨nonempty_iff_ne_empty.mpr he,
          noOpposite_mono hface.2 (hst ▸ erase_subset v t)⟩
      simp [hz, Finsupp.single_eq_of_ne he]⟩
  map_add' c b := by
    apply Subtype.ext
    simp only [AddMemClass.coe_add, map_add, Finsupp.add_apply, Finsupp.single_add]
    abel
  map_smul' r c := by
    apply Subtype.ext
    change modTwoBoundary (r • c.val) - Finsupp.single ∅ (modTwoBoundary (r • c.val) ∅) =
      r • (modTwoBoundary c.val - Finsupp.single ∅ (modTwoBoundary c.val ∅))
    simp only [map_smul, Finsupp.smul_apply, smul_sub, Finsupp.smul_single]

-- @node: signedChainBoundary_val
/-- [The underlying chain of the ordinary boundary is the augmented boundary
minus its empty-face term](goal). -/
lemma signedChainBoundary_val {n : ℕ} (c : signedChainSubmodule n) :
    (signedChainBoundary n c).val =
      modTwoBoundary c.val - Finsupp.single ∅ (modTwoBoundary c.val ∅) := rfl

-- @node: signedChainBoundary_augmented_boundary
/-- [Taking the augmented boundary of the ordinary boundary of a signed-face
chain gives zero](goal). -/
lemma signedChainBoundary_augmented_boundary {n : ℕ} (c : signedChainSubmodule n) :
    modTwoBoundary (signedChainBoundary n c).val = 0 := by
  rw [signedChainBoundary_val, map_sub, modTwoBoundary_sq, modTwoBoundary_empty, sub_zero]

-- @node: signedChainBoundary_sq
/-- [Applying the ordinary boundary twice to any signed-face chain gives zero](goal). -/
lemma signedChainBoundary_sq {n : ℕ} (c : signedChainSubmodule n) :
    signedChainBoundary n (signedChainBoundary n c) = 0 := by
  apply Subtype.ext
  rw [signedChainBoundary_val, signedChainBoundary_augmented_boundary]
  simp

-- @node: signedChainAntipode
/-- For [a number of signed coordinate axes](hyp:n), the [antipodal chain
operator](goal) replaces every vertex of every face by its opposite, carrying
the coefficients modulo two along with the faces. -/
def signedChainAntipode (n : ℕ) : signedChainSubmodule n →ₗ[ZMod 2] signedChainSubmodule n where
  toFun c := ⟨modTwoFaceMap signedAntipode c.val, by
    intro s hs
    by_contra hz
    obtain ⟨t, ht, rfl⟩ := modTwoFaceMap_support signedAntipode c.val
      (Finsupp.mem_support_iff.mpr hz)
    exact hs (signedFaceComplex_antipode (signedChain_mem_face c ht))⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

-- @node: signedChainAntipode_val
/-- [The underlying chain of the antipodal image is obtained by mapping every
vertex to its opposite](goal). -/
lemma signedChainAntipode_val {n : ℕ} (c : signedChainSubmodule n) :
    (signedChainAntipode n c).val = modTwoFaceMap signedAntipode c.val := rfl

-- @node: signedChainBoundary_antipode
/-- [Taking the ordinary boundary commutes with taking the antipodal image
of a signed-face chain](goal). -/
lemma signedChainBoundary_antipode {n : ℕ} (c : signedChainSubmodule n) :
    signedChainBoundary n (signedChainAntipode n c) =
      signedChainAntipode n (signedChainBoundary n c) := by
  apply Subtype.ext
  simp only [signedChainBoundary_val, signedChainAntipode_val, map_sub,
    modTwoBoundary_faceMap signedAntipode signedAntipode_injective, modTwoFaceMap_single,
    image_empty]
  congr 1
  have he : modTwoFaceMap signedAntipode (modTwoBoundary c.val) ∅ =
      modTwoBoundary c.val ∅ := by
    conv_lhs => rw [← (modTwoBoundary c.val).sum_single]
    simp only [Finsupp.sum, map_sum, modTwoFaceMap_single, Finsupp.finsetSum_apply,
      Finsupp.single_apply, image_eq_empty]
    conv_rhs => rw [← (modTwoBoundary c.val).sum_single]
    simp only [Finsupp.sum, Finsupp.finsetSum_apply, Finsupp.single_apply]
  exact congrArg (Finsupp.single ∅) he

-- @node: signedChainAugmentation
/-- For [a number of signed coordinate axes](hyp:n), the [augmentation of a
signed-face chain](goal) is the sum modulo two of its singleton-face coefficients. -/
def signedChainAugmentation (n : ℕ) : signedChainSubmodule n →ₗ[ZMod 2] ZMod 2 :=
  modTwoAugmentation.comp (signedChainSubmodule n).subtype

-- @node: signedChainAugmentation_boundary
/-- [The augmentation of the ordinary boundary of any signed-face chain is zero](goal). -/
lemma signedChainAugmentation_boundary {n : ℕ} (c : signedChainSubmodule n) :
    signedChainAugmentation n (signedChainBoundary n c) = 0 := by
  change modTwoAugmentation (signedChainBoundary n c).val = 0
  rw [signedChainBoundary_val, map_sub, modTwoAugmentation_boundary]
  simp

-- @node: signedChainAugmentation_antipode
/-- [The antipodal image of a signed-face chain has the same augmentation
as the original chain](goal). -/
lemma signedChainAugmentation_antipode {n : ℕ} (c : signedChainSubmodule n) :
    signedChainAugmentation n (signedChainAntipode n c) = signedChainAugmentation n c :=
  modTwoAugmentation_faceMap signedAntipode signedAntipode_injective c.val

-- @node: modTwoFaceMap_eq_mapDomain
/-- [Mapping a face chain through a vertex map is the same as replacing each
face by its image and adding coefficients modulo two whenever images coincide](goal). -/
lemma modTwoFaceMap_eq_mapDomain {V W : Type*} [DecidableEq W]
    (f : V → W) (c : ModTwoFaceChain V) :
    modTwoFaceMap f c = Finsupp.mapDomain (fun s => s.image f) c := by
  conv_lhs => rw [← c.sum_single]
  simp only [Finsupp.sum, map_sum, modTwoFaceMap_single]
  rfl

-- @node: modTwoFaceMap_involution_apply
/-- If [a vertex map applied twice returns every vertex to itself](hyp:ha),
then [the coefficient of a face in the mapped chain equals the original
coefficient of that face's image](goal). -/
lemma modTwoFaceMap_involution_apply {V : Type*} [DecidableEq V]
    (a : V → V) (ha : Function.Involutive a) (c : ModTwoFaceChain V) (s : Finset V) :
    modTwoFaceMap a c s = c (s.image a) := by
  have hi : Function.Involutive (fun t : Finset V => t.image a) := by
    intro t
    simp only [image_image]
    have hcomp : a ∘ a = id := funext ha
    rw [hcomp]
    exact image_id
  rw [modTwoFaceMap_eq_mapDomain]
  simpa only [hi s] using Finsupp.mapDomain_apply hi.injective c (s.image a)

-- @node: signedChainNorm
/-- For [a number of signed coordinate axes](hyp:n), the [chain norm
operator](goal) adds a signed-face chain to its antipodal image, modulo two. -/
def signedChainNorm (n : ℕ) : signedChainSubmodule n →ₗ[ZMod 2] signedChainSubmodule n :=
  LinearMap.id + signedChainAntipode n

-- @node: signedChainNorm_val
/-- [The underlying chain of the chain norm is the original chain plus its
antipodal image, with coefficients modulo two](goal). -/
lemma signedChainNorm_val {n : ℕ} (c : signedChainSubmodule n) :
    (signedChainNorm n c).val = c.val + modTwoFaceMap signedAntipode c.val := rfl

-- @node: signedChainNorm_kernel_subset_range
/-- If [a signed-face chain has zero chain norm](hyp:hc), then [it is the
chain norm of another signed-face chain](goal).

Choosing one face from each antipodal pair gives such a chain without
introducing faces outside the original support. -/
lemma signedChainNorm_kernel_subset_range {n : ℕ} (c : signedChainSubmodule n)
    (hc : signedChainNorm n c = 0) : ∃ b, signedChainNorm n b = c := by
  classical
  let e := Fintype.equivFin (Finset (SignedVertex n))
  let bval := c.val.filter (fun s => e s < e (s.image signedAntipode))
  have hb : bval ∈ signedChainSubmodule n := by
    intro s hs
    simp only [bval, Finsupp.filter_apply]
    split_ifs <;> simp [c.property s hs]
  let b : signedChainSubmodule n := ⟨bval, hb⟩
  have hi (s : Finset (SignedVertex n)) :
      (s.image signedAntipode).image signedAntipode = s := by
    simp only [image_image]
    have hcomp : signedAntipode ∘ signedAntipode = (id : SignedVertex n → SignedVertex n) :=
      funext signedAntipode_involutive
    rw [hcomp]
    exact image_id
  have hinv (s : Finset (SignedVertex n)) : c.val (s.image signedAntipode) = c.val s := by
    have hz := congrArg (fun z : signedChainSubmodule n => z.val s) hc
    change (c.val + modTwoFaceMap signedAntipode c.val) s = 0 at hz
    rw [Finsupp.add_apply,
      modTwoFaceMap_involution_apply signedAntipode signedAntipode_involutive] at hz
    exact add_left_cancel (hz.trans (ZModModule.add_self (c.val s)).symm)
  refine ⟨b, Subtype.ext ?_⟩
  apply Finsupp.ext
  intro s
  change bval s + modTwoFaceMap signedAntipode bval s = c.val s
  rw [modTwoFaceMap_involution_apply signedAntipode signedAntipode_involutive]
  simp only [bval, Finsupp.filter_apply, hi s]
  by_cases h : e s < e (s.image signedAntipode)
  · rw [if_pos h, if_neg (not_lt.mpr (le_of_lt h)), add_zero]
  · by_cases h' : e (s.image signedAntipode) < e s
    · rw [if_neg h, if_pos h', zero_add, hinv]
    · have heq : s.image signedAntipode = s := e.injective
        (le_antisymm (le_of_not_gt h) (le_of_not_gt h'))
      have hz : c.val s = 0 := by
        by_contra hz
        exact signedFaceComplex_ne_antipode
          (signedChain_mem_face c (Finsupp.mem_support_iff.mpr hz)) heq
      rw [if_neg h, if_neg h', zero_add, hz]

-- @node: signedChainNorm_boundary
/-- [The chain norm commutes with the ordinary boundary on signed-face chains](goal). -/
lemma signedChainNorm_boundary {n : ℕ} (c : signedChainSubmodule n) :
    signedChainNorm n (signedChainBoundary n c) =
      signedChainBoundary n (signedChainNorm n c) := by
  change signedChainBoundary n c + signedChainAntipode n (signedChainBoundary n c) =
    signedChainBoundary n (c + signedChainAntipode n c)
  rw [map_add, signedChainBoundary_antipode]

-- @node: signedChainAugmentation_norm
/-- [The augmentation of the chain norm of any signed-face chain is zero](goal). -/
lemma signedChainAugmentation_norm {n : ℕ} (c : signedChainSubmodule n) :
    signedChainAugmentation n (signedChainNorm n c) = 0 := by
  change signedChainAugmentation n (c + signedChainAntipode n c) = 0
  rw [map_add, signedChainAugmentation_antipode, ZModModule.add_self]

-- @node: signedChain_ladder_top_ne_zero
/-- If [each chain up to a given level has boundary equal to the chain norm
of the preceding chain](hyp:hc) and [the bottom chain has augmentation one](hyp:hbottom),
then [the chain at that level is nonzero](goal). -/
lemma signedChain_ladder_top_ne_zero {n : ℕ} (k : ℕ)
    (c : ℕ → signedChainSubmodule n)
    (hc : ∀ i, i < k → signedChainBoundary n (c (i + 1)) = signedChainNorm n (c i))
    (hbottom : signedChainAugmentation n (c 0) = 1) : c k ≠ 0 := by
  have h := modTwo_chain_ladder_norm_ne_zero
    (signedChainNorm n) (signedChainBoundary n) (signedChainAugmentation n)
    signedChainNorm_kernel_subset_range signedChainBoundary_sq signedChainNorm_boundary
    signedChainAugmentation_norm signedChainAugmentation_boundary k c hc hbottom
  intro hz
  exact h (by rw [hz, map_zero])

-- @node: carriedLabeledSignedHemisphereChain
/-- Given [a signed-coordinate labeling of the ambient space](hyp:f),
[a subdivision depth](hyp:r), [the absence of opposite labels on every face
of that subdivision](hyp:hf), and [a hemisphere dimension](hyp:k), the
[carried labeled hemisphere chain](goal) is the labeled hemisphere chain
viewed as a chain supported on nonempty target faces with no opposite vertices. -/
def carriedLabeledSignedHemisphereChain {n d : ℕ}
    (f : (Fin n → ℝ) → SignedVertex d) (r : ℕ)
    (hf : ∀ s ∈ (Toolkit.Foundations.Topology.sdIterate (signedGeometricComplex n) r).faces,
      NoOpposite (s.image f)) (k : ℕ) : signedChainSubmodule d :=
  ⟨labeledSignedHemisphereChain f r k, by
    intro s hs
    by_contra hz
    exact hs (labeledSignedHemisphereChain_support f r k hf
      (Finsupp.mem_support_iff.mpr hz)).1⟩

-- @node: carriedLabeledSignedHemisphereChain_boundary
/-- If [every subdivided face has no opposite labels](hyp:hf),
[the labeling sends negated face vertices to opposite labels](hyp:he), and
[the next hemisphere dimension is below the ambient dimension](hyp:hk),
then [the boundary of the next carried labeled hemisphere chain equals the
chain norm of the current one](goal). -/
lemma carriedLabeledSignedHemisphereChain_boundary {n d : ℕ}
    (f : (Fin n → ℝ) → SignedVertex d) (r : ℕ)
    (hf : ∀ s ∈ (Toolkit.Foundations.Topology.sdIterate (signedGeometricComplex n) r).faces,
      NoOpposite (s.image f))
    (he : ∀ s ∈ (Toolkit.Foundations.Topology.sdIterate (signedGeometricComplex n) r).faces,
      ∀ x ∈ s, f (-x) = signedAntipode (f x)) (k : ℕ) (hk : k + 1 < n) :
    signedChainBoundary d (carriedLabeledSignedHemisphereChain f r hf (k + 1)) =
      signedChainNorm d (carriedLabeledSignedHemisphereChain f r hf k) := by
  apply Subtype.ext
  rw [signedChainBoundary_val, signedChainNorm_val]
  change modTwoBoundary (labeledSignedHemisphereChain f r (k + 1)) -
    Finsupp.single ∅ (modTwoBoundary (labeledSignedHemisphereChain f r (k + 1)) ∅) =
    labeledSignedHemisphereChain f r k +
      modTwoFaceMap signedAntipode (labeledSignedHemisphereChain f r k)
  rw [labeledSignedHemisphereChain_boundary f r k he hk]
  have hz : (labeledSignedHemisphereChain f r k +
      modTwoFaceMap signedAntipode (labeledSignedHemisphereChain f r k)) ∅ = 0 :=
    signedChain_empty (signedChainNorm d (carriedLabeledSignedHemisphereChain f r hf k))
  rw [hz, Finsupp.single_zero, sub_zero]

-- @node: carriedLabeledSignedHemisphereChain_bottom_augmentation
/-- If [the ambient dimension is positive](hyp:hn) and [every subdivided
face has no opposite labels](hyp:hf), then [the bottom carried labeled
hemisphere chain has augmentation one](goal). -/
lemma carriedLabeledSignedHemisphereChain_bottom_augmentation {n d : ℕ} (hn : 0 < n)
    (f : (Fin n → ℝ) → SignedVertex d) (r : ℕ)
    (hf : ∀ s ∈ (Toolkit.Foundations.Topology.sdIterate (signedGeometricComplex n) r).faces,
      NoOpposite (s.image f)) :
    signedChainAugmentation d (carriedLabeledSignedHemisphereChain f r hf 0) = 1 :=
  labeledSignedHemisphereChain_bottom_augmentation hn f r

-- @node: signedSubdivision_no_antipodal_labeling
/-- If [a labeling of a subdivision of the signed sphere sends negated face
vertices to opposite labels](hyp:he), then [it cannot avoid opposite labels
on every face when the number of signed coordinate labels equals the sphere's
dimension](goal). -/
lemma signedSubdivision_no_antipodal_labeling {d : ℕ}
    (f : (Fin (d + 1) → ℝ) → SignedVertex d) (r : ℕ)
    (he : ∀ s ∈ (Toolkit.Foundations.Topology.sdIterate
        (signedGeometricComplex (d + 1)) r).faces,
      ∀ x ∈ s, f (-x) = signedAntipode (f x)) :
    ¬ (∀ s ∈ (Toolkit.Foundations.Topology.sdIterate
        (signedGeometricComplex (d + 1)) r).faces, NoOpposite (s.image f)) := by
  intro hf
  let c := carriedLabeledSignedHemisphereChain f r hf
  have hnonzero := signedChain_ladder_top_ne_zero d c
    (fun i hi => carriedLabeledSignedHemisphereChain_boundary f r hf he i (by omega))
    (carriedLabeledSignedHemisphereChain_bottom_augmentation (Nat.succ_pos d) f r hf)
  apply hnonzero
  apply Subtype.ext
  exact labeledSignedHemisphereChain_top_vanishing f r hf

end
end Papers.TbsNeuralCausalPi.Antipodal

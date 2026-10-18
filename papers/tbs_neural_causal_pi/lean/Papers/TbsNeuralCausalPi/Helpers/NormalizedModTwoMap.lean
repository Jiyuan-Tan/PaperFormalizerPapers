module
public import Papers.TbsNeuralCausalPi.Helpers.GeometricModTwoSubdivision
/-! # Mod-two chain maps for vertex labels with repetitions

A vertex labeling sends an injective face to its image and a degenerate
face to zero. This degree-preserving map commutes with the augmented
boundary even when the labeling is not injective.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi.Antipodal
noncomputable section
open Finset

-- @node: modTwoSimplicialMap
/-- For [a vertex labeling](hyp:f), the [normalized mod-two chain map](goal)
sends each face to its labeled image if its labels are distinct, and to zero otherwise,
and extends this rule linearly to chains. -/
def modTwoSimplicialMap {V W : Type*} [DecidableEq W] (f : V → W) :
    ModTwoFaceChain V →ₗ[ZMod 2] ModTwoFaceChain W :=
  Finsupp.linearCombination (ZMod 2) (fun s =>
    if Set.InjOn f (s : Set V) then Finsupp.single (s.image f) 1 else 0)

-- @node: modTwoSimplicialMap_single
/-- [Relabeling a single face with a mod-two coefficient gives its image with the
same coefficient when the labels are distinct, and zero otherwise](goal). -/
@[simp] lemma modTwoSimplicialMap_single {V W : Type*} [DecidableEq W]
    (f : V → W) (s : Finset V) (r : ZMod 2) :
    modTwoSimplicialMap f (Finsupp.single s r) =
      if Set.InjOn f (s : Set V) then Finsupp.single (s.image f) r else 0 := by
  classical
  by_cases h : Set.InjOn f (s : Set V) <;> simp [modTwoSimplicialMap, h]

-- @node: modTwoSimplicialMap_cone_single
/-- [Relabeling the cone over a single face equals taking the cone over the
relabeled face, with the cone vertex replaced by its label](goal). -/
lemma modTwoSimplicialMap_cone_single {V W : Type*} [DecidableEq V] [DecidableEq W]
    (f : V → W) (v : V) (s : Finset V) :
    modTwoSimplicialMap f (modTwoCone v (Finsupp.single s 1)) =
      modTwoCone (f v) (modTwoSimplicialMap f (Finsupp.single s 1)) := by
  classical
  by_cases hv : v ∈ s
  · simp only [modTwoCone_single, if_pos hv, map_zero, modTwoSimplicialMap_single]
    split_ifs with hf
    · rw [modTwoCone_single, if_pos (mem_image_of_mem f hv)]
    · exact (map_zero _).symm
  · have hinsert : Set.InjOn f (↑(insert v s) : Set V) ↔
        Set.InjOn f (s : Set V) ∧ f v ∉ s.image f := by
      rw [coe_insert, Set.injOn_insert hv]
      simp
    simp only [modTwoCone_single, if_neg hv, modTwoSimplicialMap_single]
    by_cases hf : Set.InjOn f (s : Set V)
    · by_cases hfv : f v ∈ s.image f
      · rw [if_neg (fun h => (hinsert.mp h).2 hfv), if_pos hf,
          modTwoCone_single, if_pos hfv]
      · rw [if_pos (hinsert.mpr ⟨hf, hfv⟩), if_pos hf,
          modTwoCone_single, if_neg hfv, image_insert]
    · rw [if_neg (fun h => hf (hinsert.mp h).1), if_neg hf, map_zero]

-- @node: modTwoSimplicialMap_cone
/-- [Relabeling a mod-two chain commutes with forming a cone, provided the
cone vertex is also replaced by its label](goal). -/
lemma modTwoSimplicialMap_cone {V W : Type*} [DecidableEq V] [DecidableEq W]
    (f : V → W) (v : V) (c : ModTwoFaceChain V) :
    modTwoSimplicialMap f (modTwoCone v c) =
      modTwoCone (f v) (modTwoSimplicialMap f c) := by
  have h : (modTwoSimplicialMap f).comp (modTwoCone v) =
      (modTwoCone (f v)).comp (modTwoSimplicialMap f) := by
    apply Finsupp.lhom_ext
    intro s r
    have he : Finsupp.single s r = r • Finsupp.single s (1 : ZMod 2) := by simp
    simp only [LinearMap.comp_apply, he, map_smul, modTwoSimplicialMap_cone_single]
  exact LinearMap.congr_fun h c

-- @node: modTwoBoundary_cone_eq
/-- [The boundary of a cone over a mod-two chain equals that chain plus the
cone over its boundary](goal). -/
lemma modTwoBoundary_cone_eq {V : Type*} [DecidableEq V]
    (v : V) (c : ModTwoFaceChain V) :
    modTwoBoundary (modTwoCone v c) = c + modTwoCone v (modTwoBoundary c) := by
  calc
    _ = (modTwoBoundary (modTwoCone v c) + modTwoCone v (modTwoBoundary c)) +
        modTwoCone v (modTwoBoundary c) := by
      rw [add_assoc, ZModModule.add_self, add_zero]
    _ = _ := by rw [modTwoBoundary_cone]

-- @node: modTwoBoundary_simplicialMap_single
/-- [Taking the boundary of a relabeled single face equals relabeling its
boundary, including when repeated labels collapse the face to zero](goal). -/
lemma modTwoBoundary_simplicialMap_single {V W : Type*}
    [DecidableEq V] [DecidableEq W] (f : V → W) (s : Finset V) :
    modTwoBoundary (modTwoSimplicialMap f (Finsupp.single s 1)) =
      modTwoSimplicialMap f (modTwoBoundary (Finsupp.single s 1)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert v s hv ih =>
      have he : Finsupp.single (insert v s) (1 : ZMod 2) =
          modTwoCone v (Finsupp.single s 1) := by
        rw [modTwoCone_single, if_neg hv]
      rw [he, modTwoSimplicialMap_cone, modTwoBoundary_cone_eq, ih,
        modTwoBoundary_cone_eq, map_add, modTwoSimplicialMap_cone]

-- @node: modTwoBoundary_simplicialMap
/-- [Relabeling a mod-two chain commutes with taking its boundary](goal). -/
lemma modTwoBoundary_simplicialMap {V W : Type*}
    [DecidableEq V] [DecidableEq W] (f : V → W) (c : ModTwoFaceChain V) :
    modTwoBoundary (modTwoSimplicialMap f c) =
      modTwoSimplicialMap f (modTwoBoundary c) := by
  have h : (modTwoBoundary (V := W)).comp (modTwoSimplicialMap f) =
      (modTwoSimplicialMap f).comp modTwoBoundary := by
    apply Finsupp.lhom_ext
    intro s r
    have he : Finsupp.single s r = r • Finsupp.single s (1 : ZMod 2) := by simp
    simp only [LinearMap.comp_apply, he, map_smul, modTwoBoundary_simplicialMap_single]
  exact LinearMap.congr_fun h c

-- @node: modTwoSimplicialMap_support
/-- If [a target face has a nonzero coefficient in the relabeled chain](hyp:ht),
then [it is the image of a source face with a nonzero coefficient on which
the labeling is injective](goal). -/
lemma modTwoSimplicialMap_support {V W : Type*} [DecidableEq W]
    (f : V → W) (c : ModTwoFaceChain V) {t : Finset W}
    (ht : t ∈ (modTwoSimplicialMap f c).support) :
    ∃ s ∈ c.support, Set.InjOn f (s : Set V) ∧ t = s.image f := by
  classical
  obtain ⟨s, hs, hst⟩ := modTwoLinearMap_support (modTwoSimplicialMap f) c ht
  rw [modTwoSimplicialMap_single] at hst
  split_ifs at hst with hf
  · exact ⟨s, hs, hf, ((Finsupp.mem_support_single _ _ _).mp hst).1⟩
  · simp at hst

-- @node: modTwoSimplicialMap_homogeneous
/-- If [every face with a nonzero coefficient in the source chain has exactly
k vertices](hyp:hc), then [every face with a nonzero coefficient in its
relabeled chain also has exactly k vertices](goal). -/
lemma modTwoSimplicialMap_homogeneous {V W : Type*} [DecidableEq W]
    (f : V → W) (c : ModTwoFaceChain V) (k : ℕ)
    (hc : ∀ s ∈ c.support, s.card = k) :
    ∀ t ∈ (modTwoSimplicialMap f c).support, t.card = k := by
  intro t ht
  obtain ⟨s, hs, hf, rfl⟩ := modTwoSimplicialMap_support f c ht
  rw [card_image_iff.mpr hf, hc s hs]

-- @node: modTwoSimplicialMap_eq_faceMap_of_support_injOn
/-- If [the labeling is injective on every face with a nonzero coefficient
in the chain](hyp:hf), then [normalized relabeling equals the ordinary
face-image map on that chain](goal). -/
lemma modTwoSimplicialMap_eq_faceMap_of_support_injOn {V W : Type*} [DecidableEq W]
    (f : V → W) (c : ModTwoFaceChain V)
    (hf : ∀ s ∈ c.support, Set.InjOn f (s : Set V)) :
    modTwoSimplicialMap f c = modTwoFaceMap f c := by
  apply modTwoLinearMap_eq_of_support
  intro s hs
  simp [hf s hs]

-- @node: modTwoAugmentation_simplicialMap_single
/-- [Relabeling a single face with any mod-two coefficient preserves its
augmentation, the sum of coefficients on one-vertex faces](goal). -/
lemma modTwoAugmentation_simplicialMap_single {V W : Type*} [DecidableEq W]
    (f : V → W) (s : Finset V) (r : ZMod 2) :
    modTwoAugmentation (modTwoSimplicialMap f (Finsupp.single s r)) =
      modTwoAugmentation (Finsupp.single s r) := by
  classical
  rw [modTwoSimplicialMap_single]
  split_ifs with hf
  · simp [card_image_iff.mpr hf]
  · have hs : s.card ≠ 1 := by
      rintro hs
      obtain ⟨v, rfl⟩ := card_eq_one.mp hs
      exact hf (by simpa only [coe_singleton] using Set.injOn_singleton f v)
    simp [hs]

-- @node: modTwoAugmentation_simplicialMap
/-- [Relabeling any mod-two chain preserves its augmentation, the sum of
coefficients on one-vertex faces](goal). -/
lemma modTwoAugmentation_simplicialMap {V W : Type*} [DecidableEq W]
    (f : V → W) (c : ModTwoFaceChain V) :
    modTwoAugmentation (modTwoSimplicialMap f c) = modTwoAugmentation c := by
  have h : (modTwoAugmentation (V := W)).comp (modTwoSimplicialMap f) =
      modTwoAugmentation := by
    apply Finsupp.lhom_ext
    exact modTwoAugmentation_simplicialMap_single f
  exact LinearMap.congr_fun h c

-- @node: modTwoSimplicialMap_id
/-- [Relabeling a mod-two chain by the identity labeling leaves it unchanged](goal). -/
lemma modTwoSimplicialMap_id {V : Type*} [DecidableEq V] (c : ModTwoFaceChain V) :
    modTwoSimplicialMap id c = c := by
  rw [modTwoSimplicialMap_eq_faceMap_of_support_injOn id c
    (fun _ _ => Function.injective_id.injOn), modTwoFaceMap_id]

-- @node: injOn_image_comp_iff
/-- If [the first labeling is injective on a finite face](hyp:hf), then
[the second labeling is injective on its image exactly when the composite
labeling is injective on the original face](goal). -/
lemma injOn_image_comp_iff {U V W : Type*} [DecidableEq V]
    (f : U → V) (g : V → W) (s : Finset U) (hf : Set.InjOn f (s : Set U)) :
    Set.InjOn g (↑(s.image f) : Set V) ↔ Set.InjOn (g ∘ f) (s : Set U) := by
  constructor
  · intro hg x hx y hy hxy
    exact hf hx hy (hg (mem_image_of_mem f hx) (mem_image_of_mem f hy) hxy)
  · intro hgf x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hy
    exact congrArg f (hgf ha hb hxy)

-- @node: modTwoSimplicialMap_comp
/-- [Relabeling a mod-two chain successively by two vertex maps gives the
same result as relabeling once by their composition](goal). -/
lemma modTwoSimplicialMap_comp {U V W : Type*} [DecidableEq V] [DecidableEq W]
    (f : U → V) (g : V → W) (c : ModTwoFaceChain U) :
    modTwoSimplicialMap g (modTwoSimplicialMap f c) =
      modTwoSimplicialMap (g ∘ f) c := by
  classical
  have h : (modTwoSimplicialMap g).comp (modTwoSimplicialMap f) =
      modTwoSimplicialMap (g ∘ f) := by
    apply Finsupp.lhom_ext
    intro s r
    simp only [LinearMap.comp_apply, modTwoSimplicialMap_single]
    by_cases hf : Set.InjOn f (s : Set U)
    · rw [if_pos hf, modTwoSimplicialMap_single]
      simp only [injOn_image_comp_iff f g s hf, image_image]
    · have hgf : ¬ Set.InjOn (g ∘ f) (s : Set U) := by
        intro hgf
        exact hf (fun x hx y hy he => hgf hx hy (congrArg g he))
      rw [if_neg hf, map_zero, if_neg hgf]
  exact LinearMap.congr_fun h c

-- @node: modTwoSimplicialMap_single_congr
/-- If [two labelings agree at every vertex of a finite face](hyp:he), then
[they give the same normalized image of that face with any mod-two coefficient](goal). -/
lemma modTwoSimplicialMap_single_congr {V W : Type*} [DecidableEq W]
    (f g : V → W) (s : Finset V) (r : ZMod 2) (he : ∀ v ∈ s, f v = g v) :
    modTwoSimplicialMap f (Finsupp.single s r) =
      modTwoSimplicialMap g (Finsupp.single s r) := by
  classical
  have hi : Set.InjOn f (s : Set V) ↔ Set.InjOn g (s : Set V) := by
    constructor
    · intro hf x hx y hy hxy
      apply hf hx hy
      rw [he x hx, he y hy]
      exact hxy
    · intro hg x hx y hy hxy
      apply hg hx hy
      rw [← he x hx, ← he y hy]
      exact hxy
  simp only [modTwoSimplicialMap_single, hi, image_congr he]

-- @node: modTwoSimplicialMap_congr_on_support
/-- If [two labelings agree at every vertex of every face with a nonzero
coefficient in a chain](hyp:he), then [their normalized images of the chain
are equal](goal). -/
lemma modTwoSimplicialMap_congr_on_support {V W : Type*} [DecidableEq W]
    (f g : V → W) (c : ModTwoFaceChain V)
    (he : ∀ s ∈ c.support, ∀ v ∈ s, f v = g v) :
    modTwoSimplicialMap f c = modTwoSimplicialMap g c := by
  apply modTwoLinearMap_eq_of_support
  intro s hs
  exact modTwoSimplicialMap_single_congr f g s 1 (he s hs)

-- @node: modTwoSimplicialMap_equivariant_of_support
/-- If [the source vertex transformation is injective](hyp:ha),
[the target vertex transformation is injective](hyp:hb), and
[labeling after the source transformation equals transforming the label
on every vertex used by the chain](hyp:he), then [transforming the chain
before normalized relabeling equals transforming its relabeled image](goal). -/
lemma modTwoSimplicialMap_equivariant_of_support {V W : Type*}
    [DecidableEq V] [DecidableEq W]
    (f : V → W) (a : V → V) (b : W → W)
    (ha : Function.Injective a) (hb : Function.Injective b) (c : ModTwoFaceChain V)
    (he : ∀ s ∈ c.support, ∀ v ∈ s, f (a v) = b (f v)) :
    modTwoSimplicialMap f (modTwoFaceMap a c) =
      modTwoFaceMap b (modTwoSimplicialMap f c) := by
  rw [← modTwoSimplicialMap_eq_faceMap_of_support_injOn a c (fun _ _ => ha.injOn),
    ← modTwoSimplicialMap_eq_faceMap_of_support_injOn b _ (fun _ _ => hb.injOn),
    modTwoSimplicialMap_comp, modTwoSimplicialMap_comp]
  exact modTwoSimplicialMap_congr_on_support _ _ c he

-- @node: modTwoSimplicialMap_equivariant
/-- If [the source vertex transformation is injective](hyp:ha),
[the target vertex transformation is injective](hyp:hb), and
[labeling after the source transformation equals transforming the label
at every vertex](hyp:he), then [transforming any chain before normalized
relabeling equals transforming its relabeled image](goal). -/
lemma modTwoSimplicialMap_equivariant {V W : Type*}
    [DecidableEq V] [DecidableEq W]
    (f : V → W) (a : V → V) (b : W → W)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (he : ∀ v, f (a v) = b (f v)) (c : ModTwoFaceChain V) :
    modTwoSimplicialMap f (modTwoFaceMap a c) =
      modTwoFaceMap b (modTwoSimplicialMap f c) := by
  have ha' : ∀ s ∈ c.support, Set.InjOn a (s : Set V) := fun _ _ => ha.injOn
  have hb' : ∀ s ∈ (modTwoSimplicialMap f c).support,
      Set.InjOn b (s : Set W) := fun _ _ => hb.injOn
  rw [← modTwoSimplicialMap_eq_faceMap_of_support_injOn a c ha',
    ← modTwoSimplicialMap_eq_faceMap_of_support_injOn b _ hb',
    modTwoSimplicialMap_comp, modTwoSimplicialMap_comp]
  exact congrArg (fun h => modTwoSimplicialMap h c) (funext he)

/-- If [every face with a nonzero coefficient in the source chain has k
vertices](hyp:hc), [k exceeds the number of target coordinate directions](hyp:hdk),
and [no such face has labels containing an opposite pair](hyp:hface), then
[the normalized relabeled chain is zero](goal). -/
-- @node: modTwoSimplicialMap_signed_dimension_vanishing
lemma modTwoSimplicialMap_signed_dimension_vanishing {V : Type*} {d k : ℕ}
    (f : V → SignedVertex d) (c : ModTwoFaceChain V)
    (hc : ∀ s ∈ c.support, s.card = k) (hdk : d < k)
    (hface : ∀ s ∈ c.support, NoOpposite (s.image f)) :
    modTwoSimplicialMap f c = 0 := by
  apply Finsupp.ext
  intro t
  by_contra ht
  have hmem : t ∈ (modTwoSimplicialMap f c).support := by
    simpa only [Finsupp.mem_support_iff, Finsupp.zero_apply] using ht
  obtain ⟨s, hs, hf, rfl⟩ := modTwoSimplicialMap_support f c hmem
  have hbound := noOpposite_card_le (hface s hs)
  rw [card_image_iff.mpr hf, hc s hs] at hbound
  exact (not_le_of_gt hdk) hbound

-- @node: modTwoSimplicialMap_signed_support
/-- If [each face with a nonzero source coefficient has k plus one vertices](hyp:hc)
and [its labels contain no opposite pair](hyp:hface), then
[any face with a nonzero coefficient in the relabeled chain](hyp:ht)
[belongs to the signed face complex and has k plus one vertices](goal). -/
lemma modTwoSimplicialMap_signed_support {V : Type*} {d k : ℕ}
    (f : V → SignedVertex d) (c : ModTwoFaceChain V)
    (hc : ∀ s ∈ c.support, s.card = k + 1)
    (hface : ∀ s ∈ c.support, NoOpposite (s.image f))
    {t : Finset (SignedVertex d)} (ht : t ∈ (modTwoSimplicialMap f c).support) :
    t ∈ (signedFaceComplex d).faces ∧ t.card = k + 1 := by
  obtain ⟨s, hs, hf, rfl⟩ := modTwoSimplicialMap_support f c ht
  have hcard : (s.image f).card = k + 1 := by rw [card_image_iff.mpr hf, hc s hs]
  exact ⟨⟨card_pos.mp (by omega), hface s hs⟩, hcard⟩

/-- Given [a labeling of Euclidean points by signed vertices](hyp:f),
[a number of subdivision rounds](hyp:r), and [a hemisphere dimension](hyp:k),
the [labeled signed hemisphere chain](goal) is the normalized relabeling
of the geometric hemisphere chain at that subdivision level and dimension. -/
-- @node: labeledSignedHemisphereChain
def labeledSignedHemisphereChain {n d : ℕ}
    (f : (Fin n → ℝ) → SignedVertex d) (r k : ℕ) : ModTwoFaceChain (SignedVertex d) :=
  modTwoSimplicialMap f (subdividedSignedHemisphereChain n r k)

-- @node: labeledSignedHemisphereChain_boundary
/-- If [the labeling sends negated vertices to opposite signed labels on
every face of the chosen subdivision](hyp:hf) and [k plus one is less than
the ambient dimension](hyp:hk), then [the boundary of the labeled hemisphere
chain in dimension k plus one is the sum of the dimension-k labeled
hemisphere chain and its antipodal image](goal). -/
lemma labeledSignedHemisphereChain_boundary {n d : ℕ}
    (f : (Fin n → ℝ) → SignedVertex d)
    (r k : ℕ)
    (hf : ∀ s ∈ (Toolkit.Foundations.Topology.sdIterate (signedGeometricComplex n) r).faces,
      ∀ x ∈ s, f (-x) = signedAntipode (f x)) (hk : k + 1 < n) :
    modTwoBoundary (labeledSignedHemisphereChain f r (k + 1)) =
      labeledSignedHemisphereChain f r k +
        modTwoFaceMap signedAntipode (labeledSignedHemisphereChain f r k) := by
  unfold labeledSignedHemisphereChain
  rw [modTwoBoundary_simplicialMap, subdividedSignedHemisphereChain_boundary n r k hk,
    map_add, modTwoSimplicialMap_equivariant_of_support f (fun x => -x) signedAntipode
      neg_injective signedAntipode_injective _ (fun s hs x hx =>
        hf s (subdividedSignedHemisphereChain_support n r k hs).1 x hx)]

-- @node: labeledSignedHemisphereChain_bottom_augmentation
/-- If [the ambient dimension is positive](hyp:hn), then [the labeled
zero-dimensional hemisphere chain has augmentation one at every subdivision
level](goal). -/
lemma labeledSignedHemisphereChain_bottom_augmentation {n d : ℕ}
    (hn : 0 < n) (f : (Fin n → ℝ) → SignedVertex d) (r : ℕ) :
    modTwoAugmentation (labeledSignedHemisphereChain f r 0) = 1 := by
  rw [labeledSignedHemisphereChain, modTwoAugmentation_simplicialMap,
    subdividedSignedHemisphereChain_bottom_augmentation hn]

-- @node: labeledSignedHemisphereChain_support
/-- If [the labels on every face of the chosen subdivision contain no
opposite pair](hyp:hf), then [any face with a nonzero coefficient in the
labeled dimension-k hemisphere chain](hyp:ht) [belongs to the signed face
complex and has k plus one vertices](goal). -/
lemma labeledSignedHemisphereChain_support {n d : ℕ}
    (f : (Fin n → ℝ) → SignedVertex d) (r k : ℕ)
    (hf : ∀ s ∈ (Toolkit.Foundations.Topology.sdIterate (signedGeometricComplex n) r).faces,
      NoOpposite (s.image f))
    {t : Finset (SignedVertex d)} (ht : t ∈ (labeledSignedHemisphereChain f r k).support) :
    t ∈ (signedFaceComplex d).faces ∧ t.card = k + 1 := by
  apply modTwoSimplicialMap_signed_support f (subdividedSignedHemisphereChain n r k)
    (fun s hs => (subdividedSignedHemisphereChain_support n r k hs).2)
    (fun s hs => hf s (subdividedSignedHemisphereChain_support n r k hs).1) ht

-- @node: labeledSignedHemisphereChain_top_vanishing
/-- If [the labels on every face of the chosen subdivision contain no
opposite pair](hyp:hf), then [the labeled dimension-d hemisphere chain
in ambient dimension d plus one, using d signed coordinate directions,
is zero](goal). -/
lemma labeledSignedHemisphereChain_top_vanishing {d : ℕ}
    (f : (Fin (d + 1) → ℝ) → SignedVertex d) (r : ℕ)
    (hf : ∀ s ∈ (Toolkit.Foundations.Topology.sdIterate
        (signedGeometricComplex (d + 1)) r).faces, NoOpposite (s.image f)) :
    labeledSignedHemisphereChain f r d = 0 := by
  apply modTwoSimplicialMap_signed_dimension_vanishing f
    (subdividedSignedHemisphereChain (d + 1) r d)
    (fun s hs => (subdividedSignedHemisphereChain_support (d + 1) r d hs).2)
    (Nat.lt_succ_self d)
    (fun s hs => hf s (subdividedSignedHemisphereChain_support (d + 1) r d hs).1)

end
end Papers.TbsNeuralCausalPi.Antipodal

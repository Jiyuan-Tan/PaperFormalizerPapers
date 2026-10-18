module
public import Toolkit.Foundations.Topology.PiecewiseAffineApproximation
public import Papers.TbsNeuralCausalPi.Helpers.ModTwoSubdivision
public import Papers.TbsNeuralCausalPi.Helpers.AntipodalAction
/-! # Geometric realization of the subdivision chain map

The abstract flags are sent to their barycenters. Barycenters are injective
on the faces of a geometric complex, which supplies exactly the local
injectivity needed for boundary and augmentation preservation.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi.Antipodal
noncomputable section
open Finset Toolkit.Foundations.Topology
attribute [local instance] Classical.propDecidable

-- @node: modTwoLinearMap_eq_of_support
/-- If [two linear maps over coefficients modulo two agree on each unit chain in the
support of a chain](hyp:h), then [they agree on that chain](goal). -/
lemma modTwoLinearMap_eq_of_support {A B : Type*}
    (T S : (A →₀ ZMod 2) →ₗ[ZMod 2] (B →₀ ZMod 2))
    (c : A →₀ ZMod 2)
    (h : ∀ s ∈ c.support, T (Finsupp.single s 1) = S (Finsupp.single s 1)) :
    T c = S c := by
  conv_lhs => rw [← c.sum_single]
  conv_rhs => rw [← c.sum_single]
  simp only [Finsupp.sum, map_sum]
  apply sum_congr rfl
  intro s hs
  have he : Finsupp.single s (c s) = c s • Finsupp.single s (1 : ZMod 2) := by simp
  rw [he, map_smul, map_smul, h s hs]

-- @node: modTwoBoundary_faceMap_single_of_injOn
/-- If [a vertex map is injective on a finite face](hyp:hf), then [mapping the unit
chain on that face commutes with taking its boundary, with coefficients modulo two](goal). -/
lemma modTwoBoundary_faceMap_single_of_injOn {V W : Type*} [DecidableEq V] [DecidableEq W]
    (f : V → W) (s : Finset V) (hf : Set.InjOn f (s : Set V)) :
    modTwoBoundary (modTwoFaceMap f (Finsupp.single s 1)) =
      modTwoFaceMap f (modTwoBoundary (Finsupp.single s 1)) := by
  simp only [modTwoFaceMap_single, modTwoBoundary_single, one_smul, map_sum,
    modTwoFaceMap_single]
  rw [sum_image (fun v hv w hw h => hf hv hw h)]
  apply sum_congr rfl
  intro v hv
  congr 1
  apply Subset.antisymm
  · exact erase_image_subset_image_erase f s v
  · intro y hy
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hy
    refine mem_erase.mpr ⟨?_, mem_image_of_mem f (mem_of_mem_erase hw)⟩
    intro he
    exact (mem_erase.mp hw).1 (hf (mem_of_mem_erase hw) hv he)

-- @node: modTwoBoundary_faceMap_of_support_injOn
/-- If [a vertex map is injective on every face in a chain's support](hyp:hf), then
[mapping the chain commutes with taking its boundary, with coefficients modulo two](goal). -/
lemma modTwoBoundary_faceMap_of_support_injOn {V W : Type*}
    [DecidableEq V] [DecidableEq W] (f : V → W) (c : ModTwoFaceChain V)
    (hf : ∀ s ∈ c.support, Set.InjOn f (s : Set V)) :
    modTwoBoundary (modTwoFaceMap f c) = modTwoFaceMap f (modTwoBoundary c) := by
  exact modTwoLinearMap_eq_of_support
    ((modTwoBoundary (V := W)).comp (modTwoFaceMap f))
    ((modTwoFaceMap f).comp modTwoBoundary) c
    (fun s hs => modTwoBoundary_faceMap_single_of_injOn f s (hf s hs))

-- @node: modTwoAugmentation_faceMap_of_support_injOn
/-- If [a vertex map is injective on every face in a chain's support](hyp:hf), then
[mapping the chain preserves its augmentation, with coefficients modulo two](goal). -/
lemma modTwoAugmentation_faceMap_of_support_injOn {V W : Type*} [DecidableEq W]
    (f : V → W) (c : ModTwoFaceChain V)
    (hf : ∀ s ∈ c.support, Set.InjOn f (s : Set V)) :
    modTwoAugmentation (modTwoFaceMap f c) = modTwoAugmentation c := by
  classical
  conv_lhs => rw [← c.sum_single]
  conv_rhs => rw [← c.sum_single]
  simp only [Finsupp.sum, map_sum, modTwoFaceMap_single, modTwoAugmentation_single]
  apply sum_congr rfl
  intro s hs
  rw [card_image_iff.mpr (hf s hs)]

/-- [The boundary map is unchanged when any procedure for deciding vertex equality
is replaced by the classical one](goal). -/
-- @node: modTwoBoundary_decidableEq
lemma modTwoBoundary_decidableEq {V : Type*} (d : DecidableEq V) :
    @modTwoBoundary V d = @modTwoBoundary V (fun a b => Classical.propDecidable (a = b)) :=
  congrArg (@modTwoBoundary V) (Subsingleton.elim _ _)

-- @node: modTwoFaceMap_decidableEq
/-- [The map on chains induced by a vertex map is unchanged when any procedure for
deciding equality of target vertices is replaced by the classical one](goal). -/
lemma modTwoFaceMap_decidableEq {V W : Type*} (d : DecidableEq W) (f : V → W) :
    @modTwoFaceMap V W d f =
      @modTwoFaceMap V W (fun a b => Classical.propDecidable (a = b)) f :=
  congrArg (fun d => @modTwoFaceMap V W d f) (Subsingleton.elim _ _)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

-- @node: geometricModTwoSubdivision
/-- On chains of finite subsets of [a real normed vector space](hyp:E),
[geometric subdivision with coefficients modulo two](goal) first subdivides each
face into abstract flags and then replaces each vertex of a flag by its barycenter. -/
def geometricModTwoSubdivision : ModTwoFaceChain E →ₗ[ZMod 2] ModTwoFaceChain E :=
  (modTwoFaceMap barycenter).comp modTwoSubdivision

-- @node: geometricModTwoSubdivision_apply
/-- [Geometric subdivision of a chain equals its abstract subdivision followed by
the map that replaces each face by its barycenter](goal). -/
lemma geometricModTwoSubdivision_apply (c : ModTwoFaceChain E) :
    geometricModTwoSubdivision c = modTwoFaceMap barycenter (modTwoSubdivision c) := rfl

/-- If [every nonempty face in a chain's support belongs to a geometric simplicial
complex](hyp:hc) and [an abstract face occurs in the subdivided chain](hyp:ht), then
[each vertex of that abstract face is a face of the original complex](goal). -/
-- @node: modTwoSubdivision_support_vertices
lemma modTwoSubdivision_support_vertices (Q : Geometry.SimplicialComplex ℝ E)
    (c : ModTwoFaceChain E)
    (hc : ∀ s ∈ c.support, s.Nonempty → s ∈ Q.faces)
    {t : Finset (Finset E)} (ht : t ∈ (modTwoSubdivision c).support) :
    ∀ u ∈ t, u ∈ Q.faces := by
  obtain ⟨s, hs, hst⟩ := modTwoLinearMap_support modTwoSubdivision c ht
  simp only [modTwoSubdivision_single, one_smul] at hst
  intro u hu
  obtain ⟨hne, hsub⟩ := (modTwoSubdivisionFace_support s hst).2.1 u hu
  exact Q.down_closed (hc s hs (hne.mono hsub)) hsub hne

-- @node: modTwoSubdivision_support_barycenter_injOn
/-- If [every nonempty face in a chain's support belongs to a geometric simplicial
complex](hyp:hc) and [an abstract face occurs in the subdivided chain](hyp:ht), then
[distinct vertices of that abstract face have distinct barycenters](goal). -/
lemma modTwoSubdivision_support_barycenter_injOn (Q : Geometry.SimplicialComplex ℝ E)
    (c : ModTwoFaceChain E)
    (hc : ∀ s ∈ c.support, s.Nonempty → s ∈ Q.faces)
    {t : Finset (Finset E)} (ht : t ∈ (modTwoSubdivision c).support) :
    Set.InjOn barycenter (t : Set (Finset E)) := by
  intro u hu w hw he
  exact barycenter_injective_on_faces
    (modTwoSubdivision_support_vertices Q c hc ht u hu)
    (modTwoSubdivision_support_vertices Q c hc ht w hw) he

-- @node: modTwoBoundary_geometricSubdivision
/-- If [every nonempty face in a chain's support belongs to a geometric simplicial
complex](hyp:hc), then [geometric subdivision commutes with taking the chain's
boundary, with coefficients modulo two](goal). -/
lemma modTwoBoundary_geometricSubdivision (Q : Geometry.SimplicialComplex ℝ E)
    (c : ModTwoFaceChain E)
    (hc : ∀ s ∈ c.support, s.Nonempty → s ∈ Q.faces) :
    modTwoBoundary (geometricModTwoSubdivision c) =
      geometricModTwoSubdivision (modTwoBoundary c) := by
  rw [geometricModTwoSubdivision_apply, modTwoBoundary_faceMap_of_support_injOn
    barycenter _ (fun _ ht => modTwoSubdivision_support_barycenter_injOn Q c hc ht),
    modTwoBoundary_subdivision, geometricModTwoSubdivision_apply]

-- @node: modTwoAugmentation_geometricSubdivision
/-- If [every nonempty face in a chain's support belongs to a geometric simplicial
complex](hyp:hc), then [geometric subdivision preserves the chain's augmentation,
with coefficients modulo two](goal). -/
lemma modTwoAugmentation_geometricSubdivision (Q : Geometry.SimplicialComplex ℝ E)
    (c : ModTwoFaceChain E)
    (hc : ∀ s ∈ c.support, s.Nonempty → s ∈ Q.faces) :
    modTwoAugmentation (geometricModTwoSubdivision c) = modTwoAugmentation c := by
  rw [geometricModTwoSubdivision_apply, modTwoAugmentation_faceMap_of_support_injOn
    barycenter _ (fun _ ht => modTwoSubdivision_support_barycenter_injOn Q c hc ht),
    modTwoAugmentation_subdivision]

-- @node: geometricModTwoSubdivision_support
/-- If [every face in a chain's support belongs to a geometric simplicial
complex](hyp:hc) and [a face occurs in the geometrically subdivided chain](hyp:ht),
then [it belongs to the subdivided complex and has the same number of vertices as
some face in the original chain's support](goal). -/
lemma geometricModTwoSubdivision_support (Q : Geometry.SimplicialComplex ℝ E)
    (c : ModTwoFaceChain E) (hc : ∀ s ∈ c.support, s ∈ Q.faces)
    {t : Finset E} (ht : t ∈ (geometricModTwoSubdivision c).support) :
    t ∈ (sd Q).faces ∧ ∃ s ∈ c.support, t.card = s.card := by
  obtain ⟨u, hu, rfl⟩ := modTwoFaceMap_support barycenter (modTwoSubdivision c) ht
  obtain ⟨s, hs, hsu⟩ := modTwoLinearMap_support modTwoSubdivision c hu
  simp only [modTwoSubdivision_single, one_smul] at hsu
  obtain ⟨hcard, hsub, hchain⟩ := modTwoSubdivisionFace_support s hsu
  have hufaces : ∀ v ∈ u, v ∈ Q.faces :=
    modTwoSubdivision_support_vertices Q c (fun s hs _ => hc s hs) hu
  have hune : u.Nonempty := card_pos.mp (by
    rw [hcard]
    exact card_pos.mpr (Q.nonempty_of_mem_faces (hc s hs)))
  refine ⟨⟨u, ⟨hune, hufaces, hchain⟩, rfl⟩, s, hs, ?_⟩
  rw [card_image_iff.mpr
    (modTwoSubdivision_support_barycenter_injOn Q c (fun s hs _ => hc s hs) hu), hcard]

-- @node: geometricModTwoSubdivision_equivariant
/-- For a simplicial group action, if [every face in a chain's support belongs to
the complex](hyp:hc), then [acting by a group element before geometric subdivision
gives the same chain as acting after subdivision](goal). -/
lemma geometricModTwoSubdivision_equivariant {G : Type*} [Group G]
    {Q : Geometry.SimplicialComplex ℝ E} (α : SimplicialAction G Q) (g : G)
    (c : ModTwoFaceChain E) (hc : ∀ s ∈ c.support, s ∈ Q.faces) :
    geometricModTwoSubdivision (modTwoFaceMap (α.action g) c) =
      modTwoFaceMap (α.action g) (geometricModTwoSubdivision c) := by
  rw [geometricModTwoSubdivision_apply, modTwoSubdivision_faceMap _ (α.action g).injective,
    modTwoFaceMap_comp, geometricModTwoSubdivision_apply, modTwoFaceMap_comp]
  apply modTwoLinearMap_eq_of_support
  intro t ht
  simp only [modTwoFaceMap_single]
  congr 1
  apply image_congr
  intro s hs
  exact (α.map_barycenter g
    (modTwoSubdivision_support_vertices Q c (fun s hs _ => hc s hs) ht s hs)).symm

-- @node: geometricModTwoSubdivisionIterate
/-- For chains in [a real normed vector space](hyp:E), [repeated geometric
subdivision with coefficients modulo two](goal) is [the identity at zero
iterations](step:1) and [one geometric subdivision after the preceding iterations
at each successor](step:2). -/
def geometricModTwoSubdivisionIterate : ℕ → ModTwoFaceChain E →ₗ[ZMod 2] ModTwoFaceChain E
  | 0 => LinearMap.id
  | k + 1 => geometricModTwoSubdivision.comp (geometricModTwoSubdivisionIterate k)

-- @node: geometricModTwoSubdivisionIterate_zero
/-- [Zero iterations of geometric subdivision leave a chain unchanged](goal). -/
@[simp] lemma geometricModTwoSubdivisionIterate_zero (c : ModTwoFaceChain E) :
    geometricModTwoSubdivisionIterate 0 c = c := rfl

-- @node: geometricModTwoSubdivisionIterate_succ
/-- [Performing one more iteration of geometric subdivision equals subdividing
the chain obtained from the preceding iterations](goal). -/
lemma geometricModTwoSubdivisionIterate_succ (k : ℕ) (c : ModTwoFaceChain E) :
    geometricModTwoSubdivisionIterate (k + 1) c =
      geometricModTwoSubdivision (geometricModTwoSubdivisionIterate k c) := rfl

-- @node: geometricModTwoSubdivisionIterate_support
/-- If [every face in a chain's support belongs to a geometric simplicial
complex](hyp:hc) and [a face occurs after a given number of geometric
subdivisions](hyp:ht), then [it belongs to the equally iterated subdivision of the
complex and has the same number of vertices as some face in the original chain's
support](goal). -/
lemma geometricModTwoSubdivisionIterate_support (Q : Geometry.SimplicialComplex ℝ E)
    (c : ModTwoFaceChain E) (hc : ∀ s ∈ c.support, s ∈ Q.faces) (k : ℕ)
    {t : Finset E} (ht : t ∈ (geometricModTwoSubdivisionIterate k c).support) :
    t ∈ (sdIterate Q k).faces ∧ ∃ s ∈ c.support, t.card = s.card := by
  induction k generalizing t with
  | zero => exact ⟨hc t ht, t, ht, rfl⟩
  | succ k ih =>
      obtain ⟨htface, u, hu, htu⟩ := geometricModTwoSubdivision_support (sdIterate Q k)
        (geometricModTwoSubdivisionIterate k c) (fun u hu => (ih hu).1) ht
      obtain ⟨s, hs, hus⟩ := (ih hu).2
      exact ⟨htface, s, hs, htu.trans hus⟩

-- @node: modTwoBoundary_geometricSubdivisionIterate
/-- If [every face in a chain's support belongs to a geometric simplicial
complex](hyp:hc), then [any number of geometric subdivisions commutes with taking
the chain's boundary, with coefficients modulo two](goal). -/
lemma modTwoBoundary_geometricSubdivisionIterate (Q : Geometry.SimplicialComplex ℝ E)
    (c : ModTwoFaceChain E) (hc : ∀ s ∈ c.support, s ∈ Q.faces) (k : ℕ) :
    modTwoBoundary (geometricModTwoSubdivisionIterate k c) =
      geometricModTwoSubdivisionIterate k (modTwoBoundary c) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [geometricModTwoSubdivisionIterate_succ,
        modTwoBoundary_geometricSubdivision (sdIterate Q k) _
          (fun s hs _ => (geometricModTwoSubdivisionIterate_support Q c hc k hs).1),
        ih, geometricModTwoSubdivisionIterate_succ]

-- @node: modTwoAugmentation_geometricSubdivisionIterate
/-- If [every face in a chain's support belongs to a geometric simplicial
complex](hyp:hc), then [any number of geometric subdivisions preserves the chain's
augmentation, with coefficients modulo two](goal). -/
lemma modTwoAugmentation_geometricSubdivisionIterate (Q : Geometry.SimplicialComplex ℝ E)
    (c : ModTwoFaceChain E) (hc : ∀ s ∈ c.support, s ∈ Q.faces) (k : ℕ) :
    modTwoAugmentation (geometricModTwoSubdivisionIterate k c) = modTwoAugmentation c := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [geometricModTwoSubdivisionIterate_succ,
        modTwoAugmentation_geometricSubdivision (sdIterate Q k) _
          (fun s hs _ => (geometricModTwoSubdivisionIterate_support Q c hc k hs).1), ih]

-- @node: simplicialAction_iterate_action
/-- [The action on the ambient space induced by a simplicial group action on any
iterated subdivision is the original action](goal). -/
lemma simplicialAction_iterate_action {G : Type*} [Group G]
    {Q : Geometry.SimplicialComplex ℝ E} (α : SimplicialAction G Q) (k : ℕ) :
    (α.iterate k).action = α.action := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih

-- @node: geometricModTwoSubdivisionIterate_equivariant
/-- For a simplicial group action, if [every face in a chain's support belongs to
the complex](hyp:hc), then [acting by a group element commutes with any number of
geometric subdivisions of the chain](goal). -/
lemma geometricModTwoSubdivisionIterate_equivariant {G : Type*} [Group G]
    {Q : Geometry.SimplicialComplex ℝ E} (α : SimplicialAction G Q) (g : G)
    (c : ModTwoFaceChain E) (hc : ∀ s ∈ c.support, s ∈ Q.faces) (k : ℕ) :
    geometricModTwoSubdivisionIterate k (modTwoFaceMap (α.action g) c) =
      modTwoFaceMap (α.action g) (geometricModTwoSubdivisionIterate k c) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [geometricModTwoSubdivisionIterate_succ, ih, geometricModTwoSubdivisionIterate_succ]
      have h := geometricModTwoSubdivision_equivariant (α.iterate k) g
        (geometricModTwoSubdivisionIterate k c)
        (fun s hs => (geometricModTwoSubdivisionIterate_support Q c hc k hs).1)
      simpa only [simplicialAction_iterate_action] using h

-- @node: signedGeometricSubdivisionIterate_neg
/-- If [every face in a chain's support belongs to the signed geometric
complex](hyp:hc), then [negating all vertices commutes with any number of geometric
subdivisions of the chain](goal). -/
lemma signedGeometricSubdivisionIterate_neg {n : ℕ}
    (c : ModTwoFaceChain (Fin n → ℝ))
    (hc : ∀ s ∈ c.support, s ∈ (signedGeometricComplex n).faces) (k : ℕ) :
    geometricModTwoSubdivisionIterate k (modTwoFaceMap (fun x : Fin n → ℝ => -x) c) =
      modTwoFaceMap (fun x : Fin n → ℝ => -x) (geometricModTwoSubdivisionIterate k c) := by
  let g : AntipodalGroup := Multiplicative.ofAdd (1 : ZMod 2)
  have hg : g ≠ 1 := by decide
  have he : ((signedAntipodalAction n).action g : (Fin n → ℝ) → (Fin n → ℝ)) =
      (fun x => -x) := funext (antipodalRepresentation_nonidentity _ hg)
  simpa only [he, modTwoFaceMap_decidableEq] using
    geometricModTwoSubdivisionIterate_equivariant (signedAntipodalAction n) g c hc k

/-- For [ambient dimension n](hyp:n), [a number r of subdivisions](hyp:r), and
[hemisphere dimension k](hyp:k), [the subdivided signed hemisphere chain](goal)
is obtained by applying r geometric subdivisions to the signed geometric
hemisphere chain of dimension k, with coefficients modulo two. -/
-- @node: subdividedSignedHemisphereChain
def subdividedSignedHemisphereChain (n r k : ℕ) : ModTwoFaceChain (Fin n → ℝ) :=
  geometricModTwoSubdivisionIterate r (signedGeometricHemisphereChain n k)

-- @node: subdividedSignedHemisphereChain_support
/-- If [a face occurs in the signed hemisphere chain of dimension k after r
subdivisions](hyp:hs), then [it belongs to the r-times subdivided signed geometric
complex and has exactly k plus one vertices](goal). -/
lemma subdividedSignedHemisphereChain_support (n r k : ℕ)
    {s : Finset (Fin n → ℝ)} (hs : s ∈ (subdividedSignedHemisphereChain n r k).support) :
    s ∈ (sdIterate (signedGeometricComplex n) r).faces ∧ s.card = k + 1 := by
  obtain ⟨hsface, t, ht, hst⟩ := geometricModTwoSubdivisionIterate_support
    (signedGeometricComplex n) (signedGeometricHemisphereChain n k)
    (fun t ht => (signedGeometricHemisphereChain_support n k ht).1) r hs
  exact ⟨hsface, hst.trans (signedGeometricHemisphereChain_support n k ht).2⟩

-- @node: subdividedSignedHemisphereChain_boundary
/-- If [k plus one is less than the ambient dimension](hyp:hk), then [the boundary
of the subdivided signed hemisphere chain of dimension k plus one is the sum,
modulo two, of the subdivided hemisphere chain of dimension k and its image under
vertex negation](goal). -/
lemma subdividedSignedHemisphereChain_boundary (n r k : ℕ) (hk : k + 1 < n) :
    modTwoBoundary (subdividedSignedHemisphereChain n r (k + 1)) =
      subdividedSignedHemisphereChain n r k +
        modTwoFaceMap (fun x : Fin n → ℝ => -x) (subdividedSignedHemisphereChain n r k) := by
  have hstep := signedGeometricHemisphereChain_boundary n k hk
  simp only [modTwoBoundary_decidableEq, modTwoFaceMap_decidableEq] at hstep ⊢
  unfold subdividedSignedHemisphereChain
  rw [modTwoBoundary_geometricSubdivisionIterate (signedGeometricComplex n) _
      (fun s hs => (signedGeometricHemisphereChain_support n (k + 1) hs).1),
    hstep, map_add]
  have h := signedGeometricSubdivisionIterate_neg (signedGeometricHemisphereChain n k)
    (fun s hs => (signedGeometricHemisphereChain_support n k hs).1) r
  simpa only [modTwoFaceMap_decidableEq] using
    congrArg (fun x => geometricModTwoSubdivisionIterate r
      (signedGeometricHemisphereChain n k) + x) h

-- @node: subdividedSignedHemisphereChain_bottom_augmentation
/-- If [the ambient dimension is positive](hyp:hn), then [the augmentation of the
zero-dimensional signed hemisphere chain is one after any number of geometric
subdivisions](goal). -/
lemma subdividedSignedHemisphereChain_bottom_augmentation {n : ℕ} (hn : 0 < n) (r : ℕ) :
    modTwoAugmentation (subdividedSignedHemisphereChain n r 0) = 1 := by
  rw [subdividedSignedHemisphereChain,
    modTwoAugmentation_geometricSubdivisionIterate (signedGeometricComplex n) _
      (fun s hs => (signedGeometricHemisphereChain_support n 0 hs).1),
    signedGeometricHemisphereChain_bottom_augmentation hn]

end
end Papers.TbsNeuralCausalPi.Antipodal

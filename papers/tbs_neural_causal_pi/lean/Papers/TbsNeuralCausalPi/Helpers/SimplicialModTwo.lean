module
public import Papers.TbsNeuralCausalPi.Helpers.AntipodalParity
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
/-! # Augmented mod-two simplicial boundary

Chains have finite support on finite vertex sets, including the empty face.
The boundary deletes one vertex. Pairing the two orders of deletion proves
that its square vanishes. Injective vertex maps commute with this boundary.
The restriction to sphere subdivisions and the construction of a PL-induced
chain map remain separate obligations.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi.Antipodal
noncomputable section
open Finset

-- @node: ModTwoFaceChain
/-- For [a vertex set](hyp:V), a [mod-two face chain](goal) assigns coefficients
zero or one to finitely many finite sets of vertices, including the empty set. -/
abbrev ModTwoFaceChain (V : Type*) := Finset V →₀ ZMod 2

-- @node: modTwo_sum_erase_symmetric
/-- If [a function of two vertices is symmetric](hyp:hf), then [its sum over
all ordered pairs of distinct vertices in a finite set is zero](goal), when
the values lie in a module over the field with two elements. -/
lemma modTwo_sum_erase_symmetric {V M : Type*} [DecidableEq V]
    [AddCommGroup M] [Module (ZMod 2) M] (s : Finset V) (f : V → V → M)
    (hf : ∀ v w, f v w = f w v) :
    (∑ v ∈ s, ∑ w ∈ s.erase v, f v w) = 0 := by
  classical
  let P := (s ×ˢ s).filter (fun p => p.1 ≠ p.2)
  have he : (∑ v ∈ s, ∑ w ∈ s.erase v, f v w) =
      ∑ p ∈ P, f p.1 p.2 := by
    simp only [P, sum_filter, sum_product]
    apply sum_congr rfl
    intro v hv
    rw [← sum_filter]
    congr 1
    ext w
    simp [and_comm, ne_comm]
  rw [he]
  apply sum_involution (fun p _ => (p.2, p.1))
  · intro p hp
    rw [hf p.2 p.1]
    exact ZModModule.add_self _
  · intro p hp _ heq
    exact (mem_filter.mp hp).2 (congrArg Prod.fst heq).symm
  · intro p hp
    simpa [P, and_comm, ne_comm] using hp
  · intro p hp
    rfl

-- @node: modTwoBoundary
/-- The [mod-two boundary operator](goal) sends each face to the sum of the
faces obtained by deleting one vertex, and extends this rule linearly to chains. -/
def modTwoBoundary {V : Type*} [DecidableEq V] :
    ModTwoFaceChain V →ₗ[ZMod 2] ModTwoFaceChain V :=
  Finsupp.linearCombination (ZMod 2)
    (fun s => ∑ v ∈ s, Finsupp.single (s.erase v) 1)

-- @node: modTwoBoundary_single
/-- [The boundary of a face with a given mod-two coefficient is that coefficient
times the sum of all faces obtained by deleting one vertex](goal). -/
@[simp] lemma modTwoBoundary_single {V : Type*} [DecidableEq V]
    (s : Finset V) (r : ZMod 2) :
    modTwoBoundary (Finsupp.single s r) =
      r • ∑ v ∈ s, Finsupp.single (s.erase v) 1 := by
  simp [modTwoBoundary]

-- @node: modTwoBoundary_empty
/-- [The boundary of the empty face is zero for either mod-two coefficient](goal). -/
@[simp] lemma modTwoBoundary_empty {V : Type*} [DecidableEq V] (r : ZMod 2) :
    modTwoBoundary (Finsupp.single (∅ : Finset V) r) = 0 := by
  simp

-- @node: modTwoBoundary_vertex
/-- [The boundary of a single-vertex face is the empty face with the same
mod-two coefficient](goal). -/
@[simp] lemma modTwoBoundary_vertex {V : Type*} [DecidableEq V]
    (v : V) (r : ZMod 2) :
    modTwoBoundary (Finsupp.single {v} r) = Finsupp.single ∅ r := by
  simp

-- @node: modTwoBoundary_sq_single
/-- [Taking the boundary twice of a face with any mod-two coefficient gives
the zero chain](goal). -/
lemma modTwoBoundary_sq_single {V : Type*} [DecidableEq V]
    (s : Finset V) (r : ZMod 2) :
    modTwoBoundary (modTwoBoundary (Finsupp.single s r)) = 0 := by
  rw [modTwoBoundary_single, map_smul, map_sum]
  simp only [modTwoBoundary_single, one_smul]
  rw [modTwo_sum_erase_symmetric s
    (fun v w => Finsupp.single ((s.erase v).erase w) (1 : ZMod 2))
    (fun v w => by rw [erase_right_comm])]
  exact smul_zero _

-- @node: modTwoBoundary_sq
/-- [Taking the boundary twice of any mod-two face chain gives the zero chain](goal). -/
lemma modTwoBoundary_sq {V : Type*} [DecidableEq V] (c : ModTwoFaceChain V) :
    modTwoBoundary (modTwoBoundary c) = 0 := by
  have h : (modTwoBoundary (V := V)).comp modTwoBoundary = 0 := by
    apply Finsupp.lhom_ext
    intro s r
    exact modTwoBoundary_sq_single s r
  exact LinearMap.congr_fun h c

-- @node: modTwoFaceMap
/-- For [a map between vertex sets](hyp:f), the [induced linear map on mod-two
face chains](goal) replaces each face by its image under the vertex map. -/
def modTwoFaceMap {V W : Type*} [DecidableEq W] (f : V → W) :
    ModTwoFaceChain V →ₗ[ZMod 2] ModTwoFaceChain W :=
  Finsupp.linearCombination (ZMod 2) (fun s => Finsupp.single (s.image f) 1)

-- @node: modTwoFaceMap_single
/-- [Mapping a face with a given mod-two coefficient produces its image face
with the same coefficient](goal). -/
@[simp] lemma modTwoFaceMap_single {V W : Type*} [DecidableEq W]
    (f : V → W) (s : Finset V) (r : ZMod 2) :
    modTwoFaceMap f (Finsupp.single s r) = Finsupp.single (s.image f) r := by
  simp [modTwoFaceMap]

-- @node: modTwoFaceMap_id
/-- [The identity map on vertices leaves every mod-two face chain unchanged](goal). -/
lemma modTwoFaceMap_id {V : Type*} [DecidableEq V] (c : ModTwoFaceChain V) :
    modTwoFaceMap id c = c := by
  have h : modTwoFaceMap (id : V → V) = LinearMap.id := by
    apply Finsupp.lhom_ext
    intro s r
    simp
  exact LinearMap.congr_fun h c

-- @node: modTwoFaceMap_comp
/-- [Mapping a mod-two face chain successively through two vertex maps gives
the same chain as mapping it through their composition](goal). -/
lemma modTwoFaceMap_comp {U V W : Type*} [DecidableEq V] [DecidableEq W]
    (f : U → V) (g : V → W) (c : ModTwoFaceChain U) :
    modTwoFaceMap g (modTwoFaceMap f c) = modTwoFaceMap (g ∘ f) c := by
  have h : (modTwoFaceMap g).comp (modTwoFaceMap f) = modTwoFaceMap (g ∘ f) := by
    apply Finsupp.lhom_ext
    intro s r
    simp [image_image]
  exact LinearMap.congr_fun h c

-- @node: modTwoBoundary_faceMap_single
/-- If [the vertex map is injective](hyp:hf), then [taking the boundary of
the image of a face with any mod-two coefficient equals mapping its boundary](goal). -/
lemma modTwoBoundary_faceMap_single {V W : Type*} [DecidableEq V] [DecidableEq W]
    (f : V → W) (hf : Function.Injective f) (s : Finset V) (r : ZMod 2) :
    modTwoBoundary (modTwoFaceMap f (Finsupp.single s r)) =
      modTwoFaceMap f (modTwoBoundary (Finsupp.single s r)) := by
  simp only [modTwoFaceMap_single, modTwoBoundary_single, map_smul, map_sum,
    modTwoFaceMap_single]
  congr 1
  rw [sum_image]
  · apply sum_congr rfl
    intro v hv
    rw [Finset.image_erase hf]
  · exact fun _ _ _ _ h => hf h

-- @node: modTwoBoundary_faceMap
/-- If [the vertex map is injective](hyp:hf), then [mapping any mod-two face
chain commutes with taking its boundary](goal). -/
lemma modTwoBoundary_faceMap {V W : Type*} [DecidableEq V] [DecidableEq W]
    (f : V → W) (hf : Function.Injective f) (c : ModTwoFaceChain V) :
    modTwoBoundary (modTwoFaceMap f c) = modTwoFaceMap f (modTwoBoundary c) := by
  have h : (modTwoBoundary (V := W)).comp (modTwoFaceMap f) =
      (modTwoFaceMap f).comp modTwoBoundary := by
    apply Finsupp.lhom_ext
    exact modTwoBoundary_faceMap_single f hf
  exact LinearMap.congr_fun h c

-- @node: modTwoAugmentation
/-- The [mod-two augmentation](goal) sums the coefficients of all single-vertex
faces; faces with any other number of vertices, including the empty face,
contribute zero. -/
def modTwoAugmentation {V : Type*} : ModTwoFaceChain V →ₗ[ZMod 2] ZMod 2 :=
  Finsupp.linearCombination (ZMod 2) (fun s => if s.card = 1 then 1 else 0)

-- @node: modTwoAugmentation_single
/-- [The augmentation of a face with a given coefficient is that coefficient
if the face has exactly one vertex, and zero otherwise](goal). -/
@[simp] lemma modTwoAugmentation_single {V : Type*} (s : Finset V) (r : ZMod 2) :
    modTwoAugmentation (Finsupp.single s r) = if s.card = 1 then r else 0 := by
  simp [modTwoAugmentation]

-- @node: modTwoAugmentation_boundary
/-- [The augmentation of the boundary of any mod-two face chain is zero](goal). -/
lemma modTwoAugmentation_boundary {V : Type*} [DecidableEq V]
    (c : ModTwoFaceChain V) : modTwoAugmentation (modTwoBoundary c) = 0 := by
  have h : (modTwoAugmentation (V := V)).comp modTwoBoundary = 0 := by
    apply Finsupp.lhom_ext
    intro s r
    simp only [LinearMap.comp_apply, modTwoBoundary_single, map_smul, map_sum,
      modTwoAugmentation_single]
    have he : (∑ v ∈ s, if (s.erase v).card = 1 then (1 : ZMod 2) else 0) = 0 := by
      by_cases hc : s.card = 2
      · have hterm : ∀ v ∈ s, (s.erase v).card = 1 := by
          intro v hv
          rw [card_erase_of_mem hv, hc]
        simp only [sum_congr rfl (fun v hv => if_pos (hterm v hv)), sum_const,
          nsmul_eq_mul, hc]
        exact ZMod.natCast_self 2
      · apply sum_eq_zero
        intro v hv
        have hcard := card_erase_of_mem hv
        have hpos := card_pos.mpr ⟨v, hv⟩
        rw [if_neg (by omega)]
    rw [he, smul_zero]
    rfl
  exact LinearMap.congr_fun h c

-- @node: modTwoAugmentation_faceMap
/-- If [the vertex map is injective](hyp:hf), then [mapping a mod-two face
chain preserves its augmentation](goal). -/
lemma modTwoAugmentation_faceMap {V W : Type*} [DecidableEq W]
    (f : V → W) (hf : Function.Injective f) (c : ModTwoFaceChain V) :
    modTwoAugmentation (modTwoFaceMap f c) = modTwoAugmentation c := by
  have h : (modTwoAugmentation (V := W)).comp (modTwoFaceMap f) =
      modTwoAugmentation := by
    apply Finsupp.lhom_ext
    intro s r
    simp [card_image_of_injective s hf]
  exact LinearMap.congr_fun h c

-- @node: modTwoCone
/-- For [a chosen apex vertex](hyp:v), the [cone operator on mod-two face
chains](goal) sends a face to zero if it already contains the apex and otherwise
adds the apex to the face, extending this rule linearly. -/
def modTwoCone {V : Type*} [DecidableEq V] (v : V) :
    ModTwoFaceChain V →ₗ[ZMod 2] ModTwoFaceChain V :=
  Finsupp.linearCombination (ZMod 2)
    (fun s => if v ∈ s then 0 else Finsupp.single (insert v s) 1)

-- @node: modTwoCone_single
/-- [Coning a face with a given mod-two coefficient gives zero if the apex
already belongs to the face, and otherwise gives the face with the apex added
and the same coefficient](goal). -/
@[simp] lemma modTwoCone_single {V : Type*} [DecidableEq V]
    (v : V) (s : Finset V) (r : ZMod 2) :
    modTwoCone v (Finsupp.single s r) =
      if v ∈ s then 0 else Finsupp.single (insert v s) r := by
  by_cases hv : v ∈ s <;> simp [modTwoCone, hv]

-- @node: modTwoBoundary_cone_single
/-- [For a face with coefficient one, the boundary of its cone plus the cone
of its boundary equals the original face](goal), including when the face is empty. -/
lemma modTwoBoundary_cone_single {V : Type*} [DecidableEq V]
    (v : V) (s : Finset V) :
    modTwoBoundary (modTwoCone v (Finsupp.single s 1)) +
      modTwoCone v (modTwoBoundary (Finsupp.single s 1)) = Finsupp.single s 1 := by
  by_cases hv : v ∈ s
  · simp only [modTwoCone_single, if_pos hv, map_zero, zero_add,
      modTwoBoundary_single, one_smul, map_sum]
    rw [sum_eq_single v]
    · rw [if_neg (notMem_erase v s), insert_erase hv]
    · intro w hw hwv
      simp [mem_erase, Ne.symm hwv, hv]
    · exact fun hn => False.elim (hn hv)
  · simp only [modTwoCone_single, if_neg hv, modTwoBoundary_single, one_smul,
      map_sum]
    rw [sum_insert hv, erase_insert hv]
    have he : (∑ w ∈ s, Finsupp.single ((insert v s).erase w) (1 : ZMod 2)) =
        ∑ w ∈ s, modTwoCone v (Finsupp.single (s.erase w) 1) := by
      apply sum_congr rfl
      intro w hw
      have hwv : w ≠ v := by intro h; exact hv (h ▸ hw)
      rw [modTwoCone_single, if_neg (fun h => hv (mem_of_mem_erase h)),
        erase_insert_of_ne hwv.symm]
    simp only [modTwoCone_single] at he
    rw [he, add_assoc, ZModModule.add_self, add_zero]

-- @node: modTwoBoundary_cone
/-- [For any mod-two face chain and any apex, the boundary of its cone plus
the cone of its boundary equals the original chain](goal). -/
lemma modTwoBoundary_cone {V : Type*} [DecidableEq V]
    (v : V) (c : ModTwoFaceChain V) :
    modTwoBoundary (modTwoCone v c) + modTwoCone v (modTwoBoundary c) = c := by
  have h : (modTwoBoundary (V := V)).comp (modTwoCone v) +
      (modTwoCone v).comp modTwoBoundary = LinearMap.id := by
    apply Finsupp.lhom_ext
    intro s r
    have he : Finsupp.single s r = r • Finsupp.single s (1 : ZMod 2) := by simp
    rw [he]
    simp only [map_smul, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.id_coe, id_eq]
    rw [modTwoBoundary_cone_single]
  exact LinearMap.congr_fun h c

-- @node: modTwoBoundary_cone_cycle
/-- If [a mod-two face chain has zero boundary](hyp:hc), then [the boundary
of its cone at any apex equals the original chain](goal). -/
lemma modTwoBoundary_cone_cycle {V : Type*} [DecidableEq V]
    (v : V) (c : ModTwoFaceChain V) (hc : modTwoBoundary c = 0) :
    modTwoBoundary (modTwoCone v c) = c := by
  simpa only [hc, map_zero, add_zero] using modTwoBoundary_cone v c

-- @node: modTwoLinearMap_support
/-- If [an index has a nonzero coefficient in the image of a mod-two chain
under a linear map](hyp:ht), then [some index with a nonzero input coefficient
has a unit chain whose image has a nonzero coefficient at that output index](goal). -/
lemma modTwoLinearMap_support {A B : Type*}
    (T : (A →₀ ZMod 2) →ₗ[ZMod 2] (B →₀ ZMod 2))
    (c : A →₀ ZMod 2) {t : B} (ht : t ∈ (T c).support) :
    ∃ s ∈ c.support, t ∈ (T (Finsupp.single s 1)).support := by
  classical
  have he : T c = ∑ s ∈ c.support, c s • T (Finsupp.single s 1) := by
    conv_lhs => rw [← c.sum_single]
    simp only [Finsupp.sum, map_sum]
    apply sum_congr rfl
    intro s hs
    have hsingle : Finsupp.single s (c s) = c s • Finsupp.single s (1 : ZMod 2) := by
      simp
    rw [hsingle, map_smul]
  rw [he] at ht
  obtain ⟨s, hs, hst⟩ := Finsupp.mem_support_finsetSum t ht
  exact ⟨s, hs, Finsupp.support_smul hst⟩

-- @node: modTwoBoundary_support
/-- If [a face has a nonzero coefficient in the boundary of a mod-two chain](hyp:ht),
then [it is obtained by deleting one vertex from a face with a nonzero
coefficient in the original chain](goal). -/
lemma modTwoBoundary_support {V : Type*} [DecidableEq V]
    (c : ModTwoFaceChain V) {t : Finset V} (ht : t ∈ (modTwoBoundary c).support) :
    ∃ s ∈ c.support, ∃ v ∈ s, t = s.erase v := by
  obtain ⟨s, hs, hst⟩ := modTwoLinearMap_support modTwoBoundary c ht
  simp only [modTwoBoundary_single, one_smul] at hst
  obtain ⟨v, hv, hvt⟩ := Finsupp.mem_support_finsetSum t hst
  exact ⟨s, hs, v, hv, (Finsupp.mem_support_single _ _ _).mp hvt |>.1⟩

-- @node: modTwoFaceMap_support
/-- If [a face has a nonzero coefficient after mapping a mod-two chain through
a vertex map](hyp:ht), then [it is the image of a face with a nonzero coefficient
in the original chain](goal). -/
lemma modTwoFaceMap_support {V W : Type*} [DecidableEq W]
    (f : V → W) (c : ModTwoFaceChain V) {t : Finset W}
    (ht : t ∈ (modTwoFaceMap f c).support) :
    ∃ s ∈ c.support, t = s.image f := by
  obtain ⟨s, hs, hst⟩ := modTwoLinearMap_support (modTwoFaceMap f) c ht
  rw [modTwoFaceMap_single] at hst
  exact ⟨s, hs, (Finsupp.mem_support_single _ _ _).mp hst |>.1⟩

-- @node: modTwoCone_support
/-- If [a face has a nonzero coefficient in the cone of a mod-two chain](hyp:ht),
then [it is obtained by adding the apex to a face with a nonzero coefficient
in the original chain that does not already contain the apex](goal). -/
lemma modTwoCone_support {V : Type*} [DecidableEq V]
    (v : V) (c : ModTwoFaceChain V) {t : Finset V}
    (ht : t ∈ (modTwoCone v c).support) :
    ∃ s ∈ c.support, v ∉ s ∧ t = insert v s := by
  obtain ⟨s, hs, hst⟩ := modTwoLinearMap_support (modTwoCone v) c ht
  rw [modTwoCone_single] at hst
  by_cases hv : v ∈ s
  · simp [hv] at hst
  · rw [if_neg hv] at hst
    exact ⟨s, hs, hv, (Finsupp.mem_support_single _ _ _).mp hst |>.1⟩

-- @node: modTwoBoundary_homogeneous
/-- If [every face with a nonzero coefficient in a mod-two chain has one more
than a fixed number of vertices](hyp:hc), then [every face with a nonzero
coefficient in its boundary has exactly that fixed number of vertices](goal). -/
lemma modTwoBoundary_homogeneous {V : Type*} [DecidableEq V]
    (c : ModTwoFaceChain V) (k : ℕ)
    (hc : ∀ s ∈ c.support, s.card = k + 1) :
    ∀ t ∈ (modTwoBoundary c).support, t.card = k := by
  intro t ht
  obtain ⟨s, hs, v, hv, rfl⟩ := modTwoBoundary_support c ht
  rw [card_erase_of_mem hv, hc s hs]
  omega

end
end Papers.TbsNeuralCausalPi.Antipodal

module

public import Papers.OaiPairedStatesHamiltonian.Helpers.RotationEulerBound
public import Papers.OaiPairedStatesHamiltonian.Helpers.CycleCap

/-! Euler bounds for regions in a sphere triangulation. -/

@[expose] public section
namespace OaiPairedStatesHamiltonian


namespace SphereMap
open Classical
attribute [local instance] propDecidable
variable (M : SphereMap)

set_option backward.isDefEq.respectTransparency false in
/-- If [the map is a sphere triangulation](hyp:hM) and [a retained region dart has
its original face outside the chosen region](hyp:hd), then [the region rotation
has at least one more face orbit than the number of original faces in the region](goal). -/
-- @node: SphereMap.region_face_orbit_lower_bound
lemma region_face_orbit_lower_bound (hM : IsSphereTriangulation M) (R : Set M.Face)
    (d : M.RegionDart R) (hd : M.faceOf d.val ∉ R) :
    (Finset.univ.filter (fun f : M.Face => f ∈ R)).card + 1 ≤
      Fintype.card (M.regionRotation R).FaceOrbit := by
  classical
  obtain ⟨q, hq, hiff, _⟩ := M.exists_region_interior_faces hM R
  let exterior := orbitOf (M.regionRotation R).facePerm d
  have hne (f : {f : M.Face // f ∈ R}) : q f ≠ exterior := by
    intro h
    exact hd (((hiff f d).mp h.symm).symm ▸ f.property)
  let lift : ({f : M.Face // f ∈ R} ⊕ Unit) → (M.regionRotation R).FaceOrbit :=
    Sum.elim q (fun _ => exterior)
  have hinj : Function.Injective lift := by
    intro a b h
    cases a with
    | inl f =>
      cases b with
      | inl g => exact congrArg Sum.inl (hq h)
      | inr u => exact (hne f h).elim
    | inr u =>
      cases b with
      | inl f => exact (hne f h.symm).elim
      | inr v => exact congrArg Sum.inr (Subsingleton.elim _ _)
  have hc := Fintype.card_le_of_injective lift hinj
  simpa only [Fintype.card_sum, Fintype.card_subtype, Fintype.card_unit] using hc

/-- If [the map is a sphere triangulation](hyp:hM), [the region's underlying graph
is connected](hyp:hconn), and [a retained region dart has its original face outside
the region](hyp:hd), then [the region's vertex count plus its number of original
faces is at most its edge count plus one](goal). -/
-- @node: SphereMap.region_euler_upper_bound
lemma region_euler_upper_bound (hM : IsSphereTriangulation M) (R : Set M.Face)
    (hconn : (M.regionRotation R).toSimpleGraph.Connected)
    (d : M.RegionDart R) (hd : M.faceOf d.val ∉ R) :
    Fintype.card (M.regionRotation R).Vertex +
      (Finset.univ.filter (fun f : M.Face => f ∈ R)).card ≤
        Fintype.card (M.regionRotation R).Edge + 1 := by
  let : Nonempty (M.regionRotation R).Dart := ⟨d⟩
  have hb := (M.regionRotation R).euler_bound hconn
  have hf := M.region_face_orbit_lower_bound hM R d hd
  omega
end SphereMap

/-- Suppose [the global vertex count plus face count equals the edge count plus
two](hyp:hglobal), [the two sides' vertex counts sum to the global vertex count
plus the boundary size](hyp:hvertices), [their edge counts sum to the global edge
count plus the same boundary size](hyp:hedges), and [their face counts sum to the
global face count](hyp:hfaces). If [the left side's vertex count plus face count
is at most its edge count plus one](hyp:hleft) and [the same bound holds on the
right side](hyp:hright), then [both bounds hold with equality](goal). -/
-- @node: two_sides_euler_squeeze
lemma two_sides_euler_squeeze (V E F h VL VR EL ER FL FR : ℕ)
    (hglobal : V + F = E + 2)
    (hvertices : VL + VR = V + h) (hedges : EL + ER = E + h)
    (hfaces : FL + FR = F)
    (hleft : VL + FL ≤ EL + 1) (hright : VR + FR ≤ ER + 1) :
    VL + FL = EL + 1 ∧ VR + FR = ER + 1 := by omega

end OaiPairedStatesHamiltonian

module
public import Papers.TbsNeuralCausalPi.Setup.Notation
public import Papers.TbsNeuralCausalPi.Helpers.AntipodalAction
public import Papers.TbsNeuralCausalPi.Helpers.AntipodalIncidence
public import Papers.TbsNeuralCausalPi.Helpers.AntipodalChains
public import Papers.TbsNeuralCausalPi.Helpers.AntipodalParity
public import Papers.TbsNeuralCausalPi.Helpers.SignedHemisphereLadder
public import Papers.TbsNeuralCausalPi.Helpers.GeometricModTwoSubdivision
public import Papers.TbsNeuralCausalPi.Helpers.SignedChainObstruction
public import Papers.TbsNeuralCausalPi.Helpers.SignedCoordinateLabels
public import Toolkit.Foundations.Topology.EquivariantTransversality
public import Mathlib.Analysis.Normed.Group.BallSphere
/-! # Local reductions for the Borsuk--Ulam dimension argument

The odd-map theorem is proved using signed-coordinate labels on fine
subdivisions and the finite antipodal chain obstruction. The earlier transverse
approximation and compact-limit reductions remain available independently.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
noncomputable section
open Toolkit.Foundations.Topology

-- @node: compact_exists_zero_of_approximate_zeros
/-- On a compact space, if [a map into a normed additive group is
continuous](hyp:hf) and [its output norm can be made smaller than every positive
real tolerance](hyp:hz), then [the map equals zero at some point](goal). -/
lemma compact_exists_zero_of_approximate_zeros
    {X F : Type*} [TopologicalSpace X] [CompactSpace X]
    [NormedAddCommGroup F] {f : X → F} (hf : Continuous f)
    (hz : ∀ ε : ℝ, 0 < ε → ∃ x, ‖f x‖ < ε) : ∃ x, f x = 0 := by
  obtain ⟨x₀, _⟩ := hz 1 (by norm_num)
  obtain ⟨x, _, hx⟩ := isCompact_univ.exists_isMinOn
    ⟨x₀, Set.mem_univ _⟩ hf.norm.continuousOn
  refine ⟨x, norm_eq_zero.mp ?_⟩
  by_contra hn
  have hp : 0 < ‖f x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
  obtain ⟨y, hy⟩ := hz ‖f x‖ hp
  exact (not_lt_of_ge (hx (Set.mem_univ y))) hy

-- @node: equivariant_exists_zero_of_transverse_zeros
/-- Suppose [a simplicial complex has finitely many faces](hyp:hQ), [a finite
group acts on it by simplicial maps](hyp:α), [the group acts linearly on the
target](hyp:ρ), and [the action on the complex is free](hyp:hfree). If [a map
on the complex is continuous](hyp:hf), [respects these actions](hyp:heq), and
[every action-respecting piecewise linear map transverse to zero on every
iterated barycentric subdivision has a zero](hyp:hzero), then [the continuous
map has a zero](goal). -/
lemma equivariant_exists_zero_of_transverse_zeros
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [Group G]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [Finite G]
    {Q : Geometry.SimplicialComplex ℝ E} (hQ : Q.faces.Finite)
    (α : SimplicialAction G Q) (ρ : G →* (F ≃ₗ[ℝ] F)) (hfree : α.IsFree)
    {f : Q.space → F} (hf : Continuous f) (heq : Equivariant α ρ f)
    (hzero : ∀ k (g : PLMap (sdIterate Q k) F),
      Equivariant (α.iterate k) ρ g → g.TransverseToZero → ∃ x, g x = 0) :
    ∃ x, f x = 0 := by
  let : CompactSpace Q.space := isCompact_iff_compactSpace.mp (isCompact_space hQ)
  apply compact_exists_zero_of_approximate_zeros hf
  intro ε hε
  obtain ⟨k, g, hgeq, hgt, hclose⟩ :=
    exists_equivariant_transverse_approximation hQ α ρ hfree hf heq hε
  obtain ⟨x, hx⟩ := hzero k g hgeq hgt
  refine ⟨originalPoint Q k x, ?_⟩
  simpa [hx, dist_eq_norm] using hclose x

-- @node: sphere_odd_exists_zero_of_signed_transverse_zeros
/-- If [every antipodal-equivariant piecewise linear map from any subdivision
of the signed d-sphere to d-dimensional real space that is transverse to zero
has a zero](hyp:hzero), then any map from the unit sup-norm d-sphere to
d-dimensional real space that [is continuous](hyp:hf) and [takes opposite
values at antipodal points](hyp:hodd) [has a zero](goal). -/
lemma sphere_odd_exists_zero_of_signed_transverse_zeros
    (d : ℕ)
    (hzero : ∀ k (g : PLMap (sdIterate (Antipodal.signedGeometricComplex (d + 1)) k)
        (L1Vec d)),
      Equivariant ((Antipodal.signedAntipodalAction (d + 1)).iterate k)
        (Antipodal.antipodalRepresentation (L1Vec d)) g →
      g.TransverseToZero → ∃ x, g x = 0)
    (f : Metric.sphere (0 : Fin (d + 1) → ℝ) 1 → L1Vec d)
    (hf : Continuous f) (hodd : ∀ x, f (-x) = -f x) : ∃ x, f x = 0 := by
  have heq := Antipodal.odd_signedSphere_equivariant f hodd
  have hcont : Continuous (fun x => f (Antipodal.signedSphereHomeomorph (d + 1) x)) := by
    fun_prop
  obtain ⟨x, hx⟩ := equivariant_exists_zero_of_transverse_zeros
    (Antipodal.signedGeometricComplex_faces_finite (d + 1))
    (Antipodal.signedAntipodalAction (d + 1))
    (Antipodal.antipodalRepresentation (L1Vec d))
    (Antipodal.signedAntipodalAction_isFree (d + 1)) hcont heq hzero
  exact ⟨Antipodal.signedSphereHomeomorph (d + 1) x, hx⟩

-- @node: sphereCubeEmbedding
/-- Given [room for d plus one coordinates in a q-dimensional cube](hyp:h)
and [a point x on the unit sup-norm d-sphere](hyp:x), [the sphere-to-cube
embedding of x](goal) rescales its coordinates from minus one through one to
zero through one in the first d plus one positions, and fills all remaining
positions with one half. -/
def sphereCubeEmbedding {d q : ℕ} (h : d + 1 ≤ q)
    (x : Metric.sphere (0 : Fin (d + 1) → ℝ) 1) : unitCube q :=
  ⟨WithLp.toLp 1 (fun j => if hj : j.val < d + 1 then
      (x.val ⟨j.val, hj⟩ + 1) / 2 else 1/2), by
    intro j
    change (if hj : j.val < d + 1 then (x.val ⟨j.val, hj⟩ + 1) / 2 else 1/2) ∈ Set.Icc 0 1
    split_ifs with hj
    · have hn : ‖x.val‖ = 1 := by simpa [Metric.mem_sphere, dist_eq_norm] using x.property
      have hb : |x.val ⟨j.val, hj⟩| ≤ 1 := by
        simpa [Real.norm_eq_abs, hn] using norm_le_pi_norm x.val ⟨j.val, hj⟩
      obtain ⟨hl, hu⟩ := abs_le.mp hb
      constructor <;> linarith
    · constructor <;> norm_num⟩

-- @node: sphereCubeEmbedding_continuous
/-- If [q is at least d plus one](hyp:h), then [the affine embedding of the
unit sup-norm d-sphere into the q-dimensional unit cube is continuous](goal). -/
@[fun_prop] lemma sphereCubeEmbedding_continuous {d q : ℕ} (h : d + 1 ≤ q) :
    Continuous (sphereCubeEmbedding h) := by
  unfold sphereCubeEmbedding
  apply Continuous.subtype_mk
  apply (PiLp.continuous_toLp 1 (fun _ : Fin q => ℝ)).comp
  apply continuous_pi
  intro j
  by_cases hj : j.val < d + 1
  · simp only [dif_pos hj]
    exact (((continuous_apply (⟨j.val, hj⟩ : Fin (d + 1))).comp continuous_subtype_val).add
      continuous_const).div_const 2
  · simp only [dif_neg hj]
    fun_prop

-- @node: sphereCubeEmbedding_injective
/-- If [q is at least d plus one](hyp:h), then [the affine embedding of the
unit sup-norm d-sphere into the q-dimensional unit cube is injective](goal). -/
lemma sphereCubeEmbedding_injective {d q : ℕ} (h : d + 1 ≤ q) :
    Function.Injective (sphereCubeEmbedding h) := by
  intro x y hxy
  apply Subtype.ext
  funext i
  have hi := congrArg (fun z : unitCube q => z.val.ofLp ⟨i.val, lt_of_lt_of_le i.isLt h⟩) hxy
  change (if hj : i.val < d + 1 then (x.val ⟨i.val, hj⟩ + 1)/2 else 1/2) =
    (if hj : i.val < d + 1 then (y.val ⟨i.val, hj⟩ + 1)/2 else 1/2) at hi
  simp only [dif_pos i.isLt] at hi
  linarith

-- @node: sphere_zero_dim_exists_zero
/-- [Every map from the unit sphere in one-dimensional real space to
zero-dimensional real space has a zero](goal). -/
lemma sphere_zero_dim_exists_zero
    (g : Metric.sphere (0 : Fin 1 → ℝ) 1 → L1Vec 0) : ∃ x, g x = 0 := by
  let x : Metric.sphere (0 : Fin 1 → ℝ) 1 :=
    ⟨fun _ => 1, by simp [Metric.mem_sphere, dist_eq_norm]⟩
  exact ⟨x, Subsingleton.elim _ _⟩

-- @node: sphere_ne_antipode
/-- [A point on a unit sup-norm sphere is distinct from its antipode](goal). -/
lemma sphere_ne_antipode {d : ℕ}
    (x : Metric.sphere (0 : Fin (d + 1) → ℝ) 1) : x ≠ -x := by
  intro hx
  have hz : x.val = 0 := by
    funext i
    have hi := congrArg (fun z : Metric.sphere (0 : Fin (d + 1) → ℝ) 1 => z.val i) hx
    change x.val i = -x.val i at hi
    change x.val i = 0
    linarith
  have hn : ‖x.val‖ = 1 := by simpa [Metric.mem_sphere, dist_eq_norm] using x.property
  rw [hz, norm_zero] at hn
  norm_num at hn

-- @node: sphere_odd_exists_zero
/-- A map from the unit sup-norm d-sphere to d-dimensional real space that
[is continuous](hyp:hf) and [takes opposite values at antipodal
points](hyp:hodd) [equals zero at some point](goal).

This is the odd-map formulation of Borsuk--Ulam, proved using signed coordinate
labels and the finite mod-two chain obstruction. -/
lemma sphere_odd_exists_zero (d : ℕ)
    (f : Metric.sphere (0 : Fin (d + 1) → ℝ) 1 → L1Vec d)
    (hf : Continuous f) (hodd : ∀ x, f (-x) = -f x) : ∃ x, f x = 0 := by
  by_cases hd : d = 0
  · subst d
    exact sphere_zero_dim_exists_zero f
  let g : (Antipodal.signedGeometricComplex (d + 1)).space → (Fin d → ℝ) :=
    fun x => (f (Antipodal.signedSphereHomeomorph (d + 1) x)).ofLp
  have hg : Continuous g := by
    fun_prop
  have hgodd : ∀ x, g ⟨-x.val, Antipodal.signedGeometricComplex_neg_mem x.property⟩ = -g x := by
    intro x
    simp only [g, Antipodal.signedSphereHomeomorph_antipode, hodd]
    rfl
  obtain ⟨x, hx⟩ := Antipodal.signedSphere_odd_exists_zero (Nat.pos_of_ne_zero hd) g hg hgodd
  refine ⟨Antipodal.signedSphereHomeomorph (d + 1) x, ?_⟩
  exact WithLp.ofLp_injective 1 hx

end
end Papers.TbsNeuralCausalPi

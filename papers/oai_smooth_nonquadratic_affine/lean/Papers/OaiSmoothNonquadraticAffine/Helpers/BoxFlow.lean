module

public import Papers.OaiSmoothNonquadraticAffine.Helpers.BoxGeometry
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-! # Squared-distance comparison for the invariant box

The squared distance is bounded above by distance to any fixed point of the box.
At a given time, fix the projection at that time. This smooth upper support gives
its upper right slope even when the nearest face changes.
-/

public section

noncomputable section

open Set Filter
open scoped Topology RealInnerProductSpace

namespace OaiSmoothNonquadraticAffine

-- @node: continuous_boxProjection
/-- [Coordinatewise projection onto the closed box is continuous](goal). -/
@[fun_prop] lemma continuous_boxProjection : Continuous boxProjection := by
  unfold boxProjection
  fun_prop

-- @node: continuous_boxDistance
/-- [The Euclidean distance to the closed box is a continuous function of the point](goal). -/
@[fun_prop] lemma continuous_boxDistance : Continuous boxDistance := by
  unfold boxDistance
  fun_prop

-- @node: boxDistance_sq_le
/-- If [p belongs to the closed box](hyp:hp), then [the squared distance from z to
the box is at most the squared Euclidean distance from z to p](goal). -/
lemma boxDistance_sq_le (z : Fin 3 → ℝ) {p : Fin 3 → ℝ} (hp : p ∈ boxB) :
    boxDistance z ^ 2 ≤ ‖WithLp.toLp 2 (z - p)‖ ^ 2 := by
  simp only [boxDistance, EuclideanSpace.real_norm_sq_eq]
  exact Finset.sum_le_sum (fun i _ => boxProjection_sq_le z hp i)

-- @node: boxDistance_eq_zero_iff
/-- [A point has zero distance to the closed box if and only if it belongs to the box](goal). -/
lemma boxDistance_eq_zero_iff (z : Fin 3 → ℝ) : boxDistance z = 0 ↔ z ∈ boxB := by
  constructor
  · intro h
    have he : z = boxProjection z := by
      have hn := norm_eq_zero.mp h
      have hz : z - boxProjection z = 0 := (WithLp.toLp_eq_zero _).mp hn
      exact sub_eq_zero.mp hz
    rw [he]
    exact boxProjection_mem z
  · intro h
    simp [boxDistance, boxProjection_eq_self h]

-- @node: box_field_distance_bound
/-- If [the autonomous field has nonnegative Lipschitz bound L on N](hyp:hL),
[z lies in N](hyp:hz), and [the box projection of z also lies in N](hyp:hp), then
[twice the inner product of the displacement from the projection to z with the
field at z is at most twice L times the squared distance to the box](goal). -/
lemma box_field_distance_bound {L : ℝ} {N : Set (Fin 3 → ℝ)}
    (hL : BoxFieldLipschitzBound L N) {z : Fin 3 → ℝ}
    (hz : z ∈ N) (hp : boxProjection z ∈ N) :
    2 * ⟪WithLp.toLp 2 (z - boxProjection z), WithLp.toLp 2 (autonomousField z)⟫ ≤
      (2 * L) * boxDistance z ^ 2 := by
  let e : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 (z - boxProjection z)
  let v : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 (autonomousField z)
  let p : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 (autonomousField (boxProjection z))
  have hface : ⟪e, p⟫ ≤ 0 := by
    simpa [e, p, PiLp.inner_apply, mul_comm] using boxProjection_field_inner_nonpos z
  have hdiff : ‖v - p‖ ≤ L * ‖e‖ := hL.2 z hz (boxProjection z) hp
  have hi := real_inner_le_norm e (v - p)
  rw [inner_sub_right] at hi
  have hm := mul_le_mul_of_nonneg_left hdiff (norm_nonneg e)
  change 2 * ⟪e, v⟫ ≤ (2 * L) * ‖e‖ ^ 2
  nlinarith

-- @node: boxDistance_liminf_slope
/-- If [the derivative of the trajectory z at time τ equals the autonomous field
at z at that time](hyp:hd), then [for every threshold above twice the inner product
of the displacement from the box projection with that field, there are times
arbitrarily close to τ from the right at which the difference quotient of squared
distance to the box is below the threshold](goal). -/
lemma boxDistance_liminf_slope {z : ℝ → Fin 3 → ℝ} {τ : ℝ}
    (hd : HasDerivAt z (autonomousField (z τ)) τ) :
    ∀ r, 2 * ⟪WithLp.toLp 2 (z τ - boxProjection (z τ)),
      WithLp.toLp 2 (autonomousField (z τ))⟫ < r →
      ∃ᶠ s in 𝓝[>] τ,
        (s - τ)⁻¹ * (boxDistance (z s) ^ 2 - boxDistance (z τ) ^ 2) < r := by
  let p := boxProjection (z τ)
  have hde : HasDerivAt (fun s => WithLp.toLp 2 (z s - p))
      (WithLp.toLp 2 (autonomousField (z τ))) τ :=
    (PiLp.hasFDerivAt_toLp 2 (z τ - p)).comp_hasDerivAt τ (hd.sub_const p)
  have hs := hde.norm_sq
  intro r hr
  have hfreq := hs.hasDerivWithinAt.liminf_right_slope_le hr
  have heq : ‖WithLp.toLp 2 (z τ - p)‖ ^ 2 = boxDistance (z τ) ^ 2 := rfl
  apply (hfreq.and_eventually self_mem_nhdsWithin).mono
  rintro s ⟨hs, hst⟩
  have hle := boxDistance_sq_le (z s) (boxProjection_mem (z τ))
  have hpos : 0 ≤ (s - τ)⁻¹ := inv_nonneg.mpr (sub_nonneg.mpr (le_of_lt hst))
  have hm := mul_le_mul_of_nonneg_left (sub_le_sub_right hle (boxDistance (z τ) ^ 2)) hpos
  apply lt_of_le_of_lt hm
  simpa only [slope, vsub_eq_sub, smul_eq_mul, heq, p] using hs

-- @node: box_invariant_of_lipschitz
/-- Suppose [z is continuous on the closed time interval from a to b](hyp:hc),
[its derivative equals the autonomous field from a up to but excluding b](hyp:hd),
and [z starts in the box at a](hyp:ha). If [the field has nonnegative Lipschitz
bound L on N](hyp:hL), [the entire trajectory lies in N](hyp:hz), and [all its box
projections lie in N](hyp:hp), then [z stays in the box throughout the closed
time interval](goal). -/
lemma box_invariant_of_lipschitz {z : ℝ → Fin 3 → ℝ} {a b : ℝ}
    (hc : ContinuousOn z (Icc a b))
    (hd : ∀ τ ∈ Ico a b, HasDerivAt z (autonomousField (z τ)) τ)
    (ha : z a ∈ boxB) {L : ℝ} {N : Set (Fin 3 → ℝ)}
    (hL : BoxFieldLipschitzBound L N)
    (hz : ∀ τ ∈ Icc a b, z τ ∈ N)
    (hp : ∀ τ ∈ Icc a b, boxProjection (z τ) ∈ N) :
    ∀ τ ∈ Icc a b, z τ ∈ boxB := by
  have hcont : ContinuousOn (fun τ => boxDistance (z τ) ^ 2) (Icc a b) :=
    (continuous_boxDistance.comp_continuousOn hc).pow 2
  have hgr := le_gronwallBound_of_liminf_deriv_right_le hcont
    (fun τ hτ => boxDistance_liminf_slope (hd τ hτ))
    (δ := 0) (K := 2 * L) (ε := 0)
    (by rw [(boxDistance_eq_zero_iff _).mpr ha]; norm_num)
    (fun τ hτ => by
      simpa only [add_zero] using box_field_distance_bound hL
        (hz τ ⟨hτ.1, hτ.2.le⟩) (hp τ ⟨hτ.1, hτ.2.le⟩))
  intro τ hτ
  have hh := hgr τ hτ
  rw [gronwallBound_ε0_δ0] at hh
  exact (boxDistance_eq_zero_iff _).mp (sq_eq_zero_iff.mp (le_antisymm hh (sq_nonneg _)))

-- @node: contDiff_autonomousField_euclidean
/-- [The autonomous vector field, viewed as a map between three-dimensional
Euclidean spaces, is continuously differentiable](goal). -/
@[fun_prop] lemma contDiff_autonomousField_euclidean :
    ContDiff ℝ 1 (fun x : EuclideanSpace ℝ (Fin 3) =>
      WithLp.toLp 2 (autonomousField (WithLp.ofLp x))) := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · change ContDiff ℝ 1 (fun x : EuclideanSpace ℝ (Fin 3) =>
      x 0 * (1 + x 1 - x 0))
    fun_prop
  · change ContDiff ℝ 1 (fun x : EuclideanSpace ℝ (Fin 3) =>
      x 1 * (9 + x 0 + (12 / 11 : ℝ) * x 1 * x 2 - 9 * x 1))
    fun_prop
  · change ContDiff ℝ 1 (fun x : EuclideanSpace ℝ (Fin 3) =>
      (11 - x 2) * x 0 - 8 * x 2 + x 1 * x 2 * (1 - x 2 / 11))
    fun_prop

-- @node: autonomous_box_forward_invariant
/-- If [a is no later than b](hyp:_hab), [z is continuous on the closed interval
from a to b](hyp:hc), [its derivative equals the autonomous field from a up to
but excluding b](hyp:hd), and [z starts in the box at a](hyp:ha), then [z remains
in the box at every time in the closed interval](goal). -/
lemma autonomous_box_forward_invariant (z : ℝ → Fin 3 → ℝ) (a b : ℝ)
    (_hab : a ≤ b) (hc : ContinuousOn z (Icc a b))
    (hd : ∀ τ ∈ Ico a b, HasDerivAt z (autonomousField (z τ)) τ)
    (ha : z a ∈ boxB) : ∀ τ ∈ Icc a b, z τ ∈ boxB := by
  have he : ContinuousOn (fun τ => WithLp.toLp 2 (z τ)) (Icc a b) :=
    (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp_continuousOn hc
  have hep : ContinuousOn (fun τ => WithLp.toLp 2 (boxProjection (z τ))) (Icc a b) :=
    (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp_continuousOn
      (continuous_boxProjection.comp_continuousOn hc)
  obtain ⟨M, hM⟩ := ((isCompact_Icc.image_of_continuousOn he).union
    (isCompact_Icc.image_of_continuousOn hep)).isBounded.subset_closedBall
      (0 : EuclideanSpace ℝ (Fin 3))
  obtain ⟨L, hL⟩ := contDiff_autonomousField_euclidean.contDiffOn.exists_lipschitzOnWith
    (by norm_num : (1 : WithTop ℕ∞) ≠ 0) (convex_closedBall (0 : EuclideanSpace ℝ (Fin 3)) M)
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3)) M)
  let N : Set (Fin 3 → ℝ) := {v | WithLp.toLp 2 v ∈ Metric.closedBall 0 M}
  apply box_invariant_of_lipschitz hc hd ha (L := L) (N := N)
  · refine ⟨L.coe_nonneg, ?_⟩
    intro v hv w hw
    simpa only [dist_eq_norm, WithLp.toLp_sub] using
      hL.dist_le_mul (WithLp.toLp 2 v) hv (WithLp.toLp 2 w) hw
  · intro τ hτ
    exact hM (Or.inl ⟨τ, hτ, rfl⟩)
  · intro τ hτ
    exact hM (Or.inr ⟨τ, hτ, rfl⟩)

end OaiSmoothNonquadraticAffine

module

public import Papers.OaiSmoothNonquadraticAffine.Helpers.ContinuationBounds
public import Papers.OaiSmoothNonquadraticAffine.Helpers.RadialSmooth
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Calculus.MeanValue

/-! # The regular radial ODE and its finite-endpoint limit

Compact confinement bounds the regular vector field. The mean value theorem
then makes the state uniformly continuous up to a finite outer endpoint.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology ContDiff NNReal

namespace OaiSmoothNonquadraticAffine

/-- For [a radius and a four-coordinate state consisting of profile, pressure,
profile slope, and pressure slope](hyp:q), [the continuation vector field](goal)
is computed by [forming the profile acceleration as the radius to the eighth
power times the profile times the pressure to the power −12/11, divided by the
eighth power of the profile slope](step:1), then [returning the two slopes, that
acceleration, and the pressure acceleration given by minus eight times the
profile acceleration times the pressure slope divided by the profile slope,
minus eleven times the radius to the eighth power times the pressure to the
power −1/11 divided by the eighth power of the profile slope](step:2). -/
-- @node: continuationField
def continuationField (q : ℝ × (Fin 4 → ℝ)) : Fin 4 → ℝ :=
  let G := q.1 ^ 8 * q.2 0 * q.2 1 ^ (-(12 / 11 : ℝ)) / q.2 2 ^ 8
  ![q.2 2, q.2 3, G,
    -8 * G / q.2 2 * q.2 3 - 11 * q.1 ^ 8 * q.2 1 ^ (-(1 / 11 : ℝ)) / q.2 2 ^ 8]

-- @node: continuationField_eq_regularField
/-- If [the radius is positive](hyp:hr), [the profile value is positive](hyp:hF),
[the pressure is positive](hyp:hP), and [the profile slope is positive](hyp:hy),
[the ambient continuation field equals the regular field at that radius and
state](goal). -/
lemma continuationField_eq_regularField {r : ℝ} {v : Fin 4 → ℝ}
    (hr : 0 < r) (hF : 0 < v 0) (hP : 0 < v 1) (hy : 0 < v 2) :
    continuationField (r, v) = regularField r v hr hF hP hy := rfl

-- @node: continuationField_contDiffAt
/-- If [the pressure coordinate is nonzero](hyp:hP) and [the profile slope
coordinate is nonzero](hyp:hy), [the continuation field is infinitely
differentiable at the given radius and state](goal). -/
@[fun_prop] lemma continuationField_contDiffAt {q : ℝ × (Fin 4 → ℝ)}
    (hP : q.2 1 ≠ 0) (hy : q.2 2 ≠ 0) :
    ContDiffAt ℝ ∞ continuationField q := by
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [continuationField] <;> fun_prop (disch := simp_all)

/-- If [the profile and pressure satisfy the radial determinant and flux
system with the paper's constants on a set of radii](hyp:h), [r belongs to that
set](hyp:hr), and [the profile slope at r is nonzero](hyp:hy), [the derivative
at r of the state consisting of profile, pressure, and their first derivatives
equals the continuation field evaluated at r and that state](goal). -/
-- @node: radialSystem_state_hasDerivAt
lemma radialSystem_state_hasDerivAt {F P : ℝ → ℝ} {J : Set ℝ}
    (h : RadialSystem radialDim radialK radialGamma F P J)
    {r : ℝ} (hr : r ∈ J) (hy : deriv F r ≠ 0) :
    HasDerivAt (fun s => ![F s, P s, deriv F s, deriv P s])
      (continuationField (r, ![F r, P r, deriv F r, deriv P r])) r := by
  have hs := h r hr
  have hF := (hs.1.differentiableAt (by norm_num)).hasDerivAt
  have hP := (hs.2.1.differentiableAt (by norm_num)).hasDerivAt
  have hY := (radialSystem_slope_differentiableAt h hr).hasDerivAt
  have hZ := ((hs.2.1.derivWithin (m := 1) (by norm_num)).differentiableAt_one).hasDerivAt
  have heqY : deriv (deriv F) r =
      r ^ 8 * F r * P r ^ (-(12 / 11 : ℝ)) / deriv F r ^ 8 := by
    apply (eq_div_iff (pow_ne_zero 8 hy)).mpr
    simpa [radialDim, radialGamma, mul_comm] using hs.2.2.1
  have heqZ := hs.2.2.2
  have hflux := ((hY.pow 8).mul hZ).deriv
  change deriv (fun s => deriv F s ^ 8 * deriv P s) r = _ at hflux
  change deriv (fun s => deriv F s ^ 8 * deriv P s) r =
    -11 * r ^ 8 * P r ^ (1 - (12 / 11 : ℝ)) at heqZ
  rw [hflux] at heqZ
  norm_num only [show (1 : ℝ) - 12 / 11 = -(1 / 11 : ℝ) by norm_num] at heqZ
  have hzval : deriv (deriv P) r =
      -8 * (r ^ 8 * F r * P r ^ (-(12 / 11 : ℝ)) / deriv F r ^ 8) /
        deriv F r * deriv P r - 11 * r ^ 8 * P r ^ (-(1 / 11 : ℝ)) / deriv F r ^ 8 := by
    rw [← heqY]
    field_simp [hy]
    dsimp only [Pi.pow_apply] at heqZ
    linear_combination heqZ
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [continuationField] using hF
  · simpa [continuationField] using hP
  · simpa [continuationField, heqY] using hY
  · simpa [continuationField, hzval] using hZ


/-- Given [normalized local solution data](hyp:hLocal), [a maximal positive
continuation with finite endpoint R](hyp:hCont), and [a positive radius
a](hyp:ha) [strictly below R](hyp:haR), [there is a nonnegative constant bounding
the norm of the continuation field along the full profile-pressure state at
every radius from a inclusive to R exclusive](goal). -/
-- @node: continuation_state_derivative_bounded
lemma continuation_state_derivative_bounded {ε : ℝ} {F₀ P₀ F P : ℝ → ℝ}
    {R a : ℝ} (hLocal : LocalSolutionData ε F₀ P₀)
    (hCont : IsMaximalContinuation F₀ P₀ ε F P (R : WithTop ℝ))
    (ha : 0 < a) (haR : a < R) :
    ∃ C : ℝ≥0, ∀ r ∈ Ico a R,
      ‖continuationField (r, ![F r, P r, deriv F r, deriv P r])‖₊ ≤ C := by
  obtain ⟨K, hK, hDom, hmem⟩ := continuation_compact_state_window hLocal hCont ha haR
  have hc : ContinuousOn continuationField K := by
    intro q hq
    exact (continuationField_contDiffAt (hDom hq).2.2.1.ne'
      (hDom hq).2.2.2.ne').continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨Real.toNNReal M, fun r hr => ?_⟩
  exact_mod_cast (hM _ (hmem r hr)).trans (Real.le_coe_toNNReal M)

/-- Given [normalized local solution data](hyp:hLocal), [a maximal positive
continuation with finite endpoint R](hyp:hCont), and [a positive radius
a](hyp:ha) [strictly below R](hyp:haR), [the state consisting of profile,
pressure, and their first derivatives is Lipschitz continuous with some
nonnegative constant from a inclusive to R exclusive](goal). -/
-- @node: continuation_state_lipschitzOn
lemma continuation_state_lipschitzOn {ε : ℝ} {F₀ P₀ F P : ℝ → ℝ}
    {R a : ℝ} (hLocal : LocalSolutionData ε F₀ P₀)
    (hCont : IsMaximalContinuation F₀ P₀ ε F P (R : WithTop ℝ))
    (ha : 0 < a) (haR : a < R) :
    ∃ C : ℝ≥0, LipschitzOnWith C (fun r => ![F r, P r, deriv F r, deriv P r])
      (Ico a R) := by
  obtain ⟨C, hC⟩ := continuation_state_derivative_bounded hLocal hCont ha haR
  refine ⟨C, (convex_Ico a R).lipschitzOnWith_of_nnnorm_hasDerivWithin_le ?_ hC⟩
  intro r hr
  have hr' : r ∈ radialInterval (R : WithTop ℝ) :=
    ⟨ha.trans_le hr.1, by exact_mod_cast hr.2⟩
  exact (radialSystem_state_hasDerivAt hCont.2.2.2.1.2.1 hr'
    (hCont.2.2.2.1.2.2 r hr').2.2.ne').hasDerivWithinAt

/-- Given [normalized local solution data](hyp:hLocal), [a maximal positive
continuation with finite endpoint R](hyp:hCont), and [a positive radius
a](hyp:ha) [strictly below R](hyp:haR), [the state consisting of profile,
pressure, and their first derivatives has a left limit at R whose profile,
pressure, and profile slope coordinates are strictly positive](goal). -/
-- @node: continuation_state_tendsto_endpoint
lemma continuation_state_tendsto_endpoint {ε : ℝ} {F₀ P₀ F P : ℝ → ℝ}
    {R a : ℝ} (hLocal : LocalSolutionData ε F₀ P₀)
    (hCont : IsMaximalContinuation F₀ P₀ ε F P (R : WithTop ℝ))
    (ha : 0 < a) (haR : a < R) :
    ∃ v : Fin 4 → ℝ, 0 < v 0 ∧ 0 < v 1 ∧ 0 < v 2 ∧
      Tendsto (fun r => ![F r, P r, deriv F r, deriv P r]) (𝓝[<] R) (𝓝 v) := by
  obtain ⟨C, hC⟩ := continuation_state_lipschitzOn hLocal hCont ha haR
  have hwin : Ico a R ∈ 𝓝[<] R := by
    exact inter_mem (mem_nhdsWithin_of_mem_nhds (Ici_mem_nhds haR)) self_mem_nhdsWithin
  have hcau : Cauchy (𝓝[<] R) := cauchy_nhds.mono inf_le_left
  obtain ⟨v, hv⟩ := cauchy_map_iff_exists_tendsto.mp
    (hcau.map_of_le hC.uniformContinuousOn (le_principal_iff.mpr hwin))
  obtain ⟨K, hK, hDom, hmem⟩ := continuation_compact_state_window hLocal hCont ha haR
  have hlim : Tendsto (fun r => (r, ![F r, P r, deriv F r, deriv P r]))
      (𝓝[<] R) (𝓝 (R, v)) := tendsto_id.mono_left inf_le_left |>.prodMk_nhds hv
  have hKv : (R, v) ∈ K := hK.isClosed.mem_of_tendsto hlim
    (Filter.Eventually.mono hwin (fun r hr => hmem r hr))
  exact ⟨v, (hDom hKv).2.1, (hDom hKv).2.2.1, (hDom hKv).2.2.2, hv⟩

end OaiSmoothNonquadraticAffine

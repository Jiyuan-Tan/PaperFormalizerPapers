module

public import Papers.OaiSmoothNonquadraticAffine.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # Smoothness of positive radial solutions away from the origin

The integrated radial system bootstraps the profiles, slope and flux together.
Local spatial smoothness then supplies the missing point at the origin.
-/

public section

open Set Filter
open scoped Topology ContDiff

namespace OaiSmoothNonquadraticAffine

-- @node: radialSystem_slope_differentiableAt
/-- If [F and P satisfy the radial system on J](hyp:h) and [r belongs to J](hyp:hr),
then [the slope F′ is differentiable at r](goal). -/
lemma radialSystem_slope_differentiableAt {m : ℕ} {k γ : ℝ}
    {F P : ℝ → ℝ} {J : Set ℝ} (h : RadialSystem m k γ F P J)
    {r : ℝ} (hr : r ∈ J) : DifferentiableAt ℝ (deriv F) r := by
  exact ((h r hr).1.derivWithin (m := 1) (by norm_num)).differentiableAt_one

-- @node: radialSystem_flux_hasDerivAt
/-- If [F and P satisfy the radial system on J](hyp:h) and [r belongs to J](hyp:hr),
then [the flux (F′) raised to m − 1 times P′ has derivative
−k times r raised to m − 1 times P raised to 1 − γ at r](goal). -/
lemma radialSystem_flux_hasDerivAt {m : ℕ} {k γ : ℝ}
    {F P : ℝ → ℝ} {J : Set ℝ} (h : RadialSystem m k γ F P J)
    {r : ℝ} (hr : r ∈ J) :
    HasDerivAt (fun t => deriv F t ^ (m - 1) * deriv P t)
      (-k * r ^ (m - 1) * P r ^ (1 - γ)) r := by
  have hP := ((h r hr).2.1.derivWithin (m := 1) (by norm_num)).differentiableAt_one
  have hd := ((radialSystem_slope_differentiableAt h hr).pow (m - 1)).mul hP
  rw [← (h r hr).2.2.2]
  exact hd.hasDerivAt

-- @node: radialSystem_contDiffOn_nat
/-- If [J is open](hyp:hJ), [F and P satisfy the radial system on J](hyp:h),
[P is strictly positive on J](hyp:hP), and [F′ is strictly positive on J](hyp:hy),
then [F, P, the slope F′, and the flux (F′) raised to m − 1 times P′ all have
continuous derivatives through order n on J](goal), for any natural number n. -/
lemma radialSystem_contDiffOn_nat {m : ℕ} {k γ : ℝ}
    {F P : ℝ → ℝ} {J : Set ℝ} (hJ : IsOpen J)
    (h : RadialSystem m k γ F P J)
    (hP : ∀ r ∈ J, 0 < P r) (hy : ∀ r ∈ J, 0 < deriv F r) (n : ℕ) :
    ContDiffOn ℝ n F J ∧ ContDiffOn ℝ n P J ∧
    ContDiffOn ℝ n (deriv F) J ∧
    ContDiffOn ℝ n (fun t => deriv F t ^ (m - 1) * deriv P t) J := by
  have hdF : DifferentiableOn ℝ F J := fun r hr =>
    ((h r hr).1.differentiableAt (by norm_num)).differentiableWithinAt
  have hdP : DifferentiableOn ℝ P J := fun r hr =>
    ((h r hr).2.1.differentiableAt (by norm_num)).differentiableWithinAt
  have hdy : DifferentiableOn ℝ (deriv F) J := fun r hr =>
    (radialSystem_slope_differentiableAt h hr).differentiableWithinAt
  have hdw : DifferentiableOn ℝ (fun t => deriv F t ^ (m - 1) * deriv P t) J :=
    fun r hr => (radialSystem_flux_hasDerivAt h hr).differentiableAt.differentiableWithinAt
  induction n with
  | zero =>
    exact ⟨contDiffOn_zero.mpr hdF.continuousOn, contDiffOn_zero.mpr hdP.continuousOn,
      contDiffOn_zero.mpr hdy.continuousOn, contDiffOn_zero.mpr hdw.continuousOn⟩
  | succ n ih =>
    have hden : ∀ r ∈ J, deriv F r ^ (m - 1) ≠ 0 :=
      fun r hr => pow_ne_zero _ (hy r hr).ne'
    have hP' : ContDiffOn ℝ n (deriv P) J := by
      apply (ih.2.2.2.div (ih.2.2.1.pow (m - 1)) hden).congr
      intro r hr
      exact (mul_div_cancel_left₀ (deriv P r) (hden r hr)).symm
    have hy' : ContDiffOn ℝ n (deriv (deriv F)) J := by
      have hnum : ContDiffOn ℝ n
          (fun r => r ^ (m - 1) * F r * P r ^ (-γ)) J :=
        ((contDiffOn_id.pow (m - 1)).mul ih.1).mul
          (ih.2.1.rpow_const_of_ne (fun r hr => (hP r hr).ne'))
      apply (hnum.div (ih.2.2.1.pow (m - 1)) hden).congr
      intro r hr
      exact (eq_div_iff (hden r hr)).mpr (by
        simpa only [mul_comm] using (h r hr).2.2.1)
    have hw' : ContDiffOn ℝ n
        (deriv (fun t => deriv F t ^ (m - 1) * deriv P t)) J := by
      have hrhs : ContDiffOn ℝ n
          (fun r => -k * r ^ (m - 1) * P r ^ (1 - γ)) J :=
        (contDiffOn_const.mul (contDiffOn_id.pow (m - 1))).mul
          (ih.2.1.rpow_const_of_ne (fun r hr => (hP r hr).ne'))
      exact hrhs.congr (fun r hr => (h r hr).2.2.2)
    have lift (f : ℝ → ℝ) (hd : DifferentiableOn ℝ f J)
        (hc : ContDiffOn ℝ n (deriv f) J) : ContDiffOn ℝ (n + 1) f J := by
      rw [contDiffOn_succ_iff_deriv_of_isOpen hJ]
      exact ⟨hd, by simp, hc⟩
    exact ⟨lift F hdF ih.2.2.1, lift P hdP hP', lift (deriv F) hdy hy',
      lift _ hdw hw'⟩

-- @node: radialSystem_contDiffOn
/-- If [J is open](hyp:hJ), [F and P satisfy the radial system on J](hyp:h),
[P is strictly positive on J](hyp:hP), and [F′ is strictly positive on J](hyp:hy),
then [F, P, the slope F′, and the flux (F′) raised to m − 1 times P′ are all
infinitely differentiable on J](goal). -/
lemma radialSystem_contDiffOn {m : ℕ} {k γ : ℝ}
    {F P : ℝ → ℝ} {J : Set ℝ} (hJ : IsOpen J)
    (h : RadialSystem m k γ F P J)
    (hP : ∀ r ∈ J, 0 < P r) (hy : ∀ r ∈ J, 0 < deriv F r) :
    ContDiffOn ℝ ∞ F J ∧ ContDiffOn ℝ ∞ P J ∧
    ContDiffOn ℝ ∞ (deriv F) J ∧
    ContDiffOn ℝ ∞ (fun t => deriv F t ^ (m - 1) * deriv P t) J := by
  exact ⟨contDiffOn_infty.mpr (fun n => (radialSystem_contDiffOn_nat hJ h hP hy n).1),
    contDiffOn_infty.mpr (fun n => (radialSystem_contDiffOn_nat hJ h hP hy n).2.1),
    contDiffOn_infty.mpr (fun n => (radialSystem_contDiffOn_nat hJ h hP hy n).2.2.1),
    contDiffOn_infty.mpr (fun n => (radialSystem_contDiffOn_nat hJ h hP hy n).2.2.2)⟩

-- @node: radialExtension_contDiffAt_of_pos
/-- If [F has continuous derivatives through order n at positive radii](hyp:hF)
and [x is nonzero](hyp:hx), then [the radial extension that evaluates F at the
Euclidean distance from the origin has continuous derivatives through order n at x](goal). -/
lemma radialExtension_contDiffAt_of_pos {m : ℕ} {F : ℝ → ℝ} {n : ℕ∞ω}
    (hF : ContDiffOn ℝ n F (Ioi 0)) {x : EuclideanSpace ℝ (Fin m)} (hx : x ≠ 0) :
    ContDiffAt ℝ n (radialExtension m F) x := by
  exact (hF.contDiffAt (isOpen_Ioi.mem_nhds (norm_pos_iff.mpr hx))).comp x
    (contDiffAt_norm ℝ hx)

-- @node: radialExtension_contDiff_of_local
/-- If [ε is positive](hyp:hε), [F has continuous derivatives through order n at
positive radii](hyp:hF), [the radial extension of F₀ has continuous derivatives
through order n on the open ball of radius ε about zero](hyp:h₀), and
[F agrees with F₀ for radii from zero inclusive to ε exclusive](hyp:heq), then
[the radial extension of F has continuous derivatives through order n everywhere](goal). -/
lemma radialExtension_contDiff_of_local {m : ℕ} {F F₀ : ℝ → ℝ} {ε : ℝ}
    {n : ℕ∞ω} (hε : 0 < ε) (hF : ContDiffOn ℝ n F (Ioi 0))
    (h₀ : ContDiffOn ℝ n (radialExtension m F₀) (Metric.ball 0 ε))
    (heq : ∀ r ∈ Ico 0 ε, F r = F₀ r) :
    ContDiff ℝ n (radialExtension m F) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    have hs : ContDiffAt ℝ n (radialExtension m F₀) 0 :=
      h₀.contDiffAt (Metric.isOpen_ball.mem_nhds (by simpa using hε))
    apply hs.congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin m)) hε] with x hx
    exact heq ‖x‖ ⟨norm_nonneg x, by simpa using hx⟩
  · exact radialExtension_contDiffAt_of_pos hF hx

-- @node: radialSystem_spatial_contDiff_of_local
/-- If [F₀ and P₀ satisfy the local solution conditions with radius ε](hyp:hLocal),
[F and P agree respectively with F₀ and P₀ for radii from zero inclusive to ε
exclusive](hyp:heq), [F and P satisfy the radial system with dimension nine,
coefficient eleven, and exponent 12/11 at all positive radii](hyp:h),
[P is strictly positive at positive radii](hyp:hP), and [F′ is strictly positive
at positive radii](hyp:hy), then [the nine-dimensional radial extensions of F and P
are both infinitely differentiable everywhere](goal). -/
lemma radialSystem_spatial_contDiff_of_local {ε : ℝ} {F₀ P₀ F P : ℝ → ℝ}
    (hLocal : LocalSolutionData ε F₀ P₀)
    (heq : ∀ r ∈ Ico 0 ε, F r = F₀ r ∧ P r = P₀ r)
    (h : RadialSystem radialDim radialK radialGamma F P (Ioi 0))
    (hP : ∀ r > 0, 0 < P r) (hy : ∀ r > 0, 0 < deriv F r) :
    ContDiff ℝ ∞ (radialExtension 9 F) ∧ ContDiff ℝ ∞ (radialExtension 9 P) := by
  have hs := radialSystem_contDiffOn isOpen_Ioi h hP hy
  exact ⟨radialExtension_contDiff_of_local hLocal.1 hs.1 hLocal.2.2.1
      (fun r hr => (heq r hr).1),
    radialExtension_contDiff_of_local hLocal.1 hs.2.1 hLocal.2.2.2.1
      (fun r hr => (heq r hr).2)⟩

end OaiSmoothNonquadraticAffine

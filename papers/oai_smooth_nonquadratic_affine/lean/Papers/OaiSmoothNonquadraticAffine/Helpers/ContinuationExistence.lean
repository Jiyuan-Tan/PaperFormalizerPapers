module

public import Papers.OaiSmoothNonquadraticAffine.Helpers.ContinuationODE
public import Mathlib.Analysis.ODE.ExistUnique

/-! # Local existence for the regular continuation system

Adjoining the radius as a clock turns the regular radial system into an
autonomous smooth ODE. Picard–Lindelöf then supplies a solution through every
state in the positive domain.
-/

public section

open Set Filter
open scoped Topology ContDiff

namespace OaiSmoothNonquadraticAffine

-- @node: continuation_augmented_contDiffAt
/-- If [the pressure coordinate is nonzero](hyp:hP) and [the slope coordinate is
nonzero](hyp:hy), [the continuation field augmented with a clock of unit speed is
infinitely differentiable at that radius and state](goal). -/
@[fun_prop] lemma continuation_augmented_contDiffAt {q : ℝ × (Fin 4 → ℝ)}
    (hP : q.2 1 ≠ 0) (hy : q.2 2 ≠ 0) :
    ContDiffAt ℝ ∞ (fun p : ℝ × (Fin 4 → ℝ) => ((1 : ℝ), continuationField p)) q := by
  exact contDiffAt_const.prodMk (continuationField_contDiffAt hP hy)

/-- If [the initial pressure is positive](hyp:hP) and [the initial slope is
positive](hyp:hy), [there are a state curve and a positive interval half-width
such that the curve passes through the initial state at the given radius and
solves the continuation ODE throughout that open interval](goal). -/
-- @node: continuation_local_state_exists
lemma continuation_local_state_exists {R : ℝ} {v : Fin 4 → ℝ}
    (hP : 0 < v 1) (hy : 0 < v 2) :
    ∃ (u : ℝ → Fin 4 → ℝ) (δ : ℝ), 0 < δ ∧ u R = v ∧
      ∀ r ∈ Ioo (R - δ) (R + δ), HasDerivAt u (continuationField (r, u r)) r := by
  have hs : ContDiffAt ℝ 1
      (fun p : ℝ × (Fin 4 → ℝ) => ((1 : ℝ), continuationField p)) (R, v) :=
    (continuation_augmented_contDiffAt hP.ne' hy.ne').of_le (by norm_num)
  obtain ⟨α, hα, δ, hδ, hd⟩ :=
    hs.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ R
  have hfst (r : ℝ) (hr : r ∈ Ioo (R - δ) (R + δ)) :
      HasDerivAt (fun r => (α r).1) 1 r :=
    (ContinuousLinearMap.fst ℝ ℝ (Fin 4 → ℝ)).hasFDerivAt.comp_hasDerivAt r (hd r hr)
  have hclock : EqOn (fun r => (α r).1) id (Ioo (R - δ) (R + δ)) := by
    apply isOpen_Ioo.eqOn_of_deriv_eq (convex_Ioo _ _).isPreconnected
      (fun r hr => (hfst r hr).differentiableAt.differentiableWithinAt)
      (fun r hr => differentiableAt_id.differentiableWithinAt)
      (fun r hr => by simpa using (hfst r hr).deriv)
      (show R ∈ Ioo (R - δ) (R + δ) by constructor <;> linarith)
    exact congrArg Prod.fst hα
  refine ⟨fun r => (α r).2, δ, hδ, congrArg Prod.snd hα, ?_⟩
  intro r hr
  have h := (ContinuousLinearMap.snd ℝ ℝ (Fin 4 → ℝ)).hasFDerivAt.comp_hasDerivAt r
    (hd r hr)
  change HasDerivAt (fun r => (α r).2) (continuationField (α r)) r at h
  have heq : continuationField (α r) = continuationField (r, (α r).2) :=
    congrArg continuationField (Prod.ext (hclock hr) rfl)
  rw [heq] at h
  exact h

/-- If [the initial radius is positive](hyp:hR), [the initial profile value is
positive](hyp:hF), [the initial pressure is positive](hyp:hP), and [the initial
slope is positive](hyp:hy), [a state curve solves the continuation ODE on some
open interval of positive half-width about that radius, passes through the
initial state, and has positive radius, profile, pressure, and slope throughout
the interval](goal). -/
-- @node: continuation_positive_local_state_exists
lemma continuation_positive_local_state_exists {R : ℝ} {v : Fin 4 → ℝ}
    (hR : 0 < R) (hF : 0 < v 0) (hP : 0 < v 1) (hy : 0 < v 2) :
    ∃ (u : ℝ → Fin 4 → ℝ) (δ : ℝ), 0 < δ ∧ u R = v ∧
      ∀ r ∈ Ioo (R - δ) (R + δ),
        (0 < r ∧ 0 < u r 0 ∧ 0 < u r 1 ∧ 0 < u r 2) ∧
        HasDerivAt u (continuationField (r, u r)) r := by
  obtain ⟨u, δ, hδ, hu, hd⟩ := continuation_local_state_exists hP hy
  have hRmem : R ∈ Ioo (R - δ) (R + δ) := by constructor <;> linarith
  have hc := (hd R hRmem).continuousAt
  have hpos : ∀ᶠ r in 𝓝 R, 0 < r ∧ 0 < u r 0 ∧ 0 < u r 1 ∧ 0 < u r 2 := by
    have h0 : ContinuousAt (fun r => u r 0) R := (continuous_apply 0).continuousAt.comp hc
    have h1 : ContinuousAt (fun r => u r 1) R := (continuous_apply 1).continuousAt.comp hc
    have h2 : ContinuousAt (fun r => u r 2) R := (continuous_apply 2).continuousAt.comp hc
    exact (lt_mem_nhds hR).and
      ((h0.eventually (lt_mem_nhds (by simpa [hu] using hF))).and
        ((h1.eventually (lt_mem_nhds (by simpa [hu] using hP))).and
          (h2.eventually (lt_mem_nhds (by simpa [hu] using hy)))))
  obtain ⟨η, hη, hηpos⟩ := Metric.eventually_nhds_iff.mp hpos
  refine ⟨u, min δ η, lt_min hδ hη, hu, fun r hr => ?_⟩
  have hrδ : r ∈ Ioo (R - δ) (R + δ) :=
    ⟨by linarith [min_le_left δ η, hr.1, hr.2], by linarith [min_le_left δ η, hr.1, hr.2]⟩
  have hrη : dist r R < η := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [min_le_right δ η, hr.1, hr.2]
  exact ⟨hηpos hrη, hd r hrδ⟩

/-- On [an open set of radii](hyp:hJ), if [the pressure and slope coordinates
never vanish](hyp:hpos) and [the state curve solves the continuation ODE at every
radius in the set](hyp:hd), [the state curve is infinitely differentiable on
that set](goal). -/
-- @node: continuation_state_contDiffOn
lemma continuation_state_contDiffOn {u : ℝ → Fin 4 → ℝ} {J : Set ℝ}
    (hJ : IsOpen J)
    (hpos : ∀ r ∈ J, u r 1 ≠ 0 ∧ u r 2 ≠ 0)
    (hd : ∀ r ∈ J, HasDerivAt u (continuationField (r, u r)) r) :
    ContDiffOn ℝ ∞ u J := by
  have hc : ContDiffOn ℝ ∞ continuationField
      {q : ℝ × (Fin 4 → ℝ) | q.2 1 ≠ 0 ∧ q.2 2 ≠ 0} :=
    fun q hq => (continuationField_contDiffAt hq.1 hq.2).contDiffWithinAt
  have hnat (n : ℕ) : ContDiffOn ℝ n u J := by
    induction n with
    | zero => exact contDiffOn_zero.mpr (fun r hr => (hd r hr).continuousAt.continuousWithinAt)
    | succ n ih =>
      rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_deriv_of_isOpen hJ]
      refine ⟨fun r hr => (hd r hr).differentiableAt.differentiableWithinAt, by simp, ?_⟩
      have hbound : (n : ℕ∞ω) ≤ ∞ := by
        exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top)
      apply ((hc.of_le hbound).comp (contDiffOn_id.prodMk ih) hpos).congr
      intro r hr
      exact (hd r hr).deriv
  exact contDiffOn_infty.mpr hnat

/-- On [an open set of radii](hyp:hJ), if [the pressure and slope coordinates
are positive throughout the set](hyp:hpos) and [the state curve solves the
continuation ODE there](hyp:hd), [its profile and pressure coordinates satisfy
the radial determinant and flux system with the paper's dimension and
constants on that set](goal). -/
-- @node: continuation_state_radialSystem
lemma continuation_state_radialSystem {u : ℝ → Fin 4 → ℝ} {J : Set ℝ}
    (hJ : IsOpen J)
    (hpos : ∀ r ∈ J, 0 < u r 1 ∧ 0 < u r 2)
    (hd : ∀ r ∈ J, HasDerivAt u (continuationField (r, u r)) r) :
    RadialSystem radialDim radialK radialGamma (fun r => u r 0) (fun r => u r 1) J := by
  have hs := continuation_state_contDiffOn hJ (fun r hr =>
    ⟨(hpos r hr).1.ne', (hpos r hr).2.ne'⟩) hd
  have hcoord (r : ℝ) (hr : r ∈ J) (i : Fin 4) := hasDerivAt_pi.mp (hd r hr) i
  have hF (r : ℝ) (hr : r ∈ J) : deriv (fun s => u s 0) r = u r 2 := by
    simpa [continuationField] using (hcoord r hr 0).deriv
  have hP (r : ℝ) (hr : r ∈ J) : deriv (fun s => u s 1) r = u r 3 := by
    simpa [continuationField] using (hcoord r hr 1).deriv
  intro r hr
  have hFe : deriv (fun s => u s 0) =ᶠ[𝓝 r] (fun s => u s 2) :=
    Filter.Eventually.mono (hJ.mem_nhds hr) (fun s hs => hF s hs)
  have hPe : deriv (fun s => u s 1) =ᶠ[𝓝 r] (fun s => u s 3) :=
    Filter.Eventually.mono (hJ.mem_nhds hr) (fun s hs => hP s hs)
  have hY : deriv (deriv (fun s => u s 0)) r =
      r ^ 8 * u r 0 * u r 1 ^ (-(12 / 11 : ℝ)) / u r 2 ^ 8 := by
    rw [hFe.deriv_eq]
    simpa [continuationField] using (hcoord r hr 2).deriv
  have hZ := (hcoord r hr 3).deriv
  dsimp [continuationField] at hZ
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ((contDiffOn_pi.mp hs) 0).contDiffAt (hJ.mem_nhds hr) |>.of_le (by decide)
  · exact ((contDiffOn_pi.mp hs) 1).contDiffAt (hJ.mem_nhds hr) |>.of_le (by decide)
  · rw [hF r hr, hY]
    dsimp [radialDim, radialGamma]
    exact mul_div_cancel₀ _ (pow_ne_zero 8 (hpos r hr).2.ne')
  · have hflux : (fun s => deriv (fun t => u t 0) s ^ 8 * deriv (fun t => u t 1) s)
        =ᶠ[𝓝 r] (fun s => u s 2 ^ 8 * u s 3) := by
      filter_upwards [hFe, hPe] with s hs hs'
      rw [hs, hs']
    change deriv (fun s => deriv (fun t => u t 0) s ^ 8 * deriv (fun t => u t 1) s) r = _
    have hfluxd := ((hcoord r hr 2).pow 8 |>.mul (hcoord r hr 3)).deriv
    change deriv (fun s => u s 2 ^ 8 * u s 3) r = _ at hfluxd
    rw [hflux.deriv_eq, hfluxd]
    dsimp [continuationField, radialDim, radialK, radialGamma]
    have hy := (hpos r hr).2.ne'
    norm_num only [show (1 : ℝ) - 12 / 11 = -(1 / 11 : ℝ) by norm_num]
    field_simp [hy]
    ring

/-- If [the initial radius is positive](hyp:hR), [the initial profile value is
positive](hyp:hF), [the initial pressure is positive](hyp:hP), and [the initial
slope is positive](hyp:hy), [there exist profile and pressure functions on an
open interval of positive half-width about that radius, matching all four
initial state coordinates and satisfying the radial system, with positive
radius, profile, pressure, profile slope, and profile second derivative
throughout the interval](goal). -/
-- @node: continuation_local_radial_exists
lemma continuation_local_radial_exists {R : ℝ} {v : Fin 4 → ℝ}
    (hR : 0 < R) (hF : 0 < v 0) (hP : 0 < v 1) (hy : 0 < v 2) :
    ∃ (F P : ℝ → ℝ) (δ : ℝ), 0 < δ ∧
      ![F R, P R, deriv F R, deriv P R] = v ∧
      RadialSystem radialDim radialK radialGamma F P (Ioo (R - δ) (R + δ)) ∧
      ∀ r ∈ Ioo (R - δ) (R + δ),
        0 < r ∧ 0 < F r ∧ 0 < P r ∧ 0 < deriv F r ∧ 0 < deriv (deriv F) r := by
  obtain ⟨u, δ, hδ, hu, hd⟩ := continuation_positive_local_state_exists hR hF hP hy
  have hcoord (r : ℝ) (hr : r ∈ Ioo (R - δ) (R + δ)) (i : Fin 4) :=
    hasDerivAt_pi.mp (hd r hr).2 i
  have hFu (r : ℝ) (hr : r ∈ Ioo (R - δ) (R + δ)) :
      deriv (fun s => u s 0) r = u r 2 := by
    simpa [continuationField] using (hcoord r hr 0).deriv
  have hPu (r : ℝ) (hr : r ∈ Ioo (R - δ) (R + δ)) :
      deriv (fun s => u s 1) r = u r 3 := by
    simpa [continuationField] using (hcoord r hr 1).deriv
  have hsys := continuation_state_radialSystem isOpen_Ioo
    (fun r hr => ⟨(hd r hr).1.2.2.1, (hd r hr).1.2.2.2⟩)
    (fun r hr => (hd r hr).2)
  have hRmem : R ∈ Ioo (R - δ) (R + δ) := by constructor <;> linarith
  refine ⟨fun r => u r 0, fun r => u r 1, δ, hδ, ?_, hsys, ?_⟩
  · rw [hFu R hRmem, hPu R hRmem]
    change ![u R 0, u R 1, u R 2, u R 3] = v
    rw [hu]
    ext i
    fin_cases i <;> rfl
  · intro r hr
    have hp := (hd r hr).1
    refine ⟨hp.1, hp.2.1, hp.2.2.1, by rw [hFu r hr]; exact hp.2.2.2, ?_⟩
    have hdet := (hsys r hr).2.2.1
    rw [hFu r hr] at hdet
    have hright : 0 < r ^ 8 * u r 0 * u r 1 ^ (-(12 / 11 : ℝ)) :=
      mul_pos (mul_pos (pow_pos hp.1 8) hp.2.1) (Real.rpow_pos_of_pos hp.2.2.1 _)
    change u r 2 ^ 8 * deriv (deriv (fun s => u s 0)) r = _ at hdet
    have hmul : 0 < u r 2 ^ 8 * deriv (deriv (fun s => u s 0)) r := by
      rw [hdet]
      exact hright
    exact (mul_pos_iff_of_pos_left (pow_pos hp.2.2.2 8)).mp hmul

/-- Given [normalized local solution data](hyp:hLocal), [a maximal positive
continuation with finite endpoint R](hyp:hCont), and [a positive radius
a](hyp:ha) [strictly below R](hyp:haR), [there are profile and pressure functions
solving the radial system on an open interval of positive half-width about R,
whose four-coordinate state at R is the left limit of the continuation and
whose radius, profile, pressure, profile slope, and profile second derivative
are positive throughout that interval](goal). -/
-- @node: continuation_endpoint_local_radial_exists
lemma continuation_endpoint_local_radial_exists {ε : ℝ} {F₀ P₀ F P : ℝ → ℝ}
    {R a : ℝ} (hLocal : LocalSolutionData ε F₀ P₀)
    (hCont : IsMaximalContinuation F₀ P₀ ε F P (R : WithTop ℝ))
    (ha : 0 < a) (haR : a < R) :
    ∃ (F' P' : ℝ → ℝ) (δ : ℝ), 0 < δ ∧
      Tendsto (fun r => ![F r, P r, deriv F r, deriv P r]) (𝓝[<] R)
        (𝓝 ![F' R, P' R, deriv F' R, deriv P' R]) ∧
      RadialSystem radialDim radialK radialGamma F' P' (Ioo (R - δ) (R + δ)) ∧
      ∀ r ∈ Ioo (R - δ) (R + δ),
        0 < r ∧ 0 < F' r ∧ 0 < P' r ∧ 0 < deriv F' r ∧ 0 < deriv (deriv F') r := by
  obtain ⟨v, hF, hP, hy, hv⟩ := continuation_state_tendsto_endpoint hLocal hCont ha haR
  obtain ⟨F', P', δ, hδ, hinit, hsys, hpos⟩ :=
    continuation_local_radial_exists (ha.trans haR) hF hP hy
  exact ⟨F', P', δ, hδ, hinit.symm ▸ hv, hsys, hpos⟩

end OaiSmoothNonquadraticAffine

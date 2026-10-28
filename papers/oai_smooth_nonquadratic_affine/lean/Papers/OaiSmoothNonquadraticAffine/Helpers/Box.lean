module

public import Papers.OaiSmoothNonquadraticAffine.Helpers.Autonomous
public import Papers.OaiSmoothNonquadraticAffine.Helpers.BoxFlow
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.Calculus.MeanValue

/-! # Forward invariance of the closed box and confinement of the radial solution -/

public section

open Set Filter
open scoped Topology

namespace OaiSmoothNonquadraticAffine

-- @node: lem:box
/-- [Every continuous trajectory on a closed time interval that solves the
autonomous differential equation before the right endpoint and starts in the box
remains in the box; moreover, every maximal positive continuation of normalized
local radial solution data has well-defined radial coordinates in the box at
every radius in its continuation interval](goal). -/
lemma box_forward_invariant :
    (∀ (z : ℝ → Fin 3 → ℝ) (a b : ℝ), a ≤ b → ContinuousOn z (Icc a b) →
      (∀ τ ∈ Ico a b, HasDerivAt z (autonomousField (z τ)) τ) →
      z a ∈ boxB → ∀ τ ∈ Icc a b, z τ ∈ boxB) ∧
    (∀ (ε : ℝ) (F₀ P₀ F P : ℝ → ℝ) (R : WithTop ℝ),
      LocalSolutionData ε F₀ P₀ → IsMaximalContinuation F₀ P₀ ε F P R →
      ∀ r ∈ radialInterval R,
        RadialCoordinateDomain F P r ∧ radialCoordinates F P r ∈ boxB)  := by
  refine ⟨autonomous_box_forward_invariant, ?_⟩
  intro ε F₀ P₀ F P R hLocal hCont r hr
  have hSol := hCont.2.2.2.1
  have hauto := autonomous_system_of_continuation hLocal hCont
  refine ⟨radial_coordinate_domain_of_positive hSol hr, ?_⟩
  have hupper : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      ∀ i : Fin 3, radialCoordinates F P s i < boxCorner i := by
    apply Filter.eventually_all.mpr
    intro i
    have ht := (tendsto_pi_nhds.mp hauto.2.1) i
    apply ht.eventually (gt_mem_nhds ?_)
    fin_cases i
    · change (0 : ℝ) < 9 / 2
      norm_num
    · change (1 : ℝ) < 7 / 2
      norm_num
    · change (0 : ℝ) < 33 / 7
      norm_num
  have hbox : ∀ᶠ s in 𝓝[>] (0 : ℝ), radialCoordinates F P s ∈ boxB := by
    filter_upwards [hupper, hauto.2.2] with s hs hp
    constructor
    · intro i
      have hl : 0 ≤ radialCoordinates F P s i := by
        fin_cases i
        · exact hp.1.le
        · exact hp.2.1.le
        · exact hp.2.2.le
      exact hl
    · intro i
      exact (hs i).le
  obtain ⟨s, hsbox, hs⟩ := (hbox.and (Ioo_mem_nhdsGT hr.1)).exists
  have hsr : Real.log s ≤ Real.log r := (Real.strictMonoOn_log.monotoneOn hs.1 hr.1 hs.2.le)
  have hderiv (τ : ℝ) (hτ : τ ∈ Icc (Real.log s) (Real.log r)) :
      HasDerivAt (fun t => radialCoordinates F P (Real.exp t))
        (autonomousField (radialCoordinates F P (Real.exp τ))) τ := by
    have her : Real.exp τ ≤ r := by
      simpa only [Real.exp_log hr.1] using Real.exp_le_exp.mpr hτ.2
    have he : Real.exp τ ∈ radialInterval R :=
      ⟨Real.exp_pos _, lt_of_le_of_lt (WithTop.coe_le_coe.mpr her) hr.2⟩
    simpa only [Real.log_exp] using radial_coordinates_log_derivative hSol he
  have hcontinuous : ContinuousOn (fun t => radialCoordinates F P (Real.exp t))
      (Icc (Real.log s) (Real.log r)) :=
    fun τ hτ => (hderiv τ hτ).continuousAt.continuousWithinAt
  have hstart : radialCoordinates F P (Real.exp (Real.log s)) ∈ boxB := by
    simpa only [Real.exp_log hs.1] using hsbox
  have hfinal := autonomous_box_forward_invariant
    (fun t => radialCoordinates F P (Real.exp t)) (Real.log s) (Real.log r)
    hsr hcontinuous (fun τ hτ => hderiv τ ⟨hτ.1, hτ.2.le⟩) hstart
    (Real.log r) ⟨hsr, le_rfl⟩
  simpa only [Real.exp_log hr.1] using hfinal

end OaiSmoothNonquadraticAffine

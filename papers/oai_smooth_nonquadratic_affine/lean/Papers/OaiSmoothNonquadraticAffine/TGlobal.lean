module

public import Papers.OaiSmoothNonquadraticAffine.Helpers.Box
public import Papers.OaiSmoothNonquadraticAffine.Helpers.ContinuationGluing
public import Papers.OaiSmoothNonquadraticAffine.Helpers.RadialHessian
public import Mathlib.Analysis.ODE.PicardLindelof

/-! # Global positive continuation and smooth spatial radial extensions -/

public section

open Set
open scoped ContDiff

namespace OaiSmoothNonquadraticAffine

-- @node: prop:global
/-- Given [local radial solution data for F₀ and P₀ with radius ε](hyp:hLocal),
[there exist profiles F and P agreeing with F₀ and P₀ for 0 ≤ r < ε, satisfying
the radial system with dimension nine, coefficient eleven, and exponent 12/11
at every positive radius, with F, P, F′, and F″ positive there, whose
nine-dimensional radial extensions are infinitely differentiable everywhere
and whose radial extension of F has a positive definite Hessian everywhere](goal). -/
theorem local_radial_solution_extends_globally (ε : ℝ) (F₀ P₀ : ℝ → ℝ)
    (hLocal : LocalSolutionData ε F₀ P₀) :
    ∃ F P : ℝ → ℝ,
      (∀ r ∈ Ico 0 ε, F r = F₀ r ∧ P r = P₀ r) ∧
      RadialSystem radialDim radialK radialGamma F P (Ioi 0) ∧
      (∀ r > 0, 0 < F r ∧ 0 < P r ∧ 0 < deriv F r ∧ 0 < deriv (deriv F) r) ∧
      ContDiff ℝ ∞ (radialExtension 9 F) ∧ ContDiff ℝ ∞ (radialExtension 9 P) ∧
      ∀ x, (hessianMatrix (radialExtension 9 F) x).PosDef := by
  suffices hExtend : ∃ F P : ℝ → ℝ,
      (∀ r ∈ Ico 0 ε, F r = F₀ r ∧ P r = P₀ r) ∧
      RadialSystem radialDim radialK radialGamma F P (Ioi 0) ∧
      (∀ r > 0, 0 < F r ∧ 0 < P r ∧ 0 < deriv F r ∧ 0 < deriv (deriv F) r) ∧
      ∀ x, (hessianMatrix (radialExtension 9 F) x).PosDef by
    obtain ⟨F, P, heq, hsys, hpos, hH⟩ := hExtend
    have hs := radialSystem_spatial_contDiff_of_local hLocal heq hsys
      (fun r hr => (hpos r hr).2.1) (fun r hr => (hpos r hr).2.2.1)
    exact ⟨F, P, heq, hsys, hpos, hs.1, hs.2, hH⟩
  obtain ⟨F, P, R, hCont⟩ := localSolutionData_exists_maximalContinuation hLocal
  suffices hGlobal : R = ⊤ by
    have hpos := hCont.2.2.2.1
    have hsys : RadialSystem radialDim radialK radialGamma F P (Ioi 0) := by
      simpa [hGlobal, radialInterval, Set.Ioi] using hpos.2.1
    have hH := radialSystem_hessian_posDef_of_local hLocal hCont.2.2.1 hsys
      (fun r hr => (hpos.2.2 r (by simpa [hGlobal, radialInterval] using hr)).2.1)
      (fun r hr => (hpos.2.2 r (by simpa [hGlobal, radialInterval] using hr)).2.2)
      (fun r hr => positiveRadialSolution_slope_deriv_pos hpos
        (by simpa [hGlobal, radialInterval] using hr))
    refine ⟨F, P, hCont.2.2.1, hsys, ?_, hH⟩
    intro r hr
    have hrR : r ∈ radialInterval R := by
      simpa [hGlobal, radialInterval] using hr
    have hp := hpos.2.2 r hrR
    exact ⟨hp.1, hp.2.1, hp.2.2, positiveRadialSolution_slope_deriv_pos hpos hrR⟩
  exact maximalContinuation_endpoint_eq_top hLocal hCont

end OaiSmoothNonquadraticAffine

module

public import Papers.OaiSmoothNonquadraticAffine.Helpers.LocalSmooth
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-! # Local radial existence through the regular integral fixed-point construction -/

public section

open Set
open scoped ContDiff

namespace OaiSmoothNonquadraticAffine

-- @node: lem:local
/-- [There exist a positive radius and profile and pressure functions satisfying
the normalized local solution conditions, including smooth spatial radial
extensions through the origin](goal). -/
lemma exists_local_radial_solution :
    ∃ ε : ℝ, 0 < ε ∧ ∃ F P : ℝ → ℝ, LocalSolutionData ε F P := by
  obtain ⟨δ, hδ, fp, hfp, hfix⟩ := exists_local_integral_solution
  let ε := min δ 1
  let F : ℝ → ℝ := fun r => (localRadialProfiles hδ fp hfp r).1
  let P : ℝ → ℝ := fun r => (localRadialProfiles hδ fp hfp r).2
  have hε : 0 < ε := lt_min hδ (by norm_num)
  have hrad := localRadialProfiles_system hδ hfp hfix
  have hzero := localRadialProfiles_zero hδ hfp
  have hAuxSmooth := localIntegralPrimitives_contDiffOn hδ hfp hfix
  have hOriginSmooth := localRadialProfiles_spatial_contDiffOn hδ hfp hAuxSmooth.1 hAuxSmooth.2
  have hHess := localRadialProfiles_hessians_zero hδ hfp hfix
  exact ⟨ε, hε, F, P, hε, hrad.1, hOriginSmooth.1, hOriginSmooth.2,
    congrArg Prod.fst hzero, congrArg Prod.snd hzero,
    hHess.1, hHess.2, hrad.2⟩

end OaiSmoothNonquadraticAffine

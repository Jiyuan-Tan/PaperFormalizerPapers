module

public import Papers.OaiSmoothNonquadraticAffine.Helpers.ContinuationMaximal
public import Mathlib.Analysis.Calculus.FDeriv.Extend

/-! # Joining regular state curves at a finite endpoint

The state limit and continuity of the regular field give matching one-sided
derivatives at the joining radius. The joined state is therefore a classical
solution, and regularity of the field then supplies smooth radial profiles.
-/

public section

open Set Filter
open scoped Topology ContDiff

namespace OaiSmoothNonquadraticAffine

/-- Suppose [the joining radius R is positive](hyp:hR), [the half-width δ is
positive](hyp:hδ), [the first state curve solves the continuation ODE between
zero and R](hyp:hu), and [the second solves it on the open interval of half-width
δ about R](hyp:hv). If [the first curve tends from the left to the second curve's
state at R](hyp:hlim), where [the pressure coordinate is nonzero](hyp:hP) and
[the slope coordinate is nonzero](hyp:hy), [the curve using the first state
below R and the second at and above R solves the continuation ODE at every
radius between zero and R plus δ](goal). -/
-- @node: continuation_state_join_hasDerivAt
lemma continuation_state_join_hasDerivAt {u v : ℝ → Fin 4 → ℝ} {R δ : ℝ}
    (hR : 0 < R) (hδ : 0 < δ)
    (hu : ∀ r ∈ Ioo 0 R, HasDerivAt u (continuationField (r, u r)) r)
    (hv : ∀ r ∈ Ioo (R - δ) (R + δ),
      HasDerivAt v (continuationField (r, v r)) r)
    (hlim : Tendsto u (𝓝[<] R) (𝓝 (v R)))
    (hP : v R 1 ≠ 0) (hy : v R 2 ≠ 0) :
    let w := fun r => if r < R then u r else v r
    ∀ r ∈ Ioo 0 (R + δ), HasDerivAt w (continuationField (r, w r)) r := by
  dsimp only
  let w := fun r => if r < R then u r else v r
  have hwR : w R = v R := by simp [w]
  have hleft (r : ℝ) (hr : r < R) : w =ᶠ[𝓝 r] u := by
    filter_upwards [isOpen_Iio.mem_nhds hr] with s hs
    exact if_pos hs
  have hright (r : ℝ) (hr : R < r) : w =ᶠ[𝓝 r] v := by
    filter_upwards [isOpen_Ioi.mem_nhds hr] with s hs
    exact if_neg (not_lt.mpr hs.le)
  have hlimw : Tendsto w (𝓝[<] R) (𝓝 (v R)) := by
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (if_pos hr).symm
  have hfield : Tendsto (fun r => continuationField (r, w r)) (𝓝[<] R)
      (𝓝 (continuationField (R, v R))) :=
    (continuationField_contDiffAt hP hy).continuousAt.tendsto.comp
      ((tendsto_id.mono_left nhdsWithin_le_nhds).prodMk_nhds hlimw)
  have hwl : HasDerivWithinAt w (continuationField (R, v R)) (Iic R) R := by
    apply hasDerivWithinAt_Iic_of_tendsto_deriv (s := Ioo 0 R)
    · intro r hr
      exact ((hu r hr).congr_of_eventuallyEq (hleft r hr.2)).differentiableAt.differentiableWithinAt
    · rw [ContinuousWithinAt, hwR]
      exact hlimw.mono_left (nhdsWithin_mono _ Ioo_subset_Iio_self)
    · exact Ioo_mem_nhdsLT hR
    · apply hfield.congr'
      filter_upwards [Ioo_mem_nhdsLT hR] with r hr
      rw [((hu r hr).congr_of_eventuallyEq (hleft r hr.2)).deriv]
      rw [(hleft r hr.2).eq_of_nhds]
  have hwr : HasDerivWithinAt w (continuationField (R, v R)) (Ici R) R := by
    apply (hv R ⟨by linarith, by linarith⟩).hasDerivWithinAt.congr
    · intro r hr
      exact if_neg (not_lt.mpr hr)
    · exact hwR
  change ∀ r ∈ Ioo 0 (R + δ), HasDerivAt w (continuationField (r, w r)) r
  intro r hr
  rcases lt_trichotomy r R with h | rfl | h
  · have hg := hleft r h
    rw [hg.eq_of_nhds]
    exact (hu r ⟨hr.1, h⟩).congr_of_eventuallyEq hg
  · rw [hwR]
    simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using hwl.union hwr
  · have hg := hright r h
    rw [hg.eq_of_nhds]
    exact (hv r ⟨by linarith, hr.2⟩).congr_of_eventuallyEq hg

/-- Given [normalized local solution data](hyp:hLocal) and [a maximal positive
continuation of those data](hyp:hCont), [its outer endpoint is infinity](goal). -/
-- @node: maximalContinuation_endpoint_eq_top
lemma maximalContinuation_endpoint_eq_top {ε : ℝ} {F₀ P₀ F P : ℝ → ℝ}
    {R : WithTop ℝ} (hLocal : LocalSolutionData ε F₀ P₀)
    (hCont : IsMaximalContinuation F₀ P₀ ε F P R) : R = ⊤ := by
  cases R using WithTop.recTopCoe with
  | top => rfl
  | coe R =>
    have hεR : ε ≤ R := by exact_mod_cast hCont.2.1
    have hR : 0 < R := hLocal.1.trans_le hεR
    have hsol := hCont.2.2.2.1
    have hmem {r : ℝ} (hr : r ∈ Ioo 0 R) : r ∈ radialInterval (R : WithTop ℝ) :=
      ⟨hr.1, by exact_mod_cast hr.2⟩
    obtain ⟨q, hqF, hqP, hqy, hlim⟩ :=
      continuation_state_tendsto_endpoint hLocal hCont
        (show 0 < R / 2 by linarith) (show R / 2 < R by linarith)
    obtain ⟨v, δ, hδ, hvR, hv⟩ := continuation_positive_local_state_exists hR hqF hqP hqy
    let u := fun r => ![F r, P r, deriv F r, deriv P r]
    let w := fun r => if r < R then u r else v r
    have hvpos : ∀ r ∈ Ioo (R - δ) (R + δ),
        0 < r ∧ 0 < v r 0 ∧ 0 < v r 1 ∧ 0 < v r 2 :=
      fun r hr => (hv r hr).1
    have hlimv : Tendsto u (𝓝[<] R) (𝓝 (v R)) := by
      simpa only [hvR] using hlim
    have hd : ∀ r ∈ Ioo 0 (R + δ), HasDerivAt w (continuationField (r, w r)) r :=
      continuation_state_join_hasDerivAt hR hδ
        (fun r hr => radialSystem_state_hasDerivAt hsol.2.1 (hmem hr)
          (hsol.2.2 r (hmem hr)).2.2.ne')
        (fun r hr => (hv r hr).2) hlimv
        (by simpa only [hvR] using hqP.ne') (by simpa only [hvR] using hqy.ne')
    have hwpos : ∀ r ∈ Ioo 0 (R + δ), 0 < w r 0 ∧ 0 < w r 1 ∧ 0 < w r 2 := by
      intro r hr
      by_cases hrR : r < R
      · simpa [w, u, hrR] using hsol.2.2 r (hmem ⟨hr.1, hrR⟩)
      · have hp := hvpos r ⟨by linarith, hr.2⟩
        simpa only [w, if_neg hrR] using hp.2
    have hsys := continuation_state_radialSystem isOpen_Ioo
      (fun r hr => ⟨(hwpos r hr).2.1, (hwpos r hr).2.2⟩) hd
    have hnew : PositiveRadialSolution (fun r => w r 0) (fun r => w r 1)
        ((R + δ : ℝ) : WithTop ℝ) := by
      refine ⟨?_, ?_, ?_⟩
      · exact_mod_cast (show 0 < R + δ by linarith)
      · simpa only [radialInterval, WithTop.coe_lt_coe, Set.Ioo] using hsys
      · intro r hr
        have hr' : r ∈ Ioo 0 (R + δ) := ⟨hr.1, by exact_mod_cast hr.2⟩
        have hdF := (hasDerivAt_pi.mp (hd r hr') 0).deriv
        have hdF' : deriv (fun s => w s 0) r = w r 2 := by
          simpa [continuationField] using hdF
        rw [hdF']
        exact hwpos r hr'
    have hlt : (R : WithTop ℝ) < ((R + δ : ℝ) : WithTop ℝ) := by
      exact_mod_cast (show R < R + δ by linarith)
    exact False.elim (hCont.2.2.2.2 ⟨R + δ, (fun r => w r 0), (fun r => w r 1),
      hlt, hnew, fun r hr => by
        have hrR : r < R := by
          rcases hr with hr | hr
          · simpa only [mem_singleton_iff.mp hr] using hR
          · exact_mod_cast hr.2
        simp [w, u, hrR]⟩)

end OaiSmoothNonquadraticAffine

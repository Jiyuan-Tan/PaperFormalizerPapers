module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
public import Mathlib.Analysis.CStarAlgebra.Projection
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Analysis.VonNeumannAlgebra.Basic
public import Papers.OaiNearInclusionsVon.Helpers.CornerPolar
public import Toolkit.Foundations.Analysis.Normed.CStarNormBounds

/-! Spectral rounding of operators close to orthogonal projections. -/

@[expose] public section

namespace Papers.OaiNearInclusionsVon

open scoped Topology

variable {A : Type*} [CStarAlgebra A]

/-- For [a real number x](hyp:x), [the spectral rounding function](goal)
returns [one when x is strictly greater than one half](step:1) and
[zero otherwise](step:2). -/
-- @node: cornerCut
noncomputable def cornerCut (x : ℝ) : ℝ := if 1 / 2 < x then 1 else 0

/-- If [a set of real numbers excludes one half](hyp:hs), then
[the spectral rounding function is continuous on that set](goal). -/
-- @node: cornerCut_continuousOn
@[fun_prop] lemma cornerCut_continuousOn (s : Set ℝ) (hs : (1 / 2 : ℝ) ∉ s) :
    ContinuousOn cornerCut s := by
  classical
  apply ContinuousOn.if _ continuousOn_const continuousOn_const
  intro x hx
  have heq : x = (1 / 2 : ℝ) := by
    have hfront : x ∈ frontier (Set.Ioi (1 / 2 : ℝ)) := hx.2
    simpa only [frontier_Ioi, Set.mem_singleton_iff] using hfront
  exact (hs (heq ▸ hx.1)).elim

/-- If [E is an orthogonal projection](hyp:hE) and [the norm distance
from X to E is less than one half](hyp:hsmall), then [one half does
not belong to the real spectrum of X](goal). -/
-- @node: corner_half_not_mem_spectrum
lemma corner_half_not_mem_spectrum (X E : A) (hE : IsStarProjection E)
    (hsmall : ‖X - E‖ < 1 / 2) : (1 / 2 : ℝ) ∉ spectrum ℝ X := by
  intro hx
  have h := Toolkit.Foundations.Analysis.Normed.min_norm_norm_sub_one_le_norm_sub_of_mem_spectrum X E hE (1 / 2) hx
  norm_num at h
  linarith

/-- If [d is less than one half](hyp:hd) and [x is within d of zero
or one](hyp:hx), then [rounding x at the one-half threshold changes
it by at most d](goal). -/
-- @node: cornerCut_error_bound
lemma cornerCut_error_bound (x d : ℝ) (hd : d < 1 / 2)
    (hx : min ‖x‖ ‖x - 1‖ ≤ d) : ‖cornerCut x - x‖ ≤ d := by
  rcases min_le_iff.mp hx with hx | hx
  · have hleft : ¬ (1 / 2 : ℝ) < x := by
      rw [Real.norm_eq_abs] at hx
      have := (abs_le.mp hx).2
      linarith
    simpa only [cornerCut, if_neg hleft, zero_sub, norm_neg] using hx
  · have hright : (1 / 2 : ℝ) < x := by
      rw [Real.norm_eq_abs] at hx
      have := (abs_le.mp hx).1
      linarith
    simpa only [cornerCut, if_pos hright, norm_sub_rev 1 x] using hx

/-- For [an algebra element X](hyp:X), [its spectral rounding](goal)
is obtained by applying the function that is one strictly above one half
and zero otherwise to X through continuous functional calculus. -/
-- @node: cornerSpectralProjection
noncomputable def cornerSpectralProjection (X : A) : A := cfc cornerCut X

/-- If [X is self-adjoint](hyp:hX), [E is an orthogonal projection](hyp:hE),
and [the norm distance from X to E is less than one half](hyp:hsmall), then
[the spectral rounding of X is an orthogonal projection, its distance from X
is at most the distance from X to E, and its distance from E is at most
twice the distance from X to E](goal). -/
-- @node: cornerSpectralProjection_spec
lemma cornerSpectralProjection_spec (X E : A) (hX : IsSelfAdjoint X)
    (hE : IsStarProjection E) (hsmall : ‖X - E‖ < 1 / 2) :
    IsStarProjection (cornerSpectralProjection X) ∧
      ‖cornerSpectralProjection X - X‖ ≤ ‖X - E‖ ∧
      ‖cornerSpectralProjection X - E‖ ≤ 2 * ‖X - E‖ := by
  have hf := cornerCut_continuousOn (spectrum ℝ X)
    (corner_half_not_mem_spectrum X E hE hsmall)
  have hp : IsStarProjection (cornerSpectralProjection X) := by
    refine ⟨?_, cfc_predicate cornerCut X⟩
    change cfc cornerCut X * cfc cornerCut X = cfc cornerCut X
    rw [← cfc_mul cornerCut cornerCut X hf hf]
    apply cfc_congr
    intro x _
    simp only [cornerCut]
    split <;> norm_num
  have herr : ‖cornerSpectralProjection X - X‖ ≤ ‖X - E‖ := by
    have heq : cornerSpectralProjection X - X = cfc (fun x => cornerCut x - x) X := by
      rw [cfc_sub cornerCut (fun x : ℝ => x) X hf (by fun_prop), cfc_id' ℝ X hX]
      rfl
    rw [heq]
    apply norm_cfc_le (norm_nonneg _)
    intro x hx
    exact cornerCut_error_bound x _ hsmall (Toolkit.Foundations.Analysis.Normed.min_norm_norm_sub_one_le_norm_sub_of_mem_spectrum X E hE x hx)
  refine ⟨hp, herr, ?_⟩
  calc
    ‖cornerSpectralProjection X - E‖ ≤ ‖cornerSpectralProjection X - X‖ + ‖X - E‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2 * ‖X - E‖ := by linarith

/-- If [X belongs to the von Neumann algebra M](hyp:hX), then
[the spectral rounding of X also belongs to M](goal). -/
-- @node: cornerSpectralProjection_mem
lemma cornerSpectralProjection_mem {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (M : VonNeumannAlgebra K)
    (X : K →L[ℂ] K) (hX : X ∈ M) : cornerSpectralProjection X ∈ M := by
  change cornerSpectralProjection X ∈ (M : Set (K →L[ℂ] K))
  rw [← M.centralizer_centralizer]
  intro Y hY
  have hcomm : Commute X Y := hY X hX
  exact (hcomm.cfc_real cornerCut).eq.symm

open Filter

/-- For [operator sequences T and E](hyp:T,E) and [a sequence of von Neumann
algebras M](hyp:M), suppose [each E is an orthogonal projection](hyp:hE),
[each T belongs to the corresponding algebra M](hyp:hT), and
[the norm distance from the adjoint of T times T to E tends to zero](hyp:herr).
Then [there is a sequence of orthogonal projections, each belonging to its
corresponding algebra M, whose norm distance from E tends to zero](goal). -/
-- @node: corner_spectral_projections
lemma corner_spectral_projections {K : ℕ → Type*} [∀ n, NormedAddCommGroup (K n)]
    [∀ n, InnerProductSpace ℂ (K n)] [∀ n, CompleteSpace (K n)]
    (T E : ∀ n, K n →L[ℂ] K n) (M : ∀ n, VonNeumannAlgebra (K n))
    (hE : ∀ n, IsStarProjection (E n)) (hT : ∀ n, T n ∈ M n)
    (herr : Tendsto (fun n => ‖star (T n) * T n - E n‖) atTop (𝓝 0)) :
    ∃ Q : ∀ n, K n →L[ℂ] K n,
      (∀ n, IsStarProjection (Q n) ∧ Q n ∈ M n) ∧
      Tendsto (fun n => ‖Q n - E n‖) atTop (𝓝 0) := by
  classical
  let X := fun n => star (T n) * T n
  let Q := fun n => if ‖X n - E n‖ < (1 / 2 : ℝ)
    then cornerSpectralProjection (X n) else 0
  have hsmall : ∀ᶠ n in atTop, ‖X n - E n‖ < (1 / 2 : ℝ) :=
    herr.eventually (gt_mem_nhds (by norm_num))
  refine ⟨Q, ?_, ?_⟩
  · intro n
    dsimp [Q]
    split_ifs with hn
    · exact ⟨(cornerSpectralProjection_spec (X n) (E n)
        (star_mul_self_nonneg _).isSelfAdjoint (hE n) hn).1,
        cornerSpectralProjection_mem (M n) (X n) (mul_mem (star_mem (hT n)) (hT n))⟩
    · exact ⟨IsStarProjection.zero _, zero_mem _⟩
  · apply squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) _
      (show Tendsto (fun n => 2 * ‖X n - E n‖) atTop (𝓝 0) by
        simpa only [mul_zero] using herr.const_mul 2)
    filter_upwards [hsmall] with n hn
    dsimp [Q]
    rw [if_pos hn]
    exact (cornerSpectralProjection_spec (X n) (E n)
      (star_mul_self_nonneg _).isSelfAdjoint (hE n) hn).2.2

end Papers.OaiNearInclusionsVon

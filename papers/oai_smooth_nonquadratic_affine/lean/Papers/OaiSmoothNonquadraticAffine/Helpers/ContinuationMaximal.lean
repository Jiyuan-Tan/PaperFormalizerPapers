module

public import Papers.OaiSmoothNonquadraticAffine.Helpers.ContinuationUniqueness

/-! # Maximal positive continuations

Overlap uniqueness glues all extensions of the local profiles. Their outer
endpoints have a supremum, and the glued profiles solve the radial system on
that entire interval, so no larger positive extension exists.
-/

public section

open Set Filter
open scoped Topology ContDiff

namespace OaiSmoothNonquadraticAffine

-- @node: radialInterval_isOpen
/-- [The set of positive radii below the given outer endpoint is open, including
when that endpoint is infinity](goal). -/
lemma radialInterval_isOpen (R : WithTop ℝ) : IsOpen (radialInterval R) := by
  cases R using WithTop.recTopCoe with
  | top => simpa [radialInterval, Set.Ioi] using (isOpen_Ioi : IsOpen (Ioi (0 : ℝ)))
  | coe b => simpa [radialInterval, Set.Ioo] using (isOpen_Ioo : IsOpen (Ioo (0 : ℝ) b))

/-- If [a profile and pressure satisfy the radial system on a set of
radii](hyp:h), [r belongs to that set](hyp:hr), [a replacement profile agrees
with the original in a neighborhood of r](hyp:hF), and [a replacement pressure
agrees with the original in a neighborhood of r](hyp:hP), [the replacement pair
satisfies the same radial system at r](goal). -/
-- @node: radialSystem_congr_germ
lemma radialSystem_congr_germ {m : ℕ} {k γ r : ℝ} {F P G Q : ℝ → ℝ}
    {J : Set ℝ} (h : RadialSystem m k γ F P J) (hr : r ∈ J)
    (hF : G =ᶠ[𝓝 r] F) (hP : Q =ᶠ[𝓝 r] P) :
    RadialSystem m k γ G Q {r} := by
  have hflux : (fun s => deriv G s ^ (m - 1) * deriv Q s) =ᶠ[𝓝 r]
      (fun s => deriv F s ^ (m - 1) * deriv P s) := by
    filter_upwards [hF.deriv, hP.deriv] with s hs hs'
    rw [hs, hs']
  intro s hs
  have he : s = r := mem_singleton_iff.mp hs
  subst s
  refine ⟨(h r hr).1.congr_of_eventuallyEq hF,
    (h r hr).2.1.congr_of_eventuallyEq hP, ?_, ?_⟩
  · rw [hF.deriv_eq, hF.deriv.deriv_eq, hF.eq_of_nhds, hP.eq_of_nhds]
    exact (h r hr).2.2.1
  · rw [hflux.deriv_eq, hP.eq_of_nhds]
    exact (h r hr).2.2.2

/-- For [a positive radial solution](hyp:h) and [a radius in its solution
interval](hyp:hr), [the profile's second derivative at that radius is
positive](goal). -/
-- @node: positiveRadialSolution_slope_deriv_pos
lemma positiveRadialSolution_slope_deriv_pos {F P : ℝ → ℝ} {R : WithTop ℝ}
    (h : PositiveRadialSolution F P R) {r : ℝ} (hr : r ∈ radialInterval R) :
    0 < deriv (deriv F) r := by
  have hp := h.2.2 r hr
  have hdet := (h.2.1 r hr).2.2.1
  have hright : 0 < r ^ (radialDim - 1) * F r * P r ^ (-radialGamma) :=
    mul_pos (mul_pos (pow_pos hr.1 _) hp.1) (Real.rpow_pos_of_pos hp.2.1 _)
  have hmul : 0 < deriv F r ^ (radialDim - 1) * deriv (deriv F) r := by
    rw [hdet]
    exact hright
  exact (mul_pos_iff_of_pos_left (pow_pos hp.2.2 _)).mp hmul

/-- Given [normalized local solution data on an interval of radius ε](hyp:hLocal),
[there exist profile and pressure functions and an outer endpoint, possibly
infinite, forming a maximal positive continuation of those data](goal). -/
-- @node: localSolutionData_exists_maximalContinuation
lemma localSolutionData_exists_maximalContinuation {ε : ℝ} {F₀ P₀ : ℝ → ℝ}
    (hLocal : LocalSolutionData ε F₀ P₀) :
    ∃ (F P : ℝ → ℝ) (R : WithTop ℝ), IsMaximalContinuation F₀ P₀ ε F P R := by
  classical
  let S : Set (WithTop ℝ) := {R | (ε : WithTop ℝ) ≤ R ∧
    ∃ F P : ℝ → ℝ, PositiveRadialSolution F P R ∧
      ∀ r ∈ Ico 0 ε, F r = F₀ r ∧ P r = P₀ r}
  have hseed : (ε : WithTop ℝ) ∈ S := by
    refine ⟨le_rfl, F₀, P₀, ⟨?_, ?_, ?_⟩, fun _ _ => ⟨rfl, rfl⟩⟩
    · exact_mod_cast hLocal.1
    · simpa [radialInterval, Set.Ioo] using hLocal.2.1
    · intro r hr
      have hr' : r ∈ Ioo 0 ε := ⟨hr.1, by exact_mod_cast hr.2⟩
      exact ⟨(hLocal.2.2.2.2.2.2.2.2 r hr').1,
        (hLocal.2.2.2.2.2.2.2.2 r hr').2.1,
        (hLocal.2.2.2.2.2.2.2.2 r hr').2.2.1⟩
  have hSne : S.Nonempty := ⟨ε, hseed⟩
  have hSb : BddAbove S := ⟨⊤, fun _ _ => le_top⟩
  let R := sSup S
  have hεR : (ε : WithTop ℝ) ≤ R := le_csSup hSb hseed
  have hcover : ∀ r ∈ radialInterval R,
      ∃ b ∈ S, r ∈ radialInterval b := by
    intro r hr
    obtain ⟨b, hb, hrb⟩ := (lt_csSup_iff hSb hSne).mp hr.2
    exact ⟨b, hb, hr.1, hrb⟩
  -- Choose one extension at each point. Uniqueness makes this choice locally
  -- equal to every extension whose interval contains the point.
  let E (r : ℝ) : Prop := ∃ b ∈ S, r ∈ radialInterval b
  have hchoose : ∀ r, E r → ∃ F P : ℝ → ℝ,
      ∃ b ∈ S, r ∈ radialInterval b ∧ PositiveRadialSolution F P b ∧
        ∀ s ∈ Ico 0 ε, F s = F₀ s ∧ P s = P₀ s := by
    intro r hr
    obtain ⟨b, hb, hrb⟩ := hr
    obtain ⟨G, Q, hGQ, heq⟩ := hb.2
    exact ⟨G, Q, b, hb, hrb, hGQ, heq⟩
  choose G Q b hb hrb hsol heq using hchoose
  let F : ℝ → ℝ := fun r => if h : E r then G r h r else F₀ r
  let P : ℝ → ℝ := fun r => if h : E r then Q r h r else P₀ r
  have hagree : ∀ c ∈ S, ∀ U V : ℝ → ℝ,
      PositiveRadialSolution U V c →
      (∀ s ∈ Ico 0 ε, U s = F₀ s ∧ V s = P₀ s) →
      ∀ r ∈ radialInterval c, F r = U r ∧ P r = V r := by
    intro c hc U V hUV hUVeq r hr
    have hE : E r := ⟨c, hc, hr⟩
    have hov := positiveRadialSolution_eqOn_overlap hLocal.1 (hb r hE).1 hc.1
      (hsol r hE) hUV (heq r hE) hUVeq r ⟨hrb r hE, hr⟩
    simpa only [F, P, dif_pos hE] using hov
  have hinitial : ∀ r ∈ Ico 0 ε, F r = F₀ r ∧ P r = P₀ r := by
    intro r hr
    by_cases hE : E r
    · simpa only [F, P, dif_pos hE] using heq r hE r hr
    · simp only [F, P, dif_neg hE, and_self]
  have hgerm : ∀ c ∈ S, ∀ U V : ℝ → ℝ,
      PositiveRadialSolution U V c →
      (∀ s ∈ Ico 0 ε, U s = F₀ s ∧ V s = P₀ s) →
      ∀ r ∈ radialInterval c, F =ᶠ[𝓝 r] U ∧ P =ᶠ[𝓝 r] V := by
    intro c hc U V hUV hUVeq r hr
    have ha : ∀ᶠ s in 𝓝 r, F s = U s ∧ P s = V s :=
      Filter.Eventually.mono ((radialInterval_isOpen c).mem_nhds hr)
        (fun s hs => hagree c hc U V hUV hUVeq s hs)
    exact ⟨ha.mono (fun _ h => h.1), ha.mono (fun _ h => h.2)⟩
  have hpositive : PositiveRadialSolution F P R := by
    refine ⟨?_, ?_, ?_⟩
    · exact (show (0 : WithTop ℝ) < ε by exact_mod_cast hLocal.1).trans_le hεR
    · intro r hr
      obtain ⟨c, hc, hrc⟩ := hcover r hr
      obtain ⟨U, V, hUV, hUVeq⟩ := hc.2
      have hg := hgerm c hc U V hUV hUVeq r hrc
      exact radialSystem_congr_germ hUV.2.1 hrc hg.1 hg.2 r (by simp)
    · intro r hr
      obtain ⟨c, hc, hrc⟩ := hcover r hr
      obtain ⟨U, V, hUV, hUVeq⟩ := hc.2
      have hg := hgerm c hc U V hUV hUVeq r hrc
      rw [hg.1.eq_of_nhds, hg.2.eq_of_nhds, hg.1.deriv_eq]
      exact hUV.2.2 r hrc
  refine ⟨F, P, R, hLocal.1, hεR, hinitial, hpositive, ?_⟩
  rintro ⟨R', F', P', hRR', hpos', hext⟩
  have hmem : R' ∈ S := by
    refine ⟨hεR.trans hRR'.le, F', P', hpos', ?_⟩
    intro r hr
    have hrR : r ∈ insert 0 (radialInterval R) := by
      rcases eq_or_lt_of_le hr.1 with he | hpos
      · exact Or.inl he.symm
      · exact mem_insert_of_mem _ ⟨hpos,
          (show (r : WithTop ℝ) < ε by exact_mod_cast hr.2).trans_le hεR⟩
    exact ⟨(hext r hrR).1.trans (hinitial r hr).1,
      (hext r hrR).2.trans (hinitial r hr).2⟩
  exact (not_lt_of_ge (le_csSup hSb hmem)) hRR'

end OaiSmoothNonquadraticAffine

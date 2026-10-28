module

public import Papers.OaiSmoothNonquadraticAffine.Helpers.Box

/-! # Compact radial windows in the finite-endpoint continuation argument -/

@[expose] public section

open Set
open scoped ContDiff

namespace OaiSmoothNonquadraticAffine

/-- For [a finite outer endpoint R](hyp:R) that [is positive](hyp:_hR) and [an inner
radius r₀](hyp:r₀) that [is positive](hyp:_hr₀) and [is less than R](hyp:_hr₀R), the
[continuation window](goal) consists of radii at least r₀ and strictly below R. -/
def continuationWindow (R : ℝ) (_hR : 0 < R) -- @realizes R(positive finite endpoint)
    (r₀ : ℝ) (_hr₀ : 0 < r₀) (_hr₀R : r₀ < R) : Set ℝ := -- @realizes r_0(radius in (0,R))
  Set.Ico r₀ R

-- @node: continuation_scalar_ratio_bounds
/-- Given [normalized local radial solution data F₀ and P₀ on radius ε](hyp:hLocal),
[a maximal positive continuation F and P up to R](hyp:hCont), and [a radius r in
the positive continuation interval](hyp:hr), [the ratios rF′/F, rF″/F′ and −rP′/P
at r lie respectively between zero and 9/2, zero and 7/2, and zero and 33/2](goal). -/
lemma continuation_scalar_ratio_bounds {ε : ℝ} {F₀ P₀ F P : ℝ → ℝ}
    {R : WithTop ℝ} (hLocal : LocalSolutionData ε F₀ P₀)
    (hCont : IsMaximalContinuation F₀ P₀ ε F P R)
    {r : ℝ} (hr : r ∈ radialInterval R) :
    (0 ≤ r * deriv F r / F r ∧ r * deriv F r / F r ≤ 9 / 2) ∧
    (0 ≤ r * deriv (deriv F) r / deriv F r ∧
      r * deriv (deriv F) r / deriv F r ≤ 7 / 2) ∧
    (0 ≤ -(r * deriv P r / P r) ∧ -(r * deriv P r / P r) ≤ 33 / 2) := by
  obtain ⟨hd, hb⟩ := box_forward_invariant.2 ε F₀ P₀ F P R hLocal hCont r hr
  rw [radialCoordinates_eq_of_domain hd] at hb
  have hA : 0 ≤ r * deriv F r / F r ∧ r * deriv F r / F r ≤ 9 / 2 :=
    ⟨hb.1 0, hb.2 0⟩
  have hB : 0 ≤ r * deriv (deriv F) r / deriv F r ∧
      r * deriv (deriv F) r / deriv F r ≤ 7 / 2 := ⟨hb.1 1, hb.2 1⟩
  have hD : 0 ≤ -(r * deriv P r / P r) / (r * deriv (deriv F) r / deriv F r) ∧
      -(r * deriv P r / P r) / (r * deriv (deriv F) r / deriv F r) ≤ 33 / 7 :=
    ⟨hb.1 2, hb.2 2⟩
  have hC₀ : 0 ≤ -(r * deriv P r / P r) := by
    have := (le_div_iff₀ hd.2.2.2.2).mp hD.1
    simpa using this
  have hC₁ := (div_le_iff₀ hd.2.2.2.2).mp hD.2
  exact ⟨hA, hB, hC₀, by nlinarith [hB.2]⟩

-- @node: continuation_log_growth_le
/-- Suppose [a is positive](hyp:ha), [a is at most b](hyp:hab), [f is differentiable
at every point of the closed interval from a to b](hyp:hf), [f is positive throughout
that interval](hyp:hp), and [x times the derivative of f divided by f is at most c
throughout that interval](hyp:hb). Then [the increase in log f from a to b is at
most c times the increase in log radius](goal). -/
lemma continuation_log_growth_le {f : ℝ → ℝ} {a b c : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, DifferentiableAt ℝ f x)
    (hp : ∀ x ∈ Icc a b, 0 < f x)
    (hb : ∀ x ∈ Icc a b, x * deriv f x / f x ≤ c) :
    Real.log (f b) - Real.log (f a) ≤ c * (Real.log b - Real.log a) := by
  have hd (x : ℝ) (hx : x ∈ Icc a b) :
      HasDerivAt (fun t => Real.log (f t) - c * Real.log t)
        (deriv f x / f x - c / x) x := by
    convert ((hf x hx).hasDerivAt.log (hp x hx).ne').sub
      ((Real.hasDerivAt_log (ha.trans_le hx.1).ne').const_mul c) using 1 <;> rfl
  have hm : AntitoneOn (fun t => Real.log (f t) - c * Real.log t) (Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt)
    intro x hx
    have hx' := interior_subset hx
    rw [(hd x hx').deriv]
    have he : deriv f x / f x - c / x = (x * deriv f x / f x - c) / x := by
      field_simp [(ha.trans_le hx'.1).ne']
    rw [he]
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hb x hx'))
      (ha.le.trans hx'.1)
  have hi := hm ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  nlinarith

-- @node: continuation_log_growth_ge
/-- Suppose [a is positive](hyp:ha), [a is at most b](hyp:hab), [f is differentiable
at every point of the closed interval from a to b](hyp:hf), [f is positive throughout
that interval](hyp:hp), and [x times the derivative of f divided by f is at least c
throughout that interval](hyp:hb). Then [the increase in log f from a to b is at
least c times the increase in log radius](goal). -/
lemma continuation_log_growth_ge {f : ℝ → ℝ} {a b c : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, DifferentiableAt ℝ f x)
    (hp : ∀ x ∈ Icc a b, 0 < f x)
    (hb : ∀ x ∈ Icc a b, c ≤ x * deriv f x / f x) :
    c * (Real.log b - Real.log a) ≤ Real.log (f b) - Real.log (f a) := by
  have hi := continuation_log_growth_le (f := fun x => (f x)⁻¹) ha hab
    (fun x hx => (hf x hx).inv (hp x hx).ne')
    (fun x hx => inv_pos.mpr (hp x hx)) (c := -c) ?_
  · simp only [Real.log_inv] at hi
    nlinarith
  · intro x hx
    change x * deriv f⁻¹ x / (f x)⁻¹ ≤ -c
    rw [((hf x hx).hasDerivAt.inv (hp x hx).ne').deriv]
    have he : x * (-(deriv f x) / f x ^ 2) / (f x)⁻¹ =
        -(x * deriv f x / f x) := by
      field_simp [(hp x hx).ne']
    rw [he]
    exact neg_le_neg (hb x hx)

-- @node: continuation_radial_segment_bounds
/-- Given [normalized local radial solution data F₀ and P₀ on radius ε](hyp:hLocal)
and [a maximal positive continuation F and P up to R](hyp:hCont), suppose [a lies
in the positive continuation interval](hyp:ha), [b lies in that interval](hyp:hb),
and [a is at most b](hyp:hab). Then [F(b) lies between F(a) and F(a)(b/a) to the
power 9/2, F′(b) lies between F′(a) and F′(a)(b/a) to the power 7/2, and P(b)
lies between P(a)(a/b) to the power 33/2 and P(a)](goal). -/
lemma continuation_radial_segment_bounds {ε : ℝ} {F₀ P₀ F P : ℝ → ℝ}
    {R : WithTop ℝ} (hLocal : LocalSolutionData ε F₀ P₀)
    (hCont : IsMaximalContinuation F₀ P₀ ε F P R)
    {a b : ℝ} (ha : a ∈ radialInterval R) (hb : b ∈ radialInterval R) (hab : a ≤ b) :
    (F a ≤ F b ∧ F b ≤ F a * (b / a) ^ (9 / 2 : ℝ)) ∧
    (deriv F a ≤ deriv F b ∧ deriv F b ≤ deriv F a * (b / a) ^ (7 / 2 : ℝ)) ∧
    (P a * (a / b) ^ (33 / 2 : ℝ) ≤ P b ∧ P b ≤ P a) := by
  have hSol := hCont.2.2.2.1
  have hm (x : ℝ) (hx : x ∈ Icc a b) : x ∈ radialInterval R :=
    ⟨ha.1.trans_le hx.1, lt_of_le_of_lt (WithTop.coe_le_coe.mpr hx.2) hb.2⟩
  have hdF (x : ℝ) (hx : x ∈ Icc a b) : DifferentiableAt ℝ F x :=
    (hSol.2.1 x (hm x hx)).1.differentiableAt (by norm_num)
  have hdy (x : ℝ) (hx : x ∈ Icc a b) : DifferentiableAt ℝ (deriv F) x :=
    ((hSol.2.1 x (hm x hx)).1.derivWithin (m := 1) (by norm_num)).differentiableAt_one
  have hdP (x : ℝ) (hx : x ∈ Icc a b) : DifferentiableAt ℝ P x :=
    (hSol.2.1 x (hm x hx)).2.1.differentiableAt (by norm_num)
  have hpF (x : ℝ) (hx : x ∈ Icc a b) := (hSol.2.2 x (hm x hx)).1
  have hpy (x : ℝ) (hx : x ∈ Icc a b) := (hSol.2.2 x (hm x hx)).2.2
  have hpP (x : ℝ) (hx : x ∈ Icc a b) := (hSol.2.2 x (hm x hx)).2.1
  have hrat (x : ℝ) (hx : x ∈ Icc a b) :=
    continuation_scalar_ratio_bounds hLocal hCont (hm x hx)
  have hF₀ := continuation_log_growth_ge ha.1 hab hdF hpF (c := 0)
    (fun x hx => (hrat x hx).1.1)
  have hF₁ := continuation_log_growth_le ha.1 hab hdF hpF
    (fun x hx => (hrat x hx).1.2)
  have hy₀ := continuation_log_growth_ge ha.1 hab hdy hpy (c := 0)
    (fun x hx => (hrat x hx).2.1.1)
  have hy₁ := continuation_log_growth_le ha.1 hab hdy hpy
    (fun x hx => (hrat x hx).2.1.2)
  have hP₀ := continuation_log_growth_ge ha.1 hab hdP hpP (c := -(33 / 2))
    (fun x hx => by linarith [(hrat x hx).2.2.2])
  have hP₁ := continuation_log_growth_le ha.1 hab hdP hpP (c := 0)
    (fun x hx => by linarith [(hrat x hx).2.2.1])
  have hp := hSol.2.2 a ha
  have hq := hSol.2.2 b hb
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · apply (Real.log_le_log_iff hp.1 hq.1).mp
    linarith
  · apply (Real.log_le_log_iff hq.1 (mul_pos hp.1
      (Real.rpow_pos_of_pos (div_pos hb.1 ha.1) _))).mp
    rw [Real.log_mul hp.1.ne' (Real.rpow_pos_of_pos (div_pos hb.1 ha.1) _).ne',
      Real.log_rpow (div_pos hb.1 ha.1), Real.log_div hb.1.ne' ha.1.ne']
    linarith
  · apply (Real.log_le_log_iff hp.2.2 hq.2.2).mp
    linarith
  · apply (Real.log_le_log_iff hq.2.2 (mul_pos hp.2.2
      (Real.rpow_pos_of_pos (div_pos hb.1 ha.1) _))).mp
    rw [Real.log_mul hp.2.2.ne' (Real.rpow_pos_of_pos (div_pos hb.1 ha.1) _).ne',
      Real.log_rpow (div_pos hb.1 ha.1), Real.log_div hb.1.ne' ha.1.ne']
    linarith
  · apply (Real.log_le_log_iff (mul_pos hp.2.1
      (Real.rpow_pos_of_pos (div_pos ha.1 hb.1) _)) hq.2.1).mp
    rw [Real.log_mul hp.2.1.ne' (Real.rpow_pos_of_pos (div_pos ha.1 hb.1) _).ne',
      Real.log_rpow (div_pos ha.1 hb.1), Real.log_div ha.1.ne' hb.1.ne']
    linarith
  · apply (Real.log_le_log_iff hq.2.1 hp.2.1).mp
    linarith

-- @node: continuation_finite_endpoint_bounds
/-- Given [normalized local radial solution data F₀ and P₀ on radius ε](hyp:hLocal)
and [a maximal positive continuation F and P with finite endpoint R](hyp:hCont),
suppose [a is positive](hyp:ha), [a is at most r](hyp:har), and [r is less than R](hyp:hrR).
Then [F(r) lies between F(a) and F(a)(R/a) to the power 9/2, F′(r) lies between
F′(a) and F′(a)(R/a) to the power 7/2, P(r) lies between P(a)(a/R) to the power
33/2 and P(a), and the absolute value of P′(r) is at most (33/2)P(a)/a](goal). -/
lemma continuation_finite_endpoint_bounds {ε : ℝ} {F₀ P₀ F P : ℝ → ℝ}
    {R a r : ℝ} (hLocal : LocalSolutionData ε F₀ P₀)
    (hCont : IsMaximalContinuation F₀ P₀ ε F P (R : WithTop ℝ))
    (ha : 0 < a) (har : a ≤ r) (hrR : r < R) :
    (F a ≤ F r ∧ F r ≤ F a * (R / a) ^ (9 / 2 : ℝ)) ∧
    (deriv F a ≤ deriv F r ∧ deriv F r ≤ deriv F a * (R / a) ^ (7 / 2 : ℝ)) ∧
    (P a * (a / R) ^ (33 / 2 : ℝ) ≤ P r ∧ P r ≤ P a) ∧
    |deriv P r| ≤ (33 / 2 : ℝ) * P a / a := by
  have hr : 0 < r := ha.trans_le har
  have hR : 0 < R := hr.trans hrR
  have ha' : a ∈ radialInterval (R : WithTop ℝ) := ⟨ha, by exact_mod_cast har.trans_lt hrR⟩
  have hr' : r ∈ radialInterval (R : WithTop ℝ) := ⟨hr, by exact_mod_cast hrR⟩
  have hs := continuation_radial_segment_bounds hLocal hCont ha' hr' har
  have hp := hCont.2.2.2.1.2.2 a ha'
  have hpr := (hCont.2.2.2.1.2.2 r hr').2.1
  have hrat := continuation_scalar_ratio_bounds hLocal hCont hr'
  have hdiv : r / a ≤ R / a := div_le_div_of_nonneg_right hrR.le ha.le
  have hinv : a / R ≤ a / r := div_le_div_of_nonneg_left ha.le hr hrR.le
  refine ⟨⟨hs.1.1, hs.1.2.trans ?_⟩, ⟨hs.2.1.1, hs.2.1.2.trans ?_⟩,
    ⟨?_, hs.2.2.2⟩, ?_⟩
  · exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (div_nonneg hr.le ha.le) hdiv (by norm_num)) hp.1.le
  · exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (div_nonneg hr.le ha.le) hdiv (by norm_num)) hp.2.2.le
  · exact (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (div_nonneg ha.le hR.le) hinv (by norm_num)) hp.2.1.le).trans hs.2.2.1
  · have hz : deriv P r ≤ 0 := by
      have hi := (div_le_iff₀ hpr).mp (neg_nonneg.mp hrat.2.2.1)
      nlinarith
    have he : |deriv P r| = (-(r * deriv P r / P r)) * P r / r := by
      rw [abs_of_nonpos hz]
      field_simp
    rw [he]
    calc
      _ ≤ (33 / 2 : ℝ) * P a / r := div_le_div_of_nonneg_right
        (mul_le_mul hrat.2.2.2 hs.2.2.2 hpr.le (by norm_num)) hr.le
      _ ≤ (33 / 2 : ℝ) * P a / a :=
        div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hp.2.1.le) ha har

-- @node: continuation_compact_state_window
/-- Given [normalized local radial solution data F₀ and P₀ on radius ε](hyp:hLocal)
and [a maximal positive continuation F and P with finite endpoint R](hyp:hCont),
with [a positive inner radius a](hyp:ha) [strictly below R](hyp:haR), [there exists
a compact set of radius-state pairs in which the radius, F, P and F′ are positive,
containing (r, F(r), P(r), F′(r), P′(r)) for every r at least a and strictly below R](goal). -/
lemma continuation_compact_state_window {ε : ℝ} {F₀ P₀ F P : ℝ → ℝ}
    {R a : ℝ} (hLocal : LocalSolutionData ε F₀ P₀)
    (hCont : IsMaximalContinuation F₀ P₀ ε F P (R : WithTop ℝ))
    (ha : 0 < a) (haR : a < R) :
    ∃ K : Set (ℝ × (Fin 4 → ℝ)), IsCompact K ∧
      K ⊆ {v | 0 < v.1 ∧ 0 < v.2 0 ∧ 0 < v.2 1 ∧ 0 < v.2 2} ∧
      ∀ r ∈ Ico a R, (r, ![F r, P r, deriv F r, deriv P r]) ∈ K := by
  have ha' : a ∈ radialInterval (R : WithTop ℝ) := ⟨ha, by exact_mod_cast haR⟩
  have hp := hCont.2.2.2.1.2.2 a ha'
  let M : ℝ := (33 / 2 : ℝ) * P a / a
  let lo : Fin 4 → ℝ := ![F a, P a * (a / R) ^ (33 / 2 : ℝ), deriv F a, -M]
  let hi : Fin 4 → ℝ :=
    ![F a * (R / a) ^ (9 / 2 : ℝ), P a, deriv F a * (R / a) ^ (7 / 2 : ℝ), M]
  refine ⟨Icc a R ×ˢ Icc lo hi, isCompact_Icc.prod isCompact_Icc, ?_, ?_⟩
  · intro v hv
    refine ⟨ha.trans_le hv.1.1, hp.1.trans_le (hv.2.1 0), ?_,
      hp.2.2.trans_le (hv.2.1 2)⟩
    exact (mul_pos hp.2.1 (Real.rpow_pos_of_pos (div_pos ha (ha.trans haR)) _)).trans_le
      (hv.2.1 1)
  · intro r hr
    have hb := continuation_finite_endpoint_bounds hLocal hCont ha hr.1 hr.2
    refine ⟨⟨hr.1, hr.2.le⟩, ?_, ?_⟩
    · intro i
      fin_cases i
      · exact hb.1.1
      · exact hb.2.2.1.1
      · exact hb.2.1.1
      · exact (abs_le.mp hb.2.2.2).1
    · intro i
      fin_cases i
      · exact hb.1.2
      · exact hb.2.2.1.2
      · exact hb.2.1.2
      · exact (abs_le.mp hb.2.2.2).2

end OaiSmoothNonquadraticAffine

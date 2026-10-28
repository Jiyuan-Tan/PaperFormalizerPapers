module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-! Unitary polar normalization and its commutation properties for finite corners. -/

@[expose] public section

namespace Papers.OaiNearInclusionsVon

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- For [an element C of the algebra](hyp:C), [its polar normalization](goal)
is C multiplied by the inverse square root of its adjoint times itself,
computed by continuous functional calculus. -/
-- @node: cornerPolar
noncomputable def cornerPolar (C : A) : A :=
  C * CFC.rpow (star C * C) (- (1 / 2 : ℝ))

/-- If [C is invertible](hyp:hC), then [its polar normalization is unitary](goal). -/
-- @node: cornerPolar_mem_unitary
lemma cornerPolar_mem_unitary (C : A) (hC : IsUnit C) :
    cornerPolar C ∈ unitary A := by
  let X := star C * C
  have hX : IsUnit X := hC.star.mul hC
  have hXpos : 0 ≤ X := star_mul_self_nonneg C
  have hF : IsSelfAdjoint (CFC.rpow X (- (1 / 2 : ℝ))) :=
    (CFC.rpow_nonneg : 0 ≤ CFC.rpow X (- (1 / 2 : ℝ))).isSelfAdjoint
  apply (hC.mul (hX.cfcRpow (- (1 / 2 : ℝ)) hXpos)).mem_unitary_of_star_mul_self
  change star (C * CFC.rpow X (- (1 / 2 : ℝ))) *
    (C * CFC.rpow X (- (1 / 2 : ℝ))) = 1
  rw [star_mul, hF.star_eq]
  calc
    CFC.rpow X (- (1 / 2 : ℝ)) * star C * (C * CFC.rpow X (- (1 / 2 : ℝ))) =
        CFC.rpow X (- (1 / 2 : ℝ)) * X * CFC.rpow X (- (1 / 2 : ℝ)) := by
      dsimp [X]; noncomm_ring
    _ = CFC.rpow X (- (1 / 2 : ℝ) + 1 + - (1 / 2 : ℝ)) := by
      simp only [CFC.rpow_eq_pow]
      rw [CFC.rpow_add hX, CFC.rpow_add hX, CFC.rpow_one X hXpos]
    _ = 1 := by norm_num [CFC.rpow_zero X hXpos]

/-- If [C commutes with B](hyp:h) and [the adjoint of C commutes with B](hyp:hs),
then [the polar normalization of C commutes with B](goal). -/
-- @node: cornerPolar_commute_right
lemma cornerPolar_commute_right (C B : A) (h : Commute C B)
    (hs : Commute (star C) B) : Commute (cornerPolar C) B := by
  exact h.mul_left ((hs.mul_left h).cfc_nnreal (fun x => x ^ (- (1 / 2 : ℝ))))

/-- If [C commutes with D](hyp:h) and [the adjoint of C commutes with D](hyp:hs),
then [the polar normalizations of C and D commute](goal). -/
-- @node: cornerPolar_commute
lemma cornerPolar_commute (C D : A) (h : Commute C D)
    (hs : Commute (star C) D) : Commute (cornerPolar C) (cornerPolar D) := by
  have h₁ := cornerPolar_commute_right C D h hs
  have h₂ : Commute (cornerPolar C) (star D) := by
    apply cornerPolar_commute_right
    · simpa only [star_star] using hs.star_star
    · simpa only [star_star] using h.star_star
  exact (cornerPolar_commute_right D (cornerPolar C) h₁.symm h₂.symm).symm

/-- If [C intertwines E with P](hyp:hCE) and [the adjoint of C times C
commutes with E](hyp:hXE), then [the polar normalization of C also
intertwines E with P](goal). -/
-- @node: cornerPolar_intertwines
lemma cornerPolar_intertwines (C E P : A) (hCE : C * E = P * C)
    (hXE : Commute (star C * C) E) : cornerPolar C * E = P * cornerPolar C := by
  have hFE : Commute (CFC.rpow (star C * C) (- (1 / 2 : ℝ))) E :=
    hXE.cfc_nnreal (fun x => x ^ (- (1 / 2 : ℝ)))
  change (C * CFC.rpow (star C * C) (- (1 / 2 : ℝ))) * E =
    P * (C * CFC.rpow (star C * C) (- (1 / 2 : ℝ)))
  calc
    _ = C * (E * CFC.rpow (star C * C) (- (1 / 2 : ℝ))) := by
      rw [mul_assoc, hFE.eq]
    _ = _ := by rw [← mul_assoc, hCE, mul_assoc]

/-- If [C is invertible](hyp:hC), [C intertwines E with P](hyp:hCE), and
[the adjoint of C times C commutes with E](hyp:hXE), then [conjugating E
by the polar normalization of C gives P](goal). -/
-- @node: cornerPolar_conjugates
lemma cornerPolar_conjugates (C E P : A) (hC : IsUnit C)
    (hCE : C * E = P * C) (hXE : Commute (star C * C) E) :
    cornerPolar C * E * star (cornerPolar C) = P := by
  rw [cornerPolar_intertwines C E P hCE hXE, mul_assoc,
    Unitary.mul_star_self_of_mem (cornerPolar_mem_unitary C hC), mul_one]

omit [PartialOrder A] [StarOrderedRing A] in
/-- If [X is self-adjoint](hyp:hX) and [x belongs to its real spectrum](hyp:hx),
then [the distance from x to one is at most the norm distance from X to the identity](goal). -/
-- @node: corner_spectrum_dist_one_le
lemma corner_spectrum_dist_one_le (X : A) (hX : IsSelfAdjoint X)
    (x : ℝ) (hx : x ∈ spectrum ℝ X) : ‖x - 1‖ ≤ ‖X - 1‖ := by
  have h := norm_apply_le_norm_cfc (fun y : ℝ => y - 1) X hx (by fun_prop) hX
  simpa only [cfc_sub (fun y : ℝ => y) (fun _ : ℝ => 1) X,
    cfc_id' ℝ X hX, cfc_const_one ℝ X] using h

/-- Suppose [X is nonnegative](hyp:hX) and [invertible](hyp:hu),
[ε is positive](hyp:hε), and [every real number within δ of one has
inverse square root within ε of one](hyp:hδ). If [X is within δ of
the identity in norm](hyp:hsmall), then [its inverse square root is
within ε of the identity in norm](goal). -/
-- @node: corner_inverse_sqrt_norm_lt
lemma corner_inverse_sqrt_norm_lt (X : A) (hX : 0 ≤ X) (hu : IsUnit X)
    (ε δ : ℝ) (hε : 0 < ε)
    (hδ : ∀ x : ℝ, ‖x - 1‖ < δ → ‖x ^ (- (1 / 2 : ℝ)) - 1‖ < ε)
    (hsmall : ‖X - 1‖ < δ) :
    ‖CFC.rpow X (- (1 / 2 : ℝ)) - 1‖ < ε := by
  have hf : ContinuousOn (fun x : ℝ => x ^ (- (1 / 2 : ℝ))) (spectrum ℝ X) := by
    apply ContinuousOn.rpow_const (by fun_prop)
    intro x hx
    exact Or.inl (fun h => spectrum.zero_notMem ℝ hu (h ▸ hx))
  rw [CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real hX,
    ← cfc_const_one ℝ X, ← cfc_sub _ _ X hf (by fun_prop)]
  apply norm_cfc_lt hε
  intro x hx
  exact hδ x ((corner_spectrum_dist_one_le X hX.isSelfAdjoint x hx).trans_lt hsmall)

/-- If [R is unitary](hyp:hR), then [the norm distance from the polar
normalization of C to R is at most the distance from C to R plus one,
multiplied by the norm distance from the inverse square root of the adjoint
of C times C to the identity, plus the distance from C to R](goal). -/
-- @node: cornerPolar_error_bound
lemma cornerPolar_error_bound (C R : A) (hR : R ∈ unitary A) :
    ‖cornerPolar C - R‖ ≤ (‖C - R‖ + 1) *
      ‖CFC.rpow (star C * C) (- (1 / 2 : ℝ)) - 1‖ + ‖C - R‖ := by
  have hRnorm : ‖R‖ ≤ 1 := by
    obtain _ | _ := subsingleton_or_nontrivial A
    · simp [Subsingleton.elim R 0]
    · exact (CStarRing.norm_of_mem_unitary hR).le
  have hCnorm : ‖C‖ ≤ ‖C - R‖ + 1 :=
    (norm_le_norm_sub_add C R).trans (add_le_add le_rfl hRnorm)
  have hdiff : cornerPolar C - C =
      C * (CFC.rpow (star C * C) (- (1 / 2 : ℝ)) - 1) := by
    simp [cornerPolar, mul_sub]
  calc
    ‖cornerPolar C - R‖ ≤ ‖cornerPolar C - C‖ + ‖C - R‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖C‖ * ‖CFC.rpow (star C * C) (- (1 / 2 : ℝ)) - 1‖ + ‖C - R‖ := by
      rw [hdiff]
      exact add_le_add (norm_mul_le _ _) le_rfl
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_right hCnorm (norm_nonneg _)) le_rfl

open Filter
open scoped Topology

variable {B : ℕ → Type*} [∀ n, CStarAlgebra (B n)]
  [∀ n, PartialOrder (B n)] [∀ n, StarOrderedRing (B n)]

/-- For [a sequence X in possibly varying algebras](hyp:X), suppose
[every X is nonnegative](hyp:hX), [X is eventually invertible](hyp:hu),
and [its norm distance to the identity tends to zero](hyp:herr).
Then [the norm distance of its inverse square root to the identity tends to zero](goal). -/
-- @node: corner_inverse_sqrt_error_tendsto
lemma corner_inverse_sqrt_error_tendsto (X : ∀ n, B n)
    (hX : ∀ n, 0 ≤ X n) (hu : ∀ᶠ n in atTop, IsUnit (X n))
    (herr : Tendsto (fun n => ‖X n - 1‖) atTop (𝓝 0)) :
    Tendsto (fun n => ‖CFC.rpow (X n) (- (1 / 2 : ℝ)) - 1‖) atTop (𝓝 0) := by
  have hf : ContinuousAt (fun x : ℝ => x ^ (- (1 / 2 : ℝ))) 1 := by
    exact Real.continuousAt_rpow_const 1 _ (Or.inl one_ne_zero)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp hf ε hε
  have hsmall := herr.eventually (gt_mem_nhds hδpos)
  filter_upwards [hu, hsmall] with n hn hsn
  simp only [dist_zero_right, norm_norm]
  apply corner_inverse_sqrt_norm_lt (X n) (hX n) hn ε δ hε _ hsn
  intro x hx
  simpa only [Real.one_rpow, dist_eq_norm] using hδ (by simpa [dist_eq_norm] using hx)

/-- For [sequences C and R in possibly varying algebras](hyp:C,R), suppose
[each R is unitary](hyp:hR), [C is eventually invertible](hyp:hu),
[the norm distance from C to R tends to zero](hyp:herr), and
[the norm distance from the adjoint of C times C to the identity tends to zero](hyp:hsq).
Then [the norm distance from the polar normalization of C to R tends to zero](goal). -/
-- @node: cornerPolar_error_tendsto
lemma cornerPolar_error_tendsto (C R : ∀ n, B n)
    (hR : ∀ n, R n ∈ unitary (B n))
    (hu : ∀ᶠ n in atTop, IsUnit (C n))
    (herr : Tendsto (fun n => ‖C n - R n‖) atTop (𝓝 0))
    (hsq : Tendsto (fun n => ‖star (C n) * C n - 1‖) atTop (𝓝 0)) :
    Tendsto (fun n => ‖cornerPolar (C n) - R n‖) atTop (𝓝 0) := by
  have hroot := corner_inverse_sqrt_error_tendsto (fun n => star (C n) * C n)
    (fun n => star_mul_self_nonneg _) (hu.mono fun n hn => hn.star.mul hn) hsq
  have hbound := ((herr.add_const 1).mul hroot).add herr
  have hzero : Tendsto (fun n => (‖C n - R n‖ + 1) *
      ‖CFC.rpow (star (C n) * C n) (- (1 / 2 : ℝ)) - 1‖ + ‖C n - R n‖)
      atTop (𝓝 0) := by simpa using hbound
  exact squeeze_zero (fun n => norm_nonneg _)
    (fun n => cornerPolar_error_bound (C n) (R n) (hR n)) hzero

end Papers.OaiNearInclusionsVon

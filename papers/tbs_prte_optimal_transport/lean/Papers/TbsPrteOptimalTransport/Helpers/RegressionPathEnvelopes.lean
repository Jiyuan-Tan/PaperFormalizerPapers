module
public import Papers.TbsPrteOptimalTransport.Helpers.HingePathEnvelopes
/-! Quadratic regression and assignment-denominator envelopes on joint binary paths. -/
public section
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

-- @node: fitted_ipw_affine_centering_error
/-- If [c is positive](hyp:hc) and [the perturbed assignment probability is at least c](hyp:hp),
[the absolute centering error of the inverse-weighted affine regression change is bounded
by the absolute product of the two directions, divided by c, times the squared path parameter](goal). -/
lemma fitted_ipw_affine_centering_error {p v dp dv c t : ℝ}
    (hc : 0 < c) (hp : c ≤ p + t * dp) :
    |p * (v - (v + t * dv)) / (p + t * dp) + t * dv| ≤
      (|dp * dv| / c) * t^2 := by
  have h := fitted_ipw_residual_centering_error (p0 := p) (v0 := v) (v := v + t * dv) hc hp
  simp only [add_sub_cancel_left, abs_mul] at h
  calc
    _ ≤ _ := h
    _ = _ := by rw [abs_mul, ← sq_abs t]; ring

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- Structural zero levels contribute zero, so the same bound covers k = 0.
-- @node: binary_positive_affine_centering_error
/-- If [c is positive](hyp:hc) and [the perturbed assignment probability at the selected
positive level is at least c whenever that level exists](hyp:hpi), [the inverse-weighted
affine regression centering error is bounded by the absolute product of the assignment
and regression directions, divided by c, times the squared path parameter, including at structural zero levels](goal). -/
lemma binary_positive_affine_centering_error
    (L : LevelData Z X) (e0 del : NuisanceBin L)
    (v0 dv : PositiveIndex L.K → X → ℝ) (i : ℕ) (x : X) (c t : ℝ)
    (hc : 0 < c)
    (hpi : 1 ≤ i ∧ i ≤ L.K → c ≤ positiveValue (e0 + t • del).piLev i x) :
    |positiveValue e0.piLev i x *
        (positiveValue v0 i x - positiveValue (fun a x => v0 a x + t * dv a x) i x) /
          positiveValue (e0 + t • del).piLev i x + t * positiveValue dv i x| ≤
      (|positiveValue del.piLev i x * positiveValue dv i x| / c) * t^2 := by
  by_cases hi : 1 ≤ i ∧ i ≤ L.K
  · simp only [positiveValue, dif_pos hi]
    have hp := hpi hi
    simp only [positiveValue, dif_pos hi] at hp
    exact fitted_ipw_affine_centering_error hc hp
  · simp only [positiveValue, dif_neg hi, sub_self, mul_zero, zero_div,
      add_zero, abs_zero, zero_mul]
    exact le_rfl

-- The regression part of the moving boundary leaves exactly three error products.
-- @node: binary_regular_regression_affine_centering_error
/-- If [c is positive](hyp:hc) and [all positive-level assignment probabilities along the
path are at least c](hyp:hpi), [the difference between the combined regression residual
means and the moving boundary change is bounded by the sum of three absolute
assignment-direction times regression-direction products, divided by c, times the squared path parameter](goal). -/
lemma binary_regular_regression_affine_centering_error
    (L : LevelData Z X) (e0 del : NuisanceBin L) (k : ℕ) (x : X) (c t : ℝ)
    (hc : 0 < c)
    (hpi : ∀ i, 1 ≤ i → i ≤ L.K → c ≤ positiveValue (e0 + t • del).piLev i x) :
    let e := e0 + t • del
    let rP := fun i => positiveValue e0.piLev i x *
      (positiveValue e0.P1 i x - positiveValue e.P1 i x) / positiveValue e.piLev i x
    let rp := fun i => positiveValue e0.piLev i x *
      (positiveValue e0.pLev i x - positiveValue e.pLev i x) / positiveValue e.piLev i x
    |(rP (k+1) - rP k - rp (k+1)) -
      ((positiveValue e.pLev (k+1) x - binFullJ L e k x) -
        (positiveValue e0.pLev (k+1) x - binFullJ L e0 k x))| ≤
    ((|positiveValue del.piLev (k+1) x * positiveValue del.P1 (k+1) x| +
      |positiveValue del.piLev k x * positiveValue del.P1 k x| +
      |positiveValue del.piLev (k+1) x * positiveValue del.pLev (k+1) x|) / c) * t^2 := by
  dsimp only
  have hr (v0 dv : PositiveIndex L.K → X → ℝ) (i : ℕ) :=
    binary_positive_affine_centering_error L e0 del v0 dv i x c t hc
      (fun hi => hpi i hi.1 hi.2)
  have hP := hr e0.P1 del.P1 (k+1)
  have hM := hr e0.P1 del.P1 k
  have hp := hr e0.pLev del.pLev (k+1)
  have hv (v0 dv : PositiveIndex L.K → X → ℝ) (i : ℕ) :
      positiveValue (fun a x => v0 a x + t * dv a x) i x - positiveValue v0 i x =
        t * positiveValue dv i x := by
    unfold positiveValue
    split_ifs <;> ring
  let A := positiveValue e0.piLev (k+1) x *
    (positiveValue e0.P1 (k+1) x - positiveValue (e0 + t • del).P1 (k+1) x) /
      positiveValue (e0 + t • del).piLev (k+1) x + t * positiveValue del.P1 (k+1) x
  let B := positiveValue e0.piLev k x *
    (positiveValue e0.P1 k x - positiveValue (e0 + t • del).P1 k x) /
      positiveValue (e0 + t • del).piLev k x + t * positiveValue del.P1 k x
  let D := positiveValue e0.piLev (k+1) x *
    (positiveValue e0.pLev (k+1) x - positiveValue (e0 + t • del).pLev (k+1) x) /
      positiveValue (e0 + t • del).piLev (k+1) x + t * positiveValue del.pLev (k+1) x
  have hid : (positiveValue e0.piLev (k+1) x *
      (positiveValue e0.P1 (k+1) x - positiveValue (e0 + t • del).P1 (k+1) x) /
        positiveValue (e0 + t • del).piLev (k+1) x -
      positiveValue e0.piLev k x *
      (positiveValue e0.P1 k x - positiveValue (e0 + t • del).P1 k x) /
        positiveValue (e0 + t • del).piLev k x -
      positiveValue e0.piLev (k+1) x *
      (positiveValue e0.pLev (k+1) x - positiveValue (e0 + t • del).pLev (k+1) x) /
        positiveValue (e0 + t • del).piLev (k+1) x) -
      ((positiveValue (e0 + t • del).pLev (k+1) x - binFullJ L (e0 + t • del) k x) -
        (positiveValue e0.pLev (k+1) x - binFullJ L e0 k x)) = A - B - D := by
    dsimp only [A, B, D, binFullJ]
    have h1 := hv e0.P1 del.P1 (k+1)
    have h2 := hv e0.P1 del.P1 k
    have h3 := hv e0.pLev del.pLev (k+1)
    change positiveValue (e0 + t • del).P1 (k+1) x - positiveValue e0.P1 (k+1) x = _ at h1
    change positiveValue (e0 + t • del).P1 k x - positiveValue e0.P1 k x = _ at h2
    change positiveValue (e0 + t • del).pLev (k+1) x - positiveValue e0.pLev (k+1) x = _ at h3
    linarith
  rw [hid]
  have hb := (abs_sub (A-B) D).trans (add_le_add
    ((abs_sub A B).trans (add_le_add hP hM)) hp)
  calc
    _ ≤ _ := hb
    _ = _ := by ring

-- Admissibility supplies all direction bounds; overlap supplies one common
-- denominator neighborhood. No additional analytic premise is needed.
-- @node: population_binary_regression_path_quadratic_envelope
/-- Under [baseline assignment overlap with constant cpi](hyp:hov), for [an admissible
binary nuisance direction from the truth](hyp:hd), [the sum of the three absolute
assignment and regression direction products divided by half cpi is integrable and,
for all sufficiently small path parameters, bounds the regression centering error
almost everywhere after multiplication by the squared path parameter](goal). -/
lemma population_binary_regression_path_quadratic_envelope
    (L : LevelData Z X) (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del)) (k : ℕ) :
    let E := fun x =>
      (|positiveValue del.piLev (k+1) x * positiveValue del.P1 (k+1) x| +
        |positiveValue del.piLev k x * positiveValue del.P1 k x| +
        |positiveValue del.piLev (k+1) x * positiveValue del.pLev (k+1) x|) / (cpi/2)
    Integrable E (xLaw M) ∧
    ∀ᶠ t : ℝ in nhds 0, ∀ᵐ x ∂xLaw M,
      let e := eta0Bin M L + t • del
      let rP := fun i => positiveValue (eta0Bin M L).piLev i x *
        (positiveValue (eta0Bin M L).P1 i x - positiveValue e.P1 i x) /
          positiveValue e.piLev i x
      let rp := fun i => positiveValue (eta0Bin M L).piLev i x *
        (positiveValue (eta0Bin M L).pLev i x - positiveValue e.pLev i x) /
          positiveValue e.piLev i x
      |(rP (k+1) - rP k - rp (k+1)) -
        ((positiveValue e.pLev (k+1) x - binFullJ L e k x) -
          (positiveValue (eta0Bin M L).pLev (k+1) x - binFullJ L (eta0Bin M L) k x))| ≤
        E x * t^2 := by
  dsimp only
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  obtain ⟨C, hC, hden⟩ := binary_assignment_denominator_direction_regular M L
    (eta0Bin M L) del hd
  obtain ⟨R, hR, hreg⟩ := binary_regression_direction_regular M L (eta0Bin M L) del hd
  obtain ⟨P, hP, hprop⟩ := binary_baseline_propensity_direction_regular M L
    (eta0Bin M L) del hd
  have hc : 0 < cpi/2 := by have := hov.1; positivity
  have hD i := binary_positive_regression_direction_regular (M := M) L del.piLev C hC hden i
  have hV i := binary_positive_regression_direction_regular (M := M) L del.P1 R hR hreg i
  have hW i := binary_positive_regression_direction_regular (M := M) L del.pLev P hP hprop i
  constructor
  · have hm : Measurable (fun x =>
        (|positiveValue del.piLev (k+1) x * positiveValue del.P1 (k+1) x| +
          |positiveValue del.piLev k x * positiveValue del.P1 k x| +
          |positiveValue del.piLev (k+1) x * positiveValue del.pLev (k+1) x|) / (cpi/2)) := by
      first | fun_prop
            | exact (((((hD (k+1)).1.mul (hV (k+1)).1).abs).add
                (((hD k).1.mul (hV k).1).abs)).add
                (((hD (k+1)).1.mul (hW (k+1)).1).abs)).div_const _
    apply Integrable.of_bound hm.aestronglyMeasurable ((C*R + C*R + C*P)/(cpi/2))
    filter_upwards [(hD (k+1)).2, (hD k).2, (hV (k+1)).2, (hV k).2,
      (hW (k+1)).2] with x hd1 hd0 hv1 hv0 hw1
    simp only [Real.norm_eq_abs] at hd1 hd0 hv1 hv0 hw1 ⊢
    rw [abs_of_nonneg (by positivity)]
    apply div_le_div_of_nonneg_right _ hc.le
    simp only [abs_mul]
    exact add_le_add (add_le_add
      (mul_le_mul hd1 hv1 (abs_nonneg _) hC)
      (mul_le_mul hd0 hv0 (abs_nonneg _) hC))
      (mul_le_mul hd1 hw1 (abs_nonneg _) hC)
  · filter_upwards [binary_assignment_denominators_uniform_neighborhood M L cpi hov del hd]
      with t ht
    filter_upwards [ae_all_iff.mpr ht] with x hx
    exact binary_regular_regression_affine_centering_error L (eta0Bin M L) del k x
      (cpi/2) t hc (fun i hi hiK => by
        simpa only [positiveValue, dif_pos (show 1 ≤ i ∧ i ≤ L.K from ⟨hi,hiK⟩)]
          using hx ⟨i,hi,hiK⟩)

end Papers.TbsPrteOptimalTransport

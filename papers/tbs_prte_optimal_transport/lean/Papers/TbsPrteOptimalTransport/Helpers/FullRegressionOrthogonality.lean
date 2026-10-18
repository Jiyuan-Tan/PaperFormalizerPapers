module
public import Papers.TbsPrteOptimalTransport.Helpers.Orthogonality
/-! Full-interval regression directions cancel by the conditional assignment identity. -/
public section

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory
open scoped Classical

-- The two assignment weights have conditional mean one. This proves exact
-- cancellation along the whole affine path, without differentiating an integral.
-- @node: full_regression_assignment_path
/-- If [the conditioning information is contained in the ambient information](hyp:hm),
[both regression weights are measurable with respect to it](hyp:hwp,hwm),
[both assignment weights are integrable](hyp:hap,ham) and
[each has conditional mean one](hyp:hcp,hcm), and
[the two weighted assignment residuals](hyp:hp,hn) and [the baseline score are integrable](hyp:hs),
then [adding any scalar multiple of the difference of the weighted assignment residuals
leaves the score integral unchanged](goal). -/
lemma full_regression_assignment_path {B : Type*} [mB : MeasurableSpace B]
    (ν : Measure B) [IsFiniteMeasure ν]
    (m : MeasurableSpace B) (hm : m ≤ mB) [SigmaFinite (ν.trim hm)]
    (s wp wm ap am : B → ℝ)
    (hwp : StronglyMeasurable[m] wp) (hwm : StronglyMeasurable[m] wm)
    (hap : Integrable ap ν) (ham : Integrable am ν)
    (hcp : ν[ap | m] =ᵐ[ν] (fun _ => (1 : ℝ)))
    (hcm : ν[am | m] =ᵐ[ν] (fun _ => (1 : ℝ)))
    (hp : Integrable (fun b => wp b * (ap b - 1)) ν)
    (hn : Integrable (fun b => wm b * (am b - 1)) ν)
    (hs : Integrable s ν) (t : ℝ) :
    (∫ b, s b + t * (wp b * (1 - ap b) - wm b * (1 - am b)) ∂ν) =
      ∫ b, s b ∂ν := by
  let : MeasurableSpace B := mB
  have h1 : Integrable (fun _ : B => (1 : ℝ)) ν := integrable_const 1
  have hm1 : StronglyMeasurable[m] (fun _ : B => (1 : ℝ)) := by fun_prop
  have hzplus := score_weighted_conditional_residual_zero ν m hm wp ap
    (fun _ => 1) hwp hap h1 hp hcp hm1
  have hzminus := score_weighted_conditional_residual_zero ν m hm wm am
    (fun _ => 1) hwm ham h1 hn hcm hm1
  have hid : (fun b => s b + t * (wp b * (1 - ap b) - wm b * (1 - am b))) =
      (fun b => s b - t * (wp b * (ap b - 1) - wm b * (am b - 1))) := by
    funext b
    ring
  rw [hid, integral_sub hs ((hp.sub' hn).const_mul t), integral_const_mul,
    integral_sub hp hn, hzplus, hzminus]
  ring

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- The structural zero level is represented by assignment weight one and
-- regression direction zero, so no nonexistent pi_0 identity is required.
-- @node: continuous_full_regression_orthogonality
/-- For [a lower full-interval regression perturbation direction indexed by positive levels below the last baseline level](hyp:dm), suppose [the conditioning information is contained in the observation information](hyp:hm),
[the upper weight is the upper treatment propensity times its full-interval regression direction](hyp:hwpdef),
[the lower weight is the corresponding lower product, set to zero at level zero](hyp:hwmdef),
[the upper assignment weight is the upper instrument-set indicator divided by its probability](hyp:hapdef),
and [the lower assignment weight is the analogous ratio, set to one at level zero](hyp:hamdef).
If [both regression weights are measurable given the conditioning information](hyp:hwp,hwm),
[both assignment weights are integrable](hyp:hap,ham) with [conditional means one](hyp:hcp,hcm),
and [their weighted centered residuals](hyp:hp,hn) and [the original full-interval score are integrable](hyp:hs),
then [the expected continuous full-interval score has derivative zero at zero along the
simultaneous upper and lower full-interval regression perturbations](goal). -/
lemma continuous_full_regression_orthogonality (L : LevelData Z X) (e : NuisanceCont L)
    (dp : Fin L.K → X → ℝ) (dm : {k : ℕ // 1 ≤ k ∧ k < L.K} → X → ℝ) (k : ℕ)
    (m : MeasurableSpace (Obs X Z)) (hm : m ≤ Prod.instMeasurableSpace)
    [SigmaFinite ((observationLaw M).trim hm)]
    (wp wm ap am : Obs X Z → ℝ)
    (hwpdef : ∀ o, wp o = positiveValue e.pLev (k+1) o.1 * fullValue dp k o.1)
    (hwmdef : ∀ o, wm o = if k = 0 then 0 else positiveValue e.pLev k o.1 *
      (if h : 1 ≤ k ∧ k < L.K then dm ⟨k,h⟩ o.1 else 0))
    (hapdef : ∀ o, ap o = indicator (o.2.1 ∈ L.S (k+1)) /
      positiveValue e.piLev (k+1) o.1)
    (hamdef : ∀ o, am o = if k = 0 then 1 else indicator (o.2.1 ∈ L.S k) /
      positiveValue e.piLev k o.1)
    (hwp : StronglyMeasurable[m] wp) (hwm : StronglyMeasurable[m] wm)
    (hap : Integrable ap (observationLaw M)) (ham : Integrable am (observationLaw M))
    (hcp : (observationLaw M)[ap | m] =ᵐ[observationLaw M] (fun _ => (1 : ℝ)))
    (hcm : (observationLaw M)[am | m] =ᵐ[observationLaw M] (fun _ => (1 : ℝ)))
    (hp : Integrable (fun o => wp o * (ap o - 1)) (observationLaw M))
    (hn : Integrable (fun o => wm o * (am o - 1)) (observationLaw M))
    (hs : Integrable (fun o => psiFullJ L e k o) (observationLaw M)) :
    HasDerivAt (fun t : ℝ => ∫ o, psiFullJ L {e with
      JfullPlus := fun k x => e.JfullPlus k x + t * dp k x
      JfullMinus := fun k x => e.JfullMinus k x + t * dm k x} k o
      ∂observationLaw M) 0 0 := by
  let : MeasurableSpace (Obs X Z) := Prod.instMeasurableSpace
  haveI : IsFiniteMeasure (observationLaw M) := by
    unfold observationLaw
    infer_instance
  have heq : (fun t : ℝ => ∫ o, psiFullJ L {e with
      JfullPlus := fun k x => e.JfullPlus k x + t * dp k x
      JfullMinus := fun k x => e.JfullMinus k x + t * dm k x} k o
      ∂observationLaw M) = (fun _ : ℝ => ∫ o, psiFullJ L e k o ∂observationLaw M) := by
    funext t
    have hid : (fun o => psiFullJ L {e with
        JfullPlus := fun k x => e.JfullPlus k x + t * dp k x
        JfullMinus := fun k x => e.JfullMinus k x + t * dm k x} k o) =
        (fun o => psiFullJ L e k o + t * (wp o * (1 - ap o) - wm o * (1 - am o))) := by
      funext o
      rw [psiFullJ_regression_path, hwpdef, hwmdef, hapdef, hamdef]
      split_ifs <;> ring
    rw [hid]
    exact full_regression_assignment_path (observationLaw M) m hm
      (fun o => psiFullJ L e k o) wp wm ap am hwp hwm hap ham hcp hcm hp hn hs t
  rw [heq]
  exact hasDerivAt_const 0 _

-- @node: binary_full_regression_path
/-- [Perturbing the positive-level binary outcome regressions along a common affine path
changes the full-interval regression contrast plus its upper-minus-lower outcome corrections
by the path size times the upper direction multiplied by one minus its normalized assignment
indicator, less the analogous lower term; the lower assignment weight is one at level zero](goal). -/
lemma binary_full_regression_path (L : LevelData Z X) (e : NuisanceBin L)
    (d : PositiveIndex L.K → X → ℝ) (k : ℕ) (o : Obs X Z) (t : ℝ) :
    let et := {e with P1 := fun k x => e.P1 k x + t * d k x}
    binFullJ L et k o.1 + RP L et (k+1) o - RP L et k o =
      binFullJ L e k o.1 + RP L e (k+1) o - RP L e k o + t *
        (positiveValue d (k+1) o.1 *
          (1 - indicator (o.2.1 ∈ L.S (k+1)) / positiveValue e.piLev (k+1) o.1) -
        positiveValue d k o.1 *
          (1 - (if k = 0 then 1 else indicator (o.2.1 ∈ L.S k) /
            positiveValue e.piLev k o.1))) := by
  dsimp only
  have hk1 : k + 1 ≠ 0 := by omega
  by_cases hk : k = 0
  · subst k
    simp only [binFullJ, RP, if_pos rfl, if_neg (by omega : 0 + 1 ≠ 0)]
    simp only [positiveValue]
    split_ifs <;> first | omega | ring
  · simp only [binFullJ, RP, if_neg hk, if_neg hk1, positiveValue]
    split_ifs <;> first | omega | ring

-- @node: binary_full_regression_orthogonality
/-- Suppose [the conditioning information is contained in the observation information](hyp:hm),
[the upper and lower weights equal their respective positive-level regression directions](hyp:hwpdef,hwmdef),
[the upper assignment weight is its instrument-set indicator divided by its probability](hyp:hapdef),
and [the lower assignment weight is the corresponding ratio, with value one at level zero](hyp:hamdef).
If [the direction weights are measurable given the conditioning information](hyp:hwp,hwm),
[the assignment weights are integrable](hyp:hap,ham) with [conditional means one](hyp:hcp,hcm),
and [the weighted centered assignment residuals](hyp:hp,hn) and
[the baseline full-interval regression contrast plus its outcome corrections are integrable](hyp:hs),
then [the expectation of that corrected binary full-interval contrast has derivative zero
at zero along the positive-level regression path](goal). -/
lemma binary_full_regression_orthogonality (L : LevelData Z X) (e : NuisanceBin L)
    (d : PositiveIndex L.K → X → ℝ) (k : ℕ)
    (m : MeasurableSpace (Obs X Z)) (hm : m ≤ Prod.instMeasurableSpace)
    [SigmaFinite ((observationLaw M).trim hm)]
    (wp wm ap am : Obs X Z → ℝ)
    (hwpdef : ∀ o, wp o = positiveValue d (k+1) o.1)
    (hwmdef : ∀ o, wm o = positiveValue d k o.1)
    (hapdef : ∀ o, ap o = indicator (o.2.1 ∈ L.S (k+1)) /
      positiveValue e.piLev (k+1) o.1)
    (hamdef : ∀ o, am o = if k = 0 then 1 else indicator (o.2.1 ∈ L.S k) /
      positiveValue e.piLev k o.1)
    (hwp : StronglyMeasurable[m] wp) (hwm : StronglyMeasurable[m] wm)
    (hap : Integrable ap (observationLaw M)) (ham : Integrable am (observationLaw M))
    (hcp : (observationLaw M)[ap | m] =ᵐ[observationLaw M] (fun _ => (1 : ℝ)))
    (hcm : (observationLaw M)[am | m] =ᵐ[observationLaw M] (fun _ => (1 : ℝ)))
    (hp : Integrable (fun o => wp o * (ap o - 1)) (observationLaw M))
    (hn : Integrable (fun o => wm o * (am o - 1)) (observationLaw M))
    (hs : Integrable (fun o => binFullJ L e k o.1 + RP L e (k+1) o - RP L e k o)
      (observationLaw M)) :
    HasDerivAt (fun t : ℝ => ∫ o,
      let et := {e with P1 := fun k x => e.P1 k x + t * d k x}
      binFullJ L et k o.1 + RP L et (k+1) o - RP L et k o ∂observationLaw M) 0 0 := by
  let : MeasurableSpace (Obs X Z) := Prod.instMeasurableSpace
  haveI : IsFiniteMeasure (observationLaw M) := by
    unfold observationLaw
    infer_instance
  have heq : (fun t : ℝ => ∫ o,
      let et := {e with P1 := fun k x => e.P1 k x + t * d k x}
      binFullJ L et k o.1 + RP L et (k+1) o - RP L et k o ∂observationLaw M) =
      (fun _ : ℝ => ∫ o, binFullJ L e k o.1 + RP L e (k+1) o - RP L e k o
        ∂observationLaw M) := by
    funext t
    have hid : (fun o =>
        let et := {e with P1 := fun k x => e.P1 k x + t * d k x}
        binFullJ L et k o.1 + RP L et (k+1) o - RP L et k o) =
        (fun o => (binFullJ L e k o.1 + RP L e (k+1) o - RP L e k o) +
          t * (wp o * (1 - ap o) - wm o * (1 - am o))) := by
      funext o
      rw [binary_full_regression_path, hwpdef, hwmdef, hapdef, hamdef]
    rw [hid]
    exact full_regression_assignment_path (observationLaw M) m hm
      (fun o => binFullJ L e k o.1 + RP L e (k+1) o - RP L e k o)
      wp wm ap am hwp hwm hap ham hcp hcm hp hn hs t
  rw [heq]
  exact hasDerivAt_const 0 _

end Papers.TbsPrteOptimalTransport

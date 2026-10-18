module
public import Papers.TbsPrteOptimalTransport.Helpers.FullRegressionOrthogonality
/-! Cancellation of treated-band regression directions in the fractional score. -/
public section
set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory
open scoped Classical

-- Conditional cancellation is needed before multiplying by a covariate weight.
-- @node: regression_assignment_conditional_residual_zero
/-- If [the conditioning information is contained in the ambient information](hyp:hm),
[the regression weight is measurable given that information](hyp:hw),
[the assignment weight is integrable](hyp:ha) and [has conditional mean one](hyp:hcenter),
and [the regression weight times one minus the assignment weight is integrable](hyp:hres),
then [this weighted assignment residual has conditional mean zero almost everywhere](goal). -/
lemma regression_assignment_conditional_residual_zero {B : Type*} [mB : MeasurableSpace B]
    (ν : Measure B) [IsFiniteMeasure ν]
    (m : MeasurableSpace B) (hm : m ≤ mB) [SigmaFinite (ν.trim hm)]
    (w a : B → ℝ) (hw : StronglyMeasurable[m] w) (ha : Integrable a ν)
    (hcenter : ν[a | m] =ᵐ[ν] (fun _ => (1 : ℝ)))
    (hres : Integrable (fun b => w b * (1 - a b)) ν) :
    ν[(fun b => w b * (1 - a b)) | m] =ᵐ[ν] 0 := by
  let : MeasurableSpace B := mB
  have h1 : Integrable (fun _ : B => (1 : ℝ)) ν := integrable_const 1
  have hm1 : StronglyMeasurable[m] (fun _ : B => (1 : ℝ)) := by fun_prop
  have hfix := condExp_of_stronglyMeasurable hm hm1 h1
  have hc : ν[(fun b => 1 - a b) | m] =ᵐ[ν] 0 := by
    filter_upwards [condExp_sub h1 ha m, hcenter] with b hb hz
    simpa only [Pi.sub_def, hfix, hz, sub_self, Pi.zero_apply] using hb
  have hp := condExp_mul_of_stronglyMeasurable_left hw hres (h1.sub ha)
  filter_upwards [hp, hc] with b hb hz
  simpa only [Pi.mul_def, hz, Pi.zero_apply, mul_zero] using hb

-- @node: full_regression_assignment_conditional_path
/-- If [the conditioning information is contained in the ambient information](hyp:hm),
[the two regression weights are measurable given it](hyp:hwp,hwm),
[the assignment weights are integrable](hyp:hap,ham) with [conditional means one](hyp:hcp,hcm),
and [the two weighted assignment residuals](hyp:hp,hn) and [the baseline score are integrable](hyp:hs),
then [adding any scalar multiple of the upper weighted residual minus the lower weighted
residual preserves the baseline score's conditional expectation almost everywhere](goal). -/
lemma full_regression_assignment_conditional_path {B : Type*} [mB : MeasurableSpace B]
    (ν : Measure B) [IsFiniteMeasure ν]
    (m : MeasurableSpace B) (hm : m ≤ mB) [SigmaFinite (ν.trim hm)]
    (s wp wm ap am : B → ℝ)
    (hwp : StronglyMeasurable[m] wp) (hwm : StronglyMeasurable[m] wm)
    (hap : Integrable ap ν) (ham : Integrable am ν)
    (hcp : ν[ap | m] =ᵐ[ν] (fun _ => (1 : ℝ)))
    (hcm : ν[am | m] =ᵐ[ν] (fun _ => (1 : ℝ)))
    (hp : Integrable (fun b => wp b * (1 - ap b)) ν)
    (hn : Integrable (fun b => wm b * (1 - am b)) ν)
    (hs : Integrable s ν) (t : ℝ) :
    ν[(fun b => s b + t * (wp b * (1 - ap b) - wm b * (1 - am b))) | m]
      =ᵐ[ν] ν[s | m] := by
  let : MeasurableSpace B := mB
  have hzplus := regression_assignment_conditional_residual_zero ν m hm wp ap hwp hap hcp hp
  have hzminus := regression_assignment_conditional_residual_zero ν m hm wm am hwm ham hcm hn
  have hdiff := condExp_sub hp hn m
  have hscale := condExp_smul t
    (fun b => wp b * (1 - ap b) - wm b * (1 - am b)) m (μ := ν)
  have hsum := condExp_add hs ((hp.sub hn).const_mul t) m
  filter_upwards [hzplus, hzminus, hdiff, hscale, hsum] with b hzp hzm hd ht hs'
  simp only [Pi.sub_def, hzp, hzm, Pi.zero_apply, sub_self] at hd
  simp only [Pi.smul_def, smul_eq_mul, hd, mul_zero] at ht
  simpa only [Pi.add_def, Pi.sub_def, ht, add_zero] using hs'

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- The representer changes with the regression. Its propensity residual
-- cancels the W factor in the treated-outcome residual, leaving assignment centering.
-- @node: continuous_band_regression_path
/-- [An affine perturbation of the upper and lower treated-band outcome regressions changes
the continuous score component by the path size times the upper treatment propensity and
regression direction multiplied by one minus the normalized upper assignment indicator,
less the analogous lower term, which vanishes at level zero](goal). -/
lemma continuous_band_regression_path (phi dphi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (e : NuisanceCont L)
    (dp : MeanIndex L → X → ℝ) (dm : MinusMeanIndex L → X → ℝ)
    (k j : ℕ) (o : Obs X Z) (t : ℝ) :
    contScoreComponents M phi dphi L {e with
      Jplus := fun a x => e.Jplus a x + t * dp a x
      Jminus := fun a x => e.Jminus a x + t * dm a x} k j o =
    contScoreComponents M phi dphi L e k j o + t *
      (positiveValue e.pLev (k+1) o.1 * meanValue dp k j o.1 *
        (1 - indicator (o.2.1 ∈ L.S (k+1)) / positiveValue e.piLev (k+1) o.1) -
      (if k = 0 then 0 else positiveValue e.pLev k o.1 * minusMeanValue dm k j o.1 *
        (1 - indicator (o.2.1 ∈ L.S k) / positiveValue e.piLev k o.1))) := by
  let et : NuisanceCont L := {e with
    Jplus := fun a x => e.Jplus a x + t * dp a x
    Jminus := fun a x => e.Jminus a x + t * dm a x}
  change contScoreComponents M phi dphi L et k j o = _
  have hn : ∀ i, nuValue M et k i o.1 = nuValue M e k i o.1 := fun _ => rfl
  have hq : ∀ i, pooledQ phi L et k i o.1 = pooledQ phi L e k i o.1 := fun _ => rfl
  have hi : ∀ b i, IFM M L et b k i o = IFM M L e b k i o := fun _ _ => rfl
  have hr : ∀ i, RqCont dphi L et k i o = RqCont dphi L e k i o := fun _ => rfl
  simp only [contScoreComponents, contJ, IFJ, alphaLow, alphaHigh, hn, hq, hi, hr]
  by_cases hk : k = 0
  · subst k
    simp [et, meanValue, minusMeanValue, RpCont, positiveValue]
    split_ifs <;> ring
  · simp [et, meanValue, minusMeanValue, RpCont, hk]
    split_ifs <;> ring

-- @node: continuous_band_regression_orthogonality
/-- Suppose [the conditioning information is contained in the observation information](hyp:hm),
[the upper weight is the upper treatment propensity times the treated-band regression direction](hyp:hwpdef),
[the lower weight is its lower-level counterpart, set to zero at level zero](hyp:hwmdef),
[the upper assignment weight is the upper instrument-set indicator divided by its probability](hyp:hapdef),
and [the lower assignment weight is the corresponding ratio, set to one at level zero](hyp:hamdef).
If [both regression weights are measurable given the conditioning information](hyp:hwp,hwm),
[the assignment weights are integrable](hyp:hap,ham) with [conditional means one](hyp:hcp,hcm),
and [the weighted centered assignment residuals](hyp:hp,hn) and [the original score component are integrable](hyp:hs),
then [the expected continuous score component has derivative zero at zero along the
simultaneous upper and lower treated-band regression path](goal). -/
lemma continuous_band_regression_orthogonality (phi dphi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (e : NuisanceCont L)
    (dp : MeanIndex L → X → ℝ) (dm : MinusMeanIndex L → X → ℝ) (k j : ℕ)
    (m : MeasurableSpace (Obs X Z)) (hm : m ≤ Prod.instMeasurableSpace)
    [SigmaFinite ((observationLaw M).trim hm)]
    (wp wm ap am : Obs X Z → ℝ)
    (hwpdef : ∀ o, wp o = positiveValue e.pLev (k+1) o.1 * meanValue dp k j o.1)
    (hwmdef : ∀ o, wm o = if k = 0 then 0 else positiveValue e.pLev k o.1 *
      minusMeanValue dm k j o.1)
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
    (hs : Integrable (fun o => contScoreComponents M phi dphi L e k j o) (observationLaw M)) :
    HasDerivAt (fun t : ℝ => ∫ o, contScoreComponents M phi dphi L {e with
      Jplus := fun k x => e.Jplus k x + t * dp k x
      Jminus := fun k x => e.Jminus k x + t * dm k x} k j o
      ∂observationLaw M) 0 0 := by
  let : MeasurableSpace (Obs X Z) := Prod.instMeasurableSpace
  have : IsFiniteMeasure (observationLaw M) := by
    unfold observationLaw
    infer_instance
  have heq : (fun t : ℝ => ∫ o, contScoreComponents M phi dphi L {e with
      Jplus := fun k x => e.Jplus k x + t * dp k x
      Jminus := fun k x => e.Jminus k x + t * dm k x} k j o
      ∂observationLaw M) = (fun _ : ℝ => ∫ o, contScoreComponents M phi dphi L e k j o ∂observationLaw M) := by
    funext t
    have hid : (fun o => contScoreComponents M phi dphi L {e with
        Jplus := fun k x => e.Jplus k x + t * dp k x
        Jminus := fun k x => e.Jminus k x + t * dm k x} k j o) =
        (fun o => contScoreComponents M phi dphi L e k j o + t * (wp o * (1 - ap o) - wm o * (1 - am o))) := by
      funext o
      rw [continuous_band_regression_path, hwpdef, hwmdef, hapdef, hamdef]
      split_ifs <;> ring
    rw [hid]
    exact full_regression_assignment_path (observationLaw M) m hm
      (fun o => contScoreComponents M phi dphi L e k j o) wp wm ap am hwp hwm hap ham hcp hcm hp hn hs t
  rw [heq]
  exact hasDerivAt_const 0 _

-- The terminal CDF value is fixed at one; its affine direction is zero.
-- @node: boundaryValue_affine_path
/-- [The upper boundary probability evaluated along an affine regression path equals its
original value plus the path size times the upper mean-direction extension; the fixed
terminal probability of one has direction zero](goal). -/
lemma boundaryValue_affine_path (L : LevelData Z X)
    (f d : IndicatorIndex L → X → ℝ) (k j : ℕ) (x : X) (t : ℝ) :
    boundaryValue (fun a x => f a x + t * d a x) k j x =
      boundaryValue f k j x + t * meanValue d k j x := by
  simp only [boundaryValue, meanValue]
  split_ifs <;> ring

-- @node: minusBoundaryValue_affine_path
/-- [The lower boundary probability evaluated along an affine regression path equals its
original value plus the path size times the lower mean-direction extension, with zero
direction wherever the boundary value is fixed](goal). -/
lemma minusBoundaryValue_affine_path (L : LevelData Z X)
    (f d : MinusIndicatorIndex L → X → ℝ) (k j : ℕ) (x : X) (t : ℝ) :
    minusBoundaryValue (fun a x => f a x + t * d a x) k j x =
      minusBoundaryValue f k j x + t * minusMeanValue d k j x := by
  simp only [minusBoundaryValue, minusMeanValue]
  split_ifs <;> ring

-- @node: continuous_boundary_regression_path
/-- [Perturbing the upper and lower boundary-probability regressions affinely changes the
continuous score component by the path size times the upper treatment propensity times
the lower-endpoint quantile times its boundary direction minus the upper-endpoint quantile
times its boundary direction, all multiplied by one minus the normalized upper assignment
indicator, less the analogous lower-level term, which vanishes at level zero](goal). -/
lemma continuous_boundary_regression_path (phi dphi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (e : NuisanceCont L)
    (dp : IndicatorIndex L → X → ℝ) (dm : MinusIndicatorIndex L → X → ℝ)
    (k j : ℕ) (o : Obs X Z) (t : ℝ) :
    contScoreComponents M phi dphi L {e with
      Mplus := fun a x => e.Mplus a x + t * dp a x
      Mminus := fun a x => e.Mminus a x + t * dm a x} k j o =
    contScoreComponents M phi dphi L e k j o + t *
      (positiveValue e.pLev (k+1) o.1 *
        (nuValue M e k j o.1 * meanValue dp k j o.1 -
          nuValue M e k (j+1) o.1 * meanValue dp k (j+1) o.1) *
        (1 - indicator (o.2.1 ∈ L.S (k+1)) / positiveValue e.piLev (k+1) o.1) -
      (if k = 0 then 0 else positiveValue e.pLev k o.1 *
        (nuValue M e k j o.1 * minusMeanValue dm k j o.1 -
          nuValue M e k (j+1) o.1 * minusMeanValue dm k (j+1) o.1) *
        (1 - indicator (o.2.1 ∈ L.S k) / positiveValue e.piLev k o.1))) := by
  let et : NuisanceCont L := {e with
    Mplus := fun a x => e.Mplus a x + t * dp a x
    Mminus := fun a x => e.Mminus a x + t * dm a x}
  change contScoreComponents M phi dphi L et k j o = _
  have hn : ∀ i, nuValue M et k i o.1 = nuValue M e k i o.1 := fun _ => rfl
  have hq : ∀ i, pooledQ phi L et k i o.1 = pooledQ phi L e k i o.1 := fun _ => rfl
  have hi : ∀ b, IFJ M L et b k j o = IFJ M L e b k j o := fun _ => rfl
  have hj : contJ L et k j o.1 = contJ L e k j o.1 := rfl
  have hr : ∀ i, RqCont dphi L et k i o = RqCont dphi L e k i o := fun _ => rfl
  have hp : ∀ i, boundaryValue et.Mplus k i o.1 =
      boundaryValue e.Mplus k i o.1 + t * meanValue dp k i o.1 :=
    fun i => boundaryValue_affine_path L e.Mplus dp k i o.1 t
  have hm : ∀ i, minusBoundaryValue et.Mminus k i o.1 =
      minusBoundaryValue e.Mminus k i o.1 + t * minusMeanValue dm k i o.1 :=
    fun i => minusBoundaryValue_affine_path L e.Mminus dm k i o.1 t
  simp only [contScoreComponents, hj, hi, alphaLow, alphaHigh, IFM, hn, hq, hr, hp, hm]
  by_cases hk : k = 0
  · subst k
    simp [et, RpCont, positiveValue, minusMeanValue]
    split_ifs <;> ring
  · simp [et, RpCont, hk]
    ring

-- @node: continuous_boundary_regression_orthogonality
/-- Suppose [the conditioning information is contained in the observation information](hyp:hm),
[the upper weight is the upper treatment propensity times the lower-endpoint quantile-weighted
boundary direction minus the upper-endpoint quantile-weighted boundary direction](hyp:hwpdef),
[the lower weight is the analogous lower-level expression, set to zero at level zero](hyp:hwmdef),
[the upper assignment weight is the upper instrument-set indicator divided by its probability](hyp:hapdef),
and [the lower assignment weight is the analogous ratio, set to one at level zero](hyp:hamdef).
If [both direction weights are measurable given the conditioning information](hyp:hwp,hwm),
[the assignment weights are integrable](hyp:hap,ham) with [conditional means one](hyp:hcp,hcm),
and [the weighted centered assignment residuals](hyp:hp,hn) and [the baseline score component are integrable](hyp:hs),
then [the expected continuous score component has derivative zero at zero along the
simultaneous upper and lower boundary-probability regression path](goal). -/
lemma continuous_boundary_regression_orthogonality (phi dphi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (e : NuisanceCont L)
    (dp : IndicatorIndex L → X → ℝ) (dm : MinusIndicatorIndex L → X → ℝ) (k j : ℕ)
    (m : MeasurableSpace (Obs X Z)) (hm : m ≤ Prod.instMeasurableSpace)
    [SigmaFinite ((observationLaw M).trim hm)]
    (wp wm ap am : Obs X Z → ℝ)
    (hwpdef : ∀ o, wp o = positiveValue e.pLev (k+1) o.1 *
      (nuValue M e k j o.1 * meanValue dp k j o.1 -
        nuValue M e k (j+1) o.1 * meanValue dp k (j+1) o.1))
    (hwmdef : ∀ o, wm o = if k = 0 then 0 else positiveValue e.pLev k o.1 *
      (nuValue M e k j o.1 * minusMeanValue dm k j o.1 -
        nuValue M e k (j+1) o.1 * minusMeanValue dm k (j+1) o.1))
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
    (hs : Integrable (fun o => contScoreComponents M phi dphi L e k j o) (observationLaw M)) :
    HasDerivAt (fun t : ℝ => ∫ o, contScoreComponents M phi dphi L {e with
      Mplus := fun k x => e.Mplus k x + t * dp k x
      Mminus := fun k x => e.Mminus k x + t * dm k x} k j o
      ∂observationLaw M) 0 0 := by
  let : MeasurableSpace (Obs X Z) := Prod.instMeasurableSpace
  have : IsFiniteMeasure (observationLaw M) := by
    unfold observationLaw
    infer_instance
  have heq : (fun t : ℝ => ∫ o, contScoreComponents M phi dphi L {e with
      Mplus := fun k x => e.Mplus k x + t * dp k x
      Mminus := fun k x => e.Mminus k x + t * dm k x} k j o
      ∂observationLaw M) = (fun _ : ℝ => ∫ o, contScoreComponents M phi dphi L e k j o ∂observationLaw M) := by
    funext t
    have hid : (fun o => contScoreComponents M phi dphi L {e with
        Mplus := fun k x => e.Mplus k x + t * dp k x
        Mminus := fun k x => e.Mminus k x + t * dm k x} k j o) =
        (fun o => contScoreComponents M phi dphi L e k j o + t * (wp o * (1 - ap o) - wm o * (1 - am o))) := by
      funext o
      rw [continuous_boundary_regression_path, hwpdef, hwmdef, hapdef, hamdef]
      split_ifs <;> ring
    rw [hid]
    exact full_regression_assignment_path (observationLaw M) m hm
      (fun o => contScoreComponents M phi dphi L e k j o) wp wm ap am hwp hwm hap ham hcp hcm hp hn hs t
  rw [heq]
  exact hasDerivAt_const 0 _

-- The J and M regressions can vary together: their assignment-centered
-- contributions add, with the terminal CDF direction still fixed at zero.
-- @node: continuous_joint_regression_path
/-- [Simultaneous affine perturbations of the treated-band outcome and boundary-probability
regressions change the continuous score component by the path size times the upper treatment
propensity times the sum of its outcome direction and its lower-minus-upper quantile-weighted
boundary directions, multiplied by one minus the normalized upper assignment indicator,
less the analogous lower-level term, which vanishes at level zero](goal). -/
lemma continuous_joint_regression_path (phi dphi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (e : NuisanceCont L)
    (dJp : MeanIndex L → X → ℝ) (dJm : MinusMeanIndex L → X → ℝ)
    (dMp : IndicatorIndex L → X → ℝ) (dMm : MinusIndicatorIndex L → X → ℝ)
    (k j : ℕ) (o : Obs X Z) (t : ℝ) :
    contScoreComponents M phi dphi L {e with
      Jplus := fun a x => e.Jplus a x + t * dJp a x
      Jminus := fun a x => e.Jminus a x + t * dJm a x
      Mplus := fun a x => e.Mplus a x + t * dMp a x
      Mminus := fun a x => e.Mminus a x + t * dMm a x} k j o =
    contScoreComponents M phi dphi L e k j o + t *
      (positiveValue e.pLev (k+1) o.1 *
        (meanValue dJp k j o.1 + nuValue M e k j o.1 * meanValue dMp k j o.1 -
          nuValue M e k (j+1) o.1 * meanValue dMp k (j+1) o.1) *
        (1 - indicator (o.2.1 ∈ L.S (k+1)) / positiveValue e.piLev (k+1) o.1) -
      (if k = 0 then 0 else positiveValue e.pLev k o.1 *
        (minusMeanValue dJm k j o.1 + nuValue M e k j o.1 * minusMeanValue dMm k j o.1 -
          nuValue M e k (j+1) o.1 * minusMeanValue dMm k (j+1) o.1) *
        (1 - indicator (o.2.1 ∈ L.S k) / positiveValue e.piLev k o.1))) := by
  let eJ : NuisanceCont L := {e with
    Jplus := fun a x => e.Jplus a x + t * dJp a x
    Jminus := fun a x => e.Jminus a x + t * dJm a x}
  change contScoreComponents M phi dphi L {eJ with
    Mplus := fun a x => eJ.Mplus a x + t * dMp a x
    Mminus := fun a x => eJ.Mminus a x + t * dMm a x} k j o = _
  rw [continuous_boundary_regression_path, continuous_band_regression_path]
  have hn : ∀ i, nuValue M eJ k i o.1 = nuValue M e k i o.1 := fun _ => rfl
  simp only [hn]
  change _ + t * (positiveValue e.pLev (k+1) o.1 * _ * _ -
    (if k = 0 then 0 else positiveValue e.pLev k o.1 * _ * _)) = _
  split_ifs <;> ring

-- This equality holds conditionally, so subsequent product scores can use
-- any measurable covariate weight, including the signed full-interval weight.
-- @node: continuous_joint_regression_conditional_path
/-- Suppose [the conditioning information is contained in the observation information](hyp:hm),
[the upper weight is the upper treatment propensity times the sum of its outcome-regression
direction and lower-minus-upper quantile-weighted boundary directions](hyp:hwpdef),
[the lower weight is the corresponding lower-level expression, set to zero at level zero](hyp:hwmdef),
[the upper assignment weight is the upper instrument-set indicator divided by its probability](hyp:hapdef),
and [the lower assignment weight is the analogous ratio, set to one at level zero](hyp:hamdef).
If [both direction weights are measurable given the conditioning information](hyp:hwp,hwm),
[the assignment weights are integrable](hyp:hap,ham) with [conditional means one](hyp:hcp,hcm),
and [the weighted assignment residuals](hyp:hp,hn) and [the original score component are integrable](hyp:hs),
then [the continuous score component's conditional expectation is unchanged almost everywhere
along the simultaneous affine outcome and boundary-probability regression path, at every path size](goal). -/
lemma continuous_joint_regression_conditional_path (phi dphi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (e : NuisanceCont L)
    (dJp : MeanIndex L → X → ℝ) (dJm : MinusMeanIndex L → X → ℝ)
    (dMp : IndicatorIndex L → X → ℝ) (dMm : MinusIndicatorIndex L → X → ℝ)
    (k j : ℕ) (m : MeasurableSpace (Obs X Z))
    (hm : m ≤ Prod.instMeasurableSpace) [SigmaFinite ((observationLaw M).trim hm)]
    (wp wm ap am : Obs X Z → ℝ)
    (hwpdef : ∀ o, wp o = positiveValue e.pLev (k+1) o.1 *
      (meanValue dJp k j o.1 + nuValue M e k j o.1 * meanValue dMp k j o.1 -
        nuValue M e k (j+1) o.1 * meanValue dMp k (j+1) o.1))
    (hwmdef : ∀ o, wm o = if k = 0 then 0 else positiveValue e.pLev k o.1 *
      (minusMeanValue dJm k j o.1 + nuValue M e k j o.1 * minusMeanValue dMm k j o.1 -
        nuValue M e k (j+1) o.1 * minusMeanValue dMm k (j+1) o.1))
    (hapdef : ∀ o, ap o = indicator (o.2.1 ∈ L.S (k+1)) /
      positiveValue e.piLev (k+1) o.1)
    (hamdef : ∀ o, am o = if k = 0 then 1 else indicator (o.2.1 ∈ L.S k) /
      positiveValue e.piLev k o.1)
    (hwp : StronglyMeasurable[m] wp) (hwm : StronglyMeasurable[m] wm)
    (hap : Integrable ap (observationLaw M)) (ham : Integrable am (observationLaw M))
    (hcp : (observationLaw M)[ap | m] =ᵐ[observationLaw M] (fun _ => (1 : ℝ)))
    (hcm : (observationLaw M)[am | m] =ᵐ[observationLaw M] (fun _ => (1 : ℝ)))
    (hp : Integrable (fun o => wp o * (1 - ap o)) (observationLaw M))
    (hn : Integrable (fun o => wm o * (1 - am o)) (observationLaw M))
    (hs : Integrable (fun o => contScoreComponents M phi dphi L e k j o) (observationLaw M))
    (t : ℝ) :
    (observationLaw M)[(fun o => contScoreComponents M phi dphi L {e with
      Jplus := fun a x => e.Jplus a x + t * dJp a x
      Jminus := fun a x => e.Jminus a x + t * dJm a x
      Mplus := fun a x => e.Mplus a x + t * dMp a x
      Mminus := fun a x => e.Mminus a x + t * dMm a x} k j o) | m]
      =ᵐ[observationLaw M]
    (observationLaw M)[(fun o => contScoreComponents M phi dphi L e k j o) | m] := by
  let : MeasurableSpace (Obs X Z) := Prod.instMeasurableSpace
  haveI : IsFiniteMeasure (observationLaw M) := by
    unfold observationLaw
    infer_instance
  have hid : (fun o => contScoreComponents M phi dphi L {e with
      Jplus := fun a x => e.Jplus a x + t * dJp a x
      Jminus := fun a x => e.Jminus a x + t * dJm a x
      Mplus := fun a x => e.Mplus a x + t * dMp a x
      Mminus := fun a x => e.Mminus a x + t * dMm a x} k j o) =
      (fun o => contScoreComponents M phi dphi L e k j o +
        t * (wp o * (1 - ap o) - wm o * (1 - am o))) := by
    funext o
    rw [continuous_joint_regression_path, hwpdef, hwmdef, hapdef, hamdef]
    split_ifs <;> ring
  rw [hid]
  exact full_regression_assignment_conditional_path (observationLaw M) m hm
    (fun o => contScoreComponents M phi dphi L e k j o)
    wp wm ap am hwp hwm hap ham hcp hcm hp hn hs t

end Papers.TbsPrteOptimalTransport

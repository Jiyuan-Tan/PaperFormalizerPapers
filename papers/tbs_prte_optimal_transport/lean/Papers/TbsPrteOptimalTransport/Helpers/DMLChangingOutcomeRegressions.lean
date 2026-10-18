module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLChangingBandRegressions
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousBandAdmissiblePropensity
/-! Outcome-weighted moving bands centered by fitted regressions.
Clipped endpoints bound the outcome on each band, and the indicator-band
energy controls the outcome energy. Fitted regression and denominator errors
then transfer to the observed IPW residual. -/
public section
set_option linter.style.haveILetI false
set_option linter.unreachableTactic false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedTactic false
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]

-- @node: outcome_weighted_band_abs_bound
/-- If [the lower band endpoint has absolute value at most the endpoint bound](hyp:ha),
[the upper endpoint obeys the same bound](hyp:hb), [the weight's absolute value is at
most the weight bound](hyp:hw), and [the endpoint bound](hyp:hB) and [weight bound](hyp:hD)
are nonnegative, then [the absolute outcome-weighted band indicator is at most the
product of those two bounds](goal). -/
lemma outcome_weighted_band_abs_bound (a b w y B D : ℝ)
    (ha : |a| ≤ B) (hb : |b| ≤ B) (hw : |w| ≤ D)
    (hB : 0 ≤ B) (hD : 0 ≤ D) :
    |y * (w * indicator (a < y ∧ y ≤ b))| ≤ B * D := by
  by_cases h : a < y ∧ y ≤ b
  · have hy : |y| ≤ B := abs_le.mpr
      ⟨(abs_le.mp ha).1.trans h.1.le, h.2.trans (abs_le.mp hb).2⟩
    simp only [indicator, if_pos h, mul_one, abs_mul]
    exact mul_le_mul hy hw (abs_nonneg _) hB
  · simp only [indicator, if_neg h, mul_zero, abs_zero]
    exact mul_nonneg hB hD

-- The fitted product coefficient is already absorbed into both the band and
-- its regression; neither convergence of their residual nor of the score is assumed.
-- @node: observationLaw_changing_outcome_band_regression_sq_tendsto_probability_zero
/-- Assume [a positive denominator floor](hyp:hc), [a nonnegative weight bound](hyp:hD),
and [a nonnegative endpoint bound](hyp:hB). Suppose [the true lower endpoint](hyp:ha),
[true upper endpoint](hyp:hb), [true weight](hyp:hw0), [true regression](hyp:hm0), and
[true denominator](hyp:hp) are measurable, as are [all fitted lower endpoints](hyp:hah),
[fitted upper endpoints](hyp:hbh), [fitted weights](hyp:hw), [fitted regressions](hyp:hmh),
and [fitted denominators](hyp:hph). Suppose [true weights](hyp:hb0) and [fitted weights](hyp:hbw)
obey the absolute weight bound almost everywhere, [true endpoints](hyp:hbound0) and
[fitted endpoints](hyp:hboundh) obey the absolute endpoint bound, [true regressions](hyp:hbm0)
and [fitted regressions](hyp:hbm) obey a common absolute regression bound, and [true
and fitted denominators exceed the positive floor](hyp:hclip). If [weight errors](hyp:hew),
[regression errors](hyp:hem), and [denominator errors](hyp:hep) are square integrable,
[lower-threshold indicator errors](hyp:hrA) and [upper-threshold indicator errors](hyp:hrB)
vanish in treated integrated square in probability, and [weight errors](hyp:hrW),
[regression errors](hyp:hrM), and [denominator errors](hyp:hrP) vanish in covariate
mean square in probability, then [the fitted and true selected, inverse-probability-weighted
outcome-band regression residuals have a difference whose observation-law mean square
converges to zero in probability along even sample sizes](goal). -/
lemma observationLaw_changing_outcome_band_regression_sq_tendsto_probability_zero
    [Fintype Z] [DecidableEq Z]
    (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X) (k : ℕ)
    (a b w0 m0 p : X → ℝ) (ah bh w mh ph : ℕ → A → X → ℝ) (c D B R : ℝ)
    (hc : 0 < c) (hD : 0 ≤ D) (hB : 0 ≤ B)
    (ha : Measurable a) (hb : Measurable b) (hw0 : Measurable w0)
    (hm0 : Measurable m0) (hp : Measurable p)
    (hah : ∀ n t, Measurable (ah n t)) (hbh : ∀ n t, Measurable (bh n t))
    (hw : ∀ n t, Measurable (w n t)) (hmh : ∀ n t, Measurable (mh n t))
    (hph : ∀ n t, Measurable (ph n t))
    (hb0 : ∀ᵐ x ∂xLaw M, |w0 x| ≤ D)
    (hbw : ∀ n t, ∀ᵐ x ∂xLaw M, |w n t x| ≤ D)
    (hbound0 : ∀ᵐ x ∂xLaw M, |a x| ≤ B ∧ |b x| ≤ B)
    (hboundh : ∀ n t, ∀ᵐ x ∂xLaw M, |ah n t x| ≤ B ∧ |bh n t x| ≤ B)
    (hbm0 : ∀ᵐ x ∂xLaw M, |m0 x| ≤ R)
    (hbm : ∀ n t, ∀ᵐ x ∂xLaw M, |mh n t x| ≤ R)
    (hclip : ∀ n t, ∀ᵐ x ∂xLaw M, c ≤ p x ∧ c ≤ ph n t x)
    (hew : ∀ n t, MemLp (fun x => w n t x - w0 x) 2 (xLaw M))
    (hem : ∀ n t, MemLp (fun x => mh n t x - m0 x) 2 (xLaw M))
    (hep : ∀ n t, MemLp (fun x => ph n t x - p x) 2 (xLaw M))
    (hrA : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x, ∫ y, (indicator (y ≤ ah (2 * (n + 1)) t x) -
        indicator (y ≤ a x)) ^ 2 ∂treatedLaw M L k x ∂xLaw M)
      atTop (fun _ _ => 0))
    (hrB : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x, ∫ y, (indicator (y ≤ bh (2 * (n + 1)) t x) -
        indicator (y ≤ b x)) ^ 2 ∂treatedLaw M L k x ∂xLaw M)
      atTop (fun _ _ => 0))
    (hrW : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x, (w (2 * (n + 1)) t x - w0 x) ^ 2 ∂xLaw M)
      atTop (fun _ _ => 0))
    (hrM : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x, (mh (2 * (n + 1)) t x - m0 x) ^ 2 ∂xLaw M)
      atTop (fun _ _ => 0))
    (hrP : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x, (ph (2 * (n + 1)) t x - p x) ^ 2 ∂xLaw M)
      atTop (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ o : Obs X Z,
        (indicator (o.2.1 ∈ L.S k) * o.2.2.1 / ph (2 * (n + 1)) t o.1 *
            (o.2.2.2 * (w (2 * (n + 1)) t o.1 * indicator
              (ah (2 * (n + 1)) t o.1 < o.2.2.2 ∧
                o.2.2.2 ≤ bh (2 * (n + 1)) t o.1)) - mh (2 * (n + 1)) t o.1) -
          indicator (o.2.1 ∈ L.S k) * o.2.2.1 / p o.1 *
            (o.2.2.2 * (w0 o.1 * indicator (a o.1 < o.2.2.2 ∧ o.2.2.2 ≤ b o.1)) - m0 o.1)) ^ 2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  let band := fun (l r q : X → ℝ) (z : X × ℝ) =>
    z.2 * (q z.1 * indicator (l z.1 < z.2 ∧ z.2 ≤ r z.1))
  have hband (l r q : X → ℝ) (hl : Measurable l) (hr : Measurable r)
      (hq : Measurable q) : Measurable (band l r q) := by fun_prop
  have hbandbound (l r q : X → ℝ)
      (hlr : ∀ᵐ x ∂xLaw M, |l x| ≤ B ∧ |r x| ≤ B)
      (hq : ∀ᵐ x ∂xLaw M, |q x| ≤ D) :
      ∀ᵐ x ∂xLaw M, ∀ y, |band l r q (x, y)| ≤ B * D := by
    filter_upwards [hlr, hq] with x hx hq
    intro y
    exact outcome_weighted_band_abs_bound _ _ _ _ _ _ hx.1 hx.2 hq hB hD
  have hmem (l r q : X → ℝ) (x : X) :
      MemLp (fun y => band l r q (x, y)) 2 (treatedLaw M L k x) := by
    have := treatedLaw_isFiniteMeasure M L k x
    exact outcome_band_memLp (treatedLaw M L k x) (l x) (r x) (q x)
  have hbound n t : ∀ᵐ x ∂xLaw M,
      |a x| ≤ B ∧ |b x| ≤ B ∧ |ah n t x| ≤ B ∧ |bh n t x| ≤ B := by
    filter_upwards [hbound0, hboundh n t] with x h0 hh
    exact ⟨h0.1, h0.2, hh.1, hh.2⟩
  let f := fun n t z => band (ah (2 * (n + 1)) t) (bh (2 * (n + 1)) t)
    (w (2 * (n + 1)) t) z - band a b w0 z
  have hf n t : Measurable (f n t) :=
    (hband _ _ _ (hah _ t) (hbh _ t) (hw _ t)).sub (hband a b w0 ha hb hw0)
  have hfm n t x : MemLp (fun y => f n t (x, y)) 2 (treatedLaw M L k x) :=
    (hmem _ _ _ x).sub (hmem a b w0 x)
  obtain ⟨hbi, hbr⟩ := treatedLaw_changing_weight_band_energy_and_convergence
    M μ L k a b w0 ah bh w D ha hb hw0 hah hbh hw hbw hew hrA hrB hrW
  have hfi n t : Integrable (fun x => ∫ y, f n t (x, y) ^ 2
      ∂treatedLaw M L k x) (xLaw M) := by
    simpa only [f, band, ← mul_sub] using
      (treatedLaw_outcome_band_energy_bound M L k a b (ah (2 * (n + 1)) t)
        (bh (2 * (n + 1)) t) w0 (w (2 * (n + 1)) t) B
        ha hb (hah _ t) (hbh _ t) hw0 (hw _ t) (hbound _ t) (hbi n t)).1
  have hfr : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x, ∫ y, f n t (x, y) ^ 2
        ∂treatedLaw M L k x ∂xLaw M) atTop (fun _ _ => 0) := by
    simpa only [f, band, ← mul_sub] using
      treatedLaw_outcome_band_sq_tendsto_probability_zero M μ L k a b
        (fun n t => ah (2 * (n + 1)) t) (fun n t => bh (2 * (n + 1)) t)
        (fun _ _ => w0) (fun n t => w (2 * (n + 1)) t) B ha hb
        (fun _ _ => hw0) (fun n t => hah _ t) (fun n t => hbh _ t)
        (fun n t => hw _ t) (fun n t => hbound _ t) hbi hbr
  obtain ⟨hi, hr⟩ := treatedLaw_regression_error_energy_and_convergence M μ L k f
    (fun n t x => mh (2 * (n + 1)) t x - m0 x) hf
    (fun n t => (hmh _ t).sub hm0) hfm (fun n t => hem _ t) hfi hfr hrM
  have hid n t z :
      (band (ah (2 * (n + 1)) t) (bh (2 * (n + 1)) t) (w (2 * (n + 1)) t) z -
        mh (2 * (n + 1)) t z.1) - (band a b w0 z - m0 z.1) =
      f n t z - (mh (2 * (n + 1)) t z.1 - m0 z.1) := by
    dsimp only [f]
    ring
  apply observationLaw_changing_selected_denominator_sq_tendsto_probability_zero
    M μ L k (fun z => band a b w0 z - m0 z.1)
    (fun n t z => band (ah (2 * (n + 1)) t) (bh (2 * (n + 1)) t)
      (w (2 * (n + 1)) t) z - mh (2 * (n + 1)) t z.1)
    p (fun n t => ph (2 * (n + 1)) t) c (B * D + R) (2 * (B * D + R)) hc
    ((hband a b w0 ha hb hw0).sub (hm0.comp measurable_fst))
    (fun n t => (hband _ _ _ (hah _ t) (hbh _ t) (hw _ t)).sub
      ((hmh _ t).comp measurable_fst)) hp (fun n t => hph _ t) (fun n t => hclip _ t)
  · filter_upwards [hbandbound a b w0 hbound0 hb0, hbm0] with x hx hm
    intro y
    exact (abs_sub _ _).trans (add_le_add (hx y) hm)
  · intro n t
    filter_upwards [hbandbound a b w0 hbound0 hb0,
      hbandbound (ah (2 * (n + 1)) t) (bh (2 * (n + 1)) t)
        (w (2 * (n + 1)) t) (hboundh _ t) (hbw _ t), hbm0, hbm _ t] with x h0 hh hm0 hm
    intro y
    exact (abs_sub _ _).trans (by
      have h1 := (abs_sub _ _).trans (add_le_add (hh y) hm)
      have h2 := (abs_sub _ _).trans (add_le_add (h0 y) hm0)
      linarith)
  · exact fun n t => hep _ t
  · intro n t
    simpa only [hid] using hi n t
  · simpa only [hid] using hr
  · exact hrP

-- @node: encoded_continuous_weighted_plus_IFJ_sq_tendsto_probability_zero
/-- Suppose [the true continuous nuisance is admissible](hyp:he0), [fitted nuisances
are clipped](hyp:hclip), [fitted shares lie in the simplex](hyp:hshares), [all encoded
fitted components are measurable](hyp:hm), [boundary densities are bounded](hyp:hd),
and [the encoded estimates satisfy the finite nuisance rates](hyp:hr). Under
[baseline overlap at the specified floor](hyp:hov), [clipping of all fitted denominators
at that floor](hyp:hden), and [a boundary level below the last baseline level](hyp:hk),
[the upper-side outcome influence term multiplied by the product-score weight and
the upper adjacent propensity converges to its true counterpart in observation-law
mean square in probability along even sample sizes](goal). -/
lemma encoded_continuous_weighted_plus_IFJ_sq_tendsto_probability_zero
    [Fintype Z]
    (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n t, ContClipping M L (eh n t))
    (hshares : ∀ n t, ContFittedSharesSimplex L (eh n t))
    (hm : ∀ n t d, Measurable (contComponent M L (eh n t) d))
    (hd : BoundaryDensitiesBounded M L)
    (hr : FiniteNuisanceRates M μ (fun n t => contComponent M L (eh n t))
      (contComponent M L (trueNuisance M L)))
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (hden : ∀ n t, ContDenominatorsClipped L (eh n t) cpi)
    (g : RegularIndex L) (k j : ℕ) (hk : k < L.K) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ o : Obs X Z,
        ((eh (2 * (n + 1)) t).gamma g o.1 *
            positiveValue (eh (2 * (n + 1)) t).pLev (k + 1) o.1 *
            IFJ M L (eh (2 * (n + 1)) t) true k j o -
          (trueNuisance M L).gamma g o.1 *
            positiveValue (trueNuisance M L).pLev (k + 1) o.1 *
            IFJ M L (trueNuisance M L) true k j o) ^ 2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  classical
  let er := fun n t => restrictContShares L (eh n t)
  have her n t : ContAdmissible M L (er n t) :=
    restrictContShares_admissible_of_encoded_clipping M L (eh n t)
      (hclip n t) (hshares n t) (hm n t)
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  let i : PositiveIndex L.K := ⟨k + 1, by omega⟩
  let B := |M.yMin| + |M.yMax|
  let w := fun (e : NuisanceCont L) x => e.gamma g x * positiveValue e.pLev (k + 1) x
  let J := fun (e : NuisanceCont L) => meanValue e.Jplus k j
  have hw (e : NuisanceCont L) (he : ContAdmissible M L e) :
      Measurable (w e) ∧ (∀ᵐ x ∂xLaw M, |w e x| ≤ 1) := by
    have hp := (fitted_continuous_full_coordinates M L e he (k + 1)).1
    rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hg, hgm, _⟩
    refine ⟨by first | fun_prop | exact (hgm g).mul hp.1, ?_⟩
    filter_upwards [hg g, hp.2] with x hx hy
    dsimp only [w]
    rw [abs_mul, abs_of_nonneg hx.1]
    exact (mul_le_mul hx.2 hy (abs_nonneg _) zero_le_one).trans (by norm_num)
  have hJ (e : NuisanceCont L) (he : ContAdmissible M L e) :
      Measurable (J e) ∧ (∀ᵐ x ∂xLaw M, |J e x| ≤ B) :=
    ⟨by first | fun_prop | exact continuous_admissible_meanValue_measurable M L e he k j,
      (continuous_admissible_band_means_abs_bound M L e he k j).1⟩
  have hpi (e : NuisanceCont L) (he : ContAdmissible M L e) :
      Measurable (e.piLev i) ∧ (∀ᵐ x ∂xLaw M, |e.piLev i x| ≤ 1) := by
    rcases he with ⟨_, _, _, _, hb, hm, _⟩
    refine ⟨by first | fun_prop | exact hm i, ?_⟩
    filter_upwards [hb i] with x hx
    simpa only [abs_of_nonneg hx.1] using hx.2
  have hmem (f : X → ℝ) (hf : Measurable f) (R : ℝ)
      (hb : ∀ᵐ x ∂xLaw M, |f x| ≤ R) : MemLp f 2 (xLaw M) :=
    MemLp.of_bound hf.aestronglyMeasurable R (by simpa only [Real.norm_eq_abs] using hb)
  have hmprod (e : NuisanceCont L) (he : ContAdmissible M L e) :
      Measurable (fun x => w e x * J e x) ∧
        (∀ᵐ x ∂xLaw M, |w e x * J e x| ≤ B) := by
    refine ⟨by first | fun_prop | exact (hw e he).1.mul (hJ e he).1, ?_⟩
    filter_upwards [(hw e he).2, (hJ e he).2] with x hx hy
    rw [abs_mul]
    exact (mul_le_mul hx hy (abs_nonneg _) zero_le_one).trans (by simp)
  obtain ⟨_, hrp, hrpi, _, _, _, hrg, _⟩ :=
    continuous_component_rates_to_oracle_rates M μ L eh (trueNuisance M L) hr
  have hrw := nuisanceRates_continuous_band_coefficient_sq_tendsto_probability_zero
    M μ L (trueNuisance M L) er he0 her hrp hrg g (k + 1)
  have hrJ : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x, (J (er (2 * (n + 1)) t) x - J (trueNuisance M L) x) ^ 2
        ∂xLaw M) atTop (fun _ _ => 0) := by
    let z0 : Z := Classical.choice inferInstance
    simpa only [contComponent, J, er, restrictContShares] using
      nuisanceRates_xLaw_sq_tendsto_probability_zero M μ _ _ hr (11, k, j, z0)
  have hrm := dml_weighted_residual_sq_tendsto_probability_zero μ (xLaw M)
    (w (trueNuisance M L)) (J (trueNuisance M L))
    (fun n t => w (er (2 * (n + 1)) t)) (fun n t => J (er (2 * (n + 1)) t)) 1 B
    (hw _ he0).1 (hJ _ he0).1 (fun n t => (hw _ (her _ t)).1)
    (fun n t => (hJ _ (her _ t)).1)
    (fun n t => (hmem _ (hw _ (her _ t)).1 _ (hw _ (her _ t)).2).sub
      (hmem _ (hw _ he0).1 _ (hw _ he0).2))
    (fun n t => (hmem _ (hJ _ (her _ t)).1 _ (hJ _ (her _ t)).2).sub
      (hmem _ (hJ _ he0).1 _ (hJ _ he0).2))
    (fun n t => (hw _ (her _ t)).2) (fun _ _ => (hJ _ he0).2) hrw hrJ
  have hcl n t : ∀ᵐ x ∂xLaw M,
      cpi / 2 ≤ (trueNuisance M L).piLev i x ∧ cpi / 2 ≤ (er n t).piLev i x := by
    apply Eventually.of_forall
    intro x
    refine ⟨?_, (hden n t).1 i x |>.1⟩
    have hx := hov.2 x i.val i.property.1 i.property.2
    change cpi / 2 ≤ (levelSetProb M L).1 i.val x
    linarith [hov.1]
  have hs := observationLaw_changing_outcome_band_regression_sq_tendsto_probability_zero
    M μ L (k + 1) (nuValue M (trueNuisance M L) k j)
    (nuValue M (trueNuisance M L) k (j + 1)) (w (trueNuisance M L))
    (fun x => w (trueNuisance M L) x * J (trueNuisance M L) x)
    ((trueNuisance M L).piLev i)
    (fun n t => nuValue M (er n t) k j) (fun n t => nuValue M (er n t) k (j + 1))
    (fun n t => w (er n t)) (fun n t x => w (er n t) x * J (er n t) x)
    (fun n t => (er n t).piLev i) (cpi / 2) 1 B B
    (by linarith [hov.1]) zero_le_one (by dsimp only [B]; positivity)
    (by fun_prop) (by fun_prop) (hw _ he0).1 (hmprod _ he0).1 (hpi _ he0).1
    (fun n t => continuous_admissible_nuValue_measurable M L _ (her n t) k j)
    (fun n t => continuous_admissible_nuValue_measurable M L _ (her n t) k (j + 1))
    (fun n t => (hw _ (her n t)).1) (fun n t => (hmprod _ (her n t)).1)
    (fun n t => (hpi _ (her n t)).1) (hw _ he0).2 (fun n t => (hw _ (her n t)).2)
    (by filter_upwards [continuous_admissible_nuValue_abs_bound M L _ he0 k j,
          continuous_admissible_nuValue_abs_bound M L _ he0 k (j + 1)] with x ha hb
        exact ⟨ha, hb⟩)
    (fun n t => by
      filter_upwards [continuous_admissible_nuValue_abs_bound M L _ (her n t) k j,
        continuous_admissible_nuValue_abs_bound M L _ (her n t) k (j + 1)] with x ha hb
      exact ⟨ha, hb⟩)
    (hmprod _ he0).2 (fun n t => (hmprod _ (her n t)).2) hcl
    (fun n t => (hmem _ (hw _ (her n t)).1 _ (hw _ (her n t)).2).sub
      (hmem _ (hw _ he0).1 _ (hw _ he0).2))
    (fun n t => (hmem _ (hmprod _ (her n t)).1 _ (hmprod _ (her n t)).2).sub
      (hmem _ (hmprod _ he0).1 _ (hmprod _ he0).2))
    (fun n t => (hmem _ (hpi _ (her n t)).1 _ (hpi _ (her n t)).2).sub
      (hmem _ (hpi _ he0).1 _ (hpi _ he0).2))
    (encoded_continuous_nuValue_indicator_sq_tendsto_probability_zero
      M μ L he0 eh hclip hshares hm hd hr k j (k + 1) (Or.inl rfl))
    (encoded_continuous_nuValue_indicator_sq_tendsto_probability_zero
      M μ L he0 eh hclip hshares hm hd hr k (j + 1) (k + 1) (Or.inl rfl))
    hrw hrm (nuisanceRates_xLaw_sq_tendsto_probability_zero M μ _ _ hrpi i)
  convert hs using 1
  funext n t
  congr 1
  funext o
  have hlev : 1 ≤ k + 1 ∧ k + 1 ≤ L.K := by omega
  simp only [IFJ, Bool.not_true, Bool.false_and, Bool.false_eq_true, if_false, if_true,
    w, J, er, restrictContShares, nuValue, positiveValue, dif_pos hlev, i]
  ring

end Papers.TbsPrteOptimalTransport

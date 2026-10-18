module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLChangingSelectedDenominators
/-! Moving bands centered by fitted regressions.
The numerator error separates into the moving weighted band and the fitted
conditional mean error. The treated-law mass bound and clipped denominators
transfer their energies to the observed regression residual. -/
public section
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]

-- @node: treatedLaw_regression_error_energy_and_convergence
/-- Suppose [the covariate-outcome functions are measurable](hyp:hf), [the covariate
regressions are measurable](hyp:hm), [the functions have square-integrable treated-law
sections](hyp:hfm), [the regressions are square integrable over covariates](hyp:hmm),
and [the functions' conditional squared energies are integrable over covariates](hyp:hfi).
If [the functions' integrated squared energies vanish in probability](hyp:hrf) and
[the regressions' covariate mean squares vanish in probability](hyp:hrm), then
[subtracting each regression from its function gives integrable conditional squared
energies whose covariate averages converge to zero in probability](goal). -/
lemma treatedLaw_regression_error_energy_and_convergence
    (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X) (k : ℕ)
    (f : ℕ → A → X × ℝ → ℝ) (m : ℕ → A → X → ℝ)
    (hf : ∀ n t, Measurable (f n t)) (hm : ∀ n t, Measurable (m n t))
    (hfm : ∀ n t x, MemLp (fun y => f n t (x, y)) 2 (treatedLaw M L k x))
    (hmm : ∀ n t, MemLp (m n t) 2 (xLaw M))
    (hfi : ∀ n t, Integrable (fun x => ∫ y, f n t (x, y) ^ 2
      ∂treatedLaw M L k x) (xLaw M))
    (hrf : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x, ∫ y, f n t (x, y) ^ 2 ∂treatedLaw M L k x ∂xLaw M)
      atTop (fun _ _ => 0))
    (hrm : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x, m n t x ^ 2 ∂xLaw M) atTop (fun _ _ => 0)) :
    (∀ n t, Integrable (fun x => ∫ y, (f n t (x, y) - m n t x) ^ 2
      ∂treatedLaw M L k x) (xLaw M)) ∧
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x, ∫ y, (f n t (x, y) - m n t x) ^ 2
        ∂treatedLaw M L k x ∂xLaw M) atTop (fun _ _ => 0) := by
  let g := fun n t (z : X × ℝ) => -m n t z.1
  have hg n t : Measurable (g n t) := by fun_prop
  have hgm n t x : MemLp (fun y => g n t (x, y)) 2 (treatedLaw M L k x) := by
    have := treatedLaw_isFiniteMeasure M L k x
    exact memLp_const (-m n t x)
  have hgi n t := treatedLaw_bounded_multiplier_integrated_sq_le M L k
    (fun x => -m n t x) (fun _ => 1) (by fun_prop) measurable_const
    (fun _ _ => by norm_num) (hmm n t).neg.integrable_sq
  have hgr : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x, ∫ y, g n t (x, y) ^ 2 ∂treatedLaw M L k x ∂xLaw M)
      atTop (fun _ _ => 0) := by
    apply probability_zero_of_nonneg_le μ _ _ hrm
    intro n
    apply Eventually.of_forall
    intro t
    refine ⟨integral_nonneg fun x => integral_nonneg fun y => sq_nonneg _, ?_⟩
    simpa only [g, mul_one, neg_sq] using (hgi n t).2
  refine ⟨?_, ?_⟩
  · intro n t
    simpa only [g, sub_eq_add_neg, mul_one] using
      (treatedLaw_sum_integrated_sq_le M L k (f n t) (g n t) (hf n t) (hg n t)
        (hfm n t) (hgm n t) (hfi n t) (by simpa only [g, mul_one] using (hgi n t).1)).1
  · simpa only [g, sub_eq_add_neg] using treatedLaw_sum_sq_tendsto_probability_zero
      M μ L k f g hf hg hfm hgm hfi
      (fun n t => by simpa only [g, mul_one] using (hgi n t).1) hrf hgr

-- The fitted product coefficient is already absorbed into both the band and
-- its regression; neither convergence of their residual nor of the score is assumed.
-- @node: observationLaw_changing_band_regression_sq_tendsto_probability_zero
/-- Assume [a positive denominator floor](hyp:hc) and [a nonnegative weight bound](hyp:hD).
Suppose [the true lower endpoint](hyp:ha), [true upper endpoint](hyp:hb), [true weight](hyp:hw0),
[true regression](hyp:hm0), and [true denominator](hyp:hp) are measurable, as are
[all fitted lower endpoints](hyp:hah), [fitted upper endpoints](hyp:hbh), [fitted weights](hyp:hw),
[fitted regressions](hyp:hmh), and [fitted denominators](hyp:hph). Suppose [true weights](hyp:hb0)
and [fitted weights](hyp:hbw) obey the common absolute weight bound almost everywhere,
[true regressions](hyp:hbm0) and [fitted regressions](hyp:hbm) obey the common absolute
regression bound, and [true and fitted denominators exceed the positive floor](hyp:hclip).
If [weight errors](hyp:hew), [regression errors](hyp:hem), and [denominator errors](hyp:hep)
are square integrable, [lower-threshold indicator errors](hyp:hrA) and [upper-threshold
indicator errors](hyp:hrB) vanish in treated integrated square in probability, and
[weight errors](hyp:hrW), [regression errors](hyp:hrM), and [denominator errors](hyp:hrP)
vanish in covariate mean square in probability, then [the fitted and true selected,
inverse-probability-weighted band regression residuals differ by a quantity whose
observation-law mean square converges to zero in probability along even sample sizes](goal). -/
lemma observationLaw_changing_band_regression_sq_tendsto_probability_zero
    [Fintype Z] [DecidableEq Z]
    (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X) (k : ℕ)
    (a b w0 m0 p : X → ℝ) (ah bh w mh ph : ℕ → A → X → ℝ) (c D R : ℝ)
    (hc : 0 < c) (hD : 0 ≤ D)
    (ha : Measurable a) (hb : Measurable b) (hw0 : Measurable w0)
    (hm0 : Measurable m0) (hp : Measurable p)
    (hah : ∀ n t, Measurable (ah n t)) (hbh : ∀ n t, Measurable (bh n t))
    (hw : ∀ n t, Measurable (w n t)) (hmh : ∀ n t, Measurable (mh n t))
    (hph : ∀ n t, Measurable (ph n t))
    (hb0 : ∀ᵐ x ∂xLaw M, |w0 x| ≤ D)
    (hbw : ∀ n t, ∀ᵐ x ∂xLaw M, |w n t x| ≤ D)
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
            (w (2 * (n + 1)) t o.1 * indicator
              (ah (2 * (n + 1)) t o.1 < o.2.2.2 ∧
                o.2.2.2 ≤ bh (2 * (n + 1)) t o.1) - mh (2 * (n + 1)) t o.1) -
          indicator (o.2.1 ∈ L.S k) * o.2.2.1 / p o.1 *
            (w0 o.1 * indicator (a o.1 < o.2.2.2 ∧ o.2.2.2 ≤ b o.1) - m0 o.1)) ^ 2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  let band := fun (l r q : X → ℝ) (z : X × ℝ) =>
    q z.1 * indicator (l z.1 < z.2 ∧ z.2 ≤ r z.1)
  have hband (l r q : X → ℝ) (hl : Measurable l) (hr : Measurable r)
      (hq : Measurable q) : Measurable (band l r q) := by fun_prop
  have hbound (l r q : X → ℝ) (hq : ∀ᵐ x ∂xLaw M, |q x| ≤ D) :
      ∀ᵐ x ∂xLaw M, ∀ y, |band l r q (x, y)| ≤ D := by
    filter_upwards [hq] with x hx
    intro y
    dsimp only [band]
    unfold indicator
    split_ifs <;> simp [hx, hD]
  have hmem (l r q : X → ℝ) (hl : Measurable l) (hr : Measurable r)
      (hq : Measurable q) (x : X) :
      MemLp (fun y => band l r q (x, y)) 2 (treatedLaw M L k x) := by
    have := treatedLaw_isFiniteMeasure M L k x
    apply MemLp.of_bound (by
      first | fun_prop | exact ((hband l r q hl hr hq).comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable) |q x|
    apply Eventually.of_forall
    intro y
    dsimp only [band]
    unfold indicator
    split_ifs <;> simp [Real.norm_eq_abs]
  let f := fun n t z => band (ah (2 * (n + 1)) t) (bh (2 * (n + 1)) t)
    (w (2 * (n + 1)) t) z - band a b w0 z
  have hf n t : Measurable (f n t) :=
    (hband _ _ _ (hah _ t) (hbh _ t) (hw _ t)).sub (hband a b w0 ha hb hw0)
  have hfm n t x : MemLp (fun y => f n t (x, y)) 2 (treatedLaw M L k x) :=
    (hmem _ _ _ (hah _ t) (hbh _ t) (hw _ t) x).sub (hmem a b w0 ha hb hw0 x)
  obtain ⟨hfi, hfr⟩ := treatedLaw_changing_weight_band_energy_and_convergence
    M μ L k a b w0 ah bh w D ha hb hw0 hah hbh hw hbw hew hrA hrB hrW
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
    p (fun n t => ph (2 * (n + 1)) t) c (D + R) (2 * (D + R)) hc
    ((hband a b w0 ha hb hw0).sub (hm0.comp measurable_fst))
    (fun n t => (hband _ _ _ (hah _ t) (hbh _ t) (hw _ t)).sub
      ((hmh _ t).comp measurable_fst)) hp (fun n t => hph _ t) (fun n t => hclip _ t)
  · filter_upwards [hbound a b w0 hb0, hbm0] with x hx hm
    intro y
    exact (abs_sub _ _).trans (add_le_add (hx y) hm)
  · intro n t
    filter_upwards [hbound a b w0 hb0,
      hbound (ah (2 * (n + 1)) t) (bh (2 * (n + 1)) t)
        (w (2 * (n + 1)) t) (hbw _ t), hbm0, hbm _ t] with x h0 hh hm0 hm
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

end Papers.TbsPrteOptimalTransport

module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLChangingSelectedDenominators
/-! Observed centered bands with moving boundaries, weights, and denominators.
The treated-band energy bound and the clipped reciprocal bound jointly control
the discrepancy used in the conditional Chebyshev step of the DML proof. -/
public section
set_option linter.style.haveILetI false
set_option linter.style.openClassical false
set_option linter.unreachableTactic false
set_option linter.unusedFintypeInType false
set_option linter.unusedTactic false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]
  [Fintype Z]

-- @node: observationLaw_changing_centered_band_sq_tendsto_probability_zero
/-- Suppose [the denominator floor is positive](hyp:hc), [the weight bound is
nonnegative](hyp:hD), [the true lower and upper boundaries, weight, and denominator
are measurable](hyp:ha,hb,hw0,hp), and [their fitted counterparts are measurable at
every sample size and training realization](hyp:hah,hbh,hw,hph). If [the true weight
is bounded in absolute value](hyp:hb0), [all fitted weights obey the same bound](hyp:hbw),
[both true and fitted denominators are at least the common floor](hyp:hclip), [weight and
denominator errors have finite second moments](hyp:hew,hep), [the lower-boundary
indicator error energy vanishes in probability](hyp:hrA), [the upper-boundary indicator
error energy vanishes in probability](hyp:hrB), and [weight and denominator squared
errors vanish in probability](hyp:hrW,hrP), then [at training sizes twice the evaluation
size, the observed second moment of the difference between fitted and true selected,
conditionally centered, weighted band scores with their respective denominators
converges to zero in probability](goal). -/
lemma observationLaw_changing_centered_band_sq_tendsto_probability_zero
    (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X) (k : ℕ)
    (a b w0 p : X → ℝ) (ah bh w ph : ℕ → A → X → ℝ) (c D : ℝ)
    (hc : 0 < c) (hD : 0 ≤ D)
    (ha : Measurable a) (hb : Measurable b) (hw0 : Measurable w0) (hp : Measurable p)
    (hah : ∀ n t, Measurable (ah n t)) (hbh : ∀ n t, Measurable (bh n t))
    (hw : ∀ n t, Measurable (w n t)) (hph : ∀ n t, Measurable (ph n t))
    (hb0 : ∀ᵐ x ∂xLaw M, |w0 x| ≤ D)
    (hbw : ∀ n t, ∀ᵐ x ∂xLaw M, |w n t x| ≤ D)
    (hclip : ∀ n t, ∀ᵐ x ∂xLaw M, c ≤ p x ∧ c ≤ ph n t x)
    (hew : ∀ n t, MemLp (fun x => w n t x - w0 x) 2 (xLaw M))
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
    (hrP : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x, (ph (2 * (n + 1)) t x - p x) ^ 2 ∂xLaw M)
      atTop (fun _ _ => 0)) :
    let f0 : X × ℝ → ℝ := fun z => w0 z.1 * indicator (a z.1 < z.2 ∧ z.2 ≤ b z.1)
    let fh : ℕ → A → X × ℝ → ℝ := fun n t z =>
      w (2 * (n + 1)) t z.1 * indicator
        (ah (2 * (n + 1)) t z.1 < z.2 ∧ z.2 ≤ bh (2 * (n + 1)) t z.1)
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ o : Obs X Z,
        (indicator (o.2.1 ∈ L.S k) * o.2.2.1 / ph (2 * (n + 1)) t o.1 *
            (fh n t (o.1, o.2.2.2) - ∫ y, fh n t (o.1, y) ∂treatedLaw M L k o.1) -
          indicator (o.2.1 ∈ L.S k) * o.2.2.1 / p o.1 *
            (f0 (o.1, o.2.2.2) - ∫ y, f0 (o.1, y) ∂treatedLaw M L k o.1)) ^ 2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  dsimp only
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
    haveI := treatedLaw_isFiniteMeasure M L k x
    apply MemLp.of_bound (by
      first | fun_prop | exact ((hband l r q hl hr hq).comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable) |q x|
    apply Eventually.of_forall
    intro y
    dsimp only [band]
    unfold indicator
    split_ifs <;> simp [Real.norm_eq_abs]
  obtain ⟨hi, hr⟩ := treatedLaw_changing_weight_band_energy_and_convergence
    M μ L k a b w0 ah bh w D ha hb hw0 hah hbh hw hbw hew hrA hrB hrW
  apply observationLaw_changing_selected_centered_denominator_sq_tendsto_probability_zero
    M μ L k (band a b w0)
    (fun n t => band (ah (2 * (n + 1)) t) (bh (2 * (n + 1)) t)
      (w (2 * (n + 1)) t)) p (fun n t => ph (2 * (n + 1)) t) c D (2 * D)
    hc hD (by positivity) (hband a b w0 ha hb hw0)
    (fun n t => hband _ _ _ (hah _ t) (hbh _ t) (hw _ t)) hp
    (fun n t => hph _ t) (fun n t => hclip _ t) (hbound a b w0 hb0)
  · intro n t
    filter_upwards [hbound a b w0 hb0,
      hbound (ah (2 * (n + 1)) t) (bh (2 * (n + 1)) t)
        (w (2 * (n + 1)) t) (hbw _ t)] with x h0 hh
    intro y
    exact (abs_sub _ _).trans (by linarith [hh y, h0 y])
  · exact hmem a b w0 ha hb hw0
  · intro n t
    exact hmem _ _ _ (hah _ t) (hbh _ t) (hw _ t)
  · exact fun n t => hep _ t
  · exact hi
  · exact hr
  · exact hrP

-- @node: encoded_continuous_selected_centered_band_sq_tendsto_probability_zero
/-- Suppose [the true continuous-outcome nuisances are admissible](hyp:he0), [all fitted
nuisances satisfy clipping](hyp:hclip), [their instrument shares form simplexes](hyp:hshares),
[their encoded components are measurable](hyp:hm), [densities at the outcome boundaries
are bounded](hyp:hd), and [the encoded nuisance components satisfy the finite nuisance
rate conditions](hyp:hr). Under [baseline overlap](hyp:hov), [uniformly clipped fitted
denominators](hyp:hden), and [a selected positive level immediately above the band
level or equal to its positive band level](hyp:hi), [the observed second moment of the
difference between fitted and true selected, conditionally centered band scores,
weighted by the regular coefficient and positive level and divided by the respective
selection probabilities, converges to zero in probability along training sizes twice
the evaluation size](goal). -/
lemma encoded_continuous_selected_centered_band_sq_tendsto_probability_zero
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
    (g : RegularIndex L) (i : PositiveIndex L.K) (k j₀ j₁ : ℕ)
    (hi : i.val = k + 1 ∨ (1 ≤ k ∧ i.val = k)) :
    let f0 : X × ℝ → ℝ := fun z =>
      ((trueNuisance M L).gamma g z.1 *
        positiveValue (trueNuisance M L).pLev i.val z.1) *
      indicator (nuValue M (trueNuisance M L) k j₀ z.1 < z.2 ∧
        z.2 ≤ nuValue M (trueNuisance M L) k j₁ z.1)
    let fh : ℕ → A → X × ℝ → ℝ := fun n t z =>
      ((eh (2 * (n + 1)) t).gamma g z.1 *
        positiveValue (eh (2 * (n + 1)) t).pLev i.val z.1) *
      indicator (nuValue M (eh (2 * (n + 1)) t) k j₀ z.1 < z.2 ∧
        z.2 ≤ nuValue M (eh (2 * (n + 1)) t) k j₁ z.1)
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ o : Obs X Z,
        (indicator (o.2.1 ∈ L.S i.val) * o.2.2.1 / (eh (2 * (n + 1)) t).piLev i o.1 *
            (fh n t (o.1, o.2.2.2) - ∫ y, fh n t (o.1, y) ∂treatedLaw M L i.val o.1) -
          indicator (o.2.1 ∈ L.S i.val) * o.2.2.1 / (trueNuisance M L).piLev i o.1 *
            (f0 (o.1, o.2.2.2) - ∫ y, f0 (o.1, y) ∂treatedLaw M L i.val o.1)) ^ 2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  classical
  let er := fun n t => restrictContShares L (eh n t)
  have her n t : ContAdmissible M L (er n t) :=
    restrictContShares_admissible_of_encoded_clipping M L (eh n t)
      (hclip n t) (hshares n t) (hm n t)
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  let w := fun (e : NuisanceCont L) x => e.gamma g x * positiveValue e.pLev i.val x
  have hw (e : NuisanceCont L) (he : ContAdmissible M L e) :
      Measurable (w e) ∧ (∀ᵐ x ∂xLaw M, |w e x| ≤ 1) := by
    have hp := (fitted_continuous_full_coordinates M L e he i.val).1
    rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hg, hgm, _⟩
    refine ⟨?_, ?_⟩
    · first | fun_prop | exact (hgm g).mul hp.1
    · filter_upwards [hg g, hp.2] with x hx hy
      dsimp only [w]
      rw [abs_mul, abs_of_nonneg hx.1]
      exact (mul_le_mul hx.2 hy (abs_nonneg _) zero_le_one).trans (by norm_num)
  have hwm (e : NuisanceCont L) (he : ContAdmissible M L e) :
      MemLp (w e) 2 (xLaw M) := by
    apply MemLp.of_bound (by first | fun_prop | exact (hw e he).1.aestronglyMeasurable) 1
    simpa only [Real.norm_eq_abs] using (hw e he).2
  have hp (e : NuisanceCont L) (he : ContAdmissible M L e) :
      Measurable (e.piLev i) ∧ MemLp (e.piLev i) 2 (xLaw M) := by
    rcases he with ⟨_, _, _, _, hb, hm, _⟩
    have hme : Measurable (e.piLev i) := by first | fun_prop | exact hm i
    refine ⟨hme, MemLp.of_bound hme.aestronglyMeasurable 1 ?_⟩
    filter_upwards [hb i] with x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2
  obtain ⟨_, hrp, hrpi, _, _, _, hrg, _⟩ :=
    continuous_component_rates_to_oracle_rates M μ L eh (trueNuisance M L) hr
  have hc : 0 < cpi / 2 := by linarith [hov.1]
  have hclip' n t : ∀ᵐ x ∂xLaw M,
      cpi / 2 ≤ (trueNuisance M L).piLev i x ∧ cpi / 2 ≤ (er n t).piLev i x := by
    apply Eventually.of_forall
    intro x
    refine ⟨?_, (hden n t).1 i x |>.1⟩
    have hx := hov.2 x i.val i.property.1 i.property.2
    change cpi / 2 ≤ (levelSetProb M L).1 i.val x
    linarith [hov.1]
  exact observationLaw_changing_centered_band_sq_tendsto_probability_zero
    M μ L i.val (nuValue M (trueNuisance M L) k j₀)
    (nuValue M (trueNuisance M L) k j₁) (w (trueNuisance M L))
    ((trueNuisance M L).piLev i)
    (fun n t => nuValue M (er n t) k j₀)
    (fun n t => nuValue M (er n t) k j₁)
    (fun n t => w (er n t)) (fun n t => (er n t).piLev i) (cpi / 2) 1
    hc zero_le_one (by fun_prop) (by fun_prop) (hw _ he0).1 (hp _ he0).1
    (fun n t => continuous_admissible_nuValue_measurable M L _ (her n t) k j₀)
    (fun n t => continuous_admissible_nuValue_measurable M L _ (her n t) k j₁)
    (fun n t => (hw _ (her n t)).1) (fun n t => (hp _ (her n t)).1)
    (hw _ he0).2 (fun n t => (hw _ (her n t)).2) hclip'
    (fun n t => (hwm _ (her n t)).sub (hwm _ he0))
    (fun n t => (hp _ (her n t)).2.sub (hp _ he0).2)
    (encoded_continuous_nuValue_indicator_sq_tendsto_probability_zero
      M μ L he0 eh hclip hshares hm hd hr k j₀ i.val hi)
    (encoded_continuous_nuValue_indicator_sq_tendsto_probability_zero
      M μ L he0 eh hclip hshares hm hd hr k j₁ i.val hi)
    (nuisanceRates_continuous_band_coefficient_sq_tendsto_probability_zero
      M μ L (trueNuisance M L) er he0 her hrp hrg g i.val)
    (nuisanceRates_xLaw_sq_tendsto_probability_zero M μ _ _ hrpi i)

end Papers.TbsPrteOptimalTransport

module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLChangingBandRegressions
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousEncodedBand
/-! Moving threshold indicators with changing fitted coefficients and regressions.
The boundary disagreement and coefficient energies control the IFM numerator;
clipped denominators transfer this control to the observed score residual. -/
public section
set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSimpArgs false
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]

-- @node: treatedLaw_changing_weight_indicator_energy_and_convergence
/-- Suppose [the true threshold is measurable](hyp:hb), [the true weight is measurable](hyp:hw0),
[all fitted thresholds are measurable](hyp:hbh), and [all fitted weights are measurable](hyp:hw).
If [fitted weights have a common absolute bound almost everywhere over covariates](hyp:hwb),
[weight errors are square integrable](hyp:hwm), [threshold-indicator errors vanish
in treated integrated square in probability](hyp:hB), and [weight errors vanish in
covariate mean square in probability](hyp:hW), then [the difference between fitted
and true weighted lower-tail indicators has integrable conditional squared energy,
whose covariate average converges to zero in probability along even sample sizes](goal). -/
lemma treatedLaw_changing_weight_indicator_energy_and_convergence
    (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X) (k : ℕ)
    (b w0 : X → ℝ) (bh w : ℕ → A → X → ℝ) (D : ℝ)
    (hb : Measurable b) (hw0 : Measurable w0)
    (hbh : ∀ n s, Measurable (bh n s))
    (hw : ∀ n s, Measurable (w n s))
    (hwb : ∀ n s, ∀ᵐ x ∂xLaw M, |w n s x| ≤ D)
    (hwm : ∀ n s, MemLp (fun x => w n s x - w0 x) 2 (xLaw M))
    (hB : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n s => ∫ x, ∫ y, (indicator (y ≤ bh (2 * (n + 1)) s x) -
        indicator (y ≤ b x)) ^ 2 ∂treatedLaw M L k x ∂xLaw M)
      atTop (fun _ _ => 0))
    (hW : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n s => ∫ x, (w (2 * (n + 1)) s x - w0 x) ^ 2 ∂xLaw M)
      atTop (fun _ _ => 0)) :
    let d : ℕ → A → X × ℝ → ℝ := fun n s p =>
      w (2 * (n + 1)) s p.1 * indicator (p.2 ≤ bh (2 * (n + 1)) s p.1) -
      w0 p.1 * indicator (p.2 ≤ b p.1)
    (∀ n s, Integrable (fun x => ∫ y, d n s (x, y) ^ 2
      ∂treatedLaw M L k x) (xLaw M)) ∧
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n s => ∫ x, ∫ y, d n s (x, y) ^ 2
        ∂treatedLaw M L k x ∂xLaw M) atTop (fun _ _ => 0) := by
  dsimp only
  let f : ℕ → A → X × ℝ → ℝ := fun n s p =>
    w (2 * (n + 1)) s p.1 * (indicator (p.2 ≤ bh (2 * (n + 1)) s p.1) - indicator (p.2 ≤ b p.1))
  let g : ℕ → A → X × ℝ → ℝ := fun n s p =>
    (w (2 * (n + 1)) s p.1 - w0 p.1) * indicator (p.2 ≤ b p.1)
  have hBand (d : X → ℝ) (hd : Measurable d) :
      Measurable (fun p : X × ℝ => indicator (p.2 ≤ d p.1)) := by
    fun_prop
  have hf n s : Measurable (f n s) :=
    ((hw _ s).comp measurable_fst).mul
      ((hBand _ (hbh _ s)).sub (hBand _ hb))
  have hg n s : Measurable (g n s) :=
    (((hw _ s).sub hw0).comp measurable_fst).mul (hBand _ hb)
  have hfm n s x : MemLp (fun y => f n s (x, y)) 2 (treatedLaw M L k x) := by
    let := treatedLaw_isFiniteMeasure M L k x
    apply MemLp.of_bound (by
      first | fun_prop | exact ((hf n s).comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
      |w (2 * (n + 1)) s x|
    apply Eventually.of_forall
    intro y
    dsimp only [f]
    unfold indicator
    split_ifs <;> simp [Real.norm_eq_abs]
  have hgm n s x : MemLp (fun y => g n s (x, y)) 2 (treatedLaw M L k x) := by
    let := treatedLaw_isFiniteMeasure M L k x
    apply MemLp.of_bound (by
      first | fun_prop | exact ((hg n s).comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
      |w (2 * (n + 1)) s x - w0 x|
    apply Eventually.of_forall
    intro y
    dsimp only [g]
    unfold indicator
    split_ifs <;> simp [Real.norm_eq_abs]
  have hgi n s := treatedLaw_bounded_multiplier_integrated_sq_le M L k
    (fun x => w (2 * (n + 1)) s x - w0 x)
    (fun p => indicator (p.2 ≤ b p.1))
    ((hw _ s).sub hw0) (hBand _ hb)
    (fun x y => by unfold indicator; split_ifs <;> norm_num)
    (hwm _ s).integrable_sq
  have hgr : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n s => ∫ x, ∫ y, g n s (x, y) ^ 2 ∂treatedLaw M L k x ∂xLaw M)
      atTop (fun _ _ => 0) := by
    apply probability_zero_of_nonneg_le μ _ _ hW
    intro n
    apply Eventually.of_forall
    intro s
    exact ⟨integral_nonneg fun x => integral_nonneg fun y => sq_nonneg _, (hgi n s).2⟩
  have hfr := treatedLaw_weighted_quantile_indicator_sq_tendsto_probability_zero M μ L k
    b bh w D hb hbh hw hwb hB
  have hfi n s := (treatedLaw_weighted_quantile_indicator_integrated_sq_bound M L k
    b (bh (2 * (n + 1)) s) (w (2 * (n + 1)) s) D
    hb (hbh _ s) (hw _ s) (hwb _ s)).1
  have hsum n s := treatedLaw_sum_integrated_sq_le M L k (f n s) (g n s)
    (hf n s) (hg n s) (hfm n s) (hgm n s) (hfi n s) (hgi n s).1
  have hs := treatedLaw_sum_sq_tendsto_probability_zero M μ L k f g hf hg hfm hgm
    hfi (fun n s => (hgi n s).1) hfr hgr
  have hid n s p : f n s p + g n s p =
      w (2 * (n + 1)) s p.1 * indicator (p.2 ≤ bh (2 * (n + 1)) s p.1) -
      w0 p.1 * indicator (p.2 ≤ b p.1) := by
    dsimp only [f, g]
    ring
  refine ⟨?_, ?_⟩
  · intro n s
    simpa only [hid] using (hsum n s).1
  · simpa only [hid] using hs

-- @node: observationLaw_changing_indicator_regression_sq_tendsto_probability_zero
/-- Assume [a positive denominator floor](hyp:hc) and [a nonnegative weight bound](hyp:hD).
Suppose [the true threshold](hyp:hb), [true weight](hyp:hw0), [true regression](hyp:hm0),
and [true denominator](hyp:hp) are measurable, as are [all fitted thresholds](hyp:hbh),
[fitted weights](hyp:hw), [fitted regressions](hyp:hmh), and [fitted denominators](hyp:hph).
Suppose [true weights](hyp:hb0) and [fitted weights](hyp:hbw) obey the common absolute
weight bound almost everywhere, [true regressions](hyp:hbm0) and [fitted regressions](hyp:hbm)
obey the common absolute regression bound, and [true and fitted denominators exceed
the positive floor](hyp:hclip). If [weight errors](hyp:hew), [regression errors](hyp:hem),
and [denominator errors](hyp:hep) are square integrable, [threshold-indicator errors
vanish in treated integrated square in probability](hyp:hrB), and [weight errors](hyp:hrW),
[regression errors](hyp:hrM), and [denominator errors](hyp:hrP) vanish in covariate
mean square in probability, then [the fitted and true selected, inverse-probability-weighted
lower-tail indicator regression residuals have a difference whose observation-law mean
square converges to zero in probability along even sample sizes](goal). -/
lemma observationLaw_changing_indicator_regression_sq_tendsto_probability_zero
    [Fintype Z] [DecidableEq Z]
    (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X) (k : ℕ)
    (b w0 m0 p : X → ℝ) (bh w mh ph : ℕ → A → X → ℝ) (c D R : ℝ)
    (hc : 0 < c) (hD : 0 ≤ D)
    (hb : Measurable b) (hw0 : Measurable w0)
    (hm0 : Measurable m0) (hp : Measurable p)
    (hbh : ∀ n t, Measurable (bh n t))
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
            (w (2 * (n + 1)) t o.1 * indicator (o.2.2.2 ≤ bh (2 * (n + 1)) t o.1) - mh (2 * (n + 1)) t o.1) -
          indicator (o.2.1 ∈ L.S k) * o.2.2.1 / p o.1 *
            (w0 o.1 * indicator (o.2.2.2 ≤ b o.1) - m0 o.1)) ^ 2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  let band := fun (r q : X → ℝ) (z : X × ℝ) =>
    q z.1 * indicator (z.2 ≤ r z.1)
  have hband (r q : X → ℝ) (hr : Measurable r)
      (hq : Measurable q) : Measurable (band r q) := by fun_prop
  have hbound (r q : X → ℝ) (hq : ∀ᵐ x ∂xLaw M, |q x| ≤ D) :
      ∀ᵐ x ∂xLaw M, ∀ y, |band r q (x, y)| ≤ D := by
    filter_upwards [hq] with x hx
    intro y
    dsimp only [band]
    unfold indicator
    split_ifs <;> simp [hx, hD]
  have hmem (r q : X → ℝ) (hr : Measurable r)
      (hq : Measurable q) (x : X) :
      MemLp (fun y => band r q (x, y)) 2 (treatedLaw M L k x) := by
    have := treatedLaw_isFiniteMeasure M L k x
    apply MemLp.of_bound (by
      first | fun_prop | exact ((hband r q hr hq).comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable) |q x|
    apply Eventually.of_forall
    intro y
    dsimp only [band]
    unfold indicator
    split_ifs <;> simp [Real.norm_eq_abs]
  let f := fun n t z => band (bh (2 * (n + 1)) t)
    (w (2 * (n + 1)) t) z - band b w0 z
  have hf n t : Measurable (f n t) :=
    (hband _ _ (hbh _ t) (hw _ t)).sub (hband b w0 hb hw0)
  have hfm n t x : MemLp (fun y => f n t (x, y)) 2 (treatedLaw M L k x) :=
    (hmem _ _ (hbh _ t) (hw _ t) x).sub (hmem b w0 hb hw0 x)
  obtain ⟨hfi, hfr⟩ := treatedLaw_changing_weight_indicator_energy_and_convergence
    M μ L k b w0 bh w D hb hw0 hbh hw hbw hew hrB hrW
  obtain ⟨hi, hr⟩ := treatedLaw_regression_error_energy_and_convergence M μ L k f
    (fun n t x => mh (2 * (n + 1)) t x - m0 x) hf
    (fun n t => (hmh _ t).sub hm0) hfm (fun n t => hem _ t) hfi hfr hrM
  have hid n t z :
      (band (bh (2 * (n + 1)) t) (w (2 * (n + 1)) t) z -
        mh (2 * (n + 1)) t z.1) - (band b w0 z - m0 z.1) =
      f n t z - (mh (2 * (n + 1)) t z.1 - m0 z.1) := by
    dsimp only [f]
    ring
  apply observationLaw_changing_selected_denominator_sq_tendsto_probability_zero
    M μ L k (fun z => band b w0 z - m0 z.1)
    (fun n t z => band (bh (2 * (n + 1)) t)
      (w (2 * (n + 1)) t) z - mh (2 * (n + 1)) t z.1)
    p (fun n t => ph (2 * (n + 1)) t) c (D + R) (2 * (D + R)) hc
    ((hband b w0 hb hw0).sub (hm0.comp measurable_fst))
    (fun n t => (hband _ _ (hbh _ t) (hw _ t)).sub
      ((hmh _ t).comp measurable_fst)) hp (fun n t => hph _ t) (fun n t => hclip _ t)
  · filter_upwards [hbound b w0 hb0, hbm0] with x hx hm
    intro y
    exact (abs_sub _ _).trans (add_le_add (hx y) hm)
  · intro n t
    filter_upwards [hbound b w0 hb0,
      hbound (bh (2 * (n + 1)) t)
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

-- @node: encoded_continuous_gamma_plus_IFM_sq_tendsto_probability_zero
/-- Suppose [the true continuous nuisance is admissible](hyp:he0), [fitted nuisances
are clipped](hyp:hclip), [fitted shares lie in the simplex](hyp:hshares), [all encoded
fitted components are measurable](hyp:hm), [boundary densities are bounded](hyp:hd),
and [the encoded estimates satisfy the finite nuisance rates](hyp:hr). Under
[baseline overlap at the specified floor](hyp:hov), [clipping of all fitted denominators
at that floor](hyp:hden), and [a boundary level below the last baseline level](hyp:hk),
[the fitted product-score weight times the upper-side distribution influence term
converges to its true counterpart in observation-law mean square in probability
along even sample sizes](goal). -/
lemma encoded_continuous_gamma_plus_IFM_sq_tendsto_probability_zero
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
            IFM M L (eh (2 * (n + 1)) t) true k j o -
          (trueNuisance M L).gamma g o.1 *
            IFM M L (trueNuisance M L) true k j o) ^ 2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  classical
  let er := fun n t => restrictContShares L (eh n t)
  have her n t : ContAdmissible M L (er n t) :=
    restrictContShares_admissible_of_encoded_clipping M L (eh n t)
      (hclip n t) (hshares n t) (hm n t)
  have : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  let i : PositiveIndex L.K := ⟨k + 1, by omega⟩
  let B : ℝ := 1
  let w := fun (e : NuisanceCont L) x => e.gamma g x
  let J := fun (e : NuisanceCont L) => boundaryValue e.Mplus k j
  have hw (e : NuisanceCont L) (he : ContAdmissible M L e) :
      Measurable (w e) ∧ (∀ᵐ x ∂xLaw M, |w e x| ≤ 1) := by
    rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hg, hgm, _⟩
    refine ⟨by fun_prop, ?_⟩
    filter_upwards [hg g] with x hx
    simpa only [w, abs_of_nonneg hx.1] using hx.2
  have hJ (e : NuisanceCont L) (he : ContAdmissible M L e) :
      Measurable (J e) ∧ (∀ᵐ x ∂xLaw M, |J e x| ≤ B) := by
    rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hb, hm, _⟩
    change Measurable (fun x => J e x) ∧ (∀ᵐ x ∂xLaw M, |J e x| ≤ B)
    by_cases hj : k < L.K ∧ j ≤ L.l k
    · refine ⟨?_, ?_⟩
      · first | fun_prop | simpa only [J, boundaryValue, dif_pos hj] using hm ⟨(k,j), hj⟩
      · filter_upwards [hb ⟨(k,j), hj⟩] with x hx
        simpa only [J, boundaryValue, dif_pos hj, abs_of_nonneg hx.1, B] using hx.2
    · by_cases hlast : k < L.K ∧ j = L.l k + 1
      · simp only [J, boundaryValue, dif_neg hj, if_pos hlast, abs_one, B]
        exact ⟨measurable_const, Eventually.of_forall (fun _ => le_rfl)⟩
      · simp only [J, boundaryValue, dif_neg hj, if_neg hlast, abs_zero, B]
        exact ⟨measurable_const, Eventually.of_forall (fun _ => zero_le_one)⟩
  have hpi (e : NuisanceCont L) (he : ContAdmissible M L e) :
      Measurable (e.piLev i) ∧ (∀ᵐ x ∂xLaw M, |e.piLev i x| ≤ 1) := by
    rcases he with ⟨_, _, _, _, hb, hm, _⟩
    refine ⟨by fun_prop, ?_⟩
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
  obtain ⟨_, _, hrpi, _, _, _, hrg, _⟩ :=
    continuous_component_rates_to_oracle_rates M μ L eh (trueNuisance M L) hr
  have hrw := nuisanceRates_xLaw_sq_tendsto_probability_zero M μ _ _ hrg g
  have hrJ : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x, (J (er (2 * (n + 1)) t) x - J (trueNuisance M L) x) ^ 2
        ∂xLaw M) atTop (fun _ _ => 0) := by
    let z0 : Z := Classical.choice inferInstance
    simpa only [contComponent, J, er, restrictContShares] using
      nuisanceRates_xLaw_sq_tendsto_probability_zero M μ _ _ hr (9, k, j, z0)
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
  have hs := observationLaw_changing_indicator_regression_sq_tendsto_probability_zero
    M μ L (k + 1) (nuValue M (trueNuisance M L) k j) (w (trueNuisance M L))
    (fun x => w (trueNuisance M L) x * J (trueNuisance M L) x)
    ((trueNuisance M L).piLev i)
    (fun n t => nuValue M (er n t) k j)
    (fun n t => w (er n t)) (fun n t x => w (er n t) x * J (er n t) x)
    (fun n t => (er n t).piLev i) (cpi / 2) 1 B
    (by linarith [hov.1]) zero_le_one
    (by fun_prop) (hw _ he0).1 (hmprod _ he0).1 (hpi _ he0).1
    (fun n t => continuous_admissible_nuValue_measurable M L _ (her n t) k j)
    (fun n t => (hw _ (her n t)).1) (fun n t => (hmprod _ (her n t)).1)
    (fun n t => (hpi _ (her n t)).1) (hw _ he0).2 (fun n t => (hw _ (her n t)).2)
    (hmprod _ he0).2 (fun n t => (hmprod _ (her n t)).2) hcl
    (fun n t => (hmem _ (hw _ (her n t)).1 _ (hw _ (her n t)).2).sub
      (hmem _ (hw _ he0).1 _ (hw _ he0).2))
    (fun n t => (hmem _ (hmprod _ (her n t)).1 _ (hmprod _ (her n t)).2).sub
      (hmem _ (hmprod _ he0).1 _ (hmprod _ he0).2))
    (fun n t => (hmem _ (hpi _ (her n t)).1 _ (hpi _ (her n t)).2).sub
      (hmem _ (hpi _ he0).1 _ (hpi _ he0).2))
    (encoded_continuous_nuValue_indicator_sq_tendsto_probability_zero
      M μ L he0 eh hclip hshares hm hd hr k j (k + 1) (Or.inl rfl))
    hrw hrm (nuisanceRates_xLaw_sq_tendsto_probability_zero M μ _ _ hrpi i)
  convert hs using 1
  funext n t
  congr 1
  funext o
  have hlev : 1 ≤ k + 1 ∧ k + 1 ≤ L.K := by omega
  simp only [IFM, Bool.not_true, Bool.false_eq_true, false_and, if_false, if_true,
    w, J, er, restrictContShares, nuValue, positiveValue, dif_pos hlev, i]
  ring

-- @node: encoded_continuous_gamma_minus_IFM_sq_tendsto_probability_zero
/-- Suppose [the true continuous nuisance is admissible](hyp:he0), [fitted nuisances
are clipped](hyp:hclip), [fitted shares lie in the simplex](hyp:hshares), [all encoded
fitted components are measurable](hyp:hm), [boundary densities are bounded](hyp:hd),
and [the encoded estimates satisfy the finite nuisance rates](hyp:hr). Under
[baseline overlap at the specified floor](hyp:hov), [clipping of all fitted denominators
at that floor](hyp:hden), [a boundary level at least one](hyp:hk0), and [a boundary
level below the last baseline level](hyp:hk), [the fitted product-score weight times
the lower-side distribution influence term converges to its true counterpart in
observation-law mean square in probability along even sample sizes](goal). -/
lemma encoded_continuous_gamma_minus_IFM_sq_tendsto_probability_zero
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
    (g : RegularIndex L) (k j : ℕ) (hk0 : 1 ≤ k) (hk : k < L.K) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ o : Obs X Z,
        ((eh (2 * (n + 1)) t).gamma g o.1 *
            IFM M L (eh (2 * (n + 1)) t) false k j o -
          (trueNuisance M L).gamma g o.1 *
            IFM M L (trueNuisance M L) false k j o) ^ 2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  classical
  let er := fun n t => restrictContShares L (eh n t)
  have her n t : ContAdmissible M L (er n t) :=
    restrictContShares_admissible_of_encoded_clipping M L (eh n t)
      (hclip n t) (hshares n t) (hm n t)
  have : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  let i : PositiveIndex L.K := ⟨k, by omega⟩
  let B : ℝ := 1
  let w := fun (e : NuisanceCont L) x => e.gamma g x
  let J := fun (e : NuisanceCont L) => minusBoundaryValue e.Mminus k j
  have hw (e : NuisanceCont L) (he : ContAdmissible M L e) :
      Measurable (w e) ∧ (∀ᵐ x ∂xLaw M, |w e x| ≤ 1) := by
    rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hg, hgm, _⟩
    refine ⟨by fun_prop, ?_⟩
    filter_upwards [hg g] with x hx
    simpa only [w, abs_of_nonneg hx.1] using hx.2
  have hJ (e : NuisanceCont L) (he : ContAdmissible M L e) :
      Measurable (J e) ∧ (∀ᵐ x ∂xLaw M, |J e x| ≤ B) := by
    rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hb, hm, _⟩
    change Measurable (fun x => J e x) ∧ (∀ᵐ x ∂xLaw M, |J e x| ≤ B)
    by_cases hj : 1 ≤ k ∧ k < L.K ∧ j ≤ L.l k
    · refine ⟨?_, ?_⟩
      · first | fun_prop | simpa only [J, minusBoundaryValue, dif_pos hj] using hm ⟨(k,j), hj⟩
      · filter_upwards [hb ⟨(k,j), hj⟩] with x hx
        simpa only [J, minusBoundaryValue, dif_pos hj, abs_of_nonneg hx.1, B] using hx.2
    · by_cases hlast : 1 ≤ k ∧ k < L.K ∧ j = L.l k + 1
      · simp only [J, minusBoundaryValue, dif_neg hj, if_pos hlast, abs_one, B]
        exact ⟨measurable_const, Eventually.of_forall (fun _ => le_rfl)⟩
      · simp only [J, minusBoundaryValue, dif_neg hj, if_neg hlast, abs_zero, B]
        exact ⟨measurable_const, Eventually.of_forall (fun _ => zero_le_one)⟩
  have hpi (e : NuisanceCont L) (he : ContAdmissible M L e) :
      Measurable (e.piLev i) ∧ (∀ᵐ x ∂xLaw M, |e.piLev i x| ≤ 1) := by
    rcases he with ⟨_, _, _, _, hb, hm, _⟩
    refine ⟨by fun_prop, ?_⟩
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
  obtain ⟨_, _, hrpi, _, _, _, hrg, _⟩ :=
    continuous_component_rates_to_oracle_rates M μ L eh (trueNuisance M L) hr
  have hrw := nuisanceRates_xLaw_sq_tendsto_probability_zero M μ _ _ hrg g
  have hrJ : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x, (J (er (2 * (n + 1)) t) x - J (trueNuisance M L) x) ^ 2
        ∂xLaw M) atTop (fun _ _ => 0) := by
    let z0 : Z := Classical.choice inferInstance
    simpa only [contComponent, J, er, restrictContShares] using
      nuisanceRates_xLaw_sq_tendsto_probability_zero M μ _ _ hr (10, k, j, z0)
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
  have hs := observationLaw_changing_indicator_regression_sq_tendsto_probability_zero
    M μ L k (nuValue M (trueNuisance M L) k j) (w (trueNuisance M L))
    (fun x => w (trueNuisance M L) x * J (trueNuisance M L) x)
    ((trueNuisance M L).piLev i)
    (fun n t => nuValue M (er n t) k j)
    (fun n t => w (er n t)) (fun n t x => w (er n t) x * J (er n t) x)
    (fun n t => (er n t).piLev i) (cpi / 2) 1 B
    (by linarith [hov.1]) zero_le_one
    (by fun_prop) (hw _ he0).1 (hmprod _ he0).1 (hpi _ he0).1
    (fun n t => continuous_admissible_nuValue_measurable M L _ (her n t) k j)
    (fun n t => (hw _ (her n t)).1) (fun n t => (hmprod _ (her n t)).1)
    (fun n t => (hpi _ (her n t)).1) (hw _ he0).2 (fun n t => (hw _ (her n t)).2)
    (hmprod _ he0).2 (fun n t => (hmprod _ (her n t)).2) hcl
    (fun n t => (hmem _ (hw _ (her n t)).1 _ (hw _ (her n t)).2).sub
      (hmem _ (hw _ he0).1 _ (hw _ he0).2))
    (fun n t => (hmem _ (hmprod _ (her n t)).1 _ (hmprod _ (her n t)).2).sub
      (hmem _ (hmprod _ he0).1 _ (hmprod _ he0).2))
    (fun n t => (hmem _ (hpi _ (her n t)).1 _ (hpi _ (her n t)).2).sub
      (hmem _ (hpi _ he0).1 _ (hpi _ he0).2))
    (encoded_continuous_nuValue_indicator_sq_tendsto_probability_zero
      M μ L he0 eh hclip hshares hm hd hr k j k (Or.inr ⟨hk0, rfl⟩))
    hrw hrm (nuisanceRates_xLaw_sq_tendsto_probability_zero M μ _ _ hrpi i)
  convert hs using 1
  funext n t
  congr 1
  funext o
  have hlev : 1 ≤ k ∧ k ≤ L.K := by omega
  have hkne : k ≠ 0 := by omega
  simp only [IFM, Bool.not_false, Bool.true_eq, Bool.false_eq_true, true_and, hkne, if_false,
    w, J, er, restrictContShares, nuValue, positiveValue, dif_pos hlev, i]
  ring

end Papers.TbsPrteOptimalTransport

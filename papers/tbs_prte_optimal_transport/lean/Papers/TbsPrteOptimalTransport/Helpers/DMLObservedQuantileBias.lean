module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousQuantileDenominatorBias
public import Papers.TbsPrteOptimalTransport.Helpers.ObservedBandBoundary
/-! Observation-level quadratic quantile bias with fitted denominators.
The selected-treatment tower identity retains the actual conditional cell mass.
Its mass bound and denominator clipping transfer the quarter-rate boundary
remainder to the IFJ/IFM observation scale, including the fixed lower endpoint. -/
public section
set_option linter.style.haveILetI false
set_option linter.style.openClassical false
set_option linter.style.whitespace false
set_option linter.unreachableTactic false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: clipped_selected_treatment_weight_bound
/-- If [the weight is measurable](hyp:hw), [the denominator is measurable](hyp:hc),
[B is nonnegative](hyp:hB), [the clipping constant is positive](hyp:hc0), [the weight's absolute
value is at most B almost everywhere](hyp:hwb), and [the denominator is at least the clipping
constant almost everywhere](hyp:hclip), then [the weight times selected-treatment cell mass
divided by the denominator is measurable and has absolute value at most B divided by the
clipping constant almost everywhere](goal). -/
lemma clipped_selected_treatment_weight_bound
    (L : LevelData Z X) (i : ℕ) (w c : X → ℝ)
    (hw : Measurable w) (hc : Measurable c) (B c0 : ℝ)
    (hB : 0 ≤ B) (hc0 : 0 < c0)
    (hwb : ∀ᵐ x ∂xLaw M, |w x| ≤ B)
    (hclip : ∀ᵐ x ∂xLaw M, c0 ≤ c x) :
    Measurable (fun x => w x * (selectedTreatmentMass M L i x / c x)) ∧
    (∀ᵐ x ∂xLaw M, |w x * (selectedTreatmentMass M L i x / c x)| ≤ B / c0) := by
  refine ⟨by fun_prop, ?_⟩
  filter_upwards [hwb, hclip] with x hwx hcx
  have hm := selectedTreatmentMass_range M L i x
  have hpos := hc0.trans_le hcx
  rw [abs_mul, abs_div, abs_of_nonneg hm.1, abs_of_pos hpos]
  calc
    _ ≤ B * (1 / c0) := mul_le_mul hwx
      (div_le_div₀ zero_le_one hm.2 hc0 hcx) (div_nonneg hm.1 hpos.le) hB
    _ = B / c0 := by ring

-- @node: nuisanceRates_observed_debiased_quantile_bias_root_n_negligible
/-- Suppose [the true boundary is measurable](hyp:ht), [fitted boundaries are measurable](hyp:hf),
[weights are measurable](hyp:hw), [denominators are measurable](hyp:hc), [B is nonnegative](hyp:hB),
and [the denominator floor is positive](hyp:hc0). Assume [weights have absolute value at most B
almost everywhere](hyp:hwb), [denominators are bounded below by that floor almost everywhere](hyp:hclip),
[boundary errors are square integrable](hyp:he), [the local radius is positive](hyp:hr),
[C is nonnegative](hyp:hC), [treated outcome interval probabilities near the true boundary are
bounded by C times length almost everywhere in covariates](hyp:hdensity), and [nuisance errors
satisfy fourth-root little-order rates](hyp:hrates). Then [the population mean of the debiased
quantile boundary remainder, weighted by the selected-treatment indicator and fitted inverse
denominator, times the square root of the evaluation size, converges to zero in probability](goal). -/
lemma nuisanceRates_observed_debiased_quantile_bias_root_n_negligible
    {A T : Type*} [MeasurableSpace A] (μ : Measure A)
    (L : LevelData Z X) (i : ℕ)
    (truth : T → X → ℝ) (fit : ℕ → A → T → X → ℝ)
    (w c : ℕ → A → X → ℝ) (b : T) (B c0 r C : ℝ)
    (ht : Measurable (truth b)) (hf : ∀ n a, Measurable (fit n a b))
    (hw : ∀ n a, Measurable (w n a)) (hc : ∀ n a, Measurable (c n a))
    (hB : 0 ≤ B) (hc0 : 0 < c0)
    (hwb : ∀ n a, ∀ᵐ x ∂xLaw M, |w n a x| ≤ B)
    (hclip : ∀ n a, ∀ᵐ x ∂xLaw M, c0 ≤ c n a x)
    (he : ∀ n a, MemLp (fun x => fit n a b x - truth b x) 2 (xLaw M))
    (hr : 0 < r) (hC : 0 ≤ C)
    (hdensity : ∀ᵐ x ∂xLaw M, ∀ u v, truth b x - r ≤ u → u ≤ v →
      v ≤ truth b x + r → (treatedLaw M L i x (Ioc u v)).toReal ≤ C * (v-u))
    (hrates : FiniteNuisanceRates M μ fit truth) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) * ∫ o : Obs X Z,
        w (2*(n+1)) a o.1 *
          (indicator (o.2.1 ∈ L.S i) * o.2.2.1 / c (2*(n+1)) a o.1 *
            ((fit (2*(n+1)) a b o.1 - o.2.2.2) *
                indicator (o.2.2.2 ≤ fit (2*(n+1)) a b o.1) -
              (truth b o.1 - o.2.2.2) * indicator (o.2.2.2 ≤ truth b o.1) -
              (fit (2*(n+1)) a b o.1 - truth b o.1) *
                indicator (o.2.2.2 ≤ truth b o.1))) ∂observationLaw M)
      atTop (fun _ _ => 0) := by
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  let v := fun n a x => w n a x * (selectedTreatmentMass M L i x / c n a x)
  have hv n a := clipped_selected_treatment_weight_bound M L i (w n a) (c n a)
    (hw n a) (hc n a) B c0 hB hc0 (hwb n a) (hclip n a)
  have hs := nuisanceRates_weighted_debiased_quantile_bias_root_n_negligible M μ L i
    truth fit v b (B/c0) r C ht hf (fun n a => (hv n a).1)
    (div_nonneg hB hc0.le) (fun n a => (hv n a).2) he hr hC hdensity hrates
  have hmean n a :
      (∫ o : Obs X Z, w n a o.1 *
        (indicator (o.2.1 ∈ L.S i) * o.2.2.1 / c n a o.1 *
          ((fit n a b o.1 - o.2.2.2) * indicator (o.2.2.2 ≤ fit n a b o.1) -
            (truth b o.1 - o.2.2.2) * indicator (o.2.2.2 ≤ truth b o.1) -
            (fit n a b o.1 - truth b o.1) * indicator (o.2.2.2 ≤ truth b o.1)))
        ∂observationLaw M) =
      ∫ x, v n a x * (∫ y,
        (fit n a b x - y) * indicator (y ≤ fit n a b x) -
          (truth b x - y) * indicator (y ≤ truth b x) -
          (fit n a b x - truth b x) * indicator (y ≤ truth b x)
        ∂treatedLaw M L i x) ∂xLaw M := by
    let g := fun x y => (fit n a b x - y) * indicator (y ≤ fit n a b x) -
      (truth b x - y) * indicator (y ≤ truth b x) -
      (fit n a b x - truth b x) * indicator (y ≤ truth b x)
    have hgm : Measurable (Function.uncurry g) := by dsimp only [g]; fun_prop
    have hei := (he n a).integrable (by norm_num)
    have hi := population_selected_integrand_integrable_of_envelope M L i g hgm
      (fun x => |fit n a b x - truth b x|) (by fun_prop) hei.abs
      (Eventually.of_forall fun x y => debiased_quantile_boundary_norm_le _ _ _)
      (w n a) (c n a) (hw n a) (hc n a) B c0 hB hc0 (hwb n a) (hclip n a)
    exact population_selected_treatment_integral_transfer M L i g hgm
      (w n a) (c n a) (hw n a) (hc n a) hi
  simpa only [hmean] using hs

-- @node: encoded_continuous_observed_quantile_bias_root_n_negligible
/-- Suppose [true nuisances are admissible](hyp:he0), [all fitted nuisances are admissible](hyp:heh),
[boundary densities are bounded](hyp:hd), and [encoded nuisance errors satisfy fourth-root
little-order rates](hyp:hrates). If [the selected positive level is immediately above the boundary
or equals its positive lower level](hyp:hi), [c is positive](hyp:hc), and [the fitted probability
of that level is at least c almost everywhere](hyp:hclip), then [the population debiased quantile
remainder weighted by the fitted regular share, selected-treatment indicator, and inverse fitted
level probability, multiplied by the square root of the evaluation size, converges to zero in probability](goal). -/
lemma encoded_continuous_observed_quantile_bias_root_n_negligible
    {A : Type*} [MeasurableSpace A] (μ : Measure A) (L : LevelData Z X)
    (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hd : BoundaryDensitiesBounded M L)
    (hrates : FiniteNuisanceRates M μ (fun n a => contComponent M L (eh n a))
      (contComponent M L (trueNuisance M L)))
    (b : BoundaryIndex L) (g : RegularIndex L) (i : PositiveIndex L.K)
    (hi : i.val = b.val.1 + 1 ∨ (1 ≤ b.val.1 ∧ i.val = b.val.1))
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).piLev i x) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) * ∫ o : Obs X Z,
        (eh (2*(n+1)) a).gamma g o.1 *
          (indicator (o.2.1 ∈ L.S i.val) * o.2.2.1 / (eh (2*(n+1)) a).piLev i o.1 *
            (((eh (2*(n+1)) a).nu b o.1 - o.2.2.2) *
                indicator (o.2.2.2 ≤ (eh (2*(n+1)) a).nu b o.1) -
              ((trueNuisance M L).nu b o.1 - o.2.2.2) *
                indicator (o.2.2.2 ≤ (trueNuisance M L).nu b o.1) -
              ((eh (2*(n+1)) a).nu b o.1 - (trueNuisance M L).nu b o.1) *
                indicator (o.2.2.2 ≤ (trueNuisance M L).nu b o.1))) ∂observationLaw M)
      atTop (fun _ _ => 0) := by
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  obtain ⟨r, C, hr, hC, hdensity⟩ := dml_quantile_boundary_density_constants M L hd
  obtain ⟨_, _, _, _, _, _, _, _, hrnu, _⟩ :=
    continuous_component_rates_to_oracle_rates M μ L eh (trueNuisance M L) hrates
  have ht : Measurable ((trueNuisance M L).nu b) := by
    first | fun_prop | skip
    rcases he0 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _⟩
    exact hm b
  have ht2 : MemLp ((trueNuisance M L).nu b) 2 (xLaw M) := by
    rcases he0 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hn, _⟩
    apply memLp_of_bounded (hn b)
    fun_prop
  have hcoords n a : Measurable ((eh n a).nu b) ∧
      MemLp ((eh n a).nu b) 2 (xLaw M) ∧ Measurable ((eh n a).gamma g) ∧
      Measurable ((eh n a).piLev i) ∧
      (∀ᵐ x ∂xLaw M, |(eh n a).gamma g x| ≤ 1) := by
    rcases heh n a with ⟨_, _, _, _, _, hpim, _, _, _, _, _, _, hgb, hgm,
      _, _, hnb, hnm, _⟩
    refine ⟨by first | fun_prop | exact hnm b, ?_,
      by first | fun_prop | exact hgm g, by first | fun_prop | exact hpim i, ?_⟩
    · apply memLp_of_bounded (hnb b)
      fun_prop
    · filter_upwards [hgb g] with x hx
      simpa only [abs_of_nonneg hx.1] using hx.2
  exact nuisanceRates_observed_debiased_quantile_bias_root_n_negligible M μ L i.val
    (trueNuisance M L).nu (fun n a => (eh n a).nu)
    (fun n a => (eh n a).gamma g) (fun n a => (eh n a).piLev i)
    b 1 c r C ht (fun n a => (hcoords n a).1)
    (fun n a => (hcoords n a).2.2.1) (fun n a => (hcoords n a).2.2.2.1)
    zero_le_one hc (fun n a => (hcoords n a).2.2.2.2) hclip
    (fun n a => (hcoords n a).2.1.sub ht2) hr hC (hdensity b i.val hi) hrnu

-- The fixed lower endpoint contributes exactly zero. Admissibility supplies
-- endpoint ordering, so the first-band remainder is the negative upper one.
-- @node: encoded_continuous_observed_fixed_lower_band_bias_root_n_negligible
/-- Suppose [true nuisances are admissible](hyp:he0), [fitted nuisances are admissible](hyp:heh),
[boundary densities are bounded](hyp:hd), and [encoded nuisance errors satisfy fourth-root
little-order rates](hyp:hrates). If [the selected positive level is adjacent to the boundary on
its upper side or is its positive lower level](hyp:hi), [c is positive](hyp:hc), and [the fitted
level probability is at least c almost everywhere](hyp:hclip), then [the population debiased
band remainder with the lower endpoint fixed at the outcome minimum, weighted by the fitted
regular share and inverse level probability among selected treated observations, is negligible
in probability after multiplication by the square root of the evaluation size](goal). -/
lemma encoded_continuous_observed_fixed_lower_band_bias_root_n_negligible
    {A : Type*} [MeasurableSpace A] (μ : Measure A) (L : LevelData Z X)
    (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hd : BoundaryDensitiesBounded M L)
    (hrates : FiniteNuisanceRates M μ (fun n a => contComponent M L (eh n a))
      (contComponent M L (trueNuisance M L)))
    (b : BoundaryIndex L) (g : RegularIndex L) (i : PositiveIndex L.K)
    (hi : i.val = b.val.1 + 1 ∨ (1 ≤ b.val.1 ∧ i.val = b.val.1))
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).piLev i x) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) * ∫ o : Obs X Z,
        (eh (2*(n+1)) a).gamma g o.1 *
          (indicator (o.2.1 ∈ L.S i.val) * o.2.2.1 / (eh (2*(n+1)) a).piLev i o.1 *
            continuousDebiasedBandBoundary M.yMin ((trueNuisance M L).nu b o.1)
              M.yMin ((eh (2*(n+1)) a).nu b o.1) o.2.2.2) ∂observationLaw M)
      atTop (fun _ _ => 0) := by
  have hs := encoded_continuous_observed_quantile_bias_root_n_negligible M μ L eh
    he0 heh hd hrates b g i hi c hc hclip
  have hn := (show TendstoInMeasure μ _ atTop (fun _ => (0 : ℝ)) from hs).neg_zero
  have hbound (e : NuisanceCont L) (he : ContAdmissible M L e) :
      ∀ᵐ x ∂xLaw M, M.yMin ≤ e.nu b x := by
    rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hnu, _⟩
    filter_upwards [hnu b] with x hx
    exact hx.1
  change TendstoInMeasure μ _ atTop (fun _ => (0 : ℝ))
  convert hn using 1
  funext n a
  simp only [Pi.neg_apply]
  rw [← mul_neg, ← integral_neg]
  congr 1
  apply integral_congr_ae
  have ho := observationLaw_covariate_ae M _
    ((hbound _ he0).and (hbound _ (heh (2*(n+1)) a)))
  filter_upwards [ho] with o hx
  rw [continuous_debiased_band_boundary_difference _ _ _ _ _ hx.1 hx.2]
  simp only [sub_self, zero_mul, sub_zero, zero_sub, mul_neg]

end Papers.TbsPrteOptimalTransport

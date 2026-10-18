module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLObservedQuantileBias
/-! Root-n negligible observation-level ramp remainders for moving band endpoints.
Integrability follows from clipped weights and the L2 boundary errors. Subtracting
and summing endpoint remainders retains their fitted assignment denominators. -/
public section
set_option linter.style.haveILetI false
set_option linter.style.openClassical false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: fitted_continuous_observed_quantile_remainder_integrable
/-- If [the fitted nuisances are admissible](hyp:he), [the reference nuisances are admissible](hyp:hb),
[the denominator floor is positive](hyp:hc), and [the fitted probability of the selected level
exceeds that floor almost everywhere](hyp:hclip), then [the debiased quantile boundary remainder
between these nuisances, weighted by the fitted regular share and the selected-treatment indicator
divided by fitted level probability, is integrable under the observation law](goal). -/
lemma fitted_continuous_observed_quantile_remainder_integrable
    (L : LevelData Z X) (e b : NuisanceCont L)
    (he : ContAdmissible M L e) (hb : ContAdmissible M L b)
    (a : BoundaryIndex L) (g : RegularIndex L) (i : PositiveIndex L.K)
    (c : ℝ) (hc : 0 < c) (hclip : ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x) :
    Integrable (fun o : Obs X Z => e.gamma g o.1 *
      (indicator (o.2.1 ∈ L.S i.val) * o.2.2.1 / e.piLev i o.1 *
        ((e.nu a o.1 - o.2.2.2) * indicator (o.2.2.2 ≤ e.nu a o.1) -
          (b.nu a o.1 - o.2.2.2) * indicator (o.2.2.2 ≤ b.nu a o.1) -
          (e.nu a o.1 - b.nu a o.1) * indicator (o.2.2.2 ≤ b.nu a o.1))))
      (observationLaw M) := by
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  rcases he with ⟨_, _, _, _, _, hpim, _, _, _, _, _, _, hgb, hgm,
    _, _, hnb, hnm, _⟩
  rcases hb with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hnb0, hnm0, _⟩
  have hfit : MemLp (e.nu a) 2 (xLaw M) := by
    apply memLp_of_bounded (hnb a)
    fun_prop
  have htrue : MemLp (b.nu a) 2 (xLaw M) := by
    apply memLp_of_bounded (hnb0 a)
    fun_prop
  have herr := (hfit.sub htrue).integrable (by norm_num)
  apply population_selected_integrand_integrable_of_envelope M L i.val
    (fun x y => (e.nu a x - y) * indicator (y ≤ e.nu a x) -
      (b.nu a x - y) * indicator (y ≤ b.nu a x) -
      (e.nu a x - b.nu a x) * indicator (y ≤ b.nu a x))
    (by fun_prop) (fun x => |e.nu a x - b.nu a x|) (by fun_prop) herr.abs
    (Eventually.of_forall fun x y => debiased_quantile_boundary_norm_le _ _ _)
    (e.gamma g) (e.piLev i) (by fun_prop) (by fun_prop) 1 c zero_le_one hc
    _ hclip
  filter_upwards [hgb g] with x hx
  simpa only [abs_of_nonneg hx.1] using hx.2

-- Each endpoint retains its own selected cell. This covers plus/minus
-- differences as well as the two endpoints of a single moving band.
-- @node: encoded_continuous_observed_ramp_pair_bias_root_n_negligible
/-- Suppose [true nuisances are admissible](hyp:he0), [fitted nuisances are admissible](hyp:heh),
[boundary densities are bounded](hyp:hd), and [encoded nuisance errors satisfy fourth-root
little-order rates](hyp:hrates). If [the first selected level is immediately above its boundary
or equals its positive lower level](hyp:hi₁), [the second level has the same relation to its own
boundary](hyp:hi₂), [c is positive](hyp:hc), and [all fitted positive-level probabilities are
at least c almost everywhere](hyp:hclip), then [the population difference of the two debiased
quantile remainders, each weighted by the common fitted regular share and its own selected-treatment
indicator and inverse fitted level probability, converges to zero in probability after multiplication
by the square root of the evaluation size](goal). -/
lemma encoded_continuous_observed_ramp_pair_bias_root_n_negligible
    {A : Type*} [MeasurableSpace A] (μ : Measure A) (L : LevelData Z X)
    (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hd : BoundaryDensitiesBounded M L)
    (hrates : FiniteNuisanceRates M μ (fun n a => contComponent M L (eh n a))
      (contComponent M L (trueNuisance M L)))
    (b₁ b₂ : BoundaryIndex L) (g : RegularIndex L) (i₁ i₂ : PositiveIndex L.K)
    (hi₁ : i₁.val = b₁.val.1 + 1 ∨ (1 ≤ b₁.val.1 ∧ i₁.val = b₁.val.1))
    (hi₂ : i₂.val = b₂.val.1 + 1 ∨ (1 ≤ b₂.val.1 ∧ i₂.val = b₂.val.1))
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a i, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).piLev i x) :
    let R := fun n a (b : BoundaryIndex L) (i : PositiveIndex L.K) (o : Obs X Z) =>
      (eh n a).gamma g o.1 *
        (indicator (o.2.1 ∈ L.S i.val) * o.2.2.1 / (eh n a).piLev i o.1 *
          (((eh n a).nu b o.1 - o.2.2.2) * indicator (o.2.2.2 ≤ (eh n a).nu b o.1) -
            ((trueNuisance M L).nu b o.1 - o.2.2.2) *
              indicator (o.2.2.2 ≤ (trueNuisance M L).nu b o.1) -
            ((eh n a).nu b o.1 - (trueNuisance M L).nu b o.1) *
              indicator (o.2.2.2 ≤ (trueNuisance M L).nu b o.1)))
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) * ∫ o,
        R (2*(n+1)) a b₁ i₁ o - R (2*(n+1)) a b₂ i₂ o ∂observationLaw M)
      atTop (fun _ _ => 0) := by
  dsimp only
  have h₁ := encoded_continuous_observed_quantile_bias_root_n_negligible M μ L eh
    he0 heh hd hrates b₁ g i₁ hi₁ c hc (fun n a => hclip n a i₁)
  have h₂ := encoded_continuous_observed_quantile_bias_root_n_negligible M μ L eh
    he0 heh hd hrates b₂ g i₂ hi₂ c hc (fun n a => hclip n a i₂)
  have hs := (show TendstoInMeasure μ _ atTop (fun _ => (0 : ℝ)) from h₁).sub_zero
    (show TendstoInMeasure μ _ atTop (fun _ => (0 : ℝ)) from h₂)
  change TendstoInMeasure μ _ atTop (fun _ => (0 : ℝ))
  convert hs using 1
  funext n a
  rw [integral_sub
    (fitted_continuous_observed_quantile_remainder_integrable M L _ _
      (heh (2*(n+1)) a) he0 b₁ g i₁ c hc (hclip _ a i₁))
    (fitted_continuous_observed_quantile_remainder_integrable M L _ _
      (heh (2*(n+1)) a) he0 b₂ g i₂ c hc (hclip _ a i₂))]
  ring

-- @node: encoded_continuous_observed_quantile_bias_integral_block_root_n_negligible
/-- Suppose [true nuisances are admissible](hyp:he0), [fitted nuisances are admissible](hyp:heh),
[boundary densities are bounded](hyp:hd), and [encoded nuisance errors satisfy fourth-root
little-order rates](hyp:hrates). If [each boundary, regular-share, and positive-level triple in
the finite block pairs the boundary with its upper adjacent level or its positive lower level](hyp:hi),
[c is positive](hyp:hc), and [all fitted positive-level probabilities are at least c almost
everywhere](hyp:hclip), then [the population integral of the sum of the block's debiased quantile
remainders, weighted by their fitted regular shares and selected-treatment indicators divided by
fitted level probabilities, is negligible in probability at the square root of the evaluation size](goal). -/
lemma encoded_continuous_observed_quantile_bias_integral_block_root_n_negligible
    {A : Type*} [MeasurableSpace A] (μ : Measure A) (L : LevelData Z X)
    (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hd : BoundaryDensitiesBounded M L)
    (hrates : FiniteNuisanceRates M μ (fun n a => contComponent M L (eh n a))
      (contComponent M L (trueNuisance M L)))
    (t : Finset (BoundaryIndex L × RegularIndex L × PositiveIndex L.K))
    (hi : ∀ b ∈ t, b.2.2.val = b.1.val.1 + 1 ∨
      (1 ≤ b.1.val.1 ∧ b.2.2.val = b.1.val.1))
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a i, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).piLev i x) :
    let R := fun n a (b : BoundaryIndex L × RegularIndex L × PositiveIndex L.K)
        (o : Obs X Z) =>
      (eh n a).gamma b.2.1 o.1 *
        (indicator (o.2.1 ∈ L.S b.2.2.val) * o.2.2.1 / (eh n a).piLev b.2.2 o.1 *
          (((eh n a).nu b.1 o.1 - o.2.2.2) * indicator (o.2.2.2 ≤ (eh n a).nu b.1 o.1) -
            ((trueNuisance M L).nu b.1 o.1 - o.2.2.2) *
              indicator (o.2.2.2 ≤ (trueNuisance M L).nu b.1 o.1) -
            ((eh n a).nu b.1 o.1 - (trueNuisance M L).nu b.1 o.1) *
              indicator (o.2.2.2 ≤ (trueNuisance M L).nu b.1 o.1)))
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
        ∫ o, ∑ b ∈ t, R (2*(n+1)) a b o ∂observationLaw M)
      atTop (fun _ _ => 0) := by
  intro R
  let F := fun b n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
    ∫ o, R (2*(n+1)) a b o ∂observationLaw M
  have hF b (hb : b ∈ t) : TendstoInMeasure μ (F b) atTop (fun _ => (0 : ℝ)) :=
    encoded_continuous_observed_quantile_bias_root_n_negligible M μ L eh he0 heh hd
      hrates b.1 b.2.1 b.2.2 (hi b hb) c hc (fun n a => hclip n a b.2.2)
  have hs : TendstoInMeasure μ (fun n a => ∑ b ∈ t, F b n a)
      atTop (fun _ => (0 : ℝ)) := by
    induction t using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      intro eps heps
      simpa only [edist_self, not_le.mpr heps, Set.ofPred_false, measure_empty]
        using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (𝓝 0))
    | @insert b t hb ih =>
      have hsingle := hF b (Finset.mem_insert_self b t)
      have hrest := ih (fun d hd => hi d (Finset.mem_insert_of_mem hd))
        (fun d hd => hF d (Finset.mem_insert_of_mem hd))
      simpa only [Finset.sum_insert hb] using hsingle.add_zero hrest
  change TendstoInMeasure μ _ atTop (fun _ => (0 : ℝ))
  convert hs using 1
  funext n a
  rw [integral_finsetSum t (fun b hb =>
    fitted_continuous_observed_quantile_remainder_integrable M L _ _
      (heh (2*(n+1)) a) he0 b.1 b.2.1 b.2.2 c hc (hclip _ a b.2.2))]
  exact Finset.mul_sum t _ _

end Papers.TbsPrteOptimalTransport

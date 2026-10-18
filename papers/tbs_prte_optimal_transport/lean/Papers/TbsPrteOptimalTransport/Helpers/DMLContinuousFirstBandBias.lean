module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLObservedRampBandBias
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousBandBoundaryMean
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationContinuousBounds
/-! Bias cancellation for the restored first continuous band.
The fixed lower endpoint makes ordering automatic from quantile clipping.
The linear CDF residual is centered even with fitted assignment denominators;
only the quadratic upper-endpoint remainder remains. -/
public section
set_option linter.style.haveILetI false
set_option linter.style.openClassical false
set_option linter.style.whitespace false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false
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

-- @node: continuous_restored_first_band_quantile_difference_mean
/-- For [admissible fitted nuisances](hyp:he) and [admissible true nuisances](hyp:he0),
consider [a level within the level count](hyp:hk) with [at least one band
boundary](hyp:hj), and [an assignment index equal to the next level on the upper
side or the current level on the lower side](hyp:hi). With [a positive denominator
floor](hyp:hc) and [fitted assignment probabilities bounded below by that floor
almost everywhere](hyp:hclip), [the fitted-instrument-weighted change in the
restored first-band correction from replacing the true upper quantile by the
fitted upper quantile, while retaining true band regressions and fitted
assignment denominators, is integrable; its mean equals the negative observation
mean of the quantile ramp remainder after subtracting its linear term at the
true quantile, weighted by the fitted instrument weight, assignment-event
indicator, and treatment indicator divided by the fitted assignment probability](goal). -/
lemma continuous_restored_first_band_quantile_difference_mean
    (L : LevelData Z X) (e : NuisanceCont L)
    (he : ContAdmissible M L e) (he0 : ContAdmissible M L (trueNuisance M L))
    (k : ℕ) (hk : k < L.K) (hj : 1 ≤ L.l k)
    (g : RegularIndex L) (plus : Bool) (i : PositiveIndex L.K)
    (hi : i.val = if plus then k+1 else k)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ a, ∀ᵐ x ∂xLaw M, c ≤ e.piLev a x) :
    let h := continuousBandRegressionHybrid e (trueNuisance M L)
    let b := {trueNuisance M L with piLev := e.piLev}
    let a : BoundaryIndex L := ⟨(k,1), hk, le_rfl, hj⟩
    let D := fun o : Obs X Z => e.gamma g o.1 *
      ((IFJ M L h plus k 0 o + M.yMin * IFM M L h plus k 0 o -
          e.nu a o.1 * IFM M L h plus k 1 o) -
        (IFJ M L b plus k 0 o + M.yMin * IFM M L b plus k 0 o -
          (trueNuisance M L).nu a o.1 * IFM M L b plus k 1 o))
    Integrable D (observationLaw M) ∧
    (∫ o, D o ∂observationLaw M) =
      -(∫ o : Obs X Z, e.gamma g o.1 *
        (indicator (o.2.1 ∈ L.S i.val) * o.2.2.1 / e.piLev i o.1 *
          ((e.nu a o.1 - o.2.2.2) * indicator (o.2.2.2 ≤ e.nu a o.1) -
            ((trueNuisance M L).nu a o.1 - o.2.2.2) *
              indicator (o.2.2.2 ≤ (trueNuisance M L).nu a o.1) -
            (e.nu a o.1 - (trueNuisance M L).nu a o.1) *
              indicator (o.2.2.2 ≤ (trueNuisance M L).nu a o.1))) ∂observationLaw M) := by
  intro h b a D
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  have hpi : ∀ a, Measurable (e.piLev a) := by
    first | fun_prop | skip
    rcases he with ⟨_, _, _, _, _, hm, _⟩
    exact hm
  have hgm : Measurable (e.gamma g) := by
    first | fun_prop | skip
    rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hm, _⟩
    exact hm g
  have hnu (f : NuisanceCont L) (hf : ContAdmissible M L f) :
      Measurable (f.nu a) ∧ MemLp (f.nu a) 2 (xLaw M) := by
    rcases hf with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hb, hm, _⟩
    refine ⟨by fun_prop, ?_⟩
    apply memLp_of_bounded (hb a)
    fun_prop
  have hn := hnu e he
  have hn0 := hnu _ he0
  have hb : Measurable (bandBoundary M L k 1) := hn0.1
  have ha : Measurable (bandBoundary M L k 0) := by
    change Measurable (fun _ : X => M.yMin)
    fun_prop
  let v := fun x => e.nu a x - (trueNuisance M L).nu a x
  have hv : Measurable (fun x => e.gamma g x * v x) := by
    dsimp only [v]
    first | fun_prop | exact hgm.mul (hn.1.sub hn0.1)
  have hgv : Integrable (fun x => e.gamma g x * v x) (xLaw M) := by
    have hg := fitted_continuous_regular_gamma_memLp M L e he g.val.1 g.val.2
    have hgeq : regularValue e.gamma g.val.1 g.val.2 = e.gamma g := by
      funext x
      simp only [regularValue, dif_pos g.property]
    rw [hgeq] at hg
    exact hg.integrable_mul (hn.2.sub hn0.2)
  have ia : Integrable (fun o : Obs X Z => (e.gamma g o.1 * (0 : ℝ)) *
      IFM M L {trueNuisance M L with piLev := e.piLev} plus k 0 o)
      (observationLaw M) := by
    simp only [mul_zero, zero_mul]
    exact integrable_zero _ _ _
  have ib := population_IFM_fitted_denominator_integrable M L e.piLev hpi c hc hclip
    plus k 1 hk hj hb _ hv hgv
  let R := fun o : Obs X Z => e.gamma g o.1 *
    (indicator (o.2.1 ∈ L.S i.val) * o.2.2.1 / e.piLev i o.1 *
      ((e.nu a o.1 - o.2.2.2) * indicator (o.2.2.2 ≤ e.nu a o.1) -
        ((trueNuisance M L).nu a o.1 - o.2.2.2) *
          indicator (o.2.2.2 ≤ (trueNuisance M L).nu a o.1) -
        (e.nu a o.1 - (trueNuisance M L).nu a o.1) *
          indicator (o.2.2.2 ≤ (trueNuisance M L).nu a o.1)))
  have iR : Integrable R (observationLaw M) :=
    fitted_continuous_observed_quantile_remainder_integrable M L e _ he he0 a g i c hc (hclip i)
  have hskip : (!plus && k == 0) = false := by
    cases plus
    · have hki : i.val = k := by simpa only [Bool.false_eq_true, if_false] using hi
      have hk0 : k ≠ 0 := by have := hki ▸ i.property.1; omega
      simp [hk0]
    · simp
  have hpos : 1 ≤ (if plus then k+1 else k) ∧ (if plus then k+1 else k) ≤ L.K :=
    hi ▸ i.property
  have hupper x : nuValue M h k 1 x = e.nu a x := by
    simp only [nuValue, Nat.one_ne_zero, if_false,
      dif_pos (show k < L.K ∧ 1 ≤ 1 ∧ 1 ≤ L.l k from ⟨hk, le_rfl, hj⟩)]
    rfl
  have hbase x : bandBoundary M L k 1 x = (trueNuisance M L).nu a x := rfl
  have hlower x : nuValue M h k 0 x = M.yMin := by simp only [nuValue, if_true]
  have hblower x : bandBoundary M L k 0 x = M.yMin := rfl
  have hpval x : positiveValue e.piLev (if plus then k+1 else k) x = e.piLev i x := by
    rw [positiveValue, dif_pos hpos]
    congr 1
    exact Subtype.ext hi.symm
  let Q := fun o : Obs X Z => e.gamma g o.1 *
    ((if !plus && k == 0 then 0 else
      indicator (o.2.1 ∈ L.S (if plus then k+1 else k)) * o.2.2.1 /
        positiveValue e.piLev (if plus then k+1 else k) o.1) *
      continuousDebiasedBandBoundary (bandBoundary M L k 0 o.1)
        (bandBoundary M L k 1 o.1) (nuValue M h k 0 o.1)
        (nuValue M h k 1 o.1) o.2.2.2)
  have hQ : Q =ᵐ[observationLaw M] fun o => -R o := by
    have low (f : NuisanceCont L) (hf : ContAdmissible M L f) :
        ∀ᵐ x ∂xLaw M, M.yMin ≤ f.nu a x := by
      rcases hf with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hb, _⟩
      filter_upwards [hb a] with x hx
      exact hx.1
    filter_upwards [observationLaw_covariate_ae M _ ((low _ he0).and (low e he))] with o ho
    dsimp only [Q, R]
    simp only [hskip, Bool.false_eq_true, if_false, hpval,
      hlower, hblower, hupper, hbase]
    rw [← hi, continuous_debiased_band_boundary_difference _ _ _ _ _ ho.1 ho.2]
    simp only [sub_self, zero_mul, sub_zero, zero_sub, mul_neg]
  have iq : Integrable Q (observationLaw M) := iR.neg.congr hQ.symm
  have hm := population_continuous_band_quantile_difference_mean M L h e.piLev hpi
    rfl rfl rfl rfl rfl plus k 0 hk (by omega) ha hb (e.gamma g) (fun _ => 0) v
    (by fun_prop) hv (fun x => by simp [nuValue, bandBoundary])
    (fun x => by rw [hupper, hbase]) ia ib iq
  have hD : (fun o : Obs X Z => e.gamma g o.1 *
      ((IFJ M L h plus k 0 o + nuValue M h k 0 o.1 * IFM M L h plus k 0 o -
          nuValue M h k 1 o.1 * IFM M L h plus k 1 o) -
        (IFJ M L b plus k 0 o + bandBoundary M L k 0 o.1 * IFM M L b plus k 0 o -
          bandBoundary M L k 1 o.1 * IFM M L b plus k 1 o))) = D := by
    funext o
    simp only [D, hupper, hbase, hlower, hblower]
  rw [hD] at hm
  refine ⟨hm.1, hm.2.trans ?_⟩
  exact (integral_congr_ae hQ).trans (integral_neg R)

-- @node: encoded_continuous_restored_first_band_quantile_difference_root_n_negligible
/-- Assume [admissible true nuisances](hyp:he0), [admissible fitted nuisances at
every sample size](hyp:heh), [bounded boundary densities](hyp:hd), and [the
componentwise rates for the encoded nuisance functions](hyp:hr). At [a level
within the level count](hyp:hk) with [at least one band boundary](hyp:hj), for
[an assignment index equal to the next level on the upper side or the current
level on the lower side](hyp:hi), [a positive denominator floor](hyp:hc) and
[all fitted assignment probabilities bounded below by that floor almost
everywhere](hyp:hclip) imply that [the population mean change in the
fitted-instrument-weighted restored first-band correction from replacing the
true upper quantile by the fitted quantile, retaining true band regressions and
fitted assignment denominators, converges in probability to zero after
multiplication by the square root of the half-sample size, with fits taken at
twice that size](goal). -/
lemma encoded_continuous_restored_first_band_quantile_difference_root_n_negligible
    {A : Type*} [MeasurableSpace A] (μ : Measure A) (L : LevelData Z X)
    (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hd : BoundaryDensitiesBounded M L)
    (hr : FiniteNuisanceRates M μ (fun n a => contComponent M L (eh n a))
      (contComponent M L (trueNuisance M L)))
    (k : ℕ) (hk : k < L.K) (hj : 1 ≤ L.l k)
    (g : RegularIndex L) (plus : Bool) (i : PositiveIndex L.K)
    (hi : i.val = if plus then k+1 else k)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a i, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).piLev i x) :
    let h := fun n a => continuousBandRegressionHybrid (eh n a) (trueNuisance M L)
    let b := fun n a => {trueNuisance M L with piLev := (eh n a).piLev}
    let a : BoundaryIndex L := ⟨(k,1), hk, le_rfl, hj⟩
    let D := fun n t (o : Obs X Z) => (eh n t).gamma g o.1 *
      ((IFJ M L (h n t) plus k 0 o + M.yMin * IFM M L (h n t) plus k 0 o -
          (eh n t).nu a o.1 * IFM M L (h n t) plus k 1 o) -
        (IFJ M L (b n t) plus k 0 o + M.yMin * IFM M L (b n t) plus k 0 o -
          (trueNuisance M L).nu a o.1 * IFM M L (b n t) plus k 1 o))
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => Real.sqrt ((n+1 : ℕ) : ℝ) *
        ∫ o, D (2*(n+1)) t o ∂observationLaw M) atTop (fun _ _ => 0) := by
  intro h b a D
  have hid : i.val = k+1 ∨ (1 ≤ k ∧ i.val = k) := by
    cases plus
    · have hik : i.val = k := by simpa only [Bool.false_eq_true, if_false] using hi
      exact Or.inr ⟨hik ▸ i.property.1, hik⟩
    · exact Or.inl (by simpa only [if_true] using hi)
  have hs := encoded_continuous_observed_quantile_bias_root_n_negligible M μ L eh
    he0 heh hd hr a g i hid c hc (fun n t => hclip n t i)
  have hn := (show TendstoInMeasure μ _ atTop (fun _ => (0 : ℝ)) from hs).neg_zero
  change TendstoInMeasure μ _ atTop (fun _ => (0 : ℝ))
  convert hn using 1
  funext n t
  have hm := (continuous_restored_first_band_quantile_difference_mean M L
    (eh (2*(n+1)) t) (heh _ t) he0 k hk hj g plus i hi c hc (hclip _ t)).2
  change Real.sqrt ((n+1 : ℕ) : ℝ) * _ = _
  rw [hm]
  simp only [Pi.neg_apply, mul_neg]
  rfl

-- @node: encoded_continuous_restored_first_band_regression_difference_root_n_negligible
/-- Under [admissible true nuisances](hyp:he0), [admissible fitted nuisances](hyp:heh),
[bounded boundary densities](hyp:hd), [the componentwise encoded nuisance
rates](hyp:hr), [a level within the level count](hyp:hk), [at least one band
boundary at that level](hyp:hj), [a positive denominator floor](hyp:hc), and
[all fitted assignment probabilities bounded below by that floor almost
everywhere](hyp:hclip), [the population mean difference between the first-band
regression corrections using fitted quantiles with true band regressions and
using true nuisances with fitted assignment denominators, multiplied by the
fitted instrument weight and the square root of the half-sample size, converges
in probability to zero when fits are taken at twice that size](goal). -/
lemma encoded_continuous_restored_first_band_regression_difference_root_n_negligible
    {A : Type*} [MeasurableSpace A] (μ : Measure A) (L : LevelData Z X)
    (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hd : BoundaryDensitiesBounded M L)
    (hr : FiniteNuisanceRates M μ (fun n a => contComponent M L (eh n a))
      (contComponent M L (trueNuisance M L)))
    (k : ℕ) (hk : k < L.K) (hj : 1 ≤ L.l k) (g : RegularIndex L)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a i, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).piLev i x) :
    let h := fun n a => continuousBandRegressionHybrid (eh n a) (trueNuisance M L)
    let b := fun n a => {trueNuisance M L with piLev := (eh n a).piLev}
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => Real.sqrt ((n+1 : ℕ) : ℝ) * ∫ o : Obs X Z,
        (eh (2*(n+1)) t).gamma g o.1 *
          (continuousBandRegressionCorrection M L (h (2*(n+1)) t) k 0 o -
            continuousBandRegressionCorrection M L (b (2*(n+1)) t) k 0 o)
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  intro h b
  let a : BoundaryIndex L := ⟨(k,1), hk, le_rfl, hj⟩
  let D := fun plus n t (o : Obs X Z) => (eh n t).gamma g o.1 *
    ((IFJ M L (h n t) plus k 0 o + M.yMin * IFM M L (h n t) plus k 0 o -
        (eh n t).nu a o.1 * IFM M L (h n t) plus k 1 o) -
      (IFJ M L (b n t) plus k 0 o + M.yMin * IFM M L (b n t) plus k 0 o -
        (trueNuisance M L).nu a o.1 * IFM M L (b n t) plus k 1 o))
  have hp : TendstoInMeasure μ (fun n t => Real.sqrt ((n+1 : ℕ) : ℝ) *
      ∫ o, D true (2*(n+1)) t o ∂observationLaw M) atTop (fun _ => (0 : ℝ)) :=
    encoded_continuous_restored_first_band_quantile_difference_root_n_negligible
      M μ L eh he0 heh hd hr k hk hj g true ⟨k+1, by omega⟩ rfl c hc hclip
  have hip n t : Integrable (D true n t) (observationLaw M) :=
    (continuous_restored_first_band_quantile_difference_mean M L (eh n t)
      (heh n t) he0 k hk hj g true ⟨k+1, by omega⟩ rfl c hc (hclip n t)).1
  have hm : TendstoInMeasure μ (fun n t => Real.sqrt ((n+1 : ℕ) : ℝ) *
      ∫ o, D false (2*(n+1)) t o ∂observationLaw M) atTop (fun _ => (0 : ℝ)) := by
    by_cases hk0 : k = 0
    · subst k
      simp only [D, IFJ, IFM, Bool.not_false, beq_self_eq_true, Bool.and_self,
        true_and, if_true, mul_zero, add_zero, sub_zero, sub_self, integral_zero]
      intro eps heps
      simpa only [edist_self, not_le.mpr heps, Set.ofPred_false, measure_empty]
        using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (𝓝 0))
    · exact encoded_continuous_restored_first_band_quantile_difference_root_n_negligible
        M μ L eh he0 heh hd hr k hk hj g false ⟨k, by omega⟩
        (by simp only [Bool.false_eq_true, if_false]) c hc hclip
  have him n t : Integrable (D false n t) (observationLaw M) := by
    by_cases hk0 : k = 0
    · subst k
      simp only [D, IFJ, IFM, Bool.not_false, beq_self_eq_true, Bool.and_self,
        true_and, if_true, mul_zero, add_zero, sub_zero, sub_self]
      exact integrable_zero _ _ _
    · exact (continuous_restored_first_band_quantile_difference_mean M L (eh n t)
        (heh n t) he0 k hk hj g false ⟨k, by omega⟩
        (by simp only [Bool.false_eq_true, if_false]) c hc (hclip n t)).1
  have hs := hp.sub_zero hm
  change TendstoInMeasure μ _ atTop (fun _ => (0 : ℝ))
  convert hs using 1
  funext n t
  rw [← mul_sub, ← integral_sub (hip _ t) (him _ t)]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with o
  have hn : nuValue M (h (2*(n+1)) t) k 1 o.1 = (eh (2*(n+1)) t).nu a o.1 := by
    simp only [nuValue, Nat.one_ne_zero, if_false,
      dif_pos (show k < L.K ∧ 1 ≤ 1 ∧ 1 ≤ L.l k from ⟨hk, le_rfl, hj⟩)]
    rfl
  have hb : nuValue M (b (2*(n+1)) t) k 1 o.1 = (trueNuisance M L).nu a o.1 := by
    simp only [nuValue, Nat.one_ne_zero, if_false,
      dif_pos (show k < L.K ∧ 1 ≤ 1 ∧ 1 ≤ L.l k from ⟨hk, le_rfl, hj⟩)]
    rfl
  simp only [continuousBandRegressionCorrection, Nat.zero_add, hn, hb]
  simp only [D, nuValue, if_true]
  ring

-- @node: fitted_continuous_weighted_band_regression_correction_integrable
/-- For [admissible fitted nuisances](hyp:he), [a positive denominator
floor](hyp:hc), [assignment probabilities bounded below by that floor almost
everywhere](hyp:hclip), and [a level within the level count](hyp:hk), [the band
regression correction at the specified band index, multiplied by the selected
fitted instrument weight, is integrable under the observation distribution](goal). -/
lemma fitted_continuous_weighted_band_regression_correction_integrable
    (L : LevelData Z X) (e : NuisanceCont L) (he : ContAdmissible M L e)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ i, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (g : RegularIndex L) (k j : ℕ) (hk : k < L.K) :
    Integrable (fun o : Obs X Z => e.gamma g o.1 *
      continuousBandRegressionCorrection M L e k j o) (observationLaw M) := by
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  have hp := fitted_continuous_gamma_IFJ_memLp M L e he c hc hclip g true k j hk
  have hm := fitted_continuous_gamma_IFJ_memLp M L e he c hc hclip g false k j hk
  have ha := fitted_continuous_quantile_gamma_IFM_contrast_memLp M L e he c hc hclip g k j hk
  have hb := fitted_continuous_quantile_gamma_IFM_contrast_memLp M L e he c hc hclip g k (j+1) hk
  have hs := (((hp.sub hm).add ha).sub hb).integrable (by norm_num)
  convert hs using 1
  funext o
  simp only [continuousBandRegressionCorrection, Pi.add_apply, Pi.sub_apply]
  ring

-- @node: continuous_reference_first_band_regression_correction_zero
/-- Under [the model's structural assumptions](hyp:hStruct), [known outcome
endpoints](hyp:hend), [admissible fitted nuisances](hyp:he), and [admissible true
nuisances](hyp:he0), consider [a level within the level count](hyp:hk) with [at
least one band boundary](hyp:hj). If [the denominator floor is positive](hyp:hc)
and [fitted assignment probabilities are bounded below by it almost
everywhere](hyp:hclip), then [the first-band regression correction formed from
true nuisances with fitted assignment denominators, multiplied by the selected
fitted instrument weight, is integrable and has population mean zero](goal). -/
lemma continuous_reference_first_band_regression_correction_zero
    (hStruct : StructuralAssumptions M) (hend : OutcomeEndpointsKnown M)
    (L : LevelData Z X) (e : NuisanceCont L)
    (he : ContAdmissible M L e) (he0 : ContAdmissible M L (trueNuisance M L))
    (k : ℕ) (hk : k < L.K) (hj : 1 ≤ L.l k) (g : RegularIndex L)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ i, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x) :
    let b := {trueNuisance M L with piLev := e.piLev}
    Integrable (fun o : Obs X Z => e.gamma g o.1 *
      continuousBandRegressionCorrection M L b k 0 o) (observationLaw M) ∧
    (∫ o : Obs X Z, e.gamma g o.1 *
      continuousBandRegressionCorrection M L b k 0 o ∂observationLaw M) = 0 := by
  dsimp only
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  have hpim : ∀ i, Measurable (e.piLev i) := by
    first | fun_prop | skip
    rcases he with ⟨_, _, _, _, _, hm, _⟩
    exact hm
  have hgm : Measurable (e.gamma g) := by
    first | fun_prop | skip
    rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hm, _⟩
    exact hm g
  have hg : MemLp (e.gamma g) 2 (xLaw M) := by
    have hs := fitted_continuous_regular_gamma_memLp M L e he g.val.1 g.val.2
    have hgeq : regularValue e.gamma g.val.1 g.val.2 = e.gamma g := by
      funext x
      simp only [regularValue, dif_pos g.property]
    rw [hgeq] at hs
    exact hs
  have ha : Measurable (bandBoundary M L k 0) := by
    change Measurable (fun _ : X => M.yMin)
    fun_prop
  let a : BoundaryIndex L := ⟨(k,1), hk, le_rfl, hj⟩
  have hb : Measurable (bandBoundary M L k 1) := by
    first | fun_prop | skip
    rcases he0 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _⟩
    exact hm a
  have hnb : MemLp (bandBoundary M L k 1) 2 (xLaw M) := by
    rcases he0 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hb0, hm, _⟩
    change MemLp ((trueNuisance M L).nu a) 2 (xLaw M)
    apply memLp_of_bounded (hb0 a)
    fun_prop
  apply population_continuous_band_regression_correction_zero M L e.piLev hpim
    k 0 hk (by omega) ha hb (e.gamma g) hgm
  · intro plus
    exact population_IFJ_fitted_denominator_integrable M hStruct hend L e.piLev hpim
      c hc hclip plus k 0 hk (by omega) ha hb _ hgm (hg.integrable (by norm_num))
  · intro plus
    apply population_IFM_fitted_denominator_integrable M L e.piLev hpim
      c hc hclip plus k 0 hk (by omega) ha (fun x => e.gamma g x * bandBoundary M L k 0 x)
        (by fun_prop)
    change Integrable (fun x => e.gamma g x * M.yMin) (xLaw M)
    exact (hg.integrable (by norm_num)).mul_const _
  · intro plus
    exact population_IFM_fitted_denominator_integrable M L e.piLev hpim
      c hc hclip plus k 1 hk hj hb _ (by fun_prop) (hg.integrable_mul hnb)

-- @node: encoded_continuous_restored_first_band_regression_correction_root_n_negligible
/-- Under [the model's structural assumptions](hyp:hStruct), [known outcome
endpoints](hyp:hend), [admissible true nuisances](hyp:he0), [admissible fitted
nuisances](hyp:heh), [bounded boundary densities](hyp:hd), [the componentwise
encoded nuisance rates](hyp:hr), [a level within the level count](hyp:hk), [at
least one band boundary at that level](hyp:hj), [a positive denominator
floor](hyp:hc), and [all fitted assignment probabilities bounded below by that
floor almost everywhere](hyp:hclip), [the population mean of the restored
first-band regression correction using true band regressions and otherwise
fitted nuisances, multiplied by the fitted instrument weight and the square
root of the half-sample size, converges in probability to zero when fits are
taken at twice that size](goal). -/
lemma encoded_continuous_restored_first_band_regression_correction_root_n_negligible
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (hStruct : StructuralAssumptions M) (hend : OutcomeEndpointsKnown M)
    (L : LevelData Z X) (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hd : BoundaryDensitiesBounded M L)
    (hr : FiniteNuisanceRates M μ (fun n a => contComponent M L (eh n a))
      (contComponent M L (trueNuisance M L)))
    (k : ℕ) (hk : k < L.K) (hj : 1 ≤ L.l k) (g : RegularIndex L)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a i, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).piLev i x) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => Real.sqrt ((n+1 : ℕ) : ℝ) * ∫ o : Obs X Z,
        (eh (2*(n+1)) t).gamma g o.1 *
          continuousBandRegressionCorrection M L
            (continuousBandRegressionHybrid (eh (2*(n+1)) t) (trueNuisance M L)) k 0 o
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  have hs := encoded_continuous_restored_first_band_regression_difference_root_n_negligible
    M μ L eh he0 heh hd hr k hk hj g c hc hclip
  convert hs using 1
  funext n t
  let e := eh (2*(n+1)) t
  let h := continuousBandRegressionHybrid e (trueNuisance M L)
  have ih := fitted_continuous_weighted_band_regression_correction_integrable M L h
    (continuous_band_regression_hybrid_admissible M L e _ (heh _ t) he0)
    c hc (hclip _ t) g k 0 hk
  change Integrable (fun o : Obs X Z => e.gamma g o.1 *
    continuousBandRegressionCorrection M L h k 0 o) (observationLaw M) at ih
  obtain ⟨ib, zb⟩ := continuous_reference_first_band_regression_correction_zero M
    hStruct hend L e (heh _ t) he0 k hk hj g c hc (hclip _ t)
  congr 1
  simp only [mul_sub]
  rw [integral_sub ih ib, zb, sub_zero]

end Papers.TbsPrteOptimalTransport

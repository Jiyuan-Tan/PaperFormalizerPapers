module
public import Papers.TbsPrteOptimalTransport.Helpers.Canonical
public import Papers.TbsPrteOptimalTransport.Helpers.ScoresBinary
public import Papers.TbsPrteOptimalTransport.Helpers.LIVPart
/-! Pooled treated moments at finite baseline propensity levels. -/
@[expose] public section
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set
open scoped Classical ENNReal
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z]
variable (M : LatentIVModel Ω X Z)

-- @node: pooledThresholdResponse
/-- For [the latent instrumental-variable model](hyp:M), [a covariate value x](hyp:x),
and [an instrument together with resistance and both potential outcomes](hyp:zv),
the [pooled threshold response](goal) consists of the treated potential outcome when
resistance is at most the propensity and the untreated outcome otherwise, the
corresponding treatment indicator, and the original instrument. -/
noncomputable def pooledThresholdResponse (x : X) (zv : Z × (ℝ × ℝ × ℝ)) : ℝ × ℝ × Z :=
  (if zv.2.1 ≤ M.prop zv.1 x then zv.2.2.2 else zv.2.2.1,
    if zv.2.1 ≤ M.prop zv.1 x then 1 else 0, zv.1)

-- @node: measurable_pooledThresholdResponse
/-- Under [the model's threshold-crossing assumptions](hyp:h), [the pooled threshold
response is measurable jointly in covariates, the instrument, resistance, and
potential outcomes](goal). -/
@[fun_prop] lemma measurable_pooledThresholdResponse (h : ThresholdCrossing M) :
    Measurable (fun a : X × (Z × (ℝ × ℝ × ℝ)) =>
      pooledThresholdResponse M a.1 a.2) := by
  unfold pooledThresholdResponse
  have hp := h.2.1
  have ht : MeasurableSet {a : X × (Z × (ℝ × ℝ × ℝ)) |
      a.2.2.1 ≤ M.prop a.2.1 a.1} := measurableSet_le measurable_snd.snd.fst
    (hp.comp (measurable_snd.fst.prodMk measurable_fst))
  exact (measurable_snd.snd.snd.snd.ite ht measurable_snd.snd.snd.fst).prodMk
    ((measurable_const.ite ht measurable_const).prodMk measurable_snd.fst)

-- @node: pooled_observed_conditional_law
/-- Under [the model's structural assumptions](hyp:h), [for almost every covariate
value the conditional distribution of outcome, treatment, and instrument is obtained
by applying the pooled threshold response to the product of the conditional instrument
law and the conditional law of resistance and potential outcomes](goal). -/
lemma pooled_observed_conditional_law (h : StructuralAssumptions M) :
    ∀ᵐ x ∂xLaw M,
      condDistrib (fun s => (M.Y s, M.W s, M.Zv s)) M.Xv M.law.toMeasure x =
        ((M.instKernel x).prod (condDistrib
          (fun s => (M.U s, M.Y0 s, M.Y1 s)) M.Xv M.law.toMeasure x)).map
          (pooledThresholdResponse M x) := by
  have hm := measurable_pooledThresholdResponse M h.2.2.2.1
  have hV : Measurable (fun s => (M.Zv s, (M.U s, M.Y0 s, M.Y1 s))) := by
    exact M.measZ.prodMk (M.measU.prodMk (M.measY0.prodMk M.measY1))
  have hmap := condDistrib_map_of_funext M.law.toMeasure M.measX hV hm
  have he : (fun s => (M.Y s, M.W s, M.Zv s)) =ᵐ[M.law.toMeasure]
      (fun s => pooledThresholdResponse M (M.Xv s)
        (M.Zv s, (M.U s, M.Y0 s, M.Y1 s))) := by
    filter_upwards [h.2.1, h.2.2.2.1.1] with s hs ht
    unfold pooledThresholdResponse
    rw [hs, ht]
    split_ifs <;> simp
  rw [← condDistrib_congr_left he] at hmap
  filter_upwards [hmap, h.2.2.1] with x hx hex
  exact hx.trans (congrArg (fun ν => ν.map (pooledThresholdResponse M x)) hex)

-- @node: pooled_response_restrict
/-- Under [threshold crossing](hyp:h), for [a measurable instrument set S](hyp:hS),
[restricting the pooled response distribution to instruments in S gives the same
measure as first restricting the instrument law to S and then applying the threshold
response](goal), at any fixed covariate value for the given latent measure. -/
lemma pooled_response_restrict (h : ThresholdCrossing M) (x : X) (S : Set Z)
    (hS : MeasurableSet S) (ν : Measure (ℝ × ℝ × ℝ)) [SFinite ν] :
    (((M.instKernel x).prod ν).map (pooledThresholdResponse M x)).restrict
        {a | a.2.2 ∈ S} =
      (((M.instKernel x).restrict S).prod ν).map (pooledThresholdResponse M x) := by
  haveI := M.instKernel_markov
  have hm : Measurable (pooledThresholdResponse M x) :=
    (measurable_pooledThresholdResponse M h).comp
      (measurable_const.prodMk measurable_id)
  rw [Measure.restrict_map hm (s := {a : ℝ × ℝ × Z | a.2.2 ∈ S})
    (hS.preimage measurable_snd.snd),
    Measure.restrict_prod_eq_prod_univ]
  congr 2
  ext a
  simp [pooledThresholdResponse]

-- @node: pooled_response_treated_integral
/-- Under [threshold crossing](hyp:h), if [the instrument set S is measurable](hyp:hS)
and [every instrument in S has propensity p at the chosen covariate value](hyp:hp),
then [the outcome-times-treatment integral over pooled responses selected by S equals
the conditional probability of S times the latent treated-outcome integral below
resistance threshold p](goal). -/
lemma pooled_response_treated_integral (h : ThresholdCrossing M) (x : X)
    (S : Set Z) (hS : MeasurableSet S) (p : ℝ)
    (hp : ∀ z ∈ S, M.prop z x = p) (ν : Measure (ℝ × ℝ × ℝ)) [SFinite ν] :
    (∫ a, a.1 * a.2.1 ∂
      ((((M.instKernel x).prod ν).map (pooledThresholdResponse M x)).restrict
        {a | a.2.2 ∈ S})) =
      (M.instKernel x S).toReal * ∫ v, (if v.1 ≤ p then v.2.2 else 0) ∂ν := by
  haveI := M.instKernel_markov
  haveI := M.instKernel_markov
  have hm : Measurable (pooledThresholdResponse M x) :=
    (measurable_pooledThresholdResponse M h).comp
      (measurable_const.prodMk measurable_id)
  rw [pooled_response_restrict M h x S hS ν, integral_map hm.aemeasurable
    (by fun_prop : AEStronglyMeasurable (fun a : ℝ × ℝ × Z => a.1 * a.2.1) _)]
  have he : (fun a : Z × (ℝ × ℝ × ℝ) =>
        (pooledThresholdResponse M x a).1 * (pooledThresholdResponse M x a).2.1) =ᵐ[
        ((M.instKernel x).restrict S).prod ν]
      (fun a => (1 : ℝ) * (if a.2.1 ≤ p then a.2.2.2 else 0)) := by
    have hs : ∀ᵐ a ∂((M.instKernel x).restrict S).prod ν, a.1 ∈ S :=
      (Measure.ae_prod_iff_ae_ae (hS.preimage measurable_fst)).2 (by
        filter_upwards [ae_restrict_mem hS] with z hz
        exact Filter.Eventually.of_forall fun v => hz)
    filter_upwards [hs] with a ha
    unfold pooledThresholdResponse
    rw [hp a.1 ha]
    split_ifs <;> simp
  rw [integral_congr_ae he, integral_prod_mul (fun _ : Z => (1 : ℝ))
    (fun v : ℝ × ℝ × ℝ => if v.1 ≤ p then v.2.2 else 0), integral_const]
  simp [Measure.restrict_apply_univ, measureReal_def]

-- @node: latent_threshold_treated_submeasure
/-- Under [the model's structural assumptions](hyp:h), [for almost every covariate
value and every threshold in the unit interval, restricting the conditional latent
law to resistance below that threshold and retaining the treated potential outcome
gives the canonical treated-outcome submeasure](goal). -/
lemma latent_threshold_treated_submeasure (h : StructuralAssumptions M) :
    ∀ᵐ x ∂xLaw M, ∀ p ∈ Icc (0 : ℝ) 1,
      ((condDistrib (fun s => (M.U s, M.Y0 s, M.Y1 s)) M.Xv M.law.toMeasure x).restrict
        {v | v.1 ≤ p}).map (fun v => v.2.2) = canonSubmeasure M true x p := by
  let V := fun s => (M.U s, M.Y0 s, M.Y1 s)
  let proj := fun v : ℝ × ℝ × ℝ => (v.1, v.2.2)
  have hV : Measurable V := M.measU.prodMk (M.measY0.prodMk M.measY1)
  have hproj : Measurable proj := by fun_prop
  have hc := condDistrib_comp (μ := M.law.toMeasure) (mβ := inferInstance)
    M.Xv hV.aemeasurable hproj
  have hl := latent_conditional_uniform_disintegration M h.2.2.2.2.1 true
  filter_upwards [hc, hl] with x hx hlx
  intro p hp
  haveI := outcomeKernel_isMarkov (latentMarginal M true)
  let K := outcomeKernel (latentMarginal M true)
  have he : (condDistrib V M.Xv M.law.toMeasure x).map proj =
      ((Kernel.const X Causalean.Stat.unifOI) ⊗ₖ
        (K.comap (Prod.swap : X × ℝ → ℝ × X) measurable_swap)) x := by
    rw [Kernel.map_apply _ hproj] at hx
    exact hx.symm.trans hlx
  have hr : ((condDistrib V M.Xv M.law.toMeasure x).restrict {v | v.1 ≤ p}).map
      (fun v => v.2.2) =
      (((condDistrib V M.Xv M.law.toMeasure x).map proj).restrict
        {uy | uy.1 ≤ p}).map Prod.snd := by
    rw [Measure.restrict_map hproj (measurableSet_le measurable_fst measurable_const),
      Measure.map_map measurable_snd hproj]
    rfl
  rw [hr, he]
  ext B hB
  rw [Measure.map_apply measurable_snd hB,
    Measure.restrict_apply (hB.preimage measurable_snd),
    Kernel.compProd_apply ((hB.preimage measurable_snd).inter
      (measurableSet_le measurable_fst measurable_const))]
  change (∫⁻ u, K (u, x) {y | y ∈ B ∧ u ≤ p} ∂Causalean.Stat.unifOI) = _
  have hrp : Causalean.Stat.unifOI.restrict (Ioc 0 p) = volume.restrict (Ioc 0 p) := by
    rw [Causalean.Stat.unifOI, Measure.restrict_restrict measurableSet_Ioc]
    apply Measure.restrict_congr_set
    filter_upwards [volume.ae_ne (1 : ℝ)] with u hu
    apply propext
    change ((0 < u ∧ u ≤ p) ∧ (0 < u ∧ u < 1)) ↔ (0 < u ∧ u ≤ p)
    exact ⟨fun h => h.1, fun h => ⟨h, h.1, lt_of_le_of_ne (h.2.trans hp.2) hu⟩⟩
  calc
    _ = ∫⁻ u, (Ioc 0 p).indicator (fun u => K (u, x) B) u ∂Causalean.Stat.unifOI := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
      by_cases ht : u ≤ p
      · simp [ht, hu.1]
      · simp [ht]
    _ = ∫⁻ u, K (u, x) B ∂volume.restrict (Ioc 0 p) := by
      rw [lintegral_indicator measurableSet_Ioc, hrp]
    _ = _ := by
      rw [canonSubmeasure, Measure.bind_apply hB (by fun_prop)]
      rfl

-- @node: latent_threshold_treated_mean
/-- Under [the model's structural assumptions](hyp:h), [for almost every covariate
value and every threshold in the unit interval, the conditional integral of the
treated potential outcome below that resistance threshold equals the canonical
treated regression at that threshold](goal). -/
lemma latent_threshold_treated_mean (h : StructuralAssumptions M) :
    ∀ᵐ x ∂xLaw M, ∀ p ∈ Icc (0 : ℝ) 1,
      (∫ v, (if v.1 ≤ p then v.2.2 else 0) ∂condDistrib
        (fun s => (M.U s, M.Y0 s, M.Y1 s)) M.Xv M.law.toMeasure x) = g1Canon M p x := by
  filter_upwards [latent_threshold_treated_submeasure M h] with x hx
  intro p hp
  rw [g1Canon, ← hx p hp, integral_map (by fun_prop) (by fun_prop),
    ← integral_indicator (measurableSet_le measurable_fst measurable_const)]
  rfl

-- @node: pooled_response_selected_mass
/-- Under [threshold crossing](hyp:h), for [a measurable instrument set S](hyp:hS)
and a latent probability measure, [the total mass of pooled responses whose retained
instrument lies in S equals the conditional instrument probability of S](goal). -/
lemma pooled_response_selected_mass (h : ThresholdCrossing M) (x : X)
    (S : Set Z) (hS : MeasurableSet S) (ν : Measure (ℝ × ℝ × ℝ))
    [IsProbabilityMeasure ν] :
    ((((M.instKernel x).prod ν).map (pooledThresholdResponse M x)).restrict
      {a | a.2.2 ∈ S}) univ = M.instKernel x S := by
  haveI := M.instKernel_markov
  have hm : Measurable (pooledThresholdResponse M x) :=
    (measurable_pooledThresholdResponse M h).comp
      (measurable_const.prodMk measurable_id)
  rw [pooled_response_restrict M h x S hS ν, Measure.map_apply hm MeasurableSet.univ,
    preimage_univ, ← univ_prod_univ, Measure.prod_prod, Measure.restrict_apply_univ,
    measure_univ, mul_one]

variable [Fintype Z] [DecidableEq Z]

-- @node: positive_baseline_class_nonempty
/-- If [the baseline and policy levels have the specified invariant ordering](hyp:hL),
[the baseline index k is at least one](hyp:hk0), and [k is at most the number of
positive baseline levels](hyp:hk), then [the baseline instrument class at k is nonempty](goal). -/
lemma positive_baseline_class_nonempty (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (x : X) (k : ℕ)
    (hk0 : 1 ≤ k) (hk : k ≤ L.K) : (L.S k).Nonempty := by
  have hlen := hL.2.2.2.1 x
  have hidx : k - 1 < (finiteLevels (fun z => M.prop z x)).length := by omega
  have hkle : k ≤ (finiteLevels (fun z => M.prop z x)).length := by omega
  have hmem : pLevel (finiteLevels (fun z => M.prop z x)) k ∈
      finiteLevels (fun z => M.prop z x) := by
    simp only [pLevel, if_neg (show k ≠ 0 by omega), if_pos hkle, List.getD,
      List.getElem?_eq_getElem hidx, Option.getD_some]
    exact List.getElem_mem _
  obtain ⟨z, hz⟩ := (finiteLevels_mem (fun z => M.prop z x) (inferInstance : Finite Z) hmem).1
  refine ⟨z, (hL.2.2.2.2.2.1 x k z hk).2 ?_⟩
  rw [hL.1 x k (by omega)]
  exact hz

-- @node: treatedSuccess_eq_canonical_regression
/-- Under [the model's structural assumptions](hyp:h), [a finite discrete instrument
reduction](hyp:hFinite), and [the specified invariant ordering of baseline and policy
levels](hyp:hL), [for almost every covariate value, treated success in every baseline
class up to the last level equals the canonical treated regression evaluated at that
class's baseline propensity](goal). -/
lemma treatedSuccess_eq_canonical_regression (h : StructuralAssumptions M)
    (hFinite : InstrumentFiniteReduction Z) (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) :
    ∀ᵐ x ∂xLaw M, ∀ k ≤ L.K, treatedSuccess M L k x = g1Canon M (L.pLev k x) x := by
  letI : DiscreteTopology Z := hFinite.2
  filter_upwards [pooled_observed_conditional_law M h,
    latent_threshold_treated_mean M h,
    instrument_singleton_pos M h.2.2.2.2.2.1 hFinite] with x hx hmean hpos
  intro k hk
  by_cases hk0 : k = 0
  · subst k
    have hp0 : L.pLev 0 x = 0 := by rw [hL.1 x 0 (by omega)]; simp [pLevel]
    simp [treatedSuccess, hp0, g1Canon, canonSubmeasure, selRegion]
  · have hS : MeasurableSet (L.S k : Set Z) := (L.S k).finite_toSet.measurableSet
    have hp : ∀ z ∈ (L.S k : Set Z), M.prop z x = L.pLev k x :=
      fun z hz => (hL.2.2.2.2.2.1 x k z hk).1 hz
    obtain ⟨z, hz⟩ := positive_baseline_class_nonempty M q L hL x k (by omega) hk
    have hmass : 0 < M.instKernel x (L.S k : Set Z) :=
      (hpos z).trans_le (measure_mono (singleton_subset_iff.mpr hz))
    haveI := M.instKernel_markov
    have hmassreal : (M.instKernel x (L.S k : Set Z)).toReal ≠ 0 :=
      (ENNReal.toReal_pos hmass.ne' (measure_ne_top _ _)).ne'
    rw [treatedSuccess, if_neg hk0, hx]
    dsimp only
    rw [pooled_response_selected_mass M h.2.2.2.1 x _ hS,
      pooled_response_treated_integral M h.2.2.2.1 x _ hS _ hp,
      hmean _ (hL.2.2.2.2.2.2.2.2.2.2.1 x k (by omega)),
      ← mul_assoc, inv_mul_cancel₀ hmassreal, one_mul]

end Papers.TbsPrteOptimalTransport

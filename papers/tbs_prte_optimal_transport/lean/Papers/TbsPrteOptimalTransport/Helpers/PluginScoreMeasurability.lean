module
public import Papers.TbsPrteOptimalTransport.Helpers.PluginMeasurability
public import Mathlib.MeasureTheory.Integral.Prod
public import Papers.TbsPrteOptimalTransport.Helpers.PluginSplitMoment
/-! Completed measurability of the continuous fitted score on a training block. -/
@[expose] public section
set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set
open scoped Classical

-- @node: unitRankClamp
/-- For [a real-valued rank](hyp:r), [the unit-rank clamp](goal) replaces values below zero by zero and values above one by one, returning a rank in the closed unit interval. -/
def unitRankClamp (r : ℝ) : Icc (0 : ℝ) 1 :=
  ⟨max 0 (min 1 r), le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

-- @node: measurable_unitRankClamp
/-- [Clamping a real rank to the closed unit interval is a measurable operation](goal). -/
@[fun_prop] lemma measurable_unitRankClamp : Measurable unitRankClamp := by
  unfold unitRankClamp
  fun_prop

-- @node: unitRankClamp_of_mem
/-- If [a rank already belongs to the closed unit interval](hyp:hr),
[clamping it to that interval leaves its numerical value unchanged](goal). -/
lemma unitRankClamp_of_mem (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
    (unitRankClamp r).val = r := by
  simp only [unitRankClamp, min_eq_right hr.2, max_eq_right hr.1]

-- @node: measurable_quantilePrimitive_rank
/-- If [a rank function is jointly measurable in its parameter and unit-interval rank](hyp:hQ),
[its integral from zero to the rank is also jointly measurable in that parameter and unit-interval rank](goal). -/
@[fun_prop] lemma measurable_quantilePrimitive_rank
    {T : Type*} [MeasurableSpace T] (Q : T → ℝ → ℝ)
    (hQ : Measurable (fun tr : T × Icc (0 : ℝ) 1 => Q tr.1 tr.2.val)) :
    Measurable (fun tr : T × Icc (0 : ℝ) 1 => quantilePrimitive (Q tr.1) tr.2.val) := by
  let f : (T × Icc (0 : ℝ) 1) × ℝ → ℝ := fun trs =>
    if 0 < trs.2 ∧ trs.2 ≤ trs.1.2.val then Q trs.1.1 (unitRankClamp trs.2) else 0
  have hm : Measurable f := by
    apply Measurable.ite
    · exact (measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd (by fun_prop))
    · exact hQ.comp (measurable_fst.fst.prodMk
        (measurable_unitRankClamp.comp measurable_snd))
    · fun_prop
  have hi := (hm.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
  convert hi using 1
  funext tr
  symm
  change (∫ s, f (tr, s)) = ∫ s in Ioc 0 tr.2.val, Q tr.1 s
  rw [← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards [] with s
  by_cases hs : s ∈ Ioc (0 : ℝ) tr.2.val
  · have hr : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2.trans tr.2.property.2⟩
    simp only [f, if_pos (show 0 < s ∧ s ≤ tr.2.val from hs),
      indicator_of_mem hs, unitRankClamp_of_mem s hr]
  · simp only [f, if_neg (show ¬(0 < s ∧ s ≤ tr.2.val) from hs), indicator_of_notMem hs]

universe u v
variable {Ω : Type u} {X Z : Type v}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]

set_option maxHeartbeats 1000000 in
-- @node: aemeasurable_fittedInt_lower_of_endpoints
/-- Under [an admissible policy map](hyp:hphi), assume joint measurability of
[the fitted propensity in training parameter, instrument, and covariates](hyp:hp),
[the fitted regression in training parameter, unit-interval threshold, and covariates](hyp:hg), and
[the fitted rank function in training parameter, covariates, and unit rank](hyp:hQ).
If [all fitted propensity values lie in the unit interval](hyp:hb),
[the lower fitted propensity support endpoint is almost everywhere measurable under the finite joint law of training parameter and observation](hyp:hl), and
[the upper fitted propensity support endpoint is almost everywhere measurable under that law](hyp:hh),
[the fitted lower score formed using the rank function's primitive is almost everywhere measurable under that law](goal). -/
@[fun_prop] lemma aemeasurable_fittedInt_lower_of_endpoints
    (M : LatentIVModel Ω X Z) {T : Type*}
    [MeasurableSpace T]
    (ν : Measure (T × Obs X Z)) [IsFiniteMeasure ν]
    (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (p : T → Z → X → ℝ) (g : T → ℝ → X → ℝ) (Q : T → X → ℝ → ℝ)
    (hp : Measurable (fun tzx : T × Z × X => p tzx.1 tzx.2.1 tzx.2.2))
    (hg : Measurable (fun tpx : T × Icc (0 : ℝ) 1 × X => g tpx.1 tpx.2.1.val tpx.2.2))
    (hQ : Measurable (fun txr : T × X × Icc (0 : ℝ) 1 => Q txr.1 txr.2.1 txr.2.2.val))
    (hb : ∀ t z x, p t z x ∈ Icc (0 : ℝ) 1)
    (hl : AEMeasurable (fun txo : T × Obs X Z => pLow (p txo.1) txo.2.1) ν)
    (hh : AEMeasurable (fun txo : T × Obs X Z => pHigh (p txo.1) txo.2.1) ν) :
    AEMeasurable (fun txo => fittedInt M false phi (p txo.1) (g txo.1)
      (fun x => quantilePrimitive (Q txo.1 x)) txo.2) ν := by
  have hpm : Measurable (fun txo : T × Obs X Z => p txo.1 txo.2.2.1 txo.2.1) :=
    hp.comp (show Measurable (fun txo : T × Obs X Z =>
      (txo.1, txo.2.2.1, txo.2.1)) by fun_prop)
  have hqm : Measurable (fun txo : T × Obs X Z => phi txo.2.2.1 txo.2.1
      (p txo.1 txo.2.2.1 txo.2.1)) := hphi.1.comp
        (show Measurable (fun txo : T × Obs X Z =>
          (txo.2.2.1, txo.2.1, (⟨p txo.1 txo.2.2.1 txo.2.1, hb txo.1 _ _⟩ : Icc (0 : ℝ) 1))) by
            exact measurable_snd.snd.fst.prodMk
              (measurable_snd.fst.prodMk hpm.subtype_mk))
  let lo := hl.mk (fun txo : T × Obs X Z => pLow (p txo.1) txo.2.1)
  let hi := hh.mk (fun txo : T × Obs X Z => pHigh (p txo.1) txo.2.1)
  have hlo : Measurable lo := hl.measurable_mk
  have hhi : Measurable hi := hh.measurable_mk
  have hgm : Measurable (fun tpx : T × ℝ × X =>
      g tpx.1 (unitRankClamp tpx.2.1).val tpx.2.2) := hg.comp (show Measurable (fun tpx : T × ℝ × X =>
      (tpx.1, unitRankClamp tpx.2.1, tpx.2.2)) by fun_prop)
  have hQr : Measurable (fun txr : (T × X) × Icc (0 : ℝ) 1 =>
      Q txr.1.1 txr.1.2 txr.2.val) := hQ.comp (show Measurable (fun txr : (T × X) × Icc (0 : ℝ) 1 =>
      (txr.1.1, txr.1.2, txr.2)) by fun_prop)
  have hCm : Measurable (fun txr : T × X × ℝ =>
      quantilePrimitive (Q txr.1 txr.2.1) (unitRankClamp txr.2.2).val) :=
    (measurable_quantilePrimitive_rank (fun tx : T × X => Q tx.1 tx.2) hQr).comp
      (show Measurable (fun txr : T × X × ℝ =>
        ((txr.1, txr.2.1), unitRankClamp txr.2.2)) by fun_prop)
  let F : T × Obs X Z → ℝ := fun txo =>
    (if 0 < lo txo then -lo txo *
      (quantilePrimitive (Q txo.1 txo.2.1) (unitRankClamp 1).val -
        quantilePrimitive (Q txo.1 txo.2.1)
          (unitRankClamp (min 1 (phi txo.2.2.1 txo.2.1
            (p txo.1 txo.2.2.1 txo.2.1) / lo txo))).val) else 0) +
    g txo.1 (unitRankClamp (min (hi txo) (max (lo txo)
      (phi txo.2.2.1 txo.2.1 (p txo.1 txo.2.2.1 txo.2.1))))).val txo.2.1 -
    g txo.1 (unitRankClamp (p txo.1 txo.2.2.1 txo.2.1)).val txo.2.1 +
    M.yMin * max 0 (phi txo.2.2.1 txo.2.1 (p txo.1 txo.2.2.1 txo.2.1) - hi txo)
  have hFm : Measurable F := by
    dsimp only [F]
    apply Measurable.add
    · apply Measurable.sub
      · apply Measurable.add
        · apply Measurable.ite (measurableSet_lt measurable_const hlo)
          · exact hlo.neg.mul ((hCm.comp
              (measurable_fst.prodMk (measurable_snd.fst.prodMk measurable_const))).sub
              (hCm.comp (measurable_fst.prodMk (measurable_snd.fst.prodMk
                (measurable_const.min (hqm.div hlo))))))
          · fun_prop
        · exact hgm.comp (measurable_fst.prodMk
            ((hhi.min (hlo.max hqm)).prodMk measurable_snd.fst))
      · exact hgm.comp (measurable_fst.prodMk (hpm.prodMk measurable_snd.fst))
    · exact measurable_const.mul (measurable_const.max (hqm.sub hhi))
  apply hFm.aemeasurable.congr
  filter_upwards [hl.ae_eq_mk, hh.ae_eq_mk] with txo hlow hhigh
  change pLow (p txo.1) txo.2.1 = lo txo at hlow
  change pHigh (p txo.1) txo.2.1 = hi txo at hhigh
  have he := propensity_support_endpoints (p txo.1) (hb txo.1) txo.2.1
  have hq := hphi.2 txo.2.2.1 txo.2.1 (p txo.1 txo.2.2.1 txo.2.1)
    (hb txo.1 txo.2.2.1 txo.2.1)
  have hcl : min (pHigh (p txo.1) txo.2.1)
      (max (pLow (p txo.1) txo.2.1) (phi txo.2.2.1 txo.2.1
        (p txo.1 txo.2.2.1 txo.2.1))) ∈ Icc (0 : ℝ) 1 :=
    ⟨le_min he.2.1.1 (he.1.1.trans (le_max_left _ _)),
      (min_le_left _ _).trans he.2.1.2⟩
  dsimp only [F, fittedInt]
  rw [← hlow, ← hhigh]
  simp only [Bool.false_eq_true, if_false, unitRankClamp_of_mem 1 ⟨zero_le_one, le_rfl⟩,
    unitRankClamp_of_mem _ hcl, unitRankClamp_of_mem _ (hb txo.1 txo.2.2.1 txo.2.1)]
  by_cases hlpos : 0 < pLow (p txo.1) txo.2.1
  · have ht : min 1 (phi txo.2.2.1 txo.2.1 (p txo.1 txo.2.2.1 txo.2.1) /
        pLow (p txo.1) txo.2.1) ∈ Icc (0 : ℝ) 1 :=
      ⟨le_min zero_le_one (div_nonneg hq.1 hlpos.le), min_le_left _ _⟩
    simp only [if_pos hlpos, unitRankClamp_of_mem _ ht, clampPolicy, policyProp]
  · simp only [if_neg hlpos, clampPolicy, policyProp]

-- @node: aemeasurable_fittedInt_lower_training_block
/-- For a standard Borel training-parameter space and a finite joint law of training parameter and observation, suppose
[the policy map is admissible](hyp:hphi), [the fitted propensity is jointly measurable in training parameter, instrument, and covariates](hyp:hp),
[the fitted regression is jointly measurable in training parameter, unit-interval threshold, and covariates](hyp:hg),
[the fitted rank function is jointly measurable in training parameter, covariates, and unit rank](hyp:hQ), and
[all fitted propensity values lie in the unit interval](hyp:hb).
Then [the fitted lower score using the rank function's primitive is almost everywhere measurable under the joint law](goal). -/
@[fun_prop] lemma aemeasurable_fittedInt_lower_training_block
    (M : LatentIVModel Ω X Z) {T : Type*}
    [MeasurableSpace T] [StandardBorelSpace T]
    (ν : Measure (T × Obs X Z)) [IsFiniteMeasure ν]
    (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (p : T → Z → X → ℝ) (g : T → ℝ → X → ℝ) (Q : T → X → ℝ → ℝ)
    (hp : Measurable (fun tzx : T × Z × X => p tzx.1 tzx.2.1 tzx.2.2))
    (hg : Measurable (fun tpx : T × Icc (0 : ℝ) 1 × X => g tpx.1 tpx.2.1.val tpx.2.2))
    (hQ : Measurable (fun txr : T × X × Icc (0 : ℝ) 1 => Q txr.1 txr.2.1 txr.2.2.val))
    (hb : ∀ t z x, p t z x ∈ Icc (0 : ℝ) 1) :
    AEMeasurable (fun txo => fittedInt M false phi (p txo.1) (g txo.1)
      (fun x => quantilePrimitive (Q txo.1 x)) txo.2) ν := by
  have hparam : Measurable (fun toz : (T × Obs X Z) × Z =>
      p toz.1.1 toz.2 toz.1.2.1) := hp.comp
    (show Measurable (fun toz : (T × Obs X Z) × Z =>
      (toz.1.1, toz.2, toz.1.2.1)) by fun_prop)
  exact aemeasurable_fittedInt_lower_of_endpoints M ν phi hphi p g Q hp hg hQ hb
    (aemeasurable_bounded_parameter_infimum ν _ hparam
      (fun txo z => (hb txo.1 z txo.2.1).1))
    (aemeasurable_bounded_parameter_supremum ν _ hparam
      (fun txo z => (hb txo.1 z txo.2.1).2))

-- @node: standardBorel_unit_sum
/-- For any standard Borel space, [adjoining one distinct extra point gives another standard Borel space](goal). -/
lemma standardBorel_unit_sum {E : Type*} [MeasurableSpace E] [StandardBorelSpace E] :
    StandardBorelSpace (Unit ⊕ E) := by
  letI := upgradeStandardBorel (E)
  have hB : borel (Unit ⊕ E) = (inferInstance : MeasurableSpace (Unit ⊕ E)) := by
    apply le_antisymm
    · apply MeasurableSpace.generateFrom_le
      intro s hs
      exact measurableSet_sum_iff.mpr
        ⟨(continuous_inl.isOpen_preimage s hs).measurableSet,
          (continuous_inr.isOpen_preimage s hs).measurableSet⟩
    · intro s hs
      obtain ⟨hl, hr⟩ := measurableSet_sum_iff.mp hs
      letI : MeasurableSpace (Unit ⊕ E) := borel (Unit ⊕ E)
      haveI : BorelSpace (Unit ⊕ E) := ⟨rfl⟩
      have hi : MeasurableSet (Sum.inl '' (Sum.inl ⁻¹' s) : Set (Unit ⊕ E)) :=
        (Topology.IsOpenEmbedding.inl (X := Unit) (Y := E)).measurableEmbedding.measurableSet_image.mpr hl
      have hj : MeasurableSet (Sum.inr '' (Sum.inr ⁻¹' s) : Set (Unit ⊕ E)) :=
        (Topology.IsOpenEmbedding.inr (X := Unit) (Y := E)).measurableEmbedding.measurableSet_image.mpr hr
      convert hi.union hj using 1
      ext q
      rcases q with u | e
      · simp only [mem_union, mem_image, mem_preimage, Sum.inl.injEq, Sum.inr_ne_inl,
          and_false, exists_false, or_false]
        constructor
        · intro hs
          exact ⟨u, hs, True.intro⟩
        · rintro ⟨x, hx, hxu⟩
          simpa only [Subsingleton.elim x u] using hx
      · simp
  haveI : BorelSpace (Unit ⊕ E) := ⟨hB.symm⟩
  constructor
  exact ⟨inferInstance, inferInstance, inferInstance⟩

-- @node: connected_fit_lower_score_aemeasurable
/-- If [the policy map is admissible](hyp:hphi) and
[the fitted propensity, regression, and quantiles satisfy the three-way partition, joint labeled-training measurability, joint input measurability, and propensity and quantile range and monotonicity conditions](hyp:hFit),
[at each sample size the fitted lower score using the fitted quantile primitive is almost everywhere measurable under the product law of the sample realization and a fresh observation](goal). -/
@[fun_prop] lemma connected_fit_lower_score_aemeasurable
    (M : LatentIVModel Ω X Z) {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] (S : ObservedSample M μ)
    (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (I : Fin 3 → SampleSplit A)
    (p : ℕ → A → Z → X → ℝ) (g : ℕ → A → ℝ → X → ℝ)
    (Q : ℕ → A → X → ℝ → ℝ)
    (hFit : ConnectedJointFitScope M μ S I p g Q) (n : ℕ) :
    AEMeasurable (fun ao : A × Obs X Z => fittedInt M false phi (p n ao.1) (g n ao.1)
      (fun x => quantilePrimitive (Q n ao.1 x)) ao.2) (μ.prod (observationLaw M)) := by
  haveI : IsProbabilityMeasure (observationLaw M) :=
    Measure.isProbabilityMeasure_map
      ((M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY))).aemeasurable)
  haveI : StandardBorelSpace (Unit ⊕ Obs X Z) := standardBorel_unit_sum
  let T := (Finset ℕ × (Fin n → Unit ⊕ Obs X Z)) ×
    (Finset ℕ × (Fin n → Unit ⊕ Obs X Z))
  let view : A → T := fun a => (trainingView M S (I 0) n a, trainingView M S (I 1) n a)
  have hv : Measurable view := by
    have htrain (j : Fin 3) : Measurable (trainingView M S (I j) n) := by
      unfold trainingView
      apply (hFit.1.1 n j).prodMk
      apply measurable_pi_lambda
      intro i
      apply Measurable.ite
      · exact (hFit.1.1 n j) (Set.to_countable {J : Finset ℕ | i.val ∈ J}).measurableSet
      · exact measurable_inr.comp (S.meas i.val)
      · fun_prop
    exact (htrain 0).prodMk (htrain 1)
  obtain ⟨F, hF, heq⟩ := measurable_training_predictor_factorization view
    (fun a (zx : Z × X) => p n a zx.1 zx.2) (hFit.2.1 n)
  let PF := fun t z x => max 0 (min 1 (F t (z, x)))
  have hPF : ∀ t z x, PF t z x ∈ Icc (0 : ℝ) 1 := fun t z x =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hpEq (a : A) : PF (view a) = p n a := by
    funext z x
    dsimp only [PF]
    rw [← heq a (z, x)]
    have hr := hFit.2.2.2.2.2.2.2.1 n a z x
    exact (congrArg (max 0) (min_eq_right hr.2)).trans (max_eq_right hr.1)
  let V := fun ao : A × Obs X Z => (view ao.1, ao.2)
  have hV : Measurable V := by fun_prop
  let ν := (μ.prod (observationLaw M)).map V
  have hm : Measurable (fun tz : (T × Obs X Z) × Z => PF tz.1.1 tz.2 tz.1.2.1) := by
    dsimp only [PF]
    exact measurable_const.max (measurable_const.min (hF.comp
      (measurable_fst.fst.prodMk (measurable_snd.prodMk measurable_fst.snd.fst))))
  have hl := (aemeasurable_bounded_parameter_infimum ν _ hm
    (fun txo z => (hPF txo.1 z txo.2.1).1)).comp_measurable hV
  have hh := (aemeasurable_bounded_parameter_supremum ν _ hm
    (fun txo z => (hPF txo.1 z txo.2.1).2)).comp_measurable hV
  have hlo : AEMeasurable (fun ao : A × Obs X Z => pLow (p n ao.1) ao.2.1)
      (μ.prod (observationLaw M)) := by
    simpa only [Function.comp_def, V, hpEq, pLow] using hl
  have hhi : AEMeasurable (fun ao : A × Obs X Z => pHigh (p n ao.1) ao.2.1)
      (μ.prod (observationLaw M)) := by
    simpa only [Function.comp_def, V, hpEq, pHigh] using hh
  rcases hFit with ⟨_, _, _, _, hp, hg, hQ, hb, _, _⟩
  exact aemeasurable_fittedInt_lower_of_endpoints M _ phi hphi (p n) (g n) (Q n)
    (hp n) (hg n) (hQ n) (hb n) hlo hhi

end Papers.TbsPrteOptimalTransport

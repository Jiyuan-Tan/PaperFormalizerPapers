module
public import Papers.TbsPrteOptimalTransport.Helpers.PluginStability
public import Papers.TbsPrteOptimalTransport.Helpers.PluginTraining
public import Papers.TbsPrteOptimalTransport.Helpers.PluginScoreMeasurability
/-! Transport of completed score versions to independent evaluation blocks. -/
public section
set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

-- @node: fixed_block_measurable_score_version
/-- Suppose [each observation is measurable](hyp:hW), [the observations are
mutually independent](hyp:hi), [each has distribution P](hyp:hLaw), and
[the training and evaluation blocks are disjoint](hyp:hd). If [the score is
measurable up to null sets under the product of the training-block law and P](hyp:hf),
[C is nonnegative](hyp:hC), and [the score is bounded in absolute value by C](hyp:hb),
then [there is an everywhere jointly measurable score bounded by C that almost
surely agrees with the original at every evaluation observation and has the
same training-dependent population mean](goal). -/
lemma fixed_block_measurable_score_version
    {A E ι : Type*} [MeasurableSpace A] [MeasurableSpace E]
    {μ : Measure A} {P : Measure E} [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (W : ι → A → E) (hW : ∀ i, Measurable (W i)) (hi : iIndepFun W μ)
    (hLaw : ∀ i, μ.map (W i) = P)
    (train eval : Finset ι) (hd : Disjoint train eval)
    (f : (train → E) → E → ℝ)
    (hf : AEMeasurable (Function.uncurry f)
      ((μ.map (fun a (j : train) => W j a)).prod P))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ t x, |f t x| ≤ C) :
    ∃ G : (train → E) → E → ℝ,
      Measurable (Function.uncurry G) ∧ (∀ t x, |G t x| ≤ C) ∧
      ∀ᵐ a ∂μ,
        (∀ i ∈ eval, f (fun j : train => W j a) (W i a) =
          G (fun j : train => W j a) (W i a)) ∧
        (∫ x, f (fun j : train => W j a) x ∂P) =
          ∫ x, G (fun j : train => W j a) x ∂P := by
  let T : A → (train → E) := fun a j => W j a
  have hT : Measurable T := by fun_prop
  let G : (train → E) → E → ℝ := fun t x =>
    max (-C) (min C (hf.mk (Function.uncurry f) (t, x)))
  have hG : Measurable (Function.uncurry G) :=
    measurable_const.max (measurable_const.min hf.measurable_mk)
  have hGb (t : train → E) (x : E) : |G t x| ≤ C := by
    apply abs_le.mpr
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hfg : Function.uncurry f =ᵐ[(μ.map T).prod P] Function.uncurry G := by
    filter_upwards [hf.ae_eq_mk] with tx htx
    dsimp only [Function.uncurry, G]
    rw [← htx]
    dsimp only [Function.uncurry]
    have hbound := abs_le.mp (hb tx.1 tx.2)
    rw [min_eq_right hbound.2, max_eq_right hbound.1]
  have hmean : ∀ᵐ a ∂μ, (∫ x, f (T a) x ∂P) = ∫ x, G (T a) x ∂P := by
    have hsections := Measure.ae_ae_eq_of_ae_eq_uncurry hfg
    exact ae_of_ae_map hT.aemeasurable (hsections.mono fun t ht => integral_congr_ae ht)
  have heval (i : eval) : ∀ᵐ a ∂μ, f (T a) (W i a) = G (T a) (W i a) := by
    have hind : IndepFun T (W i) μ :=
      (hi.indepFun_finset train eval hd hW).comp measurable_id (measurable_pi_apply i)
    have hjoint : μ.map (fun a => (T a, W i a)) = (μ.map T).prod P := by
      rw [hind.map_prod_eq_prod_map_map hT.aemeasurable (hW i).aemeasurable, hLaw]
    have hfg' : Function.uncurry f =ᵐ[μ.map (fun a => (T a, W i a))]
        Function.uncurry G := by rw [hjoint]; exact hfg
    exact ae_of_ae_map (hT.prodMk (hW i)).aemeasurable hfg'
  refine ⟨G, hG, hGb, ?_⟩
  filter_upwards [ae_all_iff.mpr heval, hmean] with a ha hm
  exact ⟨fun i hi => ha ⟨i, hi⟩, hm⟩

-- @node: random_labeled_split_average_isBigOp_aemeasurable
/-- For [sample-dependent finite split labels](hyp:label), [training and evaluation index sets specified by each label](hyp:train,eval), [score functions of the label, training observations, and one evaluation observation](hyp:f), and [sets of good labels at each sample size](hyp:good), suppose [the finite split labels are measurable](hyp:hl),
[independent of the observed sample](hyp:hind), and [always specify disjoint
training and evaluation blocks](hyp:hd). If [each score is measurable up to
null sets under the product of its training-block law and the observation law](hyp:hf),
[C is nonnegative](hyp:hC), [all scores are bounded in absolute value by C](hyp:hb),
[the good-label sets are measurable](hyp:hgood), [good evaluation blocks are
nonempty](hyp:he), [c is positive](hyp:hc), [good evaluation blocks have size at
least c times the sample size](hyp:hsize), and [the probability of a bad label
tends to zero](hyp:hbad), then [the evaluation average centered by its
training-dependent population mean is of order the inverse square root of
sample size in probability](goal). -/
lemma random_labeled_split_average_isBigOp_aemeasurable
    {A E : Type*} [MeasurableSpace A] [MeasurableSpace E]
    {μ : Measure A} {P : Measure E} [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (S : Causalean.Stat.IIDSample A E μ P)
    (L : ℕ → Type*) [∀ n, Fintype (L n)] [∀ n, MeasurableSpace (L n)]
    [∀ n, MeasurableSingletonClass (L n)]
    (label : ∀ n, A → L n) (hl : ∀ n, Measurable (label n))
    (hind : ∀ n, IndepFun (label n) (fun a (i : Fin n) => S.Z i a) μ)
    (train eval : ∀ n, L n → Finset (Fin n))
    (hd : ∀ n l, Disjoint (train n l) (eval n l))
    (f : ∀ n (l : L n), (train n l → E) → E → ℝ)
    (hf : ∀ n l, AEMeasurable (Function.uncurry (f n l))
      ((μ.map (fun a (j : train n l) => S.Z j.val.val a)).prod P))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n l t x, |f n l t x| ≤ C)
    (good : ∀ n, Set (L n)) (hgood : ∀ n, MeasurableSet (good n))
    (he : ∀ n l, l ∈ good n → 0 < (eval n l).card)
    (c : ℝ) (hc : 0 < c)
    (hsize : ∀ n l, l ∈ good n → c * n ≤ ((eval n l).card : ℝ))
    (hbad : Tendsto (fun n => μ {a | label n a ∉ good n}) atTop (𝓝 0)) :
    Causalean.Stat.IsBigOp
      (fun n a => ((eval n (label n a)).card : ℝ)⁻¹ *
        ∑ i ∈ eval n (label n a),
          (f n (label n a) (fun j : train n (label n a) => S.Z j.val.val a) (S.Z i.val a) -
            ∫ x, f n (label n a) (fun j : train n (label n a) => S.Z j.val.val a) x ∂P))
      (fun n => (n : ℝ)^(-1/2 : ℝ)) μ := by
  choose G hG hGb hEq using fun n l => fixed_block_measurable_score_version
    (fun (i : Fin n) a => S.Z i.val a) (fun i => S.meas i.val)
    (S.indep.precomp Fin.val_injective) (fun i => S.map_eq i.val)
    (train n l) (eval n l) (hd n l) (f n l) (hf n l) C hC (hb n l)
  have hRate := random_labeled_split_average_isBigOp S L label hl hind train eval
    G hG C hC hGb good hgood (fun n l _ => hd n l) he c hc hsize hbad
  have heq (n : ℕ) :
      (fun a => ((eval n (label n a)).card : ℝ)⁻¹ *
        ∑ i ∈ eval n (label n a),
          (f n (label n a) (fun j : train n (label n a) => S.Z j.val.val a) (S.Z i.val a) -
            ∫ x, f n (label n a) (fun j : train n (label n a) => S.Z j.val.val a) x ∂P)) =ᵐ[μ]
      (fun a => ((eval n (label n a)).card : ℝ)⁻¹ *
        ∑ i ∈ eval n (label n a),
          (G n (label n a) (fun j : train n (label n a) => S.Z j.val.val a) (S.Z i.val a) -
            ∫ x, G n (label n a) (fun j : train n (label n a) => S.Z j.val.val a) x ∂P)) := by
    filter_upwards [ae_all_iff.mpr (hEq n)] with a ha
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [(ha (label n a)).1 i hi, (ha (label n a)).2]
  intro δ hδ
  obtain ⟨K, hK, ht⟩ := hRate δ hδ
  refine ⟨K, hK, ht.mono ?_⟩
  intro n hn
  apply le_trans _ hn
  apply measure_mono_ae
  filter_upwards [heq n] with a ha
  intro h
  change K * (n : ℝ)^(-1/2 : ℝ) ≤ ‖_‖ at h ⊢
  rw [← ha]
  exact h

universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]
variable (M : LatentIVModel Ω X Z) {μ : Measure A} (S : ObservedSample M μ)

-- @node: labeled_training_block_score_average_isBigOp
/-- For [score representations indexed by sample size and two training-block labels, taking the union's observations and one new observation as arguments](hyp:F), suppose [the three splits form a measurable partition independent of the
sample](hyp:hPartition), [each fixed-block score representation is measurable
up to null sets under the product of the training-block and observation laws](hyp:hFm),
[C is nonnegative](hyp:hC), [all representations are bounded in absolute value
by C](hyp:hFb), and [the score equals its representation through the two
training labels and their union's observations whenever those blocks lie
within the sample](hyp:hFe). If [c is positive](hyp:hc) and [the probability
that the third block has fewer than c times the sample size observations tends
to zero](hyp:hsize), then [the third-block score average centered by its
training-dependent population mean is of order the inverse square root of
sample size in probability](goal). -/
lemma labeled_training_block_score_average_isBigOp [IsProbabilityMeasure μ]
    (I : Fin 3 → SampleSplit A) (hPartition : ThreeWayPartition M μ S I)
    (score : ℕ → A → Obs X Z → ℝ)
    (F : ∀ n (l : Finset (Fin n) × Finset (Fin n)),
      ((l.1 ∪ l.2 : Finset (Fin n)) → Obs X Z) → Obs X Z → ℝ)
    (hFm : ∀ n l, AEMeasurable (Function.uncurry (F n l))
      ((μ.map (fun a (j : (l.1 ∪ l.2 : Finset (Fin n))) => S.Z j.val.val a)).prod
        (observationLaw M)))
    (C : ℝ) (hC : 0 ≤ C) (hFb : ∀ n l t o, |F n l t o| ≤ C)
    (hFe : ∀ n a, I 0 n a ⊆ Finset.range n → I 1 n a ⊆ Finset.range n → ∀ o,
      score n a o = F n (finiteSplitLabel n (I 0 n a), finiteSplitLabel n (I 1 n a))
        (fun j => S.Z j.val.val a) o)
    (c : ℝ) (hc : 0 < c)
    (hsize : Tendsto (fun n => μ {a | ((I 2 n a).card : ℝ) < c * n})
      atTop (𝓝 0)) :
    Causalean.Stat.IsBigOp
      (fun n a => ((I 2 n a).card : ℝ)⁻¹ * ∑ i ∈ I 2 n a,
        (score n a (S.Z i a) - ∫ o, score n a o ∂observationLaw M))
      (fun n => (n : ℝ)^(-1/2 : ℝ)) μ := by
  haveI : IsProbabilityMeasure (observationLaw M) :=
    Measure.isProbabilityMeasure_map
      ((M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY))).aemeasurable)
  let L := fun n => Fin 3 → Finset (Fin n)
  let label : ∀ n, A → L n := fun n a j => finiteSplitLabel n (I j n a)
  have hl (n : ℕ) : Measurable (label n) := by
    apply measurable_pi_lambda
    intro j
    exact (measurable_of_countable (finiteSplitLabel n)).comp (hPartition.1 n j)
  have hind (n : ℕ) : IndepFun (label n) (fun a (i : Fin n) => S.Z i a) μ := by
    let encode : (Fin 3 → Finset ℕ) → L n := fun v j => finiteSplitLabel n (v j)
    have hm : Measurable encode := by
      apply measurable_pi_lambda
      intro j
      exact (measurable_of_countable (finiteSplitLabel n)).comp (measurable_pi_apply j)
    exact (hPartition.2.2 n).comp hm measurable_id
  let good : ∀ n, Set (L n) := fun n => {l | Disjoint (l 0 ∪ l 1) (l 2) ∧
    0 < (l 2).card ∧ c * n ≤ ((l 2).card : ℝ)}
  have hsub (n : ℕ) : ∀ᵐ a ∂μ, ∀ j, I j n a ⊆ Finset.range n := by
    filter_upwards [hPartition.2.1 n] with a ha
    intro j i hi
    rw [← ha.2]
    fin_cases j
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hi)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hi)
    · exact Finset.mem_union_right _ hi
  have hbad_le : ∀ᶠ n : ℕ in atTop,
      μ {a | label n a ∉ good n} ≤ μ {a | ((I 2 n a).card : ℝ) < c * n} := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    apply measure_mono_ae
    filter_upwards [hPartition.2.1 n, hsub n] with a ha hs
    intro hbad
    by_contra hnot
    have hsz : c * n ≤ ((I 2 n a).card : ℝ) := le_of_not_gt hnot
    have hsz' : c * n ≤ ((label n a 2).card : ℝ) := by
      simpa only [label, finiteSplitLabel_card n _ (hs 2)] using hsz
    have hpos : 0 < (label n a 2).card := by
      have hn' : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
      exact_mod_cast (mul_pos hc hn').trans_le hsz'
    have hd : Disjoint (label n a 0 ∪ label n a 1) (label n a 2) := by
      apply Finset.disjoint_union_left.mpr
      constructor
      · apply Finset.disjoint_left.mpr
        intro i hi he
        have h₀ : i.val ∈ I 0 n a := by simpa [label, finiteSplitLabel] using hi
        have h₂ : i.val ∈ I 2 n a := by simpa [label, finiteSplitLabel] using he
        exact Finset.disjoint_left.mp (ha.1 0 2 (by decide)) h₀ h₂
      · apply Finset.disjoint_left.mpr
        intro i hi he
        have h₁ : i.val ∈ I 1 n a := by simpa [label, finiteSplitLabel] using hi
        have h₂ : i.val ∈ I 2 n a := by simpa [label, finiteSplitLabel] using he
        exact Finset.disjoint_left.mp (ha.1 1 2 (by decide)) h₁ h₂
    exact hbad ⟨hd, hpos, hsz'⟩
  have hbad : Tendsto (fun n => μ {a | label n a ∉ good n}) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsize
      (Eventually.of_forall fun n => bot_le) hbad_le
  have hRate := random_labeled_split_average_isBigOp_aemeasurable S L label hl hind
    (fun n l => l 0 ∪ l 1) (fun n l => l 2 \ (l 0 ∪ l 1))
    (fun n l => Finset.disjoint_left.mpr (fun i hi hj => (Finset.mem_sdiff.mp hj).2 hi))
    (fun n l => F n (l 0, l 1)) (fun n l => hFm n (l 0, l 1))
    C hC (fun n l => hFb n (l 0, l 1)) good
    (fun n => (Set.to_countable _).measurableSet)
    (fun n l h => by rw [sdiff_eq_left.mpr h.1.symm]; exact h.2.1) c hc
    (fun n l h => by rw [sdiff_eq_left.mpr h.1.symm]; exact h.2.2) hbad
  have heq (n : ℕ) :
      (fun a => ((I 2 n a).card : ℝ)⁻¹ * ∑ i ∈ I 2 n a,
        (score n a (S.Z i a) - ∫ o, score n a o ∂observationLaw M)) =ᵐ[μ]
      (fun a => ((label n a 2 \ (label n a 0 ∪ label n a 1)).card : ℝ)⁻¹ *
        ∑ i ∈ label n a 2 \ (label n a 0 ∪ label n a 1),
        (F n (label n a 0, label n a 1)
          (fun j => S.Z j.val.val a) (S.Z i.val a) -
          ∫ o, F n (label n a 0, label n a 1) (fun j => S.Z j.val.val a) o
            ∂observationLaw M)) := by
    filter_upwards [hsub n, hPartition.2.1 n] with a hs hp
    have hd : Disjoint (label n a 2) (label n a 0 ∪ label n a 1) := by
      apply Finset.disjoint_union_right.mpr
      constructor
      · apply Finset.disjoint_left.mpr
        intro i hi hj
        exact Finset.disjoint_left.mp (hp.1 2 0 (by decide))
          (by simpa [label, finiteSplitLabel] using hi)
          (by simpa [label, finiteSplitLabel] using hj)
      · apply Finset.disjoint_left.mpr
        intro i hi hj
        exact Finset.disjoint_left.mp (hp.1 2 1 (by decide))
          (by simpa [label, finiteSplitLabel] using hi)
          (by simpa [label, finiteSplitLabel] using hj)
    rw [sdiff_eq_left.mpr hd]
    have hf := hFe n a (hs 0) (hs 1)
    simp_rw [hf]
    dsimp only [label]
    rw [finiteSplitLabel_card n _ (hs 2)]
    congr 1
    nth_rw 1 [← finiteSplitLabel_image n (I 2 n a) (hs 2)]
    rw [Finset.sum_image]
    exact Fin.val_injective.injOn
  intro δ hδ
  obtain ⟨K, hK, ht⟩ := hRate δ hδ
  refine ⟨K, hK, ht.mono ?_⟩
  intro n hn
  apply le_trans _ hn
  apply measure_mono_ae
  filter_upwards [heq n] with a ha
  intro h
  change K * (n : ℝ)^(-1/2 : ℝ) ≤ ‖_‖ at h ⊢
  rw [← ha]
  exact h

-- @node: connected_fit_lower_score_evaluation_isBigOp
/-- If [the policy map is jointly measurable and maps unit-interval propensities
to the unit interval](hyp:hPolicy), [the splits form a measurable partition
independent of the sample, all fits are jointly measurable and use only the two
labeled training views, fitted propensities lie in the unit interval, and fitted
quantiles are nondecreasing on interior ranks and lie between the outcome
bounds at all unit ranks](hyp:hFit), [the regression fit lies between the outcome
bounds enlarged to include zero and its integrated error at the observed and
clamped policy propensities is bounded in probability at rate rg](hyp:hRegression),
[c is positive](hyp:hc), and [the probability that the third block has fewer
than c times the sample size observations tends to zero](hyp:hsize), then
[the third-block average of the fitted lower-bound integrand, centered by its
population mean for the realized fits, is of order the inverse square root of
sample size in probability](goal). -/
lemma connected_fit_lower_score_evaluation_isBigOp [IsProbabilityMeasure μ]
    (phi : Z → X → ℝ → ℝ) (hPolicy : IsPolicyMap phi)
    (I : Fin 3 → SampleSplit A)
    (p : ℕ → A → Z → X → ℝ) (g : ℕ → A → ℝ → X → ℝ)
    (Q : ℕ → A → X → ℝ → ℝ)
    (hFit : ConnectedJointFitScope M μ S I p g Q)
    (rg : ℕ → ℝ) (hRegression : RegressionTargetRate M μ phi p g rg)
    (c : ℝ) (hc : 0 < c)
    (hsize : Tendsto (fun n => μ {a | ((I 2 n a).card : ℝ) < c * n})
      atTop (𝓝 0)) :
    Causalean.Stat.IsBigOp
      (fun n a => ((I 2 n a).card : ℝ)⁻¹ * ∑ i ∈ I 2 n a,
        (fittedInt M false phi (p n a) (g n a)
          (fun x => quantilePrimitive (Q n a x)) (S.Z i a) -
          ∫ o, fittedInt M false phi (p n a) (g n a)
            (fun x => quantilePrimitive (Q n a x)) o ∂observationLaw M))
      (fun n => (n : ℝ)^(-1/2 : ℝ)) μ := by
  haveI : IsProbabilityMeasure (observationLaw M) :=
    Measure.isProbabilityMeasure_map
      ((M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY))).aemeasurable)
  let C := outcomeMagnitude M
  have hmin : |M.yMin| ≤ C := le_max_left _ _
  have hmax : |M.yMax| ≤ C := le_max_right _ _
  have hC : 0 ≤ C := (abs_nonneg _).trans hmin
  have hlo : -C ≤ M.yMin := by linarith [neg_abs_le M.yMin]
  have hhi : M.yMax ≤ C := (le_abs_self _).trans hmax
  have hpB (n : ℕ) (a : A) (zx : Z × X) : |p n a zx.1 zx.2| ≤ 1 := by
    have hr := hFit.2.2.2.2.2.2.2.1 n a zx.1 zx.2
    rw [abs_of_nonneg hr.1]
    exact hr.2
  have hgB (n : ℕ) (a : A) (tx : Icc (0 : ℝ) 1 × X) : |g n a tx.1.val tx.2| ≤ C := by
    have hr := hRegression.1 n a tx.1.val tx.2 tx.1.property
    exact abs_le.mpr ⟨(le_min (by linarith) hlo).trans hr.1,
      hr.2.trans (max_le hC hhi)⟩
  have hQB (n : ℕ) (a : A) (xt : X × Icc (0 : ℝ) 1) : |Q n a xt.1 xt.2.val| ≤ C := by
    have hr := hFit.2.2.2.2.2.2.2.2.2 n a xt.1 xt.2.val xt.2.property
    exact abs_le.mpr ⟨hlo.trans hr.1, hr.2.trans hhi⟩
  choose Fp hFp hFpB hFpEq using fun n => labeled_training_fixed_block_factorization
    M S (I 0) (I 1) n (fun a (zx : Z × X) => p n a zx.1 zx.2)
      (hFit.2.1 n) 1 zero_le_one (hpB n)
  choose Fg hFg hFgB hFgEq using fun n => labeled_training_fixed_block_factorization
    M S (I 0) (I 1) n (fun a (tx : Icc (0 : ℝ) 1 × X) => g n a tx.1.val tx.2)
      (hFit.2.2.1 n) C hC (hgB n)
  choose FQ hFQ hFQB hFQEq using fun n => labeled_training_fixed_block_factorization
    M S (I 0) (I 1) n (fun a (xt : X × Icc (0 : ℝ) 1) => Q n a xt.1 xt.2.val)
      (hFit.2.2.2.1 n) C hC (hQB n)
  let PF := fun n l t z x => max 0 (min 1 (Fp n l t (z, x)))
  let GF := fun n l t r x => Fg n l t (unitRankClamp r, x)
  let QF := fun n l t x r => FQ n l t (x, unitRankClamp r)
  let F := fun n l t o => fittedInt M false phi (PF n l t) (GF n l t)
    (fun x => quantilePrimitive (QF n l t x)) o
  have hpR (n) (l) (t) (z) (x) : PF n l t z x ∈ Icc (0 : ℝ) 1 :=
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hpM (n : ℕ) (l : Finset (Fin n) × Finset (Fin n)) : Measurable (fun tzx : ((l.1 ∪ l.2 : Finset (Fin n)) → Obs X Z) × Z × X => PF n l tzx.1 tzx.2.1 tzx.2.2) := by
    exact measurable_const.max (measurable_const.min (hFp n l))
  have hgM (n : ℕ) (l : Finset (Fin n) × Finset (Fin n)) : Measurable (fun trx : ((l.1 ∪ l.2 : Finset (Fin n)) → Obs X Z) × Icc (0 : ℝ) 1 × X => GF n l trx.1 trx.2.1.val trx.2.2) := by
    fun_prop
  have hQM (n : ℕ) (l : Finset (Fin n) × Finset (Fin n)) : Measurable (fun txr : ((l.1 ∪ l.2 : Finset (Fin n)) → Obs X Z) × X × Icc (0 : ℝ) 1 => QF n l txr.1 txr.2.1 txr.2.2.val) := by
    fun_prop
  have hFm (n) (l) : AEMeasurable (Function.uncurry (F n l))
      ((μ.map (fun a (j : (l.1 ∪ l.2 : Finset (Fin n))) => S.Z j.val.val a)).prod
        (observationLaw M)) := by
    exact aemeasurable_fittedInt_lower_training_block M _ phi hPolicy
      (PF n l) (GF n l) (QF n l) (hpM n l) (hgM n l) (hQM n l) (hpR n l)
  have hQInt (n) (l) (t) (x) : IntegrableOn (QF n l t x) (Icc (0 : ℝ) 1) := by
    have hm : Measurable (QF n l t x) := by
      fun_prop
    apply Integrable.of_bound hm.aestronglyMeasurable C
    exact ae_of_all _ (fun r => by simpa only [Real.norm_eq_abs] using hFQB n l t (x, unitRankClamp r))
  have hFb (n) (l) (t) (o) : |F n l t o| ≤ 4 * C := by
    exact fittedInt_lower_bounded M phi hPolicy _ _ _ (hpR n l t) hC hmin
      (fun r x _ => hFgB n l t (unitRankClamp r, x)) (hQInt n l t)
      (fun x r _ => hFQB n l t (x, unitRankClamp r)) o
  have hFe (n) (a) (h₀ : I 0 n a ⊆ Finset.range n) (h₁ : I 1 n a ⊆ Finset.range n) (o) :
      fittedInt M false phi (p n a) (g n a) (fun x => quantilePrimitive (Q n a x)) o =
        F n (finiteSplitLabel n (I 0 n a), finiteSplitLabel n (I 1 n a))
          (fun j => S.Z j.val.val a) o := by
    let l := (finiteSplitLabel n (I 0 n a), finiteSplitLabel n (I 1 n a))
    let t := fun j : (l.1 ∪ l.2 : Finset (Fin n)) => S.Z j.val.val a
    have hpEq : PF n l t = p n a := by
      funext z x
      dsimp only [PF]
      rw [← hFpEq n a h₀ h₁ (z, x)]
      have hr := hFit.2.2.2.2.2.2.2.1 n a z x
      rw [min_eq_right hr.2, max_eq_right hr.1]
    have hgEq (r x) (hr : r ∈ Icc (0 : ℝ) 1) : GF n l t r x = g n a r x := by
      dsimp only [GF]
      rw [← hFgEq n a h₀ h₁ (unitRankClamp r, x), unitRankClamp_of_mem r hr]
    have hQEq (x r) (hr : r ∈ Icc (0 : ℝ) 1) : QF n l t x r = Q n a x r := by
      dsimp only [QF]
      rw [← hFQEq n a h₀ h₁ (x, unitRankClamp r), unitRankClamp_of_mem r hr]
    have hCEq (x r) (hr : r ∈ Icc (0 : ℝ) 1) :
        quantilePrimitive (QF n l t x) r = quantilePrimitive (Q n a x) r := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro u hu
      exact hQEq x u ⟨hu.1.le, hu.2.trans hr.2⟩
    have he := propensity_support_endpoints (p n a) (hFit.2.2.2.2.2.2.2.1 n a) o.1
    have hq := hPolicy.2 o.2.1 o.1 (p n a o.2.1 o.1) (hFit.2.2.2.2.2.2.2.1 n a _ _)
    have hcl : clampPolicy (p n a) (policyProp phi (p n a)) o.2.1 o.1 ∈ Icc (0 : ℝ) 1 :=
      ⟨le_min he.2.1.1 (le_max_of_le_left he.1.1), (min_le_left _ _).trans he.2.1.2⟩
    change _ = fittedInt M false phi (PF n l t) (GF n l t)
      (fun x => quantilePrimitive (QF n l t x)) o
    rw [hpEq]
    unfold fittedInt
    simp only [Bool.false_eq_true, if_false]
    rw [hgEq _ _ hcl, hgEq _ _ (hFit.2.2.2.2.2.2.2.1 n a _ _)]
    by_cases hl : 0 < pLow (p n a) o.1
    · have hr : min 1 (phi o.2.1 o.1 (p n a o.2.1 o.1) / pLow (p n a) o.1) ∈ Icc (0 : ℝ) 1 :=
        ⟨le_min zero_le_one (div_nonneg hq.1 hl.le), min_le_left _ _⟩
      rw [if_pos hl, if_pos hl, hCEq _ 1 ⟨zero_le_one, le_rfl⟩, hCEq _ _ hr]
    · rw [if_neg hl, if_neg hl]
  exact labeled_training_block_score_average_isBigOp M S I hFit.1 _ F hFm
    (4 * C) (by positivity) hFb hFe c hc hsize

end Papers.TbsPrteOptimalTransport

module
public import Papers.TbsPrteOptimalTransport.Helpers.PluginSplitMoment
/-! Measurable learner factorization through fixed finite training blocks. -/
@[expose] public section
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

-- @node: finiteSplitLabel
/-- For [a sample size n](hyp:n) and [a finite set of observation indices J](hyp:J),
the [finite split label](goal) consists of the indices below n that belong to J,
represented as indices of the sample of size n. -/
def finiteSplitLabel (n : ℕ) (J : Finset ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => i.val ∈ J)

-- @node: finiteSplitLabel_image
/-- If [every index in J is below n](hyp:hJ), then [converting the finite split
label back to natural-number indices recovers J exactly](goal). -/
lemma finiteSplitLabel_image (n : ℕ) (J : Finset ℕ)
    (hJ : J ⊆ Finset.range n) :
    (finiteSplitLabel n J).image Fin.val = J := by
  ext i
  simp only [Finset.mem_image, finiteSplitLabel, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact hj
  · intro hi
    exact ⟨⟨i, Finset.mem_range.mp (hJ hi)⟩, hi, rfl⟩

-- @node: finiteSplitLabel_card
/-- If [every index in J is below n](hyp:hJ), then [the finite split label has
the same number of elements as J](goal). -/
lemma finiteSplitLabel_card (n : ℕ) (J : Finset ℕ)
    (hJ : J ⊆ Finset.range n) : (finiteSplitLabel n J).card = J.card := by
  have h := congrArg Finset.card (finiteSplitLabel_image n J hJ)
  rwa [Finset.card_image_of_injective _ Fin.val_injective] at h

universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]
variable (M : LatentIVModel Ω X Z) {μ : Measure A} (S : ObservedSample M μ)

/-- If [the learner is jointly measurable using the two labeled training views
and its prediction argument](hyp:hf), [C is nonnegative](hyp:hC), and
[all predictions are bounded in absolute value by C](hyp:hb), then
[there is a jointly measurable predictor for each pair of finite training labels,
uniformly bounded in absolute value by C, that reproduces the learner from the
observations in the union of the two blocks whenever both blocks contain only
indices below n](goal). -/
-- @node: labeled_training_fixed_block_factorization
lemma labeled_training_fixed_block_factorization
    {B : Type*} [MeasurableSpace B] (I₀ I₁ : SampleSplit A) (n : ℕ)
    (f : A → B → ℝ)
    (hf : Measurable[(MeasurableSpace.comap
      (fun a => (trainingView M S I₀ n a, trainingView M S I₁ n a))
      inferInstance).prod inferInstance] (Function.uncurry f))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ a b, |f a b| ≤ C) :
    ∃ F : (l : Finset (Fin n) × Finset (Fin n)) →
        ((l.1 ∪ l.2 : Finset (Fin n)) → Obs X Z) → B → ℝ,
      (∀ l, Measurable (Function.uncurry (F l))) ∧
      (∀ l t b, |F l t b| ≤ C) ∧
      ∀ a, I₀ n a ⊆ Finset.range n → I₁ n a ⊆ Finset.range n → ∀ b,
        f a b = F (finiteSplitLabel n (I₀ n a), finiteSplitLabel n (I₁ n a))
          (fun i => S.Z i.val.val a) b := by
  obtain ⟨G, hG, hGb, hGeq⟩ := bounded_training_predictor_factorization
    (fun a => (trainingView M S I₀ n a, trainingView M S I₁ n a)) f hf C hC hb
  let V (l : Finset (Fin n) × Finset (Fin n)) (t : (l.1 ∪ l.2 : Finset (Fin n)) → Obs X Z) :=
    ((l.1.image Fin.val, fun i : Fin n =>
      if hi : i ∈ l.1 then (Sum.inr (t ⟨i, Finset.mem_union_left _ hi⟩) : Unit ⊕ Obs X Z)
      else Sum.inl ()),
     (l.2.image Fin.val, fun i : Fin n =>
      if hi : i ∈ l.2 then (Sum.inr (t ⟨i, Finset.mem_union_right _ hi⟩) : Unit ⊕ Obs X Z)
      else Sum.inl ()))
  have hV (l) : Measurable (V l) := by
    dsimp only [V]
    apply Measurable.prodMk
    · apply measurable_const.prodMk
      apply measurable_pi_lambda
      intro i
      by_cases hi : i ∈ l.1
      · simp only [dif_pos hi]
        fun_prop
      · simp only [dif_neg hi]
        fun_prop
    · apply measurable_const.prodMk
      apply measurable_pi_lambda
      intro i
      by_cases hi : i ∈ l.2
      · simp only [dif_pos hi]
        fun_prop
      · simp only [dif_neg hi]
        fun_prop
  refine ⟨fun l t b => G (V l t) b, ?_, ?_, ?_⟩
  · intro l
    exact hG.comp ((hV l).comp measurable_fst |>.prodMk measurable_snd)
  · intro l t b
    exact hGb _ _
  · intro a h₀ h₁ b
    rw [hGeq a b]
    congr 1
    dsimp only [V, trainingView]
    apply Prod.ext
    · apply Prod.ext
      · exact (finiteSplitLabel_image n (I₀ n a) h₀).symm
      · funext i
        by_cases hi : i.val ∈ I₀ n a
        · simp [finiteSplitLabel, hi]
        · simp [finiteSplitLabel, hi]
    · apply Prod.ext
      · exact (finiteSplitLabel_image n (I₁ n a) h₁).symm
      · funext i
        by_cases hi : i.val ∈ I₁ n a
        · simp [finiteSplitLabel, hi]
        · simp [finiteSplitLabel, hi]

/-- If [the three splits form a measurable partition independent of the sample](hyp:hPartition),
[the score is jointly measurable using the two labeled training views and the
evaluation observation](hyp:hScore), [C is nonnegative](hyp:hC), and
[the score is bounded in absolute value by C](hyp:hb), then, provided
[c is positive](hyp:hc) and [the probability that the third block has fewer
than c times the sample size observations tends to zero](hyp:hsize),
[the third-block score average centered by its training-dependent population
mean is of order the inverse square root of sample size in probability](goal). -/
-- @node: labeled_training_score_average_isBigOp
lemma labeled_training_score_average_isBigOp [IsProbabilityMeasure μ]
    (I : Fin 3 → SampleSplit A) (hPartition : ThreeWayPartition M μ S I)
    (score : ℕ → A → Obs X Z → ℝ)
    (hScore : LabeledTrainingPredictorMeasurable M μ S (I 0) (I 1) score)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n a o, |score n a o| ≤ C)
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
  choose F hFm hFb hFe using fun n => labeled_training_fixed_block_factorization
    M S (I 0) (I 1) n (score n) (hScore n) C hC (hb n)
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
  have hRate := random_labeled_split_average_isBigOp S L label hl hind
    (fun n l => l 0 ∪ l 1) (fun n l => l 2)
    (fun n l => F n (l 0, l 1)) (fun n l => hFm n (l 0, l 1))
    C hC (fun n l => hFb n (l 0, l 1)) good
    (fun n => (Set.to_countable _).measurableSet) (fun n l h => h.1)
    (fun n l h => h.2.1) c hc (fun n l h => h.2.2) hbad
  have heq (n : ℕ) :
      (fun a => ((I 2 n a).card : ℝ)⁻¹ * ∑ i ∈ I 2 n a,
        (score n a (S.Z i a) - ∫ o, score n a o ∂observationLaw M)) =ᵐ[μ]
      (fun a => ((label n a 2).card : ℝ)⁻¹ * ∑ i ∈ label n a 2,
        (F n (label n a 0, label n a 1)
          (fun j => S.Z j.val.val a) (S.Z i.val a) -
          ∫ o, F n (label n a 0, label n a 1) (fun j => S.Z j.val.val a) o
            ∂observationLaw M)) := by
    filter_upwards [hsub n] with a hs
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

end Papers.TbsPrteOptimalTransport

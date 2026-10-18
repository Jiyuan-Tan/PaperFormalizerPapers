module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLRandomSplitLaw
public import Papers.TbsPrteOptimalTransport.Helpers.DMLIndependentScoreMoments
/-! Independence of the actual random training view and held-out records.
We mix over the finite set of valid training masks. The fixed-mask evaluation
law is constant, so revealing the mask with the training records preserves
independence. No measurable structure on the sample space beyond its given
sigma algebra is needed. -/
public section

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set

universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]

-- @node: dml_random_training_indep_of_fixed_laws
/-- Under [an equal half split independent of the sample](hyp:hSplit), with
[at least two observations](hyp:hn) and [an even sample size](hyp:heven), suppose
[the evaluation statistic is measurable for each training mask](hyp:hW),
[is independent of the masked training records for every fixed half-size mask](hyp:hfixed),
and [has the same law for every such mask](hyp:hlaw). Then [the statistic selected
by the random training mask is independent of the training view and retains that law](goal). -/
lemma dml_random_training_indep_of_fixed_laws {B : Type*} [MeasurableSpace B]
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (n : ℕ) (hn : 2 ≤ n) (heven : Even n)
    (P : Measure B) (W : Finset ℕ → (Fin n → Obs X Z) → B)
    (hW : ∀ J, Measurable (W J))
    (hfixed : ∀ J ∈ (Finset.range n).powersetCard (n / 2),
      IndepFun (fun a => (J, fun i : Fin n =>
        if i.val ∈ J then (Sum.inr (S.Z i a) : Unit ⊕ Obs X Z) else Sum.inl ()))
        (fun a => W J (fun i => S.Z i a)) μ)
    (hlaw : ∀ J ∈ (Finset.range n).powersetCard (n / 2),
      μ.map (fun a => W J (fun i => S.Z i a)) = P) :
    IndepFun (trainingView M S I₁ n)
      (fun a => W (I₁ n a) (fun i => S.Z i a)) μ ∧
      μ.map (fun a => W (I₁ n a) (fun i => S.Z i a)) = P := by
  classical
  let masks := (Finset.range n).powersetCard (n / 2)
  have hvalid : ∀ᵐ a ∂μ, I₁ n a ∈ masks := by
    filter_upwards [(hSplit n hn heven).1] with a ha
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_, ha.2.2.1⟩
    intro i hi
    rw [← ha.2.1]
    exact Finset.mem_union_left _ hi
  obtain ⟨a₀, ha₀⟩ := hvalid.exists
  let k₀ : masks := ⟨I₁ n a₀, ha₀⟩
  let select : Finset ℕ → masks := fun J => if hJ : J ∈ masks then ⟨J, hJ⟩ else k₀
  let R : A → masks := fun a => select (I₁ n a)
  let T : masks → A → Finset ℕ × (Fin n → Unit ⊕ Obs X Z) := fun J a =>
    (J.val, fun i => if i.val ∈ J.val then Sum.inr (S.Z i a) else Sum.inl ())
  let V : masks → A → B := fun J a => W J.val (fun i => S.Z i a)
  have hR : Measurable R :=
    (measurable_of_countable select).comp (hSplit n hn heven).2.1
  have hT : ∀ J, Measurable (T J) := by
    intro J
    first | fun_prop | skip
    apply measurable_const.prodMk
    apply measurable_pi_lambda
    intro i
    split_ifs <;> fun_prop
  have hV : ∀ J, Measurable (V J) := fun J =>
    (hW J.val).comp (measurable_pi_iff.mpr fun i => S.meas i)
  have hsplit : ∀ J, IndepFun R (fun a => (T J a, V J a)) μ := by
    intro J
    let transform (o : Fin n → Obs X Z) :=
      ((J.val, fun i : Fin n => if i.val ∈ J.val then
        (Sum.inr (o i) : Unit ⊕ Obs X Z) else Sum.inl ()), W J.val o)
    have ht : Measurable transform := by
      first | fun_prop | skip
      apply Measurable.prodMk _ (hW J.val)
      apply measurable_const.prodMk
      apply measurable_pi_lambda
      intro i
      split_ifs <;> fun_prop
    exact (hSplit n hn heven).2.2.2.2.comp (measurable_of_countable select) ht
  have hind := dml_finite_split_training_evaluation_indep μ P R T V hR hT hV
    hsplit (fun J => hfixed J.val J.property) (fun J => hlaw J.val J.property)
  have hselected := hind.comp measurable_snd measurable_id
  have hmask : ∀ᵐ a ∂μ, (R a).val = I₁ n a := by
    filter_upwards [hvalid] with a ha
    simp only [R, select, dif_pos ha]
  have heval : (fun a => V (R a) a) =ᵐ[μ]
      (fun a => W (I₁ n a) (fun i => S.Z i a)) := by
    filter_upwards [hmask] with a ha
    simp only [V, ha]
  refine ⟨?_, ?_⟩
  · apply hselected.congr
    · filter_upwards [hmask] with a ha
      simp only [Function.comp_def, T, trainingView, ha]
    · simpa only [Function.comp_def, id_eq] using heval
  · rw [← Measure.map_congr heval]
    exact dml_finite_independent_selection_law μ P R V hR hV
      (fun J => (hsplit J).comp measurable_id measurable_snd)
      (fun J => hlaw J.val J.property)

-- A split-determined index in the evaluation complement is independent of
-- all training records, not merely of the split itself.
-- @node: equalHalfSplit_training_indep_selected_evaluation
/-- For [an equal half split independent of the sample](hyp:hSplit), with
[sample size at least two](hyp:hn) and [even sample size](hyp:heven), if
[the selection rule chooses an index in the evaluation complement of every
half-size training mask](hyp:hr), then [the selected evaluation record is
independent of the entire training view](goal). -/
lemma equalHalfSplit_training_indep_selected_evaluation
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (n : ℕ) (hn : 2 ≤ n) (heven : Even n)
    (r : Finset ℕ → ℕ)
    (hr : ∀ J ∈ (Finset.range n).powersetCard (n / 2),
      r (Finset.range n \ J) ∈ Finset.range n \ J) :
    IndepFun (trainingView M S I₁ n) (fun a => S.Z (r (I₂ n a)) a) μ := by
  classical
  let : NeZero n := ⟨by omega⟩
  let W (J : Finset ℕ) (o : Fin n → Obs X Z) :=
    o (Fin.ofNat n (r (Finset.range n \ J)))
  have hindex (J : Finset ℕ) (hJ : J ∈ (Finset.range n).powersetCard (n / 2)) :
      (Fin.ofNat n (r (Finset.range n \ J))).val = r (Finset.range n \ J) := by
    exact Nat.mod_eq_of_lt (Finset.mem_range.mp (Finset.mem_sdiff.mp (hr J hJ)).1)
  have hfixed (J : Finset ℕ) (hJ : J ∈ (Finset.range n).powersetCard (n / 2)) :
      IndepFun (fun a => (J, fun i : Fin n =>
        if i.val ∈ J then (Sum.inr (S.Z i a) : Unit ⊕ Obs X Z) else Sum.inl ()))
        (fun a => W J (fun i => S.Z i a)) μ := by
    have hJE : Disjoint J {r (Finset.range n \ J)} := by
      simp only [Finset.disjoint_singleton_right]
      exact (Finset.mem_sdiff.mp (hr J hJ)).2
    have h := (dml_fixed_masked_training_indep_evaluation M μ S n J
      {r (Finset.range n \ J)} hJE).comp measurable_id
        (measurable_pi_apply ⟨r (Finset.range n \ J), Finset.mem_singleton_self _⟩)
    simpa only [Function.comp_def, id_eq, W, hindex J hJ] using h
  have hlaw (J : Finset ℕ) (hJ : J ∈ (Finset.range n).powersetCard (n / 2)) :
      μ.map (fun a => W J (fun i => S.Z i a)) = observationLaw M := by
    simpa only [W, hindex J hJ] using S.map_eq (r (Finset.range n \ J))
  have hind := dml_random_training_indep_of_fixed_laws M μ S I₁ I₂ hSplit n hn heven
    (observationLaw M) W (fun J => measurable_pi_apply _) hfixed hlaw
  apply hind.1.congr (Filter.Eventually.of_forall fun _ => rfl)
  filter_upwards [equalHalfSplit_evaluation_complement_ae M μ S I₁ I₂ hSplit n hn heven,
      (hSplit n hn heven).1] with a ha hs
  have hJ : I₁ n a ∈ (Finset.range n).powersetCard (n / 2) := by
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_, hs.2.2.1⟩
    intro i hi
    rw [← hs.2.1]
    exact Finset.mem_union_left _ hi
  simp only [W, hindex _ hJ, ha]

-- The pair law is unchanged by the random split. This is the joint
-- independence input used to remove conditional cross moments of fitted scores.
-- @node: equalHalfSplit_training_indep_selected_evaluation_pair
/-- For [an equal half split independent of the sample](hyp:hSplit), with
[at least two observations](hyp:hn) and [even sample size](hyp:heven), suppose
[the first rule selects an evaluation index](hyp:hr₁), [the second rule selects
an evaluation index](hyp:hr₂), and [the selected indices differ for every
half-size training mask](hyp:hne). Then [the selected pair is independent of
the training view and has the product of two population observation laws](goal). -/
lemma equalHalfSplit_training_indep_selected_evaluation_pair
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (n : ℕ) (hn : 2 ≤ n) (heven : Even n)
    (r₁ r₂ : Finset ℕ → ℕ)
    (hr₁ : ∀ J ∈ (Finset.range n).powersetCard (n / 2),
      r₁ (Finset.range n \ J) ∈ Finset.range n \ J)
    (hr₂ : ∀ J ∈ (Finset.range n).powersetCard (n / 2),
      r₂ (Finset.range n \ J) ∈ Finset.range n \ J)
    (hne : ∀ J ∈ (Finset.range n).powersetCard (n / 2),
      r₁ (Finset.range n \ J) ≠ r₂ (Finset.range n \ J)) :
    IndepFun (trainingView M S I₁ n)
      (fun a => (S.Z (r₁ (I₂ n a)) a, S.Z (r₂ (I₂ n a)) a)) μ ∧
      μ.map (fun a => (S.Z (r₁ (I₂ n a)) a, S.Z (r₂ (I₂ n a)) a)) =
        (observationLaw M).prod (observationLaw M) := by
  classical
  let : NeZero n := ⟨by omega⟩
  let W (J : Finset ℕ) (o : Fin n → Obs X Z) :=
    (o (Fin.ofNat n (r₁ (Finset.range n \ J))),
      o (Fin.ofNat n (r₂ (Finset.range n \ J))))
  have hindex₁ (J : Finset ℕ) (hJ : J ∈ (Finset.range n).powersetCard (n / 2)) :
      (Fin.ofNat n (r₁ (Finset.range n \ J))).val = r₁ (Finset.range n \ J) :=
    Nat.mod_eq_of_lt (Finset.mem_range.mp (Finset.mem_sdiff.mp (hr₁ J hJ)).1)
  have hindex₂ (J : Finset ℕ) (hJ : J ∈ (Finset.range n).powersetCard (n / 2)) :
      (Fin.ofNat n (r₂ (Finset.range n \ J))).val = r₂ (Finset.range n \ J) :=
    Nat.mod_eq_of_lt (Finset.mem_range.mp (Finset.mem_sdiff.mp (hr₂ J hJ)).1)
  have hW (J : Finset ℕ) : Measurable (W J) := by fun_prop
  have hfixed (J : Finset ℕ) (hJ : J ∈ (Finset.range n).powersetCard (n / 2)) :
      IndepFun (fun a => (J, fun i : Fin n =>
        if i.val ∈ J then (Sum.inr (S.Z i a) : Unit ⊕ Obs X Z) else Sum.inl ()))
        (fun a => W J (fun i => S.Z i a)) μ := by
    let E : Finset ℕ := {r₁ (Finset.range n \ J), r₂ (Finset.range n \ J)}
    have hJE : Disjoint J E := by
      apply Finset.disjoint_left.mpr
      intro i hi he
      simp only [E, Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl
      · exact (Finset.mem_sdiff.mp (hr₁ J hJ)).2 hi
      · exact (Finset.mem_sdiff.mp (hr₂ J hJ)).2 hi
    let i₁ : E := ⟨r₁ (Finset.range n \ J), by simp [E]⟩
    let i₂ : E := ⟨r₂ (Finset.range n \ J), by simp [E]⟩
    have h := (dml_fixed_masked_training_indep_evaluation M μ S n J E hJE).comp
      measurable_id ((measurable_pi_apply i₁).prodMk (measurable_pi_apply i₂))
    simpa only [Function.comp_def, id_eq, W, hindex₁ J hJ, hindex₂ J hJ, i₁, i₂] using h
  have hlaw (J : Finset ℕ) (hJ : J ∈ (Finset.range n).powersetCard (n / 2)) :
      μ.map (fun a => W J (fun i => S.Z i a)) =
        (observationLaw M).prod (observationLaw M) := by
    have h := (S.indep.indepFun (hne J hJ)).map_prod_eq_prod_map_map
      (S.meas _).aemeasurable (S.meas _).aemeasurable
    simpa only [W, hindex₁ J hJ, hindex₂ J hJ, S.map_eq] using h
  have hind := dml_random_training_indep_of_fixed_laws M μ S I₁ I₂ hSplit n hn heven
    ((observationLaw M).prod (observationLaw M)) W hW hfixed hlaw
  have heq : (fun a => W (I₁ n a) (fun i => S.Z i a)) =ᵐ[μ]
      (fun a => (S.Z (r₁ (I₂ n a)) a, S.Z (r₂ (I₂ n a)) a)) := by
    filter_upwards [equalHalfSplit_evaluation_complement_ae M μ S I₁ I₂ hSplit n hn heven,
      (hSplit n hn heven).1] with a ha hs
    have hJ : I₁ n a ∈ (Finset.range n).powersetCard (n / 2) := by
      apply Finset.mem_powersetCard.mpr
      refine ⟨?_, hs.2.2.1⟩
      intro i hi
      rw [← hs.2.1]
      exact Finset.mem_union_left _ hi
    simp only [W, hindex₁ _ hJ, hindex₂ _ hJ, ha]
  refine ⟨hind.1.congr (Filter.Eventually.of_forall fun _ => rfl) heq, ?_⟩
  rw [← Measure.map_congr heq]
  exact hind.2

-- @node: equalHalfSplit_measurable_trainingView
/-- For [an equal half split independent of the sample](hyp:hSplit), at
[sample size at least two](hyp:hn) and [even sample size](hyp:heven),
[the training view, including its mask and revealed records, is measurable](goal). -/
@[fun_prop] lemma equalHalfSplit_measurable_trainingView
    (M : LatentIVModel Ω X Z) (μ : Measure A) (S : ObservedSample M μ)
    (I₁ I₂ : SampleSplit A) (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (n : ℕ) (hn : 2 ≤ n) (heven : Even n) :
    Measurable (trainingView M S I₁ n) := by
  classical
  first | fun_prop | skip
  let mask (J : Finset ℕ) (o : Fin n → Obs X Z) :=
    (J, fun i : Fin n => if i.val ∈ J then (Sum.inr (o i) : Unit ⊕ Obs X Z) else Sum.inl ())
  have hm : Measurable (Function.uncurry mask) := by
    apply measurable_from_prod_countable_right
    intro J
    apply measurable_const.prodMk
    apply measurable_pi_lambda
    intro i
    dsimp only [Prod.fst, Prod.snd]
    split_ifs <;> fun_prop
  exact hm.comp ((hSplit n hn heven).2.1.prodMk
    (measurable_pi_iff.mpr fun i => S.meas i))

-- @node: equalHalfSplit_measurable_selected_evaluation
/-- Under [an equal half split independent of the sample](hyp:hSplit), with
[at least two observations](hyp:hn) and [even sample size](hyp:heven),
[the record indexed by any rule applied to the evaluation mask is measurable](goal). -/
@[fun_prop] lemma equalHalfSplit_measurable_selected_evaluation
    (M : LatentIVModel Ω X Z) (μ : Measure A) (S : ObservedSample M μ)
    (I₁ I₂ : SampleSplit A) (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (n : ℕ) (hn : 2 ≤ n) (heven : Even n) (r : Finset ℕ → ℕ) :
    Measurable (fun a => S.Z (r (I₂ n a)) a) := by
  first | fun_prop | skip
  have hm : Measurable (Function.uncurry S.Z) :=
    measurable_from_prod_countable_right (fun i => S.meas i)
  exact hm.comp (((measurable_of_countable r).comp
    (hSplit n hn heven).2.2.1).prodMk measurable_id)

-- @node: equalHalfSplit_selected_evaluation_pair_indep
/-- Under [an equal half split independent of the sample](hyp:hSplit), with
[at least two observations](hyp:hn) and [even sample size](hyp:heven), if
[the first selection belongs to the evaluation complement](hyp:hr₁),
[the second selection belongs to that complement](hyp:hr₂), and
[the two selections differ for every half-size training mask](hyp:hne), then
[the two selected evaluation records are independent](goal). -/
lemma equalHalfSplit_selected_evaluation_pair_indep
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (n : ℕ) (hn : 2 ≤ n) (heven : Even n)
    (r₁ r₂ : Finset ℕ → ℕ)
    (hr₁ : ∀ J ∈ (Finset.range n).powersetCard (n / 2),
      r₁ (Finset.range n \ J) ∈ Finset.range n \ J)
    (hr₂ : ∀ J ∈ (Finset.range n).powersetCard (n / 2),
      r₂ (Finset.range n \ J) ∈ Finset.range n \ J)
    (hne : ∀ J ∈ (Finset.range n).powersetCard (n / 2),
      r₁ (Finset.range n \ J) ≠ r₂ (Finset.range n \ J)) :
    IndepFun (fun a => S.Z (r₁ (I₂ n a)) a) (fun a => S.Z (r₂ (I₂ n a)) a) μ := by
  have hpair := (equalHalfSplit_training_indep_selected_evaluation_pair M μ S I₁ I₂
    hSplit n hn heven r₁ r₂ hr₁ hr₂ hne).2
  have hmeas₁ := equalHalfSplit_measurable_selected_evaluation M μ S I₁ I₂ hSplit n hn heven r₁
  have hmeas₂ := equalHalfSplit_measurable_selected_evaluation M μ S I₁ I₂ hSplit n hn heven r₂
  apply (indepFun_iff_map_prod_eq_prod_map_map hmeas₁.aemeasurable hmeas₂.aemeasurable).mpr
  have hpop : IsProbabilityMeasure (observationLaw M) := by
    rw [← S.map_eq 0]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  have hmap₁ : μ.map (fun a => S.Z (r₁ (I₂ n a)) a) = observationLaw M := by
    change μ.map (Prod.fst ∘ (fun a => (S.Z (r₁ (I₂ n a)) a, S.Z (r₂ (I₂ n a)) a))) = _
    rw [← Measure.map_map measurable_fst (hmeas₁.prodMk hmeas₂),
      hpair, Measure.map_fst_prod, measure_univ, one_smul]
  have hmap₂ : μ.map (fun a => S.Z (r₂ (I₂ n a)) a) = observationLaw M := by
    change μ.map (Prod.snd ∘ (fun a => (S.Z (r₁ (I₂ n a)) a, S.Z (r₂ (I₂ n a)) a))) = _
    rw [← Measure.map_map measurable_snd (hmeas₁.prodMk hmeas₂),
      hpair, Measure.map_snd_prod, measure_univ, one_smul]
  rw [hpair, hmap₁, hmap₂]

-- The conditional score mean now follows from the actual random-split
-- construction, rather than an assumed training/evaluation independence.
-- @node: equalHalfSplit_fitted_score_condExp
/-- Under [an equal half split independent of the sample](hyp:hSplit), with
[at least two observations](hyp:hn) and [even sample size](hyp:heven), suppose
[the selection rule always chooses an evaluation record](hyp:hr),
[the score is measurable in the training view and the evaluation record](hyp:hf),
and [the resulting fitted score is integrable](hyp:hint). Then [its conditional
expectation given the training view equals, almost surely, its population
integral over a fresh observation with the training view held fixed](goal). -/
lemma equalHalfSplit_fitted_score_condExp
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (n : ℕ) (hn : 2 ≤ n) (heven : Even n)
    (r : Finset ℕ → ℕ)
    (hr : ∀ J ∈ (Finset.range n).powersetCard (n / 2),
      r (Finset.range n \ J) ∈ Finset.range n \ J)
    (f : (Finset ℕ × (Fin n → Unit ⊕ Obs X Z)) × Obs X Z → ℝ)
    (hf : Measurable f)
    (hint : Integrable (fun a => f (trainingView M S I₁ n a, S.Z (r (I₂ n a)) a)) μ) :
    μ[fun a => f (trainingView M S I₁ n a, S.Z (r (I₂ n a)) a) |
      MeasurableSpace.comap (trainingView M S I₁ n) inferInstance] =ᵐ[μ]
      (fun a => ∫ o, f (trainingView M S I₁ n a, o) ∂observationLaw M) := by
  have hbound : ∀ᵐ a ∂μ, r (I₂ n a) < n := by
    filter_upwards [equalHalfSplit_evaluation_complement_ae M μ S I₁ I₂ hSplit n hn heven,
      (hSplit n hn heven).1] with a ha hs
    have hJ : I₁ n a ∈ (Finset.range n).powersetCard (n / 2) := by
      apply Finset.mem_powersetCard.mpr
      refine ⟨?_, hs.2.2.1⟩
      intro i hi
      rw [← hs.2.1]
      exact Finset.mem_union_left _ hi
    rw [ha]
    exact Finset.mem_range.mp (Finset.mem_sdiff.mp (hr _ hJ)).1
  exact dml_independent_fitted_score_condExp μ (observationLaw M)
    (trainingView M S I₁ n) (fun a => S.Z (r (I₂ n a)) a)
    (equalHalfSplit_measurable_trainingView M μ S I₁ I₂ hSplit n hn heven)
    (equalHalfSplit_measurable_selected_evaluation M μ S I₁ I₂ hSplit n hn heven r)
    (equalHalfSplit_training_indep_selected_evaluation M μ S I₁ I₂ hSplit n hn heven r hr)
    (equalHalfSplit_selected_evaluation_law M μ S I₁ I₂ hSplit n hn heven r hbound) f hf hint

end Papers.TbsPrteOptimalTransport

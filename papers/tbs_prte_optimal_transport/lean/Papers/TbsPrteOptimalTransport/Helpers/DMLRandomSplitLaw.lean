module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLRandomSplitEnumeration
public import Mathlib.Probability.Independence.Basic
/-! Marginal laws under a random sample split independent of the observations.
The evaluation half is the complement of the training half almost surely.
Selecting an observation using an independent finite index preserves its law. -/
public section

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set

-- @node: dml_finite_independent_selection_law
/-- If [the finite-valued selection index is measurable](hyp:hR), [each candidate observation is measurable](hyp:hV), [the index is independent of each candidate](hyp:hind), and [all candidates have the same distribution](hyp:hlaw), then [the selected observation has that same distribution](goal). -/
lemma dml_finite_independent_selection_law {A B K : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace K]
    [Fintype K] [MeasurableSingletonClass K]
    (μ : Measure A) [IsProbabilityMeasure μ] (P : Measure B)
    (R : A → K) (V : K → A → B)
    (hR : Measurable R) (hV : ∀ k, Measurable (V k))
    (hind : ∀ k, IndepFun R (V k) μ)
    (hlaw : ∀ k, μ.map (V k) = P) :
    μ.map (fun a => V (R a) a) = P := by
  classical
  have hselected : Measurable (fun a => V (R a) a) := by
    first | fun_prop | skip
    have hu : Measurable (Function.uncurry V) :=
      measurable_from_prod_countable_right (fun k => hV k)
    exact hu.comp (hR.prodMk measurable_id)
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hselected hs]
  have hset : (fun a => V (R a) a) ⁻¹' s =
      ⋃ k, R ⁻¹' {k} ∩ V k ⁻¹' s := by
    ext a
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_singleton_iff]
    constructor
    · intro ha
      exact ⟨R a, rfl, ha⟩
    · rintro ⟨k, hk, ha⟩
      simpa only [hk] using ha
  have hd : Pairwise (fun i j => Disjoint
      (R ⁻¹' {i} ∩ V i ⁻¹' s) (R ⁻¹' {j} ∩ V j ⁻¹' s)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro a ⟨hi, _⟩ ⟨hj, _⟩
    exact hij (hi.symm.trans hj)
  have hmass : ∑ k, μ (R ⁻¹' {k}) = 1 := by
    have hdis : Pairwise (fun i j => Disjoint (R ⁻¹' {i}) (R ⁻¹' {j})) := by
      intro i j hij
      apply Set.disjoint_left.mpr
      intro a hi hj
      exact hij (hi.symm.trans hj)
    have hcover : (⋃ k, R ⁻¹' {k}) = univ := by ext a; simp
    have hm := measure_iUnion (μ := μ) hdis (fun k => hR (measurableSet_singleton k))
    simpa only [hcover, measure_univ, tsum_fintype] using hm.symm
  rw [hset, measure_iUnion hd (fun k =>
    (hR (measurableSet_singleton k)).inter (hV k hs)), tsum_fintype]
  calc
    ∑ k, μ (R ⁻¹' {k} ∩ V k ⁻¹' s) = ∑ k, μ (R ⁻¹' {k}) * P s := by
      apply Finset.sum_congr rfl
      intro k _
      rw [(hind k).measure_inter_preimage_eq_mul _ _ (measurableSet_singleton k) hs]
      rw [← Measure.map_apply (hV k) hs, hlaw k]
    _ = P s := by rw [← Finset.sum_mul, hmass, one_mul]

-- Mixing over an independent random split preserves training/evaluation
-- independence when every fixed split has the same evaluation law.
-- @node: dml_finite_split_training_evaluation_indep
/-- Suppose [the finite-valued split selector is measurable](hyp:hR), [every fixed-split training view is measurable](hyp:hT), and [every fixed-split evaluation block is measurable](hyp:hW). If [the selector is independent of each joint training and evaluation block](hyp:hsplit), [training and evaluation are independent for each fixed split](hyp:hfixed), and [all evaluation blocks have the same law](hyp:hlaw), then [the selected evaluation block is independent of the pair consisting of the selector and the selected training view](goal). -/
lemma dml_finite_split_training_evaluation_indep {A B D K : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace D]
    [MeasurableSpace K] [Fintype K] [MeasurableSingletonClass K]
    (μ : Measure A) [IsProbabilityMeasure μ] (P : Measure B)
    (R : A → K) (T : K → A → D) (W : K → A → B)
    (hR : Measurable R) (hT : ∀ k, Measurable (T k))
    (hW : ∀ k, Measurable (W k))
    (hsplit : ∀ k, IndepFun R (fun a => (T k a, W k a)) μ)
    (hfixed : ∀ k, IndepFun (T k) (W k) μ)
    (hlaw : ∀ k, μ.map (W k) = P) :
    IndepFun (fun a => (R a, T (R a) a)) (fun a => W (R a) a) μ := by
  classical
  have hpartition (U : K → Set A) (hU : ∀ k, MeasurableSet (U k)) :
      μ {a | a ∈ U (R a)} = ∑ k, μ (R ⁻¹' {k} ∩ U k) := by
    have heq : {a | a ∈ U (R a)} = ⋃ k, R ⁻¹' {k} ∩ U k := by
      ext a
      simp only [mem_setOf_eq, mem_iUnion, mem_inter_iff, mem_preimage,
        mem_singleton_iff]
      constructor
      · intro ha
        exact ⟨R a, rfl, ha⟩
      · rintro ⟨k, hk, ha⟩
        simpa only [hk] using ha
    have hd : Pairwise (fun i j => Disjoint
        (R ⁻¹' {i} ∩ U i) (R ⁻¹' {j} ∩ U j)) := by
      intro i j hij
      apply Set.disjoint_left.mpr
      rintro a ⟨hi, _⟩ ⟨hj, _⟩
      exact hij (hi.symm.trans hj)
    rw [heq, measure_iUnion hd (fun k =>
      (hR (measurableSet_singleton k)).inter (hU k)), tsum_fintype]
  have hRW (k : K) : IndepFun R (W k) μ :=
    (hsplit k).comp measurable_id measurable_snd
  have hRT (k : K) : IndepFun R (T k) μ :=
    (hsplit k).comp measurable_id measurable_fst
  have hselected := dml_finite_independent_selection_law μ P R W hR hW hRW hlaw
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t hs ht
  let sk : K → Set D := fun k => (fun d => (k, d)) ⁻¹' s
  have hsk (k : K) : MeasurableSet (sk k) :=
    (measurable_const.prodMk measurable_id) hs
  have hwm : Measurable (fun a => W (R a) a) := by
    first | fun_prop | skip
    have hu : Measurable (Function.uncurry W) :=
      measurable_from_prod_countable_right (fun k => hW k)
    exact hu.comp (hR.prodMk measurable_id)
  have hwt : μ ((fun a => W (R a) a) ⁻¹' t) = P t := by
    rw [← Measure.map_apply hwm ht, hselected]
  have htraining : μ ((fun a => (R a, T (R a) a)) ⁻¹' s) =
      ∑ k, μ (R ⁻¹' {k}) * μ (T k ⁻¹' sk k) := by
    change μ {a | a ∈ T (R a) ⁻¹' sk (R a)} = _
    rw [hpartition _ (fun k => hT k (hsk k))]
    apply Finset.sum_congr rfl
    intro k _
    exact (hRT k).measure_inter_preimage_eq_mul _ _
      (measurableSet_singleton k) (hsk k)
  rw [hwt, htraining]
  change μ {a | a ∈ T (R a) ⁻¹' sk (R a) ∩ W (R a) ⁻¹' t} = _
  rw [hpartition _ (fun k => (hT k (hsk k)).inter (hW k ht)), Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  have hjoint := (hsplit k).measure_inter_preimage_eq_mul {k} (sk k ×ˢ t)
    (measurableSet_singleton k) ((hsk k).prod ht)
  change μ (R ⁻¹' {k} ∩ (T k ⁻¹' sk k ∩ W k ⁻¹' t)) =
    μ (R ⁻¹' {k}) * μ (T k ⁻¹' sk k ∩ W k ⁻¹' t) at hjoint
  rw [hjoint, (hfixed k).measure_inter_preimage_eq_mul _ _ (hsk k) ht,
    ← Measure.map_apply (hW k) ht, hlaw k, mul_assoc]

universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]

-- @node: equalHalfSplit_evaluation_complement_ae
/-- For [an equal half split independent of the sample](hyp:hSplit), at [a sample size of at least two](hyp:hn) that [is even](hyp:heven), [the evaluation set is almost surely the complement of the training set among the first observations of that sample size](goal). -/
lemma equalHalfSplit_evaluation_complement_ae
    (M : LatentIVModel Ω X Z) (μ : Measure A) (S : ObservedSample M μ)
    (I₁ I₂ : SampleSplit A) (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (n : ℕ) (hn : 2 ≤ n) (heven : Even n) :
    I₂ n =ᵐ[μ] (fun a => Finset.range n \ I₁ n a) := by
  classical
  filter_upwards [(hSplit n hn heven).1] with a ha
  ext i
  simp only [Finset.mem_sdiff]
  constructor
  · intro hi
    refine ⟨?_, ?_⟩
    · rw [← ha.2.1]
      exact Finset.mem_union_right _ hi
    · intro hi₁
      exact Finset.disjoint_left.mp ha.1 hi₁ hi
  · rintro ⟨hi, hi₁⟩
    rw [← ha.2.1] at hi
    exact (Finset.mem_union.mp hi).resolve_left hi₁

-- @node: equalHalfSplit_evaluation_indep_sample
/-- Under [an equal half split independent of the sample](hyp:hSplit), for [a sample size of at least two](hyp:hn) that [is even](hyp:heven), [the evaluation index set is independent of the entire finite sample](goal). -/
lemma equalHalfSplit_evaluation_indep_sample
    (M : LatentIVModel Ω X Z) (μ : Measure A) (S : ObservedSample M μ)
    (I₁ I₂ : SampleSplit A) (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (n : ℕ) (hn : 2 ≤ n) (heven : Even n) :
    IndepFun (I₂ n) (fun a => fun i : Fin n => S.Z i a) μ := by
  classical
  have hm : Measurable (fun J : Finset ℕ => Finset.range n \ J) := by
    fun_prop
  have hind := (hSplit n hn heven).2.2.2.2.comp hm measurable_id
  exact hind.congr
    (equalHalfSplit_evaluation_complement_ae M μ S I₁ I₂ hSplit n hn heven).symm
    (Filter.Eventually.of_forall fun _ => rfl)

-- An index may depend on the random evaluation set, but never on its
-- observations. Independence of the split and the finite sample is used
-- before mixing the identical coordinate laws.
-- @node: equalHalfSplit_selected_evaluation_law
/-- Under [an equal half split independent of the sample](hyp:hSplit), at [a sample size of at least two](hyp:hn) that [is even](hyp:heven), suppose [an index chosen as a function of the evaluation set is almost surely below the sample size](hyp:hr). Then [the observation at that index has the population observation law](goal). -/
lemma equalHalfSplit_selected_evaluation_law
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (n : ℕ) (hn : 2 ≤ n) (heven : Even n)
    (r : Finset ℕ → ℕ) (hr : ∀ᵐ a ∂μ, r (I₂ n a) < n) :
    μ.map (fun a => S.Z (r (I₂ n a)) a) = observationLaw M := by
  classical
  have hn0 : n ≠ 0 := by omega
  letI : NeZero n := ⟨hn0⟩
  let R : A → Fin n := fun a => Fin.ofNat n (r (I₂ n a))
  have hR : Measurable R := by
    first | fun_prop | skip
    have hf : Measurable (fun J : Finset ℕ => Fin.ofNat n (r J)) :=
      measurable_of_countable _
    exact hf.comp (hSplit n hn heven).2.2.1
  have hind : ∀ i : Fin n, IndepFun R (S.Z i) μ := by
    intro i
    have hf : Measurable (fun J : Finset ℕ => Fin.ofNat n (r J)) :=
      measurable_of_countable _
    exact (equalHalfSplit_evaluation_indep_sample M μ S I₁ I₂ hSplit n hn heven).comp
      hf (measurable_pi_apply i)
  have hlaw := dml_finite_independent_selection_law μ (observationLaw M) R
    (fun i : Fin n => S.Z i) hR (fun i => S.meas i) hind (fun i => S.map_eq i)
  have heq : (fun a => S.Z (R a) a) =ᵐ[μ]
      (fun a => S.Z (r (I₂ n a)) a) := by
    filter_upwards [hr] with a ha
    simp only [R, Fin.val_ofNat, Nat.mod_eq_of_lt ha]
  rw [← Measure.map_congr heq]
  exact hlaw

-- Holding the split fixed, the masked training view uses only the
-- coordinates in J. The IID family makes it independent of every
-- disjoint evaluation block, including a pair of evaluation records.
-- @node: dml_fixed_masked_training_indep_evaluation
/-- If [the fixed training and evaluation index sets are disjoint](hyp:hJE), then [the training set together with the first observations masked outside that set is independent of the observations indexed by the evaluation set](goal). -/
lemma dml_fixed_masked_training_indep_evaluation
    (M : LatentIVModel Ω X Z) (μ : Measure A) (S : ObservedSample M μ)
    (n : ℕ) (J E : Finset ℕ) (hJE : Disjoint J E) :
    IndepFun
      (fun a => (J, fun i : Fin n =>
        if i.val ∈ J then (Sum.inr (S.Z i a) : Unit ⊕ Obs X Z) else Sum.inl ()))
      (fun a => fun i : E => S.Z i a) μ := by
  classical
  let mask (t : J → Obs X Z) :=
    (J, fun i : Fin n => if hi : i.val ∈ J then
      (Sum.inr (t ⟨i.val, hi⟩) : Unit ⊕ Obs X Z) else Sum.inl ())
  have hm : Measurable mask := by
    first | fun_prop | skip
    apply measurable_const.prodMk
    apply measurable_pi_lambda
    intro i
    split_ifs <;> fun_prop
  have hind := (S.indep.indepFun_finset J E hJE S.meas).comp hm measurable_id
  convert hind using 1
  · funext a
    dsimp only [Function.comp_def, mask]
    congr 1
  · rfl

end Papers.TbsPrteOptimalTransport

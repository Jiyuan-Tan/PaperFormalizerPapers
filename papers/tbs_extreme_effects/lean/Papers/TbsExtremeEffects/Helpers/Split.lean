module
public import Papers.TbsExtremeEffects.Helpers.SplitIndependence

/-! Random relabelling and the equal prefix split. -/

public section
set_option linter.style.haveILetI false
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
variable {q d m : ℕ}

/-- Given [an even sample size](hyp:hn), [each training set and its complement have half the indices, every complementary pair of halves has the uniform probability, and that pair is independent of the raw sample](goal) exactly when it is a uniform random split. -/
-- @node: splitLabeledHalvesUniform_iff
lemma splitLabeledHalvesUniform_iff {W : Type} [MeasurableSpace W] {n : ℕ}
    (P : Measure W) (train : W → Finset (Fin n)) (raw : W → Fin n → Obs q d)
    (hn : EvenSampleSize n) :
    ((∀ w, (train w).card = n / 2 ∧ -- @realizes \mathcal{D}_1(labeled training half of size n/2)
    (train w)ᶜ.card = n / 2 ∧ -- @realizes \mathcal{D}_2(complementary evaluation half of size n/2)
    Disjoint (train w) (train w)ᶜ ∧ train w ∪ (train w)ᶜ = Finset.univ) ∧
  (∀ A B : Finset (Fin n), A.card = n / 2 → B.card = n / 2 →
    Disjoint A B → A ∪ B = Finset.univ →
    P {w | train w = A ∧ (train w)ᶜ = B} = (n.choose (n / 2) : ℝ≥0∞)⁻¹) ∧
  IndepFun (fun w => (train w, (train w)ᶜ)) raw P) ↔ RandomSplitUniform P train raw := by
  classical
  have hhalf : n - n / 2 = n / 2 := by
    obtain ⟨k, hk⟩ := hn.2
    omega
  have hcompl (A : Finset (Fin n)) (hA : A.card = n / 2) : Aᶜ.card = n / 2 := by
    rw [Finset.card_compl, Fintype.card_fin, hA, hhalf]
  constructor
  · rintro ⟨hcard, huniform, hindep⟩
    refine ⟨fun w => (hcard w).1, ?_, ?_⟩
    · intro A hA
      have h := huniform A Aᶜ hA (hcompl A hA)
        (disjoint_compl_right) (Finset.union_compl A)
      simpa only [and_iff_left_of_imp (fun h => congrArg (fun S => Sᶜ) h)] using h
    · simpa only [Function.comp_def, id_eq] using hindep.comp measurable_fst measurable_id
  · rintro ⟨hcard, huniform, hindep⟩
    refine ⟨?_, ?_, ?_⟩
    · intro w
      exact ⟨hcard w, hcompl (train w) (hcard w),
        disjoint_compl_right, Finset.union_compl (train w)⟩
    · intro A B hA hB hdisj hunion
      have hBcompl : Aᶜ = B := by
        apply Finset.ext
        intro i
        have hd := Finset.disjoint_left.mp hdisj
        have hu : i ∈ A ∨ i ∈ B := by
          have : i ∈ A ∪ B := by rw [hunion]; exact Finset.mem_univ i
          exact Finset.mem_union.mp this
        simp only [Finset.mem_compl]
        constructor
        · intro hi
          exact hu.resolve_left hi
        · intro hi hia
          exact hd hia hi
      have hevent : {w | train w = A ∧ (train w)ᶜ = B} = {w | train w = A} := by
        ext w
        exact ⟨fun h => h.1, fun h => ⟨h, by rw [h, hBcompl]⟩⟩
      rw [hevent]
      exact huniform A hA
    · have hpair : Measurable (fun A : Finset (Fin n) => (A, Aᶜ)) := by
        fun_prop
      simpa only [Function.comp_def, id_eq] using hindep.comp hpair measurable_id

/-- For [an even sample size](hyp:hn), [the fixed training and evaluation index sets each contain half the observations](goal). -/
-- @node: equalSplit_cardinality
lemma equalSplit_cardinality (n : ℕ) (hn : EvenSampleSize n) :
    (trainIndices n).card = n / 2 ∧ (evalIndices n).card = n / 2 := by
  classical
  have htrain : (trainIndices n).card = n / 2 := by
    calc
      (trainIndices n).card = (Finset.range (n / 2)).card := by
        apply Finset.card_bij (fun i _ => i.val)
        · intro i hi
          simpa only [trainIndices, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_range] using hi
        · intro i hi j hj hij
          exact Fin.ext hij
        · intro j hj
          have hjhalf : j < n / 2 := Finset.mem_range.mp hj
          have hjn : j < n := lt_of_lt_of_le hjhalf (Nat.div_le_self n 2)
          exact ⟨⟨j, hjn⟩, by simp [trainIndices, hjhalf], rfl⟩
      _ = n / 2 := Finset.card_range _
  have heval : evalIndices n = (trainIndices n)ᶜ := by
    ext i
    simp [evalIndices, trainIndices]
  refine ⟨htrain, ?_⟩
  rw [heval, Finset.card_compl, Fintype.card_fin, htrain]
  obtain ⟨k, hk⟩ := hn.2
  omega

/-- If [the sample size is even](hyp:hn) and [sampling is iid](hyp:hiid), then [the relabelled observations are independent and each has the model's observation distribution](goal). -/
-- @node: relabelled_iid
lemma relabelled_iid (M : ExtremeModel q d) (E : NeteExperiment M) (n : ℕ)
    (hn : EvenSampleSize n) (hiid : IIDSampling E n) :
    iIndepFun (fun i : Fin n => fun w => obs E n w i) E.P ∧
    (∀ i : Fin n, E.P.map (fun w => obs E n w i) = M.mu.map (observation M)) := by
  have hmeas := measurable_obs_tuple M E n
  have hlaw := relabelled_joint_law M E n hn hiid
  have hobs : Measurable (observation M) :=
    M.measurable_X.prodMk (M.measurable_D.prodMk (M.measurable_Y.prodMk M.measurable_U))
  letI : IsProbabilityMeasure (M.mu.map (observation M)) :=
    Measure.isProbabilityMeasure_map hobs.aemeasurable
  have hmarg (i : Fin n) :
      E.P.map (fun w => obs E n w i) = M.mu.map (observation M) := by
    calc
      E.P.map (fun w => obs E n w i) =
          (E.P.map (fun w => obs E n w)).map (fun z => z i) :=
        (Measure.map_map (measurable_pi_apply i) hmeas).symm
      _ = M.mu.map (observation M) := by
        rw [hlaw]
        exact (measurePreserving_eval (fun _ : Fin n => M.mu.map (observation M)) i).map_eq
  refine ⟨?_, hmarg⟩
  apply (iIndepFun_iff_map_fun_eq_pi_map
    (fun i => ((measurable_pi_apply i).comp hmeas).aemeasurable)).mpr
  simpa only [Function.comp_def, hmarg] using hlaw


/-- If [the sample size is even](hyp:hn) and [sampling is iid](hyp:hiid), then [the evaluation tuple is independent of the sigma-algebra generated by the training tuple, split, and auxiliary fitting data](goal). -/
-- @node: evaluation_independent_training
lemma evaluation_independent_training (M : ExtremeModel q d) (E : NeteExperiment M)
    (n : ℕ) (hn : EvenSampleSize n) (hiid : IIDSampling E n) :
    Indep (trainSigma E n)
      (MeasurableSpace.comap
        (fun w (i : Fin n) => if n / 2 ≤ i.val then obs E n w i else (0, false, 0, 0))
        inferInstance) E.P := by
  classical
  let ν := M.mu.map (observation M)
  have hobs : Measurable (observation M) :=
    M.measurable_X.prodMk (M.measurable_D.prodMk (M.measurable_Y.prodMk M.measurable_U))
  let : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hobs.aemeasurable
  let S := fun w => (E.trainSet n w, E.aux w)
  let Z := fun w => obs E n w
  let T : (Fin n → Obs q d) → Fin n → Obs q d :=
    fun z i => if i.val < n / 2 then z i else (0, false, 0, 0)
  let V : (Fin n → Obs q d) → Fin n → Obs q d :=
    fun z i => if n / 2 ≤ i.val then z i else (0, false, 0, 0)
  have hS : Measurable S := (E.measurable_train n).prodMk E.measurable_aux
  have hZ : Measurable Z := measurable_obs_tuple M E n
  have hT : Measurable T := by
    apply measurable_pi_lambda
    intro i
    by_cases hi : i.val < n / 2 <;> simp only [T, hi, ↓reduceIte] <;> fun_prop
  have hV : Measurable V := by
    apply measurable_pi_lambda
    intro i
    by_cases hi : n / 2 ≤ i.val <;> simp only [V, hi, ↓reduceIte] <;> fun_prop
  have hSZ : IndepFun S Z E.P := by
    let : IsProbabilityMeasure (E.P.map S) := Measure.isProbabilityMeasure_map hS.aemeasurable
    exact split_indep_of_product_law E.P S Z hS hZ _ _
      (split_relabelled_joint_law M E n hn hiid)
  have hTV : IndepFun T V (E.P.map Z) := by
    rw [show E.P.map Z = Measure.pi (fun _ : Fin n => ν) from
      relabelled_joint_law M E n hn hiid]
    have h := split_mask_indep (Measure.pi (fun _ : Fin n => ν))
      (fun i z => z i) (fun i => measurable_pi_apply i)
      (iIndepFun_pi (fun _ => measurable_id.aemeasurable))
      (trainIndices n) (0, false, 0, 0)
    simpa only [trainIndices, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_compl, not_lt, T, V] using h
  have h := split_pair_indep E.P S Z T V hS hZ hT hV hSZ hTV
  have hswap : Measurable (fun z : (Finset (Fin n) × E.Aux) × (Fin n → Obs q d) =>
      (z.2, z.1)) := by fun_prop
  have hfinal := h.comp hswap measurable_id
  exact (IndepFun_iff_Indep _ _ E.P).mp hfinal

end Papers.TbsExtremeEffects

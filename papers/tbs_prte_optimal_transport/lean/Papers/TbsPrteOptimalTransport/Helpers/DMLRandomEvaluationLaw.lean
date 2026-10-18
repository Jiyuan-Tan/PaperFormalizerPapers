module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLRandomEvaluationMoments
public import Causalean.Stat.CLT.AsymptoticLinearity
/-! The full held-out row has the IID product law, even when the split is random.
Mixing over independent training masks preserves the joint evaluation law and
independence from the training view. This supplies joint, rather than merely
pairwise, independence for the oracle central limit theorem. -/
public section

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set

universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]

-- @node: equalHalfSplit_evaluation_row_law
/-- Under [an equal half split independent of the sample](hyp:hSplit), [the enumerated evaluation row is independent of the training view and has the product of the population observation laws, with evaluation size one more than the given index and total sample size twice that](goal). -/
lemma equalHalfSplit_evaluation_row_law
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂) (n : ℕ) :
    IndepFun (trainingView M S I₁ (2 * (n + 1)))
      (fun a i => S.Z (dmlEvaluationIndex n (I₂ (2 * (n + 1)) a) i) a) μ ∧
    μ.map (fun a i => S.Z (dmlEvaluationIndex n (I₂ (2 * (n + 1)) a) i) a) =
      Measure.pi (fun _ : Fin (n + 1) => observationLaw M) := by
  classical
  let N := 2 * (n + 1)
  let : NeZero N := ⟨by dsimp [N]; omega⟩
  have hn : 2 ≤ N := by dsimp [N]; omega
  have heven : Even N := ⟨n + 1, by dsimp [N]; omega⟩
  have hc (J : Finset ℕ) (hJ : J ∈ (Finset.range N).powersetCard (N / 2)) :
      (Finset.range N \ J).card = n + 1 := by
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hJ
    rw [Finset.card_sdiff_of_subset hsub, Finset.card_range, hcard]
    dsimp [N]
    omega
  let r (J : Finset ℕ) := dmlEvaluationIndex n (Finset.range N \ J)
  have hr (J : Finset ℕ) (hJ : J ∈ (Finset.range N).powersetCard (N / 2))
      (i : Fin (n + 1)) : r J i ∈ Finset.range N \ J :=
    dmlEvaluationIndex_mem n _ (hc J hJ) i
  have hindex (J : Finset ℕ) (hJ : J ∈ (Finset.range N).powersetCard (N / 2))
      (i : Fin (n + 1)) : (Fin.ofNat N (r J i)).val = r J i :=
    Nat.mod_eq_of_lt (Finset.mem_range.mp (Finset.mem_sdiff.mp (hr J hJ i)).1)
  let W (J : Finset ℕ) (o : Fin N → Obs X Z) :=
    fun i : Fin (n + 1) => o (Fin.ofNat N (r J i))
  have hW (J : Finset ℕ) : Measurable (W J) := by fun_prop
  have hfixed (J : Finset ℕ) (hJ : J ∈ (Finset.range N).powersetCard (N / 2)) :
      IndepFun (fun a => (J, fun i : Fin N =>
        if i.val ∈ J then (Sum.inr (S.Z i a) : Unit ⊕ Obs X Z) else Sum.inl ()))
        (fun a => W J (fun i => S.Z i a)) μ := by
    let E := Finset.range N \ J
    have hJE : Disjoint J E := by
      apply Finset.disjoint_left.mpr
      intro i hi he
      exact (Finset.mem_sdiff.mp he).2 hi
    let select (o : E → Obs X Z) := fun i : Fin (n + 1) => o ⟨r J i, hr J hJ i⟩
    have hs : Measurable select := by fun_prop
    have hind := (dml_fixed_masked_training_indep_evaluation M μ S N J E hJE).comp
      measurable_id hs
    simpa only [Function.comp_def, id_eq, W, hindex J hJ, select] using hind
  have hlaw (J : Finset ℕ) (hJ : J ∈ (Finset.range N).powersetCard (N / 2)) :
      μ.map (fun a => W J (fun i => S.Z i a)) =
        Measure.pi (fun _ : Fin (n + 1) => observationLaw M) := by
    have hinj : Function.Injective (r J) :=
      (dmlEvaluationIndex_enumerates n _ (hc J hJ)).1
    have hind := S.indep.precomp hinj
    have hm := hind.map_fun_eq_pi_map (fun i => (S.meas (r J i)).aemeasurable)
    simpa only [W, hindex J hJ, S.map_eq] using hm
  have hmix := dml_random_training_indep_of_fixed_laws M μ S I₁ I₂ hSplit N hn heven
    (Measure.pi (fun _ : Fin (n + 1) => observationLaw M)) W hW hfixed hlaw
  have heq : (fun a => W (I₁ N a) (fun i => S.Z i a)) =ᵐ[μ]
      (fun a i => S.Z (dmlEvaluationIndex n (I₂ N a) i) a) := by
    filter_upwards [equalHalfSplit_evaluation_complement_ae M μ S I₁ I₂ hSplit N hn heven,
      (hSplit N hn heven).1] with a ha hs
    have hJ : I₁ N a ∈ (Finset.range N).powersetCard (N / 2) := by
      apply Finset.mem_powersetCard.mpr
      refine ⟨?_, hs.2.2.1⟩
      intro i hi
      rw [← hs.2.1]
      exact Finset.mem_union_left _ hi
    funext i
    simp only [W, hindex _ hJ, r, ha]
  refine ⟨hmix.1.congr (Filter.Eventually.of_forall fun _ => rfl) heq, ?_⟩
  rw [← Measure.map_congr heq]
  exact hmix.2

open Filter
open scoped Topology

-- @node: equalHalfSplit_oracle_normalized_sum_clt
/-- Under [an equal half split independent of the sample](hyp:hSplit), let the oracle score be [measurable](hyp:hg), [have population mean zero](hyp:hmean), and [have an integrable square](hyp:hsq). Then [its sum over the evaluation half, divided by the square root of the evaluation size, converges in distribution to a centered normal law with variance equal to its population second moment](goal). -/
lemma equalHalfSplit_oracle_normalized_sum_clt
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (g : Obs X Z → ℝ) (hg : Measurable g)
    (hmean : ∫ o, g o ∂observationLaw M = 0)
    (hsq : Integrable (fun o => g o ^ 2) (observationLaw M)) :
    Causalean.Stat.Modes.TendstoInLaw (fun _ => μ)
      (fun n a => (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ *
        ∑ i ∈ I₂ (2 * (n + 1)) a, g (S.Z i a)) atTop
      (gaussianReal 0 (Real.toNNReal (∫ o, g o ^ 2 ∂observationLaw M))) := by
  classical
  let U := fun n a => (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ *
    ∑ i : Fin (n + 1), g (S.Z (dmlEvaluationIndex n (I₂ (2 * (n + 1)) a) i) a)
  have hU : ∀ n, Measurable (U n) := by
    intro n
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro i hi
    exact hg.comp ((equalHalfSplit_evaluationIndex_laws M μ S I₁ I₂ hSplit n).2.2.1 i)
  have hmaps (n : ℕ) : μ.map (U n) = μ.map
      (Causalean.Stat.IsAsymLinear.normalizedSum S g (fun m => Finset.range m) (n + 1)) := by
    let transform (o : Fin (n + 1) → Obs X Z) :=
      (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ * ∑ i, g (o i)
    have ht : Measurable transform := by fun_prop
    have hr := (equalHalfSplit_evaluation_row_law M μ S I₁ I₂ hSplit n).2
    have hm := (S.indep.precomp (show Function.Injective (fun i : Fin (n + 1) => i.val)
      from Fin.val_injective)).map_fun_eq_pi_map (fun i : Fin (n + 1) => (S.meas i).aemeasurable)
    simp only [S.map_eq] at hm
    have hrow : Measurable (fun a i =>
        S.Z (dmlEvaluationIndex n (I₂ (2 * (n + 1)) a) i) a) :=
      measurable_pi_iff.mpr ((equalHalfSplit_evaluationIndex_laws M μ S I₁ I₂ hSplit n).2.2.1)
    have hfixed : Measurable (fun a (i : Fin (n + 1)) => S.Z i a) := by fun_prop
    have heq : (fun a => transform (fun i : Fin (n + 1) => S.Z i a)) =
        Causalean.Stat.IsAsymLinear.normalizedSum S g (fun m => Finset.range m) (n + 1) := by
      funext a
      simp only [transform, Causalean.Stat.IsAsymLinear.normalizedSum, Finset.card_range]
      congr 1
      exact Fin.sum_univ_eq_sum_range (fun i => g (S.Z i a)) (n + 1)
    change μ.map (transform ∘ (fun a i =>
      S.Z (dmlEvaluationIndex n (I₂ (2 * (n + 1)) a) i) a)) = _
    rw [← Measure.map_map ht hrow, hr, ← hm, Measure.map_map ht hfixed]
    rw [show transform ∘ (fun a (i : Fin (n + 1)) => S.Z i a) = _ from heq]
  have hclt := S.clt_normalized_sum hg hmean hsq
  have hsub : Tendsto (fun n : ℕ => n + 1) atTop atTop := tendsto_add_atTop_nat 1
  have hlaw : Causalean.Stat.Modes.TendstoInLaw (fun _ => μ) U atTop
      (gaussianReal 0 (Real.toNNReal (∫ o, g o ^ 2 ∂observationLaw M))) := by
    refine ⟨fun n => (hU n).aemeasurable, hclt.aemeasurable_limit, ?_⟩
    apply (hclt.tendsto.comp hsub).congr'
    apply Eventually.of_forall
    intro n
    apply Subtype.ext
    exact (hmaps n).symm
  apply TendstoInDistribution.congr _ (Eventually.of_forall fun _ => rfl) hlaw
  intro n
  filter_upwards [(equalHalfSplit_evaluationIndex_laws M μ S I₁ I₂ hSplit n).1] with a ha
  dsimp only [U]
  congr 1
  calc
    _ = ∑ i ∈ Finset.univ.image (dmlEvaluationIndex n (I₂ (2 * (n + 1)) a)),
        g (S.Z i a) := (Finset.sum_image (fun i hi j hj hij => ha.1 hij)).symm
    _ = _ := by rw [ha.2]

-- @node: equalHalfSplit_oracle_dmlRV_clt
/-- Under [an equal half split independent of the sample](hyp:hSplit), suppose the oracle score is [measurable](hyp:hg), [square integrable under the population observation law](hyp:hLp), and [has population mean equal to the target](hyp:hmean). Then [the oracle DML average minus the target, multiplied by the square root of the evaluation size, converges in distribution to a centered normal law with the score's population variance about the target](goal). -/
lemma equalHalfSplit_oracle_dmlRV_clt
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (truth : Obs X Z → ℝ) (hg : Measurable truth)
    (hLp : MemLp truth 2 (observationLaw M)) (theta : ℝ)
    (hmean : ∫ o, truth o ∂observationLaw M = theta) :
    Causalean.Stat.Modes.TendstoInLaw (fun _ => μ)
      (fun n a => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (dmlRV M S I₂ (fun _ _ o => truth o) (2 * (n + 1)) a - theta)) atTop
      (gaussianReal 0 (Real.toNNReal (populationVariance M truth theta))) := by
  classical
  have : IsProbabilityMeasure (observationLaw M) := by
    rw [← S.map_eq 0]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  have hc : Measurable (fun o => truth o - theta) := by fun_prop
  have hzero : ∫ o, (truth o - theta) ∂observationLaw M = 0 := by
    rw [integral_sub (hLp.integrable (by norm_num)) (integrable_const theta),
      hmean, integral_const]
    simp
  have hsq : Integrable (fun o => (truth o - theta) ^ 2) (observationLaw M) :=
    (memLp_two_iff_integrable_sq hc.aestronglyMeasurable).mp
      (hLp.sub (memLp_const theta))
  have hclt := equalHalfSplit_oracle_normalized_sum_clt M μ S I₁ I₂ hSplit
    (fun o => truth o - theta) hc hzero hsq
  apply TendstoInDistribution.congr _ (Eventually.of_forall fun _ => rfl) hclt
  intro n
  filter_upwards [(hSplit (2 * (n + 1)) (by omega) ⟨n + 1, by omega⟩).1] with a ha
  have hcard : (I₂ (2 * (n + 1)) a).card = n + 1 := by simpa using ha.2.2.2
  have hpos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hne : (I₂ (2 * (n + 1)) a).Nonempty := by
    apply Finset.card_pos.mp
    rw [hcard]
    omega
  have hid := dmlRV_scaled_oracle_decomposition M S I₂
    (fun _ _ o => truth o) truth (2 * (n + 1)) a hne theta 0
    (Real.sqrt ((n + 1 : ℕ) : ℝ))
  simp only [sub_self, Finset.sum_const_zero, mul_zero, add_zero, hcard] at hid
  rw [hid]
  have hs : Real.sqrt ((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ)⁻¹ =
      (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ := by
    have hn : Real.sqrt ((n + 1 : ℕ) : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
    have hnn : ((n + 1 : ℕ) : ℝ) ≠ 0 := hpos.ne'
    field_simp
    exact Real.sq_sqrt hpos.le
  rw [hs]

end Papers.TbsPrteOptimalTransport

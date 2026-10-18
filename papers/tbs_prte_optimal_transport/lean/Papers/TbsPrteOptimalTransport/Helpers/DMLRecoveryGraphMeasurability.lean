module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLProcedure
public import Papers.TbsPrteOptimalTransport.Helpers.DMLRandomTrainingIndependence
public import Papers.TbsPrteOptimalTransport.Helpers.DMLScoreMeasurability
/-! Measurability of the finite recovery graph and its connected components.
A finite relation is a measurable discrete input. Taking its reflexive transitive
closure is therefore measurable without choosing paths or bounding their length.
These facts support the measurable feasible-score transfer in the DML proof. -/
public section
set_option linter.style.openClassical false
set_option maxHeartbeats 1000000

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Set
open scoped Classical

universe v
variable {B : Type*} {Z : Type v} [MeasurableSpace B] [Fintype Z] [DecidableEq Z]

-- @node: measurable_recovery_vertexValue
/-- If [each baseline propensity coordinate is measurable](hyp:hp) and [each policy
propensity coordinate is measurable](hyp:hq), then [the value at any fixed recovery
vertex is measurable](goal). -/
@[fun_prop] lemma measurable_recovery_vertexValue
    (pb qb : B → Z → ℝ) (hp : ∀ z, Measurable (fun b => pb b z))
    (hq : ∀ z, Measurable (fun b => qb b z)) (v : RecoveryVertex Z) :
    Measurable (fun b => vertexValue (pb b) (qb b) v) := by
  unfold vertexValue
  split_ifs <;> fun_prop

-- @node: measurable_recoveryActive
/-- If [each baseline propensity coordinate is measurable](hyp:hp), then [the set
of active recovery vertices at a fixed threshold is measurable](goal). -/
@[fun_prop] lemma measurable_recoveryActive
    (pb : B → Z → ℝ) (hp : ∀ z, Measurable (fun b => pb b z)) (rho : ℝ) :
    Measurable (fun b => recoveryActive (pb b) rho) := by
  try fun_prop
  apply measurable_finset_iff.mpr
  intro v
  simp only [recoveryActive, Finset.mem_filter, Finset.mem_univ, true_and]
  apply measurableSet_setOfPred.mp
  by_cases hv : v.1 = true
  · simp only [hv, true_or]
    exact MeasurableSet.univ
  · simp only [hv, false_or]
    simpa using (measurableSet_lt (measurable_const (a := rho)) (hp v.2))

-- @node: measurable_recoveryEdge
/-- If [each baseline propensity coordinate is measurable](hyp:hp) and [each policy
propensity coordinate is measurable](hyp:hq), then [the presence of a recovery edge
between two fixed vertices is measurable for fixed activity and gap thresholds](goal). -/
@[fun_prop] lemma measurable_recoveryEdge
    (pb qb : B → Z → ℝ) (hp : ∀ z, Measurable (fun b => pb b z))
    (hq : ∀ z, Measurable (fun b => qb b z)) (rho gap : ℝ)
    (v w : RecoveryVertex Z) :
    Measurable (fun b => recoveryEdge (pb b) (qb b) rho gap v w) := by
  try fun_prop
  unfold recoveryEdge
  have ha := measurable_recoveryActive pb hp rho
  have hv := (measurable_finset_mem v).comp ha
  have hw := (measurable_finset_mem w).comp ha
  have hc : Measurable (fun b =>
      |vertexValue (pb b) (qb b) v - vertexValue (pb b) (qb b) w|) := by fun_prop
  exact hv.and (hw.and (measurable_const.and
    (measurableSet_setOfPred.mp (measurableSet_lt hc measurable_const))))

-- @node: measurable_finite_relation_reflTransGen
/-- For a relation on a finite set, if [each pair's relatedness is measurable](hyp:hm),
then [reachability between any two fixed vertices by a finite path, including a
path of length zero, is measurable](goal). -/
@[fun_prop] lemma measurable_finite_relation_reflTransGen
    {V : Type*} [Finite V] (R : B → V → V → Prop)
    (hm : ∀ v w, Measurable (fun b => R b v w)) (v w : V) :
    Measurable (fun b => Relation.ReflTransGen (R b) v w) := by
  have hR : Measurable R :=
    measurable_pi_lambda _ (fun v => measurable_pi_lambda _ (hm v))
  exact (measurable_of_countable
    (fun r : V → V → Prop => Relation.ReflTransGen r v w)).comp hR

-- @node: measurable_recoveryComponent
/-- If [each baseline propensity coordinate is measurable](hyp:hp) and [each policy
propensity coordinate is measurable](hyp:hq), then [the recovery component of a fixed
vertex is measurable for fixed activity and gap thresholds](goal). -/
@[fun_prop] lemma measurable_recoveryComponent
    (pb qb : B → Z → ℝ) (hp : ∀ z, Measurable (fun b => pb b z))
    (hq : ∀ z, Measurable (fun b => qb b z)) (rho gap : ℝ)
    (v : RecoveryVertex Z) :
    Measurable (fun b => recoveryComponent (pb b) (qb b) rho gap v) := by
  try fun_prop
  apply measurable_finset_iff.mpr
  intro w
  simp only [recoveryComponent, Finset.mem_filter]
  exact ((measurable_finset_mem w).comp (measurable_recoveryActive pb hp rho)).and
    (measurable_finite_relation_reflTransGen
      (fun b => recoveryEdge (pb b) (qb b) rho gap)
      (measurable_recoveryEdge pb qb hp hq rho gap) v w)

-- @node: measurable_recovery_componentAverage
/-- If [each baseline propensity coordinate is measurable](hyp:hp) and [each policy
propensity coordinate is measurable](hyp:hq), then [their vertex-value average over
a fixed finite set of recovery vertices is measurable](goal). -/
@[fun_prop] lemma measurable_recovery_componentAverage
    (pb qb : B → Z → ℝ) (hp : ∀ z, Measurable (fun b => pb b z))
    (hq : ∀ z, Measurable (fun b => qb b z)) (C : Finset (RecoveryVertex Z)) :
    Measurable (fun b => componentAverage (pb b) (qb b) C) := by
  unfold componentAverage
  fun_prop

-- @node: measurable_recovery_varying_componentAverage
/-- If [each baseline propensity coordinate is measurable](hyp:hp), [each policy
propensity coordinate is measurable](hyp:hq), and [the finite set of recovery vertices
varies measurably](hyp:hC), then [its vertex-value average is measurable](goal). -/
@[fun_prop] lemma measurable_recovery_varying_componentAverage
    (pb qb : B → Z → ℝ) (hp : ∀ z, Measurable (fun b => pb b z))
    (hq : ∀ z, Measurable (fun b => qb b z))
    (C : B → Finset (RecoveryVertex Z)) (hC : Measurable C) :
    Measurable (fun b => componentAverage (pb b) (qb b) (C b)) := by
  try fun_prop
  have hh : Measurable (fun cb : Finset (RecoveryVertex Z) × B =>
      componentAverage (pb cb.2) (qb cb.2) cb.1) :=
    measurable_from_prod_countable_right
      (fun c => measurable_recovery_componentAverage pb qb hp hq c)
  exact hh.comp (hC.prodMk measurable_id)

-- @node: measurable_finite_list_filter
/-- If [a list of elements of a finite set varies measurably](hyp:hl) and [the Boolean
retention decision for each element is measurable](hyp:hp), then [the filtered list
is measurable when lists carry the discrete sigma algebra](goal). -/
@[fun_prop] lemma measurable_finite_list_filter
    {V : Type*} [Finite V] (l : B → List V) (p : B → V → Bool)
    (hl : @Measurable B (List V) inferInstance ⊤ l)
    (hp : ∀ v, Measurable (fun b => p b v)) :
    @Measurable B (List V) inferInstance ⊤
      (fun b => (l b).filter (p b)) := by
  letI : MeasurableSpace (List V) := ⊤
  have hm : Measurable p := measurable_pi_lambda _ hp
  exact (measurable_of_countable (fun lp : List V × (V → Bool) =>
    lp.1.filter lp.2)).comp (hl.prodMk hm)

-- @node: measurable_recoveryComponents
/-- If [each baseline propensity coordinate is measurable](hyp:hp) and [each policy
propensity coordinate is measurable](hyp:hq), then [the ordered list of recovery
components is measurable in the discrete sigma algebra, for fixed activity and gap
thresholds](goal). -/
@[fun_prop] lemma measurable_recoveryComponents
    (pb qb : B → Z → ℝ) (hp : ∀ z, Measurable (fun b => pb b z))
    (hq : ∀ z, Measurable (fun b => qb b z)) (rho gap : ℝ) :
    @Measurable B (List (Finset (RecoveryVertex Z))) inferInstance ⊤
      (fun b => recoveryComponents (pb b) (qb b) rho gap) := by
  letI : MeasurableSpace (List (Finset (RecoveryVertex Z))) := ⊤
  have hc : Measurable (fun b => (recoveryActive (pb b) rho,
      fun v => recoveryComponent (pb b) (qb b) rho gap v)) :=
    (measurable_recoveryActive pb hp rho).prodMk
      (measurable_pi_lambda _ (measurable_recoveryComponent pb qb hp hq rho gap))
  have hl : Measurable (fun b =>
      ((recoveryActive (pb b) rho).image
        (recoveryComponent (pb b) (qb b) rho gap)).toList) :=
    (measurable_of_countable (fun cf : Finset (RecoveryVertex Z) ×
      (RecoveryVertex Z → Finset (RecoveryVertex Z)) => (cf.1.image cf.2).toList)).comp hc
  have hr : Measurable (fun b => fun C D : Finset (RecoveryVertex Z) =>
      componentAverage (pb b) (qb b) C ≤ componentAverage (pb b) (qb b) D) := by
    apply measurable_pi_lambda
    intro C
    apply measurable_pi_lambda
    intro D
    exact measurableSet_setOfPred.mp (measurableSet_le
      (measurable_recovery_componentAverage pb qb hp hq C)
      (measurable_recovery_componentAverage pb qb hp hq D))
  exact (measurable_of_countable (fun lr : List (Finset (RecoveryVertex Z)) ×
    (Finset (RecoveryVertex Z) → Finset (RecoveryVertex Z) → Prop) =>
      lr.1.mergeSort (fun C D => decide (lr.2 C D)))).comp (hl.prodMk hr)

-- @node: measurable_recoverLevelsAt_labels
/-- If [each baseline propensity coordinate is measurable](hyp:hp) and [each policy
propensity coordinate is measurable](hyp:hq), then [the labels produced by level
recovery at fixed activity and gap thresholds are measurable](goal). -/
@[fun_prop] lemma measurable_recoverLevelsAt_labels
    {X : Type v} (pb qb : B → Z → ℝ)
    (hp : ∀ z, Measurable (fun b => pb b z))
    (hq : ∀ z, Measurable (fun b => qb b z)) (rho gap : ℝ) :
    Measurable (fun b => recoveryLabels
      (recoverLevelsAt (pb b) (qb b) rho gap : LevelData Z X)) := by
  letI : MeasurableSpace (List (Finset (RecoveryVertex Z))) := ⊤
  let Cs := fun b => recoveryComponents (pb b) (qb b) rho gap
  let Bs := fun b => (Cs b).filter (fun C => ∃ z, (false, z) ∈ C)
  have hCs : Measurable Cs := measurable_recoveryComponents pb qb hp hq rho gap
  have hBs : Measurable Bs := (measurable_of_countable
    (fun cs : List (Finset (RecoveryVertex Z)) =>
      cs.filter (fun C => decide (∃ z : Z, (false, z) ∈ C)))).comp hCs
  have hK : Measurable (fun b => (Bs b).length) :=
    (measurable_of_countable List.length).comp hBs
  let p := fun b k => if k = 0 then (0 : ℝ) else if k ≤ (Bs b).length then
    componentAverage (pb b) (qb b) ((Bs b).getD (k - 1) ∅) else 1
  have hp' (k : ℕ) : Measurable (fun b => p b k) := by
    dsimp only [p]
    by_cases hk : k = 0
    · simp only [hk, if_true]
      fun_prop
    · simp only [hk, if_false]
      apply Measurable.ite (measurableSet_le measurable_const hK) _ measurable_const
      apply measurable_recovery_varying_componentAverage pb qb hp hq
      exact (measurable_of_countable
        (fun bs : List (Finset (RecoveryVertex Z)) => bs.getD (k - 1) ∅)).comp hBs
  let Qs := fun b k => (Cs b).filter (fun C =>
    (∃ z, (true, z) ∈ C) ∧ p b k ≤ componentAverage (pb b) (qb b) C ∧
      (if k = (Bs b).length then componentAverage (pb b) (qb b) C ≤ 1
        else componentAverage (pb b) (qb b) C < p b (k + 1)))
  have hQs (k : ℕ) : Measurable (fun b => Qs b k) := by
    change Measurable (fun b => (Cs b).filter (fun C => decide
      ((∃ z, (true, z) ∈ C) ∧ p b k ≤ componentAverage (pb b) (qb b) C ∧
        (if k = (Bs b).length then componentAverage (pb b) (qb b) C ≤ 1
          else componentAverage (pb b) (qb b) C < p b (k + 1)))))
    apply measurable_finite_list_filter Cs _ hCs
    intro C
    have hC := measurable_recovery_componentAverage pb qb hp hq C
    have hlast : Measurable (fun b => if k = (Bs b).length then
        componentAverage (pb b) (qb b) C ≤ 1 else
        componentAverage (pb b) (qb b) C < p b (k + 1)) :=
      Measurable.ite (hK.const_eq k).setOf
        (measurableSet_setOfPred.mp (measurableSet_le hC measurable_const))
        (measurableSet_setOfPred.mp (measurableSet_lt hC (hp' (k + 1))))
    apply measurable_to_bool
    have hh := (measurable_const : Measurable
      (fun _ : B => ∃ z : Z, (true, z) ∈ C)).and
      ((measurableSet_setOfPred.mp (measurableSet_le (hp' k) hC)).and hlast)
    simpa only [Set.preimage, Set.mem_setOf_eq, Set.mem_singleton_iff,
      decide_eq_true_eq] using hh.setOf
  change Measurable (fun b => ((Bs b).length, (fun k => (Qs b k).length),
    (fun k => if k = 0 then Finset.univ.filter (fun z => pb b z ≤ rho) else
      Finset.univ.filter (fun z => (false, z) ∈ (Bs b).getD (k - 1) ∅)),
    (fun k j => if j = 0 ∨ (Qs b k).length < j then ∅ else
      Finset.univ.filter (fun z => (true, z) ∈ (Qs b k).getD (j - 1) ∅))))
  refine hK.prodMk ((measurable_pi_lambda _ (fun k => ?_)).prodMk
    ((measurable_pi_lambda _ (fun k => ?_)).prodMk
      (measurable_pi_lambda _ (fun k => measurable_pi_lambda _ (fun j => ?_)))))
  · exact (measurable_of_countable List.length).comp (hQs k)
  · by_cases hk : k = 0
    · simp only [hk, if_true]
      apply measurable_finset_iff.mpr
      intro z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact measurableSet_setOfPred.mp (measurableSet_le (hp z) measurable_const)
    · simp only [hk, if_false]
      exact (measurable_of_countable
        (fun bs : List (Finset (RecoveryVertex Z)) =>
          Finset.univ.filter (fun z => (false, z) ∈ bs.getD (k - 1) ∅))).comp hBs
  · have hlen := (measurable_of_countable List.length).comp (hQs k)
    apply Measurable.ite _ measurable_const
      ((measurable_of_countable
        (fun qs : List (Finset (RecoveryVertex Z)) =>
          Finset.univ.filter (fun z => (true, z) ∈ qs.getD (j - 1) ∅))).comp (hQs k))
    exact (measurableSet_setOfPred.mpr (measurable_const :
      Measurable (fun _ : B => j = 0))).union (measurableSet_lt hlen measurable_const)

universe u w
variable {Ω : Type u} {X : Type v} {A : Type w}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]

-- The training sigma algebra and the indexed predictor are coupled arguments;
-- `fun_prop` cannot register this rule, so it is called explicitly.
-- @node: equalHalfSplit_training_predictor_joint_measurable
/-- Under [an equal half sample split](hyp:hSplit), a predictor that [is jointly
measurable with respect to the training information and its evaluation argument](hyp:hf)
is [jointly measurable in the sample realization and evaluation argument](goal) at
any [sample size at least two](hyp:hn) that [is even](hyp:heven). -/
lemma equalHalfSplit_training_predictor_joint_measurable
    (M : LatentIVModel Ω X Z) {μ : Measure A}
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    {E : Type*} [MeasurableSpace E] (f : ℕ → A → E → ℝ)
    (hf : TrainingPredictorMeasurable M S I₁ f)
    (n : ℕ) (hn : 2 ≤ n) (heven : Even n) :
    Measurable (fun ae : A × E => f n ae.1 ae.2) := by
  try fun_prop
  obtain ⟨F, hF, heq⟩ := measurable_training_predictor_factorization
    (trainingView M S I₁ n) (f n) (hf n)
  have hv := equalHalfSplit_measurable_trainingView M μ S I₁ I₂ hSplit n hn heven
  simpa only [Function.comp_def, Function.uncurry_apply_pair, ← heq] using
    hF.comp ((hv.comp measurable_fst).prodMk measurable_snd)

-- @node: measurable_pBar_of_joint
/-- If [the evaluation subsample is measurable at the chosen sample size](hyp:hI)
and [the fitted propensity at the fixed instrument value is jointly measurable in
the sample realization and covariates](hyp:hp), then [its average over that evaluation
subsample is measurable in the sample realization](goal). -/
@[fun_prop] lemma measurable_pBar_of_joint
    (M : LatentIVModel Ω X Z) {μ : Measure A} [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₂ : SampleSplit A)
    (pHat : ℕ → A → Z → X → ℝ) (n : ℕ)
    (hI : Measurable (I₂ n)) (z : Z)
    (hp : Measurable (fun ax : A × X => pHat n ax.1 z ax.2)) :
    Measurable (fun a => pBar M S I₂ pHat n a z) := by
  try fun_prop
  have hcard : Measurable (fun a => ((I₂ n a).card : ℝ)) :=
    (measurable_of_countable (fun s : Finset ℕ => (s.card : ℝ))).comp hI
  have hsum : Measurable (fun sa : Finset ℕ × A =>
      ∑ i ∈ sa.1, pHat n sa.2 z (S.Z i sa.2).1) := by
    apply measurable_from_prod_countable_right
    intro s
    exact Finset.measurable_sum s (fun i hi =>
      hp.comp (measurable_id.prodMk (S.meas i).fst))
  exact hcard.inv.mul (hsum.comp (hI.prodMk measurable_id))

-- @node: equalHalfSplit_measurable_recoveredData_labels
/-- Under [an equal half sample split](hyp:hSplit), if [the fitted propensity is
measurable using the training information](hyp:hTrain), [takes values between zero
and one](hyp:hRange), and [the policy transformation is a valid policy map](hyp:hphi),
then [the recovered level labels are measurable](goal) at any [sample size at least
two](hyp:hn) that [is even](hyp:heven). -/
@[fun_prop] lemma equalHalfSplit_measurable_recoveredData_labels
    (M : LatentIVModel Ω X Z) {μ : Measure A} [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (pHat : ℕ → A → Z → X → ℝ)
    (hTrain : TrainingPredictorMeasurable M S I₁
      (fun n a (zx : Z × X) => pHat n a zx.1 zx.2))
    (hRange : ∀ n a z x, pHat n a z x ∈ Icc (0 : ℝ) 1)
    (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (rho : ℕ → ℝ) (gap : ℝ) (n : ℕ) (hn : 2 ≤ n) (heven : Even n) :
    Measurable (fun a => recoveryLabels
      (recoveredData M S I₁ I₂ pHat phi rho gap n a)) := by
  try fun_prop
  have hp := equalHalfSplit_training_predictor_joint_measurable M S I₁ I₂ hSplit
    (fun n a (zx : Z × X) => pHat n a zx.1 zx.2) hTrain n hn heven
  have hq := measurable_fitted_policy_graph phi hphi (pHat n) hp (hRange n)
  have hI := (hSplit n hn heven).2.2.1
  apply measurable_recoverLevelsAt_labels
  · intro z
    exact measurable_pBar_of_joint M S I₂ pHat n hI z
      (hp.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd)))
  · intro z
    exact measurable_pBar_of_joint M S I₂
      (fun n a => policyProp phi (pHat n a)) n hI z
      (hq.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd)))

-- A set-valued conclusion is not a function-property rule for `fun_prop`.
-- @node: equalHalfSplit_measurableSet_recoveryEvent
/-- Under [an equal half sample split](hyp:hSplit), if [the fitted propensity is
measurable using the training information](hyp:hTrain), [takes values between zero
and one](hyp:hRange), and [the policy transformation is a valid policy map](hyp:hphi),
then [the event of exact recovery of the specified level labels is measurable](goal)
at any [sample size at least two](hyp:hn) that [is even](hyp:heven). -/
lemma equalHalfSplit_measurableSet_recoveryEvent
    (M : LatentIVModel Ω X Z) {μ : Measure A} [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (pHat : ℕ → A → Z → X → ℝ)
    (hTrain : TrainingPredictorMeasurable M S I₁
      (fun n a (zx : Z × X) => pHat n a zx.1 zx.2))
    (hRange : ∀ n a z x, pHat n a z x ∈ Icc (0 : ℝ) 1)
    (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (rho : ℕ → ℝ) (gap : ℝ) (L : LevelData Z X)
    (n : ℕ) (hn : 2 ≤ n) (heven : Even n) :
    MeasurableSet (recoveryEvent M S I₁ I₂ pHat phi rho gap L n) := by
  try fun_prop
  have hm := equalHalfSplit_measurable_recoveredData_labels M S I₁ I₂ hSplit
    pHat hTrain hRange phi hphi rho gap n hn heven
  have hk := hm.fst
  have hl := hm.snd.fst
  have hs := hm.snd.snd.fst
  have ht := hm.snd.snd.snd
  unfold recoveryEvent
  apply measurableSet_setOfPred.mpr
  refine (hk.eq_const L.K).and (Measurable.forall (fun k => measurable_const.imp ?_))
  have hlk := (measurable_pi_apply k).comp hl
  have hsk := (measurable_pi_apply k).comp hs
  have htk := (measurable_pi_apply k).comp ht
  refine (hlk.eq_const (L.l k)).and ((hsk.eq_const (L.S k)).and
    (Measurable.forall (fun j => measurable_const.imp ?_)))
  exact ((measurable_pi_apply j).comp htk).eq_const (L.T k j)

end Papers.TbsPrteOptimalTransport

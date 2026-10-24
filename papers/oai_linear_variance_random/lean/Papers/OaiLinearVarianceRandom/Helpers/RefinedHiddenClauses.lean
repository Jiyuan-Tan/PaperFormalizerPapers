module

public import Papers.OaiLinearVarianceRandom.Helpers.HiddenClauses
public import Papers.OaiLinearVarianceRandom.Helpers.MomentLaws
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-! # Hidden clause laws after revealing prefix contents

Coordinatewise coarsenings preserve the product structure on every finite
conditioning fiber. This permits revealing the past ordinary and test contents
without revealing any of the remaining hidden clause contents.
-/

@[expose] public section

noncomputable section
namespace Papers.OaiLinearVarianceRandom
open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {n : ℕ} {Ω : Type} [MeasurableSpace Ω]

open Classical in
/-- Suppose [the clause sequence is independent and uniform](hyp:hlaw), [the fixed coordinate i is positive](hyp:hi), and [every coordinate in T is positive and differs from i](hyp:hT). After fixing clause i to c0 and observing a finite-valued function of each clause in T, [the conditional probability that all coordinates in K equal their prescribed clauses is almost surely the product of the reciprocal numbers of clauses compatible with each observation, with a zero factor whenever a prescribed clause is incompatible](goal). -/
-- @node: fixedClauseMeasure_coarsened_joint_mass
lemma fixedClauseMeasure_coarsened_joint_mass
    {E : Type*} [Finite E] [mE : MeasurableSpace E] [MeasurableSingletonClass E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Cseq : ℕ → Ω → ProperClause n)
    (hlaw : IsUniformClauseProcess μ Cseq) (i : ℕ) (hi : 1 ≤ i)
    (c0 : ProperClause n) (T : Finset ℕ)
    (hT : ∀ j : T, 1 ≤ (j : ℕ) ∧ (j : ℕ) ≠ i)
    (f : T → ProperClause n → E) (K : Finset T) (cs : T → ProperClause n) :
    (fixedClauseMeasure μ Cseq i c0)[
      eventIndicator {ω | ∀ j ∈ K, Cseq j ω = cs j} |
        MeasurableSpace.comap (fun ω j => f j (Cseq j ω)) inferInstance] =ᵐ[
          fixedClauseMeasure μ Cseq i c0]
      fun ω => ∏ j ∈ K, (if f j (cs j) = f j (Cseq j ω) then
        (Fintype.card {c : ProperClause n // f j c = f j (Cseq j ω)} : ℝ)⁻¹
        else 0) := by
  classical
  let Y : Ω → (T → E) := fun ω j => f j (Cseq j ω)
  let ν := fixedClauseMeasure μ Cseq i c0
  have hY : Measurable Y := by
    apply measurable_pi_lambda
    intro j
    exact (measurable_of_finite (f j)).comp (hlaw.1 _ (hT j).1)
  haveI : IsProbabilityMeasure ν := by
    apply cond_isProbabilityMeasure
    change μ (Cseq i ⁻¹' {c0}) ≠ 0
    rw [← Measure.map_apply (hlaw.1 i hi) (measurableSet_singleton c0),
      hlaw.2.2 i hi]
    haveI : Nonempty (ProperClause n) := ⟨c0⟩
    simp [uniformClauseMeasure, uniformOn_univ, Measure.count_singleton,
      ENNReal.div_ne_zero]
  have hmass (sets : T → Set (ProperClause n)) :
      ν {ω | ∀ j : T, Cseq j ω ∈ sets j} =
        ∏ j : T, uniformClauseMeasure n 3 (sets j) :=
    fixedClauseMeasure_joint_mass μ Cseq hlaw i hi c0 T
      (fun j hj => hT ⟨j, hj⟩) sets
  haveI : Nonempty (ProperClause n) := ⟨c0⟩
  haveI : IsProbabilityMeasure (uniformClauseMeasure n 3) := by
    unfold uniformClauseMeasure
    infer_instance
  have hA : MeasurableSet {ω | ∀ j ∈ K, Cseq j ω = cs j} := by
    have hm := MeasurableSet.iInter fun j : T =>
      MeasurableSet.iInter fun _ : j ∈ K =>
        (hlaw.1 j (hT j).1) (measurableSet_singleton (cs j))
    convert hm using 1
    ext ω
    simp
  have hce := condExp_indicator_finite_comap ν Y hY
    {ω | ∀ j ∈ K, Cseq j ω = cs j} hA
  filter_upwards [hce] with ω hω
  rw [show eventIndicator {ω | ∀ j ∈ K, Cseq j ω = cs j} =
    {ω | ∀ j ∈ K, Cseq j ω = cs j}.indicator (fun _ => (1 : ℝ)) by
      ext ω'; simp [eventIndicator, Set.indicator_apply]]
  rw [hω]
  let D : T → Set (ProperClause n) := fun j =>
    {c | f j c = f j (Cseq j ω)}
  let N : T → Set (ProperClause n) := fun j =>
    D j ∩ (if j ∈ K then {cs j} else Set.univ)
  have hden : ν (Y ⁻¹' {Y ω}) = ∏ j : T, uniformClauseMeasure n 3 (D j) := by
    convert hmass D using 1
    congr 1
    ext ω'
    simp [Y, D, funext_iff]
  have hnum : ν (Y ⁻¹' {Y ω} ∩ {ω | ∀ j ∈ K, Cseq j ω = cs j}) =
      ∏ j : T, uniformClauseMeasure n 3 (N j) := by
    convert hmass N using 1
    congr 1
    ext ω'
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
      Set.mem_ofPred_eq, funext_iff, N, D, Y]
    constructor
    · rintro ⟨he, hc⟩ j
      refine ⟨he j, ?_⟩
      by_cases hj : j ∈ K <;> simp [hj, hc]
    · intro h
      refine ⟨fun j => (h j).1, ?_⟩
      intro j hj
      simpa [hj] using (h j).2
  simp only [measureReal_def, hden, hnum, ENNReal.toReal_prod]
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  have hfactor (j : T) :
      ((uniformClauseMeasure n 3 (D j)).toReal)⁻¹ *
        (uniformClauseMeasure n 3 (N j)).toReal =
      if j ∈ K then (if f j (cs j) = f j (Cseq j ω) then
        (Fintype.card {c : ProperClause n //
          f j c = f j (Cseq j ω)} : ℝ)⁻¹ else 0) else 1 := by
    by_cases hj : j ∈ K
    · simp only [hj, if_true, N]
      have h := uniform_cond_fiber_singleton (f j) (Cseq j ω) (cs j)
      simpa only [← Nat.card_eq_fintype_card, uniformClauseMeasure, measureReal_def,
        cond_apply (show MeasurableSet (D j) by trivial), ENNReal.toReal_mul,
        ENNReal.toReal_inv, D] using h
    · simp only [N, hj, if_false, Set.inter_univ]
      apply inv_mul_cancel₀
      have hs : 0 < (uniformClauseMeasure n 3).real {Cseq j ω} := by
        simp [uniformClauseMeasure, measureReal_def, uniformOn_univ,
          Measure.count_singleton]
        exact Fintype.card_pos
      exact ne_of_gt (hs.trans_le (measureReal_mono (by
        intro c hc
        simpa only [Set.mem_singleton_iff] using hc ▸ rfl)))
  simp_rw [hfactor]
  rw [Finset.prod_ite_mem]
  congr 1
  ext j
  simp

open Classical in
/-- For [a reference clause c0](hyp:c0) on [n variables](hyp:n), [a prefix cutoff m](hyp:m), [a coordinate j](hyp:j), and [a clause c at that coordinate](hyp:c), [the prefix observation](goal) records [the root literals of c and its full contents when c is neither ordinary nor a test clause](step:1), together with [its ordinary and test contents when j is at most m, leaving both absent otherwise](step:2). -/
-- @node: testPrefixExposure
def testPrefixExposure (c0 : ProperClause n) (m j : ℕ) (c : ProperClause n) :
    (Finset (Fin n × Bool) × Option (ProperClause n)) ×
      (Option (ProperClause n) × Option (Finset (Fin n × Bool))) :=
  (expose c0 c, (if j ≤ m then ordinaryContents c0 c else none,
    if j ≤ m then testContents c0 c else none))

/-- If [the prefix cutoff m does not exceed the exposure cap](hyp:hm), [the information in the test filtration is exactly the information generated by the prefix observations of all coordinates from one through the cap except the fixed coordinate i](goal). -/
-- @node: testFiltration_eq_comap_prefix
lemma testFiltration_eq_comap_prefix (c0 : ProperClause n)
    (Cseq : ℕ → Ω → ProperClause n) (i m : ℕ) (hm : m ≤ capL n) :
    testFiltration c0 Cseq i m =
      MeasurableSpace.comap
        (fun ω (j : ((Finset.Icc 1 (capL n)).erase i)) =>
          testPrefixExposure c0 m j (Cseq j ω))
        (@MeasurableSpace.pi _ _ fun _ => (⊤ : MeasurableSpace
          (Finset (Fin n × Bool) × Option (ProperClause n))).prod
          ((⊤ : MeasurableSpace (Option (ProperClause n))).prod
            (⊤ : MeasurableSpace (Option (Finset (Fin n × Bool)))))) := by
  classical
  let T := (Finset.Icc 1 (capL n)).erase i
  let J := (Finset.Icc 1 m).erase i
  have hJT : J ⊆ T := by
    intro j hj
    obtain ⟨hne, hj⟩ := Finset.mem_erase.mp hj
    exact Finset.mem_erase.mpr ⟨hne, Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hj).1, (Finset.mem_Icc.mp hj).2.trans hm⟩⟩
  simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup,
    MeasurableSpace.comap_comp, Function.comp_def, testPrefixExposure,
    MeasurableSpace.comap_prodMk, MeasurableSpace.comap_sup]
  unfold testFiltration ordinaryFiltration exposureSigma
  apply le_antisymm
  · apply sup_le
    · apply sup_le
      · apply iSup_le
        intro j
        apply iSup_le
        intro hj
        exact le_iSup_of_le (⟨j, hj⟩ : T) le_sup_left
      · apply iSup_le
        intro j
        apply iSup_le
        intro hj
        have hjm := (Finset.mem_Icc.mp (Finset.mem_erase.mp hj).2).2
        apply le_iSup_of_le (⟨j, hJT hj⟩ : T)
        simpa only [hjm, if_true] using
          (le_sup_of_le_right le_sup_left :
            MeasurableSpace.comap (fun ω => ordinaryContents c0 (Cseq j ω)) ⊤ ≤
              _ ⊔ (MeasurableSpace.comap (fun ω => ordinaryContents c0 (Cseq j ω)) ⊤ ⊔ _))
    · apply iSup_le
      intro j
      apply iSup_le
      intro hj
      have hjm := (Finset.mem_Icc.mp (Finset.mem_erase.mp hj).2).2
      apply le_iSup_of_le (⟨j, hJT hj⟩ : T)
      simpa only [hjm, if_true] using
        (le_sup_of_le_right le_sup_right :
          MeasurableSpace.comap (fun ω => testContents c0 (Cseq j ω)) ⊤ ≤
            _ ⊔ (_ ⊔ MeasurableSpace.comap (fun ω => testContents c0 (Cseq j ω)) ⊤))
  · apply iSup_le
    intro j
    apply sup_le
    · apply le_sup_of_le_left
      apply le_sup_of_le_left
      exact le_iSup_of_le j.val (le_iSup_of_le j.property le_rfl)
    · by_cases hjm : j.val ≤ m
      · have hj : j.val ∈ J := by
          obtain ⟨hne, hj⟩ := Finset.mem_erase.mp j.property
          exact Finset.mem_erase.mpr ⟨hne,
            Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hj).1, hjm⟩⟩
        simp only [hjm, if_true]
        apply sup_le
        · apply le_sup_of_le_left
          apply le_sup_of_le_right
          exact le_iSup_of_le j.val (le_iSup_of_le hj le_rfl)
        · apply le_sup_of_le_right
          exact le_iSup_of_le j.val (le_iSup_of_le hj le_rfl)
      · simp [hjm]

open Classical in
/-- Suppose [the clause sequence is independent and uniform](hyp:hlaw), [the fixed coordinate i is positive](hyp:hi), and [the prefix cutoff m does not exceed the exposure cap](hyp:hm). After fixing clause i to c0, [almost surely, simultaneously for every subset of the other capped coordinates and every prescribed clause family, the conditional probability of those clauses given the test filtration is the product of reciprocal observation-compatible clause counts, with zero factors for incompatible prescriptions](goal). -/
-- @node: test_hidden_clause_conditional_law
lemma test_hidden_clause_conditional_law
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Cseq : ℕ → Ω → ProperClause n)
    (hlaw : IsUniformClauseProcess μ Cseq) (i : ℕ) (hi : 1 ≤ i)
    (c0 : ProperClause n) (m : ℕ) (hm : m ≤ capL n) :
    ∀ᵐ ω ∂(fixedClauseMeasure μ Cseq i c0),
      ∀ (K : Finset ((Finset.Icc 1 (capL n)).erase i))
        (cs : ((Finset.Icc 1 (capL n)).erase i) → ProperClause n),
      ((fixedClauseMeasure μ Cseq i c0)[
        eventIndicator {ω' | ∀ j ∈ K, Cseq j ω' = cs j} |
          testFiltration c0 Cseq i m]) ω =
        ∏ j ∈ K, (if testPrefixExposure c0 m j (cs j) =
            testPrefixExposure c0 m j (Cseq j ω) then
          (Fintype.card {c : ProperClause n // testPrefixExposure c0 m j c =
            testPrefixExposure c0 m j (Cseq j ω)} : ℝ)⁻¹ else 0) := by
  classical
  letI : MeasurableSpace (Finset (Fin n × Bool) × Option (ProperClause n)) := ⊤
  letI : MeasurableSpace (Option (ProperClause n)) := ⊤
  letI : MeasurableSpace (Option (Finset (Fin n × Bool))) := ⊤
  apply ae_all_iff.mpr
  intro K
  apply ae_all_iff.mpr
  intro cs
  rw [testFiltration_eq_comap_prefix c0 Cseq i m hm]
  have h := fixedClauseMeasure_coarsened_joint_mass
    (mE := (⊤ : MeasurableSpace
      (Finset (Fin n × Bool) × Option (ProperClause n))).prod
      ((⊤ : MeasurableSpace (Option (ProperClause n))).prod
        (⊤ : MeasurableSpace (Option (Finset (Fin n × Bool))))))
    μ Cseq hlaw i hi c0 _
    (fun j => ⟨(Finset.mem_Icc.mp (Finset.mem_erase.mp j.property).2).1,
      (Finset.mem_erase.mp j.property).1⟩)
    (fun j => testPrefixExposure c0 m j) K cs
  filter_upwards [h] with ω hω
  convert hω using 1
  simp only [← Nat.card_eq_fintype_card]

/-- If [coordinate j lies after the prefix cutoff m](hyp:hj) and [a is ordinary relative to the reference clause](hyp:ha), [c and a have the same prefix observation exactly when c is also ordinary](goal). -/
-- @node: testPrefixExposure_eq_iff_ordinary
lemma testPrefixExposure_eq_iff_ordinary (c0 a c : ProperClause n)
    (m j : ℕ) (hj : m < j) (ha : isOrdinary c0 a) :
    testPrefixExposure c0 m j c = testPrefixExposure c0 m j a ↔
      isOrdinary c0 c := by
  classical
  have he : expose c0 c = expose c0 a ↔ isOrdinary c0 c := by
    constructor
    · intro h
      exact (congrArg Prod.fst h).trans ha
    · intro hc
      simp [expose, ha, hc, show rootLiterals c0 a = ∅ from ha,
        show rootLiterals c0 c = ∅ from hc]
  simpa only [testPrefixExposure, if_neg (not_le.mpr hj), Prod.mk.injEq,
    and_true] using he

open Classical in
/-- Suppose [the clause sequence is independent and uniform](hyp:hlaw), [the fixed coordinate i is positive](hyp:hi), and [s is at least i and strictly below the exposure cap](hyp:hs). After fixing clause i to c0, [almost surely whenever the next clause is ordinary, its conditional probability given the test filtration through s is the reciprocal of the number of ordinary clauses for each ordinary candidate and zero for every other candidate](goal). -/
-- @node: ordinary_next_clause_conditional_mass
lemma ordinary_next_clause_conditional_mass
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Cseq : ℕ → Ω → ProperClause n)
    (hlaw : IsUniformClauseProcess μ Cseq) (i : ℕ) (hi : 1 ≤ i)
    (c0 : ProperClause n) (s : ℕ) (hs : i ≤ s ∧ s < capL n) :
    ∀ᵐ ω ∂(fixedClauseMeasure μ Cseq i c0),
      isOrdinary c0 (Cseq (s + 1) ω) → ∀ c : ProperClause n,
      ((fixedClauseMeasure μ Cseq i c0)[
        eventIndicator {ω' | Cseq (s + 1) ω' = c} |
          testFiltration c0 Cseq i s]) ω =
        if isOrdinary c0 c then
          (Fintype.card {a : ProperClause n // isOrdinary c0 a} : ℝ)⁻¹ else 0 := by
  classical
  let T := (Finset.Icc 1 (capL n)).erase i
  have hj : s + 1 ∈ T := by
    apply Finset.mem_erase.mpr
    exact ⟨by omega, Finset.mem_Icc.mpr ⟨by omega, hs.2⟩⟩
  let j : T := ⟨s + 1, hj⟩
  filter_upwards [test_hidden_clause_conditional_law μ Cseq hlaw i hi c0 s hs.2.le]
    with ω hω
  intro ho c
  have h := hω {j} (fun _ => c)
  have hevent : {ω' | ∀ k ∈ ({j} : Finset T), Cseq k ω' = c} =
      {ω' | Cseq (s + 1) ω' = c} := by
    ext ω'
    simp [j]
  rw [hevent] at h
  simp only [Finset.prod_singleton] at h
  have hf (a : ProperClause n) : testPrefixExposure c0 s (s + 1) a =
      testPrefixExposure c0 s (s + 1) (Cseq (s + 1) ω) ↔ isOrdinary c0 a :=
    testPrefixExposure_eq_iff_ordinary c0 _ a s (s + 1) (Nat.lt_succ_self s) ho
  have hc : Fintype.card {a : ProperClause n // testPrefixExposure c0 s (s + 1) a =
      testPrefixExposure c0 s (s + 1) (Cseq (s + 1) ω)} =
      Fintype.card {a : ProperClause n // isOrdinary c0 a} :=
    Fintype.card_congr (Equiv.subtypeEquivRight hf)
  simpa only [j, hf c, hc] using h

open Classical in
/-- Suppose [the clause sequence is independent and uniform](hyp:hlaw), [the fixed coordinate i is positive](hyp:hi), [s is at least i and strictly below the exposure cap](hyp:hs), [each clause's random weight is measurable with respect to the test filtration through s](hyp:hF), and [each weight is integrable under the law fixing clause i to c0](hyp:hFint). Under that fixed-clause law, [almost surely whenever the next clause is ordinary, the conditional expectation of its weight given the test filtration equals the arithmetic average of the current weights over all ordinary clauses](goal). -/
-- @node: ordinary_next_clause_condExp
lemma ordinary_next_clause_condExp
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Cseq : ℕ → Ω → ProperClause n)
    (hlaw : IsUniformClauseProcess μ Cseq) (i : ℕ) (hi : 1 ≤ i)
    (c0 : ProperClause n) (s : ℕ) (hs : i ≤ s ∧ s < capL n)
    (F : ProperClause n → Ω → ℝ)
    (hF : ∀ c, StronglyMeasurable[testFiltration c0 Cseq i s] (F c))
    (hFint : ∀ c, Integrable (F c) (fixedClauseMeasure μ Cseq i c0)) :
    ∀ᵐ ω ∂(fixedClauseMeasure μ Cseq i c0),
      isOrdinary c0 (Cseq (s + 1) ω) →
      ((fixedClauseMeasure μ Cseq i c0)[(fun ω' => F (Cseq (s + 1) ω') ω') |
        testFiltration c0 Cseq i s]) ω =
      (∑ c : ProperClause n, if isOrdinary c0 c then F c ω else 0) /
        Fintype.card {c : ProperClause n // isOrdinary c0 c} := by
  classical
  let ν := fixedClauseMeasure μ Cseq i c0
  haveI : IsProbabilityMeasure ν :=
    fixedClauseMeasure_isProbabilityMeasure μ Cseq hlaw i hi c0
  let I : ProperClause n → Ω → ℝ := fun c =>
    eventIndicator {ω | Cseq (s + 1) ω = c}
  let G : ProperClause n → Ω → ℝ := fun c => F c * I c
  have hset (c : ProperClause n) : MeasurableSet {ω | Cseq (s + 1) ω = c} :=
    (hlaw.1 _ (by omega)) (measurableSet_singleton c)
  have hI (c : ProperClause n) : Integrable (I c) ν := by
    have heq : I c = {ω | Cseq (s + 1) ω = c}.indicator (fun _ => (1 : ℝ)) := by
      ext ω
      simp [I, eventIndicator, Set.indicator_apply]
    rw [heq]
    exact (integrable_const (1 : ℝ)).indicator (hset c)
  have hG (c : ProperClause n) : Integrable (G c) ν := by
    have heq : G c = {ω | Cseq (s + 1) ω = c}.indicator (F c) := by
      ext ω
      simp [G, I, eventIndicator, Set.indicator_apply, mul_ite]
    rw [heq]
    exact (hFint c).indicator (hset c)
  have hdecomp : (fun ω => F (Cseq (s + 1) ω) ω) = ∑ c : ProperClause n, G c := by
    ext ω
    simp [G, I, eventIndicator, mul_ite]
  have hpull : ∀ᵐ ω ∂ν, ∀ c : ProperClause n,
      ν[G c | (testFiltration c0 Cseq i s)] ω =
        F c ω * ν[I c | (testFiltration c0 Cseq i s)] ω := by
    apply ae_all_iff.mpr
    intro c
    exact condExp_mul_of_stronglyMeasurable_left (hF c) (hG c) (hI c)
  have hsum := condExp_finsetSum (μ := ν) (s := Finset.univ)
    (fun c _ => hG c) (testFiltration c0 Cseq i s)
  rw [hdecomp]
  filter_upwards [hsum, hpull,
    ordinary_next_clause_conditional_mass μ Cseq hlaw i hi c0 s hs] with ω hsum hpull hn
  intro ho
  rw [hsum]
  simp only [Finset.sum_apply]
  rw [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c _
  rw [hpull c, hn ho c]
  split_ifs <;> simp

end Papers.OaiLinearVarianceRandom

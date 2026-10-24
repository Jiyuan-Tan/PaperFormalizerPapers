module

public import Papers.OaiLinearVarianceRandom.Helpers.RefinedHiddenClauses

/-! # Independent hidden tests given the ordinary filtration

The finite coordinate observation representing `ordinaryFiltration` reveals
ordinary prefix clauses while retaining the independent test-clause fibers.
-/

@[expose] public section

noncomputable section
namespace Papers.OaiLinearVarianceRandom
open MeasureTheory ProbabilityTheory
open scoped BigOperators


open Classical in
/-- Under the uniform distribution on a finite set, [the probability of an event
within an observation fiber, divided by the probability of that fiber, equals
the fraction of fiber elements belonging to the event](goal). -/
-- @node: uniform_fiber_ratio
lemma uniform_fiber_ratio {A B : Type*} [Fintype A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (f : A → B) (a : A) (s : Set A) :
    ((uniformOn (Set.univ : Set A)).real {x | f x = f a})⁻¹ *
        (uniformOn (Set.univ : Set A)).real ({x | f x = f a} ∩ s) =
      (Fintype.card {x : A // f x = f a ∧ x ∈ s} : ℝ) /
        Fintype.card {x : A // f x = f a} := by
  classical
  have : Nonempty A := ⟨a⟩
  have : Nonempty {x : A // f x = f a} := ⟨⟨a, rfl⟩⟩
  simp only [measureReal_def, uniformOn_univ,
    Measure.count_apply_finite _ (Set.toFinite _), Set.toFinite_toFinset,
    Set.toFinset_card, ENNReal.toReal_div, ENNReal.toReal_natCast]
  have hA : (Fintype.card A : ℝ) ≠ 0 := by positivity
  have hD : (Fintype.card {x : A // f x = f a} : ℝ) ≠ 0 := by positivity
  simp only [← Nat.card_eq_fintype_card]
  change ((Nat.card {x : A // f x = f a} : ℝ) / Nat.card A)⁻¹ *
    ((Nat.card {x : A // f x = f a ∧ x ∈ s} : ℝ) / Nat.card A) = _
  field_simp


open Classical in
/-- If [the clause process consists of independent uniform clauses](hyp:hlaw),
[the fixed coordinate is positive](hyp:hi), and [every observed coordinate is
positive and differs from the fixed coordinate](hyp:hT), then [after fixing that
clause and conditioning on finite coordinate observations, the conditional
probability of any rectangle of clause events is almost surely the product of
the fractions of matching observation fibers satisfying each event](goal). -/
-- @node: fixedClauseMeasure_coarsened_rectangle_mass
lemma fixedClauseMeasure_coarsened_rectangle_mass
    {n : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {E : Type*} [Finite E] [mE : MeasurableSpace E] [MeasurableSingletonClass E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Cseq : ℕ → Ω → ProperClause n)
    (hlaw : IsUniformClauseProcess μ Cseq) (i : ℕ) (hi : 1 ≤ i)
    (c0 : ProperClause n) (T : Finset ℕ)
    (hT : ∀ j : T, 1 ≤ (j : ℕ) ∧ (j : ℕ) ≠ i)
    (f : T → ProperClause n → E) (K : Finset T) (sets : T → Set (ProperClause n)) :
    (fixedClauseMeasure μ Cseq i c0)[
      eventIndicator {ω | ∀ j ∈ K, Cseq j ω ∈ sets j} |
        MeasurableSpace.comap (fun ω j => f j (Cseq j ω)) inferInstance] =ᵐ[
          fixedClauseMeasure μ Cseq i c0]
      fun ω => ∏ j ∈ K,
        (Fintype.card {c : ProperClause n //
          f j c = f j (Cseq j ω) ∧ c ∈ sets j} : ℝ) /
        Fintype.card {c : ProperClause n // f j c = f j (Cseq j ω)} := by
  classical
  let Y : Ω → (T → E) := fun ω j => f j (Cseq j ω)
  let ν := fixedClauseMeasure μ Cseq i c0
  have hY : Measurable Y := by
    apply measurable_pi_lambda
    intro j
    exact (measurable_of_finite (f j)).comp (hlaw.1 _ (hT j).1)
  have : IsProbabilityMeasure ν :=
    fixedClauseMeasure_isProbabilityMeasure μ Cseq hlaw i hi c0
  have hmass (ss : T → Set (ProperClause n)) :
      ν {ω | ∀ j : T, Cseq j ω ∈ ss j} =
        ∏ j : T, uniformClauseMeasure n 3 (ss j) :=
    fixedClauseMeasure_joint_mass μ Cseq hlaw i hi c0 T
      (fun j hj => hT ⟨j, hj⟩) ss
  have : Nonempty (ProperClause n) := ⟨c0⟩
  have : IsProbabilityMeasure (uniformClauseMeasure n 3) := by
    unfold uniformClauseMeasure
    infer_instance
  have hA : MeasurableSet {ω | ∀ j ∈ K, Cseq j ω ∈ sets j} := by
    have hm := MeasurableSet.iInter fun j : T =>
      MeasurableSet.iInter fun _ : j ∈ K => (hlaw.1 j (hT j).1) (by trivial :
        MeasurableSet (sets j))
    convert hm using 1
    ext ω
    simp
  have hce := condExp_indicator_finite_comap ν Y hY
    {ω | ∀ j ∈ K, Cseq j ω ∈ sets j} hA
  filter_upwards [hce] with ω hω
  rw [show eventIndicator {ω | ∀ j ∈ K, Cseq j ω ∈ sets j} =
    {ω | ∀ j ∈ K, Cseq j ω ∈ sets j}.indicator (fun _ => (1 : ℝ)) by
      ext ω'; simp [eventIndicator, Set.indicator_apply]]
  rw [hω]
  let D : T → Set (ProperClause n) := fun j =>
    {c | f j c = f j (Cseq j ω)}
  let N : T → Set (ProperClause n) := fun j =>
    D j ∩ (if j ∈ K then sets j else Set.univ)
  have hden : ν (Y ⁻¹' {Y ω}) = ∏ j : T, uniformClauseMeasure n 3 (D j) := by
    convert hmass D using 1
    congr 1
    ext ω'
    simp [Y, D, funext_iff]
  have hnum : ν (Y ⁻¹' {Y ω} ∩ {ω | ∀ j ∈ K, Cseq j ω ∈ sets j}) =
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
      if j ∈ K then
        (Fintype.card {c : ProperClause n // f j c = f j (Cseq j ω) ∧ c ∈ sets j} : ℝ) /
          Fintype.card {c : ProperClause n // f j c = f j (Cseq j ω)}
        else 1 := by
    by_cases hj : j ∈ K
    · simp only [hj, if_true, N]
      exact uniform_fiber_ratio (f j) (Cseq j ω) (sets j)
    · simp only [N, hj, if_false, Set.inter_univ]
      apply inv_mul_cancel₀
      have hs : 0 < (uniformClauseMeasure n 3).real {Cseq j ω} := by
        simpa [uniformClauseMeasure, measureReal_def, uniformOn_univ] using
          (show 0 < (Fintype.card (ProperClause n) : ℝ) from by positivity)
      exact ne_of_gt (hs.trans_le (measureReal_mono (by
        intro c hc
        simpa only [Set.mem_singleton_iff] using hc ▸ rfl)))
  simp_rw [hfactor]
  rw [Finset.prod_ite_mem]
  congr 1
  ext j
  simp


variable {n : ℕ} {Ω : Type} [MeasurableSpace Ω]

open Classical in
/-- For [a reference clause](hyp:c0) on [a given number of variables](hyp:n),
[a prefix cutoff](hyp:m), [a coordinate index](hyp:j), and [a clause at that
coordinate](hyp:c), the [ordinary prefix observation](goal) records its root
exposure together with its ordinary contents when the coordinate is at most
the cutoff, and no additional contents otherwise. -/
-- @node: ordinaryPrefixExposure
def ordinaryPrefixExposure (c0 : ProperClause n) (m j : ℕ) (c : ProperClause n) :
    (Finset (Fin n × Bool) × Option (ProperClause n)) × Option (ProperClause n) :=
  (expose c0 c, if j ≤ m then ordinaryContents c0 c else none)

omit [MeasurableSpace Ω] in
/-- If [the prefix cutoff is at most the cap](hyp:hm), then [the information in
the ordinary filtration equals the information generated by the ordinary prefix
observations at all positive capped coordinates except the omitted one](goal). -/
-- @node: ordinaryFiltration_eq_comap_prefix
lemma ordinaryFiltration_eq_comap_prefix (c0 : ProperClause n)
    (Cseq : ℕ → Ω → ProperClause n) (i m : ℕ) (hm : m ≤ capL n) :
    ordinaryFiltration c0 Cseq i m =
      MeasurableSpace.comap
        (fun ω (j : ((Finset.Icc 1 (capL n)).erase i)) =>
          ordinaryPrefixExposure c0 m j (Cseq j ω))
        (@MeasurableSpace.pi _ _ fun _ => (⊤ : MeasurableSpace
          (Finset (Fin n × Bool) × Option (ProperClause n))).prod
          (⊤ : MeasurableSpace (Option (ProperClause n)))) := by
  classical
  let T := (Finset.Icc 1 (capL n)).erase i
  let J := (Finset.Icc 1 m).erase i
  have hJT : J ⊆ T := by
    intro j hj
    obtain ⟨hne, hj⟩ := Finset.mem_erase.mp hj
    exact Finset.mem_erase.mpr ⟨hne, Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hj).1, (Finset.mem_Icc.mp hj).2.trans hm⟩⟩
  simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup,
    MeasurableSpace.comap_comp, Function.comp_def, ordinaryPrefixExposure,
    MeasurableSpace.comap_prodMk, MeasurableSpace.comap_sup]
  unfold ordinaryFiltration exposureSigma
  apply le_antisymm
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
        (le_sup_right : MeasurableSpace.comap
          (fun ω => ordinaryContents c0 (Cseq j ω)) ⊤ ≤ _ ⊔ _)
  · apply iSup_le
    intro j
    apply sup_le
    · apply le_sup_of_le_left
      exact le_iSup_of_le j.val (le_iSup_of_le j.property le_rfl)
    · by_cases hjm : j.val ≤ m
      · have hj : j.val ∈ J := by
          obtain ⟨hne, hj⟩ := Finset.mem_erase.mp j.property
          exact Finset.mem_erase.mpr ⟨hne,
            Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hj).1, hjm⟩⟩
        simp only [hjm, if_true]
        apply le_sup_of_le_right
        exact le_iSup_of_le j.val (le_iSup_of_le hj le_rfl)
      · simp [hjm]

open Classical in
/-- If [the clauses are independent and uniform](hyp:hlaw), [the fixed coordinate
is positive](hyp:hi), and [the prefix cutoff is at most the cap](hyp:hm), then
[under the law fixing that clause, almost surely and simultaneously for every
finite family of other capped coordinates and every clause assignment, the
conditional probability of that assignment given the ordinary filtration is
the product of inverse observation-fiber sizes when the observations match,
with a zero factor for each mismatch](goal). -/
-- @node: ordinary_hidden_clause_conditional_law
lemma ordinary_hidden_clause_conditional_law
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Cseq : ℕ → Ω → ProperClause n)
    (hlaw : IsUniformClauseProcess μ Cseq) (i : ℕ) (hi : 1 ≤ i)
    (c0 : ProperClause n) (m : ℕ) (hm : m ≤ capL n) :
    ∀ᵐ ω ∂(fixedClauseMeasure μ Cseq i c0),
      ∀ (K : Finset ((Finset.Icc 1 (capL n)).erase i))
        (cs : ((Finset.Icc 1 (capL n)).erase i) → ProperClause n),
      ((fixedClauseMeasure μ Cseq i c0)[
        eventIndicator {ω' | ∀ j ∈ K, Cseq j ω' = cs j} |
          ordinaryFiltration c0 Cseq i m]) ω =
        ∏ j ∈ K, (if ordinaryPrefixExposure c0 m j (cs j) =
            ordinaryPrefixExposure c0 m j (Cseq j ω) then
          (Fintype.card {c : ProperClause n // ordinaryPrefixExposure c0 m j c =
            ordinaryPrefixExposure c0 m j (Cseq j ω)} : ℝ)⁻¹ else 0) := by
  classical
  let : MeasurableSpace (Finset (Fin n × Bool) × Option (ProperClause n)) := ⊤
  let : MeasurableSpace (Option (ProperClause n)) := ⊤
  apply ae_all_iff.mpr
  intro K
  apply ae_all_iff.mpr
  intro cs
  rw [ordinaryFiltration_eq_comap_prefix c0 Cseq i m hm]
  have h := fixedClauseMeasure_coarsened_joint_mass
    (mE := (⊤ : MeasurableSpace
      (Finset (Fin n × Bool) × Option (ProperClause n))).prod
      (⊤ : MeasurableSpace (Option (ProperClause n))))
    μ Cseq hlaw i hi c0 _
    (fun j => ⟨(Finset.mem_Icc.mp (Finset.mem_erase.mp j.property).2).1,
      (Finset.mem_erase.mp j.property).1⟩)
    (fun j => ordinaryPrefixExposure c0 m j) K cs
  filter_upwards [h] with ω hω
  convert hω using 1
  simp only [← Nat.card_eq_fintype_card]

/-- If [one clause is a test relative to the reference clause](hyp:ha) and
[another clause has exactly the same root literals](hyp:he), then [the other
clause is also a test relative to that reference clause](goal). -/
-- @node: isTest_of_rootLiterals_eq
lemma isTest_of_rootLiterals_eq (c0 a c : ProperClause n)
    (ha : isTest c0 a) (he : rootLiterals c0 c = rootLiterals c0 a) :
    isTest c0 c := by
  simpa only [isTest, he] using ha

/-- If [a clause is a test relative to the reference clause](hyp:hc), then
[it is not ordinary relative to that reference clause](goal). -/
-- @node: isTest_not_isOrdinary
lemma isTest_not_isOrdinary (c0 c : ProperClause n) (hc : isTest c0 c) :
    ¬ isOrdinary c0 c := by
  intro ho
  have h := hc.1
  rw [show rootLiterals c0 c = ∅ from ho] at h
  simp at h

/-- If [the reference observation comes from a test clause](hyp:ha), then
[another clause has the same ordinary prefix observation at the chosen
coordinate if and only if it has the same root literals](goal). -/
-- @node: ordinaryPrefixExposure_eq_iff_test
lemma ordinaryPrefixExposure_eq_iff_test (c0 a c : ProperClause n)
    (m j : ℕ) (ha : isTest c0 a) :
    ordinaryPrefixExposure c0 m j c = ordinaryPrefixExposure c0 m j a ↔
      rootLiterals c0 c = rootLiterals c0 a := by
  classical
  constructor
  · intro h
    exact congrArg (fun e => e.1.1) h
  · intro he
    have hc := isTest_of_rootLiterals_eq c0 a c ha he
    simp [ordinaryPrefixExposure, expose, ordinaryContents, he, ha, hc,
      isTest_not_isOrdinary c0 a ha, isTest_not_isOrdinary c0 c hc]


open Classical in
/-- If [the clause process is independent and uniform](hyp:hlaw), [the fixed
coordinate is positive](hyp:hi), and [the prefix cutoff is at most the cap](hyp:hm),
then [under the law fixing that clause, almost surely every finite family of
observed test coordinates has conditional assignment probabilities given the
ordinary filtration equal to the product of inverse matching root-literal-fiber
sizes, with zero for any root-literal mismatch](goal).

The identity holds simultaneously for all families and assignments, so the
family may be chosen after observing the ordinary information. -/
-- @node: ordinary_test_clauses_conditional_mass
lemma ordinary_test_clauses_conditional_mass
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Cseq : ℕ → Ω → ProperClause n)
    (hlaw : IsUniformClauseProcess μ Cseq) (i : ℕ) (hi : 1 ≤ i)
    (c0 : ProperClause n) (m : ℕ) (hm : m ≤ capL n) :
    ∀ᵐ ω ∂(fixedClauseMeasure μ Cseq i c0),
      ∀ (K : Finset ((Finset.Icc 1 (capL n)).erase i)),
        (∀ j ∈ K, isTest c0 (Cseq j ω)) →
        ∀ cs : ((Finset.Icc 1 (capL n)).erase i) → ProperClause n,
      ((fixedClauseMeasure μ Cseq i c0)[
        eventIndicator {ω' | ∀ j ∈ K, Cseq j ω' = cs j} |
          ordinaryFiltration c0 Cseq i m]) ω =
        ∏ j ∈ K, (if rootLiterals c0 (cs j) = rootLiterals c0 (Cseq j ω) then
          (Fintype.card {c : ProperClause n //
            rootLiterals c0 c = rootLiterals c0 (Cseq j ω)} : ℝ)⁻¹ else 0) := by
  classical
  filter_upwards [ordinary_hidden_clause_conditional_law μ Cseq hlaw i hi c0 m hm]
    with ω hω
  intro K hK cs
  rw [hω K cs]
  apply Finset.prod_congr rfl
  intro j hj
  have hf (c : ProperClause n) :=
    ordinaryPrefixExposure_eq_iff_test c0 (Cseq j ω) c m j (hK j hj)
  simp only [hf]


open Classical in
/-- If [the clauses are independent and uniform](hyp:hlaw), [the fixed coordinate
is positive](hyp:hi), and [the prefix cutoff is at most the cap](hyp:hm), then
[under the law fixing that clause, almost surely and simultaneously for every
finite family of other capped coordinates and every collection of clause
events, the conditional probability that all events occur given the ordinary
filtration equals the product of the event fractions in their matching
ordinary-observation fibers](goal). -/
-- @node: ordinary_hidden_clause_rectangle_law
lemma ordinary_hidden_clause_rectangle_law
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Cseq : ℕ → Ω → ProperClause n)
    (hlaw : IsUniformClauseProcess μ Cseq) (i : ℕ) (hi : 1 ≤ i)
    (c0 : ProperClause n) (m : ℕ) (hm : m ≤ capL n) :
    ∀ᵐ ω ∂(fixedClauseMeasure μ Cseq i c0),
      ∀ (K : Finset ((Finset.Icc 1 (capL n)).erase i))
        (sets : ((Finset.Icc 1 (capL n)).erase i) → Set (ProperClause n)),
      ((fixedClauseMeasure μ Cseq i c0)[
        eventIndicator {ω' | ∀ j ∈ K, Cseq j ω' ∈ sets j} |
          ordinaryFiltration c0 Cseq i m]) ω =
        ∏ j ∈ K,
          (Fintype.card {c : ProperClause n // ordinaryPrefixExposure c0 m j c =
            ordinaryPrefixExposure c0 m j (Cseq j ω) ∧ c ∈ sets j} : ℝ) /
          Fintype.card {c : ProperClause n // ordinaryPrefixExposure c0 m j c =
            ordinaryPrefixExposure c0 m j (Cseq j ω)} := by
  classical
  let : MeasurableSpace (Finset (Fin n × Bool) × Option (ProperClause n)) := ⊤
  let : MeasurableSpace (Option (ProperClause n)) := ⊤
  apply ae_all_iff.mpr
  intro K
  apply ae_all_iff.mpr
  intro sets
  rw [ordinaryFiltration_eq_comap_prefix c0 Cseq i m hm]
  have h := fixedClauseMeasure_coarsened_rectangle_mass
    (mE := (⊤ : MeasurableSpace
      (Finset (Fin n × Bool) × Option (ProperClause n))).prod
      (⊤ : MeasurableSpace (Option (ProperClause n))))
    μ Cseq hlaw i hi c0 _
    (fun j => ⟨(Finset.mem_Icc.mp (Finset.mem_erase.mp j.property).2).1,
      (Finset.mem_erase.mp j.property).1⟩)
    (fun j => ordinaryPrefixExposure c0 m j) K sets
  filter_upwards [h] with ω hω
  exact hω

open Classical in
/-- If [the clauses are independent and uniform](hyp:hlaw), [the fixed coordinate
is positive](hyp:hi), and [the prefix cutoff is at most the cap](hyp:hm), then
[under the law fixing that clause, almost surely every finite family of
observed test coordinates and every collection of clause events has conditional
joint probability given the ordinary filtration equal to the product of event
fractions in the matching single-root-literal fibers](goal). -/
-- @node: ordinary_test_clauses_rectangle_law
lemma ordinary_test_clauses_rectangle_law
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Cseq : ℕ → Ω → ProperClause n)
    (hlaw : IsUniformClauseProcess μ Cseq) (i : ℕ) (hi : 1 ≤ i)
    (c0 : ProperClause n) (m : ℕ) (hm : m ≤ capL n) :
    ∀ᵐ ω ∂(fixedClauseMeasure μ Cseq i c0),
      ∀ (K : Finset ((Finset.Icc 1 (capL n)).erase i)),
        (∀ j ∈ K, isTest c0 (Cseq j ω)) →
        ∀ sets : ((Finset.Icc 1 (capL n)).erase i) → Set (ProperClause n),
      ((fixedClauseMeasure μ Cseq i c0)[
        eventIndicator {ω' | ∀ j ∈ K, Cseq j ω' ∈ sets j} |
          ordinaryFiltration c0 Cseq i m]) ω =
        ∏ j ∈ K,
          (Fintype.card {c : ProperClause n //
            rootLiterals c0 c = rootLiterals c0 (Cseq j ω) ∧ c ∈ sets j} : ℝ) /
          Fintype.card {c : ProperClause n //
            rootLiterals c0 c = rootLiterals c0 (Cseq j ω)} := by
  classical
  filter_upwards [ordinary_hidden_clause_rectangle_law μ Cseq hlaw i hi c0 m hm]
    with ω hω
  intro K hK sets
  rw [hω K sets]
  apply Finset.prod_congr rfl
  intro j hj
  simp only [ordinaryPrefixExposure_eq_iff_test c0 (Cseq j ω) _ m j (hK j hj)]

end Papers.OaiLinearVarianceRandom

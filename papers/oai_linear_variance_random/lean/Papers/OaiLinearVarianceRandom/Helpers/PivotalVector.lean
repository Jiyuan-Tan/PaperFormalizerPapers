module

public import Papers.OaiLinearVarianceRandom.Helpers.TestFamilyBounds

/-! # Pivotality as an event of the finite omitted clause vector

The omitted clause is restored as the fixed clause. Thus the conditional
finite-fiber law applies to pivotality itself, including its empty-solution case.
-/

@[expose] public section

noncomputable section
namespace Papers.OaiLinearVarianceRandom
open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {n : ℕ} {Ω : Type} [MeasurableSpace Ω]

open Classical in
/-- Given [a fixed clause](hyp:c0) on [a given number of variables](hyp:n),
[an omitted index](hyp:i), [clauses at all other positive capped
coordinates](hyp:cs), and [an index to evaluate](hyp:j), the [restored clause
sequence](goal) returns the given coordinate clause inside that capped domain
and the fixed clause elsewhere. -/
-- @node: restoreOmittedVector
def restoreOmittedVector (c0 : ProperClause n) (i : ℕ)
    (cs : ((Finset.Icc 1 (capL n)).erase i) → ProperClause n) (j : ℕ) :
    ProperClause n :=
  if hj : j ∈ (Finset.Icc 1 (capL n)).erase i then cs ⟨j, hj⟩ else c0

open Classical in
/-- [Restoring the omitted coordinate of a finite clause vector returns the
fixed clause](goal). -/
-- @node: restoreOmittedVector_at_omitted
lemma restoreOmittedVector_at_omitted (c0 : ProperClause n) (i : ℕ)
    (cs : ((Finset.Icc 1 (capL n)).erase i) → ProperClause n) :
    restoreOmittedVector c0 i cs i = c0 := by
  simp [restoreOmittedVector]

open Classical in
/-- [At any positive capped coordinate other than the omitted one, the restored
sequence equals the clause supplied by the finite vector](goal). -/
-- @node: restoreOmittedVector_at_coordinate
lemma restoreOmittedVector_at_coordinate (c0 : ProperClause n) (i : ℕ)
    (cs : ((Finset.Icc 1 (capL n)).erase i) → ProperClause n)
    (j : ((Finset.Icc 1 (capL n)).erase i)) :
    restoreOmittedVector c0 i cs j = cs j := by
  simp [restoreOmittedVector, j.property]

open Classical in
/-- If [two realized clause sequences agree at the omitted coordinate](hyp:hi)
and [agree at every other positive coordinate through the prefix cutoff](hyp:hc),
then [the omitted clause is pivotal for one sequence if and only if it is
pivotal for the other](goal). -/
-- @node: pivotalEvent_congr_prefix
lemma pivotalEvent_congr_prefix {Ω' : Type} [MeasurableSpace Ω']
    (Cseq : ℕ → Ω → ProperClause n) (Dseq : ℕ → Ω' → ProperClause n)
    (i m : ℕ) (ω : Ω) (ω' : Ω') (hi : Cseq i ω = Dseq i ω')
    (hc : ∀ j ∈ (Finset.Icc 1 m).erase i, Cseq j ω = Dseq j ω') :
    ω ∈ pivotalEvent Cseq i m ↔ ω' ∈ pivotalEvent Dseq i m := by
  have hs (z : Fin n → Bool) :
      (∀ j ∈ Finset.Icc 1 m, j ≠ i → ClauseSat (Cseq j ω) z) ↔
      (∀ j ∈ Finset.Icc 1 m, j ≠ i → ClauseSat (Dseq j ω') z) := by
    constructor <;> intro h j hj hji
    · rw [← hc j (Finset.mem_erase.mpr ⟨hji, hj⟩)]
      exact h j hj hji
    · rw [hc j (Finset.mem_erase.mpr ⟨hji, hj⟩)]
      exact h j hj hji
  simp only [pivotalEvent, Set.mem_ofPred_eq, omittedPrefixSat, hs, hi]

open Classical in
/-- For [a fixed clause](hyp:c0) on [a given number of variables](hyp:n),
[an omitted coordinate](hyp:i), and [a prefix cutoff](hyp:m), the [finite
pivotality event](goal) consists of clause vectors whose restored sequence has
a satisfiable prefix after omission but an unsatisfiable prefix when the fixed
clause is added. -/
-- @node: pivotalVectorEvent
def pivotalVectorEvent (c0 : ProperClause n) (i m : ℕ) :
    Set (((Finset.Icc 1 (capL n)).erase i) → ProperClause n) :=
  {cs | () ∈ pivotalEvent (fun j (_ : Unit) => restoreOmittedVector c0 i cs j) i m}

open Classical in
/-- If [the prefix cutoff is at most the cap](hyp:hm) and [the realized omitted
clause equals the fixed clause](hyp:hfixed), then [the realized finite vector
belongs to the finite pivotality event if and only if the omitted clause is
pivotal for the original sequence](goal). -/
-- @node: pivotalVectorEvent_iff
lemma pivotalVectorEvent_iff (c0 : ProperClause n)
    (Cseq : ℕ → Ω → ProperClause n) (i m : ℕ) (hm : m ≤ capL n)
    (ω : Ω) (hfixed : Cseq i ω = c0) :
    (fun j : ((Finset.Icc 1 (capL n)).erase i) => Cseq j ω) ∈
      pivotalVectorEvent c0 i m ↔ ω ∈ pivotalEvent Cseq i m := by
  apply (pivotalEvent_congr_prefix Cseq
    (fun j (_ : Unit) => restoreOmittedVector c0 i (fun j => Cseq j ω) j)
    i m ω () ?_ ?_).symm
  · simpa only [restoreOmittedVector_at_omitted] using hfixed
  · intro j hj
    obtain ⟨hji, hj⟩ := Finset.mem_erase.mp hj
    have hjL : j ∈ (Finset.Icc 1 (capL n)).erase i :=
      Finset.mem_erase.mpr ⟨hji, Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp hj).1, (Finset.mem_Icc.mp hj).2.trans hm⟩⟩
    exact (restoreOmittedVector_at_coordinate c0 i (fun j => Cseq j ω) ⟨j, hjL⟩).symm

open Classical in
/-- If [the clauses are independent and uniform](hyp:hlaw), [the fixed coordinate
is positive](hyp:hi), and [the prefix cutoff is at most the cap](hyp:hm), then
[under the law fixing that clause, the conditional probability of pivotality
given the ordinary filtration almost surely equals the fraction of finite
clause vectors in the observed ordinary-information fiber that belong to the
finite pivotality event](goal). -/
-- @node: condProb_pivotal_eq_fiber_fraction
lemma condProb_pivotal_eq_fiber_fraction
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Cseq : ℕ → Ω → ProperClause n)
    (hlaw : IsUniformClauseProcess μ Cseq) (i : ℕ) (hi : 1 ≤ i)
    (c0 : ProperClause n) (m : ℕ) (hm : m ≤ capL n) :
    (fixedClauseMeasure μ Cseq i c0)[eventIndicator (pivotalEvent Cseq i m) |
      ordinaryFiltration c0 Cseq i m] =ᵐ[fixedClauseMeasure μ Cseq i c0]
    fun ω =>
      (Fintype.card {cs : ((Finset.Icc 1 (capL n)).erase i) → ProperClause n //
        (∀ j : ((Finset.Icc 1 (capL n)).erase i), ordinaryPrefixExposure c0 m j (cs j) =
          ordinaryPrefixExposure c0 m j (Cseq j ω)) ∧
        cs ∈ pivotalVectorEvent c0 i m} : ℝ) /
      Fintype.card {cs : ((Finset.Icc 1 (capL n)).erase i) → ProperClause n //
        ∀ j : ((Finset.Icc 1 (capL n)).erase i), ordinaryPrefixExposure c0 m j (cs j) =
          ordinaryPrefixExposure c0 m j (Cseq j ω)} := by
  have he : eventIndicator (pivotalEvent Cseq i m) =ᵐ[fixedClauseMeasure μ Cseq i c0]
      eventIndicator {ω | (fun j : ((Finset.Icc 1 (capL n)).erase i) => Cseq j ω) ∈
        pivotalVectorEvent c0 i m} := by
    filter_upwards [fixedClauseMeasure_ae_eq μ Cseq hlaw i hi c0] with ω hfixed
    simp only [eventIndicator, Set.mem_ofPred_eq,
      pivotalVectorEvent_iff c0 Cseq i m hm ω hfixed]
  exact (condExp_congr_ae he).trans
    ((ordinary_hidden_clause_event_law μ Cseq hlaw i hi c0 m hm).mono
      (fun ω hω => hω (pivotalVectorEvent c0 i m)))

open Classical in
/-- If [the prefix cutoff is at most the cap](hyp:hm), [a finite clause vector
matches all ordinary prefix observations of the realized sequence](hyp:he),
and [that vector belongs to the finite pivotality event](hyp:hp), then [the
realized nonroot solution set is nonempty, and for each available root every
such solution is falsified by the nonroot part of some restored clause in
that root's realized test family](goal). -/
-- @node: pivotalVectorEvent_tests_necessary
lemma pivotalVectorEvent_tests_necessary (c0 : ProperClause n)
    (Cseq : ℕ → Ω → ProperClause n) (i m : ℕ) (hm : m ≤ capL n) (ω : Ω)
    (cs : ((Finset.Icc 1 (capL n)).erase i) → ProperClause n)
    (he : ∀ j : ((Finset.Icc 1 (capL n)).erase i), ordinaryPrefixExposure c0 m j (cs j) =
      ordinaryPrefixExposure c0 m j (Cseq j ω))
    (hp : cs ∈ pivotalVectorEvent c0 i m) :
    (nonrootSolutions c0 Cseq i m ω).Nonempty ∧
      ∀ x : roots c0, x.val ∈ availableRoots c0 Cseq i ω →
        ∀ y ∈ nonrootSolutions c0 Cseq i m ω,
          ∃ j ∈ rootTestFamily c0 Cseq i m x ω,
            ¬ testPartSat c0 (restoreOmittedVector c0 i cs j) y := by
  apply pivotal_tests_necessary_on_ordinary_fiber c0
    (fun j (_ : Unit) => restoreOmittedVector c0 i cs j) Cseq i m hm () ω
  · intro j hj
    simpa only [restoreOmittedVector_at_coordinate c0 i cs ⟨j, hj⟩] using he ⟨j, hj⟩
  · exact restoreOmittedVector_at_omitted c0 i cs
  · exact hp

open Classical in
/-- If [the prefix cutoff is at most the cap](hyp:hm) and [a coordinate belongs
to the chosen root's test family through that cutoff](hyp:hj), then [the
coordinate is positive, at most the cap, and different from the omitted
coordinate](goal). -/
-- @node: rootTestFamily_mem_cap
lemma rootTestFamily_mem_cap (c0 : ProperClause n)
    (Cseq : ℕ → Ω → ProperClause n) (i m : ℕ) (hm : m ≤ capL n)
    (ω : Ω) (x : roots c0) {j : ℕ} (hj : j ∈ rootTestFamily c0 Cseq i m x ω) :
    j ∈ (Finset.Icc 1 (capL n)).erase i := by
  obtain ⟨hji, hj⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp hj).1
  exact Finset.mem_erase.mpr ⟨hji, Finset.mem_Icc.mpr
    ⟨(Finset.mem_Icc.mp hj).1, (Finset.mem_Icc.mp hj).2.trans hm⟩⟩

open Classical in
/-- For [a reference clause](hyp:c0) on [a given number of variables](hyp:n),
[a clause process](hyp:Cseq) on [a sample space](hyp:Ω), [an omitted index](hyp:i),
[a prefix cutoff](hyp:m), [a realized sample](hyp:ω), and [a coordinate](hyp:j),
the [root test label](goal) is the root whose test family contains that
coordinate, if such a root exists, and is absent otherwise. -/
-- @node: rootTestLabel
def rootTestLabel (c0 : ProperClause n) (Cseq : ℕ → Ω → ProperClause n)
    (i m : ℕ) (ω : Ω) (j : ℕ) : Option (roots c0) :=
  if h : ∃ x : roots c0, j ∈ rootTestFamily c0 Cseq i m x ω
    then some (Classical.choose h) else none

open Classical in
/-- [A coordinate's root test label equals a particular root if and only if
the coordinate belongs to that root's test family](goal). -/
-- @node: rootTestLabel_eq_some_iff
lemma rootTestLabel_eq_some_iff (c0 : ProperClause n)
    (Cseq : ℕ → Ω → ProperClause n) (i m : ℕ) (ω : Ω)
    (j : ℕ) (x : roots c0) :
    rootTestLabel c0 Cseq i m ω j = some x ↔ j ∈ rootTestFamily c0 Cseq i m x ω := by
  unfold rootTestLabel
  split_ifs with h
  · have hj := Classical.choose_spec h
    constructor
    · intro he
      simpa only [Option.some.inj he] using hj
    · intro hx
      congr 1
      by_contra hne
      exact Finset.disjoint_left.mp
        (rootTestFamily_pairwise_disjoint c0 Cseq i m ω hne) hj hx
  · simp only [false_iff]
    exact fun hx => h ⟨x, hx⟩

open Classical in
/-- If [the prefix cutoff is at most the cap](hyp:hm), then [the number of
positive capped coordinates other than the omitted one labeled by a given
root is at most the realized incidence parameter](goal). -/
-- @node: rootTestLabel_fiber_card_le
lemma rootTestLabel_fiber_card_le (c0 : ProperClause n)
    (Cseq : ℕ → Ω → ProperClause n) (i m : ℕ) (hm : m ≤ capL n)
    (ω : Ω) (x : roots c0) :
    Fintype.card {j : ((Finset.Icc 1 (capL n)).erase i) //
      rootTestLabel c0 Cseq i m ω j = some x} ≤ incidenceParam c0 Cseq i ω := by
  let f : {j : ((Finset.Icc 1 (capL n)).erase i) //
      rootTestLabel c0 Cseq i m ω j = some x} → rootTestFamily c0 Cseq i m x ω :=
    fun j => ⟨j.val.val, (rootTestLabel_eq_some_iff c0 Cseq i m ω _ x).mp j.property⟩
  have hf : Function.Injective f := by
    intro j k he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : rootTestFamily c0 Cseq i m x ω => z.val) he
  exact (Fintype.card_le_of_injective f hf).trans (by
    simpa using rootTestFamily_card_le_incidenceParam c0 Cseq i m hm x ω)

open Classical in
/-- [The number of elements satisfying a predicate, divided by the size of
the finite ambient set, is at most one](goal), with the fraction interpreted
as zero when the ambient set is empty. -/
-- @node: finite_event_fraction_le_one
lemma finite_event_fraction_le_one {A : Type*} [Fintype A] (P : A → Prop) :
    (Fintype.card {a // P a} : ℝ) / Fintype.card A ≤ 1 := by
  apply div_le_one_of_le₀
  · exact_mod_cast Fintype.card_subtype_le P
  · exact Nat.cast_nonneg _

open Classical in
/-- [Multiplying a fixed real number once for each available root and one for
each remaining root gives that number raised to the number of available
roots](goal). -/
-- @node: availableRoot_factor_product
lemma availableRoot_factor_product (c0 : ProperClause n)
    (Cseq : ℕ → Ω → ProperClause n) (i : ℕ) (ω : Ω) (p : ℝ) :
    (∏ x : roots c0, if x.val ∈ availableRoots c0 Cseq i ω then p else 1) =
      p ^ (availableRoots c0 Cseq i ω).card := by
  rw [Finset.prod_coe_sort (roots c0) (fun x => if x ∈ availableRoots c0 Cseq i ω then p else 1)]
  rw [← Finset.prod_filter]
  have he : (roots c0).filter (fun x => x ∈ availableRoots c0 Cseq i ω) =
      availableRoots c0 Cseq i ω := by
    ext x
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨(Finset.mem_sdiff.mp h).1, h⟩⟩
  rw [he, Finset.prod_const]

open Classical in
/-- If [there are at least six variables](hyp:hn) and [the prefix cutoff is at
most the cap](hyp:hm), then [the fraction of pivotal finite clause vectors in
the realized ordinary-observation fiber is at most the killing probability
raised to the number of available roots when the nonroot solution set is
nonempty, and is zero when that solution set is empty](goal). -/
-- @node: pivotalVector_fiber_fraction_le
lemma pivotalVector_fiber_fraction_le (hn : OmissionN n) (c0 : ProperClause n)
    (Cseq : ℕ → Ω → ProperClause n) (i m : ℕ) (hm : m ≤ capL n) (ω : Ω) :
    (Fintype.card {cs : ((Finset.Icc 1 (capL n)).erase i) → ProperClause n //
      (∀ j : ((Finset.Icc 1 (capL n)).erase i), ordinaryPrefixExposure c0 m j (cs j) =
        ordinaryPrefixExposure c0 m j (Cseq j ω)) ∧ cs ∈ pivotalVectorEvent c0 i m} : ℝ) /
      Fintype.card {cs : ((Finset.Icc 1 (capL n)).erase i) → ProperClause n //
        ∀ j : ((Finset.Icc 1 (capL n)).erase i), ordinaryPrefixExposure c0 m j (cs j) =
          ordinaryPrefixExposure c0 m j (Cseq j ω)} ≤
    (if (nonrootSolutions c0 Cseq i m ω).Nonempty then 1 else 0) *
      (killProcess c0 Cseq i m ω) ^ (availableRoots c0 Cseq i ω).card := by
  by_cases hS : (nonrootSolutions c0 Cseq i m ω).Nonempty
  swap
  · haveI : IsEmpty {cs : ((Finset.Icc 1 (capL n)).erase i) → ProperClause n //
        (∀ j : ((Finset.Icc 1 (capL n)).erase i), ordinaryPrefixExposure c0 m j (cs j) =
          ordinaryPrefixExposure c0 m j (Cseq j ω)) ∧ cs ∈ pivotalVectorEvent c0 i m} :=
      ⟨fun cs => hS (pivotalVectorEvent_tests_necessary c0 Cseq i m hm ω cs.val
        cs.property.1 cs.property.2).1⟩
    simp only [Fintype.card_of_isEmpty, Nat.cast_zero, zero_div, if_neg hS, zero_mul, le_refl]
  simp only [if_pos hS, one_mul]
  let T := (Finset.Icc 1 (capL n)).erase i
  let label : T → Option (roots c0) := fun j => rootTestLabel c0 Cseq i m ω j
  let P : ∀ r : Option (roots c0), ({j : T // label j = r} → ProperClause n) → Prop :=
    fun r => match r with
    | none => fun _ => True
    | some x => fun cs => x.val ∈ availableRoots c0 Cseq i ω →
        ∀ y ∈ nonrootSolutions c0 Cseq i m ω, ∃ j, ¬ testPartSat c0 (cs j) y
  have hnecessary (cs : T → ProperClause n)
      (he : ∀ j : T, ordinaryPrefixExposure c0 m j (cs j) =
        ordinaryPrefixExposure c0 m j (Cseq j ω))
      (hp : cs ∈ pivotalVectorEvent c0 i m) : ∀ r, P r (fun j => cs j.val) := by
    intro r
    cases r with
    | none => trivial
    | some x =>
      intro hx y hy
      obtain ⟨j, hj, hkill⟩ :=
        (pivotalVectorEvent_tests_necessary c0 Cseq i m hm ω cs he hp).2 x hx y hy
      let jT : T := ⟨j, rootTestFamily_mem_cap c0 Cseq i m hm ω x hj⟩
      refine ⟨⟨jT, (rootTestLabel_eq_some_iff c0 Cseq i m ω j x).mpr hj⟩, ?_⟩
      change ¬ testPartSat c0 (restoreOmittedVector c0 i cs jT) y at hkill
      rwa [restoreOmittedVector_at_coordinate] at hkill
  let Q : Option (roots c0) → ℝ := fun r => match r with
    | none => 1
    | some x => if x.val ∈ availableRoots c0 Cseq i ω then killProcess c0 Cseq i m ω else 1
  have hfactor (r : Option (roots c0)) :
      (Fintype.card {cs : ∀ j : {j : T // label j = r},
        {c : ProperClause n // ordinaryPrefixExposure c0 m j.val c =
          ordinaryPrefixExposure c0 m j.val (Cseq j.val ω)} //
        P r (fun j => (cs j).val)} : ℝ) /
      Fintype.card (∀ j : {j : T // label j = r},
        {c : ProperClause n // ordinaryPrefixExposure c0 m j.val c =
          ordinaryPrefixExposure c0 m j.val (Cseq j.val ω)}) ≤ Q r := by
    cases r with
    | none => exact finite_event_fraction_le_one _
    | some x =>
      by_cases hx : x.val ∈ availableRoots c0 Cseq i ω
      swap
      · simpa only [Q, if_neg hx] using (finite_event_fraction_le_one
          (fun cs : ∀ j : {j : T // label j = some x},
            {c : ProperClause n // ordinaryPrefixExposure c0 m j.val c =
              ordinaryPrefixExposure c0 m j.val (Cseq j.val ω)} =>
            P (some x) (fun j => (cs j).val)))
      have hmem (j : {j : T // label j = some x}) :
          j.val.val ∈ rootTestFamily c0 Cseq i m x ω :=
        (rootTestLabel_eq_some_iff c0 Cseq i m ω _ x).mp j.property
      have hbound := ordinary_root_test_family_kill_fraction_le hn c0
        (fun j : {j : T // label j = some x} => Cseq j.val ω) m (fun j => j.val.val) x
        (fun j => (Finset.mem_filter.mp (hmem j)).2.1)
        (fun j => (Finset.mem_filter.mp (hmem j)).2.2)
        (incidenceParam c0 Cseq i ω)
        (rootTestLabel_fiber_card_le c0 Cseq i m hm ω x) (nonrootSolutions c0 Cseq i m ω)
      simp only [← Nat.card_eq_fintype_card] at hbound ⊢
      simpa only [P, Q, hx, true_implies, if_pos, killProcess] using hbound
  have hfam := finite_coordinate_fiber_event_le_families
    (fun j : T => ordinaryPrefixExposure c0 m j) (fun j => Cseq j ω)
    (pivotalVectorEvent c0 i m) label P hnecessary
  simp only [← Nat.card_eq_fintype_card] at hfam hfactor ⊢
  calc
    _ ≤ _ := hfam
    _ ≤ ∏ r, Q r := by
      apply Finset.prod_le_prod
      · intro r _
        exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      · intro r _
        exact hfactor r
    _ = _ := by
      rw [Fintype.prod_option]
      simp only [Q, one_mul]
      exact availableRoot_factor_product c0 Cseq i ω _

end Papers.OaiLinearVarianceRandom

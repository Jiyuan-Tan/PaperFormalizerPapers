module

public import Papers.OaiLinearVarianceRandom.Helpers.RootExposure

/-!
# Available roots and the necessary test events

These are the deterministic steps of the single-root flip argument. Availability
uses the full capped exposure, so it also rules out every obstructing collision
in the current prefix.
-/

@[expose] public section

noncomputable section
namespace Papers.OaiLinearVarianceRandom
open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {n : ℕ} {Ω : Type}

open Classical in
/-- For [a fixed clause determining the roots](hyp:c0) and [another clause](hyp:c)
on [n variables](hyp:n), [the true root variables](goal) are the variables of root
literals in the latter clause that are true under the assignment falsifying the fixed clause. -/
-- @node: trueRootVars
def trueRootVars (c0 c : ProperClause n) : Finset (Fin n) :=
  ((rootLiterals c0 c).filter
    (fun l => l.2 ≠ decide ((l.1, true) ∈ c0.val))).image Prod.fst

open Classical in
/-- For [a fixed clause determining the roots](hyp:c0) and [another clause](hyp:c)
on [n variables](hyp:n), [the collision-blocked roots](goal) are the true root
variables of the latter clause if it contains at least two root literals and
exactly one true root variable, and the empty set otherwise. -/
-- @node: collisionBlockedRoots
def collisionBlockedRoots (c0 c : ProperClause n) : Finset (Fin n) :=
  if 2 ≤ (rootLiterals c0 c).card ∧ (trueRootVars c0 c).card = 1
    then trueRootVars c0 c else ∅

open Classical in
/-- For [a fixed clause on n variables determining the roots](hyp:c0,n),
[a random clause sequence](hyp:Cseq), [an omitted index](hyp:i), and
[an outcome](hyp:ω), [the available roots](goal) are the roots not blocked by
any other clause among the first ten times n clauses. -/
-- @node: availableRoots
def availableRoots (c0 : ProperClause n) (Cseq : ℕ → Ω → ProperClause n)
    (i : ℕ) (ω : Ω) : Finset (Fin n) :=
  roots c0 \ (((Finset.Icc 1 (capL n)).erase i).biUnion
    (fun j => collisionBlockedRoots c0 (Cseq j ω)))

open Classical in
/-- For [a fixed clause on n variables determining the roots](hyp:c0,n),
[a clause to be tested](hyp:c), and [an assignment to the nonroot variables](hyp:y),
[nonroot satisfaction](goal) means that some literal of the tested clause uses a
nonroot variable and is true under the glued assignment. -/
-- @node: testPartSat
def testPartSat (c0 c : ProperClause n)
    (y : Fin (nonrootCount n) → Bool) : Prop :=
  ∃ l ∈ c.val, l.1 ∉ roots c0 ∧ glueAssignment c0 y l.1 = l.2

open Classical in
/-- For [a fixed clause on n variables determining the roots](hyp:c0,n),
[a random clause sequence](hyp:Cseq), [an omitted index](hyp:i),
[a prefix length](hyp:m), [a root of the fixed clause](hyp:x), and [an outcome](hyp:ω),
[the root's test family](goal) consists of the other indices from one through the
prefix length whose clauses are tests with that root variable true. -/
-- @node: rootTestFamily
def rootTestFamily (c0 : ProperClause n) (Cseq : ℕ → Ω → ProperClause n)
    (i m : ℕ) (x : roots c0) (ω : Ω) : Finset ℕ :=
  ((Finset.Icc 1 m).erase i).filter (fun j =>
    isTest c0 (Cseq j ω) ∧ x.val ∈ trueRootVars c0 (Cseq j ω))

open Classical in
/-- If [a literal uses a root variable of the fixed clause](hyp:hl), then
[it is true under the glued assignment exactly when its sign differs from the
sign of that variable in the fixed clause](goal). -/
-- @node: root_literal_true_iff
lemma root_literal_true_iff (c0 : ProperClause n)
    (y : Fin (nonrootCount n) → Bool) (l : Fin n × Bool)
    (hl : l.1 ∈ roots c0) :
    glueAssignment c0 y l.1 = l.2 ↔ l.2 ≠ decide ((l.1, true) ∈ c0.val) := by
  simp only [glueAssignment, dif_pos hl, rootFalsifier]
  cases h : decide ((l.1, true) ∈ c0.val) <;> cases l.2 <;> simp

open Classical in
/-- [Flipping any one root in the assignment that falsifies the fixed clause,
while retaining any chosen nonroot assignment, satisfies the fixed clause](goal). -/
-- @node: flipRootAssignment_satisfies_fixed
lemma flipRootAssignment_satisfies_fixed (c0 : ProperClause n) (x : roots c0)
    (y : Fin (nonrootCount n) → Bool) :
    ClauseSat c0 (flipRootAssignment c0 x y) := by
  by_contra h
  have hx := (rootFalsifier_unique c0 _).mp h x
  simp only [flipRootAssignment, glueAssignment, dif_pos x.property] at hx
  cases h : rootFalsifier c0 x <;> simp_all

open Classical in
/-- If [a clause is satisfied by the glued assignment](hyp:hs) but
[becomes unsatisfied after flipping a chosen root](hyp:hf), then
[its true root variables consist exactly of that root](goal). -/
-- @node: trueRootVars_singleton_of_flip_failure
lemma trueRootVars_singleton_of_flip_failure (c0 c : ProperClause n)
    (x : roots c0) (y : Fin (nonrootCount n) → Bool)
    (hs : ClauseSat c (glueAssignment c0 y))
    (hf : ¬ ClauseSat c (flipRootAssignment c0 x y)) :
    trueRootVars c0 c = {x.val} := by
  have honly (l : Fin n × Bool) (hl : l ∈ c.val)
      (hs : glueAssignment c0 y l.1 = l.2) : l.1 = x.val := by
    by_contra hne
    exact hf ⟨l, hl, by simpa only [flipRootAssignment, if_neg hne] using hs⟩
  apply Finset.eq_singleton_iff_unique_mem.mpr
  constructor
  · obtain ⟨l, hl, hs⟩ := hs
    have hx := honly l hl hs
    apply Finset.mem_image.mpr
    refine ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hl, ?_⟩, ?_⟩, hx⟩
    · simpa only [hx] using x.property
    · exact (root_literal_true_iff c0 y l (hx ▸ x.property)).mp hs
  · intro v hv
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hl, ht⟩ := Finset.mem_filter.mp hl
    obtain ⟨hlc, hlr⟩ := Finset.mem_filter.mp hl
    exact honly l hlc ((root_literal_true_iff c0 y l hlr).mpr ht)

open Classical in
/-- If [a clause has a true nonroot literal under the chosen nonroot assignment](hyp:hs),
then [it remains satisfied after flipping any one root of the fixed clause](goal). -/
-- @node: testPartSat_flip
lemma testPartSat_flip (c0 c : ProperClause n) (x : roots c0)
    (y : Fin (nonrootCount n) → Bool) (hs : testPartSat c0 c y) :
    ClauseSat c (flipRootAssignment c0 x y) := by
  obtain ⟨l, hl, hnr, hs⟩ := hs
  have hne : l.1 ≠ x.val := fun h => hnr (h ▸ x.property)
  exact ⟨l, hl, by simpa only [flipRootAssignment, if_neg hne] using hs⟩

open Classical in
/-- If [a clause is satisfied by the glued assignment](hyp:hs) but
[fails after a chosen root is flipped](hyp:hf), then [either it is a test clause
with that root variable true, or it blocks that root through a collision](goal). -/
-- @node: flip_failure_is_test_or_blocked
lemma flip_failure_is_test_or_blocked (c0 c : ProperClause n)
    (x : roots c0) (y : Fin (nonrootCount n) → Bool)
    (hs : ClauseSat c (glueAssignment c0 y))
    (hf : ¬ ClauseSat c (flipRootAssignment c0 x y)) :
    (isTest c0 c ∧ x.val ∈ trueRootVars c0 c) ∨
      x.val ∈ collisionBlockedRoots c0 c := by
  have ht := trueRootVars_singleton_of_flip_failure c0 c x y hs hf
  have hmem : x.val ∈ trueRootVars c0 c := by rw [ht]; exact Finset.mem_singleton_self _
  by_cases hc : 2 ≤ (rootLiterals c0 c).card
  · exact Or.inr (by simp [collisionBlockedRoots, hc, ht])
  · apply Or.inl
    refine ⟨⟨?_, ?_⟩, hmem⟩
    · have hpos : 0 < (rootLiterals c0 c).card := by
        obtain ⟨l, hl, _⟩ := Finset.mem_image.mp hmem
        exact Finset.card_pos.mpr ⟨l, (Finset.mem_filter.mp hl).1⟩
      omega
    · obtain ⟨l, hl, _⟩ := Finset.mem_image.mp hmem
      exact ⟨l, (Finset.mem_filter.mp hl).1, (Finset.mem_filter.mp hl).2⟩

open Classical in
/-- [A clause blocks at most one root if it contains at least two root literals,
and blocks no roots otherwise](goal). -/
-- @node: collisionBlockedRoots_card_le
lemma collisionBlockedRoots_card_le (c0 c : ProperClause n) :
    (collisionBlockedRoots c0 c).card ≤
      if 2 ≤ (rootLiterals c0 c).card then 1 else 0 := by
  unfold collisionBlockedRoots
  split_ifs with h h' <;> simp_all

open Classical in
/-- [The number of available roots plus the number of collisions among the
capped clauses other than the omitted clause is at least three](goal). -/
-- @node: availableRoots_card_add_collisionCount
lemma availableRoots_card_add_collisionCount (c0 : ProperClause n)
    (Cseq : ℕ → Ω → ProperClause n) (i : ℕ) (ω : Ω) :
    3 ≤ (availableRoots c0 Cseq i ω).card + collisionCount c0 Cseq i ω := by
  have hb :
      (((Finset.Icc 1 (capL n)).erase i).biUnion
        (fun j => collisionBlockedRoots c0 (Cseq j ω))).card ≤
      collisionCount c0 Cseq i ω := by
    apply (Finset.card_biUnion_le).trans
    calc
      _ ≤ ∑ j ∈ (Finset.Icc 1 (capL n)).erase i,
          if 2 ≤ (rootLiterals c0 (Cseq j ω)).card then 1 else 0 := by
        apply Finset.sum_le_sum
        intro j _
        exact collisionBlockedRoots_card_le c0 _
      _ = collisionCount c0 Cseq i ω := by
        simp [collisionCount, Finset.sum_boole]
  have hr := Finset.card_le_card_sdiff_add_card (s := roots c0)
    (t := ((Finset.Icc 1 (capL n)).erase i).biUnion
      (fun j => collisionBlockedRoots c0 (Cseq j ω)))
  rw [roots_card] at hr
  exact hr.trans (Nat.add_le_add_left hb _)

open Classical in
/-- If [a variable is an available root](hyp:hx) and [a clause index lies between
one and the cap and differs from the omitted index](hyp:hj), then
[that clause does not collision-block the variable](goal). -/
-- @node: availableRoots_not_blocked
lemma availableRoots_not_blocked (c0 : ProperClause n)
    (Cseq : ℕ → Ω → ProperClause n) (i : ℕ) (ω : Ω)
    (x : Fin n) (hx : x ∈ availableRoots c0 Cseq i ω)
    (j : ℕ) (hj : j ∈ (Finset.Icc 1 (capL n)).erase i) :
    x ∉ collisionBlockedRoots c0 (Cseq j ω) := by
  intro h
  exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_biUnion.mpr ⟨j, hj, h⟩)

open Classical in
/-- If [the prefix length does not exceed the cap](hyp:hm), [the omitted clause
equals the fixed clause](hyp:hfixed), [the omitted clause is pivotal at this
prefix](hyp:hp), and [the chosen root is available](hyp:hx), then [every nonroot
solution fails nonroot satisfaction for some clause in that root's test family](goal). -/
-- @node: pivotal_available_root_tests_kill
lemma pivotal_available_root_tests_kill (c0 : ProperClause n)
    (Cseq : ℕ → Ω → ProperClause n) (i m : ℕ) (hm : m ≤ capL n)
    (ω : Ω) (hfixed : Cseq i ω = c0) (hp : ω ∈ pivotalEvent Cseq i m)
    (x : roots c0) (hx : x.val ∈ availableRoots c0 Cseq i ω) :
    ∀ y ∈ nonrootSolutions c0 Cseq i m ω,
      ∃ j ∈ rootTestFamily c0 Cseq i m x ω, ¬ testPartSat c0 (Cseq j ω) y := by
  intro y hy
  by_contra h
  push Not at h
  have hflip : ∀ j ∈ Finset.Icc 1 m, j ≠ i →
      ClauseSat (Cseq j ω) (flipRootAssignment c0 x y) := by
    intro j hj hji
    have hjs : j ∈ (Finset.Icc 1 m).erase i := Finset.mem_erase.mpr ⟨hji, hj⟩
    have hjL : j ∈ (Finset.Icc 1 (capL n)).erase i :=
      Finset.mem_erase.mpr ⟨hji, Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp hj).1, (Finset.mem_Icc.mp hj).2.trans hm⟩⟩
    have hys := hy
    simp only [nonrootSolutions, Finset.mem_filter, Finset.mem_univ, true_and] at hys
    have hs : ClauseSat (Cseq j ω) (glueAssignment c0 y) := hys j hj hji
    by_contra hf
    rcases flip_failure_is_test_or_blocked c0 (Cseq j ω) x y hs hf with ht | hb
    · have hjt : j ∈ rootTestFamily c0 Cseq i m x ω :=
        Finset.mem_filter.mpr ⟨hjs, ht⟩
      exact hf (testPartSat_flip c0 _ x y (h j hjt))
    · exact availableRoots_not_blocked c0 Cseq i ω x hx j hjL hb
  exact hp.2 ⟨flipRootAssignment c0 x y, hflip,
    hfixed.symm ▸ flipRootAssignment_satisfies_fixed c0 x y⟩

open Classical in
/-- If [an assignment falsifies the fixed clause](hyp:hz), then [gluing its
restriction to the nonroot variables to the root falsifier recovers the entire assignment](goal). -/
-- @node: glueAssignment_of_falsifies_fixed
lemma glueAssignment_of_falsifies_fixed (c0 : ProperClause n)
    (z : Fin n → Bool) (hz : ¬ ClauseSat c0 z) :
    glueAssignment c0 (fun v => z ((nonrootEquiv c0).symm v).val) = z := by
  funext v
  by_cases hv : v ∈ roots c0
  · simpa only [glueAssignment, dif_pos hv] using
      ((rootFalsifier_unique c0 z).mp hz ⟨v, hv⟩).symm
  · simp only [glueAssignment, dif_neg hv, Equiv.symm_apply_apply]

open Classical in
/-- If [the omitted clause equals the fixed clause](hyp:hfixed) and
[is pivotal at the given prefix](hyp:hp), then [the nonroot solution set is nonempty](goal). -/
-- @node: pivotal_nonrootSolutions_nonempty
lemma pivotal_nonrootSolutions_nonempty (c0 : ProperClause n)
    (Cseq : ℕ → Ω → ProperClause n) (i m : ℕ) (ω : Ω)
    (hfixed : Cseq i ω = c0) (hp : ω ∈ pivotalEvent Cseq i m) :
    (nonrootSolutions c0 Cseq i m ω).Nonempty := by
  obtain ⟨z, hz⟩ := hp.1
  have hc : ¬ ClauseSat c0 z := by
    intro hc
    exact hp.2 ⟨z, hz, hfixed.symm ▸ hc⟩
  refine ⟨(fun v => z ((nonrootEquiv c0).symm v).val), ?_⟩
  simp only [nonrootSolutions, Finset.mem_filter, Finset.mem_univ, true_and,
    glueAssignment_of_falsifies_fixed c0 z hc]
  exact hz

open Classical in
/-- If [a clause is a test relative to the fixed clause](hyp:hc), then
[it has exactly one true root variable](goal). -/
-- @node: trueRootVars_card_of_isTest
lemma trueRootVars_card_of_isTest (c0 c : ProperClause n) (hc : isTest c0 c) :
    (trueRootVars c0 c).card = 1 := by
  obtain ⟨l, hl⟩ := Finset.card_eq_one.mp hc.1
  obtain ⟨l', hl', ht⟩ := hc.2
  rw [hl, Finset.mem_singleton] at hl'
  subst l'
  simp [trueRootVars, hl, Finset.filter_singleton, ht]

open Classical in
/-- [The test families associated with distinct roots of the fixed clause are
pairwise disjoint](goal). -/
-- @node: rootTestFamily_pairwise_disjoint
lemma rootTestFamily_pairwise_disjoint (c0 : ProperClause n)
    (Cseq : ℕ → Ω → ProperClause n) (i m : ℕ) (ω : Ω) :
    Pairwise (fun x x' : roots c0 =>
      Disjoint (rootTestFamily c0 Cseq i m x ω) (rootTestFamily c0 Cseq i m x' ω)) := by
  intro x x' hne
  apply Finset.disjoint_left.mpr
  intro j hj hj'
  have ht := (Finset.mem_filter.mp hj).2
  have ht' := (Finset.mem_filter.mp hj').2
  have heq := Finset.card_le_one.mp (trueRootVars_card_of_isTest c0 _ ht.1).le
    x.val ht.2 x'.val ht'.2
  exact hne (Subtype.ext heq)

open Classical in
/-- If [the prefix length does not exceed the cap](hyp:hm), then [the size of
any root's test family is at most the incidence count for the capped exposure](goal). -/
-- @node: rootTestFamily_card_le_incidenceCount
lemma rootTestFamily_card_le_incidenceCount (c0 : ProperClause n)
    (Cseq : ℕ → Ω → ProperClause n) (i m : ℕ) (hm : m ≤ capL n)
    (x : roots c0) (ω : Ω) :
    (rootTestFamily c0 Cseq i m x ω).card ≤ incidenceCount c0 Cseq i ω := by
  apply Finset.card_le_card
  intro j hj
  obtain ⟨hj, ht⟩ := Finset.mem_filter.mp hj
  obtain ⟨hji, hj⟩ := Finset.mem_erase.mp hj
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_erase.mpr ⟨hji, Finset.mem_Icc.mpr
    ⟨(Finset.mem_Icc.mp hj).1, (Finset.mem_Icc.mp hj).2.trans hm⟩⟩, ?_⟩
  exact ht.1.1.ge

open Classical in
/-- If [the prefix length does not exceed the cap](hyp:hm), then [the size of
any root's test family is at most the incidence parameter for the capped exposure](goal). -/
-- @node: rootTestFamily_card_le_incidenceParam
lemma rootTestFamily_card_le_incidenceParam (c0 : ProperClause n)
    (Cseq : ℕ → Ω → ProperClause n) (i m : ℕ) (hm : m ≤ capL n)
    (x : roots c0) (ω : Ω) :
    (rootTestFamily c0 Cseq i m x ω).card ≤ incidenceParam c0 Cseq i ω := by
  exact (rootTestFamily_card_le_incidenceCount c0 Cseq i m hm x ω).trans
    (le_max_right _ _)

open Classical in
/-- [The set of available roots is measurable with respect to the information
revealed by the capped root exposure](goal). -/
@[fun_prop]
-- @node: availableRoots_measurable
lemma availableRoots_measurable [MeasurableSpace Ω] (c0 : ProperClause n)
    (Cseq : ℕ → Ω → ProperClause n) (i : ℕ) :
    @Measurable Ω (Finset (Fin n)) (exposureSigma c0 Cseq i) ⊤
      (availableRoots c0 Cseq i) := by
  let : MeasurableSpace Ω := exposureSigma c0 Cseq i
  have hmem (v : Fin n) : Measurable (fun ω => v ∈ availableRoots c0 Cseq i ω) := by
    have hb (j : (Finset.Icc 1 (capL n)).erase i) :
        Measurable (fun ω => v ∈ collisionBlockedRoots c0 (Cseq j ω)) := by
      have he : @Measurable Ω _ _ ⊤ (fun ω => expose c0 (Cseq j ω)) := by
        apply Measurable.of_comap_le
        exact le_iSup_of_le j.val (le_iSup_of_le j.property le_rfl)
      apply measurableSet_setOfPred.mp
      exact he (t := {e | v ∈ if 2 ≤ e.1.card ∧
        ((e.1.filter (fun l => l.2 ≠ decide ((l.1, true) ∈ c0.val))).image Prod.fst).card = 1
        then (e.1.filter (fun l => l.2 ≠ decide ((l.1, true) ∈ c0.val))).image Prod.fst
        else ∅}) (by trivial)
    have h := (measurable_const : Measurable (fun _ : Ω => v ∈ roots c0)).and
      (Measurable.exists hb).not
    convert h using 1
    ext ω
    simp only [availableRoots, Finset.mem_sdiff, Finset.mem_biUnion, Subtype.exists, exists_prop]
  let : MeasurableSpace (Finset (Fin n)) := ⊤
  apply measurable_to_countable'
  intro s
  have h := Measurable.forall (fun v => (hmem v).iff
    (measurable_const : Measurable (fun _ : Ω => v ∈ s)))
  convert h.setOf using 1
  ext ω
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq, Finset.ext_iff]

open Classical in
/-- If [the capped exposure has no collisions](hyp:hv), then
[exactly three roots are available](goal). -/
-- @node: availableRoots_card_of_no_collision
lemma availableRoots_card_of_no_collision (c0 : ProperClause n)
    (Cseq : ℕ → Ω → ProperClause n) (i : ℕ) (ω : Ω)
    (hv : collisionCount c0 Cseq i ω = 0) :
    (availableRoots c0 Cseq i ω).card = 3 := by
  have hl := availableRoots_card_add_collisionCount c0 Cseq i ω
  have hu : (availableRoots c0 Cseq i ω).card ≤ 3 := by
    exact (Finset.card_le_card Finset.sdiff_subset).trans_eq (roots_card c0)
  omega

open Classical in
/-- If [the capped exposure has exactly one collision](hyp:hv), then
[at least two roots are available](goal). -/
-- @node: two_le_availableRoots_card_of_one_collision
lemma two_le_availableRoots_card_of_one_collision (c0 : ProperClause n)
    (Cseq : ℕ → Ω → ProperClause n) (i : ℕ) (ω : Ω)
    (hv : collisionCount c0 Cseq i ω = 1) :
    2 ≤ (availableRoots c0 Cseq i ω).card := by
  have hl := availableRoots_card_add_collisionCount c0 Cseq i ω
  omega

open Classical in
/-- For [independent uniformly distributed measurable clauses](hyp:hlaw) and
[a positive omitted index](hyp:hi), [the omitted clause equals the fixed clause
almost surely under the measure conditioned on that clause](goal). -/
-- @node: fixedClauseMeasure_ae_eq
lemma fixedClauseMeasure_ae_eq [MeasurableSpace Ω] (μ : Measure Ω)
    (Cseq : ℕ → Ω → ProperClause n) (hlaw : IsUniformClauseProcess μ Cseq)
    (i : ℕ) (hi : 1 ≤ i) (c0 : ProperClause n) :
    ∀ᵐ ω ∂(fixedClauseMeasure μ Cseq i c0), Cseq i ω = c0 := by
  apply ProbabilityTheory.ae_cond_mem
  exact (hlaw.1 i hi) (MeasurableSet.singleton c0)

open Classical in
/-- For [independent uniformly distributed measurable clauses](hyp:hlaw),
[a positive omitted index](hyp:hi), and [a prefix length at most the cap](hyp:hm),
[almost surely under the measure fixing the omitted clause, pivotality implies
a nonempty nonroot solution set and, for every available root and every nonroot
solution, a test in that root's family whose nonroot literals all fail](goal). -/
-- @node: pivotal_tests_necessary_ae
lemma pivotal_tests_necessary_ae [MeasurableSpace Ω] (μ : Measure Ω)
    (Cseq : ℕ → Ω → ProperClause n) (hlaw : IsUniformClauseProcess μ Cseq)
    (i : ℕ) (hi : 1 ≤ i) (c0 : ProperClause n) (m : ℕ) (hm : m ≤ capL n) :
    ∀ᵐ ω ∂(fixedClauseMeasure μ Cseq i c0), ω ∈ pivotalEvent Cseq i m →
      (nonrootSolutions c0 Cseq i m ω).Nonempty ∧
      ∀ x : roots c0, x.val ∈ availableRoots c0 Cseq i ω →
        ∀ y ∈ nonrootSolutions c0 Cseq i m ω,
          ∃ j ∈ rootTestFamily c0 Cseq i m x ω, ¬ testPartSat c0 (Cseq j ω) y := by
  filter_upwards [fixedClauseMeasure_ae_eq μ Cseq hlaw i hi c0] with ω hfixed
  intro hp
  exact ⟨pivotal_nonrootSolutions_nonempty c0 Cseq i m ω hfixed hp,
    fun x hx => pivotal_available_root_tests_kill c0 Cseq i m hm ω hfixed hp x hx⟩


open Classical in
/-- If [the prefix length does not exceed the cap](hyp:hm), then [the chosen
root's test family is measurable with respect to the capped root exposure](goal). -/
@[fun_prop]
-- @node: rootTestFamily_measurable
lemma rootTestFamily_measurable (c0 : ProperClause n)
    (Cseq : ℕ → Ω → ProperClause n) (i m : ℕ) (hm : m ≤ capL n)
    (x : roots c0) :
    @Measurable Ω (Finset ℕ) (exposureSigma c0 Cseq i) ⊤
      (rootTestFamily c0 Cseq i m x) := by
  classical
  let : MeasurableSpace Ω := exposureSigma c0 Cseq i
  have hmem (j : ℕ) : Measurable (fun ω => j ∈ rootTestFamily c0 Cseq i m x ω) := by
    by_cases hj : j ∈ (Finset.Icc 1 m).erase i
    · have hjL : j ∈ (Finset.Icc 1 (capL n)).erase i := by
        obtain ⟨hne, hj'⟩ := Finset.mem_erase.mp hj
        exact Finset.mem_erase.mpr ⟨hne, Finset.mem_Icc.mpr
          ⟨(Finset.mem_Icc.mp hj').1, (Finset.mem_Icc.mp hj').2.trans hm⟩⟩
      have he : @Measurable Ω _ _ ⊤ (fun ω => expose c0 (Cseq j ω)) := by
        apply Measurable.of_comap_le
        exact le_iSup_of_le j (le_iSup_of_le hjL le_rfl)
      apply measurableSet_setOfPred.mp
      convert he (t := {e | (e.1.card = 1 ∧
        ∃ l ∈ e.1, l.2 ≠ decide ((l.1, true) ∈ c0.val)) ∧
        x.val ∈ (e.1.filter
          (fun l => l.2 ≠ decide ((l.1, true) ∈ c0.val))).image Prod.fst}) (by trivial)
        using 1
      ext ω
      change (j ∈ rootTestFamily c0 Cseq i m x ω) ↔ _
      rw [rootTestFamily, Finset.mem_filter]
      simp only [hj, true_and, isTest, trueRootVars, Set.mem_preimage,
        Set.mem_ofPred_eq, expose]
      simp
    · simpa only [rootTestFamily, Finset.mem_filter, hj, false_and] using
        (measurable_const : Measurable (fun _ : Ω => False))
  let : MeasurableSpace (Finset ℕ) := ⊤
  apply measurable_to_countable'
  intro s
  have h := Measurable.forall (fun j => (hmem j).iff
    (measurable_const : Measurable (fun _ : Ω => j ∈ s)))
  convert h.setOf using 1
  ext ω
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq, Finset.ext_iff]

end Papers.OaiLinearVarianceRandom

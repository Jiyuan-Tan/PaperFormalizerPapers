module

public import Papers.OaiLinearVarianceRandom.Helpers.OrdinaryClauses
public import Papers.OaiLinearVarianceRandom.Helpers.TestNecessity

/-! # Single-root clause fibers

A fixed root literal leaves exactly a proper 2-clause on the nonroots.
Relabeling this part preserves the satisfaction event used by the test bound.
-/

@[expose] public section

noncomputable section
namespace Papers.OaiLinearVarianceRandom

variable {n : ℕ}

open Classical in
-- @node: nonrootLiteralEmbedding_image_vars
/-- [Relabeling a set of nonroot literals and then collecting their variables gives the same variable set as collecting the variables first and relabeling them](goal). -/
lemma nonrootLiteralEmbedding_image_vars (c0 : ProperClause n)
    (s : Finset (Fin (nonrootCount n) × Bool)) :
    (s.map (nonrootLiteralEmbedding c0)).image Prod.fst =
      (s.image Prod.fst).map (nonrootEmbedding c0) := by
  ext v
  simp [Finset.mem_map, Finset.mem_image, nonrootLiteralEmbedding,
    Function.Embedding.prodMap, exists_and_right]
  aesop

open Classical in
-- @node: root_not_mem_nonroot_map
/-- If [the variable of literal r is a root of the reference clause](hyp:hr), [r cannot occur in any set obtained by relabeling nonroot literals](goal). -/
lemma root_not_mem_nonroot_map (c0 : ProperClause n)
    (r : Fin n × Bool) (hr : r.1 ∈ roots c0)
    (s : Finset (Fin (nonrootCount n) × Bool)) :
    r ∉ s.map (nonrootLiteralEmbedding c0) := by
  rintro h
  obtain ⟨l, _, he⟩ := Finset.mem_map.mp h
  have he' : nonrootEmbedding c0 l.1 = r.1 := congrArg Prod.fst he
  exact nonrootEmbedding_not_root c0 l.1 (he'.symm ▸ hr)

open Classical in
-- @node: liftTestClause
/-- Given [a reference clause c0](hyp:c0) on [n variables](hyp:n), [a literal r](hyp:r) [whose variable is a root of c0](hyp:hr), and [a proper two-literal clause b on the nonroot variables](hyp:b), [the lifted clause consists of r together with the relabeled literals of b](goal). -/
def liftTestClause (c0 : ProperClause n) (r : Fin n × Bool)
    (hr : r.1 ∈ roots c0) (b : ProperClauseA (nonrootCount n) 2) : ProperClause n :=
  ⟨insert r (b.val.map (nonrootLiteralEmbedding c0)), by
    constructor
    · rw [Finset.card_insert_of_notMem (root_not_mem_nonroot_map c0 r hr b.val),
        Finset.card_map, b.property.1]
    · rw [Finset.image_insert, nonrootLiteralEmbedding_image_vars]
      have hnot : r.1 ∉ (b.val.image Prod.fst).map (nonrootEmbedding c0) := by
        intro h
        obtain ⟨v, _, he⟩ := Finset.mem_map.mp h
        exact nonrootEmbedding_not_root c0 v (he ▸ hr)
      rw [Finset.card_insert_of_notMem hnot, Finset.card_map, b.property.2]⟩

open Classical in
-- @node: liftTestClause_rootLiterals
/-- If [the variable of r is a root of the reference clause](hyp:hr), [lifting a proper two-literal clause on the nonroots by adjoining r produces a clause whose root literals consist exactly of r](goal). -/
lemma liftTestClause_rootLiterals (c0 : ProperClause n) (r : Fin n × Bool)
    (hr : r.1 ∈ roots c0) (b : ProperClauseA (nonrootCount n) 2) :
    rootLiterals c0 (liftTestClause c0 r hr b) = {r} := by
  ext l
  simp only [rootLiterals, liftTestClause, Finset.mem_filter, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨h | h, hl⟩
    · exact h
    · obtain ⟨k, _, rfl⟩ := Finset.mem_map.mp h
      exact False.elim (nonrootEmbedding_not_root c0 k.1 hl)
  · rintro rfl
    exact ⟨Or.inl rfl, hr⟩

open Classical in
-- @node: liftTestClause_injective
/-- If [the variable of r is a root of the reference clause](hyp:hr), [adjoining r after relabeling nonroot two-literal clauses is injective: two lifted clauses coincide only when their original clauses coincide](goal). -/
lemma liftTestClause_injective (c0 : ProperClause n) (r : Fin n × Bool)
    (hr : r.1 ∈ roots c0) : Function.Injective (liftTestClause c0 r hr) := by
  intro a b hab
  apply Subtype.ext
  apply Finset.map_injective (nonrootLiteralEmbedding c0)
  have h := congrArg (fun c : ProperClause n => c.val.erase r) hab
  simpa only [liftTestClause, Finset.erase_insert
    (root_not_mem_nonroot_map c0 r hr _)] using h

open Classical in
-- @node: liftTestClause_testPartSat
/-- If [the variable of r is a root of the reference clause](hyp:hr), [a nonroot assignment satisfies the test part of the clause obtained by adjoining r to b exactly when it satisfies b](goal). -/
lemma liftTestClause_testPartSat (c0 : ProperClause n) (r : Fin n × Bool)
    (hr : r.1 ∈ roots c0) (b : ProperClauseA (nonrootCount n) 2)
    (y : Fin (nonrootCount n) → Bool) :
    testPartSat c0 (liftTestClause c0 r hr b) y ↔ ClauseSat b y := by
  have hg (v : Fin (nonrootCount n)) :
      glueAssignment c0 y (nonrootEmbedding c0 v) = y v := by
    rw [glueAssignment, dif_neg (nonrootEmbedding_not_root c0 v)]
    exact congrArg y ((nonrootEquiv c0).apply_symm_apply v)
  constructor
  · rintro ⟨l, hl, hnr, hs⟩
    rcases Finset.mem_insert.mp hl with he | hl
    · subst l
      exact False.elim (hnr hr)
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hl
      exact ⟨k, hk, (hg k.1).symm.trans hs⟩
  · rintro ⟨k, hk, hs⟩
    exact ⟨nonrootLiteralEmbedding c0 k,
      Finset.mem_insert_of_mem (Finset.mem_map.mpr ⟨k, hk, rfl⟩),
      nonrootEmbedding_not_root c0 k.1, (hg k.1).trans hs⟩

open Classical in
-- @node: single_root_literal_in_range
/-- Suppose [the root literals of c consist exactly of r](hyp:he), [l is a literal of c](hyp:hl), and [l differs from r](hyp:hne). Then [l is the relabeling of a nonroot literal](goal). -/
lemma single_root_literal_in_range (c0 c : ProperClause n) (r : Fin n × Bool)
    (he : rootLiterals c0 c = {r}) (l : Fin n × Bool)
    (hl : l ∈ c.val) (hne : l ≠ r) :
    l ∈ Set.range (nonrootLiteralEmbedding c0) := by
  have hn : l.1 ∉ roots c0 := by
    intro hr
    have hm : l ∈ rootLiterals c0 c := Finset.mem_filter.mpr ⟨hl, hr⟩
    rw [he, Finset.mem_singleton] at hm
    exact hne hm
  refine ⟨(nonrootEquiv c0 ⟨l.1, hn⟩, l.2), ?_⟩
  apply Prod.ext
  · exact congrArg Subtype.val ((nonrootEquiv c0).symm_apply_apply ⟨l.1, hn⟩)
  · rfl

open Classical in
-- @node: liftTestClause_surjective
/-- If [the variable of r is a root of the reference clause](hyp:hr) and [the root literals of c consist exactly of r](hyp:he), [there is a proper two-literal clause on the nonroots whose lift by adjoining r is c](goal). -/
lemma liftTestClause_surjective (c0 c : ProperClause n) (r : Fin n × Bool)
    (hr : r.1 ∈ roots c0) (he : rootLiterals c0 c = {r}) :
    ∃ b : ProperClauseA (nonrootCount n) 2, liftTestClause c0 r hr b = c := by
  let e := nonrootLiteralEmbedding c0
  let t := (c.val.erase r).preimage e e.injective.injOn
  have ht : t.map e = c.val.erase r := by
    rw [Finset.map_eq_image, Finset.image_preimage]
    apply Finset.filter_eq_self.mpr
    intro l hl
    obtain ⟨hne, hl⟩ := Finset.mem_erase.mp hl
    exact single_root_literal_in_range c0 c r he l hl hne
  have hrmem : r ∈ c.val := by
    have h : r ∈ rootLiterals c0 c := he.symm ▸ Finset.mem_singleton_self r
    exact (Finset.mem_filter.mp h).1
  have hsplit : insert r (t.map e) = c.val := by
    rw [ht, Finset.insert_erase hrmem]
  have hcard : t.card = 2 := by
    have h := c.property.1
    rw [← hsplit, Finset.card_insert_of_notMem
      (root_not_mem_nonroot_map c0 r hr t), Finset.card_map] at h
    omega
  have hvar : (t.image Prod.fst).card = 2 := by
    have h := c.property.2
    rw [← hsplit, Finset.image_insert, nonrootLiteralEmbedding_image_vars] at h
    have hnot : r.1 ∉ (t.image Prod.fst).map (nonrootEmbedding c0) := by
      intro hv
      obtain ⟨v, _, hv⟩ := Finset.mem_map.mp hv
      exact nonrootEmbedding_not_root c0 v (hv.symm ▸ hr)
    rw [Finset.card_insert_of_notMem hnot, Finset.card_map] at h
    omega
  exact ⟨⟨t, hcard, hvar⟩, Subtype.ext hsplit⟩

-- @node: testClauseEquiv
/-- Given [a reference clause c0](hyp:c0) on [n variables](hyp:n) and [a literal r](hyp:r) [whose variable is a root of c0](hyp:hr), [adjoining r after relabeling gives a bijection between proper two-literal clauses on the nonroots and proper three-literal clauses whose root literals consist exactly of r](goal). -/
def testClauseEquiv (c0 : ProperClause n) (r : Fin n × Bool)
    (hr : r.1 ∈ roots c0) :
    ProperClauseA (nonrootCount n) 2 ≃
      {c : ProperClause n // rootLiterals c0 c = {r}} :=
  Equiv.ofBijective (fun b =>
    ⟨liftTestClause c0 r hr b, liftTestClause_rootLiterals c0 r hr b⟩)
    ⟨fun _ _ h => liftTestClause_injective c0 r hr (congrArg Subtype.val h), by
      rintro ⟨c, hc⟩
      obtain ⟨b, hb⟩ := liftTestClause_surjective c0 c r hr hc
      exact ⟨b, Subtype.ext hb⟩⟩

open Classical in
-- @node: liftTestClause_isTest
/-- If [the variable of r is a root of the reference clause](hyp:hr) and [r has the opposite sign to that variable's literal in the reference clause](hyp:hs), [adjoining r to any relabeled proper two-literal clause on the nonroots produces a test clause](goal). -/
lemma liftTestClause_isTest (c0 : ProperClause n) (r : Fin n × Bool)
    (hr : r.1 ∈ roots c0) (hs : r.2 ≠ decide ((r.1, true) ∈ c0.val))
    (b : ProperClauseA (nonrootCount n) 2) :
    isTest c0 (liftTestClause c0 r hr b) := by
  simp only [isTest, liftTestClause_rootLiterals, Finset.card_singleton,
    Finset.mem_singleton]
  exact ⟨True.intro, r, rfl, hs⟩

open Classical in
-- @node: liftTestClause_family_kills_iff
/-- If [the variable of r is a root of the reference clause](hyp:hr), [every assignment in S fails the test part of at least one clause lifted from the family of j nonroot two-literal clauses exactly when no assignment in S survives that original family](goal). -/
lemma liftTestClause_family_kills_iff (c0 : ProperClause n) (r : Fin n × Bool)
    (hr : r.1 ∈ roots c0) (j : ℕ) (S : Finset (Fin (nonrootCount n) → Bool))
    (bs : Fin j → ProperClauseA (nonrootCount n) 2) :
    (∀ y ∈ S, ∃ k, ¬ testPartSat c0 (liftTestClause c0 r hr (bs k)) y) ↔
      familySurvivors j S bs = ∅ := by
  simp only [liftTestClause_testPartSat, Finset.eq_empty_iff_forall_notMem,
    familySurvivors, Finset.mem_filter, not_and, not_forall]

open Classical in
/-- If [the variable of r is a root of the reference clause](hyp:hr), [the fraction of length-j clause families with sole root literal r whose test parts eliminate every assignment in S equals the probability that j independent uniform nonroot two-literal clauses eliminate S](goal). -/
-- @node: testClauseFamily_kill_fraction
lemma testClauseFamily_kill_fraction (c0 : ProperClause n) (r : Fin n × Bool)
    (hr : r.1 ∈ roots c0) (j : ℕ) (S : Finset (Fin (nonrootCount n) → Bool)) :
    (Fintype.card {cs : Fin j → {c : ProperClause n // rootLiterals c0 c = {r}} //
      ∀ y ∈ S, ∃ k, ¬ testPartSat c0 (cs k).val y} : ℝ) /
        Fintype.card (Fin j → {c : ProperClause n // rootLiterals c0 c = {r}}) =
      killProb j S := by
  let e := Equiv.piCongrRight (fun _ : Fin j => testClauseEquiv c0 r hr)
  have hk (bs : Fin j → ProperClauseA (nonrootCount n) 2) :
      familySurvivors j S bs = ∅ ↔
        ∀ y ∈ S, ∃ k, ¬ testPartSat c0 (e bs k).val y := by
    exact (liftTestClause_family_kills_iff c0 r hr j S bs).symm
  have hnum := Fintype.card_congr (e.subtypeEquiv
    (p := fun bs => familySurvivors j S bs = ∅)
    (q := fun cs => ∀ y ∈ S, ∃ k, ¬ testPartSat c0 (cs k).val y) hk)
  have hden := Fintype.card_congr e
  unfold killProb
  rw [← hnum, ← hden]

-- @node: killProb_mono_length
/-- If [there are at least three assignment coordinates](hyp:hu), [the probability that independent uniform two-literal clauses eliminate S is nondecreasing in the number of clauses](goal). -/
lemma killProb_mono_length {u : ℕ} (hu : OneU u)
    (S : Finset (Fin u → Bool)) : Monotone (fun j => killProb j S) := by
  apply monotone_nat_of_le_succ
  intro j
  exact sub_nonneg.mp (killProb_increment_nonneg hu j S)

open Classical in
-- @node: testClauseFamily_kill_fraction_le
/-- Suppose [there are at least six variables](hyp:hn), [the variable of r is a root of the reference clause](hyp:hr), and [j is at most d](hyp:hjd). Then [the fraction of length-j clause families with sole root literal r whose test parts eliminate every assignment in S is at most the probability that d independent uniform nonroot two-literal clauses eliminate S](goal). -/
lemma testClauseFamily_kill_fraction_le (hn : OmissionN n) (c0 : ProperClause n)
    (r : Fin n × Bool) (hr : r.1 ∈ roots c0) (j d : ℕ) (hjd : j ≤ d)
    (S : Finset (Fin (nonrootCount n) → Bool)) :
    (Fintype.card {cs : Fin j → {c : ProperClause n // rootLiterals c0 c = {r}} //
      ∀ y ∈ S, ∃ k, ¬ testPartSat c0 (cs k).val y} : ℝ) /
        Fintype.card (Fin j → {c : ProperClause n // rootLiterals c0 c = {r}}) ≤
      killProb d S := by
  rw [testClauseFamily_kill_fraction c0 r hr]
  have hu : OneU (nonrootCount n) := by
    unfold OmissionN at hn
    unfold OneU nonrootCount
    omega
  exact killProb_mono_length hu S hjd

end Papers.OaiLinearVarianceRandom

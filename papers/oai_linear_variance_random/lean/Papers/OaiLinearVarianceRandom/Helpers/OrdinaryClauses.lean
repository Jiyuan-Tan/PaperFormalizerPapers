module

public import Papers.OaiLinearVarianceRandom.Helpers.OccupationPaths
public import Mathlib.Data.Finset.Preimage

/-! # Ordinary clauses as clauses on the nonroots

Relabeling the nonroot variables identifies ordinary clauses with proper
3-clauses on the smaller cube and preserves satisfaction and survivors.
-/

@[expose] public section

noncomputable section
namespace Papers.OaiLinearVarianceRandom
open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {n : ℕ} {Ω : Type}

-- @node: nonrootEmbedding
/-- In a model with [a given number of variables](hyp:n), [a fixed root
clause](hyp:c0) determines [the injective relabeling of the nonroot variable
indices as original variable indices](goal). -/
def nonrootEmbedding (c0 : ProperClause n) : Fin (nonrootCount n) ↪ Fin n :=
  (nonrootEquiv c0).symm.toEmbedding.trans (Function.Embedding.subtype _)

-- @node: nonrootEmbedding_not_root
/-- [Every variable obtained by embedding a nonroot index lies outside the
root variables of the fixed clause](goal). -/
lemma nonrootEmbedding_not_root (c0 : ProperClause n) (v : Fin (nonrootCount n)) :
    nonrootEmbedding c0 v ∉ roots c0 :=
  ((nonrootEquiv c0).symm v).property

-- @node: nonrootLiteralEmbedding
/-- In a model with [a given number of variables](hyp:n), [a fixed root
clause](hyp:c0) determines [the injective relabeling of nonroot literals as
original literals, preserving their Boolean signs](goal). -/
def nonrootLiteralEmbedding (c0 : ProperClause n) :
    (Fin (nonrootCount n) × Bool) ↪ (Fin n × Bool) :=
  (nonrootEmbedding c0).prodMap (Function.Embedding.refl Bool)

-- @node: liftNonrootClause
/-- In a model with [a given number of variables](hyp:n), for [a fixed root
clause](hyp:c0) and [a proper three-clause on the nonroot variables](hyp:c),
[the lifted clause is the proper three-clause on the original variables
obtained by relabeling each nonroot literal while preserving its sign](goal). -/
def liftNonrootClause (c0 : ProperClause n) (c : ProperClause (nonrootCount n)) :
    ProperClause n :=
  ⟨c.val.map (nonrootLiteralEmbedding c0), by
    constructor
    · simpa using c.property.1
    · have he : (c.val.map (nonrootLiteralEmbedding c0)).image Prod.fst =
          (c.val.image Prod.fst).map (nonrootEmbedding c0) := by
        ext v
        simp [Finset.mem_map, Finset.mem_image, nonrootLiteralEmbedding,
          Function.Embedding.prodMap, exists_and_right]
        aesop
      rw [he, Finset.card_map]
      exact c.property.2⟩

-- @node: liftNonrootClause_ordinary
/-- [Lifting any proper three-clause on the nonroot variables produces an
ordinary clause, containing no variable of the fixed root clause](goal). -/
lemma liftNonrootClause_ordinary (c0 : ProperClause n)
    (c : ProperClause (nonrootCount n)) : isOrdinary c0 (liftNonrootClause c0 c) := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro l hl
  obtain ⟨hl, hr⟩ := Finset.mem_filter.mp hl
  obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hl
  exact nonrootEmbedding_not_root c0 k.1 hr

-- @node: liftNonrootClause_injective
/-- [Relabeling proper three-clauses on the nonroot variables as clauses on
the original variables is injective](goal). -/
lemma liftNonrootClause_injective (c0 : ProperClause n) :
    Function.Injective (liftNonrootClause c0) := by
  intro a b hab
  apply Subtype.ext
  exact Finset.map_injective (nonrootLiteralEmbedding c0) (congrArg Subtype.val hab)

-- @node: ordinary_literal_in_range
/-- If [a clause is ordinary relative to the fixed root clause](hyp:hc) and
[a literal belongs to that clause](hyp:hl), then [that literal is the image
of a nonroot literal under the sign-preserving relabeling](goal). -/
lemma ordinary_literal_in_range (c0 c : ProperClause n) (hc : isOrdinary c0 c)
    (l : Fin n × Bool) (hl : l ∈ c.val) :
    l ∈ Set.range (nonrootLiteralEmbedding c0) := by
  have hn : l.1 ∉ roots c0 := by
    intro hr
    have : l ∈ rootLiterals c0 c := Finset.mem_filter.mpr ⟨hl, hr⟩
    rw [hc] at this
    exact Finset.notMem_empty _ this
  refine ⟨(nonrootEquiv c0 ⟨l.1, hn⟩, l.2), ?_⟩
  apply Prod.ext
  · exact congrArg Subtype.val ((nonrootEquiv c0).symm_apply_apply ⟨l.1, hn⟩)
  · rfl

-- @node: liftNonrootClause_surjective
/-- If [a clause is ordinary relative to the fixed root clause](hyp:hc), then
[it is the lift of some proper three-clause on the nonroot variables](goal). -/
lemma liftNonrootClause_surjective (c0 c : ProperClause n) (hc : isOrdinary c0 c) :
    ∃ b : ProperClause (nonrootCount n), liftNonrootClause c0 b = c := by
  classical
  let e := nonrootLiteralEmbedding c0
  let t := c.val.preimage e e.injective.injOn
  have ht : t.map e = c.val := by
    rw [Finset.map_eq_image, Finset.image_preimage]
    exact Finset.filter_eq_self.mpr (fun l hl => ordinary_literal_in_range c0 c hc l hl)
  have hvars : (t.map e).image Prod.fst =
      (t.image Prod.fst).map (nonrootEmbedding c0) := by
    ext v
    simp [e, Finset.mem_map, Finset.mem_image, nonrootLiteralEmbedding,
      Function.Embedding.prodMap, exists_and_right]
    aesop
  have hproper : t.card = 3 ∧ (t.image Prod.fst).card = 3 := by
    constructor
    · simpa [← ht] using c.property.1
    · have h := c.property.2
      rw [← ht, hvars, Finset.card_map] at h
      exact h
  exact ⟨⟨t, hproper⟩, Subtype.ext ht⟩

-- @node: ordinaryClauseEquiv
/-- In a model with [a given number of variables](hyp:n), [a fixed root
clause](hyp:c0) determines [a bijection between proper three-clauses on the
nonroot variables and ordinary proper three-clauses on the original
variables, given by sign-preserving relabeling](goal). -/
def ordinaryClauseEquiv (c0 : ProperClause n) :
    ProperClause (nonrootCount n) ≃ {c : ProperClause n // isOrdinary c0 c} :=
  Equiv.ofBijective (fun c => ⟨liftNonrootClause c0 c, liftNonrootClause_ordinary c0 c⟩)
    ⟨fun _ _ h => liftNonrootClause_injective c0 (congrArg Subtype.val h), by
      rintro ⟨c, hc⟩
      obtain ⟨b, hb⟩ := liftNonrootClause_surjective c0 c hc
      exact ⟨b, Subtype.ext hb⟩⟩

-- @node: liftNonrootClause_sat
/-- [A nonroot assignment extended by the fixed root assignment satisfies
a lifted clause if and only if the original nonroot assignment satisfies
the original nonroot clause](goal). -/
lemma liftNonrootClause_sat (c0 : ProperClause n)
    (c : ProperClause (nonrootCount n)) (z : Fin (nonrootCount n) → Bool) :
    ClauseSat (liftNonrootClause c0 c) (glueAssignment c0 z) ↔ ClauseSat c z := by
  classical
  have hg (v : Fin (nonrootCount n)) :
      glueAssignment c0 z (nonrootEmbedding c0 v) = z v := by
    rw [glueAssignment, dif_neg (nonrootEmbedding_not_root c0 v)]
    exact congrArg z ((nonrootEquiv c0).apply_symm_apply v)
  simp only [ClauseSat, liftNonrootClause, Finset.mem_map]
  constructor
  · rintro ⟨l, ⟨k, hk, rfl⟩, hs⟩
    exact ⟨k, hk, (hg k.1).symm.trans hs⟩
  · rintro ⟨k, hk, hs⟩
    exact ⟨nonrootLiteralEmbedding c0 k, ⟨k, hk, rfl⟩, (hg k.1).trans hs⟩

open Classical in
-- @node: nonrootSolutions_succ
/-- If [the current time is at least the omitted index](hyp:hs), then [the
nonroot solutions at the next time are exactly the current nonroot solutions
whose extensions by the fixed root assignment satisfy the next clause](goal). -/
lemma nonrootSolutions_succ (c0 : ProperClause n) (Cseq : ℕ → Ω → ProperClause n)
    (i s : ℕ) (hs : i ≤ s) (ω : Ω) :
    nonrootSolutions c0 Cseq i (s + 1) ω =
      (nonrootSolutions c0 Cseq i s ω).filter
        (fun z => ClauseSat (Cseq (s + 1) ω) (glueAssignment c0 z)) := by
  classical
  ext z
  simp only [nonrootSolutions, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    exact ⟨fun j hj hji => h j (Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hj).1, (Finset.mem_Icc.mp hj).2.trans (Nat.le_succ s)⟩) hji,
      h (s + 1) (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩) (by omega)⟩
  · rintro ⟨h, hnext⟩ j hj hji
    obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
    by_cases hjs : j ≤ s
    · exact h j (Finset.mem_Icc.mpr ⟨hj1, hjs⟩) hji
    · have : j = s + 1 := by omega
      simpa [this] using hnext

-- @node: nonrootSolutions_ordinary_succ
/-- If [the current time is at least the omitted index](hyp:hs) and [the next
clause is the lift of a specified nonroot clause](hyp:hc), then [the nonroot
solutions at the next time are exactly the current solutions surviving that
nonroot clause](goal). -/
lemma nonrootSolutions_ordinary_succ (c0 : ProperClause n)
    (Cseq : ℕ → Ω → ProperClause n) (i s : ℕ) (hs : i ≤ s) (ω : Ω)
    (c : ProperClause (nonrootCount n)) (hc : Cseq (s + 1) ω = liftNonrootClause c0 c) :
    nonrootSolutions c0 Cseq i (s + 1) ω =
      survivors (nonrootSolutions c0 Cseq i s ω) c := by
  rw [nonrootSolutions_succ c0 Cseq i s hs ω, hc]
  classical
  ext z
  simp only [survivors, Finset.mem_filter, liftNonrootClause_sat]

open Classical in
/-- If [there are at least six variables](hyp:hn), then [the arithmetic
average of a real function over ordinary proper three-clauses equals its
expectation after lifting a uniformly sampled proper three-clause on the
nonroot variables](goal). -/
-- @node: ordinaryClause_average
lemma ordinaryClause_average (c0 : ProperClause n) (hn : OmissionN n)
    (f : ProperClause n → ℝ) :
    (∑ c : ProperClause n, if isOrdinary c0 c then f c else 0) /
        Fintype.card {c : ProperClause n // isOrdinary c0 c} =
      ∫ c, f (liftNonrootClause c0 c) ∂(uniformClauseMeasure (nonrootCount n) 3) := by
  have hu : 3 ≤ nonrootCount n := by unfold OmissionN at hn; unfold nonrootCount; omega
  rw [integral_uniformClause_eq_expect 3 hu, Fintype.expect_eq_sum_div_card]
  have hsum : (∑ c : ProperClause n, if isOrdinary c0 c then f c else 0) =
      ∑ c : {c : ProperClause n // isOrdinary c0 c}, f c := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp) f
  rw [hsum, ← Fintype.card_congr (ordinaryClauseEquiv c0)]
  congr 1
  exact ((ordinaryClauseEquiv c0).sum_comp (fun c => f c.val)).symm

open Classical in
/-- If [there are at least six variables](hyp:hn) and [the integer potential
length is at least one](hyp:hd), then [the indicator that the nonroot
assignment set is nonempty times its killing probability to the three-halves
power is at most three times the square root of the potential length times
the average potential increase over ordinary proper three-clauses, plus the
potential length to the three-halves power divided by the cube of the nonroot
count](goal). -/
-- @node: occupation_ordinary_drift_average
lemma occupation_ordinary_drift_average (hn : OmissionN n) (c0 : ProperClause n)
    (d : ℕ) (hd : PotentialD d) (S : Finset (Fin (nonrootCount n) → Bool)) :
    (if S.Nonempty then (1 : ℝ) else 0) * killProb d S ^ beta ≤
      3 * (d : ℝ) ^ (beta - 1) *
        ((∑ c : ProperClause n, if isOrdinary c0 c then
          potential d (S.filter (fun z => ClauseSat c (glueAssignment c0 z))) -
            potential d S else 0) /
          Fintype.card {c : ProperClause n // isOrdinary c0 c}) +
      (d : ℝ) ^ beta * (nonrootCount n : ℝ) ^ (-3 : ℝ) := by
  have hu : OneU (nonrootCount n) := by unfold OmissionN at hn; unfold OneU nonrootCount; omega
  rw [ordinaryClause_average c0 hn]
  have he (c : ProperClause (nonrootCount n)) :
      S.filter (fun z => ClauseSat (liftNonrootClause c0 c) (glueAssignment c0 z)) =
        survivors S c := by
    ext z
    simp only [Finset.mem_filter, survivors, liftNonrootClause_sat]
  simpa only [he] using occupation_uniform_drift hu d hd S

end Papers.OaiLinearVarianceRandom

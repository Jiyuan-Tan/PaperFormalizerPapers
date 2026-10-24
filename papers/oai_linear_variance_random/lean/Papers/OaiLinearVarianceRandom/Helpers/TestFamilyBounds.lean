module

public import Papers.OaiLinearVarianceRandom.Helpers.TestClauses
public import Papers.OaiLinearVarianceRandom.Helpers.TestFamilyConditioning

/-! # Killing probabilities on observed root test families

Each root's test coordinates have the same single-root-literal fiber.
Reindexing their product identifies the family killing fraction with `killProb`.
-/

public section

namespace Papers.OaiLinearVarianceRandom
open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {n : ℕ}

open Classical in
/-- If [a clause is a test relative to the reference clause](hyp:ht) and
[the chosen root is a true root of that test](hyp:hx), then [the test's root
literals consist exactly of that root with the sign opposite to its sign in
the reference clause](goal). -/
-- @node: rootLiterals_eq_singleton_of_test_root
lemma rootLiterals_eq_singleton_of_test_root (c0 c : ProperClause n)
    (x : roots c0) (ht : isTest c0 c) (hx : x.val ∈ trueRootVars c0 c) :
    rootLiterals c0 c = {(x.val, !decide ((x.val, true) ∈ c0.val))} := by
  obtain ⟨r, hr⟩ := Finset.card_eq_one.mp ht.1
  obtain ⟨l, hl, hxl⟩ := Finset.mem_image.mp hx
  obtain ⟨hl, htrue⟩ := Finset.mem_filter.mp hl
  rw [hr, Finset.mem_singleton] at hl
  subst l
  have hs : r.2 = !decide ((x.val, true) ∈ c0.val) := by
    rw [hxl] at htrue
    cases hb : decide ((x.val, true) ∈ c0.val) <;> cases hs : r.2 <;> simp_all
  rw [hr, show r = (x.val, !decide ((x.val, true) ∈ c0.val)) from Prod.ext hxl hs]

open Classical in
/-- If [the variable of the fixed literal is a root of the reference
clause](hyp:hr), then [the fraction of clause families with exactly that root
literal that collectively falsify every nonroot assignment in the chosen set
equals the canonical killing probability for a family of the same size](goal). -/
-- @node: testClauseFamily_kill_fraction_fintype
lemma testClauseFamily_kill_fraction_fintype {I : Type*} [Fintype I]
    (c0 : ProperClause n) (r : Fin n × Bool) (hr : r.1 ∈ roots c0)
    (S : Finset (Fin (nonrootCount n) → Bool)) :
    (Fintype.card {cs : I → {c : ProperClause n // rootLiterals c0 c = {r}} //
      ∀ y ∈ S, ∃ k, ¬ testPartSat c0 (cs k).val y} : ℝ) /
        Fintype.card (I → {c : ProperClause n // rootLiterals c0 c = {r}}) =
      killProb (Fintype.card I) S := by
  let e : (I → {c : ProperClause n // rootLiterals c0 c = {r}}) ≃
      (Fin (Fintype.card I) → {c : ProperClause n // rootLiterals c0 c = {r}}) :=
    { toFun := fun cs k => cs ((Fintype.equivFin I).symm k)
      invFun := fun cs k => cs (Fintype.equivFin I k)
      left_inv := by intro cs; funext k; simp
      right_inv := by intro cs; funext k; simp }
  have hk (cs : I → {c : ProperClause n // rootLiterals c0 c = {r}}) :
      (∀ y ∈ S, ∃ k, ¬ testPartSat c0 (cs k).val y) ↔
      (∀ y ∈ S, ∃ k, ¬ testPartSat c0 (e cs k).val y) := by
    constructor
    · intro h y hy
      obtain ⟨k, hk⟩ := h y hy
      exact ⟨Fintype.equivFin I k, by simpa [e] using hk⟩
    · intro h y hy
      obtain ⟨k, hk⟩ := h y hy
      exact ⟨(Fintype.equivFin I).symm k, by simpa [e] using hk⟩
  have hnum := Fintype.card_congr (e.subtypeEquiv
    (p := fun cs => ∀ y ∈ S, ∃ k, ¬ testPartSat c0 (cs k).val y)
    (q := fun cs => ∀ y ∈ S, ∃ k, ¬ testPartSat c0 (cs k).val y) hk)
  have hden := Fintype.card_congr e
  rw [hnum, hden]
  exact testClauseFamily_kill_fraction c0 r hr (Fintype.card I) S

open Classical in
/-- If [every reference clause in the family is a test](hyp:ht) and
[the chosen root is a true root of every such test](hyp:hx), then [among clause
families sharing the reference family's ordinary prefix observations, the
fraction collectively falsifying every assignment in the chosen nonroot set
equals the canonical killing probability for the family's size](goal). -/
-- @node: ordinary_root_test_family_kill_fraction
lemma ordinary_root_test_family_kill_fraction {I : Type*} [Fintype I]
    (c0 : ProperClause n) (a : I → ProperClause n) (m : ℕ) (time : I → ℕ)
    (x : roots c0) (ht : ∀ j, isTest c0 (a j))
    (hx : ∀ j, x.val ∈ trueRootVars c0 (a j))
    (S : Finset (Fin (nonrootCount n) → Bool)) :
    (Fintype.card {cs : ∀ j : I, {c : ProperClause n //
      ordinaryPrefixExposure c0 m (time j) c = ordinaryPrefixExposure c0 m (time j) (a j)} //
      ∀ y ∈ S, ∃ k, ¬ testPartSat c0 (cs k).val y} : ℝ) /
        Fintype.card (∀ j : I, {c : ProperClause n //
          ordinaryPrefixExposure c0 m (time j) c =
            ordinaryPrefixExposure c0 m (time j) (a j)}) =
      killProb (Fintype.card I) S := by
  let r : Fin n × Bool := (x.val, !decide ((x.val, true) ∈ c0.val))
  have he (j : I) (c : ProperClause n) :
      ordinaryPrefixExposure c0 m (time j) c = ordinaryPrefixExposure c0 m (time j) (a j) ↔
        rootLiterals c0 c = {r} := by
    rw [ordinaryPrefixExposure_eq_iff_test c0 (a j) c m (time j) (ht j),
      rootLiterals_eq_singleton_of_test_root c0 (a j) x (ht j) (hx j)]
  let e := Equiv.piCongrRight (fun j : I => Equiv.subtypeEquivRight (he j))
  have hk (cs : ∀ j : I, {c : ProperClause n //
      ordinaryPrefixExposure c0 m (time j) c = ordinaryPrefixExposure c0 m (time j) (a j)}) :
      (∀ y ∈ S, ∃ k, ¬ testPartSat c0 (cs k).val y) ↔
        (∀ y ∈ S, ∃ k, ¬ testPartSat c0 (e cs k).val y) := Iff.rfl
  rw [Fintype.card_congr (e.subtypeEquiv
    (p := fun cs => ∀ y ∈ S, ∃ k, ¬ testPartSat c0 (cs k).val y)
    (q := fun cs => ∀ y ∈ S, ∃ k, ¬ testPartSat c0 (cs k).val y) hk), Fintype.card_congr e]
  exact testClauseFamily_kill_fraction_fintype c0 r x.property S

open Classical in
/-- If [there are at least six variables](hyp:hn) and [the prefix length does
not exceed the cap](hyp:hm), then [the fraction of families sharing the observed
prefix information at the chosen root's test indices that collectively falsify
all nonroot solutions is at most the current killing probability parameter](goal). -/
-- @node: rootTestFamily_observed_kill_fraction_le
lemma rootTestFamily_observed_kill_fraction_le {Ω : Type}
    (hn : OmissionN n) (c0 : ProperClause n) (Cseq : ℕ → Ω → ProperClause n)
    (i m : ℕ) (hm : m ≤ capL n) (x : roots c0) (ω : Ω) :
    (Fintype.card {cs : ∀ j : rootTestFamily c0 Cseq i m x ω, {c : ProperClause n //
      ordinaryPrefixExposure c0 m j c = ordinaryPrefixExposure c0 m j (Cseq j ω)} //
      ∀ y ∈ nonrootSolutions c0 Cseq i m ω, ∃ k, ¬ testPartSat c0 (cs k).val y} : ℝ) /
        Fintype.card (∀ j : rootTestFamily c0 Cseq i m x ω, {c : ProperClause n //
          ordinaryPrefixExposure c0 m j c = ordinaryPrefixExposure c0 m j (Cseq j ω)}) ≤
      killProcess c0 Cseq i m ω := by
  have hf := ordinary_root_test_family_kill_fraction c0
    (fun j : rootTestFamily c0 Cseq i m x ω => Cseq j ω) m (fun j => j.val) x
    (fun j => (Finset.mem_filter.mp j.property).2.1)
    (fun j => (Finset.mem_filter.mp j.property).2.2) (nonrootSolutions c0 Cseq i m ω)
  simp only [← Nat.card_eq_fintype_card] at hf ⊢
  rw [hf]
  have hu : OneU (nonrootCount n) := by
    unfold OneU nonrootCount OmissionN at *
    omega
  apply killProb_mono_length hu _
  simpa using rootTestFamily_card_le_incidenceParam c0 Cseq i m hm x ω

open Classical in
/-- If [the clause index is at most the prefix length](hyp:hjm) and [two clauses
have identical ordinary prefix observations at that index](hyp:he), then
[fixing the roots as prescribed by the reference clause and using any chosen
nonroot assignment satisfies one clause exactly when it satisfies the other](goal). -/
-- @node: ordinaryPrefixExposure_clauseSat_glue_iff
lemma ordinaryPrefixExposure_clauseSat_glue_iff (c0 a c : ProperClause n)
    (m j : ℕ) (hjm : j ≤ m)
    (he : ordinaryPrefixExposure c0 m j c = ordinaryPrefixExposure c0 m j a)
    (y : Fin (nonrootCount n) → Bool) :
    ClauseSat c (glueAssignment c0 y) ↔ ClauseSat a (glueAssignment c0 y) := by
  have hr : rootLiterals c0 c = rootLiterals c0 a := congrArg (fun e => e.1.1) he
  have ho : isOrdinary c0 c ↔ isOrdinary c0 a := by simp only [isOrdinary, hr]
  have ht : isTest c0 c ↔ isTest c0 a := by simp only [isTest, hr]
  by_cases ha : isTest c0 a
  · exact iff_of_true (isTest_clauseSat_glue c0 c y (ht.mpr ha))
      (isTest_clauseSat_glue c0 a y ha)
  · have hca : c = a := by
      by_cases hao : isOrdinary c0 a
      · have h := congrArg Prod.snd he
        simpa [ordinaryPrefixExposure, hjm, ordinaryContents, ho, hao] using h
      · have h := congrArg (fun e => e.1.2) he
        simpa [ordinaryPrefixExposure, expose, ht, ha, ho, hao] using h
    rw [hca]

open Classical in
/-- If [the prefix length does not exceed the cap](hyp:hm) and [two realized
clause sequences have equal ordinary prefix observations at every capped
positive index other than the omitted index](hyp:he), then [their nonroot
solution sets for that prefix and omitted index are equal](goal). -/
-- @node: nonrootSolutions_eq_of_ordinaryPrefixExposure_eq
lemma nonrootSolutions_eq_of_ordinaryPrefixExposure_eq {Ω Ω' : Type}
    (c0 : ProperClause n) (Cseq : ℕ → Ω → ProperClause n)
    (Dseq : ℕ → Ω' → ProperClause n) (i m : ℕ) (hm : m ≤ capL n)
    (ω : Ω) (ω' : Ω')
    (he : ∀ j ∈ (Finset.Icc 1 (capL n)).erase i,
      ordinaryPrefixExposure c0 m j (Cseq j ω) =
        ordinaryPrefixExposure c0 m j (Dseq j ω')) :
    nonrootSolutions c0 Cseq i m ω = nonrootSolutions c0 Dseq i m ω' := by
  have hc (j : ℕ) (hj : j ∈ Finset.Icc 1 m) (hji : j ≠ i)
      (y : Fin (nonrootCount n) → Bool) :
      ClauseSat (Cseq j ω) (glueAssignment c0 y) ↔
        ClauseSat (Dseq j ω') (glueAssignment c0 y) := by
    exact ordinaryPrefixExposure_clauseSat_glue_iff c0 _ _ m j
      (Finset.mem_Icc.mp hj).2 (he j (Finset.mem_erase.mpr ⟨hji,
        Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hj).1, (Finset.mem_Icc.mp hj).2.trans hm⟩⟩)) y
  ext y
  simp only [nonrootSolutions, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h j hj hji => (hc j hj hji y).mp (h j hj hji),
    fun h j hj hji => (hc j hj hji y).mpr (h j hj hji)⟩

open Classical in
/-- If [the prefix length does not exceed the cap](hyp:hm) and [two realized
clause sequences have equal ordinary prefix observations at every capped
positive index other than the omitted index](hyp:he), then [their test index
families for the chosen root and prefix are equal](goal). -/
-- @node: rootTestFamily_eq_of_ordinaryPrefixExposure_eq
lemma rootTestFamily_eq_of_ordinaryPrefixExposure_eq {Ω Ω' : Type}
    (c0 : ProperClause n) (Cseq : ℕ → Ω → ProperClause n)
    (Dseq : ℕ → Ω' → ProperClause n) (i m : ℕ) (hm : m ≤ capL n)
    (ω : Ω) (ω' : Ω') (x : roots c0)
    (he : ∀ j ∈ (Finset.Icc 1 (capL n)).erase i,
      ordinaryPrefixExposure c0 m j (Cseq j ω) =
        ordinaryPrefixExposure c0 m j (Dseq j ω')) :
    rootTestFamily c0 Cseq i m x ω = rootTestFamily c0 Dseq i m x ω' := by
  apply Finset.filter_congr
  intro j hj
  obtain ⟨hji, hj⟩ := Finset.mem_erase.mp hj
  have hr := congrArg (fun e => e.1.1) (he j (Finset.mem_erase.mpr ⟨hji,
    Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hj).1, (Finset.mem_Icc.mp hj).2.trans hm⟩⟩))
  change rootLiterals c0 (Cseq j ω) = rootLiterals c0 (Dseq j ω') at hr
  simp only [isTest, trueRootVars, hr]

open Classical in
/-- If [two realized clause sequences have equal ordinary prefix observations
at every capped positive index other than the omitted index](hyp:he), then
[their sets of available roots are equal](goal). -/
-- @node: availableRoots_eq_of_ordinaryPrefixExposure_eq
lemma availableRoots_eq_of_ordinaryPrefixExposure_eq {Ω Ω' : Type}
    (c0 : ProperClause n) (Cseq : ℕ → Ω → ProperClause n)
    (Dseq : ℕ → Ω' → ProperClause n) (i m : ℕ) (ω : Ω) (ω' : Ω')
    (he : ∀ j ∈ (Finset.Icc 1 (capL n)).erase i,
      ordinaryPrefixExposure c0 m j (Cseq j ω) =
        ordinaryPrefixExposure c0 m j (Dseq j ω')) :
    availableRoots c0 Cseq i ω = availableRoots c0 Dseq i ω' := by
  unfold availableRoots
  congr 1
  apply Finset.biUnion_congr rfl
  intro j hj
  have hr := congrArg (fun e => e.1.1) (he j hj)
  change rootLiterals c0 (Cseq j ω) = rootLiterals c0 (Dseq j ω') at hr
  simp only [collisionBlockedRoots, trueRootVars, hr]
  rfl

open Classical in
/-- If [two realized clause sequences have equal ordinary prefix observations
at every capped positive index other than the omitted index](hyp:he), then
[their incidence parameters are equal](goal). -/
-- @node: incidenceParam_eq_of_ordinaryPrefixExposure_eq
lemma incidenceParam_eq_of_ordinaryPrefixExposure_eq {Ω Ω' : Type}
    (c0 : ProperClause n) (Cseq : ℕ → Ω → ProperClause n)
    (Dseq : ℕ → Ω' → ProperClause n) (i m : ℕ) (ω : Ω) (ω' : Ω')
    (he : ∀ j ∈ (Finset.Icc 1 (capL n)).erase i,
      ordinaryPrefixExposure c0 m j (Cseq j ω) =
        ordinaryPrefixExposure c0 m j (Dseq j ω')) :
    incidenceParam c0 Cseq i ω = incidenceParam c0 Dseq i ω' := by
  unfold incidenceParam incidenceCount
  congr 2
  apply Finset.filter_congr
  intro j hj
  have hr : rootLiterals c0 (Cseq j ω) = rootLiterals c0 (Dseq j ω') :=
    congrArg (fun e => e.1.1) (he j hj)
  rw [hr]

open Classical in
/-- If [the prefix length does not exceed the cap](hyp:hm) and [two realized
clause sequences have equal ordinary prefix observations at every capped
positive index other than the omitted index](hyp:he), then [their killing
probability parameters for that prefix are equal](goal). -/
-- @node: killProcess_eq_of_ordinaryPrefixExposure_eq
lemma killProcess_eq_of_ordinaryPrefixExposure_eq {Ω Ω' : Type}
    (c0 : ProperClause n) (Cseq : ℕ → Ω → ProperClause n)
    (Dseq : ℕ → Ω' → ProperClause n) (i m : ℕ) (hm : m ≤ capL n)
    (ω : Ω) (ω' : Ω')
    (he : ∀ j ∈ (Finset.Icc 1 (capL n)).erase i,
      ordinaryPrefixExposure c0 m j (Cseq j ω) =
        ordinaryPrefixExposure c0 m j (Dseq j ω')) :
    killProcess c0 Cseq i m ω = killProcess c0 Dseq i m ω' := by
  unfold killProcess
  rw [incidenceParam_eq_of_ordinaryPrefixExposure_eq c0 Cseq Dseq i m ω ω' he,
    nonrootSolutions_eq_of_ordinaryPrefixExposure_eq c0 Cseq Dseq i m hm ω ω' he]

open Classical in
/-- Suppose [the prefix length does not exceed the cap](hyp:hm), [two realized
clause sequences have equal ordinary prefix observations at every capped
positive index other than the omitted index](hyp:he), [the first sequence's
omitted clause is the reference clause](hyp:hfixed), and [that realization is
pivotal at the omitted index for the prefix](hyp:hp). Then [the second sequence
has a nonroot solution, and every one of its available roots and nonroot
solutions has a test index in its root test family whose clause in the first
sequence falsifies that nonroot assignment's test part](goal). -/
-- @node: pivotal_tests_necessary_on_ordinary_fiber
lemma pivotal_tests_necessary_on_ordinary_fiber {Ω Ω' : Type}
    (c0 : ProperClause n) (Cseq : ℕ → Ω → ProperClause n)
    (Dseq : ℕ → Ω' → ProperClause n) (i m : ℕ) (hm : m ≤ capL n)
    (ω : Ω) (ω' : Ω')
    (he : ∀ j ∈ (Finset.Icc 1 (capL n)).erase i,
      ordinaryPrefixExposure c0 m j (Cseq j ω) =
        ordinaryPrefixExposure c0 m j (Dseq j ω'))
    (hfixed : Cseq i ω = c0) (hp : ω ∈ pivotalEvent Cseq i m) :
    (nonrootSolutions c0 Dseq i m ω').Nonempty ∧
      ∀ x : roots c0, x.val ∈ availableRoots c0 Dseq i ω' →
        ∀ y ∈ nonrootSolutions c0 Dseq i m ω',
          ∃ j ∈ rootTestFamily c0 Dseq i m x ω', ¬ testPartSat c0 (Cseq j ω) y := by
  rw [← nonrootSolutions_eq_of_ordinaryPrefixExposure_eq c0 Cseq Dseq i m hm ω ω' he,
    ← availableRoots_eq_of_ordinaryPrefixExposure_eq c0 Cseq Dseq i m ω ω' he]
  refine ⟨pivotal_nonrootSolutions_nonempty c0 Cseq i m ω hfixed hp, ?_⟩
  intro x hx
  rw [← rootTestFamily_eq_of_ordinaryPrefixExposure_eq c0 Cseq Dseq i m hm ω ω' x he]
  exact pivotal_available_root_tests_kill c0 Cseq i m hm ω hfixed hp x hx

open Classical in
/-- Suppose [there are at least six variables](hyp:hn), [every reference clause
in the family is a test](hyp:ht), [the chosen root is a true root of every such
test](hyp:hx), and [the family size is at most the chosen bound](hyp:hd). Then
[among clause families with the same ordinary prefix observations, the fraction
collectively falsifying every assignment in the chosen nonroot set is at most
the canonical killing probability at that size bound](goal). -/
-- @node: ordinary_root_test_family_kill_fraction_le
lemma ordinary_root_test_family_kill_fraction_le {I : Type*} [Fintype I]
    (hn : OmissionN n) (c0 : ProperClause n) (a : I → ProperClause n)
    (m : ℕ) (time : I → ℕ) (x : roots c0)
    (ht : ∀ j, isTest c0 (a j)) (hx : ∀ j, x.val ∈ trueRootVars c0 (a j))
    (d : ℕ) (hd : Fintype.card I ≤ d) (S : Finset (Fin (nonrootCount n) → Bool)) :
    (Fintype.card {cs : ∀ j : I, {c : ProperClause n //
      ordinaryPrefixExposure c0 m (time j) c = ordinaryPrefixExposure c0 m (time j) (a j)} //
      ∀ y ∈ S, ∃ k, ¬ testPartSat c0 (cs k).val y} : ℝ) /
        Fintype.card (∀ j : I, {c : ProperClause n //
          ordinaryPrefixExposure c0 m (time j) c =
            ordinaryPrefixExposure c0 m (time j) (a j)}) ≤ killProb d S := by
  rw [ordinary_root_test_family_kill_fraction c0 a m time x ht hx S]
  have hu : OneU (nonrootCount n) := by
    unfold OneU nonrootCount OmissionN at *
    omega
  exact killProb_mono_length hu S hd

open Classical in
/-- If [there are at least six variables](hyp:hn) and [the prefix length does
not exceed the cap](hyp:hm), then [the product, over the selected roots, of the
observed-fiber fractions of test families collectively falsifying all nonroot
solutions is at most the current killing probability parameter raised to the
number of selected roots](goal). -/
-- @node: rootTestFamily_observed_kill_product_le
lemma rootTestFamily_observed_kill_product_le {Ω : Type}
    (hn : OmissionN n) (c0 : ProperClause n) (Cseq : ℕ → Ω → ProperClause n)
    (i m : ℕ) (hm : m ≤ capL n) (ω : Ω) (K : Finset (roots c0)) :
    (∏ x ∈ K,
      (Fintype.card {cs : ∀ j : rootTestFamily c0 Cseq i m x ω, {c : ProperClause n //
        ordinaryPrefixExposure c0 m j c = ordinaryPrefixExposure c0 m j (Cseq j ω)} //
        ∀ y ∈ nonrootSolutions c0 Cseq i m ω, ∃ k, ¬ testPartSat c0 (cs k).val y} : ℝ) /
      Fintype.card (∀ j : rootTestFamily c0 Cseq i m x ω, {c : ProperClause n //
        ordinaryPrefixExposure c0 m j c = ordinaryPrefixExposure c0 m j (Cseq j ω)})) ≤
      (killProcess c0 Cseq i m ω) ^ K.card := by
  calc
    _ ≤ ∏ _x ∈ K, killProcess c0 Cseq i m ω := by
      apply Finset.prod_le_prod
      · intro x hx
        exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      · intro x hx
        have h := rootTestFamily_observed_kill_fraction_le hn c0 Cseq i m hm x ω
        simp only [← Nat.card_eq_fintype_card] at h ⊢
        exact h
    _ = _ := by rw [Finset.prod_const]

open Classical in
/-- [With no collisions, the current killing probability parameter raised to
the number of available roots equals its cube; with exactly one collision,
the same power is at most its square](goal). -/
-- @node: availableRoots_killProcess_powers
lemma availableRoots_killProcess_powers {Ω : Type}
    (c0 : ProperClause n) (Cseq : ℕ → Ω → ProperClause n) (i m : ℕ) (ω : Ω) :
    (collisionCount c0 Cseq i ω = 0 →
      (killProcess c0 Cseq i m ω) ^ (availableRoots c0 Cseq i ω).card =
        (killProcess c0 Cseq i m ω) ^ 3) ∧
    (collisionCount c0 Cseq i ω = 1 →
      (killProcess c0 Cseq i m ω) ^ (availableRoots c0 Cseq i ω).card ≤
        (killProcess c0 Cseq i m ω) ^ 2) := by
  constructor
  · intro hv
    rw [availableRoots_card_of_no_collision c0 Cseq i ω hv]
  · intro hv
    have hb := killProb_bounds (incidenceParam c0 Cseq i ω)
      (nonrootSolutions c0 Cseq i m ω)
    exact pow_le_pow_of_le_one hb.1 hb.2
      (two_le_availableRoots_card_of_one_collision c0 Cseq i ω hv)

end Papers.OaiLinearVarianceRandom

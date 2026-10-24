module

public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Probability.UniformOn
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.BorelCantelli
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.Process.HittingTime
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Proper clauses and the random satisfiability process

Clauses are finite sets of signed, distinct Boolean variables. Clause indices are
one based. On sequences with no unsatisfiable prefix the totalized `hittingTime`
is capL n. This is only a bookkeeping value on a null event under the sampling
law, and makes the literal capped minimum agree with the finite-prefix cap.
-/

@[expose] public section

noncomputable section
namespace Papers.OaiLinearVarianceRandom
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option linter.unusedVariables false
set_option warn.classDefReducibility false

/-- With [a universe of n Boolean variables](hyp:n) and [clause arity a](hyp:a),
[a proper clause](goal) has exactly a signed literals on exactly a distinct variables. -/
abbrev ProperClauseA (n a : ℕ) :=
  {s : Finset (Fin n × Bool) // s.card = a ∧ (s.image Prod.fst).card = a}
  -- @realizes x_j(Boolean variables indexed by Fin n)
  -- @realizes a(clause arity, specialized to 2 and 3 below)

/-- Over [n Boolean variables](hyp:n), [a proper three-literal clause](goal)
contains three signed literals on three distinct variables. -/
abbrev ProperClause (n : ℕ) := ProperClauseA n 3

/-- For [n Boolean variables](hyp:n) and [arity a](hyp:a),
[the measurable structure on proper clauses](goal) makes every set of clauses measurable. -/
instance clauseMeasurableSpace (n a : ℕ) : MeasurableSpace (ProperClauseA n a) := ⊤

/-- For [a proper clause](hyp:C), [its variable set](goal) consists of the
distinct Boolean variables occurring in its literals. -/
def clauseVars {n a : ℕ} (C : ProperClauseA n a) : Finset (Fin n) :=
  C.val.image Prod.fst

/-- [Satisfaction](goal) of [a proper clause](hyp:C) by [a Boolean assignment](hyp:z)
means that at least one literal in the clause has the sign assigned to its variable. -/
def ClauseSat {n a : ℕ} (C : ProperClauseA n a) (z : Fin n → Bool) : Prop :=
  ∃ l ∈ C.val, z l.1 = l.2 -- @realizes z(Boolean assignment satisfying a signed literal)

/-- For [n Boolean variables](hyp:n) and [arity a](hyp:a),
[the uniform clause measure](goal) is the uniform counting measure on all proper clauses.

It is a probability measure when the arity does not exceed the number of variables. -/
def uniformClauseMeasure (n a : ℕ) : Measure (ProperClauseA n a) :=
  ProbabilityTheory.uniformOn Set.univ

-- @node: properClauseA_nonempty
/-- If [the clause arity does not exceed the number of variables](hyp:ha),
[there exists a proper clause of that arity](goal). -/
lemma properClauseA_nonempty (n a : ℕ) (ha : a ≤ n) :
    Nonempty (ProperClauseA n a) := by
  classical
  obtain ⟨s, _, hs⟩ := Finset.exists_subset_card_eq
    (s := Finset.univ (α := Fin n)) (by simpa using ha)
  refine ⟨⟨s.image (fun v => (v, false)), ?_, ?_⟩⟩
  · rw [Finset.card_image_of_injective _ (by
      intro v w h
      exact Prod.mk.inj h |>.1), hs]
  · simpa [Finset.image_image, Function.comp_def] using hs

/-- From [a set of exactly a variables](hyp:s) and [a Boolean sign for each variable in that set](hyp:f),
[the constructed proper clause](goal) contains those variables with those signs. -/
-- @node: properClauseOfSigns
def properClauseOfSigns {n a : ℕ} (s : {s : Finset (Fin n) // s.card = a})
    (f : s.val → Bool) : ProperClauseA n a := by
  classical
  refine ⟨Finset.univ.image (fun v : s.val => (v.val, f v)), ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ (by
      intro v w h
      exact Subtype.ext (Prod.mk.inj h).1)]
    simpa using s.property
  · have hs : (Finset.univ.image (fun v : s.val => (v.val, f v))).image Prod.fst =
        s.val := by
      ext v
      simp
    rw [hs, s.property]

/-- [Pairing a support of size a with a Boolean sign at each variable gives a
one-to-one correspondence with proper clauses of arity a](goal). -/
-- @node: properClauseOfSigns_bijective
lemma properClauseOfSigns_bijective (n a : ℕ) :
    Function.Bijective (fun sf : (Σ s : {s : Finset (Fin n) // s.card = a},
      s.val → Bool) => properClauseOfSigns sf.1 sf.2) := by
  classical
  have support (s : {s : Finset (Fin n) // s.card = a}) (f : s.val → Bool) :
      clauseVars (properClauseOfSigns s f) = s.val := by
    ext v
    simp [clauseVars, properClauseOfSigns]
  constructor
  · rintro ⟨s, f⟩ ⟨t, g⟩ h
    have hst : s = t := Subtype.ext (by
      simpa only [support] using congrArg clauseVars h)
    subst t
    change properClauseOfSigns s f = properClauseOfSigns s g at h
    have hfg : f = g := by
      funext v
      have hm : (v.val, f v) ∈ (properClauseOfSigns s g).val := by
        rw [← h]
        simp [properClauseOfSigns]
      exact (show g v = f v by simpa [properClauseOfSigns] using hm).symm
    subst g
    rfl
  · intro C
    let s : {s : Finset (Fin n) // s.card = a} := ⟨clauseVars C, C.property.2⟩
    have hex (v : s.val) : ∃ b : Bool, (v.val, b) ∈ C.val := by
      have hv := v.property
      simp only [s, clauseVars, Finset.mem_image] at hv
      obtain ⟨⟨w, b⟩, hb, hw⟩ := hv
      exact ⟨b, hw ▸ hb⟩
    let f : s.val → Bool := fun v => Classical.choose (hex v)
    have hf (v : s.val) : (v.val, f v) ∈ C.val := Classical.choose_spec (hex v)
    refine ⟨⟨s, f⟩, Subtype.ext ?_⟩
    apply Finset.eq_of_subset_of_card_le
    · intro l hl
      obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hl
      exact hf v
    · exact le_of_eq (C.property.1.trans (properClauseOfSigns s f).property.1.symm)

-- @node: card_properClauseA
/-- [The number of proper clauses of arity a on n variables is two to the power a
times the number of ways to choose a variables from n](goal). -/
lemma card_properClauseA (n a : ℕ) :
    Fintype.card (ProperClauseA n a) = 2 ^ a * n.choose a := by
  classical
  calc
    Fintype.card (ProperClauseA n a) =
        Fintype.card (Σ s : {s : Finset (Fin n) // s.card = a}, s.val → Bool) :=
      (Fintype.card_congr (Equiv.ofBijective _ (properClauseOfSigns_bijective n a))).symm
    _ = ∑ s : {s : Finset (Fin n) // s.card = a}, 2 ^ a := by
      rw [Fintype.card_sigma]
      apply Finset.sum_congr rfl
      intro s _
      simp [Fintype.card_coe, s.property]
    _ = 2 ^ a * n.choose a := by
      simp [Fintype.card_finset_len, Nat.mul_comm]


-- @node: ass:main-n
/-- For [a variable count n](hyp:n), [the main size condition](goal) requires at least three variables. -/
def MainN (n : ℕ) : Prop := 3 ≤ n -- @realizes n(integer variable count at least three)

-- @node: ass:omission-n
/-- For [a variable count n](hyp:n), [the omission size condition](goal) requires at least six variables. -/
def OmissionN (n : ℕ) : Prop := 6 ≤ n -- @realizes n(omission regime at least six)

-- @env: S1
variable {n : ℕ} {Ω : Type} [MeasurableSpace Ω]

-- @node: ass:main-law
/-- Under [a measure on outcomes](hyp:μ), [a sequence of random proper three-literal
clauses](hyp:Cseq) on [n variables](hyp:n) satisfies [the uniform clause process law](goal)
when [each positively indexed clause is measurable](step:1), [these clauses are mutually
independent](step:2), and [each has the uniform clause distribution](step:3). -/
def IsUniformClauseProcess (μ : Measure Ω) (Cseq : ℕ → Ω → ProperClause n) : Prop :=
  (∀ j, 1 ≤ j → Measurable (Cseq j)) ∧ -- @realizes C_j(measurable at positive indices)
  iIndepFun (fun j => Cseq (j + 1)) μ ∧ -- @realizes C_j(independent sampling with replacement)
  ∀ j, 1 ≤ j → μ.map (Cseq j) = uniformClauseMeasure n 3 -- @realizes C_j(uniform law)

/-- For [a sequence of proper three-literal clauses](hyp:c) on [n variables](hyp:n)
and [a prefix length m](hyp:m), [the prefix formula](goal) is the ordered list
of clauses at indices one through m. -/
def prefixFormula (c : ℕ → ProperClause n) (m : ℕ) : List (ProperClause n) :=
  ((List.range m).map (fun j => c (j + 1))) -- @realizes F_m(conjunction of the first m clauses)

/-- For [a clause sequence](hyp:c) on [n variables](hyp:n) and [a prefix length m](hyp:m),
[prefix satisfiability](goal) means that one Boolean assignment satisfies every
clause at indices one through m. -/
def PrefixSat (c : ℕ → ProperClause n) (m : ℕ) : Prop :=
  ∃ z : Fin n → Bool, ∀ j ∈ Finset.Icc 1 m, ClauseSat (c j) z
  -- @realizes m(nonnegative prefix index)
  -- @realizes j(clause indices one through m)

/-- For [a variable count n](hyp:n), [the deterministic cap](goal) is ten times n. -/
def capL (n : ℕ) : ℕ := 10 * n -- @realizes L(cap equals ten times n)

open Classical in
-- @node: def:main-process
/-- For [a clause sequence](hyp:c) on [n variables](hyp:n), [the hitting time](goal)
is [the first positive index with an unsatisfiable prefix, if one exists](step:1),
and [ten times n if every prefix is satisfiable](step:2). -/
def hittingTime (c : ℕ → ProperClause n) : ℕ :=
  if ∃ m, 1 ≤ m ∧ ¬ PrefixSat c m then
    sInf {m | 1 ≤ m ∧ ¬ PrefixSat c m}
  else capL n
  -- @realizes H_n(first unsatisfiable prefix; capL n only on the null event of no hit)

/-- For [a clause sequence](hyp:c) on [n variables](hyp:n), [the capped time](goal)
is the minimum of its hitting time and ten times n.

If every prefix is satisfiable, the hitting time and the capped time both equal the cap. -/
-- @node: def:omission-cap
def cappedTime (c : ℕ → ProperClause n) : ℕ :=
  min (hittingTime c) (capL n)
  -- @realizes T(the minimum of H_n and L)

/-- [The capped time equals the first unsatisfiable prefix index between one
and the cap, with the cap returned if no such index exists](goal). -/
lemma cappedTime_eq_hittingBtwn (c : ℕ → ProperClause n) :
    cappedTime c =
      MeasureTheory.hittingBtwn (fun m (_ : Unit) => ¬ PrefixSat c m)
        {True} 1 (capL n) () := by
  classical
  unfold cappedTime
  by_cases h : ∃ m, 1 ≤ m ∧ ¬ PrefixSat c m
  · have hmem : 1 ≤ hittingTime c ∧ ¬ PrefixSat c (hittingTime c) := by
      simpa only [hittingTime, if_pos h, Set.mem_ofPred_eq] using
        (Nat.sInf_mem (s := {m | 1 ≤ m ∧ ¬ PrefixSat c m}) h)
    have hle : ∀ m, 1 ≤ m → ¬ PrefixSat c m → hittingTime c ≤ m := by
      intro m hm hs
      simpa only [hittingTime, if_pos h] using
        (Nat.sInf_le (s := {m | 1 ≤ m ∧ ¬ PrefixSat c m}) ⟨hm, hs⟩)
    unfold MeasureTheory.hittingBtwn
    simp only [Set.mem_Icc, Set.mem_singleton_iff, eq_iff_iff, iff_true]
    by_cases hHL : hittingTime c ≤ capL n
    · rw [min_eq_left hHL, if_pos ⟨hittingTime c, ⟨hmem.1, hHL⟩, hmem.2⟩]
      apply le_antisymm
      · apply le_csInf
        · exact ⟨hittingTime c, ⟨hmem.1, hHL⟩, hmem.2⟩
        · intro k hk
          exact hle k hk.1.1 hk.2
      · exact Nat.sInf_le ⟨⟨hmem.1, hHL⟩, hmem.2⟩
    · have hno : ¬ ∃ m, (1 ≤ m ∧ m ≤ capL n) ∧ ¬ PrefixSat c m := by
        rintro ⟨m, ⟨hm, hmL⟩, hs⟩
        exact hHL ((hle m hm hs).trans hmL)
      rw [if_neg hno, min_eq_right (le_of_lt (lt_of_not_ge hHL))]
  · have hno : ¬ ∃ m, (1 ≤ m ∧ m ≤ capL n) ∧ ¬ PrefixSat c m := by
      rintro ⟨m, ⟨hm, _⟩, hs⟩
      exact h ⟨m, hm, hs⟩
    simp only [hittingTime, if_neg h, min_self, MeasureTheory.hittingBtwn,
      Set.mem_Icc, Set.mem_singleton_iff, eq_iff_iff, iff_true, if_neg hno]

/-- If [two clause sequences agree at every index from one through the cap](hyp:h),
[their capped times are equal](goal). -/
lemma cappedTime_congr (c c' : ℕ → ProperClause n)
    (h : ∀ j ∈ Finset.Icc 1 (capL n), c j = c' j) :
    cappedTime c = cappedTime c' := by
  classical
  have hsat (m : ℕ) (hm : m ≤ capL n) : PrefixSat c m ↔ PrefixSat c' m := by
    have heq (j : ℕ) (hj : j ∈ Finset.Icc 1 m) : c j = c' j :=
      h j (Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp hj).1, (Finset.mem_Icc.mp hj).2.trans hm⟩)
    unfold PrefixSat
    constructor
    · rintro ⟨z, hz⟩
      exact ⟨z, fun j hj => heq j hj ▸ hz j hj⟩
    · rintro ⟨z, hz⟩
      exact ⟨z, fun j hj => (heq j hj).symm ▸ hz j hj⟩
  have hset : (Set.Icc 1 (capL n) ∩ {m | ¬ PrefixSat c m}) =
      (Set.Icc 1 (capL n) ∩ {m | ¬ PrefixSat c' m}) := by
    ext m
    constructor
    · rintro ⟨hm, hs⟩
      exact ⟨hm, fun hs' => hs ((hsat m hm.2).mpr hs')⟩
    · rintro ⟨hm, hs⟩
      exact ⟨hm, fun hs' => hs ((hsat m hm.2).mp hs')⟩
  have hex : (∃ m ∈ Set.Icc 1 (capL n), ¬ PrefixSat c m) ↔
      (∃ m ∈ Set.Icc 1 (capL n), ¬ PrefixSat c' m) := by
    change (Set.Icc 1 (capL n) ∩ {m | ¬ PrefixSat c m}).Nonempty ↔
      (Set.Icc 1 (capL n) ∩ {m | ¬ PrefixSat c' m}).Nonempty
    rw [hset]
  rw [cappedTime_eq_hittingBtwn, cappedTime_eq_hittingBtwn]
  simp only [MeasureTheory.hittingBtwn, Set.mem_singleton_iff, eq_iff_iff, iff_true]
  rw [hset, hex]

-- @node: def:omission-formula
/-- For [a clause sequence](hyp:c) on [n variables](hyp:n), [an index to omit](hyp:i),
and [a prefix length m](hyp:m), [omitted prefix satisfiability](goal) means that
one Boolean assignment satisfies every clause at indices one through m except the omitted index. -/
def omittedPrefixSat (c : ℕ → ProperClause n) (i m : ℕ) : Prop :=
  ∃ z : Fin n → Bool, ∀ j ∈ Finset.Icc 1 m, j ≠ i → ClauseSat (c j) z
  -- @realizes B_m^{(i)}(original-index conjunction excluding i)

-- @node: def:omission-time-delay
/-- For [a clause sequence](hyp:c) on [n variables](hyp:n) and [an omitted index](hyp:i),
[the omitted capped time](goal) is the first original prefix index from one through
ten times n that is unsatisfiable after omitting that clause, or the cap if none exists. -/
def omittedCappedTime (c : ℕ → ProperClause n) (i : ℕ) : ℕ :=
  MeasureTheory.hittingBtwn (fun m (_ : Unit) => ¬ omittedPrefixSat c i m)
    {True} 1 (capL n) ()
  -- @realizes T^{(i)}(omitted first unsatisfiable original index, capped at L)

/-- For [a clause sequence](hyp:c) on [n variables](hyp:n) and [an omitted clause index](hyp:i),
[the omission delay](goal) is the omitted capped time minus the original capped
time, with subtraction truncated at zero. -/
def delay (c : ℕ → ProperClause n) (i : ℕ) : ℕ :=
  omittedCappedTime c i - cappedTime c -- @realizes D_i(nonnegative omission delay T^(i) minus T)

-- @node: prefixSat_antitone
/-- [If a prefix of a clause sequence is satisfiable, every shorter prefix is satisfiable](goal). -/
lemma prefixSat_antitone (c : ℕ → ProperClause n) : Antitone (PrefixSat c) := by
  intro a b hab
  rintro ⟨z, hz⟩
  exact ⟨z, fun j hj => hz j (Finset.mem_Icc.mpr
    ⟨(Finset.mem_Icc.mp hj).1, (Finset.mem_Icc.mp hj).2.trans hab⟩)⟩

-- @node: omittedPrefixSat_antitone
/-- [If a prefix is satisfiable after omitting a fixed clause index, every shorter
prefix is satisfiable after the same omission](goal). -/
lemma omittedPrefixSat_antitone (c : ℕ → ProperClause n) (i : ℕ) :
    Antitone (omittedPrefixSat c i) := by
  intro a b hab
  rintro ⟨z, hz⟩
  exact ⟨z, fun j hj => hz j (Finset.mem_Icc.mpr
    ⟨(Finset.mem_Icc.mp hj).1, (Finset.mem_Icc.mp hj).2.trans hab⟩)⟩

-- @node: cappedTime_le_iff
/-- If [m is at least one](hyp:hm) and [m is strictly below the cap](hyp:hmL),
[the capped time is at most m exactly when the first m clauses are unsatisfiable](goal). -/
lemma cappedTime_le_iff (c : ℕ → ProperClause n) (m : ℕ)
    (hm : 1 ≤ m) (hmL : m < capL n) :
    cappedTime c ≤ m ↔ ¬ PrefixSat c m := by
  rw [cappedTime_eq_hittingBtwn, MeasureTheory.hittingBtwn_le_iff_of_lt m hmL]
  simp only [Set.mem_singleton_iff, eq_iff_iff, iff_true]
  constructor
  · rintro ⟨j, hj, hs⟩ hsat
    exact hs (prefixSat_antitone c hj.2 hsat)
  · intro hs
    exact ⟨m, ⟨hm, le_rfl⟩, hs⟩

-- @node: omittedCappedTime_le_iff
/-- If [m is at least one](hyp:hm) and [m is strictly below the cap](hyp:hmL),
[the omitted capped time is at most m exactly when the first m clauses, with
the designated index omitted, are unsatisfiable](goal). -/
lemma omittedCappedTime_le_iff (c : ℕ → ProperClause n) (i m : ℕ)
    (hm : 1 ≤ m) (hmL : m < capL n) :
    omittedCappedTime c i ≤ m ↔ ¬ omittedPrefixSat c i m := by
  rw [omittedCappedTime, MeasureTheory.hittingBtwn_le_iff_of_lt m hmL]
  simp only [Set.mem_singleton_iff, eq_iff_iff, iff_true]
  constructor
  · rintro ⟨j, hj, hs⟩ hsat
    exact hs (omittedPrefixSat_antitone c i hj.2 hsat)
  · intro hs
    exact ⟨m, ⟨hm, le_rfl⟩, hs⟩

-- @node: cappedTime_le_omittedCappedTime
/-- With [at least six variables](hyp:hn), [the capped time of any clause sequence
is no greater than its capped time after omitting one clause](goal). -/
lemma cappedTime_le_omittedCappedTime (hn : OmissionN n)
    (c : ℕ → ProperClause n) (i : ℕ) : cappedTime c ≤ omittedCappedTime c i := by
  classical
  by_cases h : omittedCappedTime c i < capL n
  · have hpos : 1 ≤ omittedCappedTime c i := by
      apply MeasureTheory.le_hittingBtwn (u := fun m (_ : Unit) =>
        ¬ omittedPrefixSat c i m) (s := {True}) (ω := ())
      unfold capL
      unfold OmissionN at hn
      omega
    apply (cappedTime_le_iff c _ hpos h).mpr
    have hunsat := (omittedCappedTime_le_iff c i _ hpos h).mp le_rfl
    rintro ⟨z, hz⟩
    exact hunsat ⟨z, fun j hj _ => hz j hj⟩
  · exact (min_le_right _ _).trans (le_of_not_gt h)

/-- If [every positively indexed random clause is measurable](hyp:hlaw),
[satisfiability of any fixed finite prefix is a measurable event](goal). -/
@[fun_prop]
-- @node: measurable_prefixSat
lemma measurable_prefixSat (Cseq : ℕ → Ω → ProperClause n)
    (hlaw : ∀ j, 1 ≤ j → Measurable (Cseq j)) (m : ℕ) :
    Measurable (fun ω => PrefixSat (fun j => Cseq j ω) m) := by
  classical
  have hc (z : Fin n → Bool) (j : Finset.Icc 1 m) :
      Measurable (fun ω => ClauseSat (Cseq j ω) z) :=
    (measurable_of_finite (fun c : ProperClause n => ClauseSat c z)).comp
      (hlaw j (Finset.mem_Icc.mp j.property).1)
  have h := Measurable.exists (fun z => Measurable.forall (hc z))
  convert h using 1
  ext ω
  simp [PrefixSat, Subtype.forall]

/-- If [every positively indexed random clause is measurable](hyp:hlaw),
[the hitting time is measurable, including the branch returning the cap when
no prefix is unsatisfiable](goal). -/
@[fun_prop]
-- @node: measurable_hittingTime
lemma measurable_hittingTime (Cseq : ℕ → Ω → ProperClause n)
    (hlaw : ∀ j, 1 ≤ j → Measurable (Cseq j)) :
    Measurable (fun ω => hittingTime (fun j => Cseq j ω)) := by
  classical
  let P : Ω → ℕ → Prop := fun ω m => 1 ≤ m ∧ ¬ PrefixSat (fun j => Cseq j ω) m
  have hP (m : ℕ) : Measurable (fun ω => P ω m) :=
    measurable_const.and (measurable_prefixSat Cseq hlaw m).not
  have heq (k : ℕ) : {ω | hittingTime (fun j => Cseq j ω) = k} =
      {ω | (P ω k ∧ ∀ j, j < k → ¬ P ω j) ∨
        (¬ (∃ j, P ω j)) ∧ capL n = k} := by
    ext ω
    change (if ∃ j, P ω j then sInf {j | P ω j} else capL n) = k ↔ _
    by_cases h : ∃ j, P ω j
    · simp only [if_pos h, Set.mem_setOf_eq, h, not_true_eq_false,
        false_and, or_false, ite_true]
      constructor
      · intro hk
        refine ⟨hk ▸ Nat.sInf_mem h, ?_⟩
        intro j hj hp
        have := Nat.sInf_le (s := {j | P ω j}) hp
        exact (not_le_of_gt hj) (hk ▸ this)
      · rintro ⟨hk, hmin⟩
        apply le_antisymm (Nat.sInf_le (s := {j | P ω j}) hk)
        by_contra hlt
        exact hmin (sInf {j | P ω j}) (Nat.lt_of_not_ge hlt)
          (Nat.sInf_mem (s := {j | P ω j}) h)
    · have hpk : ¬ P ω k := fun hk => h ⟨k, hk⟩
      simp only [if_neg h, Set.mem_setOf_eq, hpk, h, false_and,
        not_false_eq_true, true_and, false_or, ite_false]
  apply measurable_to_countable'
  intro k
  rw [show (fun ω => hittingTime (fun j => Cseq j ω)) ⁻¹' {k} =
    {ω | hittingTime (fun j => Cseq j ω) = k} from rfl, heq]
  exact ((hP k).and (Measurable.forall fun j =>
    measurable_const.imp (hP j).not)).or
      ((Measurable.exists hP).not.and measurable_const) |>.setOf

-- @node: ae_exists_unsat
/-- With [at least three variables](hyp:hn) and [independent, measurable random
clauses uniformly distributed over proper three-literal clauses](hyp:hlaw) under
a probability measure, [almost every outcome has an unsatisfiable prefix of positive length](goal). -/
lemma ae_exists_unsat (hn : MainN n) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Cseq : ℕ → Ω → ProperClause n) (hlaw : IsUniformClauseProcess μ Cseq) :
    ∀ᵐ ω ∂μ, ∃ m, 1 ≤ m ∧ ¬ PrefixSat (fun j => Cseq j ω) m := by
  classical
  letI : Nonempty (ProperClause n) := properClauseA_nonempty n 3 hn
  let c0 : ProperClause n := Classical.choice inferInstance
  have hocc (c : ProperClause n) : ∀ᵐ ω ∂μ, ∃ j : ℕ, Cseq (j + 1) ω = c := by
    classical
    let s : ℕ → Set Ω := fun j => {ω | Cseq (j + 1) ω = c}
    have hm (j : ℕ) : MeasurableSet (s j) := by
      exact (hlaw.1 _ (by omega)) (measurableSet_singleton c)
    have hi : iIndepSet s μ := by
      apply iIndep_comap_mem_iff.mp
      exact hlaw.2.1.comp (fun _ x => x = c) (fun _ => measurable_of_finite _)
    have hmass (j : ℕ) : μ (s j) = uniformClauseMeasure n 3 {c} := by
      rw [← hlaw.2.2 (j + 1) (by omega), Measure.map_apply (hlaw.1 _ (by omega))
        (measurableSet_singleton c)]
      rfl
    have hnz : uniformClauseMeasure n 3 {c} ≠ 0 := by
      haveI : Nonempty (ProperClause n) := ⟨c⟩
      simp [uniformClauseMeasure, uniformOn_univ, Measure.count_singleton,
        ENNReal.div_ne_zero]
    have hsum : (∑' j, μ (s j)) = ∞ := by
      simp_rw [hmass]
      exact ENNReal.tsum_const_eq_top_of_ne_zero hnz
    have hae := (mem_ae_iff_prob_eq_one (MeasurableSet.measurableSet_limsup hm)).mpr
      (measure_limsup_eq_one hm hi hsum)
    filter_upwards [hae] with ω hω
    exact (Filter.mem_limsup_iff_frequently_mem.mp hω).exists
  have hall : ∀ᵐ ω ∂μ, ∀ c : ProperClause n, ∃ j, Cseq (j + 1) ω = c :=
    ae_all_iff.mpr hocc
  filter_upwards [hall] with ω hω
  let t : ProperClause n → ℕ := fun c => Classical.choose (hω c)
  let M := Finset.univ.sup t + 1
  refine ⟨M, Nat.succ_pos _, ?_⟩
  rintro ⟨z, hz⟩
  let c : ProperClause n := properClauseOfSigns
    ⟨clauseVars c0, c0.property.2⟩ (fun v => !(z v.val))
  have hc : ClauseSat c z := by
    rw [← Classical.choose_spec (hω c)]
    exact hz (t c + 1) (Finset.mem_Icc.mpr
      ⟨Nat.succ_pos _, Nat.succ_le_succ (Finset.le_sup (Finset.mem_univ c))⟩)
  obtain ⟨l, hl, hs⟩ := hc
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hl
  have hbad : z v.val = !(z v.val) := hs
  cases h : z v.val <;> simp [h] at hbad

/-- Under [a probability measure](hyp:μ), for [a natural-valued random time](hyp:H)
and [a natural time m](hyp:m), [the survival probability](goal) is the probability
that the random time exceeds m. -/
def survivalFn (μ : Measure Ω) [IsProbabilityMeasure μ] (H : Ω → ℕ) (m : ℕ) : ℝ :=
  μ.real {ω | m < H ω}
  -- @realizes s_n(natural-time survival probability under a probability measure, valued in [0,1])

/-- Under [a probability measure](hyp:μ), for [a natural-valued random time](hyp:H)
and [an integer time m](hyp:m), [the integer-time survival function](goal) equals
[one when m is negative](step:1) and [the probability that the random time exceeds m otherwise](step:2). -/
def survivalFnInt (μ : Measure Ω) [IsProbabilityMeasure μ] (H : Ω → ℕ)
    (m : ℤ) : ℝ :=
  if m < 0 then 1 else μ.real {ω | m < (H ω : ℤ)}

/-- Under [a probability measure](hyp:μ), for [a natural-valued random time](hyp:H)
and [a real probability threshold p](hyp:p), [the level location](goal) is the
least natural time at which survival is at most p, or zero if there is no such time.

For the clause process and thresholds strictly between zero and one,
`levelLocation_minimum` proves that this minimum is attained and positive. -/
def levelLocation (μ : Measure Ω) [IsProbabilityMeasure μ] (H : Ω → ℕ) (p : ℝ) : ℕ :=
  sInf {m : ℕ | survivalFn μ H m ≤ p}
  -- @realizes r_n(first integer crossing of probability level p)
  -- @realizes p(deterministic level, restricted to the open unit interval by consumers)

/-- For [a probability measure](hyp:μ) and [a natural-valued random time](hyp:H),
[the survival-level pair](goal) consists of the natural-time survival function
and the function assigning each real threshold its first crossing time,
with zero returned when there is no crossing. -/
-- @node: def:window-levels
def survivalLevels (μ : Measure Ω) [IsProbabilityMeasure μ] (H : Ω → ℕ) :
    (ℕ → ℝ) × (ℝ → ℕ) :=
  (survivalFn μ H, levelLocation μ H)

-- @node: ass:wilson-levels
/-- For [an upper probability level](hyp:p1) and [a lower probability level](hyp:p2),
[the Wilson level condition](goal) requires that [the lower level is positive](step:1),
[the lower level is strictly below the upper level](step:2), and
[the upper level is strictly below one](step:3). -/
def WilsonLevels (p1 p2 : ℝ) : Prop :=
  0 < p2 ∧ -- @realizes p_2(positive fixed lower level)
  p2 < p1 ∧ -- @realizes p_2(strictly below the fixed upper level)
  p1 < 1 -- @realizes p_1(fixed upper level strictly below one)

-- @node: ass:wilson-endpoints
/-- For [an integer-time survival function](hyp:sn), [an upper probability level](hyp:p1),
[a lower probability level](hyp:p2), [a first integer endpoint](hyp:m1), and
[a second integer endpoint](hyp:m2), [the Wilson endpoint condition](goal) requires
[survival at the first endpoint to be at least the upper level](step:1) and
[survival at the second endpoint to be at most the lower level](step:2). -/
def WilsonEndpoints (sn : ℤ → ℝ) (p1 p2 : ℝ) (m1 m2 : ℤ) : Prop :=
  p1 ≤ sn m1 ∧ -- @realizes m_1(survival probability at least p_1)
  sn m2 ≤ p2 -- @realizes m_2(survival probability at most p_2)

-- @node: ass:window-eta
/-- For [a real window parameter](hyp:η), [the window-level condition](goal)
requires that [the parameter is positive](step:1) and [strictly below one half](step:2). -/
def WindowEta (η : ℝ) : Prop :=
  0 < η ∧ -- @realizes \eta(positive deterministic level)
  η < 1 / 2 -- @realizes \eta(strictly below one half)

/-- [The Wilson separation assertion](goal) says that for any two fixed probability
levels strictly between zero and one, with the lower strictly below the upper,
there is a positive constant such that, for all sufficiently large variable counts
of at least three and every uniform independent proper three-clause process,
any integer endpoints with survival at least the upper level and at most the
lower level are separated by at least that constant times the square root of the variable count.

David B. Wilson (2002), *On the critical exponents of random k-SAT*,
Corollary 4, arXiv:math/0005136v2; DOI 10.1002/rsa.10050.
https://arxiv.org/html/math/0005136#S2
The source's `(0.0015 + o(1)) (p1-p2) sqrt n` implies the stated positive
level-dependent separation for the with-replacement proper 3-clause ensemble. -/
-- @node: thm:wilson
def WilsonSeparation : Sort 0 :=
  ∀ p1 p2 : ℝ, WilsonLevels p1 p2 →
    ∃ a : ℝ, 0 < a ∧ -- @realizes a(p_1,p_2)(positive constant depending only on fixed levels)
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → MainN n →
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (Cseq : ℕ → Ω → ProperClause n), IsUniformClauseProcess μ Cseq →
        ∀ m1 m2 : ℤ,
          WilsonEndpoints (survivalFnInt μ (fun ω => hittingTime (fun j => Cseq j ω)))
            p1 p2 m1 m2 → a * Real.sqrt n ≤ (m2 : ℝ) - (m1 : ℝ)

/-- For [a random clause sequence](hyp:Cseq) on [n variables](hyp:n) and
[a revelation index i](hyp:i), [the clause information at i](goal) is the sigma
field generated by the clauses at indices one through i. -/
def clauseSigma (Cseq : ℕ → Ω → ProperClause n) (i : ℕ) : MeasurableSpace Ω :=
  ⨆ j ∈ Finset.Icc 1 i, MeasurableSpace.comap (Cseq j) ⊤
  -- @realizes \mathcal F_i(sigma-field generated by clauses one through i)

/-- For [a measure](hyp:μ), [a random clause sequence](hyp:Cseq) on
[n Boolean variables](hyp:n), [a revelation index i](hyp:i), and
[a real-valued random variable](hyp:X), [the conditional-expectation increment](goal)
is its conditional expectation given clauses one through i minus its conditional
expectation given the clauses through the preceding index, with no clauses
revealed at index zero. -/
def delta (μ : Measure Ω) (Cseq : ℕ → Ω → ProperClause n) (i : ℕ)
    (X : Ω → ℝ) : Ω → ℝ :=
  fun ω => (μ[X | clauseSigma Cseq i]) ω - (μ[X | clauseSigma Cseq (i - 1)]) ω
  -- @realizes X(input random variable; integrability scoped in analytic uses)
  -- @realizes \Delta_i(difference of the two conditional expectations)

/-- For [a measure](hyp:μ) and [a random clause sequence](hyp:Cseq) on
[n Boolean variables](hyp:n), [the mean hitting time](goal) is the integral of
the first positive unsatisfiable-prefix length, using the prescribed cap when
no prefix is unsatisfiable. -/
def meanHittingTime (μ : Measure Ω) (Cseq : ℕ → Ω → ProperClause n) : ℝ :=
  ∫ ω, (hittingTime (fun j => Cseq j ω) : ℝ) ∂μ -- @realizes \mu_n(mean hitting time)

/-- Under [a probability measure](hyp:μ), for [a random clause sequence](hyp:Cseq)
on [n Boolean variables](hyp:n), [the lower quartile of the hitting time](goal)
is the least natural time at which its survival probability is at most three
quarters, with zero returned if there is no such time. -/
def lowerQuartile (μ : Measure Ω) [IsProbabilityMeasure μ] (Cseq : ℕ → Ω → ProperClause n) : ℕ :=
  levelLocation μ (fun ω => hittingTime (fun j => Cseq j ω)) (3 / 4)
  -- @realizes a_n(level location at three quarters)

/-- Under [a probability measure](hyp:μ), for [a random clause sequence](hyp:Cseq)
on [n Boolean variables](hyp:n), [the upper quartile of the hitting time](goal)
is the least natural time at which its survival probability is at most one
quarter, with zero returned if there is no such time. -/
def upperQuartile (μ : Measure Ω) [IsProbabilityMeasure μ] (Cseq : ℕ → Ω → ProperClause n) : ℕ :=
  levelLocation μ (fun ω => hittingTime (fun j => Cseq j ω)) (1 / 4)
  -- @realizes b_n(level location at one quarter)

/-- For [a random clause sequence](hyp:Cseq) on [n Boolean variables](hyp:n)
and [a pair of outcomes](hyp:ω), [the copied hitting time](goal) is the hitting
time evaluated at the second outcome. -/
def hittingTimeCopy (Cseq : ℕ → Ω → ProperClause n) (ω : Ω × Ω) : ℕ :=
  hittingTime (fun j => Cseq j ω.2)
  -- @realizes H_n'(second-coordinate hitting time under the product measure)

/-- With [at least three variables](hyp:hn) and [independent, measurable clauses
uniformly distributed over proper three-literal clauses](hyp:hlaw) under a
probability measure, [the hitting time is at least one almost surely](goal),
including when it takes the fallback cap. -/
-- @node: ae_hittingTime_pos
lemma ae_hittingTime_pos (hn : MainN n) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Cseq : ℕ → Ω → ProperClause n) (hlaw : IsUniformClauseProcess μ Cseq) :
    ∀ᵐ ω ∂μ, 1 ≤ hittingTime (fun j => Cseq j ω) := by
  classical
  filter_upwards [] with ω
  unfold hittingTime
  split_ifs with h
  · exact (Nat.sInf_mem h).1
  · unfold capL
    unfold MainN at hn
    omega
    -- @realizes H_n(positive integer almost everywhere in every admissible world)

-- @node: levelLocation_pos_and_spec
/-- With [at least three variables](hyp:hn), [independent, measurable clauses
uniformly distributed over proper three-literal clauses](hyp:hlaw) under a
probability measure, and [a probability level strictly between zero and one](hyp:hp),
[the first time the hitting-time survival probability is at most that level is
positive, survival there is at most the level, and survival at every earlier
natural time is strictly above the level](goal). -/
lemma levelLocation_pos_and_spec (hn : MainN n) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Cseq : ℕ → Ω → ProperClause n)
    (hlaw : IsUniformClauseProcess μ Cseq) (p : ℝ)
    (hp : 0 < p ∧ p < 1) : -- @realizes p(probability level in the open unit interval)
    let H := fun ω => hittingTime (fun j => Cseq j ω)
    0 < levelLocation μ H p ∧ survivalFn μ H (levelLocation μ H p) ≤ p ∧
      ∀ m : ℕ, m < levelLocation μ H p → p < survivalFn μ H m := by
  classical
  let H := fun ω => hittingTime (fun j => Cseq j ω)
  have hH : Measurable H := measurable_hittingTime Cseq hlaw.1
  have htail : Filter.Tendsto (fun k : ℕ => μ {ω | k < H ω})
      Filter.atTop (nhds 0) := by
    have hempty : (⋂ k : ℕ, {ω | k < H ω}) = ∅ := by
      ext ω
      simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      exact (lt_irrefl (H ω)) (h (H ω))
    have hm (k : ℕ) : MeasurableSet {ω | k < H ω} := by
      exact measurableSet_lt measurable_const hH
    have hant : Antitone (fun k : ℕ => {ω | k < H ω}) := by
      intro a b hab ω hω
      exact hab.trans_lt hω
    simpa only [hempty, measure_empty, Function.comp_def] using
      tendsto_measure_iInter_atTop (fun k => (hm k).nullMeasurableSet) hant
        ⟨0, measure_ne_top μ _⟩
  have hsurv : Filter.Tendsto (fun k : ℕ => survivalFn μ H k)
      Filter.atTop (nhds 0) := by
    simpa only [survivalFn, measureReal_def, ENNReal.toReal_zero, Function.comp_def] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp htail
  have hex : ∃ k : ℕ, survivalFn μ H k ≤ p := by
    obtain ⟨k, hk⟩ := (hsurv.eventually (gt_mem_nhds hp.1)).exists
    exact ⟨k, hk.le⟩
  have hspec : survivalFn μ H (levelLocation μ H p) ≤ p := Nat.sInf_mem hex
  have hzero : survivalFn μ H 0 = 1 := by
    have hevent : {ω | 0 < H ω} =ᵐ[μ] Set.univ := by
      filter_upwards [ae_hittingTime_pos hn μ Cseq hlaw] with ω hω
      change (0 < H ω) = True
      apply eq_true
      exact_mod_cast (Nat.zero_lt_of_lt hω)
    simp only [survivalFn]
    rw [measureReal_congr hevent]
    simp
  refine ⟨?_, hspec, ?_⟩
  · by_contra hpos
    change ¬ 0 < levelLocation μ H p at hpos
    have hz : levelLocation μ H p = 0 := Nat.eq_zero_of_not_pos hpos
    have hbad : 1 ≤ p := by simpa only [hz, hzero] using hspec
    exact (not_le_of_gt hp.2) hbad
  · intro m hm
    apply lt_of_not_ge
    intro hle
    exact (not_le_of_gt hm) (Nat.sInf_le (s := {k | survivalFn μ H k ≤ p}) hle)
    -- @realizes r_n(finite positive first crossing, with the preceding values above p)

-- keep: Public minimum characterization of the level-location component of survivalLevels; certifies the paper-defined r_n(p) is an attained first crossing for 0 < p < 1.
/-- With [at least three variables](hyp:hn), [independent, measurable clauses
uniformly distributed over proper three-literal clauses](hyp:hlaw) under a
probability measure, and [a probability level strictly between zero and one](hyp:hp),
[the level location is positive and is the least natural time at which the
hitting-time survival probability is at most that level](goal). -/
lemma levelLocation_minimum (hn : MainN n) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Cseq : ℕ → Ω → ProperClause n)
    (hlaw : IsUniformClauseProcess μ Cseq) (p : ℝ) (hp : 0 < p ∧ p < 1) :
    let H := fun ω => hittingTime (fun j => Cseq j ω)
    0 < levelLocation μ H p ∧
      IsLeast {m : ℕ | survivalFn μ H m ≤ p} (levelLocation μ H p) := by
  let H := fun ω => hittingTime (fun j => Cseq j ω)
  have h := levelLocation_pos_and_spec hn μ Cseq hlaw p hp
  refine ⟨h.1, h.2.1, ?_⟩
  intro m hm
  exact Nat.sInf_le (s := {k : ℕ | survivalFn μ H k ≤ p}) hm

-- @node: hittingTimeCopy_indep_and_law
/-- With [at least three variables](hyp:hn) and [independent, measurable clauses
uniformly distributed over proper three-literal clauses](hyp:hlaw) under a
probability measure, [the hitting times evaluated at the two coordinates of
the product probability space are independent, and the second has the same
distribution as the original hitting time](goal). -/
lemma hittingTimeCopy_indep_and_law (hn : MainN n) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Cseq : ℕ → Ω → ProperClause n)
    (hlaw : IsUniformClauseProcess μ Cseq) :
    IndepFun (fun ω : Ω × Ω => hittingTime (fun j => Cseq j ω.1))
      (hittingTimeCopy Cseq) (μ.prod μ) ∧ -- @realizes H_n'(independent copy)
    (μ.prod μ).map (hittingTimeCopy Cseq) =
      μ.map (fun ω => hittingTime (fun j => Cseq j ω)) := by
  have hm := measurable_hittingTime Cseq hlaw.1
  refine ⟨indepFun_prod hm hm, ?_⟩
  change (μ.prod μ).map ((fun ω => hittingTime (fun j => Cseq j ω)) ∘ Prod.snd) = _
  rw [← Measure.map_map hm measurable_snd, Measure.map_snd_prod,
    measure_univ, one_smul]
    -- @realizes H_n'(same unconditional distribution as H_n)

end Papers.OaiLinearVarianceRandom

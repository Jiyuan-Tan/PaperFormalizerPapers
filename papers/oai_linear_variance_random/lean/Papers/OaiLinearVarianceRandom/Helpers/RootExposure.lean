module

public import Papers.OaiLinearVarianceRandom.Helpers.AssignmentSets
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Probability.Process.Filtration
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# Root exposure and the pivotality processes

The exposure records root literals at every capped index, and the entire clause
only at the exposed indices. Masked content maps reveal precisely ordinary or
test contents. Hidden-clause laws are consequences of the independent process.
-/

@[expose] public section

noncomputable section
namespace Papers.OaiLinearVarianceRandom
open MeasureTheory ProbabilityTheory
open scoped BigOperators
set_option linter.unusedVariables false
set_option warn.classDefReducibility false

-- @env: S3
variable {n : ℕ} {Ω : Type} [MeasurableSpace Ω]

open Classical in
-- @node: ass:tests-time
/-- For [an omitted index](hyp:i), [a prefix time](hyp:m), and [a cap](hyp:L),
[the test-time condition](goal) requires [the prefix time to be at least the omitted
index](step:1) and [strictly below the cap](step:2). -/
def TestsTime (i m L : ℕ) : Prop := i ≤ m ∧ m < L
  -- @realizes m(prefix time between the omitted index and cap)

open Classical in
-- @node: ass:occupation-time
/-- For [an omitted index](hyp:i), [a prefix time](hyp:m), and [a cap](hyp:L),
[the occupation-time condition](goal) requires [the prefix time to be at least the
omitted index](step:1) and [strictly below the cap](step:2). -/
def OccupationTime (i m L : ℕ) : Prop := i ≤ m ∧ m < L

open Classical in
-- @node: ass:duration-time
/-- For [an omitted index](hyp:i), [a prefix time](hyp:m), and [a cap](hyp:L),
[the duration-time condition](goal) requires [the prefix time to be at least the
omitted index](step:1) and [strictly below the cap](step:2). -/
def DurationTime (i m L : ℕ) : Prop := i ≤ m ∧ m < L

open Classical in
-- @node: ass:delay-index
/-- For [an omitted clause index](hyp:i) and [a cap](hyp:L), [the delay-index
condition](goal) requires [the index to be positive](step:1) and [no greater than
the cap](step:2). -/
def DelayIndex (i L : ℕ) : Prop :=
  1 ≤ i ∧ -- @realizes i(positive omitted clause index)
  i ≤ L -- @realizes i(at most the cap)

open Classical in
-- @node: ass:moments-range
/-- For [a variable count](hyp:n) and [an omitted index](hyp:i), [the moments
range condition](goal) requires [at least six variables](step:1), [a positive
omitted index](step:2), and [an omitted index no greater than ten times the variable
count](step:3). -/
def MomentsRange (n i : ℕ) : Prop :=
  6 ≤ n ∧ -- @realizes n(variable count in the omission regime)
  1 ≤ i ∧ -- @realizes i(positive omitted index)
  i ≤ capL n -- @realizes i(omitted index within the cap)

open Classical in
-- @node: def:tests-omitted-alias
/-- For [a clause sequence](hyp:c) on [n variables](hyp:n), [an omitted index](hyp:i), and [a prefix
length](hyp:m), [omitted-prefix satisfiability](goal) means that one assignment
satisfies every clause from index one through the prefix length except the omitted
clause. -/
def omittedPrefixSatAt (c : ℕ → ProperClause n) (i m : ℕ) : Prop :=
  omittedPrefixSat c i m -- @realizes B_m(fixed-index omitted-prefix shorthand)

open Classical in
-- @node: def:tests-roots
/-- Among [n variables](hyp:n), the [roots](goal) of [a fixed clause](hyp:c0) are the variables appearing in
that clause. -/
def roots (c0 : ProperClause n) : Finset (Fin n) :=
  clauseVars c0 -- @realizes R(three variables of the fixed omitted clause)

open Classical in
/-- Among [n variables](hyp:n), for [a fixed clause](hyp:c0) and [one of its root variables](hyp:v),
[the falsifying value](goal) is false if the positive literal occurs in the clause,
and true otherwise. -/
def rootFalsifier (c0 : ProperClause n) (v : roots c0) : Bool :=
  !(decide ((v.val, true) ∈ c0.val))
  -- @realizes w(unique root assignment falsifying the fixed clause)

open Classical in
-- @node: roots_card
/-- [A fixed proper clause](hyp:c0) [has exactly three root variables](goal). -/
lemma roots_card (c0 : ProperClause n) : (roots c0).card = 3 := by
  exact c0.property.2

open Classical in
-- @node: rootFalsifier_unique
/-- For [a fixed proper clause](hyp:c0) and [a Boolean assignment](hyp:z),
[the clause is unsatisfied exactly when the assignment takes the falsifying value
at every root variable](goal). -/
lemma rootFalsifier_unique (c0 : ProperClause n) (z : Fin n → Bool) :
    ¬ ClauseSat c0 z ↔ ∀ v : roots c0, z v = rootFalsifier c0 v := by
  have hinj : Set.InjOn Prod.fst (↑c0.val : Set (Fin n × Bool)) :=
    Finset.card_image_iff.mp (c0.property.2.trans c0.property.1.symm)
  constructor
  · intro hn v
    by_cases ht : (v.val, true) ∈ c0.val
    · have hz : z v ≠ true := fun hz => hn ⟨(v.val, true), ht, hz⟩
      cases hv : z v <;> simp_all [rootFalsifier]
    · have hf : (v.val, false) ∈ c0.val := by
        obtain ⟨⟨w, b⟩, hw, heq⟩ := Finset.mem_image.mp v.property
        change w = v.val at heq
        cases b with
        | false => simpa only [heq] using hw
        | true => exact False.elim (ht (by simpa only [heq] using hw))
      have hz : z v ≠ false := fun hz => hn ⟨(v.val, false), hf, hz⟩
      cases hv : z v <;> simp_all [rootFalsifier]
  · intro hz
    rintro ⟨⟨v, b⟩, hl, hs⟩
    have hv : v ∈ roots c0 := Finset.mem_image_of_mem Prod.fst hl
    have heq := hz ⟨v, hv⟩
    cases b with
    | false =>
        have ht : (v, true) ∉ c0.val := by
          intro ht
          have := hinj hl ht rfl
          cases this
        simp [rootFalsifier, ht] at heq
        exact Bool.noConfusion (heq.symm.trans hs)
    | true =>
        simp [rootFalsifier, hl] at heq
        exact Bool.noConfusion (heq.symm.trans hs)

open Classical in
-- @node: def:tests-nonroots
/-- For [a total variable count](hyp:n), [the nonroot count](goal) is that count
minus three, with subtraction truncated at zero. -/
def nonrootCount (n : ℕ) : ℕ := n - 3 -- @realizes u(nonroot count n minus three)

open Classical in
-- @node: card_nonroots
/-- For [a fixed proper clause](hyp:c0), [the number of variables outside its
roots equals the total variable count minus three](goal). -/
lemma card_nonroots (c0 : ProperClause n) :
    Fintype.card {v : Fin n // v ∉ roots c0} = nonrootCount n := by
  rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe, roots_card]
  rfl

open Classical in
/-- Among [n variables](hyp:n), for [a fixed proper clause](hyp:c0), [the nonroot enumeration](goal) is a
bijection from variables outside its roots to consecutive indices starting at zero
and ending just below the nonroot count. -/
def nonrootEquiv (c0 : ProperClause n) :
    {v : Fin n // v ∉ roots c0} ≃ Fin (nonrootCount n) :=
  Fintype.equivFinOfCardEq (card_nonroots c0)

open Classical in
/-- Among [n variables](hyp:n), for [a fixed clause](hyp:c0), [a Boolean assignment indexed by the
nonroots](hyp:y), and [a variable](hyp:v), [the glued assignment's value](goal)
is the clause's falsifying value on roots and the indexed nonroot value elsewhere. -/
def glueAssignment (c0 : ProperClause n) (y : Fin (nonrootCount n) → Bool)
    (v : Fin n) : Bool :=
  if h : v ∈ roots c0 then rootFalsifier c0 ⟨v, h⟩
  else y (nonrootEquiv c0 ⟨v, h⟩)

open Classical in
/-- Among [n variables](hyp:n), for [a fixed clause](hyp:c0), [a root to flip](hyp:x), [a nonroot
assignment](hyp:y), and [a variable at which to evaluate](hyp:v), [the flipped
assignment's value](goal) is the glued assignment's value with the chosen root's
Boolean value reversed. -/
def flipRootAssignment (c0 : ProperClause n)
    (x : roots c0) -- @realizes x(root variable considered for the single-root flip)
    (y : Fin (nonrootCount n) → Bool) (v : Fin n) : Bool :=
  if v = x.val then !(glueAssignment c0 y v) else glueAssignment c0 y v

open Classical in
-- @node: def:a
/-- For [a random clause sequence](hyp:Cseq) on [n variables](hyp:n) with
[outcome space Ω](hyp:Ω), [an omitted index](hyp:i), and
[a prefix length](hyp:m), [the pivotal event](goal) consists of outcomes where
[the prefix with that clause omitted is satisfiable](step:1), but [no assignment
satisfies both that omitted prefix and the omitted clause](step:2). -/
def pivotalEvent (Cseq : ℕ → Ω → ProperClause n) (i m : ℕ) : Set Ω :=
  {ω | omittedPrefixSat (fun j => Cseq j ω) i m ∧
    ¬ ∃ z : Fin n → Bool,
      (∀ j ∈ Finset.Icc 1 m, j ≠ i → ClauseSat (Cseq j ω) z) ∧ ClauseSat (Cseq i ω) z}
  -- @realizes A_m(B_m satisfiable but its conjunction with the omitted clause unsatisfiable)

open Classical in
-- @node: pivotalEvent_eq_time_interval
/-- With [at least six variables](hyp:hn), for [a random clause sequence](hyp:Cseq),
[an omitted index](hyp:i), and [a prefix time](hyp:m), if [the omitted index is
positive and within the cap](hyp:hi) and [the prefix time is at least that index
and strictly below the cap](hyp:hm), then [the pivotal event is exactly the event
that the full sequence's capped unsatisfiability time is at most the prefix time
and the omitted sequence's capped unsatisfiability time is greater](goal). -/
lemma pivotalEvent_eq_time_interval (hn : OmissionN n)
    (Cseq : ℕ → Ω → ProperClause n) (i m : ℕ)
    (hi : DelayIndex i (capL n)) (hm : TestsTime i m (capL n)) :
    pivotalEvent Cseq i m =
      {ω | cappedTime (fun j => Cseq j ω) ≤ m ∧
        m < omittedCappedTime (fun j => Cseq j ω) i} := by
  ext ω
  have hmpos : 1 ≤ m := hi.1.trans hm.1
  rw [Set.mem_setOf_eq, ← not_le, omittedCappedTime_le_iff _ i m hmpos hm.2,
    not_not, cappedTime_le_iff _ m hmpos hm.2]
  have heq : (∃ z : Fin n → Bool,
      (∀ j ∈ Finset.Icc 1 m, j ≠ i → ClauseSat (Cseq j ω) z) ∧
      ClauseSat (Cseq i ω) z) ↔ PrefixSat (fun j => Cseq j ω) m := by
    constructor
    · rintro ⟨z, hz, hzi⟩
      refine ⟨z, fun j hj => ?_⟩
      by_cases hji : j = i
      · simpa only [hji] using hzi
      · exact hz j hj hji
    · rintro ⟨z, hz⟩
      exact ⟨z, (fun j hj _ => hz j hj), hz i (Finset.mem_Icc.mpr ⟨hi.1, hm.1⟩)⟩
  change (_ ∧ ¬ _) ↔ _ ∧ _
  rw [heq, and_comm]

open Classical in
-- @node: def:delay
/-- For [a random clause sequence](hyp:Cseq) on [n variables](hyp:n) with
[outcome space Ω](hyp:Ω), [an omitted index](hyp:i), and
[an outcome](hyp:ω), [the delay indicator sum](goal) counts the pivotal prefix
times from the omitted index up to, but excluding, the cap. -/
def delayIndicatorSum (Cseq : ℕ → Ω → ProperClause n) (i : ℕ) (ω : Ω) : ℕ :=
  ((Finset.Ico i (capL n)).filter (fun m => ω ∈ pivotalEvent Cseq i m)).card
  -- @realizes D_i(sum of pivotality indicators from i through L minus one)

open Classical in
-- @node: delay_eq_delayIndicatorSum
/-- With [at least six variables](hyp:hn), for [a random clause sequence](hyp:Cseq),
[an omitted index](hyp:i), and [an outcome](hyp:ω), if [the omitted index is positive
and within the cap](hyp:hi), then [the delay caused by omitting that clause equals
the number of pivotal prefix times from that index up to, but excluding, the cap](goal). -/
lemma delay_eq_delayIndicatorSum (hn : OmissionN n)
    (Cseq : ℕ → Ω → ProperClause n) (i : ℕ) (hi : DelayIndex i (capL n)) (ω : Ω) :
    delay (fun j => Cseq j ω) i = delayIndicatorSum Cseq i ω := by
  let c := fun j => Cseq j ω
  have hL : omittedCappedTime c i ≤ capL n := MeasureTheory.hittingBtwn_le ()
  have hT : 1 ≤ cappedTime c := by
    rw [cappedTime_eq_hittingBtwn]
    apply MeasureTheory.le_hittingBtwn (ω := ())
    unfold capL
    unfold OmissionN at hn
    omega
  have hset : (Finset.Ico i (capL n)).filter (fun m => ω ∈ pivotalEvent Cseq i m) =
      Finset.Ico (cappedTime c) (omittedCappedTime c i) := by
    ext m
    constructor
    · intro hm
      obtain ⟨hm, hp⟩ := Finset.mem_filter.mp hm
      have hm' := Finset.mem_Ico.mp hm
      rw [pivotalEvent_eq_time_interval hn Cseq i m hi hm'] at hp
      exact Finset.mem_Ico.mpr hp
    · intro hm
      have hm' := Finset.mem_Ico.mp hm
      have hmpos := hT.trans hm'.1
      have hmL : m < capL n := hm'.2.trans_le hL
      have hsat : omittedPrefixSat c i m := by
        by_contra hs
        exact (not_le.mpr hm'.2) ((omittedCappedTime_le_iff c i m hmpos hmL).mpr hs)
      have hunsat := (cappedTime_le_iff c m hmpos hmL).mp hm'.1
      have him : i ≤ m := by
        by_contra h
        obtain ⟨z, hz⟩ := hsat
        apply hunsat
        refine ⟨z, fun j hj => hz j hj ?_⟩
        have hjm := (Finset.mem_Icc.mp hj).2
        omega
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Ico.mpr ⟨him, hmL⟩, ?_⟩
      rw [pivotalEvent_eq_time_interval hn Cseq i m hi ⟨him, hmL⟩]
      exact hm'
  unfold delayIndicatorSum
  rw [hset, Nat.card_Ico]
  rfl

open Classical in
-- @node: def:tests-solution-set
/-- Among [n variables](hyp:n) with [outcome space Ω](hyp:Ω), for
[a fixed clause determining the roots](hyp:c0), [a random clause
sequence](hyp:Cseq), [an omitted index](hyp:i), [a prefix length](hyp:m), and
[an outcome](hyp:ω), [the nonroot solution set](goal) consists of nonroot Boolean
assignments that satisfy all clauses in the prefix except the omitted one when
combined with the fixed clause's falsifying root values. -/
def nonrootSolutions (c0 : ProperClause n) (Cseq : ℕ → Ω → ProperClause n)
    (i m : ℕ) (ω : Ω) : Finset (Fin (nonrootCount n) → Bool) :=
  Finset.univ.filter (fun y =>
    ∀ j ∈ Finset.Icc 1 m, j ≠ i → ClauseSat (Cseq j ω) (glueAssignment c0 y))
  -- @realizes S_m(nonroot assignments satisfying B_m with the fixed falsifying roots)

open Classical in
/-- Among [n variables](hyp:n), for [a fixed clause determining the roots](hyp:c0) and [a clause to
inspect](hyp:c), [the root literals](goal) are the literals of the inspected clause
whose variables belong to those roots. -/
def rootLiterals (c0 c : ProperClause n) : Finset (Fin n × Bool) :=
  c.val.filter (fun l => l.1 ∈ roots c0)

open Classical in
/-- Among [n variables](hyp:n), relative to [a fixed clause determining the roots](hyp:c0), [a clause](hyp:c)
[is ordinary](goal) when it contains no root literals. -/
def isOrdinary (c0 c : ProperClause n) : Prop := rootLiterals c0 c = ∅

open Classical in
/-- Among [n variables](hyp:n), relative to [a fixed clause determining the roots and their signs](hyp:c0),
[a clause](hyp:c) [is a test](goal) when [it contains exactly one root literal](step:1)
and [contains a root literal whose sign is opposite to its sign in the fixed
clause](step:2). -/
def isTest (c0 c : ProperClause n) : Prop :=
  (rootLiterals c0 c).card = 1 ∧
    ∃ l ∈ rootLiterals c0 c, l.2 ≠ decide ((l.1, true) ∈ c0.val)

open Classical in
/-- Among [n variables](hyp:n), for [a fixed clause determining the roots](hyp:c0) and [a clause to
reveal](hyp:c), [the exposure record](goal) contains its root literals and, if it
is neither ordinary nor a test, its full contents; otherwise the full contents
are withheld. -/
def expose (c0 c : ProperClause n) :
    Finset (Fin n × Bool) × Option (ProperClause n) :=
  (rootLiterals c0 c, if isOrdinary c0 c ∨ isTest c0 c then none else some c)

open Classical in
-- @node: def:tests-exposure
/-- Among [n variables](hyp:n) with [outcome space Ω](hyp:Ω), for
[a fixed clause determining the roots](hyp:c0), [a random clause
sequence](hyp:Cseq), and [an omitted index](hyp:i), [the exposure information](goal)
is the sigma-algebra generated by the root exposure records at all indices from
one through the cap except the omitted index, including future indices. -/
def exposureSigma (c0 : ProperClause n) (Cseq : ℕ → Ω → ProperClause n)
    (i : ℕ) : MeasurableSpace Ω :=
  ⨆ j ∈ (Finset.Icc 1 (capL n)).erase i,
    MeasurableSpace.comap (fun ω => expose c0 (Cseq j ω)) ⊤
 
  -- @realizes \cE(capped root exposure, including future indices)

open Classical in
/-- Among [n variables](hyp:n) with [outcome space Ω](hyp:Ω), for
[a fixed clause determining the roots](hyp:c0), [a random clause
sequence](hyp:Cseq), [an omitted index](hyp:i), and [an outcome](hyp:ω), [the
incidence count](goal) counts indices from one through the cap, excluding the
omitted index, whose clauses contain at least one root literal. -/
def incidenceCount (c0 : ProperClause n) (Cseq : ℕ → Ω → ProperClause n)
    (i : ℕ) (ω : Ω) : ℕ :=
  (((Finset.Icc 1 (capL n)).erase i).filter
    (fun j => 1 ≤ (rootLiterals c0 (Cseq j ω)).card)).card
  -- @realizes Z(count of indices other than i meeting at least one root, across the whole cap)

open Classical in
/-- Among [n variables](hyp:n) with [outcome space Ω](hyp:Ω), for
[a fixed clause determining the roots](hyp:c0), [a random clause
sequence](hyp:Cseq), [an omitted index](hyp:i), and [an outcome](hyp:ω), [the
collision count](goal) counts indices from one through the cap, excluding the
omitted index, whose clauses contain at least two root literals. -/
def collisionCount (c0 : ProperClause n) (Cseq : ℕ → Ω → ProperClause n)
    (i : ℕ) (ω : Ω) : ℕ :=
  (((Finset.Icc 1 (capL n)).erase i).filter
    (fun j => 2 ≤ (rootLiterals c0 (Cseq j ω)).card)).card
  -- @realizes V(count of indices meeting at least two roots, across the whole cap)

/-- Among [n variables](hyp:n) with [outcome space Ω](hyp:Ω), for
[a fixed clause determining the roots](hyp:c0), [a random clause
sequence](hyp:Cseq), [an omitted index](hyp:i), and [an outcome](hyp:ω), [the
exposure counts](goal) are the incidence count followed by the collision count
over all indices from one through the cap except the omitted index. -/
-- @node: def:tests-counts
def exposureCounts (c0 : ProperClause n) (Cseq : ℕ → Ω → ProperClause n)
    (i : ℕ) (ω : Ω) : ℕ × ℕ :=
  (incidenceCount c0 Cseq i ω, collisionCount c0 Cseq i ω)

open Classical in
-- @node: def:tests-d
/-- Among [n variables](hyp:n) with [outcome space Ω](hyp:Ω), for
[a fixed clause determining the roots](hyp:c0), [a random clause
sequence](hyp:Cseq), [an omitted index](hyp:i), and [an outcome](hyp:ω), [the
incidence parameter](goal) is the larger of one and the incidence count. -/
def incidenceParam (c0 : ProperClause n) (Cseq : ℕ → Ω → ProperClause n)
    (i : ℕ) (ω : Ω) : ℕ :=
  max 1 (incidenceCount c0 Cseq i ω) -- @realizes d(maximum of one and Z)

open Classical in
/-- Among [n variables](hyp:n), for [a fixed clause determining the roots](hyp:c0) and [a clause to
inspect](hyp:c), [the masked ordinary contents](goal) reveal the full clause if
it has no root literals, and reveal nothing otherwise. -/
def ordinaryContents (c0 c : ProperClause n) : Option (ProperClause n) :=
  if isOrdinary c0 c then some c else none

open Classical in
/-- Among [n variables](hyp:n), for [a fixed clause determining the roots](hyp:c0) and [a clause to
inspect](hyp:c), [the masked test contents](goal) reveal only the nonroot literals
when the clause is a test, and reveal nothing otherwise. -/
def testContents (c0 c : ProperClause n) : Option (Finset (Fin n × Bool)) :=
  if isTest c0 c then some (c.val.filter (fun l => l.1 ∉ roots c0)) else none

open Classical in
-- @node: def:tests-filtrations
/-- Among [n variables](hyp:n) with [outcome space Ω](hyp:Ω), for
[a fixed clause determining the roots](hyp:c0), [a random clause
sequence](hyp:Cseq), [an omitted index](hyp:i), and [a prefix time](hyp:m), [the
ordinary information at that time](goal) combines the capped exposure information
with the masked ordinary clause contents at indices from one through that time,
excluding the omitted index. -/
def ordinaryFiltration (c0 : ProperClause n) (Cseq : ℕ → Ω → ProperClause n)
    (i m : ℕ) : MeasurableSpace Ω :=
  exposureSigma c0 Cseq i ⊔
    ⨆ j ∈ (Finset.Icc 1 m).erase i,
      MeasurableSpace.comap (fun ω => ordinaryContents c0 (Cseq j ω)) ⊤
  -- @realizes \cG_m(exposure joined with ordinary contents through m)

open Classical in
/-- Among [n variables](hyp:n) with [outcome space Ω](hyp:Ω), for
[a fixed clause determining the roots](hyp:c0), [a random clause
sequence](hyp:Cseq), [an omitted index](hyp:i), and [a prefix time](hyp:m), [the
test information at that time](goal) combines the ordinary information with the
masked test contents at indices from one through that time, excluding the omitted
index. -/
def testFiltration (c0 : ProperClause n) (Cseq : ℕ → Ω → ProperClause n)
    (i m : ℕ) : MeasurableSpace Ω :=
  ordinaryFiltration c0 Cseq i m ⊔
    ⨆ j ∈ (Finset.Icc 1 m).erase i,
      MeasurableSpace.comap (fun ω => testContents c0 (Cseq j ω)) ⊤
  -- @realizes \cH_m(ordinary filtration joined with test parts through m)

open Classical in
-- @node: def:p
/-- Among [n variables](hyp:n) with [outcome space Ω](hyp:Ω), for
[a fixed clause determining the roots](hyp:c0), [a random clause
sequence](hyp:Cseq), [an omitted index](hyp:i), [a prefix time](hyp:m), and
[an outcome](hyp:ω), [the killing process](goal) is the killing probability of
the nonroot solution set at that time, using the incidence parameter. -/
def killProcess (c0 : ProperClause n) (Cseq : ℕ → Ω → ProperClause n)
    (i m : ℕ) (ω : Ω) : ℝ :=
  killProb (incidenceParam c0 Cseq i ω) (nonrootSolutions c0 Cseq i m ω)
  -- @realizes p_m(killing probability q_d of the nonroot solution set)

open Classical in
-- @node: def:occupation-k
/-- [The absolute occupation constant](goal) is the real number seven. -/
def occupationK : ℝ := 7 -- @realizes K(absolute occupation constant seven)

open Classical in
/-- For [a measure on outcomes](hyp:μ) in [a measurable outcome space Ω](hyp:Ω),
[a random clause sequence](hyp:Cseq) on [n variables](hyp:n),
[an omitted index](hyp:i), and [a fixed clause value](hyp:c0), [the fixed-clause
measure](goal) is the original measure conditioned on the clause at the omitted
index equaling that value. -/
def fixedClauseMeasure (μ : Measure Ω) (Cseq : ℕ → Ω → ProperClause n)
    (i : ℕ) (c0 : ProperClause n) : Measure Ω :=
  ProbabilityTheory.cond μ {ω | Cseq i ω = c0}

open Classical in
/-- In [an outcome space Ω](hyp:Ω), for [an event](hyp:A) and [an outcome](hyp:ω), [the real-valued event
indicator](goal) is one when the outcome belongs to the event and zero otherwise. -/
def eventIndicator (A : Set Ω) (ω : Ω) : ℝ := if ω ∈ A then 1 else 0

open Classical in
/-- Among [n variables](hyp:n) with [outcome space Ω](hyp:Ω), for
[a fixed clause determining the roots](hyp:c0), [a random clause
sequence](hyp:Cseq), [an omitted index](hyp:i), [a prefix time](hyp:s), and
[an outcome](hyp:ω), [the occupation integrand](goal) is the killing probability
raised to the power three halves when the nonroot solution set is nonempty, and
zero otherwise. -/
def occupationTerm (c0 : ProperClause n) (Cseq : ℕ → Ω → ProperClause n)
    (i s : ℕ) (ω : Ω) : ℝ :=
  (if (nonrootSolutions c0 Cseq i s ω).Nonempty then 1 else 0) *
    (killProcess c0 Cseq i s ω) ^ beta
  -- @realizes s(nonnegative prefix index in the future occupation sum)

open Classical in
/-- Among [n variables](hyp:n) with [outcome space Ω](hyp:Ω), for
[a fixed clause determining the roots](hyp:c0), [a random clause
sequence](hyp:Cseq), [an omitted index](hyp:i), [a prefix time](hyp:m), and
[an outcome](hyp:ω), [the duration bound](goal) is the smaller of the cap and
seven times the incidence parameter to the power three halves times the killing
probability to the power minus three halves when that probability is positive;
otherwise it is the cap. -/
def durationBound (c0 : ProperClause n) (Cseq : ℕ → Ω → ProperClause n)
    (i m : ℕ) (ω : Ω) : ℝ :=
  if 0 < killProcess c0 Cseq i m ω then
    min (capL n : ℝ) (occupationK * (incidenceParam c0 Cseq i ω : ℝ) ^ beta *
      (killProcess c0 Cseq i m ω) ^ (-beta))
  else capL n -- @realizes W_m(capped duration formula, L when p_m is zero)

open Classical in
-- @node: nonrootSolutions_antitone
/-- For [a fixed clause determining the roots](hyp:c0), [a random clause
sequence](hyp:Cseq), [an omitted index](hyp:i), and [an outcome](hyp:ω), [the
nonroot solution sets can only shrink as the prefix length increases](goal). -/
lemma nonrootSolutions_antitone (c0 : ProperClause n)
    (Cseq : ℕ → Ω → ProperClause n) (i : ℕ) (ω : Ω) :
    Antitone (fun m => nonrootSolutions c0 Cseq i m ω) := by
  intro a b hab z hz
  simp only [nonrootSolutions, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
  intro j hj hji
  exact hz j (Finset.mem_Icc.mpr
    ⟨(Finset.mem_Icc.mp hj).1, (Finset.mem_Icc.mp hj).2.trans hab⟩) hji

open Classical in
-- @node: isTest_clauseSat_glue
/-- For [a fixed clause determining the roots and their falsifying values](hyp:c0),
[a clause to test](hyp:c), and [any Boolean assignment to the nonroot variables](hyp:y),
if [the tested clause has exactly one root literal, with sign opposite to its sign
in the fixed clause](hyp:hc), then [combining the nonroot assignment with the fixed
clause's falsifying root values satisfies the tested clause](goal). -/
lemma isTest_clauseSat_glue (c0 c : ProperClause n)
    (y : Fin (nonrootCount n) → Bool) (hc : isTest c0 c) :
    ClauseSat c (glueAssignment c0 y) := by
  obtain ⟨l, hl, hs⟩ := hc.2
  obtain ⟨hlc, hlr⟩ := Finset.mem_filter.mp hl
  refine ⟨l, hlc, ?_⟩
  simp only [glueAssignment, dif_pos hlr, rootFalsifier]
  cases h : decide ((l.1, true) ∈ c0.val) <;> cases hb : l.2 <;> simp_all

open Classical in
/-- For [a fixed clause determining the roots](hyp:c0), [a random clause sequence](hyp:Cseq),
[an omitted index](hyp:i), [a prefix length](hyp:m), [a clause index](hyp:j), and
[a Boolean assignment to the nonroot variables](hyp:y), suppose [the prefix length
does not exceed the cap](hyp:hm) and [the clause index lies between one and the
prefix length and differs from the omitted index](hyp:hj). Then [whether that
clause is satisfied by the nonroot assignment combined with the fixed clause's
falsifying root values is measurable with respect to the ordinary information
at that prefix length](goal). -/
@[fun_prop]
-- @node: clauseSat_glue_measurable
lemma clauseSat_glue_measurable (c0 : ProperClause n)
    (Cseq : ℕ → Ω → ProperClause n) (i m j : ℕ)
    (hm : m ≤ capL n) (hj : j ∈ (Finset.Icc 1 m).erase i)
    (y : Fin (nonrootCount n) → Bool) :
    Measurable[ordinaryFiltration c0 Cseq i m]
      (fun ω => ClauseSat (Cseq j ω) (glueAssignment c0 y)) := by
  let : MeasurableSpace Ω := ordinaryFiltration c0 Cseq i m
  have hjL : j ∈ (Finset.Icc 1 (capL n)).erase i := by
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hj
    exact Finset.mem_erase.mpr ⟨hne, Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hmem).1, (Finset.mem_Icc.mp hmem).2.trans hm⟩⟩
  have he : @Measurable Ω _ _ ⊤ (fun ω => expose c0 (Cseq j ω)) := by
    apply Measurable.of_comap_le
    apply le_sup_of_le_left
    exact le_iSup_of_le j (le_iSup_of_le hjL le_rfl)
  have ho : @Measurable Ω _ _ ⊤ (fun ω => ordinaryContents c0 (Cseq j ω)) := by
    apply Measurable.of_comap_le
    apply le_sup_of_le_right
    exact le_iSup_of_le j (le_iSup_of_le hj le_rfl)
  have ht : MeasurableSet {ω | isTest c0 (Cseq j ω)} :=
    he (t := {e | e.1.card = 1 ∧
      ∃ l ∈ e.1, l.2 ≠ decide ((l.1, true) ∈ c0.val)}) (by trivial)
  have hes : MeasurableSet {ω | ∃ c, (expose c0 (Cseq j ω)).2 = some c ∧
      ClauseSat c (glueAssignment c0 y)} :=
    he (t := {e | ∃ c, e.2 = some c ∧ ClauseSat c (glueAssignment c0 y)}) (by trivial)
  have hos : MeasurableSet {ω | ∃ c, ordinaryContents c0 (Cseq j ω) = some c ∧
      ClauseSat c (glueAssignment c0 y)} :=
    ho (t := {o | ∃ c, o = some c ∧ ClauseSat c (glueAssignment c0 y)}) (by trivial)
  apply measurableSet_setOfPred.mp
  convert (ht.union hes).union hos using 1
  ext ω
  change ClauseSat (Cseq j ω) (glueAssignment c0 y) ↔
    (isTest c0 (Cseq j ω) ∨ _) ∨ _
  constructor
  · intro hs
    by_cases ht : isTest c0 (Cseq j ω)
    · exact Or.inl (Or.inl ht)
    · by_cases ho : isOrdinary c0 (Cseq j ω)
      · exact Or.inr ⟨Cseq j ω, by simp [ordinaryContents, ho], hs⟩
      · exact Or.inl (Or.inr ⟨Cseq j ω, by simp [expose, ho, ht], hs⟩)
  · rintro ((ht | ⟨c, heq, hs⟩) | ⟨c, heq, hs⟩)
    · exact isTest_clauseSat_glue c0 _ y ht
    · have heq' : Cseq j ω = c := by
        simp only [expose] at heq
        split at heq <;> simp_all
      exact heq'.symm ▸ hs
    · have heq' : Cseq j ω = c := by
        simp only [ordinaryContents] at heq
        split at heq <;> simp_all
      exact heq'.symm ▸ hs

open Classical in
/-- For [a fixed clause determining the roots](hyp:c0), [a random clause sequence](hyp:Cseq),
[an omitted index](hyp:i), and [a prefix length](hyp:m), if [the prefix length is
at least the omitted index and no greater than the cap](hyp:hm), then [the set of
nonroot assignments satisfying the prefix with that index omitted, when combined
with the fixed clause's falsifying root values, is measurable with respect to
the ordinary information at that prefix length](goal). -/
@[fun_prop]
-- @node: nonrootSolutions_measurable
lemma nonrootSolutions_measurable (c0 : ProperClause n)
    (Cseq : ℕ → Ω → ProperClause n) (i m : ℕ) (hm : i ≤ m ∧ m ≤ capL n) :
    @Measurable Ω (Finset (Fin (nonrootCount n) → Bool))
      (ordinaryFiltration c0 Cseq i m) ⊤ (nonrootSolutions c0 Cseq i m) := by
  let : MeasurableSpace Ω := ordinaryFiltration c0 Cseq i m
  have hmem (y : Fin (nonrootCount n) → Bool) :
      Measurable (fun ω => y ∈ nonrootSolutions c0 Cseq i m ω) := by
    have h : Measurable (fun ω => ∀ j : (Finset.Icc 1 m).erase i,
        ClauseSat (Cseq j ω) (glueAssignment c0 y)) :=
      Measurable.forall (fun j => clauseSat_glue_measurable c0 Cseq i m j hm.2 j.property y)
    convert h using 1
    ext ω
    simp only [nonrootSolutions, Finset.mem_filter, Finset.mem_univ, true_and,
      Subtype.forall, Finset.mem_erase]
    aesop
  let : MeasurableSpace (Finset (Fin (nonrootCount n) → Bool)) := ⊤
  apply measurable_to_countable'
  intro s
  have h := Measurable.forall (fun y => (hmem y).iff
    (measurable_const : Measurable (fun _ : Ω => y ∈ s)))
  convert h.setOf using 1
  ext ω
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq, Finset.ext_iff]

open Classical in
/-- For [a fixed clause determining the roots](hyp:c0), [a random clause sequence](hyp:Cseq),
and [an omitted index](hyp:i), [the larger of one and the number of clauses meeting
the roots, counted from one through the cap except at the omitted index, is
measurable with respect to the capped root exposure information](goal). -/
@[fun_prop]
-- @node: incidenceParam_measurable
lemma incidenceParam_measurable (c0 : ProperClause n)
    (Cseq : ℕ → Ω → ProperClause n) (i : ℕ) :
    @Measurable Ω ℕ (exposureSigma c0 Cseq i) inferInstance
      (incidenceParam c0 Cseq i) := by
  let : MeasurableSpace Ω := exposureSigma c0 Cseq i
  have he (j : ℕ) (hj : j ∈ (Finset.Icc 1 (capL n)).erase i) :
      @Measurable Ω _ _ ⊤ (fun ω => expose c0 (Cseq j ω)) := by
    apply Measurable.of_comap_le
    exact le_iSup_of_le j (le_iSup_of_le hj le_rfl)
  have hcount : Measurable (incidenceCount c0 Cseq i) := by
    have hevent (j : ℕ) (hj : j ∈ (Finset.Icc 1 (capL n)).erase i) :
        MeasurableSet {ω | 1 ≤ (rootLiterals c0 (Cseq j ω)).card} := by
      exact (he j hj) (t := {e | 1 ≤ e.1.card}) (by trivial)
    have hs : Measurable (fun ω =>
        ∑ j ∈ (Finset.Icc 1 (capL n)).erase i,
          if 1 ≤ (rootLiterals c0 (Cseq j ω)).card then (1 : ℕ) else 0) := by
      apply Finset.measurable_sum
      intro j hj
      exact Measurable.ite (hevent j hj) measurable_const measurable_const
    change Measurable (fun ω =>
      (((Finset.Icc 1 (capL n)).erase i).filter
        (fun j => 1 ≤ (rootLiterals c0 (Cseq j ω)).card)).card)
    simpa only [Finset.sum_boole, Nat.cast_id] using hs
  exact measurable_const.max hcount
    -- @realizes d(measurable with respect to the entire exposure)

open Classical in
/-- For [a fixed clause determining the roots](hyp:c0), [a random clause sequence](hyp:Cseq),
[an omitted index](hyp:i), and [a prefix length](hyp:m), if [the prefix length is
at least the omitted index and no greater than the cap](hyp:hm), then [the killing
probability of the nonroot solution set, evaluated using the incidence parameter,
is strongly measurable with respect to the ordinary information at that prefix
length](goal). -/
@[fun_prop]
-- @node: killProcess_stronglyMeasurable
lemma killProcess_stronglyMeasurable (c0 : ProperClause n)
    (Cseq : ℕ → Ω → ProperClause n) (i m : ℕ) (hm : i ≤ m ∧ m ≤ capL n) :
    StronglyMeasurable[ordinaryFiltration c0 Cseq i m] (killProcess c0 Cseq i m) := by
  let : MeasurableSpace Ω := ordinaryFiltration c0 Cseq i m
  have hd : Measurable (incidenceParam c0 Cseq i) :=
    (incidenceParam_measurable c0 Cseq i).mono le_sup_left le_rfl
  have hs : Measurable (nonrootSolutions c0 Cseq i m) :=
    (nonrootSolutions_measurable c0 Cseq i m hm).mono le_rfl le_top
  have hk : Measurable (fun p : ℕ × Finset (Fin (nonrootCount n) → Bool) =>
      killProb p.1 p.2) := by
    fun_prop
  exact (hk.comp (hd.prodMk hs)).stronglyMeasurable

open Classical in
-- @node: exposure_counts_range
/-- For [a fixed clause determining the roots](hyp:c0), [a random clause sequence](hyp:Cseq),
[an omitted index](hyp:i), and [an outcome](hyp:ω), if [the omitted index is positive
and no greater than the cap](hyp:hi), then [the incidence count and collision count
are each at most the cap minus one, and the incidence parameter is at least one](goal). -/
lemma exposure_counts_range (c0 : ProperClause n)
    (Cseq : ℕ → Ω → ProperClause n) (i : ℕ) (hi : DelayIndex i (capL n)) (ω : Ω) :
    incidenceCount c0 Cseq i ω ≤ capL n - 1 ∧ -- @realizes Z(at most L minus one)
    collisionCount c0 Cseq i ω ≤ capL n - 1 ∧ -- @realizes V(at most L minus one)
    1 ≤ incidenceParam c0 Cseq i ω := by -- @realizes d(positive by construction)
  have hcard : ((Finset.Icc 1 (capL n)).erase i).card = capL n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_Icc.mpr hi), Nat.card_Icc]
    omega
  refine ⟨?_, ?_, le_max_left _ _⟩
  · exact (Finset.card_filter_le _ _).trans_eq hcard
  · exact (Finset.card_filter_le _ _).trans_eq hcard

open Classical in
-- @node: killProcess_bounds
/-- With [at least six variables](hyp:hn), for [a fixed clause determining the roots](hyp:c0),
[a random clause sequence](hyp:Cseq), [an omitted index](hyp:i), [a prefix length](hyp:m),
and [an outcome](hyp:ω), [the killing probability of the nonroot solution set lies
between zero and one, inclusive](goal). -/
lemma killProcess_bounds (hn : OmissionN n) (c0 : ProperClause n)
    (Cseq : ℕ → Ω → ProperClause n) (i m : ℕ) (ω : Ω) :
    0 ≤ killProcess c0 Cseq i m ω ∧ killProcess c0 Cseq i m ω ≤ 1 := by
  exact killProb_bounds _ _
    -- @realizes p_m(probability in the closed unit interval)

open Classical in
-- @node: killProcess_monotone
/-- With [at least six variables](hyp:hn), for [a fixed clause determining the roots](hyp:c0),
[a random clause sequence](hyp:Cseq), [an omitted index](hyp:i), and [an outcome](hyp:ω),
[the killing probability of the nonroot solution set is nondecreasing as the
prefix length increases](goal). -/
lemma killProcess_monotone (hn : OmissionN n) (c0 : ProperClause n)
    (Cseq : ℕ → Ω → ProperClause n) (i : ℕ) (ω : Ω) :
    Monotone (fun m => killProcess c0 Cseq i m ω) := by
  intro a b hab
  exact killProb_antitone _ (nonrootSolutions_antitone c0 Cseq i ω hab)
    -- @realizes p_m(nondecreasing with prefix time)

open Classical in
-- @node: durationBound_range
/-- For [a fixed clause determining the roots](hyp:c0), [a random clause sequence](hyp:Cseq),
[an omitted index](hyp:i), [a prefix length](hyp:m), and [an outcome](hyp:ω),
[the duration bound lies between zero and the cap, inclusive](goal). -/
lemma durationBound_range (c0 : ProperClause n)
    (Cseq : ℕ → Ω → ProperClause n) (i m : ℕ) (ω : Ω) :
    0 ≤ durationBound c0 Cseq i m ω ∧ durationBound c0 Cseq i m ω ≤ capL n := by
  unfold durationBound
  split_ifs
  · exact ⟨le_min (Nat.cast_nonneg _) (by unfold occupationK; positivity), min_le_left _ _⟩
  · exact ⟨Nat.cast_nonneg _, le_rfl⟩
    -- @realizes W_m(real bound between zero and L)

end Papers.OaiLinearVarianceRandom

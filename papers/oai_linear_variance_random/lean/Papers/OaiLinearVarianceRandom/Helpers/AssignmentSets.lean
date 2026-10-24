module

public import Papers.OaiLinearVarianceRandom.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Data.Nat.Choose.Cast

/-!
# Assignment sets, killing probabilities, and the potential

All auxiliary clause families are sampled with replacement. Finite uniform
averages implement the killing probabilities without adding sampling witnesses
to the clause-process results.
-/

@[expose] public section

noncomputable section
namespace Papers.OaiLinearVarianceRandom
open MeasureTheory ProbabilityTheory
open scoped BigOperators
set_option linter.unusedVariables false

-- @env: S2
variable {u : ℕ}

open Classical in
-- @node: ass:one-u
/-- For [an assignment dimension u](hyp:u), [the dimension condition requires at least three coordinates](goal). -/
def OneU (u : ℕ) : Prop := 3 ≤ u -- @realizes u(assignment dimension at least three)

open Classical in
-- @node: ass:one-nonempty
/-- For [a set S of Boolean assignments](hyp:S) on [u coordinates](hyp:u),
[the nonemptiness condition requires S to contain an assignment](goal). -/
def OneNonempty (S : Finset (Fin u → Bool)) : Prop := S.Nonempty
  -- @realizes S(nonempty assignment set for the one-clause inequality)

open Classical in
-- @node: ass:potential-d
/-- For [an integer potential length d](hyp:d), [the positivity condition requires d to be at least one](goal). -/
def PotentialD (d : ℕ) : Prop := 1 ≤ d -- @realizes d(positive integer potential length)

open Classical in
-- @node: ass:one-clause-law
/-- For [a clause length a](hyp:a) and [a probability law ν on proper clauses of that length](hyp:ν)
over [u coordinates](hyp:u), [the uniform-clause condition says that ν is uniform over those clauses](goal). -/
def OneClauseLaw (a : ℕ) (ν : Measure (ProperClauseA u a)) : Prop :=
  ν = uniformClauseMeasure u a

open Classical in
-- @node: ass:potential-clause
/-- Given [a law ν for proper three-literal clauses](hyp:ν), [laws νj for auxiliary families of j proper two-literal clauses](hyp:νj),
and [joint laws for each auxiliary family and a three-literal clause](hyp:joint), all over [u coordinates](hyp:u),
[the potential clause-law condition](goal) requires [ν to be uniform](step:1) and
[each joint law to be the product of the corresponding auxiliary-family law and ν](step:2). -/
def PotentialClauseLaw (ν : Measure (ProperClauseA u 3))
    (νj : (j : ℕ) → Measure (Fin j → ProperClauseA u 2))
    (joint : (j : ℕ) → Measure ((Fin j → ProperClauseA u 2) × ProperClauseA u 3)) : Prop :=
  ν = uniformClauseMeasure u 3 ∧ -- @realizes C(uniform proper 3-clause marginal)
  ∀ j, joint j = (νj j).prod ν -- @realizes C(independent of every auxiliary clause family)

open Classical in
-- @node: ass:one-replacement
/-- Given [a law ν for proper two-literal clauses](hyp:ν) on [u coordinates](hyp:u)
and [laws νj for families of j such clauses](hyp:νj), [sampling with replacement means that every family law is the product of j copies of ν](goal). -/
def SampledWithReplacement (ν : Measure (ProperClauseA u 2))
    (νj : (j : ℕ) → Measure (Fin j → ProperClauseA u 2)) : Prop :=
  ∀ j, νj j = Measure.pi (fun _ : Fin j => ν)

open Classical in
-- @node: def:one-survivors
/-- For [an assignment set S](hyp:S) on [u coordinates](hyp:u) and [a proper clause C](hyp:C),
[the survivors are the assignments in S that satisfy C](goal). -/
def survivors {a : ℕ} (S : Finset (Fin u → Bool)) (C : ProperClauseA u a) :
    Finset (Fin u → Bool) := S.filter (ClauseSat C)
  -- @realizes S[C](assignments in S satisfying C)

open Classical in
/-- For [a family size j](hyp:j), [an assignment set S](hyp:S) on [u coordinates](hyp:u),
and [a family cs of j proper two-literal clauses](hyp:cs), [the family survivors are the assignments in S satisfying every clause in cs](goal). -/
def familySurvivors (j : ℕ) (S : Finset (Fin u → Bool))
    (cs : Fin j → ProperClauseA u 2) : Finset (Fin u → Bool) :=
  S.filter (fun z => ∀ k, ClauseSat (cs k) z)
  -- @realizes Y(assignments satisfying all j auxiliary clauses, including j zero)

open Classical in
-- @node: def:one-killing
/-- For [a number j of auxiliary clauses](hyp:j) and [an assignment set S](hyp:S) on [u coordinates](hyp:u),
[the killing probability is the fraction of all ordered families of j proper two-literal clauses that leave no survivors in S](goal). -/
def killProb (j : ℕ) (S : Finset (Fin u → Bool)) : ℝ :=
  (Fintype.card {cs : Fin j → ProperClauseA u 2 // familySurvivors j S cs = ∅} : ℝ) /
    Fintype.card (Fin j → ProperClauseA u 2)
  -- @realizes q_j(uniform with-replacement j-clause killing probability)

open Classical in
-- @node: def:one-empty-conventions
/-- [The killing-probability conventions](goal) require, in every dimension of at least three,
[the empty assignment set to have killing probability one for every family size](step:1) and
[every nonempty assignment set to have killing probability zero when no clauses are sampled](step:2). -/
def killProb_conventions : Prop :=
  ∀ u : ℕ, OneU u →
    (∀ j : ℕ, killProb (u := u) j ∅ = 1) ∧
    (∀ S : Finset (Fin u → Bool), S ≠ ∅ → killProb 0 S = 0)

open Classical in
-- @node: killProb_empty
/-- If [there are at least three coordinates](hyp:hu), then for [any number j of sampled clauses](hyp:j),
[the probability of killing the empty assignment set is one](goal). -/
lemma killProb_empty (hu : OneU u) (j : ℕ) :
    killProb (u := u) j ∅ = 1 := by
  haveI := properClauseA_nonempty u 2 (by unfold OneU at hu; omega)
  simp [killProb, familySurvivors]

open Classical in
-- @node: killProb_zero_of_nonempty
/-- If [there are at least three coordinates](hyp:hu) and [the assignment set S](hyp:S)
[is nonempty](hyp:hS), then [sampling zero clauses has probability zero of killing S](goal). -/
lemma killProb_zero_of_nonempty (hu : OneU u) (S : Finset (Fin u → Bool))
    (hS : OneNonempty S) : killProb 0 S = 0 := by
  have hempty : IsEmpty {cs : Fin 0 → ProperClauseA u 2 //
      familySurvivors 0 S cs = ∅} := by
    refine ⟨fun cs => ?_⟩
    have h : S = ∅ := by simpa [familySurvivors] using cs.property
    exact hS.ne_empty h
  simp [killProb]

open Classical in
-- @node: killProb_bounds
/-- For [any family size j](hyp:j) and [assignment set S](hyp:S),
[the killing probability lies between zero and one, inclusive](goal). -/
lemma killProb_bounds (j : ℕ) (S : Finset (Fin u → Bool)) :
    0 ≤ killProb j S ∧ killProb j S ≤ 1 := by
  constructor
  · unfold killProb
    positivity
  · exact div_le_one_of_le₀ (by exact_mod_cast (Fintype.card_subtype_le
      (fun cs : Fin j → ProperClauseA u 2 => familySurvivors j S cs = ∅)))
      (Nat.cast_nonneg _)

open Classical in
-- @node: killProb_antitone
/-- For [a family size j](hyp:j), if [S′ is a subset of S](hyp:h),
[the probability of killing S is no greater than the probability of killing S′](goal). -/
lemma killProb_antitone (j : ℕ) {S S' : Finset (Fin u → Bool)} (h : S' ⊆ S) :
    killProb j S ≤ killProb j S' := by
  unfold killProb
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Fintype.card_le_of_injective
    (fun cs : {cs : Fin j → ProperClauseA u 2 // familySurvivors j S cs = ∅} =>
      (⟨cs.val, Finset.eq_empty_iff_forall_notMem.mpr (by
        intro z hz
        have hz' := Finset.mem_filter.mp hz
        have : z ∈ familySurvivors j S cs.val :=
          Finset.mem_filter.mpr ⟨h hz'.1, hz'.2⟩
        simpa [cs.property] using this)⟩ :
          {cs : Fin j → ProperClauseA u 2 // familySurvivors j S' cs = ∅}))
    (by intro cs ds heq; apply Subtype.ext; exact congrArg (fun x => x.val) heq)

open Classical in
-- @node: def:one-beta
/-- [The exponent β is three halves](goal). -/
def beta : ℝ := 3 / 2 -- @realizes \beta(fixed real exponent three halves)

open Classical in
-- @node: def:one-h
/-- For [a clause length a](hyp:a) and [an assignment set S](hyp:S) on [u coordinates](hyp:u),
[the single-clause killing probability is the fraction of proper clauses of length a that leave no survivors in S](goal). -/
def oneKillProb (a : ℕ) (S : Finset (Fin u → Bool)) : ℝ :=
  (Fintype.card {C : ProperClauseA u a // survivors S C = ∅} : ℝ) /
    Fintype.card (ProperClauseA u a)
  -- @realizes h_a(uniform probability that one proper a-clause kills S)

open Classical in
-- @node: def:potential
/-- For [a potential length d](hyp:d) and [an assignment set S](hyp:S) on [u coordinates](hyp:u),
[the potential is the sum of the killing probabilities for family sizes from zero through d minus one](goal). -/
def potential (d : ℕ) (S : Finset (Fin u → Bool)) : ℝ :=
  ∑ j ∈ Finset.range d, killProb j S -- @realizes P_d(sum of q_j for j less than d)

open Classical in
/-- For [an assignment set S](hyp:S) on [u coordinates](hyp:u), [the frozen-coordinate count is the number of coordinates on which all assignments in S agree](goal). -/
def frozenCount (S : Finset (Fin u → Bool)) : ℕ :=
  (Finset.univ.filter (fun v => ∀ z ∈ S, ∀ z' ∈ S, z v = z' v)).card
  -- @realizes b(frozen-coordinate count between zero and u)

open Classical in
/-- For [a real argument t](hyp:t) and [a nonnegative integer length a](hyp:a),
[the falling factorial is the product of t minus k as k ranges from zero through a minus one](goal). -/
def fallingFactorial (t : ℝ) (a : ℕ) : ℝ :=
  ∏ k ∈ Finset.range a, (t - k) -- @realizes (t)_a(product of t minus k for k less than a)
  -- @realizes t(real falling-factorial argument)

open Classical in
-- @node: survivors_eq_empty_iff
/-- For [an assignment set S](hyp:S) and [a proper clause C](hyp:C),
[there are no survivors exactly when every assignment in S falsifies every literal of C](goal). -/
lemma survivors_eq_empty_iff {a : ℕ} (S : Finset (Fin u → Bool))
    (C : ProperClauseA u a) :
    survivors S C = ∅ ↔ ∀ l ∈ C.val, ∀ z ∈ S, z l.1 ≠ l.2 := by
  simp only [survivors, Finset.filter_eq_empty_iff, ClauseSat, not_exists, not_and]
  constructor
  · intro h l hl z hz
    exact h hz l hl
  · intro h z hz l hl
    exact h l hl z hz

open Classical in
-- @node: card_killingClauses
/-- For [a clause length a](hyp:a) and [an assignment set S](hyp:S) that [is nonempty](hyp:hS),
[the number of proper clauses of length a that kill S equals the number of ways to choose a frozen coordinates of S](goal). -/
lemma card_killingClauses (a : ℕ) (S : Finset (Fin u → Bool))
    (hS : OneNonempty S) :
    Fintype.card {C : ProperClauseA u a // survivors S C = ∅} =
      (frozenCount S).choose a := by
  obtain ⟨z₀, hz₀⟩ := hS
  let F : Finset (Fin u × Bool) :=
    Finset.univ.filter (fun l => ∀ z ∈ S, z l.1 ≠ l.2)
  have memF (l : Fin u × Bool) : l ∈ F ↔ ∀ z ∈ S, z l.1 ≠ l.2 := by
    simp [F]
  have sign (l : Fin u × Bool) (hl : l ∈ F) : l.2 = !(z₀ l.1) := by
    have h := (memF l).mp hl z₀ hz₀
    cases h₀ : z₀ l.1 <;> cases h₁ : l.2 <;> simp_all
  have inj : Set.InjOn Prod.fst (↑F : Set (Fin u × Bool)) := by
    intro l hl k hk h
    exact Prod.ext h (by rw [sign l hl, sign k hk, h])
  have cardF : F.card = frozenCount S := by
    rw [← Finset.card_image_iff.mpr inj]
    congr 1
    ext v
    constructor
    · intro hv
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro z hz z' hz'
      have h := (memF l).mp hl z hz
      have h' := (memF l).mp hl z' hz'
      cases h₁ : z l.1 <;> cases h₂ : z' l.1 <;> cases h₃ : l.2 <;> simp_all
    · intro hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
      apply Finset.mem_image.mpr
      refine ⟨(v, !(z₀ v)), (memF _).mpr ?_, rfl⟩
      intro z hz
      have h := hv z hz z₀ hz₀
      rw [h]
      cases z₀ v <;> simp
  let f : {C : ProperClauseA u a // survivors S C = ∅} →
      {t : Finset (Fin u × Bool) // t ∈ F.powersetCard a} := fun C =>
    ⟨C.val.val, Finset.mem_powersetCard.mpr
      ⟨fun l hl => (memF l).mpr ((survivors_eq_empty_iff S C.val).mp C.property l hl),
        C.val.property.1⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro C D h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun t => t.val) h
    · intro t
      obtain ⟨ht, hcard⟩ := Finset.mem_powersetCard.mp t.property
      let C : ProperClauseA u a := ⟨t.val, hcard,
        (Finset.card_image_of_injOn (inj.mono ht)).trans hcard⟩
      refine ⟨⟨C, (survivors_eq_empty_iff S C).mpr ?_⟩, rfl⟩
      intro l hl
      exact (memF l).mp (ht hl)
  calc
    _ = Fintype.card {t : Finset (Fin u × Bool) // t ∈ F.powersetCard a} :=
      Fintype.card_congr (Equiv.ofBijective f hf)
    _ = (F.card).choose a := by rw [Fintype.card_coe, Finset.card_powersetCard]
    _ = _ := by rw [cardF]

open Classical in
-- @node: oneKillProb_eq_choose
/-- For [a clause length a](hyp:a) and [an assignment set S](hyp:S) that [is nonempty](hyp:hS),
[the single-clause killing probability equals the number of ways to choose a frozen coordinates, divided by two to the power a times the number of ways to choose a coordinates from all u coordinates](goal). -/
lemma oneKillProb_eq_choose (a : ℕ) (S : Finset (Fin u → Bool))
    (hS : OneNonempty S) :
    oneKillProb a S = ((frozenCount S).choose a : ℝ) / (2 ^ a * u.choose a) := by
  rw [oneKillProb, card_killingClauses a S hS, card_properClauseA]
  push_cast
  rfl

open Classical in
-- @node: frozenCount_le
/-- For [any assignment set S](hyp:S), [the number of frozen coordinates is at most the total number u of coordinates](goal). -/
lemma frozenCount_le (S : Finset (Fin u → Bool)) : frozenCount S ≤ u := by
  simpa [frozenCount] using
    (Finset.card_filter_le (s := Finset.univ (α := Fin u))
      (p := fun v => ∀ z ∈ S, ∀ z' ∈ S, z v = z' v))

-- @node: cast_choose_three
/-- For [a nonnegative integer t](hyp:t), [the number of ways to choose three elements from t elements equals t times t minus one times t minus two, divided by six, with the arithmetic evaluated over the real numbers](goal). -/
lemma cast_choose_three (t : ℕ) :
    (t.choose 3 : ℝ) = (t : ℝ) * (t - 1) * (t - 2) / 6 := by
  have h := Nat.descFactorial_eq_factorial_mul_choose t 3
  by_cases ht : 2 ≤ t
  · have h' : (t : ℝ) * (t - 1) * (t - 2) = 6 * (t.choose 3 : ℝ) := by
      have hcast := congrArg (fun k : ℕ => (k : ℝ)) h
      norm_num [Nat.descFactorial_succ, Nat.cast_sub ht,
        Nat.cast_sub (show 1 ≤ t by omega)] at hcast
      nlinarith [hcast]
    linarith
  · rw [Nat.choose_eq_zero_of_lt (by omega)]
    interval_cases t <;> norm_num

open Classical in
-- @node: oneKillProb_two_formula
/-- For [an assignment set S](hyp:S) that [is nonempty](hyp:hS),
[the probability that one proper two-literal clause kills S equals b(b − 1) divided by 4u(u − 1), where b is the frozen-coordinate count and u is the total coordinate count](goal). -/
lemma oneKillProb_two_formula (S : Finset (Fin u → Bool)) (hS : OneNonempty S) :
    oneKillProb 2 S = (frozenCount S : ℝ) * (frozenCount S - 1) /
      (4 * (u : ℝ) * (u - 1)) := by
  rw [oneKillProb_eq_choose 2 S hS, Nat.cast_choose_two, Nat.cast_choose_two]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  norm_num
  ring

open Classical in
-- @node: oneKillProb_three_formula
/-- For [an assignment set S](hyp:S) that [is nonempty](hyp:hS),
[the probability that one proper three-literal clause kills S equals b(b − 1)(b − 2) divided by 8u(u − 1)(u − 2), where b is the frozen-coordinate count and u is the total coordinate count](goal). -/
lemma oneKillProb_three_formula (S : Finset (Fin u → Bool)) (hS : OneNonempty S) :
    oneKillProb 3 S = (frozenCount S : ℝ) * (frozenCount S - 1) * (frozenCount S - 2) /
      (8 * (u : ℝ) * (u - 1) * (u - 2)) := by
  rw [oneKillProb_eq_choose 3 S hS, cast_choose_three, cast_choose_three]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  norm_num
  ring

-- @node: rpow_beta_eq_mul_sqrt
/-- If [a real number x is nonnegative](hyp:hx), [x raised to the exponent β, which is three halves, equals x times its square root](goal). -/
lemma rpow_beta_eq_mul_sqrt {x : ℝ} (hx : 0 ≤ x) :
    x ^ beta = x * Real.sqrt x := by
  have h := Real.rpow_add_of_nonneg hx (by norm_num : (0 : ℝ) ≤ 1)
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  simpa only [show (1 : ℝ) + 1 / 2 = beta by norm_num [beta],
    Real.rpow_one, ← Real.sqrt_eq_rpow] using h

set_option maxHeartbeats 800000 in
-- Finite-probability formulas and the three real-algebra cases elaborate together.
open Classical in
-- @node: lem:one
/-- Suppose [there are at least three coordinates](hyp:hu), [ν specifies a clause law for each clause length](hyp:ν),
and [the laws for lengths two and three are uniform](hyp:hclause). For [an assignment set S](hyp:S)
that [is nonempty](hyp:hS), with [auxiliary laws νj for families of two-literal clauses](hyp:νj)
that [sample independently with replacement from the two-literal law](hyp:hreplacement),
[the two-literal killing probability raised to three halves is at most three times the three-literal killing probability plus the inverse cube of the coordinate count](goal). -/
lemma oneKillProb_two_rpow_le (hu : OneU u)
    (ν : (a : ℕ) → Measure (ProperClauseA u a))
    (hclause : ∀ a, a = 2 ∨ a = 3 → OneClauseLaw a (ν a))
    (S : Finset (Fin u → Bool)) (hS : OneNonempty S)
    (νj : (j : ℕ) → Measure (Fin j → ProperClauseA u 2))
    (hreplacement : SampledWithReplacement (ν 2) νj) :
    (oneKillProb 2 S) ^ beta ≤ 3 * oneKillProb 3 S + (u : ℝ) ^ (-3 : ℝ) := by
  classical
  have huR : (3 : ℝ) ≤ u := by exact_mod_cast hu
  have hu0 : 0 < (u : ℝ) := by linarith
  have hu1 : 0 < (u : ℝ) - 1 := by linarith
  have hu2 : 0 < (u : ℝ) - 2 := by linarith
  have hb0 : (0 : ℝ) ≤ frozenCount S := Nat.cast_nonneg _
  have hbu : (frozenCount S : ℝ) ≤ u := by exact_mod_cast frozenCount_le S
  have h2nonneg : 0 ≤ oneKillProb 2 S := by unfold oneKillProb; positivity
  have h3nonneg : 0 ≤ oneKillProb 3 S := by unfold oneKillProb; positivity
  have hsqrt : Real.sqrt (oneKillProb 2 S) ≤ (frozenCount S : ℝ) / (2 * u) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [oneKillProb_two_formula S hS, div_pow]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith only [mul_nonneg (mul_nonneg hb0 hu0.le) (sub_nonneg.mpr hbu)]
  rw [rpow_beta_eq_mul_sqrt h2nonneg]
  by_cases hbsmall : frozenCount S < 2
  · have hz : oneKillProb 2 S = 0 := by
      rw [oneKillProb_eq_choose 2 S hS, Nat.choose_eq_zero_of_lt hbsmall]
      simp
    rw [hz, zero_mul]
    positivity
  · by_cases hbeq : frozenCount S = 2
    · have h2 : oneKillProb 2 S = 1 / (2 * (u : ℝ) * (u - 1)) := by
        rw [oneKillProb_two_formula S hS, hbeq]
        push_cast
        field_simp
        ring
      have hle : oneKillProb 2 S ≤ (1 / (u : ℝ)) ^ 2 := by
        rw [h2, div_pow]
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        nlinarith only [mul_nonneg hu0.le hu2.le]
      have hs : Real.sqrt (oneKillProb 2 S) ≤ 1 / (u : ℝ) :=
        Real.sqrt_le_iff.mpr ⟨by positivity, hle⟩
      calc
        _ ≤ (1 / (u : ℝ)) ^ 2 * (1 / (u : ℝ)) :=
          mul_le_mul hle hs (Real.sqrt_nonneg _) (by positivity)
        _ = (u : ℝ) ^ (-3 : ℝ) := by
          rw [Real.rpow_neg hu0.le]
          norm_num
          simp [pow_succ, mul_assoc]
        _ ≤ _ := le_add_of_nonneg_left (by positivity)
    · have hb3 : (3 : ℝ) ≤ frozenCount S := by exact_mod_cast (show 3 ≤ frozenCount S by omega)
      have hratio : (frozenCount S : ℝ) / (2 * u) ≤
          3 * ((frozenCount S : ℝ) - 2) / (2 * ((u : ℝ) - 2)) := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        nlinarith only [mul_nonneg hu0.le (sub_nonneg.mpr hb3), hb0]
      have hid : oneKillProb 2 S *
          (3 * ((frozenCount S : ℝ) - 2) / (2 * ((u : ℝ) - 2))) =
          3 * oneKillProb 3 S := by
        rw [oneKillProb_two_formula S hS, oneKillProb_three_formula S hS]
        field_simp
        ring
      calc
        _ ≤ oneKillProb 2 S * ((frozenCount S : ℝ) / (2 * u)) :=
          mul_le_mul_of_nonneg_left hsqrt h2nonneg
        _ ≤ oneKillProb 2 S *
            (3 * ((frozenCount S : ℝ) - 2) / (2 * ((u : ℝ) - 2))) :=
          mul_le_mul_of_nonneg_left hratio h2nonneg
        _ = 3 * oneKillProb 3 S := hid
        _ ≤ _ := le_add_of_nonneg_right (by positivity)


end Papers.OaiLinearVarianceRandom

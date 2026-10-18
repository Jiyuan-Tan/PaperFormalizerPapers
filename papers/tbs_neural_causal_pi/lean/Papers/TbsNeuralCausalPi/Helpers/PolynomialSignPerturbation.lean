module
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Data.Set.Card
public import Mathlib.Tactic
/-! # Reducing weak polynomial comparisons to strict signs

One extra parameter separates every zero from both comparison thresholds on
a finite sample. This preserves the original parameter count up to one and
the degree up to its maximum with one. The degree-dependent sign-count bound
itself remains a separate local proof obligation.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
noncomputable section

-- @node: finite_sign_margin
/-- For a finite collection of real values, [there is a positive margin smaller than the absolute value of every nonzero entry](goal). -/
lemma finite_sign_margin {I : Type*} (s : Finset I) (v : I → ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i ∈ s, v i ≠ 0 → δ < |v i| := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨δ, hδ, hbound⟩ := ih
    by_cases hv : v i = 0
    · refine ⟨δ, hδ, ?_⟩
      intro j hj hj0
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact (hj0 hv).elim
      · exact hbound j hj hj0
    · refine ⟨min δ (|v i| / 2), lt_min hδ (half_pos (abs_pos.mpr hv)), ?_⟩
      intro j hj hj0
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact (min_le_right _ _).trans_lt (half_lt_self (abs_pos.mpr hv))
      · exact (min_le_left _ _).trans_lt (hbound j hj hj0)

-- @node: finite_comparisons_strict_shift
/-- For finitely many real values, [one positive shift makes nonpositivity equivalent to strict negativity after subtraction and negativity equivalent to strict negativity after addition, with neither shifted value ever zero](goal). -/
lemma finite_comparisons_strict_shift {I : Type*} [Fintype I] (v : I → ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i,
      (v i ≤ 0 ↔ v i - δ < 0) ∧
      (v i < 0 ↔ v i + δ < 0) ∧ v i - δ ≠ 0 ∧ v i + δ ≠ 0 := by
  obtain ⟨δ, hδ, hb⟩ := finite_sign_margin Finset.univ v
  refine ⟨δ, hδ, ?_⟩
  intro i
  rcases lt_trichotomy (v i) 0 with hi | hi | hi
  · have hm := hb i (Finset.mem_univ i) hi.ne
    rw [abs_of_neg hi] at hm
    constructor
    · constructor <;> intro h <;> linarith
    · constructor
      · constructor <;> intro h <;> linarith
      · constructor <;> intro h <;> linarith
  · rw [hi]
    constructor
    · constructor <;> intro h <;> linarith
    · constructor
      · constructor <;> intro h <;> linarith
      · constructor <;> intro h <;> linarith
  · have hm := hb i (Finset.mem_univ i) hi.ne'
    rw [abs_of_pos hi] at hm
    constructor
    · constructor <;> intro h <;> linarith
    · constructor
      · constructor <;> intro h <;> linarith
      · constructor <;> intro h <;> linarith

-- @node: signShiftPolynomial
/-- For [a real polynomial](hyp:p) and [a choice of upward or downward shift](hyp:upper), the [shifted polynomial in one additional variable](goal) [adds that variable for an upward shift](step:1) and [subtracts it otherwise](step:2). -/
def signShiftPolynomial {V : Type*} (p : MvPolynomial V ℝ) (upper : Bool) :
    MvPolynomial (Option V) ℝ :=
  if upper then MvPolynomial.rename some p + MvPolynomial.X none
  else MvPolynomial.rename some p - MvPolynomial.X none

-- @node: signShiftAssignment
/-- Given [values for the original variables](hyp:a) and [a shift amount](hyp:δ), the [extended assignment](goal) [assigns the shift amount to the new variable](step:1) and [retains the original value for each original variable](step:2). -/
def signShiftAssignment {V : Type*} (a : V → ℝ) (δ : ℝ) : Option V → ℝ
  | none => δ
  | some v => a v

-- @node: signShiftPolynomial_eval
/-- [Evaluating the shifted polynomial at the extended assignment gives the original polynomial value plus the shift for the upward choice, and minus the shift otherwise](goal). -/
lemma signShiftPolynomial_eval {V : Type*} (p : MvPolynomial V ℝ)
    (a : V → ℝ) (δ : ℝ) (upper : Bool) :
    MvPolynomial.eval (signShiftAssignment a δ) (signShiftPolynomial p upper) =
      if upper then MvPolynomial.eval a p + δ else MvPolynomial.eval a p - δ := by
  cases upper <;>
    simp [signShiftPolynomial, MvPolynomial.eval_rename, signShiftAssignment, Function.comp_def]

-- @node: signShiftPolynomial_degree
/-- [The total degree of either shifted polynomial is at most the larger of the original total degree and one](goal). -/
lemma signShiftPolynomial_degree {V : Type*} (p : MvPolynomial V ℝ) (upper : Bool) :
    (signShiftPolynomial p upper).totalDegree ≤ max p.totalDegree 1 := by
  cases upper
  · exact (MvPolynomial.totalDegree_sub _ _).trans
      (max_le_max (MvPolynomial.totalDegree_rename_le _ _) (by simp))
  · exact (MvPolynomial.totalDegree_add _ _).trans
      (max_le_max (MvPolynomial.totalDegree_rename_le _ _) (by simp))

-- @node: polynomial_comparisons_strict_signs
/-- For finitely many real polynomials and an assignment of their variables, [there is an extended assignment under which downward shifts encode the original nonpositive comparisons and upward shifts encode the original negative comparisons as strict negative signs, and all shifted values are nonzero](goal). -/
lemma polynomial_comparisons_strict_signs {I V : Type*} [Fintype I]
    (p : I → MvPolynomial V ℝ) (a : V → ℝ) :
    ∃ b : Option V → ℝ, ∀ i,
      (MvPolynomial.eval a (p i) ≤ 0 ↔
        MvPolynomial.eval b (signShiftPolynomial (p i) false) < 0) ∧
      (MvPolynomial.eval a (p i) < 0 ↔
        MvPolynomial.eval b (signShiftPolynomial (p i) true) < 0) ∧
      MvPolynomial.eval b (signShiftPolynomial (p i) false) ≠ 0 ∧
      MvPolynomial.eval b (signShiftPolynomial (p i) true) ≠ 0 := by
  obtain ⟨δ, _, hδ⟩ := finite_comparisons_strict_shift (fun i => MvPolynomial.eval a (p i))
  refine ⟨signShiftAssignment a δ, ?_⟩
  intro i
  simpa only [signShiftPolynomial_eval, Bool.false_eq_true, ↓reduceIte] using hδ i

-- @node: polynomialComparisonPattern
/-- For [a family of real polynomials](hyp:p) and [an assignment of their variables](hyp:a), the [comparison pattern](goal) records for each polynomial [whether its value is nonpositive](step:1) and [whether its value is negative](step:2). -/
def polynomialComparisonPattern {I V : Type*} (p : I → MvPolynomial V ℝ)
    (a : V → ℝ) : I → Bool × Bool :=
  fun i => (decide (MvPolynomial.eval a (p i) ≤ 0), decide (MvPolynomial.eval a (p i) < 0))

-- @node: comparisonPatternEncode
/-- For [an indexed family of pairs of truth values](hyp:f), the [single Boolean encoding on indices paired with a selector](goal) [returns the second truth value when the selector is true](step:1) and [the first truth value otherwise](step:2). -/
def comparisonPatternEncode {I : Type*} (f : I → Bool × Bool) : I × Bool → Bool :=
  fun ib => if ib.2 then (f ib.1).2 else (f ib.1).1

-- @node: comparisonPatternEncode_injective
/-- [Encoding each pair of truth values by an index and a Boolean selector preserves distinct comparison patterns](goal). -/
lemma comparisonPatternEncode_injective {I : Type*} :
    Function.Injective (comparisonPatternEncode : (I → Bool × Bool) → (I × Bool → Bool)) := by
  intro f g h
  funext i
  apply Prod.ext
  · simpa [comparisonPatternEncode] using congrFun h (i, false)
  · simpa [comparisonPatternEncode] using congrFun h (i, true)

-- @node: strictPolynomialSignPattern
/-- For [a family of real polynomials](hyp:p) and [an assignment of their variables](hyp:a), the [strict sign pattern](goal) records whether each polynomial value is negative. -/
def strictPolynomialSignPattern {I V : Type*} (p : I → MvPolynomial V ℝ)
    (a : V → ℝ) : I → Bool :=
  fun i => decide (MvPolynomial.eval a (p i) < 0)

-- @node: polynomialComparisonPattern_range_subset
/-- For a finite family of real polynomials, [every encoded pattern of nonpositive and negative comparisons is a strict sign pattern of the upward and downward shifted polynomials](goal). -/
lemma polynomialComparisonPattern_range_subset {I V : Type*} [Fintype I]
    (p : I → MvPolynomial V ℝ) :
    Set.range (fun a => comparisonPatternEncode (polynomialComparisonPattern p a)) ⊆
      Set.range (strictPolynomialSignPattern
        (fun ib : I × Bool => signShiftPolynomial (p ib.1) ib.2)) := by
  rintro _ ⟨a, rfl⟩
  obtain ⟨b, hb⟩ := polynomial_comparisons_strict_signs p a
  refine ⟨b, ?_⟩
  funext ib
  rcases ib with ⟨i, upper⟩
  cases upper
  · exact (Bool.decide_congr (hb i).1).symm
  · exact (Bool.decide_congr (hb i).2.1).symm

-- @node: polynomialComparisonPattern_encard_le
/-- For a finite family of real polynomials, [the number of attainable comparison patterns is at most the number of attainable strict sign patterns of the upward and downward shifted polynomials](goal). -/
lemma polynomialComparisonPattern_encard_le {I V : Type*} [Fintype I]
    (p : I → MvPolynomial V ℝ) :
    (Set.range (polynomialComparisonPattern p)).encard ≤
      (Set.range (strictPolynomialSignPattern
        (fun ib : I × Bool => signShiftPolynomial (p ib.1) ib.2))).encard := by
  calc
    _ = (comparisonPatternEncode '' Set.range (polynomialComparisonPattern p)).encard :=
      (comparisonPatternEncode_injective.encard_image _).symm
    _ ≤ _ := Set.encard_mono (by
      rintro _ ⟨pattern, ⟨a, rfl⟩, rfl⟩
      exact polynomialComparisonPattern_range_subset p ⟨a, rfl⟩)

-- @node: polynomialComparisonPattern_range_subset_nonzero
/-- For a finite family of real polynomials, [every encoded comparison pattern is a strict sign pattern of the shifted polynomials at an assignment where all of those polynomials are nonzero](goal). -/
lemma polynomialComparisonPattern_range_subset_nonzero {I V : Type*} [Fintype I]
    (p : I → MvPolynomial V ℝ) :
    Set.range (fun a => comparisonPatternEncode (polynomialComparisonPattern p a)) ⊆
      strictPolynomialSignPattern (fun ib : I × Bool => signShiftPolynomial (p ib.1) ib.2) ''
        {b | ∀ ib : I × Bool, MvPolynomial.eval b (signShiftPolynomial (p ib.1) ib.2) ≠ 0} := by
  rintro _ ⟨a, rfl⟩
  obtain ⟨b, hb⟩ := polynomial_comparisons_strict_signs p a
  refine ⟨b, ?_, ?_⟩
  · rintro ⟨i, upper⟩
    cases upper
    · exact (hb i).2.2.1
    · exact (hb i).2.2.2
  · funext ib
    rcases ib with ⟨i, upper⟩
    cases upper
    · exact (Bool.decide_congr (hb i).1).symm
    · exact (Bool.decide_congr (hb i).2.1).symm

-- @node: polynomialComparisonPattern_encard_le_nonzero
/-- For a finite family of real polynomials, [the number of attainable comparison patterns is at most the number of strict sign patterns of the shifted polynomials attained where all shifted polynomials are nonzero](goal). -/
lemma polynomialComparisonPattern_encard_le_nonzero {I V : Type*} [Fintype I]
    (p : I → MvPolynomial V ℝ) :
    (Set.range (polynomialComparisonPattern p)).encard ≤
      (strictPolynomialSignPattern (fun ib : I × Bool => signShiftPolynomial (p ib.1) ib.2) ''
        {b | ∀ ib : I × Bool, MvPolynomial.eval b (signShiftPolynomial (p ib.1) ib.2) ≠ 0}).encard := by
  calc
    _ = (comparisonPatternEncode '' Set.range (polynomialComparisonPattern p)).encard :=
      (comparisonPatternEncode_injective.encard_image _).symm
    _ ≤ _ := Set.encard_mono (by
      rintro _ ⟨pattern, ⟨a, rfl⟩, rfl⟩
      exact polynomialComparisonPattern_range_subset_nonzero p ⟨a, rfl⟩)

end
end Papers.TbsNeuralCausalPi

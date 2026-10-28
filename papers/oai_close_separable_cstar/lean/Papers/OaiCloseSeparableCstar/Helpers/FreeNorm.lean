module

public import Papers.OaiCloseSeparableCstar.Basic
public import Mathlib.GroupTheory.FreeGroup.Reduce

/-! # Lemma 9: the free-generator operator norm bound -/

@[expose] public section

open scoped BigOperators

namespace Papers.OaiCloseSeparableCstar

/-- For [a generator letter with a specified sign](hyp:a), the [first-letter
projection](goal) retains exactly the coordinates indexed by reduced words beginning
with that letter and sets all other coordinates to zero. -/
-- @node: firstLetterProj
noncomputable def firstLetterProj (a : ℕ × Bool) : Op KSp :=
  diagOp (fun x : FG => if x.toWord.head? = some a then (1 : Op ℂ) else 0) 1
    (by intro x; split_ifs <;> simp)

-- @node: firstLetterProj_apply
/-- [The coordinate of a first-letter projection equals the original vector's
coordinate when the reduced word starts with the selected letter, and is zero
otherwise](goal). -/
lemma firstLetterProj_apply (a : ℕ × Bool) (v : KSp) (x : FG) :
    (firstLetterProj a v) x = if x.toWord.head? = some a then v x else 0 := by
  classical
  change (if x.toWord.head? = some a then (1 : Op ℂ) else 0) (v x) = _
  split_ifs <;> rfl

-- @node: firstLetterProj_star
/-- [The projection onto words beginning with a given letter equals its own
adjoint](goal). -/
lemma firstLetterProj_star (a : ℕ × Bool) : star (firstLetterProj a) = firstLetterProj a := by
  classical
  ext v x
  rw [diagonal_star_apply (firstLetterProj a)
    (fun x => if x.toWord.head? = some a then (1 : Op ℂ) else 0)
    (by intros; rfl)]
  rw [firstLetterProj_apply]
  split_ifs <;> simp

-- @node: firstLetterProj_norm_le
/-- [The operator norm of the projection onto words beginning with a given
letter is at most one](goal). -/
lemma firstLetterProj_norm_le (a : ℕ × Bool) : ‖firstLetterProj a‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  rw [one_mul]
  apply lp.norm_mono (by norm_num)
  intro x
  rw [firstLetterProj_apply]
  split_ifs <;> simp

-- @node: firstLetterProj_mul_eq_zero
/-- If [two signed generator letters are distinct](hyp:hab), then [the product
of their first-letter projections is the zero operator](goal). -/
lemma firstLetterProj_mul_eq_zero {a b : ℕ × Bool} (hab : a ≠ b) :
    firstLetterProj a * firstLetterProj b = 0 := by
  classical
  ext v x
  change (firstLetterProj a (firstLetterProj b v)) x = 0
  rw [firstLetterProj_apply, firstLetterProj_apply]
  by_cases ha : x.toWord.head? = some a
  · have hb : x.toWord.head? ≠ some b := by
      intro hb
      exact hab (Option.some.inj (ha.symm.trans hb))
    simp [ha, hab]
  · simp [ha]

/-- [Multiplying a reduced word on the left by the inverse of a generator
produces a word starting with that inverse if and only if the original word
does not start with the positive generator](goal). -/
-- @node: firstLetter_inv_mul
lemma firstLetter_inv_mul (i : ℕ) (x : FG) :
    ((gen i)⁻¹ * x).toWord.head? = some (i, false) ↔
      x.toWord.head? ≠ some (i, true) := by
  have hw : ((gen i)⁻¹ * x).toWord = FreeGroup.reduce ((i, false) :: x.toWord) := by
    simp [FreeGroup.toWord_mul, FreeGroup.toWord_inv, gen, FreeGroup.toWord_of,
      FreeGroup.invRev]
  rw [hw, FreeGroup.reduce.cons, FreeGroup.reduce_toWord]
  have hr := FreeGroup.isReduced_toWord (x := x)
  cases hx : x.toWord with
  | nil => simp
  | cons a w =>
    rcases a with ⟨j, b⟩
    cases b
    · simp
    · by_cases hij : i = j
      · subst j
        cases w with
        | nil => simp
        | cons a w =>
          have hn : a ≠ (i, false) := by
            intro ha
            subst a
            simp [FreeGroup.IsReduced, hx, List.isChain_cons_cons] at hr
          simp [hn]
      · simp [hij, Ne.symm hij]

/-- [Left translation by a generator equals the sum of its translation followed
by projection onto words starting with that positive generator, and its translation
preceded by projection onto words starting with the inverse generator](goal). -/
-- @node: leftReg_generator_split
lemma leftReg_generator_split (i : ℕ) :
    (leftReg (gen i) : Op KSp) =
      firstLetterProj (i, true) * (leftReg (gen i) : Op KSp) +
      (leftReg (gen i) : Op KSp) * firstLetterProj (i, false) := by
  classical
  ext v x
  change v ((gen i)⁻¹ * x) =
    (firstLetterProj (i, true) ((leftReg (gen i) : Op KSp) v)) x +
      (firstLetterProj (i, false) v) ((gen i)⁻¹ * x)
  rw [firstLetterProj_apply, firstLetterProj_apply]
  change v ((gen i)⁻¹ * x) =
    (if x.toWord.head? = some (i, true) then v ((gen i)⁻¹ * x) else 0) + _
  by_cases hx : x.toWord.head? = some (i, true)
  · have hn : ((gen i)⁻¹ * x).toWord.head? ≠ some (i, false) := by
      exact fun h => (firstLetter_inv_mul i x).mp h hx
    simp [hx, hn]
  · simp [hx, (firstLetter_inv_mul i x).mpr hx]

/-- If [each operator in a finite family has norm at most one](hyp:hA) and
[the adjoint of any member times any distinct member is zero](hyp:horth), then
[the norm of their sum is at most the square root of the number of indices](goal). -/
-- @node: norm_sum_orthogonal_contractions
lemma norm_sum_orthogonal_contractions {ι : Type*} (s : Finset ι) (A : ι → Op KSp)
    (hA : ∀ i ∈ s, ‖A i‖ ≤ 1)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → star (A i) * A j = 0) :
    ‖∑ i ∈ s, A i‖ ≤ Real.sqrt s.card := by
  classical
  have he : star (∑ i ∈ s, A i) * (∑ i ∈ s, A i) =
      ∑ i ∈ s, star (A i) * A i := by
    rw [star_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    exact Finset.sum_eq_single i (fun j hj hji => horth i hi j hj hji.symm)
      (fun hn => (hn hi).elim)
  have hs : ‖∑ i ∈ s, A i‖ ^ 2 ≤ (s.card : ℝ) := by
    calc
      _ = ‖star (∑ i ∈ s, A i) * (∑ i ∈ s, A i)‖ := by
        rw [CStarRing.norm_star_mul_self, pow_two]
      _ = ‖∑ i ∈ s, star (A i) * A i‖ := congrArg norm he
      _ ≤ ∑ i ∈ s, ‖star (A i) * A i‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ s, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [CStarRing.norm_star_mul_self]
        exact (mul_le_mul (hA i hi) (hA i hi) (norm_nonneg _) zero_le_one).trans_eq
          (one_mul 1)
      _ = _ := by simp
  exact (Real.le_sqrt (norm_nonneg _) (Nat.cast_nonneg _)).mpr hs

/-- If [the assignment of signed first letters to indices is injective](hyp:ha)
and [each operator indexed by the finite set has norm at most one](hyp:hT), then
[the sum of these operators, each followed by its assigned first-letter projection,
has norm at most the square root of the number of indices](goal). -/
-- @node: norm_sum_firstLetter_contractions
lemma norm_sum_firstLetter_contractions {ι : Type*} (s : Finset ι)
    (a : ι → ℕ × Bool) (ha : Function.Injective a) (T : ι → Op KSp)
    (hT : ∀ i ∈ s, ‖T i‖ ≤ 1) :
    ‖∑ i ∈ s, firstLetterProj (a i) * T i‖ ≤ Real.sqrt s.card := by
  apply norm_sum_orthogonal_contractions
  · intro i hi
    exact (norm_mul_le _ _).trans
      ((mul_le_mul (firstLetterProj_norm_le _) (hT i hi)
        (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))
  · intro i hi j hj hij
    rw [star_mul, firstLetterProj_star]
    calc
      star (T i) * firstLetterProj (a i) * (firstLetterProj (a j) * T j) =
          star (T i) * (firstLetterProj (a i) * firstLetterProj (a j)) * T j := by
            simp only [mul_assoc]
      _ = 0 := by rw [firstLetterProj_mul_eq_zero (fun h => hij (ha h))]; simp

-- @node: lem:free-norm
/-- If [the number of generators is positive](hyp:hm), then [the norm of the
sum of left translations by the first that many free generators is at most twice
the square root of their number](goal). -/
lemma norm_sum_leftReg_gen_le (m : ℕ) (hm : 0 < m) :
    ‖∑ i ∈ Finset.range m, (leftReg (gen i) : Op KSp)‖ ≤ 2 * Real.sqrt m := by
  let U : ℕ → Op KSp := fun i => (leftReg (gen i) : Op KSp)
  have hU (i : ℕ) : ‖U i‖ ≤ 1 := unitary_norm_le_one (leftReg (gen i))
  have ha : ‖∑ i ∈ Finset.range m, firstLetterProj (i, true) * U i‖ ≤
      Real.sqrt m := by
    simpa using norm_sum_firstLetter_contractions (Finset.range m)
      (fun i => (i, true)) (fun _ _ h => congrArg Prod.fst h) U (fun i _ => hU i)
  have hb : ‖∑ i ∈ Finset.range m, U i * firstLetterProj (i, false)‖ ≤
      Real.sqrt m := by
    have h := norm_sum_firstLetter_contractions (Finset.range m)
      (fun i => (i, false)) (fun _ _ h => congrArg Prod.fst h)
      (fun i => star (U i)) (fun i _ => by simpa only [norm_star] using hU i)
    have he : (∑ i ∈ Finset.range m, firstLetterProj (i, false) * star (U i)) =
        star (∑ i ∈ Finset.range m, U i * firstLetterProj (i, false)) := by
      simp only [star_sum, star_mul, firstLetterProj_star]
    simpa only [he, norm_star, Finset.card_range] using h
  have hs : (∑ i ∈ Finset.range m, U i) =
      (∑ i ∈ Finset.range m, firstLetterProj (i, true) * U i) +
      (∑ i ∈ Finset.range m, U i * firstLetterProj (i, false)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => leftReg_generator_split i)
  change ‖∑ i ∈ Finset.range m, U i‖ ≤ _
  rw [hs]
  exact (norm_add_le _ _).trans ((add_le_add ha hb).trans_eq (by ring))

end Papers.OaiCloseSeparableCstar

module
public import Papers.OaiMetricMarkovCotype.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic

/-! # The Hilbert finite-chain Markov type inequality

The argument uses the Dirichlet form of a reversible transition operator.
Zero stationary masses are allowed: the weighted form need not be definite.
-/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace Papers.OaiMetricMarkovCotype

-- @node: symmetric_contraction_power_bound
/-- Suppose [a real bilinear form is symmetric](hyp:hsym), [a linear operator is self-adjoint
for that form](hyp:hself), and [the quadratic form minus its one-step pairing](hyp:hminus)
and [the quadratic form plus its one-step pairing](hyp:hplus) are nonnegative on every vector.
Then [the loss in pairing after any number of iterations is at most that number times the
one-step loss](goal). -/
lemma symmetric_contraction_power_bound {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (T : V →ₗ[ℝ] V)
    (hsym : ∀ x y, B x y = B y x)
    (hself : ∀ x y, B (T x) y = B x (T y))
    (hminus : ∀ x, 0 ≤ B x x - B x (T x))
    (hplus : ∀ x, 0 ≤ B x x + B x (T x))
    (u : V) (t : ℕ) :
    B u u - B u ((T ^ t) u) ≤ (t : ℝ) * (B u u - B u (T u)) := by
  let e : V → ℝ := fun x => B x x - B x (T x)
  let c : V → V → ℝ := fun x y => B x y - B x (T y)
  have hc_sym (x y : V) : c x y = c y x := by
    dsimp [c]
    rw [← hself, hsym x y, hsym (T x) y]
  have he_contract (x : V) : e (T x) ≤ e x := by
    have h := hplus (x - T x)
    simp only [map_sub, LinearMap.sub_apply] at h
    rw [hsym (T x) x, ← hself x (T x)] at h
    dsimp [e]
    linarith
  have he_pow (k : ℕ) : e ((T ^ k) u) ≤ e u := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact (he_contract _).trans ih
  have hc_le (x y : V) : 2 * c x y ≤ e x + e y := by
    have h := hminus (x - y)
    simp only [map_sub, LinearMap.sub_apply] at h
    have hxy := hc_sym x y
    dsimp [e, c] at *
    linarith
  have hc_pow (k : ℕ) : c u ((T ^ k) u) ≤ e u := by
    have h := hc_le u ((T ^ k) u)
    have h' := he_pow k
    linarith
  induction t with
  | zero => simp
  | succ t ih =>
    have h := hc_pow t
    rw [pow_succ', Module.End.mul_apply]
    simp only [Nat.cast_add, Nat.cast_one]
    dsimp [c, e] at h
    nlinarith

variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] {n : ℕ}

-- @node: weightedHilbertForm
/-- For [real weights on the finite state set](hyp:π), [the weighted Hilbert bilinear form](goal)
is the sum, over states, of the weight times the inner product of the two vector values. -/
def weightedHilbertForm (π : Fin n → ℝ) :
    (Fin n → 𝓗) →ₗ[ℝ] (Fin n → 𝓗) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun u v => ∑ i, π i * inner ℝ (u i) (v i))
    (by intros; simp [inner_add_left, mul_add, Finset.sum_add_distrib])
    (by intros; simp [real_inner_smul_left, Finset.mul_sum, mul_left_comm])
    (by intros; simp [inner_add_right, mul_add, Finset.sum_add_distrib])
    (by intros; simp [inner_smul_right, Finset.mul_sum, mul_left_comm])

-- @node: finiteHilbertTransition
/-- For [a real matrix on the finite state set](hyp:A), [the Hilbert-valued transition operator](goal)
assigns to each state the sum of vector values weighted by the corresponding matrix row. -/
def finiteHilbertTransition (A : Matrix (Fin n) (Fin n) ℝ) :
    (Fin n → 𝓗) →ₗ[ℝ] (Fin n → 𝓗) where
  toFun u i := ∑ j, A i j • u j
  map_add' u v := by ext i; simp [smul_add, Finset.sum_add_distrib]
  map_smul' c u := by ext i; simp [Finset.smul_sum, smul_smul, mul_comm]

-- @node: reversible_weighted_columns
/-- If [a matrix is stochastic](hyp:hA) and [satisfies detailed balance with the state weights](hyp:hrev),
then [each weighted column sum equals the weight of that column's state](goal). -/
lemma reversible_weighted_columns (π : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : IsStochastic A) (hrev : IsReversible A π) (j : Fin n) :
    ∑ i, π i * A i j = π j := by
  calc ∑ i, π i * A i j = ∑ i, π j * A j i :=
         Finset.sum_congr rfl (fun i _ => hrev.detailed_balance i j)
       _ = π j := by rw [← Finset.mul_sum, hA.row_sums, mul_one]

-- @node: weightedHilbertForm_symmetric
/-- [Interchanging the two Hilbert-valued state functions leaves their weighted inner product
unchanged](goal). -/
lemma weightedHilbertForm_symmetric (π : Fin n → ℝ) (u v : Fin n → 𝓗) :
    weightedHilbertForm π u v = weightedHilbertForm π v u := by
  simp only [weightedHilbertForm, LinearMap.mk₂_apply, real_inner_comm (u _) (v _)]

-- @node: finiteHilbertTransition_symmetric
/-- If [the transition matrix satisfies detailed balance with the weights](hyp:hrev), then
[applying the transition operator to either argument gives the same weighted inner product](goal). -/
lemma finiteHilbertTransition_symmetric (π : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (hrev : IsReversible A π) (u v : Fin n → 𝓗) :
    weightedHilbertForm π (finiteHilbertTransition A u) v =
      weightedHilbertForm π u (finiteHilbertTransition A v) := by
  simp only [weightedHilbertForm, LinearMap.mk₂_apply, finiteHilbertTransition,
    LinearMap.coe_mk, AddHom.coe_mk, sum_inner, inner_sum,
    real_inner_smul_left, inner_smul_right, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← mul_assoc, hrev.detailed_balance, mul_assoc]

-- @node: weighted_pair_left
/-- If [every matrix row sums to one](hyp:hrow), then [the weighted sum over state pairs of
a function of the first state equals its weighted sum over single states](goal). -/
lemma weighted_pair_left (π : Fin n → ℝ) (P : Matrix (Fin n) (Fin n) ℝ)
    (hrow : ∀ i, ∑ j, P i j = 1) (f : Fin n → ℝ) :
    ∑ i, ∑ j, π i * P i j * f i = ∑ i, π i * f i := by
  apply Finset.sum_congr rfl
  intro i _
  calc ∑ j, π i * P i j * f i = π i * (∑ j, P i j) * f i := by
         simp only [Finset.sum_mul, Finset.mul_sum]
       _ = π i * f i := by rw [hrow, mul_one]

-- @node: weighted_pair_right
/-- If [the weights are preserved by the matrix's weighted column sums](hyp:hcol), then
[the weighted sum over state pairs of a function of the second state equals its weighted
sum over single states](goal). -/
lemma weighted_pair_right (π : Fin n → ℝ) (P : Matrix (Fin n) (Fin n) ℝ)
    (hcol : ∀ j, ∑ i, π i * P i j = π j) (f : Fin n → ℝ) :
    ∑ i, ∑ j, π i * P i j * f j = ∑ j, π j * f j := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_mul, hcol]

-- @node: weightedHilbert_pair_identity
/-- If [every matrix row sums to one](hyp:hrow) and [the weighted column sums preserve the
state weights](hyp:hcol), then [the weighted pair sum of the two squared vector norms plus
a scalar multiple of their inner product equals twice the weighted squared norm plus that
scalar times the pairing with the transitioned vector](goal). -/
lemma weightedHilbert_pair_identity (π : Fin n → ℝ) (P : Matrix (Fin n) (Fin n) ℝ)
    (hrow : ∀ i, ∑ j, P i j = 1) (hcol : ∀ j, ∑ i, π i * P i j = π j)
    (u : Fin n → 𝓗) (c : ℝ) :
    (∑ i, ∑ j, π i * P i j *
      (‖u i‖ ^ 2 + c * inner ℝ (u i) (u j) + ‖u j‖ ^ 2)) =
      2 * weightedHilbertForm π u u +
        c * weightedHilbertForm π u (finiteHilbertTransition P u) := by
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [weighted_pair_left π P hrow, weighted_pair_right π P hcol]
  simp only [weightedHilbertForm, LinearMap.mk₂_apply, real_inner_self_eq_norm_sq,
    finiteHilbertTransition, LinearMap.coe_mk, AddHom.coe_mk,
    inner_sum, inner_smul_right, Finset.mul_sum]
  have hcross : (∑ i, ∑ j, π i * P i j * (c * inner ℝ (u i) (u j))) =
      c * ∑ i, ∑ j, π i * (P i j * inner ℝ (u i) (u j)) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hcross]
  simp only [← Finset.mul_sum]
  ring

-- @node: finiteHilbertTransition_form_bounds
/-- If [the state weights form a probability vector](hyp:hπ), [the matrix is stochastic](hyp:hA),
and [detailed balance holds](hyp:hrev), then [both the difference and the sum of a vector's
weighted squared norm and its pairing with its transitioned value are nonnegative](goal). -/
lemma finiteHilbertTransition_form_bounds (π : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (hπ : IsProbabilityVector π)
    (hA : IsStochastic A) (hrev : IsReversible A π) (u : Fin n → 𝓗) :
    0 ≤ weightedHilbertForm π u u - weightedHilbertForm π u (finiteHilbertTransition A u) ∧
    0 ≤ weightedHilbertForm π u u + weightedHilbertForm π u (finiteHilbertTransition A u) := by
  have hn (sign : ℝ) : 0 ≤ ∑ i, ∑ j, π i * A i j * ‖u i + sign • u j‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (mul_nonneg (hπ.1 i) (hA.nonneg i j)) (sq_nonneg _)
  have hm := hn (-1)
  have hp := hn 1
  simp only [neg_one_smul, ← sub_eq_add_neg, norm_sub_sq_real] at hm
  simp only [one_smul, norm_add_sq_real] at hp
  have hm' := weightedHilbert_pair_identity π A hA.row_sums
    (reversible_weighted_columns π A hA hrev) u (-2)
  have hp' := weightedHilbert_pair_identity π A hA.row_sums
    (reversible_weighted_columns π A hA hrev) u 2
  simp only [neg_mul, ← sub_eq_add_neg] at hm'
  constructor <;> linarith

-- @node: finiteHilbertTransition_mul
/-- [The transition operator associated with a matrix product equals the composition of the
two transition operators in the same order](goal). -/
lemma finiteHilbertTransition_mul (A P : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → 𝓗) :
    finiteHilbertTransition (A * P) u =
      finiteHilbertTransition A (finiteHilbertTransition P u) := by
  ext i
  simp only [finiteHilbertTransition, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]

-- @node: finiteHilbertTransition_pow
/-- [Applying the transition operator of a matrix power equals iterating the matrix's
transition operator that many times](goal). -/
lemma finiteHilbertTransition_pow (A : Matrix (Fin n) (Fin n) ℝ) (t : ℕ)
    (u : Fin n → 𝓗) :
    finiteHilbertTransition (A ^ t) u = (finiteHilbertTransition A ^ t) u := by
  induction t with
  | zero =>
    ext i
    simp [finiteHilbertTransition, Matrix.one_apply]
  | succ t ih =>
    rw [pow_succ', finiteHilbertTransition_mul, ih, pow_succ', Module.End.mul_apply]

-- @node: stochastic_power_rows
/-- If [a matrix is stochastic](hyp:hA), then [every row of each nonnegative integer power
of the matrix sums to one](goal). -/
lemma stochastic_power_rows (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsStochastic A)
    (t : ℕ) (i : Fin n) : ∑ j, (A ^ t) i j = 1 := by
  have h : A ∈ Matrix.rowStochastic ℝ (Fin n) :=
    Matrix.mem_rowStochastic_iff_sum.mpr ⟨hA.nonneg, hA.row_sums⟩
  exact Matrix.sum_row_of_mem_rowStochastic (pow_mem h t) i

-- @node: stationary_power_columns
/-- If [the weighted column sums of a matrix equal the original state weights](hyp:hcol),
then [the weighted column sums of every nonnegative integer power equal those same weights](goal). -/
lemma stationary_power_columns (π : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hcol : ∀ j, ∑ i, π i * A i j = π j) (t : ℕ) (j : Fin n) :
    ∑ i, π i * (A ^ t) i j = π j := by
  induction t generalizing j with
  | zero => simp [Matrix.one_apply]
  | succ t ih =>
    simp only [pow_succ, Matrix.mul_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [← mul_assoc, ← Finset.sum_mul]
    simp_rw [ih]
    exact hcol j

-- @node: weightedHilbert_distance_identity
/-- If [every matrix row sums to one](hyp:hrow) and [weighted column sums preserve the
state weights](hyp:hcol), then [the weighted pair sum of squared Hilbert distances equals
twice the weighted squared norm minus twice the pairing with the transitioned vector](goal). -/
lemma weightedHilbert_distance_identity (π : Fin n → ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ)
    (hrow : ∀ i, ∑ j, P i j = 1) (hcol : ∀ j, ∑ i, π i * P i j = π j)
    (u : Fin n → 𝓗) :
    (∑ i, ∑ j, π i * P i j * dist (u i) (u j) ^ 2) =
      2 * weightedHilbertForm π u u -
        2 * weightedHilbertForm π u (finiteHilbertTransition P u) := by
  simpa only [dist_eq_norm, norm_sub_sq_real, neg_mul, ← sub_eq_add_neg] using
    weightedHilbert_pair_identity π P hrow hcol u (-2)

-- @node: hilbert_finite_chain_markov_type_bound
/-- For [probability weights on the states](hyp:hπ) and [a stochastic transition matrix](hyp:hA)
[satisfying detailed balance with those weights](hyp:hrev), [the expected squared Hilbert
distance after any number of steps is at most that number times the expected one-step
squared distance](goal). -/
lemma hilbert_finite_chain_markov_type_bound (π : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (hπ : IsProbabilityVector π)
    (hA : IsStochastic A) (hrev : IsReversible A π) (u : Fin n → 𝓗) (t : ℕ) :
    (∑ i, ∑ j, π i * (A ^ t) i j * dist (u i) (u j) ^ 2) ≤
      (t : ℝ) * ∑ i, ∑ j, π i * A i j * dist (u i) (u j) ^ 2 := by
  have h := symmetric_contraction_power_bound
    (weightedHilbertForm π) (finiteHilbertTransition A)
    (weightedHilbertForm_symmetric π)
    (finiteHilbertTransition_symmetric π A hrev)
    (fun v => (finiteHilbertTransition_form_bounds π A hπ hA hrev v).1)
    (fun v => (finiteHilbertTransition_form_bounds π A hπ hA hrev v).2) u t
  rw [← finiteHilbertTransition_pow] at h
  rw [weightedHilbert_distance_identity π (A ^ t) (stochastic_power_rows A hA t)
      (stationary_power_columns π A (reversible_weighted_columns π A hA hrev) t),
    weightedHilbert_distance_identity π A hA.row_sums
      (reversible_weighted_columns π A hA hrev)]
  nlinarith

end Papers.OaiMetricMarkovCotype

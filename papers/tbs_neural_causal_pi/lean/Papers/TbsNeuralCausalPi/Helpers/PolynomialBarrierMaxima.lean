module
public import Papers.TbsNeuralCausalPi.Helpers.PolynomialQuotientRoots
/-! # Counting signs using perturbed barrier maxima

A small even-power penalty preserves a positive interior maximum in every
realized sign cell. Its gradient has pure-power leading terms, so the
coordinate-algebra root bound applies directly to these maxima. No persistence
of roots of the unperturbed critical equations is required.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open Filter
open scoped Topology
noncomputable section

-- @node: polynomialEvenPenalty
/-- For [a nonnegative integer k](hyp:k), the [even-power penalty
polynomial](goal) is the sum of the coordinates raised to the power 2k. -/
def polynomialEvenPenalty {V : Type*} [Fintype V] (k : ℕ) : MvPolynomial V ℝ :=
  ∑ i, MvPolynomial.X i ^ (2 * k)

-- @node: polynomialEvenPenalty_eval
/-- [The even-power penalty evaluated at a coordinate vector equals the sum
of its coordinates raised to the power 2k](goal). -/
lemma polynomialEvenPenalty_eval {V : Type*} [Fintype V] (k : ℕ) (a : V → ℝ) :
    MvPolynomial.eval a (polynomialEvenPenalty k) = ∑ i, a i ^ (2 * k) := by
  simp [polynomialEvenPenalty, map_sum]

-- @node: polynomialEvenPenalty_nonneg
/-- [The even-power penalty is nonnegative at every real coordinate
vector](goal). -/
lemma polynomialEvenPenalty_nonneg {V : Type*} [Fintype V] (k : ℕ) (a : V → ℝ) :
    0 ≤ MvPolynomial.eval a (polynomialEvenPenalty k) := by
  rw [polynomialEvenPenalty_eval]
  exact Finset.sum_nonneg (fun i _ => by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _)

-- @node: polynomialCompactBarrier_positive_box
/-- If [the compact barrier with threshold R is strictly positive at a
point](hyp:ha), [every coordinate of the point lies between −(|R| + 1) and
|R| + 1, and every polynomial in the family is nonzero there](goal). -/
lemma polynomialCompactBarrier_positive_box {I V : Type*} [Fintype I] [Fintype V]
    (p : I → MvPolynomial V ℝ) (R : ℝ) {a : V → ℝ}
    (ha : 0 < MvPolynomial.eval a (polynomialCompactBarrier p R)) :
    a ∈ Set.Icc (fun _ => -(|R| + 1)) (fun _ => |R| + 1) ∧
      a ∈ polynomialNonzeroDomain p := by
  have h := polynomialCompactSuperlevel_properties p R ha (show a ∈ polynomialCompactSuperlevel p R
    (MvPolynomial.eval a (polynomialCompactBarrier p R)) from by
      simp only [polynomialCompactSuperlevel, Set.mem_setOf_eq]; exact le_refl _)
  refine ⟨⟨?_, ?_⟩, h.1⟩ <;> intro v
  all_goals
    have hv : a v ^ 2 < R :=
      (Finset.single_le_sum (fun w _ => sq_nonneg (a w)) (Finset.mem_univ v)).trans_lt h.2
    have hR := le_abs_self R
    have habs := abs_nonneg R
    nlinarith [sq_nonneg (a v + 1), sq_nonneg (a v - 1)]

-- @node: polynomial_barrier_penalty_preserves_signs
/-- [There exist a ball threshold and a strictly positive penalty coefficient
such that every strict sign pattern realized on the common nonzero domain
has a representative where the compact barrier minus that coefficient
times the even-power penalty is strictly positive](goal). -/
lemma polynomial_barrier_penalty_preserves_signs {I V : Type*}
    [Fintype I] [Fintype V] (p : I → MvPolynomial V ℝ) (k : ℕ) :
    ∃ R δ : ℝ, 0 < δ ∧ ∀ σ ∈ strictPolynomialSignPattern p '' polynomialNonzeroDomain p,
      ∃ a : V → ℝ, strictPolynomialSignPattern p a = σ ∧
        0 < MvPolynomial.eval a (polynomialCompactBarrier p R -
          MvPolynomial.C δ * polynomialEvenPenalty k) := by
  classical
  obtain ⟨R, ε, _, hε, hsigns⟩ := polynomialCompactSuperlevel_carries_signs p
  let patterns := strictPolynomialSignPattern p '' polynomialNonzeroDomain p
  have hw (σ : patterns) : ∃ a ∈ polynomialCompactSuperlevel p R ε,
      strictPolynomialSignPattern p a = σ.val := by
    change σ.val ∈ strictPolynomialSignPattern p '' polynomialCompactSuperlevel p R ε
    rw [hsigns]
    exact σ.property
  choose a ha hs using hw
  let value (σ : patterns) := MvPolynomial.eval (a σ) (polynomialCompactBarrier p R) /
    (MvPolynomial.eval (a σ) (polynomialEvenPenalty k) + 1)
  have hv (σ : patterns) : 0 < value σ :=
    div_pos (hε.trans_le (ha σ)) (by linarith [polynomialEvenPenalty_nonneg k (a σ)])
  obtain ⟨δ, hδ, hb⟩ := finite_sign_margin Finset.univ value
  refine ⟨R, δ, hδ, ?_⟩
  intro σ hσ
  let w : patterns := ⟨σ, hσ⟩
  refine ⟨a w, hs w, ?_⟩
  have h := hb w (Finset.mem_univ w) (hv w).ne'
  rw [abs_of_pos (hv w)] at h
  have hm := (lt_div_iff₀ (show 0 <
    MvPolynomial.eval (a w) (polynomialEvenPenalty k) + 1 by
      linarith [polynomialEvenPenalty_nonneg k (a w)])).mp h
  simp only [map_sub, map_mul, MvPolynomial.eval_C]
  nlinarith

-- @node: polynomial_penalized_sign_cell_localMax
/-- If [the penalty coefficient is strictly positive](hyp:hδ) and [the
compact barrier minus the scaled even-power penalty is strictly positive
at a point a](hyp:ha), [there exists a point where all the polynomials are
nonzero, with the same strict sign pattern as a, at which the penalized
barrier has a local maximum](goal). -/
lemma polynomial_penalized_sign_cell_localMax {I V : Type*}
    [Fintype I] [Fintype V] (p : I → MvPolynomial V ℝ) (R : ℝ) (k : ℕ)
    {δ : ℝ} (hδ : 0 < δ) {a : V → ℝ}
    (ha : 0 < MvPolynomial.eval a (polynomialCompactBarrier p R -
      MvPolynomial.C δ * polynomialEvenPenalty k)) :
    ∃ y : V → ℝ, y ∈ polynomialNonzeroDomain p ∧
      strictPolynomialSignPattern p y = strictPolynomialSignPattern p a ∧
      IsLocalMax (fun x => MvPolynomial.eval x (polynomialCompactBarrier p R -
        MvPolynomial.C δ * polynomialEvenPenalty k)) y := by
  let Q := polynomialCompactBarrier p R - MvPolynomial.C δ * polynomialEvenPenalty k
  have hle (x : V → ℝ) : MvPolynomial.eval x Q ≤
      MvPolynomial.eval x (polynomialCompactBarrier p R) := by
    dsimp [Q]
    simp only [map_sub, map_mul, MvPolynomial.eval_C]
    exact sub_le_self _ (mul_nonneg hδ.le (polynomialEvenPenalty_nonneg k x))
  have hac := polynomialCompactBarrier_positive_box p R (ha.trans_le (hle a))
  let σ := strictPolynomialSignPattern p a
  let s := Set.Icc (fun _ : V => -(|R| + 1)) (fun _ => |R| + 1)
  have has : a ∈ s ∩ polynomialClosedSignCell p σ :=
    ⟨hac.1, (polynomialClosedSignCell_iff p σ hac.2).mpr rfl⟩
  obtain ⟨y, hy, hmax⟩ :=
    (isCompact_Icc.inter_right (polynomialClosedSignCell_isClosed p σ)).exists_isMaxOn
      ⟨a, has⟩ (MvPolynomial.continuous_eval Q).continuousOn
  have hyp : 0 < MvPolynomial.eval y Q := ha.trans_le (hmax has)
  have hyc := polynomialCompactBarrier_positive_box p R (hyp.trans_le (hle y))
  have hsign := (polynomialClosedSignCell_iff p σ hyc.2).mp hy.2
  refine ⟨y, hyc.2, hsign, ?_⟩
  have he : ∀ᶠ x in 𝓝 y, strictPolynomialSignPattern p x = σ :=
    (strictPolynomialSignPattern_eventually_eq p hyc.2).mono (fun x hx => hx.trans hsign)
  have hp : ∀ᶠ x in 𝓝 y, 0 < MvPolynomial.eval x Q :=
    (isOpen_lt continuous_const (MvPolynomial.continuous_eval Q)).mem_nhds hyp
  filter_upwards [he, hp] with x hx hxpos
  have hxc := polynomialCompactBarrier_positive_box p R (hxpos.trans_le (hle x))
  exact hmax ⟨hxc.1, (polynomialClosedSignCell_iff p σ hxc.2).mpr hx⟩


-- @node: polynomialEvenPenalty_pderiv
/-- [The partial derivative of the even-power penalty with respect to a
coordinate is the monomial with coefficient 2k and exponent 2k − 1 in
that coordinate](goal).

The exponent uses subtraction truncated at zero, so the formula also
applies when k is zero. -/
lemma polynomialEvenPenalty_pderiv {V : Type*} [Fintype V] (k : ℕ) (i : V) :
    MvPolynomial.pderiv i (polynomialEvenPenalty k) =
      MvPolynomial.monomial (Finsupp.single i (2 * k - 1)) (2 * k : ℝ) := by
  classical
  rw [polynomialEvenPenalty, map_sum, Finset.sum_eq_single i]
  · simp [MvPolynomial.pderiv_pow, MvPolynomial.X_pow_eq_monomial,
      MvPolynomial.C_mul_monomial]
  · intro j _ hji
    simp [MvPolynomial.pderiv_pow, MvPolynomial.pderiv_X_of_ne hji]
  · simp

-- @node: polynomial_localMax_gradient_zero
/-- If [a real polynomial has a local maximum at a point](hyp:ha), [each
of its partial derivatives evaluates to zero at that point](goal). -/
lemma polynomial_localMax_gradient_zero {V : Type*} [Fintype V]
    (Q : MvPolynomial V ℝ) {a : V → ℝ}
    (ha : IsLocalMax (fun x => MvPolynomial.eval x Q) a) (i : V) :
    MvPolynomial.eval a (MvPolynomial.pderiv i Q) = 0 := by
  classical
  have h := ha.hasFDerivAt_eq_zero (polynomial_eval_hasStrictFDerivAt Q a).hasFDerivAt
  have hi := congrArg (fun f : (V → ℝ) →L[ℝ] ℝ => f (Pi.single i 1)) h
  simpa [polynomialGradientMap_single] using hi

-- @node: polynomial_penalized_gradient_equation
/-- [The partial derivative of a polynomial minus δ times the even-power
penalty equals the original partial derivative plus the monomial with
coefficient −δ times 2k and exponent 2k − 1 in the chosen coordinate](goal).

The exponent uses subtraction truncated at zero. -/
lemma polynomial_penalized_gradient_equation {V : Type*} [Fintype V]
    (Q : MvPolynomial V ℝ) (k : ℕ) (δ : ℝ) (i : V) :
    MvPolynomial.pderiv i (Q - MvPolynomial.C δ * polynomialEvenPenalty k) =
      MvPolynomial.monomial (Finsupp.single i (2 * k - 1)) (-δ * (2 * k : ℝ)) +
        MvPolynomial.pderiv i Q := by
  rw [map_sub, MvPolynomial.pderiv_C_mul, polynomialEvenPenalty_pderiv,
    MvPolynomial.C_mul_monomial]
  rw [sub_eq_add_neg, add_comm]
  congr 1
  rw [← map_neg]
  congr 1
  ring

-- @node: strictPolynomialSignPattern_encard_le_degree_power
/-- If [each of m polynomials in v variables has total degree at most d](hyp:hd),
[the number of strict sign patterns realized where all the polynomials are
nonzero is at most (4md + 5) to the power v](goal). -/
lemma strictPolynomialSignPattern_encard_le_degree_power {I V : Type*}
    [Fintype I] [Fintype V]
    (p : I → MvPolynomial V ℝ) (d : ℕ) (hd : ∀ i, (p i).totalDegree ≤ d) :
    (strictPolynomialSignPattern p '' polynomialNonzeroDomain p).encard ≤
      ((4 * Fintype.card I * d + 5) ^ Fintype.card V : ℕ) := by
  classical
  letI : LinearOrder V := LinearOrder.lift' (Fintype.equivFin V) (Fintype.equivFin V).injective
  let k := 2 * Fintype.card I * d + 3
  obtain ⟨R, δ, hδ, hw⟩ := polynomial_barrier_penalty_preserves_signs p k
  let Q := polynomialCompactBarrier p R
  let equations := fun i : V =>
    MvPolynomial.monomial (Finsupp.single i (2 * k - 1)) (-δ * (2 * k : ℝ)) +
      MvPolynomial.pderiv i Q
  have hcover : strictPolynomialSignPattern p '' polynomialNonzeroDomain p ⊆
      strictPolynomialSignPattern p '' {a | ∀ i, MvPolynomial.eval a (equations i) = 0} := by
    intro σ hσ
    obtain ⟨a, ha, hap⟩ := hw σ hσ
    obtain ⟨y, _, hsign, hmax⟩ := polynomial_penalized_sign_cell_localMax p R k hδ hap
    refine ⟨y, ?_, hsign.trans ha⟩
    intro i
    dsimp [equations]
    rw [← polynomial_penalized_gradient_equation]
    exact polynomial_localMax_gradient_zero _ hmax i
  have hdeg (i : V) : (MvPolynomial.pderiv i Q).totalDegree < 2 * k - 1 := by
    have hder : (MvPolynomial.pderiv i Q).totalDegree ≤ Q.totalDegree := by
      by_cases hz : MvPolynomial.pderiv i Q = 0
      · simp [hz]
      · exact (Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension.totalDegree_pderiv_lt hz).le
    have hQ := polynomialCompactBarrier_degree p R d hd
    dsimp [Q] at hder ⊢
    dsimp [k]
    omega
  have hδk (i : V) : -δ * (2 * k : ℝ) ≠ 0 := by
    apply mul_ne_zero (neg_ne_zero.mpr hδ.ne')
    have hk : 0 < k := by dsimp [k]; omega
    positivity
  have hcount := polynomial_perturbed_system_roots_encard_le
    (fun i => MvPolynomial.pderiv i Q) (fun _ => 2 * k - 1)
    (fun _ => -δ * (2 * k : ℝ)) hδk hdeg
  have hfinal := (Set.encard_mono hcover).trans ((Set.encard_image_le _ _).trans hcount)
  have hbase : 2 * k - 1 = 4 * Fintype.card I * d + 5 := by
    have : 2 * k = 4 * Fintype.card I * d + 6 := by dsimp [k]; ring
    omega
  simpa only [hbase, Finset.prod_const, Finset.card_univ] using hfinal


-- @node: polynomialComparisonPattern_encard_le_degree_power
/-- If [each of m polynomials in v variables has total degree at most d](hyp:hd),
[the number of realized polynomial comparison patterns is at most
(8m max(d, 1) + 5) to the power v + 1](goal). -/
lemma polynomialComparisonPattern_encard_le_degree_power {I V : Type*}
    [Fintype I] [Fintype V] (p : I → MvPolynomial V ℝ) (d : ℕ)
    (hd : ∀ i, (p i).totalDegree ≤ d) :
    (Set.range (polynomialComparisonPattern p)).encard ≤
      ((8 * Fintype.card I * max d 1 + 5) ^ (Fintype.card V + 1) : ℕ) := by
  let shifted : I × Bool → MvPolynomial (Option V) ℝ :=
    fun ib => signShiftPolynomial (p ib.1) ib.2
  have h := strictPolynomialSignPattern_encard_le_degree_power shifted (max d 1)
    (fun ib => (signShiftPolynomial_degree _ _).trans (max_le_max (hd ib.1) le_rfl))
  have hcount := (polynomialComparisonPattern_encard_le_nonzero p).trans h
  simpa only [Fintype.card_prod, Fintype.card_bool, Fintype.card_option,
    show 4 * (Fintype.card I * 2) = 8 * Fintype.card I by ring] using hcount

end
end Papers.TbsNeuralCausalPi

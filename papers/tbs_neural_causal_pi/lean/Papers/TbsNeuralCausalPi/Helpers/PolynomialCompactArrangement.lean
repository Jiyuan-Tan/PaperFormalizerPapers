module
public import Papers.TbsNeuralCausalPi.Helpers.PolynomialSignComponents
public import Mathlib.Topology.Order.Compact
/-! # Compact algebraic domains carrying every strict polynomial sign

A squared arrangement product times a quadratic ball barrier gives a compact
positive superlevel set. A single choice of radius and positive level retains
all realized strict signs. Thus the component-count problem can be localized
to a compact algebraic domain without adding variables or lifting monomials.
No multivariate degree-dependent component estimate is assumed here.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
noncomputable section

-- @node: polynomialBallBarrier
/-- For [a real threshold R](hyp:R), the [ball barrier polynomial](goal)
is R minus the sum of the squared coordinates. -/
def polynomialBallBarrier {V : Type*} [Fintype V] (R : ℝ) : MvPolynomial V ℝ :=
  MvPolynomial.C R - ∑ v, MvPolynomial.X v ^ 2

-- @node: polynomialBallBarrier_eval
/-- [The ball barrier evaluated at a coordinate vector equals its threshold
minus the sum of that vector's squared coordinates](goal). -/
lemma polynomialBallBarrier_eval {V : Type*} [Fintype V] (R : ℝ) (a : V → ℝ) :
    MvPolynomial.eval a (polynomialBallBarrier R) = R - ∑ v, a v ^ 2 := by
  simp [polynomialBallBarrier, map_sum]

-- @node: polynomialBallBarrier_degree
/-- [The ball barrier polynomial has total degree at most two](goal). -/
lemma polynomialBallBarrier_degree {V : Type*} [Fintype V] (R : ℝ) :
    (polynomialBallBarrier (V := V) R).totalDegree ≤ 2 := by
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le
  · simp
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro v _
    exact (MvPolynomial.totalDegree_pow _ 2).trans (by simp)

-- @node: polynomialCompactBarrier
/-- For [a finite family of real polynomials](hyp:p) and [a real ball
threshold R](hyp:R), the [compact barrier polynomial](goal) is the square
of their product multiplied by the ball barrier with threshold R. -/
def polynomialCompactBarrier {I V : Type*} [Fintype I] [Fintype V]
    (p : I → MvPolynomial V ℝ) (R : ℝ) : MvPolynomial V ℝ :=
  (∏ i, p i) ^ 2 * polynomialBallBarrier R

-- @node: polynomialCompactBarrier_eval
/-- [Evaluating the compact barrier gives the squared product of the
individual polynomial values multiplied by the ball threshold minus the
sum of squared coordinates](goal). -/
lemma polynomialCompactBarrier_eval {I V : Type*} [Fintype I] [Fintype V]
    (p : I → MvPolynomial V ℝ) (R : ℝ) (a : V → ℝ) :
    MvPolynomial.eval a (polynomialCompactBarrier p R) =
      (∏ i, MvPolynomial.eval a (p i)) ^ 2 * (R - ∑ v, a v ^ 2) := by
  simp [polynomialCompactBarrier, polynomialBallBarrier_eval, map_prod]

-- @node: polynomialCompactBarrier_degree
/-- If [every polynomial in a family of size m has total degree at most d](hyp:hd),
[its compact barrier has total degree at most 2md + 2](goal). -/
lemma polynomialCompactBarrier_degree {I V : Type*} [Fintype I] [Fintype V]
    (p : I → MvPolynomial V ℝ) (R : ℝ) (d : ℕ)
    (hd : ∀ i, (p i).totalDegree ≤ d) :
    (polynomialCompactBarrier p R).totalDegree ≤ 2 * Fintype.card I * d + 2 := by
  apply (MvPolynomial.totalDegree_mul _ _).trans
  exact (Nat.add_le_add
    ((MvPolynomial.totalDegree_pow _ 2).trans
      (Nat.mul_le_mul_left 2 (polynomialArrangementProduct_degree p d hd)))
    (polynomialBallBarrier_degree R)).trans_eq (by ring)

-- @node: polynomialCompactSuperlevel
/-- For [a finite family of real polynomials](hyp:p), [a ball threshold R](hyp:R),
and [a real level ε](hyp:ε), the [compact barrier superlevel set](goal)
consists of coordinate vectors at which the compact barrier is at least ε. -/
def polynomialCompactSuperlevel {I V : Type*} [Fintype I] [Fintype V]
    (p : I → MvPolynomial V ℝ) (R ε : ℝ) : Set (V → ℝ) :=
  {a | ε ≤ MvPolynomial.eval a (polynomialCompactBarrier p R)}

-- @node: polynomialCompactSuperlevel_properties
/-- If [the barrier level is strictly positive](hyp:hε) and [a point belongs
to the corresponding compact barrier superlevel set](hyp:ha), [every
polynomial is nonzero at that point and the sum of its squared coordinates
is strictly below the ball threshold](goal). -/
lemma polynomialCompactSuperlevel_properties {I V : Type*} [Fintype I] [Fintype V]
    (p : I → MvPolynomial V ℝ) (R : ℝ) {ε : ℝ} (hε : 0 < ε)
    {a : V → ℝ} (ha : a ∈ polynomialCompactSuperlevel p R ε) :
    a ∈ polynomialNonzeroDomain p ∧ ∑ v, a v ^ 2 < R := by
  classical
  have hpos : 0 < (∏ i, MvPolynomial.eval a (p i)) ^ 2 * (R - ∑ v, a v ^ 2) := by
    rw [← polynomialCompactBarrier_eval]
    exact hε.trans_le ha
  have hp : (∏ i, MvPolynomial.eval a (p i)) ≠ 0 := by
    intro hz
    simp [hz] at hpos
  constructor
  · exact Finset.prod_ne_zero_iff.mp hp |> fun h i => h i (Finset.mem_univ i)
  · have hball := (mul_pos_iff_of_pos_left (sq_pos_of_ne_zero hp)).mp hpos
    linarith

-- @node: polynomialCompactSuperlevel_isCompact
/-- If [the barrier level is strictly positive](hyp:hε), [the compact
barrier superlevel set is compact](goal). -/
lemma polynomialCompactSuperlevel_isCompact {I V : Type*} [Fintype I] [Fintype V]
    (p : I → MvPolynomial V ℝ) (R : ℝ) {ε : ℝ} (hε : 0 < ε) :
    IsCompact (polynomialCompactSuperlevel p R ε) := by
  have hclosed : IsClosed (polynomialCompactSuperlevel p R ε) :=
    isClosed_le continuous_const (MvPolynomial.continuous_eval _)
  apply (isCompact_Icc (a := fun _ : V => -(|R| + 1))
    (b := fun _ : V => |R| + 1)).of_isClosed_subset hclosed
  intro a ha
  have hsum := (polynomialCompactSuperlevel_properties p R hε ha).2
  have hcoord (v : V) : a v ^ 2 < R :=
    (Finset.single_le_sum (fun w _ => sq_nonneg (a w)) (Finset.mem_univ v)).trans_lt hsum
  constructor <;> intro v <;>
    have hv := hcoord v <;>
    have hR := le_abs_self R <;>
    have habs := abs_nonneg R <;>
    nlinarith [sq_nonneg (a v + 1), sq_nonneg (a v - 1)]

-- @node: polynomialCompactSuperlevel_carries_signs
/-- [There exist a positive ball threshold and a positive barrier level such
that the compact barrier superlevel set realizes exactly the strict sign
patterns realized where all the polynomials are nonzero](goal).

Zero polynomials and an empty set of realized signs are allowed. -/
lemma polynomialCompactSuperlevel_carries_signs {I V : Type*}
    [Fintype I] [Fintype V] (p : I → MvPolynomial V ℝ) :
    ∃ R ε : ℝ, 0 < R ∧ 0 < ε ∧
      strictPolynomialSignPattern p '' polynomialCompactSuperlevel p R ε =
        strictPolynomialSignPattern p '' polynomialNonzeroDomain p := by
  classical
  let patterns := strictPolynomialSignPattern p '' polynomialNonzeroDomain p
  have hw (v : patterns) : ∃ a, a ∈ polynomialNonzeroDomain p ∧
      strictPolynomialSignPattern p a = v.val := v.property
  choose a ha hpattern using hw
  let R : ℝ := 1 + ∑ v : patterns, ∑ j, a v j ^ 2
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have hnorm (v : patterns) : ∑ j, a v j ^ 2 < R := by
    have h : (∑ j, a v j ^ 2) ≤ ∑ w : patterns, ∑ j, a w j ^ 2 :=
      Finset.single_le_sum
      (fun w (_ : w ∈ (Finset.univ : Finset patterns)) =>
        Finset.sum_nonneg (fun j _ => sq_nonneg (a w j))) (Finset.mem_univ v)
    dsimp [R]
    linarith
  have hpositive (v : patterns) :
      0 < MvPolynomial.eval (a v) (polynomialCompactBarrier p R) := by
    rw [polynomialCompactBarrier_eval]
    apply mul_pos
    · apply sq_pos_of_ne_zero
      exact Finset.prod_ne_zero_iff.mpr (fun i _ => ha v i)
    · linarith [hnorm v]
  obtain ⟨ε, hε, hmargin⟩ := finite_sign_margin Finset.univ
    (fun v : patterns => MvPolynomial.eval (a v) (polynomialCompactBarrier p R))
  refine ⟨R, ε, hR, hε, Set.Subset.antisymm ?_ ?_⟩
  · exact Set.image_mono (fun x hx =>
      (polynomialCompactSuperlevel_properties p R hε hx).1)
  · intro v hv
    let w : patterns := ⟨v, hv⟩
    refine ⟨a w, ?_, hpattern w⟩
    have h := hmargin w (Finset.mem_univ w) (hpositive w).ne'
    rw [abs_of_pos (hpositive w)] at h
    exact h.le

-- @node: strictPolynomialSignPattern_eq_on_subset_component
/-- If [a set contains only points where all the polynomials are nonzero](hyp:hs),
[a point x belongs to that set](hyp:hx), and [a point y belongs to the connected
component of x within that set](hyp:hy), [the strict polynomial sign patterns
at x and y are equal](goal). -/
lemma strictPolynomialSignPattern_eq_on_subset_component {I V : Type*}
    (p : I → MvPolynomial V ℝ) {s : Set (V → ℝ)}
    (hs : s ⊆ polynomialNonzeroDomain p) {x y : V → ℝ}
    (hx : x ∈ s) (hy : y ∈ connectedComponentIn s x) :
    strictPolynomialSignPattern p x = strictPolynomialSignPattern p y := by
  funext i
  apply Bool.decide_congr
  exact sign_eq_on_preconnected_nonzero isPreconnected_connectedComponentIn
    (fun a => MvPolynomial.eval a (p i)) (MvPolynomial.continuous_eval (p i)).continuousOn
    (fun a ha => hs (connectedComponentIn_subset s x ha) i)
    (mem_connectedComponentIn hx) hy

-- @node: strictPolynomialSignPattern_encard_le_subset_components
/-- If [a set contains only points where all the polynomials are nonzero](hyp:hs),
[the number of strict sign patterns realized on that set is at most the
number of its connected components](goal). -/
lemma strictPolynomialSignPattern_encard_le_subset_components {I V : Type*}
    (p : I → MvPolynomial V ℝ) {s : Set (V → ℝ)}
    (hs : s ⊆ polynomialNonzeroDomain p) :
    (strictPolynomialSignPattern p '' s).encard ≤
      ((fun a => connectedComponentIn s a) '' s).encard := by
  classical
  let patterns := strictPolynomialSignPattern p '' s
  have hw (v : patterns) : ∃ a, a ∈ s ∧ strictPolynomialSignPattern p a = v.val :=
    v.property
  choose a ha hpattern using hw
  let component : patterns → Set (V → ℝ) := fun v => connectedComponentIn s (a v)
  have hinj : Function.Injective component := by
    intro v w h
    have hm : a w ∈ connectedComponentIn s (a v) := by
      rw [show connectedComponentIn s (a v) = connectedComponentIn s (a w) from h]
      exact mem_connectedComponentIn (ha w)
    apply Subtype.ext
    exact (hpattern v).symm.trans
      ((strictPolynomialSignPattern_eq_on_subset_component p hs (ha v) hm).trans (hpattern w))
  exact hinj.encard_range.trans (Set.encard_mono (by
    rintro _ ⟨v, rfl⟩
    exact ⟨a v, ha v, rfl⟩))

-- @node: strictPolynomialSignPattern_compact_component_reduction
/-- If [every polynomial in a family of size m has total degree at most d](hyp:hd),
[there exist a polynomial of total degree at most 2md + 2 and a positive level
whose superlevel set is compact and has at least as many connected components
as the family has strict sign patterns on its common nonzero domain](goal).

The superlevel set uses the original variables. -/
lemma strictPolynomialSignPattern_compact_component_reduction {I V : Type*}
    [Fintype I] [Finite V] (p : I → MvPolynomial V ℝ) (d : ℕ)
    (hd : ∀ i, (p i).totalDegree ≤ d) :
    ∃ (Q : MvPolynomial V ℝ) (ε : ℝ), 0 < ε ∧
      Q.totalDegree ≤ 2 * Fintype.card I * d + 2 ∧
      IsCompact {a | ε ≤ MvPolynomial.eval a Q} ∧
      (strictPolynomialSignPattern p '' polynomialNonzeroDomain p).encard ≤
        ((fun a => connectedComponentIn {b | ε ≤ MvPolynomial.eval b Q} a) ''
          {a | ε ≤ MvPolynomial.eval a Q}).encard := by
  let := Fintype.ofFinite V
  obtain ⟨R, ε, _, hε, hsigns⟩ := polynomialCompactSuperlevel_carries_signs p
  refine ⟨polynomialCompactBarrier p R, ε, hε,
    polynomialCompactBarrier_degree p R d hd,
    polynomialCompactSuperlevel_isCompact p R hε, ?_⟩
  rw [← hsigns]
  exact strictPolynomialSignPattern_encard_le_subset_components p
    (fun a ha => (polynomialCompactSuperlevel_properties p R hε ha).1)

end
end Papers.TbsNeuralCausalPi

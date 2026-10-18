module
public import Papers.TbsNeuralCausalPi.Helpers.PolynomialComponentMinima
public import Mathlib.Analysis.Calculus.LagrangeMultipliers
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Causalean.Mathlib.AlgebraicGeometry.Dimension.PolynomialMap.Jacobian
/-! # Critical witnesses for polynomial sign patterns

On a compact zero set avoiding the original polynomials, each sign cell
has a coordinate minimizer which is a local minimum on the whole zero set.
This supplies critical witnesses without assuming that components are open
or that the hypersurface is regular. Quantitative counting is separate.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open Filter
open scoped Topology
noncomputable section

-- @node: polynomialClosedSignCell
/-- For [a polynomial family](hyp:p) and [a Boolean sign assignment](hyp:σ),
the [closed sign cell](goal) is the set of points where every polynomial is
nonpositive when its assigned sign is true and nonnegative when it is false. -/
def polynomialClosedSignCell {I V : Type*} (p : I → MvPolynomial V ℝ)
    (σ : I → Bool) : Set (V → ℝ) :=
  {a | ∀ i, if σ i then MvPolynomial.eval a (p i) ≤ 0
    else 0 ≤ MvPolynomial.eval a (p i)}

-- @node: polynomialClosedSignCell_isClosed
/-- [The cell imposing nonpositive values for true signs and nonnegative
values for false signs on a polynomial family is closed](goal). -/
lemma polynomialClosedSignCell_isClosed {I V : Type*}
    (p : I → MvPolynomial V ℝ) (σ : I → Bool) :
    IsClosed (polynomialClosedSignCell p σ) := by
  unfold polynomialClosedSignCell
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro i
  cases σ i
  · exact isClosed_le continuous_const (MvPolynomial.continuous_eval _)
  · exact isClosed_le (MvPolynomial.continuous_eval _) continuous_const

-- @node: polynomialClosedSignCell_iff
/-- If [all polynomials in the family are nonzero at a](hyp:ha), then
[a belongs to the closed cell for a sign assignment exactly when its strict
sign pattern equals that assignment](goal). -/
lemma polynomialClosedSignCell_iff {I V : Type*}
    (p : I → MvPolynomial V ℝ) (σ : I → Bool) {a : V → ℝ}
    (ha : a ∈ polynomialNonzeroDomain p) :
    a ∈ polynomialClosedSignCell p σ ↔ strictPolynomialSignPattern p a = σ := by
  constructor
  · intro h
    funext i
    have hi := h i
    cases hs : σ i
    · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hi
      simp [strictPolynomialSignPattern, hs, not_lt.mpr hi]
    · simp only [hs, ↓reduceIte] at hi
      simp [strictPolynomialSignPattern, hs, lt_of_le_of_ne hi (ha i)]
  · intro h i
    have hi := congrFun h i
    dsimp [strictPolynomialSignPattern] at hi
    cases hs : σ i
    · simp only [hs, decide_eq_false_iff_not] at hi
      simpa [hs] using le_of_not_gt hi
    · simp only [hs, decide_eq_true_eq] at hi
      simpa [hs] using hi.le

-- @node: strictPolynomialSignPattern_eventually_eq
/-- If [all polynomials of a finite family are nonzero at a](hyp:ha), then
[their strict sign pattern is constant on some neighborhood of a](goal). -/
lemma strictPolynomialSignPattern_eventually_eq {I V : Type*} [Finite I]
    (p : I → MvPolynomial V ℝ) {a : V → ℝ}
    (ha : a ∈ polynomialNonzeroDomain p) :
    ∀ᶠ x in 𝓝 a, strictPolynomialSignPattern p x = strictPolynomialSignPattern p a := by
  suffices h : ∀ᶠ x in 𝓝 a, ∀ i,
      strictPolynomialSignPattern p x i = strictPolynomialSignPattern p a i by
    exact h.mono (fun x hx => funext hx)
  apply (Filter.eventually_all).mpr
  intro i
  by_cases hi : MvPolynomial.eval a (p i) < 0
  · filter_upwards [(isOpen_lt (MvPolynomial.continuous_eval (p i)) continuous_const).mem_nhds hi]
      with x hx
    exact Bool.decide_congr ⟨fun _ => hi, fun _ => hx⟩
  · have hp : 0 < MvPolynomial.eval a (p i) :=
      lt_of_le_of_ne (le_of_not_gt hi) (ha i).symm
    filter_upwards [(isOpen_lt continuous_const (MvPolynomial.continuous_eval (p i))).mem_nhds hp]
      with x hx
    exact Bool.decide_congr ⟨fun h => False.elim ((not_lt_of_gt hx) h),
      fun h => False.elim (hi h)⟩

-- @node: polynomial_sign_cell_exists_localMin
/-- If [the zero set of Q is compact](hyp:hQ), [every original polynomial is
nonzero throughout that zero set](hyp:hn), and [a is a zero of Q](hyp:ha), then
[there is a zero of Q with the same strict sign pattern as a at which
coordinate v has a local minimum relative to the entire zero set](goal). -/
lemma polynomial_sign_cell_exists_localMin {I V : Type*} [Finite I]
    (p : I → MvPolynomial V ℝ) (Q : MvPolynomial V ℝ) (v : V)
    (hQ : IsCompact {a | MvPolynomial.eval a Q = 0})
    (hn : {a | MvPolynomial.eval a Q = 0} ⊆ polynomialNonzeroDomain p)
    {a : V → ℝ} (ha : MvPolynomial.eval a Q = 0) :
    ∃ y : V → ℝ, MvPolynomial.eval y Q = 0 ∧
      strictPolynomialSignPattern p y = strictPolynomialSignPattern p a ∧
      IsLocalMinOn (fun x => x v) {x | MvPolynomial.eval x Q = 0} y := by
  let σ := strictPolynomialSignPattern p a
  have hac : a ∈ polynomialClosedSignCell p σ :=
    (polynomialClosedSignCell_iff p σ (hn ha)).mpr rfl
  obtain ⟨y, hy, hmin⟩ :=
    (hQ.inter_right (polynomialClosedSignCell_isClosed p σ)).exists_isMinOn
      ⟨a, ha, hac⟩ (show ContinuousOn (fun x : V → ℝ => x v) _ by fun_prop)
  have hsign := (polynomialClosedSignCell_iff p σ (hn hy.1)).mp hy.2
  refine ⟨y, hy.1, hsign, ?_⟩
  have he : ∀ᶠ x in 𝓝 y, strictPolynomialSignPattern p x = σ :=
    (strictPolynomialSignPattern_eventually_eq p (hn hy.1)).mono
      (fun x hx => hx.trans hsign)
  filter_upwards [he.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hx hxQ
  exact hmin ⟨hxQ, (polynomialClosedSignCell_iff p σ (hn hxQ)).mpr hx⟩

-- @node: polynomialGradientMap
/-- For [a polynomial Q](hyp:Q) and [an evaluation point a](hyp:a), the
[gradient linear map](goal) sends a direction to the sum of its coordinates
weighted by the corresponding partial derivatives of Q evaluated at a. -/
def polynomialGradientMap {V : Type*} [Fintype V] (Q : MvPolynomial V ℝ)
    (a : V → ℝ) : (V → ℝ) →L[ℝ] ℝ :=
  ∑ i, MvPolynomial.eval a (MvPolynomial.pderiv i Q) •
    ContinuousLinearMap.proj i

-- @node: polynomialGradientMap_apply
/-- [The gradient linear map of Q at a, applied to a direction w, equals
the sum over coordinates of the partial derivative of Q at a times the
corresponding coordinate of w](goal). -/
lemma polynomialGradientMap_apply {V : Type*} [Fintype V] (Q : MvPolynomial V ℝ)
    (a w : V → ℝ) :
    polynomialGradientMap Q a w = ∑ i, MvPolynomial.eval a (MvPolynomial.pderiv i Q) * w i := by
  simp [polynomialGradientMap, ContinuousLinearMap.sum_apply]

-- @node: polynomial_eval_hasStrictFDerivAt
/-- [Evaluation of a polynomial Q has a strict total derivative at every
point a, given by the gradient linear map of Q at a](goal). -/
lemma polynomial_eval_hasStrictFDerivAt {V : Type*} [Fintype V]
    (Q : MvPolynomial V ℝ) (a : V → ℝ) :
    HasStrictFDerivAt (fun x => MvPolynomial.eval x Q) (polynomialGradientMap Q a) a := by
  classical
  induction Q using MvPolynomial.induction_on with
  | C c => simpa [polynomialGradientMap, MvPolynomial.pderiv_C] using
      (hasStrictFDerivAt_const c a)
  | add p q hp hq =>
      convert! hp.add hq using 1
      · funext x; simp
      · ext w
        simp [polynomialGradientMap_apply, add_mul, Finset.sum_add_distrib]
  | mul_X p i hp =>
      convert! hp.mul (hasStrictFDerivAt_apply i a) using 1
      · funext x; simp
      · ext w
        simp [polynomialGradientMap_apply, MvPolynomial.pderiv_mul,
          Pi.single_apply, apply_ite, add_mul, mul_add, mul_ite, Finset.sum_add_distrib, Finset.mul_sum,
          Finset.sum_mul, mul_assoc, mul_comm, mul_left_comm]

-- @node: polynomialGradientMap_single
/-- [Applying the gradient linear map of Q at a to the unit direction in
coordinate i gives the partial derivative of Q in coordinate i evaluated
at a](goal). -/
lemma polynomialGradientMap_single {V : Type*} [Fintype V] [DecidableEq V]
    (Q : MvPolynomial V ℝ) (a : V → ℝ) (i : V) :
    polynomialGradientMap Q a (Pi.single i 1) =
      MvPolynomial.eval a (MvPolynomial.pderiv i Q) := by
  simp [polynomialGradientMap_apply, Pi.single_apply]

-- @node: polynomial_localMin_critical
/-- If [a is a zero of Q](hyp:ha) and [coordinate v has a local minimum at a
relative to the zero set of Q](hyp:hmin), then [every partial derivative of Q
in a coordinate other than v vanishes at a](goal).

This also holds at singular points of the zero set. -/
lemma polynomial_localMin_critical {V : Type*} [Fintype V]
    (Q : MvPolynomial V ℝ) (v : V) {a : V → ℝ}
    (ha : MvPolynomial.eval a Q = 0)
    (hmin : IsLocalMinOn (fun x => x v) {x | MvPolynomial.eval x Q = 0} a) :
    ∀ i, i ≠ v → MvPolynomial.eval a (MvPolynomial.pderiv i Q) = 0 := by
  classical
  have he : IsLocalExtrOn (fun x => x v)
      {x | MvPolynomial.eval x Q = MvPolynomial.eval a Q} a := by
    rw [ha]
    exact Or.inl hmin
  obtain ⟨α, β, hnonzero, hmul⟩ :=
    he.exists_multipliers_of_hasStrictFDerivAt_1d
      (polynomial_eval_hasStrictFDerivAt Q a) (hasStrictFDerivAt_apply v a)
  have hα : α ≠ 0 := by
    intro hz
    have hβ := congrArg (fun f : (V → ℝ) →L[ℝ] ℝ => f (Pi.single v 1)) hmul
    have hb : β = 0 := by simpa [hz] using hβ
    exact hnonzero (by simp [hz, hb])
  intro i hi
  have hi' := congrArg (fun f : (V → ℝ) →L[ℝ] ℝ => f (Pi.single i 1)) hmul
  have hprod : α * MvPolynomial.eval a (MvPolynomial.pderiv i Q) = 0 := by
    simpa [polynomialGradientMap_single, Pi.single_apply, hi] using hi'
  exact (mul_eq_zero.mp hprod).resolve_left hα

-- @node: polynomialCoordinateCriticalSet
/-- For [a polynomial Q](hyp:Q) and [a distinguished coordinate v](hyp:v),
the [coordinate critical set](goal) consists of points where [Q vanishes](step:1)
and [all partial derivatives in coordinates other than v vanish](step:2). -/
def polynomialCoordinateCriticalSet {V : Type*} (Q : MvPolynomial V ℝ) (v : V) :
    Set (V → ℝ) :=
  {a | MvPolynomial.eval a Q = 0 ∧
    ∀ i, i ≠ v → MvPolynomial.eval a (MvPolynomial.pderiv i Q) = 0}

-- @node: polynomial_sign_cell_exists_critical
/-- If [the zero set of Q is compact](hyp:hQ), [every original polynomial is
nonzero on that zero set](hyp:hn), and [a is a zero of Q](hyp:ha), then
[there is a zero of Q with the same strict sign pattern as a where all partial
derivatives of Q other than the one in coordinate v vanish](goal). -/
lemma polynomial_sign_cell_exists_critical {I V : Type*} [Finite I] [Fintype V]
    (p : I → MvPolynomial V ℝ) (Q : MvPolynomial V ℝ) (v : V)
    (hQ : IsCompact {a | MvPolynomial.eval a Q = 0})
    (hn : {a | MvPolynomial.eval a Q = 0} ⊆ polynomialNonzeroDomain p)
    {a : V → ℝ} (ha : MvPolynomial.eval a Q = 0) :
    ∃ y ∈ polynomialCoordinateCriticalSet Q v,
      strictPolynomialSignPattern p y = strictPolynomialSignPattern p a := by
  obtain ⟨y, hy, hsign, hmin⟩ := polynomial_sign_cell_exists_localMin p Q v hQ hn ha
  exact ⟨y, ⟨hy, polynomial_localMin_critical Q v hy hmin⟩, hsign⟩

-- @node: strictPolynomialSignPattern_critical_reduction
/-- If [each polynomial in the family has total degree at most d](hyp:hd), then
[there is a polynomial Q in the same variables, of total degree at most twice
the number of polynomials times d plus two, whose zero set is compact and
whose coordinate critical set for v has at least as many points as there are
strict sign patterns where all original polynomials are nonzero](goal). -/
lemma strictPolynomialSignPattern_critical_reduction {I V : Type*}
    [Fintype I] [Fintype V] (v : V) (p : I → MvPolynomial V ℝ) (d : ℕ)
    (hd : ∀ i, (p i).totalDegree ≤ d) :
    ∃ Q : MvPolynomial V ℝ,
      Q.totalDegree ≤ 2 * Fintype.card I * d + 2 ∧
      IsCompact {a | MvPolynomial.eval a Q = 0} ∧
      (strictPolynomialSignPattern p '' polynomialNonzeroDomain p).encard ≤
        (polynomialCoordinateCriticalSet Q v).encard := by
  classical
  let : Nonempty V := ⟨v⟩
  obtain ⟨R, ε, _, hε, hsigns⟩ := polynomialCompactLevel_carries_signs p
  let Q := polynomialCompactBarrier p R - MvPolynomial.C ε
  have hzero : {a | MvPolynomial.eval a Q = 0} =
      {a | MvPolynomial.eval a (polynomialCompactBarrier p R) = ε} := by
    ext a
    simp [Q, sub_eq_zero]
  have hc : IsCompact {a | MvPolynomial.eval a Q = 0} := by
    rw [hzero]
    exact polynomialCompactLevel_isCompact p R hε
  have hn : {a | MvPolynomial.eval a Q = 0} ⊆ polynomialNonzeroDomain p := by
    rw [hzero]
    intro a ha
    exact (polynomialCompactSuperlevel_properties p R hε ha.ge).1
  refine ⟨Q, ?_, hc, ?_⟩
  · exact (MvPolynomial.totalDegree_sub _ _).trans
      (max_le (polynomialCompactBarrier_degree p R d hd) (by simp))
  · have hs : strictPolynomialSignPattern p '' polynomialNonzeroDomain p ⊆
        strictPolynomialSignPattern p '' polynomialCoordinateCriticalSet Q v := by
      rw [← hsigns, ← hzero]
      rintro _ ⟨a, ha, rfl⟩
      exact polynomial_sign_cell_exists_critical p Q v hc hn ha
    exact (Set.encard_mono hs).trans (Set.encard_image_le _ _)

-- @node: polynomialCriticalEquations
/-- For [a polynomial Q](hyp:Q), [a distinguished coordinate v](hyp:v), and
[an equation index i](hyp:i), the [critical equation polynomial](goal) is
[Q when i is v](step:1) and [the partial derivative of Q in coordinate i
otherwise](step:2). -/
def polynomialCriticalEquations {V : Type*} [DecidableEq V]
    (Q : MvPolynomial V ℝ) (v i : V) : MvPolynomial V ℝ :=
  if i = v then Q else MvPolynomial.pderiv i Q

-- @node: polynomialCriticalEquations_zero_set
/-- [The common zero set of the critical equation polynomials for Q and
coordinate v is exactly the set where Q and all its partial derivatives in
coordinates other than v vanish](goal). -/
lemma polynomialCriticalEquations_zero_set {V : Type*} [DecidableEq V]
    (Q : MvPolynomial V ℝ) (v : V) :
    {a | ∀ i, MvPolynomial.eval a (polynomialCriticalEquations Q v i) = 0} =
      polynomialCoordinateCriticalSet Q v := by
  ext a
  constructor
  · intro h
    refine ⟨?_, fun i hi => ?_⟩
    · simpa [polynomialCriticalEquations] using h v
    · simpa [polynomialCriticalEquations, hi] using h i
  · rintro ⟨hQ, hd⟩ i
    by_cases hi : i = v
    · simpa [polynomialCriticalEquations, hi] using hQ
    · simpa [polynomialCriticalEquations, hi] using hd i hi

-- @node: polynomialCriticalEquations_degree
/-- [Each critical equation polynomial for Q and distinguished coordinate v
has total degree at most the total degree of Q](goal). -/
lemma polynomialCriticalEquations_degree {V : Type*} [DecidableEq V]
    (Q : MvPolynomial V ℝ) (v i : V) :
    (polynomialCriticalEquations Q v i).totalDegree ≤ Q.totalDegree := by
  by_cases hi : i = v
  · simp [polynomialCriticalEquations, hi]
  · simp only [polynomialCriticalEquations, if_neg hi]
    by_cases hz : MvPolynomial.pderiv i Q = 0
    · simp [hz]
    · exact (Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension.totalDegree_pderiv_lt hz).le

-- @node: polynomialComparisonPattern_critical_reduction
/-- If [each polynomial in the family has total degree at most d](hyp:hd), then
[there is a polynomial Q in one additional variable, of total degree at most
four times the number of polynomials times the larger of d and one, plus two,
whose zero set is compact and whose coordinate critical set for the added
coordinate has at least as many points as there are weak and strict comparison
patterns of the original family](goal). -/
lemma polynomialComparisonPattern_critical_reduction {I V : Type*}
    [Fintype I] [Fintype V] (p : I → MvPolynomial V ℝ) (d : ℕ)
    (hd : ∀ i, (p i).totalDegree ≤ d) :
    ∃ Q : MvPolynomial (Option V) ℝ,
      Q.totalDegree ≤ 4 * Fintype.card I * max d 1 + 2 ∧
      IsCompact {a | MvPolynomial.eval a Q = 0} ∧
      (Set.range (polynomialComparisonPattern p)).encard ≤
        (polynomialCoordinateCriticalSet Q none).encard := by
  let shifted : I × Bool → MvPolynomial (Option V) ℝ :=
    fun ib => signShiftPolynomial (p ib.1) ib.2
  obtain ⟨Q, hdegree, hcompact, hcount⟩ :=
    strictPolynomialSignPattern_critical_reduction none shifted (max d 1)
      (fun ib => (signShiftPolynomial_degree _ _).trans (max_le_max (hd ib.1) le_rfl))
  refine ⟨Q, hdegree.trans_eq ?_, hcompact, ?_⟩
  · simp only [Fintype.card_prod, Fintype.card_bool]
    ring
  · exact (polynomialComparisonPattern_encard_le_nonzero p).trans hcount

end
end Papers.TbsNeuralCausalPi

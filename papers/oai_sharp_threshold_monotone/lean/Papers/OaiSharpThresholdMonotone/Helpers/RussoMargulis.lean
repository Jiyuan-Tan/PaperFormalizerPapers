module
public import Papers.OaiSharpThresholdMonotone.Helpers.Fourier
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Polynomial probabilities, Russo–Margulis, and quantile recovery

Continuity, strict monotonicity, endpoint values, and quantile identities are
conclusions established from the increasing nontrivial family, never hypotheses.
-/

@[expose] public section

open scoped BigOperators
open Causalean.Experimentation.DesignBased

namespace Papers.OaiSharpThresholdMonotone

variable {n : ℕ}

-- @node: propertyProbabilityPolynomial
/-- For [a family of graphs](hyp:P) on [a fixed number of labeled vertices](hyp:n),
the [probability polynomial](goal) sums, over graphs in the family, the product of
one factor of the probability variable for each present edge and one factor of
one minus that variable for each absent edge. -/
noncomputable def propertyProbabilityPolynomial (P : Set (GraphConfig n)) : Polynomial ℝ :=
  ∑ x : GraphConfig n, Polynomial.C (boolValue (propertyIndicator P) x) *
    ∏ e : GraphEdge n, if x e then Polynomial.X else 1 - Polynomial.X

-- @node: thresholdProperty_bundles
/-- For [a family of graphs](hyp:P), if [the family is invariant under vertex relabeling, increasing under edge
addition, nonempty, and proper](hyp:hP), then [it is a graph property, an increasing
graph property, and a nontrivial graph property in the respective bundled
formulations](goal). -/
lemma thresholdProperty_bundles (P : Set (GraphConfig n)) (hP : ThresholdProperty P) :
    IsGraphProperty P ∧ IsIncreasingGraphProperty P ∧ IsNontrivialGraphProperty P := by
  exact ⟨⟨hP.1⟩, ⟨hP.1, hP.2.1⟩, ⟨hP.1, hP.2.2⟩⟩

-- @node: propertyIndicator_symmetric
/-- For [a family of graphs](hyp:P), if [the family is invariant under vertex relabeling](hyp:hP), then [its
Boolean membership indicator is also invariant under vertex relabeling](goal). -/
lemma propertyIndicator_symmetric (P : Set (GraphConfig n)) (hP : GraphPropertyInvariant P) :
    GraphSymmetric (propertyIndicator P) := by
  classical
  intro τ x
  simp only [propertyIndicator, hP τ x]

-- @node: propertyIndicator_monotone
/-- For [a family of graphs](hyp:P), if [the family is closed under adding edges](hyp:hP), then [its Boolean
membership indicator is monotone under edge addition](goal). -/
lemma propertyIndicator_monotone (P : Set (GraphConfig n)) (hP : IncreasingFamily P) :
    Monotone (propertyIndicator P) := by
  classical
  intro x y hxy
  by_cases hx : x ∈ P
  · have hy := hP x y hxy hx
    simp [propertyIndicator, hx, hy]
  · simp [propertyIndicator, hx]

-- @node: propertyIndicator_nonconstant
/-- For [a family of graphs](hyp:P), if [the family is nonempty and is not the family of all graphs](hyp:hP),
then [there are two graphs with different Boolean membership indicators](goal). -/
lemma propertyIndicator_nonconstant (P : Set (GraphConfig n)) (hP : NontrivialFamily P) :
    ∃ x y, propertyIndicator P x ≠ propertyIndicator P y := by
  classical
  obtain ⟨x, hx⟩ := hP.1
  obtain ⟨y, hy⟩ : ∃ y, y ∉ P := by
    by_contra hn
    push Not at hn
    exact hP.2 (Set.eq_univ_of_forall hn)
  exact ⟨x, y, by simp [propertyIndicator, hx, hy]⟩

-- @node: propertyProb_eq_expectation
/-- For [a graph family](hyp:P) and [a bias parameter](hyp:p), [the probability of the family under the biased graph distribution equals
the expectation of its membership indicator, coded as zero or one](goal). -/
lemma propertyProb_eq_expectation (P : Set (GraphConfig n)) (p : ℝ) :
    propertyProb p P = (biasedLaw (GraphEdge n) p).E (boolValue (propertyIndicator P)) := by
  classical
  unfold propertyProb FiniteDesign.Pr
  apply FiniteDesign.E_congr
  intro x
  simp [FiniteDesign.ind, boolValue, propertyIndicator]

-- @node: propertyProb_mem_Icc
/-- For [a graph family](hyp:P) and [a bias parameter](hyp:p), [the probability of the family under the biased graph distribution lies
between zero and one, inclusive](goal). -/
lemma propertyProb_mem_Icc (P : Set (GraphConfig n)) (p : ℝ) :
    propertyProb p P ∈ Set.Icc 0 1 := by
  classical
  exact ⟨(biasedLaw (GraphEdge n) p).Pr_nonneg _,
    (biasedLaw (GraphEdge n) p).Pr_le_one _⟩

-- @node: propertyProbabilityPolynomial_eval
/-- For [a graph family](hyp:P) and [an edge probability](hyp:p), if [the edge probability is between zero and one, inclusive](hyp:hp), then
[evaluating a graph family's probability polynomial at that probability gives
its probability under independent Bernoulli edges](goal). -/
lemma propertyProbabilityPolynomial_eval (P : Set (GraphConfig n)) (p : ℝ)
    (hp : p ∈ Set.Icc 0 1) :
    (propertyProbabilityPolynomial P).eval p = propertyProb p P := by
  classical
  rw [propertyProb_eq_expectation, biasedLaw_eq_bernoulliDesign p hp]
  simp only [propertyProbabilityPolynomial, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod, apply_ite,
    Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_one,
    FiniteDesign.E, bernoulliDesign, prodDesign_p, coinDesign, Bool.cond_eq_ite]
  apply Finset.sum_congr rfl
  intro x _
  rw [mul_comm]

-- @node: propertyProb_continuous
/-- For [a fixed graph family](hyp:P), [its probability is a continuous function of the real
bias parameter](goal). -/
lemma propertyProb_continuous (P : Set (GraphConfig n)) :
    Continuous (fun p => propertyProb p P) := by
  classical
  simp only [propertyProb_eq_expectation, FiniteDesign.E, biasedLaw,
    bernoulliDesign, prodDesign_p, coinDesign, Bool.cond_eq_ite]
  apply continuous_finsetSum
  intro x _
  apply Continuous.mul _ continuous_const
  apply continuous_finsetProd
  intro e _
  split_ifs <;> fun_prop

-- @node: propertyProb_endpoints
/-- For [a family of graphs](hyp:P), if [the family is invariant under vertex relabeling, increasing under edge
addition, nonempty, and proper](hyp:hP), then [its probability is zero when the edge
probability is zero and one when the edge probability is one](goal). -/
lemma propertyProb_endpoints (P : Set (GraphConfig n)) (hP : ThresholdProperty P) :
    propertyProb 0 P = 0 ∧ propertyProb 1 P = 1 := by
  classical
  have hEval (b : Bool) : propertyProb (if b then 1 else 0) P =
      boolValue (propertyIndicator P) (fun _ => b) := by
    rw [propertyProb_eq_expectation]
    unfold FiniteDesign.E
    rw [Finset.sum_eq_single (fun _ => b)]
    · cases b <;> simp [biasedLaw, bernoulliDesign, prodDesign_p, coinDesign]
    · intro x _ hne
      obtain ⟨e, he⟩ : ∃ e, x e ≠ b := by
        by_contra hn
        push Not at hn
        exact hne (funext hn)
      have hzero : (biasedLaw (GraphEdge n) (if b then 1 else 0)).p x = 0 := by
        simp only [biasedLaw, bernoulliDesign, prodDesign_p, coinDesign]
        apply Finset.prod_eq_zero (Finset.mem_univ e)
        cases b <;> cases hxe : x e <;> simp_all
      rw [hzero, zero_mul]
    · simp
  have hbot : (fun _ : GraphEdge n => false) ∉ P := by
    intro hb
    apply hP.2.2.2
    apply Set.eq_univ_of_forall
    intro x
    exact hP.2.1 _ x (by intro e; simp) hb
  have htop : (fun _ : GraphEdge n => true) ∈ P := by
    obtain ⟨x, hx⟩ := hP.2.2.1
    exact hP.2.1 x _ (by intro e; simp) hx
  constructor
  · simpa [boolValue, propertyIndicator, hbot] using hEval false
  · simpa [boolValue, propertyIndicator, htop] using hEval true

-- @node: increasing_edge_difference
/-- For [a graph family](hyp:P), [a chosen edge](hyp:e), and [an assignment of all other edges](hyp:x),
if [the family is increasing under edge addition](hyp:hP), then [holding
all other edges fixed, changing one edge from absent to present increases its
zero-or-one membership indicator by either zero or one](goal). -/
lemma increasing_edge_difference (P : Set (GraphConfig n)) (hP : IncreasingFamily P)
    (e : GraphEdge n) (x : {e' : GraphEdge n // e' ≠ e} → Bool) :
    coordDiffRemaining (boolValue (propertyIndicator P)) e x = 0 ∨
      coordDiffRemaining (boolValue (propertyIndicator P)) e x = 1 := by
  classical
  have hxy : insertCoordinate e x false ≤ insertCoordinate e x true := by
    intro j
    by_cases hj : j = e <;> simp [insertCoordinate, hj]
  have hmono := propertyIndicator_monotone P hP hxy
  unfold coordDiffRemaining boolValue
  cases h0 : propertyIndicator P (insertCoordinate e x false) <;>
    cases h1 : propertyIndicator P (insertCoordinate e x true) <;>
    simp only [Bool.false_eq_true, ↓reduceIte, sub_self, sub_zero, zero_sub,
      eq_self, true_or, or_true]
  rw [h0, h1] at hmono
  exact False.elim ((by decide : ¬ (true : Bool) ≤ false) hmono)

-- @node: bernoulli_sum_erase_resample
/-- For [Boolean coordinate weights](hyp:w), [alternative Boolean weights](hyp:t),
[a real-valued function of finitely many Boolean coordinates](hyp:g), and [a chosen coordinate](hyp:i),
if [the two coordinate weights sum to one](hyp:hw), then [summing the function
with product weights on all coordinates except one and an alternative weight on
that coordinate equals its full product-weighted sum after resampling that
coordinate and summing with the alternative weights](goal). -/
lemma bernoulli_sum_erase_resample {J : Type*} [Fintype J] [DecidableEq J]
    (w t : Bool → ℝ) (hw : ∑ b, w b = 1)
    (g : (J → Bool) → ℝ) (i : J) :
    (∑ x, (∏ j ∈ Finset.univ.erase i, w (x j)) * t (x i) * g x) =
      ∑ x, (∏ j : J, w (x j)) * ∑ b, t b * g (Function.update x i b) := by
  classical
  let e : ((J → Bool) × Bool) ≃ ((J → Bool) × Bool) :=
    { toFun := fun z => (Function.update z.1 i z.2, z.1 i)
      invFun := fun z => (Function.update z.1 i z.2, z.1 i)
      left_inv := by intro z; simp
      right_inv := by intro z; simp }
  have hup (x : J → Bool) (b : Bool) :
      (∏ j ∈ Finset.univ.erase i, w (Function.update x i b j)) =
        ∏ j ∈ Finset.univ.erase i, w (x j) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  have he := Fintype.sum_equiv e
    (fun z => w z.2 * (∏ j ∈ Finset.univ.erase i, w (z.1 j)) * t (z.1 i) * g z.1)
    (fun z => (∏ j : J, w (z.1 j)) * t z.2 * g (Function.update z.1 i z.2)) (by
      intro z
      dsimp [e]
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Function.update_self, hup]
      simp)
  simp only [Fintype.sum_prod_type] at he
  simp_rw [← Finset.sum_mul] at he
  rw [hw] at he
  simpa only [one_mul, Finset.mul_sum, mul_assoc] using he

-- @node: increasing_full_edge_difference
/-- For [a graph family](hyp:P), [a graph configuration](hyp:x), and [a chosen edge](hyp:i),
if [the family is increasing under edge addition](hyp:hP), then [the
difference between its zero-or-one membership indicators with a chosen edge forced
present and forced absent equals one when that edge is pivotal and zero
otherwise](goal). -/
lemma increasing_full_edge_difference (P : Set (GraphConfig n)) (hP : IncreasingFamily P)
    (x : GraphConfig n) (i : GraphEdge n) :
    boolValue (propertyIndicator P) (coordinateReplace i x true) -
        boolValue (propertyIndicator P) (coordinateReplace i x false) =
      if propertyIndicator P (coordinateReplace i x true) ≠
          propertyIndicator P (coordinateReplace i x false) then 1 else 0 := by
  classical
  have hm : propertyIndicator P (coordinateReplace i x false) ≤
      propertyIndicator P (coordinateReplace i x true) := by
    apply propertyIndicator_monotone P hP
    intro j
    by_cases h : j = i
    · subst j
      simp [coordinateReplace,
        Causalean.Mathlib.Probability.PoissonAddOnePoincare.coordinateReplace]
    · simp [coordinateReplace,
        Causalean.Mathlib.Probability.PoissonAddOnePoincare.coordinateReplace,
        Function.update_of_ne h]
  cases ht : propertyIndicator P (coordinateReplace i x true) <;>
    cases hb : propertyIndicator P (coordinateReplace i x false) <;>
      simp_all only [boolValue, ne_eq, Bool.false_eq_true, not_false_eq_true, ↓reduceIte,
        sub_self, sub_zero, Bool.true_eq_false, not_true_eq_false]
  exact Bool.noConfusion (hm rfl)

-- @node: russo_margulis
/-- For [a graph family](hyp:P) and [an edge probability](hyp:p), if [the family is nonempty, proper,
invariant under relabeling, and increasing under edge addition](hyp:hP) and [the edge probability is strictly between zero and
one](hyp:hp), then [the derivative of its probability with respect to the edge probability
equals the sum of its edge pivotal probabilities](goal). -/
lemma russo_margulis (P : Set (GraphConfig n)) (hP : ThresholdProperty P)
    (p : ℝ) (hp : BiasInterior p) :
    HasDerivAt (fun t => propertyProb t P) (graphTotalInfluence p (propertyIndicator P)) p := by
  classical
  let w : Bool → ℝ := fun b => if b then p else 1 - p
  let t : Bool → ℝ := fun b => if b then 1 else -1
  have hw : ∑ b, w b = 1 := by simp [w]
  have hcoin (b : Bool) : HasDerivAt (fun q : ℝ => if b then q else 1 - q) (t b) p := by
    cases b
    · simpa [t] using (hasDerivAt_id p).const_sub 1
    · simpa [t] using hasDerivAt_id' p
  have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun x _ =>
    (HasDerivAt.fun_finsetProd (u := Finset.univ) (fun j _ => hcoin (x j))).mul_const
      (boolValue (propertyIndicator P) x))
  have hcoeff :
      (∑ x : GraphConfig n, (∑ i : GraphEdge n,
        (∏ j ∈ Finset.univ.erase i, w (x j)) * t (x i)) * boolValue (propertyIndicator P) x) =
      graphTotalInfluence p (propertyIndicator P) := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    unfold graphTotalInfluence
    apply Finset.sum_congr rfl
    intro i _
    rw [bernoulli_sum_erase_resample w t hw]
    simp only [Fintype.sum_bool, t, Bool.false_eq_true, ↓reduceIte, neg_one_mul,
      one_mul, ← sub_eq_add_neg]
    change (∑ x : GraphConfig n, (∏ j : GraphEdge n, w (x j)) *
      (boolValue (propertyIndicator P) (coordinateReplace i x true) -
        boolValue (propertyIndicator P) (coordinateReplace i x false))) = _
    simp_rw [increasing_full_edge_difference P hP.2.1]
    rw [edgeInfluence, biasedLaw_eq_bernoulliDesign p ⟨hp.1.le, hp.2.le⟩]
    simp [FiniteDesign.Pr, FiniteDesign.E, FiniteDesign.ind, bernoulliDesign,
      prodDesign_p, coinDesign, w, Bool.cond_eq_ite]
  have hpoly : HasDerivAt (fun q => (propertyProbabilityPolynomial P).eval q)
      (graphTotalInfluence p (propertyIndicator P)) p := by
    rw [← hcoeff]
    simpa only [propertyProbabilityPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_prod, apply_ite, Polynomial.eval_X,
      Polynomial.eval_sub, Polynomial.eval_one, smul_eq_mul, w, t, mul_comm] using hd
  apply hpoly.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hp] with q hq
  exact (propertyProbabilityPolynomial_eval P q ⟨hq.1.le, hq.2.le⟩).symm

-- @node: graphVariance_indicator_eq
/-- For [a graph family](hyp:P) and [a bias parameter](hyp:p), [the variance of the family's zero-or-one membership indicator equals
its probability multiplied by one minus that probability](goal). -/
lemma graphVariance_indicator_eq (P : Set (GraphConfig n)) (p : ℝ) :
    graphVariance p (propertyIndicator P) = propertyProb p P * (1 - propertyProb p P) := by
  classical
  have hind : boolValue (propertyIndicator P) = FiniteDesign.ind (fun x => x ∈ P) := by
    funext x
    simp [boolValue, propertyIndicator, FiniteDesign.ind]
  rw [graphVariance, hind, FiniteDesign.Var_ind]
  rfl

-- @node: propertyProb_interior
/-- For [a graph family](hyp:P) and [an edge probability](hyp:p), if [the family is invariant under relabeling, increasing under edge addition,
nonempty, and proper](hyp:hP) and [the edge probability lies strictly between zero
and one](hyp:hp), then [the family's probability also lies strictly between zero
and one](goal). -/
lemma propertyProb_interior (P : Set (GraphConfig n)) (hP : ThresholdProperty P)
    (p : ℝ) (hp : BiasInterior p) :
    0 < propertyProb p P ∧ propertyProb p P < 1 := by
  classical
  have hweight (x : GraphConfig n) : 0 < (biasedLaw (GraphEdge n) p).p x := by
    rw [biasedLaw_eq_bernoulliDesign p ⟨hp.1.le, hp.2.le⟩]
    simp only [bernoulliDesign, prodDesign_p, coinDesign]
    apply Finset.prod_pos
    intro e _
    cases x e <;> simp [hp.1, sub_pos.mpr hp.2]
  obtain ⟨x, hx⟩ := hP.2.2.1
  obtain ⟨y, hy⟩ : ∃ y, y ∉ P := by
    by_contra hn
    push Not at hn
    exact hP.2.2.2 (Set.eq_univ_of_forall hn)
  have hmass : (biasedLaw (GraphEdge n) p).p x ≤ propertyProb p P := by
    unfold propertyProb FiniteDesign.Pr FiniteDesign.E
    calc
      _ = (biasedLaw (GraphEdge n) p).p x * FiniteDesign.ind (fun z => z ∈ P) x := by
        simp [FiniteDesign.ind, hx]
      _ ≤ _ := Finset.single_le_sum
        (fun z _ => mul_nonneg ((biasedLaw (GraphEdge n) p).p_nonneg z)
          (by simp [FiniteDesign.ind]; split_ifs <;> norm_num)) (Finset.mem_univ x)
  have hmissing : propertyProb p P + (biasedLaw (GraphEdge n) p).p y ≤ 1 := by
    rw [← (biasedLaw (GraphEdge n) p).p_sum]
    unfold propertyProb FiniteDesign.Pr FiniteDesign.E
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ y)]
    simp only [FiniteDesign.ind, hy, ↓reduceIte, mul_zero, add_zero]
    conv_rhs => rw [← Finset.sum_erase_add _ _ (Finset.mem_univ y)]
    gcongr with z hzmem
    by_cases hz : z ∈ P <;> simp [hz, (biasedLaw (GraphEdge n) p).p_nonneg z]
  exact ⟨(hweight x).trans_le hmass, by linarith [hweight y]⟩

-- @node: propertyProb_strictMonoOn
/-- For [a graph family](hyp:P), if [the family is invariant under relabeling, increasing under edge addition,
nonempty, and proper](hyp:hP), then [its probability is strictly increasing as the
edge probability ranges from zero to one, including the endpoints](goal). -/
lemma propertyProb_strictMonoOn (P : Set (GraphConfig n)) (hP : ThresholdProperty P) :
    StrictMonoOn (fun p => propertyProb p P) (Set.Icc 0 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 1) (propertyProb_continuous P).continuousOn
  intro p hp
  rw [interior_Icc] at hp
  rw [(russo_margulis P hP p hp).deriv]
  have hμ := propertyProb_interior P hP p hp
  have hv : 0 < graphVariance p (propertyIndicator P) := by
    rw [graphVariance_indicator_eq]
    exact mul_pos hμ.1 (sub_pos.mpr hμ.2)
  have hbound := variance_le_biasScale_sq_mul_influence p hp (propertyIndicator P)
  change graphVariance p (propertyIndicator P) ≤
    biasScale p ^ 2 * totalCoordInfluence p (propertyIndicator P) at hbound
  rw [graphTotalInfluence_eq_totalCoordInfluence]
  have hprod := hv.trans_le hbound
  exact (mul_pos_iff.mp hprod).resolve_right (by
    rintro ⟨hneg, _⟩
    exact (sq_nonneg (biasScale p)).not_gt hneg) |>.2

-- @node: propertyQuantile_defining_set_nonempty
/-- For [a graph family](hyp:P) and [a target probability](hyp:a), if [the family is nonempty, proper,
invariant under relabeling, and increasing under edge addition](hyp:hP) and [the target probability is strictly between zero and
one](hyp:ha), then [there exists an edge probability between zero and one, inclusive,
at which the family's probability reaches or exceeds the target](goal). -/
lemma propertyQuantile_defining_set_nonempty (P : Set (GraphConfig n))
    (hP : ThresholdProperty P) (a : ℝ) (ha : 0 < a ∧ a < 1) :
    {p : ℝ | p ∈ Set.Icc 0 1 ∧ a ≤ propertyProb p P}.Nonempty := by
  refine ⟨1, ⟨by norm_num, le_rfl⟩, ?_⟩
  rw [(propertyProb_endpoints P hP).2]
  exact ha.2.le

-- @node: propertyQuantile_spec
/-- For [a graph family](hyp:P) and [a target probability](hyp:a), if [the family is nonempty, proper,
invariant under relabeling, and increasing under edge addition](hyp:hP) and [the target probability is strictly between zero and
one](hyp:ha), then [the corresponding quantile lies strictly between zero and one,
attains the target probability, and is the unique edge probability in the closed
unit interval attaining that target](goal). -/
lemma propertyQuantile_spec (P : Set (GraphConfig n)) (hP : ThresholdProperty P)
    (a : ℝ) (ha : 0 < a ∧ a < 1) : -- @realizes a(level in the open unit interval)
    propertyQuantile a P ∈ Set.Ioo 0 1 ∧
      propertyProb (propertyQuantile a P) P = a ∧
      ∀ p ∈ Set.Icc (0 : ℝ) 1, propertyProb p P = a → p = propertyQuantile a P := by
  have hend := propertyProb_endpoints P hP
  have haimage : a ∈ Set.Icc (propertyProb 0 P) (propertyProb 1 P) := by
    rw [hend.1, hend.2]
    exact ⟨ha.1.le, ha.2.le⟩
  obtain ⟨q, hq, hqa⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
    (propertyProb_continuous P).continuousOn haimage
  change propertyProb q P = a at hqa
  have hmono := propertyProb_strictMonoOn P hP
  have hqi : q ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · by_contra hn
      have hq0 : q = 0 := le_antisymm (not_lt.mp hn) hq.1
      rw [hq0, hend.1] at hqa
      linarith [ha.1]
    · by_contra hn
      have hq1 : q = 1 := le_antisymm hq.2 (not_lt.mp hn)
      rw [hq1, hend.2] at hqa
      linarith [ha.2]
  have hquant : propertyQuantile a P = q := by
    apply le_antisymm
    · exact csInf_le ⟨0, fun p hp => hp.1.1⟩ ⟨hq, hqa.ge⟩
    · apply le_csInf (propertyQuantile_defining_set_nonempty P hP a ha)
      intro p hp
      by_contra hn
      have hlt := hmono hp.1 hq (lt_of_not_ge hn)
      change propertyProb p P < propertyProb q P at hlt
      rw [hqa] at hlt
      exact (not_lt_of_ge hp.2) hlt
  refine ⟨hquant.symm ▸ hqi, hquant.symm ▸ hqa, ?_⟩
  intro p hp hpa
  rw [hquant]
  exact hmono.injOn hp hq (hpa.trans hqa.symm)
    -- @realizes p_a(\mathcal P)(interior unique solution at the given level)

-- @node: propertyQuantile_strictMonoOn
/-- For [a graph family](hyp:P), if [the family is nonempty, proper, invariant under relabeling,
and increasing under edge addition](hyp:hP), then [its quantile is strictly increasing as the target
probability ranges strictly between zero and one](goal). -/
lemma propertyQuantile_strictMonoOn (P : Set (GraphConfig n)) (hP : ThresholdProperty P) :
    StrictMonoOn (fun a => propertyQuantile a P) (Set.Ioo 0 1) := by
  intro a ha b hb hab
  have hqa := propertyQuantile_spec P hP a ha
  have hqb := propertyQuantile_spec P hP b hb
  by_contra hn
  have hle := (propertyProb_strictMonoOn P hP).monotoneOn
    ⟨hqb.1.1.le, hqb.1.2.le⟩ ⟨hqa.1.1.le, hqa.1.2.le⟩ (not_lt.mp hn)
  change propertyProb (propertyQuantile b P) P ≤ propertyProb (propertyQuantile a P) P at hle
  rw [hqa.2.1, hqb.2.1] at hle
  exact (not_le_of_gt hab) hle

-- @node: logOdds_hasDerivAt
/-- For [a graph family](hyp:P) and [an edge probability](hyp:p), if [the family is nonempty, proper,
invariant under relabeling, and increasing under edge addition](hyp:hP) and [the edge probability is strictly between zero and
one](hyp:hp), then [the derivative of the logarithm of the family's probability odds
equals its total edge influence divided by its probability times one minus that
probability](goal). -/
lemma logOdds_hasDerivAt (P : Set (GraphConfig n)) (hP : ThresholdProperty P)
    (p : ℝ) (hp : BiasInterior p) :
    HasDerivAt (fun t => Real.log (propertyProb t P / (1 - propertyProb t P)))
      (graphTotalInfluence p (propertyIndicator P) /
        (propertyProb p P * (1 - propertyProb p P))) p := by
  have hμ := propertyProb_interior P hP p hp
  have hden : 1 - propertyProb p P ≠ 0 := (sub_pos.mpr hμ.2).ne'
  have hd := russo_margulis P hP p hp
  have hquot := hd.div (hd.const_sub 1) hden
  have hlog := hquot.log (div_ne_zero hμ.1.ne' hden)
  change HasDerivAt (fun t => Real.log (propertyProb t P / (1 - propertyProb t P)))
    ((graphTotalInfluence p (propertyIndicator P) * (1 - propertyProb p P) -
      propertyProb p P * -graphTotalInfluence p (propertyIndicator P)) /
      (1 - propertyProb p P) ^ 2 / (propertyProb p P / (1 - propertyProb p P))) p at hlog
  convert hlog using 1
  field_simp [hμ.1.ne', hden]
  ring


-- @node: quantile_width_le_of_logOdds_derivative_bound
/-- For [a graph family](hyp:P), [a tail probability](hyp:ε), and [a proposed derivative lower bound](hyp:A),
suppose [the family is nonempty, proper, invariant under relabeling, and increasing
under edge addition](hyp:hP), [the tail probability is strictly between zero
and one half](hyp:hε), [the proposed derivative lower bound is positive](hyp:hA),
and [total influence divided by probability times one minus probability is at least
that bound at every interior edge probability](hyp:hderiv). Then [the difference
between the quantiles at one minus the tail probability and at the tail probability
is at most twice the reciprocal of the bound times the logarithm of the ratio of
one minus the tail probability to the tail probability](goal). -/
lemma quantile_width_le_of_logOdds_derivative_bound (P : Set (GraphConfig n))
    (hP : ThresholdProperty P) (ε : ℝ) (hε : ThresholdEpsilon ε) (A : ℝ) (hA : 0 < A)
    (hderiv : ∀ p : ℝ, BiasInterior p →
      A ≤ graphTotalInfluence p (propertyIndicator P) /
        (propertyProb p P * (1 - propertyProb p P))) :
    propertyQuantile (1 - ε) P - propertyQuantile ε P ≤
      2 / A * Real.log ((1 - ε) / ε) := by
  have hεone : ε < 1 := lt_trans hε.2 (by norm_num)
  have hlevel : 0 < 1 - ε ∧ 1 - ε < 1 :=
    ⟨sub_pos.mpr hεone, by linarith [hε.1]⟩
  have hlo := propertyQuantile_spec P hP ε ⟨hε.1, hεone⟩
  have hhi := propertyQuantile_spec P hP (1 - ε) hlevel
  have horder : propertyQuantile ε P ≤ propertyQuantile (1 - ε) P := by
    apply le_of_lt
    exact propertyQuantile_strictMonoOn P hP ⟨hε.1, hεone⟩ hlevel (by linarith [hε.2])
  let L : ℝ → ℝ := fun p => Real.log (propertyProb p P / (1 - propertyProb p P))
  have hd (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
      HasDerivAt L (graphTotalInfluence p (propertyIndicator P) /
        (propertyProb p P * (1 - propertyProb p P))) p :=
    logOdds_hasDerivAt P hP p hp
  have hc : ContinuousOn L (Set.Ioo (0 : ℝ) 1) := by
    intro p hp
    exact (hd p hp).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ L (Set.Ioo (0 : ℝ) 1) := by
    intro p hp
    exact (hd p hp).differentiableAt.differentiableWithinAt
  have hbound := (convex_Ioo (0 : ℝ) 1).mul_sub_le_image_sub_of_le_deriv hc
    (by simpa only [interior_Ioo] using hdiff)
    (C := A) (by
      intro p hp
      have hpi : p ∈ Set.Ioo (0 : ℝ) 1 := by simpa only [interior_Ioo] using hp
      rw [(hd p hpi).deriv]
      exact hderiv p hpi)
    (propertyQuantile ε P) hlo.1 (propertyQuantile (1 - ε) P) hhi.1 horder
  change A * (propertyQuantile (1 - ε) P - propertyQuantile ε P) ≤
    Real.log (propertyProb (propertyQuantile (1 - ε) P) P /
      (1 - propertyProb (propertyQuantile (1 - ε) P) P)) -
    Real.log (propertyProb (propertyQuantile ε P) P /
      (1 - propertyProb (propertyQuantile ε P) P)) at hbound
  rw [hlo.2.1, hhi.2.1] at hbound
  have hcancel : 1 - (1 - ε) = ε := by ring
  rw [hcancel, Real.log_div hlevel.1.ne' hε.1.ne',
    Real.log_div hε.1.ne' hlevel.1.ne'] at hbound
  calc
    propertyQuantile (1 - ε) P - propertyQuantile ε P ≤
        (2 * Real.log ((1 - ε) / ε)) / A := by
      apply (le_div_iff₀ hA).2
      rw [Real.log_div hlevel.1.ne' hε.1.ne']
      nlinarith [hbound]
    _ = 2 / A * Real.log ((1 - ε) / ε) := by ring

-- @node: threshold_logarithm_bound
/-- For [a tail probability](hyp:ε), if [it is strictly between zero and one half](hyp:hε), then
[the logarithm of the ratio of one minus that probability to that probability is
at most twice the logarithm of the reciprocal of twice that probability](goal). -/
lemma threshold_logarithm_bound (ε : ℝ) (hε : ThresholdEpsilon ε) :
    Real.log ((1 - ε) / ε) ≤ 2 * Real.log (1 / (2 * ε)) := by
  have hεpos : 0 < ε := hε.1
  have hεone : ε < 1 := lt_trans hε.2 (by norm_num)
  have hratio : (1 - ε) / ε ≤ (1 / (2 * ε)) ^ 2 := by
    have hquad : 4 * ε * (1 - ε) ≤ 1 := by
      nlinarith [sq_nonneg (2 * ε - 1)]
    rw [div_pow]
    apply (div_le_div_iff₀ hεpos (sq_pos_of_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hεpos))).2
    norm_num
    nlinarith [mul_nonneg hεpos.le (sub_nonneg.mpr hquad)]
  calc
    Real.log ((1 - ε) / ε) ≤ Real.log ((1 / (2 * ε)) ^ 2) :=
      Real.log_le_log (div_pos (sub_pos.mpr hεone) hεpos) hratio
    _ = 2 * Real.log (1 / (2 * ε)) := by rw [Real.log_pow]; norm_num

end Papers.OaiSharpThresholdMonotone

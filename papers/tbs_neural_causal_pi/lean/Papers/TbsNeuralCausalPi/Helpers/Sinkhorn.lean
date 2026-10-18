module
public import Papers.TbsNeuralCausalPi.Setup.Notation
public import Causalean.Mathlib.InformationTheory.Entropy
/-! # Finite entropy regularization error -/
public section
namespace Papers.TbsNeuralCausalPi
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
open scoped ENNReal
/-- If [the first marginal weights form a probability vector](hyp:hmu) and
[the second marginal weights form a probability vector](hyp:hnu), [their
independent product is a feasible transport plan with these marginals](goal). -/
-- @node: product_mem_transportPlans
lemma product_mem_transportPlans {n m : ℕ} {mu : Fin n → ℝ} {nu : Fin m → ℝ}
    (hmu : mu ∈ probabilitySimplex n) (hnu : nu ∈ probabilitySimplex m) :
    (fun i j => mu i * nu j) ∈ transportPlans mu nu := by
  refine ⟨hmu, hnu, fun i j => mul_nonneg (hmu.1 i) (hnu.1 j), ?_, ?_⟩
  · intro i
    rw [← Finset.mul_sum, hnu.2, mul_one]
  · intro j
    rw [← Finset.sum_mul, hmu.2, one_mul]

/-- If [a transport plan is feasible for its marginals](hyp:hT), [the sum of
all its entries is one](goal). -/
-- @node: transportPlan_sum_eq_one
lemma transportPlan_sum_eq_one {n m : ℕ} {mu : Fin n → ℝ} {nu : Fin m → ℝ}
    {T : Fin n → Fin m → ℝ} (hT : T ∈ transportPlans mu nu) :
    ∑ i, ∑ j, T i j = 1 := by
  simp_rw [hT.2.2.2.1]
  exact hT.1.2

/-- If [a transport plan is feasible for its marginals](hyp:hT), [each selected
entry of the plan is at most one](goal). -/
-- @node: transportPlan_entry_le_one
lemma transportPlan_entry_le_one {n m : ℕ} {mu : Fin n → ℝ} {nu : Fin m → ℝ}
    {T : Fin n → Fin m → ℝ} (hT : T ∈ transportPlans mu nu) (i : Fin n) (j : Fin m) :
    T i j ≤ 1 := by
  calc
    T i j ≤ ∑ k, T i k := Finset.single_le_sum (fun k _ => hT.2.2.1 i k) (Finset.mem_univ j)
    _ ≤ ∑ k, ∑ l, T k l := Finset.single_le_sum
      (fun k _ => Finset.sum_nonneg fun l _ => hT.2.2.1 k l) (Finset.mem_univ i)
    _ = 1 := transportPlan_sum_eq_one hT

/-- If [a transport plan is feasible for its marginals](hyp:hT), [its entropy
penalty is nonnegative and at most one plus the logarithm of the product of
the two marginal sizes](goal).

The entropy penalty used here is one plus Shannon entropy. -/
-- @node: planEntropy_bounds
lemma planEntropy_bounds {n m : ℕ} {mu : Fin n → ℝ} {nu : Fin m → ℝ}
    {T : Fin n → Fin m → ℝ} (hT : T ∈ transportPlans mu nu) :
    0 ≤ planEntropy T ∧ planEntropy T ≤ Real.log (m*n : ℕ) + 1 := by
  have hsum : ∑ z : Fin n × Fin m, T z.1 z.2 = 1 := by
    simpa only [Fintype.sum_prod_type] using transportPlan_sum_eq_one hT
  have heq : planEntropy T = 1 +
      Causalean.Mathlib.InformationTheory.entropy (fun z : Fin n × Fin m => T z.1 z.2) := by
    simp [planEntropy, Causalean.Mathlib.InformationTheory.entropy,
      Real.negMulLog, Fintype.sum_prod_type, Finset.sum_neg_distrib, sub_eq_add_neg]
  have hlo := Causalean.Mathlib.InformationTheory.entropy_nonneg
    (fun z : Fin n × Fin m => hT.2.2.1 z.1 z.2)
    (fun z => transportPlan_entry_le_one hT z.1 z.2)
  have hhi := Causalean.Mathlib.InformationTheory.entropy_le_log_card
    (fun z : Fin n × Fin m => hT.2.2.1 z.1 z.2) hsum
  simp only [Fintype.card_prod, Fintype.card_fin] at hhi
  rw [Nat.mul_comm n m] at hhi
  rw [heq]
  constructor <;> linarith

/-- If [a transport plan is feasible for its marginals](hyp:hT), [its transport
cost between the two collections of points is nonnegative](goal). -/
-- @node: transportCost_nonneg
lemma transportCost_nonneg {n m d : ℕ} (x : Fin n → L1Vec d) (y : Fin m → L1Vec d)
    {mu : Fin n → ℝ} {nu : Fin m → ℝ} {T : Fin n → Fin m → ℝ}
    (hT : T ∈ transportPlans mu nu) : 0 ≤ transportCost x y T := by
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg dist_nonneg (hT.2.2.1 i j)

/-- If [both marginal weight vectors are probability vectors](hyp:hmu,hnu)
and [the regularization strength is nonnegative](hyp:hlam), [the
entropy-regularized transport value minus the unregularized value lies between
minus the regularization strength times one plus the logarithm of the product
of marginal sizes, and zero](goal). -/
-- @node: entropicW1_sub_discreteW1_bounds
lemma entropicW1_sub_discreteW1_bounds {n m d : ℕ}
    (x : Fin n → L1Vec d) (y : Fin m → L1Vec d)
    {mu : Fin n → ℝ} {nu : Fin m → ℝ}
    (hmu : mu ∈ probabilitySimplex n) (hnu : nu ∈ probabilitySimplex m)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    -(Real.log (m*n : ℕ) + 1) * lam ≤ entropicW1 lam x y mu nu - discreteW1 x y mu nu ∧
    entropicW1 lam x y mu nu - discreteW1 x y mu nu ≤ 0 := by
  have hne : (transportPlans mu nu).Nonempty := ⟨_, product_mem_transportPlans hmu hnu⟩
  have hcost : BddBelow (transportCost x y '' transportPlans mu nu) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨T, hT, rfl⟩
    exact transportCost_nonneg x y hT
  have hreg : BddBelow ((fun T => transportCost x y T - lam * planEntropy T) ''
      transportPlans mu nu) := by
    refine ⟨-lam * (Real.log (m*n : ℕ) + 1), ?_⟩
    rintro _ ⟨T, hT, rfl⟩
    have hc := transportCost_nonneg x y hT
    have he := mul_le_mul_of_nonneg_left (planEntropy_bounds hT).2 hlam
    linarith
  have hu : entropicW1 lam x y mu nu ≤ discreteW1 x y mu nu := by
    apply le_csInf (hne.image (transportCost x y))
    rintro _ ⟨T, hT, rfl⟩
    calc
      entropicW1 lam x y mu nu ≤ transportCost x y T - lam * planEntropy T :=
        csInf_le hreg ⟨T, hT, rfl⟩
      _ ≤ transportCost x y T := sub_le_self _ (mul_nonneg hlam (planEntropy_bounds hT).1)
  have hl : discreteW1 x y mu nu - lam * (Real.log (m*n : ℕ) + 1) ≤
      entropicW1 lam x y mu nu := by
    apply le_csInf (hne.image (fun T => transportCost x y T - lam * planEntropy T))
    rintro _ ⟨T, hT, rfl⟩
    have hc : discreteW1 x y mu nu ≤ transportCost x y T := csInf_le hcost ⟨T, hT, rfl⟩
    have he := mul_le_mul_of_nonneg_left (planEntropy_bounds hT).2 hlam
    linarith
  constructor <;> linarith

/-- If [the marginal weights form a probability vector](hyp:hmu), [the plan
placing each weight on the diagonal and zero elsewhere is feasible for two
copies of that marginal](goal). -/
-- @node: diagonal_mem_transportPlans
lemma diagonal_mem_transportPlans {n : ℕ} {mu : Fin n → ℝ}
    (hmu : mu ∈ probabilitySimplex n) :
    (fun i j => if i = j then mu i else 0) ∈ transportPlans mu mu := by
  refine ⟨hmu, hmu, ?_, ?_, ?_⟩
  · intro i j
    dsimp only
    split
    · exact hmu.1 i
    · exact le_rfl
  · intro i
    simp
  · intro j
    simp

/-- If [the weights form a probability vector](hyp:hmu), [the discrete
Wasserstein transport value from the weighted point collection to itself is zero](goal). -/
-- @node: discreteW1_self
lemma discreteW1_self {n d : ℕ} (x : Fin n → L1Vec d)
    {mu : Fin n → ℝ} (hmu : mu ∈ probabilitySimplex n) : discreteW1 x x mu mu = 0 := by
  have hne : (transportPlans mu mu).Nonempty := ⟨_, product_mem_transportPlans hmu hmu⟩
  have hb : BddBelow (transportCost x x '' transportPlans mu mu) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨T, hT, rfl⟩
    exact transportCost_nonneg x x hT
  apply le_antisymm
  · have h := csInf_le hb
      (Set.mem_image_of_mem (transportCost x x) (diagonal_mem_transportPlans hmu))
    simpa [discreteW1, transportCost] using h
  · apply le_csInf (hne.image (transportCost x x))
    rintro _ ⟨T, hT, rfl⟩
    exact transportCost_nonneg x x hT

-- @node: lem:sinkhorn-approx
/-- If [both point collections are nonempty](hyp:hn,hm), [both marginal weight
vectors are probability vectors](hyp:hmu,hnu), and [the regularization strength is positive](hyp:hlam),
[the regularized transport value minus the discrete Wasserstein value lies
between minus the regularization strength times one plus the logarithm of
the product of marginal sizes, and zero; the absolute difference between
Sinkhorn divergence and discrete Wasserstein distance is at most twice that
same positive bound](goal). -/
lemma sinkhorn_approx {n m d : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (x : Fin n → L1Vec d) (y : Fin m → L1Vec d)
    (mu : Fin n → ℝ) (nu : Fin m → ℝ)
    (hmu : mu ∈ probabilitySimplex n) (hnu : nu ∈ probabilitySimplex m)
    (lam : ℝ) (hlam : 0 < lam) :
    -(Real.log (m*n : ℕ) + 1) * lam ≤ entropicW1 lam x y mu nu - discreteW1 x y mu nu ∧
    entropicW1 lam x y mu nu - discreteW1 x y mu nu ≤ 0 ∧
    |sinkhornDivergence lam x y mu nu - discreteW1 x y mu nu| ≤
      2 * (Real.log (m*n : ℕ) + 1) * lam := by
  have hxy := entropicW1_sub_discreteW1_bounds x y hmu hnu hlam.le
  have hxx := entropicW1_sub_discreteW1_bounds x x hmu hmu hlam.le
  have hyy := entropicW1_sub_discreteW1_bounds y y hnu hnu hlam.le
  rw [discreteW1_self x hmu, sub_zero] at hxx
  rw [discreteW1_self y hnu, sub_zero] at hyy
  refine ⟨hxy.1, hxy.2, ?_⟩
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hlog : Real.log (m*n : ℕ) = Real.log (m : ℝ) + Real.log (n : ℝ) := by
    rw [Nat.cast_mul, Real.log_mul hm0 hn0]
  have hlogn : Real.log (n*n : ℕ) = 2 * Real.log (n : ℝ) := by
    rw [Nat.cast_mul, Real.log_mul hn0 hn0]
    ring
  have hlogm : Real.log (m*m : ℕ) = 2 * Real.log (m : ℝ) := by
    rw [Nat.cast_mul, Real.log_mul hm0 hm0]
    ring
  have hln : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hlm : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast hm)
  rw [hlogn] at hxx
  rw [hlogm] at hyy
  rw [hlog, sinkhornDivergence, abs_le]
  constructor <;> nlinarith [mul_nonneg hln hlam.le, mul_nonneg hlm hlam.le]

end Papers.TbsNeuralCausalPi

module
public import Papers.OaiMetricMarkovCotype.Basic

/-! # The dual of real null sequences

Finite truncations determine continuous functionals on null sequences. The
coordinate coefficients of such a functional are summable, by testing against
finite sign sequences.
-/

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open Filter
namespace Papers.OaiMetricMarkovCotype

-- @node: cZeroCut
/-- For [a finite set of indices](hyp:s) and [a real sequence](hyp:x), the
[finite truncation](goal) retains the sequence on that set and is zero elsewhere. -/
def cZeroCut (s : Finset ℕ) (x : ℕ → ℝ) : ZeroAtInftyContinuousMap ℕ ℝ where
  toFun i := if i ∈ s then x i else 0
  continuous_toFun := by fun_prop
  zero_at_infty' := by
    rw [cocompact_eq_cofinite]
    apply tendsto_const_nhds.congr'
    filter_upwards [s.finite_toSet.compl_mem_cofinite] with i hi
    simp_all

-- @node: cZeroCut_apply
/-- [The truncation of a sequence to a finite set equals its original value at
indices in the set and zero at all other indices](goal). -/
@[simp] lemma cZeroCut_apply (s : Finset ℕ) (x : ℕ → ℝ) (i : ℕ) :
    cZeroCut s x i = if i ∈ s then x i else 0 := rfl

-- @node: cZero_norm_le
/-- If [a real bound is nonnegative](hyp:hC) and [every coordinate of a null
sequence has absolute value at most that bound](hyp:h), then [the supremum norm
of the sequence is at most that bound](goal). -/
lemma cZero_norm_le (x : ZeroAtInftyContinuousMap ℕ ℝ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i, ‖x i‖ ≤ C) : ‖x‖ ≤ C :=
  (BoundedContinuousFunction.norm_le hC).2 h

-- @node: cZero_apply_le_norm
/-- [The absolute value of any coordinate of a real null sequence is at most
its supremum norm](goal). -/
lemma cZero_apply_le_norm (x : ZeroAtInftyContinuousMap ℕ ℝ) (i : ℕ) :
    ‖x i‖ ≤ ‖x‖ := x.toBCF.norm_coe_le_norm i

-- @node: cZeroCut_tendsto
/-- [The truncations of a real null sequence to its first n coordinates converge
to that sequence in the supremum norm as n tends to infinity](goal). -/
lemma cZeroCut_tendsto (x : ZeroAtInftyContinuousMap ℕ ℝ) :
    Tendsto (fun n => cZeroCut (Finset.range n) x) atTop (𝓝 x) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  have hx : Tendsto x atTop (𝓝 0) := by
    simpa [cocompact_eq_cofinite, Nat.cofinite_eq_atTop] using zero_at_infty x
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hx (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm]
  apply lt_of_le_of_lt (cZero_norm_le _ (by positivity) ?_) (half_lt_self hε)
  intro i
  by_cases hi : i < n
  · simpa [cZeroCut, hi] using (half_pos hε).le
  · have := hN i (hn.trans (Nat.le_of_not_gt hi))
    simpa [cZeroCut, hi, dist_eq_norm] using this.le

-- @node: cZeroBasis
/-- For [a coordinate index](hyp:i), the [coordinate unit sequence](goal) is one
at that index and zero everywhere else. -/
def cZeroBasis (i : ℕ) : ZeroAtInftyContinuousMap ℕ ℝ :=
  cZeroCut {i} (fun _ => 1)

-- @node: cZeroBasis_apply
/-- [A coordinate unit sequence has value one at its defining index and zero
at every other index](goal). -/
@[simp] lemma cZeroBasis_apply (i j : ℕ) :
    cZeroBasis i j = if j = i then 1 else 0 := by simp [cZeroBasis]

-- @node: cZeroCut_eq_sum
/-- [The truncation of a real sequence to a finite set is the sum of its
coordinate values times the corresponding coordinate unit sequences](goal). -/
lemma cZeroCut_eq_sum (s : Finset ℕ) (x : ℕ → ℝ) :
    cZeroCut s x = ∑ i ∈ s, x i • cZeroBasis i := by
  classical
  induction s using Finset.induction_on with
  | empty => ext j; simp [cZeroCut]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, ← ih]
    ext j
    by_cases hj : j = i
    · subst j; simp [cZeroCut, hi]
    · simp [cZeroCut, hj, ZeroAtInftyContinuousMap.coe_add]

-- @node: cZeroDual_sum_abs_le
/-- [For a continuous linear functional on real null sequences, the sum over
any finite set of the absolute values of its coordinate coefficients is at most
its operator norm](goal). -/
lemma cZeroDual_sum_abs_le (f : StrongDual ℝ (ZeroAtInftyContinuousMap ℕ ℝ))
    (s : Finset ℕ) : ∑ i ∈ s, |f (cZeroBasis i)| ≤ ‖f‖ := by
  let signs : ℕ → ℝ := fun i => if 0 ≤ f (cZeroBasis i) then 1 else -1
  have hb : ‖cZeroCut s signs‖ ≤ 1 := by
    apply cZero_norm_le _ zero_le_one
    intro i
    by_cases hi : i ∈ s <;> by_cases hs : 0 ≤ f (cZeroBasis i) <;>
      simp [cZeroCut_apply, signs, hs, hi]
  have he : f (cZeroCut s signs) = ∑ i ∈ s, |f (cZeroBasis i)| := by
    rw [cZeroCut_eq_sum, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [map_smul, smul_eq_mul, signs]
    split_ifs with h
    · simp [abs_of_nonneg h]
    · simp [abs_of_neg (lt_of_not_ge h)]
  calc
    ∑ i ∈ s, |f (cZeroBasis i)| = f (cZeroCut s signs) := he.symm
    _ ≤ ‖f (cZeroCut s signs)‖ := Real.le_norm_self _
    _ ≤ ‖f‖ * ‖cZeroCut s signs‖ := f.le_opNorm _
    _ ≤ ‖f‖ := by simpa using mul_le_mul_of_nonneg_left hb (norm_nonneg f)

-- @node: cZeroDual_coeff_mem
/-- [The values of a continuous linear functional on the coordinate unit
sequences form an absolutely summable real sequence](goal). -/
lemma cZeroDual_coeff_mem (f : StrongDual ℝ (ZeroAtInftyContinuousMap ℕ ℝ)) :
    Memℓp (fun i => f (cZeroBasis i)) 1 := by
  apply memℓp_gen
  simpa using summable_of_sum_le (fun i => abs_nonneg (f (cZeroBasis i)))
    (cZeroDual_sum_abs_le f)

-- @node: realEllOne_abs_summable
/-- [The absolute values of the coordinates of a real ℓ¹ sequence have a finite
sum](goal). -/
lemma realEllOne_abs_summable (a : RealEllOne) : Summable (fun i => ‖a i‖) := by
  simpa using a.property.summable (by norm_num)

-- @node: ellOnePairing_summable
/-- [The coordinatewise products of a real ℓ¹ sequence and a real null sequence
form a summable series](goal). -/
lemma ellOnePairing_summable (a : RealEllOne) (x : ZeroAtInftyContinuousMap ℕ ℝ) :
    Summable (fun i => a i * x i) := by
  apply Summable.of_norm_bounded ((realEllOne_abs_summable a).mul_right ‖x‖)
  intro i
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (cZero_apply_le_norm x i) (norm_nonneg _)

-- @node: ellOnePairing_bound
/-- [The absolute value of the sum of coordinatewise products of a real ℓ¹
sequence and a real null sequence is at most the ℓ¹ norm of the former times
the supremum norm of the latter](goal). -/
lemma ellOnePairing_bound (a : RealEllOne) (x : ZeroAtInftyContinuousMap ℕ ℝ) :
    ‖∑' i, a i * x i‖ ≤ ‖a‖ * ‖x‖ := by
  calc
    ‖∑' i, a i * x i‖ ≤ ∑' i, ‖a i * x i‖ :=
      norm_tsum_le_tsum_norm (ellOnePairing_summable a x).norm
    _ ≤ ∑' i, ‖a i‖ * ‖x‖ := by
      apply Summable.tsum_le_tsum _ (ellOnePairing_summable a x).norm
        ((realEllOne_abs_summable a).mul_right ‖x‖)
      intro i
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (cZero_apply_le_norm x i) (norm_nonneg _)
    _ = ‖a‖ * ‖x‖ := by
      rw [tsum_mul_right]
      congr 1
      rw [lp.norm_eq_tsum_rpow (by norm_num)]
      simp

-- @node: ellOnePairing
/-- For [a real ℓ¹ sequence](hyp:a), the [associated continuous linear
functional on null sequences](goal) sums the products of corresponding coordinates. -/
def ellOnePairing (a : RealEllOne) : StrongDual ℝ (ZeroAtInftyContinuousMap ℕ ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun x => ∑' i, a i * x i
      map_add' := by
        intro x y
        simp only [ZeroAtInftyContinuousMap.coe_add, Pi.add_apply, mul_add]
        exact (ellOnePairing_summable a x).tsum_add (ellOnePairing_summable a y)
      map_smul' := by
        intro c x
        simp only [ZeroAtInftyContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply]
        simp_rw [mul_left_comm (a _) c]
        exact tsum_mul_left }
    ‖a‖ (ellOnePairing_bound a)

-- @node: ellOnePairing_basis
/-- [Pairing a real ℓ¹ sequence with a coordinate unit sequence returns the
corresponding coordinate of the ℓ¹ sequence](goal). -/
lemma ellOnePairing_basis (a : RealEllOne) (i : ℕ) :
    ellOnePairing a (cZeroBasis i) = a i := by
  change (∑' j, a j * cZeroBasis i j) = a i
  simp [cZeroBasis_apply, tsum_ite_eq]

-- @node: ellOnePairing_norm
/-- [The operator norm of the functional associated with a real ℓ¹ sequence
equals the ℓ¹ norm of that sequence](goal). -/
lemma ellOnePairing_norm (a : RealEllOne) : ‖ellOnePairing a‖ = ‖a‖ := by
  apply le_antisymm
  · exact LinearMap.mkContinuous_norm_le _ (norm_nonneg a) _
  · apply lp.norm_le_of_forall_sum_le (by norm_num) (norm_nonneg _)
    intro s
    simpa [ellOnePairing_basis] using cZeroDual_sum_abs_le (ellOnePairing a) s

-- @node: cZeroDual_ext_basis
/-- If [two continuous linear functionals on real null sequences agree on every
coordinate unit sequence](hyp:h), then [the two functionals are equal](goal). -/
lemma cZeroDual_ext_basis (f g : StrongDual ℝ (ZeroAtInftyContinuousMap ℕ ℝ))
    (h : ∀ i, f (cZeroBasis i) = g (cZeroBasis i)) : f = g := by
  ext x
  have he (n : ℕ) : f (cZeroCut (Finset.range n) x) = g (cZeroCut (Finset.range n) x) := by
    simp only [cZeroCut_eq_sum, map_sum, map_smul, h]
  exact tendsto_nhds_unique
    ((f.continuous.tendsto x).comp (cZeroCut_tendsto x))
    (((g.continuous.tendsto x).comp (cZeroCut_tendsto x)).congr'
      (Eventually.of_forall (fun n => (he n).symm)))

-- @node: ellOneDualIsometry
/-- The [linear isometric embedding of real ℓ¹ into the continuous dual of real
null sequences](goal) sends each sequence to its coordinatewise pairing functional. -/
def ellOneDualIsometry : RealEllOne →ₗᵢ[ℝ] StrongDual ℝ (ZeroAtInftyContinuousMap ℕ ℝ) where
  toFun := ellOnePairing
  map_add' a b := by
    apply cZeroDual_ext_basis
    intro i
    simp [ellOnePairing_basis]
  map_smul' c a := by
    apply cZeroDual_ext_basis
    intro i
    simp [ellOnePairing_basis]
  norm_map' := ellOnePairing_norm

-- @node: ellOneDualIsometry_surjective
/-- [Every continuous linear functional on real null sequences is the
coordinatewise pairing with some real ℓ¹ sequence](goal). -/
lemma ellOneDualIsometry_surjective : Function.Surjective ellOneDualIsometry := by
  intro f
  let a : RealEllOne := ⟨fun i => f (cZeroBasis i), cZeroDual_coeff_mem f⟩
  refine ⟨a, cZeroDual_ext_basis _ f (fun i => ?_)⟩
  exact ellOnePairing_basis a i

end Papers.OaiMetricMarkovCotype

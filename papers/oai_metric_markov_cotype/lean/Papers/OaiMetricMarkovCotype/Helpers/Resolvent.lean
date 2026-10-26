module
public import Papers.OaiMetricMarkovCotype.Helpers.StoppedWalk
public import Papers.OaiMetricMarkovCotype.Helpers.GeometricMoments

/-! # Convergence and harmonicity of the geometric resolvent -/

public section

noncomputable section
open scoped BigOperators
namespace Papers.OaiMetricMarkovCotype

variable {n : ℕ} {𝓑 : Type*} [Fintype 𝓑]

-- @node: isStochastic_pow
/-- If [a matrix is stochastic](hyp:hA), then [each of its nonnegative integer powers is
also stochastic](goal). -/
lemma isStochastic_pow (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsStochastic A)
    (s : ℕ) : IsStochastic (A ^ s) := by
  have h : A ∈ Matrix.rowStochastic ℝ (Fin n) :=
    Matrix.mem_rowStochastic_iff_sum.mpr ⟨hA.nonneg, hA.row_sums⟩
  obtain ⟨hn, hr⟩ := Matrix.mem_rowStochastic_iff_sum.mp (pow_mem h s)
  exact ⟨hn, hr⟩

-- @node: stochastic_average_norm_le
/-- If [a matrix is stochastic](hyp:hA), then [the absolute value of a row-weighted average
of real state values is at most the sum of their absolute values](goal). -/
lemma stochastic_average_norm_le (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : IsStochastic A) (z : Fin n → ℝ) (i : Fin n) :
    ‖∑ j, A i j * z j‖ ≤ ∑ j, ‖z j‖ := by
  have ha (j : Fin n) : A i j ≤ 1 := by
    rw [← hA.row_sums i]
    exact Finset.single_le_sum (fun j _ => hA.nonneg i j) (Finset.mem_univ j)
  calc
    _ ≤ ∑ j, ‖A i j * z j‖ := norm_sum_le _ _
    _ ≤ _ := Finset.sum_le_sum fun j _ => by
      rw [norm_mul, Real.norm_of_nonneg (hA.nonneg i j)]
      exact mul_le_of_le_one_left (norm_nonneg _) (ha j)

-- @node: resolvent_coordinate_summable
/-- For [a strictly positive integer time parameter](hyp:ht) and [a stochastic transition
matrix](hyp:hA), [the series of expected values of any fixed coordinate from any starting
state, discounted by successive powers of the geometric survival probability, converges](goal). -/
lemma resolvent_coordinate_summable (t : ℕ) (ht : GeometricParameterDomain t)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsStochastic A)
    (z : Fin n → 𝓑 → ℝ) (i : Fin n) (B : 𝓑) :
    Summable (fun s : ℕ => geomSurvProb t ht ^ s * ∑ j, (A ^ s) i j * z j B) := by
  have hq := geomSurvProb_pos_lt_one t ht
  simpa using summable_geometric_weighted_bounded hq.1.le hq.2 (by norm_num : (0 : ℝ) ≤ 1)
    (fun s => ∑ j, (A ^ s) i j * z j B) (∑ j, ‖z j B‖)
    (fun s => stochastic_average_norm_le (A ^ s) (isStochastic_pow A hA s) _ i)

-- @node: resolvent_summable
/-- For [a strictly positive integer time parameter](hyp:ht) and [a stochastic transition
matrix](hyp:hA), [the vector series of expected state values discounted by successive
powers of the geometric survival probability converges from every starting state](goal). -/
lemma resolvent_summable (t : ℕ) (ht : GeometricParameterDomain t)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsStochastic A)
    (z : Fin n → 𝓑 → ℝ) (i : Fin n) :
    Summable (fun s : ℕ => geomSurvProb t ht ^ s • ∑ j, (A ^ s) i j • z j) := by
  apply Pi.summable.mpr
  intro B
  simpa using resolvent_coordinate_summable t ht A hA z i B

-- @node: resolvent_apply
/-- For [a strictly positive integer time parameter](hyp:ht) and [a stochastic transition
matrix](hyp:hA), [each coordinate of the resolvent equals the killing probability times
the sum of expected coordinate values discounted by powers of the survival probability](goal). -/
lemma resolvent_apply (t : ℕ) (ht : GeometricParameterDomain t)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsStochastic A)
    (z : Fin n → 𝓑 → ℝ) (i : Fin n) (B : 𝓑) :
    resolvent t ht A z i B =
      geomKillProb t ht * ∑' s : ℕ, geomSurvProb t ht ^ s * ∑ j, (A ^ s) i j * z j B := by
  simp only [resolvent, Pi.smul_apply, smul_eq_mul]
  rw [tsum_apply (resolvent_summable t ht A hA z i)]
  simp

-- @node: resolvent_mem_unitCube
/-- For [a strictly positive integer time parameter](hyp:ht) and [a stochastic transition
matrix](hyp:hA), if [every input vector has all coordinates between zero and one](hyp:hz),
then [the resolvent vector at every state also has all coordinates between zero and one](goal). -/
lemma resolvent_mem_unitCube (t : ℕ) (ht : GeometricParameterDomain t)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsStochastic A)
    (z : Fin n → 𝓑 → ℝ) (hz : ∀ i, z i ∈ unitCube 𝓑) (i : Fin n) :
    resolvent t ht A z i ∈ unitCube 𝓑 := by
  intro B _
  rw [resolvent_apply t ht A hA]
  have hq := geomSurvProb_pos_lt_one t ht
  have hp : 0 < geomKillProb t ht := by unfold geomKillProb; positivity
  have hsum := resolvent_coordinate_summable t ht A hA z i B
  have hgeom := hasSum_geometric_of_lt_one hq.1.le hq.2
  have hbounds (s : ℕ) : 0 ≤ (∑ j, (A ^ s) i j * z j B) ∧
      (∑ j, (A ^ s) i j * z j B) ≤ 1 := by
    have hs := isStochastic_pow A hA s
    constructor
    · exact Finset.sum_nonneg fun j _ => mul_nonneg (hs.nonneg i j) (hz j B (Set.mem_univ B)).1
    · calc
        _ ≤ ∑ j, (A ^ s) i j * 1 := Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (hz j B (Set.mem_univ B)).2 (hs.nonneg i j)
        _ = 1 := by simpa using hs.row_sums i
  constructor
  · exact mul_nonneg hp.le (tsum_nonneg fun s => mul_nonneg (pow_nonneg hq.1.le s) (hbounds s).1)
  · calc
      _ ≤ geomKillProb t ht * ∑' s : ℕ, geomSurvProb t ht ^ s := by
        apply mul_le_mul_of_nonneg_left _ hp.le
        exact hsum.tsum_le_tsum (fun s =>
          mul_le_of_le_one_right (pow_nonneg hq.1.le s) (hbounds s).2) hgeom.summable
      _ = 1 := by
        rw [hgeom.tsum_eq]
        have heq : 1 - geomSurvProb t ht = geomKillProb t ht := by simp [geomSurvProb]
        rw [heq, mul_inv_cancel₀ hp.ne']

-- @node: resolvent_fixed_point
/-- For [a strictly positive integer time parameter](hyp:ht) and [a stochastic transition
matrix](hyp:hA), [the resolvent at each state equals the killing probability times the
input there plus the survival probability times the transition average of the resolvent](goal). -/
lemma resolvent_fixed_point (t : ℕ) (ht : GeometricParameterDomain t)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsStochastic A)
    (z : Fin n → 𝓑 → ℝ) (i : Fin n) :
    resolvent t ht A z i = geomKillProb t ht • z i +
      geomSurvProb t ht • ∑ j, A i j • resolvent t ht A z j := by
  ext B
  let p := geomKillProb t ht
  let q := geomSurvProb t ht
  let v : ℕ → Fin n → ℝ := fun s j => ∑ k, (A ^ s) j k * z k B
  have hs (j : Fin n) : Summable (fun s => q ^ s * v s j) :=
    resolvent_coordinate_summable t ht A hA z j B
  have hv0 : v 0 i = z i B := by simp [v, Matrix.one_apply]
  have hv (s : ℕ) : v (s + 1) i = ∑ j, A i j * v s j := by
    simp only [v, pow_succ', Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have htail : (∑' s : ℕ, q ^ (s + 1) * v (s + 1) i) =
      q * ∑ j, A i j * ∑' s : ℕ, q ^ s * v s j := by
    calc
      _ = q * ∑' s : ℕ, ∑ j, A i j * (q ^ s * v s j) := by
        rw [← tsum_mul_left]
        apply tsum_congr
        intro s
        rw [hv, pow_succ, Finset.mul_sum]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by
        rw [Summable.tsum_finsetSum (fun j _ => (hs j).mul_left (A i j))]
        simp_rw [tsum_mul_left]
  have hshift := (hs i).tsum_eq_zero_add
  rw [pow_zero, one_mul, hv0, htail] at hshift
  simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  simp_rw [resolvent_apply t ht A hA]
  change p * (∑' s : ℕ, q ^ s * v s i) = p * z i B +
    q * ∑ j, A i j * (p * ∑' s : ℕ, q ^ s * v s j)
  rw [hshift, mul_add]
  simp only [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

end Papers.OaiMetricMarkovCotype

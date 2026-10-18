module
public import Papers.TbsNeuralCausalPi.Helpers.ApproximationStep
public import Papers.TbsNeuralCausalPi.Helpers.ApproximationLatents
public import Mathlib.Probability.Kernel.Composition.MeasureComp
/-! # Maximal coupling of categorical mechanisms

The common mass is coupled on equal labels. The residual masses have disjoint
supports and are coupled by their normalized product, giving the half-L1 cost
used in the categorical history and descendant propagation arguments.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
open scoped NNReal ENNReal

/-- For [a probability vector p](hyp:hp) and [a probability vector q](hyp:hq),
[removing their coordinatewise common mass leaves equal residual totals, each
equal to half the sum of their absolute coordinate differences](goal). -/
-- @node: categorical_residual_mass
lemma categorical_residual_mass {k : ℕ} {p q : Fin k → ℝ}
    (hp : p ∈ probabilitySimplex k) (hq : q ∈ probabilitySimplex k) :
    (∑ i, (p i - min (p i) (q i))) =
      (∑ i, (q i - min (p i) (q i))) ∧
    (∑ i, (p i - min (p i) (q i))) = (∑ i, |p i - q i|) / 2 := by
  have heq : (∑ i, (p i - min (p i) (q i))) =
      (∑ i, (q i - min (p i) (q i))) := by
    simp only [Finset.sum_sub_distrib, hp.2, hq.2]
  refine ⟨heq, ?_⟩
  have habs : ∀ i, |p i - q i| =
      (p i - min (p i) (q i)) + (q i - min (p i) (q i)) := by
    intro i
    rcases le_total (p i) (q i) with h | h
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
      ring
    · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
      ring
  simp_rw [habs, Finset.sum_add_distrib]
  rw [← heq]
  ring

/-- For [weight vectors p and q](hyp:p,q), [row label i and column label j](hyp:i,j),
the [coupling weight](goal) is the common mass on the diagonal plus the product of
the two residual masses divided by the total residual mass of p.

Division by zero contributes zero when the residual total vanishes. -/
-- @node: categoricalCouplingWeights
noncomputable def categoricalCouplingWeights {k : ℕ} (p q : Fin k → ℝ) (i j : Fin k) : ℝ :=
  (if i = j then min (p i) (q i) else 0) +
    (p i - min (p i) (q i)) * (q j - min (p j) (q j)) /
      (∑ l, (p l - min (p l) (q l)))

/-- For [a probability vector p](hyp:hp) and [a probability vector q](hyp:hq),
[the explicit coupling weights are nonnegative, have row sums p and column sums q,
and have off-diagonal mass equal to half the sum of absolute coordinate differences](goal). -/
-- @node: categoricalCouplingWeights_properties
lemma categoricalCouplingWeights_properties {k : ℕ} {p q : Fin k → ℝ}
    (hp : p ∈ probabilitySimplex k) (hq : q ∈ probabilitySimplex k) :
    (∀ i j, 0 ≤ categoricalCouplingWeights p q i j) ∧
      (∀ i, ∑ j, categoricalCouplingWeights p q i j = p i) ∧
      (∀ j, ∑ i, categoricalCouplingWeights p q i j = q j) ∧
      (∑ i, ∑ j, if i = j then 0 else categoricalCouplingWeights p q i j) =
        (∑ i, |p i - q i|) / 2 := by
  classical
  let a : Fin k → ℝ := fun i => p i - min (p i) (q i)
  let b : Fin k → ℝ := fun i => q i - min (p i) (q i)
  let t := ∑ i, a i
  have ha : ∀ i, 0 ≤ a i := fun i => sub_nonneg.mpr (min_le_left _ _)
  have hb : ∀ i, 0 ≤ b i := fun i => sub_nonneg.mpr (min_le_right _ _)
  have ht : 0 ≤ t := Finset.sum_nonneg fun i _ => ha i
  have hmass := categorical_residual_mass hp hq
  have hbt : ∑ i, b i = t := hmass.1.symm
  have htabs : t = (∑ i, |p i - q i|) / 2 := hmass.2
  have hab : ∀ i, a i * b i = 0 := by
    intro i
    rcases le_total (p i) (q i) with h | h
    · simp [a, b, min_eq_left h]
    · simp [a, b, min_eq_right h]
  have hrow : ∀ i, a i * t / t = a i := by
    intro i
    by_cases hz : t = 0
    · have hai : a i = 0 := by
        have hle : a i ≤ t := Finset.single_le_sum (fun j _ => ha j) (Finset.mem_univ i)
        exact le_antisymm (hz ▸ hle) (ha i)
      simp [hz, hai]
    · exact mul_div_cancel_right₀ (a i) hz
  have hcol : ∀ i, t * b i / t = b i := by
    intro i
    by_cases hz : t = 0
    · have hbi : b i = 0 := by
        have hle : b i ≤ ∑ j, b j :=
          Finset.single_le_sum (fun j _ => hb j) (Finset.mem_univ i)
        rw [hbt, hz] at hle
        exact le_antisymm hle (hb i)
      simp [hz, hbi]
    · rw [mul_comm, mul_div_cancel_right₀ _ hz]
  let r : Fin k → Fin k → ℝ := fun i j =>
    (if i = j then min (p i) (q i) else 0) + a i * b j / t
  have hr : ∀ i j, 0 ≤ r i j := by
    intro i j
    apply add_nonneg
    · split_ifs
      · exact le_min (hp.1 i) (hq.1 i)
      · exact le_rfl
    · exact div_nonneg (mul_nonneg (ha i) (hb j)) ht
  have hrrow : ∀ i, ∑ j, r i j = p i := by
    intro i
    simp only [r, Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum]
    rw [hbt, hrow]
    simp [a]
  have hrcol : ∀ j, ∑ i, r i j = q j := by
    intro j
    simp only [r, Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul]
    rw [hcol]
    simp [b]
  change (∀ i j, 0 ≤ r i j) ∧ (∀ i, ∑ j, r i j = p i) ∧
    (∀ j, ∑ i, r i j = q j) ∧ _
  refine ⟨hr, hrrow, hrcol, ?_⟩
  have hoff : ∀ i j, (if i = j then 0 else r i j) = a i * b j / t := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp [hab]
    · simp [hij, r]
  change (∑ i, ∑ j, if i = j then 0 else r i j) = _
  simp_rw [hoff, ← Finset.sum_div, ← Finset.mul_sum, hbt]
  rw [Finset.sum_div]
  simpa only [hrow] using htabs

/-- For [a probability vector p](hyp:hp) and [a probability vector q](hyp:hq),
[there exists a nonnegative coupling matrix with row sums p, column sums q, and
disagreement mass equal to half the sum of absolute coordinate differences](goal). -/
-- @node: exists_categorical_maximal_coupling
lemma exists_categorical_maximal_coupling {k : ℕ} {p q : Fin k → ℝ}
    (hp : p ∈ probabilitySimplex k) (hq : q ∈ probabilitySimplex k) :
    ∃ r : Fin k → Fin k → ℝ,
      (∀ i j, 0 ≤ r i j) ∧ (∀ i, ∑ j, r i j = p i) ∧
      (∀ j, ∑ i, r i j = q j) ∧
      (∑ i, ∑ j, if i = j then 0 else r i j) = (∑ i, |p i - q i|) / 2 :=
  ⟨categoricalCouplingWeights p q, categoricalCouplingWeights_properties hp hq⟩

/-- If [each coordinate of p varies measurably with the input](hyp:hp) and
[each coordinate of q does too](hyp:hq), then [every entry of their explicit
coupling matrix varies measurably with the input](goal). -/
-- @node: categoricalCouplingWeights_measurable
@[fun_prop] lemma categoricalCouplingWeights_measurable
    {X : Type*} [MeasurableSpace X] {k : ℕ} (p q : X → Fin k → ℝ)
    (hp : ∀ i, Measurable (fun x => p x i))
    (hq : ∀ i, Measurable (fun x => q x i)) (i j : Fin k) :
    Measurable (fun x => categoricalCouplingWeights (p x) (q x) i j) := by
  unfold categoricalCouplingWeights
  split_ifs <;> fun_prop

/-- Given [a probability vector p](hyp:hp), [a probability vector q](hyp:hq),
a label cost [equal to zero on matching labels](hyp:hdiag) and [bounded above by D
for every pair](hyp:hcost), [there exists a nonnegative coupling with marginals p
and q whose expected cost is at most D times half the sum of absolute coordinate
differences](goal). -/
-- @node: categorical_maximal_coupling_cost_le
lemma categorical_maximal_coupling_cost_le {k : ℕ} {p q : Fin k → ℝ}
    (hp : p ∈ probabilitySimplex k) (hq : q ∈ probabilitySimplex k)
    (cost : Fin k → Fin k → ℝ) (D : ℝ)
    (hdiag : ∀ i, cost i i = 0) (hcost : ∀ i j, cost i j ≤ D) :
    ∃ r : Fin k → Fin k → ℝ,
      (∀ i j, 0 ≤ r i j) ∧ (∀ i, ∑ j, r i j = p i) ∧
      (∀ j, ∑ i, r i j = q j) ∧
      (∑ i, ∑ j, r i j * cost i j) ≤ D / 2 * ∑ i, |p i - q i| := by
  classical
  obtain ⟨r, hr, hrow, hcol, hoff⟩ := exists_categorical_maximal_coupling hp hq
  refine ⟨r, hr, hrow, hcol, ?_⟩
  calc
    (∑ i, ∑ j, r i j * cost i j) ≤
        ∑ i, ∑ j, D * (if i = j then 0 else r i j) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      by_cases hij : i = j
      · subst j
        simp [hdiag]
      · simp only [hij, ↓reduceIte]
        exact (mul_le_mul_of_nonneg_left (hcost i j) (hr i j)).trans_eq (mul_comm _ _)
    _ = D * ((∑ i, |p i - q i|) / 2) := by
      simp_rw [← Finset.mul_sum]
      rw [hoff]
    _ = _ := by ring

/-- For [a probability vector p](hyp:hp) and [a probability vector q](hyp:hq),
if [all pairs of encoded labels are at distance at most D](hyp:hdiam), then
[the Wasserstein distance between the encoded categorical laws is at most D
times half the sum of absolute coordinate differences](goal). -/
-- @node: categorical_wasserstein_half_l1_le
lemma categorical_wasserstein_half_l1_le
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {k : ℕ} {p q : Fin k → ℝ}
    (hp : p ∈ probabilitySimplex k) (hq : q ∈ probabilitySimplex k)
    (v : Fin k → X) (D : ℝ) (hdiam : ∀ i j, dist (v i) (v j) ≤ D) :
    wasserstein1 (∑ i, ENNReal.ofReal (p i) • Measure.dirac (v i))
      (∑ j, ENNReal.ofReal (q j) • Measure.dirac (v j)) ≤
      ENNReal.ofReal (D / 2 * ∑ i, |p i - q i|) := by
  classical
  obtain ⟨r, hr, hrow, hcol, hcost⟩ := categorical_maximal_coupling_cost_le hp hq
    (fun i j => dist (v i) (v j)) D (fun _ => dist_self _) hdiam
  let rho : Measure (X × X) :=
    ∑ i, ∑ j, ENNReal.ofReal (r i j) • (Measure.dirac (v i)).prod (Measure.dirac (v j))
  have hc := Toolkit.Foundations.MeasureTheory.finite_product_mixture_coupling
    (fun i => Measure.dirac (v i)) (fun j => Measure.dirac (v j))
    (fun _ => inferInstance) (fun _ => inferInstance)
    (fun i => ENNReal.ofReal (p i)) (fun j => ENNReal.ofReal (q j))
    (fun i j => ENNReal.ofReal (r i j))
    (by rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hp.1 i), hp.2]; simp)
    (fun i => by rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hr i j), hrow])
    (fun j => by rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hr i j), hcol])
  calc
    wasserstein1 _ _ ≤ ∫⁻ z, edist z.1 z.2 ∂rho :=
      (wasserstein1_eq_couplings _ _).trans_le
        (iInf_le_of_le ⟨rho, hc.isProbabilityMeasure, hc.map_fst, hc.map_snd⟩ le_rfl)
    _ = ENNReal.ofReal (∑ i, ∑ j, r i j * dist (v i) (v j)) := by
      simp only [rho, lintegral_finsetSum_measure, lintegral_smul_measure]
      simp only [Measure.prod_dirac, Measure.map_dirac, lintegral_dirac,
        smul_eq_mul, edist_dist]
      simp_rw [← ENNReal.ofReal_mul (hr _ _)]
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ =>
        Finset.sum_nonneg (fun j _ => mul_nonneg (hr i j) dist_nonneg))]
      congr 1
      funext i
      exact (ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (hr i j) dist_nonneg)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hcost

/-- [The distance between any two one-based numeric labels among k categories
is at most k minus one, with the subtraction truncated at zero](goal). -/
-- @node: categorical_label_diameter_le
lemma categorical_label_diameter_le {k : ℕ} (i j : Fin k) :
    dist (i.val + 1 : ℝ) (j.val + 1 : ℝ) ≤ (k - 1 : ℕ) := by
  rw [Real.dist_eq, abs_le]
  have hi : i.val ≤ k - 1 := by omega
  have hj : j.val ≤ k - 1 := by omega
  have hi' : (i.val : ℝ) ≤ (k - 1 : ℕ) := by exact_mod_cast hi
  have hj' : (j.val : ℝ) ≤ (k - 1 : ℕ) := by exact_mod_cast hj
  constructor <;> linarith [Nat.cast_nonneg (α := ℝ) i.val, Nat.cast_nonneg (α := ℝ) j.val]

/-- For [a probability vector p](hyp:hp) and [a probability vector q](hyp:hq),
if [every absolute coordinate difference is at most e](hyp:he), then [the
Wasserstein distance between their one-based numeric label laws is at most
k times k minus one times e divided by two](goal). -/
-- @node: categorical_wasserstein_sup_error_le
lemma categorical_wasserstein_sup_error_le {k : ℕ} {p q : Fin k → ℝ}
    (hp : p ∈ probabilitySimplex k) (hq : q ∈ probabilitySimplex k)
    {e : ℝ} (he : ∀ j, |p j - q j| ≤ e) :
    wasserstein1 (∑ i, ENNReal.ofReal (p i) • Measure.dirac (i.val + 1 : ℝ))
      (∑ j, ENNReal.ofReal (q j) • Measure.dirac (j.val + 1 : ℝ)) ≤
      ENNReal.ofReal ((k : ℝ) * (k - 1 : ℕ) / 2 * e) := by
  calc
    _ ≤ ENNReal.ofReal (((k - 1 : ℕ) : ℝ) / 2 * ∑ i, |p i - q i|) :=
      categorical_wasserstein_half_l1_le hp hq _ _ categorical_label_diameter_le
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ ((k - 1 : ℕ) : ℝ) / 2 * ∑ _i : Fin k, e := by
          gcongr
          exact he _
        _ = _ := by simp; ring

/-- For [a probability vector p](hyp:hp) and [a probability vector q](hyp:hq),
if [their one-norm distance is at most L times the distance between x and y](hyp:hprop),
then [the Wasserstein distance between their one-based numeric label laws is at
most half of k minus one times L times the distance between x and y](goal). -/
-- @node: categorical_wasserstein_propensity_le
lemma categorical_wasserstein_propensity_le
    {X : Type*} [PseudoMetricSpace X] {k : ℕ} {p q : L1Vec k}
    (hp : p.ofLp ∈ probabilitySimplex k) (hq : q.ofLp ∈ probabilitySimplex k)
    {x y : X} {L : ℝ} (hprop : dist p q ≤ L * dist x y) :
    wasserstein1 (∑ i, ENNReal.ofReal (p.ofLp i) • Measure.dirac (i.val + 1 : ℝ))
      (∑ j, ENNReal.ofReal (q.ofLp j) • Measure.dirac (j.val + 1 : ℝ)) ≤
      ENNReal.ofReal (((k - 1 : ℕ) : ℝ) / 2 * L * dist x y) := by
  calc
    _ ≤ ENNReal.ofReal (((k - 1 : ℕ) : ℝ) / 2 * ∑ i, |p.ofLp i - q.ofLp i|) :=
      categorical_wasserstein_half_l1_le hp hq _ _ categorical_label_diameter_le
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [PiLp.dist_eq_of_L1, Real.dist_eq] using hprop

/-- For [a probability vector p](hyp:hp) and [a probability vector q](hyp:hq),
suppose [the distance from the first encoding of label i to the second encoding
of label j is at most H, plus D when the labels differ](hyp:hcost). Then [the
Wasserstein distance between the two encoded laws is at most H plus D times half
the sum of absolute coordinate differences](goal). -/
-- @node: categorical_wasserstein_cross_history_le
lemma categorical_wasserstein_cross_history_le
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {k : ℕ} {p q : Fin k → ℝ}
    (hp : p ∈ probabilitySimplex k) (hq : q ∈ probabilitySimplex k)
    (v w : Fin k → X) (H D : ℝ)
    (hcost : ∀ i j, dist (v i) (w j) ≤ H + if i = j then 0 else D) :
    wasserstein1 (∑ i, ENNReal.ofReal (p i) • Measure.dirac (v i))
      (∑ j, ENNReal.ofReal (q j) • Measure.dirac (w j)) ≤
      ENNReal.ofReal (H + D / 2 * ∑ i, |p i - q i|) := by
  classical
  obtain ⟨r, hr, hrow, hcol, hoff⟩ := exists_categorical_maximal_coupling hp hq
  have hmass : (∑ i, ∑ j, r i j) = 1 := by simp_rw [hrow]; exact hp.2
  have hbound : (∑ i, ∑ j, r i j * dist (v i) (w j)) ≤
      H + D / 2 * ∑ i, |p i - q i| := by
    calc
      _ ≤ ∑ i, ∑ j, r i j * (H + if i = j then 0 else D) := by
        apply Finset.sum_le_sum
        intro i _
        exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hcost i j) (hr i j)
      _ = H * (∑ i, ∑ j, r i j) + D * (∑ i, ∑ j, if i = j then 0 else r i j) := by
        simp_rw [mul_add, Finset.sum_add_distrib]
        congr 1
        · simp_rw [← Finset.sum_mul]
          ring
        · simp_rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          split_ifs <;> ring
      _ = _ := by rw [hmass, hoff]; ring
  let rho : Measure (X × X) :=
    ∑ i, ∑ j, ENNReal.ofReal (r i j) • (Measure.dirac (v i)).prod (Measure.dirac (w j))
  have hc := Toolkit.Foundations.MeasureTheory.finite_product_mixture_coupling
    (fun i => Measure.dirac (v i)) (fun j => Measure.dirac (w j))
    (fun _ => inferInstance) (fun _ => inferInstance)
    (fun i => ENNReal.ofReal (p i)) (fun j => ENNReal.ofReal (q j))
    (fun i j => ENNReal.ofReal (r i j))
    (by rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hp.1 i), hp.2]; simp)
    (fun i => by rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hr i j), hrow])
    (fun j => by rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hr i j), hcol])
  calc
    wasserstein1 _ _ ≤ ∫⁻ z, edist z.1 z.2 ∂rho :=
      (wasserstein1_eq_couplings _ _).trans_le
        (iInf_le_of_le ⟨rho, hc.isProbabilityMeasure, hc.map_fst, hc.map_snd⟩ le_rfl)
    _ = ENNReal.ofReal (∑ i, ∑ j, r i j * dist (v i) (w j)) := by
      simp only [rho, lintegral_finsetSum_measure, lintegral_smul_measure]
      simp only [Measure.prod_dirac, Measure.map_dirac, lintegral_dirac,
        smul_eq_mul, edist_dist]
      simp_rw [← ENNReal.ofReal_mul (hr _ _)]
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ =>
        Finset.sum_nonneg (fun j _ => mul_nonneg (hr i j) dist_nonneg))]
      congr 1
      funext i
      exact (ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (hr i j) dist_nonneg)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hbound

/-- For [a probability vector p](hyp:hp) and [a probability vector q](hyp:hq),
[the Wasserstein distance between histories x and y with respective one-based
categorical labels appended is at most the history distance plus half of k minus
one times the one-norm distance between p and q](goal). -/
-- @node: categorical_wasserstein_appended_history_le
lemma categorical_wasserstein_appended_history_le
    {h k : ℕ} (x y : L1Vec h) {p q : L1Vec k}
    (hp : p.ofLp ∈ probabilitySimplex k) (hq : q.ofLp ∈ probabilitySimplex k) :
    wasserstein1
      (∑ i : Fin k, ENNReal.ofReal (p.ofLp i) • Measure.dirac
        (WithLp.toLp 1 (Sum.elim x.ofLp (fun _ : Unit => (i.val + 1 : ℝ)))))
      (∑ j : Fin k, ENNReal.ofReal (q.ofLp j) • Measure.dirac
        (WithLp.toLp 1 (Sum.elim y.ofLp (fun _ : Unit => (j.val + 1 : ℝ))))) ≤
      ENNReal.ofReal (dist x y + ((k - 1 : ℕ) : ℝ) / 2 * dist p q) := by
  have hc := categorical_wasserstein_cross_history_le hp hq
    (fun i => WithLp.toLp 1 (Sum.elim x.ofLp (fun _ : Unit => (i.val + 1 : ℝ))))
    (fun j => WithLp.toLp 1 (Sum.elim y.ofLp (fun _ : Unit => (j.val + 1 : ℝ))))
    (dist x y) (k - 1 : ℕ) (by
      intro i j
      simp only [PiLp.dist_eq_of_L1, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
        Fintype.sum_unique]
      by_cases hij : i = j
      · simp [hij]
      · simp only [hij, ↓reduceIte]
        exact add_le_add le_rfl (categorical_label_diameter_le i j))
  simpa only [PiLp.dist_eq_of_L1, Real.dist_eq] using hc

/-- Suppose [p assigns probability vectors on S](hyp:hp), [q assigns probability
vectors on S](hyp:hq), and p is [Lipschitz on S](hyp:hLip) with [nonnegative
constant L](hyp:L). For [x in S](hyp:hx) and [y in S](hyp:hy), if [each coordinate
of p and q differs by at most e at y](hyp:herr), then [the Wasserstein distance
between x with a label drawn from p at x and y with a label drawn from q at y is
at most one plus half of k minus one times L, multiplied by the history distance,
plus k times k minus one times e divided by two](goal). -/
-- @node: categorical_wasserstein_history_perturbation_le
lemma categorical_wasserstein_history_perturbation_le
    {h k : ℕ} (S : Set (L1Vec h)) (p q : L1Vec h → L1Vec k)
    (hp : ∀ x ∈ S, (p x).ofLp ∈ probabilitySimplex k)
    (hq : ∀ x ∈ S, (q x).ofLp ∈ probabilitySimplex k)
    (L : ℝ≥0) (hLip : LipschitzOnWith L p S)
    {x y : L1Vec h} (hx : x ∈ S) (hy : y ∈ S)
    {e : ℝ} (herr : ∀ j, |(p y).ofLp j - (q y).ofLp j| ≤ e) :
    wasserstein1
      (∑ i : Fin k, ENNReal.ofReal ((p x).ofLp i) • Measure.dirac
        (WithLp.toLp 1 (Sum.elim x.ofLp (fun _ : Unit => (i.val + 1 : ℝ)))))
      (∑ j : Fin k, ENNReal.ofReal ((q y).ofLp j) • Measure.dirac
        (WithLp.toLp 1 (Sum.elim y.ofLp (fun _ : Unit => (j.val + 1 : ℝ))))) ≤
      ENNReal.ofReal ((1 + ((k - 1 : ℕ) : ℝ) * L / 2) * dist x y +
        (k : ℝ) * (k - 1 : ℕ) / 2 * e) := by
  have hlocal : dist (p y) (q y) ≤ (k : ℝ) * e := by
    rw [PiLp.dist_eq_of_L1]
    simp only [Real.dist_eq]
    calc
      _ ≤ ∑ _j : Fin k, e := Finset.sum_le_sum fun j _ => herr j
      _ = _ := by simp
  have hprop : dist (p x) (q y) ≤ (L : ℝ) * dist x y + (k : ℝ) * e :=
    (dist_triangle (p x) (p y) (q y)).trans
      (add_le_add (hLip.dist_le_mul x hx y hy) hlocal)
  calc
    _ ≤ ENNReal.ofReal (dist x y + ((k - 1 : ℕ) : ℝ) / 2 * dist (p x) (q y)) :=
      categorical_wasserstein_appended_history_le x y (hp x hx) (hq y hy)
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ dist x y + ((k - 1 : ℕ) : ℝ) / 2 *
            ((L : ℝ) * dist x y + (k : ℝ) * e) := by gcongr
        _ = _ := by ring

/-- Suppose [p assigns probability vectors on S](hyp:hp), [q assigns probability
vectors on S](hyp:hq), and p is [Lipschitz on S](hyp:hLip) with [nonnegative
constant L](hyp:L). For [x in S](hyp:hx) and [y in S](hyp:hy), [the Wasserstein
distance between the histories with respective labels drawn from p at x and q
at y is at most one plus half of k minus one times L, multiplied by the history
distance, plus k times k minus one divided by two times the supremum coordinate
error between p and q on S](goal).

The supremum error may be infinite. -/
-- @node: categorical_wasserstein_history_supDistOn_le
lemma categorical_wasserstein_history_supDistOn_le
    {h k : ℕ} (S : Set (L1Vec h)) (p q : L1Vec h → L1Vec k)
    (hp : ∀ x ∈ S, (p x).ofLp ∈ probabilitySimplex k)
    (hq : ∀ x ∈ S, (q x).ofLp ∈ probabilitySimplex k)
    (L : ℝ≥0) (hLip : LipschitzOnWith L p S)
    {x y : L1Vec h} (hx : x ∈ S) (hy : y ∈ S) :
    wasserstein1
      (∑ i : Fin k, ENNReal.ofReal ((p x).ofLp i) • Measure.dirac
        (WithLp.toLp 1 (Sum.elim x.ofLp (fun _ : Unit => (i.val + 1 : ℝ)))))
      (∑ j : Fin k, ENNReal.ofReal ((q y).ofLp j) • Measure.dirac
        (WithLp.toLp 1 (Sum.elim y.ofLp (fun _ : Unit => (j.val + 1 : ℝ))))) ≤
      ENNReal.ofReal (1 + ((k - 1 : ℕ) : ℝ) * L / 2) * edist x y +
        ENNReal.ofReal ((k : ℝ) * (k - 1 : ℕ) / 2) * supDistOn S p q := by
  let e : ℝ := ‖(p y - q y).ofLp‖
  have he : 0 ≤ e := norm_nonneg _
  have herr : ∀ j, |(p y).ofLp j - (q y).ofLp j| ≤ e := by
    intro j
    exact norm_le_pi_norm ((p y - q y).ofLp) j
  have hsup : ENNReal.ofReal e ≤ supDistOn S p q := by
    exact le_iSup_of_le (⟨y, hy⟩ : S) le_rfl
  calc
    _ ≤ ENNReal.ofReal ((1 + ((k - 1 : ℕ) : ℝ) * L / 2) * dist x y +
        (k : ℝ) * (k - 1 : ℕ) / 2 * e) :=
      categorical_wasserstein_history_perturbation_le S p q hp hq L hLip hx hy herr
    _ = ENNReal.ofReal (1 + ((k - 1 : ℕ) : ℝ) * L / 2) * edist x y +
        ENNReal.ofReal ((k : ℝ) * (k - 1 : ℕ) / 2) * ENNReal.ofReal e := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), edist_dist]
    _ ≤ _ := by gcongr

/-- For [input-dependent weight vectors p and q](hyp:p,q) with [measurable
coordinates of p](hyp:hp) and [measurable coordinates of q](hyp:hq), the
[categorical coupling kernel](goal) places the explicit coupling weight on each
ordered pair of labels at each input. -/
-- @node: categoricalCouplingKernel
noncomputable def categoricalCouplingKernel
    {X : Type*} [MeasurableSpace X] {k : ℕ} (p q : X → Fin k → ℝ)
    (hp : ∀ i, Measurable (fun x => p x i))
    (hq : ∀ i, Measurable (fun x => q x i)) :
    ProbabilityTheory.Kernel X (Fin k × Fin k) where
  toFun x := ∑ i, ∑ j, ENNReal.ofReal (categoricalCouplingWeights (p x) (q x) i j) •
    Measure.dirac (i,j)
  measurable' := by fun_prop

/-- If [p has measurable coordinates](hyp:hp), [q has measurable coordinates](hyp:hq),
[p is a probability vector at every input](hyp:hps), and [q is a probability
vector at every input](hyp:hqs), then [the explicit kernel at each input is a
probability coupling of the corresponding categorical laws](goal). -/
-- @node: categoricalCouplingKernel_coupling
lemma categoricalCouplingKernel_coupling
    {X : Type*} [MeasurableSpace X] {k : ℕ} (p q : X → Fin k → ℝ)
    (hp : ∀ i, Measurable (fun x => p x i))
    (hq : ∀ i, Measurable (fun x => q x i))
    (hps : ∀ x, p x ∈ probabilitySimplex k)
    (hqs : ∀ x, q x ∈ probabilitySimplex k) (x : X) :
    categoricalCouplingKernel p q hp hq x ∈ couplings
      (∑ i, ENNReal.ofReal (p x i) • Measure.dirac i)
      (∑ j, ENNReal.ofReal (q x j) • Measure.dirac j) := by
  classical
  obtain ⟨hr, hrow, hcol, hoff⟩ := categoricalCouplingWeights_properties (hps x) (hqs x)
  have hc := Toolkit.Foundations.MeasureTheory.finite_product_mixture_coupling
    (fun i : Fin k => Measure.dirac i) (fun j : Fin k => Measure.dirac j)
    (fun _ => inferInstance) (fun _ => inferInstance)
    (fun i => ENNReal.ofReal (p x i)) (fun j => ENNReal.ofReal (q x j))
    (fun i j => ENNReal.ofReal (categoricalCouplingWeights (p x) (q x) i j))
    (by rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => (hps x).1 i), (hps x).2]; simp)
    (fun i => by rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hr i j), hrow])
    (fun j => by rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hr i j), hcol])
  have heq : categoricalCouplingKernel p q hp hq x =
      ∑ i, ∑ j, ENNReal.ofReal (categoricalCouplingWeights (p x) (q x) i j) •
        (Measure.dirac i).prod (Measure.dirac j) := by
    simp [categoricalCouplingKernel, Measure.prod_dirac]
  rw [heq]
  exact ⟨hc.isProbabilityMeasure, hc.map_fst, hc.map_snd⟩

/-- If [p has measurable coordinates](hyp:hp), [q has measurable coordinates](hyp:hq),
[p is a probability vector at every input](hyp:hps), and [q is a probability
vector at every input](hyp:hqs), then [the disagreement probability under the
explicit coupling kernel equals half the sum of absolute coordinate differences
between p and q at that input](goal). -/
-- @node: categoricalCouplingKernel_disagreement
lemma categoricalCouplingKernel_disagreement
    {X : Type*} [MeasurableSpace X] {k : ℕ} (p q : X → Fin k → ℝ)
    (hp : ∀ i, Measurable (fun x => p x i))
    (hq : ∀ i, Measurable (fun x => q x i))
    (hps : ∀ x, p x ∈ probabilitySimplex k)
    (hqs : ∀ x, q x ∈ probabilitySimplex k) (x : X) :
    (∫⁻ z, (if z.1 = z.2 then 0 else 1 : ℝ≥0∞)
      ∂categoricalCouplingKernel p q hp hq x) =
        ENNReal.ofReal ((∑ i, |p x i - q x i|) / 2) := by
  classical
  obtain ⟨hr, hrow, hcol, hoff⟩ := categoricalCouplingWeights_properties (hps x) (hqs x)
  have hn (i j : Fin k) :
      0 ≤ (if i = j then 0 else categoricalCouplingWeights (p x) (q x) i j) := by
    split_ifs
    · exact le_rfl
    · exact hr i j
  rw [← hoff]
  simp only [categoricalCouplingKernel, ProbabilityTheory.Kernel.coe_mk,
    lintegral_finsetSum_measure, lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hn i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => hn i j)]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

end Papers.TbsNeuralCausalPi

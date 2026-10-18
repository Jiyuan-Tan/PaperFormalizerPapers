module
public import Papers.TbsNeuralCausalPi.Setup.CitedResults
/-! # Square-root transfer of empirical covers

The squared-loss reduction in the uniform empirical Wasserstein proof uses
square roots of normalized test functions. Cauchy--Schwarz changes a vector
cover at radius `2 * d * K * m * r^2` into an averaged scalar cover at radius `r`.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
open scoped ENNReal NNReal
noncomputable section

/-- If [a is nonnegative](hyp:ha) and [b is nonnegative](hyp:hb),
[the squared difference of their square roots is at most their absolute
difference](goal). -/
-- @node: empirical_sqrt_sub_sq_le
lemma empirical_sqrt_sub_sq_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.sqrt a - Real.sqrt b)^2 ≤ |a-b| := by
  have hsa := Real.sq_sqrt ha
  have hsb := Real.sq_sqrt hb
  have hna := Real.sqrt_nonneg a
  have hnb := Real.sqrt_nonneg b
  rcases le_total a b with hab | hba
  · rw [abs_of_nonpos (sub_nonpos.mpr hab)]
    have hs := Real.sqrt_le_sqrt hab
    nlinarith [mul_nonneg hna (sub_nonneg.mpr hs)]
  · rw [abs_of_nonneg (sub_nonneg.mpr hba)]
    have hs := Real.sqrt_le_sqrt hba
    nlinarith [mul_nonneg hnb (sub_nonneg.mpr hs)]

/-- For [a positive number of observations](hyp:hm), if [every entry of u
is nonnegative](hyp:hu) and [every entry of v is nonnegative](hyp:hv),
[the average absolute difference of their square roots is at most the
square root of their average absolute difference](goal). -/
-- @node: averagedL1_sqrt_le
lemma averagedL1_sqrt_le {m : ℕ} (hm : 0 < m) (u v : Fin m → ℝ)
    (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i) :
    averagedL1 (fun i => Real.sqrt (u i)) (fun i => Real.sqrt (v i)) ≤
      Real.sqrt (averagedL1 u v) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (R := ℝ) (r := fun i : Fin m => |Real.sqrt (u i) - Real.sqrt (v i)|)
    (f := fun _ => 1) (g := fun i => |u i - v i|) Finset.univ
    (by intros; positivity) (by intros; positivity)
    (by intro i _; simpa only [sq_abs, one_mul] using empirical_sqrt_sub_sq_le (hu i) (hv i))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one] at hcs
  apply Real.le_sqrt_of_sq_le
  unfold averagedL1
  calc
    _ = ((m : ℝ)⁻¹)^2 * (∑ i, |Real.sqrt (u i) - Real.sqrt (v i)|)^2 := by ring
    _ ≤ ((m : ℝ)⁻¹)^2 * ((m : ℝ) * ∑ i, |u i - v i|) :=
      mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
    _ = _ := by field_simp

/-- Suppose [the sample size m is positive](hyp:hm), [R is positive](hyp:hR),
[the test h is one-Lipschitz on S](hyp:hLip), [its absolute value on S is
bounded by R](hyp:hbound), and [all entries of u](hyp:hu) and
[all entries of v](hyp:hv) lie in S. Then [the average absolute difference
between the square roots of (h(u) + R)/(2R) and (h(v) + R)/(2R) is at most
the square root of the sum of paired distances divided by 2Rm](goal). -/
-- @node: normalized_test_sqrt_empirical_dist_le
lemma normalized_test_sqrt_empirical_dist_le {E : Type*} [PseudoMetricSpace E]
    {m : ℕ} (hm : 0 < m) {S : Set E} {h : E → ℝ} {R : ℝ} (hR : 0 < R)
    (hLip : ∀ x ∈ S, ∀ y ∈ S, |h x - h y| ≤ dist x y)
    (hbound : ∀ x ∈ S, |h x| ≤ R) (u v : Fin m → E)
    (hu : ∀ i, u i ∈ S) (hv : ∀ i, v i ∈ S) :
    averagedL1 (fun i => Real.sqrt ((h (u i) + R) / (2 * R)))
      (fun i => Real.sqrt ((h (v i) + R) / (2 * R))) ≤
      Real.sqrt ((2 * R * m)⁻¹ * ∑ i, dist (u i) (v i)) := by
  have hnonneg (x : E) (hx : x ∈ S) : 0 ≤ (h x + R) / (2 * R) := by
    apply div_nonneg _ (by positivity)
    linarith [(abs_le.mp (hbound x hx)).1]
  refine (averagedL1_sqrt_le hm _ _ (fun i => hnonneg _ (hu i))
    (fun i => hnonneg _ (hv i))).trans (Real.sqrt_le_sqrt ?_)
  unfold averagedL1
  calc
    _ ≤ (m : ℝ)⁻¹ * ∑ i, dist (u i) (v i) / (2 * R) := by
      gcongr with i
      rw [← sub_div, add_sub_add_right_eq_sub, abs_div, abs_of_pos (by positivity : 0 < 2 * R)]
      exact div_le_div_of_nonneg_right (hLip _ (hu i) _ (hv i)) (by positivity)
    _ = _ := by rw [← Finset.sum_div, mul_inv_rev]; ring

/-- For [a real-valued test h](hyp:h), [a real normalization scale R](hyp:R),
and [an evaluation point x](hyp:x), [the normalized square-root test value](goal)
is the square root of (h(x) + R)/(2R). -/
-- @node: normalizedSqrtTest
def normalizedSqrtTest {E : Type*} (h : E → ℝ) (R : ℝ) (x : E) : ℝ :=
  Real.sqrt ((h x + R) / (2 * R))

/-- If [R is positive](hyp:hR) and [the absolute test value at x is at most
R](hyp:hx), [the normalized square-root test value at x lies between zero
and one](goal). -/
-- @node: normalizedSqrtTest_mem_Icc
lemma normalizedSqrtTest_mem_Icc {E : Type*} {h : E → ℝ} {R : ℝ}
    (hR : 0 < R) {x : E} (hx : |h x| ≤ R) :
    normalizedSqrtTest h R x ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨Real.sqrt_nonneg _, ?_⟩
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by norm_num, ?_⟩
  apply (div_le_iff₀ (by positivity : 0 < 2 * R)).mpr
  nlinarith [(abs_le.mp hx).2]

/-- If [R is positive](hyp:hR) and [the test value at x is at least −R](hyp:hx),
[the square of the normalized square-root test at x equals
(h(x) + R)/(2R)](goal). -/
-- @node: normalizedSqrtTest_sq
lemma normalizedSqrtTest_sq {E : Type*} {h : E → ℝ} {R : ℝ}
    (hR : 0 < R) {x : E} (hx : -R ≤ h x) :
    (normalizedSqrtTest h R x)^2 = (h x + R) / (2 * R) := by
  apply Real.sq_sqrt
  exact div_nonneg (by linarith) (by positivity)

/-- If [the test h is measurable](hyp:hh), [its normalized square-root
transform is measurable for every real scale R](goal). -/
-- @node: measurable_normalizedSqrtTest
@[fun_prop] lemma measurable_normalizedSqrtTest {E : Type*} [MeasurableSpace E]
    {h : E → ℝ} (hh : Measurable h) (R : ℝ) : Measurable (normalizedSqrtTest h R) := by
  unfold normalizedSqrtTest
  fun_prop

/-- If [R is positive](hyp:hR), [h is measurable](hyp:hh),
[h is everywhere bounded in absolute value by R](hyp:hbound), and
[the sample size m is positive](hyp:hm), [the population mean of h minus
its sample mean equals 2R times the population mean minus sample mean of
the squared normalized square-root test](goal). -/
-- @node: normalizedSqrtTest_squared_loss_contrast
lemma normalizedSqrtTest_squared_loss_contrast {E : Type*} [MeasurableSpace E]
    (mu : ProbabilityMeasure E) {h : E → ℝ} {R : ℝ} (hR : 0 < R)
    (hh : Measurable h) (hbound : ∀ x, |h x| ≤ R)
    {m : ℕ} (hm : 0 < m) (x : Fin m → E) :
    (∫ y, h y ∂(mu : Measure E)) - (m : ℝ)⁻¹ * ∑ i, h (x i) =
      2 * R * ((∫ y, (normalizedSqrtTest h R y)^2 ∂(mu : Measure E)) -
        (m : ℝ)⁻¹ * ∑ i, (normalizedSqrtTest h R (x i))^2) := by
  have hi : Integrable h (mu : Measure E) := by
    apply Integrable.of_bound hh.aestronglyMeasurable R
    exact Filter.Eventually.of_forall (fun y => by simpa only [Real.norm_eq_abs] using hbound y)
  have hs (y : E) : (normalizedSqrtTest h R y)^2 = (h y + R) / (2 * R) :=
    normalizedSqrtTest_sq hR (abs_le.mp (hbound y)).1
  simp_rw [hs]
  rw [integral_div, integral_add hi (integrable_const R)]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul,
    ← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp
  ring

/-- If [R is positive](hyp:hR), [the absolute value of h is bounded by R
on S](hyp:hbound), and [every function in the class takes values in S](hyp:hF),
[composing each class member with the normalized square-root test gives
functions taking values between zero and one](goal). -/
-- @node: normalizedSqrtTest_class_range
lemma normalizedSqrtTest_class_range {X E : Type*} {F : Set (X → E)}
    {S : Set E} {h : E → ℝ} {R : ℝ} (hR : 0 < R)
    (hbound : ∀ y ∈ S, |h y| ≤ R) (hF : ∀ f ∈ F, ∀ x, f x ∈ S) :
    ∀ z ∈ ((fun f : X → E => normalizedSqrtTest h R ∘ f) '' F),
      ∀ x, z x ∈ Set.Icc (0 : ℝ) 1 := by
  rintro _ ⟨f, hf, rfl⟩ x
  exact normalizedSqrtTest_mem_Icc hR (hbound _ (hF f hf x))

/-- If [R is positive](hyp:hR), [r is positive](hyp:hr),
[the sample size m is positive](hyp:hm), [h is one-Lipschitz on S](hyp:hLip),
[h is bounded in absolute value by R on S](hyp:hbound), and
[all vector functions in the class take values in S](hyp:hF),
[the worst-case average-distance covering number of the normalized
square-root test compositions at radius r is at most the vector class's
unnormalized empirical covering number at radius 2Rmr²](goal). -/
-- @node: normalizedSqrtTest_cover_le
lemma normalizedSqrtTest_cover_le {X : Type*} {d m : ℕ}
    {F : Set (X → L1Vec d)} {S : Set (L1Vec d)} {h : L1Vec d → ℝ}
    {R r : ℝ} (hR : 0 < R) (hr : 0 < r) (hm : 0 < m)
    (hLip : LipschitzOnWith 1 h S) (hbound : ∀ y ∈ S, |h y| ≤ R)
    (hF : ∀ f ∈ F, ∀ x, f x ∈ S) :
    N1avg r ((fun f : X → L1Vec d => normalizedSqrtTest h R ∘ f) '' F) m
      (normalizedSqrtTest_class_range hR hbound hF) ≤
      empiricalL1CoveringNumber (ENNReal.ofReal (2 * R * m * r^2)) F m := by
  classical
  unfold N1avg empiricalL1CoveringNumber
  refine iSup_le fun x => le_trans ?_ (le_iSup _ x)
  let ev (f : X → L1Vec d) : WithLp 1 (Fin m × Fin d → ℝ) :=
    WithLp.toLp 1 (fun ij => (f (x ij.1)).ofLp ij.2)
  let T (v : WithLp 1 (Fin m × Fin d → ℝ)) : Fin m → ℝ :=
    fun i => normalizedSqrtTest h R (WithLp.toLp 1 (fun j => v.ofLp (i, j)))
  unfold strictCoveringNumber
  refine le_iInf fun C => ?_
  have hsub : T '' C.val ⊆
      (fun z : X → ℝ => fun i => z (x i)) ''
        ((fun f : X → L1Vec d => normalizedSqrtTest h R ∘ f) '' F) := by
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨f, hf, rfl⟩ := C.property.1 hv
    exact ⟨_, ⟨f, hf, rfl⟩, rfl⟩
  have hcover : SetRel.IsCover {p | averagedL1 p.1 p.2 < r}
      ((fun z : X → ℝ => fun i => z (x i)) ''
        ((fun f : X → L1Vec d => normalizedSqrtTest h R ∘ f) '' F)) (T '' C.val) := by
    rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    obtain ⟨v, hv, hdist⟩ := C.property.2 (Set.mem_image_of_mem ev hf)
    refine ⟨T v, Set.mem_image_of_mem T hv, ?_⟩
    obtain ⟨g, hg, rfl⟩ := C.property.1 hv
    change edist (ev f) (ev g) < ENNReal.ofReal (2 * R * m * r^2) at hdist
    rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff (by positivity)] at hdist
    have heval : dist (ev f) (ev g) = ∑ i, dist (f (x i)) (g (x i)) := by
      simp only [ev, PiLp.dist_eq_of_L1, Fintype.sum_prod_type]
    rw [heval] at hdist
    have htest := normalized_test_sqrt_empirical_dist_le hm hR
      (fun y hy z hz => by
        simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
          hLip.dist_le_mul y hy z hz) hbound (fun i => f (x i)) (fun i => g (x i))
      (fun i => hF f hf _) (fun i => hF g hg _)
    change averagedL1 (fun i => normalizedSqrtTest h R (f (x i)))
      (fun i => normalizedSqrtTest h R (g (x i))) < r
    refine htest.trans_lt ((Real.sqrt_lt' hr).mpr ?_)
    have hscale : 0 < 2 * R * (m : ℝ) := by positivity
    exact (inv_mul_lt_iff₀ hscale).mpr hdist
  exact (iInf_le_of_le ⟨T '' C.val, hsub, hcover⟩ le_rfl).trans
    (Set.encard_image_le T C.val)

end
end Papers.TbsNeuralCausalPi

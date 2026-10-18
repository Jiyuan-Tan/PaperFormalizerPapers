module
public import Papers.TbsNeuralCausalPi.Helpers.RegressionComparison
public import Mathlib.Analysis.Normed.Lp.ProdLp
/-! # Vector covariate regression comparison on the bounded input domain

The compact input domain is the set `Q` in the dose-response proof. The two
contrasts are estimated on the joint carrying set, with the paper's one-norm.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
open scoped ENNReal NNReal
set_option linter.style.longLine false

-- @node: regressionJointMeasurable
/-- For [a covariate dimension q](hyp:q), [the measurable sets of the joint
covariate-outcome space with the sum metric](goal) are its Borel sets. -/
instance regressionJointMeasurable (q : ℕ) :
    MeasurableSpace (WithLp 1 (L1Vec q × ℝ)) := borel _

-- @node: regressionJointBorel
/-- For [a covariate dimension q](hyp:q), [the joint covariate-outcome space
with the sum metric has its Borel measurable structure](goal). -/
instance regressionJointBorel (q : ℕ) :
    BorelSpace (WithLp 1 (L1Vec q × ℝ)) := ⟨rfl⟩

-- @node: regression_gap_le_wasserstein_vec
/-- Suppose [the covariate set Q is measurable](hyp:hQ) and [compact](hyp:hQcompact),
[the outcome bound K is positive](hyp:hK), and [K is at most the regression
bound B](hyp:hB). For [a nonnegative Lipschitz constant L](hyp:L), assume
[f is measurable](hyp:hf), [the fitted regression is measurable](hyp:hfhat),
[f is L-Lipschitz on Q](hyp:hLip), [the fitted regression is L-Lipschitz on
Q](hyp:hLiphat), [both are bounded in absolute value by B on Q](hyp:hbound),
[both laws give full mass to covariates in Q and outcomes bounded by K](hyp:hsupport),
[f represents the conditional mean outcome under the second law](hyp:hreg), and
[the fitted regression represents it under the first law](hyp:hreghat).
Then [the mean squared regression difference under the second law is at most
four times L times B plus twice B times the maximum of L and one, multiplied
by the Wasserstein distance of order one between the joint laws in the sum metric](goal). -/
lemma regression_gap_le_wasserstein_vec {q : ℕ}
    (mu nu : ProbabilityMeasure (WithLp 1 (L1Vec q × ℝ)))
    (Q : Set (L1Vec q)) (hQ : MeasurableSet Q) (hQcompact : IsCompact Q) (K B : ℝ) (hK : 0 < K) (hB : K ≤ B)
    (f fhat : L1Vec q → ℝ) (L : ℝ≥0)
    (hf : Measurable f) (hfhat : Measurable fhat)
    (hLip : LipschitzOnWith L f Q) (hLiphat : LipschitzOnWith L fhat Q)
    (hbound : ∀ z ∈ Q, |f z| ≤ B ∧ |fhat z| ≤ B)
    (hsupport : (mu : Measure (WithLp 1 (L1Vec q × ℝ))) {z : WithLp 1 (L1Vec q × ℝ) | z.ofLp.1 ∈ Q ∧ |z.ofLp.2| ≤ K} = 1 ∧
      (nu : Measure (WithLp 1 (L1Vec q × ℝ))) {z : WithLp 1 (L1Vec q × ℝ) | z.ofLp.1 ∈ Q ∧ |z.ofLp.2| ≤ K} = 1)
    (hreg : (fun z : WithLp 1 (L1Vec q × ℝ) => f (z.ofLp.1)) =ᵐ[(nu : Measure (WithLp 1 (L1Vec q × ℝ)))]
      (nu : Measure (WithLp 1 (L1Vec q × ℝ)))[fun z : WithLp 1 (L1Vec q × ℝ) => z.ofLp.2 | MeasurableSpace.comap
        (fun z : WithLp 1 (L1Vec q × ℝ) => z.ofLp.1) (borel _)] )
    (hreghat : (fun z : WithLp 1 (L1Vec q × ℝ) => fhat (z.ofLp.1)) =ᵐ[(mu : Measure (WithLp 1 (L1Vec q × ℝ)))]
      (mu : Measure (WithLp 1 (L1Vec q × ℝ)))[fun z : WithLp 1 (L1Vec q × ℝ) => z.ofLp.2 | MeasurableSpace.comap
        (fun z : WithLp 1 (L1Vec q × ℝ) => z.ofLp.1) (borel _)] ) :
    (∫ z : WithLp 1 (L1Vec q × ℝ), (f (z.ofLp.1)-fhat (z.ofLp.1))^2 ∂(nu : Measure (WithLp 1 (L1Vec q × ℝ)))) ≤
      (4*L*B+2*B*max (L:ℝ) 1) * (wasserstein1 (mu : Measure (WithLp 1 (L1Vec q × ℝ))) (nu : Measure (WithLp 1 (L1Vec q × ℝ)))).toReal := by
  let X := WithLp 1 (L1Vec q × ℝ)
  let T : X → L1Vec q := fun z => z.ofLp.1
  let Y : X → ℝ := fun z => z.ofLp.2
  let S : Set X := {z | T z ∈ Q ∧ |Y z| ≤ K}
  let a : L1Vec q → ℝ := fun t => fhat t - f t
  let g : X → ℝ := fun z => a (T z) * Y z
  let H : X → ℝ := fun z => a (T z) * fhat (T z)
  let F : X → ℝ := fun z => a (T z) * f (T z)
  have hB0 : 0 ≤ B := hK.le.trans hB
  let b : ℝ≥0 := ⟨B, hB0⟩
  have hT : Continuous T := by fun_prop
  have hY : Continuous Y := by fun_prop
  have hdist (x y : X) : dist x y = dist (T x) (T y) + |Y x - Y y| := by
    simpa only [WithLp.fst, WithLp.snd, Real.dist_eq] using
      (WithLp.prod_dist_eq_of_L1 x y)
  have ha : Measurable a := hfhat.sub hf
  have hg : Measurable g := by fun_prop
  have hH : Measurable H := by fun_prop
  have hF : Measurable F := by fun_prop
  have hS : IsCompact S := by
    have heq : S = (WithLp.toLp 1) '' (Q ×ˢ Set.Icc (-K) K) := by
      ext z
      simp only [S, T, Y, Set.mem_ofPred_eq, Set.mem_image, Set.mem_prod,
        Set.mem_Icc, abs_le]
      constructor
      · intro hz
        exact ⟨z.ofLp, hz, WithLp.toLp_ofLp 1 z⟩
      · rintro ⟨w, hw, rfl⟩
        exact hw
    rw [heq]
    exact (hQcompact.prod isCompact_Icc).image (by fun_prop)
  have hmem (rho : ProbabilityMeasure X) (hrho : (rho : Measure X) S = 1) :
      ∀ᵐ z ∂(rho : Measure X), z ∈ S :=
    (ae_mem_iff_measure_eq hS.measurableSet.nullMeasurableSet).2 (by simpa using hrho)
  have hab (t : L1Vec q) (ht : t ∈ Q) : |a t| ≤ 2 * B :=
    (abs_sub _ _).trans (by linarith [(hbound t ht).1, (hbound t ht).2])
  have had (t : L1Vec q) (ht : t ∈ Q) (u : L1Vec q) (hu : u ∈ Q) :
      |a t - a u| ≤ 2 * L * dist t u := by
    simpa only [a, Real.dist_eq, NNReal.coe_add, two_mul] using
      (hLiphat.sub hLip).dist_le_mul t ht u hu
  have hgLip : LipschitzOnWith (2 * b * max L 1) g S := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hsplit : g x - g y =
        a (T x) * (Y x - Y y) + Y y * (a (T x) - a (T y)) := by dsimp [g]; ring
    rw [Real.dist_eq, hsplit]
    calc
      _ ≤ |a (T x)| * |Y x - Y y| + |Y y| * |a (T x) - a (T y)| := by
        simpa only [abs_mul] using abs_add_le
          (a (T x) * (Y x - Y y)) (Y y * (a (T x) - a (T y)))
      _ ≤ (2 * B) * |Y x - Y y| + K * (2 * L * dist (T x) (T y)) := by
        gcongr
        · exact hab _ hx.1
        · exact hy.2
        · exact had _ hx.1 _ hy.1
      _ ≤ (2 * B * max (L : ℝ) 1) * (dist (T x) (T y) + |Y x - Y y|) := by
        have ht := mul_le_mul_of_nonneg_right (le_max_left (L : ℝ) 1)
          (dist_nonneg : 0 ≤ dist (T x) (T y))
        have hy' := mul_le_mul_of_nonneg_right (le_max_right (L : ℝ) 1)
          (abs_nonneg (Y x - Y y))
        have hk := mul_le_mul_of_nonneg_right hB
          (mul_nonneg L.coe_nonneg (dist_nonneg : 0 ≤ dist (T x) (T y)))
        nlinarith [mul_nonneg b.coe_nonneg (sub_nonneg.mpr ht),
          mul_nonneg b.coe_nonneg (sub_nonneg.mpr hy')]
      _ = _ := by
        change _ = (2 * B * max (L : ℝ) 1) * dist x y
        rw [hdist]
  have hHLip : LipschitzOnWith (4 * L * b) H S := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hh : |fhat (T x) - fhat (T y)| ≤ L * dist (T x) (T y) := by
      simpa only [Real.dist_eq] using hLiphat.dist_le_mul (T x) hx.1 (T y) hy.1
    have hsplit : H x - H y =
        a (T x) * (fhat (T x) - fhat (T y)) +
          fhat (T y) * (a (T x) - a (T y)) := by dsimp [H]; ring
    rw [Real.dist_eq, hsplit]
    calc
      _ ≤ |a (T x)| * |fhat (T x) - fhat (T y)| +
          |fhat (T y)| * |a (T x) - a (T y)| := by
        simpa only [abs_mul] using abs_add_le
          (a (T x) * (fhat (T x) - fhat (T y)))
          (fhat (T y) * (a (T x) - a (T y)))
      _ ≤ (2 * B) * (L * dist (T x) (T y)) + B * (2 * L * dist (T x) (T y)) := by
        gcongr
        · exact hab _ hx.1
        · exact (hbound _ hy.1).2
        · exact had _ hx.1 _ hy.1
      _ = (4 * (L : ℝ) * B) * dist (T x) (T y) := by ring
      _ ≤ (4 * (L : ℝ) * B) * dist x y := by
        gcongr
        rw [hdist]
        exact le_add_of_nonneg_right (abs_nonneg _)
      _ = _ := by rfl
  have hi (rho : ProbabilityMeasure X) (hrho : (rho : Measure X) S = 1)
      (u : X → ℝ) (hu : Measurable u) (c : ℝ) (hb : ∀ z ∈ S, |u z| ≤ c) :
      Integrable u (rho : Measure X) := by
    apply Integrable.of_bound hu.aestronglyMeasurable c
    filter_upwards [hmem rho hrho] with z hz
    simpa only [Real.norm_eq_abs] using hb z hz
  have hiY (rho : ProbabilityMeasure X) (hrho : (rho : Measure X) S = 1) :
      Integrable Y (rho : Measure X) :=
    hi rho hrho Y hY.measurable K (fun _ hz => hz.2)
  have hig (rho : ProbabilityMeasure X) (hrho : (rho : Measure X) S = 1) :
      Integrable g (rho : Measure X) := by
    apply hi rho hrho g hg (2 * B * K)
    intro z hz
    dsimp only [g]
    rw [abs_mul]
    exact mul_le_mul (hab _ hz.1) hz.2 (abs_nonneg _) (by positivity)
  have hiH : Integrable H (nu : Measure X) := by
    apply hi nu hsupport.2 H hH (2 * B * B)
    intro z hz
    dsimp only [H]
    rw [abs_mul]
    exact mul_le_mul (hab _ hz.1) (hbound _ hz.1).2 (abs_nonneg _) (by positivity)
  have hiF : Integrable F (nu : Measure X) := by
    apply hi nu hsupport.2 F hF (2 * B * B)
    intro z hz
    dsimp only [F]
    rw [abs_mul]
    exact mul_le_mul (hab _ hz.1) (hbound _ hz.1).1 (abs_nonneg _) (by positivity)
  have hgm : (∫ z, g z ∂(mu : Measure X)) = ∫ z, H z ∂(mu : Measure X) :=
    regression_weighted_outcome_integral (mu : Measure X) T Y hT.measurable
      a fhat ha (hiY mu hsupport.1) (hig mu hsupport.1) hreghat
  have hgn : (∫ z, g z ∂(nu : Measure X)) = ∫ z, F z ∂(nu : Measure X) :=
    regression_weighted_outcome_integral (nu : Measure X) T Y hT.measurable
      a f ha (hiY nu hsupport.2) (hig nu hsupport.2) hreg
  have hgc := regression_compact_support_contrast_le mu nu S hS
    hsupport.1 hsupport.2 g (2 * b * max L 1) hgLip
  have hhc := regression_compact_support_contrast_le mu nu S hS
    hsupport.1 hsupport.2 (fun z => -H z) (4 * L * b) hHLip.neg
  simp only [integral_neg] at hhc
  have hsquare :
      (∫ z : X, (f (T z) - fhat (T z))^2 ∂(nu : Measure X)) =
        (∫ z, H z ∂(nu : Measure X)) - ∫ z, F z ∂(nu : Measure X) := by
    rw [← integral_sub hiH hiF]
    apply integral_congr_ae
    filter_upwards [] with z
    dsimp [H, F, a]
    ring
  rw [hgm, hgn] at hgc
  change (∫ z : X, (f (T z) - fhat (T z))^2 ∂(nu : Measure X)) ≤ _
  rw [hsquare]
  change _ ≤ (2 * B * max (L : ℝ) 1) * _ at hgc
  change -_ - -_ ≤ (4 * (L : ℝ) * B) * _ at hhc
  linarith

end Papers.TbsNeuralCausalPi

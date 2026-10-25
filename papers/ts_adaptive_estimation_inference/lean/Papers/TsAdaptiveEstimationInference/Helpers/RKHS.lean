module
public import StatLean.NonparametricStatistics.RKHS.Basic
public import StatLean.NonparametricStatistics.RKHS.Representer
public import Causalean.Mathlib.Analysis.MoorePenrose
public import Causalean.Mathlib.Analysis.InnerProductSpace.Gram
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
/-! The conditional finite-sample RKHS quadratic program. -/
@[expose] public section
set_option linter.style.longLine false
namespace Papers.TsAdaptiveEstimationInference
open scoped BigOperators
variable {𝒳 𝒵 H F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [RKHS ℝ H 𝒳 ℝ] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [CompleteSpace F] [RKHS ℝ F 𝒵 ℝ]

-- @env: S4
variable (H F) (N : ℕ) (X : Fin N → 𝒳) (Z : Fin N → 𝒵) (y : Fin N → ℝ) -- @realizes \boldsymbol y(real outcome vector indexed by Fin N)

/-- In the [primal reproducing kernel Hilbert space](hyp:H), the [kernel representer](goal)
at [an input point](hyp:x) is the function whose inner product with any function gives its value at that point. -/
noncomputable abbrev kernelRepresenter (x : 𝒳) : H :=
  StatLean.NonparametricStatistics.kernelFun H x

-- @node: ass:rkhs-qp-spaces
/-- For the [primal space](hyp:H) and [critic space](hyp:F), [kernel compatibility](goal)
requires that the [proposed primal kernel](hyp:kH) [equals the primal space's canonical kernel](step:1)
and that the [proposed critic kernel](hyp:kF) [equals the critic space's canonical kernel](step:2). -/
noncomputable def RKHSSpaces (kH : 𝒳 → 𝒳 → ℝ) (kF : 𝒵 → 𝒵 → ℝ) : Prop :=
  kH = StatLean.NonparametricStatistics.scalarKernel H ∧ -- @realizes k_{\mathcal H}(given kernel equals the canonical reproducing kernel)
  kF = StatLean.NonparametricStatistics.scalarKernel F -- @realizes k_{\mathcal F}(given kernel equals the canonical reproducing kernel)

/-- For a [primal reproducing kernel Hilbert space](hyp:H) and [a sample of the given size](hyp:N)
with [primal inputs](hyp:X), the [primal Gram matrix](goal) records the canonical kernel evaluated at every pair of sample inputs. -/
noncomputable def gramH : Matrix (Fin N) (Fin N) ℝ := -- @realizes K_{\mathcal H}(Gram matrix of the primal reproducing kernel)
  Causalean.Mathlib.Analysis.InnerProductSpace.gram
    (StatLean.NonparametricStatistics.scalarKernel H) X

/-- For a [critic reproducing kernel Hilbert space](hyp:F) and [a sample of the given size](hyp:N)
with [critic inputs](hyp:Z), the [critic Gram matrix](goal) records the canonical kernel evaluated at every pair of sample inputs. -/
noncomputable def gramF : Matrix (Fin N) (Fin N) ℝ := -- @realizes K_{\mathcal F}(Gram matrix of the critic reproducing kernel)
  Causalean.Mathlib.Analysis.InnerProductSpace.gram
    (StatLean.NonparametricStatistics.scalarKernel F) Z

-- @node: def:rkhs-matrices
/-- For the [critic space](hyp:F), [sample size](hyp:N), [critic inputs](hyp:Z), and
[ridge parameter](hyp:η), the [critic smoothing matrix](goal) is the critic Gram matrix times the inverse of its shift by sample size times the ridge parameter. -/
noncomputable def criticSmoother (η : ℝ) : Matrix (Fin N) (Fin N) ℝ := -- @realizes P_\eta(critic Gram times the inverse of its ridge shift)
  gramF F N Z * (gramF F N Z + (N * η) • (1 : Matrix (Fin N) (Fin N) ℝ))⁻¹

-- @node: def:rkhs-loss
/-- For the [primal space](hyp:H), [critic space](hyp:F), [sample size](hyp:N),
[primal inputs](hyp:X), [critic inputs](hyp:Z), [outcomes](hyp:y), [critic ridge parameter](hyp:η),
and [candidate fit](hyp:h), the [adversarial loss](goal) is the supremum over critics of twice the empirical residual–critic product, minus the empirical squared critic values and the ridge-weighted squared critic norm. -/
noncomputable def rkhsAdversarialLoss (η : ℝ) (h : H) : ℝ := -- @realizes L_{N,\eta}(full RKHS supremum with positive critic ridge)
  ⨆ f : F, (2 / N) * ∑ i, (y i - h (X i)) * f (Z i) -
    (1 / N) * ∑ i, f (Z i) ^ 2 - η * ‖f‖ ^ 2

/-- For the [primal space](hyp:H), [sample size](hyp:N), [sample inputs](hyp:X), and
[candidate function](hyp:h), the [empirical squared magnitude](goal) is the sum of squared sample evaluations divided by the sample size. -/
noncomputable def rkhsEmpSq (h : H) : ℝ := (N : ℝ)⁻¹ * ∑ i, h (X i) ^ 2

-- @node: ass:rkhs-qp-representative
/-- In the [primal space](hyp:H), for [a sample of the given size](hyp:N) with [inputs](hyp:X),
a [candidate function](hyp:h) is a [minimum-norm representative](goal) if its norm is no greater than that of any function with the same sample evaluations. -/
def MinNormRepresentative (h : H) : Prop :=
  ∀ g : H, (∀ i, g (X i) = h (X i)) → ‖h‖ ≤ ‖g‖

/-- For the [primal space](hyp:H), [critic space](hyp:F), [sample size](hyp:N),
[primal inputs](hyp:X), [critic inputs](hyp:Z), [outcomes](hyp:y), [critic ridge parameter](hyp:η),
[fit penalty weight](hyp:lam), and [kernel coefficients](hyp:α), the [coefficient objective](goal)
first [forms residuals by subtracting the primal Gram matrix times the coefficients from outcomes](step:1),
then [adds their critic-smoothed quadratic form to the penalty-weighted squared Euclidean magnitude of the fitted evaluations](step:2). -/
noncomputable def rkhsCoefficientObjective (η lam : ℝ) (α : Fin N → ℝ) : ℝ :=
  let residual := y - (gramH H N X).mulVec α
  dotProduct residual ((criticSmoother F N Z η).mulVec residual) +
    lam * dotProduct α ((gramH H N X * gramH H N X).mulVec α)

-- @node: def:rkhs-qp
/-- For the [primal space](hyp:H), [critic space](hyp:F), [sample size](hyp:N),
[primal inputs](hyp:X), [critic inputs](hyp:Z), [outcomes](hyp:y), [critic ridge parameter](hyp:η),
and [fit penalty weight](hyp:lam), the [coefficient minimizer condition](goal) says that
the [candidate coefficients](hyp:α) have objective value no greater than any alternative coefficients. -/
noncomputable def IsRKHSCoefficientMinimizer (η lam : ℝ) (α : Fin N → ℝ) : Prop :=
  ∀ α', rkhsCoefficientObjective H F N X Z y η lam α ≤
    rkhsCoefficientObjective H F N X Z y η lam α'

/-- For the [primal space](hyp:H), [critic space](hyp:F), [sample size](hyp:N),
[primal inputs](hyp:X), [critic inputs](hyp:Z), [outcomes](hyp:y), [critic ridge parameter](hyp:η),
and [fit penalty weight](hyp:lam), the [selected coefficient vector](goal) applies the Moore–Penrose inverse of the sum of the primal-Gram–smoother–primal-Gram product and the penalty-weighted squared primal Gram matrix to the primal Gram matrix times the smoothed outcomes. -/
noncomputable def rkhsMinimumCoefficients (η lam : ℝ) : Fin N → ℝ := -- @realizes \widehat\alpha_\lambda(Moore--Penrose formula without invertibility or spectral hypotheses)
  (Causalean.Mathlib.Analysis.moorePenroseInverse
    (gramH H N X * criticSmoother F N Z η * gramH H N X +
      lam • (gramH H N X * gramH H N X))).mulVec
    ((gramH H N X * criticSmoother F N Z η).mulVec y)

/-- For the [primal space](hyp:H), [critic space](hyp:F), [sample size](hyp:N),
[primal inputs](hyp:X), [critic inputs](hyp:Z), [outcomes](hyp:y), [critic ridge parameter](hyp:η),
and [fit penalty weight](hyp:lam), the [optimal fit condition](goal) says that the [candidate function](hyp:h)
minimizes adversarial loss plus the weighted empirical squared magnitude over all primal functions. -/
noncomputable def IsRKHSFit (η lam : ℝ) (h : H) : Prop :=
  ∀ g : H, rkhsAdversarialLoss H F N X Z y η h + lam * rkhsEmpSq H N X h ≤
    rkhsAdversarialLoss H F N X Z y η g + lam * rkhsEmpSq H N X g

/-- For the [critic space](hyp:F), [sample size](hyp:N), [critic inputs](hyp:Z),
[outcomes](hyp:y), [critic ridge parameter](hyp:η), and [fitted evaluation vector](hyp:v),
the [evaluation loss](goal) is the supremum over critics of twice the empirical residual–critic product, minus the empirical squared critic values and the ridge-weighted squared critic norm. -/
-- @node: rkhsEvaluationLoss
noncomputable def rkhsEvaluationLoss (η : ℝ) (v : Fin N → ℝ) : ℝ :=
  ⨆ f : F, (2 / N) * ∑ i, (y i - v i) * f (Z i) -
    (1 / N) * ∑ i, f (Z i) ^ 2 - η * ‖f‖ ^ 2

/-- If [the sample size is positive](hyp:hN) and [the critic ridge parameter is nonnegative](hyp:hη),
[every critic's objective is at most the mean squared residual for the given fitted evaluations](goal). -/
-- @node: rkhsCritic_le_residual
lemma rkhsCritic_le_residual (hN : 0 < N) (η : ℝ) (hη : 0 ≤ η)
    (v : Fin N → ℝ) (f : F) :
    (2 / N) * ∑ i, (y i - v i) * f (Z i) -
      (1 / N) * ∑ i, f (Z i) ^ 2 - η * ‖f‖ ^ 2 ≤
      (1 / N) * ∑ i, (y i - v i) ^ 2 := by
  have hs : 2 * (∑ i, (y i - v i) * f (Z i)) - ∑ i, f (Z i) ^ 2 ≤
      ∑ i, (y i - v i) ^ 2 := by
    calc
      _ = ∑ i, (2 * (y i - v i) * f (Z i) - f (Z i) ^ 2) := by
        rw [Finset.sum_sub_distrib, Finset.mul_sum]
        congr 1
        simp only [mul_assoc]
      _ ≤ _ := Finset.sum_le_sum fun i _ => by nlinarith [sq_nonneg (y i - v i - f (Z i))]
  have hm := mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ 1 / N)
  have hp := mul_nonneg hη (sq_nonneg ‖f‖)
  simp only [div_eq_mul_inv] at hm ⊢
  nlinarith only [hm, hp]

/-- If [the sample size is positive](hyp:hN) and [the critic ridge parameter is nonnegative](hyp:hη),
[the evaluation loss lies between zero and the mean squared residual](goal). -/
-- @node: rkhsEvaluationLoss_bounds
lemma rkhsEvaluationLoss_bounds (hN : 0 < N) (η : ℝ) (hη : 0 ≤ η)
    (v : Fin N → ℝ) :
    0 ≤ rkhsEvaluationLoss F N Z y η v ∧
    rkhsEvaluationLoss F N Z y η v ≤ (1 / N) * ∑ i, (y i - v i) ^ 2 := by
  have hb : BddAbove (Set.range fun f : F =>
      (2 / N) * ∑ i, (y i - v i) * f (Z i) -
        (1 / N) * ∑ i, f (Z i) ^ 2 - η * ‖f‖ ^ 2) :=
    ⟨_, by
      rintro _ ⟨f, rfl⟩
      exact rkhsCritic_le_residual F N Z y hN η hη v f⟩
  constructor
  · have hh := le_ciSup hb (0 : F)
    simpa [rkhsEvaluationLoss] using hh
  · exact ciSup_le fun f => rkhsCritic_le_residual F N Z y hN η hη v f

/-- If [the sample size is positive](hyp:hN) and [the critic ridge parameter is nonnegative](hyp:hη),
[the evaluation loss is convex over all fitted evaluation vectors](goal). -/
-- @node: rkhsEvaluationLoss_convex
lemma rkhsEvaluationLoss_convex (hN : 0 < N) (η : ℝ) (hη : 0 ≤ η) :
    ConvexOn ℝ Set.univ (rkhsEvaluationLoss F N Z y η) := by
  refine ⟨convex_univ, ?_⟩
  intro u _ v _ a b ha hb hab
  apply ciSup_le
  intro f
  have hbd (w : Fin N → ℝ) : BddAbove (Set.range fun f : F =>
      (2 / N) * ∑ i, (y i - w i) * f (Z i) -
        (1 / N) * ∑ i, f (Z i) ^ 2 - η * ‖f‖ ^ 2) :=
    ⟨_, by
      rintro _ ⟨g, rfl⟩
      exact rkhsCritic_le_residual F N Z y hN η hη w g⟩
  have hu := le_ciSup (hbd u) f
  have hv := le_ciSup (hbd v) f
  have he : (2 / N) * ∑ i, (y i - (a • u + b • v) i) * f (Z i) -
      (1 / N) * ∑ i, f (Z i) ^ 2 - η * ‖f‖ ^ 2 =
      a * ((2 / N) * ∑ i, (y i - u i) * f (Z i) -
        (1 / N) * ∑ i, f (Z i) ^ 2 - η * ‖f‖ ^ 2) +
      b * ((2 / N) * ∑ i, (y i - v i) * f (Z i) -
        (1 / N) * ∑ i, f (Z i) ^ 2 - η * ‖f‖ ^ 2) := by
    have hs : (∑ i, (y i - (a • u + b • v) i) * f (Z i)) =
        a * (∑ i, (y i - u i) * f (Z i)) + b * (∑ i, (y i - v i) * f (Z i)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [show b = 1 - a by linarith only [hab]]
      ring
    rw [hs]
    rw [show b = 1 - a by linarith only [hab]]
    ring
  rw [he]
  exact add_le_add (mul_le_mul_of_nonneg_left hu ha) (mul_le_mul_of_nonneg_left hv hb)

/-- If [the sample size is positive](hyp:hN), [the critic ridge parameter is positive](hyp:hη),
and [the empirical fit penalty weight is positive](hyp:hlam), [there exists a primal function minimizing adversarial loss plus the weighted empirical squared magnitude](goal).

The minimization takes place over the finite-dimensional evaluation range; no compactness of the RKHS is used. -/
-- @node: rkhs_fit_exists
lemma rkhs_fit_exists (hN : 0 < N) (η lam : ℝ) (hη : 0 < η) (hlam : 0 < lam) :
    ∃ h : H, IsRKHSFit H F N X Z y η lam h := by
  let ev : H →ₗ[ℝ] (Fin N → ℝ) :=
    (ContinuousLinearMap.pi fun i => StatLean.NonparametricStatistics.evalCLM ℝ H (X i)).toLinearMap
  let J : (Fin N → ℝ) → ℝ := fun v =>
    rkhsEvaluationLoss F N Z y η v + lam * ((N : ℝ)⁻¹ * ∑ i, v i ^ 2)
  have hcont : Continuous J := by
    apply Continuous.add
    · exact continuousOn_univ.mp
        ((rkhsEvaluationLoss_convex F N Z y hN η hη.le).continuousOn isOpen_univ)
    · fun_prop
  have hbounded : Bornology.IsBounded {v : ev.range | J v ≤ J 0} := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨Real.sqrt ((N : ℝ) / lam * J 0), ?_⟩
    intro v hv
    have h0 := (rkhsEvaluationLoss_bounds F N Z y hN η hη.le v).1
    have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    have he : ∑ i, (v : Fin N → ℝ) i ^ 2 ≤ (N : ℝ) / lam * J 0 := by
      have hpen : lam * ((N : ℝ)⁻¹ * ∑ i, (v : Fin N → ℝ) i ^ 2) ≤ J 0 := by
        change rkhsEvaluationLoss F N Z y η v +
          lam * ((N : ℝ)⁻¹ * ∑ i, (v : Fin N → ℝ) i ^ 2) ≤ J 0 at hv
        linarith only [h0, hv]
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hlam).mpr
      have hm := mul_le_mul_of_nonneg_left hpen hn.le
      simp only [mul_left_comm (N : ℝ) lam, mul_inv_cancel_left₀ hn.ne'] at hm
      nlinarith only [hm]
    change ‖(v : Fin N → ℝ)‖ ≤ _
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    have hi : (v : Fin N → ℝ) i ^ 2 ≤ ∑ j, (v : Fin N → ℝ) j ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    rw [Real.norm_eq_abs]
    exact (Real.le_sqrt (abs_nonneg _) (le_trans (sq_nonneg _) (hi.trans he))).mpr
      (by simpa only [sq_abs] using hi.trans he)
  obtain ⟨v, hmin⟩ := (hcont.comp continuous_subtype_val).exists_forall_le_of_isBounded
    (0 : ev.range) hbounded
  obtain ⟨h, hh⟩ := v.property
  refine ⟨h, ?_⟩
  intro g
  have hm := hmin ⟨ev g, LinearMap.mem_range_self ev g⟩
  change J (v : Fin N → ℝ) ≤ J (ev g) at hm
  rw [← hh] at hm
  exact hm

/-- For the [primal space](hyp:H), [critic space](hyp:F), [sample size](hyp:N),
[primal inputs](hyp:X), [critic inputs](hyp:Z), [outcomes](hyp:y), [critic ridge parameter](hyp:η),
and [empirical fit penalty weight](hyp:lam), assuming [a positive sample size](hyp:hN),
[a positive critic ridge parameter](hyp:hη), and [a positive fit penalty weight](hyp:hlam),
the [selected fit](goal) is a function chosen to minimize adversarial loss plus the weighted empirical squared magnitude. -/
noncomputable def rkhsSelectedFit (hN : 0 < N) (η lam : ℝ)
    (hη : 0 < η) (hlam : 0 < lam) : H :=
  (rkhs_fit_exists H F N X Z y hN η lam hη hlam).choose

/-- If [a function has minimum norm among all functions with its sample evaluations](hyp:hh),
[it belongs to the linear span of the sample kernel representers](goal). -/
-- @node: rkhs_minNorm_mem_dataSpan
lemma rkhs_minNorm_mem_dataSpan (h : H) (hh : MinNormRepresentative H N X h) :
    h ∈ StatLean.NonparametricStatistics.dataSpan X := by
  let S : Submodule ℝ H := StatLean.NonparametricStatistics.dataSpan X
  have hle : ‖h‖ ≤ ‖S.starProjection h‖ :=
    hh _ (fun i => StatLean.NonparametricStatistics.starProjection_dataSpan_apply h i)
  exact (S.mem_iff_norm_starProjection h).mpr
    (le_antisymm (S.norm_starProjection_apply_le h) hle)

/-- If [a function has minimum norm among all functions with its sample evaluations](hyp:hh),
[it can be expressed as a linear combination of the sample kernel representers](goal). -/
-- @node: rkhs_minNorm_representer
lemma rkhs_minNorm_representer (h : H) (hh : MinNormRepresentative H N X h) :
    ∃ α : Fin N → ℝ, h = ∑ i, α i • kernelRepresenter H (X i) := by
  obtain ⟨α, hα⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp
    (rkhs_minNorm_mem_dataSpan H N X h hh)
  exact ⟨α, hα.symm⟩

/-- [The value of a sample-kernel expansion at any sample input equals the corresponding entry of the primal Gram matrix times its coefficient vector](goal). -/
-- @node: rkhs_representer_evaluation
lemma rkhs_representer_evaluation (α : Fin N → ℝ) (i : Fin N) :
    (∑ j, α j • kernelRepresenter H (X j)) (X i) = (gramH H N X).mulVec α i := by
  change (StatLean.NonparametricStatistics.evalCLM ℝ H (X i))
    (∑ j, α j • kernelRepresenter H (X j)) = _
  simp only [map_sum, map_smul, StatLean.NonparametricStatistics.evalCLM_apply,
    kernelRepresenter, gramH, Causalean.Mathlib.Analysis.InnerProductSpace.gram,
    Matrix.mulVec, dotProduct, smul_eq_mul, StatLean.NonparametricStatistics.scalarKernel,
    mul_comm]

/-- [The squared RKHS norm of a sample-kernel expansion equals the quadratic form of its coefficients with the primal Gram matrix](goal). -/
-- @node: rkhs_representer_norm_sq
lemma rkhs_representer_norm_sq (α : Fin N → ℝ) :
    ‖∑ i, α i • kernelRepresenter H (X i)‖ ^ 2 =
      dotProduct α ((gramH H N X).mulVec α) := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [sum_inner, real_inner_smul_left, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  rw [StatLean.NonparametricStatistics.inner_kernelFun]
  rw [rkhs_representer_evaluation]

/-- If [two primal functions agree at every sample input](hyp:hv),
[their adversarial losses plus weighted empirical squared magnitudes are equal](goal). -/
-- @node: rkhs_objective_depends_on_evaluations
lemma rkhs_objective_depends_on_evaluations (η lam : ℝ) (h g : H)
    (hv : ∀ i, h (X i) = g (X i)) :
    rkhsAdversarialLoss H F N X Z y η h + lam * rkhsEmpSq H N X h =
      rkhsAdversarialLoss H F N X Z y η g + lam * rkhsEmpSq H N X g := by
  simp only [rkhsAdversarialLoss, rkhsEmpSq, hv]

/-- If [the critic ridge parameter is nonnegative](hyp:hη),
[orthogonally projecting any critic onto the span of the sample kernel representers weakly increases its residual-based objective](goal). -/
-- @node: rkhs_critic_projection_improves
lemma rkhs_critic_projection_improves (η : ℝ) (hη : 0 ≤ η)
    (v : Fin N → ℝ) (f : F) :
    (2 / N) * ∑ i, (y i - v i) * f (Z i) -
        (1 / N) * ∑ i, f (Z i) ^ 2 - η * ‖f‖ ^ 2 ≤
      (2 / N) * ∑ i, (y i - v i) *
          ((StatLean.NonparametricStatistics.dataSpan Z).starProjection f) (Z i) -
        (1 / N) * ∑ i,
          ((StatLean.NonparametricStatistics.dataSpan Z).starProjection f) (Z i) ^ 2 -
        η * ‖(StatLean.NonparametricStatistics.dataSpan Z).starProjection f‖ ^ 2 := by
  simp only [StatLean.NonparametricStatistics.starProjection_dataSpan_apply]
  have hn := (StatLean.NonparametricStatistics.dataSpan (H := F) Z).norm_starProjection_apply_le f
  have hs : ‖(StatLean.NonparametricStatistics.dataSpan Z).starProjection f‖ ^ 2 ≤ ‖f‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hn 2
  linarith only [mul_le_mul_of_nonneg_left hs hη]

/-- If [the sample size is positive](hyp:hN) and [the critic ridge parameter is nonnegative](hyp:hη),
[the evaluation loss equals the supremum over coefficient vectors of twice the empirical residual product with the critic Gram matrix times the coefficients, minus the empirical squared fitted critic values and the ridge-weighted Gram quadratic form](goal). -/
-- @node: rkhs_critic_sup_coefficients
lemma rkhs_critic_sup_coefficients (hN : 0 < N) (η : ℝ) (hη : 0 ≤ η)
    (v : Fin N → ℝ) :
    rkhsEvaluationLoss F N Z y η v =
      ⨆ γ : Fin N → ℝ,
        (2 / N) * ∑ i, (y i - v i) * (gramF F N Z).mulVec γ i -
          (1 / N) * ∑ i, ((gramF F N Z).mulVec γ i) ^ 2 -
          η * dotProduct γ ((gramF F N Z).mulVec γ) := by
  let J : F → ℝ := fun f => (2 / N) * ∑ i, (y i - v i) * f (Z i) -
    (1 / N) * ∑ i, f (Z i) ^ 2 - η * ‖f‖ ^ 2
  let c : (Fin N → ℝ) → F := fun γ => ∑ i, γ i • kernelRepresenter F (Z i)
  have heq (γ : Fin N → ℝ) : J (c γ) =
      (2 / N) * ∑ i, (y i - v i) * (gramF F N Z).mulVec γ i -
        (1 / N) * ∑ i, ((gramF F N Z).mulVec γ i) ^ 2 -
        η * dotProduct γ ((gramF F N Z).mulVec γ) := by
    dsimp [J, c]
    simp only [rkhs_representer_evaluation, rkhs_representer_norm_sq]
    rfl
  have hb : BddAbove (Set.range J) := ⟨_, by
    rintro _ ⟨f, rfl⟩
    exact rkhsCritic_le_residual F N Z y hN η hη v f⟩
  have hbc : BddAbove (Set.range fun γ => J (c γ)) := hb.mono (by
    rintro _ ⟨γ, rfl⟩
    exact ⟨c γ, rfl⟩)
  have hsup : (⨆ f, J f) = ⨆ γ, J (c γ) := by
    apply le_antisymm
    · apply ciSup_le
      intro f
      obtain ⟨γ, hγ⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp
        ((StatLean.NonparametricStatistics.dataSpan (H := F) Z).starProjection_apply_mem f)
      have hproj := rkhs_critic_projection_improves F N Z y η hη v f
      change J f ≤ J ((StatLean.NonparametricStatistics.dataSpan Z).starProjection f) at hproj
      exact hproj.trans (by rw [← hγ]; exact le_ciSup hbc γ)
    · exact ciSup_le fun γ => le_ciSup hb (c γ)
  change (⨆ f, J f) = _
  rw [hsup]
  exact congrArg (fun f : (Fin N → ℝ) → ℝ => ⨆ γ, f γ) (funext heq)

/-- [The primal sample Gram matrix is positive semidefinite](goal). -/
-- @node: rkhs_gram_posSemidef
lemma rkhs_gram_posSemidef : (gramH H N X).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    exact StatLean.NonparametricStatistics.scalarKernel_conj_symm H (X j) (X i)
  · intro α
    simpa only [star_trivial, ← rkhs_representer_norm_sq] using
      sq_nonneg ‖∑ i, α i • kernelRepresenter H (X i)‖

/-- If [the sample size is positive](hyp:hN) and [the critic ridge parameter is positive](hyp:hη),
[the critic Gram matrix plus sample size times the ridge parameter times the identity is positive definite](goal). -/
-- @node: rkhs_critic_ridge_posDef
lemma rkhs_critic_ridge_posDef (hN : 0 < N) (η : ℝ) (hη : 0 < η) :
    (gramF F N Z + (N * η) • (1 : Matrix (Fin N) (Fin N) ℝ)).PosDef := by
  exact Matrix.PosDef.posSemidef_add (rkhs_gram_posSemidef F N Z)
    (Matrix.PosDef.one.smul (by positivity : (0 : ℝ) < N * η))

/-- If [the sample size is positive](hyp:hN) and [the critic ridge parameter is positive](hyp:hη),
[applying the inverse of the ridge-shifted critic Gram matrix to a residual vector gives coefficients whose Gram-matrix product plus sample size times the ridge parameter times those coefficients equals the residual vector at every observation](goal). -/
-- @node: rkhs_critic_normal_equation
lemma rkhs_critic_normal_equation (hN : 0 < N) (η : ℝ) (hη : 0 < η)
    (r : Fin N → ℝ) :
    let γ := (gramF F N Z + (N * η) • (1 : Matrix (Fin N) (Fin N) ℝ))⁻¹.mulVec r
    ∀ i, (gramF F N Z).mulVec γ i + (N * η) * γ i = r i := by
  dsimp
  have he := congrArg (fun M : Matrix (Fin N) (Fin N) ℝ => M.mulVec r)
    (Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp
      (rkhs_critic_ridge_posDef F N Z hN η hη).isUnit))
  rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec] at he
  intro i
  have hi := congrFun he i
  simpa only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hi

/-- If [the critic Gram matrix times a coefficient vector plus sample size times the ridge parameter times that vector equals the residual vector](hyp:hγ),
[the sum of residuals times any critic's sample values equals the sum of that critic's sample values times the associated kernel expansion's sample values, plus sample size times the ridge parameter times their RKHS inner product](goal). -/
-- @node: rkhs_critic_stationarity
lemma rkhs_critic_stationarity (η : ℝ) (r γ : Fin N → ℝ)
    (hγ : ∀ i, (gramF F N Z).mulVec γ i + (N * η) * γ i = r i) (f : F) :
    ∑ i, r i * f (Z i) =
      (∑ i, (∑ j, γ j • kernelRepresenter F (Z j)) (Z i) * f (Z i)) +
        (N * η) * inner ℝ (∑ j, γ j • kernelRepresenter F (Z j)) f := by
  simp only [sum_inner, real_inner_smul_left,
    StatLean.NonparametricStatistics.inner_kernelFun, rkhs_representer_evaluation]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← hγ i]
  change ((_ : ℝ) + _) * _ = _ * _ + _
  change ((gramH F N Z).mulVec γ i + N * η * γ i) * f (Z i) = _
  ring

/-- If [the sample size is positive](hyp:hN), [the critic ridge parameter is nonnegative](hyp:hη),
and [the critic Gram matrix times the coefficients plus sample size times the ridge parameter times those coefficients equals the residual vector](hyp:hγ),
[every critic's objective is bounded above by the residual vector's inner product with the Gram matrix times those coefficients, divided by sample size](goal). -/
-- @node: rkhs_critic_maximum
lemma rkhs_critic_maximum (hN : 0 < N) (η : ℝ) (hη : 0 ≤ η)
    (r γ : Fin N → ℝ)
    (hγ : ∀ i, (gramF F N Z).mulVec γ i + (N * η) * γ i = r i) (f : F) :
    (2 / N) * ∑ i, r i * f (Z i) - (1 / N) * ∑ i, f (Z i) ^ 2 - η * ‖f‖ ^ 2 ≤
      (1 / N) * dotProduct r ((gramF F N Z).mulVec γ) := by
  let g : F := ∑ j, γ j • kernelRepresenter F (Z j)
  have hstat := rkhs_critic_stationarity F N Z η r γ hγ f
  have hself := rkhs_critic_stationarity F N Z η r γ hγ g
  change (∑ i, r i * f (Z i)) = (∑ i, g (Z i) * f (Z i)) +
    (N * η) * inner ℝ g f at hstat
  change (∑ i, r i * g (Z i)) = (∑ i, g (Z i) * g (Z i)) +
    (N * η) * inner ℝ g g at hself
  rw [real_inner_self_eq_norm_sq] at hself
  have hsq : 0 ≤ (∑ i, f (Z i) ^ 2) - 2 * (∑ i, g (Z i) * f (Z i)) +
      ∑ i, g (Z i) ^ 2 := by
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg (f (Z i) - g (Z i)))
    have he : (∑ i, (f (Z i) - g (Z i)) ^ 2) =
        (∑ i, f (Z i) ^ 2) - 2 * (∑ i, g (Z i) * f (Z i)) + ∑ i, g (Z i) ^ 2 := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rwa [he] at this
  have hnorm : 0 ≤ ‖f‖ ^ 2 - 2 * inner ℝ g f + ‖g‖ ^ 2 := by
    rw [real_inner_comm f g, ← norm_sub_sq_real]
    positivity
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hcancel : (1 / (N : ℝ)) * (N * η) = η := by field_simp
  have hval : dotProduct r ((gramF F N Z).mulVec γ) = ∑ i, r i * g (Z i) := by
    simp only [g, dotProduct, rkhs_representer_evaluation]
    rfl
  rw [hval, hstat, hself]
  simp only [← sq]
  have hgap := add_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 1 / N) hsq)
    (mul_nonneg hη hnorm)
  have he :
      (1 / (N : ℝ)) * ((∑ i, g (Z i) ^ 2) + N * η * ‖g‖ ^ 2) -
        ((2 / N) * ((∑ i, g (Z i) * f (Z i)) + N * η * inner ℝ g f) -
          (1 / N) * ∑ i, f (Z i) ^ 2 - η * ‖f‖ ^ 2) =
      (1 / N) * ((∑ i, f (Z i) ^ 2) - 2 * (∑ i, g (Z i) * f (Z i)) +
        ∑ i, g (Z i) ^ 2) + η * (‖f‖ ^ 2 - 2 * inner ℝ g f + ‖g‖ ^ 2) := by
    field_simp
    <;> ring
  linarith only [he, hgap]

/-- If [the sample size is positive](hyp:hN) and [the critic ridge parameter is positive](hyp:hη),
[the evaluation loss equals the residual vector's quadratic form with the critic smoothing matrix, divided by sample size](goal). -/
-- @node: rkhs_profiled_loss
lemma rkhs_profiled_loss (hN : 0 < N) (η : ℝ) (hη : 0 < η)
    (v : Fin N → ℝ) :
    rkhsEvaluationLoss F N Z y η v =
      (1 / N) * dotProduct (y - v) ((criticSmoother F N Z η).mulVec (y - v)) := by
  let r := y - v
  let γ := (gramF F N Z + (N * η) • (1 : Matrix (Fin N) (Fin N) ℝ))⁻¹.mulVec r
  let g : F := ∑ j, γ j • kernelRepresenter F (Z j)
  have hγ := rkhs_critic_normal_equation F N Z hN η hη r
  have hbound := rkhs_critic_maximum F N Z hN η hη.le r γ hγ
  have hb : BddAbove (Set.range fun f : F =>
      (2 / N) * ∑ i, (y i - v i) * f (Z i) - (1 / N) * ∑ i, f (Z i) ^ 2 - η * ‖f‖ ^ 2) :=
    ⟨_, by rintro _ ⟨f, rfl⟩; exact hbound f⟩
  have hv : (criticSmoother F N Z η).mulVec r = (gramF F N Z).mulVec γ := by
    exact (Matrix.mulVec_mulVec r _ _).symm
  change _ = (1 / N) * dotProduct r ((criticSmoother F N Z η).mulVec r)
  rw [hv]
  apply le_antisymm
  · exact ciSup_le hbound
  · have hself := rkhs_critic_stationarity F N Z η r γ hγ g
    have heval : (∑ i, r i * g (Z i)) = dotProduct r ((gramF F N Z).mulVec γ) := by
      simp only [g, dotProduct, rkhs_representer_evaluation]
      rfl
    change (∑ i, r i * g (Z i)) = (∑ i, g (Z i) * g (Z i)) +
      (N * η) * inner ℝ g g at hself
    rw [real_inner_self_eq_norm_sq, heval] at hself
    have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    have hc : (1 / (N : ℝ)) * (N * η) = η := by field_simp
    have heq : (2 / N) * ∑ i, (y i - v i) * g (Z i) -
        (1 / N) * ∑ i, g (Z i) ^ 2 - η * ‖g‖ ^ 2 =
        (1 / N) * dotProduct r ((gramF F N Z).mulVec γ) := by
      change (2 / N) * (∑ i, r i * g (Z i)) - _ - _ = _
      rw [heval]
      simp only [← sq] at hself
      rw [hself]
      field_simp
      <;> ring
    rw [← heq]
    exact le_ciSup hb g

/-- The [computational penalty domain](goal) requires that the [fit penalty weight](hyp:lam) be nonnegative, allowing zero. -/
def ComputationalPenaltyDomain (lam : ℝ) : Prop :=
  0 ≤ lam -- @realizes \lambda(nonnegative finite computational penalty, including zero)

end Papers.TsAdaptiveEstimationInference

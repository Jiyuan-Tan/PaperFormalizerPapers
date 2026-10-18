module
public import Papers.TbsNeuralCausalPi.Helpers.SimulationSamplingConcentration
public import Papers.TbsNeuralCausalPi.Helpers.EstimationLimits
/-! # Polynomial failure bounds at the simulation mesh

These are the numerical steps of the current-class sampling argument. The
mesh controls both parts of the concentration energy, and a sufficiently large
fixed tolerance multiplier absorbs an entropy bound into an inverse-cubic
tail. The table construction and its entropy estimate remain separate tasks.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory Filter
open scoped ENNReal Topology

-- @node: simulation_mesh_latent_energy
/-- If [the sample-size parameter m is at least one](hyp:hm), [the dimension
parameter D is nonnegative](hyp:hD), and [the tolerance rho is at least
$m^{-1/(D+2)}\log m$](hyp:hrho), then [$m^{D/(D+2)}(\log m)^2$ is at most
$m\rho^2$](goal). -/
lemma simulation_mesh_latent_energy {m D rho : ℝ}
    (hm : 1 ≤ m) (hD : 0 ≤ D)
    (hrho : m ^ (-(1 : ℝ) / (D + 2)) * Real.log m ≤ rho) :
    m ^ (D / (D + 2)) * (Real.log m) ^ 2 ≤ m * rho ^ 2 := by
  have hmpos : 0 < m := by linarith
  have hbase : 0 ≤ m ^ (-(1 : ℝ) / (D + 2)) * Real.log m :=
    mul_nonneg (Real.rpow_nonneg hmpos.le _) (Real.log_nonneg hm)
  have heq : m * (m ^ (-(1 : ℝ) / (D + 2)) * Real.log m) ^ 2 =
      m ^ (D / (D + 2)) * (Real.log m) ^ 2 := by
    have hpower : m * (m ^ (-(1 : ℝ) / (D + 2))) ^ 2 = m ^ (D / (D + 2)) := by
      calc
        _ = m ^ (1 + (-(1 : ℝ) / (D + 2)) * 2) := by
          rw [Real.rpow_add hmpos, Real.rpow_one, Real.rpow_mul hmpos.le]
          norm_num
        _ = _ := by
          congr 1
          field_simp
          ring
    rw [mul_pow, ← mul_assoc, hpower]
  rw [← heq]
  exact mul_le_mul_of_nonneg_left (sq_le_sq₀ hbase (hbase.trans hrho) |>.2 hrho) hmpos.le

-- @node: simulation_mesh_depth_energy
/-- If [the sample-size parameter m is at least one](hyp:hm), [the depth
parameter H is nonnegative](hyp:hH), and [the tolerance rho is at least
$H\log m/\sqrt m$](hyp:hrho), then [$H^2(\log m)^2$ is at most $m\rho^2$](goal). -/
lemma simulation_mesh_depth_energy {m H rho : ℝ}
    (hm : 1 ≤ m) (hH : 0 ≤ H)
    (hrho : H * Real.log m / Real.sqrt m ≤ rho) :
    H ^ 2 * (Real.log m) ^ 2 ≤ m * rho ^ 2 := by
  have hmpos : 0 < m := by linarith
  have hs := Real.sq_sqrt hmpos.le
  have hspos := Real.sqrt_pos.mpr hmpos
  have hbase : 0 ≤ H * Real.log m / Real.sqrt m :=
    div_nonneg (mul_nonneg hH (Real.log_nonneg hm)) (Real.sqrt_nonneg _)
  have heq : m * (H * Real.log m / Real.sqrt m) ^ 2 = H ^ 2 * (Real.log m) ^ 2 := by
    rw [div_pow, mul_pow, hs]
    field_simp
  rw [← heq]
  exact mul_le_mul_of_nonneg_left (sq_le_sq₀ hbase (hbase.trans hrho) |>.2 hrho) hmpos.le

-- @node: simulation_mesh_log_energy
/-- If [the sample-size parameter m is at least one](hyp:hm), [the dimension
parameter D is nonnegative](hyp:hD), and [the tolerance rho is at least
$m^{-1/(D+2)}\log m$](hyp:hrho), then [the squared logarithm of m is at most
$m\rho^2$](goal). -/
lemma simulation_mesh_log_energy {m D rho : ℝ}
    (hm : 1 ≤ m) (hD : 0 ≤ D)
    (hrho : m ^ (-(1 : ℝ) / (D + 2)) * Real.log m ≤ rho) :
    (Real.log m) ^ 2 ≤ m * rho ^ 2 := by
  have hp : 1 ≤ m ^ (D / (D + 2)) := Real.one_le_rpow hm (by positivity)
  exact (by nlinarith [sq_nonneg (Real.log m)] :
    (Real.log m) ^ 2 ≤ m ^ (D / (D + 2)) * (Real.log m) ^ 2).trans
      (simulation_mesh_latent_energy hm hD hrho)

-- @node: simulation_exponential_tail_le_inverse_power
/-- Suppose [the sample-size parameter m is at least one](hyp:hm), [the
desired power p is nonnegative](hyp:hp), [the logarithm of m is at least
one](hyp:hlog), [the squared logarithm of m is at most $m\rho^2$](hyp:henergy),
[the entropy is at most $K m\rho^2$](hyp:hentropy), and [the multiplier A
satisfies $K+p\leq cA^2$](hyp:hA). Then [the exponential bound
$\exp(\mathrm{entropy}-cm(A\rho)^2)$ is at most $m^{-p}$](goal). -/
lemma simulation_exponential_tail_le_inverse_power
    {m rho entropy c A K p : ℝ} (hm : 1 ≤ m) (hp : 0 ≤ p)
    (hlog : 1 ≤ Real.log m)
    (henergy : (Real.log m) ^ 2 ≤ m * rho ^ 2)
    (hentropy : entropy ≤ K * (m * rho ^ 2))
    (hA : K + p ≤ c * A ^ 2) :
    Real.exp (entropy - c * m * (A * rho) ^ 2) ≤ m ^ (-p) := by
  have hmpos : 0 < m := by linarith
  have hlogenergy : Real.log m ≤ m * rho ^ 2 := by
    nlinarith [sq_nonneg (Real.log m - 1)]
  have hnonneg : 0 ≤ m * rho ^ 2 := by positivity
  have hcoeff := mul_le_mul_of_nonneg_right hA hnonneg
  have hpenergy := mul_le_mul_of_nonneg_left hlogenergy hp
  rw [Real.rpow_def_of_pos hmpos]
  apply Real.exp_le_exp.mpr
  nlinarith

-- @node: simulation_exists_cubic_tail_multiplier
/-- For [a positive concentration coefficient c](hyp:hc), [there is a positive
multiplier A such that, for every m with m and its logarithm at least one,
every tolerance rho with $(\log m)^2\leq m\rho^2$, and every entropy at most
$Km\rho^2$, the exponential bound $\exp(\mathrm{entropy}-cm(A\rho)^2)$ is
at most $m^{-3}$](goal). -/
lemma simulation_exists_cubic_tail_multiplier {c K : ℝ} (hc : 0 < c) :
    ∃ A : ℝ, 0 < A ∧ ∀ m rho entropy : ℝ,
      1 ≤ m → 1 ≤ Real.log m →
      (Real.log m) ^ 2 ≤ m * rho ^ 2 →
      entropy ≤ K * (m * rho ^ 2) →
      Real.exp (entropy - c * m * (A * rho) ^ 2) ≤ m ^ (-(3 : ℝ)) := by
  let A := Real.sqrt (max 0 (K + 3) / c) + 1
  have hs : 0 ≤ Real.sqrt (max 0 (K + 3) / c) := Real.sqrt_nonneg _
  have hsq := Real.sq_sqrt (show 0 ≤ max 0 (K + 3) / c by positivity)
  have hA : 0 < A := by dsimp [A]; linarith
  have hcoeff : K + 3 ≤ c * A ^ 2 := by
    have hmax := le_max_right 0 (K + 3)
    have hid : c * (max 0 (K + 3) / c) = max 0 (K + 3) := by field_simp
    dsimp [A]
    nlinarith
  exact ⟨A, hA, fun m rho entropy hm hl he hh =>
    simulation_exponential_tail_le_inverse_power hm (by norm_num) hl he hh hcoeff⟩

-- @node: simulation_mesh_joint_energy
/-- If [the sample-size parameter m is at least one](hyp:hm), [the dimension
parameter D is nonnegative](hyp:hD), and [the depth parameter H is
nonnegative](hyp:hH), then [for the mesh
$\rho=m^{-1/(D+2)}\log m+H\log m/\sqrt m$, the combined energy
$m^{D/(D+2)}(\log m)^2+H^2(\log m)^2$ is at most $m\rho^2$](goal). -/
lemma simulation_mesh_joint_energy {m D H : ℝ}
    (hm : 1 ≤ m) (hD : 0 ≤ D) (hH : 0 ≤ H) :
    let rho := m ^ (-(1 : ℝ) / (D + 2)) * Real.log m +
      H * Real.log m / Real.sqrt m
    m ^ (D / (D + 2)) * (Real.log m) ^ 2 + H ^ 2 * (Real.log m) ^ 2 ≤
      m * rho ^ 2 := by
  dsimp only
  have ha : 0 ≤ m ^ (-(1 : ℝ) / (D + 2)) * Real.log m :=
    mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.log_nonneg hm)
  have hb : 0 ≤ H * Real.log m / Real.sqrt m :=
    div_nonneg (mul_nonneg hH (Real.log_nonneg hm)) (Real.sqrt_nonneg _)
  have hfirst := simulation_mesh_latent_energy hm hD (le_refl
    (m ^ (-(1 : ℝ) / (D + 2)) * Real.log m))
  have hsecond := simulation_mesh_depth_energy hm hH (le_refl
    (H * Real.log m / Real.sqrt m))
  have hcross := mul_nonneg (mul_nonneg (show 0 ≤ m by linarith) ha) hb
  nlinarith

-- @node: simulation_mesh_cubic_tail
/-- For [a positive concentration coefficient c](hyp:hc), [there is a positive
multiplier A such that, whenever m and its logarithm are at least one, D and H
are nonnegative, and the entropy is at most $Km\rho^2$ for the mesh
$\rho=m^{-1/(D+2)}\log m+H\log m/\sqrt m$, the exponential bound
$\exp(\mathrm{entropy}-cm(A\rho)^2)$ is at most $m^{-3}$](goal). -/
lemma simulation_mesh_cubic_tail {c K : ℝ} (hc : 0 < c) :
    ∃ A : ℝ, 0 < A ∧ ∀ m D H entropy : ℝ,
      1 ≤ m → 1 ≤ Real.log m → 0 ≤ D → 0 ≤ H →
      let rho := m ^ (-(1 : ℝ) / (D + 2)) * Real.log m +
        H * Real.log m / Real.sqrt m
      entropy ≤ K * (m * rho ^ 2) →
      Real.exp (entropy - c * m * (A * rho) ^ 2) ≤ m ^ (-(3 : ℝ)) := by
  obtain ⟨A, hA, htail⟩ := simulation_exists_cubic_tail_multiplier (K := K) hc
  refine ⟨A, hA, ?_⟩
  intro m D H entropy hm hl hD hH
  dsimp only
  intro hentropy
  apply htail m _ entropy hm hl _ hentropy
  apply simulation_mesh_log_energy hm hD
  have hb : 0 ≤ H * Real.log m / Real.sqrt m :=
    div_nonneg (mul_nonneg hH (Real.log_nonneg hm)) (Real.sqrt_nonneg _)
  linarith

-- @node: consistencyGrowth_simulation_mesh_tendsto_zero
/-- Under [the consistency growth schedule for sample sizes, network widths
and depths, temperature, and regularization](hyp:h), [the simulation mesh
$m^{-1/(\max(1,D_U)+2)}\log m+(1+L_1+L_2)\log m/\sqrt m$ tends to zero
along the schedule](goal). -/
lemma consistencyGrowth_simulation_mesh_tendsto_zero {dU DU : ℕ}
    {m W0 L1 L2 : ℕ → ℕ} {tau lam : ℕ → ℝ}
    (h : ConsistencyGrowthSchedule dU m W0 L1 L2 tau lam) :
    Tendsto (fun r => (m r : ℝ) ^ (-(1 : ℝ) / (max 1 DU + 2)) * Real.log (m r) +
      (1 + (L1 r : ℝ) + L2 r) * Real.log (m r) / Real.sqrt (m r)) atTop (𝓝 0) := by
  have hm := consistencyGrowth_simulation_tendsto h
  have hbase : Tendsto (fun r => (m r : ℝ) ^ (-(1 : ℝ) / (max 1 DU + 2)) *
      Real.log (m r)) atTop (𝓝 0) := by
    simpa only [neg_div, pow_one, Function.comp_def] using
      (estimation_log_pow_mul_neg_rpow_tendsto
        (by positivity : 0 < (1 : ℝ) / (max 1 DU + 2)) 1).comp hm
  have hconstant := estimation_depth_sampling_tendsto (depth := fun _ => (1 : ℝ))
    (p := 0) hm (by norm_num) (by
      simpa only [Real.rpow_zero] using
        (Asymptotics.isBigO_refl (fun _ : ℕ => (1 : ℝ)) atTop))
  have hdepth := consistencyGrowth_depth_sampling_tendsto_zero h
  have hsum := hbase.add (hconstant.add hdepth)
  simp only [zero_add] at hsum
  convert hsum using 1
  ext r
  simp only [Nat.cast_add, add_mul, add_div, one_mul]
  ring

end Papers.TbsNeuralCausalPi

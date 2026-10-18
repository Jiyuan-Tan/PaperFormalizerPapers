module
public import Papers.TbsNeuralCausalPi.Setup.EmpiricalAdmissibility
public import Papers.TbsNeuralCausalPi.Helpers.SimulationTailRates
public import Papers.TbsNeuralCausalPi.Helpers.SimulationIndicatorConcentration
/-! # Entropy absorption at the complete-simulation mesh

The two terms of the prescribed mesh pay for the latent-table entropy and
the squared-depth entropy. These numerical bounds do not supply the remaining
representation pattern count or a pseudo-dimension assumption on a main result.
-/
public section
namespace Papers.TbsNeuralCausalPi

-- @node: simulation_mesh_inv_le_rpow
/-- If [m is at least one](hyp:hm), [D is nonnegative](hyp:_hD),
[log m is at least one](hyp:hl), and [the radius rho is at least
$m^{-1/(D+2)}\log m$](hyp:hrho), then [rho is positive and its reciprocal
is at most $m^{1/(D+2)}$](goal). -/
lemma simulation_mesh_inv_le_rpow {m D rho : ℝ}
    (hm : 1 ≤ m) (_hD : 0 ≤ D) (hl : 1 ≤ Real.log m)
    (hrho : m ^ (-(1 : ℝ) / (D + 2)) * Real.log m ≤ rho) :
    0 < rho ∧ rho⁻¹ ≤ m ^ ((1 : ℝ) / (D + 2)) := by
  have hmpos : 0 < m := by linarith
  have ha : 0 < m ^ (-(1 : ℝ) / (D + 2)) := Real.rpow_pos_of_pos hmpos _
  have har : m ^ (-(1 : ℝ) / (D + 2)) ≤ rho :=
    (le_mul_of_one_le_right ha.le hl).trans hrho
  have hr : 0 < rho := ha.trans_le har
  refine ⟨hr, ?_⟩
  have hi := one_div_le_one_div_of_le ha har
  simpa only [one_div, neg_div, Real.rpow_neg hmpos.le, inv_inv] using hi

-- @node: simulation_mesh_inverse_dimension_le
/-- If [m is at least one](hyp:hm), [D is nonnegative](hyp:hD),
[the integer dimension d is at most D](hyp:hd), [log m is at least
one](hyp:hl), and [rho is at least $m^{-1/(D+2)}\log m$](hyp:hrho),
then [the d-th power of the reciprocal radius is at most
$m^{D/(D+2)}$](goal). -/
lemma simulation_mesh_inverse_dimension_le {m D rho : ℝ} (d : ℕ)
    (hm : 1 ≤ m) (hD : 0 ≤ D) (hd : (d : ℝ) ≤ D) (hl : 1 ≤ Real.log m)
    (hrho : m ^ (-(1 : ℝ) / (D + 2)) * Real.log m ≤ rho) :
    (rho⁻¹) ^ d ≤ m ^ (D / (D + 2)) := by
  obtain ⟨hr, hi⟩ := simulation_mesh_inv_le_rpow hm hD hl hrho
  calc
    (rho⁻¹) ^ d ≤ (m ^ ((1 : ℝ) / (D + 2))) ^ d :=
      pow_le_pow_left₀ (inv_nonneg.mpr hr.le) hi d
    _ = m ^ ((d : ℝ) / (D + 2)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ m)]
      congr 1
      ring
    _ ≤ m ^ (D / (D + 2)) :=
      Real.monotone_rpow_of_base_ge_one hm (div_le_div_of_nonneg_right hd (by positivity))

-- @node: simulation_mesh_log_inverse_le
/-- If [m is at least two](hyp:hm), [D is nonnegative](hyp:hD),
[log m is at least one](hyp:hl), and [rho is at least
$m^{-1/(D+2)}\log m$](hyp:hrho), then [the logarithm of two plus the
reciprocal radius is at most twice log m](goal). -/
lemma simulation_mesh_log_inverse_le {m D rho : ℝ}
    (hm : 2 ≤ m) (hD : 0 ≤ D) (hl : 1 ≤ Real.log m)
    (hrho : m ^ (-(1 : ℝ) / (D + 2)) * Real.log m ≤ rho) :
    Real.log (2 + rho⁻¹) ≤ 2 * Real.log m := by
  obtain ⟨hr, hi⟩ := simulation_mesh_inv_le_rpow (by linarith) hD hl hrho
  have hp : m ^ ((1 : ℝ) / (D + 2)) ≤ m := by
    calc
      _ ≤ m ^ (1 : ℝ) := Real.monotone_rpow_of_base_ge_one (by linarith)
        ((div_le_one (by positivity)).mpr (by linarith))
      _ = m := Real.rpow_one _
  have hb : 2 + rho⁻¹ ≤ m ^ 2 := by nlinarith [hi.trans hp]
  have h := Real.log_le_log (by positivity : 0 < 2 + rho⁻¹) hb
  simpa only [Real.log_pow, Nat.cast_ofNat] using h

-- @node: simulation_mesh_log_depth_le
/-- If [m is at least two](hyp:hm), [D is nonnegative](hyp:hD),
[H is nonnegative](hyp:hH), [H is at most m](hyp:hHm), [log m is at
least one](hyp:hl), and [rho is at least $m^{-1/(D+2)}\log m$](hyp:hrho),
then [the logarithm of two plus H divided by rho is at most three times
log m](goal). -/
lemma simulation_mesh_log_depth_le {m D H rho : ℝ}
    (hm : 2 ≤ m) (hD : 0 ≤ D) (hH : 0 ≤ H) (hHm : H ≤ m)
    (hl : 1 ≤ Real.log m)
    (hrho : m ^ (-(1 : ℝ) / (D + 2)) * Real.log m ≤ rho) :
    Real.log (2 + H / rho) ≤ 3 * Real.log m := by
  obtain ⟨hr, hi⟩ := simulation_mesh_inv_le_rpow (by linarith) hD hl hrho
  have hp : m ^ ((1 : ℝ) / (D + 2)) ≤ m := by
    calc
      _ ≤ m ^ (1 : ℝ) := Real.monotone_rpow_of_base_ge_one (by linarith)
        ((div_le_one (by positivity)).mpr (by linarith))
      _ = m := Real.rpow_one _
  have hratio : H / rho ≤ m ^ 2 := by
    rw [div_eq_mul_inv]
    nlinarith [mul_le_mul hHm (hi.trans hp) (inv_nonneg.mpr hr.le) (by linarith : 0 ≤ m)]
  have hb : 2 + H / rho ≤ m ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg m) (show 0 ≤ m - 2 by linarith)]
  have h := Real.log_le_log (by positivity : 0 < 2 + H / rho) hb
  simpa only [Real.log_pow, Nat.cast_ofNat] using h

-- @node: simulation_mesh_entropy_terms_le
/-- Suppose [m is at least two](hyp:hm), [D is at least one](hyp:hD),
[the integer dimension d is at most D](hyp:hd), [H is nonnegative](hyp:hH),
[H is at most m](hyp:hHm), and [log m is at least one](hyp:hl).
If [rho is at least $m^{-1/(D+2)}\log m$](hyp:hrho) and [at least
$H\log m/\sqrt m$](hyp:hdepth), then [the three entropy terms
$(1+\rho^{-1})\log(2+\rho^{-1})$,
$\rho^{-d}\log^2(2+\rho^{-1})$, and
$H^2\log(2+H/\rho)\log(2+\rho^{-1})$ are bounded respectively by
$4m\rho^2$, $4m\rho^2$, and $6m\rho^2$](goal). -/
lemma simulation_mesh_entropy_terms_le {m D H rho : ℝ} (d : ℕ)
    (hm : 2 ≤ m) (hD : 1 ≤ D) (hd : (d : ℝ) ≤ D)
    (hH : 0 ≤ H) (hHm : H ≤ m) (hl : 1 ≤ Real.log m)
    (hrho : m ^ (-(1 : ℝ) / (D + 2)) * Real.log m ≤ rho)
    (hdepth : H * Real.log m / Real.sqrt m ≤ rho) :
    (1 + rho⁻¹) * Real.log (2 + rho⁻¹) ≤ 4 * (m * rho ^ 2) ∧
    (rho⁻¹) ^ d * (Real.log (2 + rho⁻¹)) ^ 2 ≤ 4 * (m * rho ^ 2) ∧
    H ^ 2 * Real.log (2 + H / rho) * Real.log (2 + rho⁻¹) ≤
      6 * (m * rho ^ 2) := by
  have hm1 : 1 ≤ m := by linarith
  have hD0 : 0 ≤ D := by linarith
  obtain ⟨hr, _⟩ := simulation_mesh_inv_le_rpow hm1 hD0 hl hrho
  have hx := simulation_mesh_log_inverse_le hm hD0 hl hrho
  have hy := simulation_mesh_log_depth_le hm hD0 hH hHm hl hrho
  have hx0 : 0 ≤ Real.log (2 + rho⁻¹) := Real.log_nonneg (by linarith [inv_nonneg.mpr hr.le])
  have hy0 : 0 ≤ Real.log (2 + H / rho) := Real.log_nonneg (by
    linarith [div_nonneg hH hr.le])
  have hlatent := simulation_mesh_latent_energy hm1 hD0 hrho
  have hdeep := simulation_mesh_depth_energy hm1 hH hdepth
  have hp0 : 0 ≤ m ^ (D / (D + 2)) := Real.rpow_nonneg (by linarith) _
  have hp1 : 1 ≤ m ^ (D / (D + 2)) := Real.one_le_rpow hm1 (by positivity)
  have hi := simulation_mesh_inverse_dimension_le 1 hm1 hD0
    (by simpa using hD) hl hrho
  simp only [pow_one] at hi
  have hdgrid := simulation_mesh_inverse_dimension_le d hm1 hD0 hd hl hrho
  have hx2 : (Real.log (2 + rho⁻¹)) ^ 2 ≤ 4 * (Real.log m) ^ 2 := by
    nlinarith
  have hxlinear : Real.log (2 + rho⁻¹) ≤ 2 * (Real.log m) ^ 2 := by
    nlinarith
  have hxy : Real.log (2 + H / rho) * Real.log (2 + rho⁻¹) ≤
      6 * (Real.log m) ^ 2 := by
    have hmul := mul_le_mul hy hx hx0 (by linarith : 0 ≤ 3 * Real.log m)
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · have hmul := mul_le_mul (show 1 + rho⁻¹ ≤ 2 * m ^ (D / (D + 2)) by linarith)
      hxlinear hx0 (by positivity : 0 ≤ 2 * m ^ (D / (D + 2)))
    nlinarith
  · have hmul := mul_le_mul hdgrid hx2 (sq_nonneg _) hp0
    nlinarith
  · have hmul := mul_le_mul_of_nonneg_left hxy (sq_nonneg H)
    nlinarith

-- @node: simulation_mesh_pseudodim_entropy_le
/-- Suppose [m is at least two](hyp:hm), [D is at least one](hyp:hD),
[d is at most D](hyp:hd), [H is nonnegative](hyp:hH), [H is at most
m](hyp:hHm), [log m is at least one](hyp:hl), and [V is nonnegative](hyp:hV).
If [rho is at least $m^{-1/(D+2)}\log m$](hyp:hrho), [rho is at least
$H\log m/\sqrt m$](hyp:hdepth), and [v plus one is at most
$V(\rho^{-d}\log(2+\rho^{-1})+H^2\log(2+H/\rho))$](hyp:hdim), then
[the combined entropy $(1+\rho^{-1})\log(2+\rho^{-1})+
(v+1)\log(2+\rho^{-1})$ is at most $(4+10V)m\rho^2$](goal). -/
lemma simulation_mesh_pseudodim_entropy_le {m D H rho V : ℝ} (d v : ℕ)
    (hm : 2 ≤ m) (hD : 1 ≤ D) (hd : (d : ℝ) ≤ D)
    (hH : 0 ≤ H) (hHm : H ≤ m) (hl : 1 ≤ Real.log m) (hV : 0 ≤ V)
    (hrho : m ^ (-(1 : ℝ) / (D + 2)) * Real.log m ≤ rho)
    (hdepth : H * Real.log m / Real.sqrt m ≤ rho)
    (hdim : (v : ℝ) + 1 ≤ V *
      ((rho⁻¹) ^ d * Real.log (2 + rho⁻¹) + H ^ 2 * Real.log (2 + H / rho))) :
    (1 + rho⁻¹) * Real.log (2 + rho⁻¹) +
        ((v : ℝ) + 1) * Real.log (2 + rho⁻¹) ≤
      (4 + 10 * V) * (m * rho ^ 2) := by
  obtain ⟨hfirst, hgrid, hdeep⟩ :=
    simulation_mesh_entropy_terms_le d hm hD hd hH hHm hl hrho hdepth
  obtain ⟨hr, _⟩ := simulation_mesh_inv_le_rpow (by linarith) (by linarith) hl hrho
  have hx0 : 0 ≤ Real.log (2 + rho⁻¹) := Real.log_nonneg (by linarith [inv_nonneg.mpr hr.le])
  have hcount := mul_le_mul_of_nonneg_right hdim hx0
  have hsum := mul_le_mul_of_nonneg_left (add_le_add hgrid hdeep) hV
  nlinarith

-- @node: simulation_mesh_tolerance_entropy_le
/-- For [a positive radius rho](hyp:hr) and [a tolerance multiplier A at
least one](hyp:hA), [the entropy
$(1+\rho^{-1})\log(2+\rho^{-1})+(v+1)\log(2+(A\rho)^{-1})$
is at most the same expression with A replaced by one](goal). -/
lemma simulation_mesh_tolerance_entropy_le {rho A : ℝ} (v : ℕ)
    (hr : 0 < rho) (hA : 1 ≤ A) :
    (1 + rho⁻¹) * Real.log (2 + rho⁻¹) +
        ((v : ℝ) + 1) * Real.log (2 + (A * rho)⁻¹) ≤
      (1 + rho⁻¹) * Real.log (2 + rho⁻¹) +
        ((v : ℝ) + 1) * Real.log (2 + rho⁻¹) := by
  have hmul : rho ≤ A * rho := by nlinarith
  have hi : (A * rho)⁻¹ ≤ rho⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hr hmul
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.log_le_log (by positivity) (by linarith)

-- @node: simulation_mesh_pseudodim_cubic_tail
/-- Given [a nonnegative entropy coefficient Ctail](hyp:hC), [a positive
concentration coefficient c](hyp:hc), and [a nonnegative dimension coefficient
V](hyp:hV), [there is a multiplier A at least one such that the exponential
tail $\exp\{Ctail[(1+\rho^{-1})\log(2+\rho^{-1})+
(v+1)\log(2+(A\rho)^{-1})]-cm(A\rho)^2\}$ is at most $m^{-3}$
whenever $m\ge2$, $D\ge1$, the nonnegative integer d is at most D,
$0\le H\le m$, $\log m\ge1$, the radius is
$\rho=m^{-1/(D+2)}\log m+H\log m/\sqrt m$, and the nonnegative
integer v satisfies $v+1\le V(\rho^{-d}\log(2+\rho^{-1})+
H^2\log(2+H/\rho))$](goal). -/
lemma simulation_mesh_pseudodim_cubic_tail {Ctail c V : ℝ}
    (hC : 0 ≤ Ctail) (hc : 0 < c) (hV : 0 ≤ V) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (m D H : ℝ) (d v : ℕ),
      2 ≤ m → 1 ≤ D → (d : ℝ) ≤ D → 0 ≤ H → H ≤ m → 1 ≤ Real.log m →
      let rho := m ^ (-(1 : ℝ) / (D + 2)) * Real.log m +
        H * Real.log m / Real.sqrt m
      (v : ℝ) + 1 ≤ V *
        ((rho⁻¹) ^ d * Real.log (2 + rho⁻¹) + H ^ 2 * Real.log (2 + H / rho)) →
      Real.exp (Ctail * ((1 + rho⁻¹) * Real.log (2 + rho⁻¹) +
        ((v : ℝ) + 1) * Real.log (2 + (A * rho)⁻¹)) -
          c * m * (A * rho) ^ 2) ≤ m ^ (-(3 : ℝ)) := by
  let K := Ctail * (4 + 10 * V)
  let A := Real.sqrt (max 0 (K + 3) / c) + 1
  have hs : 0 ≤ Real.sqrt (max 0 (K + 3) / c) := Real.sqrt_nonneg _
  have hsq := Real.sq_sqrt (show 0 ≤ max 0 (K + 3) / c by positivity)
  have hA : 1 ≤ A := by dsimp [A]; linarith
  have hcoeff : K + 3 ≤ c * A ^ 2 := by
    have hmax := le_max_right 0 (K + 3)
    have hid : c * (max 0 (K + 3) / c) = max 0 (K + 3) := by field_simp
    dsimp [A]
    nlinarith
  refine ⟨A, hA, ?_⟩
  intro m D H d v hm hD hd hH hHm hl rho hdim
  have hlatent : m ^ (-(1 : ℝ) / (D + 2)) * Real.log m ≤ rho := by
    dsimp [rho]
    have hpos : 0 ≤ H * Real.log m / Real.sqrt m := by positivity
    linarith
  have hdepth : H * Real.log m / Real.sqrt m ≤ rho := by
    dsimp [rho]
    have hpos : 0 ≤ m ^ (-(1 : ℝ) / (D + 2)) * Real.log m := by positivity
    linarith
  obtain ⟨hr, _⟩ := simulation_mesh_inv_le_rpow (by linarith) (by linarith) hl hlatent
  have hdimEntropy := simulation_mesh_pseudodim_entropy_le d v
    hm hD hd hH hHm hl hV hlatent hdepth hdim
  have htol := simulation_mesh_tolerance_entropy_le v hr hA
  have hentropy := mul_le_mul_of_nonneg_left (htol.trans hdimEntropy) hC
  apply simulation_exponential_tail_le_inverse_power (K := K)
    (by linarith) (by norm_num) hl _ _ hcoeff
  · exact simulation_mesh_log_energy (by linarith) (by linarith) hlatent
  · simpa only [K, mul_assoc] using hentropy

-- @node: uniform_simulation_indicator_mesh_cubic_concentration
/-- Assuming [the Anthony--Bartlett packing bound](hyp:hpacking), [the
Anthony--Bartlett squared-loss bound](hyp:hsquared), and [a nonnegative
dimension coefficient V](hyp:hV), [there is a multiplier A at least one
giving the following uniform deviation bound: for any probability law on a
standard Borel space and any measurable Boolean class with a Borel
parameterization and pseudo-dimension at most v, the probability that some
class member's empirical mean from m independent draws differs from its
population mean by more than $(1+A)\rho$ is at most $m^{-3}$, provided
$m\ge2$, $D\ge1$, the nonnegative integer d is at most D,
$0\le H\le m$, $\log m\ge1$,
$\rho=m^{-1/(D+2)}\log m+H\log m/\sqrt m$, and
$v+1\le V(\rho^{-d}\log(2+\rho^{-1})+H^2\log(2+H/\rho))$](goal). -/
lemma uniform_simulation_indicator_mesh_cubic_concentration
    (hpacking : AnthonyBartlettPacking) (hsquared : AnthonyBartlettSquaredLoss)
    {V : ℝ} (hV : 0 ≤ V) :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ (X : Type) [MeasurableSpace X] [StandardBorelSpace X]
        (mu : MeasureTheory.ProbabilityMeasure X)
        (I : Type*) (B : I → X → Bool) (m d v : ℕ) (D H : ℝ),
        2 ≤ m → 1 ≤ D → (d : ℝ) ≤ D → 0 ≤ H → H ≤ m → 1 ≤ Real.log m →
        let rho := (m : ℝ) ^ (-(1 : ℝ) / (D + 2)) * Real.log m +
          H * Real.log m / Real.sqrt m
        (v : ℝ) + 1 ≤ V *
          ((rho⁻¹) ^ d * Real.log (2 + rho⁻¹) + H ^ 2 * Real.log (2 + H / rho)) →
        Causalean.Stat.Concentration.HasPseudoDimAtMost
          (fun i x => if B i x then (1 : ℝ) else 0) v →
        (∀ i, Measurable (B i)) → BorelParametrizedClass (Set.range B) →
        (MeasureTheory.Measure.pi (fun _ : Fin m => (mu : MeasureTheory.Measure X)))
          {x | ∃ i, rho + A * rho <
            |(∫ y, (if B i y then (1 : ℝ) else 0) ∂(mu : MeasureTheory.Measure X)) -
              (m : ℝ)⁻¹ * ∑ j, if B i (x j) then (1 : ℝ) else 0|} ≤
          ENNReal.ofReal ((m : ℝ) ^ (-(3 : ℝ))) := by
  obtain ⟨Ctail, c, hC, hc, htail⟩ :=
    uniform_simulation_indicator_concentration hpacking hsquared
  obtain ⟨A, hA, hmesh⟩ := simulation_mesh_pseudodim_cubic_tail hC.le hc hV
  refine ⟨A, hA, ?_⟩
  intro X _ _ mu I B m d v D H hm hD hd hH hHm hl rho hdim hv hB hparam
  have hmreal : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hlatent : (m : ℝ) ^ (-(1 : ℝ) / (D + 2)) * Real.log m ≤ rho := by
    dsimp [rho]
    have hpos : 0 ≤ H * Real.log m / Real.sqrt m := by positivity
    linarith
  obtain ⟨hr, _⟩ := simulation_mesh_inv_le_rpow (by linarith) (by linarith) hl hlatent
  have heps : 0 < A * rho := mul_pos (by linarith) hr
  exact (htail X mu I B v hv hB hparam m (by omega) rho (A * rho) hr heps).trans
    (ENNReal.ofReal_le_ofReal (hmesh m D H d v hmreal hD hd hH hHm hl hdim))

end Papers.TbsNeuralCausalPi

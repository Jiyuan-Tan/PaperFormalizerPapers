module

public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Topology.Order.IntermediateValue
public import Papers.HawkesD75660b.Helpers.BorelMoments
public import Papers.HawkesD75660b.Helpers.AnalyticBorel.BorelSeries

/-! The Borel generating function and the restricted principal Lambert inverse. -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology

namespace Papers.HawkesD75660b

-- @env: S4
variable (ρ : ℝ≥0)

/-- For [a nonnegative branching parameter ρ](hyp:ρ) and [an argument x in the
closed unit interval](hyp:x), the [Borel probability generating function](goal)
is the sum over nonnegative integers j of the Borel mass at j times x to the power j.
@realizes x(argument with carrier exactly [0,1]) -/
def borelPGF (x : unitInterval) : ℝ := ∑' j : ℕ, borelMass ρ j * (x : ℝ) ^ j

/-- For [a real argument z at least −exp(−1)](hyp:z), the [principal Lambert
function](goal) is the supremum of the real numbers w at least −1 satisfying
w exp(w) = z.
@realizes \mathsf{W}_0(inverse fiber restricted to w>=-1; domain z>=-exp(-1))
@realizes z(argument with carrier [-exp(-1),infinity)) -/
def lambertW0 (z : Set.Ici (-Real.exp (-1))) : ℝ :=
  sSup {w : ℝ | -1 ≤ w ∧ w * Real.exp w = (z : ℝ)}

-- @node: mul_exp_derivative
/-- [The derivative of w exp(w) at any real w is exp(w)(1 + w)](goal). -/
lemma mul_exp_derivative (w : ℝ) :
    HasDerivAt (fun w : ℝ => w * Real.exp w) (Real.exp w * (1 + w)) w := by
  convert (hasDerivAt_id w).mul (Real.hasDerivAt_exp w) using 1 <;>
    first | rfl | (dsimp; ring)

-- @node: mul_exp_strictMonoOn
/-- [The function w exp(w) is strictly increasing on the real numbers at least −1](goal). -/
lemma mul_exp_strictMonoOn :
    StrictMonoOn (fun w : ℝ => w * Real.exp w) (Set.Ici (-1)) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici (-1))
    (f' := fun w => Real.exp w * (1 + w))
  · fun_prop
  · intro w _
    exact (mul_exp_derivative w).hasDerivWithinAt
  · intro w hw
    have hw' : -1 < w := by simpa only [interior_Ici, Set.mem_Ioi] using hw
    exact mul_pos (Real.exp_pos _) (by linarith)

-- @node: mul_exp_exists
/-- If [z is at least −exp(−1)](hyp:hz), [there is a real w at least −1 with
w exp(w) = z](goal). -/
lemma mul_exp_exists (z : ℝ) (hz : -Real.exp (-1) ≤ z) :
    ∃ w : ℝ, -1 ≤ w ∧ w * Real.exp w = z := by
  have hnonneg : 0 ≤ max z 0 := le_max_right _ _
  have hexp : 1 ≤ Real.exp (max z 0) := Real.one_le_exp_iff.mpr hnonneg
  have hupper : z ≤ max z 0 * Real.exp (max z 0) := by
    calc
      z ≤ max z 0 := le_max_left _ _
      _ = max z 0 * 1 := (mul_one _).symm
      _ ≤ max z 0 * Real.exp (max z 0) := mul_le_mul_of_nonneg_left hexp hnonneg
  have hc : ContinuousOn (fun w : ℝ => w * Real.exp w) (Set.Icc (-1) (max z 0)) := by
    fun_prop
  obtain ⟨w, hw, heq⟩ := intermediate_value_Icc (by linarith : (-1 : ℝ) ≤ max z 0) hc
    (show z ∈ Set.Icc ((-1 : ℝ) * Real.exp (-1)) (max z 0 * Real.exp (max z 0)) from
      ⟨by simpa using hz, hupper⟩)
  exact ⟨w, hw.1, heq⟩

-- @node: lambertW0_spec
/-- For every z at least −exp(−1), [the principal Lambert value is at least −1,
satisfies w exp(w) = z, and is the unique real value at least −1 satisfying
that equation](goal). -/
lemma lambertW0_spec (z : Set.Ici (-Real.exp (-1))) :
    -1 ≤ lambertW0 z ∧ lambertW0 z * Real.exp (lambertW0 z) = (z : ℝ) ∧
      ∀ w : ℝ, -1 ≤ w → w * Real.exp w = (z : ℝ) → w = lambertW0 z := by
  obtain ⟨w, hw, heq⟩ := mul_exp_exists (z : ℝ) z.property
  have hunique : ∀ v : ℝ, -1 ≤ v → v * Real.exp v = (z : ℝ) → v = w := by
    intro v hv hvz
    exact mul_exp_strictMonoOn.injOn hv hw (hvz.trans heq.symm)
  have hset : {v : ℝ | -1 ≤ v ∧ v * Real.exp v = (z : ℝ)} = {w} := by
    ext v
    constructor
    · intro hv
      exact Set.mem_singleton_iff.mpr (hunique v hv.1 hv.2)
    · intro hv
      rcases Set.mem_singleton_iff.mp hv with rfl
      exact ⟨hw, heq⟩
  have hvalue : lambertW0 z = w := by
    simp only [lambertW0, hset, csSup_singleton]
  rw [hvalue]
  exact ⟨hw, heq, hunique⟩

-- @node: borelPGF_equation
/-- If [the branching parameter ρ is subcritical](hyp:hρ), then for every x in
the closed unit interval, [the Borel generating function F satisfies
F(x) = x exp(ρ(F(x) − 1)) and lies between zero and one](goal). -/
lemma borelPGF_equation (hρ : subcritical ρ) (x : unitInterval) :
    borelPGF ρ x = (x : ℝ) * Real.exp ((ρ : ℝ) * (borelPGF ρ x - 1)) ∧
      0 ≤ borelPGF ρ x ∧ borelPGF ρ x ≤ 1 := by
  by_cases hzero : ρ = 0
  · subst ρ
    have hmass (j : ℕ) : borelMass 0 j = if j = 1 then 1 else 0 := by
      cases j with
      | zero => simp [borelMass]
      | succ j => cases j <;> simp [borelMass]
    have hvalue : borelPGF 0 x = (x : ℝ) := by
      simp [borelPGF, hmass]
    rw [hvalue]
    exact ⟨by simp, x.property.1, x.property.2⟩
  · have hpos : 0 < (ρ : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hzero)
    have hlt : (ρ : ℝ) < 1 := by exact_mod_cast hρ
    have hmass (j : ℕ) :
        borelMass ρ j = Papers.HawkesD75660b.AnalyticBorel.borelMass (ρ : ℝ) j := by
      rfl
    have hvalue : borelPGF ρ x =
        Papers.HawkesD75660b.AnalyticBorel.borelPGF (ρ : ℝ) (x : ℝ) := by
      simp only [borelPGF, Papers.HawkesD75660b.AnalyticBorel.borelPGF, hmass]
    rw [hvalue]
    exact Papers.HawkesD75660b.AnalyticBorel.borelPGF_equation ⟨hpos, hlt⟩ x.property

-- @node: borelMass_sum
/-- If [the branching parameter ρ is subcritical](hyp:hρ), [the Borel masses
over all nonnegative integers sum to one](goal). -/
lemma borelMass_sum (hρ : subcritical ρ) : ∑' j, borelMass ρ j = 1 := by
  let x : unitInterval := ⟨1, by constructor <;> norm_num⟩
  have heq := borelPGF_equation ρ hρ x
  have hvalue : borelPGF ρ x = 1 := by
    have hfixed : borelPGF ρ x = Real.exp ((ρ : ℝ) * (borelPGF ρ x - 1)) := by
      simpa only [x, one_mul] using heq.1
    have htangent := Real.add_one_le_exp ((ρ : ℝ) * (borelPGF ρ x - 1))
    rw [← hfixed] at htangent
    have hr : (ρ : ℝ) < 1 := by exact_mod_cast hρ
    have hprod : 0 ≤ (1 - (ρ : ℝ)) * (1 - borelPGF ρ x) :=
      mul_nonneg (by linarith) (by linarith [heq.2.2])
    have hzero : (1 - (ρ : ℝ)) * (1 - borelPGF ρ x) = 0 := by
      nlinarith
    have := (mul_eq_zero.mp hzero).resolve_left (by linarith)
    linarith
  simpa only [borelPGF, x, one_pow, mul_one] using hvalue

-- @node: borelMeasure_probability
/-- If [the branching parameter ρ is subcritical](hyp:hρ), [the Borel measure
with parameter ρ is a probability measure](goal). -/
lemma borelMeasure_probability (hρ : subcritical ρ) :
    IsProbabilityMeasure (borelMeasure ρ) := by
  constructor
  unfold borelMeasure
  rw [Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _),
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (borelMass_nonneg ρ) (borelMass_summable ρ hρ),
    borelMass_sum ρ hρ, ENNReal.ofReal_one]

-- @node: borelPGF_derivative_summable
/-- If [R is nonnegative](hyp:hR) and [ρ exp(1 − ρ) R is less than one](hyp:hRρ),
[the series with terms equal to the Borel mass at j times j times R to the
power j − 1 is summable](goal), where the exponent is zero when j is zero. -/
lemma borelPGF_derivative_summable (R : ℝ) (hR : 0 ≤ R)
    (hRρ : (ρ : ℝ) * Real.exp (1 - (ρ : ℝ)) * R < 1) :
    Summable (fun j : ℕ => borelMass ρ j * j * R ^ (j - 1)) := by
  let q := (ρ : ℝ) * Real.exp (1 - (ρ : ℝ)) * R
  have hq : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [q]; positivity)]
    exact hRρ
  have hs : Summable (fun j : ℕ => (j + 1 : ℝ) * q ^ j) := by
    simpa only [pow_one, add_mul, one_mul, Nat.cast_add, Nat.cast_one] using
      (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hq).add
        (summable_geometric_of_norm_lt_one hq)
  apply (summable_nat_add_iff 1).mp
  apply Summable.of_nonneg_of_le
    (fun j => mul_nonneg (mul_nonneg (borelMass_nonneg ρ _) (by positivity))
      (pow_nonneg hR _)) (fun j => ?_)
    (hs.mul_left (Real.exp (1 - (ρ : ℝ))))
  calc
    borelMass ρ (j + 1) * (j + 1 : ℕ) * R ^ (j + 1 - 1) ≤
        (Real.exp (1 - (ρ : ℝ)) *
          ((ρ : ℝ) * Real.exp (1 - (ρ : ℝ))) ^ j) * (j + 1 : ℕ) * R ^ j := by
      simp only [Nat.add_sub_cancel]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (borelMass_succ_geometric_bound ρ j) (by positivity))
        (pow_nonneg hR _)
    _ = Real.exp (1 - (ρ : ℝ)) * ((j + 1 : ℝ) * q ^ j) := by
      simp only [q, mul_pow, Nat.cast_add, Nat.cast_one]
      ring

-- @node: borelPGF_hasDerivAt_one
/-- If [the branching parameter ρ is subcritical](hyp:hρ), [the real power
series of Borel masses has a derivative at one equal to the sum of j times
the Borel mass at j](goal). -/
lemma borelPGF_hasDerivAt_one (hρ : subcritical ρ) :
    HasDerivAt (fun x : ℝ => ∑' j : ℕ, borelMass ρ j * x ^ j)
      (∑' j : ℕ, borelMass ρ j * j) 1 := by
  let q := (ρ : ℝ) * Real.exp (1 - (ρ : ℝ))
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q < 1 := borel_geometric_ratio_lt_one ρ hρ
  let R : ℝ := 2 / (q + 1)
  have hR : 1 < R := (lt_div_iff₀ (by positivity : 0 < q + 1)).mpr (by linarith)
  have hRq : q * R < 1 := by
    dsimp [R]
    rw [← mul_div_assoc, div_lt_one (by positivity : 0 < q + 1)]
    linarith
  have hs := borelPGF_derivative_summable ρ R (by linarith) hRq
  have hd := hasDerivAt_tsum_of_isPreconnected hs isOpen_Ioo (convex_Ioo (-R) R).isPreconnected
    (g := fun j x => borelMass ρ j * x ^ j)
    (g' := fun j x => borelMass ρ j * ((j : ℝ) * x ^ (j - 1)))
    (fun j x _ => (hasDerivAt_pow j x).const_mul (borelMass ρ j))
    (fun j x hx => ?_) (y₀ := (1 : ℝ)) (y := (1 : ℝ)) (by constructor <;> linarith)
    (by simpa using borelMass_summable ρ hρ) (by constructor <;> linarith)
  · simpa only [one_pow, mul_one] using hd
  · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (borelMass_nonneg ρ j),
      abs_of_nonneg (Nat.cast_nonneg j), abs_pow]
    have hxR : |x| ≤ R := (abs_le.mpr ⟨by linarith [hx.1], le_of_lt hx.2⟩)
    calc
      borelMass ρ j * ((j : ℝ) * |x| ^ (j - 1)) ≤
          borelMass ρ j * ((j : ℝ) * R ^ (j - 1)) := by
        gcongr <;> first | fun_prop | assumption | positivity | exact borelMass_nonneg ρ j
      _ = _ := by ring

-- @node: borelPGF_hasDerivAt
/-- If [the branching parameter ρ is subcritical](hyp:hρ) and [x lies in the
closed unit interval](hyp:hx), [the real power series of Borel masses is
differentiable at x, with derivative equal to the sum of the Borel mass at j
times j times x to the power j − 1](goal), where the exponent is zero when j is zero. -/
lemma borelPGF_hasDerivAt (hρ : subcritical ρ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt (fun x : ℝ => ∑' j : ℕ, borelMass ρ j * x ^ j)
      (∑' j : ℕ, borelMass ρ j * ((j : ℝ) * x ^ (j - 1))) x := by
  let q := (ρ : ℝ) * Real.exp (1 - (ρ : ℝ))
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q < 1 := borel_geometric_ratio_lt_one ρ hρ
  let R : ℝ := 2 / (q + 1)
  have hR : 1 < R := (lt_div_iff₀ (by positivity : 0 < q + 1)).mpr (by linarith)
  have hRq : q * R < 1 := by
    dsimp [R]
    rw [← mul_div_assoc, div_lt_one (by positivity : 0 < q + 1)]
    linarith
  have hs := borelPGF_derivative_summable ρ R (by linarith) hRq
  have hd := hasDerivAt_tsum_of_isPreconnected hs isOpen_Ioo (convex_Ioo (-R) R).isPreconnected
    (g := fun j x => borelMass ρ j * x ^ j)
    (g' := fun j x => borelMass ρ j * ((j : ℝ) * x ^ (j - 1)))
    (fun j x _ => (hasDerivAt_pow j x).const_mul (borelMass ρ j))
    (fun j x hx => ?_) (y₀ := (1 : ℝ)) (y := x) (by constructor <;> linarith)
    (by simpa using borelMass_summable ρ hρ) (by constructor <;> linarith [hx.1, hx.2])
  · exact hd
  · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (borelMass_nonneg ρ j),
      abs_of_nonneg (Nat.cast_nonneg j), abs_pow]
    have hxR : |x| ≤ R := (abs_le.mpr ⟨by linarith [hx.1], le_of_lt hx.2⟩)
    calc
      borelMass ρ j * ((j : ℝ) * |x| ^ (j - 1)) ≤
          borelMass ρ j * ((j : ℝ) * R ^ (j - 1)) := by
        gcongr <;> first | fun_prop | assumption | positivity | exact borelMass_nonneg ρ j
      _ = _ := by ring

-- @node: borel_first_moment
/-- If [the branching parameter ρ is subcritical](hyp:hρ), [the mean of the
Borel measure with parameter ρ is 1 / (1 − ρ)](goal). -/
lemma borel_first_moment (hρ : subcritical ρ) :
    (∫ j : ℕ, (j : ℝ) ∂borelMeasure ρ) = 1 / (1 - (ρ : ℝ)) := by
  let F : ℝ → ℝ := fun x => ∑' j : ℕ, borelMass ρ j * x ^ j
  let M : ℝ := ∑' j : ℕ, borelMass ρ j * j
  have hF : F 1 = 1 := by simpa [F] using borelMass_sum ρ hρ
  have hd : HasDerivAt F M 1 := borelPGF_hasDerivAt_one ρ hρ
  have he : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      F x = x * Real.exp ((ρ : ℝ) * (F x - 1)) := by
    intro x hx
    exact (borelPGF_equation ρ hρ ⟨x, hx⟩).1
  have hrhs := (hasDerivAt_id (1 : ℝ)).mul (((hd.sub_const 1).const_mul (ρ : ℝ)).exp)
  have hsame := hrhs.hasDerivWithinAt.congr_of_mem he (by norm_num : (1 : ℝ) ∈ Set.Icc 0 1)
  have hu := uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1) 1 (by norm_num)
  have hM := (hd.hasDerivWithinAt.derivWithin hu).symm.trans (hsame.derivWithin hu)
  simp only [hF, sub_self, mul_zero, Real.exp_zero, mul_one, one_mul, id_eq] at hM
  have hm : M = 1 / (1 - (ρ : ℝ)) := by
    have hρ' : (ρ : ℝ) < 1 := by exact_mod_cast hρ
    apply (eq_div_iff (by linarith : 1 - (ρ : ℝ) ≠ 0)).mpr
    nlinarith [hM]
  change (∫ j : ℕ, (j : ℝ) ∂Measure.sum
    (fun j => ENNReal.ofReal (borelMass ρ j) • Measure.dirac j)) = _
  rw [integral_sum_dirac (fun j => ENNReal.ofReal_ne_top)]
  simpa only [ENNReal.toReal_ofReal (borelMass_nonneg ρ _), smul_eq_mul] using hm

/-- For [a nonnegative branching parameter ρ](hyp:ρ) and [a real input u](hyp:u),
the [forward substitution](goal) is u exp(−u) divided by ρ exp(−ρ). -/
def forwardSubstitution (u : ℝ) : ℝ :=
  u * Real.exp (-u) / ((ρ : ℝ) * Real.exp (-(ρ : ℝ)))

-- @node: forwardSubstitution_derivative
/-- If [ρ is strictly positive](hyp:hpos), [the forward substitution has
derivative exp(−u)(1 − u) / (ρ exp(−ρ)) at every real u](goal). -/
lemma forwardSubstitution_derivative (hpos : 0 < ρ) (u : ℝ) :
    HasDerivAt (forwardSubstitution ρ)
      (Real.exp (-u) * (1-u) / ((ρ : ℝ) * Real.exp (-(ρ : ℝ)))) u := by
  convert ((hasDerivAt_id u).mul ((hasDerivAt_id u).neg.exp)).div_const
    ((ρ : ℝ) * Real.exp (-(ρ : ℝ))) using 1 <;>
    first | rfl | (simp only [Pi.neg_apply, id_eq]; ring)

-- @node: forwardSubstitution_range
/-- If [ρ is subcritical](hyp:hρ), [ρ is strictly positive](hyp:hpos), and
[u lies between zero and ρ](hyp:hu), [the forward substitution at u lies
between zero and one](goal). -/
lemma forwardSubstitution_range (hρ : subcritical ρ) (hpos : 0 < ρ)
    {u : ℝ} (hu : u ∈ Set.Icc 0 (ρ : ℝ)) :
    forwardSubstitution ρ u ∈ Set.Icc (0 : ℝ) 1 := by
  have hρ' : (ρ : ℝ) < 1 := by exact_mod_cast hρ
  have hmono : MonotoneOn (forwardSubstitution ρ) (Set.Icc 0 (ρ : ℝ)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 (ρ : ℝ))
    · unfold forwardSubstitution
      fun_prop
    · intro x hx
      exact (forwardSubstitution_derivative ρ hpos x).hasDerivWithinAt
    · intro x hx
      have hxρ : x ≤ (ρ : ℝ) := (interior_subset hx).2
      exact div_nonneg (mul_nonneg (Real.exp_pos _).le (by linarith)) (by positivity)
  constructor
  · exact div_nonneg (mul_nonneg hu.1 (Real.exp_pos _).le) (by positivity)
  · have hbound := hmono hu ⟨ρ.coe_nonneg, le_rfl⟩ hu.2
    have hden : (ρ : ℝ) * Real.exp (-(ρ : ℝ)) ≠ 0 := by positivity
    simpa only [forwardSubstitution, div_self hden] using hbound

-- @node: borelPGF_weighted_identity
/-- If [ρ is subcritical](hyp:hρ) and [x lies in the closed unit interval](hyp:hx),
[the sum of j times the Borel mass at j times x to the power j, multiplied by
1 − ρ F(x), equals the Borel generating function F(x)](goal). -/
lemma borelPGF_weighted_identity (hρ : subcritical ρ) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (∑' j : ℕ, borelMass ρ j * (j : ℝ) * x ^ j) *
      (1 - (ρ : ℝ) * borelPGF ρ ⟨x, hx⟩) = borelPGF ρ ⟨x, hx⟩ := by
  let F : ℝ → ℝ := fun y => ∑' j : ℕ, borelMass ρ j * y ^ j
  let D : ℝ := ∑' j : ℕ, borelMass ρ j * ((j : ℝ) * x ^ (j - 1))
  have hd : HasDerivAt F D x := borelPGF_hasDerivAt ρ hρ hx
  have he : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      F y = y * Real.exp ((ρ : ℝ) * (F y - 1)) := by
    intro y hy
    exact (borelPGF_equation ρ hρ ⟨y, hy⟩).1
  have hrhs := (hasDerivAt_id x).mul (((hd.sub_const 1).const_mul (ρ : ℝ)).exp)
  have hsame := hrhs.hasDerivWithinAt.congr_of_mem he hx
  have hu := uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1) x hx
  have hD := (hd.hasDerivWithinAt.derivWithin hu).symm.trans (hsame.derivWithin hu)
  have hweighted : (∑' j : ℕ, borelMass ρ j * (j : ℝ) * x ^ j) = x * D := by
    dsimp only [D]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro j
    cases j with
    | zero => simp
    | succ j => simp only [Nat.add_sub_cancel, pow_succ]; ring
  change _ = F x
  rw [hweighted]
  have hFx := he x hx
  dsimp only [id_eq] at hD
  change x * D * (1 - (ρ : ℝ) * F x) = F x
  have hm : x * D = F x + (ρ : ℝ) * F x * (x * D) := by
    calc
      x * D = x * Real.exp ((ρ : ℝ) * (F x - 1)) +
          (ρ : ℝ) * (x * Real.exp ((ρ : ℝ) * (F x - 1))) * (x * D) := by
        conv_lhs => rw [hD]
        ring
      _ = _ := by rw [← hFx]
  nlinarith [hm]

-- @node: borelPGF_forwardSubstitution
/-- If [ρ is subcritical](hyp:hρ), [ρ is strictly positive](hyp:hpos), and
[u lies between zero and ρ](hyp:hu), [the Borel generating function evaluated
at u exp(−u) / (ρ exp(−ρ)) equals u / ρ](goal). -/
lemma borelPGF_forwardSubstitution (hρ : subcritical ρ) (hpos : 0 < ρ)
    {u : ℝ} (hu : u ∈ Set.Icc 0 (ρ : ℝ)) :
    borelPGF ρ ⟨forwardSubstitution ρ u, forwardSubstitution_range ρ hρ hpos hu⟩ =
      u / (ρ : ℝ) := by
  by_cases hz : u = 0
  · subst u
    simp only [forwardSubstitution, zero_mul, zero_div, borelPGF]
    have ht (j : ℕ) : borelMass ρ j * (0 : ℝ) ^ j = 0 := by
      cases j <;> simp [borelMass]
    simp only [ht, tsum_zero]
  · have hr : 0 < (ρ : ℝ) := by exact_mod_cast hpos
    have hs : (ρ : ℝ) < 1 := by exact_mod_cast hρ
    exact AnalyticBorel.borelPGF_tilt_value ⟨hr, hs⟩
      (lt_of_le_of_ne hu.1 (Ne.symm hz)) hu.2 (by
        dsimp [forwardSubstitution]
        field_simp)

end Papers.HawkesD75660b

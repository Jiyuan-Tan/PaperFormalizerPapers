module
public import Papers.TbsNeuralCausalPi.Setup.SCM
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.MeasureTheory.Integral.IntegrableOn
/-! # Clamped finite-grid mechanisms for the backdoor counterexample

Treatment labels are one and two. The outcome interpolates the prescribed
values at covariate minus one and zero and at binary latent coordinates.
All regularity bounds hold on the entire real input space.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open scoped NNReal
noncomputable section

-- @node: counterexampleClamp
/-- For [a real input](hyp:x), [the unit-interval clamp](goal) truncates values
below zero to zero and values above one to one. -/
def counterexampleClamp (x : ℝ) : ℝ := max 0 (min x 1)

-- @node: counterexampleClamp_bounds
/-- [Clamping any real input produces a value between zero and one, inclusive](goal). -/
lemma counterexampleClamp_bounds (x : ℝ) :
    counterexampleClamp x ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩

-- @node: counterexampleClamp_fixes
/-- If [the input lies between zero and one, inclusive](hyp:hx),
[clamping leaves it unchanged](goal). -/
lemma counterexampleClamp_fixes {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    counterexampleClamp x = x := by
  unfold counterexampleClamp
  rw [min_eq_left hx.2, max_eq_right hx.1]

-- @node: counterexampleClamp_lipschitz
/-- [The unit-interval clamp is Lipschitz with constant one](goal). -/
lemma counterexampleClamp_lipschitz : LipschitzWith 1 counterexampleClamp := by
  exact (LipschitzWith.id.min_const 1).const_max 0

-- @node: counterexampleClamp_measurable
/-- [The unit-interval clamp is measurable](goal). -/
@[fun_prop] lemma counterexampleClamp_measurable : Measurable counterexampleClamp := by
  unfold counterexampleClamp
  fun_prop

-- @node: counterexampleBlend
/-- Given [an interpolation weight](hyp:t), [a first endpoint value](hyp:a),
and [a second endpoint value](hyp:b), [their blend](goal) is the weight times
the first value plus one minus the weight times the second value. -/
def counterexampleBlend (t a b : ℝ) : ℝ := t * a + (1-t) * b

-- @node: counterexampleBlend_bounds
/-- If [the interpolation weight lies in the unit interval](hyp:ht),
[the first endpoint lies in the unit interval](hyp:ha), and
[the second endpoint lies in the unit interval](hyp:hb),
[their blend also lies in the unit interval](goal). -/
lemma counterexampleBlend_bounds {t a b : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    counterexampleBlend t a b ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact add_nonneg (mul_nonneg ht.1 ha.1) (mul_nonneg (sub_nonneg.mpr ht.2) hb.1)
  · have h := add_le_add (mul_le_mul_of_nonneg_left ha.2 ht.1)
      (mul_le_mul_of_nonneg_left hb.2 (sub_nonneg.mpr ht.2))
    simpa [counterexampleBlend] using h

-- @node: counterexampleBlend_dist
/-- If [the first blend's weight lies in the unit interval](hyp:ht) and
[the second blend's first endpoint](hyp:hc) and [second endpoint](hyp:hd)
both lie in the unit interval, [the absolute difference between the blends
is at most the sum of the absolute changes in weight and endpoint values](goal). -/
lemma counterexampleBlend_dist {t a b s c d : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hc : c ∈ Set.Icc (0 : ℝ) 1)
    (hd : d ∈ Set.Icc (0 : ℝ) 1) :
    |counterexampleBlend t a b - counterexampleBlend s c d| ≤
      |t-s| + |a-c| + |b-d| := by
  have hcd : |c-d| ≤ 1 := abs_le.mpr ⟨by linarith [hc.1, hd.2], by linarith [hc.2, hd.1]⟩
  calc
    _ = |(t-s)*(c-d) + t*(a-c) + (1-t)*(b-d)| := by
      congr 1
      unfold counterexampleBlend
      ring
    _ ≤ |(t-s)*(c-d)| + |t*(a-c)| + |(1-t)*(b-d)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ |t-s| + |a-c| + |b-d| := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg ht.1,
        abs_of_nonneg (sub_nonneg.mpr ht.2)]
      gcongr
      · exact mul_le_of_le_one_right (abs_nonneg _) hcd
      · exact mul_le_of_le_one_left (abs_nonneg _) ht.2
      · exact mul_le_of_le_one_left (abs_nonneg _) (by linarith [ht.1])

-- @node: counterexampleBlend_lipschitz
/-- If [the weight function is Lipschitz with its given constant](hyp:ht),
[the first endpoint function is Lipschitz with its given constant](hyp:ha), and
[the second endpoint function is Lipschitz with its given constant](hyp:hb),
and [the weight](hyp:htb), [first endpoint](hyp:hab), and [second endpoint](hyp:hbb)
each stay in the unit interval, [their pointwise blend is Lipschitz with
constant equal to the sum of the three constants](goal). -/
lemma counterexampleBlend_lipschitz {E : Type*} [PseudoMetricSpace E]
    {t a b : E → ℝ} {Kt Ka Kb : ℝ≥0}
    (ht : LipschitzWith Kt t) (ha : LipschitzWith Ka a) (hb : LipschitzWith Kb b)
    (htb : ∀ x, t x ∈ Set.Icc (0 : ℝ) 1)
    (hab : ∀ x, a x ∈ Set.Icc (0 : ℝ) 1)
    (hbb : ∀ x, b x ∈ Set.Icc (0 : ℝ) 1) :
    LipschitzWith (Kt + Ka + Kb) (fun x => counterexampleBlend (t x) (a x) (b x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := counterexampleBlend_dist (a := a x) (b := b x) (s := t y)
    (htb x) (hab y) (hbb y)
  simp only [← Real.dist_eq] at h
  exact h.trans (by
    simpa only [NNReal.coe_add, add_mul] using
      add_le_add (add_le_add (ht.dist_le_mul x y) (ha.dist_le_mul x y)) (hb.dist_le_mul x y))

-- @node: counterexampleTrueOutcome
/-- For [a vector containing a covariate, a one-based treatment label, and two
latent noise values](hyp:z), [the limiting outcome mechanism](goal) blends
the clamped treatment minus one with a treatment-weighted blend of the clamped
noises, using the clamped negative covariate as the outer weight. -/
def counterexampleTrueOutcome (z : L1Vec 4) : ℝ :=
  counterexampleBlend (counterexampleClamp (-z.ofLp 0))
    (counterexampleClamp (z.ofLp 1 - 1))
    (counterexampleBlend (counterexampleClamp (z.ofLp 1 - 1))
      (counterexampleClamp (z.ofLp 2)) (counterexampleClamp (z.ofLp 3)))

-- @node: counterexampleTrueOutcome_bounds
/-- [The limiting outcome lies between zero and one, inclusive, for every
covariate, treatment, and pair of latent noise inputs](goal). -/
lemma counterexampleTrueOutcome_bounds (z : L1Vec 4) :
    counterexampleTrueOutcome z ∈ Set.Icc (0 : ℝ) 1 := by
  exact counterexampleBlend_bounds (counterexampleClamp_bounds _)
    (counterexampleClamp_bounds _) (counterexampleBlend_bounds
      (counterexampleClamp_bounds _) (counterexampleClamp_bounds _) (counterexampleClamp_bounds _))

-- @node: counterexampleCoordinate_lipschitz
/-- [Extracting any coordinate from a vector is Lipschitz with constant one
under the sum-of-absolute-differences distance](goal). -/
lemma counterexampleCoordinate_lipschitz {d : ℕ} (j : Fin d) :
    LipschitzWith 1 (fun z : L1Vec d => z.ofLp j) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa using PiLp.dist_apply_le x y j

-- @node: counterexampleTrueOutcome_lipschitz
/-- [The limiting outcome mechanism is Lipschitz with constant five under the
sum-of-absolute-differences distance on its four inputs](goal). -/
lemma counterexampleTrueOutcome_lipschitz : LipschitzWith 5 counterexampleTrueOutcome := by
  have hp := counterexampleCoordinate_lipschitz (d := 4)
  have hx : LipschitzWith 1 (fun z : L1Vec 4 => counterexampleClamp (-z.ofLp 0)) := by
    simpa [Function.comp_def, Pi.neg_apply] using counterexampleClamp_lipschitz.comp (hp 0).neg
  have ht : LipschitzWith 1 (fun z : L1Vec 4 => counterexampleClamp (z.ofLp 1-1)) := by
    have hshift : LipschitzWith 1 (fun z : L1Vec 4 => z.ofLp 1 - 1) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa only [Real.dist_eq, sub_sub_sub_cancel_right, NNReal.coe_one, one_mul] using (hp 1).dist_le_mul x y
    simpa [Function.comp_def] using counterexampleClamp_lipschitz.comp hshift
  have hu (j : Fin 4) : LipschitzWith 1 (fun z : L1Vec 4 => counterexampleClamp (z.ofLp j)) := by
    simpa [Function.comp_def] using counterexampleClamp_lipschitz.comp (hp j)
  have hi := counterexampleBlend_lipschitz ht (hu 2) (hu 3)
    (fun _ => counterexampleClamp_bounds _) (fun _ => counterexampleClamp_bounds _)
    (fun _ => counterexampleClamp_bounds _)
  have h := counterexampleBlend_lipschitz hx ht hi
    (fun _ => counterexampleClamp_bounds _) (fun _ => counterexampleClamp_bounds _)
    (fun _ => counterexampleBlend_bounds (counterexampleClamp_bounds _)
      (counterexampleClamp_bounds _) (counterexampleClamp_bounds _))
  norm_num at h
  exact h

-- @node: counterexampleTrueOutcome_measurable
/-- [The limiting outcome mechanism is measurable](goal). -/
@[fun_prop] lemma counterexampleTrueOutcome_measurable : Measurable counterexampleTrueOutcome := by
  unfold counterexampleTrueOutcome counterexampleBlend
  fun_prop

-- @node: counterexampleTrueOutcome_at_negative
/-- If [the covariate equals minus one](hyp:hx) and [the treatment input lies
between one and two, inclusive](hyp:ht), [the limiting outcome equals the
treatment input minus one](goal). -/
lemma counterexampleTrueOutcome_at_negative (z : L1Vec 4) (hx : z.ofLp 0 = -1)
    (ht : z.ofLp 1 ∈ Set.Icc (1 : ℝ) 2) :
    counterexampleTrueOutcome z = z.ofLp 1 - 1 := by
  have ht' : z.ofLp 1 - 1 ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  unfold counterexampleTrueOutcome
  rw [hx, counterexampleClamp_fixes ht']
  norm_num [counterexampleClamp, counterexampleBlend]

-- @node: counterexampleTrueOutcome_at_zero
/-- If [the covariate is zero](hyp:hx), [the treatment label is one or two](hyp:ht),
and [the first latent noise](hyp:ha) and [the second latent noise](hyp:hb) lie
in the unit interval, [the limiting outcome equals the first noise for
treatment two and the second noise for treatment one](goal). -/
lemma counterexampleTrueOutcome_at_zero (z : L1Vec 4) (hx : z.ofLp 0 = 0)
    (ht : z.ofLp 1 = 1 ∨ z.ofLp 1 = 2)
    (ha : z.ofLp 2 ∈ Set.Icc (0 : ℝ) 1) (hb : z.ofLp 3 ∈ Set.Icc (0 : ℝ) 1) :
    counterexampleTrueOutcome z = if z.ofLp 1 = 2 then z.ofLp 2 else z.ofLp 3 := by
  unfold counterexampleTrueOutcome
  rw [counterexampleClamp_fixes ha, counterexampleClamp_fixes hb, hx]
  rcases ht with ht | ht <;> norm_num [ht, counterexampleBlend, counterexampleClamp]


-- @node: counterexampleTrueTreatmentProbability
/-- At [a real covariate value](hyp:x), [the limiting probability of treatment
two](goal) is one half plus one eighth of one minus the clamped negative covariate. -/
def counterexampleTrueTreatmentProbability (x : ℝ) : ℝ :=
  1/2 + (1-counterexampleClamp (-x))/8

-- @node: counterexampleTrueTreatmentProbability_bounds
/-- [The limiting probability of treatment two lies between one half and
five eighths, inclusive, at every covariate value](goal). -/
lemma counterexampleTrueTreatmentProbability_bounds (x : ℝ) :
    counterexampleTrueTreatmentProbability x ∈ Set.Icc (1/2 : ℝ) (5/8) := by
  have h := counterexampleClamp_bounds (-x)
  constructor <;> dsimp [counterexampleTrueTreatmentProbability] <;> linarith [h.1, h.2]

-- @node: counterexampleTrueTreatmentProbability_lipschitz
/-- [The limiting probability of treatment two is Lipschitz in the covariate
with constant one eighth](goal). -/
lemma counterexampleTrueTreatmentProbability_lipschitz :
    LipschitzWith (1/8) counterexampleTrueTreatmentProbability := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := counterexampleClamp_lipschitz.dist_le_mul (-x) (-y)
  simp only [Real.dist_eq, NNReal.coe_one, one_mul, neg_sub_neg, abs_sub_comm y x] at h
  have heq : counterexampleTrueTreatmentProbability x - counterexampleTrueTreatmentProbability y =
      -(counterexampleClamp (-x)-counterexampleClamp (-y))/8 := by
    unfold counterexampleTrueTreatmentProbability
    ring
  rw [Real.dist_eq, heq, abs_div, abs_neg]
  norm_num [Real.dist_eq]
  linarith

-- @node: counterexampleTrueTreatmentProbability_measurable
/-- [The limiting probability of treatment two is a measurable function of
the covariate](goal). -/
@[fun_prop] lemma counterexampleTrueTreatmentProbability_measurable :
    Measurable counterexampleTrueTreatmentProbability := by
  unfold counterexampleTrueTreatmentProbability
  fun_prop

-- @node: counterexampleTrueTreatmentProbability_values
/-- [The limiting probability of treatment two equals one half at covariate
minus one and five eighths at covariate zero](goal). -/
lemma counterexampleTrueTreatmentProbability_values :
    counterexampleTrueTreatmentProbability (-1) = 1/2 ∧
      counterexampleTrueTreatmentProbability 0 = 5/8 := by
  norm_num [counterexampleTrueTreatmentProbability, counterexampleClamp]

-- @node: counterexampleTruePropensity
/-- At [a real covariate value](hyp:x), [the limiting propensity vector](goal)
contains the probabilities of treatment one and treatment two, in that order:
one minus the limiting probability of treatment two, followed by that probability. -/
def counterexampleTruePropensity (x : ℝ) : L1Vec 2 :=
  WithLp.toLp 1 (fun j => if j = 0 then
    1-counterexampleTrueTreatmentProbability x else counterexampleTrueTreatmentProbability x)

-- @node: counterexampleTruePropensity_simplex
/-- [At every covariate value, the limiting propensity vector has nonnegative
components that sum to one](goal). -/
lemma counterexampleTruePropensity_simplex (x : ℝ) :
    (counterexampleTruePropensity x).ofLp ∈ stdSimplex ℝ (Fin 2) := by
  have h := counterexampleTrueTreatmentProbability_bounds x
  constructor
  · intro j
    fin_cases j <;> dsimp [counterexampleTruePropensity] <;> linarith [h.1, h.2]
  · simp [counterexampleTruePropensity, Fin.sum_univ_two]

-- @node: counterexampleTruePropensity_lipschitz
/-- [The limiting propensity vector is Lipschitz in the covariate with constant
one quarter, measuring vector differences by the sum of absolute component differences](goal). -/
lemma counterexampleTruePropensity_lipschitz : LipschitzWith (1/4) counterexampleTruePropensity := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := counterexampleTrueTreatmentProbability_lipschitz.dist_le_mul x y
  rw [PiLp.dist_eq_of_L1, Fin.sum_univ_two]
  norm_num [counterexampleTruePropensity, Real.dist_eq] at h ⊢
  rw [show 1-counterexampleTrueTreatmentProbability x +
      counterexampleTrueTreatmentProbability y - 1 =
      -(counterexampleTrueTreatmentProbability x-counterexampleTrueTreatmentProbability y) by ring,
    abs_neg]
  linarith

-- @node: counterexampleTruePropensity_measurable
/-- [The limiting propensity vector is a measurable function of the covariate](goal). -/
@[fun_prop] lemma counterexampleTruePropensity_measurable : Measurable counterexampleTruePropensity := by
  exact counterexampleTruePropensity_lipschitz.continuous.measurable

-- @node: counterexampleApproxOutcome
/-- For [a real scale parameter](hyp:delta) and [a vector containing a covariate
and a one-based treatment input](hyp:z), [the approximating outcome mechanism](goal)
blends the clamped treatment minus one with the clamped covariate divided by
the scale, using the clamped negative covariate as the weight. -/
def counterexampleApproxOutcome (delta : ℝ) (z : L1Vec 2) : ℝ :=
  counterexampleBlend (counterexampleClamp (-z.ofLp 0))
    (counterexampleClamp (z.ofLp 1-1)) (counterexampleClamp (z.ofLp 0/delta))

-- @node: counterexampleApproxOutcome_bounds
/-- [The approximating outcome lies between zero and one, inclusive, for every
real scale parameter and every covariate and treatment input](goal). -/
lemma counterexampleApproxOutcome_bounds (delta : ℝ) (z : L1Vec 2) :
    counterexampleApproxOutcome delta z ∈ Set.Icc (0 : ℝ) 1 := by
  exact counterexampleBlend_bounds (counterexampleClamp_bounds _)
    (counterexampleClamp_bounds _) (counterexampleClamp_bounds _)

-- @node: counterexampleApproxOutcome_measurable
/-- [For every real scale parameter, the approximating outcome is a measurable
function of the covariate and treatment input](goal). -/
@[fun_prop] lemma counterexampleApproxOutcome_measurable (delta : ℝ) :
    Measurable (counterexampleApproxOutcome delta) := by
  unfold counterexampleApproxOutcome counterexampleBlend
  fun_prop

-- @node: counterexampleScaledClamp_lipschitz
/-- If [the scale parameter is positive](hyp:hdelta), [dividing a real input
by that scale and then clamping is Lipschitz with constant equal to the
reciprocal of the scale](goal). -/
lemma counterexampleScaledClamp_lipschitz (delta : ℝ) (hdelta : 0 < delta) :
    LipschitzWith (delta.toNNReal⁻¹) (fun x : ℝ => counterexampleClamp (x/delta)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := counterexampleClamp_lipschitz.dist_le_mul (x/delta) (y/delta)
  simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h
  rw [← sub_div, abs_div, abs_of_pos hdelta] at h
  simpa [Real.dist_eq, Real.coe_toNNReal _ hdelta.le, div_eq_mul_inv, mul_comm] using h

-- @node: counterexampleApproxOutcome_lipschitz
/-- If [the scale parameter is positive](hyp:hdelta), [the approximating outcome
is Lipschitz with constant two plus the reciprocal of the scale, under the
sum-of-absolute-differences distance on covariate and treatment inputs](goal). -/
lemma counterexampleApproxOutcome_lipschitz (delta : ℝ) (hdelta : 0 < delta) :
    LipschitzWith (2+delta.toNNReal⁻¹) (counterexampleApproxOutcome delta) := by
  have hp := counterexampleCoordinate_lipschitz (d := 2)
  have hx : LipschitzWith 1 (fun z : L1Vec 2 => counterexampleClamp (-z.ofLp 0)) := by
    simpa [Function.comp_def, Pi.neg_apply] using counterexampleClamp_lipschitz.comp (hp 0).neg
  have ht : LipschitzWith 1 (fun z : L1Vec 2 => counterexampleClamp (z.ofLp 1-1)) := by
    have hshift : LipschitzWith 1 (fun z : L1Vec 2 => z.ofLp 1 - 1) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa only [Real.dist_eq, sub_sub_sub_cancel_right, NNReal.coe_one, one_mul] using (hp 1).dist_le_mul x y
    simpa [Function.comp_def] using counterexampleClamp_lipschitz.comp hshift
  have hz : LipschitzWith (delta.toNNReal⁻¹)
      (fun z : L1Vec 2 => counterexampleClamp (z.ofLp 0/delta)) := by
    simpa [Function.comp_def] using (counterexampleScaledClamp_lipschitz delta hdelta).comp (hp 0)
  have h := counterexampleBlend_lipschitz hx ht hz
    (fun _ => counterexampleClamp_bounds _) (fun _ => counterexampleClamp_bounds _)
    (fun _ => counterexampleClamp_bounds _)
  norm_num at h
  exact h

-- @node: counterexampleApproxOutcome_at_negative
/-- If [the covariate equals minus one](hyp:hx) and [the treatment input lies
between one and two, inclusive](hyp:ht), [the approximating outcome equals
the treatment input minus one for every real scale parameter](goal). -/
lemma counterexampleApproxOutcome_at_negative (delta : ℝ) (z : L1Vec 2)
    (hx : z.ofLp 0 = -1) (ht : z.ofLp 1 ∈ Set.Icc (1 : ℝ) 2) :
    counterexampleApproxOutcome delta z = z.ofLp 1 - 1 := by
  have ht' : z.ofLp 1 - 1 ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  unfold counterexampleApproxOutcome
  rw [hx, counterexampleClamp_fixes ht']
  norm_num [counterexampleClamp, counterexampleBlend]

-- @node: counterexampleApproxOutcome_at_zero
/-- If [the covariate equals zero](hyp:hx), [the approximating outcome equals
zero for every real scale parameter and treatment input](goal). -/
lemma counterexampleApproxOutcome_at_zero (delta : ℝ) (z : L1Vec 2) (hx : z.ofLp 0 = 0) :
    counterexampleApproxOutcome delta z = 0 := by
  norm_num [counterexampleApproxOutcome, hx, counterexampleClamp, counterexampleBlend]

-- @node: counterexampleApproxOutcome_at_delta
/-- If [the scale parameter is positive](hyp:hdelta) and [the covariate equals
that scale](hyp:hx), [the approximating outcome equals one regardless of the
treatment input](goal). -/
lemma counterexampleApproxOutcome_at_delta (delta : ℝ) (hdelta : 0 < delta)
    (z : L1Vec 2) (hx : z.ofLp 0 = delta) : counterexampleApproxOutcome delta z = 1 := by
  have hn : counterexampleClamp (-delta) = 0 := by
    unfold counterexampleClamp
    rw [min_eq_left (by linarith), max_eq_left (by linarith)]
  unfold counterexampleApproxOutcome
  rw [hx, hn, div_self (ne_of_gt hdelta)]
  norm_num [counterexampleClamp, counterexampleBlend]


-- @node: counterexampleApproxTreatmentProbability
/-- For [a real scale parameter](hyp:delta) and [a real covariate value](hyp:x),
[the approximating probability of treatment two](goal) is one half plus one
quarter of the clamped ratio of covariate to scale. -/
def counterexampleApproxTreatmentProbability (delta x : ℝ) : ℝ :=
  1/2 + counterexampleClamp (x/delta)/4

-- @node: counterexampleApproxTreatmentProbability_bounds
/-- [The approximating probability of treatment two lies between one half and
three quarters, inclusive, for every real scale and covariate value](goal). -/
lemma counterexampleApproxTreatmentProbability_bounds (delta x : ℝ) :
    counterexampleApproxTreatmentProbability delta x ∈ Set.Icc (1/2 : ℝ) (3/4) := by
  have h := counterexampleClamp_bounds (x/delta)
  constructor <;> dsimp [counterexampleApproxTreatmentProbability] <;> linarith [h.1, h.2]

-- @node: counterexampleApproxTreatmentProbability_lipschitz
/-- If [the scale parameter is positive](hyp:hdelta), [the approximating
probability of treatment two is Lipschitz in the covariate with constant
one quarter of the reciprocal of the scale](goal). -/
lemma counterexampleApproxTreatmentProbability_lipschitz (delta : ℝ) (hdelta : 0 < delta) :
    LipschitzWith (delta.toNNReal⁻¹/4) (counterexampleApproxTreatmentProbability delta) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := (counterexampleScaledClamp_lipschitz delta hdelta).dist_le_mul x y
  have heq : counterexampleApproxTreatmentProbability delta x -
      counterexampleApproxTreatmentProbability delta y =
      (counterexampleClamp (x/delta)-counterexampleClamp (y/delta))/4 := by
    unfold counterexampleApproxTreatmentProbability
    ring
  simp only [Real.dist_eq] at h
  rw [Real.dist_eq, heq, abs_div]
  norm_num [Real.dist_eq] at h ⊢
  nlinarith

-- @node: counterexampleApproxTreatmentProbability_measurable
/-- [For every real scale parameter, the approximating probability of treatment
two is a measurable function of the covariate](goal). -/
@[fun_prop] lemma counterexampleApproxTreatmentProbability_measurable (delta : ℝ) :
    Measurable (counterexampleApproxTreatmentProbability delta) := by
  unfold counterexampleApproxTreatmentProbability
  fun_prop

-- @node: counterexampleApproxTreatmentProbability_values
/-- If [the scale parameter is positive](hyp:hdelta), [the approximating
probability of treatment two equals one half at covariate minus one, one half
at covariate zero, and three quarters at a covariate equal to the scale](goal). -/
lemma counterexampleApproxTreatmentProbability_values (delta : ℝ) (hdelta : 0 < delta) :
    counterexampleApproxTreatmentProbability delta (-1) = 1/2 ∧
      counterexampleApproxTreatmentProbability delta 0 = 1/2 ∧
      counterexampleApproxTreatmentProbability delta delta = 3/4 := by
  have hn : counterexampleClamp (-1/delta) = 0 := by
    unfold counterexampleClamp
    have hneg : -1/delta ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by norm_num) hdelta.le
    rw [min_eq_left (hneg.trans zero_le_one), max_eq_left hneg]
  unfold counterexampleApproxTreatmentProbability
  rw [hn, div_self (ne_of_gt hdelta)]
  norm_num [counterexampleClamp]

-- @node: counterexampleApproxPropensity
/-- For [a real scale parameter](hyp:delta) and [a real covariate value](hyp:x),
[the approximating propensity vector](goal) contains the probabilities of
treatment one and treatment two, in that order: one minus the approximating
probability of treatment two, followed by that probability. -/
def counterexampleApproxPropensity (delta x : ℝ) : L1Vec 2 :=
  WithLp.toLp 1 (fun j => if j = 0 then
    1-counterexampleApproxTreatmentProbability delta x else counterexampleApproxTreatmentProbability delta x)

-- @node: counterexampleApproxPropensity_simplex
/-- [For every real scale and covariate value, the approximating propensity
vector has nonnegative components that sum to one](goal). -/
lemma counterexampleApproxPropensity_simplex (delta x : ℝ) :
    (counterexampleApproxPropensity delta x).ofLp ∈ stdSimplex ℝ (Fin 2) := by
  have h := counterexampleApproxTreatmentProbability_bounds delta x
  constructor
  · intro j
    fin_cases j <;> dsimp [counterexampleApproxPropensity] <;> linarith [h.1, h.2]
  · simp [counterexampleApproxPropensity, Fin.sum_univ_two]

-- @node: counterexampleApproxPropensity_lipschitz
/-- If [the scale parameter is positive](hyp:hdelta), [the approximating
propensity vector is Lipschitz in the covariate with constant one half of the
reciprocal of the scale, using the sum of absolute coordinate differences
to measure changes in the vector](goal). -/
lemma counterexampleApproxPropensity_lipschitz (delta : ℝ) (hdelta : 0 < delta) :
    LipschitzWith (delta.toNNReal⁻¹/2) (counterexampleApproxPropensity delta) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := (counterexampleApproxTreatmentProbability_lipschitz delta hdelta).dist_le_mul x y
  rw [PiLp.dist_eq_of_L1, Fin.sum_univ_two]
  norm_num [counterexampleApproxPropensity, Real.dist_eq] at h ⊢
  rw [show 1-counterexampleApproxTreatmentProbability delta x +
      counterexampleApproxTreatmentProbability delta y - 1 =
      -(counterexampleApproxTreatmentProbability delta x-counterexampleApproxTreatmentProbability delta y) by ring,
    abs_neg]
  nlinarith

-- @node: counterexampleApproxPropensity_measurable
/-- [For every real scale parameter, the approximating propensity vector is
a measurable function of the covariate](goal). -/
@[fun_prop] lemma counterexampleApproxPropensity_measurable (delta : ℝ) :
    Measurable (counterexampleApproxPropensity delta) := by
  unfold counterexampleApproxPropensity
  apply (PiLp.continuous_toLp 1 _).measurable.comp
  apply measurable_pi_lambda
  intro j
  by_cases hj : j = 0 <;> simp only [hj, if_true, if_false] <;> fun_prop


-- @node: counterexampleTrueOutcome_integrable
/-- If [the vector of covariate, treatment, and two latent noise inputs is
measurable](hyp:hz), [the limiting outcome evaluated at that vector is
integrable under any finite measure on the input sample space](goal).

The outcome lies in the unit interval, so no additional moment assumption is needed. -/
lemma counterexampleTrueOutcome_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsFiniteMeasure P]
    (z : Ω → L1Vec 4) (hz : Measurable z) :
    MeasureTheory.Integrable (fun u => counterexampleTrueOutcome (z u)) P := by
  apply MeasureTheory.Integrable.of_bound
    (counterexampleTrueOutcome_measurable.comp hz).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun u => by
    dsimp only [Function.comp_def]
    rw [Real.norm_eq_abs, abs_of_nonneg (counterexampleTrueOutcome_bounds (z u)).1]
    exact (counterexampleTrueOutcome_bounds (z u)).2)

-- @node: counterexampleApproxOutcome_integrable
/-- If [the vector of covariate and treatment inputs is measurable](hyp:hz),
[the approximating outcome evaluated at that vector is integrable under any
finite measure on the input sample space, for every real scale parameter](goal). -/
lemma counterexampleApproxOutcome_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsFiniteMeasure P]
    (delta : ℝ) (z : Ω → L1Vec 2) (hz : Measurable z) :
    MeasureTheory.Integrable (fun u => counterexampleApproxOutcome delta (z u)) P := by
  apply MeasureTheory.Integrable.of_bound
    ((counterexampleApproxOutcome_measurable delta).comp hz).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun u => by
    dsimp only [Function.comp_def]
    rw [Real.norm_eq_abs, abs_of_nonneg (counterexampleApproxOutcome_bounds delta (z u)).1]
    exact (counterexampleApproxOutcome_bounds delta (z u)).2)

end
end Papers.TbsNeuralCausalPi

module
public import Papers.TbsPrteOptimalTransport.Helpers.JointTailAdmissibility
/-! Uniform continuous nuisance direction bounds derived from admissibility. -/
public section
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

-- This extends the unit-interval argument to signed weights and outcome means.
-- @node: affine_interval_direction_regular
/-- For [a positive path radius](hyp:hr), suppose [the baseline function is measurable](hyp:hm0)
and [the function displaced by half the radius is measurable](hyp:hmt), and both
[the baseline](hyp:hb0) and [the displaced function](hyp:hbt) lie almost surely in the same closed interval.
Then [the direction is measurable and its absolute value is almost surely at most twice the absolute interval width divided by the radius](goal). -/
lemma affine_interval_direction_regular {B : Type*} [MeasurableSpace B]
    (ν : Measure B) (p d : B → ℝ) (r lo hi : ℝ) (hr : 0 < r)
    (hm0 : Measurable p) (hmt : Measurable (fun b => p b + (r/2) * d b))
    (hb0 : ∀ᵐ b ∂ν, p b ∈ Icc lo hi)
    (hbt : ∀ᵐ b ∂ν, p b + (r/2) * d b ∈ Icc lo hi) :
    Measurable d ∧ ∀ᵐ b ∂ν, ‖d b‖ ≤ 2 * |hi-lo| / r := by
  constructor
  · have hid : d = fun b => ((p b + (r/2) * d b) - p b) / (r/2) := by
      funext b
      field_simp
      <;> ring
    rw [hid]
    exact (hmt.sub hm0).div_const _
  · filter_upwards [hb0, hbt] with b hb ht
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · rw [← neg_div, div_le_iff₀ hr]
      nlinarith [hb.1, hb.2, ht.1, ht.2, le_abs_self (hi-lo)]
    · apply (le_div_iff₀ hr).2
      nlinarith [hb.1, hb.2, ht.1, ht.2, le_abs_self (hi-lo)]

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- The same admissible radius controls every coordinate of this family.
-- @node: continuous_assignment_direction_regular
/-- If [the continuous nuisance direction is admissible at the baseline nuisance collection](hyp:hd),
[all assignment probability directions are measurable and share a finite nonnegative almost sure bound under the covariate distribution](goal). -/
lemma continuous_assignment_direction_regular (L : LevelData Z X) (eta del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl eta) (.inl del)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : PositiveIndex L.K,
      Measurable (del.piLev a) ∧ ∀ᵐ x ∂xLaw M, ‖del.piLev a x‖ ≤ C := by
  obtain ⟨r, hr, hpath⟩ := hd.admissible
  have h0 := hpath 0 (by simpa using hr)
  have ht := hpath (r/2) (by rw [abs_of_pos (by positivity)]; linarith)
  refine ⟨2/r, by positivity, ?_⟩
  intro a
  apply affine_unit_direction_regular (xLaw M) (eta.piLev a) (del.piLev a) r hr
  · have hm : Measurable (fun x => eta.piLev a x + 0 * del.piLev a x) := h0.2.2.2.2.2.1 a
    simpa only [zero_mul, add_zero] using hm
  · exact ht.2.2.2.2.2.1 a
  · have hb : ∀ᵐ x ∂xLaw M, eta.piLev a x + 0 * del.piLev a x ∈
        Icc (0 : ℝ) 1 := h0.2.2.2.2.1 a
    simpa only [zero_mul, add_zero] using hb
  · exact ht.2.2.2.2.1 a

-- The same admissible radius controls every coordinate of this family.
-- @node: continuous_baseline_direction_regular
/-- If [the continuous nuisance direction is admissible at the baseline nuisance collection](hyp:hd),
[all baseline treatment propensity directions are measurable and share a finite nonnegative almost sure bound under the covariate distribution](goal). -/
lemma continuous_baseline_direction_regular (L : LevelData Z X) (eta del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl eta) (.inl del)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : PositiveIndex L.K,
      Measurable (del.pLev a) ∧ ∀ᵐ x ∂xLaw M, ‖del.pLev a x‖ ≤ C := by
  obtain ⟨r, hr, hpath⟩ := hd.admissible
  have h0 := hpath 0 (by simpa using hr)
  have ht := hpath (r/2) (by rw [abs_of_pos (by positivity)]; linarith)
  refine ⟨2/r, by positivity, ?_⟩
  intro a
  apply affine_unit_direction_regular (xLaw M) (eta.pLev a) (del.pLev a) r hr
  · have hm : Measurable (fun x => eta.pLev a x + 0 * del.pLev a x) := h0.2.2.2.1 a
    simpa only [zero_mul, add_zero] using hm
  · exact ht.2.2.2.1 a
  · have hb : ∀ᵐ x ∂xLaw M, eta.pLev a x + 0 * del.pLev a x ∈
        Icc (0 : ℝ) 1 := h0.2.2.1 a
    simpa only [zero_mul, add_zero] using hb
  · exact ht.2.2.1 a

-- The same admissible radius controls every coordinate of this family.
-- @node: continuous_full_weight_direction_regular
/-- If [the continuous nuisance direction is admissible at the baseline nuisance collection](hyp:hd),
[all full-interval weight directions are measurable and share a finite nonnegative almost sure bound under the covariate distribution](goal). -/
lemma continuous_full_weight_direction_regular (L : LevelData Z X) (eta del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl eta) (.inl del)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : Fin L.K,
      Measurable (del.gammaFull a) ∧ ∀ᵐ x ∂xLaw M, ‖del.gammaFull a x‖ ≤ C := by
  obtain ⟨r, hr, hpath⟩ := hd.admissible
  have h0 := hpath 0 (by simpa using hr)
  have ht := hpath (r/2) (by rw [abs_of_pos (by positivity)]; linarith)
  refine ⟨2 * |(1 : ℝ) - (-1)| / r, by positivity, ?_⟩
  intro a
  apply affine_interval_direction_regular (xLaw M) (eta.gammaFull a) (del.gammaFull a) r (-1) 1 hr
  · have hm : Measurable (fun x => eta.gammaFull a x + 0 * del.gammaFull a x) := h0.2.2.2.2.2.2.2.2.2.2.2.1 a
    simpa only [zero_mul, add_zero] using hm
  · exact ht.2.2.2.2.2.2.2.2.2.2.2.1 a
  · have hb : ∀ᵐ x ∂xLaw M, eta.gammaFull a x + 0 * del.gammaFull a x ∈
        Icc (-1 : ℝ) 1 := h0.2.2.2.2.2.2.2.2.2.2.1 a
    simpa only [zero_mul, add_zero] using hb
  · exact ht.2.2.2.2.2.2.2.2.2.2.1 a

-- Both full-outcome regressions use the known outcome interval. Their common
-- direction bound follows from two points of the admissible path.
-- @node: continuous_full_outcome_direction_regular
/-- If [the continuous nuisance direction is admissible at the baseline nuisance collection](hyp:hd),
[the full-interval outcome regression directions on both sides are measurable and share one finite nonnegative almost sure bound across all their indices](goal). -/
lemma continuous_full_outcome_direction_regular (L : LevelData Z X)
    (eta del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl eta) (.inl del)) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ k : Fin L.K, Measurable (del.JfullPlus k) ∧
        ∀ᵐ x ∂xLaw M, ‖del.JfullPlus k x‖ ≤ C) ∧
      (∀ k : {k : ℕ // 1 ≤ k ∧ k < L.K}, Measurable (del.JfullMinus k) ∧
        ∀ᵐ x ∂xLaw M, ‖del.JfullMinus k x‖ ≤ C) := by
  obtain ⟨r, hr, hpath⟩ := hd.admissible
  have h0 := hpath 0 (by simpa using hr)
  have ht := hpath (r/2) (by rw [abs_of_pos (by positivity)]; linarith)
  rcases h0 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, hp0, hmp0, hm0, hmm0, _⟩
  rcases ht with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, hpt, hmpt, hmt, hmmt, _⟩
  refine ⟨2 * |M.yMax-M.yMin| / r, by positivity, ?_⟩
  constructor
  · intro k
    apply affine_interval_direction_regular (xLaw M) (eta.JfullPlus k)
      (del.JfullPlus k) r M.yMin M.yMax hr
    · have hm : Measurable (fun x => eta.JfullPlus k x + 0 * del.JfullPlus k x) := hmp0 k
      simpa only [zero_mul, add_zero] using hm
    · exact hmpt k
    · have hb : ∀ᵐ x ∂xLaw M, eta.JfullPlus k x + 0 * del.JfullPlus k x ∈
          Icc M.yMin M.yMax := hp0 k
      simpa only [zero_mul, add_zero] using hb
    · exact hpt k
  · intro k
    apply affine_interval_direction_regular (xLaw M) (eta.JfullMinus k)
      (del.JfullMinus k) r M.yMin M.yMax hr
    · have hm : Measurable (fun x => eta.JfullMinus k x + 0 * del.JfullMinus k x) := hmm0 k
      simpa only [zero_mul, add_zero] using hm
    · exact hmmt k
    · have hb : ∀ᵐ x ∂xLaw M, eta.JfullMinus k x + 0 * del.JfullMinus k x ∈
          Icc M.yMin M.yMax := hm0 k
      simpa only [zero_mul, add_zero] using hb
    · exact hmt k

-- Neighborhood admissibility yields a uniform bounded denominator direction;
-- population overlap then supplies a single neighborhood for every covariate.
-- @node: continuous_assignment_path_uniform_lower_bound
/-- Given [baseline assignment overlap with the specified positive lower bound](hyp:hov) and
[an admissible continuous nuisance direction at the population nuisance collection](hyp:hd),
[throughout some neighborhood of zero every assignment probability along the affine path is almost surely at least half that lower bound](goal). -/
lemma continuous_assignment_path_uniform_lower_bound (L : LevelData Z X)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del)) :
    ∀ᶠ t : ℝ in 𝓝 0, ∀ a : PositiveIndex L.K, ∀ᵐ x ∂xLaw M,
      cpi / 2 ≤ (trueNuisance M L + t • del).piLev a x := by
  obtain ⟨C, hC, hreg⟩ := continuous_assignment_direction_regular M L
    (trueNuisance M L) del hd
  have hr : 0 < cpi / (2 * (C+1)) := div_pos hov.1 (by positivity)
  filter_upwards [continuousAt_id.abs.eventually_lt_const (by simpa using hr)] with t ht
  change |t| < cpi / (2 * (C+1)) at ht
  intro a
  filter_upwards [(hreg a).2] with x hx
  have hpi : cpi ≤ (trueNuisance M L).piLev a x := by
    simpa only [trueNuisance, levelSetProb] using hov.2 x a.val a.property.1 a.property.2
  have hmul : |t * del.piLev a x| ≤ |t| * C := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using hx)
      (abs_nonneg t)
  have hsmall := (lt_div_iff₀ (by positivity : 0 < 2 * (C+1))).mp ht
  change cpi / 2 ≤ (trueNuisance M L).piLev a x + t * del.piLev a x
  nlinarith [neg_abs_le (t * del.piLev a x), abs_nonneg t]

end Papers.TbsPrteOptimalTransport

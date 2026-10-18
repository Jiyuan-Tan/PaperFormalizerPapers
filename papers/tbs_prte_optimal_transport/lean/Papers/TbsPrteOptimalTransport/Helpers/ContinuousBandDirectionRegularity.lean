module
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousDirectionRegularity
public import Papers.TbsPrteOptimalTransport.Helpers.WeightedQuantileBoundary
/-! Regular-band nuisance direction bounds and boundary cancellation from admissibility. -/
public section
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: continuous_quantile_direction_regular
/-- If [a continuous nuisance direction is admissible at the given nuisance functions](hyp:hd),
then [there is a nonnegative constant bounding every quantile-direction coordinate in
absolute value almost surely under the covariate law, and every such coordinate is measurable](goal). -/
lemma continuous_quantile_direction_regular (L : LevelData Z X) (eta del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl eta) (.inl del)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : BoundaryIndex L,
      Measurable (del.nu a) ∧ ∀ᵐ x ∂xLaw M, ‖del.nu a x‖ ≤ C := by
  obtain ⟨r, hr, hpath⟩ := hd.admissible
  have h0 := hpath 0 (by simpa using hr)
  have ht := hpath (r/2) (by rw [abs_of_pos (by positivity)]; linarith)
  rcases h0 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    hb0, hm0, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  rcases ht with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    hbt, hmt, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  refine ⟨2 * |(M.yMax)-(M.yMin)| / r, by positivity, ?_⟩
  intro a
  apply affine_interval_direction_regular (xLaw M) (eta.nu a) (del.nu a)
    r (M.yMin) (M.yMax) hr
  · have hm : Measurable (fun x => eta.nu a x + 0 * del.nu a x) := hm0 a
    simpa only [zero_mul, add_zero] using hm
  · exact hmt a
  · have hb : ∀ᵐ x ∂xLaw M, eta.nu a x + 0 * del.nu a x ∈
        Icc (M.yMin) (M.yMax) := hb0 a
    simpa only [zero_mul, add_zero] using hb
  · exact hbt a

-- @node: continuous_regular_weight_direction_regular
/-- If [a continuous nuisance direction is admissible at the given nuisance functions](hyp:hd),
then [all regular-band weight directions are measurable and share a finite nonnegative
almost-sure absolute bound under the covariate law](goal). -/
lemma continuous_regular_weight_direction_regular (L : LevelData Z X) (eta del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl eta) (.inl del)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : RegularIndex L,
      Measurable (del.gamma a) ∧ ∀ᵐ x ∂xLaw M, ‖del.gamma a x‖ ≤ C := by
  obtain ⟨r, hr, hpath⟩ := hd.admissible
  have h0 := hpath 0 (by simpa using hr)
  have ht := hpath (r/2) (by rw [abs_of_pos (by positivity)]; linarith)
  rcases h0 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hb0, hm0, _, _,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  rcases ht with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hbt, hmt, _, _,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  refine ⟨2 * |(1)-(0)| / r, by positivity, ?_⟩
  intro a
  apply affine_interval_direction_regular (xLaw M) (eta.gamma a) (del.gamma a)
    r (0) (1) hr
  · have hm : Measurable (fun x => eta.gamma a x + 0 * del.gamma a x) := hm0 a
    simpa only [zero_mul, add_zero] using hm
  · exact hmt a
  · have hb : ∀ᵐ x ∂xLaw M, eta.gamma a x + 0 * del.gamma a x ∈
        Icc (0) (1) := hb0 a
    simpa only [zero_mul, add_zero] using hb
  · exact hbt a

-- @node: continuous_band_plus_outcome_direction_regular
/-- If [a continuous nuisance direction is admissible at the given nuisance functions](hyp:hd),
then [all upper-level band outcome-regression directions are measurable and share a
finite nonnegative almost-sure absolute bound under the covariate law](goal). -/
lemma continuous_band_plus_outcome_direction_regular (L : LevelData Z X) (eta del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl eta) (.inl del)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : MeanIndex L,
      Measurable (del.Jplus a) ∧ ∀ᵐ x ∂xLaw M, ‖del.Jplus a x‖ ≤ C := by
  obtain ⟨r, hr, hpath⟩ := hd.admissible
  have h0 := hpath 0 (by simpa using hr)
  have ht := hpath (r/2) (by rw [abs_of_pos (by positivity)]; linarith)
  rcases h0 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, hb0, hm0, _, _, _, _, _, _, _⟩
  rcases ht with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, hbt, hmt, _, _, _, _, _, _, _⟩
  refine ⟨2 * |(max 0 M.yMax)-(min 0 M.yMin)| / r, by positivity, ?_⟩
  intro a
  apply affine_interval_direction_regular (xLaw M) (eta.Jplus a) (del.Jplus a)
    r (min 0 M.yMin) (max 0 M.yMax) hr
  · have hm : Measurable (fun x => eta.Jplus a x + 0 * del.Jplus a x) := hm0 a
    simpa only [zero_mul, add_zero] using hm
  · exact hmt a
  · have hb : ∀ᵐ x ∂xLaw M, eta.Jplus a x + 0 * del.Jplus a x ∈
        Icc (min 0 M.yMin) (max 0 M.yMax) := hb0 a
    simpa only [zero_mul, add_zero] using hb
  · exact hbt a

-- @node: continuous_band_minus_outcome_direction_regular
/-- If [a continuous nuisance direction is admissible at the given nuisance functions](hyp:hd),
then [all lower-level band outcome-regression directions are measurable and share a
finite nonnegative almost-sure absolute bound under the covariate law](goal). -/
lemma continuous_band_minus_outcome_direction_regular (L : LevelData Z X) (eta del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl eta) (.inl del)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : MinusMeanIndex L,
      Measurable (del.Jminus a) ∧ ∀ᵐ x ∂xLaw M, ‖del.Jminus a x‖ ≤ C := by
  obtain ⟨r, hr, hpath⟩ := hd.admissible
  have h0 := hpath 0 (by simpa using hr)
  have ht := hpath (r/2) (by rw [abs_of_pos (by positivity)]; linarith)
  rcases h0 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, hb0, hm0, _, _, _, _, _⟩
  rcases ht with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, hbt, hmt, _, _, _, _, _⟩
  refine ⟨2 * |(max 0 M.yMax)-(min 0 M.yMin)| / r, by positivity, ?_⟩
  intro a
  apply affine_interval_direction_regular (xLaw M) (eta.Jminus a) (del.Jminus a)
    r (min 0 M.yMin) (max 0 M.yMax) hr
  · have hm : Measurable (fun x => eta.Jminus a x + 0 * del.Jminus a x) := hm0 a
    simpa only [zero_mul, add_zero] using hm
  · exact hmt a
  · have hb : ∀ᵐ x ∂xLaw M, eta.Jminus a x + 0 * del.Jminus a x ∈
        Icc (min 0 M.yMin) (max 0 M.yMax) := hb0 a
    simpa only [zero_mul, add_zero] using hb
  · exact hbt a

-- @node: continuous_band_plus_indicator_direction_regular
/-- If [a continuous nuisance direction is admissible at the given nuisance functions](hyp:hd),
then [all upper-level boundary-indicator regression directions are measurable and share
a finite nonnegative almost-sure absolute bound under the covariate law](goal). -/
lemma continuous_band_plus_indicator_direction_regular (L : LevelData Z X) (eta del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl eta) (.inl del)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : IndicatorIndex L,
      Measurable (del.Mplus a) ∧ ∀ᵐ x ∂xLaw M, ‖del.Mplus a x‖ ≤ C := by
  obtain ⟨r, hr, hpath⟩ := hd.admissible
  have h0 := hpath 0 (by simpa using hr)
  have ht := hpath (r/2) (by rw [abs_of_pos (by positivity)]; linarith)
  rcases h0 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, hb0, hm0, _, _, _, _, _, _, _, _, _, _, _⟩
  rcases ht with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, hbt, hmt, _, _, _, _, _, _, _, _, _, _, _⟩
  refine ⟨2 * |(1)-(0)| / r, by positivity, ?_⟩
  intro a
  apply affine_interval_direction_regular (xLaw M) (eta.Mplus a) (del.Mplus a)
    r (0) (1) hr
  · have hm : Measurable (fun x => eta.Mplus a x + 0 * del.Mplus a x) := hm0 a
    simpa only [zero_mul, add_zero] using hm
  · exact hmt a
  · have hb : ∀ᵐ x ∂xLaw M, eta.Mplus a x + 0 * del.Mplus a x ∈
        Icc (0) (1) := hb0 a
    simpa only [zero_mul, add_zero] using hb
  · exact hbt a

-- @node: continuous_band_minus_indicator_direction_regular
/-- If [a continuous nuisance direction is admissible at the given nuisance functions](hyp:hd),
then [all lower-level boundary-indicator regression directions are measurable and share
a finite nonnegative almost-sure absolute bound under the covariate law](goal). -/
lemma continuous_band_minus_indicator_direction_regular (L : LevelData Z X) (eta del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl eta) (.inl del)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : MinusIndicatorIndex L,
      Measurable (del.Mminus a) ∧ ∀ᵐ x ∂xLaw M, ‖del.Mminus a x‖ ≤ C := by
  obtain ⟨r, hr, hpath⟩ := hd.admissible
  have h0 := hpath 0 (by simpa using hr)
  have ht := hpath (r/2) (by rw [abs_of_pos (by positivity)]; linarith)
  rcases h0 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, hb0, hm0, _, _, _, _, _, _, _, _, _⟩
  rcases ht with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, hbt, hmt, _, _, _, _, _, _, _, _, _⟩
  refine ⟨2 * |(1)-(0)| / r, by positivity, ?_⟩
  intro a
  apply affine_interval_direction_regular (xLaw M) (eta.Mminus a) (del.Mminus a)
    r (0) (1) hr
  · have hm : Measurable (fun x => eta.Mminus a x + 0 * del.Mminus a x) := hm0 a
    simpa only [zero_mul, add_zero] using hm
  · exact hmt a
  · have hb : ∀ᵐ x ∂xLaw M, eta.Mminus a x + 0 * del.Mminus a x ∈
        Icc (0) (1) := hb0 a
    simpa only [zero_mul, add_zero] using hb
  · exact hbt a

-- The quadratic boundary estimate needs L2 directions, which are consequences
-- of the clipped admissible path rather than additional hypotheses.
-- @node: continuous_quantile_direction_memLp
/-- If [a continuous nuisance direction is admissible at the given nuisance functions](hyp:hd),
then [its quantile direction at any boundary is square-integrable under the covariate law](goal). -/
lemma continuous_quantile_direction_memLp (L : LevelData Z X) (eta del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl eta) (.inl del)) (a : BoundaryIndex L) :
    MemLp (del.nu a) 2 (xLaw M) := by
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  obtain ⟨C, _, hb⟩ := continuous_quantile_direction_regular M L eta del hd
  exact MemLp.of_bound (hb a).1.aestronglyMeasurable C (hb a).2

-- @node: population_continuous_admissible_quantile_boundary_orthogonality
/-- Suppose [the treated outcome densities at band boundaries are bounded](hyp:h),
[the nuisance direction is admissible](hyp:hd), [the selected treatment level is the
upper adjacent level or the positive lower adjacent level of the boundary](hyp:hi),
and [the true boundary is measurable](hyp:ha). For [weights measurable at every time](hyp:hw)
with [a nonnegative bound](hyp:hB) that [bounds their absolute values almost surely
at every time](hyp:hwb), [the weighted population change in the integrated quantile
hinge loss, after subtracting its linear boundary term, has derivative zero at time zero](goal). -/
lemma population_continuous_admissible_quantile_boundary_orthogonality
    (L : LevelData Z X) (h : BoundaryDensitiesBounded M L)
    (eta del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl eta) (.inl del))
    (a : BoundaryIndex L) (i : ℕ)
    (hi : i = a.val.1 + 1 ∨ (1 ≤ a.val.1 ∧ i = a.val.1))
    (ha : Measurable (bandBoundary M L a.val.1 a.val.2))
    (w : ℝ → X → ℝ) (hw : ∀ t, Measurable (w t))
    (B : ℝ) (hB : 0 ≤ B) (hwb : ∀ t, ∀ᵐ x ∂xLaw M, |w t x| ≤ B) :
    HasDerivAt (fun t : ℝ => ∫ x, w t x * (∫ y,
      (bandBoundary M L a.val.1 a.val.2 x + t * del.nu a x - y) *
        indicator (y ≤ bandBoundary M L a.val.1 a.val.2 x + t * del.nu a x) -
      (bandBoundary M L a.val.1 a.val.2 x - y) *
        indicator (y ≤ bandBoundary M L a.val.1 a.val.2 x) -
      (t * del.nu a x) * indicator (y ≤ bandBoundary M L a.val.1 a.val.2 x)
      ∂treatedLaw M L i x) ∂xLaw M) 0 0 := by
  obtain ⟨_, _, hdir⟩ := continuous_quantile_direction_regular M L eta del hd
  exact population_continuous_weighted_quantile_boundary_orthogonality M L h
    a.val.1 a.val.2 a.property.1 a.property.2.1 a.property.2.2 i hi ha
    (del.nu a) (hdir a).1 (continuous_quantile_direction_memLp M L eta del hd a)
    w hw B hB hwb

end Papers.TbsPrteOptimalTransport

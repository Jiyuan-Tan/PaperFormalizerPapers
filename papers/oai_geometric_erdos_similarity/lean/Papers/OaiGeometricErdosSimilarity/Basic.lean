module
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # Geometric progressions, periodic density, and nested dyadic grids -/

@[expose] public section

namespace Papers.OaiGeometricErdosSimilarity

open MeasureTheory

-- @env: S1
variable (q : ℝ) -- @realizes \R(real number carrier) @realizes q(real ratio; range via QDomain)

-- @node: ass:q-domain
/-- For [a real ratio q](hyp:q), [the admissible-ratio condition](goal) requires
[q to be positive](step:1) and [q to be less than one](step:2). -/
def QDomain (q : ℝ) : Prop := 0 < q ∧ q < 1 -- @realizes q(0 < q < 1)

-- @node: ass:branching-domain
/-- For [a natural-number branching count M](hyp:M), [the branching-domain
condition is that M is at least two](goal). -/
def BranchingDomain (M : ℕ) : Prop := 2 ≤ M -- @realizes M(integer branching number at least two)

-- @node: ass:depth-domain
/-- For [a natural-number tree depth d](hyp:d), [the depth-domain condition is
that d is at least one](goal). -/
def DepthDomain (d : ℕ) : Prop := 1 ≤ d -- @realizes d(positive integer tree height)

-- @node: ass:gap-domain
/-- For [a natural-number gap g](hyp:g), [the gap-domain condition is that g is
at least one](goal). -/
def GapDomain (g : ℕ) : Prop := 1 ≤ g -- @realizes g(positive integer gap)

-- @node: ass:base-length-domain
/-- For [a natural-number base length r0](hyp:r0), [the base-length-domain
condition is that r0 is at least one](goal). -/
def BaseLengthDomain (r0 : ℕ) : Prop := 1 ≤ r0 -- @realizes r_0(positive integer base length)

-- @node: ass:terminal-probability-domain
/-- For [a real terminal probability p](hyp:p), [the terminal-probability
condition](goal) requires [p to be positive](step:1) and [p to be less than one](step:2). -/
def TerminalProbabilityDomain (p : ℝ) : Prop := 0 < p ∧ p < 1
  -- @realizes p(terminal probability in (0,1))

-- @node: ass:conditional-scales-parameters
/-- For [a terminal probability p](hyp:p), [branching count M](hyp:M),
[tree depth d](hyp:d), [gap g](hyp:g), and [base length r0](hyp:r0),
[admissibility of the conditional-scales parameters](goal) requires
[p to lie strictly between zero and one](step:1), [M to be at least two](step:2),
[d to be at least one](step:3), [g to be at least one](step:4), and
[r0 to be at least one](step:5). -/
def ConditionalScalesParameters (p : ℝ) (M d g r0 : ℕ) : Prop :=
  TerminalProbabilityDomain p ∧ BranchingDomain M ∧ DepthDomain d ∧
    GapDomain g ∧ BaseLengthDomain r0

-- @node: def:lebesgue-measure
/-- [Lebesgue measure on the real line](goal) assigns intervals their usual length. -/
noncomputable abbrev lebesgueMeasure : Measure ℝ := MeasureTheory.volume
  -- @realizes m(Lebesgue measure)

/-- For [a set A of real numbers](hyp:A), [one-periodicity means that a point
belongs to A exactly when that point plus one belongs to A](goal). -/
def IsOnePeriodic (A : Set ℝ) : Prop := ∀ z, z ∈ A ↔ z + 1 ∈ A

-- @node: def:geometric-progression
/-- For [a real ratio q](hyp:q), [the geometric progression is the set of all
positive-integer powers of q](goal). -/
def geometricProgression (q : ℝ) : Set ℝ := -- @realizes G_q(set of positive-index powers)
  {y | ∃ n : ℕ, 1 ≤ n ∧ y = q ^ n} -- @realizes n(natural sequence index at least one)
    -- @realizes \N(natural indices)

-- @node: def:periodic-density
/-- For [a set A of real numbers](hyp:A), [its periodic density is the Lebesgue
measure of its intersection with the interval from zero, included, to one,
excluded, expressed as a real number](goal). -/
noncomputable def periodicDensity (A : Set ℝ) : ℝ :=
  -- @realizes A(real subset; measurable and periodic at uses)
  -- @realizes \rho(volume in the fundamental interval)
  (lebesgueMeasure (A ∩ Set.Ico (0 : ℝ) 1)).toReal

-- @node: periodicDensity_mem_Icc
/-- For [any set A of real numbers](hyp:A), [its periodic density lies between
zero and one, inclusive](goal). -/
lemma periodicDensity_mem_Icc (A : Set ℝ) : periodicDensity A ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact ENNReal.toReal_nonneg
  · have hvol : lebesgueMeasure (Set.Ico (0 : ℝ) 1) = 1 := by
      simp [lebesgueMeasure]
    have hbound : lebesgueMeasure (A ∩ Set.Ico (0 : ℝ) 1) ≤ 1 := by
      rw [← hvol]
      exact measure_mono Set.inter_subset_right
    exact (ENNReal.toReal_mono (by simp) hbound).trans_eq (by simp)

-- @node: mem_affine_image_iff
/-- For [a real ratio q](hyp:q), [translation x](hyp:x), [scale s](hyp:s), and
[point y](hyp:y), [y belongs to the translated and scaled geometric progression
exactly when y equals x plus s times a positive-integer power of q](goal). -/
lemma mem_affine_image_iff (q x s y : ℝ) :
    y ∈ (fun z => x + s * z) '' geometricProgression q ↔
      ∃ n : ℕ, 1 ≤ n ∧ y = x + s * q ^ n := by
  constructor
  · rintro ⟨z, ⟨n, hn, rfl⟩, rfl⟩
    exact ⟨n, hn, rfl⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨q ^ n, ⟨n, hn, rfl⟩, rfl⟩

/-- For [a real ratio q](hyp:q), [the grid constant is four divided by one minus q](goal). -/
noncomputable def gridConst (q : ℝ) : ℝ := 4 / (1 - q) -- @realizes c(4 divided by 1-q)

/-- For [a natural-number grid index b](hyp:b), [the grid-index condition is that
b is at least one](goal).

The paper's grids are indexed by positive integers; formulas extend to zero internally. -/
def GridIndexDomain (b : ℕ) : Prop := 1 ≤ b -- @realizes b(positive integer grid index)

-- @node: def:grid-resolution
/-- For [a real ratio q](hyp:q) and [natural-number grid index b](hyp:b),
[the grid resolution is two raised to the nonnegative part of the ceiling of
the base-two logarithm of the grid constant times q to the power minus b](goal). -/
noncomputable def gridResolution (q : ℝ) (b : ℕ) : ℕ := -- @realizes N_b(dyadic ceiling resolution)
  2 ^ (⌈Real.logb 2 (gridConst q * q ^ (-(b : ℤ)))⌉).toNat

/-- For [a real ratio q](hyp:q) and [natural-number grid index b](hyp:b),
[the grid lattice consists of all integer multiples of the reciprocal grid resolution](goal). -/
noncomputable def gridLattice (q : ℝ) (b : ℕ) : Set ℝ :=
  -- @realizes \Gamma_b(reciprocal-resolution integer lattice)
  -- @realizes \Z(integer lattice coefficients)
  {y | ∃ k : ℤ, y = (k : ℝ) / gridResolution q b}

-- @node: def:grid-key
-- @realizes J_b(floor key with left-closed cells)
/-- For [a real ratio q](hyp:q), [natural-number grid index b](hyp:b), and
[real point z](hyp:z), [the grid key is the natural-number floor of the grid
resolution times the fractional part of z](goal). -/
noncomputable def gridKey (q : ℝ) (b : ℕ)
    (z : ℝ) : ℕ :=
  -- @realizes z(real point argument)
  -- @realizes \{z\}(Int.fract z)
  ⌊(gridResolution q b : ℝ) * Int.fract z⌋₊

-- @node: gridResolution_pos
/-- For [any real ratio q](hyp:q) and [natural-number grid index b](hyp:b),
[the grid resolution is strictly positive](goal). -/
lemma gridResolution_pos (q : ℝ) (b : ℕ) : 0 < gridResolution q b := by
  exact pow_pos (by norm_num) _

-- @node: gridKey_lt
/-- For [any real ratio q](hyp:q), [natural-number grid index b](hyp:b), and
[real point z](hyp:z), [the grid key of z is strictly less than the grid resolution](goal). -/
lemma gridKey_lt (q : ℝ) (b : ℕ) (z : ℝ) : gridKey q b z < gridResolution q b := by
  have hN : (0 : ℝ) < gridResolution q b := by exact_mod_cast gridResolution_pos q b
  apply (Nat.floor_lt (mul_nonneg hN.le (Int.fract_nonneg z))).mpr
  exact mul_lt_of_lt_one_right hN (Int.fract_lt_one z)

/-- For [a real ratio q](hyp:q), [natural-number grid index b](hyp:b), and
[real point z](hyp:z), [the bounded grid key is the grid key of z regarded as
an index between zero, inclusive, and the grid resolution, exclusive](goal). -/
noncomputable def gridKeyFin (q : ℝ) (b : ℕ) (z : ℝ) : Fin (gridResolution q b) :=
  ⟨gridKey q b z, gridKey_lt q b z⟩

-- @node: def:grid-size
/-- For [a real ratio q](hyp:q) and [natural-number grid index b](hyp:b),
[the grid-size comparison](goal) requires [the grid resolution to be at least
the grid constant times q to the power minus b](step:1) and [strictly less than
twice that quantity](step:2). -/
def GridSizeComparison (q : ℝ) (b : ℕ) : Prop :=
  gridConst q * q ^ (-(b : ℤ)) ≤ (gridResolution q b : ℝ) ∧
    (gridResolution q b : ℝ) < 2 * gridConst q * q ^ (-(b : ℤ))

-- @node: gridSizeComparison_of_qDomain
/-- If [q lies strictly between zero and one](hyp:hq), then for
[any natural-number grid index b](hyp:b), [the grid resolution is at least
the grid constant times q to the power minus b and strictly less than twice
that quantity](goal). -/
lemma gridSizeComparison_of_qDomain (hq : QDomain q) (b : ℕ) :
    GridSizeComparison q b := by
  let X := gridConst q * q ^ (-(b : ℤ))
  have hc : 1 ≤ gridConst q := by
    unfold gridConst
    apply (le_div_iff₀ (by linarith [hq.2] : 0 < 1 - q)).mpr
    linarith [hq.1]
  have hpow : 1 ≤ q ^ (-(b : ℤ)) := by
    rw [zpow_neg, zpow_natCast]
    exact (one_le_inv₀ (pow_pos hq.1 b)).mpr (pow_le_one₀ hq.1.le hq.2.le)
  have hX : 1 ≤ X := one_le_mul_of_one_le_of_one_le hc hpow
  have hlog : 0 ≤ Real.logb 2 X := Real.logb_nonneg (by norm_num) hX
  have hcast : ((⌈Real.logb 2 X⌉.toNat : ℕ) : ℝ) = (⌈Real.logb 2 X⌉ : ℤ) := by
    exact_mod_cast Int.toNat_of_nonneg (Int.ceil_nonneg hlog)
  have hN : (gridResolution q b : ℝ) = (2 : ℝ) ^ (⌈Real.logb 2 X⌉ : ℤ) := by
    simp only [gridResolution, Nat.cast_pow, Nat.cast_ofNat]
    rw [← Real.rpow_natCast, hcast, Real.rpow_intCast]
  unfold GridSizeComparison
  rw [mul_assoc]
  change X ≤ (gridResolution q b : ℝ) ∧ (gridResolution q b : ℝ) < 2 * X
  rw [hN, ← Real.rpow_intCast]
  constructor
  · exact (Real.logb_le_iff_le_rpow (by norm_num) (by positivity : 0 < X)).mp
      (Int.le_ceil _)
  · calc
      (2 : ℝ) ^ ((⌈Real.logb 2 X⌉ : ℤ) : ℝ) < (2 : ℝ) ^ (Real.logb 2 X + 1) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (Int.ceil_lt_add_one _)
      _ = 2 * X := by
        rw [Real.rpow_add (by norm_num), Real.rpow_logb (by norm_num) (by norm_num)
          (by positivity : 0 < X), Real.rpow_one]
        ring

-- @node: def:grid-nesting
/-- For [a real ratio q](hyp:q), [grid nesting](goal) means that
[every grid resolution is a natural-number power of two](step:1),
[resolutions are nondecreasing with the grid index](step:2), and
[whenever a positive grid index is no greater than another index, its resolution
divides the latter resolution and every point's coarser key is the integer
quotient of its finer key by the ratio of resolutions](step:3). -/
def GridNesting (q : ℝ) : Prop :=
  (∀ b : ℕ, ∃ j : ℕ, gridResolution q b = 2 ^ j) ∧
  Monotone (gridResolution q) ∧
  ∀ b b' : ℕ, GridIndexDomain b → -- @realizes b(positive coarser grid index)
    b ≤ b' → -- @realizes b'(finer grid index at least the positive index b)
    gridResolution q b ∣ gridResolution q b' ∧
    ∀ z, gridKey q b z = gridKey q b' z / (gridResolution q b' / gridResolution q b)

-- @node: gridNesting_of_qDomain
/-- If [q lies strictly between zero and one](hyp:hq), then [the grid resolutions
are powers of two and nondecreasing, and for any positive coarser index and any
larger index the coarser resolution divides the finer resolution, with coarser
keys obtained by integer division of finer keys by the resolution ratio](goal). -/
lemma gridNesting_of_qDomain (hq : QDomain q) : GridNesting q := by
  have hexp : Monotone (fun b : ℕ =>
      (⌈Real.logb 2 (gridConst q * q ^ (-(b : ℤ)))⌉).toNat) := by
    intro b b' hbb'
    apply Int.toNat_le_toNat
    apply Int.ceil_mono
    apply Real.logb_le_logb_of_le (by norm_num)
    · exact mul_pos (div_pos (by norm_num) (sub_pos.mpr hq.2)) (zpow_pos hq.1 _)
    · apply mul_le_mul_of_nonneg_left _ (le_of_lt (div_pos (by norm_num) (sub_pos.mpr hq.2)))
      simp only [zpow_neg, zpow_natCast]
      exact inv_le_inv₀ (pow_pos hq.1 _) (pow_pos hq.1 _) |>.mpr
        (pow_le_pow_of_le_one hq.1.le hq.2.le hbb')
  refine ⟨fun b => ⟨_, rfl⟩, ?_, ?_⟩
  · intro b b' hbb'
    exact Nat.pow_le_pow_right (by norm_num) (hexp hbb')
  · intro b b' _ hbb'
    have hdvd : gridResolution q b ∣ gridResolution q b' :=
      pow_dvd_pow 2 (hexp hbb')
    refine ⟨hdvd, ?_⟩
    intro z
    have hratio : gridResolution q b' / gridResolution q b ≠ 0 := by
      have hmul := Nat.div_mul_cancel hdvd
      have hp := gridResolution_pos q b'
      intro hz
      rw [hz, Nat.zero_mul] at hmul
      omega
    have hmul : (gridResolution q b' : ℝ) =
        (gridResolution q b : ℝ) * (gridResolution q b' / gridResolution q b : ℕ) := by
      exact_mod_cast (Nat.mul_div_cancel' hdvd).symm
    unfold gridKey
    rw [hmul, mul_right_comm]
    exact (Nat.mul_cast_floor_div_cancel hratio _).symm

end Papers.OaiGeometricErdosSimilarity

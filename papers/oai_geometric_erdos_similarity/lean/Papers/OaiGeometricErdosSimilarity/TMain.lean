module
public import Papers.OaiGeometricErdosSimilarity.TPeriodic

/-! # Compact sets of large measure avoiding every affine geometric copy -/

@[expose] public section

namespace Papers.OaiGeometricErdosSimilarity

-- @realizes p_k(summable density budget)
/-- For [a measure deficit η](hyp:η) [strictly between zero and one](hyp:_hη) and
[an integer dilation index k](hyp:k), the [density budget](goal) is η divided by 64,
multiplied by four to the power minus the absolute value of k. -/
noncomputable def densityBudget (η : ℝ)
    (_hη : TerminalProbabilityDomain η) -- @realizes p_k(budget defined for 0 < η < 1)
    (k : ℤ) : ℝ :=
  -- @realizes k(integer dilation index)
  η / 64 * (4 : ℝ) ^ (-|k|)

-- @node: densityBudget_domain
/-- For [a measure deficit η](hyp:η) [strictly between zero and one](hyp:hη) and
[any integer dilation index k](hyp:k), [the density budget is strictly between
zero and one](goal). -/
lemma densityBudget_domain (η : ℝ) (hη : TerminalProbabilityDomain η) (k : ℤ) :
    TerminalProbabilityDomain (densityBudget η hη k) := by
  have hp : 0 < (4 : ℝ) ^ (-|k|) := zpow_pos (by norm_num) _
  have hle : (4 : ℝ) ^ (-|k|) ≤ 1 :=
    zpow_le_one_of_nonpos₀ (by norm_num) (neg_nonpos.mpr (abs_nonneg k))
  constructor
  · exact mul_pos (div_pos hη.1 (by norm_num)) hp
  · change η / 64 * (4 : ℝ) ^ (-|k|) < 1
    have := mul_le_mul_of_nonneg_left hle (div_nonneg hη.1.le (by norm_num) : 0 ≤ η / 64)
    nlinarith [hη.2]

/-- For [a geometric ratio q](hyp:q) [strictly between zero and one](hyp:hq),
[a measure deficit η](hyp:η) [strictly between zero and one](hyp:hη), and
[an integer dilation index k](hyp:k), the [periodic hitting set](goal) is one
chosen open, period-one set with density at most six times the density budget
at k that meets every sequence of points x + t qⁿ with t between one and two
and n a positive integer. -/
noncomputable def periodicHittingSet (q η : ℝ) -- @realizes H_k(chosen at p_k)
    (hq : QDomain q) (hη : TerminalProbabilityDomain η) (k : ℤ) : Set ℝ :=
  Classical.choose (exists_open_periodic_hitting_set q hq (densityBudget η hη k)
    (densityBudget_domain η hη k))

-- @node: periodicHittingSet_spec
/-- For [a geometric ratio q](hyp:q) [strictly between zero and one](hyp:hq),
[a measure deficit η](hyp:η) [strictly between zero and one](hyp:hη), and
[an integer dilation index k](hyp:k), [the chosen hitting set is open, is invariant
under translation by one, has periodic density at most six times the density
budget at k, and contains some point x + t qⁿ with positive integer n for every
real x and every t between one and two, inclusive](goal). -/
lemma periodicHittingSet_spec (q η : ℝ) (hq : QDomain q)
    (hη : TerminalProbabilityDomain η) (k : ℤ) :
    IsOpen (periodicHittingSet q η hq hη k) ∧
      IsOnePeriodic (periodicHittingSet q η hq hη k) ∧
      periodicDensity (periodicHittingSet q η hq hη k) ≤ 6 * densityBudget η hη k ∧
      ∀ x t : ℝ, t ∈ Set.Icc (1 : ℝ) 2 → ∃ n : ℕ, 1 ≤ n ∧
        x + t * q ^ n ∈ periodicHittingSet q η hq hη k := by
  exact Classical.choose_spec (exists_open_periodic_hitting_set q hq
    (densityBudget η hη k) (densityBudget_domain η hη k))

/-- For [a geometric ratio q](hyp:q) [strictly between zero and one](hyp:hq) and
[a measure deficit η](hyp:η) [strictly between zero and one](hyp:hη), the
[global open set](goal) is the union, over all integer indices k, of the chosen
periodic hitting set at k scaled by both two to the power k and its negative. -/
noncomputable def globalOpen (q η : ℝ) -- @realizes C(union of signed dyadic images)
    (hq : QDomain q) (hη : TerminalProbabilityDomain η) : Set ℝ :=
  ⋃ k : ℤ, ((fun y => (2 : ℝ) ^ k * y) '' periodicHittingSet q η hq hη k ∪
    (fun y => -((2 : ℝ) ^ k) * y) '' periodicHittingSet q η hq hη k)

-- @node: def:global-open
/-- For [a geometric ratio q](hyp:q) [strictly between zero and one](hyp:hq) and
[a measure deficit η](hyp:η) [strictly between zero and one](hyp:hη), the
[avoiding set](goal) consists of the points in the closed unit interval that
do not belong to the global open set. -/
noncomputable def avoidingSet (q η : ℝ) -- @realizes E_{q,\eta}(unit interval minus C)
    (hq : QDomain q) (hη : TerminalProbabilityDomain η) : Set ℝ :=
  Set.Icc 0 1 \ globalOpen q η hq hη

-- @node: globalOpen_isOpen
/-- For [a geometric ratio q](hyp:q) [strictly between zero and one](hyp:hq) and
[a measure deficit η](hyp:η) [strictly between zero and one](hyp:hη),
[the global open set is open](goal). -/
lemma globalOpen_isOpen (q η : ℝ) (hq : QDomain q)
    (hη : TerminalProbabilityDomain η) : IsOpen (globalOpen q η hq hη) := by
  apply isOpen_iUnion
  intro k
  have hp : (2 : ℝ) ^ k ≠ 0 := ne_of_gt (zpow_pos (by norm_num) k)
  have hH := (periodicHittingSet_spec q η hq hη k).1
  exact ((Homeomorph.mulLeft₀ _ hp).isOpenMap _ hH).union
    ((Homeomorph.mulLeft₀ _ (neg_ne_zero.mpr hp)).isOpenMap _ hH)

-- @node: avoidingSet_isCompact
/-- For [a geometric ratio q](hyp:q) [strictly between zero and one](hyp:hq) and
[a measure deficit η](hyp:η) [strictly between zero and one](hyp:hη),
[the avoiding set is compact](goal). -/
lemma avoidingSet_isCompact (q η : ℝ) (hq : QDomain q)
    (hη : TerminalProbabilityDomain η) : IsCompact (avoidingSet q η hq hη) := by
  exact isCompact_Icc.diff (globalOpen_isOpen q η hq hη)

-- @node: globalOpen_neg_iff
/-- For [a geometric ratio q](hyp:q) [strictly between zero and one](hyp:hq),
[a measure deficit η](hyp:η) [strictly between zero and one](hyp:hη), and
[a real point x](hyp:x), [minus x belongs to the global open set if and only if
x does](goal). -/
lemma globalOpen_neg_iff (q η : ℝ) (hq : QDomain q)
    (hη : TerminalProbabilityDomain η) (x : ℝ) :
    -x ∈ globalOpen q η hq hη ↔ x ∈ globalOpen q η hq hη := by
  have hneg : ∀ z ∈ globalOpen q η hq hη, -z ∈ globalOpen q η hq hη := by
    intro z hz
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hz
    apply Set.mem_iUnion.mpr
    refine ⟨k, ?_⟩
    rcases hk with hk | hk
    · obtain ⟨y, hy, rfl⟩ := hk
      exact Or.inr ⟨y, hy, by ring⟩
    · obtain ⟨y, hy, rfl⟩ := hk
      exact Or.inl ⟨y, hy, by ring⟩
  constructor
  · intro hx
    simpa only [neg_neg] using hneg (-x) hx
  · exact hneg x

-- @node: globalOpen_hits_positive
/-- For [a geometric ratio q](hyp:q) [strictly between zero and one](hyp:hq),
[a measure deficit η](hyp:η) [strictly between zero and one](hyp:hη),
[a real center x](hyp:x), and [a real scale s](hyp:s) [that is positive](hyp:hs),
[some point x + s qⁿ with positive integer n belongs to the global open set](goal). -/
lemma globalOpen_hits_positive (q η : ℝ) (hq : QDomain q)
    (hη : TerminalProbabilityDomain η) (x s : ℝ) (hs : 0 < s) :
    ∃ n : ℕ, 1 ≤ n ∧ x + s * q ^ n ∈ globalOpen q η hq hη := by
  obtain ⟨k, hklo, hkhi⟩ := exists_mem_Ico_zpow hs (by norm_num : (1 : ℝ) < 2)
  have hp : 0 < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
  have ht : s / (2 : ℝ) ^ k ∈ Set.Icc (1 : ℝ) 2 := by
    constructor
    · exact (le_div_iff₀ hp).mpr (by simpa using hklo)
    · apply (div_le_iff₀ hp).mpr
      rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one] at hkhi
      linarith
  obtain ⟨n, hn, hhit⟩ := (periodicHittingSet_spec q η hq hη k).2.2.2
    (x / (2 : ℝ) ^ k) (s / (2 : ℝ) ^ k) ht
  refine ⟨n, hn, Set.mem_iUnion.mpr ⟨k, Or.inl ?_⟩⟩
  refine ⟨x / (2 : ℝ) ^ k + s / (2 : ℝ) ^ k * q ^ n, hhit, ?_⟩
  field_simp
  <;> ring

-- @node: avoidingSet_avoids
/-- For [a geometric ratio q](hyp:q) [strictly between zero and one](hyp:hq),
[a measure deficit η](hyp:η) [strictly between zero and one](hyp:hη),
[a real center x](hyp:x), and [a real scale s](hyp:s) [that is nonzero](hyp:hs),
[some point x + s qⁿ with positive integer n lies outside the avoiding set](goal). -/
lemma avoidingSet_avoids (q η : ℝ) (hq : QDomain q)
    (hη : TerminalProbabilityDomain η) (x s : ℝ) (hs : s ≠ 0) :
    ∃ n : ℕ, 1 ≤ n ∧ x + s * q ^ n ∉ avoidingSet q η hq hη := by
  have hhit : ∃ n : ℕ, 1 ≤ n ∧ x + s * q ^ n ∈ globalOpen q η hq hη := by
    rcases lt_or_gt_of_ne hs with hsneg | hspos
    · obtain ⟨n, hn, hmem⟩ := globalOpen_hits_positive q η hq hη (-x) (-s)
        (neg_pos.mpr hsneg)
      refine ⟨n, hn, (globalOpen_neg_iff q η hq hη _).mp ?_⟩
      convert hmem using 1 <;> ring
    · exact globalOpen_hits_positive q η hq hη x s hspos
  obtain ⟨n, hn, hmem⟩ := hhit
  exact ⟨n, hn, fun hE => hE.2 hmem⟩

open MeasureTheory
open scoped BigOperators

-- @node: periodic_indicator_intervalIntegral
/-- For [a set A of real numbers](hyp:A) [that is measurable](hyp:hA) and
[real endpoints a and b](hyp:a,b) [with a at most b](hyp:hab), [the integral of
the indicator of A from a to b equals the Lebesgue measure of A intersected
with the closed interval from a to b, expressed as a real number](goal). -/
lemma periodic_indicator_intervalIntegral (A : Set ℝ) (hA : MeasurableSet A)
    (a b : ℝ) (hab : a ≤ b) :
    (∫ x in a..b, A.indicator (fun _ => (1 : ℝ)) x) =
      (volume (A ∩ Set.Icc a b)).toReal := by
  rw [intervalIntegral.integral_of_le hab, setIntegral_indicator hA]
  simp only [integral_const, smul_eq_mul, mul_one, measureReal_def]
  congr 1
  rw [Measure.restrict_apply_univ, Set.inter_comm]
  exact measure_congr (Filter.EventuallyEq.inter Filter.EventuallyEq.rfl Ioc_ae_eq_Icc)

-- @node: periodic_measure_nat_interval
/-- For [a set A of real numbers](hyp:A) [that is measurable](hyp:hA) and
[invariant under translation by one](hyp:hper), [any real starting point a](hyp:a),
and [any nonnegative integer length N](hyp:N), [the Lebesgue measure of A in the
closed interval from a to a + N, expressed as a real number, equals N times
the periodic density of A](goal). -/
lemma periodic_measure_nat_interval (A : Set ℝ) (hA : MeasurableSet A)
    (hper : IsOnePeriodic A) (a : ℝ) (N : ℕ) :
    (volume (A ∩ Set.Icc a (a + N))).toReal = (N : ℝ) * periodicDensity A := by
  let f := A.indicator (fun _ => (1 : ℝ))
  have hf : Function.Periodic f 1 := by
    intro x
    dsimp [f]
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem ((hper x).mp hx), Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem (fun h => hx ((hper x).mpr h)),
        Set.indicator_of_notMem hx]
  have hi (a b : ℝ) : IntervalIntegrable f volume a b := by
    constructor <;> exact (integrable_const (1 : ℝ)).indicator hA
  have hbase : (∫ x in 0..1, f x) = periodicDensity A := by
    rw [periodic_indicator_intervalIntegral A hA 0 1 (by norm_num)]
    unfold periodicDensity lebesgueMeasure
    congr 1
    exact measure_congr (Filter.EventuallyEq.inter Filter.EventuallyEq.rfl Ico_ae_eq_Icc.symm)
  have h := hf.intervalIntegral_add_zsmul_eq (N : ℤ) a hi
  rw [hf.intervalIntegral_add_eq a 0] at h
  simp only [zero_add, zsmul_eq_mul, Int.cast_natCast, mul_one] at h
  rw [hbase] at h
  rwa [periodic_indicator_intervalIntegral A hA a (a + N)
    (le_add_of_nonneg_right (Nat.cast_nonneg N))] at h

-- @node: volume_mul_image
/-- For [a real scale a](hyp:a) [that is nonzero](hyp:ha) and [any set S of real
numbers](hyp:S), [the Lebesgue measure of S scaled by a equals the absolute
value of a times the Lebesgue measure of S](goal). -/
lemma volume_mul_image (a : ℝ) (ha : a ≠ 0) (S : Set ℝ) :
    volume ((fun x => a * x) '' S) = ENNReal.ofReal |a| * volume S := by
  rw [Set.image_eq_preimage_of_inverse (g := fun x : ℝ => a⁻¹ * x)
    (fun x => by simp [ha]) (fun x => by simp [ha])]
  simpa only [inv_inv] using Real.volume_preimage_mul_left (inv_ne_zero ha) S

-- @node: periodic_dilate_unit_bound
/-- For [a set A of real numbers](hyp:A) [that is measurable](hyp:hA) and
[invariant under translation by one](hyp:hper), and [a real scale a](hyp:a)
[that is positive](hyp:ha), [if a is at least one or its reciprocal is a
nonnegative integer](hyp:hscale), [the Lebesgue measure of the scaled set in
the closed unit interval, expressed as a real number, is at most the larger
of one and a times the periodic density of A](goal). -/
lemma periodic_dilate_unit_bound (A : Set ℝ) (hA : MeasurableSet A)
    (hper : IsOnePeriodic A) (a : ℝ) (ha : 0 < a)
    (hscale : 1 ≤ a ∨ ∃ N : ℕ, a⁻¹ = N) :
    (volume (((fun y => a * y) '' A) ∩ Set.Icc 0 1)).toReal ≤
      max 1 a * periodicDensity A := by
  have heq : ((fun y => a * y) '' A) ∩ Set.Icc 0 1 =
      (fun y => a * y) '' (A ∩ Set.Icc 0 a⁻¹) := by
    rw [Set.image_inter (fun x y h => mul_left_cancel₀ ha.ne' h), Set.image_mul_left_Icc' ha]
    simp [ha.ne']
  rw [heq, volume_mul_image a ha.ne', ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg a), abs_of_pos ha]
  rcases hscale with hlarge | ⟨N, hN⟩
  · have hsub : A ∩ Set.Icc 0 a⁻¹ ⊆ A ∩ Set.Icc 0 1 := by
      apply Set.inter_subset_inter_right
      exact Set.Icc_subset_Icc le_rfl ((inv_le_one₀ ha).mpr hlarge)
    have hbound := measureReal_mono (μ := volume) hsub
      (measure_ne_top_of_subset Set.inter_subset_right (by simp))
    have hone := periodic_measure_nat_interval A hA hper 0 1
    simp only [Nat.cast_one, zero_add, one_mul] at hone
    rw [max_eq_right hlarge]
    exact mul_le_mul_of_nonneg_left (hbound.trans_eq hone) ha.le
  · have hint := periodic_measure_nat_interval A hA hper 0 N
    simp only [zero_add] at hint
    rw [hN, hint]
    have haN : a * (N : ℝ) = 1 := by rw [← hN, mul_inv_cancel₀ ha.ne']
    calc
      a * ((N : ℝ) * periodicDensity A) = periodicDensity A := by rw [← mul_assoc, haN, one_mul]
      _ ≤ max 1 a * periodicDensity A := by
        exact le_mul_of_one_le_left (periodicDensity_mem_Icc A).1 (le_max_left _ _)

-- @node: reflected_periodic_density
/-- For [a set A of real numbers](hyp:A) [that is measurable](hyp:hA) and
[invariant under translation by one](hyp:hper), [its reflection through zero
is measurable, is invariant under translation by one, and has the same periodic
density as A](goal). -/
lemma reflected_periodic_density (A : Set ℝ) (hA : MeasurableSet A)
    (hper : IsOnePeriodic A) :
    MeasurableSet ((fun x : ℝ => -x) '' A) ∧
      IsOnePeriodic ((fun x : ℝ => -x) '' A) ∧
      periodicDensity ((fun x : ℝ => -x) '' A) = periodicDensity A := by
  have hpre : (fun x : ℝ => -x) '' A = (fun x : ℝ => -x) ⁻¹' A := by
    rw [Function.Involutive.image_eq_preimage_symm (fun x : ℝ => neg_neg x)]
  refine ⟨?_, ?_, ?_⟩
  · rw [hpre]
    exact hA.preimage (by fun_prop)
  · intro x
    simp only [hpre, Set.mem_preimage]
    have h := hper (-(x + 1))
    have heq : -(x + 1) + 1 = -x := by ring
    rw [heq] at h
    exact h.symm
  · have heq : ((fun x : ℝ => -x) '' A) ∩ Set.Icc 0 1 =
        (fun x : ℝ => -x) '' (A ∩ Set.Icc (-1) 0) := by
      rw [Set.image_inter (neg_injective)]
      congr 1
      ext x
      simp only [Set.mem_image, Set.mem_Icc]
      constructor
      · intro hx
        exact ⟨-x, ⟨by linarith [hx.2], by linarith [hx.1]⟩, neg_neg x⟩
      · rintro ⟨y, hy, rfl⟩
        constructor <;> linarith [hy.1, hy.2]
    change (volume (((fun x : ℝ => -x) '' A) ∩ Set.Ico 0 1)).toReal = periodicDensity A
    have hc : volume (((fun x : ℝ => -x) '' A) ∩ Set.Ico 0 1) =
        volume (((fun x : ℝ => -x) '' A) ∩ Set.Icc 0 1) :=
      measure_congr (Filter.EventuallyEq.inter Filter.EventuallyEq.rfl
        (Ico_ae_eq_Icc (a := (0 : ℝ)) (b := 1)))
    rw [hc, heq]
    have hvol : volume ((fun x : ℝ => -x) '' (A ∩ Set.Icc (-1) 0)) =
        volume (A ∩ Set.Icc (-1) 0) := by
      simpa using volume_mul_image (-1) (by norm_num) (A ∩ Set.Icc (-1) 0)
    rw [hvol]
    have h := periodic_measure_nat_interval A hA hper (-1) 1
    simpa only [Nat.cast_one, neg_add_cancel, one_mul] using h

-- @node: dyadic_dilate_unit_bound
/-- For [a set A of real numbers](hyp:A) [that is measurable](hyp:hA) and
[invariant under translation by one](hyp:hper), and [any integer k](hyp:k),
[the Lebesgue measure in the closed unit interval of A scaled by two to the
power k is at most the larger of one and two to the power k times the periodic
density of A](goal). -/
lemma dyadic_dilate_unit_bound (A : Set ℝ) (hA : MeasurableSet A)
    (hper : IsOnePeriodic A) (k : ℤ) :
    volume (((fun y => (2 : ℝ) ^ k * y) '' A) ∩ Set.Icc 0 1) ≤
      ENNReal.ofReal (max 1 ((2 : ℝ) ^ k) * periodicDensity A) := by
  have hp : 0 < (2 : ℝ) ^ k := zpow_pos (by norm_num) _
  have hscale : 1 ≤ (2 : ℝ) ^ k ∨ ∃ N : ℕ, ((2 : ℝ) ^ k)⁻¹ = N := by
    rcases k with n | n
    · left
      simpa only [Int.ofNat_eq_natCast, zpow_natCast] using
        (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) : 1 ≤ (2 : ℝ) ^ n)
    · right
      refine ⟨2 ^ (n + 1), ?_⟩
      simp [zpow_negSucc]
  have hb := periodic_dilate_unit_bound A hA hper _ hp hscale
  have hfin : volume (((fun y => (2 : ℝ) ^ k * y) '' A) ∩ Set.Icc 0 1) ≠ ⊤ :=
    measure_ne_top_of_subset Set.inter_subset_right (by simp)
  rw [← ENNReal.ofReal_toReal hfin]
  exact ENNReal.ofReal_le_ofReal hb

-- @node: signed_dyadic_unit_bound
/-- For [a set A of real numbers](hyp:A) [that is measurable](hyp:hA) and
[invariant under translation by one](hyp:hper), and [any integer k](hyp:k),
[the Lebesgue measure in the closed unit interval of the union of A scaled by
two to the power k and by its negative is at most twice the larger of one and
two to the power k times the periodic density of A](goal). -/
lemma signed_dyadic_unit_bound (A : Set ℝ) (hA : MeasurableSet A)
    (hper : IsOnePeriodic A) (k : ℤ) :
    volume ((((fun y => (2 : ℝ) ^ k * y) '' A) ∪
      ((fun y => -((2 : ℝ) ^ k) * y) '' A)) ∩ Set.Icc 0 1) ≤
      ENNReal.ofReal (2 * max 1 ((2 : ℝ) ^ k) * periodicDensity A) := by
  obtain ⟨hm, hp, hd⟩ := reflected_periodic_density A hA hper
  have heq : (fun y => -((2 : ℝ) ^ k) * y) '' A =
      (fun y => (2 : ℝ) ^ k * y) '' ((fun y : ℝ => -y) '' A) := by
    rw [Set.image_image]
    congr 1
    funext y
    ring
  rw [Set.union_inter_distrib_right]
  calc
    _ ≤ _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (max 1 ((2 : ℝ) ^ k) * periodicDensity A) +
        ENNReal.ofReal (max 1 ((2 : ℝ) ^ k) * periodicDensity A) := by
      apply add_le_add (dyadic_dilate_unit_bound A hA hper k)
      rw [heq]
      simpa only [hd] using dyadic_dilate_unit_bound _ hm hp k
    _ = _ := by
      rw [← ENNReal.ofReal_add (mul_nonneg (le_trans zero_le_one (le_max_left _ _))
        (periodicDensity_mem_Icc A).1) (mul_nonneg (le_trans zero_le_one (le_max_left _ _))
        (periodicDensity_mem_Icc A).1)]
      congr 1
      ring

-- @node: densityBudget_weighted_hasSum
/-- For [a measure deficit η](hyp:η) [strictly between zero and one](hyp:hη),
[the sum over all integer indices k of twelve times the density budget at k
times the larger of one and two to the power k converges to seven η divided
by sixteen](goal). -/
lemma densityBudget_weighted_hasSum (η : ℝ) (hη : TerminalProbabilityDomain η) :
    HasSum (fun k : ℤ => 12 * densityBudget η hη k * max 1 ((2 : ℝ) ^ k))
      (7 * η / 16) := by
  let c := 12 * η / 64
  have hpos (n : ℕ) :
      12 * densityBudget η hη (n : ℤ) * max 1 ((2 : ℝ) ^ (n : ℤ)) =
        c * (1 / 2 : ℝ) ^ n := by
    have hpow : 1 ≤ (2 : ℝ) ^ (n : ℤ) := by
      simpa using (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) : 1 ≤ (2 : ℝ) ^ n)
    rw [max_eq_right hpow]
    simp only [densityBudget, abs_of_nonneg (Int.natCast_nonneg n), zpow_neg, zpow_natCast]
    rw [← inv_pow]
    calc
      12 * (η / 64 * (4 : ℝ)⁻¹ ^ n) * 2 ^ n =
          (12 * η / 64) * ((4 : ℝ)⁻¹ ^ n * 2 ^ n) := by ring
      _ = _ := by rw [← mul_pow]; norm_num [c]
  have hneg (n : ℕ) :
      12 * densityBudget η hη (-((n : ℤ) + 1)) * max 1 ((2 : ℝ) ^ (-((n : ℤ) + 1))) =
        (c / 4) * (1 / 4 : ℝ) ^ n := by
    have hk : -((n : ℤ) + 1) ≤ 0 := by omega
    rw [max_eq_left (zpow_le_one_of_nonpos₀ (by norm_num) hk)]
    simp only [densityBudget, abs_of_nonpos hk, neg_neg, mul_one]
    rw [show -((n : ℤ) + 1) = -((n + 1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast,
      ← inv_pow, pow_succ]
    norm_num [c]
    ring
  have hp : HasSum (fun n : ℕ => c * (1 / 2 : ℝ) ^ n) (c * 2) := by
    have hp := (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_left c
    norm_num at hp
    exact hp
  have hn : HasSum (fun n : ℕ => (c / 4) * (1 / 4 : ℝ) ^ n) (c / 3) := by
    have hn := (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num : (1 / 4 : ℝ) < 1)).mul_left (c / 4)
    norm_num at hn
    have hc : c / 4 * (4 / 3) = c / 3 := by ring
    rw [hc] at hn
    exact hn
  have h : HasSum (fun k : ℤ => 12 * densityBudget η hη k * max 1 ((2 : ℝ) ^ k))
      (c * 2 + c / 3) :=
    HasSum.of_nat_of_neg_add_one (by simpa only [hpos] using hp)
      (by simpa only [hneg] using hn)
  have hc : c * 2 + c / 3 = 7 * η / 16 := by dsimp [c]; ring
  rwa [hc] at h

-- @node: globalOpen_unit_measure_le
/-- For [a geometric ratio q](hyp:q) [strictly between zero and one](hyp:hq) and
[a measure deficit η](hyp:η) [strictly between zero and one](hyp:hη),
[the Lebesgue measure of the global open set in the closed unit interval is
at most seven η divided by sixteen](goal). -/
lemma globalOpen_unit_measure_le (q η : ℝ) (hq : QDomain q)
    (hη : TerminalProbabilityDomain η) :
    volume (globalOpen q η hq hη ∩ Set.Icc 0 1) ≤ ENNReal.ofReal (7 * η / 16) := by
  have hs := densityBudget_weighted_hasSum η hη
  have hnonneg (k : ℤ) : 0 ≤ 12 * densityBudget η hη k * max 1 ((2 : ℝ) ^ k) := by
    have := (densityBudget_domain η hη k).1
    positivity
  unfold globalOpen
  rw [Set.iUnion_inter]
  calc
    _ ≤ _ := measure_iUnion_le _
    _ ≤ ∑' k : ℤ, ENNReal.ofReal (12 * densityBudget η hη k * max 1 ((2 : ℝ) ^ k)) := by
      apply ENNReal.tsum_le_tsum
      intro k
      have hH := periodicHittingSet_spec q η hq hη k
      apply (signed_dyadic_unit_bound _ hH.1.measurableSet hH.2.1 k).trans
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ 2 * max 1 ((2 : ℝ) ^ k) * (6 * densityBudget η hη k) :=
          mul_le_mul_of_nonneg_left hH.2.2.1 (by positivity)
        _ = _ := by ring
    _ = _ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg hs.summable, hs.tsum_eq]

-- @node: thm:main
/-- For [a real geometric ratio q](hyp:q) [greater than zero](hyp:hq0) and
[less than one](hyp:hq1), and [a real measure deficit η](hyp:η)
[greater than zero](hyp:hη0) and [less than one](hyp:hη1), [there exists a compact
subset E of the closed unit interval with Lebesgue measure strictly greater
than one minus η such that, for every real center x and every nonzero real
scale s, some point x + s qⁿ with positive integer n lies outside E](goal). -/
theorem exists_compact_avoiding_geometric_affine_copies (q η : ℝ)
    (hq0 : 0 < q) (hq1 : q < 1) (hη0 : 0 < η) (hη1 : η < 1) : -- @realizes \eta(deficit in (0,1))
    ∃ E : Set ℝ, IsCompact E ∧ E ⊆ Set.Icc 0 1 ∧
      ENNReal.ofReal (1 - η) < lebesgueMeasure E ∧
      ∀ x : ℝ, -- @realizes x(every real center)
      ∀ s : ℝ, s ≠ 0 → -- @realizes s(every nonzero real dilation)
        ∃ n : ℕ, 1 ≤ n ∧ x + s * q ^ n ∉ E := by
  let hq : QDomain q := ⟨hq0, hq1⟩
  let hη : TerminalProbabilityDomain η := ⟨hη0, hη1⟩
  refine ⟨avoidingSet q η hq hη, avoidingSet_isCompact q η hq hη,
    Set.diff_subset, ?_, ?_⟩
  · have hbound := globalOpen_unit_measure_le q η hq hη
    have hEfin : volume (avoidingSet q η hq hη) ≠ ⊤ :=
      measure_ne_top_of_subset Set.sdiff_subset (by simp)
    have hCfin : volume (globalOpen q η hq hη ∩ Set.Icc 0 1) ≠ ⊤ :=
      measure_ne_top_of_subset Set.inter_subset_right (by simp)
    have hsplit := measure_sdiff_add_inter (μ := volume) (Set.Icc (0 : ℝ) 1)
      (globalOpen_isOpen q η hq hη).measurableSet
    rw [Set.inter_comm] at hsplit
    have hreal := congrArg ENNReal.toReal hsplit
    change (volume (avoidingSet q η hq hη) +
      volume (globalOpen q η hq hη ∩ Set.Icc 0 1)).toReal = _ at hreal
    rw [ENNReal.toReal_add hEfin hCfin] at hreal
    norm_num at hreal
    have hsmall : (volume (globalOpen q η hq hη ∩ Set.Icc 0 1)).toReal ≤ 7 * η / 16 := by
      simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ 7 * η / 16)] using
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
    rw [← ENNReal.ofReal_toReal hEfin]
    apply ENNReal.ofReal_lt_ofReal_iff'.mpr
    constructor <;> linarith
  · exact avoidingSet_avoids q η hq hη

end Papers.OaiGeometricErdosSimilarity

module
public import Papers.OaiGeometricErdosSimilarity.Helpers
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! # Open periodic sets meeting every normalized affine progression

All construction parameters are chosen from the ratio and budget. Each random realization is
openly enlarged; its closed exceptional-center set is then repaired by an open periodic
neighborhood, whose centers are hit at sufficiently large positive indices.
-/

@[expose] public section

namespace Papers.OaiGeometricErdosSimilarity

open Causalean.Experimentation.DesignBased
attribute [local instance] Classical.propDecidable

variable {q p : ℝ} {M d g r0 n0 : ℕ}

-- @node: scaleCount_decay
/-- If [q lies strictly between zero and one](hyp:hq) and [a exceeds twice the
natural logarithm of 1/q](hyp:ha), [the scale-count bound at length r times
exp(−ar) converges to zero as r grows](goal). -/
lemma scaleCount_decay (hq : QDomain q) {a : ℝ}
    (ha : 2 * Real.log (1 / q) < a) :
    Filter.Tendsto (fun r : ℕ => scaleCount M q r * Real.exp (-(a * r)))
      Filter.atTop (nhds 0) := by
  have hlog : 0 < Real.log (1 / q) := Real.log_pos (by
    rw [one_div]
    exact (one_lt_inv₀ hq.1).2 hq.2)
  have ha0 : 0 < a := by linarith
  have hbase : Real.exp (2 * Real.log (1 / q)) = (q⁻¹) ^ 2 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul]
    rw [Real.exp_log (div_pos zero_lt_one hq.1)]
    simp [one_div]
  have hexp (r : ℕ) : Real.exp (-(a * r)) = Real.exp (-a) ^ r := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hprod (r : ℕ) : q ^ (-(2 * (r : ℤ))) * Real.exp (-(a * r)) =
      Real.exp (2 * Real.log (1 / q) - a) ^ r := by
    rw [show -(2 * (r : ℤ)) = -((2 * r : ℕ) : ℤ) by omega,
      zpow_neg, zpow_natCast, pow_mul, ← inv_pow, ← inv_pow, hexp,
      ← mul_pow, ← hbase, ← Real.exp_add]
    congr 2
  have h0 := tendsto_pow_atTop_nhds_zero_of_lt_one
    (Real.exp_pos (-a)).le (by simpa using (Real.exp_lt_one_iff.mpr (neg_neg_of_pos ha0)))
  have h1 := tendsto_pow_const_mul_const_pow_of_lt_one 1
    (Real.exp_pos (-a)).le (by simpa using (Real.exp_lt_one_iff.mpr (neg_neg_of_pos ha0)))
  have h2 := tendsto_pow_const_mul_const_pow_of_lt_one 1
    (Real.exp_pos (2 * Real.log (1 / q) - a)).le
    (Real.exp_lt_one_iff.mpr (sub_neg.mpr ha))
  have hlim := (h0.const_mul 4).add
    ((h1.const_mul (2 * ((M : ℝ) - 1))).add
      (h2.const_mul (4 * ((M : ℝ) - 1) * gridConst q)))
  simp only [mul_zero, add_zero] at hlim
  convert hlim using 1
  funext r
  simp only [pow_one]
  rw [← hexp, ← hprod]
  unfold scaleCount
  ring

-- @node: construction_parameters_exist
/-- If [q lies strictly between zero and one](hyp:hq) and [p lies strictly between
zero and one](hyp:hp), [there exist integers M ≥ 2, d ≥ 1, rstar ≥ 1, and g ≥ 1
such that p(M − 1)/2 exceeds twice the natural logarithm of 1/q,
(1 − 2 to the power 1 − M) to the power d is less than p, the scale-count bound
times exp(−p(M − 1)r/2) is less than p for every r ≥ rstar, and four times the
edge count times the grid constant times q to the power g + 1 is less than p](goal). -/
lemma construction_parameters_exist (hq : QDomain q) (hp : TerminalProbabilityDomain p) :
    ∃ M : ℕ, BranchingDomain M ∧
      2 * Real.log (1 / q) < p * ((M : ℝ) - 1) / 2 ∧ -- @realizes \alpha(decay exponent)
      ∃ d : ℕ, DepthDomain d ∧ (1 - (2 : ℝ) ^ (1 - (M : ℤ))) ^ d < p ∧
      ∃ rstar : ℕ, BaseLengthDomain rstar ∧ -- @realizes r_*(positive threshold)
        (∀ r : ℕ, rstar ≤ r →
          scaleCount M q r * Real.exp (-(p * ((M : ℝ) - 1) * r / 2)) < p) ∧
        ∃ g : ℕ, GapDomain g ∧ 4 * edgeCount M d * gridConst q * q ^ (g + 1) < p := by
  obtain ⟨N, hN⟩ := exists_nat_gt (4 * Real.log (1 / q) / p + 1)
  let M := N + 2
  have hM : BranchingDomain M := by unfold BranchingDomain M; omega
  have hα : 2 * Real.log (1 / q) < p * ((M : ℝ) - 1) / 2 := by
    have hN' : 4 * Real.log (1 / q) < ((N : ℝ) - 1) * p := by
      apply (div_lt_iff₀ hp.1).mp
      linarith
    dsimp [M]
    push_cast
    nlinarith [hp.1]
  have hβpos : 0 < (2 : ℝ) ^ (1 - (M : ℤ)) := zpow_pos (by norm_num) _
  have hβle : (2 : ℝ) ^ (1 - (M : ℤ)) ≤ 1 :=
    zpow_le_one_of_nonpos₀ (by norm_num) (by
      have : 2 ≤ M := hM
      omega)
  have hdlim := tendsto_pow_atTop_nhds_zero_of_lt_one
    (sub_nonneg.mpr hβle) (sub_lt_self (1 : ℝ) hβpos)
  obtain ⟨D, hD⟩ := Filter.eventually_atTop.mp (hdlim.eventually (gt_mem_nhds hp.1))
  let d := max D 1
  have hd : DepthDomain d := le_max_right _ _
  have hdp : (1 - (2 : ℝ) ^ (1 - (M : ℤ))) ^ d < p := hD d (le_max_left _ _)
  have hr_lim := scaleCount_decay (M := M) hq hα
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp (hr_lim.eventually (gt_mem_nhds hp.1))
  let rstar := max R 1
  have hrstar : BaseLengthDomain rstar := le_max_right _ _
  have hsmall (r : ℕ) (hr : rstar ≤ r) :
      scaleCount M q r * Real.exp (-(p * ((M : ℝ) - 1) * r / 2)) < p := by
    have hb := hR r ((le_max_left R 1).trans hr)
    convert hb using 1 <;> congr 2 <;> ring
  have hg_lim : Filter.Tendsto
      (fun g : ℕ => 4 * (edgeCount M d : ℝ) * gridConst q * q ^ (g + 1))
      Filter.atTop (nhds 0) := by
    simpa only [pow_succ, zero_mul, mul_zero, mul_assoc] using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hq.1.le hq.2).mul_const q).const_mul
        (4 * (edgeCount M d : ℝ) * gridConst q)
  obtain ⟨G, hG⟩ := Filter.eventually_atTop.mp (hg_lim.eventually (gt_mem_nhds hp.1))
  exact ⟨M, hM, hα, d, hd, hdp, rstar, hrstar, hsmall,
    max G 1, le_max_right _ _, hG _ (le_max_left _ _)⟩

-- @node: periodic_preimage_circle_image
/-- If [a real set A is invariant under translation by one](hyp:hper), [mapping A
to the circle of circumference one and taking its full preimage recovers A](goal). -/
lemma periodic_preimage_circle_image (A : Set ℝ) (hper : IsOnePeriodic A) :
    ((↑) : ℝ → AddCircle (1 : ℝ)) ⁻¹' (((↑) : ℝ → AddCircle (1 : ℝ)) '' A) = A := by
  have hp : Function.Periodic (fun x : ℝ => x ∈ A) 1 :=
    fun x => propext (hper x).symm
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    have hz : ((y - x : ℝ) : AddCircle (1 : ℝ)) = 0 := by
      rw [AddCircle.coe_sub, hxy, sub_self]
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hz
    have hshift : x + (n : ℝ) * 1 = y := by
      simp only [zsmul_eq_mul] at hn
      linarith
    have hmem := hp.int_mul n x
    rw [hshift] at hmem
    exact hmem ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

-- @node: periodicDensity_circle_preimage
/-- If [B is a measurable subset of the circle of circumference one](hyp:hB),
[the periodic density of its preimage on the real line equals its circle measure,
expressed as a real number](goal). -/
lemma periodicDensity_circle_preimage (B : Set (AddCircle (1 : ℝ)))
    (hB : MeasurableSet B) :
    periodicDensity (((↑) : ℝ → AddCircle (1 : ℝ)) ⁻¹' B) =
      (MeasureTheory.volume B).toReal := by
  have heq : MeasureTheory.volume
      ((((↑) : ℝ → AddCircle (1 : ℝ)) ⁻¹' B) ∩ Set.Ico (0 : ℝ) 1) =
      MeasureTheory.volume ((((↑) : ℝ → AddCircle (1 : ℝ)) ⁻¹' B) ∩ Set.Ioc (0 : ℝ) 1) := by
    exact MeasureTheory.measure_congr
      (Filter.EventuallyEq.inter Filter.EventuallyEq.rfl MeasureTheory.Ico_ae_eq_Ioc)
  unfold periodicDensity lebesgueMeasure
  rw [heq]
  exact congrArg ENNReal.toReal
    (by simpa only [zero_add] using
      (AddCircle.add_projection_respects_measure (1 : ℝ) 0 hB).symm)

-- @node: exists_open_periodic_superset
/-- If [A is measurable](hyp:hA), [A is invariant under translation by one](hyp:hper),
and [ε is positive](hyp:hε), [A has an open superset invariant under translation
by one whose periodic density is at most the periodic density of A plus ε](goal). -/
lemma exists_open_periodic_superset (A : Set ℝ) (hA : MeasurableSet A)
    (hper : IsOnePeriodic A) (ε : ℝ) (hε : 0 < ε) :
    ∃ O : Set ℝ, IsOpen O ∧ IsOnePeriodic O ∧ A ⊆ O ∧
      periodicDensity O ≤ periodicDensity A + ε := by
  let B : Set (AddCircle (1 : ℝ)) := ((↑) : ℝ → AddCircle (1 : ℝ)) '' A
  have hpre : ((↑) : ℝ → AddCircle (1 : ℝ)) ⁻¹' B = A :=
    periodic_preimage_circle_image A hper
  have hB : MeasurableSet B := by
    apply measurableSet_quotient.mpr
    change MeasurableSet (((↑) : ℝ → AddCircle (1 : ℝ)) ⁻¹' B)
    rwa [hpre]
  obtain ⟨V, hBV, hV, hvol⟩ := B.exists_isOpen_lt_add
    (μ := MeasureTheory.volume) (MeasureTheory.measure_ne_top _ _)
    (ENNReal.ofReal_ne_zero_iff.mpr hε)
  refine ⟨((↑) : ℝ → AddCircle (1 : ℝ)) ⁻¹' V,
    hV.preimage (AddCircle.continuous_mk' _), ?_, ?_, ?_⟩
  · intro x
    change (x : AddCircle (1 : ℝ)) ∈ V ↔ ((x + 1 : ℝ) : AddCircle (1 : ℝ)) ∈ V
    rw [AddCircle.coe_add_period]
  · intro x hx
    exact hBV ⟨x, hx, rfl⟩
  · rw [periodicDensity_circle_preimage V hV.measurableSet]
    have hden : periodicDensity A = (MeasureTheory.volume B).toReal := by
      rw [← hpre]
      exact periodicDensity_circle_preimage B hB
    rw [hden]
    have hreal := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨MeasureTheory.measure_ne_top _ _, ENNReal.ofReal_ne_top⟩) hvol.le
    simpa only [ENNReal.toReal_add (MeasureTheory.measure_ne_top _ _) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hε.le] using hreal

/-- For [ratio q](hyp:q), [branching count M](hyp:M), [depth d](hyp:d),
[gap g](hyp:g), [base length r0](hyp:r0), [starting index n0](hyp:n0), and
[probability budget p](hyp:p), given [M ≥ 2](hyp:hM), [0 < p < 1](hyp:hp), and
[a random-table outcome ω](hyp:ω), [the enlarged random set is a chosen open,
one-periodic superset of the random set with periodic density at most that of
the random set plus p](goal). -/
noncomputable def enlargedRandomSet (hM : BranchingDomain M) (hp : TerminalProbabilityDomain p)
    (ω : Outcome q M d g r0 n0) : Set ℝ :=
      -- @realizes B^+(one chosen open periodic enlargement per outcome)
  Classical.choose (exists_open_periodic_superset (randomSet hM ω)
    (measurableSet_randomSet hM ω) (randomSet_isOnePeriodic hM ω) p hp.1)

-- @node: enlargedRandomSet_spec
/-- Given [M ≥ 2](hyp:hM), [0 < p < 1](hyp:hp), and [a random-table outcome ω](hyp:ω),
[the enlarged random set is open, invariant under translation by one, contains
the random set, and has periodic density at most that of the random set plus p](goal). -/
lemma enlargedRandomSet_spec (hM : BranchingDomain M) (hp : TerminalProbabilityDomain p)
    (ω : Outcome q M d g r0 n0) :
    IsOpen (enlargedRandomSet hM hp ω) ∧ IsOnePeriodic (enlargedRandomSet hM hp ω) ∧
    randomSet hM ω ⊆ enlargedRandomSet hM hp ω ∧
    periodicDensity (enlargedRandomSet hM hp ω) ≤ periodicDensity (randomSet hM ω) + p := by
  exact Classical.choose_spec (exists_open_periodic_superset (randomSet hM ω)
    (measurableSet_randomSet hM ω) (randomSet_isOnePeriodic hM ω) p hp.1)

/-- For [ratio q](hyp:q), [branching count M](hyp:M), [depth d](hyp:d),
[gap g](hyp:g), [base length r0](hyp:r0), [starting index n0](hyp:n0), and
[probability budget p](hyp:p), given [M ≥ 2](hyp:hM), [0 < p < 1](hyp:hp), and
[a random-table outcome ω](hyp:ω), [the exceptional centers are the real points x
for which some scale t between one and two, inclusive, makes every point
x + t qⁿ at a construction index fall outside the enlarged random set](goal). -/
noncomputable def exceptionalCenters (hM : BranchingDomain M) (hp : TerminalProbabilityDomain p)
    (ω : Outcome q M d g r0 n0) : Set ℝ :=
      -- @realizes R(centers missing the fixed open enlargement at some normalized scale)
  {x | ∃ t ∈ Set.Icc (1 : ℝ) 2, ∀ n ∈ indexSet q M d g r0 n0,
    localPoint x t q n ∉ enlargedRandomSet hM hp ω}

-- @node: exceptionalCenters_closed_periodic
/-- Given [M ≥ 2](hyp:hM), [0 < p < 1](hyp:hp), and [a random-table outcome ω](hyp:ω),
[the set of exceptional centers is closed and invariant under translation by one](goal). -/
lemma exceptionalCenters_closed_periodic (hM : BranchingDomain M)
    (hp : TerminalProbabilityDomain p) (ω : Outcome q M d g r0 n0) :
    IsClosed (exceptionalCenters hM hp ω) ∧ IsOnePeriodic (exceptionalCenters hM hp ω) := by
  have hopen := (enlargedRandomSet_spec hM hp ω).1
  have hper := (enlargedRandomSet_spec hM hp ω).2.1
  constructor
  · letI : CompactSpace (Set.Icc (1 : ℝ) 2) := isCompact_iff_compactSpace.mp isCompact_Icc
    let F : Set (ℝ × Set.Icc (1 : ℝ) 2) :=
      {z | ∀ n ∈ indexSet q M d g r0 n0,
        localPoint z.1 z.2.val q n ∉ enlargedRandomSet hM hp ω}
    have hF : IsClosed F := by
      simp only [F, Set.setOf_forall]
      apply isClosed_biInter
      intro n hn
      apply hopen.isClosed_compl.preimage
      unfold localPoint
      fun_prop
    have heq : exceptionalCenters hM hp ω = Prod.fst '' F := by
      ext x
      constructor
      · rintro ⟨t, ht, hmiss⟩
        exact ⟨(x, ⟨t, ht⟩), hmiss, rfl⟩
      · rintro ⟨⟨y, t⟩, hmiss, rfl⟩
        exact ⟨t.val, t.property, hmiss⟩
    rw [heq]
    exact isClosedMap_fst_of_compactSpace F hF
  · intro x
    constructor
    · rintro ⟨t, ht, hmiss⟩
      refine ⟨t, ht, ?_⟩
      intro n hn hhit
      apply hmiss n hn
      apply (hper (localPoint x t q n)).mpr
      convert hhit using 1 <;> simp only [localPoint] <;> ring
    · rintro ⟨t, ht, hmiss⟩
      refine ⟨t, ht, ?_⟩
      intro n hn hhit
      apply hmiss n hn
      have hhit' := (hper (localPoint x t q n)).mp hhit
      convert hhit' using 1 <;> simp only [localPoint] <;> ring

/-- For [ratio q](hyp:q), [branching count M](hyp:M), [depth d](hyp:d),
[gap g](hyp:g), [base length r0](hyp:r0), [starting index n0](hyp:n0), and
[probability budget p](hyp:p), given [M ≥ 2](hyp:hM), [0 < p < 1](hyp:hp), and
[a random-table outcome ω](hyp:ω), [the open repair set is a chosen open,
one-periodic superset of the exceptional centers with periodic density at most
that of the exceptional centers plus p](goal). -/
noncomputable def openRepairSet (hM : BranchingDomain M) (hp : TerminalProbabilityDomain p)
    (ω : Outcome q M d g r0 n0) : Set ℝ :=
      -- @realizes V(one chosen open periodic superset of the exceptional centers)
  Classical.choose (exists_open_periodic_superset (exceptionalCenters hM hp ω)
    (exceptionalCenters_closed_periodic hM hp ω).1.measurableSet
    (exceptionalCenters_closed_periodic hM hp ω).2 p hp.1)

-- @node: openRepairSet_spec
/-- Given [M ≥ 2](hyp:hM), [0 < p < 1](hyp:hp), and [a random-table outcome ω](hyp:ω),
[the open repair set is open, invariant under translation by one, contains all
exceptional centers, and has periodic density at most that of the exceptional
centers plus p](goal). -/
lemma openRepairSet_spec (hM : BranchingDomain M) (hp : TerminalProbabilityDomain p)
    (ω : Outcome q M d g r0 n0) :
    IsOpen (openRepairSet hM hp ω) ∧ IsOnePeriodic (openRepairSet hM hp ω) ∧
    exceptionalCenters hM hp ω ⊆ openRepairSet hM hp ω ∧
    periodicDensity (openRepairSet hM hp ω) ≤ periodicDensity (exceptionalCenters hM hp ω) + p
      := by
  exact Classical.choose_spec (exists_open_periodic_superset (exceptionalCenters hM hp ω)
    (exceptionalCenters_closed_periodic hM hp ω).1.measurableSet
    (exceptionalCenters_closed_periodic hM hp ω).2 p hp.1)

-- @node: pr_le_bad_fibers_add
/-- For [a probability design D on a finite outcome space](hyp:D), [an event A](hyp:A),
[a finite-valued classification c](hyp:c), and [a set B of bad classes](hyp:B),
if [ε is nonnegative](hyp:hε) and [the conditional probability of A in every
class outside B is at most ε](hyp:hgood), [the probability of A is at most the
probability of belonging to a bad class plus ε](goal). -/
lemma pr_le_bad_fibers_add {Ω I : Type*} [Fintype Ω] [Fintype I]
    (D : FiniteDesign Ω) (A : Ω → Prop) (c : Ω → I) (B : I → Prop)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hgood : ∀ i, ¬ B i → condPr D A (fun ω => c ω = i) ≤ ε) :
    D.Pr A ≤ D.Pr (fun ω => B (c ω)) + ε := by
  classical
  let F (i : I) := condPr D A (fun ω => c ω = i)
  have htotal := condPr_eq_condE_of_finite_fibers D A c (fun _ => True) F
    (fun _ => rfl)
  have havg : D.Pr A = D.E (fun ω => F (c ω)) := by
    simp only [condPr, condE, and_true, if_true] at htotal
    unfold FiniteDesign.Pr FiniteDesign.ind at htotal ⊢
    simp only [if_true, D.E_const, div_one] at htotal
    exact htotal
  have hbound (i : I) : F i ≤ FiniteDesign.ind B i + ε := by
    by_cases hi : B i
    · have hmono := D.Pr_mono (fun ω => A ω ∧ c ω = i) (fun ω => c ω = i)
        (fun _ h => h.2)
      have hden := D.Pr_nonneg (fun ω => c ω = i)
      have hle : F i ≤ 1 := by
        dsimp [F, condPr]
        by_cases hz : D.Pr (fun ω => c ω = i) = 0
        · simp [hz]
        · exact (div_le_iff₀ (lt_of_le_of_ne hden (Ne.symm hz))).mpr (by simpa using hmono)
      simpa [FiniteDesign.ind, hi] using hle.trans (by linarith : (1 : ℝ) ≤ 1 + ε)
    · simpa [F, FiniteDesign.ind, hi] using hgood i hi
  calc
    D.Pr A = D.E (fun ω => F (c ω)) := havg
    _ ≤ D.E (fun ω => FiniteDesign.ind B (c ω) + ε) :=
      Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (hbound _) (D.p_nonneg ω))
    _ = D.Pr (fun ω => B (c ω)) + ε := by rw [D.E_add, D.E_const]; rfl

-- @node: pr_exceptionalCenters_le_of_stable
/-- Suppose [0 < q < 1](hyp:hq), [M ≥ 2](hyp:hM), [d ≥ 1](hyp:hd),
[g ≥ 1](hyp:hg), [r0 ≥ 1](hyp:hr), [n0 ≥ 1](hyp:hn0),
[twice q to the power n0 is at most 1/4](hyp:hn0q), and [0 < p < 1](hyp:hp).
If [the scale-count bound times exp(−p(M − 1)r/2) is less than p for every
r ≥ r0](hyp:hdecay) and [x satisfies the stable-center condition, so each edge's
forward interval from x avoids every predecessor's endpoint grid](hyp:hx),
[the probability under the random-table law that x is exceptional is at most
(1 − 2 to the power 1 − M) to the power d plus p](goal). -/
lemma pr_exceptionalCenters_le_of_stable (hq : QDomain q) (hM : BranchingDomain M)
    (hd : DepthDomain d) (hg : GapDomain g) (hr : BaseLengthDomain r0)
    (hn0 : 1 ≤ n0) (hn0q : 2 * q ^ n0 ≤ 1 / 4)
    (hp : TerminalProbabilityDomain p)
    (hdecay : ∀ r : ℕ, r0 ≤ r →
      scaleCount M q r * Real.exp (-(p * ((M : ℝ) - 1) * r / 2)) < p)
    (x : ℝ) (hx : StableCenterCondition q M d g r0 n0 x) :
    (tableLaw q M d g r0 n0 p).Pr (fun ω => x ∈ exceptionalCenters hM hp ω) ≤
      (1 - (2 : ℝ) ^ (1 - (M : ℤ))) ^ d + p := by
  let D := tableLaw q M d g r0 n0 p
  let A : Outcome q M d g r0 n0 → Prop := fun ω => ∃ t ∈ Set.Icc (1 : ℝ) 2,
    ∀ n ∈ indexSet q M d g r0 n0, localPoint x t q n ∉ randomSet hM ω
  have hcover : D.Pr (fun ω => x ∈ exceptionalCenters hM hp ω) ≤ D.Pr A := by
    apply D.Pr_mono
    rintro ω ⟨t, ht, hmiss⟩
    exact ⟨t, ht, fun n hn hhit => hmiss n hn ((enlargedRandomSet_spec hM hp ω).2.2.1 hhit)⟩
  have hfiber (ξ : NondefaultEdge M d → Bool)
      (hξ : ¬ firstDefault q M d g r0 hM x ξ = none) :
      condPr D A (fun ω => exposedValues ω x = ξ) ≤ p := by
    obtain ⟨U, hU⟩ := Option.ne_none_iff_exists'.mp hξ
    have hcond := condPr_exists_scale_miss_le hq hM hd hg hr hn0 hn0q hp
      ⟨hp, hM, hd, hg, hr⟩ x hx ξ
      (show ConditionalScalesDefaultAtom q M d g r0 hM x ξ from by
        change (firstDefault q M d g r0 hM x ξ).isSome; rw [hU]; rfl)
      U (vertexHeight U.val) ⟨hU, rfl⟩
    have hatom : (fun ω : Outcome q M d g r0 n0 => exposedValues ω x = ξ) =
        atomEvent q M d g r0 n0 x ξ := by
      funext ω
      exact propext ⟨fun h e => congrFun h e, fun h => funext h⟩
    rw [hatom]
    exact hcond.trans (hdecay _ (baseLength_le_windowLength M g r0 _)).le
  have hb := pr_le_bad_fibers_add D A (fun ω => exposedValues ω x)
    (fun ξ => firstDefault q M d g r0 hM x ξ = none) p hp.1.le hfiber
  change D.Pr A ≤ D.Pr (noDefaultEvent q M d g r0 n0 hM x) + p at hb
  rw [show D.Pr (noDefaultEvent q M d g r0 n0 hM x) =
    (1 - (2 : ℝ) ^ (1 - (M : ℤ))) ^ d from pr_noDefaultEvent hM x] at hb
  exact hcover.trans hb

-- @node: expected_exceptional_density_le
/-- Suppose [0 < q < 1](hyp:hq), [M ≥ 2](hyp:hM), [d ≥ 1](hyp:hd),
[g ≥ 1](hyp:hg), [r0 ≥ 1](hyp:hr), [n0 ≥ 1](hyp:hn0),
[twice q to the power n0 is at most 1/4](hyp:hn0q), and [0 < p < 1](hyp:hp).
If [four times the edge count times the grid constant times q to the power
g + 1 is less than p](hyp:hgap), [(1 − 2 to the power 1 − M) to the power d
is less than p](hyp:hdepth), and [the scale-count bound times
exp(−p(M − 1)r/2) is less than p for every r ≥ r0](hyp:hdecay),
[the expected periodic density of the exceptional centers under the random-table
law is at most 3p](goal). -/
lemma expected_exceptional_density_le (hq : QDomain q) (hM : BranchingDomain M)
    (hd : DepthDomain d) (hg : GapDomain g) (hr : BaseLengthDomain r0)
    (hn0 : 1 ≤ n0) -- @realizes n_0(positive starting index)
    (hn0q : 2 * q ^ n0 ≤ 1 / 4) -- @realizes n_0(smallness at the supplied index)
    (hp : TerminalProbabilityDomain p)
    (hgap : 4 * edgeCount M d * gridConst q * q ^ (g + 1) < p)
    (hdepth : (1 - (2 : ℝ) ^ (1 - (M : ℤ))) ^ d < p)
    (hdecay : ∀ r : ℕ, r0 ≤ r →
      scaleCount M q r * Real.exp (-(p * ((M : ℝ) - 1) * r / 2)) < p) :
    (tableLaw q M d g r0 n0 p).E
      (fun ω => periodicDensity (exceptionalCenters hM hp ω)) ≤ 3 * p := by
  classical
  let μ := MeasureTheory.volume.restrict (Set.Ico (0 : ℝ) 1)
  let D := tableLaw q M d g r0 n0 p
  let S := stableSet q M d g r0 n0
  have hS : MeasurableSet S := stableSet_measurable q g r0 hr hn0
  have hmeas (ω : Outcome q M d g r0 n0) :=
    (exceptionalCenters_closed_periodic hM hp ω).1.measurableSet
  have hint (ω : Outcome q M d g r0 n0) :
      MeasureTheory.Integrable ((exceptionalCenters hM hp ω).indicator (fun _ => (1 : ℝ))) μ := by
    first | fun_prop | skip
    exact MeasureTheory.integrable_const (1 : ℝ) |>.indicator (hmeas ω)
  have hden (A : Set ℝ) (hA : MeasurableSet A) : periodicDensity A =
      ∫ z, A.indicator (fun _ => (1 : ℝ)) z ∂μ := by
    rw [MeasureTheory.integral_indicator hA]
    simp [μ, periodicDensity, lebesgueMeasure, MeasureTheory.integral_const,
      MeasureTheory.Measure.real, MeasureTheory.Measure.restrict_apply hA]
  have hswap : D.E (fun ω => periodicDensity (exceptionalCenters hM hp ω)) =
      ∫ z, D.Pr (fun ω => z ∈ exceptionalCenters hM hp ω) ∂μ := by
    simp only [FiniteDesign.Pr, FiniteDesign.E, hden _ (hmeas _),
      ← MeasureTheory.integral_const_mul]
    rw [MeasureTheory.integral_finsetSum]
    · rfl
    · intro ω _
      exact (hint ω).const_mul _
  have hintPr : MeasureTheory.Integrable
      (fun z => D.Pr (fun ω => z ∈ exceptionalCenters hM hp ω)) μ := by
    first | fun_prop | skip
    change MeasureTheory.Integrable (fun z => ∑ ω, D.p ω *
      FiniteDesign.ind (fun ω => z ∈ exceptionalCenters hM hp ω) ω) μ
    apply MeasureTheory.integrable_finsetSum
    intro ω _
    change MeasureTheory.Integrable (fun z => D.p ω *
      (exceptionalCenters hM hp ω).indicator (fun _ => (1 : ℝ)) z) μ
    exact (hint ω).const_mul _
  have hbound (z : ℝ) : D.Pr (fun ω => z ∈ exceptionalCenters hM hp ω) ≤
      Sᶜ.indicator (fun _ => (1 : ℝ)) z + 2 * p := by
    by_cases hz : z ∈ S
    · have hb := pr_exceptionalCenters_le_of_stable hq hM hd hg hr hn0 hn0q hp
        hdecay z (show IsStableCenter q M d g r0 n0 z from hz).stable
      simpa [S, Set.indicator, hz, Set.mem_compl_iff] using
        hb.trans (by linarith : (1 - (2 : ℝ) ^ (1 - (M : ℤ))) ^ d + p ≤ 2 * p)
    · have hb : D.Pr (fun ω => z ∈ exceptionalCenters hM hp ω) ≤ 1 := by
        have := D.Pr_mono (fun ω => z ∈ exceptionalCenters hM hp ω) (fun _ => True)
          (fun _ _ => trivial)
        have htrue : D.Pr (fun _ => True) = 1 := by
          change D.E (fun _ => (1 : ℝ)) = 1
          exact D.E_const 1
        rwa [htrue] at this
      simpa [Set.indicator, hz] using hb.trans (by linarith [hp.1] : (1 : ℝ) ≤ 1 + 2 * p)
  calc
    D.E (fun ω => periodicDensity (exceptionalCenters hM hp ω)) =
        ∫ z, D.Pr (fun ω => z ∈ exceptionalCenters hM hp ω) ∂μ := hswap
    _ ≤ ∫ z, Sᶜ.indicator (fun _ => (1 : ℝ)) z + 2 * p ∂μ :=
      MeasureTheory.integral_mono hintPr
        (((MeasureTheory.integrable_const (1 : ℝ)).indicator hS.compl).add
          (MeasureTheory.integrable_const _)) hbound
    _ = periodicDensity Sᶜ + 2 * p := by
      rw [MeasureTheory.integral_add
        ((MeasureTheory.integrable_const (1 : ℝ)).indicator hS.compl)
        (MeasureTheory.integrable_const _), ← hden _ hS.compl]
      simp [μ]
    _ ≤ 3 * p := by
      have hb := stableSet_compl_density_le (M := M) (d := d) q g r0 hq hr hn0
      change periodicDensity Sᶜ ≤ _ at hb
      linarith

-- @node: exists_outcome_le_design_mean
/-- For [a probability design D on a nonempty finite outcome space](hyp:D) and
[a real-valued statistic X](hyp:X), [some outcome has a value of X no larger
than its expectation under D](goal). -/
lemma exists_outcome_le_design_mean {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (D : FiniteDesign Ω) (X : Ω → ℝ) : ∃ ω, X ω ≤ D.E X := by
  classical
  obtain ⟨ω, _, hmin⟩ := Finset.exists_min_image Finset.univ X Finset.univ_nonempty
  refine ⟨ω, ?_⟩
  calc
    X ω = D.E (fun _ => X ω) := (D.E_const _).symm
    _ ≤ D.E X := Finset.sum_le_sum (fun z _ =>
      mul_le_mul_of_nonneg_left (hmin z (Finset.mem_univ z)) (D.p_nonneg z))

-- @node: exists_good_outcome
/-- Suppose [0 < q < 1](hyp:hq), [M ≥ 2](hyp:hM), [d ≥ 1](hyp:hd),
[g ≥ 1](hyp:hg), [r0 ≥ 1](hyp:hr), [n0 ≥ 1](hyp:hn0),
[twice q to the power n0 is at most 1/4](hyp:hn0q), and [0 < p < 1](hyp:hp).
If [four times the edge count times the grid constant times q to the power
g + 1 is less than p](hyp:hgap), [(1 − 2 to the power 1 − M) to the power d
is less than p](hyp:hdepth), and [the scale-count bound times
exp(−p(M − 1)r/2) is less than p for every r ≥ r0](hyp:hdecay),
[there is a random-table outcome for which the sum of the periodic densities
of the enlarged random set and the exceptional centers is at most 5p](goal). -/
lemma exists_good_outcome (hq : QDomain q) (hM : BranchingDomain M)
    (hd : DepthDomain d) (hg : GapDomain g) (hr : BaseLengthDomain r0)
    (hn0 : 1 ≤ n0) -- @realizes n_0(positive starting index)
    (hn0q : 2 * q ^ n0 ≤ 1 / 4) -- @realizes n_0(smallness at the supplied index)
    (hp : TerminalProbabilityDomain p)
    (hgap : 4 * edgeCount M d * gridConst q * q ^ (g + 1) < p)
    (hdepth : (1 - (2 : ℝ) ^ (1 - (M : ℤ))) ^ d < p)
    (hdecay : ∀ r : ℕ, r0 ≤ r →
      scaleCount M q r * Real.exp (-(p * ((M : ℝ) - 1) * r / 2)) < p) :
    ∃ ω : Outcome q M d g r0 n0, periodicDensity (enlargedRandomSet hM hp ω) +
      periodicDensity (exceptionalCenters hM hp ω) ≤ 5 * p := by
  let D := tableLaw q M d g r0 n0 p
  have hrandom := expected_periodicDensity_randomSet_eq (n0 := n0) hq hM hd hg hr hp
  have hexception := expected_exceptional_density_le hq hM hd hg hr hn0 hn0q hp
    hgap hdepth hdecay
  have henlarge : D.E (fun ω => periodicDensity (enlargedRandomSet hM hp ω)) ≤ 2 * p := by
    calc
      _ ≤ D.E (fun ω => periodicDensity (randomSet hM ω) + p) :=
        Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left
          (enlargedRandomSet_spec hM hp ω).2.2.2 (D.p_nonneg ω))
      _ = 2 * p := by rw [D.E_add, D.E_const, hrandom]; ring
  obtain ⟨ω, hω⟩ := exists_outcome_le_design_mean D
    (fun ω => periodicDensity (enlargedRandomSet hM hp ω) +
      periodicDensity (exceptionalCenters hM hp ω))
  refine ⟨ω, hω.trans ?_⟩
  rw [D.E_add]
  exact (add_le_add henlarge hexception).trans (by ring_nf; rfl)

-- @node: eventually_localPoint_mem_of_isOpen
/-- If [0 < q < 1](hyp:hq), [V is open](hyp:hV), and [x belongs to V](hyp:hx),
then for any real scale t, [x + t qⁿ belongs to V for every sufficiently large
natural index n](goal). -/
lemma eventually_localPoint_mem_of_isOpen (hq : QDomain q) {V : Set ℝ}
    (hV : IsOpen V) {x : ℝ} (hx : x ∈ V) (t : ℝ) :
    ∀ᶠ n : ℕ in Filter.atTop, localPoint x t q n ∈ V := by
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hq.1.le hq.2
  have hlim : Filter.Tendsto (fun n : ℕ => localPoint x t q n)
      Filter.atTop (nhds x) := by
    simpa only [localPoint, mul_zero, add_zero] using
      (tendsto_const_nhds.add (tendsto_const_nhds.mul hpow))
  exact hlim.eventually (hV.mem_nhds hx)

-- @node: repairedSet_hits
/-- Given [0 < q < 1](hyp:hq), [M ≥ 2](hyp:hM), [d ≥ 1](hyp:hd),
[g ≥ 1](hyp:hg), [r0 ≥ 1](hyp:hr), [n0 ≥ 1](hyp:hn0), [0 < p < 1](hyp:hp),
and [a random-table outcome ω](hyp:ω), [for every real center x and every scale
t between one and two, inclusive, some positive integer n makes x + t qⁿ
belong to the union of the enlarged random set and the open repair set](goal). -/
lemma repairedSet_hits (hq : QDomain q) (hM : BranchingDomain M)
    (hd : DepthDomain d) (hg : GapDomain g) (hr : BaseLengthDomain r0)
    (hn0 : 1 ≤ n0) -- @realizes n_0(positive starting index)
    (hp : TerminalProbabilityDomain p) (ω : Outcome q M d g r0 n0) :
    ∀ x t : ℝ, t ∈ Set.Icc (1 : ℝ) 2 → ∃ n : ℕ, 1 ≤ n ∧
      localPoint x t q n ∈ enlargedRandomSet hM hp ω ∪ openRepairSet hM hp ω := by
  intro x t ht
  by_cases hx : x ∈ exceptionalCenters hM hp ω
  · have hV := openRepairSet_spec hM hp ω
    have hev := eventually_localPoint_mem_of_isOpen hq hV.1 (hV.2.2.1 hx) t
    obtain ⟨n, hn, hhit⟩ := (Filter.eventually_ge_atTop 1 |>.and hev).exists
    exact ⟨n, hn, Set.mem_union_right _ hhit⟩
  · have hhit : ∃ n ∈ indexSet q M d g r0 n0,
        localPoint x t q n ∈ enlargedRandomSet hM hp ω := by
      by_contra hnone
      apply hx
      refine ⟨t, ht, ?_⟩
      intro n hn hmem
      exact hnone ⟨n, hn, hmem⟩
    obtain ⟨n, hn, hmem⟩ := hhit
    obtain ⟨e, he, hne⟩ := Finset.mem_biUnion.mp hn
    exact ⟨n, windowSet_positive q g r0 hq hM hd hg hr hn0 e n hne,
      Set.mem_union_left _ hmem⟩

-- @node: periodicDensity_union_le
/-- For [real sets A and B](hyp:A,B), [the periodic density of their union is
at most the sum of their periodic densities](goal). -/
lemma periodicDensity_union_le (A B : Set ℝ) :
    periodicDensity (A ∪ B) ≤ periodicDensity A + periodicDensity B := by
  simpa only [periodicDensity, Set.union_inter_distrib_right, MeasureTheory.measureReal_def] using
    (MeasureTheory.measureReal_union_le (μ := lebesgueMeasure)
      (A ∩ Set.Ico (0 : ℝ) 1) (B ∩ Set.Ico (0 : ℝ) 1))

-- @node: prop:periodic
/-- If [0 < q < 1](hyp:hq) and [0 < p < 1](hyp:hp), [there is an open real set H
invariant under translation by one, with periodic density at most 6p, such that
for every real center x and every scale t between one and two, inclusive,
some positive integer n makes x + t qⁿ belong to H](goal). -/
theorem exists_open_periodic_hitting_set (q : ℝ) (hq : QDomain q)
    (p : ℝ) (hp : TerminalProbabilityDomain p) :
    ∃ H : Set ℝ, IsOpen H ∧ IsOnePeriodic H ∧
      periodicDensity H ≤ 6 * p ∧ -- @realizes H(open periodic set; density at most 6p)
      ∀ x t : ℝ, t ∈ Set.Icc (1 : ℝ) 2 → ∃ n : ℕ, 1 ≤ n ∧ x + t * q ^ n ∈ H := by
  let n0 := firstIndex q -- @realizes n_0(internal admissible witness)
  have hn0 : 1 ≤ n0 := (firstIndex_spec q hq).1 -- @realizes n_0(positive witness)
  have hn0q : 2 * q ^ n0 ≤ 1 / 4 := (firstIndex_spec q hq).2
    -- @realizes n_0(witness satisfies smallness)
  obtain ⟨M, hM, hα, d, hd, hdepth, rstar, hr, hdecay, g, hg, hgap⟩ :=
    construction_parameters_exist hq hp
  obtain ⟨ω, hω⟩ := exists_good_outcome hq hM hd hg hr hn0 hn0q hp hgap hdepth hdecay
  have hB := enlargedRandomSet_spec hM hp ω
  have hV := openRepairSet_spec hM hp ω
  refine ⟨enlargedRandomSet hM hp ω ∪ openRepairSet hM hp ω,
    hB.1.union hV.1, ?_, ?_, ?_⟩
  · intro x
    exact or_congr (hB.2.1 x) (hV.2.1 x)
  · have hρ := periodicDensity_union_le (enlargedRandomSet hM hp ω) (openRepairSet hM hp ω)
    linarith [hV.2.2.2]
  · exact repairedSet_hits hq hM hd hg hr hn0 hp ω

end Papers.OaiGeometricErdosSimilarity

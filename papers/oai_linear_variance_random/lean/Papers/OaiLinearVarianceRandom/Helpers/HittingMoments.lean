module

public import Papers.OaiLinearVarianceRandom.Helpers.HiddenClauses
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Finite moments of the satisfiability hitting time

Avoidance of one falsifying clause for each assignment gives a geometric tail.
This supplies square integrability before using the quartile variance argument.
-/

public section

namespace Papers.OaiLinearVarianceRandom
open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {n : ℕ} {Ω : Type} [MeasurableSpace Ω]

/-- If [the prefix length is less than the first unsatisfiable time](hyp:hm),
then [that prefix is satisfiable](goal). -/
-- @node: prefixSat_of_lt_hittingTime
lemma prefixSat_of_lt_hittingTime (c : ℕ → ProperClause n) (m : ℕ)
    (hm : m < hittingTime c) : PrefixSat c m := by
  classical
  by_cases h : ∃ k, 1 ≤ k ∧ ¬ PrefixSat c k
  · by_contra hs
    have hmpos : 1 ≤ m := by
      by_contra hz
      have : m = 0 := by omega
      subst m
      exact hs ⟨fun _ => false, by simp⟩
    have hle := Nat.sInf_le (s := {k | 1 ≤ k ∧ ¬ PrefixSat c k}) ⟨hmpos, hs⟩
    rw [hittingTime, if_pos h] at hm
    exact (not_le_of_gt hm) hle
  · by_cases hmpos : 1 ≤ m
    · exact not_not.mp (fun hs => h ⟨m, hmpos, hs⟩)
    · have : m = 0 := by omega
      subst m
      exact ⟨fun _ => false, by simp⟩

/-- With [at least three variables](hyp:hn) and [an independent uniform clause
process](hyp:hlaw), [there is a nonnegative ratio strictly below one such that,
at every nonnegative integer time, the probability that the first unsatisfiable
time is later is at most two to the number of variables times that ratio to the
given time](goal). -/
-- @node: hittingTime_geometric_tail
lemma hittingTime_geometric_tail (hn : MainN n)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Cseq : ℕ → Ω → ProperClause n) (hlaw : IsUniformClauseProcess μ Cseq) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ m : ℕ,
      μ.real {ω | m < hittingTime (fun j => Cseq j ω)} ≤ (2 : ℝ) ^ n * r ^ m := by
  classical
  letI : Nonempty (ProperClause n) := properClauseA_nonempty n 3 hn
  let c0 : ProperClause n := Classical.choice inferInstance
  let ν := uniformClauseMeasure n 3
  haveI : IsProbabilityMeasure ν := by dsimp [ν, uniformClauseMeasure]; infer_instance
  let p : ℝ := (Fintype.card (ProperClause n) : ℝ)⁻¹
  have hp : 0 < p := by dsimp [p]; positivity
  have hsingle (c : ProperClause n) : ν.real {c} = p := by
    simp [ν, p, uniformClauseMeasure, measureReal_def, uniformOn_univ,
      Measure.count_singleton]
  have hp1 : p ≤ 1 := by
    rw [← hsingle c0]
    simpa using (measureReal_mono (μ := ν) (Set.subset_univ {c0}))
  refine ⟨1 - p, sub_nonneg.mpr hp1, by linarith, ?_⟩
  intro m
  let bad : (Fin n → Bool) → ProperClause n := fun z =>
    properClauseOfSigns ⟨clauseVars c0, c0.property.2⟩ (fun v => !(z v.val))
  have hbad (z : Fin n → Bool) : ¬ ClauseSat (bad z) z := by
    rintro ⟨l, hl, hs⟩
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hl
    have he : z v.val = !(z v.val) := hs
    cases hz : z v.val <;> simp [hz] at he
  let E : (Fin n → Bool) → Set Ω := fun z =>
    {ω | ∀ j : Fin m, Cseq (j.val + 1) ω ≠ bad z}
  have hmass (z : Fin n → Bool) : μ.real (E z) = (1 - p) ^ m := by
    have h := clauseProcess_joint_mass μ Cseq hlaw
      (fun j : Fin m => j.val + 1) (by intro a b h; apply Fin.ext; exact Nat.add_right_cancel h)
      (fun _ => by omega) (fun _ => ({bad z} : Set (ProperClause n))ᶜ)
    have hs : ν.real ({bad z}ᶜ) = 1 - p := by
      rw [measureReal_compl (by trivial), hsingle]
      simp
    change (μ (E z)).toReal = _
    rw [show μ (E z) = ∏ _j : Fin m, ν ({bad z}ᶜ) by simpa [E, ν] using h,
      ENNReal.toReal_prod]
    simp only [← measureReal_def, hs, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hsub : {ω | m < hittingTime (fun j => Cseq j ω)} ⊆ ⋃ z, E z := by
    intro ω hω
    obtain ⟨z, hz⟩ := prefixSat_of_lt_hittingTime _ m hω
    refine Set.mem_iUnion.mpr ⟨z, ?_⟩
    intro j heq
    exact hbad z (heq ▸ hz (j.val + 1) (Finset.mem_Icc.mpr ⟨by omega, j.isLt⟩))
  calc
    _ ≤ μ.real (⋃ z, E z) := measureReal_mono hsub
    _ ≤ ∑ z : Fin n → Bool, μ.real (E z) := measureReal_iUnion_fintype_le _
    _ = _ := by simp [hmass, Fintype.card_fun, Fintype.card_fin]

/-- With [at least three variables](hyp:hn) and [an independent uniform clause
process](hyp:hlaw), [every nonnegative integer power of the first unsatisfiable
time is integrable](goal). -/
-- @node: hittingTime_integrable_pow
lemma hittingTime_integrable_pow (hn : MainN n)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Cseq : ℕ → Ω → ProperClause n) (hlaw : IsUniformClauseProcess μ Cseq) (q : ℕ) :
    Integrable (fun ω => (hittingTime (fun j => Cseq j ω) : ℝ) ^ q) μ := by
  classical
  let H := fun ω => hittingTime (fun j => Cseq j ω)
  have hH : Measurable H := measurable_hittingTime Cseq hlaw.1
  obtain ⟨r, hr0, hr1, htail⟩ := hittingTime_geometric_tail hn μ Cseq hlaw
  let S : ℕ → Set Ω := fun k => {ω | H ω = k}
  have hS (k : ℕ) : MeasurableSet (S k) := hH (measurableSet_singleton k)
  have hi (k : ℕ) : IntegrableOn (fun ω => (H ω : ℝ) ^ q) (S k) μ := by
    apply (integrableOn_const (C := (k : ℝ) ^ q)).congr
    filter_upwards [ae_restrict_mem (hS k)] with ω hω
    rw [show H ω = k from hω]
  have heq (k : ℕ) : (∫ ω in S k, ‖(H ω : ℝ) ^ q‖ ∂μ) =
      μ.real (S k) * (k : ℝ) ^ q := by
    rw [show (∫ ω in S k, ‖(H ω : ℝ) ^ q‖ ∂μ) =
      ∫ _ω in S k, (k : ℝ) ^ q ∂μ by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem (hS k)] with ω hω
        rw [show H ω = k from hω, Real.norm_eq_abs, abs_of_nonneg (by positivity)],
      setIntegral_const, smul_eq_mul]
  have hgeom : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ q * r ^ k) := by
    have hg := summable_pow_mul_geometric_of_norm_lt_one q
      (by rwa [Real.norm_eq_abs, abs_of_nonneg hr0] : ‖r‖ < 1)
    -- A shifted polynomial still has a summable geometric envelope.
    by_cases hr : r = 0
    · subst r
      rw [← summable_nat_add_iff 1]
      simp
    · have h := ((summable_nat_add_iff 1).2 hg).mul_right r⁻¹
      apply h.congr
      intro k
      rw [pow_succ]
      field_simp
  have hsum : Summable (fun k => ∫ ω in S k, ‖(H ω : ℝ) ^ q‖ ∂μ) := by
    rw [← summable_nat_add_iff 1]
    apply Summable.of_nonneg_of_le (fun k => integral_nonneg (fun _ => norm_nonneg _))
      (fun k => ?_) (hgeom.mul_left ((2 : ℝ) ^ n))
    rw [heq]
    have hb : μ.real (S (k + 1)) ≤ (2 : ℝ) ^ n * r ^ k :=
      (measureReal_mono (fun ω hω => by change k < H ω; rw [hω]; omega)).trans (htail k)
    calc
      _ ≤ ((2 : ℝ) ^ n * r ^ k) * ((k + 1 : ℕ) : ℝ) ^ q :=
        mul_le_mul_of_nonneg_right hb (by positivity)
      _ = _ := by ring
  have hu : (⋃ k, S k) = Set.univ := by ext ω; simp [S]
  simpa only [hu, integrableOn_univ] using
    integrableOn_iUnion_of_summable_integral_norm hi hsum

/-- With [at least three variables](hyp:hn) and [an independent uniform clause
process](hyp:hlaw), [the first unsatisfiable time is square integrable](goal). -/
-- @node: hittingTime_memLp_two
lemma hittingTime_memLp_two (hn : MainN n)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Cseq : ℕ → Ω → ProperClause n) (hlaw : IsUniformClauseProcess μ Cseq) :
    MemLp (fun ω => (hittingTime (fun j => Cseq j ω) : ℝ)) 2 μ := by
  have hm : Measurable (fun ω => (hittingTime (fun j => Cseq j ω) : ℝ)) :=
    (measurable_of_countable (fun k : ℕ => (k : ℝ))).comp
      (measurable_hittingTime Cseq hlaw.1)
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
  exact hittingTime_integrable_pow hn μ Cseq hlaw 2

/-- If [a real random variable is square integrable](hyp:hX), [the lower
threshold is no greater than the upper threshold](hyp:hab), [the probability of
being at or below the lower threshold is at least one quarter](hyp:ha), and [the
probability of being at or above the upper threshold is at least one
quarter](hyp:hb), then [its variance is at least one sixteenth of the squared
distance between the thresholds](goal). -/
-- @node: variance_lower_of_quarter_events
lemma variance_lower_of_quarter_events
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hX : MemLp X 2 μ) (a b : ℝ) (hab : a ≤ b)
    (ha : (1 / 4 : ℝ) ≤ μ.real {ω | X ω ≤ a})
    (hb : (1 / 4 : ℝ) ≤ μ.real {ω | b ≤ X ω}) :
    (b - a) ^ 2 / 16 ≤ variance X μ := by
  by_cases heq : a = b
  · simpa only [heq, sub_self, zero_pow (by omega : 2 ≠ 0), zero_div] using
      (variance_nonneg X μ)
  have hablt : a < b := lt_of_le_of_ne hab heq
  have hc : 0 < (b - a) / 2 := by linarith
  have hcheb : μ.real {ω | (b - a) / 2 ≤ |X ω - ∫ x, X x ∂μ|} ≤
      variance X μ / ((b - a) / 2) ^ 2 := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (meas_ge_le_variance_div_sq hX hc)
    simpa only [ENNReal.toReal_ofReal
      (div_nonneg (variance_nonneg X μ) (sq_nonneg _)), ← measureReal_def] using h
  have hmass : (1 / 4 : ℝ) ≤
      μ.real {ω | (b - a) / 2 ≤ |X ω - ∫ x, X x ∂μ|} := by
    by_cases hm : (∫ x, X x ∂μ) ≤ (a + b) / 2
    · apply hb.trans (measureReal_mono ?_)
      intro ω hω
      change b ≤ X ω at hω
      exact (by linarith : (b - a) / 2 ≤ X ω - ∫ x, X x ∂μ).trans (le_abs_self _)
    · apply ha.trans (measureReal_mono ?_)
      intro ω hω
      change X ω ≤ a at hω
      exact (by linarith : (b - a) / 2 ≤ -(X ω - ∫ x, X x ∂μ)).trans (neg_le_abs _)
  have h := (le_div_iff₀ (sq_pos_of_pos hc)).mp (hmass.trans hcheb)
  nlinarith

end Papers.OaiLinearVarianceRandom

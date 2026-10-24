module

public import Papers.OaiLinearVarianceRandom.Helpers.OrdinaryClauses
public import Papers.OaiLinearVarianceRandom.Helpers.RefinedHiddenClauses
public import Papers.OaiLinearVarianceRandom.Helpers.OccupationMeasure

/-! # Conditional potential drift at an ordinary step

The conditional next-clause law and the finite ordinary-clause average give
the one-step occupation inequality with the random current solution set.
-/

public section

noncomputable section
namespace Papers.OaiLinearVarianceRandom
open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {n : ℕ} {Ω : Type} [MeasurableSpace Ω]

open Classical in
-- @node: occupation_ordinary_conditional_drift
/-- If [there are at least six variables](hyp:hn), [the positive-index clauses
are measurable, independent, and uniformly distributed](hyp:hlaw), [the
omitted index lies between one and the cap](hyp:hi), and [the current time
is at least that index and strictly below the cap](hyp:hs), then [conditional
on the omitted clause being the fixed root clause, almost surely whenever
the next clause is ordinary, the current occupation term is at most three
times the square root of the incidence parameter times the conditional
expected next potential increase given the current test filtration, plus
the three-halves power of that parameter divided by the cube of the nonroot
count](goal). -/
lemma occupation_ordinary_conditional_drift (hn : OmissionN n)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Cseq : ℕ → Ω → ProperClause n) (hlaw : IsUniformClauseProcess μ Cseq)
    (i : ℕ) (hi : DelayIndex i (capL n)) (c0 : ProperClause n)
    (s : ℕ) (hs : i ≤ s ∧ s < capL n) :
    ∀ᵐ ω ∂(fixedClauseMeasure μ Cseq i c0),
      isOrdinary c0 (Cseq (s + 1) ω) →
      occupationTerm c0 Cseq i s ω ≤
        3 * (incidenceParam c0 Cseq i ω : ℝ) ^ (beta - 1) *
          ((fixedClauseMeasure μ Cseq i c0)[(fun ω' =>
            potential (incidenceParam c0 Cseq i ω') (nonrootSolutions c0 Cseq i (s + 1) ω') -
              potential (incidenceParam c0 Cseq i ω') (nonrootSolutions c0 Cseq i s ω')) |
            testFiltration c0 Cseq i s]) ω +
        (incidenceParam c0 Cseq i ω : ℝ) ^ beta *
          (nonrootCount n : ℝ) ^ (-3 : ℝ) := by
  let ν := fixedClauseMeasure μ Cseq i c0
  have : IsProbabilityMeasure ν :=
    fixedClauseMeasure_isProbabilityMeasure μ Cseq hlaw i hi.1 c0
  let F : ProperClause n → Ω → ℝ := fun c ω =>
    potential (incidenceParam c0 Cseq i ω)
      ((nonrootSolutions c0 Cseq i s ω).filter
        (fun z => ClauseSat c (glueAssignment c0 z))) -
      potential (incidenceParam c0 Cseq i ω) (nonrootSolutions c0 Cseq i s ω)
  have hF (c : ProperClause n) :
      StronglyMeasurable[testFiltration c0 Cseq i s] (F c) := by
    let : MeasurableSpace Ω := testFiltration c0 Cseq i s
    have hd : Measurable (incidenceParam c0 Cseq i) :=
      (incidenceParam_measurable c0 Cseq i).mono (le_sup_left.trans le_sup_left) le_rfl
    have hS : Measurable (nonrootSolutions c0 Cseq i s) :=
      (nonrootSolutions_measurable c0 Cseq i s ⟨hs.1, hs.2.le⟩).mono le_sup_left le_top
    have hf : Measurable (fun p : ℕ × Finset (Fin (nonrootCount n) → Bool) =>
        potential p.1 (p.2.filter (fun z => ClauseSat c (glueAssignment c0 z))) -
          potential p.1 p.2) := by fun_prop
    exact (hf.comp (hd.prodMk hS)).stronglyMeasurable
  have hFint (c : ProperClause n) : Integrable (F c) ν := by
    apply Integrable.of_bound
      ((hF c).mono (testFiltration_le c0 Cseq hlaw.1 i s)).aestronglyMeasurable
      (capL n : ℝ)
    filter_upwards [] with ω
    have hb := potential_bounds (incidenceParam c0 Cseq i ω)
      (nonrootSolutions c0 Cseq i s ω)
    have ha := potential_bounds (incidenceParam c0 Cseq i ω)
      ((nonrootSolutions c0 Cseq i s ω).filter
        (fun z => ClauseSat c (glueAssignment c0 z)))
    have hd : (incidenceParam c0 Cseq i ω : ℝ) ≤ capL n := by
      exact_mod_cast (show incidenceParam c0 Cseq i ω ≤ capL n from
        max_le (hi.1.trans hi.2)
          ((exposure_counts_range c0 Cseq i hi ω).1.trans (Nat.sub_le _ _)))
    rw [Real.norm_eq_abs, abs_le]
    dsimp [F]
    constructor <;> linarith
  have heq : (fun ω => F (Cseq (s + 1) ω) ω) = (fun ω =>
      potential (incidenceParam c0 Cseq i ω) (nonrootSolutions c0 Cseq i (s + 1) ω) -
        potential (incidenceParam c0 Cseq i ω) (nonrootSolutions c0 Cseq i s ω)) := by
    funext ω
    dsimp [F]
    rw [nonrootSolutions_succ c0 Cseq i s hs.1 ω]
  have hce := ordinary_next_clause_condExp μ Cseq hlaw i hi.1 c0 s hs F hF hFint
  rw [heq] at hce
  filter_upwards [hce] with ω hω
  intro ho
  rw [hω ho]
  exact occupation_ordinary_drift_average hn c0 (incidenceParam c0 Cseq i ω)
    (le_max_left _ _) (nonrootSolutions c0 Cseq i s ω)

end Papers.OaiLinearVarianceRandom

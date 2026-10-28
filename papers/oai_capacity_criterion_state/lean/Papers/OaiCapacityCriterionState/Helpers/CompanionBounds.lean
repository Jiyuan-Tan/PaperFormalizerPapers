module

public import Papers.OaiCapacityCriterionState.Helpers.CitedGates
public import Papers.OaiCapacityCriterionState.Helpers.LocalMoments

/-! # Cubic information saving from the companion inequality

The fourth moment dominates the square of quadratic information. Consequently,
the companion class has a cubic saving when two experiments are combined.
All probability and integrability conditions follow from the posterior laws.
-/

public section

open MeasureTheory

namespace OaiCapacityCriterionState

-- @node: quadInfo_sq_le_fourthMoment
/-- [For any posterior law, the square of its quadratic information is at most the
expected square of the quadratic posterior statistic, its fourth moment](goal). -/
lemma quadInfo_sq_le_fourthMoment (mu : PosteriorLaw) :
    quadInfo mu ^ 2 ≤ ∫ p, quadStat p ^ 2 ∂(mu : Measure (Fin 4 → ℝ)) := by
  unfold PosteriorLaw at mu
  let : IsProbabilityMeasure (mu : Measure (Fin 4 → ℝ)) := mu.property.1
  have hi := quadStat_integrable mu
  have hi2 : Integrable (fun p => quadStat p ^ 2) (mu : Measure (Fin 4 → ℝ)) := by
    apply posterior_continuous_integrable
    first | fun_prop | unfold quadStat postCoords Matrix.mulVec dotProduct; fun_prop
  have hmul : Integrable (fun p => (2 * quadInfo mu) * quadStat p)
      (mu : Measure (Fin 4 → ℝ)) := hi.const_mul _
  have hcenter :
      (∫ p, (quadStat p - quadInfo mu) ^ 2 ∂(mu : Measure (Fin 4 → ℝ))) =
        (∫ p, quadStat p ^ 2 ∂(mu : Measure (Fin 4 → ℝ))) - quadInfo mu ^ 2 := by
    calc
      _ = ∫ p, (quadStat p ^ 2 - (2 * quadInfo mu) * quadStat p) + quadInfo mu ^ 2
          ∂(mu : Measure (Fin 4 → ℝ)) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun p => by ring
      _ = _ := by
        have hadd := integral_add (hi2.sub hmul) (integrable_const (quadInfo mu ^ 2))
        simp only [Pi.sub_apply] at hadd
        rw [hadd, integral_sub hi2 hmul, integral_const_mul]
        simp only [integral_const, probReal_univ, one_smul]
        change _ - (2 * quadInfo mu) * quadInfo mu + quadInfo mu ^ 2 = _
        ring
  have hnonneg : 0 ≤ ∫ p, (quadStat p - quadInfo mu) ^ 2
      ∂(mu : Measure (Fin 4 → ℝ)) := integral_nonneg fun p => sq_nonneg _
  rw [hcenter] at hnonneg
  exact sub_nonneg.mp hnonneg

-- @node: quadInfo_cubic_saving_of_fourthMoment_saving
/-- If [combining two posterior laws gives quadratic information at most their summed
information minus one thousandth of the sum of each law's fourth moment times the other's
quadratic information](hyp:hsave), then [the combined information is at most their sum
minus one thousandth of the product of their quadratic informations and their sum](goal). -/
lemma quadInfo_cubic_saving_of_fourthMoment_saving (mu nu : PosteriorLaw)
    (hsave : quadInfo (starLaw mu nu) ≤ quadInfo mu + quadInfo nu -
      (1 / 1000 : ℝ) *
        ((∫ p, quadStat p ^ 2 ∂(mu : Measure (Fin 4 → ℝ))) * quadInfo nu +
          quadInfo mu * ∫ p, quadStat p ^ 2 ∂(nu : Measure (Fin 4 → ℝ)))) :
    quadInfo (starLaw mu nu) ≤ quadInfo mu + quadInfo nu -
      (1 / 1000 : ℝ) * quadInfo mu * quadInfo nu * (quadInfo mu + quadInfo nu) := by
  have hmu := mul_le_mul_of_nonneg_right (quadInfo_sq_le_fourthMoment mu)
    (quadInfo_mem_Icc nu).1
  have hnu := mul_le_mul_of_nonneg_left (quadInfo_sq_le_fourthMoment nu)
    (quadInfo_mem_Icc mu).1
  refine hsave.trans ?_
  nlinarith [hmu, hnu]

-- @node: quadInfo_transform_subadditive_of_cubic_saving
/-- If [the quadratic information from combining two posterior laws is at most their
summed information minus one thousandth of the product of their informations and their
sum](hyp:hsave), then [the combined information plus its cube divided by 3000 is at most
the sum of the two individual informations, each augmented by its cube divided by 3000](goal). -/
lemma quadInfo_transform_subadditive_of_cubic_saving (mu nu : PosteriorLaw)
    (hsave : quadInfo (starLaw mu nu) ≤ quadInfo mu + quadInfo nu -
      (1 / 1000 : ℝ) * quadInfo mu * quadInfo nu * (quadInfo mu + quadInfo nu)) :
    quadInfo (starLaw mu nu) + quadInfo (starLaw mu nu) ^ 3 / 3000 ≤
      (quadInfo mu + quadInfo mu ^ 3 / 3000) +
        (quadInfo nu + quadInfo nu ^ 3 / 3000) := by
  have hmu := (quadInfo_mem_Icc mu).1
  have hnu := (quadInfo_mem_Icc nu).1
  have hstar := (quadInfo_mem_Icc
    ⟨starLaw mu nu, starLaw_isPosteriorLaw mu nu mu.property nu.property⟩).1
  have hsaving : 0 ≤ (1 / 1000 : ℝ) * quadInfo mu * quadInfo nu *
      (quadInfo mu + quadInfo nu) := by positivity
  have hsum : quadInfo (starLaw mu nu) ≤ quadInfo mu + quadInfo nu :=
    hsave.trans (sub_le_self _ hsaving)
  have hcube := pow_le_pow_left₀ hstar hsum 3
  calc
    _ ≤ (quadInfo mu + quadInfo nu -
        (1 / 1000 : ℝ) * quadInfo mu * quadInfo nu * (quadInfo mu + quadInfo nu)) +
        (quadInfo mu + quadInfo nu) ^ 3 / 3000 :=
      add_le_add hsave (div_le_div_of_nonneg_right hcube (by norm_num))
    _ = _ := by ring

-- @node: companion_class_cubic_saving
/-- Assuming [the companion moment-saving proposition](hyp:hCompanion), [there exists
a class of symmetric posterior laws containing both the revealing and uninformative laws,
closed under channel updates with parameters between zero and one inclusive and under combining
conditionally independent experiments, such that combining any two members reduces the
sum of their quadratic informations by at least one thousandth of their product times
their sum, and information augmented by its cube divided by 3000 is subadditive under
this combination](goal). -/
lemma companion_class_cubic_saving (hCompanion : CompanionMomentSaving) :
    ∃ C : Set (Measure (Fin 4 → ℝ)),
      (∀ mu ∈ C, IsPosteriorLaw mu ∧ IsSymmetricLaw mu) ∧
      revealingLaw ∈ C ∧ uninformativeLaw ∈ C ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ mu ∈ C, channelStep t mu ∈ C) ∧
      (∀ mu ∈ C, ∀ nu ∈ C, starLaw mu nu ∈ C) ∧
      ∀ mu ∈ C, ∀ nu ∈ C,
        (quadInfo (starLaw mu nu) ≤ quadInfo mu + quadInfo nu -
          (1 / 1000 : ℝ) * quadInfo mu * quadInfo nu * (quadInfo mu + quadInfo nu)) ∧
        quadInfo (starLaw mu nu) + quadInfo (starLaw mu nu) ^ 3 / 3000 ≤
          (quadInfo mu + quadInfo mu ^ 3 / 3000) +
            (quadInfo nu + quadInfo nu ^ 3 / 3000) := by
  obtain ⟨C, hC, hrevealing, huninformative, hchannel, hstar, hsave⟩ := hCompanion
  refine ⟨C, hC, hrevealing, huninformative, hchannel, hstar, ?_⟩
  intro mu hmu nu hnu
  let mu' : PosteriorLaw := ⟨mu, (hC mu hmu).1⟩
  let nu' : PosteriorLaw := ⟨nu, (hC nu hnu).1⟩
  have hcubic := quadInfo_cubic_saving_of_fourthMoment_saving mu' nu' (hsave mu hmu nu hnu)
  exact ⟨hcubic, quadInfo_transform_subadditive_of_cubic_saving mu' nu' hcubic⟩

end OaiCapacityCriterionState

module
public import Papers.TbsNeuralCausalPi.TLipAte
public import Papers.TbsNeuralCausalPi.Helpers.RateChangeMeasure
public import Papers.TbsNeuralCausalPi.Helpers.InterventionalUniformMoments
public import Papers.TbsNeuralCausalPi.Helpers.CanonicalConditionalPropensity
/-! # Integrated causal-effect error under the intervention law

The reference-law square estimate is transferred using the actual density.
Square integrability of the causal means is derived from finite evaluation,
bounded private inputs, and bounded admissible doses.
-/
public section
namespace Papers.TbsNeuralCausalPi
set_option linter.style.longLine false
set_option linter.style.whitespace false
open MeasureTheory Filter
open scoped NNReal ENNReal
variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
  {C : Fin b → Set (Fin n)}

-- @node: trueObjective_sub_eq_integral_meanOutcome_gap
/-- Fix [a nonnegative Lipschitz bound L](hyp:L). Suppose [the first model's continuous mechanisms satisfy this bound](hyp:hcont), [the second model's continuous mechanisms satisfy it](hyp:hconthat), [the first model's observed and private latent coordinates are almost surely bounded in absolute value by the positive constant K](hyp:hbound), and [the second model satisfies the same coordinate bound](hyp:hboundhat). If [treatment is scalar](hyp:hT), [outcome is scalar](hyp:hY), [the intervention probability law is supported almost surely on the closed dose interval](hyp:hsupport), [its doses are almost surely admissible interventions](hyp:hadm), [the first model's population objective is defined](hyp:hMdefined), and [the second model's population objective is defined](hyp:hMhatdefined), then [the first objective minus the second equals the integral over that interval of the first causal mean outcome minus the second, under the intervention law](goal). -/
lemma trueObjective_sub_eq_integral_meanOutcome_gap
    (M Mhat : EuclideanSCM kind dims) (L : ℝ≥0) (K : ℝ)
    (hcont : ContinuousMechanismsLipschitz M L)
    (hconthat : ContinuousMechanismsLipschitz Mhat L)
    (hbound : VariablesBoundedAt M K) (hboundhat : VariablesBoundedAt Mhat K)
    (T Y : Fin n) (hT : valueDim (kind T) = 1) (hY : valueDim (kind Y) = 1)
    (muT : Measure ℝ) [IsProbabilityMeasure muT] (t1 t2 : ℝ)
    (hsupport : ∀ᵐ t ∂muT, t ∈ Set.Icc t1 t2)
    (hadm : ∀ᵐ t ∂muT, AdmissibleIntervention kind (singleIntervention T t))
    (hMdefined : objectiveDefined M (singleLawIntervention T) muT (scalarOutcome Y hY))
    (hMhatdefined : objectiveDefined Mhat (singleLawIntervention T) muT (scalarOutcome Y hY)) :
    trueObjective M (singleLawIntervention T) muT (scalarOutcome Y hY) hMdefined -
      trueObjective Mhat (singleLawIntervention T) muT (scalarOutcome Y hY) hMhatdefined =
      ∫ t in Set.Icc t1 t2, meanOutcome M T Y hY t - meanOutcome Mhat T Y hY t ∂muT := by
  have hdoses : ∀ᵐ t ∂muT, |t| ≤ |t1| + |t2| ∧
      AdmissibleIntervention kind (singleIntervention T t) := by
    filter_upwards [hsupport, hadm] with t ht ha
    refine ⟨abs_le.mpr ⟨?_, ?_⟩, ha⟩
    · linarith [ht.1, neg_abs_le t1, abs_nonneg t2]
    · linarith [ht.2, le_abs_self t2, abs_nonneg t1]
  have hi (N : EuclideanSCM kind dims) (hN : ContinuousMechanismsLipschitz N L)
      (hNK : VariablesBoundedAt N K) : Integrable (meanOutcome N T Y hY) muT := by
    have hsq := meanOutcome_integrable_sq_of_bounded_doses N L hN K hNK
      T Y hT hY muT (|t1| + |t2|) (by positivity) hdoses
    have hm : AEStronglyMeasurable (meanOutcome N T Y hY) muT := by fun_prop
    exact ((memLp_two_iff_integrable_sq hm).2 hsq).integrable (by norm_num)
  have heq (N : EuclideanSCM kind dims)
      (hNdefined : objectiveDefined N (singleLawIntervention T) muT (scalarOutcome Y hY)) :
      trueObjective N (singleLawIntervention T) muT (scalarOutcome Y hY) hNdefined =
        ∫ t, meanOutcome N T Y hY t ∂muT := by
    apply integral_congr_ae
    filter_upwards [hadm] with t ht
    simp only [singleLawIntervention, dif_pos ht]
    rfl
  rw [heq M hMdefined, heq Mhat hMhatdefined, ← integral_sub (hi M hcont hbound) (hi Mhat hconthat hboundhat),
    Measure.restrict_eq_self_of_ae_mem hsupport]

-- @node: integrated_dose_response_gap_le
/-- Fix [a nonnegative common Lipschitz bound L](hyp:L) and [a scalar outcome](hyp:hY). Suppose [the first model has independent latent blocks](hyp:hind), [the second model has independent latent blocks](hyp:hindhat), [the first model's continuous mechanisms are L-Lipschitz](hyp:hcont), [the second model's continuous mechanisms are L-Lipschitz](hyp:hconthat), [the first model's categorical probabilities are L-Lipschitz and represent its conditional category laws](hyp:hprop), [the second model's categorical probabilities have the same properties](hyp:hprophat), [the first model's observed and private latent coordinates are almost surely bounded in absolute value by positive K](hyp:hbound), [the second model satisfies the same bound](hyp:hboundhat), and [there is no hidden confounding](hyp:hnoconf). For [scalar treatment](hyp:hT) with [the treatment statistic equal to its scalar coordinate](hyp:htreatment), take [a conditional density p indexed by treatment parents and dose](hyp:p) that [represents the first model's conditional treatment law relative to the reference probability law P](hyp:hdensity), with [positive overlap constant delta](hyp:hdelta) and [density at least delta throughout the closed dose interval for almost every observed parent vector](hyp:hoverlap). If [the finite intervention measure is absolutely continuous with respect to P](hyp:hac) and [its density relative to P has finite extended square integral on the interval](hyp:hAT), then [the absolute integrated causal-mean gap under the intervention measure is bounded by the density's L² norm on the interval times the square root of the reference square-error bound: twice the dose comparison coefficient divided by delta times the observational Wasserstein distance, plus twice the squared dose Lipschitz constant times the squared distance times P's mass of the interval](goal). -/
lemma integrated_dose_response_gap_le
    (M Mhat : CanonicalSCM kind dims dag G C)
    (L : ℝ≥0) (K : ℝ) (T Y : Fin n) (hY : valueDim (kind Y) = 1)
    (hind : LatentBlocksIndependent M.toEuclideanSCM)
    (hindhat : LatentBlocksIndependent Mhat.toEuclideanSCM)
    (hcont : ContinuousMechanismsLipschitz M.toEuclideanSCM L)
    (hconthat : ContinuousMechanismsLipschitz Mhat.toEuclideanSCM L)
    (hprop : CategoricalPropensityLipschitz M.toEuclideanSCM M.f L)
    (hprophat : CategoricalPropensityLipschitz Mhat.toEuclideanSCM Mhat.f L)
    (hbound : VariablesBoundedAt M.toEuclideanSCM K)
    (hboundhat : VariablesBoundedAt Mhat.toEuclideanSCM K)
    (hnoconf : NoHiddenConfounding G) (P : ProbabilityMeasure ℝ)
    (treatment : Joint kind → ℝ) (hT : valueDim (kind T) = 1)
    (htreatment : treatment = scalarOutcome T hT)
    (p : ParentSpace M.toEuclideanSCM T × ℝ → ℝ≥0∞) (delta t1 t2 : ℝ)
    (hdensity : TreatmentReferenceDensity M.toEuclideanSCM T treatment P p)
    (hdelta : 0 < delta)
    (hoverlap : ∀ᵐ x ∂((observationalLaw M.toEuclideanSCM).map
      (parentValues M.toEuclideanSCM T)),
      ∀ t ∈ Set.Icc t1 t2, ENNReal.ofReal delta ≤ p (x,t))
    (muT : Measure ℝ) [IsFiniteMeasure muT] (hac : muT ≪ (P : Measure ℝ))
    (hAT : (∫⁻ t in Set.Icc t1 t2, (muT.rnDeriv (P : Measure ℝ) t)^2
      ∂(P : Measure ℝ)) < ⊤) :
    |∫ t in Set.Icc t1 t2,
      meanOutcome M.toEuclideanSCM T Y hY t - meanOutcome Mhat.toEuclideanSCM T Y hY t
        ∂muT| ≤
      Real.sqrt (∫⁻ t in Set.Icc t1 t2, (muT.rnDeriv (P : Measure ℝ) t)^2
        ∂(P : Measure ℝ)).toReal *
      Real.sqrt (2*doseCW kind L ⟨K, le_of_lt hbound.1⟩/delta *
        (wasserstein1 (observationalLaw Mhat.toEuclideanSCM)
          (observationalLaw M.toEuclideanSCM)).toReal +
        2*(doseLip kind L)^2 *
          (wasserstein1 (observationalLaw Mhat.toEuclideanSCM)
            (observationalLaw M.toEuclideanSCM)).toReal^2 *
          ((P : Measure ℝ) (Set.Icc t1 t2)).toReal) := by
  have hadm := treatment_intervention_ae_admissible M.toEuclideanSCM T hT P
    treatment htreatment p delta t1 t2 hdensity hdelta hoverlap
  have hdoses : ∀ᵐ t ∂(P : Measure ℝ).restrict (Set.Icc t1 t2),
      |t| ≤ |t1| + |t2| ∧ AdmissibleIntervention kind (singleIntervention T t) := by
    filter_upwards [hadm, ae_restrict_mem measurableSet_Icc] with t ht hm
    refine ⟨abs_le.mpr ⟨?_, ?_⟩, ht⟩
    · have := neg_abs_le t1
      have := abs_nonneg t2
      linarith [hm.1]
    · have := le_abs_self t2
      have := abs_nonneg t1
      linarith [hm.2]
  have hf2 := meanOutcome_integrable_sq_of_bounded_doses M.toEuclideanSCM L hcont K
    hbound T Y hT hY ((P : Measure ℝ).restrict (Set.Icc t1 t2))
    (|t1| + |t2|) (by positivity) hdoses
  have hg2 := meanOutcome_integrable_sq_of_bounded_doses Mhat.toEuclideanSCM L hconthat K
    hboundhat T Y hT hY ((P : Measure ℝ).restrict (Set.Icc t1 t2))
    (|t1| + |t2|) (by positivity) hdoses
  have hf : AEStronglyMeasurable (meanOutcome M.toEuclideanSCM T Y hY)
      ((P : Measure ℝ).restrict (Set.Icc t1 t2)) := by fun_prop
  have hg : AEStronglyMeasurable (meanOutcome Mhat.toEuclideanSCM T Y hY)
      ((P : Measure ℝ).restrict (Set.Icc t1 t2)) := by fun_prop
  have hgap2 := ((memLp_two_iff_integrable_sq hf).2 hf2).sub
    ((memLp_two_iff_integrable_sq hg).2 hg2)
  have htransfer := estimation_change_measure_square_bound muT (P : Measure ℝ)
    (Set.Icc t1 t2) measurableSet_Icc hac _ (hf.sub hg) hgap2.integrable_sq hAT
  have hsq := lipschitz_dose_response_gap M Mhat L K T Y hY hind hindhat
    hcont hconthat hprop hprophat hbound hboundhat ⟨hbound, hboundhat⟩
    hnoconf P treatment hT htreatment p delta t1 t2 hdensity hdelta hoverlap
  calc
    _ ≤ _ := htransfer
    _ ≤ _ := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsq) (Real.sqrt_nonneg _)

-- @node: rateObjective_error_le_reference_square
/-- Fix [a nonnegative common Lipschitz bound L](hyp:L) and [a scalar outcome](hyp:hY). Assume [independent latent blocks in the first model](hyp:hind), [independent latent blocks in the second model](hyp:hindhat), [L-Lipschitz continuous mechanisms in the first model](hyp:hcont), [L-Lipschitz continuous mechanisms in the second model](hyp:hconthat), [L-Lipschitz categorical probabilities representing conditional category laws in the first model](hyp:hprop), [the same categorical regularity in the second model](hyp:hprophat), [observed and private latent coordinates almost surely bounded in absolute value by positive K in the first model](hyp:hbound), [the same coordinate bound in the second model](hyp:hboundhat), and [no hidden confounding](hyp:hnoconf). With [scalar treatment](hyp:hT) and [the treatment statistic equal to its scalar coordinate](hyp:htreatment), let [p be a conditional density indexed by treatment parents and dose](hyp:p), [representing the first model's conditional treatment law relative to the reference probability law P](hyp:hdensity), with [delta positive](hyp:hdelta) and [p at least delta throughout the closed dose interval for almost every observed parent vector](hyp:hoverlap). If [the intervention probability law is absolutely continuous with respect to P](hyp:hac), [is supported almost surely on the interval](hyp:hsupport), [has a density with finite extended square integral on the interval](hyp:hAT), and [the first model's objective is defined](hyp:hMdefined) and [the second model's objective is defined](hyp:hMhatdefined), then [the absolute difference of the population objectives is at most the intervention density's L² norm on the interval times the square root of twice the dose comparison coefficient divided by delta times the observational Wasserstein distance, plus twice the squared dose Lipschitz constant times the squared distance times P's mass of the interval](goal). -/
lemma rateObjective_error_le_reference_square
    (M Mhat : CanonicalSCM kind dims dag G C)
    (L : ℝ≥0) (K : ℝ) (T Y : Fin n) (hY : valueDim (kind Y) = 1)
    (hind : LatentBlocksIndependent M.toEuclideanSCM)
    (hindhat : LatentBlocksIndependent Mhat.toEuclideanSCM)
    (hcont : ContinuousMechanismsLipschitz M.toEuclideanSCM L)
    (hconthat : ContinuousMechanismsLipschitz Mhat.toEuclideanSCM L)
    (hprop : CategoricalPropensityLipschitz M.toEuclideanSCM M.f L)
    (hprophat : CategoricalPropensityLipschitz Mhat.toEuclideanSCM Mhat.f L)
    (hbound : VariablesBoundedAt M.toEuclideanSCM K)
    (hboundhat : VariablesBoundedAt Mhat.toEuclideanSCM K)
    (hnoconf : NoHiddenConfounding G) (P : ProbabilityMeasure ℝ)
    (treatment : Joint kind → ℝ) (hT : valueDim (kind T) = 1)
    (htreatment : treatment = scalarOutcome T hT)
    (p : ParentSpace M.toEuclideanSCM T × ℝ → ℝ≥0∞) (delta t1 t2 : ℝ)
    (hdensity : TreatmentReferenceDensity M.toEuclideanSCM T treatment P p)
    (hdelta : 0 < delta)
    (hoverlap : ∀ᵐ x ∂((observationalLaw M.toEuclideanSCM).map
      (parentValues M.toEuclideanSCM T)),
      ∀ t ∈ Set.Icc t1 t2, ENNReal.ofReal delta ≤ p (x,t))
    (muT : Measure ℝ) [IsProbabilityMeasure muT] (hac : muT ≪ (P : Measure ℝ))
    (hsupport : ∀ᵐ t ∂muT, t ∈ Set.Icc t1 t2)
    (hAT : (∫⁻ t in Set.Icc t1 t2, (muT.rnDeriv (P : Measure ℝ) t)^2
      ∂(P : Measure ℝ)) < ⊤)
    (hMdefined : objectiveDefined M.toEuclideanSCM (singleLawIntervention T) muT
      (scalarOutcome Y hY))
    (hMhatdefined : objectiveDefined Mhat.toEuclideanSCM (singleLawIntervention T) muT
      (scalarOutcome Y hY)) :
    |trueObjective M.toEuclideanSCM (singleLawIntervention T) muT (scalarOutcome Y hY) hMdefined -
      trueObjective Mhat.toEuclideanSCM (singleLawIntervention T) muT (scalarOutcome Y hY) hMhatdefined| ≤
      Real.sqrt (∫⁻ t in Set.Icc t1 t2, (muT.rnDeriv (P : Measure ℝ) t)^2
        ∂(P : Measure ℝ)).toReal *
      Real.sqrt (2*doseCW kind L ⟨K, le_of_lt hbound.1⟩/delta *
        (wasserstein1 (observationalLaw Mhat.toEuclideanSCM)
          (observationalLaw M.toEuclideanSCM)).toReal +
        2*(doseLip kind L)^2 *
          (wasserstein1 (observationalLaw Mhat.toEuclideanSCM)
            (observationalLaw M.toEuclideanSCM)).toReal^2 *
          ((P : Measure ℝ) (Set.Icc t1 t2)).toReal) := by
  have hadmP := treatment_intervention_ae_admissible M.toEuclideanSCM T hT P
    treatment htreatment p delta t1 t2 hdensity hdelta hoverlap
  have hadm : ∀ᵐ t ∂muT, AdmissibleIntervention kind (singleIntervention T t) := by
    have h := (hac.restrict (Set.Icc t1 t2)).ae_le hadmP
    rwa [Measure.restrict_eq_self_of_ae_mem hsupport] at h
  rw [trueObjective_sub_eq_integral_meanOutcome_gap M.toEuclideanSCM Mhat.toEuclideanSCM
    L K hcont hconthat hbound hboundhat T Y hT hY muT t1 t2 hsupport hadm hMdefined hMhatdefined]
  exact integrated_dose_response_gap_le M Mhat L K T Y hY hind hindhat hcont hconthat
    hprop hprophat hbound hboundhat hnoconf P treatment hT htreatment p delta t1 t2
    hdensity hdelta hoverlap muT hac hAT

-- @node: restrictedCandidate_rateObjective_error_le_reference_square
/-- Fix [nonnegative regularity and size bounds L and K](hyp:L,K), and suppose [the neural candidate satisfies the restrictions on mechanism Lipschitz constants, continuous output sizes, and categorical raw maps at those bounds](hyp:hR). Assume [a scalar outcome](hyp:hY), [independent latent blocks in the reference model](hyp:hind), [L-Lipschitz continuous mechanisms in that model](hyp:hcont), [L-Lipschitz categorical probabilities representing its conditional category laws](hyp:hprop), [reference observed and private latent coordinates almost surely bounded in absolute value by positive K](hyp:hbound), [the same coordinate bound for the candidate](hyp:hboundhat), and [no hidden confounding](hyp:hnoconf). For [scalar treatment](hyp:hT) and [a treatment statistic equal to its scalar coordinate](hyp:htreatment), take [a conditional density p indexed by treatment parents and dose](hyp:p), [representing the reference model's conditional treatment law relative to the probability law P](hyp:hdensity), with [positive delta](hyp:hdelta) and [p at least delta throughout the closed dose interval for almost every observed parent vector](hyp:hoverlap). If [the intervention probability law is absolutely continuous with respect to P](hyp:hac), [is supported almost surely on the interval](hyp:hsupport), [has a density with finite extended square integral on the interval](hyp:hAT), and [the reference objective is defined](hyp:hMdefined) and [the candidate objective is defined](hyp:hMhatdefined), then [the absolute difference between the candidate and reference rate objectives is at most the intervention density's L² norm on the interval times the square root of twice the dose comparison coefficient divided by delta times their observational Wasserstein distance, plus twice the squared dose Lipschitz constant times the squared distance times P's mass of the interval](goal). -/
lemma restrictedCandidate_rateObjective_error_le_reference_square
    {counts : Fin b → ℕ} {F0 : StructuralClass kind dims dag C}
    {F1 : GeneratorClass dims counts}
    (M : CanonicalSCM kind dims dag G C)
    (R : NCMIn kind dims dag G C counts F0 F1) (L K : ℝ≥0)
    (hR : restrictedCandidate K L R)
    (T Y : Fin n) (hY : valueDim (kind Y) = 1)
    (hind : LatentBlocksIndependent M.toEuclideanSCM)
    (hcont : ContinuousMechanismsLipschitz M.toEuclideanSCM L)
    (hprop : CategoricalPropensityLipschitz M.toEuclideanSCM M.f L)
    (hbound : VariablesBoundedAt M.toEuclideanSCM K)
    (hboundhat : VariablesBoundedAt R.canonical.toEuclideanSCM K)
    (hnoconf : NoHiddenConfounding G) (P : ProbabilityMeasure ℝ)
    (treatment : Joint kind → ℝ) (hT : valueDim (kind T) = 1)
    (htreatment : treatment = scalarOutcome T hT)
    (p : ParentSpace M.toEuclideanSCM T × ℝ → ℝ≥0∞) (delta t1 t2 : ℝ)
    (hdensity : TreatmentReferenceDensity M.toEuclideanSCM T treatment P p)
    (hdelta : 0 < delta)
    (hoverlap : ∀ᵐ x ∂((observationalLaw M.toEuclideanSCM).map
      (parentValues M.toEuclideanSCM T)),
      ∀ t ∈ Set.Icc t1 t2, ENNReal.ofReal delta ≤ p (x,t))
    (muT : Measure ℝ) [IsProbabilityMeasure muT] (hac : muT ≪ (P : Measure ℝ))
    (hsupport : ∀ᵐ t ∂muT, t ∈ Set.Icc t1 t2)
    (hAT : (∫⁻ t in Set.Icc t1 t2, (muT.rnDeriv (P : Measure ℝ) t)^2
      ∂(P : Measure ℝ)) < ⊤)
    (hMdefined : objectiveDefined M.toEuclideanSCM (singleLawIntervention T) muT
      (scalarOutcome Y hY))
    (hMhatdefined : objectiveDefined R.canonical.toEuclideanSCM (singleLawIntervention T) muT
      (scalarOutcome Y hY)) :
    let w := wasserstein1 (observationalLaw R.canonical.toEuclideanSCM)
      (observationalLaw M.toEuclideanSCM)
    |trueObjective R.canonical.toEuclideanSCM (singleLawIntervention T) muT
        (rateObjective (scalarOutcome Y hY)) hMhatdefined -
      trueObjective M.toEuclideanSCM (singleLawIntervention T) muT
        (rateObjective (scalarOutcome Y hY)) hMdefined| ≤
      Real.sqrt (∫⁻ t in Set.Icc t1 t2, (muT.rnDeriv (P : Measure ℝ) t)^2
        ∂(P : Measure ℝ)).toReal *
      Real.sqrt (2*doseCW kind L ⟨K, le_of_lt hbound.1⟩/delta * w.toReal +
        2*(doseLip kind L)^2 * w.toReal^2 * ((P : Measure ℝ) (Set.Icc t1 t2)).toReal) := by
  obtain ⟨hconthat, hprophat⟩ := restrictedCandidate_mechanism_regularity K L R hR
  have h := rateObjective_error_le_reference_square M R.canonical L K T Y hY hind
    (canonical_latent_blocks_independent R.canonical) hcont hconthat hprop hprophat
    hbound hboundhat hnoconf P treatment hT htreatment p delta t1 t2
    hdensity hdelta hoverlap muT hac hsupport hAT hMdefined hMhatdefined
  simpa only [rateObjective, abs_sub_comm] using h

end Papers.TbsNeuralCausalPi

module
public import Papers.TbsExtremeEffects.Helpers.ConditionalConsistency
public import Toolkit.Foundations.Probability.Conditioning.JoinFactorization
public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-! Positivity extends the realized-treatment conditional mean identity to both arms. -/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
variable {q d : ℕ}

-- @node: ae_eq_of_eq_on_event_of_conditional_positive
/-- If [the conditioning sigma-field is contained in the ambient one](hyp:hG), [the event is measurable](hyp:hE), [both functions are measurable with respect to that field](hyp:hf,hg), [the event has strictly positive conditional probability almost surely](hyp:hpos), and [the functions agree almost surely on the event](hyp:heq), then [they agree almost surely everywhere](goal). -/
lemma ae_eq_of_eq_on_event_of_conditional_positive {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {G : MeasurableSpace Ω} (hG : G ≤ mΩ)
    {E : Set Ω} (hE : @MeasurableSet Ω mΩ E) {f g : Ω → ℝ}
    (hf : Measurable[G] f) (hg : Measurable[G] g)
    (hpos : ∀ᵐ w ∂μ, 0 < μ[E.indicator (fun _ => (1 : ℝ)) | G] w)
    (heq : ∀ᵐ w ∂μ, w ∈ E → f w = g w) : f =ᵐ[μ] g := by
  let : MeasurableSpace Ω := mΩ
  let A : Set Ω := {w | f w ≠ g w}
  have hA : MeasurableSet[G] A := (measurableSet_eq_fun hf hg).compl
  have hzero : A.indicator (E.indicator (fun _ => (1 : ℝ))) =ᵐ[μ] 0 := by
    filter_upwards [heq] with w hw
    by_cases ha : w ∈ A
    · have hn : w ∉ E := fun he => ha (hw he)
      simp [Set.indicator_of_mem ha, Set.indicator_of_notMem hn]
    · simp [Set.indicator_of_notMem ha]
  have hc := (condExp_indicator ((integrable_const (1 : ℝ)).indicator hE) hA).symm.trans
    (condExp_congr_ae (m := G) hzero)
  filter_upwards [hc, hpos] with w hw hp
  by_contra hn
  have ha : w ∈ A := hn
  simp only [Set.indicator_of_mem ha, condExp_zero, Pi.zero_apply] at hw
  exact (ne_of_gt hp) hw

-- @node: conditionalPotentialMean_stronglyMeasurable
/-- [The conditional potential-outcome mean](goal), for the specified model and treatment arm, is strongly measurable with respect to the chosen conditioning sigma-field. -/
@[fun_prop]
lemma conditionalPotentialMean_stronglyMeasurable (M : ExtremeModel q d) (a : Bool)
    (G : MeasurableSpace M.Om) : StronglyMeasurable[G] (conditionalPotentialMean M a G) := by
  apply StronglyMeasurable.sub
  · exact StronglyMeasurable.limUnder (fun k => stronglyMeasurable_condExp)
  · exact StronglyMeasurable.limUnder (fun k => stronglyMeasurable_condExp)

-- @node: propensity_condExp_given_XU
/-- If [the noise is independent of the covariates and treatment](hyp:hNoise), then [the conditional expectation of treatment given covariates and noise equals the propensity score evaluated at the covariates](goal). -/
lemma propensity_condExp_given_XU (M : ExtremeModel q d) (hNoise : NoiseIndependent M) :
    M.mu[(fun w => if M.D w then (1 : ℝ) else 0) | sigmaXU M] =ᵐ[M.mu]
      (fun w => M.p (M.X w)) := by
  let F := MeasurableSpace.comap M.D inferInstance
  let H := MeasurableSpace.comap M.U inferInstance
  let : MeasurableSpace M.Om := M.measurableSpace
  have hind : Indep H (F ⊔ sigmaX M) M.mu := by
    have hn : Indep (MeasurableSpace.comap M.U inferInstance)
        (MeasurableSpace.comap (fun w => (M.X w, M.D w)) inferInstance) M.mu := hNoise
    have h : Indep H (sigmaX M ⊔ F) M.mu := by
      simpa only [inferInstance, Prod.instMeasurableSpace, MeasurableSpace.comap_prodMk,
        F, H, sigmaX] using hn
    simpa only [sup_comm] using h
  have hF : F ≤ M.measurableSpace := M.measurable_D.comap_le
  have hX : sigmaX M ≤ M.measurableSpace := M.measurable_X.comap_le
  have hH : H ≤ M.measurableSpace := M.measurable_U.comap_le
  have hf : Measurable[F] (fun w => if M.D w then (1 : ℝ) else 0) := by
    have hD : Measurable[F] M.D := Measurable.of_comap_le le_rfl
    exact measurable_const.ite (hD (measurableSet_singleton true)) measurable_const
  have hi : Integrable (fun w => if M.D w then (1 : ℝ) else 0) M.mu := by
    apply Integrable.of_bound (hf.mono hF le_rfl).aestronglyMeasurable 1
    exact Eventually.of_forall fun w => by cases M.D w <;> norm_num
  have hc := Toolkit.Foundations.Probability.Conditioning.condExp_sup_eq_of_indep_sup
    hF hX hH hind hi hf.stronglyMeasurable.aestronglyMeasurable
  simpa only [sigmaXU, sigmaX, H, inferInstance, Prod.instMeasurableSpace,
    MeasurableSpace.comap_prodMk] using hc.trans M.propensity_identity.symm

-- @node: treatment_conditional_positive
/-- If [the noise is independent of covariates and treatment](hyp:hNoise) and [the identification-side positivity conditions hold](hyp:hSide), then [each treatment arm has strictly positive conditional probability given covariates and noise, almost surely](goal). -/
lemma treatment_conditional_positive (M : ExtremeModel q d) (hNoise : NoiseIndependent M)
    (hSide : IdentificationSideConditions M) (a : Bool) :
    ∀ᵐ w ∂M.mu, 0 < M.mu[({w | M.D w = a}).indicator (fun _ => (1 : ℝ)) |
      sigmaXU M] w := by
  have hG : sigmaXU M ≤ M.measurableSpace := (M.measurable_X.prodMk M.measurable_U).comap_le
  have hi : Integrable (fun w => if M.D w then (1 : ℝ) else 0) M.mu := by
    have hm : Measurable (fun w => if M.D w then (1 : ℝ) else 0) :=
      measurable_const.ite (M.measurable_D (measurableSet_singleton true)) measurable_const
    apply Integrable.of_bound hm.aestronglyMeasurable 1
    exact Eventually.of_forall fun w => by cases M.D w <;> norm_num
  have hp := propensity_condExp_given_XU M hNoise
  cases a
  · have heq : ({w | M.D w = false}).indicator (fun _ => (1 : ℝ)) =
        (fun _ => (1 : ℝ)) - (fun w => if M.D w then (1 : ℝ) else 0) := by
      funext w
      cases h : M.D w <;> simp [h]
    rw [heq]
    have hc := condExp_sub (m := sigmaXU M) (integrable_const (1 : ℝ)) hi
    filter_upwards [hc, hp, hSide.1] with w hc hp hs
    simp only [Pi.sub_apply, condExp_const hG] at hc
    rw [hc, hp]
    linarith [hs.2]
  · have heq : ({w | M.D w = true}).indicator (fun _ => (1 : ℝ)) =
        (fun w => if M.D w then (1 : ℝ) else 0) := by
      funext w
      cases h : M.D w <;> simp [h]
    rw [heq]
    filter_upwards [hp, hSide.1] with w hp hs
    rw [hp]
    exact hs.1

-- @node: regression_eq_potentialMean
/-- If [observed outcomes equal their realized potential outcomes](hyp:hConsistency), [the regression is a conditional-mean version](hyp:hMean), [the noise is independent of covariates and treatment](hyp:hNoise), and [the identification-side conditions hold](hyp:hSide), then [the regression for either treatment arm equals its conditional potential-outcome mean given covariates and noise, almost surely](goal). -/
lemma regression_eq_potentialMean (M : ExtremeModel q d)
    (hConsistency : Consistency M) (hMean : ConditionalMeanVersion M)
    (hNoise : NoiseIndependent M) (hSide : IdentificationSideConditions M) (a : Bool) :
    (fun w => M.f (M.X w) a (M.U w)) =ᵐ[M.mu]
      conditionalPotentialMean M a (sigmaXU M) := by
  have hG : sigmaXU M ≤ M.measurableSpace := (M.measurable_X.prodMk M.measurable_U).comap_le
  have hf : Measurable[sigmaXU M] (fun w => M.f (M.X w) a (M.U w)) := by
    have hpair : Measurable[sigmaXU M] (fun w => (M.X w, M.U w)) :=
      Measurable.of_comap_le le_rfl
    exact hMean.1.comp (hpair.fst.prodMk (measurable_const.prodMk hpair.snd))
  apply ae_eq_of_eq_on_event_of_conditional_positive M.mu hG
    (M.measurable_D (measurableSet_singleton a)) hf
    (conditionalPotentialMean_stronglyMeasurable M a (sigmaXU M)).measurable
    (treatment_conditional_positive M hNoise hSide a)
  exact regression_eq_potentialMean_on_treatment M hConsistency hMean hSide a

end Papers.TbsExtremeEffects

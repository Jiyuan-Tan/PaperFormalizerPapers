module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousFullMean
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousDenominatorBias
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationContinuousFullRegressions
/-! Exact mean of joint full-interval regression perturbations with fitted denominators.
The common outcome term cancels before the instrument kernel is integrated.
This retains the propensity/outcome cross term in the coefficient error. -/
public section
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.unreachableTactic false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: fitted_continuous_full_joint_regression_mean_difference
/-- Suppose [two nuisance records have identical assignment probabilities](hyp:hpi),
[these probabilities are measurable](hyp:hpimeas), [the covariate weight is
measurable](hyp:hw), and [the upper](hyp:hCp) and [lower](hyp:hCm) differences
in treatment-propensity-weighted outcome means are measurable. If [the weighted
score difference is integrable](hyp:hi), then [its expectation equals the covariate
mean of the weighted upper coefficient difference times one minus the true-to-fitted
assignment-probability ratio, less the corresponding lower term](goal). -/
lemma fitted_continuous_full_joint_regression_mean_difference
    (L : LevelData Z X) (e b : NuisanceCont L) (hpi : e.piLev = b.piLev)
    (hpimeas : ∀ a, Measurable (b.piLev a))
    (k : Fin L.K) (w : X → ℝ) (hw : Measurable w)
    (hCp : Measurable (fun x => continuousFullRegressionCoefficient L e true k x -
      continuousFullRegressionCoefficient L b true k x))
    (hCm : Measurable (fun x => continuousFullRegressionCoefficient L e false k x -
      continuousFullRegressionCoefficient L b false k x))
    (hi : Integrable (fun o : Obs X Z => w o.1 *
      (psiFullJ L e k o - psiFullJ L b k o)) (observationLaw M)) :
    (∫ o : Obs X Z, w o.1 * (psiFullJ L e k o - psiFullJ L b k o)
      ∂observationLaw M) =
    ∫ x, w x *
      ((continuousFullRegressionCoefficient L e true k x -
        continuousFullRegressionCoefficient L b true k x) *
          (1 - (∑ z ∈ L.S (k.val+1), instProb M z x) / positiveValue b.piLev (k.val+1) x) -
       (continuousFullRegressionCoefficient L e false k x -
        continuousFullRegressionCoefficient L b false k x) *
          (1 - (∑ z ∈ L.S k.val, instProb M z x) / positiveValue b.piLev k.val x))
      ∂xLaw M := by
  let Cp := fun x => continuousFullRegressionCoefficient L e true k x -
    continuousFullRegressionCoefficient L b true k x
  let Cm := fun x => continuousFullRegressionCoefficient L e false k x -
    continuousFullRegressionCoefficient L b false k x
  let f : Z × X → ℝ := fun zx => w zx.2 *
    (Cp zx.2 * (1 - indicator (zx.1 ∈ L.S (k.val+1)) /
      positiveValue b.piLev (k.val+1) zx.2) -
     Cm zx.2 * (1 - indicator (zx.1 ∈ L.S k.val) /
      positiveValue b.piLev k.val zx.2))
  have hpim i : Measurable (positiveValue b.piLev i) := by
    first | fun_prop | skip
    unfold positiveValue
    split_ifs <;> first | fun_prop | exact hpimeas _
  have hf : Measurable f := by
    dsimp only [f]
    fun_prop
  have hd (o : Obs X Z) :
      w o.1 * (psiFullJ L e k o - psiFullJ L b k o) = f (o.2.1, o.1) := by
    rw [continuous_full_fixed_denominator_difference L e b hpi]
  have hsum (x : X) : (∑ z, instProb M z x) = 1 := by
    haveI := M.instKernel_markov
    change (∑ z, (M.instKernel x).real {z}) = 1
    rw [sum_measureReal_singleton Finset.univ]
    simp
  have hsel (C : Finset Z) (x : X) :
      (∑ z, instProb M z x * indicator (z ∈ C)) = ∑ z ∈ C, instProb M z x := by
    simp only [indicator, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hs (x : X) : (∑ z, instProb M z x * f (z,x)) =
      w x * (Cp x * (1 - (∑ z ∈ L.S (k.val+1), instProb M z x) /
        positiveValue b.piLev (k.val+1) x) -
      Cm x * (1 - (∑ z ∈ L.S k.val, instProb M z x) /
        positiveValue b.piLev k.val x)) := by
    have heq (z : Z) : instProb M z x * f (z,x) =
        (w x * Cp x) * instProb M z x -
          (w x * Cp x * (positiveValue b.piLev (k.val+1) x)⁻¹) *
            (instProb M z x * indicator (z ∈ L.S (k.val+1))) -
        ((w x * Cm x) * instProb M z x -
          (w x * Cm x * (positiveValue b.piLev k.val x)⁻¹) *
            (instProb M z x * indicator (z ∈ L.S k.val))) := by
      dsimp only [f]
      simp only [div_eq_mul_inv]
      ring
    simp_rw [heq]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    simp only [← Finset.mul_sum, hsum, hsel, mul_one]
    simp only [div_eq_mul_inv]
    ring
  simp_rw [hd]
  have ht := population_instrument_integral M f hf (by simpa only [← hd] using hi)
  simpa only [hs, Cp, Cm] using ht

-- @node: fitted_continuous_weighted_full_component_integrable
/-- Under [admissibility of the fitted nuisance](hyp:he), [potential-outcome support
restrictions](hyp:hp), [consistency](hyp:hcons), and [known outcome endpoints](hyp:hend),
if [the overlap bound is positive](hyp:hc) and [fitted assignment probabilities
are almost surely above it](hyp:hclip), then [the full-interval component score
multiplied by its fitted signed weight is integrable](goal). -/
lemma fitted_continuous_weighted_full_component_integrable
    (L : LevelData Z X) (e : NuisanceCont L) (he : ContAdmissible M L e)
    (hp : PotentialSupport M) (hcons : Consistency M) (hend : OutcomeEndpointsKnown M)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (k : Fin L.K) :
    Integrable (fun o : Obs X Z => e.gammaFull k o.1 * psiFullJ L e k o)
      (observationLaw M) := by
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  have ip := (fitted_continuous_full_score_product_memLp M L e he hp hcons hend
    c hc hclip k).integrable (by norm_num)
  have ie := (fitted_continuous_full_event_mean M L e he k).1
  have ic := ((fitted_continuous_gammaFull_memLp M L e he k).comp_measurePreserving
    (observationLaw_fst_measurePreserving M)).integrable_mul
      ((fitted_contFullJ_memLp M L e he k).comp_measurePreserving
        (observationLaw_fst_measurePreserving M))
  convert! (ip.sub' ie).fun_add ic using 1
  funext o
  simp only [psiFullProd, fullValue, dif_pos k.isLt, Pi.mul_apply, Function.comp_apply]
  ring

-- The reference keeps the fitted denominator but restores both regressions.
-- Its admissibility and the required moments follow from the two clipped fits.
-- @node: fitted_continuous_full_joint_regression_bias_bound
/-- Assume [the true nuisance is admissible](hyp:he0), [the fitted nuisance is
admissible](hyp:he), [potential-outcome support restrictions hold](hyp:hp),
[consistency holds](hyp:hcons), and [outcome endpoints are known](hyp:hend), with
[a positive overlap bound](hyp:hc) and [fitted assignment probabilities almost
surely above it](hyp:hclip). Then [the absolute mean fitted-weighted score change
from restoring both regressions is bounded by the sum, at the two adjacent levels,
of assignment-probability L2 error times treatment-propensity-weighted outcome-mean
L2 error divided by the overlap bound](goal). -/
lemma fitted_continuous_full_joint_regression_bias_bound
    (L : LevelData Z X) (e : NuisanceCont L)
    (he0 : ContAdmissible M L (trueNuisance M L)) (he : ContAdmissible M L e)
    (hp : PotentialSupport M) (hcons : Consistency M) (hend : OutcomeEndpointsKnown M)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (k : Fin L.K) :
    let b := {trueNuisance M L with piLev := e.piLev, gammaFull := e.gammaFull}
    |∫ o : Obs X Z, e.gammaFull k o.1 * (psiFullJ L e k o - psiFullJ L b k o)
      ∂observationLaw M| ≤
      finiteL2Error M (positiveValue e.piLev (k.val+1))
        (positiveValue (trueNuisance M L).piLev (k.val+1)) *
        finiteL2Error M (fun x => positiveValue e.pLev (k.val+1) x * fullValue e.JfullPlus k x)
          (fun x => positiveValue (trueNuisance M L).pLev (k.val+1) x *
            fullValue (trueNuisance M L).JfullPlus k x) / c +
      finiteL2Error M (positiveValue e.piLev k.val) (positiveValue (trueNuisance M L).piLev k.val) *
        finiteL2Error M (fun x => positiveValue e.pLev k.val x * minusFullValue e k x)
          (fun x => positiveValue (trueNuisance M L).pLev k.val x *
            minusFullValue (trueNuisance M L) k x) / c := by
  dsimp only
  let b := {trueNuisance M L with piLev := e.piLev, gammaFull := e.gammaFull}
  have hb : ContAdmissible M L b := by
    dsimp only [b]
    rcases he0 with ⟨h1, h2, h3, h4, _, _, h7, h8, h9, h10, _, _, hrest⟩
    rcases he with ⟨_, _, _, _, h5, h6, _, _, _, _, h11, h12, _⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hrest⟩
  have hi := (fitted_continuous_weighted_full_component_integrable M L e he
    hp hcons hend c hc hclip k).sub
      (fitted_continuous_weighted_full_component_integrable M L b hb
        hp hcons hend c hc hclip k)
  change Integrable (fun o : Obs X Z => e.gammaFull k o.1 * psiFullJ L e k o -
    e.gammaFull k o.1 * psiFullJ L b k o) (observationLaw M) at hi
  have hcoef (s : NuisanceCont L) (hs : ContAdmissible M L s) (plus : Bool) :
      Measurable (continuousFullRegressionCoefficient L s plus k) := by
    change Measurable (fun x => continuousFullRegressionCoefficient L s plus k x)
    cases plus
    · by_cases hk0 : k.val = 0
      · simp only [continuousFullRegressionCoefficient, Bool.false_eq_true,
          if_false, hk0, if_true]
        fun_prop
      · simpa only [continuousFullRegressionCoefficient, Bool.false_eq_true,
          if_false, hk0, Pi.mul_def] using
          (fitted_continuous_full_coordinates M L s hs k).1.1.mul
            (fitted_continuous_full_coordinates M L s hs k).2.2.1
    · simpa only [continuousFullRegressionCoefficient, Bool.true_eq, if_true, Pi.mul_def] using
        (fitted_continuous_full_coordinates M L s hs (k.val+1)).1.1.mul
          (fitted_continuous_full_coordinates M L s hs k).2.1.1
  have hd := fitted_continuous_full_joint_regression_mean_difference M L e b rfl
    (fun a => by
      have ha := (fitted_continuous_assignment_coordinates M L e he a.val).1
      change Measurable (fun x => positiveValue e.piLev a.val x) at ha
      simpa only [positiveValue, dif_pos a.property] using
        ha)
    k (e.gammaFull k) (fitted_continuous_gammaFull_coordinates M L e he k).1
    ((hcoef e he true).sub (hcoef b hb true))
    ((hcoef e he false).sub (hcoef b hb false))
    (by simpa only [mul_sub] using hi)
  let B := fun (plus : Bool) x => e.gammaFull k x *
    (1 - positiveValue (trueNuisance M L).piLev (if plus then k.val+1 else k.val) x /
      positiveValue e.piLev (if plus then k.val+1 else k.val) x) *
    ((positiveValue e.pLev (if plus then k.val+1 else k.val) x *
        (if plus then fullValue e.JfullPlus k x else minusFullValue e k x)) -
      (positiveValue (trueNuisance M L).pLev (if plus then k.val+1 else k.val) x *
        (if plus then fullValue (trueNuisance M L).JfullPlus k x
          else minusFullValue (trueNuisance M L) k x)))
  have hpB := fitted_continuous_full_joint_denominator_bias_bound M L (trueNuisance M L)
    e he0 he c hc hclip true k
  have hmB := fitted_continuous_full_joint_denominator_bias_bound M L (trueNuisance M L)
    e he0 he c hc hclip false k
  have heq : (∫ o : Obs X Z, e.gammaFull k o.1 *
      (psiFullJ L e k o - psiFullJ L b k o) ∂observationLaw M) =
      ∫ x, B true x - B false x ∂xLaw M := by
    rw [hd]
    apply integral_congr_ae
    filter_upwards [] with x
    have hpden : positiveValue (trueNuisance M L).piLev (k.val+1) x =
        ∑ z ∈ L.S (k.val+1), instProb M z x := by
      simp [positiveValue, trueNuisance, levelSetProb,
        show 1 ≤ k.val+1 ∧ k.val+1 ≤ L.K by omega]
    by_cases hk0 : k.val = 0
    · have hz (s : NuisanceCont L) : positiveValue s.pLev k.val x = 0 := by
        simp [positiveValue, hk0]
      simp only [B, continuousFullRegressionCoefficient, Bool.true_eq,
        Bool.false_eq_true, if_true, if_false, if_pos hk0, b, hpden, hz, zero_mul, sub_zero]
      ring
    · have hmden : positiveValue (trueNuisance M L).piLev k.val x =
          ∑ z ∈ L.S k.val, instProb M z x := by
        simp [positiveValue, trueNuisance, levelSetProb,
          show 1 ≤ k.val ∧ k.val ≤ L.K by omega]
      have hmb : minusFullValue b k x = minusFullValue (trueNuisance M L) k x := rfl
      simp only [B, continuousFullRegressionCoefficient, Bool.true_eq,
        Bool.false_eq_true, if_true, if_false, hk0, hmb]
      simp only [b, hpden, hmden]
      ring
  rw [heq, integral_sub hpB.1 hmB.1]
  exact (abs_sub _ _).trans (add_le_add hpB.2 hmB.2)

-- @node: nuisanceRates_continuous_full_joint_regression_bias_root_n_negligible
/-- Suppose [the true nuisance is admissible](hyp:he0), [all fitted nuisances are
admissible](hyp:heh), [potential-outcome support restrictions hold](hyp:hp),
[consistency holds](hyp:hcons), and [outcome endpoints are known](hyp:hend). Given
[a positive overlap bound](hyp:hc), [a uniform almost-sure lower bound on fitted
assignment probabilities](hyp:hclip), and inverse-fourth-root little-order L2 rates
for [assignment probabilities](hyp:hrpi), [treatment propensities](hyp:hrp),
[upper outcome means](hyp:hrplus), and [lower outcome means](hyp:hrminus), [the
mean fitted-weighted score change from restoring both regressions, multiplied by
the square root of the half-sample size, converges in probability to zero](goal). -/
lemma nuisanceRates_continuous_full_joint_regression_bias_root_n_negligible
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (L : LevelData Z X) (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hp : PotentialSupport M) (hcons : Consistency M) (hend : OutcomeEndpointsKnown M)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a (i : PositiveIndex L.K), ∀ᵐ x ∂xLaw M, c ≤ (eh n a).piLev i x)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) (trueNuisance M L).piLev)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) (trueNuisance M L).pLev)
    (hrplus : FiniteNuisanceRates M μ (fun n a => (eh n a).JfullPlus) (trueNuisance M L).JfullPlus)
    (hrminus : FiniteNuisanceRates M μ (fun n a => (eh n a).JfullMinus) (trueNuisance M L).JfullMinus)
    (k : Fin L.K) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
        (∫ o : Obs X Z, (eh (2*(n+1)) a).gammaFull k o.1 *
          (psiFullJ L (eh (2*(n+1)) a) k o -
            psiFullJ L {trueNuisance M L with
              piLev := (eh (2*(n+1)) a).piLev
              gammaFull := (eh (2*(n+1)) a).gammaFull} k o) ∂observationLaw M))
      atTop (fun _ _ => 0) := by
  let pi := fun (s : NuisanceCont L) (plus : Bool) =>
    positiveValue s.piLev (if plus then k.val+1 else k.val)
  let C := fun (s : NuisanceCont L) (plus : Bool) x =>
    positiveValue s.pLev (if plus then k.val+1 else k.val) x *
      (if plus then fullValue s.JfullPlus k x else minusFullValue s k x)
  let E := fun (plus : Bool) n a =>
    finiteL2Error M (pi (eh (2*(n+1)) a) plus) (pi (trueNuisance M L) plus) *
      finiteL2Error M (C (eh (2*(n+1)) a) plus) (C (trueNuisance M L) plus)
  have hr (plus : Bool) : Causalean.Stat.IsLittleOp (E plus)
      (fun n => ((2*(n+1) : ℕ) : ℝ)^(-1/2 : ℝ)) μ :=
    dml_quarter_rate_product μ _ _
      (nuisanceRates_positiveValue M μ L.K _ _ hrpi (if plus then k.val+1 else k.val))
      (nuisanceRates_continuous_full_coefficient_quarter_rate M μ L (trueNuisance M L)
        eh he0 heh hrp hrplus hrminus plus k)
  have hs := (hr true).add_eventually_nonneg_rate
    (Eventually.of_forall (fun _ => Real.rpow_nonneg (by positivity) _)) (hr false)
  apply dml_root_n_bias_tendsto_probability μ
  apply Causalean.Stat.IsLittleOp.of_abs_le_const_mul (by positivity : 0 < 1/c) hs
  intro n a
  have hb := fitted_continuous_full_joint_regression_bias_bound M L (eh (2*(n+1)) a)
    he0 (heh _ a) hp hcons hend c hc (hclip _ a) k
  have hE (plus : Bool) : 0 ≤ E plus n a :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rw [abs_of_nonneg (add_nonneg (hE true) (hE false))]
  exact hb.trans_eq (by
    dsimp only [E, pi, C]
    simp only [Bool.true_eq, Bool.false_eq_true, if_true, if_false]
    ring)

end Papers.TbsPrteOptimalTransport

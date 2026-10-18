module
public import Papers.TbsPrteOptimalTransport.Helpers.AdmissibleFullDenominators
/-! Population mean identities when full-interval regressions, denominators,
and signed product weights are fitted simultaneously. -/
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

-- The fitted reciprocal is a covariate weight in the assignment tower identity.
-- @node: population_fitted_assignment_weighted_mean
/-- For [a measurable fitted assignment divisor](hyp:hq) and [a measurable
covariate weight](hyp:hw), if [the clipping constant is positive](hyp:hc), [the
divisor is almost surely at least that constant](hyp:hclip), and [the weight is
almost surely bounded in absolute value by the given bound](hyp:hbound), [the
weight times the selected-instrument indicator divided by the fitted divisor and
its conditional-probability counterpart are both integrable and have equal
population means](goal). -/
lemma population_fitted_assignment_weighted_mean (C : Finset Z)
    (q w : X → ℝ) (hq : Measurable q) (hw : Measurable w)
    (c B : ℝ) (hc : 0 < c) (hclip : ∀ᵐ x ∂xLaw M, c ≤ q x)
    (hbound : ∀ᵐ x ∂xLaw M, ‖w x‖ ≤ B) :
    Integrable (fun o : Obs X Z => w o.1 * indicator (o.2.1 ∈ C) / q o.1)
      (observationLaw M) ∧
    Integrable (fun o : Obs X Z => w o.1 * (∑ z ∈ C, instProb M z o.1) / q o.1)
      (observationLaw M) ∧
    (∫ o : Obs X Z, w o.1 * indicator (o.2.1 ∈ C) / q o.1 ∂observationLaw M) =
      ∫ o : Obs X Z, w o.1 * (∑ z ∈ C, instProb M z o.1) / q o.1
        ∂observationLaw M := by
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  let a : X → ℝ := fun x => w x / q x
  have ha : Measurable a := by fun_prop
  have hab : ∀ᵐ x ∂xLaw M, ‖a x‖ ≤ B / c := by
    filter_upwards [hclip, hbound] with x hx hb
    change ‖w x / q x‖ ≤ B / c
    rw [norm_div, Real.norm_eq_abs (q x), abs_of_pos (hc.trans_le hx)]
    exact (div_le_div_of_nonneg_right hb (hc.trans_le hx).le).trans
      (div_le_div_of_nonneg_left ((norm_nonneg _).trans hb) hc hx)
  have ia : Integrable (fun o : Obs X Z => a o.1) (observationLaw M) :=
    Integrable.of_bound (ha.comp measurable_fst).aestronglyMeasurable (B/c)
      (observationLaw_covariate_ae M _ hab)
  have hp := population_instrument_set_probability_measurable M C
  have ip : Integrable (fun o : Obs X Z => a o.1 * ∑ z ∈ C, instProb M z o.1)
      (observationLaw M) := by
    apply ia.mul_bdd (hp.comp measurable_fst).aestronglyMeasurable
    apply Eventually.of_forall
    intro o
    change ‖∑ z ∈ C, instProb M z o.1‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (population_instrument_set_probability_range M C o.1).1]
    exact (population_instrument_set_probability_range M C o.1).2
  have hz := population_assignment_residual_integrable M C a ha (B/c) hab
  have iz : Integrable (fun o : Obs X Z => a o.1 * indicator (o.2.1 ∈ C))
      (observationLaw M) := by
    convert! hz.fun_add ip using 1
    funext o
    ring
  have z := population_assignment_weighted_integral_zero M C a ha hz
  simp_rw [mul_sub] at z
  rw [integral_sub iz ip] at z
  have eq := sub_eq_zero.mp z
  have h := And.intro iz (And.intro ip eq)
  simpa only [a, div_mul_eq_mul_div] using h

-- The population outcome residual stays centered. The remaining term is the
-- fitted regression error times the true assignment mass over its fitted mass.
-- @node: population_RP_joint_fitted_weighted_mean
/-- Under [baseline overlap](hyp:hov), [an almost surely binary outcome](hyp:hy),
and [admissibility of the true binary nuisance](hyp:he), suppose [the fitted
outcome regressions](hyp:hP) and [fitted assignment probabilities](hyp:hpi) are
measurable, [the clipping constant is positive](hyp:hc), [all fitted assignment
probabilities are almost surely at least that constant](hyp:hclip), [all fitted
outcome regressions are almost surely bounded by the given outcome
bound](hyp:hPB), and [the covariate weight is measurable](hyp:hw) and [almost
surely bounded by the given weight bound](hyp:hwB). Then [the weighted fitted
outcome residual correction and the weight times the true assignment probability
times the true-minus-fitted outcome regression divided by the fitted assignment
probability are both integrable and have equal population means at the given
level](goal). -/
lemma population_RP_joint_fitted_weighted_mean
    (L : LevelData Z X) (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (hy : OutcomeBinaryAE M) (he : BinAdmissible M L (eta0Bin M L))
    (P pi : PositiveIndex L.K → X → ℝ)
    (hP : ∀ a, Measurable (P a)) (hpi : ∀ a, Measurable (pi a))
    (c D : ℝ) (hc : 0 < c) (hclip : ∀ a, ∀ᵐ x ∂xLaw M, c ≤ pi a x)
    (hPB : ∀ a, ∀ᵐ x ∂xLaw M, ‖P a x‖ ≤ D)
    (w : X → ℝ) (hw : Measurable w) (B : ℝ)
    (hwB : ∀ᵐ x ∂xLaw M, ‖w x‖ ≤ B) (i : ℕ) :
    Integrable (fun o : Obs X Z => w o.1 *
      RP L {eta0Bin M L with P1 := P, piLev := pi} i o) (observationLaw M) ∧
    Integrable (fun o : Obs X Z => w o.1 * positiveValue (eta0Bin M L).piLev i o.1 *
      (positiveValue (eta0Bin M L).P1 i o.1 - positiveValue P i o.1) /
        positiveValue pi i o.1) (observationLaw M) ∧
    (∫ o : Obs X Z, w o.1 * RP L {eta0Bin M L with P1 := P, piLev := pi} i o
      ∂observationLaw M) =
      ∫ o : Obs X Z, w o.1 * positiveValue (eta0Bin M L).piLev i o.1 *
        (positiveValue (eta0Bin M L).P1 i o.1 - positiveValue P i o.1) /
          positiveValue pi i o.1 ∂observationLaw M := by
  by_cases hi : 1 ≤ i ∧ i ≤ L.K
  · let a : PositiveIndex L.K := ⟨i, hi⟩
    let v : X → ℝ := fun x => w x * ((eta0Bin M L).P1 a x - P a x)
    have hv : Measurable v := hw.mul (((he.2.2.2.1 a).2.1).sub (hP a))
    have hvB : ∀ᵐ x ∂xLaw M, ‖v x‖ ≤ B * (1+D) := by
      filter_upwards [hwB, hPB a, he.2.2.1 a] with x hx hp ht
      have htB : ‖(eta0Bin M L).P1 a x‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg ht.2.1.1]
        exact ht.2.1.2
      calc
        _ = ‖w x‖ * ‖(eta0Bin M L).P1 a x - P a x‖ := norm_mul _ _
        _ ≤ B * (1+D) := mul_le_mul hx
          ((norm_sub_le _ _).trans (add_le_add htB hp)) (norm_nonneg _)
          ((norm_nonneg _).trans hx)
    obtain ⟨iz, im, hz⟩ := population_fitted_assignment_weighted_mean M (L.S i)
      (pi a) v (hpi a) hv c (B*(1+D)) hc (hclip a) hvB
    have ir := (population_binary_RP_fitted_denominator_integrable M L cpi hov hy he
      pi hpi c hc hclip i).bdd_mul (hw.comp measurable_fst).aestronglyMeasurable
        (observationLaw_covariate_ae M _ hwB)
    change Integrable (fun o : Obs X Z => w o.1 *
      RP L {eta0Bin M L with piLev := pi} i o) (observationLaw M) at ir
    have zr := population_RP_denominator_weighted_integral_zero M L pi hpi i w hw ir
    have hid : (fun o : Obs X Z => w o.1 *
        RP L {eta0Bin M L with P1 := P, piLev := pi} i o) =
        (fun o => w o.1 * RP L {eta0Bin M L with piLev := pi} i o +
          v o.1 * indicator (o.2.1 ∈ L.S i) / pi a o.1) := by
      funext o
      simp only [RP, if_neg (show i ≠ 0 by omega), positiveValue, dif_pos hi, v, a]
      ring
    constructor
    · change Integrable (fun o => w o.1 * RP L _ i o) _
      rw [hid]
      exact ir.fun_add iz
    · have hmean : (fun o : Obs X Z => v o.1 * (∑ z ∈ L.S i, instProb M z o.1) / pi a o.1) =
          (fun o : Obs X Z => w o.1 * positiveValue (eta0Bin M L).piLev i o.1 *
            (positiveValue (eta0Bin M L).P1 i o.1 - positiveValue P i o.1) /
              positiveValue pi i o.1) := by
        funext o
        simp only [positiveValue, dif_pos hi, eta0Bin, levelSetProb, v, a]
        ring
      constructor
      · rwa [← hmean]
      · rw [hid, integral_add ir iz, zr, zero_add, hz, hmean]
  · have hz : ∀ o : Obs X Z, w o.1 *
        RP L {eta0Bin M L with P1 := P, piLev := pi} i o = 0 := by
      intro o
      by_cases hi0 : i = 0 <;> simp [RP, hi0, positiveValue, hi]
    simp only [hz, positiveValue, dif_neg hi, mul_zero, sub_self, zero_div, integral_zero]
    exact ⟨integrable_zero _ _ _, integrable_zero _ _ _, True.intro⟩

-- The signed assignment residual uses the true gamma, regardless of its fitted
-- value. Centering it first leaves exactly the two fitted outcome residual means.
-- @node: population_binary_full_joint_fitted_mean
/-- Under [baseline overlap](hyp:hov), [an almost surely binary outcome](hyp:hy),
and [admissibility of the true binary nuisance](hyp:he), suppose [the fitted
outcome regressions](hyp:hP) and [assignment probabilities](hyp:hpi) are
measurable, [the clipping constant is positive](hyp:hc), [the outcome bound is
nonnegative](hyp:hD), [the fitted assignment probabilities are almost surely
bounded below by the clipping constant](hyp:hclip), [the fitted outcome
regressions are almost surely bounded by the outcome bound](hyp:hPB), and [the
fitted instrument weight at the chosen level is measurable](hyp:hg) and [almost
surely bounded by the given weight bound](hyp:hgB). Then [the full binary product
score with these fitted components is integrable, and its mean equals the mean
of the fitted full outcome contrast times the true instrument weight, plus the
fitted instrument weight times the upper-level true assignment probability and
true-minus-fitted outcome regression divided by the fitted assignment
probability, minus the corresponding lower-level term](goal). -/
lemma population_binary_full_joint_fitted_mean
    (L : LevelData Z X) (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (hy : OutcomeBinaryAE M) (he : BinAdmissible M L (eta0Bin M L))
    (P pi : PositiveIndex L.K → X → ℝ) (g : Fin L.K → X → ℝ)
    (hP : ∀ a, Measurable (P a)) (hpi : ∀ a, Measurable (pi a))
    (c D : ℝ) (hc : 0 < c) (hD : 0 ≤ D)
    (hclip : ∀ a, ∀ᵐ x ∂xLaw M, c ≤ pi a x)
    (hPB : ∀ a, ∀ᵐ x ∂xLaw M, ‖P a x‖ ≤ D)
    (k : Fin L.K) (hg : Measurable (g k)) (B : ℝ)
    (hgB : ∀ᵐ x ∂xLaw M, ‖g k x‖ ≤ B) :
    let e := {eta0Bin M L with P1 := P, piLev := pi, gammaFull := g}
    Integrable (psiFullProdBin L e k) (observationLaw M) ∧
    (∫ o, psiFullProdBin L e k o ∂observationLaw M) =
      ∫ o : Obs X Z, binFullJ L e k o.1 * (eta0Bin M L).gammaFull k o.1 +
        g k o.1 * positiveValue (eta0Bin M L).piLev (k+1) o.1 *
          (positiveValue (eta0Bin M L).P1 (k+1) o.1 - positiveValue P (k+1) o.1) /
            positiveValue pi (k+1) o.1 -
        g k o.1 * positiveValue (eta0Bin M L).piLev k o.1 *
          (positiveValue (eta0Bin M L).P1 k o.1 - positiveValue P k o.1) /
            positiveValue pi k o.1 ∂observationLaw M := by
  dsimp only
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  let e : NuisanceBin L := {eta0Bin M L with P1 := P, piLev := pi, gammaFull := g}
  have hpos i := binary_positive_regression_direction_regular M L P D hD
    (fun a => ⟨hP a, hPB a⟩) i
  have hJ : Measurable (binFullJ L e k) := (hpos (k+1)).1.sub (hpos k).1
  have hJB : ∀ᵐ x ∂xLaw M, ‖binFullJ L e k x‖ ≤ 2*D := by
    filter_upwards [(hpos (k+1)).2, (hpos k).2] with x hx hy
    exact (norm_sub_le _ _).trans (by linarith)
  let J := binFullJ L e k
  have iA := population_assignment_residual_integrable M (higherPolicy L k) J hJ (2*D) hJB
  have iB := population_assignment_residual_integrable M (higherBaseline L k) J hJ (2*D) hJB
  have z := population_signed_assignment_weighted_integral_zero M
    (higherPolicy L k) (higherBaseline L k) J hJ iA iB
  have hgamma : ∀ x, (eta0Bin M L).gammaFull k x =
      (∑ z ∈ higherPolicy L k, instProb M z x) -
        ∑ z ∈ higherBaseline L k, instProb M z x := by
    intro x
    rfl
  have hg0 : Measurable ((eta0Bin M L).gammaFull k) := he.2.2.2.2.2.2.2.2.2.2.1 k
  have hg0B : ∀ᵐ x ∂xLaw M, ‖(eta0Bin M L).gammaFull k x‖ ≤ 1 := by
    filter_upwards [he.2.2.2.2.2.2.2.2.2.1 k] with x hx
    simpa only [Real.norm_eq_abs, abs_le, mem_Icc] using hx
  have iJ : Integrable (fun o : Obs X Z => J o.1) (observationLaw M) :=
    Integrable.of_bound (hJ.comp measurable_fst).aestronglyMeasurable (2*D)
      (observationLaw_covariate_ae M _ hJB)
  have iJg := iJ.mul_bdd (hg0.comp measurable_fst).aestronglyMeasurable
    (observationLaw_covariate_ae M _ hg0B)
  change Integrable (fun o : Obs X Z => J o.1 * (eta0Bin M L).gammaFull k o.1)
    (observationLaw M) at iJg
  let r : Obs X Z → ℝ := fun o => J o.1 *
    (indicator (o.2.1 ∈ higherPolicy L k) - indicator (o.2.1 ∈ higherBaseline L k) -
      (eta0Bin M L).gammaFull k o.1)
  have ir : Integrable r (observationLaw M) := by
    convert! iA.sub' iB using 1
    funext o
    dsimp only [r]
    rw [hgamma]
    ring
  have zr : (∫ o, r o ∂observationLaw M) = 0 := by
    simpa only [r, hgamma] using z
  have ip i := population_RP_joint_fitted_weighted_mean M L cpi hov hy he
    P pi hP hpi c D hc hclip hPB (g k) hg B hgB i
  have hid : (fun o => psiFullProdBin L e k o) =
      (fun o => J o.1 * (eta0Bin M L).gammaFull k o.1 + r o +
        g k o.1 * RP L {eta0Bin M L with P1 := P, piLev := pi} (k+1) o -
        g k o.1 * RP L {eta0Bin M L with P1 := P, piLev := pi} k o) := by
    funext o
    simp only [psiFullProdBin, fullValue, dif_pos k.isLt, e, J, r, RP]
    ring
  constructor
  · change Integrable (fun o => psiFullProdBin L e k o) _
    rw [hid]
    exact ((iJg.fun_add ir).fun_add (ip (k+1)).1).sub' (ip k).1
  · change (∫ o, psiFullProdBin L e k o ∂observationLaw M) = _
    rw [hid, integral_sub ((iJg.fun_add ir).fun_add (ip (k+1)).1) (ip k).1,
      integral_add (iJg.fun_add ir) (ip (k+1)).1, integral_add iJg ir,
      zr, add_zero, (ip (k+1)).2.2, (ip k).2.2,
      ← integral_add iJg (ip (k+1)).2.1,
      ← integral_sub (iJg.fun_add (ip (k+1)).2.1) (ip k).2.1]

-- This is the actual affine path in the whole nuisance vector. The other
-- nuisance fields do not enter the full score, and remain free to vary.
-- @node: population_binary_full_joint_path_local_mean_of_admissible
/-- Under [baseline overlap](hyp:hov) and [an almost surely binary
outcome](hyp:hy), for [an admissible joint binary nuisance direction at the
truth](hyp:hd), [at all sufficiently small perturbations the full product score
at the chosen level is integrable, and its mean equals the mean of the perturbed
full outcome contrast times the true instrument weight, plus the perturbed
instrument weight times the upper-level true assignment probability and
true-minus-perturbed outcome regression divided by the perturbed assignment
probability, minus the corresponding lower-level term](goal). -/
lemma population_binary_full_joint_path_local_mean_of_admissible
    (L : LevelData Z X) (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (hy : OutcomeBinaryAE M) (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del)) (k : Fin L.K) :
    ∀ᶠ t : ℝ in nhds 0,
      Integrable (psiFullProdBin L (eta0Bin M L + t • del) k) (observationLaw M) ∧
      (∫ o, psiFullProdBin L (eta0Bin M L + t • del) k o ∂observationLaw M) =
        ∫ o : Obs X Z,
          binFullJ L (eta0Bin M L + t • del) k o.1 * (eta0Bin M L).gammaFull k o.1 +
          (eta0Bin M L + t • del).gammaFull k o.1 *
            positiveValue (eta0Bin M L).piLev (k+1) o.1 *
            (positiveValue (eta0Bin M L).P1 (k+1) o.1 -
              positiveValue (eta0Bin M L + t • del).P1 (k+1) o.1) /
                positiveValue (eta0Bin M L + t • del).piLev (k+1) o.1 -
          (eta0Bin M L + t • del).gammaFull k o.1 *
            positiveValue (eta0Bin M L).piLev k o.1 *
            (positiveValue (eta0Bin M L).P1 k o.1 -
              positiveValue (eta0Bin M L + t • del).P1 k o.1) /
                positiveValue (eta0Bin M L + t • del).piLev k o.1 ∂observationLaw M := by
  have he := binary_admissible_direction_origin M L (eta0Bin M L) del hd
  obtain ⟨C, hC, hr⟩ := binary_assignment_denominator_direction_regular M L
    (eta0Bin M L) del hd
  obtain ⟨R, hR, hreg⟩ := binary_regression_direction_regular M L (eta0Bin M L) del hd
  obtain ⟨G, hG, hgr⟩ := binary_full_weight_direction_regular M L (eta0Bin M L) del hd
  have hcpi := hov.1
  have radius : 0 < cpi / (2 * (C+1)) := by positivity
  filter_upwards [continuousAt_id.abs.eventually_lt_const (by simpa using radius)] with t ht
  let P := (eta0Bin M L + t • del).P1
  let pi := (eta0Bin M L + t • del).piLev
  let g := (eta0Bin M L + t • del).gammaFull
  have hP a : Measurable (P a) :=
    ((he.2.2.2.1 a).2.1).add ((hreg a).1.const_mul t)
  have hpi a : Measurable (pi a) :=
    ((he.2.2.2.1 a).2.2).add ((hr a).1.const_mul t)
  have hp : ∀ a, ∀ᵐ x ∂xLaw M, cpi / 2 ≤ pi a x := by
    intro a
    filter_upwards [(hr a).2] with x hx
    have htrue : cpi ≤ (eta0Bin M L).piLev a x := hov.2 x a.val a.property.1 a.property.2
    have hb : |t * del.piLev a x| ≤ |t| * C := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using hx) (abs_nonneg t)
    have ht' : |t| * (2 * (C+1)) < cpi := (lt_div_iff₀ (by positivity)).mp ht
    have hlo := neg_abs_le (t * del.piLev a x)
    change cpi / 2 ≤ (eta0Bin M L).piLev a x + t * del.piLev a x
    nlinarith [abs_nonneg t]
  have hPB : ∀ a, ∀ᵐ x ∂xLaw M, ‖P a x‖ ≤ 1 + |t| * R := by
    intro a
    filter_upwards [he.2.2.1 a, (hreg a).2] with x hx hdx
    have htrue : ‖(eta0Bin M L).P1 a x‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg hx.2.1.1]
      exact hx.2.1.2
    change ‖(eta0Bin M L).P1 a x + t * del.P1 a x‖ ≤ _
    exact (norm_add_le _ _).trans (add_le_add htrue (by
      rw [norm_mul, Real.norm_eq_abs t]
      exact mul_le_mul_of_nonneg_left hdx (abs_nonneg t)))
  have hg : Measurable (g k) :=
    (he.2.2.2.2.2.2.2.2.2.2.1 k).add ((hgr k).1.const_mul t)
  have hgB : ∀ᵐ x ∂xLaw M, ‖g k x‖ ≤ 1 + |t| * G := by
    filter_upwards [he.2.2.2.2.2.2.2.2.2.1 k, (hgr k).2] with x hx hdx
    have htrue : ‖(eta0Bin M L).gammaFull k x‖ ≤ 1 := by
      simpa only [Real.norm_eq_abs, abs_le, mem_Icc] using hx
    change ‖(eta0Bin M L).gammaFull k x + t * del.gammaFull k x‖ ≤ _
    exact (norm_add_le _ _).trans (add_le_add htrue (by
      rw [norm_mul, Real.norm_eq_abs t]
      exact mul_le_mul_of_nonneg_left hdx (abs_nonneg t)))
  have hmean := population_binary_full_joint_fitted_mean M L cpi hov hy he P pi g hP hpi
    (cpi / 2) (1 + |t| * R) (by positivity) (by positivity) hp hPB k hg (1 + |t| * G) hgB
  have hscore : psiFullProdBin L {eta0Bin M L with P1 := P, piLev := pi, gammaFull := g} k =
      psiFullProdBin L (eta0Bin M L + t • del) k := rfl
  simpa only [hscore, binFullJ, P, pi, g] using hmean

end Papers.TbsPrteOptimalTransport

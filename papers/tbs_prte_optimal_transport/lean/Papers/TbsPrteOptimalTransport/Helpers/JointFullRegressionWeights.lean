module
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationRegressionDirections
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationBinaryWeightAssembly
public import Papers.TbsPrteOptimalTransport.Helpers.BinaryRegressionOrthogonality
/-! Simultaneous regression and signed product-weight directions for full binary intervals. -/
public section
set_option linter.style.haveILetI false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set
open scoped Classical

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- Overlap and bounded covariate weights also control the uncentered assignment term.
-- @node: population_weighted_normalized_assignment_integrable
/-- If [the overlap constant is positive](hyp:hc), [the conditional probability of
the selected instrument set is everywhere at least that constant](hyp:hp), and
[the covariate weight is measurable](hyp:hw) and [almost surely bounded in absolute
value by a fixed constant](hyp:hb), then [the weight times the set-membership
indicator divided by that conditional probability is integrable under the
observation law](goal). -/
lemma population_weighted_normalized_assignment_integrable (C : Finset Z) (c : ℝ)
    (hc : 0 < c) (hp : ∀ x, c ≤ ∑ z ∈ C, instProb M z x)
    (w : X → ℝ) (hw : Measurable w) (B : ℝ)
    (hb : ∀ᵐ x ∂xLaw M, ‖w x‖ ≤ B) :
    Integrable (fun o : Obs X Z => w o.1 *
      (indicator (o.2.1 ∈ C) / (∑ z ∈ C, instProb M z o.1))) (observationLaw M) := by
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  have iw : Integrable (fun o : Obs X Z => w o.1) (observationLaw M) := by
    apply Integrable.of_bound (hw.comp measurable_fst).aestronglyMeasurable B
    exact observationLaw_covariate_ae M _ hb
  have iz := population_normalized_assignment_integrable M C c hc hp w hw B hb
  convert iw.sub' iz using 1
  funext o
  ring

-- The regression-only path is affine even at the structural zero boundary.
-- @node: binary_full_product_regression_affine_path
/-- [Perturbing only the treated-success regressions along an affine path changes
the full-interval binary product score by the path parameter times the adjacent
regression-direction difference multiplied by the policy-minus-baseline membership
contrast, minus the signed full-interval weight times the adjacent difference of
inverse-probability-weighted regression directions](goal). -/
lemma binary_full_product_regression_affine_path (L : LevelData Z X) (e : NuisanceBin L)
    (d : PositiveIndex L.K → X → ℝ) (k : ℕ) (o : Obs X Z) (t : ℝ) :
    psiFullProdBin L {e with P1 := fun a x => e.P1 a x + t * d a x} k o =
      psiFullProdBin L e k o + t *
        ((positiveValue d (k+1) o.1 - positiveValue d k o.1) *
          (indicator (o.2.1 ∈ higherPolicy L k) - indicator (o.2.1 ∈ higherBaseline L k)) -
        fullValue e.gammaFull k o.1 *
          (indicator (o.2.1 ∈ L.S (k+1)) / positiveValue e.piLev (k+1) o.1 *
            positiveValue d (k+1) o.1 -
          indicator (o.2.1 ∈ L.S k) / positiveValue e.piLev k o.1 * positiveValue d k o.1)) := by
  have hJ : binFullJ L {e with P1 := fun a x => e.P1 a x + t * d a x} k o.1 =
      binFullJ L e k o.1 + t * (positiveValue d (k+1) o.1 - positiveValue d k o.1) := by
    simp only [binFullJ, positiveValue]
    split_ifs <;> ring
  simp only [psiFullProdBin, hJ, binary_RP_regression_path]
  ring

-- The cross term is displayed explicitly; separate partial derivatives alone
-- would not justify orthogonality along the simultaneous path.
-- @node: binary_full_product_joint_regression_weight_path
/-- [Perturbing both the treated-success regressions and the signed full-interval
weight gives the regression-only score plus the path parameter times the weight
direction and the original adjacent residual difference, minus the squared path
parameter times the weight direction and the adjacent difference of
inverse-probability-weighted regression directions](goal). -/
lemma binary_full_product_joint_regression_weight_path (L : LevelData Z X)
    (e : NuisanceBin L) (d : PositiveIndex L.K → X → ℝ)
    (dg : Fin L.K → X → ℝ) (k : ℕ) (o : Obs X Z) (t : ℝ) :
    psiFullProdBin L {e with
      P1 := fun a x => e.P1 a x + t * d a x
      gammaFull := fun a x => e.gammaFull a x + t * dg a x} k o =
      psiFullProdBin L {e with P1 := fun a x => e.P1 a x + t * d a x} k o +
      t * (fullValue dg k o.1 * (RP L e (k+1) o - RP L e k o)) -
      t ^ 2 * (fullValue dg k o.1 *
        (indicator (o.2.1 ∈ L.S (k+1)) / positiveValue e.piLev (k+1) o.1 *
          positiveValue d (k+1) o.1 -
        indicator (o.2.1 ∈ L.S k) / positiveValue e.piLev k o.1 * positiveValue d k o.1)) := by
  let et : NuisanceBin L := {e with P1 := fun a x => e.P1 a x + t * d a x}
  change psiFullProdBin L {et with
    gammaFull := fun a x => et.gammaFull a x + t * dg a x} k o = _
  rw [binary_full_product_weight_path L et dg k o t]
  dsimp only [et]
  rw [binary_RP_regression_path, binary_RP_regression_path]
  ring

-- @node: population_binary_regression_assignment_integrable_of_admissible
/-- Under [a positive uniform lower bound on baseline-class probabilities](hyp:hov),
if [the nuisance direction is admissible at the true binary nuisance functions](hyp:hd),
then [the baseline-class membership indicator times the corresponding regression
direction, divided by the true class probability, is integrable for every level
under the observation law](goal). -/
lemma population_binary_regression_assignment_integrable_of_admissible
    (L : LevelData Z X) (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del)) (i : ℕ) :
    Integrable (fun o : Obs X Z => indicator (o.2.1 ∈ L.S i) /
      positiveValue (eta0Bin M L).piLev i o.1 * positiveValue del.P1 i o.1)
      (observationLaw M) := by
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  obtain ⟨C, hC, hr⟩ := binary_regression_direction_regular M L (eta0Bin M L) del hd
  obtain ⟨hm, hb⟩ := binary_positive_regression_direction_regular M L del.P1 C hC hr i
  by_cases hi : 1 ≤ i ∧ i ≤ L.K
  · have hpdef : ∀ x, positiveValue (eta0Bin M L).piLev i x =
        ∑ z ∈ L.S i, instProb M z x := by
      intro x
      simp only [positiveValue, dif_pos hi, eta0Bin, levelSetProb]
    simp_rw [hpdef]
    simpa only [mul_comm] using population_weighted_normalized_assignment_integrable M
      (L.S i) cpi hov.1 (fun x => hov.2 x i hi.1 hi.2) _ hm C hb
  · simp only [positiveValue, dif_neg hi, mul_zero]
    exact integrable_const 0

-- Integrability is derived for every affine regression point, even outside
-- the admissible neighborhood, from the bounded direction and fixed denominators.
-- @node: population_binary_full_regression_path_integrable_of_admissible
/-- Under [positive uniform baseline overlap](hyp:hov) and [almost surely binary
outcomes](hyp:hy), if [the nuisance direction is admissible at the true binary
nuisance functions](hyp:hd), then [each valid full-interval product score is
integrable at every point on the affine path that perturbs only the treated-success
regressions](goal). -/
lemma population_binary_full_regression_path_integrable_of_admissible
    (L : LevelData Z X) (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (hy : OutcomeBinaryAE M) (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del))
    (k : Fin L.K) (t : ℝ) :
    Integrable (psiFullProdBin L {eta0Bin M L with
      P1 := fun a x => (eta0Bin M L).P1 a x + t * del.P1 a x} k) (observationLaw M) := by
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  have he := binary_admissible_direction_origin M L (eta0Bin M L) del hd
  have ibase := population_binary_full_product_integrable_of_overlap M L cpi hov hy he k
  obtain ⟨C, hC, hr⟩ := binary_regression_direction_regular M L (eta0Bin M L) del hd
  have hdpos i := binary_positive_regression_direction_regular M L del.P1 C hC hr i
  have idpos (i : ℕ) : Integrable (fun o : Obs X Z => positiveValue del.P1 i o.1)
      (observationLaw M) := by
    apply Integrable.of_bound ((hdpos i).1.comp measurable_fst).aestronglyMeasurable C
    exact observationLaw_covariate_ae M _ (hdpos i).2
  let a : Obs X Z → ℝ := fun o => indicator (o.2.1 ∈ higherPolicy L k) -
    indicator (o.2.1 ∈ higherBaseline L k)
  have ha : Measurable a := by
    dsimp only [a]
    unfold indicator
    exact (Measurable.ite ((higherPolicy L k).finite_toSet.measurableSet.preimage
      measurable_snd.fst) measurable_const measurable_const).sub
      (Measurable.ite ((higherBaseline L k).finite_toSet.measurableSet.preimage
        measurable_snd.fst) measurable_const measurable_const)
  have hab : ∀ᵐ o ∂observationLaw M, ‖a o‖ ≤ 1 := by
    apply Filter.Eventually.of_forall
    intro o
    simp only [a, indicator]
    split_ifs <;> norm_num
  have iA := ((idpos (k+1)).sub' (idpos k)).mul_bdd ha.aestronglyMeasurable hab
  have hg : Measurable (gammaFull M L k) := he.2.2.2.2.2.2.2.2.2.2.1 k
  have hgb : ∀ᵐ x ∂xLaw M, ‖gammaFull M L k x‖ ≤ 1 := by
    filter_upwards [he.2.2.2.2.2.2.2.2.2.1 k] with x hx
    simpa only [eta0Bin, Set.mem_Icc, Real.norm_eq_abs, abs_le] using hx
  have ip i := population_binary_regression_assignment_integrable_of_admissible M
    L cpi hov del hd i
  have iR := ((ip (k+1)).sub' (ip k)).bdd_mul
    (hg.comp measurable_fst).aestronglyMeasurable (observationLaw_covariate_ae M _ hgb)
  change Integrable (fun o => psiFullProdBin L _ k o) _
  simp_rw [binary_full_product_regression_affine_path]
  simpa only [fullValue, dif_pos k.isLt, eta0Bin, a, Function.comp_apply] using
    ibase.fun_add ((iA.sub' iR).const_mul t)

-- The two first-order contributions are centered by the existing population
-- proofs. Only a quadratic product remains, so its derivative at zero vanishes.
-- @node: population_binary_full_joint_regression_weight_orthogonality_of_admissible
/-- Under [positive uniform baseline overlap](hyp:hov) and [almost surely binary
outcomes](hyp:hy), if [the nuisance direction is admissible at the true binary
nuisance functions](hyp:hd), then [the population mean of each valid full-interval
product score has derivative zero at the origin along the simultaneous affine
path in treated-success regressions and signed full-interval weights](goal). -/
lemma population_binary_full_joint_regression_weight_orthogonality_of_admissible
    (L : LevelData Z X) (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (hy : OutcomeBinaryAE M) (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del)) (k : Fin L.K) :
    HasDerivAt (fun t : ℝ => ∫ o, psiFullProdBin L {eta0Bin M L with
      P1 := fun a x => (eta0Bin M L).P1 a x + t * del.P1 a x
      gammaFull := fun a x => (eta0Bin M L).gammaFull a x + t * del.gammaFull a x}
      k o ∂observationLaw M) 0 0 := by
  have he := binary_admissible_direction_origin M L (eta0Bin M L) del hd
  obtain ⟨C, hC, hr⟩ := binary_full_weight_direction_regular M L (eta0Bin M L) del hd
  obtain ⟨hm, hb⟩ := hr k
  have ip i := population_binary_weighted_RP_integrable M L cpi hov hy he i
    (del.gammaFull k) hm C hb
  let r : Obs X Z → ℝ := fun o => del.gammaFull k o.1 *
    (RP L (eta0Bin M L) (k+1) o - RP L (eta0Bin M L) k o)
  have ir : Integrable r (observationLaw M) := by
    simpa only [r, mul_sub] using (ip (k+1)).sub' (ip k)
  have zr : (∫ o, r o ∂observationLaw M) = 0 := by
    simp only [r, mul_sub]
    rw [integral_sub (ip (k+1)) (ip k),
      population_RP_weighted_integral_zero M L (k+1) _ hm (ip (k+1)),
      population_RP_weighted_integral_zero M L k _ hm (ip k), sub_self]
  let q : Obs X Z → ℝ := fun o => del.gammaFull k o.1 *
    (indicator (o.2.1 ∈ L.S (k+1)) / positiveValue (eta0Bin M L).piLev (k+1) o.1 *
      positiveValue del.P1 (k+1) o.1 -
    indicator (o.2.1 ∈ L.S k) / positiveValue (eta0Bin M L).piLev k o.1 *
      positiveValue del.P1 k o.1)
  have ia i := population_binary_regression_assignment_integrable_of_admissible M
    L cpi hov del hd i
  have iq : Integrable q (observationLaw M) :=
    ((ia (k+1)).sub' (ia k)).bdd_mul (hm.comp measurable_fst).aestronglyMeasurable
      (observationLaw_covariate_ae M _ hb)
  have heq : (fun t : ℝ => ∫ o, psiFullProdBin L {eta0Bin M L with
      P1 := fun a x => (eta0Bin M L).P1 a x + t * del.P1 a x
      gammaFull := fun a x => (eta0Bin M L).gammaFull a x + t * del.gammaFull a x}
      k o ∂observationLaw M) =
      (fun t : ℝ => (∫ o, psiFullProdBin L {eta0Bin M L with
        P1 := fun a x => (eta0Bin M L).P1 a x + t * del.P1 a x} k o
        ∂observationLaw M) - t ^ 2 * (∫ o, q o ∂observationLaw M)) := by
    funext t
    simp_rw [binary_full_product_joint_regression_weight_path,
      fullValue, dif_pos k.isLt]
    change (∫ o, psiFullProdBin L _ k o + t * r o - t ^ 2 * q o
      ∂observationLaw M) = _
    rw [integral_sub
      ((population_binary_full_regression_path_integrable_of_admissible M
        L cpi hov hy del hd k t).fun_add (ir.const_mul t)) (iq.const_mul (t^2)),
      integral_add (population_binary_full_regression_path_integrable_of_admissible M
        L cpi hov hy del hd k t) (ir.const_mul t), integral_const_mul,
      integral_const_mul, zr, mul_zero, add_zero]
  rw [heq]
  have hquad : HasDerivAt (fun t : ℝ => t ^ 2 * (∫ o, q o ∂observationLaw M)) 0 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (∫ o, q o ∂observationLaw M)
  simpa only [sub_zero, Pi.sub_def] using
    (population_binary_full_product_regression_orthogonality_of_admissible M
      L cpi hov hy del hd k).sub hquad

-- @node: population_binary_full_joint_regression_weight_path_integrable
/-- Under [positive uniform baseline overlap](hyp:hov) and [almost surely binary
outcomes](hyp:hy), if [the nuisance direction is admissible at the true binary
nuisance functions](hyp:hd), then [each valid full-interval product score is
integrable at every point on the simultaneous affine path in treated-success
regressions and signed full-interval weights](goal). -/
lemma population_binary_full_joint_regression_weight_path_integrable
    (L : LevelData Z X) (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (hy : OutcomeBinaryAE M) (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del))
    (k : Fin L.K) (t : ℝ) :
    Integrable (psiFullProdBin L {eta0Bin M L with
      P1 := fun a x => (eta0Bin M L).P1 a x + t * del.P1 a x
      gammaFull := fun a x => (eta0Bin M L).gammaFull a x + t * del.gammaFull a x}
      k) (observationLaw M) := by
  have he := binary_admissible_direction_origin M L (eta0Bin M L) del hd
  obtain ⟨C, hC, hr⟩ := binary_full_weight_direction_regular M L (eta0Bin M L) del hd
  obtain ⟨hm, hb⟩ := hr k
  have ip i := population_binary_weighted_RP_integrable M L cpi hov hy he i
    (del.gammaFull k) hm C hb
  have ir : Integrable (fun o : Obs X Z => del.gammaFull k o.1 *
      (RP L (eta0Bin M L) (k+1) o - RP L (eta0Bin M L) k o)) (observationLaw M) := by
    simpa only [mul_sub] using (ip (k+1)).sub' (ip k)
  have ia i := population_binary_regression_assignment_integrable_of_admissible M
    L cpi hov del hd i
  have iq := ((ia (k+1)).sub' (ia k)).bdd_mul
    (hm.comp measurable_fst).aestronglyMeasurable (observationLaw_covariate_ae M _ hb)
  change Integrable (fun o => psiFullProdBin L _ k o) _
  simp_rw [binary_full_product_joint_regression_weight_path,
    fullValue, dif_pos k.isLt]
  simpa only [Function.comp_apply] using
    ((population_binary_full_regression_path_integrable_of_admissible M
      L cpi hov hy del hd k t).fun_add (ir.const_mul t)).sub' (iq.const_mul (t^2))

-- Assembly for the entire full-interval part of the score, with a common
-- simultaneous direction across all positive levels and signed weights.
-- @node: population_binary_full_sum_joint_regression_weight_orthogonality
/-- Under [positive uniform baseline overlap](hyp:hov) and [almost surely binary
outcomes](hyp:hy), if [the nuisance direction is admissible at the true binary
nuisance functions](hyp:hd), then [the population mean of the sum of all full-interval
product scores has derivative zero at the origin along the simultaneous affine
path in treated-success regressions and signed full-interval weights](goal). -/
lemma population_binary_full_sum_joint_regression_weight_orthogonality
    (L : LevelData Z X) (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (hy : OutcomeBinaryAE M) (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del)) :
    HasDerivAt (fun t : ℝ => ∫ o,
      ∑ k ∈ Finset.range L.K, psiFullProdBin L {eta0Bin M L with
        P1 := fun a x => (eta0Bin M L).P1 a x + t * del.P1 a x
        gammaFull := fun a x => (eta0Bin M L).gammaFull a x + t * del.gammaFull a x}
        k o ∂observationLaw M) 0 0 := by
  let et : ℝ → NuisanceBin L := fun t => {eta0Bin M L with
    P1 := fun a x => (eta0Bin M L).P1 a x + t * del.P1 a x
    gammaFull := fun a x => (eta0Bin M L).gammaFull a x + t * del.gammaFull a x}
  have hi (t : ℝ) : ∀ k ∈ Finset.range L.K,
      Integrable (psiFullProdBin L (et t) k) (observationLaw M) := by
    intro k hk
    exact population_binary_full_joint_regression_weight_path_integrable M
      L cpi hov hy del hd ⟨k, Finset.mem_range.mp hk⟩ t
  have hdv : ∀ k ∈ Finset.range L.K,
      HasDerivAt (fun t : ℝ => ∫ o, psiFullProdBin L (et t) k o
        ∂observationLaw M) 0 0 := by
    intro k hk
    exact population_binary_full_joint_regression_weight_orthogonality_of_admissible M
      L cpi hov hy del hd ⟨k, Finset.mem_range.mp hk⟩
  have hs := HasDerivAt.fun_sum hdv
  have heq : (fun t : ℝ => ∫ o, ∑ k ∈ Finset.range L.K,
      psiFullProdBin L (et t) k o ∂observationLaw M) =
      (fun t : ℝ => ∑ k ∈ Finset.range L.K,
        ∫ o, psiFullProdBin L (et t) k o ∂observationLaw M) := by
    funext t
    exact integral_finsetSum _ (hi t)
  change HasDerivAt (fun t : ℝ => ∫ o, ∑ k ∈ Finset.range L.K,
    psiFullProdBin L (et t) k o ∂observationLaw M) 0 0
  rw [heq]
  simpa only [Finset.sum_const_zero] using hs

-- Finite conditional moments compute the fitted residual even when the
-- regression and its denominator move together.
-- @node: binary_RP_finite_conditional_mean
/-- If [the instrument weights within the baseline class sum to the reference
class probability](hyp:hmass) and [their weighted responses sum to that probability
times the reference treated-success regression](hyp:hmoment), then [the weighted
sum of fitted treated-success residuals, evaluated with treatment equal to one,
equals the reference class probability times the reference-minus-fitted regression
difference divided by the fitted class probability](goal). -/
lemma binary_RP_finite_conditional_mean (L : LevelData Z X)
    (e e0 : NuisanceBin L) (i : ℕ) (x : X) (pi r : Z → ℝ)
    (hmass : ∑ z ∈ L.S i, pi z = positiveValue e0.piLev i x)
    (hmoment : ∑ z ∈ L.S i, pi z * r z =
      positiveValue e0.piLev i x * positiveValue e0.P1 i x) :
    (∑ z, pi z * RP L e i (x, z, 1, r z)) =
      positiveValue e0.piLev i x *
        (positiveValue e0.P1 i x - positiveValue e.P1 i x) /
          positiveValue e.piLev i x := by
  by_cases hi : i = 0
  · subst i
    simp [RP, positiveValue]
  · simp only [RP, if_neg hi, mul_one]
    have hid : ∀ z, pi z *
        (indicator (z ∈ L.S i) / positiveValue e.piLev i x *
          (r z - positiveValue e.P1 i x)) =
        if z ∈ L.S i then
          (pi z * r z - pi z * positiveValue e.P1 i x) /
            positiveValue e.piLev i x else 0 := by
      intro z
      by_cases hz : z ∈ L.S i <;> simp [indicator, hz] <;> ring
    simp_rw [hid]
    rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.sum_div, Finset.sum_sub_distrib,
      ← Finset.sum_mul, hmoment, hmass]
    ring

-- The product's plug-in and signed assignment residual combine before any
-- differentiation, leaving the outcome residuals as the only fitted corrections.
-- @node: binary_full_product_finite_conditional_mean
/-- If [the instrument weights reproduce the reference class probabilities at both
adjacent levels](hyp:hmass), [their response moments reproduce those probabilities
times the reference treated-success regressions](hyp:hmoment), and [their
policy-minus-baseline membership contrast equals the reference signed full-interval
weight](hyp:hgamma), then [the weighted full-interval product score, evaluated with
treatment equal to one, equals the fitted regression increment times the reference
signed weight plus the fitted signed weight times the adjacent difference of
reference-probability-weighted regression errors divided by fitted probabilities](goal). -/
lemma binary_full_product_finite_conditional_mean (L : LevelData Z X)
    (e e0 : NuisanceBin L) (k : ℕ) (x : X) (pi r : Z → ℝ)
    (hmass : ∀ i ∈ ({k, k+1} : Finset ℕ),
      ∑ z ∈ L.S i, pi z = positiveValue e0.piLev i x)
    (hmoment : ∀ i ∈ ({k, k+1} : Finset ℕ),
      ∑ z ∈ L.S i, pi z * r z =
        positiveValue e0.piLev i x * positiveValue e0.P1 i x)
    (hgamma : ∑ z, pi z * (indicator (z ∈ higherPolicy L k) -
      indicator (z ∈ higherBaseline L k)) = fullValue e0.gammaFull k x) :
    (∑ z, pi z * psiFullProdBin L e k (x, z, 1, r z)) =
      binFullJ L e k x * fullValue e0.gammaFull k x +
      fullValue e.gammaFull k x *
        (positiveValue e0.piLev (k+1) x *
          (positiveValue e0.P1 (k+1) x - positiveValue e.P1 (k+1) x) /
            positiveValue e.piLev (k+1) x -
        positiveValue e0.piLev k x *
          (positiveValue e0.P1 k x - positiveValue e.P1 k x) /
            positiveValue e.piLev k x) := by
  have hid : ∀ z, pi z * psiFullProdBin L e k (x, z, 1, r z) =
      binFullJ L e k x * (pi z * (indicator (z ∈ higherPolicy L k) -
        indicator (z ∈ higherBaseline L k))) +
      fullValue e.gammaFull k x *
        (pi z * RP L e (k+1) (x, z, 1, r z) -
          pi z * RP L e k (x, z, 1, r z)) := by
    intro z
    simp only [psiFullProdBin]
    ring
  simp_rw [hid]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_sub_distrib, hgamma,
    binary_RP_finite_conditional_mean L e e0 (k+1) x pi r
      (hmass _ (by simp)) (hmoment _ (by simp)),
    binary_RP_finite_conditional_mean L e e0 k x pi r
      (hmass _ (by simp)) (hmoment _ (by simp))]

-- At the origin the residual numerator is zero. Thus the denominator's
-- derivative disappears, while the regression derivative is exactly canceled.
-- @node: binary_full_residual_joint_path_derivative
/-- If [the baseline-class probability is nonzero whenever the level is a valid
positive level](hyp:hpi), then [the reference class probability times the
reference-minus-path treated-success regression difference, divided by the path's
class probability, has derivative equal to the negative regression direction at
the origin of the simultaneous affine nuisance path](goal). -/
lemma binary_full_residual_joint_path_derivative (L : LevelData Z X)
    (e del : NuisanceBin L) (i : ℕ) (x : X)
    (hpi : 1 ≤ i ∧ i ≤ L.K → positiveValue e.piLev i x ≠ 0) :
    HasDerivAt (fun t : ℝ => positiveValue e.piLev i x *
      (positiveValue e.P1 i x - positiveValue (e + t • del).P1 i x) /
        positiveValue (e + t • del).piLev i x)
      (-positiveValue del.P1 i x) 0 := by
  by_cases hi : 1 ≤ i ∧ i ≤ L.K
  · simp only [positiveValue, dif_pos hi]
    have hn : HasDerivAt (fun t : ℝ => e.piLev ⟨i, hi⟩ x *
        (e.P1 ⟨i, hi⟩ x - (e.P1 ⟨i, hi⟩ x + t * del.P1 ⟨i, hi⟩ x)))
        (e.piLev ⟨i, hi⟩ x * (-del.P1 ⟨i, hi⟩ x)) 0 := by
      convert! ((hasDerivAt_const 0 (e.P1 ⟨i, hi⟩ x)).sub
        (((hasDerivAt_id (0 : ℝ)).mul_const (del.P1 ⟨i, hi⟩ x)).const_add
          (e.P1 ⟨i, hi⟩ x))).const_mul (e.piLev ⟨i, hi⟩ x) using 1 <;> first | rfl | ring
    have hd := ((hasDerivAt_id (0 : ℝ)).mul_const
      (del.piLev ⟨i, hi⟩ x)).const_add (e.piLev ⟨i, hi⟩ x)
    have hp : e.piLev ⟨i, hi⟩ x ≠ 0 := by
      simpa only [positiveValue, dif_pos hi] using hpi hi
    convert! hn.div hd (by simpa using hp) using 1
    simp only [id_eq, zero_mul, add_zero, sub_self, mul_zero, sub_zero]
    field_simp [hp]
  · simp only [positiveValue, dif_neg hi, zero_mul, sub_self, zero_div, neg_zero]
    exact hasDerivAt_const 0 0

-- This is a simultaneous path in the entire nuisance vector, rather than
-- separate partial derivatives. All unused nuisance fields remain free to vary.
-- @node: binary_full_product_joint_finite_conditional_orthogonality
/-- If [the instrument weights reproduce both adjacent baseline-class probabilities](hyp:hmass),
[their response moments reproduce those probabilities times the corresponding
treated-success regressions](hyp:hmoment), [their policy-minus-baseline membership
contrast reproduces the signed full-interval weight](hyp:hgamma), and [the adjacent
class probabilities are nonzero at valid positive levels](hyp:hpi), then [the
weighted full-interval product score, evaluated with treatment equal to one, has
derivative zero at the origin along any simultaneous affine nuisance direction](goal). -/
lemma binary_full_product_joint_finite_conditional_orthogonality
    (L : LevelData Z X) (e del : NuisanceBin L) (k : Fin L.K)
    (x : X) (pi r : Z → ℝ)
    (hmass : ∀ i ∈ ({k.val, k.val+1} : Finset ℕ),
      ∑ z ∈ L.S i, pi z = positiveValue e.piLev i x)
    (hmoment : ∀ i ∈ ({k.val, k.val+1} : Finset ℕ),
      ∑ z ∈ L.S i, pi z * r z =
        positiveValue e.piLev i x * positiveValue e.P1 i x)
    (hgamma : ∑ z, pi z * (indicator (z ∈ higherPolicy L k) -
      indicator (z ∈ higherBaseline L k)) = fullValue e.gammaFull k x)
    (hpi : ∀ i ∈ ({k.val, k.val+1} : Finset ℕ),
      1 ≤ i ∧ i ≤ L.K → positiveValue e.piLev i x ≠ 0) :
    HasDerivAt (fun t : ℝ =>
      ∑ z, pi z * psiFullProdBin L (e + t • del) k (x, z, 1, r z)) 0 0 := by
  have hp := binary_full_residual_joint_path_derivative L e del (k.val+1) x
    (hpi _ (by simp))
  have hm := binary_full_residual_joint_path_derivative L e del k x
    (hpi _ (by simp))
  have hJ : HasDerivAt (fun t : ℝ => binFullJ L (e + t • del) k x)
      (positiveValue del.P1 (k.val+1) x - positiveValue del.P1 k x) 0 := by
    have hd (i : ℕ) : HasDerivAt (fun t : ℝ => positiveValue (e + t • del).P1 i x)
        (positiveValue del.P1 i x) 0 := by
      unfold positiveValue
      split_ifs
      · change HasDerivAt (fun t : ℝ => e.P1 _ x + t * del.P1 _ x) (del.P1 _ x) 0
        convert! ((hasDerivAt_id (0 : ℝ)).mul_const
          (del.P1 _ x)).const_add (e.P1 _ x) using 1 <;> first | rfl | ring
      · exact hasDerivAt_const 0 0
    exact (hd (k.val+1)).sub (hd k)
  have hg : HasDerivAt (fun t : ℝ => fullValue (e + t • del).gammaFull k x)
      (fullValue del.gammaFull k x) 0 := by
    simp only [fullValue, dif_pos k.isLt]
    change HasDerivAt (fun t : ℝ => e.gammaFull k x + t * del.gammaFull k x)
      (del.gammaFull k x) 0
    convert! ((hasDerivAt_id (0 : ℝ)).mul_const
      (del.gammaFull k x)).const_add (e.gammaFull k x) using 1 <;> first | rfl | ring
  have h := (hJ.mul_const (fullValue e.gammaFull k x)).add (hg.mul (hp.sub hm))
  convert! h using 1
  · funext t
    exact binary_full_product_finite_conditional_mean L (e + t • del) e k x pi r
      hmass hmoment hgamma
  · have he0 : e + (0 : ℝ) • del = e := by
      change (⟨e.prop + 0 • del.prop, e.pLev + 0 • del.pLev,
        e.P1 + 0 • del.P1, e.piLev + 0 • del.piLev, e.tauLev + 0 • del.tauLev,
        e.share + 0 • del.share, e.gammaFull + 0 • del.gammaFull,
        e.gamma + 0 • del.gamma, e.gammaTail + 0 • del.gammaTail⟩ : NuisanceBin L) = e
      simp only [zero_smul, add_zero]
      cases e
      rfl
    simp only [Pi.sub_apply, he0, sub_self, mul_zero, zero_div, zero_add]
    ring

-- The interaction remainder retains all three nuisance errors. This identity
-- supplies a quadratic bound after local overlap bounds the fitted reciprocal.
-- @node: binary_full_joint_scalar_remainder
/-- If [the perturbed probability, pi plus t times dpi, is nonzero](hyp:hpi), then
[the change from m times g in the sum of the perturbed regression times g and
the perturbed weight times pi times the reference-minus-perturbed regression
divided by the perturbed probability equals t squared times dm times
(g times dpi minus dg times pi), divided by the perturbed probability](goal). -/
lemma binary_full_joint_scalar_remainder (m g pi dm dg dpi t : ℝ)
    (hpi : pi + t * dpi ≠ 0) :
    (m + t * dm) * g + (g + t * dg) * pi * (m - (m + t * dm)) /
        (pi + t * dpi) - m * g =
      t ^ 2 * (dm * (g * dpi - dg * pi) / (pi + t * dpi)) := by
  field_simp [hpi]
  <;> ring

-- @node: binary_full_joint_scalar_remainder_bound
/-- If [c is positive](hyp:hc) and [the perturbed probability, pi plus t times dpi,
is at least c](hyp:hpi), then [the absolute change from m times g in the sum of
the perturbed regression times g and the perturbed weight times pi times the
reference-minus-perturbed regression divided by the perturbed probability is at
most t squared times the absolute regression direction, multiplied by the sum
of the absolute weight times the absolute probability direction and the absolute
weight direction times the absolute reference probability, divided by c](goal). -/
lemma binary_full_joint_scalar_remainder_bound (m g pi dm dg dpi t c : ℝ)
    (hc : 0 < c) (hpi : c ≤ pi + t * dpi) :
    |(m + t * dm) * g + (g + t * dg) * pi * (m - (m + t * dm)) /
        (pi + t * dpi) - m * g| ≤
      t ^ 2 * (|dm| * (|g| * |dpi| + |dg| * |pi|) / c) := by
  have hp : 0 < pi + t * dpi := hc.trans_le hpi
  rw [binary_full_joint_scalar_remainder m g pi dm dg dpi t hp.ne',
    abs_mul, abs_of_nonneg (sq_nonneg t), abs_div, abs_mul, abs_of_pos hp]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg t)
  calc
    |dm| * |g * dpi - dg * pi| / (pi + t * dpi) ≤
        |dm| * (|g| * |dpi| + |dg| * |pi|) / (pi + t * dpi) := by
      apply div_le_div_of_nonneg_right _ hp.le
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg dm)
      simpa only [sub_zero, zero_sub, abs_neg, abs_mul] using
        abs_sub_le (g * dpi) 0 (dg * pi)
    _ ≤ |dm| * (|g| * |dpi| + |dg| * |pi|) / c :=
      div_le_div_of_nonneg_left (by positivity) hc hpi

end Papers.TbsPrteOptimalTransport

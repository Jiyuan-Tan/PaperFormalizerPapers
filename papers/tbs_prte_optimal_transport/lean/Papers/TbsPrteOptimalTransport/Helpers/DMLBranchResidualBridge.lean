module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLBranchCoefficientBridge
/-! Binary branch coefficients multiplied by clipped IPW residuals.
Success, treatment, and policy residual rates combine with branch convergence
to control both unweighted fractional correction terms. -/
public section
set_option linter.style.openClassical false
set_option linter.unusedTactic false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: nuisanceRates_fractional_treatment_residual_sq_tendsto_probability_zero_of_branch_convergence
/-- For [a valid policy map](hyp:hphi) with [its specified derivative](hyp:hd)
and [a bounded Lipschitz derivative](hyp:hDerivative), assume [admissible
reference nuisances](hyp:he0), [admissible fitted nuisances](hyp:heh), [a
positive denominator bound](hyp:hc), and [reference and fitted assignment
probabilities bounded below almost everywhere](hyp:hclip). If
[instrument propensities satisfy quarter-rate control](hyp:hrp),
[level propensities satisfy quarter-rate control](hyp:hrlev),
[success regressions satisfy quarter-rate control](hyp:hrP),
[assignment probabilities satisfy quarter-rate control](hyp:hrpi),
[all regular cell shares satisfy quarter-rate control](hyp:hrs), [the residual
index is at most the level count](hyp:hi), and [the integrated squared errors
of the three branch indicators vanish in probability](hyp:hbranch), [the
inverse-weighted treatment residual multiplied by either the boundary indicator
or the dominance-times-active indicator has integrated squared error tending
to zero in probability along even sample sizes](goal). -/
lemma nuisanceRates_fractional_treatment_residual_sq_tendsto_probability_zero_of_branch_convergence
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e0 : NuisanceBin L) (eh : ℕ → A → NuisanceBin L)
    (he0 : BinAdmissible M L e0) (heh : ∀ n a, BinAdmissible M L (eh n a))
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a (i : PositiveIndex L.K), ∀ᵐ x ∂xLaw M,
      c ≤ e0.piLev i x ∧ c ≤ (eh n a).piLev i x)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) e0.prop)
    (hrlev : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrP : FiniteNuisanceRates M μ (fun n a => (eh n a).P1) e0.P1)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) e0.piLev)
    (hrs : ∀ a : RegularIndex L,
      FiniteNuisanceRates M μ (fun n t => (eh n t).share a) (e0.share a))
    (k j i : ℕ) (hi : i ≤ L.K) (b : Bool)
    (hbranch : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o : Obs X Z,
        (Iact phi L (eh (2*(n+1)) a) k j o.1 - Iact phi L e0 k j o.1)^2 +
        (Dbd phi L (eh (2*(n+1)) a) k j o.1 - Dbd phi L e0 k j o.1)^2 +
        (Edom phi L (eh (2*(n+1)) a) k j o.1 - Edom phi L e0 k j o.1)^2
        ∂observationLaw M) atTop (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o : Obs X Z,
        ((if b then Dbd phi L (eh (2*(n+1)) a) k j o.1 else
            Edom phi L (eh (2*(n+1)) a) k j o.1 * Iact phi L (eh (2*(n+1)) a) k j o.1) *
            Rp L (eh (2*(n+1)) a) i o -
          (if b then Dbd phi L e0 k j o.1 else
            Edom phi L e0 k j o.1 * Iact phi L e0 k j o.1) * Rp L e0 i o)^2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  let w := fun (e : NuisanceBin L) (o : Obs X Z) => if b then Dbd phi L e k j o.1 else
    Edom phi L e k j o.1 * Iact phi L e k j o.1
  have hw (e : NuisanceBin L) (he : BinAdmissible M L e) :=
    fitted_fractional_treatment_coefficient_memLp M phi hphi L e he k j b
  apply dml_ae_weighted_residual_sq_tendsto_probability_zero μ (observationLaw M)
    (w e0) (Rp L e0 i) (fun n a => w (eh (2*(n+1)) a))
    (fun n a => Rp L (eh (2*(n+1)) a) i) 1 (1/c)
    (hw e0 he0).1 (by fun_prop) (fun n a => (hw _ (heh (2*(n+1)) a)).1)
    (by
      intro n a
      first | fun_prop | exact (fitted_Rp_memLp M L _ (heh (2*(n+1)) a) c hc
        (fun t => (hclip (2*(n+1)) a t).mono (fun _ hx => hx.2)) i hi).1)
  · exact fun n a => (hw _ (heh (2*(n+1)) a)).sub (hw e0 he0)
  · intro n a
    exact (fitted_Rp_memLp M L _ (heh (2*(n+1)) a) c hc
      (fun t => (hclip _ a t).mono (fun _ hx => hx.2)) i hi).sub
      (fitted_Rp_memLp M L e0 he0 c hc
        (fun t => (hclip (2*(n+1)) a t).mono (fun _ hx => hx.1)) i hi)
  · intro n a
    exact Eventually.of_forall (fun o => by
      dsimp only [w]
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · unfold Edom Iact indicator
        split_ifs <;> norm_num
      · unfold Dbd indicator
        split_ifs <;> norm_num)
  · exact fun n a => fitted_Rp_abs_bound M L e0 he0 c hc
      (fun t => (hclip n a t).mono (fun _ hx => hx.1)) i hi
  · exact nuisanceRates_fractional_treatment_coefficient_sq_tendsto_probability_zero_of_branch_convergence
      M μ phi dphi hphi hd hDerivative L e0 eh he0 heh hrp hrlev hrP hrs k j b hbranch
  · exact nuisanceRates_Rp_sq_tendsto_probability_zero M μ L e0 eh he0 heh
      c hc hclip hrlev hrpi i hi

-- @node: nuisanceRates_fractional_policy_residual_sq_tendsto_probability_zero_of_branch_convergence
/-- Assume [a valid policy map](hyp:hphi), [its specified derivative](hyp:hd),
[a bounded Lipschitz derivative](hyp:hDerivative), [admissible reference
nuisances](hyp:he0), [admissible fitted nuisances](hyp:heh), [a positive
denominator bound](hyp:hc), and [reference and fitted regular-cell
probabilities bounded below almost everywhere](hyp:hclip). With
[quarter-rate control of instrument propensities](hyp:hrp),
[quarter-rate control of level propensities](hyp:hrlev),
[quarter-rate control of success regressions](hyp:hrP),
[quarter-rate control of regular-cell probabilities](hyp:hrt),
[quarter-rate control of all regular cell shares](hyp:hrs), [a level index
at most the level count](hyp:hk), and [vanishing integrated squared branch
indicator errors in probability](hyp:hbranch), [the policy residual multiplied
by either the active indicator or the dominance-times-active indicator has
integrated squared error tending to zero in probability along even sample
sizes](goal). -/
lemma nuisanceRates_fractional_policy_residual_sq_tendsto_probability_zero_of_branch_convergence
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e0 : NuisanceBin L) (eh : ℕ → A → NuisanceBin L)
    (he0 : BinAdmissible M L e0) (heh : ∀ n a, BinAdmissible M L (eh n a))
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a (i : RegularIndex L), ∀ᵐ x ∂xLaw M,
      c ≤ e0.tauLev i x ∧ c ≤ (eh n a).tauLev i x)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) e0.prop)
    (hrlev : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrP : FiniteNuisanceRates M μ (fun n a => (eh n a).P1) e0.P1)
    (hrt : FiniteNuisanceRates M μ (fun n a => (eh n a).tauLev) e0.tauLev)
    (hrs : ∀ a : RegularIndex L,
      FiniteNuisanceRates M μ (fun n t => (eh n t).share a) (e0.share a))
    (k j i : ℕ) (hk : k ≤ L.K) (b : Bool)
    (hbranch : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o : Obs X Z,
        (Iact phi L (eh (2*(n+1)) a) k j o.1 - Iact phi L e0 k j o.1)^2 +
        (Dbd phi L (eh (2*(n+1)) a) k j o.1 - Dbd phi L e0 k j o.1)^2 +
        (Edom phi L (eh (2*(n+1)) a) k j o.1 - Edom phi L e0 k j o.1)^2
        ∂observationLaw M) atTop (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o : Obs X Z,
        ((if b then Iact phi L (eh (2*(n+1)) a) k j o.1 else
            Edom phi L (eh (2*(n+1)) a) k j o.1 * Iact phi L (eh (2*(n+1)) a) k j o.1) *
            RqBin dphi L (eh (2*(n+1)) a) k i o -
          (if b then Iact phi L e0 k j o.1 else
            Edom phi L e0 k j o.1 * Iact phi L e0 k j o.1) * RqBin dphi L e0 k i o)^2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  obtain ⟨B, D, hB, hD, hb⟩ := hDerivative
  have hDerivative : PolicyDerivativeBoundedLipschitz dphi := ⟨B, D, hB, hD, hb⟩
  let w := fun (e : NuisanceBin L) (o : Obs X Z) => if b then Iact phi L e k j o.1 else
    Edom phi L e k j o.1 * Iact phi L e k j o.1
  have hw (e : NuisanceBin L) (he : BinAdmissible M L e) :=
    fitted_fractional_policy_coefficient_memLp M phi hphi L e he k j b
  apply dml_ae_weighted_residual_sq_tendsto_probability_zero μ (observationLaw M)
    (w e0) (RqBin dphi L e0 k i) (fun n a => w (eh (2*(n+1)) a))
    (fun n a => RqBin dphi L (eh (2*(n+1)) a) k i) 1 ((L.T k i).card * B / c)
    (hw e0 he0).1 (by
      first | fun_prop | skip
      unfold RqBin
      split_ifs with hz
      · fun_prop
      · have hr : k ≤ L.K ∧ 1 ≤ i ∧ i ≤ L.l k := ⟨hk, by omega, by omega⟩
        simp only [regularValue, dif_pos hr]
        have hm : AEStronglyMeasurable (fun o : Obs X Z => (e0.tauLev ⟨(k,i), hr⟩ o.1)⁻¹)
            (observationLaw M) := ((he0.2.2.2.2.2.1 ⟨(k,i), hr⟩).1.comp measurable_fst).inv.aestronglyMeasurable
        exact hm.mul (fitted_RqBin_numerator_memLp M phi dphi hphi hd hDerivative L e0 he0 k i).1) (fun n a => (hw _ (heh (2*(n+1)) a)).1)
    (by
      intro n a
      first | fun_prop | exact (fitted_RqBin_memLp M phi dphi hphi hd hDerivative L _ (heh (2*(n+1)) a) c hc
        (fun t => (hclip (2*(n+1)) a t).mono (fun _ hx => hx.2)) k i hk).1)
  · exact fun n a => (hw _ (heh (2*(n+1)) a)).sub (hw e0 he0)
  · intro n a
    exact (fitted_RqBin_memLp M phi dphi hphi hd hDerivative L _ (heh (2*(n+1)) a) c hc
      (fun t => (hclip _ a t).mono (fun _ hx => hx.2)) k i hk).sub
      (fitted_RqBin_memLp M phi dphi hphi hd hDerivative L e0 he0 c hc
        (fun t => (hclip (2*(n+1)) a t).mono (fun _ hx => hx.1)) k i hk)
  · intro n a
    exact Eventually.of_forall (fun o => by
      dsimp only [w]
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · unfold Edom Iact indicator
        split_ifs <;> norm_num
      · unfold Iact indicator
        split_ifs <;> norm_num)
  · exact fun n a => fitted_RqBin_abs_bound M dphi B hB
      (fun z x p hp => (hb z x p p hp hp).1) L e0 he0 c hc
      (fun t => (hclip n a t).mono (fun _ hx => hx.1)) k i hk
  · exact nuisanceRates_fractional_policy_coefficient_sq_tendsto_probability_zero_of_branch_convergence
      M μ phi dphi hphi hd hDerivative L e0 eh he0 heh hrp hrlev hrP hrs k j b hbranch
  · exact nuisanceRates_RqBin_sq_tendsto_probability_zero M μ phi dphi hphi hd hDerivative
      L e0 eh he0 heh c hc hclip hrp hrt k i hk

-- @node: nuisanceRates_regular_regression_correction_sq_tendsto_probability_zero_of_branch_convergence
/-- With [a valid policy map](hyp:hphi), [its specified derivative](hyp:hd),
[a bounded Lipschitz derivative](hyp:hDerivative), [admissible reference
nuisances](hyp:he0), [admissible fitted nuisances](hyp:heh), and [binary outcomes
almost surely](hyp:hy), assume [a positive denominator bound](hyp:hc) and
[reference and fitted assignment probabilities bounded below almost
everywhere](hyp:hclip). If [instrument propensities satisfy quarter-rate
control](hyp:hrp), [level propensities satisfy quarter-rate control](hyp:hrlev),
[success regressions satisfy quarter-rate control](hyp:hrP),
[assignment probabilities satisfy quarter-rate control](hyp:hrpi),
[all regular cell shares satisfy quarter-rate control](hyp:hrs),
[the level index is below the level count](hyp:hk), and
[the integrated sum of squared errors in the three branch indicators vanishes
in probability](hyp:hbranch), [the regular regression correction has integrated
squared error tending to zero in probability along even sample sizes](goal). -/
lemma nuisanceRates_regular_regression_correction_sq_tendsto_probability_zero_of_branch_convergence
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e0 : NuisanceBin L) (eh : ℕ → A → NuisanceBin L)
    (he0 : BinAdmissible M L e0) (heh : ∀ n a, BinAdmissible M L (eh n a))
    (hy : OutcomeBinaryAE M) (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a (i : PositiveIndex L.K), ∀ᵐ x ∂xLaw M,
      c ≤ e0.piLev i x ∧ c ≤ (eh n a).piLev i x)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) e0.prop)
    (hrlev : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrP : FiniteNuisanceRates M μ (fun n a => (eh n a).P1) e0.P1)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) e0.piLev)
    (hrs : ∀ a : RegularIndex L,
      FiniteNuisanceRates M μ (fun n t => (eh n t).share a) (e0.share a))
    (k j : ℕ) (hk : k < L.K)
    (hbranch : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o : Obs X Z,
        (Iact phi L (eh (2*(n+1)) a) k j o.1 - Iact phi L e0 k j o.1)^2 +
        (Dbd phi L (eh (2*(n+1)) a) k j o.1 - Dbd phi L e0 k j o.1)^2 +
        (Edom phi L (eh (2*(n+1)) a) k j o.1 - Edom phi L e0 k j o.1)^2
        ∂observationLaw M) atTop (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o,
        (binaryRegularRegressionCorrection phi L (eh (2*(n+1)) a) k j o -
          binaryRegularRegressionCorrection phi L e0 k j o)^2 ∂observationLaw M)
      atTop (fun _ _ => 0) := by
  let P := fun (e : NuisanceBin L) i (o : Obs X Z) => Dbd phi L e k j o.1 * RP L e i o
  let T := fun (e : NuisanceBin L) (o : Obs X Z) => Dbd phi L e k j o.1 * Rp L e (k+1) o
  let B := fun (e : NuisanceBin L) (o : Obs X Z) =>
    if j = 1 then Edom phi L e k j o.1 * Iact phi L e k j o.1 * Rp L e k o else 0
  have hP (e : NuisanceBin L) (he : BinAdmissible M L e)
      (hpi : ∀ i, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x) (i : ℕ) (hi : i ≤ L.K) :
      MemLp (P e i) 2 (observationLaw M) :=
    fitted_Dbd_RP_memLp M phi hphi L e he hy c hc hpi k j i hi
  have hT (e : NuisanceBin L) (he : BinAdmissible M L e)
      (hpi : ∀ i, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x) :
      MemLp (T e) 2 (observationLaw M) := by
    simpa only [T, ↓reduceIte] using fitted_fractional_treatment_residual_memLp M
      phi hphi L e he c hc hpi k j (k+1) (by omega) true
  have hB (e : NuisanceBin L) (he : BinAdmissible M L e)
      (hpi : ∀ i, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x) :
      MemLp (B e) 2 (observationLaw M) := by
    by_cases hj : j = 1
    · simpa only [B, hj, Bool.false_eq_true, ↓reduceIte] using fitted_fractional_treatment_residual_memLp M
        phi hphi L e he c hc hpi k j k hk.le false
    · simpa only [B, hj, Bool.false_eq_true, ↓reduceIte] using
        (MemLp.zero' : MemLp (0 : Obs X Z → ℝ) 2 (observationLaw M))
  have h0 (n : ℕ) (a : A) : ∀ i, ∀ᵐ x ∂xLaw M, c ≤ e0.piLev i x :=
    fun i => (hclip (2*(n+1)) a i).mono (fun _ hx => hx.1)
  have hH (n : ℕ) (a : A) : ∀ i, ∀ᵐ x ∂xLaw M, c ≤ (eh (2*(n+1)) a).piLev i x :=
    fun i => (hclip _ a i).mono (fun _ hx => hx.2)
  have hz : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun (_ : ℕ) (_ : A) => (0 : ℝ)) atTop (fun _ _ => 0) := by
    rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm]
    intro eps heps
    simpa only [sub_self, norm_zero, not_le.mpr heps, Set.ofPred_false,
      measure_empty] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (𝓝 0))
  have hrP' (i : ℕ) (hi : i ≤ L.K) :=
    nuisanceRates_Dbd_RP_sq_tendsto_probability_zero_of_branch_convergence M μ phi dphi hphi hd hDerivative
      L e0 eh he0 heh hy c hc hclip hrp hrlev hrP hrpi hrs k j i hi hbranch
  have hrT := nuisanceRates_fractional_treatment_residual_sq_tendsto_probability_zero_of_branch_convergence
    M μ phi dphi hphi hd hDerivative L e0 eh he0 heh c hc hclip hrp hrlev hrP hrpi hrs
      k j (k+1) (by omega) true hbranch
  have hrB : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o, (B (eh (2*(n+1)) a) o - B e0 o)^2 ∂observationLaw M)
      atTop (fun _ _ => 0) := by
    by_cases hj : j = 1
    · simpa only [B, hj, Bool.false_eq_true, ↓reduceIte] using
        nuisanceRates_fractional_treatment_residual_sq_tendsto_probability_zero_of_branch_convergence
          M μ phi dphi hphi hd hDerivative L e0 eh he0 heh c hc hclip hrp hrlev hrP hrpi hrs
            k j k hk.le false hbranch
    · simpa only [B, hj, ↓reduceIte, sub_self, zero_pow (by norm_num : 2 ≠ 0),
        integral_zero] using hz
  have hpair := dml_three_term_sq_tendsto_probability_zero μ (observationLaw M)
    (fun n a o => P (eh (2*(n+1)) a) (k+1) o - P e0 (k+1) o)
    (fun _ _ _ => 0) (fun n a o => P (eh (2*(n+1)) a) k o - P e0 k o)
    (fun n a => (hP _ (heh (2*(n+1)) a) (hH n a) (k+1) (by omega)).sub
      (hP e0 he0 (h0 n a) (k+1) (by omega)))
    (fun _ _ => MemLp.zero')
    (fun n a => (hP _ (heh (2*(n+1)) a) (hH n a) k hk.le).sub (hP e0 he0 (h0 n a) k hk.le))
    (hrP' (k+1) (by omega)) (by simpa using hz) (hrP' k hk.le)
  have ht := dml_three_term_sq_tendsto_probability_zero μ (observationLaw M)
    (fun n a o => (P (eh (2*(n+1)) a) (k+1) o - P e0 (k+1) o) + 0 -
      (P (eh (2*(n+1)) a) k o - P e0 k o))
    (fun n a o => -(T (eh (2*(n+1)) a) o - T e0 o))
    (fun n a o => B (eh (2*(n+1)) a) o - B e0 o)
    (fun n a => (((hP _ (heh (2*(n+1)) a) (hH n a) (k+1) (by omega)).sub
      (hP e0 he0 (h0 n a) (k+1) (by omega))).add MemLp.zero').sub
      ((hP _ (heh (2*(n+1)) a) (hH n a) k hk.le).sub (hP e0 he0 (h0 n a) k hk.le)))
    (fun n a => ((hT _ (heh (2*(n+1)) a) (hH n a)).sub (hT e0 he0 (h0 n a))).neg)
    (fun n a => (hB _ (heh (2*(n+1)) a) (hH n a)).sub (hB e0 he0 (h0 n a)))
    hpair (by simpa only [T, ↓reduceIte, neg_sq] using hrT) hrB
  convert ht using 1
  funext n a
  apply integral_congr_ae
  exact Eventually.of_forall (fun o => by
    dsimp only [P, T, B, binaryRegularRegressionCorrection]
    ring)

-- @node: nuisanceRates_regular_policy_correction_sq_tendsto_probability_zero_of_branch_convergence
/-- For [a valid policy map](hyp:hphi) with [its specified derivative](hyp:hd)
and [a bounded Lipschitz derivative](hyp:hDerivative), assume [admissible
reference nuisances](hyp:he0), [admissible fitted nuisances](hyp:heh), [a
positive denominator bound](hyp:hc), and [reference and fitted regular-cell
probabilities bounded below almost everywhere](hyp:hclip). Given
[quarter-rate control of instrument propensities](hyp:hrp),
[quarter-rate control of level propensities](hyp:hrlev),
[quarter-rate control of success regressions](hyp:hrP),
[quarter-rate control of regular-cell probabilities](hyp:hrt),
[quarter-rate control of all regular cell shares](hyp:hrs), [a level index
at most the level count](hyp:hk), and [vanishing integrated squared errors of
the three branch indicators in probability](hyp:hbranch), [the regular policy
correction has integrated squared error tending to zero in probability along
even sample sizes](goal). -/
lemma nuisanceRates_regular_policy_correction_sq_tendsto_probability_zero_of_branch_convergence
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e0 : NuisanceBin L) (eh : ℕ → A → NuisanceBin L)
    (he0 : BinAdmissible M L e0) (heh : ∀ n a, BinAdmissible M L (eh n a))
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a (r : RegularIndex L), ∀ᵐ x ∂xLaw M,
      c ≤ e0.tauLev r x ∧ c ≤ (eh n a).tauLev r x)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) e0.prop)
    (hrlev : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrP : FiniteNuisanceRates M μ (fun n a => (eh n a).P1) e0.P1)
    (hrt : FiniteNuisanceRates M μ (fun n a => (eh n a).tauLev) e0.tauLev)
    (hrs : ∀ r : RegularIndex L,
      FiniteNuisanceRates M μ (fun n a => (eh n a).share r) (e0.share r))
    (k j : ℕ) (hk : k ≤ L.K) (hbranch : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o : Obs X Z,
        (Iact phi L (eh (2*(n+1)) a) k j o.1 - Iact phi L e0 k j o.1)^2 +
        (Dbd phi L (eh (2*(n+1)) a) k j o.1 - Dbd phi L e0 k j o.1)^2 +
        (Edom phi L (eh (2*(n+1)) a) k j o.1 - Edom phi L e0 k j o.1)^2
        ∂observationLaw M) atTop (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o,
        (binaryRegularPolicyCorrection phi dphi L (eh (2*(n+1)) a) k j o -
          binaryRegularPolicyCorrection phi dphi L e0 k j o)^2 ∂observationLaw M)
      atTop (fun _ _ => 0) := by
  let F := fun (e : NuisanceBin L) (o : Obs X Z) =>
    Iact phi L e k j o.1 * RqBin dphi L e k j o
  let G := fun (e : NuisanceBin L) (o : Obs X Z) =>
    Edom phi L e k j o.1 * Iact phi L e k j o.1 * RqBin dphi L e k (j-1) o
  have hF (e : NuisanceBin L) (he : BinAdmissible M L e)
      (hcl : ∀ r, ∀ᵐ x ∂xLaw M, c ≤ e.tauLev r x) :
      MemLp (F e) 2 (observationLaw M) := by
    simpa only [F, ↓reduceIte] using fitted_fractional_policy_residual_memLp
      M phi dphi hphi hd hDerivative L e he c hc hcl k j j hk true
  have hG (e : NuisanceBin L) (he : BinAdmissible M L e)
      (hcl : ∀ r, ∀ᵐ x ∂xLaw M, c ≤ e.tauLev r x) :
      MemLp (G e) 2 (observationLaw M) := by
    simpa only [G, Bool.false_eq_true, ↓reduceIte] using fitted_fractional_policy_residual_memLp
      M phi dphi hphi hd hDerivative L e he c hc hcl k j (j-1) hk false
  have h0 (n : ℕ) (a : A) : ∀ r, ∀ᵐ x ∂xLaw M, c ≤ e0.tauLev r x :=
    fun r => (hclip (2*(n+1)) a r).mono (fun _ hx => hx.1)
  have hH (n : ℕ) (a : A) : ∀ r, ∀ᵐ x ∂xLaw M, c ≤ (eh (2*(n+1)) a).tauLev r x :=
    fun r => (hclip (2*(n+1)) a r).mono (fun _ hx => hx.2)
  have hrF := nuisanceRates_fractional_policy_residual_sq_tendsto_probability_zero_of_branch_convergence
    M μ phi dphi hphi hd hDerivative L e0 eh he0 heh c hc hclip
    hrp hrlev hrP hrt hrs k j j hk true hbranch
  have hrG := nuisanceRates_fractional_policy_residual_sq_tendsto_probability_zero_of_branch_convergence
    M μ phi dphi hphi hd hDerivative L e0 eh he0 heh c hc hclip
    hrp hrlev hrP hrt hrs k j (j-1) hk false hbranch
  have hz : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun (_ : ℕ) (_ : A) => (0 : ℝ)) atTop (fun _ _ => 0) := by
    rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm]
    intro eps heps
    simpa only [sub_self, norm_zero, not_le.mpr heps, Set.ofPred_false,
      measure_empty] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (𝓝 0))
  have hs := dml_three_term_sq_tendsto_probability_zero μ (observationLaw M)
    (fun n a o => F (eh (2*(n+1)) a) o - F e0 o)
    (fun _ _ _ => (0 : ℝ))
    (fun n a o => G (eh (2*(n+1)) a) o - G e0 o)
    (fun n a => (hF _ (heh _ a) (hH n a)).sub (hF e0 he0 (h0 n a)))
    (fun _ _ => MemLp.zero')
    (fun n a => (hG _ (heh _ a) (hH n a)).sub (hG e0 he0 (h0 n a)))
    (by simpa only [F, ↓reduceIte] using hrF)
    (by simpa only [zero_pow (by norm_num : 2 ≠ 0), integral_zero] using hz)
    (by simpa only [G, Bool.false_eq_true, ↓reduceIte] using hrG)
  have hid (n : ℕ) (a : A) (o : Obs X Z) :
      binaryRegularPolicyCorrection phi dphi L (eh (2*(n+1)) a) k j o -
        binaryRegularPolicyCorrection phi dphi L e0 k j o =
      F (eh (2*(n+1)) a) o - F e0 o + 0 - (G (eh (2*(n+1)) a) o - G e0 o) := by
    dsimp only [binaryRegularPolicyCorrection, F, G]
    ring
  simpa only [hid] using hs

end Papers.TbsPrteOptimalTransport

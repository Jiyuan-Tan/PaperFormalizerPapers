module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousJointMean
/-! Finite-block bounds for joint continuous full-interval regression bias.
The fitted denominators are retained while both regression coordinates are
restored, and the component bounds are summed before taking the root-n limit. -/
public section
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.unusedFintypeInType false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: fitted_continuous_full_joint_regression_block_bias_bound
/-- Assume [the true nuisance is admissible](hyp:he0), [the fitted nuisance is
admissible](hyp:he), [potential-outcome support restrictions](hyp:hp),
[consistency](hyp:hcons), [known outcome endpoints](hyp:hend), [a positive overlap
bound](hyp:hc), and [fitted assignment probabilities almost surely above it](hyp:hclip).
If [the assignment-error bound is nonnegative](hyp:hwt), [all adjacent
treatment-propensity-weighted outcome-mean L2 errors are bounded by the regression
error bound](hyp:hC), and [all adjacent assignment-probability L2 errors are bounded
by the assignment-error bound](hyp:hpi), then [the sum of fitted-weighted score
changes from restoring both regressions is integrable and its absolute mean is
at most twice the level count divided by the overlap bound times the product of
the two error bounds](goal). -/
lemma fitted_continuous_full_joint_regression_block_bias_bound
    (L : LevelData Z X) (e : NuisanceCont L)
    (he0 : ContAdmissible M L (trueNuisance M L)) (he : ContAdmissible M L e)
    (hp : PotentialSupport M) (hcons : Consistency M) (hend : OutcomeEndpointsKnown M)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (reg wt : ℝ) (hwt : 0 ≤ wt)
    (hC : ∀ (plus : Bool) (k : Fin L.K), finiteL2Error M
      (fun x => positiveValue e.pLev (if plus then k.val+1 else k.val) x *
        (if plus then fullValue e.JfullPlus k x else minusFullValue e k x))
      (fun x => positiveValue (trueNuisance M L).pLev (if plus then k.val+1 else k.val) x *
        (if plus then fullValue (trueNuisance M L).JfullPlus k x
          else minusFullValue (trueNuisance M L) k x)) ≤ reg)
    (hpi : ∀ (plus : Bool) (k : Fin L.K), finiteL2Error M
      (positiveValue e.piLev (if plus then k.val+1 else k.val))
      (positiveValue (trueNuisance M L).piLev (if plus then k.val+1 else k.val)) ≤ wt) :
    let b := {trueNuisance M L with piLev := e.piLev, gammaFull := e.gammaFull}
    Integrable (fun o : Obs X Z => ∑ k : Fin L.K,
      e.gammaFull k o.1 * (psiFullJ L e k o - psiFullJ L b k o)) (observationLaw M) ∧
    |∫ o : Obs X Z, ∑ k : Fin L.K,
      e.gammaFull k o.1 * (psiFullJ L e k o - psiFullJ L b k o) ∂observationLaw M| ≤
      (2 * (L.K : ℝ) / c) * (reg * wt) := by
  dsimp only
  let b := {trueNuisance M L with piLev := e.piLev, gammaFull := e.gammaFull}
  have hb : ContAdmissible M L b := by
    dsimp only [b]
    rcases he0 with ⟨h1, h2, h3, h4, _, _, h7, h8, h9, h10, _, _, hrest⟩
    rcases he with ⟨_, _, _, _, h5, h6, _, _, _, _, h11, h12, _⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hrest⟩
  have hi (k : Fin L.K) : Integrable (fun o : Obs X Z =>
      e.gammaFull k o.1 * (psiFullJ L e k o - psiFullJ L b k o)) (observationLaw M) := by
    have hh := (fitted_continuous_weighted_full_component_integrable M L e he
      hp hcons hend c hc hclip k).sub
        (fitted_continuous_weighted_full_component_integrable M L b hb
          hp hcons hend c hc hclip k)
    change Integrable (fun o : Obs X Z => e.gammaFull k o.1 * psiFullJ L e k o -
      e.gammaFull k o.1 * psiFullJ L b k o) (observationLaw M) at hh
    simpa only [mul_sub] using hh
  refine ⟨integrable_finsetSum _ (fun k _ => hi k), ?_⟩
  rw [integral_finsetSum _ (fun k _ => hi k)]
  calc
    _ ≤ ∑ k : Fin L.K, |∫ o : Obs X Z,
        e.gammaFull k o.1 * (psiFullJ L e k o - psiFullJ L b k o) ∂observationLaw M| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin L.K, (wt * reg / c + wt * reg / c) := by
      apply Finset.sum_le_sum
      intro k _
      apply (fitted_continuous_full_joint_regression_bias_bound M L e
        he0 he hp hcons hend c hc hclip k).trans
      apply add_le_add
      · exact div_le_div_of_nonneg_right
          (mul_le_mul (hpi true k) (hC true k) (Real.sqrt_nonneg _) hwt) hc.le
      · exact div_le_div_of_nonneg_right
          (mul_le_mul (hpi false k) (hC false k) (Real.sqrt_nonneg _) hwt) hc.le
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

-- @node: nuisanceRates_continuous_full_joint_regression_block_bias_root_n_negligible
/-- Under [admissibility of the true nuisance](hyp:he0), [admissibility of every
fitted nuisance](hyp:heh), [potential-outcome support restrictions](hyp:hp),
[consistency](hyp:hcons), [known outcome endpoints](hyp:hend), [a positive overlap
bound](hyp:hc), and [a uniform almost-sure lower bound on fitted assignment
probabilities](hyp:hclip), suppose inverse-fourth-root little-order L2 rates hold
for [assignment probabilities](hyp:hrpi), [treatment propensities](hyp:hrp),
[upper means](hyp:hrplus), and [lower means](hyp:hrminus). Then [the mean sum over
all levels of fitted-weighted score changes from restoring both regressions,
multiplied by the square root of the half-sample size, converges in probability
to zero](goal). -/
lemma nuisanceRates_continuous_full_joint_regression_block_bias_root_n_negligible
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
    (hrminus : FiniteNuisanceRates M μ (fun n a => (eh n a).JfullMinus) (trueNuisance M L).JfullMinus) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
        (∫ o : Obs X Z, ∑ k : Fin L.K, (eh (2*(n+1)) a).gammaFull k o.1 *
          (psiFullJ L (eh (2*(n+1)) a) k o -
            psiFullJ L {trueNuisance M L with
              piLev := (eh (2*(n+1)) a).piLev
              gammaFull := (eh (2*(n+1)) a).gammaFull} k o) ∂observationLaw M))
      atTop (fun _ _ => 0) := by
  let ks := (Finset.univ : Finset (Bool × Fin L.K)).toList
  let C := fun (e : NuisanceCont L) (i : Bool × Fin L.K) x =>
    positiveValue e.pLev (if i.1 then i.2.val+1 else i.2.val) x *
      (if i.1 then fullValue e.JfullPlus i.2 x else minusFullValue e i.2 x)
  let pi := fun (e : NuisanceCont L) (i : Bool × Fin L.K) =>
    positiveValue e.piLev (if i.1 then i.2.val+1 else i.2.val)
  let reg := fun n a => maxErrors (ks.map (fun i =>
    finiteL2Error M (C (eh (2*(n+1)) a) i) (C (trueNuisance M L) i)))
  let wt := fun n a => maxErrors (ks.map (fun i =>
    finiteL2Error M (pi (eh (2*(n+1)) a) i) (pi (trueNuisance M L) i)))
  have hr := nuisanceRates_finite_maxErrors M μ
    (fun n a => C (eh n a)) (C (trueNuisance M L)) ks (fun i =>
      nuisanceRates_continuous_full_coefficient_quarter_rate M μ L (trueNuisance M L) eh
        he0 heh hrp hrplus hrminus i.1 i.2)
  have hw := nuisanceRates_finite_maxErrors M μ
    (fun n a => pi (eh n a)) (pi (trueNuisance M L)) ks (fun i =>
      nuisanceRates_positiveValue M μ L.K _ _ hrpi (if i.1 then i.2.val+1 else i.2.val))
  have hprod := dml_quarter_rate_product μ reg wt hr hw
  apply dml_root_n_bias_tendsto_probability μ
  apply Causalean.Stat.IsLittleOp.of_abs_le_const_mul
    (by positivity : 0 < 2 * (L.K : ℝ) / c + 1) hprod
  intro n a
  have hbound := (fitted_continuous_full_joint_regression_block_bias_bound M L
    (eh (2*(n+1)) a) he0 (heh _ a) hp hcons hend c hc (hclip _ a)
    (reg n a) (wt n a) (maxErrors_nonneg _)
    (fun plus k => le_maxErrors_of_mem
      (List.mem_map.mpr ⟨(plus, k), by simp [ks], rfl⟩))
    (fun plus k => le_maxErrors_of_mem
      (List.mem_map.mpr ⟨(plus, k), by simp [ks], rfl⟩))).2
  rw [abs_of_nonneg (mul_nonneg (maxErrors_nonneg _) (maxErrors_nonneg _))]
  exact hbound.trans (mul_le_mul_of_nonneg_right (by linarith)
    (mul_nonneg (maxErrors_nonneg _) (maxErrors_nonneg _)))

end Papers.TbsPrteOptimalTransport

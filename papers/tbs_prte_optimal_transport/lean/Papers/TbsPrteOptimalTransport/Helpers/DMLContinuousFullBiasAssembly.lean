module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousHybridMean
/-! Finite continuous full-interval score bias assembly.
The actual fitted product scores have a second-order mean remainder,
which vanishes at root-n scale under the componentwise nuisance rates. -/
public section
set_option linter.style.longLine false
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

-- @node: fitted_continuous_full_score_block_bias_bound
/-- In [a threshold-crossing model](hyp:h) with [invariant level ordering for
the alternative propensity](hyp:hOrder), assume [admissible true nuisances](hyp:he0),
[admissible fitted nuisances](hyp:he), [potential outcomes in the outcome domain almost surely](hyp:hp),
[consistency](hyp:hcons), [known outcome endpoints](hyp:hend), [a positive
denominator floor](hyp:hc), and [fitted assignment probabilities bounded below
by that floor almost everywhere](hyp:hclip). If [the weight error bound is
nonnegative](hyp:hwt), [both treatment-probability-weighted outcome-mean errors
are bounded in root mean square by the regression bound](hyp:hC), [both
assignment-probability errors are bounded in root mean square by the weight
bound](hyp:hpi), [every full-interval outcome-contrast error obeys the regression
bound](hyp:hJ), and [every instrument-weight error obeys the weight bound](hyp:hg),
then [the fitted full-interval score block is integrable and its absolute mean
bias relative to the true covariate target is at most the product of the number
of levels, the sum of one and twice the reciprocal denominator floor, and the
regression and weight bounds](goal). -/
lemma fitted_continuous_full_score_block_bias_bound (h : ThresholdCrossing M)
    (q : Z → X → ℝ) (L : LevelData Z X) (hOrder : LevelOrderInvariant M.prop q L)
    (e : NuisanceCont L) (he0 : ContAdmissible M L (trueNuisance M L))
    (he : ContAdmissible M L e)
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
      (positiveValue (trueNuisance M L).piLev (if plus then k.val+1 else k.val)) ≤ wt)
    (hJ : ∀ k : Fin L.K, finiteL2Error M (contFullJ L e k)
      (contFullJ L (trueNuisance M L) k) ≤ reg)
    (hg : ∀ k : Fin L.K, finiteL2Error M (e.gammaFull k)
      ((trueNuisance M L).gammaFull k) ≤ wt) :
    Integrable (fun o => ∑ k : Fin L.K, psiFullProd L e k o) (observationLaw M) ∧
    |(∫ o, ∑ k : Fin L.K, psiFullProd L e k o ∂observationLaw M) -
      (∫ x, ∑ k : Fin L.K, gammaFull M L k x *
        contFullJ L (trueNuisance M L) k x ∂xLaw M)| ≤
      ((L.K : ℝ) * (2 / c + 1)) * (reg * wt) := by
  have hi k := (fitted_continuous_full_product_mean_decomposition M L e he
    hp hcons hend c hc hclip k).1
  have ht (k : Fin L.K) : Integrable (fun x => gammaFull M L k x *
      contFullJ L (trueNuisance M L) k x) (xLaw M) :=
    (fitted_continuous_gammaFull_memLp M L _ he0 k).integrable_mul
      (fitted_contFullJ_memLp M L _ he0 k)
  refine ⟨integrable_finsetSum _ (fun k _ => hi k), ?_⟩
  rw [integral_finsetSum _ (fun k _ => hi k),
    integral_finsetSum _ (fun k _ => ht k), ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ k : Fin L.K, |(∫ o, psiFullProd L e k o ∂observationLaw M) -
        (∫ x, gammaFull M L k x * contFullJ L (trueNuisance M L) k x ∂xLaw M)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin L.K, (wt * reg / c + wt * reg / c + wt * reg) := by
      apply Finset.sum_le_sum
      intro k _
      apply (fitted_continuous_full_product_bias_bound M h q L hOrder e he0 he
        hp hcons hend c hc hclip k).trans
      apply add_le_add
      · apply add_le_add
        · exact div_le_div_of_nonneg_right
            (mul_le_mul (hpi true k) (hC true k) (Real.sqrt_nonneg _) hwt) hc.le
        · exact div_le_div_of_nonneg_right
            (mul_le_mul (hpi false k) (hC false k) (Real.sqrt_nonneg _) hwt) hc.le
      · exact mul_le_mul (hg k) (hJ k) (Real.sqrt_nonneg _) hwt
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

-- @node: nuisanceRates_continuous_full_score_block_bias_root_n_negligible
/-- In [a threshold-crossing model](hyp:h) with [invariant level ordering for
the alternative propensity](hyp:hOrder), [admissible true nuisances](hyp:he0),
[admissible fitted nuisances at every sample size](hyp:heh), [potential outcomes
almost surely in the outcome domain](hyp:hp), [consistency](hyp:hcons), [known outcome endpoints](hyp:hend),
[a positive denominator floor](hyp:hc), and [all fitted assignment probabilities
bounded below by that floor almost everywhere](hyp:hclip), suppose componentwise
nuisance rates hold for [assignment probabilities](hyp:hrpi), [treatment
probabilities](hyp:hrp), [upper full-interval means](hyp:hrplus), [lower full-interval
means](hyp:hrminus), and [instrument weights](hyp:hrg). Then [the mean bias of the
fitted full-interval score block relative to the true covariate target, using
fits at twice the half-sample size and multiplied by the square root of the
half-sample size, converges in probability to zero](goal). -/
lemma nuisanceRates_continuous_full_score_block_bias_root_n_negligible
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (h : ThresholdCrossing M) (q : Z → X → ℝ) (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop q L) (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hp : PotentialSupport M) (hcons : Consistency M) (hend : OutcomeEndpointsKnown M)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a (i : PositiveIndex L.K), ∀ᵐ x ∂xLaw M, c ≤ (eh n a).piLev i x)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) (trueNuisance M L).piLev)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) (trueNuisance M L).pLev)
    (hrplus : FiniteNuisanceRates M μ (fun n a => (eh n a).JfullPlus) (trueNuisance M L).JfullPlus)
    (hrminus : FiniteNuisanceRates M μ (fun n a => (eh n a).JfullMinus) (trueNuisance M L).JfullMinus)
    (hrg : FiniteNuisanceRates M μ (fun n a => (eh n a).gammaFull) (trueNuisance M L).gammaFull) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
        ((∫ o, ∑ k : Fin L.K, psiFullProd L (eh (2*(n+1)) a) k o ∂observationLaw M) -
          (∫ x, ∑ k : Fin L.K, gammaFull M L k x *
            contFullJ L (trueNuisance M L) k x ∂xLaw M)))
      atTop (fun _ _ => 0) := by
  let ks := (Finset.univ : Finset ((Bool × Fin L.K) ⊕ Fin L.K)).toList
  let R := fun (e : NuisanceCont L) (i : (Bool × Fin L.K) ⊕ Fin L.K) =>
    match i with
    | .inl (plus, k) => fun x =>
        positiveValue e.pLev (if plus then k.val+1 else k.val) x *
          (if plus then fullValue e.JfullPlus k x else minusFullValue e k x)
    | .inr k => contFullJ L e k
  let W := fun (e : NuisanceCont L) (i : (Bool × Fin L.K) ⊕ Fin L.K) =>
    match i with
    | .inl (plus, k) => positiveValue e.piLev (if plus then k.val+1 else k.val)
    | .inr k => e.gammaFull k
  let reg := fun n a => maxErrors (ks.map (fun i =>
    finiteL2Error M (R (eh (2*(n+1)) a) i) (R (trueNuisance M L) i)))
  let wt := fun n a => maxErrors (ks.map (fun i =>
    finiteL2Error M (W (eh (2*(n+1)) a) i) (W (trueNuisance M L) i)))
  have hr := nuisanceRates_finite_maxErrors M μ
    (fun n a => R (eh n a)) (R (trueNuisance M L)) ks (fun i => by
      cases i with
      | inl i =>
          exact nuisanceRates_continuous_full_coefficient_quarter_rate M μ L
            (trueNuisance M L) eh he0 heh hrp hrplus hrminus i.1 i.2
      | inr k =>
          exact nuisanceRates_contFullJ_quarter_rate M μ L
            (trueNuisance M L) eh he0 heh hrp hrplus hrminus k)
  have hw := nuisanceRates_finite_maxErrors M μ
    (fun n a => W (eh n a)) (W (trueNuisance M L)) ks (fun i => by
      cases i with
      | inl i =>
          exact nuisanceRates_positiveValue M μ L.K _ _ hrpi
            (if i.1 then i.2.val+1 else i.2.val)
      | inr k => exact hrg k)
  have hprod := dml_quarter_rate_product μ reg wt hr hw
  apply dml_root_n_bias_tendsto_probability μ
  apply Causalean.Stat.IsLittleOp.of_abs_le_const_mul
    (by positivity : 0 < (L.K : ℝ) * (2 / c + 1) + 1) hprod
  intro n a
  have hb := (fitted_continuous_full_score_block_bias_bound M h q L hOrder
    (eh (2*(n+1)) a) he0 (heh _ a) hp hcons hend c hc (hclip _ a)
    (reg n a) (wt n a) (maxErrors_nonneg _)
    (fun plus k => le_maxErrors_of_mem
      (List.mem_map.mpr ⟨Sum.inl (plus, k), by simp [ks], rfl⟩))
    (fun plus k => le_maxErrors_of_mem
      (List.mem_map.mpr ⟨Sum.inl (plus, k), by simp [ks], rfl⟩))
    (fun k => le_maxErrors_of_mem
      (List.mem_map.mpr ⟨Sum.inr k, by simp [ks], rfl⟩))
    (fun k => le_maxErrors_of_mem
      (List.mem_map.mpr ⟨Sum.inr k, by simp [ks], rfl⟩))).2
  rw [abs_of_nonneg (mul_nonneg (maxErrors_nonneg _) (maxErrors_nonneg _))]
  exact hb.trans (mul_le_mul_of_nonneg_right (by linarith)
    (mul_nonneg (maxErrors_nonneg _) (maxErrors_nonneg _)))

end Papers.TbsPrteOptimalTransport

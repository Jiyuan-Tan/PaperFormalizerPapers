module
public import Papers.TbsNeuralCausalPi.Setup.Assumptions.Auxiliary
public import Papers.TbsNeuralCausalPi.Setup.Assumptions.Conventions
public import Mathlib.MeasureTheory.Constructions.Pi
public import Papers.TbsNeuralCausalPi.Helpers.KantorovichCube
public import Papers.TbsNeuralCausalPi.Helpers.RegressionVector
/-! # Push-forward Wasserstein bound -/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.haveILetI false
open MeasureTheory
open scoped ENNReal NNReal

namespace PushForward
open Toolkit.Foundations.MeasureTheory

-- @node: PushForward.contrast_le_cost
/-- Given [a probability coupling of the two source laws](hyp:hpi),
[measurable maps to the outcome space](hyp:hF,hFhat), with [the first map Lipschitz
with nonnegative constant L](hyp:L,hLip) and [pointwise discrepancy at most the
extended nonnegative bound E](hyp:E,herror),
and [a real-valued test function with Lipschitz constant one](hyp:hg) that is
[integrable under both output laws](hyp:hi,hj), [the positive part of its
expectation difference is at most L times the coupling's expected distance plus E](goal). -/
lemma contrast_le_cost {X Y : Type*} [MeasurableSpace X] [MetricSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace Y] [MetricSpace Y] [BorelSpace Y]
    {mu nu : Measure X} {pi : Measure (X × X)}
    (hpi : Causalean.Stat.IsCoupling pi mu nu)
    (F Fhat : X → Y) (hF : Measurable F) (hFhat : Measurable Fhat)
    (L : ℝ≥0) (hLip : LipschitzWith L F) (E : ℝ≥0∞)
    (herror : ∀ x, edist (F x) (Fhat x) ≤ E)
    (g : Y → ℝ) (hg : LipschitzWith 1 g)
    (hi : Integrable g (mu.map F)) (hj : Integrable g (nu.map Fhat)) :
    ENNReal.ofReal (lipschitzContrast (mu.map F) (nu.map Fhat) g) ≤
      (L : ℝ≥0∞) * (∫⁻ z, edist z.1 z.2 ∂pi) + E := by
  let := hpi.isProbabilityMeasure
  have him : Integrable (fun x => g (F x)) mu :=
    (integrable_map_measure hi.aestronglyMeasurable hF.aemeasurable).1 hi
  have hjm : Integrable (fun x => g (Fhat x)) nu :=
    (integrable_map_measure hj.aestronglyMeasurable hFhat.aemeasurable).1 hj
  have himp : Integrable (fun x => g (F x)) (pi.map Prod.fst) :=
    hpi.map_fst.symm ▸ him
  have hjmp : Integrable (fun x => g (Fhat x)) (pi.map Prod.snd) :=
    hpi.map_snd.symm ▸ hjm
  have hip : Integrable (fun z : X × X => g (F z.1)) pi := by
    exact himp.comp_measurable measurable_fst
  have hjp : Integrable (fun z : X × X => g (Fhat z.2)) pi := by
    exact hjmp.comp_measurable measurable_snd
  have hmi : (∫ y, g y ∂mu.map F) = ∫ z, g (F z.1) ∂pi := by
    rw [integral_map hF.aemeasurable hi.aestronglyMeasurable, ← hpi.map_fst]
    exact integral_map measurable_fst.aemeasurable himp.aestronglyMeasurable
  have hmj : (∫ y, g y ∂nu.map Fhat) = ∫ z, g (Fhat z.2) ∂pi := by
    rw [integral_map hFhat.aemeasurable hj.aestronglyMeasurable, ← hpi.map_snd]
    exact integral_map measurable_snd.aemeasurable hjmp.aestronglyMeasurable
  calc
    ENNReal.ofReal (lipschitzContrast (mu.map F) (nu.map Fhat) g) ≤
        edist (∫ y, g y ∂mu.map F) (∫ y, g y ∂nu.map Fhat) := by
      rw [lipschitzContrast, edist_dist, Real.dist_eq]
      exact ENNReal.ofReal_le_ofReal (le_abs_self _)
    _ ≤ ∫⁻ z, edist (g (F z.1)) (g (Fhat z.2)) ∂pi := by
      rw [hmi, hmj]
      exact edist_integral_le_lintegral_edist hip hjp
    _ ≤ ∫⁻ z : X × X, (L : ℝ≥0∞) * edist z.1 z.2 + E ∂pi := by
      apply lintegral_mono
      intro z
      calc
        edist (g (F z.1)) (g (Fhat z.2)) ≤ edist (F z.1) (Fhat z.2) := by
          simpa using hg.edist_le_mul (F z.1) (Fhat z.2)
        _ ≤ edist (F z.1) (F z.2) + edist (F z.2) (Fhat z.2) := edist_triangle _ _ _
        _ ≤ (L : ℝ≥0∞) * edist z.1 z.2 + E :=
          add_le_add (hLip.edist_le_mul _ _) (herror _)
    _ = (L : ℝ≥0∞) * (∫⁻ z, edist z.1 z.2 ∂pi) + E := by
      rw [lintegral_add_left (by fun_prop), lintegral_const_mul _ (by fun_prop)]
      simp

-- @node: PushForward.map_le_of_compact_range
/-- For two probability laws and [two measurable outcome maps](hyp:hF,hFhat),
suppose [the first map has nonnegative Lipschitz constant L](hyp:L,hLip), [their pointwise
distance is at most the extended nonnegative bound E](hyp:E,herror), and [a compact set](hyp:hC)
[contains the first map's range](hyp:hFC) and [the second map's range](hyp:hFhatC).
Then [the Wasserstein distance between the output laws is at most L times the
source Wasserstein distance plus E](goal). -/
lemma map_le_of_compact_range {X Y : Type*} [MeasurableSpace X] [MetricSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace Y] [MetricSpace Y] [BorelSpace Y]
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (F Fhat : X → Y) (hF : Measurable F) (hFhat : Measurable Fhat)
    (L : ℝ≥0) (hLip : LipschitzWith L F) (E : ℝ≥0∞)
    (herror : ∀ x, edist (F x) (Fhat x) ≤ E)
    (C : Set Y) (hC : IsCompact C)
    (hFC : ∀ x, F x ∈ C) (hFhatC : ∀ x, Fhat x ∈ C) :
    Papers.TbsNeuralCausalPi.wasserstein1 (mu.map F) (nu.map Fhat) ≤
      (L : ℝ≥0∞) * Papers.TbsNeuralCausalPi.wasserstein1 mu nu + E := by
  classical
  let : IsProbabilityMeasure (mu.map F) := Measure.isProbabilityMeasure_map hF.aemeasurable
  let : IsProbabilityMeasure (nu.map Fhat) := Measure.isProbabilityMeasure_map hFhat.aemeasurable
  have hm : (mu.map F) C = 1 := by
    rw [Measure.map_apply hF hC.measurableSet]
    have : F ⁻¹' C = Set.univ := Set.eq_univ_of_forall hFC
    rw [this, measure_univ]
  have hn : (nu.map Fhat) C = 1 := by
    rw [Measure.map_apply hFhat hC.measurableSet]
    have : Fhat ⁻¹' C = Set.univ := Set.eq_univ_of_forall hFhatC
    rw [this, measure_univ]
  rw [wasserstein1_eq_toolkit,
    Toolkit.Foundations.MeasureTheory.wasserstein1_eq_iSup_lipschitzOn
      _ _ C hC hm hn]
  refine iSup_le fun f => ?_
  obtain ⟨g, hg, heq⟩ := f.property.extend_real
  have hma : ∀ᵐ y ∂mu.map F, y ∈ C :=
    (ae_mem_iff_measure_eq hC.measurableSet.nullMeasurableSet).2 (by simpa using hm)
  have hna : ∀ᵐ y ∂nu.map Fhat, y ∈ C :=
    (ae_mem_iff_measure_eq hC.measurableSet.nullMeasurableSet).2 (by simpa using hn)
  have hi : Integrable g (mu.map F) := by
    have hi := hg.continuous.continuousOn.integrableOn_compact (μ := mu.map F) hC
    rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hma] at hi
  have hj : Integrable g (nu.map Fhat) := by
    have hj := hg.continuous.continuousOn.integrableOn_compact (μ := nu.map Fhat) hC
    rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hna] at hj
  have he : lipschitzContrast (mu.map F) (nu.map Fhat) f.val =
      lipschitzContrast (mu.map F) (nu.map Fhat) g := by
    unfold lipschitzContrast
    congr 1
    · apply integral_congr_ae
      filter_upwards [hma] with y hy using heq hy
    · apply integral_congr_ae
      filter_upwards [hna] with y hy using heq hy
  rw [he]
  have hp : mu.prod nu ∈ couplings mu nu := by
    refine ⟨inferInstance, ?_, ?_⟩ <;> simp
  let : Nonempty (couplings mu nu) := ⟨⟨mu.prod nu, hp⟩⟩
  rw [wasserstein1_eq_couplings,
    ENNReal.mul_iInf (by simp), ENNReal.iInf_add]
  refine le_iInf fun pi => ?_
  exact contrast_le_cost ⟨pi.property.1, pi.property.2.1, pi.property.2.2⟩
    F Fhat hF hFhat L hLip E herror g hg hi hj

end PushForward

-- @env: S5
variable {d₁ d₂ : ℕ}

-- @node: lem:push-forward-err
/-- Suppose [the source carrier is compact](hyp:hcompact), [both source laws
are probability laws](hyp:hprob), and [each assigns full mass to that carrier](hyp:hmuK,hmuhatK).
For [maps measurable on the carrier](hyp:hF,hFhat), assume [the first has
nonnegative Lipschitz constant L there](hyp:L,hLip) and [the uniform error uses the coordinatewise
supremum convention](hyp:hNorm). Then [the output Wasserstein distance is at most
L times the source distance plus the output dimension times the uniform coordinate error](goal). -/
lemma wasserstein_map_le (K : Set (L1Vec d₁))
    (hcompact : IsCompact K)
    (mu muhat : Measure (L1Vec d₁))
    (hprob : MeasuresAreProbability mu muhat)
    (hmuK : mu K = 1) (hmuhatK : muhat K = 1)
    (F Fhat : L1Vec d₁ → L1Vec d₂) -- @realizes \hat{F}(measurable comparison map on the same compact source domain)
    (hF : Measurable (fun x : K => F x))
    (hFhat : Measurable (fun x : K => Fhat x))
    (L : ℝ≥0) (hLip : LipschitzOnWith L F K)
    (hNorm : SupNormConventionPushForward (d := d₂) K) :
    wasserstein1 (mu.map F) (muhat.map Fhat) ≤
      (L : ℝ≥0∞) * wasserstein1 mu muhat + (d₂ : ℝ≥0∞) * supDistOn K F Fhat := by
  classical
  let : BorelSpace (L1Vec d₁) := ⟨rfl⟩
  let : BorelSpace (L1Vec d₂) := ⟨rfl⟩
  let : IsProbabilityMeasure mu := hprob.1
  let : IsProbabilityMeasure muhat := hprob.2
  let E : ℝ≥0∞ := (d₂ : ℝ≥0∞) * supDistOn K F Fhat
  by_cases hE : E = ∞
  · change wasserstein1 _ _ ≤ _ + E
    rw [hE, add_top]
    exact le_top
  have herr (x : K) : edist (F x) (Fhat x) ≤ E := by
    rw [PiLp.edist_eq_sum (p := 1) (by norm_num)]
    simp only [ENNReal.toReal_one, ENNReal.rpow_one, one_div_one]
    calc
      ∑ j : Fin d₂, edist ((F x).ofLp j) ((Fhat x).ofLp j) ≤
          ∑ _j : Fin d₂, supDistOn K F Fhat := by
        apply Finset.sum_le_sum
        intro j _
        rw [edist_dist, Real.dist_eq, hNorm F Fhat]
        exact le_iSup_of_le x (le_iSup_of_le j le_rfl)
      _ = E := by simp [E]
  let m := mu.comap ((↑) : K → L1Vec d₁)
  let n := muhat.comap ((↑) : K → L1Vec d₁)
  have hm := Toolkit.Foundations.MeasureTheory.probability_comap_subtype
    mu K hcompact.measurableSet hmuK
  have hn := Toolkit.Foundations.MeasureTheory.probability_comap_subtype
    muhat K hcompact.measurableSet hmuhatK
  let : IsProbabilityMeasure m := hm.1
  let : IsProbabilityMeasure n := hn.1
  have hma : ∀ᵐ x ∂mu, x ∈ K :=
    (ae_mem_iff_measure_eq hcompact.measurableSet.nullMeasurableSet).2
      (by simpa using hmuK)
  have hna : ∀ᵐ x ∂muhat, x ∈ K :=
    (ae_mem_iff_measure_eq hcompact.measurableSet.nullMeasurableSet).2
      (by simpa using hmuhatK)
  have hFae : AEMeasurable F mu := by
    have h := aemeasurable_restrict_of_measurable_subtype (μ := mu) hcompact.measurableSet hF
    rwa [Measure.restrict_eq_self_of_ae_mem hma] at h
  have hFhatae : AEMeasurable Fhat muhat := by
    have h := aemeasurable_restrict_of_measurable_subtype (μ := muhat) hcompact.measurableSet hFhat
    rwa [Measure.restrict_eq_self_of_ae_mem hna] at h
  have hmap : m.map (fun x : K => F x) = mu.map F := by
    rw [← hm.2]
    exact (AEMeasurable.map_map_of_aemeasurable
      (by simpa only [m, hm.2] using hFae) measurable_subtype_coe.aemeasurable).symm
  have hmaphat : n.map (fun x : K => Fhat x) = muhat.map Fhat := by
    rw [← hn.2]
    exact (AEMeasurable.map_map_of_aemeasurable
      (by simpa only [n, hn.2] using hFhatae) measurable_subtype_coe.aemeasurable).symm
  obtain ⟨R, hR⟩ := (hcompact.image_of_continuousOn hLip.continuousOn).isBounded.exists_norm_le
  let C : Set (L1Vec d₂) := Metric.closedBall 0 (R + E.toReal)
  have hFC (x : K) : F x ∈ C := by
    change dist (F x) 0 ≤ R + E.toReal
    rw [dist_zero_right]
    exact (hR _ (Set.mem_image_of_mem F x.property)).trans
      (le_add_of_nonneg_right ENNReal.toReal_nonneg)
  have hFhatC (x : K) : Fhat x ∈ C := by
    change dist (Fhat x) 0 ≤ R + E.toReal
    rw [dist_zero_right]
    have hd : dist (F x) (Fhat x) ≤ E.toReal := by
      have h := ENNReal.toReal_mono hE (herr x)
      simpa only [edist_dist, ENNReal.toReal_ofReal dist_nonneg] using h
    have ht := norm_le_norm_add_norm_sub (F x) (Fhat x)
    rw [← dist_eq_norm] at ht
    exact ht.trans (add_le_add (hR _ (Set.mem_image_of_mem F x.property)) hd)
  have hb := PushForward.map_le_of_compact_range m n
    (fun x : K => F x) (fun x : K => Fhat x) hF hFhat L hLip.to_restrict E herr
    C (isCompact_closedBall _ _) hFC hFhatC
  rw [hmap, hmaphat] at hb
  have hw : wasserstein1 m n = wasserstein1 mu muhat := by
    rw [wasserstein1_eq_toolkit, wasserstein1_eq_toolkit]
    exact (Toolkit.Foundations.MeasureTheory.wasserstein1_subtype_comap
      mu muhat K hcompact.measurableSet hmuK hmuhatK).symm
  rw [hw] at hb
  exact hb

/-- If [the common mixture weights are nonnegative and sum to one](hyp:hweights),
[all paired components have finite first moments](hyp:hmoments), and [all
components are probability laws](hyp:hprob), then for [a test function with
Lipschitz constant one](hyp:hf), [the positive part of the mixture expectation
difference is bounded by the weighted sum of the paired component Wasserstein distances](goal). -/
-- @node: mixture_lipschitz_contrast_le
lemma mixture_lipschitz_contrast_le {n d : ℕ}
    (p : Fin n → ℝ) (mu muhat : Fin n → Measure (L1Vec d))
    (hweights : MixtureWeights p) (hmoments : ComponentsFiniteFirstMoment mu muhat)
    (hprob : MixtureComponentsProbability mu muhat)
    (f : L1Vec d → ℝ) (hf : LipschitzWith 1 f) :
    ENNReal.ofReal
      ((∫ x, f x ∂(∑ k, ENNReal.ofReal (p k) • mu k)) -
        ∫ x, f x ∂(∑ k, ENNReal.ofReal (p k) • muhat k)) ≤
      ∑ k, ENNReal.ofReal (p k) * wasserstein1 (mu k) (muhat k) := by
  classical
  let : BorelSpace (L1Vec d) := ⟨rfl⟩
  have hp (k) : 0 ≤ p k := hweights.1 k
  have hi (k) : Integrable f (mu k) ∧ Integrable f (muhat k) := by
    let : IsProbabilityMeasure (mu k) := (hprob k).1
    let : IsProbabilityMeasure (muhat k) := (hprob k).2
    exact ⟨Toolkit.Foundations.MeasureTheory.integrable_lipschitz_of_firstMoment
      0 hf (by simpa only [dist_zero_right] using (hmoments k).1),
      Toolkit.Foundations.MeasureTheory.integrable_lipschitz_of_firstMoment
      0 hf (by simpa only [dist_zero_right] using (hmoments k).2)⟩
  have him (k) : Integrable f (ENNReal.ofReal (p k) • mu k) := by
    exact (hi k).1.smul_measure ENNReal.ofReal_ne_top
  have hih (k) : Integrable f (ENNReal.ofReal (p k) • muhat k) := by
    exact (hi k).2.smul_measure ENNReal.ofReal_ne_top
  rw [integral_finsetSum_measure (fun k _ => him k),
    integral_finsetSum_measure (fun k _ => hih k)]
  simp only [integral_smul_measure, ENNReal.toReal_ofReal (hp _), smul_eq_mul]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  let c : Fin n → ℝ := fun k => (∫ x, f x ∂mu k) - ∫ x, f x ∂muhat k
  change ENNReal.ofReal (∑ k, p k * c k) ≤ _
  calc
    ENNReal.ofReal (∑ k, p k * c k) ≤
        ENNReal.ofReal (∑ k, p k * max (c k) 0) := by
      apply ENNReal.ofReal_le_ofReal
      exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (le_max_left _ _) (hp k)
    _ = ∑ k, ENNReal.ofReal (p k) * ENNReal.ofReal (c k) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => mul_nonneg (hp k) (le_max_right _ _))]
      apply Finset.sum_congr rfl
      intro k _
      rw [ENNReal.ofReal_mul (hp k)]
      simp
    _ ≤ ∑ k, ENNReal.ofReal (p k) * wasserstein1 (mu k) (muhat k) := by
      apply Finset.sum_le_sum
      intro k _
      gcongr
      rw [wasserstein1_eq_toolkit]
      exact Toolkit.Foundations.MeasureTheory.lipschitzContrast_le_wasserstein1
        hf (hi k).1 (hi k).2

-- @node: lem:combin-err
/-- For [at least one component](hyp:hn), suppose [the common weights are
nonnegative and sum to one](hyp:hweights), [the paired components have finite
first moments](hyp:hmoments), and [each component is a probability law](hyp:hprob).
Then [the Wasserstein distance between the mixtures is bounded by the weighted
sum of the paired component distances](goal). -/
lemma wasserstein_mixture_le {n d : ℕ} (hn : 1 ≤ n)
    (p : Fin n → ℝ) (mu muhat : Fin n → Measure (L1Vec d)) -- @realizes \mu_i(mixture component probability laws) -- @realizes \hat{\mu}_i(paired comparison component probability laws)
    (hweights : MixtureWeights p) (hmoments : ComponentsFiniteFirstMoment mu muhat)
    (hprob : MixtureComponentsProbability mu muhat) : -- @realizes \mu_i(component laws each have total mass one)
    wasserstein1 (∑ k, ENNReal.ofReal (p k) • mu k)
      (∑ k, ENNReal.ofReal (p k) • muhat k) ≤
        ∑ k, ENNReal.ofReal (p k) * wasserstein1 (mu k) (muhat k) := by
  classical
  let C (k : Fin n) := couplings (mu k) (muhat k)
  have hnonempty (k : Fin n) : Nonempty (C k) := by
    let : IsProbabilityMeasure (mu k) := (hprob k).1
    let : IsProbabilityMeasure (muhat k) := (hprob k).2
    exact ⟨⟨(mu k).prod (muhat k), inferInstance, by simp, by simp⟩⟩
  letI (k : Fin n) : Nonempty (C k) := hnonempty k
  let cost (k : Fin n) (pi : C k) : ℝ≥0∞ :=
    ENNReal.ofReal (p k) * ∫⁻ z, edist z.1 z.2 ∂pi.val
  have hmix (pi : ∀ k, C k) :
      wasserstein1 (∑ k, ENNReal.ofReal (p k) • mu k)
        (∑ k, ENNReal.ofReal (p k) • muhat k) ≤ ∑ k, cost k (pi k) := by
    let rho : Measure (L1Vec d × L1Vec d) :=
      ∑ k, ENNReal.ofReal (p k) • (pi k).val
    letI (k : Fin n) : IsProbabilityMeasure (pi k).val := (pi k).property.1
    have hrho : rho ∈ couplings (∑ k, ENNReal.ofReal (p k) • mu k)
        (∑ k, ENNReal.ofReal (p k) • muhat k) := by
      refine ⟨⟨?_⟩, ?_, ?_⟩
      · simp only [rho, Measure.finsetSum_apply, Measure.smul_apply,
          measure_univ, smul_eq_mul, mul_one]
        rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => hweights.1 k), hweights.2]
        simp
      · simp only [rho, Measure.map_finset_sum measurable_fst.aemeasurable,
          Measure.map_smul, (pi _).property.2.1]
      · simp only [rho, Measure.map_finset_sum measurable_snd.aemeasurable,
          Measure.map_smul, (pi _).property.2.2]
    calc
      wasserstein1 _ _ ≤ ∫⁻ z, edist z.1 z.2 ∂rho :=
        (wasserstein1_eq_couplings _ _).trans_le (iInf_le_of_le ⟨rho, hrho⟩ le_rfl)
      _ = ∑ k, cost k (pi k) := by
        simp [rho, cost, lintegral_smul_measure]
  have hdir (t : Finset (Fin n)) (a b : ∀ k, C k) :
      ∃ c : ∀ k, C k, ∀ k ∈ t,
        cost k (c k) ≤ cost k (a k) ∧ cost k (c k) ≤ cost k (b k) := by
    refine ⟨fun k => if cost k (a k) ≤ cost k (b k) then a k else b k, ?_⟩
    intro k hk
    dsimp only
    split_ifs with h
    · exact ⟨le_rfl, h⟩
    · exact ⟨le_of_not_ge h, le_rfl⟩
  have heval (k : Fin n) :
      (⨅ pi : ∀ j, C j, cost k (pi k)) = ⨅ q : C k, cost k q := by
    apply le_antisymm
    · refine le_iInf fun q => ?_
      let pi : ∀ j, C j := Function.update (fun j => Classical.choice (hnonempty j)) k q
      exact iInf_le_of_le pi (by simp [pi])
    · exact le_iInf fun pi => iInf_le (fun q => cost k q) (pi k)
  calc
    wasserstein1 _ _ ≤ ⨅ pi : ∀ k, C k, ∑ k, cost k (pi k) := le_iInf hmix
    _ = ∑ k, ⨅ pi : ∀ j, C j, cost k (pi k) := ENNReal.iInf_sum hdir
    _ = ∑ k, ENNReal.ofReal (p k) * wasserstein1 (mu k) (muhat k) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [heval, wasserstein1_eq_couplings]
      exact (ENNReal.mul_iInf (by simp)).symm

/-- Given [a first collection of factor measures](hyp:mu) and
[a second collection on the same factor spaces](hyp:muhat),
if [each factor in both collections is a probability law](hyp:hprob),
[the Wasserstein distance between their independent product laws, with coordinates
concatenated and distance measured by the sum of absolute coordinate differences,
is at most the sum of the paired factor distances](goal). -/
lemma wasserstein_pi_le_probability {n : ℕ} (dims : Fin n → ℕ)
    (mu muhat : ∀ k, Measure (L1Vec (dims k))) -- @realizes \mu_i(probability laws on the respective product-factor spaces)
    (hprob : ∀ k, IsProbabilityMeasure (mu k) ∧ IsProbabilityMeasure (muhat k)) : -- @realizes \mu_i(each product-factor law is a probability law)
    wasserstein1
      ((Measure.pi mu).map (fun x => WithLp.toLp 1 (fun p : Σ k, Fin (dims k) => (x p.1).ofLp p.2)))
      ((Measure.pi muhat).map (fun x => WithLp.toLp 1 (fun p : Σ k, Fin (dims k) => (x p.1).ofLp
        p.2))) ≤
        ∑ k, wasserstein1 (mu k) (muhat k) := by
  classical
  let (k : Fin n) : BorelSpace (L1Vec (dims k)) := ⟨rfl⟩
  let : BorelSpace (WithLp 1 ((Σ k, Fin (dims k)) → ℝ)) := ⟨rfl⟩
  letI (k : Fin n) : IsProbabilityMeasure (mu k) := (hprob k).1
  letI (k : Fin n) : IsProbabilityMeasure (muhat k) := (hprob k).2
  let C (k : Fin n) := couplings (mu k) (muhat k)
  have hnonempty (k : Fin n) : Nonempty (C k) :=
    ⟨⟨(mu k).prod (muhat k), inferInstance, by simp, by simp⟩⟩
  letI (k : Fin n) : Nonempty (C k) := hnonempty k
  let cost (k : Fin n) (pi : C k) : ℝ≥0∞ := ∫⁻ z, edist z.1 z.2 ∂pi.val
  let F (x : ∀ k, L1Vec (dims k)) :=
    WithLp.toLp 1 (fun p : Σ k, Fin (dims k) => (x p.1).ofLp p.2)
  have hF : Measurable F := by
    unfold F
    apply Continuous.measurable
    fun_prop
  have hdist (x y : ∀ k, L1Vec (dims k)) :
      edist (F x) (F y) = ∑ k, edist (x k) (y k) := by
    simp only [F, PiLp.edist_eq_of_L1]
    exact Fintype.sum_sigma _
  have hprod (pi : ∀ k, C k) :
      wasserstein1 ((Measure.pi mu).map F) ((Measure.pi muhat).map F) ≤
        ∑ k, cost k (pi k) := by
    letI (k : Fin n) : IsProbabilityMeasure (pi k).val := (pi k).property.1
    let P := Measure.pi (fun k => (pi k).val)
    let G (z : ∀ k, L1Vec (dims k) × L1Vec (dims k)) :=
      (F (fun k => (z k).1), F (fun k => (z k).2))
    have hG : Measurable G := by fun_prop
    have hfst : P.map (fun z k => (z k).1) = Measure.pi mu := by
      rw [Measure.pi_map_pi (fun k => measurable_fst.aemeasurable)]
      simp only [(pi _).property.2.1]
    have hsnd : P.map (fun z k => (z k).2) = Measure.pi muhat := by
      rw [Measure.pi_map_pi (fun k => measurable_snd.aemeasurable)]
      simp only [(pi _).property.2.2]
    have hcoupling : P.map G ∈ couplings ((Measure.pi mu).map F)
        ((Measure.pi muhat).map F) := by
      refine ⟨Measure.isProbabilityMeasure_map hG.aemeasurable, ?_, ?_⟩
      · rw [Measure.map_map measurable_fst hG, ← hfst,
          Measure.map_map hF (by fun_prop)]
        rfl
      · rw [Measure.map_map measurable_snd hG, ← hsnd,
          Measure.map_map hF (by fun_prop)]
        rfl
    calc
      wasserstein1 _ _ ≤ ∫⁻ z, edist z.1 z.2 ∂P.map G :=
        (wasserstein1_eq_couplings _ _).trans_le (iInf_le_of_le ⟨P.map G, hcoupling⟩ le_rfl)
      _ = ∫⁻ z, ∑ k, edist (z k).1 (z k).2 ∂P := by
        rw [lintegral_map (by fun_prop) hG]
        simp only [G, hdist]
      _ = ∑ k, cost k (pi k) := by
        rw [lintegral_finsetSum _ (fun k _ => by fun_prop)]
        apply Finset.sum_congr rfl
        intro k hk
        exact (measurePreserving_eval (fun k => (pi k).val) k).lintegral_comp
          (f := fun z : L1Vec (dims k) × L1Vec (dims k) => edist z.1 z.2)
          (by fun_prop)
  have hdir (t : Finset (Fin n)) (a b : ∀ k, C k) :
      ∃ c : ∀ k, C k, ∀ k ∈ t,
        cost k (c k) ≤ cost k (a k) ∧ cost k (c k) ≤ cost k (b k) := by
    refine ⟨fun k => if cost k (a k) ≤ cost k (b k) then a k else b k, ?_⟩
    intro k hk
    dsimp only
    split_ifs with h
    · exact ⟨le_rfl, h⟩
    · exact ⟨le_of_not_ge h, le_rfl⟩
  have heval (k : Fin n) :
      (⨅ pi : ∀ j, C j, cost k (pi k)) = ⨅ q : C k, cost k q := by
    apply le_antisymm
    · refine le_iInf fun q => ?_
      let pi : ∀ j, C j := Function.update (fun j => Classical.choice (hnonempty j)) k q
      exact iInf_le_of_le pi (by simp [pi])
    · exact le_iInf fun pi => iInf_le (fun q => cost k q) (pi k)
  calc
    wasserstein1 _ _ ≤ ⨅ pi : ∀ k, C k, ∑ k, cost k (pi k) := le_iInf hprod
    _ = ∑ k, ⨅ pi : ∀ j, C j, cost k (pi k) := ENNReal.iInf_sum hdir
    _ = ∑ k, wasserstein1 (mu k) (muhat k) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [wasserstein1_eq_couplings]
      exact heval k

-- @node: lem:product-err
/-- For [a first finite collection of sigma-finite factor measures](hyp:mu) and
[a second collection on the same factor spaces](hyp:muhat), [the Wasserstein
distance between their independent products, after concatenating coordinates
and using the sum of absolute coordinate differences, is at most the sum of the
paired factor Wasserstein distances](goal). -/
lemma wasserstein_pi_le {n : ℕ} (dims : Fin n → ℕ)
    (mu muhat : ∀ k, Measure (L1Vec (dims k)))
    [∀ k, SigmaFinite (mu k)] [∀ k, SigmaFinite (muhat k)] :
    wasserstein1
      ((Measure.pi mu).map (fun x => WithLp.toLp 1 (fun p : Σ k, Fin (dims k) => (x p.1).ofLp p.2)))
      ((Measure.pi muhat).map (fun x => WithLp.toLp 1 (fun p : Σ k, Fin (dims k) => (x p.1).ofLp
        p.2))) ≤
        ∑ k, wasserstein1 (mu k) (muhat k) := by
  classical
  by_cases hprob : ∀ k, IsProbabilityMeasure (mu k) ∧ IsProbabilityMeasure (muhat k)
  · exact wasserstein_pi_le_probability dims mu muhat hprob
  · -- A factor without a probability coupling makes the right side infinite.
    push Not at hprob
    obtain ⟨k, hk⟩ := hprob
    have htop : wasserstein1 (mu k) (muhat k) = ⊤ := by
      rw [wasserstein1_eq_couplings]
      apply top_unique
      refine le_iInf fun pi => ?_
      letI := pi.property.1
      have hmu : IsProbabilityMeasure (mu k) := by
        rw [← pi.property.2.1]
        exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
      have hmuhat : IsProbabilityMeasure (muhat k) := by
        rw [← pi.property.2.2]
        exact Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
      exact (hk hmu hmuhat).elim
    calc
      wasserstein1 _ _ ≤ ⊤ := le_top
      _ = wasserstein1 (mu k) (muhat k) := htop.symm
      _ ≤ ∑ j, wasserstein1 (mu j) (muhat j) :=
        Finset.single_le_sum (f := fun j => wasserstein1 (mu j) (muhat j))
          (fun j _ => bot_le) (Finset.mem_univ k)

end Papers.TbsNeuralCausalPi

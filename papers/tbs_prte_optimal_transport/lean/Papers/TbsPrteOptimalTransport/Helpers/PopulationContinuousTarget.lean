module
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationContinuousTotalMean
public import Papers.TbsPrteOptimalTransport.TJSpecialization
/-! Identification of the continuous score's population plug-in contrasts. -/
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

-- @node: population_treated_law_unnormalized
/-- Under [the structural model assumptions](hyp:h), [a level ordering consistent
with the baseline and alternative propensities](hyp:hL), and [baseline overlap at
the given positive lower bound](hyp:hov), [for almost every covariate value and
every positive level up to the last level, the treated outcome law multiplied by
the level propensity equals the canonical treated submeasure at that
propensity](goal). -/
lemma population_treated_law_unnormalized (h : StructuralAssumptions M)
    (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (cpi : ℝ)
    (hov : BaselineOverlapWitness M L cpi) :
    ∀ᵐ x ∂xLaw M, ∀ i, 1 ≤ i → i ≤ L.K →
      ENNReal.ofReal (L.pLev i x) • treatedLaw M L i x =
        canonSubmeasure M true x (L.pLev i x) := by
  haveI := M.instKernel_markov
  filter_upwards [population_treated_cdf_unnormalized M h q L hL,
    canonical_submeasure_mass M h true] with x ht hc
  intro i hi hiK
  have hp := hL.2.2.2.2.2.2.2.2.2.2.1 x i (by omega)
  haveI := treatedLaw_isFiniteMeasure M L i x
  haveI : IsFiniteMeasure (canonSubmeasure M true x (L.pLev i x)) := by
    constructor
    rw [hc _ hp]
    simp
  have hm : M.instKernel x (L.S i : Set Z) ≠ 0 := by
    have hs := sum_measureReal_singleton (μ := M.instKernel x) (L.S i)
    change (∑ z ∈ L.S i, (M.instKernel x {z}).toReal) =
      (M.instKernel x (L.S i : Set Z)).toReal at hs
    have hv := hov.2 x i hi hiK
    change cpi ≤ ∑ z ∈ L.S i, (M.instKernel x {z}).toReal at hv
    rw [hs] at hv
    have hpos := hov.1.trans_le hv
    exact fun hz => by simpa [hz] using hpos
  ext B hB
  have hfinite : (ENNReal.ofReal (L.pLev i x) • treatedLaw M L i x) B ≠ ⊤ := by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  apply (ENNReal.toReal_eq_toReal_iff' hfinite (measure_ne_top _ _)).mp
  simpa only [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hp.1] using ht i hiK hm B hB

-- @node: population_treated_integral_unnormalized
/-- Under [the structural model assumptions](hyp:h), [a level ordering consistent
with the baseline and alternative propensities](hyp:hL), and [baseline overlap at
the given positive lower bound](hyp:hov), [for almost every covariate value, at
each positive level up to the last level, the level propensity times any outcome
function's treated-law integral equals its canonical treated-submeasure
integral](goal). -/
lemma population_treated_integral_unnormalized (h : StructuralAssumptions M)
    (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (cpi : ℝ)
    (hov : BaselineOverlapWitness M L cpi) :
    ∀ᵐ x ∂xLaw M, ∀ i, 1 ≤ i → i ≤ L.K → ∀ f : ℝ → ℝ,
      L.pLev i x * (∫ y, f y ∂treatedLaw M L i x) =
        ∫ y, f y ∂canonSubmeasure M true x (L.pLev i x) := by
  filter_upwards [population_treated_law_unnormalized M h q L hL cpi hov] with x hx
  intro i hi hiK f
  rw [← hx i hi hiK, integral_smul_measure, ENNReal.toReal_ofReal
    (hL.2.2.2.2.2.2.2.2.2.2.1 x i (by omega)).1, smul_eq_mul]

-- @node: population_continuous_full_contrast_eq_Jfull
/-- Under [the structural model assumptions](hyp:h), [known outcome
endpoints](hyp:he), [a consistent level ordering](hyp:hL), and [baseline
overlap](hyp:hov), if [the level index is valid](hyp:hk), [the continuous full
contrast evaluated at the true nuisance equals the canonical full outcome
increment for almost every covariate value](goal). -/
lemma population_continuous_full_contrast_eq_Jfull (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (cpi : ℝ)
    (hov : BaselineOverlapWitness M L cpi) (k : ℕ) (hk : k < L.K) :
    ∀ᵐ x ∂xLaw M, contFullJ L (trueNuisance M L) k x = Jfull M L k x := by
  filter_upwards [population_treated_integral_unnormalized M h q L hL cpi hov,
    discrete_Jfull_eq_regression_increment M h he q L hL] with x ht hj
  rw [hj k hk]
  have hplus := ht (k+1) (by omega) (by omega) (fun y => y)
  have hp : positiveValue (trueNuisance M L).pLev (k+1) x = L.pLev (k+1) x := by
    simp [positiveValue, trueNuisance, show 1 ≤ k+1 ∧ k+1 ≤ L.K by omega]
  have hf : fullValue (trueNuisance M L).JfullPlus k x =
      ∫ y, y ∂treatedLaw M L (k+1) x := by
    simp [fullValue, trueNuisance, treatedBandMean, hk]
  rw [contFullJ, hp, hf, hplus]
  by_cases hk0 : k = 0
  · subst k
    have hp0 : L.pLev 0 x = 0 := by
      rw [hL.1 x 0 (by omega)]
      simp [pLevel]
    simp [positiveValue, hp0, g1Canon, canonSubmeasure, selRegion]
  · have hminus := ht k (by omega) hk.le (fun y => y)
    have hp' : positiveValue (trueNuisance M L).pLev k x = L.pLev k x := by
      simp [positiveValue, trueNuisance, show 1 ≤ k ∧ k ≤ L.K by omega]
    have hf' : minusFullValue (trueNuisance M L) k x =
        ∫ y, y ∂treatedLaw M L k x := by
      simp [minusFullValue, trueNuisance, treatedBandMean, hk0, hk, show 1 ≤ k by omega]
    rw [hp', hf', hminus]
    rfl

-- @node: canonical_treated_increment_integral
/-- If [the lower propensity is nonnegative](hyp:ha), [the upper propensity is at
least the lower propensity](hyp:hab), and [the outcome function is integrable
under the canonical treated submeasures at the lower](hyp:hia) and [upper
propensities](hyp:hib), [its integral under their measure difference equals the
upper integral minus the lower integral](goal). -/
lemma canonical_treated_increment_integral (x : X) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (f : ℝ → ℝ)
    (hia : Integrable f (canonSubmeasure M true x a))
    (hib : Integrable f (canonSubmeasure M true x b)) :
    (∫ y, f y ∂(canonSubmeasure M true x b - canonSubmeasure M true x a)) =
      (∫ y, f y ∂canonSubmeasure M true x b) -
        ∫ y, f y ∂canonSubmeasure M true x a := by
  let K := (outcomeKernel (latentMarginal M true)).comap
    (fun u : ℝ => (u, x)) (by fun_prop)
  letI := outcomeKernel_isMarkov (latentMarginal M true)
  let mu := (volume.restrict (Ioc 0 a)).bind K
  let nu := (volume.restrict (Ioc a b)).bind K
  letI : IsFiniteMeasure mu := ⟨(interval_kernel_finite K 0 a).lt_top⟩
  letI : IsFiniteMeasure nu := ⟨(interval_kernel_finite K a b).lt_top⟩
  have hadd : canonSubmeasure M true x b = mu + nu :=
    interval_kernel_add K 0 a b ha hab
  have hinu : Integrable f nu := hib.mono_measure (by
    rw [hadd]
    exact Measure.le_iff.mpr (fun B _ => Measure.le_add_left le_rfl B))
  have himu : Integrable f mu := by
    simpa only [canonSubmeasure, selRegion, Bool.true_eq, if_true, mu, K,
      Kernel.coe_comap, Function.comp_def] using hia
  rw [canonical_treated_increment M x a b ha hab]
  change (∫ y, f y ∂nu) = (∫ y, f y ∂canonSubmeasure M true x b) - ∫ y, f y ∂mu
  rw [hadd, integral_add_measure himu hinu, add_sub_cancel_left]

-- @node: population_continuous_band_contrast_eq_Jband
/-- Under [the structural model assumptions](hyp:h), [known outcome
endpoints](hyp:he), [a consistent level ordering](hyp:hL), and [baseline
overlap](hyp:hov), if [the level index is valid](hyp:hk), [the band index is
valid](hyp:hj), and [the gap outcome law is continuous at both band
boundaries](hyp:hn), [the continuous band contrast at the true nuisance equals the
canonical band outcome increment for almost every covariate value](goal). -/
lemma population_continuous_band_contrast_eq_Jband (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (cpi : ℝ)
    (hov : BaselineOverlapWitness M L cpi) (k j : ℕ)
    (hk : k < L.K) (hj : j < L.l k)
    (hn : GapLawContinuousAtBoundaries M L k j) :
    ∀ᵐ x ∂xLaw M, contJ L (trueNuisance M L) k j x = Jband M false L k j x := by
  filter_upwards [population_treated_integral_unnormalized M h q L hL cpi hov,
    canonical_submeasure_supported M h true,
    continuous_discrete_Jband M h he M.prop q L hL k j hk hj hn] with x ht hs hb
  let band := Ioc (bandBoundary M L k j x) (bandBoundary M L k (j+1) x)
  let f : ℝ → ℝ := band.indicator (fun y => y)
  have ha := hL.2.2.2.2.2.2.2.2.2.2.1 x k (by omega)
  have hab := hL.2.2.2.2.2.2.2.1 x k (k+1) (by omega) (by omega)
  have hi (i : ℕ) (hiK : i ≤ L.K) : Integrable f (canonSubmeasure M true x (L.pLev i x)) := by
    let K := (outcomeKernel (latentMarginal M true)).comap
      (fun u : ℝ => (u, x)) (by fun_prop)
    letI := outcomeKernel_isMarkov (latentMarginal M true)
    letI : IsFiniteMeasure (canonSubmeasure M true x (L.pLev i x)) :=
      ⟨(interval_kernel_finite K 0 (L.pLev i x)).lt_top⟩
    have hid : Integrable (fun y : ℝ => y) (canonSubmeasure M true x (L.pLev i x)) :=
      Integrable.of_bound (by fun_prop) (outcomeMagnitude M)
        (supported_outcome_norm_bound M h he _
          (hs _ (hL.2.2.2.2.2.2.2.2.2.2.1 x i (by omega))))
    exact hid.indicator measurableSet_Ioc
  have hinc := canonical_treated_increment_integral M x _ _ ha.1 hab.le f
    (hi k hk.le) (hi (k+1) (by omega))
  have hplus := ht (k+1) (by omega) (by omega) f
  simp only [f, band, integral_indicator measurableSet_Ioc] at hplus hinc
  have hp : positiveValue (trueNuisance M L).pLev (k+1) x = L.pLev (k+1) x := by
    simp [positiveValue, trueNuisance, show 1 ≤ k+1 ∧ k+1 ≤ L.K by omega]
  have hmean : meanValue (trueNuisance M L).Jplus k j x =
      ∫ y in band, y ∂treatedLaw M L (k+1) x := by
    simp [meanValue, trueNuisance, treatedBandMean, hk, hj.le, band]
  have hw : 0 < L.pLev (k+1) x - L.pLev k x := sub_pos.mpr hab
  rw [hb, ← integral_indicator measurableSet_Ioc, discreteGapLaw,
    integral_smul_measure, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hw.le, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ hw.ne', one_mul]
  change contJ L (trueNuisance M L) k j x = ∫ y, f y ∂_
  rw [show f = band.indicator (fun y => y) from rfl, integral_indicator measurableSet_Ioc]
  rw [hinc, contJ, hp, hmean, hplus]
  by_cases hk0 : k = 0
  · subst k
    have hp0 : L.pLev 0 x = 0 := by
      rw [hL.1 x 0 (by omega)]
      simp [pLevel]
    simp [positiveValue, hp0, canonSubmeasure, selRegion]
  · have hminus := ht k (by omega) hk.le f
    simp only [f, band, integral_indicator measurableSet_Ioc] at hminus
    have hp' : positiveValue (trueNuisance M L).pLev k x = L.pLev k x := by
      simp [positiveValue, trueNuisance, show 1 ≤ k ∧ k ≤ L.K by omega]
    have hm : minusMeanValue (trueNuisance M L).Jminus k j x =
        ∫ y in band, y ∂treatedLaw M L k x := by
      simp [minusMeanValue, trueNuisance, treatedBandMean, hk0, hk,
        show 1 ≤ k by omega, hj.le, band]
    rw [hp', hm, hminus]

-- @node: population_continuous_band_contrast_eq_Jband_of_density
/-- Under [the structural model assumptions](hyp:h), [known outcome
endpoints](hyp:he), [a consistent level ordering](hyp:hL), [baseline
overlap](hyp:hov), [bounded boundary densities](hyp:hd), and [no atom at the lower
outcome endpoint](hyp:h0), if [the level index is valid](hyp:hk) and [the band
index is valid](hyp:hj), [the continuous band contrast at the true nuisance equals
the canonical band outcome increment for almost every covariate value](goal). -/
lemma population_continuous_band_contrast_eq_Jband_of_density
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (q : Z → X → ℝ) (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (hd : BoundaryDensitiesBounded M L) (h0 : NoAtomAtLowerEndpoint M L)
    (k j : ℕ) (hk : k < L.K) (hj : j < L.l k) :
    ∀ᵐ x ∂xLaw M, contJ L (trueNuisance M L) k j x = Jband M false L k j x := by
  apply population_continuous_band_contrast_eq_Jband M h he q L hL cpi hov k j hk hj
  filter_upwards [population_discrete_gap_boundaries_noAtom M h q L hL cpi hov hd h0]
    with x hx
  exact ⟨hx k hk j hj.le, hx k hk (j+1) (by omega)⟩

-- @node: population_continuous_score_mean_eq_target
/-- Under [the structural model assumptions](hyp:h), [known outcome
endpoints](hyp:he), [a measurable policy map preserving the unit interval](hyp:hphi),
[measurability of its candidate derivative evaluated at the baseline
propensity](hyp:hdphi), and [boundedness and Lipschitz continuity of that
derivative](hyp:hDerivative), assume [a positive number of levels](hyp:hK), [a
level ordering consistent with baseline and policy propensities](hyp:hL),
[measurable level propensities](hyp:hlev), [baseline overlap](hyp:hov), [policy
overlap](hyp:hpol), [measurable band boundaries](hyp:hb), [bounded boundary
densities](hyp:hd), and [no atom at the lower outcome endpoint](hyp:h0). Then [the
continuous score evaluated at the true nuisance is integrable and its population
mean equals the discrete policy target using the lower outcome endpoint](goal). -/
lemma population_continuous_score_mean_eq_target
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (hlev : ∀ k, Measurable (L.pLev k)) (cpi : ℝ)
    (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (hb : ∀ k < L.K, ∀ j ≤ L.l k, Measurable (bandBoundary M L k j))
    (hd : BoundaryDensitiesBounded M L) (h0 : NoAtomAtLowerEndpoint M L) :
    Integrable (fun o => psiCont M phi dphi L hK o (trueNuisance M L))
      (observationLaw M) ∧
    (∫ o, psiCont M phi dphi L hK o (trueNuisance M L) ∂observationLaw M) =
      discreteTarget M false L (policyProp phi M.prop) := by
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  haveI := M.instKernel_markov
  obtain ⟨hi, hm⟩ := population_continuous_total_mean_from_overlap M h he phi dphi
    hphi hdphi hDerivative L hK hL hlev cpi hov hpol hb hd h0
  have hobs := M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY))
  have hmap : (observationLaw M).map Prod.fst = xLaw M := by
    simpa only [observationLaw, xLaw, Function.comp_def] using
      Measure.map_map measurable_fst hobs
  have hg k : Measurable (gammaFull M L k) := by
    first | fun_prop | skip
    exact (population_instrument_set_probability_measurable M _).sub
      (population_instrument_set_probability_measurable M _)
  have hgm k j : Measurable (gamma M L k j) :=
    population_instrument_set_probability_measurable M _
  have hgb k : ∀ᵐ x ∂xLaw M, ‖gammaFull M L k x‖ ≤ 1 := by
    apply Eventually.of_forall
    intro x
    have ha := population_instrument_set_probability_range M (higherPolicy L k) x
    have hb := population_instrument_set_probability_range M (higherBaseline L k) x
    change |(∑ z ∈ higherPolicy L k, instProb M z x) -
      (∑ z ∈ higherBaseline L k, instProb M z x)| ≤ 1
    rw [abs_le]
    constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
  have hgmb k j : ∀ᵐ x ∂xLaw M, ‖gamma M L k j x‖ ≤ 1 := by
    apply Eventually.of_forall
    intro x
    have hr := population_instrument_set_probability_range M (policyUnion L k j) x
    change |∑ z ∈ policyUnion L k j, instProb M z x| ≤ 1
    rw [abs_of_nonneg hr.1]
    exact hr.2
  have mf k : Measurable (fun x => gammaFull M L k x *
      contFullJ L (trueNuisance M L) k x) := by
    first | fun_prop | skip
    exact (hg k).mul (population_continuous_full_J_measurable M h.2.2.2.1 _ L hL k)
  have mr k (hk : k < L.K) j (hj : j ∈ Finset.Icc 1 (L.l k)) :
      Measurable (fun x => gamma M L k j x * contJ L (trueNuisance M L) k (j-1) x) := by
    have hj' := Finset.mem_Icc.mp hj
    have hJ := population_continuous_band_J_measurable M h.2.2.2.1 _ L hL k (j-1)
      hk (by omega) (hb k hk (j-1) (by omega)) (hb k hk ((j-1)+1) (by omega))
    exact (hgm k j).mul hJ
  have ifull k : Integrable (fun x => gammaFull M L k x *
      contFullJ L (trueNuisance M L) k x) (xLaw M) := by
    have ig := Integrable.of_bound (hg k).aestronglyMeasurable 1 (hgb k)
    simpa only [mul_comm] using ig.bdd_mul
      (population_continuous_full_J_measurable M h.2.2.2.1 _ L hL k).aestronglyMeasurable
      (population_contFullJ_norm_bound M h he _ L hL k)
  have ireg k (hk : k < L.K) j (hj : j ∈ Finset.Icc 1 (L.l k)) :
      Integrable (fun x => gamma M L k j x * contJ L (trueNuisance M L) k (j-1) x)
        (xLaw M) := by
    have hj' := Finset.mem_Icc.mp hj
    have ig := Integrable.of_bound (hgm k j).aestronglyMeasurable 1 (hgmb k j)
    have hJ := population_continuous_band_J_measurable M h.2.2.2.1 _ L hL k (j-1)
      hk (by omega) (hb k hk (j-1) (by omega)) (hb k hk ((j-1)+1) (by omega))
    simpa only [mul_comm] using ig.bdd_mul hJ.aestronglyMeasurable
      (population_contJ_norm_bound M h he _ L hL k (j-1) hk (by omega))
  have hq := population_policyProp_measurable M h.2.2.2.1 phi hphi
  have itail : Integrable (tailContribution M false L (policyProp phi M.prop)) (xLaw M) := by
    apply Integrable.const_mul
    apply integrable_finsetSum
    intro z hz
    have miz : Measurable (instProb M z) :=
      (Kernel.measurable_coe _ (measurableSet_singleton z)).ennreal_toReal
    apply Integrable.of_bound
      (miz.mul ((hq.comp (measurable_const.prodMk measurable_id)).sub (hlev L.K))).aestronglyMeasurable 2
    apply Eventually.of_forall
    intro x
    have hqr := hphi.2 z x (M.prop z x) (M.rangeProp _ _)
    have hpr := hL.2.2.2.2.2.2.2.2.2.2.1 x L.K (by omega)
    have hdiff : |policyProp phi M.prop z x - L.pLev L.K x| ≤ 2 := by
      change |phi z x (M.prop z x) - L.pLev L.K x| ≤ 2
      rw [abs_le]
      constructor <;> linarith [hqr.1, hqr.2, hpr.1, hpr.2]
    have hip : |instProb M z x| ≤ 1 := by
      rw [instProb, abs_of_nonneg ENNReal.toReal_nonneg]
      exact measureReal_le_one
    simpa only [Pi.mul_apply, Pi.sub_apply, Function.comp_apply, id_eq,
      Real.norm_eq_abs, abs_mul, one_mul] using
      mul_le_mul hip hdiff (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have hfull : ∀ᵐ x ∂xLaw M, ∀ k < L.K,
      contFullJ L (trueNuisance M L) k x = Jfull M L k x := by
    simp only [ae_all_iff]
    exact fun k hk => population_continuous_full_contrast_eq_Jfull M h he _ L hL cpi hov k hk
  have hband : ∀ᵐ x ∂xLaw M, ∀ k < L.K, ∀ j < L.l k,
      contJ L (trueNuisance M L) k j x = Jband M false L k j x := by
    simp only [ae_all_iff]
    exact fun k hk j hj => population_continuous_band_contrast_eq_Jband_of_density
      M h he _ L hL cpi hov hd h0 k j hk hj
  have icomp k (hk : k ∈ Finset.range L.K) :=
    (ifull k).fun_add (integrable_finsetSum _ (ireg k (Finset.mem_range.mp hk)))
  refine ⟨hi, hm.trans ?_⟩
  have mfull k : (∫ o : Obs X Z, gammaFull M L k o.1 *
      contFullJ L (trueNuisance M L) k o.1 ∂observationLaw M) =
      ∫ x, gammaFull M L k x * contFullJ L (trueNuisance M L) k x ∂xLaw M := by
    rw [← hmap]
    exact (integral_map measurable_fst.aemeasurable (mf k).aestronglyMeasurable).symm
  have mreg k (hk : k < L.K) j (hj : j ∈ Finset.Icc 1 (L.l k)) :
      (∫ o : Obs X Z, gamma M L k j o.1 * contJ L (trueNuisance M L) k (j-1) o.1
        ∂observationLaw M) =
      ∫ x, gamma M L k j x * contJ L (trueNuisance M L) k (j-1) x ∂xLaw M := by
    rw [← hmap]
    exact (integral_map measurable_fst.aemeasurable (mr k hk j hj).aestronglyMeasurable).symm
  have mprefix :
      (∑ k ∈ Finset.range L.K,
        ((∫ o : Obs X Z, gammaFull M L k o.1 * contFullJ L (trueNuisance M L) k o.1
          ∂observationLaw M) + ∑ j ∈ Finset.Icc 1 (L.l k),
          ∫ o : Obs X Z, gamma M L k j o.1 * contJ L (trueNuisance M L) k (j-1) o.1
            ∂observationLaw M)) =
      ∫ x, ∑ k ∈ Finset.range L.K, (gammaFull M L k x *
        contFullJ L (trueNuisance M L) k x + ∑ j ∈ Finset.Icc 1 (L.l k),
          gamma M L k j x * contJ L (trueNuisance M L) k (j-1) x) ∂xLaw M := by
    rw [integral_finsetSum _ icomp]
    apply Finset.sum_congr rfl
    intro k hk
    rw [integral_add (ifull k)
      (integrable_finsetSum _ (ireg k (Finset.mem_range.mp hk))),
      integral_finsetSum _ (ireg k (Finset.mem_range.mp hk)), mfull]
    congr 1
    exact Finset.sum_congr rfl (fun j hj => mreg k (Finset.mem_range.mp hk) j hj)
  rw [mprefix, ← integral_add (integrable_finsetSum _ icomp) itail]
  unfold discreteTarget
  apply integral_congr_ae
  filter_upwards [hfull, hband] with x hf hr
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [hf k (Finset.mem_range.mp hk)]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_Icc.mp hj
  rw [hr k (Finset.mem_range.mp hk) (j-1) (by omega)]

end Papers.TbsPrteOptimalTransport

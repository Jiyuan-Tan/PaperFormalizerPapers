module
public import Papers.TbsPrteOptimalTransport.Helpers.JointAttainment
/-! Cumulative observational constraints of the pasted attaining kernel. -/
public section
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

-- @node: markov_evaluation_integrable
/-- For a probability kernel and a finite integrating measure, if [the outcome event is
measurable](hyp:hB), [its conditional probability is an integrable real-valued function](goal). -/
lemma markov_evaluation_integrable {A : Type*} [MeasurableSpace A]
    (mu : Measure A) [IsFiniteMeasure mu] (K : Kernel A ℝ) [IsMarkovKernel K]
    (B : Set ℝ) (hB : MeasurableSet B) :
    Integrable (fun a => (K a B).toReal) mu := by
  have hm : Measurable (fun a => (K a B).toReal) :=
    (K.measurable_coe hB).ennreal_toReal
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  filter_upwards [] with a
  rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  exact (ENNReal.toReal_mono (by simp) (prob_le_one)).trans_eq (by simp)

-- @node: markov_bind_evaluation_integral
/-- If [the outcome event is measurable](hyp:hB), [integrating its conditional probability
under a probability kernel gives its real-valued measure under the resulting mixture](goal). -/
lemma markov_bind_evaluation_integral {A : Type*} [MeasurableSpace A]
    (mu : Measure A) (K : Kernel A ℝ) [IsMarkovKernel K]
    (B : Set ℝ) (hB : MeasurableSet B) :
    (∫ a, (K a B).toReal ∂mu) = (mu.bind K B).toReal := by
  rw [Measure.bind_apply hB (by fun_prop)]
  exact integral_toReal (K.measurable_coe hB).aemeasurable
    (Eventually.of_forall fun a => measure_lt_top (K a) B)

-- @node: range_cumulative_integral_eq
/-- If [a finite interval decomposition represents the propensity range](hyp:hD),
[the first function](hyp:hf) and [the second function](hyp:hg) are integrable on the unit interval,
[their integrals agree on every gap](hyp:hgap), and [they agree almost everywhere on each
local-instrumental-variable interval](hyp:hliv), then [at any point in the propensity range](hyp:hp)
[their cumulative integrals from zero, excluding zero and including that point, agree](goal). -/
lemma range_cumulative_integral_eq (D : RangeData) (R : Set ℝ) (hD : D.Valid R)
    (f g : ℝ → ℝ) (hf : IntegrableOn f (Icc (0 : ℝ) 1))
    (hg : IntegrableOn g (Icc (0 : ℝ) 1))
    (hgap : ∀ k < D.count,
      (∫ u in RangeDecomposition.gap D k, f u) =
        ∫ u in RangeDecomposition.gap D k, g u)
    (hliv : ∀ k < D.count, f =ᵐ[volume.restrict (D.liv k)] g)
    (p : ℝ) (hp : p ∈ R) :
    (∫ u in Ioc 0 p, f u) = ∫ u in Ioc 0 p, g u := by
  rw [hD.2.2] at hp
  obtain ⟨i, hi⟩ := mem_iUnion.mp hp
  let k : ℕ := i.val
  have hk : k < D.count := i.isLt
  have hk' : k < D.1 := hk
  have hb := range_endpoint_bounds D R hD hk
  have hlo := range_gapLo_bounds D R hD hk
  have hip : D.low k ≤ p ∧ p ≤ D.high k := by
    simpa only [RangeData.low, RangeData.high, dif_pos hk', mem_Icc] using hi
  have hprefix : (∫ u in Ioc 0 (D.gapLo k), f u) =
      ∫ u in Ioc 0 (D.gapLo k), g u := by
    have hpf := range_prefix_integral D R hD f hf k hk.le
    have hpg := range_prefix_integral D R hD g hg k hk.le
    change (∫ u in Ioc 0 (if k = 0 then 0 else D.high (k-1)), f u) = _
    rw [hpf]
    change _ = ∫ u in Ioc 0 (if k = 0 then 0 else D.high (k-1)), g u
    rw [hpg]
    congr 1
    · exact Finset.sum_congr rfl fun j hj => hgap j ((Finset.mem_range.mp hj).trans hk)
    · exact Finset.sum_congr rfl fun j hj =>
        integral_congr_ae (hliv j ((Finset.mem_range.mp hj).trans hk))
  have hpartial : (∫ u in Ioc (D.low k) p, f u) =
      ∫ u in Ioc (D.low k) p, g u := by
    apply integral_congr_ae
    apply (hliv k hk).filter_mono
    apply ae_mono (Measure.restrict_mono_set volume _)
    intro u hu
    exact ⟨hu.1.le, hu.2.trans hip.2⟩
  have hfi := hf.mono_set (show Ioc 0 p ⊆ Icc (0 : ℝ) 1 from
    fun u hu => ⟨hu.1.le, hu.2.trans (hip.2.trans hb.2.2)⟩)
  have hgi := hg.mono_set (show Ioc 0 p ⊆ Icc (0 : ℝ) 1 from
    fun u hu => ⟨hu.1.le, hu.2.trans (hip.2.trans hb.2.2)⟩)
  rw [integral_adjacent_Ioc f hlo.1 (hlo.2.trans hip.1) hfi,
    integral_adjacent_Ioc g hlo.1 (hlo.2.trans hip.1) hgi, hprefix]
  congr 1
  rw [integral_adjacent_Ioc f hlo.2 hip.1
      (hfi.mono_set (Ioc_subset_Ioc_left hlo.1)),
    integral_adjacent_Ioc g hlo.2 hip.1
      (hgi.mono_set (Ioc_subset_Ioc_left hlo.1)), hpartial]
  simp only [integral_Ioc_eq_integral_Ioo]
  have hgapk := hgap k hk
  rw [range_gap_eq_Ioo_of_valid D R hD k hk] at hgapk
  exact congrArg (fun v => v + ∫ u in Ioo (D.low k) p, g u) hgapk

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z]
variable (M : LatentIVModel Ω X Z)

-- @node: attaining_version_gap_evaluation
/-- Under [the structural assumptions](hyp:h), [continuity of propensities on instrument
components](hyp:hc), and [finitely many instrument components](hyp:hfin), suppose
[the target weight is measurable](hyp:hm), [the rank specification has a kernel-extension
interpretation](hyp:hQ), and [the chosen kernel is an attaining version for that weight
and specification](hyp:hK). Then [for almost every covariate value, on every propensity-range
gap and for every measurable outcome event, its integrated conditional probability equals
that of the original treated latent-outcome kernel](goal). -/
lemma attaining_version_gap_evaluation (h : StructuralAssumptions M)
    (hc : PropensityContinuousOnComponents M) (hfin : FiniteInstrumentComponents Z)
    (om : X → ℝ → ℝ) (hm : TargetWeightMeasurable om)
    (Q : X → ℕ → ℝ → ℝ) (hQ : RankKernelExtensionReading M Q)
    (K : Kernel (ℝ × X) ℝ) (hK : IsAttainingKernelVersion M om Q K) :
    ∀ᵐ x ∂xLaw M, ∀ k < (CondRangeDecomposition M x).count,
      ∀ B : Set ℝ, MeasurableSet B →
      (∫ u in RangeDecomposition.gap (CondRangeDecomposition M x) k,
        (K (u, x) B).toReal) =
      ∫ u in RangeDecomposition.gap (CondRangeDecomposition M x) k,
        (outcomeKernel (latentMarginal M true) (u, x) B).toReal := by
  letI := hK.1
  letI := outcomeKernel_isMarkov (latentMarginal M true)
  filter_upwards [hK.2.2.2, gap_attaining_canonical_increment M h hc hfin om hm Q hQ]
    with x hx hinc
  intro k hk B hB
  let D := CondRangeDecomposition M x
  by_cases hab : D.gapLo k < D.gapHi k
  · let Kx := K.comap (fun u : ℝ => (u, x)) (by fun_prop)
    let K0 := (outcomeKernel (latentMarginal M true)).comap
      (fun u : ℝ => (u, x)) (by fun_prop)
    have hbind : (volume.restrict (RangeDecomposition.gap D k)).bind Kx =
        (volume.restrict (RangeDecomposition.gap D k)).bind K0 := by
      calc
        _ = (volume.restrict (RangeDecomposition.gap D k)).bind
            (gapAttainingLaw M om Q x k) := by
          apply Measure.bind_congr_right
          filter_upwards [ae_restrict_mem (measurableSet_Ioo.inter measurableSet_Icc)] with u hu
          exact hx k hk u hu
        _ = canonSubmeasure M true x (D.gapHi k) -
            canonSubmeasure M true x (D.gapLo k) := hinc k hk hab
        _ = (volume.restrict (RangeDecomposition.gap D k)).bind K0 := by
          rw [canonical_treated_increment M x _ _
            (conditional_gap_endpoints M x k hk).1.1 hab.le]
          rw [conditional_gap_eq_Ioo M x k hk]
          change (volume.restrict (Ioc _ _)).bind K0 =
            (volume.restrict (Ioo _ _)).bind K0
          rw [restrict_Ioo_eq_restrict_Ioc]
    exact (markov_bind_evaluation_integral _ Kx B hB).trans
      ((congrArg (fun mu : Measure ℝ => (mu B).toReal) hbind).trans
        (markov_bind_evaluation_integral _ K0 B hB).symm)
  · have hz : RangeDecomposition.gap D k = ∅ := by
      rw [conditional_gap_eq_Ioo M x k hk]
      exact Ioo_eq_empty_of_le (le_of_not_gt hab)
    change (∫ u in RangeDecomposition.gap D k, (K (u, x) B).toReal) =
      ∫ u in RangeDecomposition.gap D k, (outcomeKernel (latentMarginal M true) (u, x) B).toReal
    simp only [hz, Measure.restrict_empty, integral_zero_measure]

-- @node: attaining_version_liv_evaluation
/-- Under [the structural assumptions](hyp:h), [continuity of propensities on instrument
components](hyp:hc), and [finitely many instrument components](hyp:hfin), if [the chosen
kernel is an attaining version for the target weight and rank specification](hyp:hK),
[for almost every covariate value it agrees with the original treated latent-outcome kernel
almost everywhere on every local-instrumental-variable interval](goal). -/
lemma attaining_version_liv_evaluation (h : StructuralAssumptions M)
    (hc : PropensityContinuousOnComponents M) (hfin : FiniteInstrumentComponents Z)
    (om : X → ℝ → ℝ) (Q : X → ℕ → ℝ → ℝ)
    (K : Kernel (ℝ × X) ℝ) (hK : IsAttainingKernelVersion M om Q K) :
    ∀ᵐ x ∂xLaw M, ∀ k < (CondRangeDecomposition M x).count,
      K ∘ (fun u => (u, x)) =ᵐ[volume.restrict ((CondRangeDecomposition M x).liv k)]
        outcomeKernel (latentMarginal M true) ∘ (fun u => (u, x)) := by
  filter_upwards [attaining_version_section_eq M om Q K hK,
    range_decomposition_valid M h hfin hc] with x hx hv
  intro k hk
  have hs := liv_interval_range _ _ hv ⟨k, hk⟩
  filter_upwards [hx.filter_mono (ae_mono (Measure.restrict_mono_set volume hs)),
    ae_restrict_mem measurableSet_Icc] with u hu humem
  exact hu.trans (pasted_attaining_law_on_liv M om Q x hv k hk u humem)

-- @node: attaining_version_cumulative_evaluation
/-- Under [the structural assumptions](hyp:h), [continuity of propensities on instrument
components](hyp:hc), and [finitely many instrument components](hyp:hfin), suppose
[the target weight is measurable](hyp:hm), [the rank specification admits the prescribed
kernel-extension interpretation](hyp:hQ), and [the chosen kernel is an attaining version](hyp:hK).
Then [for almost every covariate value, every attainable propensity, and every measurable
outcome event, integrating the kernel's event probability over ranks above zero and up to
that propensity gives the canonical treated submeasure of the event](goal). -/
lemma attaining_version_cumulative_evaluation (h : StructuralAssumptions M)
    (hc : PropensityContinuousOnComponents M) (hfin : FiniteInstrumentComponents Z)
    (om : X → ℝ → ℝ) (hm : TargetWeightMeasurable om)
    (Q : X → ℕ → ℝ → ℝ) (hQ : RankKernelExtensionReading M Q)
    (K : Kernel (ℝ × X) ℝ) (hK : IsAttainingKernelVersion M om Q K) :
    ∀ᵐ x ∂xLaw M, ∀ p ∈ range (fun z => M.prop z x),
      ∀ B : Set ℝ, MeasurableSet B →
      (∫ u in Ioc 0 p, (K (u, x) B).toReal) =
        (canonSubmeasure M true x p B).toReal := by
  letI := hK.1
  letI := outcomeKernel_isMarkov (latentMarginal M true)
  filter_upwards [attaining_version_gap_evaluation M h hc hfin om hm Q hQ K hK,
    attaining_version_liv_evaluation M h hc hfin om Q K hK,
    range_decomposition_valid M h hfin hc] with x hgap hliv hv
  intro p hp B hB
  let Kx := K.comap (fun u : ℝ => (u, x)) (by fun_prop)
  let K0 := (outcomeKernel (latentMarginal M true)).comap
    (fun u : ℝ => (u, x)) (by fun_prop)
  calc
    _ = ∫ u in Ioc 0 p, (K0 u B).toReal := by
      apply range_cumulative_integral_eq _ _ hv
        (fun u => (Kx u B).toReal) (fun u => (K0 u B).toReal)
        (markov_evaluation_integrable _ Kx B hB)
        (markov_evaluation_integrable _ K0 B hB)
        (fun k hk => hgap k hk B hB) _ p hp
      intro k hk
      exact (hliv k hk).mono fun u hu => congrArg (fun mu : Measure ℝ => (mu B).toReal) hu
    _ = _ := markov_bind_evaluation_integral _ K0 B hB

-- @node: supported_joint_outcomeKernel_eq
/-- For a probability kernel of outcomes given rank and covariates, [forming a joint law
by drawing an independent uniform rank and the population covariates, then drawing an outcome
from the kernel, recovers that kernel as the joint law's conditional outcome kernel almost
everywhere under the rank-covariate distribution](goal). -/
lemma supported_joint_outcomeKernel_eq (K : Kernel (ℝ × X) ℝ) [IsMarkovKernel K] :
    outcomeKernel ((Causalean.Stat.unifOI.prod (xLaw M)).bind
      (fun ux => (K ux).map (fun y => (ux, y)))) =ᵐ[Causalean.Stat.unifOI.prod (xLaw M)] K := by
  haveI : IsProbabilityMeasure (xLaw M) :=
    Measure.isProbabilityMeasure_map M.measX.aemeasurable
  rw [kernel_joint_bind_eq_compProd]
  unfold outcomeKernel
  rw [dif_pos (inferInstance : IsFiniteMeasure ((Causalean.Stat.unifOI.prod (xLaw M)) ⊗ₘ K))]
  exact condKernel_compProd _ K

-- @node: supported_joint_outcomeKernel_section_eq
/-- For a probability kernel of outcomes given rank and covariates, [the conditional outcome
kernel of its induced joint law equals the original kernel for almost every covariate value
and Lebesgue-almost every rank in the closed unit interval](goal). -/
lemma supported_joint_outcomeKernel_section_eq (K : Kernel (ℝ × X) ℝ) [IsMarkovKernel K] :
    ∀ᵐ x ∂xLaw M, ∀ᵐ u ∂volume.restrict (Icc (0 : ℝ) 1),
      outcomeKernel ((Causalean.Stat.unifOI.prod (xLaw M)).bind
        (fun ux => (K ux).map (fun y => (ux, y)))) (u, x) = K (u, x) := by
  haveI : IsProbabilityMeasure (xLaw M) :=
    Measure.isProbabilityMeasure_map M.measX.aemeasurable
  have hswap : ∀ᵐ xu ∂(xLaw M).prod Causalean.Stat.unifOI,
      outcomeKernel ((Causalean.Stat.unifOI.prod (xLaw M)).bind
        (fun ux => (K ux).map (fun y => (ux, y)))) (xu.2, xu.1) = K (xu.2, xu.1) := by
    have hh : ∀ᵐ ux ∂((xLaw M).prod Causalean.Stat.unifOI).map Prod.swap,
        outcomeKernel ((Causalean.Stat.unifOI.prod (xLaw M)).bind
          (fun ux => (K ux).map (fun y => (ux, y)))) ux = K ux := by
      rw [Measure.prod_swap]
      exact supported_joint_outcomeKernel_eq M K
    exact ae_of_ae_map measurable_swap.aemeasurable hh
  simpa only [Causalean.Stat.unifOI, restrict_Ioo_eq_restrict_Icc] using
    Measure.ae_ae_of_ae_prod hswap

-- @node: attaining_version_joint_compatible
/-- Under [the structural assumptions](hyp:h), [continuity of propensities on instrument
components](hyp:hc), and [finitely many instrument components](hyp:hfin), if [the target
weight is measurable](hyp:hm), [the rank specification has the required kernel-extension
interpretation](hyp:hQ), and [the chosen kernel is an attaining version](hyp:hK), [the joint
law obtained by combining independent uniform ranks and population covariates with that
kernel satisfies the treated observational compatibility restrictions](goal). -/
lemma attaining_version_joint_compatible (h : StructuralAssumptions M)
    (hc : PropensityContinuousOnComponents M) (hfin : FiniteInstrumentComponents Z)
    (om : X → ℝ → ℝ) (hm : TargetWeightMeasurable om)
    (Q : X → ℕ → ℝ → ℝ) (hQ : RankKernelExtensionReading M Q)
    (K : Kernel (ℝ × X) ℝ) (hK : IsAttainingKernelVersion M om Q K) :
    TreatedCompatible (transportData M) ((Causalean.Stat.unifOI.prod (xLaw M)).bind
      (fun ux => (K ux).map (fun y => (ux, y)))) := by
  apply treated_compatible_of_toReal M
  letI := hK.1
  have hcum := attaining_version_cumulative_evaluation M h hc hfin om hm Q hQ K hK
  have hsec := supported_joint_outcomeKernel_section_eq M K
  have hmap : (zxLaw M).map Prod.snd = xLaw M := by
    rw [zxLaw, Measure.map_map measurable_snd (M.measZ.prodMk M.measX)]
    rfl
  have hgood := hcum.and hsec
  rw [← hmap] at hgood
  have hzx := ae_of_ae_map measurable_snd.aemeasurable hgood
  change ∀ᵐ zx ∂zxLaw M, ∀ B : Set ℝ, MeasurableSet B → _
  filter_upwards [hzx] with zx hx
  intro B hB
  calc
    _ = ∫ u in Ioc 0 (M.prop zx.1 zx.2), (K (u, zx.2) B).toReal := by
      apply integral_congr_ae
      have hs : Ioc 0 (M.prop zx.1 zx.2) ⊆ Icc (0 : ℝ) 1 :=
        fun u hu => ⟨hu.1.le, hu.2.trans (M.rangeProp zx.1 zx.2).2⟩
      filter_upwards [hx.2.filter_mono (ae_mono (Measure.restrict_mono_set volume hs))]
        with u hu
      rw [hmap] at hu
      rw [hu]
    _ = _ := hx.1 _ (mem_range_self zx.1) B hB

end Papers.TbsPrteOptimalTransport

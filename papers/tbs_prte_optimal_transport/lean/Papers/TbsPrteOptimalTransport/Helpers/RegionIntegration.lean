module
public import Papers.TbsPrteOptimalTransport.Helpers.RegionPartition
public import Papers.TbsPrteOptimalTransport.Helpers.LIVPart
/-! Integration over the ordered conditional gap, LIV, and tail regions. -/
public section
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

-- @node: range_endpoint_bounds
/-- If [the range decomposition is valid for R](hyp:hD) and
[k indexes an available component](hyp:hk), then
[its endpoints satisfy zero ≤ lower endpoint ≤ upper endpoint ≤ one](goal). -/
lemma range_endpoint_bounds (D : RangeData) (R : Set ℝ) (hD : D.Valid R)
    {k : ℕ} (hk : k < D.count) :
    0 ≤ D.low k ∧ D.low k ≤ D.high k ∧ D.high k ≤ 1 := by
  have hk' : k < D.1 := hk
  simpa only [RangeData.low, RangeData.high, dif_pos hk'] using hD.1 ⟨k, hk'⟩

-- @node: range_gapLo_bounds
/-- If [the range decomposition is valid for R](hyp:hD) and
[k indexes an available component](hyp:hk), then
[the lower endpoint of its preceding gap lies between zero and component k's
lower endpoint](goal). -/
lemma range_gapLo_bounds (D : RangeData) (R : Set ℝ) (hD : D.Valid R)
    {k : ℕ} (hk : k < D.count) : 0 ≤ D.gapLo k ∧ D.gapLo k ≤ D.low k := by
  by_cases hz : k = 0
  · subst k
    simpa only [RangeData.gapLo, ↓reduceIte] using
      And.intro (le_refl (0 : ℝ)) (range_endpoint_bounds D R hD hk).1
  · have hp : k - 1 < D.count := by omega
    have hb := range_endpoint_bounds D R hD hp
    rw [RangeData.gapLo, if_neg hz]
    exact ⟨hb.1.trans hb.2.1,
      (range_high_lt_low D R hD (show k - 1 < k by omega) hk).le⟩

-- @node: integral_adjacent_Ioc
/-- If [a is at most b](hyp:hab), [b is at most c](hyp:hbc), and
[f is integrable between a and c, excluding a and including c](hyp:hf), then
[its integral on that interval is the sum of its integrals from a to b and from b
to c, each excluding its left endpoint and including its right endpoint](goal). -/
lemma integral_adjacent_Ioc (f : ℝ → ℝ) {a b c : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hf : IntegrableOn f (Ioc a c)) :
    (∫ u in Ioc a c, f u) = (∫ u in Ioc a b, f u) + ∫ u in Ioc b c, f u := by
  rw [← Ioc_union_Ioc_eq_Ioc hab hbc]
  exact setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
    (hf.mono_set (Ioc_subset_Ioc_right hbc))
    (hf.mono_set (Ioc_subset_Ioc_left hab))

-- @node: range_prefix_integral
/-- If [the range decomposition is valid for R](hyp:hD),
[f is integrable on the closed unit interval](hyp:hf), and
[n does not exceed the number of components](hyp:hn), then
[the integral from zero, excluded, to the upper endpoint of the first n components
equals the sum of the integrals over their gaps and LIV intervals, with a zero
integral when n is zero](goal). -/
lemma range_prefix_integral (D : RangeData) (R : Set ℝ) (hD : D.Valid R)
    (f : ℝ → ℝ) (hf : IntegrableOn f (Icc (0 : ℝ) 1))
    (n : ℕ) (hn : n ≤ D.count) :
    (∫ u in Ioc 0 (if n = 0 then 0 else D.high (n - 1)), f u) =
      (∑ k ∈ Finset.range n, ∫ u in RangeDecomposition.gap D k, f u) +
      ∑ k ∈ Finset.range n, ∫ u in D.liv k, f u := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hk : n < D.count := by omega
    have hb := range_endpoint_bounds D R hD hk
    have hg := range_gapLo_bounds D R hD hk
    have hi : IntegrableOn f (Ioc 0 (D.high n)) :=
      hf.mono_set (fun u hu => ⟨hu.1.le, hu.2.trans hb.2.2⟩)
    have hi' : IntegrableOn f (Ioc (D.gapLo n) (D.high n)) :=
      hf.mono_set (fun u hu => ⟨hg.1.trans hu.1.le, hu.2.trans hb.2.2⟩)
    have hsplit := integral_adjacent_Ioc f hg.1 (hg.2.trans hb.2.1) hi
    have hsplit' := integral_adjacent_Ioc f hg.2 hb.2.1 hi'
    have hprev : (∫ u in Ioc 0 (D.gapLo n), f u) =
        (∑ k ∈ Finset.range n, ∫ u in RangeDecomposition.gap D k, f u) +
        ∑ k ∈ Finset.range n, ∫ u in D.liv k, f u := by
      simpa only [RangeData.gapLo] using ih (by omega)
    simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte,
      Nat.add_sub_cancel, Finset.sum_range_succ]
    rw [hsplit, hsplit', hprev, integral_Ioc_eq_integral_Ioo,
      ← integral_Icc_eq_integral_Ioc]
    rw [range_gap_eq_Ioo_of_valid D R hD n hk]
    change _ = _ + (∫ u in Ioo (D.gapLo n) (D.low n), f u) +
      (_ + ∫ u in Icc (D.low n) (D.high n), f u)
    ring

-- @node: range_regions_integral
/-- If [the range decomposition is valid for R](hyp:hD) and
[f is integrable on the closed unit interval](hyp:hf), then
[its integral on that interval equals the sum of all gap integrals, all LIV interval
integrals, and the tail integral](goal). -/
lemma range_regions_integral (D : RangeData) (R : Set ℝ) (hD : D.Valid R)
    (f : ℝ → ℝ) (hf : IntegrableOn f (Icc (0 : ℝ) 1)) :
    (∫ u in Icc (0 : ℝ) 1, f u) =
      (∑ k ∈ Finset.range D.count, ∫ u in RangeDecomposition.gap D k, f u) +
      (∑ k ∈ Finset.range D.count, ∫ u in D.liv k, f u) +
      ∫ u in D.tail, f u := by
  have hb : 0 ≤ D.tailLo ∧ D.tailLo ≤ 1 := by
    by_cases hz : D.count = 0
    · simp [RangeData.tailLo, hz]
    · have hk : D.count - 1 < D.count := by omega
      have he := range_endpoint_bounds D R hD hk
      simpa only [RangeData.tailLo, if_neg hz] using
        And.intro (he.1.trans he.2.1) he.2.2
  rw [integral_Icc_eq_integral_Ioc,
    integral_adjacent_Ioc f hb.1 hb.2 (hf.mono_set Ioc_subset_Icc_self)]
  exact congrArg (fun v => v + ∫ u in D.tail, f u)
    (range_prefix_integral D R hD f hf D.count le_rfl)

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z]
variable (M : LatentIVModel Ω X Z)

-- @node: supported_kernel_weighted_integrable
/-- Under [the structural assumptions](hyp:h) and [known outcome endpoints](hyp:he),
if [the probability kernel is supported on the outcome set at almost every rank
under the rank measure](hyp:hs) and [the weight is integrable under that measure](hyp:hi),
then [the kernel's mean outcome multiplied by the weight is also integrable](goal). -/
lemma supported_kernel_weighted_integrable (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) (mu : Measure ℝ) (K : Kernel ℝ ℝ)
    [IsMarkovKernel K] (hs : ∀ᵐ u ∂mu, K u M.Ysetᶜ = 0)
    (w : ℝ → ℝ) (hi : Integrable w mu) :
    Integrable (fun u => (∫ y, y ∂K u) * w u) mu := by
  have hm : AEStronglyMeasurable (fun u => ∫ y, y ∂K u) mu := by
    exact (stronglyMeasurable_id.integral_kernel (κ := K)).aestronglyMeasurable
  have hb : ∀ᵐ u ∂mu, ‖∫ y, y ∂K u‖ ≤ outcomeMagnitude M := by
    filter_upwards [hs] with u hu
    simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using
      norm_integral_le_of_norm_le_const (supported_outcome_norm_bound M h he (K u) hu)
  exact hi.bdd_mul hm hb

-- @node: attaining_version_section_eq
/-- If [K is an attaining kernel version for the target weight and rank extension](hyp:hK),
then [for almost every covariate value, K equals the pasted attaining law at
Lebesgue-almost every rank in the closed unit interval](goal). -/
lemma attaining_version_section_eq (om : X → ℝ → ℝ) (Q : X → ℕ → ℝ → ℝ)
    (K : Kernel (ℝ × X) ℝ) (hK : IsAttainingKernelVersion M om Q K) :
    ∀ᵐ x ∂xLaw M, ∀ᵐ u ∂volume.restrict (Icc (0 : ℝ) 1),
      K (u, x) = pastedAttainingLaw M om Q x u := by
  haveI : IsProbabilityMeasure (xLaw M) := Measure.isProbabilityMeasure_map M.measX.aemeasurable
  have hswap : ∀ᵐ xu ∂(xLaw M).prod Causalean.Stat.unifOI,
      K (xu.2, xu.1) = pastedAttainingLaw M om Q xu.1 xu.2 := by
    have hh : ∀ᵐ ux ∂((xLaw M).prod Causalean.Stat.unifOI).map Prod.swap,
        K ux = pastedAttainingLaw M om Q ux.2 ux.1 := by
      rw [Measure.prod_swap]
      exact hK.2.2.1
    exact ae_of_ae_map measurable_swap.aemeasurable hh
  simpa only [Causalean.Stat.unifOI, restrict_Ioo_eq_restrict_Icc] using
    Measure.ae_ae_of_ae_prod hswap

-- @node: attaining_version_section_integrable
/-- Under [the structural assumptions](hyp:h) and [known outcome endpoints](hyp:he),
if [the target weight is integrable](hyp:hi) and
[K is an attaining kernel version for that weight and rank extension](hyp:hK), then
[for almost every covariate value, the target-weighted mean outcome under K is
integrable over the closed unit interval of ranks](goal). -/
lemma attaining_version_section_integrable (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) (om : X → ℝ → ℝ)
    (hi : TargetWeightIntegrable M om) (Q : X → ℕ → ℝ → ℝ)
    (K : Kernel (ℝ × X) ℝ) (hK : IsAttainingKernelVersion M om Q K) :
    ∀ᵐ x ∂xLaw M,
      IntegrableOn (fun u => (∫ y, y ∂K (u, x)) * om x u) (Icc (0 : ℝ) 1) := by
  haveI : IsProbabilityMeasure (xLaw M) := Measure.isProbabilityMeasure_map M.measX.aemeasurable
  letI := hK.1
  filter_upwards [Integrable.prod_right_ae hi] with x hx
  let Kx := K.comap (fun u : ℝ => (u, x)) (by fun_prop)
  exact supported_kernel_weighted_integrable M h he _ Kx
    (Filter.Eventually.of_forall fun u => hK.2.1 (u, x)) (om x) hx

-- @node: attaining_version_gap_cost
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
[continuity of propensity on instrument components](hyp:hc), and
[finitely many instrument components](hyp:hfin), suppose [the target weight is measurable](hyp:hm)
and [integrable](hyp:hi), [Q supplies the rank kernel extension](hyp:hQ), and
[K is an attaining kernel version](hyp:hK). Then [for almost every covariate value,
K's weighted outcome integral on each gap equals the nonnegative gap length times
the integral of the outcome and weight quantiles paired at opposite ranks](goal). -/
lemma attaining_version_gap_cost (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) (hc : PropensityContinuousOnComponents M)
    (hfin : FiniteInstrumentComponents Z) (om : X → ℝ → ℝ)
    (hm : TargetWeightMeasurable om) (hi : TargetWeightIntegrable M om)
    (Q : X → ℕ → ℝ → ℝ) (hQ : RankKernelExtensionReading M Q)
    (K : Kernel (ℝ × X) ℝ) (hK : IsAttainingKernelVersion M om Q K) :
    ∀ᵐ x ∂xLaw M, ∀ k < (CondRangeDecomposition M x).count,
      (∫ u in RangeDecomposition.gap (CondRangeDecomposition M x) k,
        (∫ y, y ∂K (u, x)) * om x u) =
      max 0 ((CondRangeDecomposition M x).gapHi k - (CondRangeDecomposition M x).gapLo k) *
        ∫ t in Ioo (0 : ℝ) 1, (gapQuantiles M om x k).1 t *
          (gapQuantiles M om x k).2 (1 - t) := by
  filter_upwards [attaining_version_section_eq M om Q K hK,
    pasted_attaining_gap_cost M h he hc hfin om hm hi Q hQ] with x hx hcost
  intro k hk
  have hb := conditional_gap_endpoints M x k hk
  have hs : RangeDecomposition.gap (CondRangeDecomposition M x) k ⊆ Icc (0 : ℝ) 1 :=
    fun _ hu => hu.2
  calc
    _ = ∫ u in RangeDecomposition.gap (CondRangeDecomposition M x) k,
        (∫ y, y ∂pastedAttainingLaw M om Q x u) * om x u := by
      apply integral_congr_ae
      filter_upwards [hx.filter_mono (ae_mono (Measure.restrict_mono_set volume hs))] with u hu
      rw [hu]
    _ = _ := hcost k hk

-- @node: attaining_version_liv_cost
/-- Under [the structural assumptions](hyp:h), [continuity of propensity on instrument
components](hyp:hc), and [finitely many instrument components](hyp:hfin), if
[K is an attaining kernel version](hyp:hK), then [for almost every covariate value,
the target-weighted mean outcome integrated over each LIV interval is the same
under K and the treated latent outcome law](goal). -/
lemma attaining_version_liv_cost (h : StructuralAssumptions M)
    (hc : PropensityContinuousOnComponents M) (hfin : FiniteInstrumentComponents Z)
    (om : X → ℝ → ℝ) (Q : X → ℕ → ℝ → ℝ)
    (K : Kernel (ℝ × X) ℝ) (hK : IsAttainingKernelVersion M om Q K) :
    ∀ᵐ x ∂xLaw M, ∀ k < (CondRangeDecomposition M x).count,
      (∫ u in (CondRangeDecomposition M x).liv k,
        (∫ y, y ∂K (u, x)) * om x u) =
      ∫ u in (CondRangeDecomposition M x).liv k,
        (∫ y, y ∂outcomeKernel (latentMarginal M true) (u, x)) * om x u := by
  filter_upwards [attaining_version_section_eq M om Q K hK,
    range_decomposition_valid M h hfin hc] with x hx hv
  intro k hk
  have hs := liv_interval_range _ _ hv ⟨k, hk⟩
  calc
    _ = ∫ u in (CondRangeDecomposition M x).liv k,
        (∫ y, y ∂pastedAttainingLaw M om Q x u) * om x u := by
      apply integral_congr_ae
      filter_upwards [hx.filter_mono (ae_mono (Measure.restrict_mono_set volume hs))] with u hu
      rw [hu]
    _ = _ := pasted_attaining_liv_cost M om Q x hv k hk

-- @node: range_tail_subset_unit
/-- If [the range decomposition is valid for R](hyp:hD), then
[its tail is contained in the closed unit interval](goal). -/
lemma range_tail_subset_unit (D : RangeData) (R : Set ℝ) (hD : D.Valid R) :
    D.tail ⊆ Icc (0 : ℝ) 1 := by
  have hb : 0 ≤ D.tailLo := by
    by_cases hz : D.count = 0
    · simp [RangeData.tailLo, hz]
    · have he := range_endpoint_bounds D R hD (show D.count - 1 < D.count by omega)
      simpa only [RangeData.tailLo, if_neg hz] using he.1.trans he.2.1
  exact fun u hu => ⟨hb.trans hu.1.le, hu.2⟩

-- @node: attaining_version_tail_cost
/-- Under [the structural assumptions](hyp:h), [continuity of propensity on instrument
components](hyp:hc), and [finitely many instrument components](hyp:hfin), if
[K is an attaining kernel version](hyp:hK), then [for almost every covariate value,
K's target-weighted outcome integral on the tail equals the integral of the lower
outcome endpoint times the positive part of the weight plus the upper endpoint
times its negative part](goal). -/
lemma attaining_version_tail_cost (h : StructuralAssumptions M)
    (hc : PropensityContinuousOnComponents M) (hfin : FiniteInstrumentComponents Z)
    (om : X → ℝ → ℝ) (Q : X → ℕ → ℝ → ℝ)
    (K : Kernel (ℝ × X) ℝ) (hK : IsAttainingKernelVersion M om Q K) :
    ∀ᵐ x ∂xLaw M,
      (∫ u in (CondRangeDecomposition M x).tail,
        (∫ y, y ∂K (u, x)) * om x u) =
      ∫ u in (CondRangeDecomposition M x).tail,
        M.yMin * max 0 (om x u) + M.yMax * min 0 (om x u) := by
  filter_upwards [attaining_version_section_eq M om Q K hK,
    range_decomposition_valid M h hfin hc] with x hx hv
  have hs := range_tail_subset_unit _ _ hv
  calc
    _ = ∫ u in (CondRangeDecomposition M x).tail,
        (∫ y, y ∂pastedAttainingLaw M om Q x u) * om x u := by
      apply integral_congr_ae
      filter_upwards [hx.filter_mono (ae_mono (Measure.restrict_mono_set volume hs))] with u hu
      rw [hu]
    _ = _ := pasted_attaining_tail_cost M om Q x hv

-- @node: attaining_version_objective_decomposition
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
[continuity of propensity on instrument components](hyp:hc), and
[finitely many instrument components](hyp:hfin), suppose [the target weight is measurable](hyp:hm)
and [integrable](hyp:hi), [Q supplies the rank kernel extension](hyp:hQ), and
[K is an attaining kernel version](hyp:hK). Then [for almost every covariate value,
K's weighted outcome integral over the unit interval equals the sum of gap lengths
times opposite-rank quantile integrals, the treated latent law's weighted LIV
integrals, and the tail integral using the lower outcome endpoint for positive
weights and the upper endpoint for negative weights](goal). -/
lemma attaining_version_objective_decomposition (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) (hc : PropensityContinuousOnComponents M)
    (hfin : FiniteInstrumentComponents Z) (om : X → ℝ → ℝ)
    (hm : TargetWeightMeasurable om) (hi : TargetWeightIntegrable M om)
    (Q : X → ℕ → ℝ → ℝ) (hQ : RankKernelExtensionReading M Q)
    (K : Kernel (ℝ × X) ℝ) (hK : IsAttainingKernelVersion M om Q K) :
    ∀ᵐ x ∂xLaw M,
      (∫ u in Icc (0 : ℝ) 1, (∫ y, y ∂K (u, x)) * om x u) =
      (∑ k ∈ Finset.range (CondRangeDecomposition M x).count,
        max 0 ((CondRangeDecomposition M x).gapHi k - (CondRangeDecomposition M x).gapLo k) *
          ∫ t in Ioo (0 : ℝ) 1, (gapQuantiles M om x k).1 t *
            (gapQuantiles M om x k).2 (1 - t)) +
      (∑ k ∈ Finset.range (CondRangeDecomposition M x).count,
        ∫ u in (CondRangeDecomposition M x).liv k,
          (∫ y, y ∂outcomeKernel (latentMarginal M true) (u, x)) * om x u) +
      ∫ u in (CondRangeDecomposition M x).tail,
        M.yMin * max 0 (om x u) + M.yMax * min 0 (om x u) := by
  filter_upwards [range_decomposition_valid M h hfin hc,
    attaining_version_section_integrable M h he om hi Q K hK,
    attaining_version_gap_cost M h he hc hfin om hm hi Q hQ K hK,
    attaining_version_liv_cost M h hc hfin om Q K hK,
    attaining_version_tail_cost M h hc hfin om Q K hK] with x hv hint hg hl ht
  rw [range_regions_integral _ _ hv _ hint, ht]
  congr 1
  congr 1
  · apply Finset.sum_congr rfl
    intro k hk
    exact hg k (Finset.mem_range.mp hk)
  · apply Finset.sum_congr rfl
    intro k hk
    exact hl k (Finset.mem_range.mp hk)

-- @node: attaining_version_liv_derivative_cost
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
[continuity of propensity on instrument components](hyp:hc), and
[finitely many instrument components](hyp:hfin), if [K is an attaining kernel version](hyp:hK),
then [for almost every covariate value, K's target-weighted outcome integral over
each LIV interval equals the integral of the derivative of the canonical treated
regression with respect to propensity, multiplied by the target weight](goal). -/
lemma attaining_version_liv_derivative_cost (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) (hc : PropensityContinuousOnComponents M)
    (hfin : FiniteInstrumentComponents Z) (om : X → ℝ → ℝ)
    (Q : X → ℕ → ℝ → ℝ) (K : Kernel (ℝ × X) ℝ)
    (hK : IsAttainingKernelVersion M om Q K) :
    ∀ᵐ x ∂xLaw M, ∀ k < (CondRangeDecomposition M x).count,
      (∫ u in (CondRangeDecomposition M x).liv k,
        (∫ y, y ∂K (u, x)) * om x u) =
      ∫ u in (CondRangeDecomposition M x).liv k,
        deriv (fun p => g1Canon M p x) u * om x u := by
  filter_upwards [attaining_version_liv_cost M h hc hfin om Q K hK,
    canonical_regression_deriv M h he, range_decomposition_valid M h hfin hc]
    with x hx hd hv
  intro k hk
  rw [hx k hk]
  apply integral_congr_ae
  have hs := liv_interval_range _ _ hv ⟨k, hk⟩
  filter_upwards [hd.filter_mono (ae_mono (Measure.restrict_mono_set volume hs))] with u hu
  rw [hu]

-- @node: attaining_version_conditional_bound
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
[continuity of propensity on instrument components](hyp:hc), and
[finitely many instrument components](hyp:hfin), suppose [the target weight is measurable](hyp:hm)
and [integrable](hyp:hi), [Q supplies the rank kernel extension](hyp:hQ), and
[K is an attaining kernel version](hyp:hK). Then [for almost every covariate value,
K's target-weighted mean outcome integrated over the unit rank interval equals
the conditional lower-bound integrand](goal). -/
lemma attaining_version_conditional_bound (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) (hc : PropensityContinuousOnComponents M)
    (hfin : FiniteInstrumentComponents Z) (om : X → ℝ → ℝ)
    (hm : TargetWeightMeasurable om) (hi : TargetWeightIntegrable M om)
    (Q : X → ℕ → ℝ → ℝ) (hQ : RankKernelExtensionReading M Q)
    (K : Kernel (ℝ × X) ℝ) (hK : IsAttainingKernelVersion M om Q K) :
    ∀ᵐ x ∂xLaw M,
      (∫ u in Icc (0 : ℝ) 1, (∫ y, y ∂K (u, x)) * om x u) =
        conditionalBoundIntegrand M false om x := by
  filter_upwards [attaining_version_objective_decomposition M h he hc hfin om hm hi Q hQ K hK,
    canonical_regression_deriv M h he, range_decomposition_valid M h hfin hc]
    with x hx hd hv
  rw [hx]
  simp only [conditionalBoundIntegrand, Bool.false_eq_true, ↓reduceIte]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  apply integral_congr_ae
  have hs := liv_interval_range _ _ hv ⟨k, Finset.mem_range.mp hk⟩
  filter_upwards [hd.filter_mono (ae_mono (Measure.restrict_mono_set volume hs))] with u hu
  rw [hu]

-- @node: attaining_version_conditional_bound_integrable
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
[continuity of propensity on instrument components](hyp:hc), and
[finitely many instrument components](hyp:hfin), if [the target weight is measurable](hyp:hm)
and [integrable](hyp:hi), [Q supplies the rank kernel extension](hyp:hQ), and
[K is an attaining kernel version](hyp:hK), then [the conditional lower-bound
integrand is integrable under the covariate distribution](goal). -/
lemma attaining_version_conditional_bound_integrable (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) (hc : PropensityContinuousOnComponents M)
    (hfin : FiniteInstrumentComponents Z) (om : X → ℝ → ℝ)
    (hm : TargetWeightMeasurable om) (hi : TargetWeightIntegrable M om)
    (Q : X → ℕ → ℝ → ℝ) (hQ : RankKernelExtensionReading M Q)
    (K : Kernel (ℝ × X) ℝ) (hK : IsAttainingKernelVersion M om Q K) :
    Integrable (conditionalBoundIntegrand M false om) (xLaw M) := by
  letI := hK.1
  let Ks := K.comap (Prod.swap : X × ℝ → ℝ × X) (by fun_prop)
  have hmK : AEStronglyMeasurable (fun xu : X × ℝ => ∫ y, y ∂K (xu.2, xu.1))
      ((xLaw M).prod (volume.restrict (Icc (0 : ℝ) 1))) := by
    exact (stronglyMeasurable_id.integral_kernel (κ := Ks)).aestronglyMeasurable
  have hb : ∀ᵐ xu ∂(xLaw M).prod (volume.restrict (Icc (0 : ℝ) 1)),
      ‖∫ y, y ∂K (xu.2, xu.1)‖ ≤ outcomeMagnitude M := by
    filter_upwards [] with xu
    simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using
      norm_integral_le_of_norm_le_const
        (supported_outcome_norm_bound M h he (K (xu.2, xu.1)) (hK.2.1 _))
  have hf := hi.bdd_mul hmK hb
  exact hf.integral_prod_left.congr
    (attaining_version_conditional_bound M h he hc hfin om hm hi Q hQ K hK)

-- @node: attaining_version_integrated_bound
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
[continuity of propensity on instrument components](hyp:hc), and
[finitely many instrument components](hyp:hfin), suppose [the target weight is measurable](hyp:hm)
and [integrable](hyp:hi), [Q supplies the rank kernel extension](hyp:hQ), and
[K is an attaining kernel version](hyp:hK). Then [K's target-weighted mean outcome,
integrated over unit ranks and the covariate distribution, equals the covariate
lower-bound value](goal). -/
lemma attaining_version_integrated_bound (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) (hc : PropensityContinuousOnComponents M)
    (hfin : FiniteInstrumentComponents Z) (om : X → ℝ → ℝ)
    (hm : TargetWeightMeasurable om) (hi : TargetWeightIntegrable M om)
    (Q : X → ℕ → ℝ → ℝ) (hQ : RankKernelExtensionReading M Q)
    (K : Kernel (ℝ × X) ℝ) (hK : IsAttainingKernelVersion M om Q K) :
    (∫ x, (∫ u in Icc (0 : ℝ) 1, (∫ y, y ∂K (u, x)) * om x u) ∂xLaw M) =
      covariateLowerValue M om := by
  exact integral_congr_ae
    (attaining_version_conditional_bound M h he hc hfin om hm hi Q hQ K hK)

end Papers.TbsPrteOptimalTransport

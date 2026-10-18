module
public import Papers.TbsPrteOptimalTransport.Helpers.LIVPart
public import Papers.TbsPrteOptimalTransport.Helpers.RandomizedRank
public import Papers.TbsPrteOptimalTransport.Helpers.OrderedRanges
public import Papers.TbsPrteOptimalTransport.Helpers.GapKernelQuantile
/-! Attainment shared proof obligations. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z]
variable (M : LatentIVModel Ω X Z)

-- @node: rangeDecomposition_valid_or_empty
/-- [The chosen decomposition of a real set is valid for that set or has no components](goal). -/
lemma rangeDecomposition_valid_or_empty (R : Set ℝ) :
    (RangeDecomposition R).Valid R ∨ (RangeDecomposition R).count = 0 := by
  unfold RangeDecomposition
  split
  · exact Or.inl (Classical.choose_spec _)
  · exact Or.inr rfl

-- @node: rangeData_gap_endpoints
/-- If [the range decomposition is valid for the given set](hyp:hD) and
[the gap index is below its component count](hyp:hk), [both gap endpoints lie in the closed unit interval](goal). -/
lemma rangeData_gap_endpoints (D : RangeData) (R : Set ℝ) (hD : D.Valid R)
    (k : ℕ) (hk : k < D.count) :
    D.gapLo k ∈ Icc (0 : ℝ) 1 ∧ D.gapHi k ∈ Icc (0 : ℝ) 1 := by
  change k < D.1 at hk
  have hhigh := hD.1 ⟨k, hk⟩
  constructor
  · unfold RangeData.gapLo
    split
    · exact ⟨le_rfl, zero_le_one⟩
    · have hk' : k - 1 < D.1 := by change k < D.1 at hk; omega
      have he := hD.1 ⟨k - 1, hk'⟩
      simp only [RangeData.high, dif_pos hk', mem_Icc]
      exact ⟨he.1.trans he.2.1, he.2.2⟩
  · simpa only [RangeData.gapHi, RangeData.low, dif_pos hk, mem_Icc] using
      And.intro hhigh.1 (hhigh.2.1.trans hhigh.2.2)

-- @node: conditional_gap_endpoints
/-- If [the index is below the conditional range decomposition's component count](hyp:hk),
[both endpoints of that covariate-specific gap lie in the closed unit interval](goal). -/
lemma conditional_gap_endpoints (x : X) (k : ℕ)
    (hk : k < (CondRangeDecomposition M x).count) :
    (CondRangeDecomposition M x).gapLo k ∈ Icc (0 : ℝ) 1 ∧
    (CondRangeDecomposition M x).gapHi k ∈ Icc (0 : ℝ) 1 := by
  rcases rangeDecomposition_valid_or_empty (range (fun z => M.prop z x)) with hv | hz
  · exact rangeData_gap_endpoints _ _ hv k hk
  · change k < (RangeDecomposition (range (fun z => M.prop z x))).count at hk
    omega

-- @node: canonical_treated_increment
/-- If [the lower rank is nonnegative](hyp:ha) and [does not exceed the upper rank](hyp:hab),
[the increment in the canonical treated submeasure equals the outcome kernel integrated over ranks above the lower endpoint and at most the upper endpoint](goal). -/
lemma canonical_treated_increment (x : X) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    canonSubmeasure M true x b - canonSubmeasure M true x a =
      (volume.restrict (Ioc a b)).bind
        (fun u => outcomeKernel (latentMarginal M true) (u, x)) := by
  let K := (outcomeKernel (latentMarginal M true)).comap
    (fun u : ℝ => (u, x)) (by fun_prop)
  letI := outcomeKernel_isMarkov (latentMarginal M true)
  have hf := interval_kernel_finite K 0 a
  letI : IsFiniteMeasure ((volume.restrict (Ioc 0 a)).bind K) := ⟨hf.lt_top⟩
  change (volume.restrict (Ioc 0 b)).bind K -
    (volume.restrict (Ioc 0 a)).bind K = (volume.restrict (Ioc a b)).bind K
  rw [interval_kernel_add K 0 a b ha hab, add_comm, Measure.add_sub_cancel]

-- @node: measurable_gap_quantile_extension
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
[propensity continuity on instrument components](hyp:hc), and [finitely many instrument components](hyp:hfin),
[there exists a jointly measurable family that, for almost every covariate value, agrees with the endpoint-extended outcome quantile on every nonempty gap at every rank in the closed unit interval](goal). -/
lemma measurable_gap_quantile_extension
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (hc : PropensityContinuousOnComponents M) (hfin : FiniteInstrumentComponents Z) :
    ∃ Q : X → ℕ → ℝ → ℝ,
      Measurable (fun a : X × ℕ × ℝ => Q a.1 a.2.1 a.2.2) ∧
      ∀ᵐ x ∂xLaw M, ∀ k < (CondRangeDecomposition M x).count,
        (CondRangeDecomposition M x).gapLo k < (CondRangeDecomposition M x).gapHi k →
        ∀ t ∈ Icc (0 : ℝ) 1, Q x k t = endpointGapQuantile M x k t := by
  classical
  obtain ⟨D, hcount, hend, hD⟩ := measurable_ordered_gap_law_version M h hc hfin
  let a : X × ℕ → ℝ := fun xk => (D xk.1).gapLo xk.2
  let b : X × ℕ → ℝ := fun xk => (D xk.1).gapHi xk.2
  have ha : Measurable a := measurable_from_prod_countable_left fun k => (hend k).1
  have hb : Measurable b := measurable_from_prod_countable_left fun k => (hend k).2
  let K := (outcomeKernel (latentMarginal M true)).comap
    (fun uxk : ℝ × (X × ℕ) => (uxk.1, uxk.2.1)) (by fun_prop)
  letI := outcomeKernel_isMarkov (latentMarginal M true)
  obtain ⟨L, hL, hLeq⟩ := exists_normalized_interval_kernel K a b ha hb M.yMin
  letI := hL
  let Q : X → ℕ → ℝ → ℝ := fun x k t =>
    if t = 0 then M.yMin else if t = 1 then M.yMax else
      if t ∈ Ioo (0 : ℝ) 1 then Causalean.Stat.quantile (L (x, k)) t else 0
  refine ⟨Q, ?_, ?_⟩
  · exact (measurable_kernel_endpoint_quantile L M.yMin M.yMax).comp
      (show Measurable (fun xkt : X × ℕ × ℝ => ((xkt.1, xkt.2.1), xkt.2.2)) by fun_prop)
  filter_upwards [hD] with x hx
  intro k hk hab t ht
  have ha0 := (conditional_gap_endpoints M x k hk).1.1
  have heq : L (x, k) = gapLaw M x k := by
    rw [hLeq]
    dsimp only [a, b]
    simp only [hx, if_pos hab]
    rw [gapLaw, if_pos hab,
      canonical_treated_increment M x _ _ ha0 hab.le]
    rfl
  dsimp only [Q]
  unfold endpointGapQuantile
  by_cases ht0 : t = 0
  · simp only [ht0, if_true]
  by_cases ht1 : t = 1
  · simp only [ht0, ht1, if_false, if_true]
  have ht' : t ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
  simp only [ht0, ht1, if_false, if_pos ht', heq]

-- @node: gap_law_isProbability
/-- Under [the structural assumptions](hyp:h), [propensity continuity on instrument components](hyp:hc),
and [finitely many instrument components](hyp:hfin), [for almost every covariate value, every nonempty gap has a probability outcome law](goal). -/
lemma gap_law_isProbability (h : StructuralAssumptions M)
    (hc : PropensityContinuousOnComponents M) (hfin : FiniteInstrumentComponents Z) :
    ∀ᵐ x ∂xLaw M, ∀ k < (CondRangeDecomposition M x).count,
      (CondRangeDecomposition M x).gapLo k < (CondRangeDecomposition M x).gapHi k →
        IsProbabilityMeasure (gapLaw M x k) := by
  filter_upwards [] with x
  intro k hk hab
  have he := conditional_gap_endpoints M x k hk
  let D := CondRangeDecomposition M x
  letI := outcomeKernel_isMarkov (latentMarginal M true)
  let K := (outcomeKernel (latentMarginal M true)).comap
    (fun u : ℝ => (u, x)) (by fun_prop)
  constructor
  rw [gapLaw, if_pos hab, canonical_treated_increment M x _ _ he.1.1 hab.le,
    Measure.smul_apply]
  change (ENNReal.ofReal (D.gapHi k - D.gapLo k))⁻¹ *
    ((volume.restrict (Ioc (D.gapLo k) (D.gapHi k))).bind K) univ = 1
  rw [interval_kernel_mass K]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr (sub_pos.mpr hab))
    ENNReal.ofReal_ne_top

-- @node: quantile_mem_closed_of_supported
/-- For a probability distribution, if [a set is closed](hyp:hS) and [has zero probability outside it](hyp:hs),
then [at any rank strictly between zero and one](hyp:ht), [the quantile belongs to that set](goal). -/
lemma quantile_mem_closed_of_supported (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (S : Set ℝ) (hS : IsClosed S) (hs : mu Sᶜ = 0)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : Causalean.Stat.quantile mu t ∈ S := by
  by_contra hq
  let q := Causalean.Stat.quantile mu t
  obtain ⟨e, he, hball⟩ := Metric.isOpen_iff.mp hS.isOpen_compl q hq
  have hnull : mu (Ioc (q - e / 2) q) = 0 := by
    apply measure_mono_null _ hs
    intro y hy
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hy.2)]
    linarith [hy.1]
  have hmeasure : mu (Iic q) = mu (Iic (q - e / 2)) := by
    rw [← Iic_union_Ioc_eq_Iic (show q - e / 2 ≤ q by linarith),
      measure_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc, hnull, add_zero]
  have hcdf : cdf mu q = cdf mu (q - e / 2) := by
    simp only [cdf_eq_real, measureReal_def, hmeasure]
  have hle := Causalean.Stat.le_cdf_quantile (μ := mu) ht.2
  rw [hcdf] at hle
  have hqle := Causalean.Stat.quantile_le_of_le_cdf (μ := mu) ht.1 hle
  change q ≤ q - e / 2 at hqle
  linarith

-- @node: gap_law_supported
/-- Under [the structural assumptions](hyp:h), [for almost every covariate value, the outcome law of each nonempty gap assigns zero mass outside the outcome domain](goal). -/
lemma gap_law_supported (h : StructuralAssumptions M) :
    ∀ᵐ x ∂xLaw M, ∀ k < (CondRangeDecomposition M x).count,
      (CondRangeDecomposition M x).gapLo k < (CondRangeDecomposition M x).gapHi k →
        gapLaw M x k M.Ysetᶜ = 0 := by
  filter_upwards [canonical_submeasure_supported M h true] with x hx
  intro k hk hab
  have he := conditional_gap_endpoints M x k hk
  rw [gapLaw, if_pos hab, Measure.smul_apply]
  have hz : (canonSubmeasure M true x ((CondRangeDecomposition M x).gapHi k) -
      canonSubmeasure M true x ((CondRangeDecomposition M x).gapLo k)) M.Ysetᶜ = 0 := by
    apply le_zero_iff.mp
    exact (Measure.sub_le _).trans_eq (hx _ he.2)
  simp only [hz, smul_zero]

-- @node: conditional_gap_quantile_supported
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
[finitely many instrument components](hyp:hc), and [propensity continuity on those components](hyp:hp),
[for almost every covariate value, every nonempty gap's endpoint-extended quantile belongs to the outcome domain at every rank in the closed unit interval](goal). -/
lemma conditional_gap_quantile_supported (h : StructuralAssumptions M) -- @realizes Q_{Y,k\mid x}(outcome-supported quantile including endpoint extension)
    (he : OutcomeEndpointsKnown M) (hc : FiniteInstrumentComponents Z)
    (hp : PropensityContinuousOnComponents M) :
    ∀ᵐ x ∂xLaw M, ∀ k < (CondRangeDecomposition M x).count,
      (CondRangeDecomposition M x).gapLo k < (CondRangeDecomposition M x).gapHi k →
      ∀ t ∈ Icc (0 : ℝ) 1, endpointGapQuantile M x k t ∈ M.Yset := by
  filter_upwards [gap_law_isProbability M h hp hc, gap_law_supported M h] with x hprob hs
  intro k hk hab t ht
  by_cases ht0 : t = 0
  · simpa [endpointGapQuantile, ht0] using he.1.1
  by_cases ht1 : t = 1
  · simpa [endpointGapQuantile, ht0, ht1] using he.2.1
  letI := hprob k hk hab
  rw [endpointGapQuantile, if_neg ht0, if_neg ht1]
  exact quantile_mem_closed_of_supported _ M.Yset h.2.2.2.2.2.2.1.isClosed
    (hs k hk hab) t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩


-- @node: property_at_constant_covariate
/-- If [the covariate equals a fixed value almost surely](hyp:hX) and
[a property holds for almost every value under the covariate distribution](hyp:hP),
[that property holds at the fixed covariate value](goal). -/
lemma property_at_constant_covariate (x0 : X)
    (hX : ∀ᵐ s ∂M.law.toMeasure, M.Xv s = x0) (P : X → Prop)
    (hP : ∀ᵐ x ∂xLaw M, P x) : P x0 := by
  have hpull := ae_of_ae_map M.measX.aemeasurable hP
  obtain ⟨s, hs, hsX⟩ := (hpull.and hX).exists
  rwa [hsX] at hs

-- @node: conditional_interval_law_probability
/-- If [the instrument has finitely many values](hyp:hfin), then for
[any interval between successive conditional propensity levels](hyp:i),
[its outcome law is a probability distribution](goal). -/
lemma conditional_interval_law_probability (x : X) (hfin : Finite Z)
    (i : Fin (finiteLevels (fun z => M.prop z x)).length) :
    IsProbabilityMeasure (conditionalIntervalLaw M x i) := by
  have hr := finite_levels_ranges (fun z => M.prop z x) (fun z => M.rangeProp z x) hfin
  have ha := hr.1 i (by omega)
  have hab := hr.2.1 i i.isLt
  letI := outcomeKernel_isMarkov (latentMarginal M true)
  let K := (outcomeKernel (latentMarginal M true)).comap
    (fun u : ℝ => (u, x)) (by fun_prop)
  constructor
  rw [conditionalIntervalLaw, canonical_treated_increment M x _ _ ha.1 hab.le,
    Measure.smul_apply]
  change (ENNReal.ofReal (pLevel (finiteLevels (fun z => M.prop z x)) (i+1) -
    pLevel (finiteLevels (fun z => M.prop z x)) i))⁻¹ *
    ((volume.restrict (Ioc _ _)).bind K) univ = 1
  rw [interval_kernel_mass K]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr (sub_pos.mpr hab))
    ENNReal.ofReal_ne_top

-- @node: no_covariate_interval_quantile_supported
/-- If [the covariate is almost surely constant](hyp:hX), [the structural assumptions hold](hyp:h),
[the outcome endpoints are known](hyp:he), and [the instrument has finitely many values](hyp:hfin),
then for [any propensity interval at that covariate value](hyp:i),
[its outcome quantile lies in the outcome domain at every rank strictly between zero and one](goal). -/
lemma no_covariate_interval_quantile_supported (x0 : X) (hX : ∀ᵐ s ∂M.law.toMeasure, M.Xv s = x0)
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M) (hfin : Finite Z)
    (om : ℝ → ℝ)
    (i : Fin (finiteLevels (fun z => M.prop z x0)).length) :
    ∀ t ∈ Ioo (0 : ℝ) 1, (intervalQuantiles M x0 hX om i).1 t ∈ M.Yset := by -- @realizes Q_{Y,i}(no-covariate interval outcome quantile takes values in the outcome domain)
  have hs := property_at_constant_covariate M x0 hX _
    (canonical_submeasure_supported M h true)
  have hr := finite_levels_ranges (fun z => M.prop z x0) (fun z => M.rangeProp z x0) hfin
  have hb := hr.1 (i+1) (by omega)
  have hsupport : intervalLaw M x0 hX i M.Ysetᶜ = 0 := by
    unfold intervalLaw conditionalIntervalLaw
    rw [Measure.smul_apply]
    have hz : (canonSubmeasure M true x0 (pLevel (finiteLevels (fun z => M.prop z x0)) (i+1)) -
        canonSubmeasure M true x0 (pLevel (finiteLevels (fun z => M.prop z x0)) i)) M.Ysetᶜ = 0 := by
      apply le_zero_iff.mp
      exact (Measure.sub_le _).trans_eq (hs _ hb)
    simp only [hz, smul_zero]
  letI : IsProbabilityMeasure (intervalLaw M x0 hX i) :=
    conditional_interval_law_probability M x0 hfin i
  intro t ht
  exact quantile_mem_closed_of_supported _ M.Yset h.2.2.2.2.2.2.1.isClosed hsupport t ht
-- @node: no_covariate_gap_quantile_supported
/-- If [the covariate is almost surely constant](hyp:hX), [the structural assumptions hold](hyp:h),
[outcome endpoints are known](hyp:he), [the instrument has finitely many components](hyp:hfin),
[propensity is continuous on those components](hyp:hc), and [the selected gap has strictly ordered endpoints](hyp:hk),
[its outcome quantile lies in the outcome domain at every rank strictly between zero and one](goal). -/
lemma no_covariate_gap_quantile_supported (x0 : X) (hX : ∀ᵐ s ∂M.law.toMeasure, M.Xv s = x0) -- @realizes Q_{Y,k}(nonempty-gap quantile takes values in the outcome domain)
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (hfin : FiniteInstrumentComponents Z) (hc : PropensityContinuousOnComponents M)
    (om : ℝ → ℝ) (k : Fin (CondRangeDecomposition M x0).count)
    (hk : (CondRangeDecomposition M x0).gapLo k <
      (CondRangeDecomposition M x0).gapHi k) :
    ∀ t ∈ Ioo (0 : ℝ) 1, (gapQuantiles0 M x0 hX om k hk).1 t ∈ M.Yset := by
  have hprob := property_at_constant_covariate M x0 hX _
    (gap_law_isProbability M h hc hfin)
  have hs := property_at_constant_covariate M x0 hX _ (gap_law_supported M h)
  have heq : gapLaw0 M x0 hX k hk = gapLaw M x0 k := by
    simp only [gapLaw0, canonSubmeasure0, gapLaw, if_pos hk]
  letI : IsProbabilityMeasure (gapLaw0 M x0 hX k hk) := by
    rw [heq]
    exact hprob k k.isLt hk
  intro t ht
  apply quantile_mem_closed_of_supported _ M.Yset h.2.2.2.2.2.2.1.isClosed _ t ht
  rw [heq]
  exact hs k k.isLt hk


/-- For [a latent instrumental-variable model](hyp:M), [a covariate value](hyp:x), and
[a rank-indexed outcome kernel](hyp:K), [conditional treated feasibility](goal) means
[the kernel gives a probability distribution at every rank](step:1),
[it is supported on the outcome domain at almost every rank in the closed unit interval](step:2),
and [its mass integrated up to each attainable propensity agrees with the canonical treated submeasure on every measurable outcome set](step:3). -/
def ConditionalTreatedFeasible (x : X) (K : Kernel ℝ ℝ) : Prop :=
  IsMarkovKernel K ∧ (∀ᵐ u ∂volume.restrict (Icc (0:ℝ) 1), K u M.Ysetᶜ = 0) ∧
  ∀ p ∈ range (fun z => M.prop z x), ∀ A : Set ℝ, MeasurableSet A →
    (∫ u in Ioc 0 p, (K u A).toReal) = (canonSubmeasure M true x p A).toReal
  -- @realizes \Gamma_{1,x}(conditional feasible probability kernels on the outcome domain)
end Papers.TbsPrteOptimalTransport

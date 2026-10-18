module
public import Papers.TbsPrteOptimalTransport.Helpers.DiscreteIV
public import Papers.TbsPrteOptimalTransport.Helpers.Attainment
/-! Quantile-band change of variables for the discrete nuisance components. -/
public section
set_option linter.style.longLine false
set_option linter.unusedVariables false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal Topology

-- @node: binary_law_mean_eq_one_sub_cdf_zero
/-- If [a probability law assigns all its mass to zero and one](hyp:hs), then
[its mean equals one minus its cumulative probability at zero](goal). -/
lemma binary_law_mean_eq_one_sub_cdf_zero (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hs : ν ({0, 1} : Set ℝ)ᶜ = 0) :
    (∫ y, y ∂ν) = 1 - cdf ν 0 := by
  have he : (fun y : ℝ => y) =ᵐ[ν] (Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ)) := by
    filter_upwards [ae_iff.mpr hs] with y hy
    simp only [mem_compl_iff, not_not, mem_insert_iff, mem_singleton_iff] at hy
    rcases hy with rfl | rfl <;> simp
  rw [integral_congr_ae he, integral_indicator measurableSet_Ioi, integral_const]
  simp only [smul_eq_mul, mul_one]
  rw [measureReal_def, Measure.restrict_apply MeasurableSet.univ, univ_inter]
  change ν.real (Ioi 0) = _
  rw [← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic, cdf_eq_real]

-- @node: binary_law_quantile_step
/-- If [a probability law is supported on zero and one](hyp:hs) and
[the rank lies strictly between zero and one](hyp:ht), then [its quantile is one
when the rank exceeds the cumulative probability at zero, and zero otherwise](goal). -/
lemma binary_law_quantile_step (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hs : ν ({0, 1} : Set ℝ)ᶜ = 0) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    Causalean.Stat.quantile ν t = if cdf ν 0 < t then 1 else 0 := by
  have hq := quantile_mem_closed_of_supported ν ({0, 1} : Set ℝ)
    (isClosed_singleton.union isClosed_singleton) hs t ht
  simp only [mem_insert_iff, mem_singleton_iff] at hq
  have hle := Causalean.Stat.quantile_le_iff (μ := ν) (x := 0) ht.1 ht.2
  split_ifs with h
  · rcases hq with hq | hq
    · have := hle.mp (by rw [hq])
      linarith
    · exact hq
  · rcases hq with hq | hq
    · exact hq
    · have := hle.mpr (le_of_not_gt h)
      rw [hq] at this
      norm_num at this

-- @node: binary_law_quantile_band_integral
/-- For [a probability law supported on zero and one](hyp:hs), if [the lower band
rank is nonnegative](hyp:hs0) and [the upper band rank is at most one](hyp:ht1),
then [the quantile integral over the band, excluding its lower endpoint, equals
the nonnegative part of the upper rank minus the larger of the lower rank and
one minus the law's mean](goal). -/
lemma binary_law_quantile_band_integral (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hs : ν ({0, 1} : Set ℝ)ᶜ = 0) (s t : ℝ) (hs0 : 0 ≤ s) (ht1 : t ≤ 1) :
    (∫ u in Ioc s t, Causalean.Stat.quantile ν u) =
      max 0 (t - max s (1 - ∫ y, y ∂ν)) := by
  have he : Causalean.Stat.quantile ν =ᵐ[volume.restrict (Ioc s t)]
      (Ioi (cdf ν 0)).indicator (fun _ => (1 : ℝ)) := by
    have hn1 : ∀ᵐ u : ℝ ∂volume, u ∉ ({1} : Set ℝ) :=
      (Set.countable_singleton (1 : ℝ)).ae_notMem volume
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae hn1] with u hu hu1
    have hu1' : u ≠ 1 := by simpa only [mem_singleton_iff] using hu1
    rw [binary_law_quantile_step ν hs ⟨hs0.trans_lt hu.1, lt_of_le_of_ne (hu.2.trans ht1) hu1'⟩]
    simp only [indicator_apply, mem_Ioi]
  rw [integral_congr_ae he, integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi]
  have hset : Ioi (cdf ν 0) ∩ Ioc s t = Ioc (max s (cdf ν 0)) t := by
    ext u
    simp only [mem_inter_iff, mem_Ioi, mem_Ioc, max_lt_iff]
    tauto
  rw [hset, integral_const]
  simp only [measureReal_def, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_Ioc, ENNReal.toReal_ofReal',
    smul_eq_mul, mul_one]
  rw [binary_law_mean_eq_one_sub_cdf_zero ν hs]
  simp only [sub_sub_cancel, max_comm]

-- @node: cdf_quantile_eq_of_no_atom
/-- If [a rank lies strictly between zero and one](hyp:ht) and [a probability law
has no atom at its quantile at that rank](hyp:hn), then [the cumulative probability
at that quantile equals the rank](goal). -/
lemma cdf_quantile_eq_of_no_atom (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hn : ν {Causalean.Stat.quantile ν t} = 0) :
    cdf ν (Causalean.Stat.quantile ν t) = t := by
  have he : ν (Iic (Causalean.Stat.quantile ν t)) =
      ν (Iio (Causalean.Stat.quantile ν t)) := by
    rw [← Iio_union_right (a := Causalean.Stat.quantile ν t),
      measure_union (disjoint_singleton_right.mpr (by simp))
        (measurableSet_singleton _), hn, add_zero]
  apply le_antisymm
  · rw [cdf_eq_real, measureReal_def, he]
    exact DistributionalTransform.leftCDF_quantile_le ν ht.1 ht.2
  · exact Causalean.Stat.le_cdf_quantile ht.2

-- @node: quantile_band_integral_of_cdf
/-- If [the lower rank is nonnegative](hyp:hs), [the upper rank is at most one](hyp:ht),
[the cumulative probability at the lower outcome endpoint equals the lower rank](hyp:ha),
and [the cumulative probability at the upper outcome endpoint equals the upper rank](hyp:hb),
then [the quantile integral over those ranks equals the outcome integral between
those endpoints, with both integrals excluding their lower endpoints](goal). -/
lemma quantile_band_integral_of_cdf (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (a b s t : ℝ) (hs : 0 ≤ s) (ht : t ≤ 1)
    (ha : cdf ν a = s) (hb : cdf ν b = t) :
    (∫ u in Ioc s t, Causalean.Stat.quantile ν u) = ∫ y in Ioc a b, y ∂ν := by
  have hmap := Causalean.Stat.quantile_map_uniform ν
  have htrans : (∫ y in Ioc a b, y ∂ν) =
      ∫ u, (Ioc s t).indicator (Causalean.Stat.quantile ν) u
        ∂Causalean.Stat.unifOI := by
    rw [← integral_indicator measurableSet_Ioc]
    conv_lhs => rw [← hmap]
    have hmeas : AEStronglyMeasurable ((Ioc a b).indicator (fun y : ℝ => y))
        (Causalean.Stat.unifOI.map (Causalean.Stat.quantile ν)) :=
      ((measurable_id : Measurable (fun y : ℝ => y)).indicator measurableSet_Ioc).aestronglyMeasurable
    rw [integral_map (Causalean.Stat.aemeasurable_quantile_unifOI ν) hmeas]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    have he : Causalean.Stat.quantile ν u ∈ Ioc a b ↔ u ∈ Ioc s t := by
      simp only [mem_Ioc]
      rw [← not_le, Causalean.Stat.quantile_le_iff hu.1 hu.2,
        ha, not_le, Causalean.Stat.quantile_le_iff hu.1 hu.2, hb]
    simp only [indicator_apply]
    rw [if_congr he rfl rfl]
  rw [htrans, Causalean.Stat.unifOI, integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc]
  apply setIntegral_congr_set
  filter_upwards [Ioo_ae_eq_Ioc (μ := volume) (a := (0 : ℝ)) (b := 1)] with u hu
  apply propext
  change u ∈ Ioc s t ↔ u ∈ Ioc s t ∩ Ioo (0 : ℝ) 1
  change (u ∈ Ioo (0 : ℝ) 1) = (u ∈ Ioc (0 : ℝ) 1) at hu
  simp only [mem_inter_iff]
  rw [hu]
  simp only [mem_Ioc]
  constructor
  · exact fun h => ⟨h, lt_of_le_of_lt hs h.1, h.2.trans ht⟩
  · exact fun h => h.1

-- @node: cdf_lower_endpoint_eq_zero
/-- If [an outcome is the least element of a set](hyp:ha), [a probability law is
supported on that set](hyp:hs), and [the law has no atom at that outcome](hyp:hn),
then [its cumulative probability at that outcome is zero](goal). -/
lemma cdf_lower_endpoint_eq_zero (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (S : Set ℝ) (a : ℝ) (ha : IsLeast S a) (hs : ν Sᶜ = 0) (hn : ν {a} = 0) :
    cdf ν a = 0 := by
  have hl : ν (Iio a) = 0 := measure_mono_null (by
    intro y hy
    exact fun hys => (not_le_of_gt hy) (ha.2 hys)) hs
  rw [cdf_eq_real, measureReal_def, ← Iio_union_right (a := a),
    measure_union (disjoint_singleton_right.mpr (by simp)) (measurableSet_singleton a),
    hl, hn, zero_add, ENNReal.toReal_zero]

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: discrete_gap_law_probability
/-- If [the baseline and policy propensities obey the given invariant level ordering](hyp:hL)
and [the gap index is below the number of baseline gaps](hyp:hk), then [the
normalized treated-outcome law for that gap at the given covariate value is a
probability measure](goal). -/
lemma discrete_gap_law_probability (prop q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant prop q L) (k : ℕ) (hk : k < L.K) (x : X) :
    IsProbabilityMeasure (discreteGapLaw M L k x) := by
  have ha := hL.2.2.2.2.2.2.2.2.2.2.1 x k (by omega)
  have hab := hL.2.2.2.2.2.2.2.1 x k (k+1) (by omega) (by omega)
  letI := outcomeKernel_isMarkov (latentMarginal M true)
  let K := (outcomeKernel (latentMarginal M true)).comap
    (fun u : ℝ => (u, x)) (by fun_prop)
  constructor
  rw [discreteGapLaw, canonical_treated_increment M x _ _ ha.1 hab.le,
    Measure.smul_apply]
  change (ENNReal.ofReal (L.pLev (k+1) x - L.pLev k x))⁻¹ *
    ((volume.restrict (Ioc (L.pLev k x) (L.pLev (k+1) x))).bind K) univ = 1
  rw [interval_kernel_mass K]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr (sub_pos.mpr hab))
    ENNReal.ofReal_ne_top

-- @node: discrete_gap_law_supported
/-- Under [the model's structural assumptions](hyp:h) and [the invariant ordering
of baseline and policy levels](hyp:hL), [for almost every covariate value, every
valid baseline gap's outcome law assigns zero mass outside the model's outcome set](goal). -/
lemma discrete_gap_law_supported (h : StructuralAssumptions M)
    (prop q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant prop q L) :
    ∀ᵐ x ∂xLaw M, ∀ k < L.K, discreteGapLaw M L k x M.Ysetᶜ = 0 := by
  filter_upwards [canonical_submeasure_supported M h true] with x hx
  intro k hk
  have hb := hL.2.2.2.2.2.2.2.2.2.2.1 x (k+1) (by omega)
  rw [discreteGapLaw, Measure.smul_apply]
  have hz : (canonSubmeasure M true x (L.pLev (k+1) x) -
      canonSubmeasure M true x (L.pLev k x)) M.Ysetᶜ = 0 :=
    le_zero_iff.mp ((Measure.sub_le _).trans_eq (hx _ hb))
  simp only [hz, smul_zero]

-- @node: kappa_lt_one_of_policy_level
/-- If [baseline and policy levels have the specified invariant ordering](hyp:hL),
[the baseline gap is valid](hyp:hk), and [the policy level index is at least one](hyp:hj0)
and [does not exceed the number of policy levels within that gap](hyp:hj), then
[the policy level's normalized position within the gap is strictly below one](goal). -/
lemma kappa_lt_one_of_policy_level (prop q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant prop q L) (x : X) (k j : ℕ)
    (hk : k < L.K) (hj0 : 1 ≤ j) (hj : j ≤ L.l k) : kappa L k j x < 1 := by
  rcases hL with ⟨hbase, hpolicy, hboundary, hcount, hlength, hS, hT,
    hstrict, hqstrict, hinputs, hpRange, hqRange⟩
  have hidx : j - 1 < (policyLevelsAt prop q x k).length := by
    rw [hlength x k hk.le]
    omega
  have hm : (policyLevelsAt prop q x k).getD (j-1) 0 ∈ policyLevelsAt prop q x k := by
    rw [List.getD_eq_getElem _ _ hidx]
    exact List.getElem_mem hidx
  simp only [policyLevelsAt, Finset.mem_sort, Finset.mem_filter] at hm
  have hwidth := hstrict x k (k+1) (by omega) (by omega)
  have hpk : k < (finiteLevels (fun z => prop z x)).length := by
    rw [hcount x]
    exact hk
  rw [if_pos hpk] at hm
  have hq : L.qLev k j x < L.pLev (k+1) x := by
    rw [hpolicy x k j hk.le (by omega), if_neg (by omega), if_pos hj,
      hbase x (k+1) (by omega)]
    exact hm.2.2
  exact (div_lt_one (sub_pos.mpr hwidth)).mpr (sub_lt_sub_right hq _)

-- @node: level_gap_quantile_ae
/-- [The endpoint-adjusted quantile for a baseline gap agrees with the ordinary
quantile of its outcome law at Lebesgue-almost every rank](goal). -/
lemma level_gap_quantile_ae (L : LevelData Z X) (k : ℕ) (x : X) :
    levelGapQuantile M L k x =ᵐ[volume] Causalean.Stat.quantile (discreteGapLaw M L k x) := by
  filter_upwards [((Set.countable_singleton (0 : ℝ)).ae_notMem volume),
    ((Set.countable_singleton (1 : ℝ)).ae_notMem volume)] with t ht0 ht1
  simp only [mem_singleton_iff] at ht0 ht1
  simp only [levelGapQuantile, if_neg ht0, if_neg ht1]

-- @node: discrete_band_boundary_cdf
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
and [the invariant ordering of baseline and policy levels](hyp:hL), [for almost
every covariate value, each valid gap and band boundary with no atom has cumulative
probability equal to its normalized rank, including at rank zero](goal). -/
lemma discrete_band_boundary_cdf (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) (prop q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant prop q L) :
    ∀ᵐ x ∂xLaw M, ∀ k < L.K, ∀ j ≤ L.l k,
      discreteGapLaw M L k x {bandBoundary M L k j x} = 0 →
      cdf (discreteGapLaw M L k x) (bandBoundary M L k j x) = kappa L k j x := by
  filter_upwards [discrete_gap_law_supported M h prop q L hL] with x hx
  intro k hk j hj hn
  letI := discrete_gap_law_probability M prop q L hL k hk x
  have hjzero : j = 0 → kappa L k j x = 0 := by
    intro hj0
    rw [kappa, hL.2.1 x k j hk.le (by omega), if_pos hj0, sub_self, zero_div]
  by_cases hz : j = 0 ∨ kappa L k j x = 0
  · have hr : kappa L k j x = 0 := hz.elim hjzero id
    have hbd : bandBoundary M L k j x = M.yMin := by
      simp only [bandBoundary, if_pos hz]
    rw [hbd] at hn ⊢
    rw [hr]
    exact cdf_lower_endpoint_eq_zero _ M.Yset M.yMin he.1 (hx k hk) hn
  · have hj0 : 1 ≤ j := by omega
    have hkr := (canonical_level_ranges prop q L (fun z x => (hL.2.2.2.2.2.2.2.2.2.1 z x).1)
      (fun z x => (hL.2.2.2.2.2.2.2.2.2.1 z x).2) hL).2.2 x k j hk (by omega)
    have ht : kappa L k j x ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne hkr.1 (Ne.symm (not_or.mp hz).2),
        kappa_lt_one_of_policy_level prop q L hL x k j hk hj0 hj⟩
    rw [bandBoundary, if_neg hz] at hn ⊢
    exact cdf_quantile_eq_of_no_atom _ ht hn

-- @node: continuous_discrete_Jband
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
and [the invariant ordering of baseline and policy levels](hyp:hL), if [the baseline
gap is valid](hyp:hk), [the band index is below the number of policy levels in
that gap](hyp:hj), and [the gap law has no atoms at the band's boundaries almost
everywhere](hyp:hn), then [for almost every covariate value the continuous-outcome
band contribution equals the baseline gap width times the outcome integral between
the two band boundaries, excluding the lower boundary](goal). -/
lemma continuous_discrete_Jband (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) (prop q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant prop q L) (k j : ℕ) (hk : k < L.K)
    (hj : j < L.l k) (hn : GapLawContinuousAtBoundaries M L k j) :
    ∀ᵐ x ∂xLaw M, Jband M false L k j x = (L.pLev (k+1) x - L.pLev k x) *
      ∫ y in Ioc (bandBoundary M L k j x) (bandBoundary M L k (j+1) x), y ∂discreteGapLaw M L k x := by
  filter_upwards [discrete_band_boundary_cdf M h he prop q L hL, hn] with x hx hnx
  letI := discrete_gap_law_probability M prop q L hL k hk x
  have hinputs := hL.2.2.2.2.2.2.2.2.2.1
  have hr := (canonical_level_ranges prop q L (fun z x => (hinputs z x).1)
    (fun z x => (hinputs z x).2) hL).2.2
  have hc := quantile_band_integral_of_cdf (discreteGapLaw M L k x)
    (bandBoundary M L k j x) (bandBoundary M L k (j+1) x)
    (kappa L k j x) (kappa L k (j+1) x)
    (hr x k j hk (by omega)).1 (hr x k (j+1) hk (by omega)).2
    (hx k hk j (by omega) hnx.1) (hx k hk (j+1) (by omega) hnx.2)
  unfold Jband
  simp only [Bool.false_eq_true, ↓reduceIte]
  congr 1
  exact (integral_congr_ae ((level_gap_quantile_ae M L k x).restrict)).trans hc

end Papers.TbsPrteOptimalTransport

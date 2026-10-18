module
public import Papers.TbsPrteOptimalTransport.Helpers.RangeRegularity
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
/-!
# Randomized ranks on conditional gaps

The distributional transform of an arbitrary real probability law is uniform,
including laws with atoms, and its lower quantile recovers the original draw
almost surely. We first prove this for a single law, then apply it to each
conditional gap's weight law. The general transform helpers are untagged as
required by the orchestrator's proof directive.
-/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
namespace Papers.TbsPrteOptimalTransport.DistributionalTransform
/-- For [a measure on the real line](hyp:ν) and [a real threshold](hyp:y), the [left cumulative distribution value](goal) is the real-valued mass strictly below that threshold. -/
noncomputable def leftCDF (ν : Measure ℝ) (y : ℝ) : ℝ := ν.real (Iio y)
/-- For [a measure on the real line](hyp:ν) and [a pair consisting of an outcome and a randomization value](hyp:a), the [randomized rank](goal) is the mass strictly below the outcome plus the randomization value times the difference between the cumulative distribution value and that strictly lower mass. -/
noncomputable def rank (ν : Measure ℝ) (a : ℝ × ℝ) : ℝ :=
  leftCDF ν a.1 + a.2 * (cdf ν a.1 - leftCDF ν a.1)

/-- For a probability law on the real line, [the mass strictly below a threshold is nondecreasing in that threshold](goal). -/
lemma leftCDF_mono (ν : Measure ℝ) [IsProbabilityMeasure ν] : Monotone (leftCDF ν) := by
  intro a b hab
  exact measureReal_mono (Iio_subset_Iio hab)

/-- For a probability law on the real line, [the mass strictly below a threshold is a measurable function of the threshold](goal). -/
@[fun_prop] lemma measurable_leftCDF (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    Measurable (leftCDF ν) := by
  exact (leftCDF_mono ν).measurable

/-- For a probability law on the real line, [the randomized rank is measurable as a function of the outcome and the randomization value](goal). -/
@[fun_prop] lemma measurable_rank (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    Measurable (rank ν) := by
  have hc : Measurable (cdf ν) := (monotone_cdf ν).measurable
  unfold rank
  fun_prop

/-- For a real probability law, [the mass strictly below any threshold is no greater than the cumulative distribution value at that threshold](goal). -/
lemma leftCDF_le_cdf (ν : Measure ℝ) [IsProbabilityMeasure ν] (y : ℝ) :
    leftCDF ν y ≤ cdf ν y := by
  rw [cdf_eq_real]
  exact measureReal_mono Iio_subset_Iic_self

/-- If [one threshold is strictly below another](hyp:hab), then [the cumulative distribution value at the lower threshold is no greater than the mass strictly below the upper threshold](goal). -/
lemma cdf_le_leftCDF (ν : Measure ℝ) [IsProbabilityMeasure ν] {a b : ℝ} (hab : a < b) :
    cdf ν a ≤ leftCDF ν b := by
  rw [cdf_eq_real]
  exact measureReal_mono (Iic_subset_Iio.mpr hab)

/-- For a real probability law, [the mass strictly below a threshold equals the left-hand limit of its cumulative distribution function at that threshold](goal). -/
lemma leftCDF_eq_leftLim (ν : Measure ℝ) [IsProbabilityMeasure ν] (y : ℝ) :
    leftCDF ν y = Function.leftLim (cdf ν) y := by
  have hn : 0 ≤ Function.leftLim (cdf ν) y :=
    (cdf_nonneg ν (y - 1)).trans ((monotone_cdf ν).le_leftLim (sub_lt_self y one_pos))
  have he : ν (Iio y) = ENNReal.ofReal (Function.leftLim (cdf ν) y) := by
    calc
      ν (Iio y) = (cdf ν).measure (Iio y) := by rw [measure_cdf]
      _ = _ := by rw [(cdf ν).measure_Iio (tendsto_cdf_atBot ν), sub_zero]
  change (ν (Iio y)).toReal = _
  rw [he, ENNReal.toReal_ofReal hn]

/-- If [the quantile level is positive](hyp:ht0) and [strictly less than one](hyp:ht1), then [the mass strictly below the lower quantile at that level is no greater than the level itself](goal). -/
lemma leftCDF_quantile_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    leftCDF ν (Causalean.Stat.quantile ν t) ≤ t := by
  rw [leftCDF_eq_leftLim]
  apply le_of_tendsto ((monotone_cdf ν).tendsto_leftLim _)
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact (lt_of_not_ge (fun h =>
    (not_le_of_gt hy) (Causalean.Stat.quantile_le_of_le_cdf ht0 h))).le

/-- If [the randomization value lies between zero and one inclusive](hyp:hs), then [the randomized rank of an outcome lies between the mass strictly below the outcome and the cumulative distribution value at the outcome](goal). -/
lemma rank_bounds (ν : Measure ℝ) [IsProbabilityMeasure ν] (y s : ℝ)
    (hs : s ∈ Icc (0 : ℝ) 1) :
    leftCDF ν y ≤ rank ν (y, s) ∧ rank ν (y, s) ≤ cdf ν y := by
  have hd := sub_nonneg.mpr (leftCDF_le_cdf ν y)
  dsimp [rank]
  constructor
  · nlinarith [mul_nonneg hs.1 hd]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hs.2) hd]

/-- If [a threshold is nonnegative](hyp:ht0) and [no greater than one](hyp:ht1), then [the uniform law on the open unit interval assigns probability equal to that threshold to the event of being strictly below it](goal). -/
lemma unif_Iio {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Causalean.Stat.unifOI (Iio t) = ENNReal.ofReal t := by
  rw [Causalean.Stat.unifOI, Measure.restrict_apply measurableSet_Iio]
  have he : Iio t ∩ Ioo (0 : ℝ) 1 = Ioo 0 t := by
    ext s
    simp only [mem_inter_iff, mem_Iio, mem_Ioo]
    constructor
    · exact fun h => ⟨h.2.1, h.1⟩
    · exact fun h => ⟨h.2, h.1, h.2.trans_le ht1⟩
  rw [he, Real.volume_Ioo, sub_zero]

/-- Under the product of a real probability law and an independent uniform law on the open unit interval, [the randomization coordinate lies strictly between zero and one almost surely](goal). -/
lemma ae_snd_mem (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    ∀ᵐ a ∂ν.prod Causalean.Stat.unifOI, a.2 ∈ Ioo (0 : ℝ) 1 := by
  exact (measurePreserving_snd (μ := ν) (ν := Causalean.Stat.unifOI)).quasiMeasurePreserving.ae
    (ae_restrict_mem measurableSet_Ioo)

/-- For a real probability law, [the probability mass at a point equals the cumulative distribution value there minus the mass strictly below it](goal). -/
lemma jump_mass (ν : Measure ℝ) [IsProbabilityMeasure ν] (q : ℝ) :
    ν.real {q} = cdf ν q - leftCDF ν q := by
  have he := measureReal_union (μ := ν)
    (show Disjoint (Iio q) {q} by
      simp only [disjoint_left, mem_Iio, mem_singleton_iff]
      exact fun a ha he => ha.ne he) (measurableSet_singleton q)
  rw [Iio_union_right, ← cdf_eq_real] at he
  dsimp [leftCDF]
  linarith

/-- Suppose [the quantile level is positive](hyp:ht0) and [less than one](hyp:ht1), [the randomization value lies strictly between zero and one](hyp:hs), and [there is a positive probability mass at the lower quantile](hyp:hd). Then [the randomized rank is below the level exactly when the outcome is below that quantile, or equals it and the randomization value is below the fraction of its atom needed to reach the level](goal). -/
lemma rank_lt_quantile_iff (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {t y s : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hs : s ∈ Ioo (0 : ℝ) 1)
    (hd : 0 < cdf ν (Causalean.Stat.quantile ν t) - leftCDF ν (Causalean.Stat.quantile ν t)) :
    rank ν (y,s) < t ↔ y < Causalean.Stat.quantile ν t ∨
      y = Causalean.Stat.quantile ν t ∧
        s < (t - leftCDF ν (Causalean.Stat.quantile ν t)) /
          (cdf ν (Causalean.Stat.quantile ν t) - leftCDF ν (Causalean.Stat.quantile ν t)) := by
  have hb := rank_bounds ν y s ⟨hs.1.le, hs.2.le⟩
  rcases lt_trichotomy y (Causalean.Stat.quantile ν t) with hy | hy | hy
  · have hc : cdf ν y < t := lt_of_not_ge (fun hc =>
      (not_le_of_gt hy) (Causalean.Stat.quantile_le_of_le_cdf ht0 hc))
    exact iff_of_true (hb.2.trans_lt hc) (Or.inl hy)
  · subst y
    simp only [lt_self_iff_false, false_or, true_and]
    rw [lt_div_iff₀ hd]
    dsimp [rank]
    constructor <;> intro hh <;> linarith
  · have hl := cdf_le_leftCDF ν hy
    have ht := Causalean.Stat.le_cdf_quantile (μ := ν) ht1
    have hn : ¬ rank ν (y,s) < t := not_lt.mpr (ht.trans (hl.trans hb.1))
    simp only [hn, false_iff, not_or, not_and]
    exact ⟨not_lt.mpr hy.le, fun he => (ne_of_gt hy) he |>.elim⟩

-- Strict left rays avoid assigning positive mass to the ends of CDF plateaus.
-- The event splits into the lower ray and a fraction of the quantile's atom.
/-- If [a threshold is positive](hyp:ht0) and [less than one](hyp:ht1), then [the probability that the randomized rank is strictly below that threshold equals the threshold, under an independent outcome draw and uniform randomization](goal). -/
lemma rank_Iio_interior (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (ν.prod Causalean.Stat.unifOI) ((rank ν) ⁻¹' Iio t) = ENNReal.ofReal t := by
  let q := Causalean.Stat.quantile ν t
  let A := leftCDF ν q
  let B := cdf ν q
  have hA : A ≤ t := leftCDF_quantile_le ν ht0 ht1
  have hB : t ≤ B := Causalean.Stat.le_cdf_quantile ht1
  have hAB : A ≤ B := leftCDF_le_cdf ν q
  have hAn : 0 ≤ A := measureReal_nonneg
  have hBn : B ≤ 1 := cdf_le_one ν q
  have hnull := ae_snd_mem ν
  rcases lt_or_eq_of_le hAB with hd | hd
  · let r := (t - A) / (B - A)
    have hd' : 0 < B - A := sub_pos.mpr hd
    have hr0 : 0 ≤ r := div_nonneg (sub_nonneg.mpr hA) hd'.le
    have hr1 : r ≤ 1 := (div_le_one hd').mpr (by linarith)
    have he : (rank ν ⁻¹' Iio t) =ᵐ[ν.prod Causalean.Stat.unifOI]
        (((Iio q ×ˢ univ) ∪ ({q} ×ˢ Iio r)) : Set (ℝ × ℝ)) := by
      filter_upwards [hnull] with a ha
      apply propext
      change rank ν a < t ↔ (a.1 < q ∧ True) ∨ (a.1 = q ∧ a.2 < r)
      simpa only [and_true] using (rank_lt_quantile_iff ν (y := a.1) ht0 ht1 ha hd')
    rw [measure_congr he, measure_union]
    · rw [Measure.prod_prod, Measure.prod_prod, measure_univ, mul_one,
        unif_Iio hr0 hr1, ← ofReal_measureReal (μ := ν) (s := Iio q),
        ← ofReal_measureReal (μ := ν) (s := {q}), jump_mass]
      change ENNReal.ofReal A + ENNReal.ofReal (B - A) * ENNReal.ofReal r = _
      rw [← ENNReal.ofReal_mul hd'.le, ← ENNReal.ofReal_add hAn (mul_nonneg hd'.le hr0)]
      congr 1
      dsimp [r]
      rw [mul_div_cancel₀ _ (ne_of_gt hd')]
      ring
    · apply Set.disjoint_prod.mpr
      apply Or.inl
      simp only [disjoint_left, mem_Iio, mem_singleton_iff]
      exact fun y hy he => hy.ne he
    · exact (measurableSet_singleton q).prod measurableSet_Iio
  · have hAt : A = t := le_antisymm hA (by simpa [← hd] using hB)
    have he : (rank ν ⁻¹' Iio t) =ᵐ[ν.prod Causalean.Stat.unifOI] (Iio q ×ˢ univ : Set (ℝ × ℝ)) := by
      filter_upwards [hnull] with a ha
      apply propext
      change rank ν a < t ↔ (a.1 < q ∧ True)
      simp only [and_true]
      rcases lt_trichotomy a.1 q with hy | hy | hy
      · have hc : cdf ν a.1 < t := lt_of_not_ge (fun hc =>
          (not_le_of_gt hy) (Causalean.Stat.quantile_le_of_le_cdf ht0 hc))
        exact iff_of_true ((rank_bounds ν a.1 a.2 ⟨ha.1.le, ha.2.le⟩).2.trans_lt hc) hy
      · have hr : rank ν a = t := by
          change leftCDF ν a.1 + a.2 * (cdf ν a.1 - leftCDF ν a.1) = t
          rw [hy]
          change A + a.2 * (B - A) = t
          rw [← hd, sub_self, mul_zero, add_zero, hAt]
        simp [hr, hy]
      · have hl := cdf_le_leftCDF ν hy
        have hb := (rank_bounds ν a.1 a.2 ⟨ha.1.le, ha.2.le⟩).1
        exact iff_of_false (not_lt.mpr (hB.trans (hl.trans hb))) (not_lt.mpr hy.le)
    rw [measure_congr he, Measure.prod_prod, measure_univ, mul_one,
      ← ofReal_measureReal (μ := ν) (s := Iio q)]
    change ENNReal.ofReal A = _
    rw [hAt]

/-- For any real probability law, [the randomized rank of a draw from that law, using an independent uniform randomization, has the uniform law on the open unit interval](goal). -/
lemma uniform (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    (ν.prod Causalean.Stat.unifOI).map (rank ν) = Causalean.Stat.unifOI := by
  let ρ := (ν.prod Causalean.Stat.unifOI).map (rank ν)
  have hm := measurable_rank ν
  haveI : IsProbabilityMeasure ρ := Measure.isProbabilityMeasure_map hm.aemeasurable
  have hmid {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : ρ (Iio t) = ENNReal.ofReal t := by
    rw [Measure.map_apply hm measurableSet_Iio]
    exact rank_Iio_interior ν ht0 ht1
  have hlow {t : ℝ} (ht : t ≤ 0) : ρ (Iio t) = 0 := by
    rw [Measure.map_apply hm measurableSet_Iio]
    have he : (rank ν ⁻¹' Iio t) =ᵐ[ν.prod Causalean.Stat.unifOI] (∅ : Set (ℝ × ℝ)) := by
      filter_upwards [ae_snd_mem ν] with a ha
      apply propext
      change rank ν a < t ↔ False
      have hb := (rank_bounds ν a.1 a.2 ⟨ha.1.le, ha.2.le⟩).1
      have hn : 0 ≤ leftCDF ν a.1 := measureReal_nonneg
      exact iff_false_intro (not_lt.mpr (ht.trans (hn.trans hb)))
    rw [measure_congr he, measure_empty]
  have hhigh {t : ℝ} (ht : 1 ≤ t) : ρ (Iio t) = 1 := by
    have hr : 1 ≤ ρ.real (Iio t) := by
      apply le_of_forall_lt_imp_le_of_dense
      intro r hr
      by_cases hr0 : 0 < r
      · have he : ρ.real (Iio r) = r := by
          rw [measureReal_def, hmid hr0 hr, ENNReal.toReal_ofReal hr0.le]
        rw [← he]
        exact measureReal_mono (μ := ρ) (Iio_subset_Iio (hr.le.trans ht))
      · exact (le_of_not_gt hr0).trans measureReal_nonneg
    have he : ρ.real (Iio t) = 1 := le_antisymm (by
      calc
        ρ.real (Iio t) ≤ ρ.real univ := measureReal_mono (subset_univ _)
        _ = 1 := by simp) hr
    rw [← ofReal_measureReal (μ := ρ) (s := Iio t), he, ENNReal.ofReal_one]
  have hrays (t : ℝ) : ρ (Iio t) = Causalean.Stat.unifOI (Iio t) := by
    by_cases ht0 : 0 < t
    · by_cases ht1 : t < 1
      · rw [hmid ht0 ht1, unif_Iio ht0.le ht1.le]
      · rw [hhigh (le_of_not_gt ht1)]
        have he : Iio t ∩ Ioo (0 : ℝ) 1 = Ioo 0 1 := by
          ext s
          constructor
          · exact fun h => h.2
          · exact fun h => ⟨h.2.trans_le (le_of_not_gt ht1), h⟩
        rw [Causalean.Stat.unifOI, Measure.restrict_apply measurableSet_Iio,
          he, Real.volume_Ioo]
        norm_num
    · rw [hlow (le_of_not_gt ht0)]
      have he : Iio t ∩ Ioo (0 : ℝ) 1 = ∅ := by
        ext s
        simp only [mem_inter_iff, mem_Iio, mem_Ioo, mem_empty_iff_false, iff_false, not_and]
        exact fun h hs _ => (not_lt_of_ge (le_of_not_gt ht0)) (hs.trans h)
      rw [Causalean.Stat.unifOI, Measure.restrict_apply measurableSet_Iio, he, measure_empty]
  apply Measure.ext_of_Ici ρ Causalean.Stat.unifOI
  intro t
  rw [← compl_Iio, measure_compl measurableSet_Iio (by finiteness),
    measure_compl measurableSet_Iio (by finiteness), hrays, measure_univ, measure_univ]

-- A bounded strictly increasing transform makes the order argument integrable
-- without any moment assumption on either of the original random variables.
/-- Under a finite measure, if [the first real-valued function is almost everywhere measurable](hyp:hf), [the second is almost everywhere measurable](hyp:hg), [their induced distributions coincide](hyp:hmap), and [the first is no greater than the second almost everywhere](hyp:hle), then [the two functions agree almost everywhere](goal). -/
lemma ordered_same_law_ae_eq {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsFiniteMeasure μ] (f g : A → ℝ)
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (hmap : μ.map f = μ.map g) (hle : f ≤ᵐ[μ] g) : f =ᵐ[μ] g := by
  have hi (z : A → ℝ) (hz : AEMeasurable z μ) :
      Integrable (fun a => Real.arctan (z a)) μ := by
    refine ⟨(Real.continuous_arctan.measurable.comp_aemeasurable hz).aestronglyMeasurable, ?_⟩
    apply HasFiniteIntegral.of_bounded (C := Real.pi / 2)
    filter_upwards [] with a
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨(Real.arctan_mem_Ioo (z a)).1.le, (Real.arctan_mem_Ioo (z a)).2.le⟩
  have hint : (∫ a, Real.arctan (f a) ∂μ) = ∫ a, Real.arctan (g a) ∂μ := by
    rw [← integral_map hf Real.continuous_arctan.measurable.aestronglyMeasurable,
      ← integral_map hg Real.continuous_arctan.measurable.aestronglyMeasurable, hmap]
  have he := (integral_eq_iff_of_ae_le (hi f hf) (hi g hg)
    (hle.mono fun a ha => Real.arctan_mono ha)).mp hint
  exact he.mono fun a ha => Real.arctan_injective ha

-- The Galois connection gives Q(rank) ≤ y. Both sides have law ν, so the
-- preceding order lemma upgrades this inequality to almost-sure equality.
/-- For any real probability law, [evaluating its lower quantile function at the randomized rank recovers the original outcome almost surely under the product of that law and an independent uniform randomization](goal). -/
lemma recover (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    ∀ᵐ a ∂ν.prod Causalean.Stat.unifOI, Causalean.Stat.quantile ν (rank ν a) = a.1 := by
  let μ := ν.prod Causalean.Stat.unifOI
  have hm : AEMeasurable (rank ν) μ := (measurable_rank ν).aemeasurable
  have hU := uniform ν
  have hQ : AEMeasurable (Causalean.Stat.quantile ν) (μ.map (rank ν)) := by
    rw [hU]
    exact Causalean.Stat.aemeasurable_quantile_unifOI ν
  have hQcomp := hQ.comp_aemeasurable hm
  have hmap : μ.map (fun a => Causalean.Stat.quantile ν (rank ν a)) = μ.map Prod.fst := by
    change μ.map (Causalean.Stat.quantile ν ∘ rank ν) = μ.map Prod.fst
    rw [← AEMeasurable.map_map_of_aemeasurable hQ hm]
    change ((ν.prod Causalean.Stat.unifOI).map (rank ν)).map _ = _
    rw [hU, Causalean.Stat.quantile_map_uniform]
    simp [μ]
  apply ordered_same_law_ae_eq μ _ Prod.fst hQcomp measurable_fst.aemeasurable hmap
  have hmem : ∀ᵐ a ∂μ, rank ν a ∈ Ioo (0 : ℝ) 1 := by
    apply ae_of_ae_map hm
    rw [hU]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [hmem, ae_snd_mem ν] with a ha hs
  exact Causalean.Stat.quantile_le_of_le_cdf ha.1
    (rank_bounds ν a.1 a.2 ⟨hs.1.le, hs.2.le⟩).2

-- Pull the single-law result back along the measured variable. Measurable
-- representatives are used only to justify the product pushforward identity.
/-- If [a real-valued random variable is almost everywhere measurable under a probability measure](hyp:hf), then [its randomized rank computed from its own distribution is uniform on the open unit interval, and its value is almost surely recovered by evaluating its distribution's lower quantile function at that rank](goal), using independent uniform randomization. -/
lemma transform_of_aemeasurable {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] (f : A → ℝ) (hf : AEMeasurable f μ) :
    (μ.prod Causalean.Stat.unifOI).map (fun a => rank (μ.map f) (f a.1, a.2)) =
      Causalean.Stat.unifOI ∧
    (∀ᵐ a ∂μ.prod Causalean.Stat.unifOI,
      f a.1 = Causalean.Stat.quantile (μ.map f) (rank (μ.map f) (f a.1, a.2))) := by
  haveI : IsProbabilityMeasure (μ.map f) := Measure.isProbabilityMeasure_map hf
  let g : A × ℝ → ℝ × ℝ := fun a => (f a.1, a.2)
  have he : g =ᵐ[μ.prod Causalean.Stat.unifOI] Prod.map (hf.mk f) id := by
    have hfst := (measurePreserving_fst (μ := μ) (ν := Causalean.Stat.unifOI)).quasiMeasurePreserving.ae
      hf.ae_eq_mk
    filter_upwards [hfst] with a ha
    exact congrArg (fun y => (y, a.2)) ha
  have hg : AEMeasurable g (μ.prod Causalean.Stat.unifOI) := by
    exact (hf.measurable_mk.prodMap measurable_id).aemeasurable.congr he.symm
  have hmap : (μ.prod Causalean.Stat.unifOI).map g = (μ.map f).prod Causalean.Stat.unifOI := by
    rw [Measure.map_congr he, ← Measure.map_prod_map μ Causalean.Stat.unifOI
      hf.measurable_mk measurable_id, Measure.map_id, ← Measure.map_congr hf.ae_eq_mk]
  constructor
  · change (μ.prod Causalean.Stat.unifOI).map (rank (μ.map f) ∘ g) = _
    rw [← AEMeasurable.map_map_of_aemeasurable
      ((measurable_rank (μ.map f)).aemeasurable) hg, hmap]
    exact uniform (μ.map f)
  · have hr : ∀ᵐ b ∂(μ.prod Causalean.Stat.unifOI).map g,
        b.1 = Causalean.Stat.quantile (μ.map f) (rank (μ.map f) b) := by
      rw [hmap]
      exact (recover (μ.map f)).mono fun b hb => hb.symm
    exact ae_of_ae_map hg hr

end Papers.TbsPrteOptimalTransport.DistributionalTransform

namespace Papers.TbsPrteOptimalTransport
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z]
variable (M : LatentIVModel Ω X Z)
-- @node: randomized_rank_uniform
/-- If [the model satisfies the structural assumptions](hyp:h) and [the target weight is measurable on covariates and unit-interval ranks](hyp:hm), then [for almost every covariate value and every positive-length gap in the conditional range decomposition, the randomized weight rank of a uniform gap draw is uniform on the open unit interval, and the gap weight quantile at that rank recovers the target weight almost surely](goal). -/
lemma randomized_rank_uniform (h : StructuralAssumptions M) (om : X → ℝ → ℝ)
    (hm : TargetWeightMeasurable om) :
    ∀ᵐ x ∂xLaw M, ∀ k < (CondRangeDecomposition M x).count,
      (CondRangeDecomposition M x).gapLo k < (CondRangeDecomposition M x).gapHi k →
      ((gapUnif M x k).prod Causalean.Stat.unifOI).map
        (fun a => randomizedRank M om x k a.1 a.2) = Causalean.Stat.unifOI ∧
      (∀ᵐ a ∂(gapUnif M x k).prod Causalean.Stat.unifOI,
        om x a.1 = (gapQuantiles M om x k).2 (randomizedRank M om x k a.1 a.2)) := by
  filter_upwards [] with x
  intro k hk hab
  have hex : ∃ D : RangeData, D.Valid (range (fun z => M.prop z x)) := by
    by_contra hn
    have hz : (CondRangeDecomposition M x).count = 0 := by
      simp [CondRangeDecomposition, RangeDecomposition, hn, RangeData.count]
    omega
  have hv : (CondRangeDecomposition M x).Valid (range (fun z => M.prop z x)) := by
    change (RangeDecomposition _).Valid _
    rw [RangeDecomposition, dif_pos hex]
    exact Classical.choose_spec hex
  have hh := hv.1 ⟨k, hk⟩
  have hlo : 0 ≤ (CondRangeDecomposition M x).gapLo k := by
    unfold RangeData.gapLo
    split
    · exact le_rfl
    · have hk' : k - 1 < (CondRangeDecomposition M x).1 := by
        change k < (CondRangeDecomposition M x).1 at hk
        omega
      have he := hv.1 ⟨k - 1, hk'⟩
      simp only [RangeData.high, dif_pos hk']
      exact he.1.trans he.2.1
  have hhi : (CondRangeDecomposition M x).gapHi k ≤ 1 := by
    have hk' : k < (CondRangeDecomposition M x).1 := hk
    simpa only [RangeData.gapHi, RangeData.low, dif_pos hk'] using hh.2.1.trans hh.2.2
  have hsub : Measurable (fun u : Icc (0 : ℝ) 1 => om x u.val) := by
    exact hm.comp (measurable_const.prodMk measurable_id)
  have hunit : AEMeasurable (om x) (volume.restrict (Icc (0 : ℝ) 1)) :=
    aemeasurable_restrict_of_measurable_subtype measurableSet_Icc hsub
  have hgap : AEMeasurable (om x) (gapUnif M x k) := by
    change AEMeasurable (om x) (_ • volume.restrict (Ioo _ _))
    apply AEMeasurable.smul_measure
    apply hunit.mono_measure
    apply Measure.restrict_mono_set
    intro u hu
    exact ⟨hlo.trans hu.1.le, hu.2.le.trans hhi⟩
  haveI : IsProbabilityMeasure (gapUnif M x k) := uniformInterval_isProbability _ _ hab
  haveI : IsProbabilityMeasure ((gapUnif M x k).map (om x)) := Measure.isProbabilityMeasure_map hgap
  have hr := DistributionalTransform.transform_of_aemeasurable (gapUnif M x k) (om x) hgap
  simpa only [DistributionalTransform.rank, DistributionalTransform.leftCDF,
    cdf_eq_real, measureReal_def, randomizedRank, weightCDF, weightCDFLeft,
    gapQuantiles, weightLaw] using hr
end Papers.TbsPrteOptimalTransport

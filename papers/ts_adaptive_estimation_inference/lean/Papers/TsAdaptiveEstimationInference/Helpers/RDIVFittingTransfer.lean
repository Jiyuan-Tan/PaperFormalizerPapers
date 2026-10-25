module
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVFrozenFitting
/-! Transfer the frozen fitting comparison to the observed fitting block. -/
@[expose] public section

namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory Filter
set_option linter.style.longLine false

variable {𝒲 X Z Ω : Type*} [MeasurableSpace 𝒲] [MeasurableSpace X]
  [MeasurableSpace Z] [mΩ : MeasurableSpace Ω]
  (V : IVWorld 𝒲 X Z) (P : Measure Ω) [IsProbabilityMeasure P]
  (sample : AnalysisSample V P) (split : SampleSplit)

/-- For [an IV population](hyp:V), [an input reference measure](hyp:μ), [a
conditional density](hyp:g), [a penalty weight](hyp:lam), [a primal candidate](hyp:h),
and [an observation](hyp:w), [the fitting loss](goal) is the squared outcome
residual from density-based regression plus the penalty weight times the
squared candidate input value. -/
-- @node: rdivFittingLoss
noncomputable def rdivFittingLoss (μ : Measure X) (g : X → Z → ℝ)
    (lam : ℝ) (h : V.Hbar.toSubmodule) (w : 𝒲) : ℝ :=
  (V.Y w - densityOperator μ g (primalVersion V h) (V.zOf w)) ^ 2 +
    lam * primalVersion V h (V.xOf w) ^ 2

/-- Under [the conditional-density IV setting](hyp:hIV), [density-class
realizability](hyp:hDensity), [common-support density bounds](hyp:hBounds),
[a hypothesis envelope of size B](hyp:hHyp), and [an outcome bound of size B](hyp:hY),
for [a density in the class](hyp:hg) and [a primal candidate](hyp:h) [in the
hypothesis class](hyp:hh), [the fitting loss is integrable and its expectation
equals expected squared residual loss plus the penalty weight times the
candidate's squared Hilbert norm](goal). -/
-- @node: rdiv_fitting_loss_integral
lemma rdiv_fitting_loss_integral (μ : Measure X)
    (G : Set (X → Z → ℝ)) (g₀ g : X → Z → ℝ)
    (support : Set (X × Z)) (B c₀ CG lam : ℝ)
    (hIV : RDIVSetting V μ g₀) (hDensity : DensityRealizable V μ G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hHyp : HypothesisClassBounded V support B) (hY : OutcomeBounded V B)
    (hg : g ∈ G) (h : V.Hbar.toSubmodule) (hh : h ∈ V.H) :
    Integrable (rdivFittingLoss V μ g lam h) V.law ∧
      (∫ w, rdivFittingLoss V μ g lam h w ∂V.law) =
        (∫ w, (V.Y w - densityOperator μ g (primalVersion V h) (V.zOf w)) ^ 2 ∂V.law) +
          lam * ‖h‖ ^ 2 := by
  have hT := rdiv_density_operator_memLp V μ G g₀ g support B c₀ CG
    hIV hDensity hBounds hHyp hY.1 hg h hh
  have hTp : MemLp (fun w => densityOperator μ g (primalVersion V h) (V.zOf w))
      2 V.law := (memLp_map_measure_iff hT.1 V.measurable_z.aemeasurable).1 hT
  have hYp : MemLp V.Y 2 V.law := MemLp.of_bound
    V.measurable_Y.aestronglyMeasurable B (by simpa only [Real.norm_eq_abs] using hY.2)
  have hi := (hYp.sub hTp).integrable_sq
  simp only [Pi.sub_apply] at hi
  have hhp : MemLp (fun w => primalVersion V h (V.xOf w)) 2 V.law :=
    (memLp_congr_ae (V.primal_coherent h)).2 (Lp.memLp (h : Lp ℝ 2 V.law))
  have hnorm : (∫ w, primalVersion V h (V.xOf w) ^ 2 ∂V.law) = ‖h‖ ^ 2 := by
    calc
      _ = ∫ w, ((h : Lp ℝ 2 V.law) w) ^ 2 ∂V.law := by
        apply integral_congr_ae
        filter_upwards [V.primal_coherent h] with w hw
        exact congrArg (fun x : ℝ => x ^ 2) hw
      _ = _ := by
        simpa only [L2.inner_def, RCLike.inner_apply, conj_trivial, ← pow_two,
          Submodule.norm_coe] using real_inner_self_eq_norm_sq (h : Lp ℝ 2 V.law)
  refine ⟨hi.add (hhp.integrable_sq.const_mul lam), ?_⟩
  unfold rdivFittingLoss
  rw [integral_add hi (hhp.integrable_sq.const_mul lam), integral_const_mul, hnorm]

omit [IsProbabilityMeasure P] in
/-- For [a primal candidate](hyp:h), [averaging the fitting loss with the density
estimated from the fixed preliminary realization over the fitting block equals
the empirical penalized risk using that same frozen density](goal). -/
-- @node: rdiv_fitting_loss_average
lemma rdiv_fitting_loss_average (μ : Measure X)
    (gHat : ℕ → Ω → X → Z → ℝ) (n : ℕ) (preliminary ω : Ω)
    (lam : ℝ) (h : V.Hbar.toSubmodule) :
    blockAverage V P sample (split.fit n)
      (rdivFittingLoss V μ (gHat n preliminary) lam h) ω =
      empiricalRisk V P sample split μ (fun _ _ => gHat n preliminary) n ω lam h := by
  simp only [blockAverage, rdivFittingLoss, empiricalRisk, rdivEmpiricalLoss,
    estimatedOperator, primalEmpSq, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

omit [IsProbabilityMeasure P] in
/-- [The sum of a function over an enumeration of the fitting block, divided
by the block size, equals its block average](goal). -/
-- @node: rdiv_fitting_tuple_average
lemma rdiv_fitting_tuple_average (n : ℕ) (f : 𝒲 → ℝ) (ω : Ω) :
    (n : ℝ)⁻¹ * ∑ j : Fin n,
      f (sample.Z ((Finset.equivFinOfCardEq (split.card_fit n)).symm j) ω) =
      blockAverage V P sample (split.fit n) f ω := by
  classical
  unfold blockAverage
  rw [split.card_fit]
  congr 1
  rw [← Finset.sum_coe_sort (split.fit n)]
  exact (Equiv.sum_comp (Finset.equivFinOfCardEq (split.card_fit n)).symm
    (fun i : split.fit n => f (sample.Z i ω)))

/-- For [an IV population](hyp:V), [a sampling probability law](hyp:P), [an
analysis sample](hyp:sample), [a sample split](hyp:split), [an input reference
measure](hyp:μ), [a conditional density](hyp:g), [a fitting block size](hyp:n),
[a sample realization](hyp:ω), [a penalty weight](hyp:lam), [a candidate](hyp:h),
and [a comparator](hyp:hstar), [the fitting deviation](goal) is the absolute
difference between the fitting-block average and population expectation of
the candidate's fitting loss minus the comparator's fitting loss. -/
-- @node: rdivFittingDeviation
noncomputable def rdivFittingDeviation (μ : Measure X) (g : X → Z → ℝ)
    (n : ℕ) (ω : Ω) (lam : ℝ) (h hstar : V.Hbar.toSubmodule) : ℝ :=
  |blockAverage V P sample (split.fit n)
      (fun w => rdivFittingLoss V μ g lam h w - rdivFittingLoss V μ g lam hstar w) ω -
    ∫ w, rdivFittingLoss V μ g lam h w - rdivFittingLoss V μ g lam hstar w ∂V.law|

omit [IsProbabilityMeasure P] in
/-- For [a primal comparator](hyp:hstar), [the empirical supremum of the
localized fitting-loss class on the enumerated fitting observations equals
the supremum of the nonnegative fitting deviations over hypotheses within
the specified Hilbert radius of that comparator](goal). -/
-- @node: rdiv_fitting_supremum_eq
lemma rdiv_fitting_supremum_eq (μ : Measure X) (g : X → Z → ℝ)
    (n : ℕ) (ω : Ω) (lam r : ℝ) (hstar : V.Hbar.toSubmodule) :
    empiricalSupremum V.law (rdivFittedLossClass V μ g lam r hstar) n
      (fun j => sample.Z ((Finset.equivFinOfCardEq (split.card_fit n)).symm j) ω) =
      ⨆ h : {h : V.H // ‖h.1 - hstar‖ ≤ r},
        ENNReal.ofReal (rdivFittingDeviation V P sample split μ g n ω lam h.1.1 hstar) := by
  have heq (h : V.Hbar.toSubmodule) :
      (n : ℝ)⁻¹ * ∑ j : Fin n,
        (rdivFittingLoss V μ g lam h
          (sample.Z ((Finset.equivFinOfCardEq (split.card_fit n)).symm j) ω) -
        rdivFittingLoss V μ g lam hstar
          (sample.Z ((Finset.equivFinOfCardEq (split.card_fit n)).symm j) ω)) =
      blockAverage V P sample (split.fit n)
        (fun w => rdivFittingLoss V μ g lam h w - rdivFittingLoss V μ g lam hstar w) ω :=
    rdiv_fitting_tuple_average V P sample split n
      (fun w => rdivFittingLoss V μ g lam h w - rdivFittingLoss V μ g lam hstar w) ω
  have heq' (h : V.Hbar.toSubmodule) :
      ENNReal.ofReal |(n : ℝ)⁻¹ * ∑ j : Fin n,
        (rdivFittingLoss V μ g lam h
          (sample.Z ((Finset.equivFinOfCardEq (split.card_fit n)).symm j) ω) -
        rdivFittingLoss V μ g lam hstar
          (sample.Z ((Finset.equivFinOfCardEq (split.card_fit n)).symm j) ω)) -
        ∫ w, rdivFittingLoss V μ g lam h w - rdivFittingLoss V μ g lam hstar w ∂V.law| =
      ENNReal.ofReal (rdivFittingDeviation V P sample split μ g n ω lam h hstar) := by
    rw [heq]
    rfl
  unfold empiricalSupremum
  apply le_antisymm
  · apply iSup_le
    intro f
    obtain ⟨h, hh, hr, hf⟩ := f.2
    apply le_iSup_of_le ⟨⟨h, hh⟩, hr⟩
    simpa only [hf, rdivFittingLoss] using (heq' h).le
  · apply iSup_le
    intro h
    apply le_iSup_of_le ⟨_, ⟨h.1.1, h.1.2, h.2, rfl⟩⟩
    simpa only [rdivFittingLoss] using (heq' h.1.1).ge

omit [IsProbabilityMeasure P] in
/-- Under [the conditional-density IV setting](hyp:hIV), [density-class
realizability](hyp:hDensity), [common-support density bounds](hyp:hBounds),
[a hypothesis envelope of size B](hyp:hHyp), and [an outcome bound of size B](hyp:hY),
suppose [the frozen fitted density belongs to the density class](hyp:hg) and
[the candidate and comparator](hyp:h,hstar) [both belong to the hypothesis
class](hyp:hh,hstarH). Then [the fitting deviation equals the absolute difference
between their conditional penalized-risk difference and their empirical
penalized-risk difference using the same frozen density](goal). -/
-- @node: rdiv_fitting_deviation_eq_risks
lemma rdiv_fitting_deviation_eq_risks (μ : Measure X)
    (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (gHat : ℕ → Ω → X → Z → ℝ) (support : Set (X × Z))
    (B c₀ CG : ℝ) (n : ℕ) (preliminary ω : Ω) (lam : ℝ)
    (hIV : RDIVSetting V μ g₀) (hDensity : DensityRealizable V μ G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hHyp : HypothesisClassBounded V support B) (hY : OutcomeBounded V B)
    (hg : gHat n preliminary ∈ G)
    (h hstar : V.Hbar.toSubmodule) (hh : h ∈ V.H) (hstarH : hstar ∈ V.H) :
    rdivFittingDeviation V P sample split μ (gHat n preliminary) n ω lam h hstar =
      |(conditionalRisk V μ gHat n preliminary lam h -
          conditionalRisk V μ gHat n preliminary lam hstar) -
        (empiricalRisk V P sample split μ (fun _ _ => gHat n preliminary) n ω lam h -
          empiricalRisk V P sample split μ (fun _ _ => gHat n preliminary) n ω lam hstar)| := by
  obtain ⟨hi, he⟩ := rdiv_fitting_loss_integral V μ G g₀ _ support B c₀ CG lam
    hIV hDensity hBounds hHyp hY hg h hh
  obtain ⟨hsi, hse⟩ := rdiv_fitting_loss_integral V μ G g₀ _ support B c₀ CG lam
    hIV hDensity hBounds hHyp hY hg hstar hstarH
  unfold rdivFittingDeviation
  rw [integral_sub hi hsi, he, hse]
  have havg : blockAverage V P sample (split.fit n)
      (fun w => rdivFittingLoss V μ (gHat n preliminary) lam h w -
        rdivFittingLoss V μ (gHat n preliminary) lam hstar w) ω =
      blockAverage V P sample (split.fit n)
        (rdivFittingLoss V μ (gHat n preliminary) lam h) ω -
      blockAverage V P sample (split.fit n)
        (rdivFittingLoss V μ (gHat n preliminary) lam hstar) ω := by
    simp only [blockAverage, Finset.sum_sub_distrib, mul_sub]
  rw [havg, rdiv_fitting_loss_average V P sample split μ gHat,
    rdiv_fitting_loss_average V P sample split μ gHat]
  exact abs_sub_comm _ _

/-- Suppose [the grid ratio is at least one half and less than one](hyp:hρ),
[the failure budget is between zero and one](hyp:hξ), [the conditional-density
IV setting holds](hyp:hIV), [the range condition holds](hyp:hRange), [the
minimum-norm solution belongs to the hypothesis class](hyp:hRealizable),
[the density class is realizable](hyp:hDensity), [common-support density bounds
hold](hyp:hBounds), [outcomes are bounded by B](hyp:hOutcome), [hypotheses have
envelope B](hyp:hHyp), [the density estimator selects measurable likelihood
maximizers](hyp:hMLE), [the RDIV classes satisfy the measurability conditions](hyp:hMeas),
[the fitting suprema have coherent measurable versions at rational radii](hyp:hFittingVersion),
[the hypothesis radii bound the relevant critical radii](hyp:hRadius), and
[the density and hypothesis radii satisfy the confidence floor](hyp:hFloor).
Then [any positive constant giving the frozen, gridwise conditional risk
comparison with failure probability at most one quarter of grid confidence
also gives, for every positive sample size, a measurable event of probability
at least one minus one quarter of the failure budget on which the observed
conditional-versus-empirical risk differences from the minimum-norm solution
are uniformly bounded over the grid and hypothesis class by that constant
times the hypothesis radius times Hilbert distance plus squared radius](goal). -/
-- @node: rdiv_thaw_fitting_comparisons
lemma rdiv_thaw_fitting_comparisons
    (μ : Measure X) (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (gHat : ℕ → Ω → X → Z → ℝ) (support : Set (X × Z))
    (B c₀ CG ρ ξ : ℝ) (δG δH : ℕ → ℝ → ℝ)
    (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1) (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1)
    (hIV : RDIVSetting V μ g₀) (hRange : RangeCondition V)
    (hRealizable : H0MemHypothesisClass V)
    (hDensity : DensityRealizable V μ G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hOutcome : OutcomeBounded V B) (hHyp : HypothesisClassBounded V support B)
    (hMLE : MLEMaximizerSelected V P sample split G gHat)
    (hMeas : RDIVClassesMeasurable V P sample split μ G g₀ gHat)
    (hFittingVersion : RDIVFittingSupremumVersion V P sample split μ gHat ρ)
    (hRadius : HypothesisCriticalRadiusBound V μ G δH ρ)
    (hFloor : RDIVRadiusFloor δG δH ρ) :
    ∀ C : ℝ, 0 < C →
    (∀ n : ℕ, 0 < n → ∀ lam ∈ regGrid ρ n,
      ∀ᵐ preliminary ∂P,
        1 - gridConfidence ρ ξ n / 4 ≤ P.real {ω | ∀ h ∈ V.H,
          |(conditionalRisk V μ gHat n preliminary lam h -
              conditionalRisk V μ gHat n preliminary lam (minNormSolution V)) -
            (empiricalRisk V P sample split μ (fun _ _ => gHat n preliminary) n ω lam h -
              empiricalRisk V P sample split μ (fun _ _ => gHat n preliminary) n ω lam
                (minNormSolution V))| ≤
          C * (δH n (gridConfidence ρ ξ n / 4) * ‖h - minNormSolution V‖ +
            δH n (gridConfidence ρ ξ n / 4) ^ 2)}) →
    ∀ n : ℕ, 0 < n → ∃ F : Set Ω,
      MeasurableSet F ∧ 1 - ξ / 4 ≤ P.real F ∧
      ∀ ω ∈ F, ∀ lam ∈ regGrid ρ n, ∀ h ∈ V.H,
        |(conditionalRisk V μ gHat n ω lam h -
            conditionalRisk V μ gHat n ω lam (minNormSolution V)) -
          (empiricalRisk V P sample split μ gHat n ω lam h -
            empiricalRisk V P sample split μ gHat n ω lam (minNormSolution V))| ≤
          C * (δH n (gridConfidence ρ ξ n / 4) * ‖h - minNormSolution V‖ +
            δH n (gridConfidence ρ ξ n / 4) ^ 2) := by
  intro C hC hfrozen n hn
  classical
  let Q := {q : ℚ // 0 < q}
  let r := δH n (gridConfidence ρ ξ n / 4)
  have hquarter : ξ / 4 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [hξ.1, hξ.2]
  have heq : gridConfidence ρ (ξ / 4) n = gridConfidence ρ ξ n / 4 := by
    unfold gridConfidence
    ring
  have hr : 0 < r := by
    have h := (hRadius n hn (ξ / 4) hquarter).1.1
    rwa [heq] at h
  let tuple : Ω → Fin n → 𝒲 := fun ω j =>
    sample.Z ((Finset.equivFinOfCardEq (split.card_fit n)).symm j) ω
  have htuple : Measurable tuple := measurable_pi_lambda _ fun j => sample.meas _
  have htupleLaw : P.map tuple = Measure.pi (fun _ : Fin n => V.law) := by
    have hinj : Function.Injective (fun j : Fin n =>
        ((Finset.equivFinOfCardEq (split.card_fit n)).symm j : ℕ)) :=
      Subtype.val_injective.comp (Equiv.injective _)
    have hi := sample.indep.precomp hinj
    have hm := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
      (fun j : Fin n => (sample.meas _).aemeasurable)).mp hi
    change P.map tuple = _ at hm
    rw [hm]
    simp_rw [sample.map_eq]
  have hlocal : ∀ lam ∈ regGrid ρ n, ∃ E : Set Ω,
      MeasurableSet E ∧ 1 - gridConfidence ρ ξ n / 4 ≤ P.real E ∧
      ∀ ω ∈ E, ∀ h ∈ V.H,
        rdivFittingDeviation V P sample split μ (gHat n ω) n ω lam h
          (minNormSolution V) ≤ C * (r * ‖h - minNormSolution V‖ + r ^ 2) := by
    intro lam hlam
    -- One countable family retains both fresh-tuple and observed-block coherence.
    choose S hSm hSsec hScoh using
      (fun q : Q => hFittingVersion.2 n hn lam hlam q.1 q.2)
    let R : Ω → Ω → Prop := fun pre fit => ∀ q : Q,
      S q (pre, tuple fit) ≤ ENNReal.ofReal (C * (r * (q.1 : ℝ) + r ^ 2))
    have htfit : @Measurable Ω (Fin n → 𝒲)
        (⨆ i ∈ split.fit n, MeasurableSpace.comap (sample.Z i) inferInstance)
        inferInstance tuple := by
      letI : MeasurableSpace Ω :=
        ⨆ i ∈ split.fit n, MeasurableSpace.comap (sample.Z i) inferInstance
      apply measurable_pi_lambda
      intro j
      apply measurable_iff_comap_le.2
      exact le_iSup_of_le _ (le_iSup_of_le
        ((Finset.equivFinOfCardEq (split.card_fit n)).symm j).2 le_rfl)
    have hR : MeasurableSet[(preliminarySigma V P sample split n).prod
        (⨆ i ∈ split.fit n, MeasurableSpace.comap (sample.Z i) inferInstance)]
        {p : Ω × Ω | R p.1 p.2} := by
      letI : MeasurableSpace (Ω × Ω) := (preliminarySigma V P sample split n).prod
        (⨆ i ∈ split.fit n, MeasurableSpace.comap (sample.Z i) inferInstance)
      simp only [R, Set.setOf_forall]
      apply MeasurableSet.iInter
      intro q
      exact measurableSet_le ((hSm q).comp
        (measurable_fst.prodMk (htfit.comp measurable_snd))) measurable_const
    -- Fresh fitting tuples have the iid product law. Thus the original frozen
    -- bound transfers to the measurable versions without spending probability.
    have hsections : ∀ᵐ pre ∂P,
        1 - gridConfidence ρ ξ n / 4 ≤ P.real {fit | R pre fit} := by
      filter_upwards [ae_all_iff.2 hSsec, hfrozen n hn lam hlam,
        (hMLE n hn).1] with pre hsec hprob hg
      have hident : ∀ᵐ fit ∂P, ∀ q : Q,
          S q (pre, tuple fit) = empiricalSupremum V.law
            (rdivFittedLossClass V μ (gHat n pre) lam (q.1 : ℝ)
              (minNormSolution V)) n (tuple fit) := by
        apply ae_all_iff.2
        intro q
        have hs : ∀ᵐ ws ∂P.map tuple, S q (pre, ws) = empiricalSupremum V.law
            (rdivFittedLossClass V μ (gHat n pre) lam (q.1 : ℝ)
              (minNormSolution V)) n ws := by
          rw [htupleLaw]
          exact hsec q
        exact ae_of_ae_map htuple.aemeasurable hs
      apply hprob.trans
      apply ENNReal.toReal_mono (measure_ne_top P _)
      apply measure_mono_ae
      filter_upwards [hident] with fit hid hgood
      intro q
      rw [hid q]
      change empiricalSupremum V.law _ n (tuple fit) ≤ _
      rw [rdiv_fitting_supremum_eq V P sample split]
      apply iSup_le
      intro h
      have hd := rdiv_fitting_deviation_eq_risks V P sample split μ G g₀ gHat
        support B c₀ CG n pre fit lam hIV hDensity hBounds hHyp hOutcome hg.1
        h.1.1 (minNormSolution V) h.1.2 hRealizable
      rw [hd]
      exact ENNReal.ofReal_le_ofReal ((hgood h.1.1 h.1.2).trans (by
        change C * (r * ‖h.1.1 - minNormSolution V‖ + r ^ 2) ≤ _
        gcongr
        exact h.2))
    have hη : gridConfidence ρ ξ n / 4 ∈ Set.Ioo (0 : ℝ) 1 := by
      have hk : (1 : ℝ) ≤ (terminalIndex ρ n + 1 : ℕ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
      have hle : gridConfidence ρ ξ n ≤ ξ := by
        unfold gridConfidence
        exact (div_le_iff₀ (by positivity)).2 (by nlinarith only [hk, hξ.1])
      constructor
      · unfold gridConfidence
        positivity [hξ.1]
      · linarith [hξ.2]
    obtain ⟨hE, hpE⟩ := rdiv_fitting_event_of_frozen_sections V P sample split
      n R hR _ hη hsections
    -- Remove a measurable null superset of the coherence exceptions, then
    -- recover the exact affine envelope by decreasing rational radii.
    have hcoh : ∀ᵐ ω ∂P, ∀ q : Q,
        S q (ω, tuple ω) = empiricalSupremum V.law
          (rdivFittedLossClass V μ (gHat n ω) lam (q.1 : ℝ)
            (minNormSolution V)) n (tuple ω) := ae_all_iff.2 hScoh
    obtain ⟨N, hsub, hN, hN0⟩ := exists_measurable_superset_of_null
      (show P {ω | ¬ ∀ q : Q, S q (ω, tuple ω) = empiricalSupremum V.law
          (rdivFittedLossClass V μ (gHat n ω) lam (q.1 : ℝ)
            (minNormSolution V)) n (tuple ω)} = 0 from ae_iff.mp hcoh)
    refine ⟨{ω | R ω ω} \ N, hE.diff hN, ?_, ?_⟩
    · simpa only [measureReal_def, measure_sdiff_null hN0] using hpE
    intro ω hω h hh
    have hid : ∀ q : Q, S q (ω, tuple ω) = empiricalSupremum V.law
        (rdivFittedLossClass V μ (gHat n ω) lam (q.1 : ℝ)
          (minNormSolution V)) n (tuple ω) := by
      by_contra hbad
      exact hω.2 (hsub hbad)
    have hb := (rdiv_uniform_bound_iff_rational_localizations
      (fun h : V.H => ‖h.1 - minNormSolution V‖)
      (fun h : V.H => rdivFittingDeviation V P sample split μ (gHat n ω) n ω lam h.1
        (minNormSolution V)) (C * r) (C * r ^ 2)
      (fun h => norm_nonneg _) (mul_nonneg hC.le hr.le)
      (mul_nonneg hC.le (sq_nonneg r))).2 (by
        intro q hq
        have hq' : 0 < q := by exact_mod_cast hq
        have hb := hω.1 ⟨q, hq'⟩
        rw [hid ⟨q, hq'⟩] at hb
        rw [rdiv_fitting_supremum_eq V P sample split] at hb
        convert hb using 1 <;> ring)
    simpa only [mul_add, mul_assoc] using hb ⟨h, hh⟩
  -- The finite grid union uses the original quarter budget; the final density
  -- membership restriction is probability one.
  choose E hE hpE hgood using (fun lam : regGrid ρ n => hlocal lam.1 lam.2)
  let F : ℝ → Set Ω := fun lam => if h : lam ∈ regGrid ρ n then E ⟨lam, h⟩ else Set.univ
  have hFm (lam : ℝ) (hlam : lam ∈ regGrid ρ n) : MeasurableSet (F lam) := by
    simpa only [F, dif_pos hlam] using hE ⟨lam, hlam⟩
  have hFp (lam : ℝ) (hlam : lam ∈ regGrid ρ n) :
      1 - gridConfidence ρ ξ n / 4 ≤ P.real (F lam) := by
    simpa only [F, dif_pos hlam] using hpE ⟨lam, hlam⟩
  obtain ⟨hF, hpF⟩ := rdiv_fitting_grid_event_budget P ρ ξ hξ.1.le n F hFm hFp
  have hG : ∀ᵐ ω ∂P, gHat n ω ∈ G := (hMLE n hn).1.mono fun _ h => h.1
  obtain ⟨N, hsub, hN, hN0⟩ := exists_measurable_superset_of_null (ae_iff.mp hG)
  refine ⟨(⋂ lam ∈ regGrid ρ n, F lam) \ N, hF.diff hN, ?_, ?_⟩
  · simpa only [measureReal_def, measure_sdiff_null hN0] using hpF
  intro ω hω lam hlam h hh
  have hg : gHat n ω ∈ G := by
    by_contra hbad
    exact hω.2 (hsub hbad)
  have hmem : ω ∈ E ⟨lam, hlam⟩ := by
    simpa only [F, dif_pos hlam] using Set.mem_iInter₂.mp hω.1 lam hlam
  have hb := hgood ⟨lam, hlam⟩ ω hmem h hh
  rw [rdiv_fitting_deviation_eq_risks V P sample split μ G g₀ gHat
    support B c₀ CG n ω ω lam hIV hDensity hBounds hHyp hOutcome hg
    h (minNormSolution V) hh hRealizable] at hb
  exact hb

/-- Assume [localized Lipschitz vector concentration](hyp:hVector), [a grid
ratio at least one half and less than one](hyp:hρ), [a failure budget between
zero and one](hyp:hξ), [the conditional-density IV setting](hyp:hIV), [the range
condition](hyp:hRange), [membership of the minimum-norm solution in the
hypothesis class](hyp:hRealizable), [density-class realizability](hyp:hDensity),
[common-support density bounds](hyp:hBounds), [outcomes bounded by B](hyp:hOutcome),
[a hypothesis envelope of size B](hyp:hHyp), [measurable likelihood-maximizer
selection](hyp:hMLE), [the conditional class measurability conditions](hyp:hConditionalMeas),
[coherent measurable fitting-supremum versions at rational radii](hyp:hFittingVersion),
[bounds on the hypothesis critical radii](hyp:hRadius), and [the confidence
floor for both radii](hyp:hFloor). Then [there is a positive constant such that
every positive sample size admits a measurable event of probability at least
one minus one quarter of the failure budget, on which conditional-versus-empirical
penalized-risk differences from the minimum-norm solution are uniformly
bounded over the regularization grid and hypothesis class by the constant
times the hypothesis radius times Hilbert distance plus squared radius,
evaluating the radius at one quarter of grid confidence](goal). -/
-- @node: rdiv_fitting_comparison_event
lemma rdiv_fitting_comparison_event
    (μ : Measure X) (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (gHat : ℕ → Ω → X → Z → ℝ) (support : Set (X × Z))
    (B c₀ CG ρ ξ : ℝ) (δG δH : ℕ → ℝ → ℝ)
    (hVector : LipschitzVectorLocalizedConcentration V P sample split)
    (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1) (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1)
    (hIV : RDIVSetting V μ g₀) (hRange : RangeCondition V)
    (hRealizable : H0MemHypothesisClass V)
    (hDensity : DensityRealizable V μ G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hOutcome : OutcomeBounded V B) (hHyp : HypothesisClassBounded V support B)
    (hMLE : MLEMaximizerSelected V P sample split G gHat)
    (hConditionalMeas : PinRDIVMeasurabilityReading V P sample split μ G g₀ gHat)
    (hFittingVersion : RDIVFittingSupremumVersion V P sample split μ gHat ρ)
    (hRadius : HypothesisCriticalRadiusBound V μ G δH ρ)
    (hFloor : RDIVRadiusFloor δG δH ρ) :
    ∃ C > 0, ∀ n : ℕ, 0 < n → ∃ F : Set Ω,
      MeasurableSet F ∧ 1 - ξ / 4 ≤ P.real F ∧
      ∀ ω ∈ F, ∀ lam ∈ regGrid ρ n, ∀ h ∈ V.H,
        |(conditionalRisk V μ gHat n ω lam h -
            conditionalRisk V μ gHat n ω lam (minNormSolution V)) -
          (empiricalRisk V P sample split μ gHat n ω lam h -
            empiricalRisk V P sample split μ gHat n ω lam (minNormSolution V))| ≤
          C * (δH n (gridConfidence ρ ξ n / 4) * ‖h - minNormSolution V‖ +
            δH n (gridConfidence ρ ξ n / 4) ^ 2) := by
  obtain ⟨C, hC, hfrozen⟩ := rdiv_frozen_fitting_comparison V P sample split
    μ G g₀ gHat support B c₀ CG ρ ξ δG δH hVector hρ hξ hIV hRange
    hRealizable hDensity hBounds hOutcome hHyp hMLE hConditionalMeas hFittingVersion hRadius hFloor
  refine ⟨C, hC, ?_⟩
  exact rdiv_thaw_fitting_comparisons V P sample split μ G g₀ gHat support B c₀ CG
    ρ ξ δG δH hρ hξ hIV hRange hRealizable hDensity hBounds hOutcome
    hHyp hMLE hConditionalMeas hFittingVersion hRadius hFloor C hC hfrozen

/-! PRIOR PROOF (carry-over before conditional process scope was corrected).
This proof used an additional joint-supremum conjunct. Its deterministic
identities and independence transport remain available above; the local
thawing obligation must construct the measurable version/event from the
specified conditional processes, without adding that conjunct as a premise.
  classical
  obtain ⟨C, hC, hfrozen⟩ := rdiv_frozen_fitting_comparison V P sample split
    μ G g₀ gHat support B c₀ CG ρ ξ δG δH hVector hρ hξ hIV hRange
    hRealizable hDensity hBounds hOutcome hHyp hMLE hMeas hRadius hFloor
  refine ⟨C, hC, ?_⟩
  intro n hn
  let d := δH n (gridConfidence ρ ξ n / 4)
  have hquarter : ξ / 4 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [hξ.1, hξ.2]
  have hd : 0 ≤ d := by
    have hh := (hRadius n hn (ξ / 4) hquarter).1.1.le
    have he : gridConfidence ρ (ξ / 4) n = gridConfidence ρ ξ n / 4 := by
      unfold gridConfidence
      ring
    rwa [he] at hh
  let radius : V.H → ℝ := fun h => ‖h.1 - minNormSolution V‖
  let value : ℝ → Ω → Ω → V.H → ℝ := fun lam preliminary ω h =>
    rdivFittingDeviation V P sample split μ (gHat n preliminary) n ω lam
      h.1 (minNormSolution V)
  have hlocal : ∀ lam ∈ regGrid ρ n, ∀ q : ℚ, 0 < (q : ℝ) →
      @Measurable (Ω × Ω) ENNReal
        ((preliminarySigma V P sample split n).prod
          (⨆ i ∈ split.fit n, MeasurableSpace.comap (sample.Z i) inferInstance))
        inferInstance (fun p =>
          ⨆ h : {h // radius h ≤ (q : ℝ)}, ENNReal.ofReal (value lam p.1 p.2 h.1)) := by
    intro lam hlam q hq
    have hdom : lam ∈ Set.Ioc (0 : ℝ) 2 := by
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hlam
      have hρpos : 0 < ρ := by linarith only [hρ.1]
      refine ⟨mul_pos (by norm_num) (pow_pos hρpos k), ?_⟩
      have hp := pow_le_pow_of_le_one hρpos.le hρ.2.le (Nat.zero_le k)
      simpa only [gridValue, pow_zero, mul_one] using
        mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 2)
    have hg : ∀ᵐ ω ∂P, gHat n ω ∈ G := (hMLE n hn).1.mono fun _ h => h.1
    have hm := (hMeas.2.2.2 n (gHat n) hn (hMLE n hn).2 hg
      lam hdom q hq (minNormSolution V) hRealizable).1
    let obs := sample.Z
    let mf := ⨆ i ∈ split.fit n, MeasurableSpace.comap (obs i) inferInstance
    let : MeasurableSpace Ω := mΩ
    let tuple : Ω → Fin n → 𝒲 := fun ω j =>
      sample.Z ((Finset.equivFinOfCardEq (split.card_fit n)).symm j) ω
    have htuple : @Measurable Ω (Fin n → 𝒲) mf inferInstance tuple := by
      let : MeasurableSpace Ω := mf
      apply measurable_pi_lambda
      intro j
      apply measurable_iff_comap_le.2
      change MeasurableSpace.comap (obs _) _ ≤ mf
      exact le_iSup_of_le _ (le_iSup_of_le
        ((Finset.equivFinOfCardEq (split.card_fit n)).symm j).property le_rfl)
    have hc := hm.comp (measurable_fst.prodMk (htuple.comp measurable_snd))
    simpa only [Function.comp_def, tuple, rdiv_fitting_supremum_eq, radius, value] using hc
  have hsections : ∀ lam ∈ regGrid ρ n, ∀ᵐ preliminary ∂P,
      1 - gridConfidence ρ ξ n / 4 ≤
        P.real {ω | ∀ h, value lam preliminary ω h ≤ C * d * radius h + C * d ^ 2} := by
    intro lam hlam
    filter_upwards [hfrozen n hn lam hlam, (hMLE n hn).1] with preliminary hp hg
    apply hp.trans
    apply measureReal_mono (h₂ := measure_ne_top P _)
    intro ω hω h
    dsimp [value]
    rw [rdiv_fitting_deviation_eq_risks V P sample split μ G g₀ gHat support
      B c₀ CG n preliminary ω lam hIV hDensity hBounds hHyp hOutcome hg.1
      h.1 (minNormSolution V) h.2 hRealizable]
    have hb := hω h.1 h.2
    simpa only [d, radius, mul_add, mul_assoc] using hb
  obtain ⟨F, hF, hpF, hbound⟩ := rdiv_fitting_grid_event_of_localized_suprema
    V P sample split n ρ ξ (C * d) (C * d ^ 2) hξ radius value
    (fun _ => norm_nonneg _) (mul_nonneg hC.le hd) (by positivity) hlocal hsections
  have hg : ∀ᵐ ω ∂P, gHat n ω ∈ G := (hMLE n hn).1.mono fun _ h => h.1
  obtain ⟨N, hNsub, hN, hpN⟩ := exists_measurable_superset_of_null (ae_iff.1 hg)
  have hNae : ∀ᵐ ω ∂P, ω ∉ N := by
    rw [ae_iff]
    simpa using hpN
  refine ⟨F \ N, hF.diff hN, ?_, ?_⟩
  · have heq : (F \ N : Set Ω) =ᵐ[P] F := by
      filter_upwards [hNae] with ω hω
      exact propext ⟨fun h => h.1, fun h => ⟨h, hω⟩⟩
    rwa [measureReal_congr heq]
  intro ω hω lam hlam h hh
  have hgω : gHat n ω ∈ G := by
    by_contra hnot
    exact hω.2 (hNsub hnot)
  have hb := hbound ω hω.1 lam hlam ⟨h, hh⟩
  dsimp [value] at hb
  rw [rdiv_fitting_deviation_eq_risks V P sample split μ G g₀ gHat support
    B c₀ CG n ω ω lam hIV hDensity hBounds hHyp hOutcome hgω
    h (minNormSolution V) hh hRealizable] at hb
  dsimp [radius, d] at hb
  simpa only [empiricalRisk, rdivEmpiricalLoss, estimatedOperator, ← Submodule.coe_sub, Submodule.norm_coe, mul_add, mul_assoc]
    using hb

-/

end Papers.TsAdaptiveEstimationInference

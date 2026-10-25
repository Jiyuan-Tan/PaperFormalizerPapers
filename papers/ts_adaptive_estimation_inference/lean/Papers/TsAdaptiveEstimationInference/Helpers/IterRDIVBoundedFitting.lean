module
public import Papers.TsAdaptiveEstimationInference.Helpers.IterRDIVFitting
/-! Bounded fixed-center fitting deviations for the finite sample prefix.
The envelope is simultaneous over the hypothesis class. No concentration
assumption is used. The frozen branch has probability one; selected-density
transport retains its explicit prescribed allocation. -/
public section
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory
variable {W X Z Ω : Type*} [MeasurableSpace W] [MeasurableSpace X]
  [MeasurableSpace Z] [MeasurableSpace Ω]

/-- Under [the RDIV model](hyp:hIV), [density realizability](hyp:hDensity),
[the density bounds](hyp:hBounds), [the hypothesis envelope B](hyp:hHyp), and
[the outcome envelope B](hyp:hY), if [the density belongs to its class](hyp:hg),
[the penalty lies in $(0,2]$](hyp:hlam), and [the preceding population center
belongs to the hypothesis class or this is the first iteration](hyp:hcenter),
then [almost every observation simultaneously gives every hypothesis a
fixed-center loss between zero and 12 B²](goal).

A single population null set bounds every fixed-center loss, including the
zero penalty center at the first iteration. -/
-- @node: iter_rdiv_fixed_center_loss_ae_bound
lemma iter_rdiv_fixed_center_loss_ae_bound (V : IVWorld W X Z)
    (mu : Measure X) (G : Set (X → Z → ℝ)) (g₀ g : X → Z → ℝ)
    (support : Set (X × Z)) (B c₀ CG lam : ℝ) (j : ℕ)
    (hIV : RDIVSetting V mu g₀) (hDensity : DensityRealizable V mu G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hHyp : HypothesisClassBounded V support B) (hY : OutcomeBounded V B)
    (hg : g ∈ G) (hlam : lam ∈ Set.Ioc (0 : ℝ) 2)
    (hcenter : populationIterate V lam (j - 1) ∈ V.H ∨ j = 1) :
    ∀ᵐ w ∂V.law, ∀ h ∈ V.H,
      0 ≤ iterRdivFixedCenterLoss V mu g lam j h w ∧
        iterRdivFixedCenterLoss V mu g lam j h w ≤ 12 * B ^ 2 := by
  have hs : ∀ᵐ p ∂V.law.map (fun w => (V.xOf w, V.zOf w)), p ∈ support := by
    rw [hIV.2.1]
    apply (ae_withDensity_iff (hDensity.2 g₀ hDensity.1).1.ennreal_ofReal).2
    exact ae_of_all _ fun p hp => by
      by_contra h
      have hz := hBounds.2.2.2.2 g₀ hDensity.1 p h
      apply hp
      change ENNReal.ofReal (g₀ p.1 p.2) = 0
      rw [hz, ENNReal.ofReal_zero]
  have hsW := ae_of_ae_map (V.measurable_x.prodMk V.measurable_z).aemeasurable hs
  have hop := ae_of_ae_map V.measurable_z.aemeasurable
    (rdiv_hypothesis_density_operator_bounded V mu G g₀ g support B c₀ CG
      hDensity hBounds hHyp hY.1 hg)
  filter_upwards [hsW, hop, hY.2, primalVersion_zero_ae V] with w hw hTw hYw hzero
  intro h hh
  have hhB := hHyp h hh (V.xOf w, V.zOf w) hw
  have hcB : |primalVersion V (populationIterate V lam (j - 1)) (V.xOf w)| ≤ B := by
    rcases hcenter with hc | rfl
    · exact hHyp _ hc (V.xOf w, V.zOf w) hw
    · simpa [populationIterate, hzero, algorithmicZero] using hY.1
  have hres : |V.Y w - densityOperator mu g (primalVersion V h) (V.zOf w)| ≤ 2 * B :=
    (abs_sub _ _).trans (by linarith only [hYw, hTw h hh])
  have hpen : |primalVersion V h (V.xOf w) -
      primalVersion V (populationIterate V lam (j - 1)) (V.xOf w)| ≤ 2 * B :=
    (abs_sub _ _).trans (by linarith only [hhB, hcB])
  have hresSq := pow_le_pow_left₀ (abs_nonneg _) hres 2
  have hpenSq := pow_le_pow_left₀ (abs_nonneg _) hpen 2
  rw [sq_abs] at hresSq hpenSq
  unfold iterRdivFixedCenterLoss
  constructor
  · positivity [hlam.1]
  · have hm := mul_le_mul_of_nonneg_left hpenSq hlam.1.le
    have htwo := mul_le_mul_of_nonneg_right hlam.2 (sq_nonneg (2 * B))
    nlinarith only [hresSq, hm, htwo]

/-- Assume [the RDIV model](hyp:hIV), [density realizability](hyp:hDensity),
[bounded densities](hyp:hBounds), [hypotheses bounded by B](hyp:hHyp), and
[outcomes bounded by B](hyp:hY). If [the fixed density is in its class](hyp:hg),
[the penalty lies in $(0,2]$](hyp:hlam), [the sample size is positive](hyp:hn),
[the population comparator is in the hypothesis class](hyp:hstar), and [its
preceding center is in the class or this is iteration one](hyp:hcenter), then
[there is a measurable probability-one event on which every centered fitting
loss differs from its population mean by at most 24 B²](goal).

The actual fitting block has a measurable probability-one subset on which
the centered deviation is bounded uniformly over all hypotheses. The density
is fixed here, ready for conditional transport by the recorded versions. -/
-- @node: iter_rdiv_bounded_frozen_fixed_center_event
lemma iter_rdiv_bounded_frozen_fixed_center_event (V : IVWorld W X Z)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (sample : AnalysisSample V P) (split : SampleSplit)
    (mu : Measure X) (G : Set (X → Z → ℝ)) (g₀ g : X → Z → ℝ)
    (support : Set (X × Z)) (B c₀ CG lam : ℝ) (n j : ℕ)
    (hIV : RDIVSetting V mu g₀) (hDensity : DensityRealizable V mu G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hHyp : HypothesisClassBounded V support B) (hY : OutcomeBounded V B)
    (hg : g ∈ G) (hlam : lam ∈ Set.Ioc (0 : ℝ) 2) (hn : 0 < n)
    (hstar : populationIterate V lam j ∈ V.H)
    (hcenter : populationIterate V lam (j - 1) ∈ V.H ∨ j = 1) :
    ∃ E : Set Ω, MeasurableSet E ∧ P.real E = 1 ∧ ∀ ω ∈ E, ∀ h ∈ V.H,
      |blockAverage V P sample (split.fit n)
          (fun w => iterRdivFixedCenterLoss V mu g lam j h w -
            iterRdivFixedCenterLoss V mu g lam j (populationIterate V lam j) w) ω -
        ∫ w, iterRdivFixedCenterLoss V mu g lam j h w -
          iterRdivFixedCenterLoss V mu g lam j (populationIterate V lam j) w ∂V.law| ≤
        24 * B ^ 2 := by
  have hb := iter_rdiv_fixed_center_loss_ae_bound V mu G g₀ g support B c₀ CG
    lam j hIV hDensity hBounds hHyp hY hg hlam hcenter
  have hsample : ∀ᵐ ω ∂P, ∀ i : ℕ, ∀ h ∈ V.H,
      0 ≤ iterRdivFixedCenterLoss V mu g lam j h (sample.Z i ω) ∧
        iterRdivFixedCenterLoss V mu g lam j h (sample.Z i ω) ≤ 12 * B ^ 2 := by
    apply ae_all_iff.mpr
    intro i
    have hi : P.map (sample.Z i) = V.law := by
      rw [← (sample.identDist i).map_eq, sample.law]
    have hb' : ∀ᵐ w ∂P.map (sample.Z i), ∀ h ∈ V.H,
        0 ≤ iterRdivFixedCenterLoss V mu g lam j h w ∧
          iterRdivFixedCenterLoss V mu g lam j h w ≤ 12 * B ^ 2 := by
      simpa only [hi] using hb
    exact ae_of_ae_map (sample.meas i).aemeasurable hb'
  obtain ⟨N, hsub, hN, hN0⟩ := exists_measurable_superset_of_null hsample
  refine ⟨Nᶜ, hN.compl, ?_, ?_⟩
  · simp [measureReal_def, measure_compl hN, hN0]
  intro ω hω h hh
  have hsamp : ∀ i : ℕ, ∀ h ∈ V.H,
      0 ≤ iterRdivFixedCenterLoss V mu g lam j h (sample.Z i ω) ∧
        iterRdivFixedCenterLoss V mu g lam j h (sample.Z i ω) ≤ 12 * B ^ 2 := by
    by_contra hbad
    exact hω (hsub hbad)
  let f := fun w => iterRdivFixedCenterLoss V mu g lam j h w -
    iterRdivFixedCenterLoss V mu g lam j (populationIterate V lam j) w
  have hf : Integrable f V.law :=
    (iter_rdiv_fixed_center_loss_integral V mu G g₀ g support B c₀ CG lam j
      hIV hDensity hBounds hHyp hY hg h hh).1.sub
    (iter_rdiv_fixed_center_loss_integral V mu G g₀ g support B c₀ CG lam j
      hIV hDensity hBounds hHyp hY hg _ hstar).1
  have hfB : ∀ᵐ w ∂V.law, |f w| ≤ 12 * B ^ 2 := by
    filter_upwards [hb] with w hw
    have ha := hw h hh
    have hc := hw _ hstar
    exact abs_le.mpr ⟨by dsimp [f]; linarith, by dsimp [f]; linarith⟩
  have hmean : |∫ w, f w ∂V.law| ≤ 12 * B ^ 2 := by
    apply abs_le.mpr
    constructor
    · have hlo := integral_mono_ae (integrable_const (- (12 * B ^ 2))) hf
        (hfB.mono fun w hw => (abs_le.mp hw).1)
      simpa using hlo
    · have hhi := integral_mono_ae hf (integrable_const (12 * B ^ 2))
        (hfB.mono fun w hw => (abs_le.mp hw).2)
      simpa using hhi
  have havg : |blockAverage V P sample (split.fit n) f ω| ≤ 12 * B ^ 2 := by
    have hterm (i : ℕ) : |f (sample.Z i ω)| ≤ 12 * B ^ 2 := by
      have ha := hsamp i h hh
      have hc := hsamp i _ hstar
      exact abs_le.mpr ⟨by dsimp [f]; linarith, by dsimp [f]; linarith⟩
    have hsum : |∑ i ∈ split.fit n, f (sample.Z i ω)| ≤
        ∑ i ∈ split.fit n, (12 * B ^ 2) :=
      (show |∑ i ∈ split.fit n, f (sample.Z i ω)| ≤
        ∑ i ∈ split.fit n, |f (sample.Z i ω)| by
          simpa only [Real.norm_eq_abs] using
            norm_sum_le (split.fit n) (fun i => f (sample.Z i ω))).trans
      (Finset.sum_le_sum (fun i _ => hterm i))
    unfold blockAverage
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ ((split.fit n).card : ℝ)⁻¹)]
    apply (mul_le_mul_of_nonneg_left hsum (by positivity)).trans
    simp [split.card_fit, ne_of_gt hn]
  exact (abs_sub _ _).trans (by linarith only [havg, hmean])

/-- Suppose [the RDIV model holds](hyp:hIV), [the density is realizable](hyp:hDensity),
[densities satisfy their bounds](hyp:hBounds), [hypotheses](hyp:hHyp) and
[outcomes](hyp:hY) are bounded by B, [the selected densities maximize
likelihood](hyp:hMLE), and [fixed-center suprema have coherent versions](hyp:hVersion).
If [the sample size is positive](hyp:hn) and [at most N](hyp:hnN), [the horizon
is positive](hyp:ht), [the iteration is positive](hyp:hj) and [within the
horizon](hyp:hjt), [the penalty is on the grid](hyp:hlam) and [in $(0,2]$](hyp:hdom),
[the population comparator belongs to the class](hyp:hstar), [its preceding
center belongs to the class or the iteration is one](hyp:hcenter), [the squared
radius is at least the inverse sample size](hyp:hr), and [the failure allocation
is between zero and one](hyp:hη), then [a measurable event of probability at least
one minus that allocation bounds every selected-density centered fitting
deviation by 24 B² N times the squared radius](goal).

Coherent-version transport gives the finite-prefix fitting bound for the
original selected density. The radius floor is checked here, not supplied as a
concentration conclusion. This event can use any prescribed positive allocation. -/
-- @node: iter_rdiv_bounded_fixed_center_fitting_event
lemma iter_rdiv_bounded_fixed_center_fitting_event (V : IVWorld W X Z)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (sample : AnalysisSample V P) (split : SampleSplit)
    (mu : Measure X) (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (gHat : ℕ → Ω → X → Z → ℝ) (support : Set (X × Z))
    (B c₀ CG ρ lam r η : ℝ) (n N t j : ℕ)
    (hIV : RDIVSetting V mu g₀) (hDensity : DensityRealizable V mu G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hHyp : HypothesisClassBounded V support B) (hY : OutcomeBounded V B)
    (hMLE : MLEMaximizerSelected V P sample split G gHat)
    (hVersion : IterRDIVFixedCenterSupremumVersion V P sample split mu gHat ρ)
    (hn : 0 < n) (hnN : n ≤ N) (ht : 1 ≤ t) (hj : 1 ≤ j) (hjt : j ≤ t)
    (hlam : lam ∈ regGrid ρ n) (hdom : lam ∈ Set.Ioc (0 : ℝ) 2)
    (hstar : populationIterate V lam j ∈ V.H)
    (hcenter : populationIterate V lam (j - 1) ∈ V.H ∨ j = 1)
    (hr : 1 / (n : ℝ) ≤ r ^ 2) (hη : η ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ E : Set Ω, MeasurableSet E ∧ 1 - η ≤ P.real E ∧ ∀ ω ∈ E, ∀ h ∈ V.H,
      |blockAverage V P sample (split.fit n)
          (fun w => iterRdivFixedCenterLoss V mu (gHat n ω) lam j h w -
            iterRdivFixedCenterLoss V mu (gHat n ω) lam j
              (populationIterate V lam j) w) ω -
        ∫ w, iterRdivFixedCenterLoss V mu (gHat n ω) lam j h w -
          iterRdivFixedCenterLoss V mu (gHat n ω) lam j
            (populationIterate V lam j) w ∂V.law| ≤
        (24 * B ^ 2 * N) * r ^ 2 := by
  have hlocal : ∀ᵐ pre ∂P, 1 - η ≤ P.real {fit | ∀ h ∈ V.H,
      |blockAverage V P sample (split.fit n)
          (fun w => iterRdivFixedCenterLoss V mu (gHat n pre) lam j h w -
            iterRdivFixedCenterLoss V mu (gHat n pre) lam j
              (populationIterate V lam j) w) fit -
        ∫ w, iterRdivFixedCenterLoss V mu (gHat n pre) lam j h w -
          iterRdivFixedCenterLoss V mu (gHat n pre) lam j
            (populationIterate V lam j) w ∂V.law| ≤
        0 * ‖h - populationIterate V lam j‖ + 24 * B ^ 2} := by
    filter_upwards [(hMLE n hn).1] with pre hpre
    obtain ⟨F, hF, hpF, hgood⟩ := iter_rdiv_bounded_frozen_fixed_center_event
      V P sample split mu G g₀ (gHat n pre) support B c₀ CG lam n j
      hIV hDensity hBounds hHyp hY hpre.1 hdom hn hstar hcenter
    have hp : 1 - η ≤ P.real F := by rw [hpF]; linarith only [hη.1]
    apply hp.trans
    apply measureReal_mono (h₂ := measure_ne_top P _)
    intro fit hfit h hh
    simpa only [zero_mul, zero_add] using hgood fit hfit h hh
  obtain ⟨E, hE, hpE, hgood⟩ := iter_rdiv_thaw_fixed_center_deviations V P sample split
    mu gHat ρ n t j lam 0 (24 * B ^ 2) η hn ht hj hjt hlam
    le_rfl (by positivity) hη hVersion hlocal
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hN : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le hn hnN)
  have hfloor : 1 / (N : ℝ) ≤ r ^ 2 :=
    (one_div_le_one_div_of_le hnR (by exact_mod_cast hnN)).trans hr
  have hNr : 1 ≤ (N : ℝ) * r ^ 2 := by
    simpa only [mul_comm] using (div_le_iff₀ hN).mp hfloor
  have hscale : 24 * B ^ 2 ≤ (24 * B ^ 2 * N) * r ^ 2 := by
    have hm := mul_le_mul_of_nonneg_left hNr (by positivity : 0 ≤ 24 * B ^ 2)
    nlinarith only [hm]
  refine ⟨E, hE, hpE, ?_⟩
  intro ω hω h hh
  have hb := hgood ω hω h hh
  simp only [zero_mul, zero_add] at hb
  exact hb.trans hscale

/-- Under [the RDIV model](hyp:hIV), [density realizability](hyp:hDensity),
[density bounds](hyp:hBounds), [the hypothesis envelope B](hyp:hHyp), [the
outcome envelope B](hyp:hY), [likelihood-maximizing density selection](hyp:hMLE),
and [coherent fixed-center supremum versions](hyp:hVersion), suppose [the sample
size is positive](hyp:hn), [is at most N](hyp:hnN), [the horizon is positive](hyp:ht),
[the failure probability lies between zero and one](hyp:hξ), and [the squared
radius exceeds the inverse sample size](hyp:hfloor). If [all grid penalties in
the segment lie in $(0,2]$](hyp:hdom) and [their positive population iterates
through the horizon belong to the hypothesis class](hyp:hstar), then [one
measurable event of probability at least one minus a quarter of the failure
probability bounds all corresponding centered fitting deviations by 24 B² N
times the squared radius, uniformly over hypotheses](goal).

A finite-prefix fitting event retains the original fixed-center increments
on the whole iteration grid. The per-coordinate allocation is exactly eta/4,
so the union spends only the fitting quarter, including at sample size one. -/
-- @node: iter_rdiv_bounded_fixed_center_iteration_grid_event
lemma iter_rdiv_bounded_fixed_center_iteration_grid_event (V : IVWorld W X Z)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (sample : AnalysisSample V P) (split : SampleSplit)
    (mu : Measure X) (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (gHat : ℕ → Ω → X → Z → ℝ) (support : Set (X × Z))
    (B c₀ CG ρ ξ r : ℝ) (n N t : ℕ) (segment : Set ℝ)
    (hIV : RDIVSetting V mu g₀) (hDensity : DensityRealizable V mu G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hHyp : HypothesisClassBounded V support B) (hY : OutcomeBounded V B)
    (hMLE : MLEMaximizerSelected V P sample split G gHat)
    (hVersion : IterRDIVFixedCenterSupremumVersion V P sample split mu gHat ρ)
    (hn : 0 < n) (hnN : n ≤ N) (ht : 1 ≤ t)
    (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1) (hfloor : 1 / (n : ℝ) ≤ r ^ 2)
    (hdom : ∀ lam ∈ regGrid ρ n, lam ∈ segment → lam ∈ Set.Ioc (0 : ℝ) 2)
    (hstar : ∀ lam ∈ regGrid ρ n, lam ∈ segment → ∀ j, 1 ≤ j → j ≤ t →
      populationIterate V lam j ∈ V.H) :
    ∃ E : Set Ω, MeasurableSet E ∧ 1 - ξ / 4 ≤ P.real E ∧
      ∀ ω ∈ E, ∀ lam ∈ regGrid ρ n, lam ∈ segment → ∀ j, 1 ≤ j → j ≤ t →
        ∀ h ∈ V.H,
        |blockAverage V P sample (split.fit n)
            (fun w => iterRdivFixedCenterLoss V mu (gHat n ω) lam j h w -
              iterRdivFixedCenterLoss V mu (gHat n ω) lam j
                (populationIterate V lam j) w) ω -
          ∫ w, iterRdivFixedCenterLoss V mu (gHat n ω) lam j h w -
            iterRdivFixedCenterLoss V mu (gHat n ω) lam j
              (populationIterate V lam j) w ∂V.law| ≤
          (24 * B ^ 2 * N) * r ^ 2 := by
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hkR : (1 : ℝ) ≤ (terminalIndex ρ n + 1 : ℕ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  have hden : 1 ≤ (t : ℝ) * (terminalIndex ρ n + 1 : ℕ) := by nlinarith
  have hη : iterGridConfidence ρ ξ n t ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · unfold iterGridConfidence
      positivity [hξ.1]
    · unfold iterGridConfidence
      rw [Nat.cast_mul]
      apply (div_lt_iff₀ (by positivity)).2
      simpa only [one_mul] using hξ.2.trans_le hden
  classical
  let good : ℕ → ℝ → Ω → Prop := fun j lam ω =>
    lam ∈ segment → ∀ h ∈ V.H,
      |blockAverage V P sample (split.fit n)
          (fun w => iterRdivFixedCenterLoss V mu (gHat n ω) lam j h w -
            iterRdivFixedCenterLoss V mu (gHat n ω) lam j
              (populationIterate V lam j) w) ω -
        ∫ w, iterRdivFixedCenterLoss V mu (gHat n ω) lam j h w -
          iterRdivFixedCenterLoss V mu (gHat n ω) lam j
            (populationIterate V lam j) w ∂V.law| ≤
        (24 * B ^ 2 * N) * r ^ 2
  have hlocal : ∀ j ∈ Finset.Icc 1 t, ∀ lam ∈ regGrid ρ n,
      ∃ E : Set Ω, MeasurableSet E ∧
        1 - iterGridConfidence ρ ξ n t / 4 ≤ P.real E ∧
        ∀ ω ∈ E, good j lam ω := by
    intro j hj lam hl
    obtain ⟨hj₁, hjt⟩ := Finset.mem_Icc.mp hj
    by_cases hs : lam ∈ segment
    · have hcenter : populationIterate V lam (j - 1) ∈ V.H ∨ j = 1 := by
        by_cases hjone : j = 1
        · exact Or.inr hjone
        · exact Or.inl (hstar lam hl hs (j - 1) (by omega) (by omega))
      obtain ⟨E, hE, hpE, hgood⟩ := iter_rdiv_bounded_fixed_center_fitting_event
        V P sample split mu G g₀ gHat support B c₀ CG ρ lam r
        (iterGridConfidence ρ ξ n t / 4) n N t j hIV hDensity hBounds hHyp hY
        hMLE hVersion hn hnN ht hj₁ hjt hl (hdom lam hl hs)
        (hstar lam hl hs j hj₁ hjt) hcenter hfloor
        ⟨by linarith only [hη.1], by linarith only [hη.2]⟩
      exact ⟨E, hE, hpE, fun ω hω _ => hgood ω hω⟩
    · refine ⟨Set.univ, MeasurableSet.univ, ?_, ?_⟩
      · simp only [measureReal_def, measure_univ, ENNReal.toReal_one]
        linarith [hη.1]
      · intro ω hω hs'
        exact (hs hs').elim
  choose F hF hpF hgood using hlocal
  let E : ℕ → ℝ → Set Ω := fun j lam =>
    if hj : j ∈ Finset.Icc 1 t then
      if hl : lam ∈ regGrid ρ n then F j hj lam hl else Set.univ
    else Set.univ
  have hEm : ∀ j ∈ Finset.Icc 1 t, ∀ lam ∈ regGrid ρ n, MeasurableSet (E j lam) := by
    intro j hj lam hl
    simpa only [E, dif_pos hj, dif_pos hl] using hF j hj lam hl
  have hEp : ∀ j ∈ Finset.Icc 1 t, ∀ lam ∈ regGrid ρ n,
      1 - iterGridConfidence ρ ξ n t / 4 ≤ P.real (E j lam) := by
    intro j hj lam hl
    simpa only [E, dif_pos hj, dif_pos hl] using hpF j hj lam hl
  obtain ⟨hm, hp⟩ := iter_rdiv_iteration_grid_event_budget P ρ ξ n t hξ.1.le ht E hEm hEp
  refine ⟨⋂ j ∈ Finset.Icc 1 t, ⋂ lam ∈ regGrid ρ n, E j lam, hm, hp, ?_⟩
  intro ω hω lam hl hs j hj hjt h hh
  have hj' : j ∈ Finset.Icc 1 t := Finset.mem_Icc.mpr ⟨hj, hjt⟩
  have hmem := Set.mem_iInter₂.mp (Set.mem_iInter₂.mp hω j hj') lam hl
  simp only [E, dif_pos hj', dif_pos hl] at hmem
  exact hgood j hj' lam hl ω hmem hs h hh


end Papers.TsAdaptiveEstimationInference

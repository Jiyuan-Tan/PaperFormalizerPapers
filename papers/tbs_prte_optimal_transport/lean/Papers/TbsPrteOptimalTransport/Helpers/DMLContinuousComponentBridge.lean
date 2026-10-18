module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLBinaryComponentBridge
/-! Continuous nuisance coordinates for the oracle DML argument.
Restricting shares to their policy sets preserves the encoded nuisance family
and the score, while supplying the support condition used by admissibility. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Set Filter
open scoped Classical

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]

-- @node: restrictContShares
/-- For [a system of treatment levels and policy sets](hyp:L) and [a continuous nuisance record](hyp:e),
[the share-restricted nuisance record](goal) sets each share outside its policy set to zero and retains all other coordinates. -/
noncomputable def restrictContShares (L : LevelData Z X)
    (e : NuisanceCont L) : NuisanceCont L :=
  { e with share := fun a z x => if z ∈ L.T a.val.1 a.val.2 then e.share a z x else 0 }

-- @node: contComponent_restrictContShares
/-- [Restricting nuisance shares to their policy sets leaves every encoded continuous nuisance coordinate unchanged at every covariate value](goal). -/
lemma contComponent_restrictContShares (M : LatentIVModel Ω X Z)
    (L : LevelData Z X) (e : NuisanceCont L) (c : ℕ × ℕ × ℕ × Z) (x : X) :
    contComponent M L (restrictContShares L e) c x = contComponent M L e c x := by
  rcases c with ⟨code, k, j, z⟩
  simp only [contComponent, restrictContShares]
  split <;> try rfl
  by_cases hz : z ∈ L.T k j
  · simp only [if_pos hz, shareValue]
  · simp only [if_neg hz]

-- @node: pooledQ_restrictContShares
/-- [Restricting nuisance shares to their policy sets leaves the pooled policy quantity unchanged for every level pair and covariate value](goal). -/
lemma pooledQ_restrictContShares (phi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (e : NuisanceCont L) (k j : ℕ) (x : X) :
    pooledQ phi L (restrictContShares L e) k j x = pooledQ phi L e k j x := by
  unfold pooledQ
  split
  · rfl
  · split
    · rfl
    · apply Finset.sum_congr rfl
      intro z hz
      simp only [shareValue]
      split
      · simp only [restrictContShares, if_pos hz]
      · rfl

-- @node: RqCont_restrictContShares
/-- [Restricting nuisance shares to their policy sets leaves the continuous policy-derivative correction unchanged at every observation and level pair](goal). -/
lemma RqCont_restrictContShares (dphi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (e : NuisanceCont L) (k j : ℕ) (o : Obs X Z) :
    RqCont dphi L (restrictContShares L e) k j o = RqCont dphi L e k j o := by
  rfl

-- @node: psiCont_restrictContShares
/-- If [the number of treatment levels is positive](hyp:hK),
[restricting nuisance shares to their policy sets leaves the continuous orthogonal score unchanged at every observation](goal). -/
lemma psiCont_restrictContShares (M : LatentIVModel Ω X Z)
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (hK : LevelCountPos L.K) (o : Obs X Z) (e : NuisanceCont L) :
    psiCont M phi dphi L hK o (restrictContShares L e) =
      psiCont M phi dphi L hK o e := by
  simp only [psiCont, psiProd, contScoreComponents,
    pooledQ_restrictContShares, RqCont_restrictContShares]
  rfl

-- @node: restrictContShares_admissible_of_encoded_clipping
/-- If [the continuous nuisance coordinates satisfy clipping bounds](hyp:hc),
[the fitted shares form a simplex on each policy set](hyp:hs), and
[every encoded coordinate is measurable](hyp:hm), then
[restricting shares to their policy sets produces an admissible continuous nuisance record](goal). -/
lemma restrictContShares_admissible_of_encoded_clipping (M : LatentIVModel Ω X Z)
    (L : LevelData Z X) (e : NuisanceCont L)
    (hc : ContClipping M L e) (hs : ContFittedSharesSimplex L e)
    (hm : ∀ c, Measurable (contComponent M L e c)) :
    ContAdmissible M L (restrictContShares L e) := by
  obtain ⟨hp, hl, hr, hshare, hf, ht, hn, hmp, hmm, hjp, hjm, hjfp, hjfm, _hprob⟩ := hc
  let z₀ : Z := Classical.choice inferInstance
  have hm_prop (z : Z) : Measurable (e.prop z) := by
    first | fun_prop | skip
    simpa [contComponent] using
      (show Measurable (fun x => contComponent M L e (0, 0, 0, z) x) from hm (0, 0, 0, z))
  have hm_pLev (k : PositiveIndex L.K) : Measurable (e.pLev k) := by
    first | fun_prop | skip
    simpa [contComponent, positiveValue, k.property] using
      (show Measurable (fun x => contComponent M L e (1, k, 0, z₀) x) from hm (1, k, 0, z₀))
  have hm_piLev (k : PositiveIndex L.K) : Measurable (e.piLev k) := by
    first | fun_prop | skip
    simpa [contComponent, positiveValue, k.property] using
      (show Measurable (fun x => contComponent M L e (2, k, 0, z₀) x) from hm (2, k, 0, z₀))
  have hm_tauLev (a : RegularIndex L) : Measurable (e.tauLev a) := by
    first | fun_prop | skip
    simpa [contComponent, regularValue, a.property] using
      (show Measurable (fun x => contComponent M L e (3, a.val.1, a.val.2, z₀) x) from hm (3, a.val.1, a.val.2, z₀))
  have hm_gammaFull (k : Fin L.K) : Measurable (e.gammaFull k) := by
    first | fun_prop | skip
    simpa [contComponent, fullValue, k.isLt] using
      (show Measurable (fun x => contComponent M L e (5, k, 0, z₀) x) from hm (5, k, 0, z₀))
  have hm_gamma (a : RegularIndex L) : Measurable (e.gamma a) := by
    first | fun_prop | skip
    simpa [contComponent, regularValue, a.property] using
      (show Measurable (fun x => contComponent M L e (6, a.val.1, a.val.2, z₀) x) from hm (6, a.val.1, a.val.2, z₀))
  have hm_gammaTail : Measurable (e.gammaTail) := by
    first | fun_prop | skip
    simpa [contComponent] using
      (show Measurable (fun x => contComponent M L e (7, 0, 0, z₀) x) from hm (7, 0, 0, z₀))
  have hm_nu (a : BoundaryIndex L) : Measurable (e.nu a) := by
    first | fun_prop | skip
    have hne : a.val.2 ≠ 0 := by have h := a.property; omega
    simpa [contComponent, nuValue, a.property, hne] using
      (show Measurable (fun x => contComponent M L e (8, a.val.1, a.val.2, z₀) x) from hm (8, a.val.1, a.val.2, z₀))
  have hm_Mplus (a : IndicatorIndex L) : Measurable (e.Mplus a) := by
    first | fun_prop | skip
    simpa [contComponent, boundaryValue, a.property] using
      (show Measurable (fun x => contComponent M L e (9, a.val.1, a.val.2, z₀) x) from hm (9, a.val.1, a.val.2, z₀))
  have hm_Mminus (a : MinusIndicatorIndex L) : Measurable (e.Mminus a) := by
    first | fun_prop | skip
    simpa [contComponent, minusBoundaryValue, a.property] using
      (show Measurable (fun x => contComponent M L e (10, a.val.1, a.val.2, z₀) x) from hm (10, a.val.1, a.val.2, z₀))
  have hm_Jplus (a : MeanIndex L) : Measurable (e.Jplus a) := by
    first | fun_prop | skip
    simpa [contComponent, meanValue, a.property] using
      (show Measurable (fun x => contComponent M L e (11, a.val.1, a.val.2, z₀) x) from hm (11, a.val.1, a.val.2, z₀))
  have hm_Jminus (a : MinusMeanIndex L) : Measurable (e.Jminus a) := by
    first | fun_prop | skip
    simpa [contComponent, minusMeanValue, a.property] using
      (show Measurable (fun x => contComponent M L e (12, a.val.1, a.val.2, z₀) x) from hm (12, a.val.1, a.val.2, z₀))
  have hm_JfullPlus (k : Fin L.K) : Measurable (e.JfullPlus k) := by
    first | fun_prop | skip
    simpa [contComponent, fullValue, k.isLt] using
      (show Measurable (fun x => contComponent M L e (13, k, 0, z₀) x) from hm (13, k, 0, z₀))
  have hm_JfullMinus (k : {k : ℕ // 1 ≤ k ∧ k < L.K}) : Measurable (e.JfullMinus k) := by
    first | fun_prop | skip
    simpa [contComponent, minusFullValue, k.property] using
      (show Measurable (fun x => contComponent M L e (14, k, 0, z₀) x) from hm (14, k, 0, z₀))
  have hm_share (a : RegularIndex L) (z : Z) :
      Measurable ((restrictContShares L e).share a z) := by
    first | fun_prop | skip
    simpa [contComponent, shareValue, restrictContShares, a.property] using
      (show Measurable (fun x => contComponent M L e (4, a.val.1, a.val.2, z) x)
        from hm (4, a.val.1, a.val.2, z))
  refine ⟨fun z => Eventually.of_forall (hp z), hm_prop,
    fun k => Eventually.of_forall (fun x => (hl k x).1), hm_pLev,
    fun k => Eventually.of_forall (fun x => (hl k x).2), hm_piLev,
    fun a => Eventually.of_forall (fun x => (hr a x).1), hm_tauLev,
    ?_, hm_share, fun k => Eventually.of_forall (hf k), hm_gammaFull,
    fun a => Eventually.of_forall (fun x => (hr a x).2), hm_gamma,
    Eventually.of_forall ht, hm_gammaTail,
    fun a => Eventually.of_forall (hn a), hm_nu,
    fun a => Eventually.of_forall (hmp a), hm_Mplus,
    fun a => Eventually.of_forall (hmm a), hm_Mminus,
    fun a => Eventually.of_forall (hjp a), hm_Jplus,
    fun a => Eventually.of_forall (hjm a), hm_Jminus,
    fun k => Eventually.of_forall (hjfp k), hm_JfullPlus,
    fun k => Eventually.of_forall (hjfm k), hm_JfullMinus, ?_⟩
  · intro a z
    apply Eventually.of_forall
    intro x
    by_cases hz : z ∈ L.T a.val.1 a.val.2
    · simpa only [restrictContShares, if_pos hz] using hshare a z x
    · simp [restrictContShares, hz]
  · intro a
    apply Eventually.of_forall
    intro x
    refine ⟨?_, ?_⟩
    · simpa only [restrictContShares, Finset.sum_ite_mem, Finset.inter_self]
        using (hs a x).2
    · intro z hz
      simp only [restrictContShares, if_neg hz]

-- @node: continuous_component_rates_to_oracle_rates
/-- If [the encoded fitted continuous nuisance family has the finite nuisance convergence rates relative to a reference record](hyp:hr), then
[those rates hold separately for instrument propensities, treatment and assignment probabilities, regular policy masses, shares restricted to each policy set, full and regular product weights, the tail weight, quantile boundaries, both indicator regressions, both band mean regressions, and both full-interval mean regressions](goal). -/
lemma continuous_component_rates_to_oracle_rates (M : LatentIVModel Ω X Z)
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (L : LevelData Z X) (eh : ℕ → A → NuisanceCont L) (e0 : NuisanceCont L)
    (hr : FiniteNuisanceRates M μ (fun n a => contComponent M L (eh n a))
      (contComponent M L e0)) :
    FiniteNuisanceRates M μ (fun n a => (eh n a).prop) e0.prop ∧
    FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev ∧
    FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) e0.piLev ∧
    FiniteNuisanceRates M μ (fun n a => (eh n a).tauLev) e0.tauLev ∧
    (∀ t, FiniteNuisanceRates M μ (fun n a => (restrictContShares L (eh n a)).share t)
      ((restrictContShares L e0).share t)) ∧
    FiniteNuisanceRates M μ (fun n a => (eh n a).gammaFull) e0.gammaFull ∧
    FiniteNuisanceRates M μ (fun n a => (eh n a).gamma) e0.gamma ∧
    FiniteNuisanceRates M μ (fun n a (_ : Unit) => (eh n a).gammaTail)
      (fun _ => e0.gammaTail) ∧
    FiniteNuisanceRates M μ (fun n a => (eh n a).nu) e0.nu ∧
    FiniteNuisanceRates M μ (fun n a => (eh n a).Mplus) e0.Mplus ∧
    FiniteNuisanceRates M μ (fun n a => (eh n a).Mminus) e0.Mminus ∧
    FiniteNuisanceRates M μ (fun n a => (eh n a).Jplus) e0.Jplus ∧
    FiniteNuisanceRates M μ (fun n a => (eh n a).Jminus) e0.Jminus ∧
    FiniteNuisanceRates M μ (fun n a => (eh n a).JfullPlus) e0.JfullPlus ∧
    FiniteNuisanceRates M μ (fun n a => (eh n a).JfullMinus) e0.JfullMinus := by
  let z₀ : Z := Classical.choice inferInstance
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply nuisanceRates_of_encoded_coordinate M μ _ _ hr
      (fun z : Z => (0, 0, 0, z))
    · intro n a z x
      rfl
    · intro z x
      rfl
  · apply nuisanceRates_of_encoded_coordinate M μ _ _ hr
      (fun k : PositiveIndex L.K => (1, k, 0, z₀))
    · intro n a k x
      simp [contComponent, positiveValue, k.property]
    · intro k x
      simp [contComponent, positiveValue, k.property]
  · apply nuisanceRates_of_encoded_coordinate M μ _ _ hr
      (fun k : PositiveIndex L.K => (2, k, 0, z₀))
    · intro n a k x
      simp [contComponent, positiveValue, k.property]
    · intro k x
      simp [contComponent, positiveValue, k.property]
  · apply nuisanceRates_of_encoded_coordinate M μ _ _ hr
      (fun a : RegularIndex L => (3, a.val.1, a.val.2, z₀))
    · intro n sample a x
      simp [contComponent, regularValue, a.property]
    · intro a x
      simp [contComponent, regularValue, a.property]
  · intro t
    apply nuisanceRates_of_encoded_coordinate M μ _ _ hr
      (fun z => (4, t.val.1, t.val.2, z))
    · intro n a z x
      simp [contComponent, shareValue, restrictContShares, t.property]
    · intro z x
      simp [contComponent, shareValue, restrictContShares, t.property]
  · apply nuisanceRates_of_encoded_coordinate M μ _ _ hr
      (fun k : Fin L.K => (5, k, 0, z₀))
    · intro n a k x
      simp [contComponent, fullValue, k.isLt]
    · intro k x
      simp [contComponent, fullValue, k.isLt]
  · apply nuisanceRates_of_encoded_coordinate M μ _ _ hr
      (fun a : RegularIndex L => (6, a.val.1, a.val.2, z₀))
    · intro n sample a x
      simp [contComponent, regularValue, a.property]
    · intro a x
      simp [contComponent, regularValue, a.property]
  · apply nuisanceRates_of_encoded_coordinate M μ _ _ hr
      (fun u : Unit => (7, 0, 0, z₀))
    · intro n a u x
      simp [contComponent]
    · intro u x
      simp [contComponent]
  · apply nuisanceRates_of_encoded_coordinate M μ _ _ hr
      (fun a : BoundaryIndex L => (8, a.val.1, a.val.2, z₀))
    · intro n sample a x
      have hne : a.val.2 ≠ 0 := by have h := a.property; omega
      simp [contComponent, nuValue, a.property, hne]
    · intro a x
      have hne : a.val.2 ≠ 0 := by have h := a.property; omega
      simp [contComponent, nuValue, a.property, hne]
  · apply nuisanceRates_of_encoded_coordinate M μ _ _ hr
      (fun a : IndicatorIndex L => (9, a.val.1, a.val.2, z₀))
    · intro n sample a x
      simp [contComponent, boundaryValue, a.property]
    · intro a x
      simp [contComponent, boundaryValue, a.property]
  · apply nuisanceRates_of_encoded_coordinate M μ _ _ hr
      (fun a : MinusIndicatorIndex L => (10, a.val.1, a.val.2, z₀))
    · intro n sample a x
      simp [contComponent, minusBoundaryValue, a.property]
    · intro a x
      simp [contComponent, minusBoundaryValue, a.property]
  · apply nuisanceRates_of_encoded_coordinate M μ _ _ hr
      (fun a : MeanIndex L => (11, a.val.1, a.val.2, z₀))
    · intro n sample a x
      simp [contComponent, meanValue, a.property]
    · intro a x
      simp [contComponent, meanValue, a.property]
  · apply nuisanceRates_of_encoded_coordinate M μ _ _ hr
      (fun a : MinusMeanIndex L => (12, a.val.1, a.val.2, z₀))
    · intro n sample a x
      simp [contComponent, minusMeanValue, a.property]
    · intro a x
      simp [contComponent, minusMeanValue, a.property]
  · apply nuisanceRates_of_encoded_coordinate M μ _ _ hr
      (fun k : Fin L.K => (13, k, 0, z₀))
    · intro n a k x
      simp [contComponent, fullValue, k.isLt]
    · intro k x
      simp [contComponent, fullValue, k.isLt]
  · apply nuisanceRates_of_encoded_coordinate M μ _ _ hr
      (fun k : {k : ℕ // 1 ≤ k ∧ k < L.K} => (14, k, 0, z₀))
    · intro n a k x
      simp [contComponent, minusFullValue, k.property]
    · intro k x
      simp [contComponent, minusFullValue, k.property]

-- @node: restrictContShares_eq_of_admissible
/-- If [a continuous nuisance record is admissible](hyp:he), then
[restricting its shares to their policy sets leaves all shares unchanged for almost every covariate value](goal). -/
lemma restrictContShares_eq_of_admissible (M : LatentIVModel Ω X Z)
    (L : LevelData Z X) (e : NuisanceCont L) (he : ContAdmissible M L e) :
    ∀ᵐ x ∂xLaw M, ∀ a z, (restrictContShares L e).share a z x = e.share a z x := by
  rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hs⟩
  have hs' := ae_all_iff.mpr hs
  filter_upwards [hs'] with x hx
  intro a z
  by_cases hz : z ∈ L.T a.val.1 a.val.2
  · simp only [restrictContShares, if_pos hz]
  · simp only [restrictContShares, if_neg hz, (hx a).2 z hz]

end Papers.TbsPrteOptimalTransport

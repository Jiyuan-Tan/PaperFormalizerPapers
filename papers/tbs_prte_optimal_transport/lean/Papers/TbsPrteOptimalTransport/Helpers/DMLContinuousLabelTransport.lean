module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousScoreBounds
/-! Transport continuous nuisances across equal recovered labels.
Numerical population and empirical levels need not agree: only the indices and
instrument sets enter the fitted score and clipping conditions. -/
@[expose] public section
set_option linter.style.openClassical false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]

-- @node: relabelContNuisance
/-- For [a destination level structure](hyp:L), [a source level structure](hyp:L'),
[equality of their recovered labels](hyp:hL), and [a continuous nuisance record on
the source structure](hyp:e), the [relabeled nuisance record](goal) preserves all
numerical coordinates while treating them as coordinates on the destination structure. -/
def relabelContNuisance (L L' : LevelData Z X)
    (hL : recoveryLabels L' = recoveryLabels L) (e : NuisanceCont L') :
    NuisanceCont L := by
  rcases L with ⟨K, l, S, T, p, q⟩
  rcases L' with ⟨K', l', S', T', p', q'⟩
  have hk : K' = K := congrArg Prod.fst hL
  have hl : l' = l := congrArg (fun t => t.2.1) hL
  cases hk
  cases hl
  exact {
    prop := e.prop
    pLev := e.pLev
    piLev := e.piLev
    tauLev := e.tauLev
    share := e.share
    higherPolicyFit := e.higherPolicyFit
    higherBaselineFit := e.higherBaselineFit
    gammaFull := e.gammaFull
    gamma := e.gamma
    gammaTail := e.gammaTail
    nu := e.nu
    Mplus := e.Mplus
    Mminus := e.Mminus
    Jplus := e.Jplus
    Jminus := e.Jminus
    JfullPlus := e.JfullPlus
    JfullMinus := e.JfullMinus }

-- @node: contComponent_relabelContNuisance
/-- If [two level structures have identical recovered labels](hyp:hL), then
[relabeling a continuous nuisance record preserves every encoded component at
every covariate value](goal). -/
lemma contComponent_relabelContNuisance (M : LatentIVModel Ω X Z)
    (L L' : LevelData Z X) (hL : recoveryLabels L' = recoveryLabels L)
    (e : NuisanceCont L') (c : ℕ × ℕ × ℕ × Z) (x : X) :
    contComponent M L (relabelContNuisance L L' hL e) c x =
      contComponent M L' e c x := by
  rcases L with ⟨K, l, S, T, p, q⟩
  rcases L' with ⟨K', l', S', T', p', q'⟩
  simp only [recoveryLabels, Prod.mk.injEq] at hL
  rcases hL with ⟨rfl, rfl, rfl, rfl⟩
  cases e
  simp only [relabelContNuisance]
  rfl

-- @node: relabelContNuisance_regular
/-- If [two level structures have identical recovered labels](hyp:hL) and the
source nuisance satisfies [clipping](hyp:hc), [the fitted-share simplex
restrictions](hyp:hs), and [denominator clipping at the given overlap level](hyp:hd),
then [its relabeled record satisfies all three restrictions on the destination
structure](goal). -/
lemma relabelContNuisance_regular (M : LatentIVModel Ω X Z)
    (L L' : LevelData Z X) (hL : recoveryLabels L' = recoveryLabels L)
    (e : NuisanceCont L') (cpi : ℝ)
    (hc : ContClipping M L' e) (hs : ContFittedSharesSimplex L' e)
    (hd : ContDenominatorsClipped L' e cpi) :
    ContClipping M L (relabelContNuisance L L' hL e) ∧
    ContFittedSharesSimplex L (relabelContNuisance L L' hL e) ∧
    ContDenominatorsClipped L (relabelContNuisance L L' hL e) cpi := by
  rcases L with ⟨K, l, S, T, p, q⟩
  rcases L' with ⟨K', l', S', T', p', q'⟩
  simp only [recoveryLabels, Prod.mk.injEq] at hL
  rcases hL with ⟨rfl, rfl, rfl, rfl⟩
  cases e
  simp only [relabelContNuisance]
  exact ⟨hc, hs, hd⟩

-- @node: psiCont_relabelContNuisance
/-- If [the two level structures have identical recovered labels](hyp:hL) and
[the destination](hyp:hK) and [source](hyp:hK') each have a positive number of
levels, then [relabeling the nuisance record leaves the continuous score unchanged
at every observation](goal). -/
lemma psiCont_relabelContNuisance (M : LatentIVModel Ω X Z)
    (phi dphi : Z → X → ℝ → ℝ) (L L' : LevelData Z X)
    (hL : recoveryLabels L' = recoveryLabels L)
    (hK : LevelCountPos L.K) (hK' : LevelCountPos L'.K)
    (e : NuisanceCont L') (o : Obs X Z) :
    psiCont M phi dphi L hK o (relabelContNuisance L L' hL e) =
      psiCont M phi dphi L' hK' o e := by
  rcases L with ⟨K, l, S, T, p, q⟩
  rcases L' with ⟨K', l', S', T', p', q'⟩
  simp only [recoveryLabels, Prod.mk.injEq] at hL
  rcases hL with ⟨rfl, rfl, rfl, rfl⟩
  cases e
  simp only [relabelContNuisance]
  rfl

-- @node: repairContNuisance_component_eq_of_labels_eq
/-- Suppose [the source and destination have identical recovered labels](hyp:hL),
[every regular destination policy set is nonempty](hyp:hne), [the encoded array
equals every component of the source nuisance](hyp:heq), and that nuisance satisfies
[clipping](hyp:hc), [the fitted-share simplex restrictions](hyp:hs), and
[denominator clipping](hyp:hd). Then [decoding and repairing the array on the
destination structure reproduces every source component at every covariate value](goal). -/
lemma repairContNuisance_component_eq_of_labels_eq
    (M : LatentIVModel Ω X Z) (L L' : LevelData Z X)
    (hL : recoveryLabels L' = recoveryLabels L) (cpi : ℝ)
    (hne : ∀ a : RegularIndex L, (L.T a.val.1 a.val.2).Nonempty)
    (F : (ℕ × ℕ × ℕ × Z) → X → ℝ) (e : NuisanceCont L')
    (heq : ∀ c x, F c x = contComponent M L' e c x)
    (hc : ContClipping M L' e) (hs : ContFittedSharesSimplex L' e)
    (hd : ContDenominatorsClipped L' e cpi) (c : ℕ × ℕ × ℕ × Z) (x : X) :
    contComponent M L (repairContNuisance M L cpi hne (decodeContComponents L F)) c x =
      contComponent M L' e c x := by
  let er := relabelContNuisance L L' hL e
  have hr := relabelContNuisance_regular M L L' hL e cpi hc hs hd
  have hF : ∀ c x, F c x = contComponent M L er c x := by
    intro c x
    rw [contComponent_relabelContNuisance]
    exact heq c x
  rw [← contComponent_relabelContNuisance M L L' hL e c x]
  exact repairContNuisance_component_eq_on_recovery M L L rfl cpi hne F er
    hF hr.1 hr.2.1 hr.2.2 c x

-- @node: psiCont_eq_of_contComponent_eq_of_labels_eq
/-- If [two level structures have identical recovered labels](hyp:hL), [the first
has a positive level count](hyp:hK), [the second has a positive level count](hyp:hK'),
and [their nuisance records agree in every encoded component at every covariate
value](hyp:heq), then [their continuous scores agree at every observation](goal). -/
lemma psiCont_eq_of_contComponent_eq_of_labels_eq (M : LatentIVModel Ω X Z)
    (phi dphi : Z → X → ℝ → ℝ) (L L' : LevelData Z X)
    (hL : recoveryLabels L' = recoveryLabels L)
    (hK : LevelCountPos L.K) (hK' : LevelCountPos L'.K)
    (e : NuisanceCont L) (f : NuisanceCont L')
    (heq : ∀ c x, contComponent M L e c x = contComponent M L' f c x)
    (o : Obs X Z) :
    psiCont M phi dphi L hK o e = psiCont M phi dphi L' hK' o f := by
  rw [← psiCont_relabelContNuisance M phi dphi L L' hL hK hK' f o]
  apply psiCont_eq_of_contComponent_eq
  intro c x
  rw [contComponent_relabelContNuisance]
  exact heq c x

-- @node: fittedContScore_eq_oracle_of_labels_eq
/-- For [continuous-outcome nuisance estimates on the recovered levels](hyp:eHat), if [the population structure has a positive level count](hyp:hK), [the recovered
labels equal the population labels at the given sample size and sample realization](hyp:hLabels),
and [the oracle nuisance components equal the recovered fitted components](hyp:heq),
then [the fitted continuous score equals the oracle score on the population
structure at every observation](goal). -/
lemma fittedContScore_eq_oracle_of_labels_eq
    (M : LatentIVModel Ω X Z) {A : Type*} [MeasurableSpace A]
    {μ : Measure A} [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (pHat : ℕ → A → Z → X → ℝ) (phi dphi : Z → X → ℝ → ℝ)
    (rho : ℕ → ℝ) (gap : ℝ) (L : LevelData Z X) (hK : LevelCountPos L.K)
    (eHat : ∀ n a, NuisanceCont (recoveredData M S I₁ I₂ pHat phi rho gap n a))
    (oracle : ℕ → A → NuisanceCont L) (n : ℕ) (a : A)
    (hLabels : recoveryLabels (recoveredData M S I₁ I₂ pHat phi rho gap n a) =
      recoveryLabels L)
    (heq : ∀ c x, contComponent M L (oracle n a) c x =
      contComponent M _ (eHat n a) c x) (o : Obs X Z) :
    fittedContScore M S I₁ I₂ pHat phi dphi rho gap eHat n a o =
      psiCont M phi dphi L hK o (oracle n a) := by
  have hK' : LevelCountPos (recoveredData M S I₁ I₂ pHat phi rho gap n a).K := by
    rw [show (recoveredData M S I₁ I₂ pHat phi rho gap n a).K = L.K from
      congrArg Prod.fst hLabels]
    exact hK
  simp only [fittedContScore, dif_pos hK']
  exact (psiCont_eq_of_contComponent_eq_of_labels_eq M phi dphi L _ hLabels
    hK hK' (oracle n a) (eHat n a) heq o).symm

-- @node: contDMLRegime_regular_oracle_nuisance_records_of_labels_eq
/-- Assume [the population level count is positive](hyp:hK), [outcome endpoints
are known](hyp:hend), and [the continuous-outcome nuisance estimates on recovered levels](hyp:eHat)
[satisfy the finite
continuous DML regime](hyp:hr). If [the probability of being outside the recovery
events tends to zero](hyp:hG) and [recovered labels equal population labels on
those events along even sample sizes](hyp:hLabels), then [there exists a nuisance
sequence on the population structure whose components are training-measurable,
whose records satisfy clipping, share-simplex, denominator-clipping and admissibility
restrictions, which agrees componentwise with the recovered fits on recovery
events, and whose component L2 errors are of smaller order in probability than
the inverse fourth root of sample size](goal). -/
lemma contDMLRegime_regular_oracle_nuisance_records_of_labels_eq
    (M : LatentIVModel Ω X Z) {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (pHat : ℕ → A → Z → X → ℝ) (phi : Z → X → ℝ → ℝ)
    (rho : ℕ → ℝ) (gap cpi : ℝ) (L : LevelData Z X) (ch : ℝ)
    (hK : LevelCountPos L.K) (hend : OutcomeEndpointsKnown M)
    (eHat : ∀ n a, NuisanceCont (recoveredData M S I₁ I₂ pHat phi rho gap n a))
    (hr : FiniteContDMLRegime M μ S I₁ I₂ pHat phi rho gap cpi L ch eHat)
    (G : ℕ → Set A)
    (hG : Tendsto (fun n => μ (G n)ᶜ) atTop (𝓝 0))
    (hLabels : ∀ n a, a ∈ G n →
      recoveryLabels (recoveredData M S I₁ I₂ pHat phi rho gap (2 * (n + 1)) a) =
        recoveryLabels L) :
    ∃ oracle : ℕ → A → NuisanceCont L,
      (∀ c, TrainingPredictorMeasurable M S I₁
        (fun n a => contComponent M L (oracle n a) c)) ∧
      (∀ n a, ContClipping M L (oracle n a) ∧
        ContFittedSharesSimplex L (oracle n a) ∧
        ContDenominatorsClipped L (oracle n a) cpi) ∧
      (∀ n a, ContAdmissible M L (oracle n a)) ∧
      (∀ n a, a ∈ G n → ∀ c x,
        contComponent M L (oracle (2 * (n + 1)) a) c x =
          contComponent M _ (eHat (2 * (n + 1)) a) c x) ∧
      FiniteNuisanceRates M μ (fun n a => contComponent M L (oracle n a))
        (contComponent M L (trueNuisance M L)) := by
  obtain ⟨n, hn⟩ := (hG.eventually
    (gt_mem_nhds (by norm_num : (0 : ENNReal) < 1))).exists
  have hnG : (G n).Nonempty := by
    by_contra h
    have hz := Set.not_nonempty_iff_eq_empty.mp h
    simp only [hz, Set.compl_empty, measure_univ, lt_self_iff_false] at hn
  obtain ⟨a, ha⟩ := hnG
  have hL := hLabels n a ha
  have hK' : LevelCountPos
      (recoveredData M S I₁ I₂ pHat phi rho gap (2 * (n + 1)) a).K := by
    rw [show (recoveredData M S I₁ I₂ pHat phi rho gap (2 * (n + 1)) a).K = L.K
      from congrArg Prod.fst hL]
    exact hK
  have hfit := hr.1.2.2.1.2.2.2.1 (2 * (n + 1)) a
  have hgeometry := continuous_clipping_simplex_geometry _ cpi hK'
    (eHat (2 * (n + 1)) a) hfit.2.2.1 hfit.2.2.2
  have hgeometry' : cpi ≤ 2 ∧
      ∀ r : RegularIndex L, (L.T r.val.1 r.val.2).Nonempty := by
    have ht := congrArg (fun t => t.2.2.2) hL
    have hk := congrArg Prod.fst hL
    have hl := congrArg (fun t => t.2.1) hL
    dsimp only [recoveryLabels] at ht hk hl
    rcases hgeometry with ⟨hc, hn⟩
    refine ⟨hc, ?_⟩
    intro r
    have hr' : r.val.1 ≤ (recoveredData M S I₁ I₂ pHat phi rho gap
        (2 * (n + 1)) a).K ∧ 1 ≤ r.val.2 ∧ r.val.2 ≤
        (recoveredData M S I₁ I₂ pHat phi rho gap (2 * (n + 1)) a).l r.val.1 := by
      rw [hk, hl]
      exact r.property
    simpa only [ht] using hn ⟨r.val, hr'⟩
  obtain ⟨hcpi, hne⟩ := hgeometry'
  obtain ⟨F, hm, hb, heq, hrate⟩ := contDMLRegime_oracle_component_predictors
    M μ S I₁ I₂ pHat phi rho gap cpi L ch eHat hr G hG hLabels
  let raw := fun n a => repairContNuisance M L cpi hne (decodeContComponents L (F n a))
  let oracle := fun n a => normalizeContAuxiliaryFits L (raw n a)
  have hreg (n : ℕ) (a : A) : ContClipping M L (oracle n a) ∧
      ContFittedSharesSimplex L (oracle n a) ∧
      ContDenominatorsClipped L (oracle n a) cpi := by
    have h := repairContNuisance_regular M L cpi hcpi (hend.1.2 hend.2.1)
      hne (decodeContComponents L (F n a))
    exact normalizeContAuxiliaryFits_regular M L _ cpi h.1 h.2.1 h.2.2
  have hmeas (c) : TrainingPredictorMeasurable M S I₁
      (fun n a => contComponent M L (oracle n a) c) := by
    intro n
    let : MeasurableSpace A :=
      MeasurableSpace.comap (trainingView M S I₁ n) inferInstance
    have hh := repairContNuisance_decoded_measurable M L cpi hne (F n)
      (fun c => hm c n) c
    change Measurable (fun ax : A × X => contComponent M L (oracle n ax.1) c ax.2)
    simpa only [oracle, raw, contComponent_normalizeContAuxiliaryFits] using hh
  have heq' : ∀ n a, a ∈ G n → ∀ c x,
      contComponent M L (oracle (2 * (n + 1)) a) c x =
        contComponent M _ (eHat (2 * (n + 1)) a) c x := by
    intro n a ha c x
    have hf := hr.1.2.2.1.2.2.2.1 (2 * (n + 1)) a
    simp only [oracle, contComponent_normalizeContAuxiliaryFits, raw]
    exact repairContNuisance_component_eq_of_labels_eq M L _ (hLabels n a ha)
      cpi hne _ _ (heq n a ha) hf.1 hf.2.2.2 hf.2.2.1 c x
  have hadm (n : ℕ) (a : A) : ContAdmissible M L (oracle n a) := by
    have hmsection (c) : Measurable (contComponent M L (raw n a) c) := by
      let : MeasurableSpace A :=
        MeasurableSpace.comap (trainingView M S I₁ n) inferInstance
      have hh := repairContNuisance_decoded_measurable M L cpi hne (F n)
        (fun c => hm c n) c
      exact hh.comp (measurable_const.prodMk measurable_id)
    have h := repairContNuisance_regular M L cpi hcpi (hend.1.2 hend.2.1)
      hne (decodeContComponents L (F n a))
    exact restrictContShares_admissible_of_encoded_clipping M L (raw n a)
      h.1 h.2.1 hmsection
  refine ⟨oracle, hmeas, hreg, hadm, heq', ?_⟩
  exact nuisanceRates_transfer_on_recovery M μ
      (fun n a => contComponent M _ (eHat n a))
      (fun n a => contComponent M L (oracle n a))
      (contComponent M L (trueNuisance M L)) G hG heq' hr.2.1

-- @node: contDMLRegime_oracle_score_convergence_on_recovery_of_labels_eq
/-- Suppose [the policy is a valid policy map](hyp:hphi), [its derivative is the
given derivative function](hyp:hd), [that derivative is bounded and Lipschitz](hyp:hDerivative),
[the structural assumptions hold](hyp:hStruct), [outcome endpoints are known](hyp:hend),
[the population level count is positive](hyp:hK), [level ordering is invariant](hyp:hOrder),
[the true nuisance is admissible](hyp:he0), and [baseline](hyp:hov) and [policy](hyp:hpol)
overlap hold. For [continuous-outcome nuisance estimates on the recovered levels](hyp:eHat), under [the finite continuous DML regime](hyp:hr), [recovery events
whose complements have vanishing probability](hyp:hG), and [equality of recovered
and population labels on those events](hyp:hLabels), [there exists an admissible,
clipped population-structure nuisance sequence with simplex shares and clipped
denominators, training-measurable score errors, integrated squared score errors
converging in probability to zero, and scores equal to the recovered fitted scores
on the recovery events along even sample sizes](goal). -/
lemma contDMLRegime_oracle_score_convergence_on_recovery_of_labels_eq
    (M : LatentIVModel Ω X Z) {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] (S : ObservedSample M μ)
    (I₁ I₂ : SampleSplit A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (hStruct : StructuralAssumptions M) (hend : OutcomeEndpointsKnown M)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (hpol : PolicyOverlap M L cpi)
    (pHat : ℕ → A → Z → X → ℝ) (rho : ℕ → ℝ) (gap ch : ℝ)
    (eHat : ∀ n a, NuisanceCont (recoveredData M S I₁ I₂ pHat phi rho gap n a))
    (hr : FiniteContDMLRegime M μ S I₁ I₂ pHat phi rho gap cpi L ch eHat)
    (G : ℕ → Set A) (hG : Tendsto (fun n => μ (G n)ᶜ) atTop (𝓝 0))
    (hLabels : ∀ n a, a ∈ G n →
      recoveryLabels (recoveredData M S I₁ I₂ pHat phi rho gap (2 * (n + 1)) a) =
        recoveryLabels L) :
    ∃ oracle : ℕ → A → NuisanceCont L,
      (∀ n a, ContClipping M L (oracle n a) ∧
        ContFittedSharesSimplex L (oracle n a) ∧
        ContDenominatorsClipped L (oracle n a) cpi) ∧
      (∀ n a, ContAdmissible M L (oracle n a)) ∧
      TrainingPredictorMeasurable M S I₁ (fun n a o =>
        psiCont M phi dphi L hK o (oracle n a) -
          psiCont M phi dphi L hK o (trueNuisance M L)) ∧
      Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
        (fun n a => ∫ o,
          (psiCont M phi dphi L hK o (oracle (2 * (n + 1)) a) -
            psiCont M phi dphi L hK o (trueNuisance M L)) ^ 2 ∂observationLaw M)
        atTop (fun _ _ => 0) ∧
      (∀ n a, a ∈ G n → ∀ o,
        fittedContScore M S I₁ I₂ pHat phi dphi rho gap eHat (2 * (n + 1)) a o =
          psiCont M phi dphi L hK o (oracle (2 * (n + 1)) a)) := by
  cases Subsingleton.elim ‹DecidableEq Z› (fun a b => Classical.propDecidable (a = b))
  obtain ⟨oracle, hm, hc, ha, heq, hrate⟩ :=
    contDMLRegime_regular_oracle_nuisance_records_of_labels_eq M μ S I₁ I₂ pHat phi
      rho gap cpi L ch hK hend eHat hr G hG hLabels
  have hscore := training_measurable_continuous_score_of_components M S I₁
    phi dphi hphi hd L hK oracle hm (fun n a => (hc n a).1.1)
  have hdiff := training_measurable_continuous_score_difference M S I₁
    phi dphi hphi hd L hK he0 _ hscore
  have hsection (n : ℕ) (a : A) (c) :
      Measurable (contComponent M L (oracle n a) c) := by
    let : MeasurableSpace A :=
      MeasurableSpace.comap (trainingView M S I₁ n) inferInstance
    exact (hm c n).comp (measurable_const.prodMk measurable_id)
  have hconv := encoded_continuous_total_score_sq_tendsto_probability_zero
    M μ hStruct.2.2.2.1 phi dphi hphi hd hDerivative L hK hOrder
    hStruct.1 hStruct.2.1 hend he0 oracle (fun n a => (hc n a).1)
    (fun n a => (hc n a).2.1) hsection hrate hr.2.2.1 cpi hov hpol
    (fun n a => (hc n a).2.2)
  refine ⟨oracle, hc, ha, hdiff, hconv, ?_⟩
  intro n a hna o
  exact fittedContScore_eq_oracle_of_labels_eq M S I₁ I₂ pHat phi dphi
    rho gap L hK eHat oracle _ a (hLabels n a hna) (heq n a hna) o

-- @node: contDMLRegime_mean_variance_consistent_on_recovery_of_labels_eq
/-- Under [an equal half-sample split](hyp:hSplit), [a valid policy map](hyp:hphi),
[the specified policy derivative](hyp:hd), [a bounded Lipschitz derivative](hyp:hDerivative),
[the structural assumptions](hyp:hStruct), [known outcome endpoints](hyp:hend),
[a positive population level count](hyp:hK), [invariant level ordering](hyp:hOrder),
[measurable baseline levels](hyp:hlev), [measurable band boundaries](hyp:hb),
[baseline overlap](hyp:hov), and [policy overlap](hyp:hpol), assume [the finite
continuous DML regime](hyp:hr) for [continuous-outcome nuisance estimates on the recovered levels](hyp:eHat), [recovery events with vanishing complement
probabilities](hyp:hG), and [correct recovered labels on those events](hyp:hLabels).
Then [the fitted score mean converges in probability to the discrete lower target,
and its empirical variance converges to the population variance of the true score
centered at that target, along even sample sizes](goal). -/
lemma contDMLRegime_mean_variance_consistent_on_recovery_of_labels_eq
    (M : LatentIVModel Ω X Z) {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] (S : ObservedSample M μ)
    (I₁ I₂ : SampleSplit A) (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (hStruct : StructuralAssumptions M) (hend : OutcomeEndpointsKnown M)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (hlev : ∀ k, Measurable (L.pLev k))
    (hb : ∀ k < L.K, ∀ j ≤ L.l k, Measurable (bandBoundary M L k j))
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (pHat : ℕ → A → Z → X → ℝ) (rho : ℕ → ℝ) (gap ch : ℝ)
    (eHat : ∀ n a, NuisanceCont (recoveredData M S I₁ I₂ pHat phi rho gap n a))
    (hr : FiniteContDMLRegime M μ S I₁ I₂ pHat phi rho gap cpi L ch eHat)
    (G : ℕ → Set A) (hG : Tendsto (fun n => μ (G n)ᶜ) atTop (𝓝 0))
    (hLabels : ∀ n a, a ∈ G n →
      recoveryLabels (recoveredData M S I₁ I₂ pHat phi rho gap (2 * (n + 1)) a) =
        recoveryLabels L) :
    let score := fittedContScore M S I₁ I₂ pHat phi dphi rho gap eHat
    let truth := fun o => psiCont M phi dphi L hK o (trueNuisance M L)
    let theta := discreteTarget M false L (policyProp phi M.prop)
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => dmlRV M S I₂ score (2 * (n + 1)) a - theta)
      atTop (fun _ _ => 0) ∧
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => varianceRV M S I₂ score (2 * (n + 1)) a)
      atTop (fun _ _ => populationVariance M truth theta) := by
  cases Subsingleton.elim ‹DecidableEq Z› (fun a b => Classical.propDecidable (a = b))
  have hq := population_policyProp_measurable M hStruct.2.2.2.1 phi hphi
  have he0 := population_continuous_nuisance_admissible M hStruct hend
    (policyProp phi M.prop) hq L hOrder hlev cpi hov hpol
  obtain ⟨oracle, hc, ha, hm, hrate, heq⟩ :=
    contDMLRegime_oracle_score_convergence_on_recovery_of_labels_eq M μ S I₁ I₂ phi dphi hphi hd
      hDerivative hStruct hend L hK hOrder he0 cpi hov hpol pHat rho gap ch eHat hr G hG hLabels
  have hpos : 0 < cpi / 2 := by linarith [hov.1]
  have hp0 (i : PositiveIndex L.K) :
      ∀ᵐ x ∂xLaw M, cpi / 2 ≤ (trueNuisance M L).piLev i x := by
    apply Eventually.of_forall
    intro x
    have hx := hov.2 x i.val i.property.1 i.property.2
    change cpi / 2 ≤ (levelSetProb M L).1 i.val x
    linarith [hov.1]
  have ht0 (r : RegularIndex L) :
      ∀ᵐ x ∂xLaw M, cpi / 2 ≤ (trueNuisance M L).tauLev r x := by
    have hne := continuous_admissible_policy_nonempty M L _ he0 r
    apply Eventually.of_forall
    intro x
    have hx : cpi ≤ (trueNuisance M L).tauLev r x :=
      hpol.2 x r.val.1 r.val.2 r.property.1 r.property.2.1 r.property.2.2 hne
    linarith [hpol.1]
  have hpf n a (i : PositiveIndex L.K) :
      ∀ᵐ x ∂xLaw M, cpi / 2 ≤ (oracle n a).piLev i x :=
    Eventually.of_forall (fun x => (hc n a).2.2.1 i x |>.1)
  have htf n a (r : RegularIndex L) :
      ∀ᵐ x ∂xLaw M, cpi / 2 ≤ (oracle n a).tauLev r x :=
    Eventually.of_forall (fun x => ((hc n a).2.2.2 r x
      (contFittedSharesSimplex_policy_nonempty L _ (hc n a).2.1 r)).1)
  obtain ⟨C, hbound⟩ := fitted_continuous_total_score_uniform_bound M phi dphi hphi
    hDerivative L hK hStruct.1 hStruct.2.1 hend (cpi / 2) hpos
  have hdiff n a : ∀ᵐ o ∂observationLaw M,
      |psiCont M phi dphi L hK o (oracle n a) -
        psiCont M phi dphi L hK o (trueNuisance M L)| ≤ C + C := by
    filter_upwards [hbound _ (ha n a) (hpf n a) (htf n a),
      hbound _ he0 hp0 ht0] with o hf ht
    exact (abs_sub _ _).trans (add_le_add hf ht)
  have hdphi := policy_derivative_graph_measurable phi dphi hphi hd M.prop
    hStruct.2.2.2.1.2.1 M.rangeProp
  have hmean := (population_continuous_score_mean_eq_target M hStruct hend phi dphi
    hphi hdphi hDerivative L hK hOrder hlev cpi hov hpol hb hr.2.2.1 hr.2.2.2).2
  have hLp := true_continuous_total_score_memLp_of_overlap M phi dphi hphi hd hDerivative
    L hK he0 hStruct.1 hStruct.2.1 hend cpi hov hpol
  dsimp only
  exact equalHalfSplit_ae_bounded_training_feasible_mean_variance_consistent M μ S I₁ I₂
    hSplit (fun n a o => psiCont M phi dphi L hK o (oracle n a)) _ _ hmean hLp hm
    (C+C) hdiff hrate _ G hG (fun n a hna i hi => heq n a hna (S.Z i a))

-- @node: contDMLRegime_lower_bound_variance_consistent_on_recovery_of_labels_eq
/-- Assume [an equal half-sample split](hyp:hSplit), [a valid policy map](hyp:hphi),
[the specified policy derivative](hyp:hd), [a bounded Lipschitz derivative](hyp:hDerivative),
[the structural assumptions](hyp:hStruct), [known outcome endpoints](hyp:hend),
[separated propensity gaps](hyp:hGap), [finite-instrument reduction](hyp:hFinite),
[a positive level count at the reference covariate](hyp:hK), [invariant level
ordering](hyp:hOrder), [baseline overlap](hyp:hov), and [policy overlap](hyp:hpol).
With [continuous-outcome nuisance estimates on the recovered levels](hyp:eHat), [the finite continuous DML regime](hyp:hr), [recovery events whose complements
have vanishing probability](hyp:hG), and [correct recovered labels on those
events](hyp:hLabels), [the fitted score's empirical variance converges in probability,
along even sample sizes, to the true score's population variance centered at the
transport lower bound](goal). -/
lemma contDMLRegime_lower_bound_variance_consistent_on_recovery_of_labels_eq
    (M : LatentIVModel Ω X Z) {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] (S : ObservedSample M μ)
    (I₁ I₂ : SampleSplit A) (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (hStruct : StructuralAssumptions M) (hend : OutcomeEndpointsKnown M)
    (x0 : X) (hGap : PropensityGapSeparation M.prop (policyProp phi M.prop))
    (hFinite : InstrumentFiniteReduction Z)
    (hK : LevelCountPos (LevelStructure M.prop (policyProp phi M.prop) x0).K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop)
      (LevelStructure M.prop (policyProp phi M.prop) x0))
    (cpi : ℝ)
    (hov : BaselineOverlapWitness M (LevelStructure M.prop (policyProp phi M.prop) x0) cpi)
    (hpol : PolicyOverlap M (LevelStructure M.prop (policyProp phi M.prop) x0) cpi)
    (pHat : ℕ → A → Z → X → ℝ) (rho : ℕ → ℝ) (gap ch : ℝ)
    (eHat : ∀ n a, NuisanceCont (recoveredData M S I₁ I₂ pHat phi rho gap n a))
    (hr : FiniteContDMLRegime M μ S I₁ I₂ pHat phi rho gap cpi
      (LevelStructure M.prop (policyProp phi M.prop) x0) ch eHat)
    (G : ℕ → Set A) (hG : Tendsto (fun n => μ (G n)ᶜ) atTop (𝓝 0))
    (hLabels : ∀ n a, a ∈ G n → recoveryLabels (recoveredData M S I₁ I₂ pHat phi rho gap
      (2 * (n + 1)) a) = recoveryLabels (LevelStructure M.prop (policyProp phi M.prop) x0)) :
    let L := LevelStructure M.prop (policyProp phi M.prop) x0
    let score := fittedContScore M S I₁ I₂ pHat phi dphi rho gap eHat
    let truth := fun o => psiCont M phi dphi L hK o (trueNuisance M L)
    let theta := thetaLower1 (transportData M) (policyWeight M (policyProp phi M.prop))
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => varianceRV M S I₂ score (2 * (n + 1)) a)
      atTop (fun _ _ => populationVariance M truth theta) := by
  cases Subsingleton.elim ‹DecidableEq Z› (fun a b => Classical.propDecidable (a = b))
  have hlev := population_LevelStructure_baseline_measurable M hStruct.2.2.2.1
    (policyProp phi M.prop) x0 hOrder
  have hq := population_policyProp_measurable M hStruct.2.2.2.1 phi hphi
  have hb := population_bandBoundary_measurable M (policyProp phi M.prop) hq
    _ hOrder hlev
  have htarget := (discrete_reduction M hStruct.2.2.2.2.2.2 hend hStruct.1
    hStruct.2.1 hStruct.2.2.1 hStruct.2.2.2.1 hStruct.2.2.2.2.1
    hStruct.2.2.2.2.2.1 phi hphi x0 hGap hOrder hFinite).2.2.1
  dsimp only
  rw [htarget]
  exact (contDMLRegime_mean_variance_consistent_on_recovery_of_labels_eq M μ S I₁ I₂ hSplit
    phi dphi hphi hd hDerivative hStruct hend _ hK hOrder hlev
    (fun k hk j hj => hb k j hk hj) cpi hov hpol pHat rho gap ch eHat hr
    G hG hLabels).2

end Papers.TbsPrteOptimalTransport

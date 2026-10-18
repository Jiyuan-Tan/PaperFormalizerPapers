module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLReconstructedRegularity
public import Causalean.Mathlib.Analysis.ClipInterval
/-! Clipped continuous oracle nuisances reconstructed from training predictors.
The repair is the identity on recovered feasible coordinates and restores the
simplex, bounded outcome ranges and positive denominators elsewhere. -/
@[expose] public section
set_option linter.style.openClassical false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Set Filter
open Causalean.Mathlib.Analysis
open scoped Classical Topology
universe u v
variable {Ω : Type u} {X Z : Type v}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]
  [Fintype Z] [DecidableEq Z]

-- @node: repairContShares
/-- On [the instrument space](hyp:Z) and [covariate space](hyp:X), for [level data](hyp:L)
with [a nonempty policy set at every regular index](hyp:hne),
[candidate nuisances](hyp:e), [a regular index](hyp:a), [an instrument value](hyp:z), and
[covariates](hyp:x), the [repaired policy share](goal) is the clipped share on the policy
set and zero outside it when the clipped shares sum to one; otherwise it puts all mass
on a chosen member of the policy set. -/
noncomputable def repairContShares (L : LevelData Z X)
    (hne : ∀ a : RegularIndex L, (L.T a.val.1 a.val.2).Nonempty)
    (e : NuisanceCont L) (a : RegularIndex L) (z : Z) (x : X) : ℝ :=
  if (∑ w ∈ L.T a.val.1 a.val.2, clipIcc 0 1 (e.share a w x)) = 1 then
    if z ∈ L.T a.val.1 a.val.2 then clipIcc 0 1 (e.share a z x) else 0
  else if z = Classical.choose (hne a) then 1 else 0

-- @node: repairContShares_regular
/-- If [every regular policy set is nonempty](hyp:hne), [the repaired shares lie between
zero and one, sum to one on the policy set, and vanish outside it](goal). -/
lemma repairContShares_regular (L : LevelData Z X)
    (hne : ∀ a : RegularIndex L, (L.T a.val.1 a.val.2).Nonempty)
    (e : NuisanceCont L) (a : RegularIndex L) (x : X) :
    (∀ z, repairContShares L hne e a z x ∈ Icc (0 : ℝ) 1) ∧
    (∑ z ∈ L.T a.val.1 a.val.2, repairContShares L hne e a z x) = 1 ∧
    (∀ z, z ∉ L.T a.val.1 a.val.2 → repairContShares L hne e a z x = 0) := by
  have hz := Classical.choose_spec (hne a)
  unfold repairContShares
  split_ifs with hs
  · refine ⟨?_, ?_, ?_⟩
    · intro z
      split_ifs
      · exact clipIcc_mem_Icc zero_le_one _
      · exact ⟨le_rfl, zero_le_one⟩
    · simpa only [Finset.sum_ite_mem, Finset.inter_self] using hs
    · intro z hnot
      simp only [if_neg hnot]
  · refine ⟨?_, ?_, ?_⟩
    · intro z
      split_ifs <;> norm_num
    · simp [hz]
    · intro z hnot
      have hne' : z ≠ Classical.choose (hne a) := fun heq => hnot (heq ▸ hz)
      simp only [if_neg hne']

-- @node: repairContShares_eq_of_regular
/-- If [every regular policy set is nonempty](hyp:hne), [the nuisances satisfy the clipping
bounds](hyp:hc), and [the fitted shares form a simplex](hyp:hs), [repairing a share equals
restricting the original share to the policy set](goal). -/
lemma repairContShares_eq_of_regular (M : LatentIVModel Ω X Z) (L : LevelData Z X)
    (hne : ∀ a : RegularIndex L, (L.T a.val.1 a.val.2).Nonempty)
    (e : NuisanceCont L) (hc : ContClipping M L e) (hs : ContFittedSharesSimplex L e)
    (a : RegularIndex L) (z : Z) (x : X) :
    repairContShares L hne e a z x = (restrictContShares L e).share a z x := by
  have hsum : (∑ w ∈ L.T a.val.1 a.val.2, clipIcc 0 1 (e.share a w x)) = 1 := by
    simpa only [clipIcc_eq_self (hc.2.2.2.1 a _ x)] using (hs a x).2
  simp only [repairContShares, if_pos hsum, restrictContShares,
    clipIcc_eq_self (hc.2.2.2.1 a z x)]

-- @node: repairContNuisance
/-- On [the population space](hyp:Ω), [covariate space](hyp:X), and [instrument space](hyp:Z),
for [a latent instrumental-variable model](hyp:M), [level data](hyp:L),
[a denominator threshold](hyp:cpi), [nonempty regular policy sets](hyp:hne), and
[candidate nuisances](hyp:e), the [repaired continuous nuisance record](goal) clips
probabilities to the unit interval, denominators to the interval from the larger of zero
and half the threshold to one, and outcome moments to their respective outcome bounds;
it repairs the policy shares and sets both higher-level auxiliary fits to zero. -/
noncomputable def repairContNuisance (M : LatentIVModel Ω X Z)
    (L : LevelData Z X) (cpi : ℝ)
    (hne : ∀ a : RegularIndex L, (L.T a.val.1 a.val.2).Nonempty)
    (e : NuisanceCont L) : NuisanceCont L :=
  { prop := fun z x => clipIcc 0 1 (e.prop z x)
    pLev := fun k x => clipIcc 0 1 (e.pLev k x)
    piLev := fun k x => clipIcc (max 0 (cpi / 2)) 1 (e.piLev k x)
    tauLev := fun a x => clipIcc (max 0 (cpi / 2)) 1 (e.tauLev a x)
    gammaFull := fun k x => clipIcc (-1) 1 (e.gammaFull k x)
    gamma := fun a x => clipIcc 0 1 (e.gamma a x)
    nu := fun a x => clipIcc M.yMin M.yMax (e.nu a x)
    Mplus := fun a x => clipIcc 0 1 (e.Mplus a x)
    Mminus := fun a x => clipIcc 0 1 (e.Mminus a x)
    Jplus := fun a x => clipIcc (min 0 M.yMin) (max 0 M.yMax) (e.Jplus a x)
    Jminus := fun a x => clipIcc (min 0 M.yMin) (max 0 M.yMax) (e.Jminus a x)
    JfullPlus := fun k x => clipIcc M.yMin M.yMax (e.JfullPlus k x)
    JfullMinus := fun k x => clipIcc M.yMin M.yMax (e.JfullMinus k x)
    share := repairContShares L hne e
    higherPolicyFit := fun _ _ => 0
    higherBaselineFit := fun _ _ => 0
    gammaTail := fun x => clipIcc 0 1 (e.gammaTail x) }

-- @node: repairContNuisance_regular
/-- If [the denominator threshold is at most two](hyp:hcpi), [the outcome endpoints are
ordered](hyp:hy), and [every regular policy set is nonempty](hyp:hne), [the repaired
nuisances satisfy the clipping bounds, the fitted-share simplex restrictions, and the
denominator clipping restrictions](goal). -/
lemma repairContNuisance_regular (M : LatentIVModel Ω X Z)
    (L : LevelData Z X) (cpi : ℝ) (hcpi : cpi ≤ 2) (hy : M.yMin ≤ M.yMax)
    (hne : ∀ a : RegularIndex L, (L.T a.val.1 a.val.2).Nonempty)
    (e : NuisanceCont L) :
    ContClipping M L (repairContNuisance M L cpi hne e) ∧
    ContFittedSharesSimplex L (repairContNuisance M L cpi hne e) ∧
    ContDenominatorsClipped L (repairContNuisance M L cpi hne e) cpi := by
  have hden : max 0 (cpi / 2) ≤ (1 : ℝ) := max_le zero_le_one (by linarith)
  have hd (r : ℝ) := clipIcc_mem_Icc hden r
  have hu (r : ℝ) := clipIcc_mem_Icc zero_le_one r
  have hd0 (r : ℝ) : clipIcc (max 0 (cpi / 2)) 1 r ∈ Icc (0 : ℝ) 1 :=
    ⟨(le_max_left _ _).trans (hd r).1, (hd r).2⟩
  have hdc (r : ℝ) : clipIcc (max 0 (cpi / 2)) 1 r ∈ Icc (cpi / 2) 1 :=
    ⟨(le_max_right _ _).trans (hd r).1, (hd r).2⟩
  have hband : min 0 M.yMin ≤ max 0 M.yMax :=
    (min_le_left _ _).trans (le_max_left _ _)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact fun z x => hu _
  · exact fun k x => ⟨hu _, hd0 _⟩
  · exact fun a x => ⟨hd0 _, hu _⟩
  · exact fun a z x => (repairContShares_regular L hne e a x).1 z
  · exact fun k x => clipIcc_mem_Icc (by norm_num) _
  · exact fun x => hu _
  · exact fun a x => clipIcc_mem_Icc hy _
  · exact fun a x => hu _
  · exact fun a x => hu _
  · exact fun a x => clipIcc_mem_Icc hband _
  · exact fun a x => clipIcc_mem_Icc hband _
  · exact fun k x => clipIcc_mem_Icc hy _
  · exact fun k x => clipIcc_mem_Icc hy _
  · exact fun k x => ⟨⟨le_rfl, zero_le_one⟩, ⟨le_rfl, zero_le_one⟩⟩
  · exact fun a x => ⟨fun z => ((repairContShares_regular L hne e a x).1 z).1,
      (repairContShares_regular L hne e a x).2.1⟩
  · exact ⟨fun k x => hdc _, fun a x _ => hdc _⟩

-- @node: repairContNuisance_eq_of_regular
/-- If [regular policy sets are nonempty](hyp:hne) and [the original nuisances satisfy
the clipping bounds](hyp:hc), [the share simplex restrictions](hyp:hs), and
[the denominator clipping restrictions](hyp:hd), [repairing them equals normalizing
their auxiliary fits](goal). -/
lemma repairContNuisance_eq_of_regular (M : LatentIVModel Ω X Z)
    (L : LevelData Z X) (cpi : ℝ)
    (hne : ∀ a : RegularIndex L, (L.T a.val.1 a.val.2).Nonempty)
    (e : NuisanceCont L) (hc : ContClipping M L e)
    (hs : ContFittedSharesSimplex L e) (hd : ContDenominatorsClipped L e cpi) :
    repairContNuisance M L cpi hne e = normalizeContAuxiliaryFits L e := by
  obtain ⟨hp, hl, hr, ha, hf, ht, hn, hmp, hmm, hjp, hjm, hjfp, hjfm, hprob⟩ := hc
  have hpi (k) (x) : e.piLev k x ∈ Icc (max 0 (cpi / 2)) 1 :=
    ⟨max_le (hl k x).2.1 (hd.1 k x).1, (hd.1 k x).2⟩
  have htau (a) (x) : e.tauLev a x ∈ Icc (max 0 (cpi / 2)) 1 :=
    ⟨max_le (hr a x).1.1 (hd.2 a x (hne a)).1, (hd.2 a x (hne a)).2⟩
  cases e
  unfold repairContNuisance normalizeContAuxiliaryFits restrictContShares
  congr 1
  all_goals first
    | exact funext fun a => funext fun z => funext fun x =>
        repairContShares_eq_of_regular M L hne _
          ⟨hp, hl, hr, ha, hf, ht, hn, hmp, hmm, hjp, hjm, hjfp, hjfm, hprob⟩ hs a z x
    | (funext z x; exact clipIcc_eq_self (hp z x))
    | (funext k x; exact clipIcc_eq_self ((hl k x).1))
    | (funext k x; exact clipIcc_eq_self (hpi k x))
    | (funext a x; exact clipIcc_eq_self (htau a x))
    | (funext k x; exact clipIcc_eq_self (hf k x))
    | (funext a x; exact clipIcc_eq_self ((hr a x).2))
    | (funext a x; exact clipIcc_eq_self (hn a x))
    | (funext a x; exact clipIcc_eq_self (hmp a x))
    | (funext a x; exact clipIcc_eq_self (hmm a x))
    | (funext a x; exact clipIcc_eq_self (hjp a x))
    | (funext a x; exact clipIcc_eq_self (hjm a x))
    | (funext k x; exact clipIcc_eq_self (hjfp k x))
    | (funext k x; exact clipIcc_eq_self (hjfm k x))
    | (funext x; exact clipIcc_eq_self (ht x))

-- @node: repairContShares_measurable
/-- If [every regular policy set is nonempty](hyp:hne) and [each original share is jointly
measurable in the nuisance index and covariates](hyp:hm), [each repaired share is jointly
measurable in those variables](goal). -/
@[fun_prop] lemma repairContShares_measurable {B : Type*} [MeasurableSpace B]
    (L : LevelData Z X)
    (hne : ∀ a : RegularIndex L, (L.T a.val.1 a.val.2).Nonempty)
    (e : B → NuisanceCont L)
    (hm : ∀ a z, Measurable (fun bx : B × X => (e bx.1).share a z bx.2))
    (a : RegularIndex L) (z : Z) :
    Measurable (fun bx : B × X => repairContShares L hne (e bx.1) a z bx.2) := by
  try fun_prop
  have hsum : Measurable (fun bx : B × X =>
      ∑ w ∈ L.T a.val.1 a.val.2, clipIcc 0 1 ((e bx.1).share a w bx.2)) := by
    fun_prop
  have hset : MeasurableSet {bx : B × X |
      (∑ w ∈ L.T a.val.1 a.val.2, clipIcc 0 1 ((e bx.1).share a w bx.2)) = 1} :=
    measurableSet_eq_fun hsum measurable_const
  unfold repairContShares
  apply Measurable.ite hset
  · split_ifs <;> fun_prop
  · split_ifs <;> fun_prop

-- @node: repairContNuisance_decoded_measurable
/-- If [regular policy sets are nonempty](hyp:hne) and [each encoded predictor is jointly
measurable in its index and covariates](hyp:hm), [each component obtained by decoding and
repairing these predictors is jointly measurable in the same variables](goal). -/
@[fun_prop] lemma repairContNuisance_decoded_measurable
    (M : LatentIVModel Ω X Z) {B : Type*} [MeasurableSpace B]
    (L : LevelData Z X) (cpi : ℝ)
    (hne : ∀ a : RegularIndex L, (L.T a.val.1 a.val.2).Nonempty)
    (F : B → (ℕ × ℕ × ℕ × Z) → X → ℝ)
    (hm : ∀ c, Measurable (fun bx : B × X => F bx.1 c bx.2))
    (c : ℕ × ℕ × ℕ × Z) :
    Measurable (fun bx : B × X => contComponent M L
      (repairContNuisance M L cpi hne (decodeContComponents L (F bx.1))) c bx.2) := by
  try fun_prop
  have hs (a : RegularIndex L) (z : Z) : Measurable (fun bx : B × X =>
      repairContShares L hne (decodeContComponents L (F bx.1)) a z bx.2) := by
    refine repairContShares_measurable L hne (fun b => decodeContComponents L (F b)) ?_ a z
    intro a z
    change Measurable (fun bx : B × X => F bx.1
      (4, a.val.1, a.val.2, z) bx.2)
    exact hm _
  rcases c with ⟨code, k, j, z⟩
  unfold contComponent repairContNuisance
  dsimp only
  split <;> try dsimp only
  all_goals try simp only [positiveValue, regularValue, shareValue, fullValue,
    nuValue, boundaryValue, minusBoundaryValue, meanValue, minusMeanValue, minusFullValue]
  all_goals simp only [decodeContComponents]
  all_goals repeat' first | fun_prop | split

-- @node: repairContNuisance_component_eq_on_recovery
/-- If [the recovered and target level data coincide](hyp:hL), [target regular policy
sets are nonempty](hyp:hne), [the predictors reproduce every original nuisance
component](hyp:heq), and the original nuisances satisfy [clipping](hyp:hc),
[share simplex restrictions](hyp:hs), and [denominator clipping](hyp:hd), [decoding and
repairing the predictors preserves every original component at every covariate value](goal). -/
lemma repairContNuisance_component_eq_on_recovery
    (M : LatentIVModel Ω X Z) (L L' : LevelData Z X) (hL : L' = L) (cpi : ℝ)
    (hne : ∀ a : RegularIndex L, (L.T a.val.1 a.val.2).Nonempty)
    (F : (ℕ × ℕ × ℕ × Z) → X → ℝ) (e : NuisanceCont L')
    (heq : ∀ c x, F c x = contComponent M L' e c x)
    (hc : ContClipping M L' e) (hs : ContFittedSharesSimplex L' e)
    (hd : ContDenominatorsClipped L' e cpi) (c : ℕ × ℕ × ℕ × Z) (x : X) :
    contComponent M L (repairContNuisance M L cpi hne (decodeContComponents L F)) c x =
      contComponent M L' e c x := by
  subst L'
  have hF : F = contComponent M L e := funext fun c => funext (heq c)
  rw [hF, decodeContComponents_contComponent]
  have hr := normalizeContAuxiliaryFits_regular M L e cpi hc hs hd
  rw [repairContNuisance_eq_of_regular M L cpi hne _ hr.1 hr.2.1 hr.2.2,
    contComponent_normalizeContAuxiliaryFits, contComponent_normalizeContAuxiliaryFits]


-- @node: continuous_clipping_simplex_geometry
/-- If [there is at least one positive level](hyp:hK), [nuisance denominators satisfy
the clipping restrictions](hyp:hd), and [fitted shares form a simplex](hyp:hs),
[the denominator threshold is at most two and every regular policy set is nonempty](goal). -/
lemma continuous_clipping_simplex_geometry (L : LevelData Z X) (cpi : ℝ)
    (hK : LevelCountPos L.K) (e : NuisanceCont L)
    (hd : ContDenominatorsClipped L e cpi) (hs : ContFittedSharesSimplex L e) :
    cpi ≤ 2 ∧ ∀ a : RegularIndex L, (L.T a.val.1 a.val.2).Nonempty := by
  let x : X := Classical.choice inferInstance
  have hh := hd.1 ⟨1, ⟨le_rfl, hK⟩⟩ x
  refine ⟨by linarith [hh.1, hh.2], ?_⟩
  intro a
  by_contra h
  have hz := Finset.not_nonempty_iff_eq_empty.mp h
  have hh := (hs a x).2
  simp only [hz, Finset.sum_empty] at hh
  exact zero_ne_one hh

-- @node: contDMLRegime_regular_oracle_nuisance_records
/-- Assume [there is a positive level](hyp:hK), [the outcome endpoints are known](hyp:hend),
and [the fitted nuisance records](hyp:eHat) [satisfy the finite continuous DML regime](hyp:hr).
If [the complements of the recovery events have probability tending to zero](hyp:hG)
and [the recovered level data equal the target data on those events at sample sizes twice
one plus the index](hyp:hLevels), [there exist oracle nuisance records whose components
are measurable from the training sample, which satisfy clipping, share simplex and
denominator restrictions everywhere, are admissible everywhere, agree with the fitted
components on recovery events, and have componentwise L² errors toward truth that are
smaller in probability than the inverse fourth root of sample size](goal). -/
lemma contDMLRegime_regular_oracle_nuisance_records
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
    (hLevels : ∀ n a, a ∈ G n →
      recoveredData M S I₁ I₂ pHat phi rho gap (2 * (n + 1)) a = L) :
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
  have hL := hLevels n a ha
  have hK' : LevelCountPos
      (recoveredData M S I₁ I₂ pHat phi rho gap (2 * (n + 1)) a).K := by
    rw [hL]
    exact hK
  have hfit := hr.1.2.2.1.2.2.2.1 (2 * (n + 1)) a
  have hgeometry := continuous_clipping_simplex_geometry _ cpi hK'
    (eHat (2 * (n + 1)) a) hfit.2.2.1 hfit.2.2.2
  have hgeometry' : cpi ≤ 2 ∧
      ∀ r : RegularIndex L, (L.T r.val.1 r.val.2).Nonempty := by
    exact hL ▸ hgeometry
  obtain ⟨hcpi, hne⟩ := hgeometry'
  have hlabels : ∀ n a, a ∈ G n →
      recoveryLabels (recoveredData M S I₁ I₂ pHat phi rho gap (2 * (n + 1)) a) =
        recoveryLabels L := fun n a ha => congrArg recoveryLabels (hLevels n a ha)
  obtain ⟨F, hm, hb, heq, hrate⟩ := contDMLRegime_oracle_component_predictors
    M μ S I₁ I₂ pHat phi rho gap cpi L ch eHat hr G hG hlabels
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
    exact repairContNuisance_component_eq_on_recovery M L _ (hLevels n a ha)
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

end Papers.TbsPrteOptimalTransport

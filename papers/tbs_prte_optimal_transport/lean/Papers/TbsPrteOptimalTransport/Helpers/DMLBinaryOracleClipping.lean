module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLReconstructedRegularity
public import Causalean.Mathlib.Analysis.ClipInterval
/-! Regular binary oracle records away from the recovery event.
Fixed-label factors can leave the clipping and simplex ranges off their image.
A measurable pointwise repair restores these ranges and is the identity on
supported feasible records, so it preserves their rates on exact recovery. -/
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

-- @node: repairBinShares
/-- For [level data](hyp:L), [nonempty instrument groups at every regular index](hyp:hne),
[a binary nuisance record](hyp:e), [a regular index](hyp:a), [an instrument value](hyp:z),
and [a covariate value](hyp:x), the [repaired share](goal) uses
[shares clipped to the unit interval and set to zero outside the group when their group sum is one](step:1),
and otherwise [puts all mass on a chosen instrument in the group](step:2). -/
noncomputable def repairBinShares (L : LevelData Z X)
    (hne : ∀ a : RegularIndex L, (L.T a.val.1 a.val.2).Nonempty)
    (e : NuisanceBin L) (a : RegularIndex L) (z : Z) (x : X) : ℝ :=
  if (∑ w ∈ L.T a.val.1 a.val.2, clipIcc 0 1 (e.share a w x)) = 1 then
    if z ∈ L.T a.val.1 a.val.2 then clipIcc 0 1 (e.share a z x) else 0
  else if z = Classical.choose (hne a) then 1 else 0

-- @node: repairBinShares_regular
/-- If [every regular instrument group is nonempty](hyp:hne), then
[the repaired shares lie in the unit interval, sum to one within the selected group,
and vanish outside it](goal). -/
lemma repairBinShares_regular (L : LevelData Z X)
    (hne : ∀ a : RegularIndex L, (L.T a.val.1 a.val.2).Nonempty)
    (e : NuisanceBin L) (a : RegularIndex L) (x : X) :
    (∀ z, repairBinShares L hne e a z x ∈ Icc (0 : ℝ) 1) ∧
    (∑ z ∈ L.T a.val.1 a.val.2, repairBinShares L hne e a z x) = 1 ∧
    (∀ z, z ∉ L.T a.val.1 a.val.2 → repairBinShares L hne e a z x = 0) := by
  have hz := Classical.choose_spec (hne a)
  unfold repairBinShares
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

-- @node: repairBinShares_eq_of_regular
/-- If [each regular instrument group is nonempty](hyp:hne),
[the nuisance record satisfies binary clipping](hyp:hc), and
[its fitted shares form a simplex in each group](hyp:hs), then
[repairing a share gives its original value inside the group and zero outside](goal). -/
lemma repairBinShares_eq_of_regular (L : LevelData Z X)
    (hne : ∀ a : RegularIndex L, (L.T a.val.1 a.val.2).Nonempty)
    (e : NuisanceBin L) (hc : BinClipping L e) (hs : BinFittedSharesSimplex L e)
    (a : RegularIndex L) (z : Z) (x : X) :
    repairBinShares L hne e a z x = (restrictBinShares L e).share a z x := by
  have hsum : (∑ w ∈ L.T a.val.1 a.val.2, clipIcc 0 1 (e.share a w x)) = 1 := by
    simpa only [clipIcc_eq_self (hc.2.2.2.1 a _ x)] using (hs a x).2
  simp only [repairBinShares, if_pos hsum, restrictBinShares,
    clipIcc_eq_self (hc.2.2.2.1 a z x)]

-- @node: repairBinNuisance
/-- For [level data](hyp:L), [a denominator clipping constant](hyp:cpi),
[nonempty regular instrument groups](hyp:hne), and [a binary nuisance record](hyp:e),
the [repaired binary nuisance record](goal) clips
[instrument propensities](step:1), [baseline level propensities](step:2), and
[treated-success regressions](step:3) to the unit interval;
clips [baseline level masses](step:4) and [regular group masses](step:5) between
the larger of zero and half the clipping constant and one;
[repairs the within-group shares to a supported simplex](step:6);
clips [higher-policy minus higher-baseline probability weights to the interval from minus one to one](step:7);
and clips [regular policy-union probability weights](step:8) and [the tail policy probability](step:9)
to the unit interval. -/
noncomputable def repairBinNuisance (L : LevelData Z X) (cpi : ℝ)
    (hne : ∀ a : RegularIndex L, (L.T a.val.1 a.val.2).Nonempty)
    (e : NuisanceBin L) : NuisanceBin L :=
  { prop := fun z x => clipIcc 0 1 (e.prop z x)
    pLev := fun k x => clipIcc 0 1 (e.pLev k x)
    P1 := fun k x => clipIcc 0 1 (e.P1 k x)
    piLev := fun k x => clipIcc (max 0 (cpi / 2)) 1 (e.piLev k x)
    tauLev := fun a x => clipIcc (max 0 (cpi / 2)) 1 (e.tauLev a x)
    share := repairBinShares L hne e
    gammaFull := fun k x => clipIcc (-1) 1 (e.gammaFull k x)
    gamma := fun a x => clipIcc 0 1 (e.gamma a x)
    gammaTail := fun x => clipIcc 0 1 (e.gammaTail x) }

-- @node: repairBinNuisance_regular
/-- If [the denominator clipping constant is at most two](hyp:hcpi) and
[every regular instrument group is nonempty](hyp:hne), then
[the repaired record satisfies binary clipping, fitted-share simplex constraints,
and denominator clipping at that constant](goal). -/
lemma repairBinNuisance_regular (L : LevelData Z X) (cpi : ℝ) (hcpi : cpi ≤ 2)
    (hne : ∀ a : RegularIndex L, (L.T a.val.1 a.val.2).Nonempty)
    (e : NuisanceBin L) :
    BinClipping L (repairBinNuisance L cpi hne e) ∧
    BinFittedSharesSimplex L (repairBinNuisance L cpi hne e) ∧
    BinDenominatorsClipped L (repairBinNuisance L cpi hne e) cpi := by
  have hden : max 0 (cpi / 2) ≤ (1 : ℝ) := max_le zero_le_one (by linarith)
  have hd (r : ℝ) := clipIcc_mem_Icc hden r
  have hu (r : ℝ) := clipIcc_mem_Icc zero_le_one r
  have hd0 (r : ℝ) : clipIcc (max 0 (cpi / 2)) 1 r ∈ Icc (0 : ℝ) 1 :=
    ⟨(le_max_left _ _).trans (hd r).1, (hd r).2⟩
  have hdc (r : ℝ) : clipIcc (max 0 (cpi / 2)) 1 r ∈ Icc (cpi / 2) 1 :=
    ⟨(le_max_right _ _).trans (hd r).1, (hd r).2⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact fun z x => hu _
  · exact fun k x => ⟨hu _, hu _, hd0 _⟩
  · exact fun a x => ⟨hd0 _, hu _⟩
  · exact fun a z x => (repairBinShares_regular L hne e a x).1 z
  · exact fun x => hu _
  · refine ⟨(fun k x => max (clipIcc (-1) 1 (e.gammaFull k x)) 0),
      (fun k x => max (-clipIcc (-1) 1 (e.gammaFull k x)) 0), ?_, ?_⟩
    · intro k x
      let r := clipIcc (-1) 1 (e.gammaFull k x)
      have hr : r ∈ Icc (-1 : ℝ) 1 := clipIcc_mem_Icc (by norm_num) _
      exact ⟨⟨le_max_right _ _, max_le hr.2 zero_le_one⟩,
        ⟨le_max_right _ _, max_le (by linarith [hr.1]) zero_le_one⟩⟩
    · intro k x
      let r := clipIcc (-1) 1 (e.gammaFull k x)
      change r = max r 0 - max (-r) 0
      rcases le_total 0 r with h | h
      · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), sub_zero]
      · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h), zero_sub, neg_neg]
  · exact fun a x => ⟨fun z => ((repairBinShares_regular L hne e a x).1 z).1,
      (repairBinShares_regular L hne e a x).2.1⟩
  · exact ⟨fun k x => hdc _, fun a x _ => hdc _⟩

-- @node: repairBinNuisance_eq_of_regular
/-- If [all regular instrument groups are nonempty](hyp:hne),
[the record satisfies binary clipping](hyp:hc), [its fitted shares form simplices](hyp:hs),
and [its denominators satisfy clipping at the chosen constant](hyp:hd), then
[repair leaves the record unchanged except for setting shares outside their groups to zero](goal). -/
lemma repairBinNuisance_eq_of_regular (L : LevelData Z X) (cpi : ℝ)
    (hne : ∀ a : RegularIndex L, (L.T a.val.1 a.val.2).Nonempty)
    (e : NuisanceBin L) (hc : BinClipping L e) (hs : BinFittedSharesSimplex L e)
    (hd : BinDenominatorsClipped L e cpi) :
    repairBinNuisance L cpi hne e = restrictBinShares L e := by
  have hpi (k) (x) : e.piLev k x ∈ Icc (max 0 (cpi / 2)) 1 :=
    ⟨max_le (hc.2.1 k x).2.2.1 (hd.1 k x).1, (hd.1 k x).2⟩
  have htau (a) (x) : e.tauLev a x ∈ Icc (max 0 (cpi / 2)) 1 :=
    ⟨max_le (hc.2.2.1 a x).1.1 (hd.2 a x (hne a)).1, (hd.2 a x (hne a)).2⟩
  have hfull (k) (x) : e.gammaFull k x ∈ Icc (-1 : ℝ) 1 := by
    exact binClipping_full_range L e hc k x
  cases e
  unfold repairBinNuisance restrictBinShares
  congr 1
  all_goals first
    | exact funext fun a => funext fun z => funext fun x =>
        repairBinShares_eq_of_regular L hne _ hc hs a z x
    | (funext i x; exact clipIcc_eq_self (hc.1 i x))
    | (funext i x; exact clipIcc_eq_self ((hc.2.1 i x).1))
    | (funext i x; exact clipIcc_eq_self ((hc.2.1 i x).2.1))
    | (funext i x; exact clipIcc_eq_self (hpi i x))
    | (funext i x; exact clipIcc_eq_self (htau i x))
    | (funext i x; exact clipIcc_eq_self (hfull i x))
    | (funext i x; exact clipIcc_eq_self ((hc.2.2.1 i x).2))
    | (funext x; exact clipIcc_eq_self (hc.2.2.2.2.1 x))

-- @node: repairBinShares_measurable
/-- If [every regular instrument group is nonempty](hyp:hne) and
[each original share is jointly measurable in the record index and covariates](hyp:hm),
then [each repaired share is jointly measurable in those variables](goal). -/
@[fun_prop] lemma repairBinShares_measurable {B : Type*} [MeasurableSpace B]
    (L : LevelData Z X)
    (hne : ∀ a : RegularIndex L, (L.T a.val.1 a.val.2).Nonempty)
    (e : B → NuisanceBin L)
    (hm : ∀ a z, Measurable (fun bx : B × X => (e bx.1).share a z bx.2))
    (a : RegularIndex L) (z : Z) :
    Measurable (fun bx : B × X => repairBinShares L hne (e bx.1) a z bx.2) := by
  try fun_prop
  have hsum : Measurable (fun bx : B × X =>
      ∑ w ∈ L.T a.val.1 a.val.2, clipIcc 0 1 ((e bx.1).share a w bx.2)) := by
    fun_prop
  have hset : MeasurableSet {bx : B × X |
      (∑ w ∈ L.T a.val.1 a.val.2, clipIcc 0 1 ((e bx.1).share a w bx.2)) = 1} :=
    measurableSet_eq_fun hsum measurable_const
  unfold repairBinShares
  apply Measurable.ite hset
  · split_ifs <;> fun_prop
  · split_ifs <;> fun_prop

-- @node: repairBinNuisance_decoded_measurable
/-- If [each regular instrument group is nonempty](hyp:hne) and
[each encoded component is jointly measurable in the record index and covariates](hyp:hm),
then [every encoded component obtained by decoding and repairing is jointly measurable](goal). -/
@[fun_prop] lemma repairBinNuisance_decoded_measurable
    {B : Type*} [MeasurableSpace B] (L : LevelData Z X) (cpi : ℝ)
    (hne : ∀ a : RegularIndex L, (L.T a.val.1 a.val.2).Nonempty)
    (F : B → (ℕ × ℕ × ℕ × Z) → X → ℝ)
    (hm : ∀ c, Measurable (fun bx : B × X => F bx.1 c bx.2))
    (c : ℕ × ℕ × ℕ × Z) :
    Measurable (fun bx : B × X => binComponent L
      (repairBinNuisance L cpi hne (decodeBinComponents L (F bx.1))) c bx.2) := by
  try fun_prop
  have hs (a : RegularIndex L) (z : Z) : Measurable (fun bx : B × X =>
      repairBinShares L hne (decodeBinComponents L (F bx.1)) a z bx.2) := by
    refine repairBinShares_measurable L hne (fun b => decodeBinComponents L (F b)) ?_ a z
    intro a z
    change Measurable (fun bx : B × X => F bx.1
      (5, a.val.1, a.val.2, z) bx.2)
    exact hm _
  rcases c with ⟨code, k, j, z⟩
  unfold binComponent repairBinNuisance
  dsimp only
  split <;> try dsimp only
  all_goals try simp only [positiveValue, regularValue, fullValue]
  all_goals simp only [decodeBinComponents]
  all_goals repeat' first | fun_prop | split

-- @node: repairBinNuisance_component_eq_on_recovery
/-- If [the recovered and reference level data coincide](hyp:hL),
[all reference regular instrument groups are nonempty](hyp:hne), and
[the encoded functions equal the components of the recovered nuisance record](hyp:heq),
with [binary clipping](hyp:hc), [simplex shares](hyp:hs), and
[clipped denominators](hyp:hd), then
[decoding and repairing under the reference data preserves every component at every covariate value](goal). -/
lemma repairBinNuisance_component_eq_on_recovery
    (L L' : LevelData Z X) (hL : L' = L) (cpi : ℝ)
    (hne : ∀ a : RegularIndex L, (L.T a.val.1 a.val.2).Nonempty)
    (F : (ℕ × ℕ × ℕ × Z) → X → ℝ) (e : NuisanceBin L')
    (heq : ∀ c x, F c x = binComponent L' e c x)
    (hc : BinClipping L' e) (hs : BinFittedSharesSimplex L' e)
    (hd : BinDenominatorsClipped L' e cpi) (c : ℕ × ℕ × ℕ × Z) (x : X) :
    binComponent L (repairBinNuisance L cpi hne (decodeBinComponents L F)) c x =
      binComponent L' e c x := by
  subst L'
  have hF : F = binComponent L e := funext fun c => funext (heq c)
  rw [hF, decodeBinComponents_binComponent]
  have hr := restrictBinShares_regular L e cpi hc hs hd
  rw [repairBinNuisance_eq_of_regular L cpi hne _ hr.1 hr.2.1 hr.2.2,
    binComponent_restrictBinShares, binComponent_restrictBinShares]

-- @node: binary_clipping_simplex_geometry
/-- If [there is at least one positive level](hyp:hK),
[the record's denominators are clipped at half the chosen constant](hyp:hd), and
[its fitted shares form simplices](hyp:hs), then
[the constant is at most two and every regular instrument group is nonempty](goal). -/
lemma binary_clipping_simplex_geometry (L : LevelData Z X) (cpi : ℝ)
    (hK : LevelCountPos L.K) (e : NuisanceBin L)
    (hd : BinDenominatorsClipped L e cpi) (hs : BinFittedSharesSimplex L e) :
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

-- @node: binDMLRegime_regular_oracle_nuisance_records
/-- Suppose [the reference level count is positive](hyp:hK),
[the fitted binary nuisance records on the recovered level structures](hyp:eHat)
[satisfy the finite binary double machine learning regime](hyp:hr),
[the complements of the recovery events have probability tending to zero](hyp:hG), and
[the recovered level data equal the reference data on those events at even sample sizes](hyp:hLevels).
Then [there exist reference-level oracle records with training-measurable components,
binary clipping, simplex shares, clipped denominators, admissibility, and finite nuisance rates,
whose components equal the fitted components on the recovery events](goal). -/
lemma binDMLRegime_regular_oracle_nuisance_records
    (M : LatentIVModel Ω X Z) {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (pHat : ℕ → A → Z → X → ℝ) (phi : Z → X → ℝ → ℝ)
    (rho : ℕ → ℝ) (gap cpi : ℝ) (L : LevelData Z X) (ch : ℝ)
    (hK : LevelCountPos L.K)
    (eHat : ∀ n a, NuisanceBin (recoveredData M S I₁ I₂ pHat phi rho gap n a))
    (hr : FiniteBinDMLRegime M μ S I₁ I₂ pHat phi rho gap cpi L ch eHat)
    (G : ℕ → Set A)
    (hG : Tendsto (fun n => μ (G n)ᶜ) atTop (𝓝 0))
    (hLevels : ∀ n a, a ∈ G n →
      recoveredData M S I₁ I₂ pHat phi rho gap (2 * (n + 1)) a = L) :
    ∃ oracle : ℕ → A → NuisanceBin L,
      (∀ c, TrainingPredictorMeasurable M S I₁
        (fun n a => binComponent L (oracle n a) c)) ∧
      (∀ n a, BinClipping L (oracle n a) ∧
        BinFittedSharesSimplex L (oracle n a) ∧
        BinDenominatorsClipped L (oracle n a) cpi) ∧
      (∀ n a, BinAdmissible M L (oracle n a)) ∧
      (∀ n a, a ∈ G n → ∀ c x,
        binComponent L (oracle (2 * (n + 1)) a) c x =
          binComponent _ (eHat (2 * (n + 1)) a) c x) ∧
      FiniteNuisanceRates M μ (fun n a => binComponent L (oracle n a))
        (binComponent L (eta0Bin M L)) := by
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
  have hfit := hr.1.2.2.2.2.1 (2 * (n + 1)) a
  have hgeometry := binary_clipping_simplex_geometry _ cpi hK'
    (eHat (2 * (n + 1)) a) hfit.2.2.1 hfit.2.2.2
  have hgeometry' : cpi ≤ 2 ∧
      ∀ r : RegularIndex L, (L.T r.val.1 r.val.2).Nonempty := by
    exact hL ▸ hgeometry
  obtain ⟨hcpi, hne⟩ := hgeometry'
  have hlabels : ∀ n a, a ∈ G n →
      recoveryLabels (recoveredData M S I₁ I₂ pHat phi rho gap (2 * (n + 1)) a) =
        recoveryLabels L := fun n a ha => congrArg recoveryLabels (hLevels n a ha)
  obtain ⟨F, hm, hb, heq, hrate⟩ := binDMLRegime_oracle_component_predictors
    M μ S I₁ I₂ pHat phi rho gap cpi L ch eHat hr G hG hlabels
  let raw := fun n a => repairBinNuisance L cpi hne (decodeBinComponents L (F n a))
  let oracle := fun n a => restrictBinShares L (raw n a)
  have hreg (n : ℕ) (a : A) : BinClipping L (oracle n a) ∧
      BinFittedSharesSimplex L (oracle n a) ∧
      BinDenominatorsClipped L (oracle n a) cpi := by
    have h := repairBinNuisance_regular L cpi hcpi hne (decodeBinComponents L (F n a))
    exact restrictBinShares_regular L _ cpi h.1 h.2.1 h.2.2
  have hmeas (c) : TrainingPredictorMeasurable M S I₁
      (fun n a => binComponent L (oracle n a) c) := by
    intro n
    let : MeasurableSpace A :=
      MeasurableSpace.comap (trainingView M S I₁ n) inferInstance
    have hh := repairBinNuisance_decoded_measurable L cpi hne (F n)
      (fun c => hm c n) c
    change Measurable (fun ax : A × X => binComponent L (oracle n ax.1) c ax.2)
    simpa only [oracle, raw, binComponent_restrictBinShares] using hh
  have heq' : ∀ n a, a ∈ G n → ∀ c x,
      binComponent L (oracle (2 * (n + 1)) a) c x =
        binComponent _ (eHat (2 * (n + 1)) a) c x := by
    intro n a ha c x
    have hf := hr.1.2.2.2.2.1 (2 * (n + 1)) a
    simp only [oracle, binComponent_restrictBinShares, raw]
    exact repairBinNuisance_component_eq_on_recovery L _ (hLevels n a ha)
      cpi hne _ _ (heq n a ha) hf.2.1 hf.2.2.2 hf.2.2.1 c x
  refine ⟨oracle, hmeas, hreg, ?_, heq', ?_⟩
  · intro n a
    have hmsection (c) : Measurable (binComponent L (raw n a) c) := by
      let : MeasurableSpace A :=
        MeasurableSpace.comap (trainingView M S I₁ n) inferInstance
      have hh := repairBinNuisance_decoded_measurable L cpi hne (F n)
        (fun c => hm c n) c
      exact hh.comp (measurable_const.prodMk measurable_id)
    have h := repairBinNuisance_regular L cpi hcpi hne (decodeBinComponents L (F n a))
    exact restrictBinShares_admissible_of_encoded_clipping M L (raw n a)
      h.1 h.2.1 hmsection
  · exact nuisanceRates_transfer_on_recovery M μ
      (fun n a => binComponent _ (eHat n a))
      (fun n a => binComponent L (oracle n a))
      (binComponent L (eta0Bin M L)) G hG heq' hr.2.1

end Papers.TbsPrteOptimalTransport

module
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationInstrumentMoments
/-! Regularity derived from admissible binary paths and baseline overlap. -/
public section
set_option linter.style.haveILetI false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedTactic false
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set
open scoped Classical

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: binary_admissible_direction_origin
/-- If [a binary nuisance perturbation is an admissible direction around a nuisance specification](hyp:hd),
[that specification itself is admissible](goal). -/
lemma binary_admissible_direction_origin (L : LevelData Z X) (eta del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr eta) (.inr del)) :
    BinAdmissible M L eta := by
  obtain ⟨r, hr, hpath⟩ := hd.admissible
  have h0 := hpath 0 (by simpa using hr)
  have hid : eta + (0 : ℝ) • del = eta := by
    change NuisanceBinData.mk (eta.prop + (0 : ℝ) • del.prop)
      (eta.pLev + (0 : ℝ) • del.pLev) (eta.P1 + (0 : ℝ) • del.P1)
      (eta.piLev + (0 : ℝ) • del.piLev) (eta.tauLev + (0 : ℝ) • del.tauLev)
      (eta.share + (0 : ℝ) • del.share) (eta.gammaFull + (0 : ℝ) • del.gammaFull)
      (eta.gamma + (0 : ℝ) • del.gamma) (eta.gammaTail + (0 : ℝ) • del.gammaTail) = eta
    simp only [zero_smul, add_zero]
    cases eta
    rfl
  rwa [hid] at h0

-- The same radius works for every full-interval weight. Measurability follows
-- by subtracting two measurable points of the path; the range has width two.
-- @node: binary_full_weight_direction_regular
/-- If [a binary nuisance perturbation is admissible around a nuisance specification](hyp:hd),
[all its full-interval weight perturbations are measurable and share a nonnegative,
finite almost-sure bound under the covariate distribution](goal). -/
lemma binary_full_weight_direction_regular (L : LevelData Z X) (eta del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr eta) (.inr del)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : Fin L.K,
      Measurable (del.gammaFull k) ∧ ∀ᵐ x ∂xLaw M, ‖del.gammaFull k x‖ ≤ C := by
  obtain ⟨r, hr, hpath⟩ := hd.admissible
  have h0 := hpath 0 (by simpa using hr)
  have ht := hpath (r / 2) (by rw [abs_of_pos (by positivity)]; linarith)
  rcases h0 with ⟨_, _, _, _, _, _, _, _, _, hg0, hmg0, _, _⟩
  rcases ht with ⟨_, _, _, _, _, _, _, _, _, hgt, hmgt, _, _⟩
  refine ⟨4 / r, by positivity, ?_⟩
  intro k
  have hm0 : Measurable (eta.gammaFull k) := by
    have hm : Measurable (fun x => eta.gammaFull k x + 0 * del.gammaFull k x) := hmg0 k
    simpa only [zero_mul, add_zero] using hm
  have hmt : Measurable (fun x => eta.gammaFull k x + (r / 2) * del.gammaFull k x) :=
    hmgt k
  constructor
  · have hid : del.gammaFull k = fun x =>
        ((eta.gammaFull k x + (r / 2) * del.gammaFull k x) - eta.gammaFull k x) / (r / 2) := by
      funext x
      field_simp
      <;> ring
    rw [hid]
    exact (hmt.sub hm0).div_const _
  · filter_upwards [hg0 k, hgt k] with x hx0 hxt
    change eta.gammaFull k x + 0 * del.gammaFull k x ∈ Icc (-1 : ℝ) 1 at hx0
    change eta.gammaFull k x + (r / 2) * del.gammaFull k x ∈ Icc (-1 : ℝ) 1 at hxt
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · rw [← neg_div, div_le_iff₀ hr]
      nlinarith [hx0.1, hx0.2, hxt.1, hxt.2]
    · apply (le_div_iff₀ hr).2
      nlinarith [hx0.1, hx0.2, hxt.1, hxt.2]

-- @node: population_binary_RP_integrable
/-- Under [baseline overlap with the specified positive lower bound](hyp:hov),
[almost-surely binary outcomes](hyp:hy), and [admissibility of the population binary
nuisance specification](hyp:he), [the treated-success residual correction at any
level is integrable under the observation distribution](goal). -/
lemma population_binary_RP_integrable (L : LevelData Z X) (cpi : ℝ)
    (hov : BaselineOverlapWitness M L cpi) (hy : OutcomeBinaryAE M)
    (he : BinAdmissible M L (eta0Bin M L)) (k : ℕ) :
    Integrable (RP L (eta0Bin M L) k) (observationLaw M) := by
  haveI : IsFiniteMeasure (observationLaw M) := by
    unfold observationLaw
    infer_instance
  have hcpi : 0 < cpi := hov.1
  have hobs := M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY))
  have hyw : ∀ᵐ o : Obs X Z ∂observationLaw M,
      o.2.2.2 ∈ Icc (0 : ℝ) 1 ∧ o.2.2.1 ∈ Icc (0 : ℝ) 1 := by
    have hset : MeasurableSet {o : Obs X Z |
        o.2.2.2 ∈ Icc (0 : ℝ) 1 ∧ o.2.2.1 ∈ Icc (0 : ℝ) 1} :=
      (measurableSet_Icc.preimage measurable_snd.snd.snd).inter
        (measurableSet_Icc.preimage measurable_snd.snd.fst)
    exact (ae_map_iff hobs.aemeasurable hset).2 (by
      filter_upwards [hy] with s hs
      rcases hs with hs | hs <;> rcases M.rangeW s with hw | hw <;> simp [hs, hw])
  by_cases hk : 1 ≤ k ∧ k ≤ L.K
  · have hk0 : k ≠ 0 := by omega
    have hP := observationLaw_covariate_ae M _ (he.2.2.1 ⟨k, hk⟩)
    apply (integrable_const (2 / cpi : ℝ)).mono'
      (population_RP_measurable M L k).aestronglyMeasurable
    filter_upwards [hyw, hP] with o ho hPo
    have hP0 : 0 ≤ treatedSuccess M L k o.1 := hPo.2.1.1
    have hP1 : treatedSuccess M L k o.1 ≤ 1 := hPo.2.1.2
    have hp := hov.2 o.1 k hk.1 hk.2
    have hp0 : 0 < (levelSetProb M L).1 k o.1 := hov.1.trans_le hp
    have habs : |o.2.2.2 * o.2.2.1 - treatedSuccess M L k o.1| ≤ 2 := by
      rw [abs_le]
      constructor <;> nlinarith [mul_nonneg ho.1.1 ho.2.1,
        mul_le_one₀ ho.1.2 ho.2.1 ho.2.2]
    simp only [RP, if_neg hk0, positiveValue, dif_pos hk, eta0Bin,
      Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos hp0]
    have hi : |indicator (o.2.1 ∈ L.S k)| ≤ 1 := by
      unfold indicator
      split_ifs <;> norm_num
    calc
      _ ≤ (1 / (levelSetProb M L).1 k o.1) * 2 :=
        mul_le_mul (div_le_div_of_nonneg_right hi hp0.le) habs (abs_nonneg _) (by positivity)
      _ = 2 / (levelSetProb M L).1 k o.1 := by ring
      _ ≤ 2 / cpi := div_le_div_of_nonneg_left (by norm_num) hov.1 hp
    all_goals rw [abs_of_pos (by positivity : 0 < 2 / cpi)]
  · have hz : RP L (eta0Bin M L) k = fun _ => (0 : ℝ) := by
      funext o
      by_cases hk0 : k = 0 <;> simp [RP, hk0, positiveValue, hk]
    rw [hz]
    exact integrable_const 0

-- @node: population_binary_full_contrast_integrable
/-- If [the population binary nuisance specification is admissible](hyp:he),
[the difference in treated-success probabilities between two consecutive levels,
evaluated at observed covariates, is integrable under the observation distribution](goal). -/
lemma population_binary_full_contrast_integrable (L : LevelData Z X)
    (he : BinAdmissible M L (eta0Bin M L)) (k : ℕ) :
    Integrable (fun o : Obs X Z => binFullJ L (eta0Bin M L) k o.1)
      (observationLaw M) := by
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  have hlevels : ∀ i : ℕ, ∀ᵐ o : Obs X Z ∂observationLaw M,
      positiveValue (eta0Bin M L).P1 i o.1 ∈ Icc (0 : ℝ) 1 := by
    intro i
    by_cases hi : 1 ≤ i ∧ i ≤ L.K
    · have hb := observationLaw_covariate_ae M _ (he.2.2.1 ⟨i, hi⟩)
      filter_upwards [hb] with o ho
      simpa only [positiveValue, dif_pos hi] using ho.2.1
    · simp only [positiveValue, dif_neg hi]
      exact Filter.Eventually.of_forall (fun _ => ⟨le_rfl, zero_le_one⟩)
  apply (integrable_const (2 : ℝ)).mono'
    (((population_binFullJ_measurable M L k).comp measurable_fst).aestronglyMeasurable)
  filter_upwards [hlevels (k+1), hlevels k] with o hp hm
  simp only [Function.comp_apply, binFullJ, Real.norm_eq_abs, abs_le]
  constructor <;> linarith [hp.1, hp.2, hm.1, hm.2]

-- @node: population_binary_weighted_RP_integrable
/-- Under [baseline overlap with the specified positive lower bound](hyp:hov),
[almost-surely binary outcomes](hyp:hy), and [admissibility of the population binary
nuisance specification](hyp:he), if [a covariate weight is measurable](hyp:hw) and
[its absolute value is almost surely bounded by the given constant](hyp:hb),
[the weight times the treated-success residual correction is integrable under
the observation distribution](goal). -/
lemma population_binary_weighted_RP_integrable (L : LevelData Z X) (cpi : ℝ)
    (hov : BaselineOverlapWitness M L cpi) (hy : OutcomeBinaryAE M)
    (he : BinAdmissible M L (eta0Bin M L)) (k : ℕ)
    (w : X → ℝ) (hw : Measurable w) (C : ℝ)
    (hb : ∀ᵐ x ∂xLaw M, ‖w x‖ ≤ C) :
    Integrable (fun o : Obs X Z => w o.1 * RP L (eta0Bin M L) k o)
      (observationLaw M) := by
  have hi := population_binary_RP_integrable M L cpi hov hy he k
  exact hi.bdd_mul (hw.comp measurable_fst).aestronglyMeasurable
    (observationLaw_covariate_ae M _ hb)

-- @node: population_binary_full_product_integrable_of_overlap
/-- Under [baseline overlap with the specified positive lower bound](hyp:hov),
[almost-surely binary outcomes](hyp:hy), and [admissibility of the population binary
nuisance specification](hyp:he), [the full-interval product score at each valid
baseline interval is integrable under the observation distribution](goal). -/
lemma population_binary_full_product_integrable_of_overlap (L : LevelData Z X) (cpi : ℝ)
    (hov : BaselineOverlapWitness M L cpi) (hy : OutcomeBinaryAE M)
    (he : BinAdmissible M L (eta0Bin M L)) (k : Fin L.K) :
    Integrable (psiFullProdBin L (eta0Bin M L) k) (observationLaw M) := by
  have heCopy := he
  rcases heCopy with ⟨_, _, _, _, _, _, _, _, _, hgamma, hmgamma, _, _⟩
  have hg : Measurable (gammaFull M L k) := hmgamma k
  have hgb : ∀ᵐ x ∂xLaw M, ‖gammaFull M L k x‖ ≤ 1 := by
    filter_upwards [hgamma k] with x hx
    simpa only [eta0Bin, Set.mem_Icc, Real.norm_eq_abs, abs_le] using hx
  have ip := population_binary_weighted_RP_integrable M L cpi hov hy he (k+1)
    (gammaFull M L k) hg 1 hgb
  have im := population_binary_weighted_RP_integrable M L cpi hov hy he k
    (gammaFull M L k) hg 1 hgb
  let a : Obs X Z → ℝ := fun o => indicator (o.2.1 ∈ higherPolicy L k) -
    indicator (o.2.1 ∈ higherBaseline L k)
  have ha : Measurable a := by
    dsimp only [a]
    unfold indicator
    exact (Measurable.ite ((higherPolicy L k).finite_toSet.measurableSet.preimage
      measurable_snd.fst) measurable_const measurable_const).sub
      (Measurable.ite ((higherBaseline L k).finite_toSet.measurableSet.preimage
        measurable_snd.fst) measurable_const measurable_const)
  have hab : ∀ o, ‖a o‖ ≤ 1 := by
    intro o
    simp only [a, indicator]
    split_ifs <;> norm_num
  have ie := (population_binary_full_contrast_integrable M L he k).mul_bdd ha.aestronglyMeasurable
    (Filter.Eventually.of_forall hab)
  have hid : ∀ o, psiFullProdBin L (eta0Bin M L) k o =
      binFullJ L (eta0Bin M L) k o.1 * a o +
      gammaFull M L k o.1 * RP L (eta0Bin M L) (k+1) o -
      gammaFull M L k o.1 * RP L (eta0Bin M L) k o := by
    intro o
    simp only [psiFullProdBin, fullValue, dif_pos k.isLt, eta0Bin, a]
    ring
  change Integrable (fun o => psiFullProdBin L (eta0Bin M L) k o) _
  simp_rw [hid]
  exact (ie.fun_add ip).sub' im

-- All analytic inputs to the earlier component cancellation are now derived
-- from the paper's overlap, binary outcome, and neighborhood admissibility.
-- @node: population_binary_full_weight_orthogonality_of_admissible
/-- Under [baseline overlap with the specified positive lower bound](hyp:hov) and
[almost-surely binary outcomes](hyp:hy), if [a nuisance perturbation is admissible
at the population binary specification](hyp:hd), [the expected full-interval product
score has derivative zero at zero when its full-interval weight alone is varied
linearly in that direction](goal). -/
lemma population_binary_full_weight_orthogonality_of_admissible
    (L : LevelData Z X) (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (hy : OutcomeBinaryAE M) (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del)) (k : Fin L.K) :
    HasDerivAt (fun t : ℝ => ∫ o, psiFullProdBin L
      {eta0Bin M L with gammaFull := fun i x =>
        (eta0Bin M L).gammaFull i x + t * del.gammaFull i x} k o
      ∂observationLaw M) 0 0 := by
  have he := binary_admissible_direction_origin M L (eta0Bin M L) del hd
  obtain ⟨C, hC, hreg⟩ := binary_full_weight_direction_regular M L (eta0Bin M L) del hd
  obtain ⟨hm, hb⟩ := hreg k
  exact population_binary_full_product_weight_orthogonality M L del.gammaFull k hm
    (population_binary_full_product_integrable_of_overlap M L cpi hov hy he k)
    (population_binary_weighted_RP_integrable M L cpi hov hy he (k+1) _ hm C hb)
    (population_binary_weighted_RP_integrable M L cpi hov hy he k _ hm C hb)

-- @node: population_binary_full_product_mean_of_overlap
/-- Under [baseline overlap with the specified positive lower bound](hyp:hov),
[almost-surely binary outcomes](hyp:hy), and [admissibility of the population binary
nuisance specification](hyp:he), [the expected full-interval product score equals
the covariate average of the population full-interval weight times the adjacent
treated-success probability contrast](goal). -/
lemma population_binary_full_product_mean_of_overlap (L : LevelData Z X) (cpi : ℝ)
    (hov : BaselineOverlapWitness M L cpi) (hy : OutcomeBinaryAE M)
    (he : BinAdmissible M L (eta0Bin M L)) (k : Fin L.K) :
    (∫ o, psiFullProdBin L (eta0Bin M L) k o ∂observationLaw M) =
      ∫ x, gammaFull M L k x * binFullJ L (eta0Bin M L) k x ∂xLaw M := by
  have heCopy := he
  rcases heCopy with ⟨_, _, _, _, _, _, _, _, _, hgamma, hmgamma, _, _⟩
  have hg : Measurable (gammaFull M L k) := hmgamma k
  have hgb : ∀ᵐ x ∂xLaw M, ‖gammaFull M L k x‖ ≤ 1 := by
    filter_upwards [hgamma k] with x hx
    simpa only [eta0Bin, Set.mem_Icc, Real.norm_eq_abs, abs_le] using hx
  have ip := population_binary_weighted_RP_integrable M L cpi hov hy he (k+1)
    (gammaFull M L k) hg 1 hgb
  have im := population_binary_weighted_RP_integrable M L cpi hov hy he k
    (gammaFull M L k) hg 1 hgb
  have ifull := population_binary_full_product_integrable_of_overlap M L cpi hov hy he k
  have ie : Integrable (fun o : Obs X Z => binFullJ L (eta0Bin M L) k o.1 *
      (indicator (o.2.1 ∈ higherPolicy L k) - indicator (o.2.1 ∈ higherBaseline L k)))
      (observationLaw M) := by
    have hid : (fun o : Obs X Z => binFullJ L (eta0Bin M L) k o.1 *
        (indicator (o.2.1 ∈ higherPolicy L k) - indicator (o.2.1 ∈ higherBaseline L k))) =
        (fun o => psiFullProdBin L (eta0Bin M L) k o -
          gammaFull M L k o.1 * RP L (eta0Bin M L) (k+1) o +
          gammaFull M L k o.1 * RP L (eta0Bin M L) k o) := by
      funext o
      simp only [psiFullProdBin, fullValue, dif_pos k.isLt, eta0Bin]
      ring
    rw [hid]
    exact (ifull.sub' ip).fun_add im
  exact population_binary_full_product_mean M L k ie ip im

end Papers.TbsPrteOptimalTransport

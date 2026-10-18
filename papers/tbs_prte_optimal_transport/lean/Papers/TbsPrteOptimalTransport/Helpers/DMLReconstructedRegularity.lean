module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousComponentDecoding
public import Papers.TbsPrteOptimalTransport.Helpers.DMLBinaryComponentDecoding
/-! Regularity of supported nuisance reconstructions on the exact-recovery event.
The coordinate encoding discards off-policy shares and unused auxiliary fits.
Normalizing these fields preserves clipping, simplex sums and denominator bounds;
coordinate equality then transports these properties to the oracle record. -/
public section
set_option linter.style.openClassical false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Set Filter
open scoped Classical Topology

universe u v
variable {Ω : Type u} {X Z : Type v}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]
  [Fintype Z] [DecidableEq Z]

-- @node: normalizeContAuxiliaryFits_regular
/-- If [a continuous nuisance record satisfies clipping](hyp:hc),
[its fitted shares form simplices](hyp:hs), and [its denominators satisfy
clipping at the given threshold](hyp:hd), then [normalizing its auxiliary
fits preserves clipping, the simplex conditions, and denominator clipping
at the same threshold](goal). -/
lemma normalizeContAuxiliaryFits_regular (M : LatentIVModel Ω X Z)
    (L : LevelData Z X) (e : NuisanceCont L) (cpi : ℝ)
    (hc : ContClipping M L e) (hs : ContFittedSharesSimplex L e)
    (hd : ContDenominatorsClipped L e cpi) :
    ContClipping M L (normalizeContAuxiliaryFits L e) ∧
      ContFittedSharesSimplex L (normalizeContAuxiliaryFits L e) ∧
      ContDenominatorsClipped L (normalizeContAuxiliaryFits L e) cpi := by
  obtain ⟨hp, hl, hr, ha, hf, ht, hn, hmp, hmm, hjp, hjm, hjfp, hjfm, _hprob⟩ := hc
  refine ⟨⟨hp, hl, hr, ?_, hf, ht, hn, hmp, hmm, hjp, hjm, hjfp, hjfm, ?_⟩, ?_, hd⟩
  · intro a z x
    change (if z ∈ L.T a.val.1 a.val.2 then e.share a z x else 0) ∈ Icc (0 : ℝ) 1
    split_ifs
    · exact ha a z x
    · exact ⟨le_rfl, zero_le_one⟩
  · exact fun k x => ⟨⟨le_rfl, zero_le_one⟩, ⟨le_rfl, zero_le_one⟩⟩
  · intro a x
    refine ⟨?_, ?_⟩
    · intro z
      change 0 ≤ if z ∈ L.T a.val.1 a.val.2 then e.share a z x else 0
      split_ifs
      · exact (hs a x).1 z
      · exact le_rfl
    · change (∑ z ∈ L.T a.val.1 a.val.2,
        if z ∈ L.T a.val.1 a.val.2 then e.share a z x else 0) = 1
      simpa only [Finset.sum_ite_mem, Finset.inter_self] using (hs a x).2

-- @node: restrictBinShares_regular
/-- If [a binary nuisance record satisfies clipping](hyp:hc),
[its fitted shares form simplices](hyp:hs), and [its denominators satisfy
clipping at the given threshold](hyp:hd), then [setting off-support shares
to zero preserves clipping, the simplex conditions, and denominator clipping
at the same threshold](goal). -/
lemma restrictBinShares_regular (L : LevelData Z X) (e : NuisanceBin L) (cpi : ℝ)
    (hc : BinClipping L e) (hs : BinFittedSharesSimplex L e)
    (hd : BinDenominatorsClipped L e cpi) :
    BinClipping L (restrictBinShares L e) ∧
      BinFittedSharesSimplex L (restrictBinShares L e) ∧
      BinDenominatorsClipped L (restrictBinShares L e) cpi := by
  have hfull := binClipping_full_range L e hc
  obtain ⟨hp, hl, hr, ha, ht, hop⟩ := hc
  refine ⟨⟨hp, hl, hr, ?_, ht, hop⟩, ?_, hd⟩
  · intro a z x
    change (if z ∈ L.T a.val.1 a.val.2 then e.share a z x else 0) ∈ Icc (0 : ℝ) 1
    split_ifs
    · exact ha a z x
    · exact ⟨le_rfl, zero_le_one⟩
  · intro a x
    refine ⟨?_, ?_⟩
    · intro z
      change 0 ≤ if z ∈ L.T a.val.1 a.val.2 then e.share a z x else 0
      split_ifs
      · exact (hs a x).1 z
      · exact le_rfl
    · change (∑ z ∈ L.T a.val.1 a.val.2,
        if z ∈ L.T a.val.1 a.val.2 then e.share a z x else 0) = 1
      simpa only [Finset.sum_ite_mem, Finset.inter_self] using (hs a x).2

-- @node: continuous_regularity_of_component_eq_of_level_eq
/-- If [two level descriptions agree](hyp:hL), [two continuous nuisance
records have identical encoded components at every covariate value](hyp:heq),
and the second record [satisfies clipping](hyp:hc), [has simplex fitted
shares](hyp:hs), and [has clipped denominators](hyp:hd), then [the normalized
first record satisfies clipping, the simplex conditions, and denominator
clipping at the same threshold](goal). -/
lemma continuous_regularity_of_component_eq_of_level_eq (M : LatentIVModel Ω X Z)
    (L L' : LevelData Z X) (hL : L' = L)
    (e : NuisanceCont L) (f : NuisanceCont L') (cpi : ℝ)
    (heq : ∀ c x, contComponent M L e c x = contComponent M L' f c x)
    (hc : ContClipping M L' f) (hs : ContFittedSharesSimplex L' f)
    (hd : ContDenominatorsClipped L' f cpi) :
    ContClipping M L (normalizeContAuxiliaryFits L e) ∧
      ContFittedSharesSimplex L (normalizeContAuxiliaryFits L e) ∧
      ContDenominatorsClipped L (normalizeContAuxiliaryFits L e) cpi := by
  subst L'
  have hfun : contComponent M L e = contComponent M L f :=
    funext fun c => funext (heq c)
  have hrecords : normalizeContAuxiliaryFits L e = normalizeContAuxiliaryFits L f := by
    rw [← decodeContComponents_contComponent M L e,
      ← decodeContComponents_contComponent M L f, hfun]
  rw [hrecords]
  exact normalizeContAuxiliaryFits_regular M L f cpi hc hs hd

-- @node: binary_regularity_of_component_eq_of_level_eq
/-- If [two level descriptions agree](hyp:hL), [two binary nuisance records
have identical encoded components at every covariate value](hyp:heq), and
the second record [satisfies clipping](hyp:hc), [has simplex fitted shares](hyp:hs),
and [has clipped denominators](hyp:hd), then [restricting the first record's
shares to their support yields clipping, simplex shares, and denominator
clipping at the same threshold](goal). -/
lemma binary_regularity_of_component_eq_of_level_eq
    (L L' : LevelData Z X) (hL : L' = L)
    (e : NuisanceBin L) (f : NuisanceBin L') (cpi : ℝ)
    (heq : ∀ c x, binComponent L e c x = binComponent L' f c x)
    (hc : BinClipping L' f) (hs : BinFittedSharesSimplex L' f)
    (hd : BinDenominatorsClipped L' f cpi) :
    BinClipping L (restrictBinShares L e) ∧
      BinFittedSharesSimplex L (restrictBinShares L e) ∧
      BinDenominatorsClipped L (restrictBinShares L e) cpi := by
  subst L'
  have hfun : binComponent L e = binComponent L f := funext fun c => funext (heq c)
  have hrecords : restrictBinShares L e = restrictBinShares L f := by
    rw [← decodeBinComponents_binComponent L e,
      ← decodeBinComponents_binComponent L f, hfun]
  rw [hrecords]
  exact restrictBinShares_regular L f cpi hc hs hd

-- @node: psiBin_rearrangeP1_eq_of_component_eq_of_level_eq
/-- If [two level descriptions coincide](hyp:hL), [the first has a positive
number of levels](hyp:hK), [the second has a positive number of levels](hyp:hK'),
and [two binary nuisance records have identical encoded components at every
covariate value](hyp:heq), then [their rearranged binary scores agree at
every observation](goal). -/
lemma psiBin_rearrangeP1_eq_of_component_eq_of_level_eq
    (M : LatentIVModel Ω X Z) (phi dphi : Z → X → ℝ → ℝ)
    (L L' : LevelData Z X) (hL : L' = L)
    (hK : LevelCountPos L.K) (hK' : LevelCountPos L'.K)
    (e : NuisanceBin L) (f : NuisanceBin L')
    (heq : ∀ c x, binComponent L e c x = binComponent L' f c x) (o : Obs X Z) :
    psiBin M phi dphi L hK o (rearrangeP1 L e) =
      psiBin M phi dphi L' hK' o (rearrangeP1 L' f) := by
  subst L'
  exact psiBin_rearrangeP1_eq_of_binComponent_eq M phi dphi L hK e f heq o

-- @node: fittedBinScore_eq_oracle_of_component_eq
/-- For [binary nuisance records fitted on the recovered levels](hyp:eHat), with [a positive number of fixed levels](hyp:hK), if [the recovered level
data equal the fixed level data at the given sample size and realization](hyp:hLevels)
and [the oracle and fitted binary records have identical encoded components
at every covariate value](hyp:heq), then [the feasible binary score equals
the rearranged oracle score at every observation](goal). -/
lemma fittedBinScore_eq_oracle_of_component_eq
    (M : LatentIVModel Ω X Z) {A : Type*} [MeasurableSpace A]
    {μ : Measure A} [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (pHat : ℕ → A → Z → X → ℝ) (phi dphi : Z → X → ℝ → ℝ)
    (rho : ℕ → ℝ) (gap : ℝ) (L : LevelData Z X) (hK : LevelCountPos L.K)
    (eHat : ∀ n a, NuisanceBin (recoveredData M S I₁ I₂ pHat phi rho gap n a))
    (oracle : ℕ → A → NuisanceBin L) (n : ℕ) (a : A)
    (hLevels : recoveredData M S I₁ I₂ pHat phi rho gap n a = L)
    (heq : ∀ c x, binComponent L (oracle n a) c x =
      binComponent _ (eHat n a) c x) (o : Obs X Z) :
    fittedBinScore M S I₁ I₂ pHat phi dphi rho gap eHat n a o =
      psiBin M phi dphi L hK o (rearrangeP1 L (oracle n a)) := by
  have hK' : LevelCountPos (recoveredData M S I₁ I₂ pHat phi rho gap n a).K := by
    rw [hLevels]
    exact hK
  simp only [fittedBinScore, dif_pos hK']
  exact (psiBin_rearrangeP1_eq_of_component_eq_of_level_eq M phi dphi L _ hLevels
    hK hK' (oracle n a) (eHat n a) heq o).symm

-- @node: contDMLRegime_oracle_regular_on_recovery
/-- For [continuous nuisance records fitted on the recovered levels](hyp:eHat), under [the finite continuous DML regime](hyp:hr), if [the recovered level
data equal the fixed level data at the given sample size and realization](hyp:hLevels)
and [the oracle's encoded components equal those of the fitted continuous
record at every covariate value](hyp:heq), then [the normalized oracle record
satisfies clipping, simplex shares, and denominator clipping at the regime's
threshold](goal). -/
lemma contDMLRegime_oracle_regular_on_recovery
    (M : LatentIVModel Ω X Z) {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (pHat : ℕ → A → Z → X → ℝ) (phi : Z → X → ℝ → ℝ)
    (rho : ℕ → ℝ) (gap cpi : ℝ) (L : LevelData Z X) (ch : ℝ)
    (eHat : ∀ n a, NuisanceCont (recoveredData M S I₁ I₂ pHat phi rho gap n a))
    (hr : FiniteContDMLRegime M μ S I₁ I₂ pHat phi rho gap cpi L ch eHat)
    (oracle : ℕ → A → NuisanceCont L) (n : ℕ) (a : A)
    (hLevels : recoveredData M S I₁ I₂ pHat phi rho gap n a = L)
    (heq : ∀ c x, contComponent M L (oracle n a) c x =
      contComponent M _ (eHat n a) c x) :
    ContClipping M L (normalizeContAuxiliaryFits L (oracle n a)) ∧
      ContFittedSharesSimplex L (normalizeContAuxiliaryFits L (oracle n a)) ∧
      ContDenominatorsClipped L (normalizeContAuxiliaryFits L (oracle n a)) cpi := by
  have hfit := hr.1.2.2.1.2.2.2.1 n a
  exact continuous_regularity_of_component_eq_of_level_eq M L _ hLevels
    (oracle n a) (eHat n a) cpi heq hfit.1 hfit.2.2.2 hfit.2.2.1

-- @node: binDMLRegime_oracle_regular_on_recovery
/-- For [binary nuisance records fitted on the recovered levels](hyp:eHat), under [the finite binary DML regime](hyp:hr), if [the recovered level
data equal the fixed level data at the given sample size and realization](hyp:hLevels)
and [the oracle's encoded components equal those of the fitted binary
record at every covariate value](hyp:heq), then [the oracle record with
off-support shares set to zero satisfies clipping, simplex shares, and
denominator clipping at the regime's threshold](goal). -/
lemma binDMLRegime_oracle_regular_on_recovery
    (M : LatentIVModel Ω X Z) {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (pHat : ℕ → A → Z → X → ℝ) (phi : Z → X → ℝ → ℝ)
    (rho : ℕ → ℝ) (gap cpi : ℝ) (L : LevelData Z X) (ch : ℝ)
    (eHat : ∀ n a, NuisanceBin (recoveredData M S I₁ I₂ pHat phi rho gap n a))
    (hr : FiniteBinDMLRegime M μ S I₁ I₂ pHat phi rho gap cpi L ch eHat)
    (oracle : ℕ → A → NuisanceBin L) (n : ℕ) (a : A)
    (hLevels : recoveredData M S I₁ I₂ pHat phi rho gap n a = L)
    (heq : ∀ c x, binComponent L (oracle n a) c x =
      binComponent _ (eHat n a) c x) :
    BinClipping L (restrictBinShares L (oracle n a)) ∧
      BinFittedSharesSimplex L (restrictBinShares L (oracle n a)) ∧
      BinDenominatorsClipped L (restrictBinShares L (oracle n a)) cpi := by
  have hfit := hr.1.2.2.2.2.1 n a
  exact binary_regularity_of_component_eq_of_level_eq L _ hLevels
    (oracle n a) (eHat n a) cpi heq hfit.2.1 hfit.2.2.2 hfit.2.2.1

end Papers.TbsPrteOptimalTransport

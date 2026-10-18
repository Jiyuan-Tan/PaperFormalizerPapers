module
public import Papers.TbsPrteOptimalTransport.Helpers.Orthogonality
/-! Bridge from the encoded binary fitting assumptions to the oracle nuisance carrier.
Shares outside their policy set are irrelevant to both the score and the encoded rates.
Setting them to zero supplies the support convention used by binary admissibility. -/
@[expose] public section
set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Set Filter
open scoped Classical

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]

-- @node: restrictBinShares
/-- For [policy level data](hyp:L) and [a binary nuisance record](hyp:e), the
[restricted binary nuisance record](goal) retains every component except that
each instrument share is set to zero outside its corresponding policy set. -/
noncomputable def restrictBinShares (L : LevelData Z X) (e : NuisanceBin L) : NuisanceBin L :=
  { e with
    share := fun a z x => if z ∈ L.T a.val.1 a.val.2 then e.share a z x else 0 }

-- @node: binComponent_restrictBinShares
/-- [Setting shares to zero outside their policy sets leaves every encoded
binary nuisance component unchanged at every covariate value](goal). -/
lemma binComponent_restrictBinShares (L : LevelData Z X) (e : NuisanceBin L)
    (c : ℕ × ℕ × ℕ × Z) (x : X) :
    binComponent L (restrictBinShares L e) c x = binComponent L e c x := by
  rcases c with ⟨code, k, j, z⟩
  simp only [binComponent, restrictBinShares]
  split <;> try rfl
  split
  · split <;> rfl
  · rfl

-- @node: pooledQBin_restrictBinShares
/-- [Setting shares to zero outside their policy sets leaves the pooled binary
policy quantity unchanged at every level, policy index, and covariate value](goal). -/
lemma pooledQBin_restrictBinShares (phi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (e : NuisanceBin L) (k j : ℕ) (x : X) :
    pooledQBin phi L (restrictBinShares L e) k j x = pooledQBin phi L e k j x := by
  unfold pooledQBin
  split
  · rfl
  · split
    · rfl
    · apply Finset.sum_congr rfl
      intro z hz
      simp only [restrictBinShares]
      split
      · rfl
      · rfl

-- @node: psiBin_restrictBinShares
/-- With [a positive number of policy levels](hyp:hK), [setting shares to zero
outside their policy sets leaves the binary score unchanged at each observation](goal). -/
lemma psiBin_restrictBinShares (M : LatentIVModel Ω X Z)
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (hK : LevelCountPos L.K) (o : Obs X Z) (e : NuisanceBin L) :
    psiBin M phi dphi L hK o (restrictBinShares L e) = psiBin M phi dphi L hK o e := by
  simp only [psiBin, psiFullProdBin, psiProdBin, binScoreComponents, hMinus,
    Dbd, Edom, Iact, pooledQBin_restrictBinShares]
  rfl

-- @node: rearrangeP1_restrictBinShares
/-- [Rearranging the binary success probabilities and setting shares to zero
outside their policy sets give the same nuisance record regardless of the order
of these two operations](goal). -/
lemma rearrangeP1_restrictBinShares (L : LevelData Z X) (e : NuisanceBin L) :
    rearrangeP1 L (restrictBinShares L e) = restrictBinShares L (rearrangeP1 L e) := by
  rfl

-- @node: restrictBinShares_eq_of_admissible
/-- If [a binary nuisance record is admissible](hyp:he), then [setting shares
to zero outside their policy sets preserves all its shares simultaneously for
almost every covariate value](goal). -/
lemma restrictBinShares_eq_of_admissible (M : LatentIVModel Ω X Z)
    (L : LevelData Z X) (e : NuisanceBin L) (he : BinAdmissible M L e) :
    ∀ᵐ x ∂xLaw M, ∀ a z, (restrictBinShares L e).share a z x = e.share a z x := by
  have hs := ae_all_iff.mpr he.2.2.2.2.2.2.2.2.1
  filter_upwards [hs] with x hx
  intro a z
  by_cases hz : z ∈ L.T a.val.1 a.val.2
  · simp only [restrictBinShares, if_pos hz]
  · simp only [restrictBinShares, if_neg hz, (hx a).2 z hz]

-- @node: restrictBinShares_admissible_of_encoded_clipping
/-- If [a binary nuisance record satisfies the clipping restrictions](hyp:hc),
[its fitted shares satisfy the simplex restrictions](hyp:hs), and [every encoded
component is measurable](hyp:hm), then [setting its shares to zero outside their
policy sets produces an admissible binary nuisance record](goal). -/
lemma restrictBinShares_admissible_of_encoded_clipping (M : LatentIVModel Ω X Z)
    (L : LevelData Z X) (e : NuisanceBin L)
    (hc : BinClipping L e) (hs : BinFittedSharesSimplex L e)
    (hm : ∀ c, Measurable (binComponent L e c)) :
    BinAdmissible M L (restrictBinShares L e) := by
  have hfull := binClipping_full_range L e hc
  obtain ⟨hprop, hlev, hreg, hshare, htail, hop⟩ := hc
  let z₀ : Z := Classical.choice inferInstance
  have hp (z : Z) : Measurable (e.prop z) := by
    first | fun_prop | simpa only [binComponent] using (show Measurable (fun x => binComponent L e (0, 0, 0, z) x) from hm (0, 0, 0, z))
  have hl (k : PositiveIndex L.K) :
      Measurable (e.pLev k) ∧ Measurable (e.P1 k) ∧ Measurable (e.piLev k) := by
    refine ⟨?_, ?_, ?_⟩
    · first | fun_prop | simpa [binComponent, positiveValue, k.property] using (show Measurable (fun x => binComponent L e (1, k, 0, z₀) x) from hm (1, k, 0, z₀))
    · first | fun_prop | simpa [binComponent, positiveValue, k.property] using (show Measurable (fun x => binComponent L e (2, k, 0, z₀) x) from hm (2, k, 0, z₀))
    · first | fun_prop | simpa [binComponent, positiveValue, k.property] using (show Measurable (fun x => binComponent L e (3, k, 0, z₀) x) from hm (3, k, 0, z₀))
  have hr (a : RegularIndex L) : Measurable (e.tauLev a) ∧ Measurable (e.gamma a) := by
    refine ⟨?_, ?_⟩
    · first | fun_prop | simpa [binComponent, regularValue, a.property] using (show Measurable (fun x => binComponent L e (4, a.val.1, a.val.2, z₀) x) from hm (4, a.val.1, a.val.2, z₀))
    · first | fun_prop | simpa [binComponent, regularValue, a.property] using (show Measurable (fun x => binComponent L e (7, a.val.1, a.val.2, z₀) x) from hm (7, a.val.1, a.val.2, z₀))
  have hms (a : RegularIndex L) (z : Z) :
      Measurable ((restrictBinShares L e).share a z) := by
    first | fun_prop | simpa [binComponent, restrictBinShares, a.property] using (show Measurable (fun x => binComponent L e (5, a.val.1, a.val.2, z) x) from hm (5, a.val.1, a.val.2, z))
  have hmf (k : Fin L.K) : Measurable (e.gammaFull k) := by
    first | fun_prop | simpa [binComponent, fullValue, k.isLt] using (show Measurable (fun x => binComponent L e (6, k, 0, z₀) x) from hm (6, k, 0, z₀))
  have hmt : Measurable e.gammaTail := by
    first | fun_prop | simpa only [binComponent] using (show Measurable (fun x => binComponent L e (8, 0, 0, z₀) x) from hm (8, 0, 0, z₀))
  refine ⟨fun z => Eventually.of_forall (hprop z), hp,
    fun k => Eventually.of_forall (hlev k), hl,
    fun a => Eventually.of_forall (hreg a), hr, ?_, hms, ?_, ?_, hmf,
    Eventually.of_forall htail, hmt⟩
  · intro a z
    apply Eventually.of_forall
    intro x
    by_cases hz : z ∈ L.T a.val.1 a.val.2
    · simpa only [restrictBinShares, if_pos hz] using hshare a z x
    · simp [restrictBinShares, hz]
  · intro a
    apply Eventually.of_forall
    intro x
    refine ⟨?_, ?_⟩
    · simpa only [restrictBinShares, Finset.sum_ite_mem, Finset.inter_self] using (hs a x).2
    · intro z hz
      simp only [restrictBinShares, if_neg hz]
  · intro k
    apply Eventually.of_forall
    intro x
    exact hfull k x

-- @node: nuisanceRates_of_encoded_coordinate
/-- Suppose [each encoded nuisance coordinate has root integrated squared error,
at twice the sample index plus two, of smaller order in probability than the
inverse fourth root of that index](hyp:hr). If [each new fitted coordinate equals the
encoded fitted coordinate selected by a fixed coding map](hyp:hf) and [each new
true coordinate equals the corresponding encoded true coordinate](hyp:hg), then
[each new coordinate has the same rate for its root integrated squared error](goal). -/
lemma nuisanceRates_of_encoded_coordinate (M : LatentIVModel Ω X Z)
    {A C D : Type*} [MeasurableSpace A] (μ : Measure A)
    (fit : ℕ → A → C → X → ℝ) (truth : C → X → ℝ)
    (hr : FiniteNuisanceRates M μ fit truth) (code : D → C)
    (f : ℕ → A → D → X → ℝ) (g : D → X → ℝ)
    (hf : ∀ n a d x, f n a d x = fit n a (code d) x)
    (hg : ∀ d x, g d x = truth (code d) x) :
    FiniteNuisanceRates M μ f g := by
  intro d
  have hfit (n : ℕ) (a : A) : f n a d = fit n a (code d) := by
    funext x
    exact hf n a d x
  have htruth : g d = truth (code d) := by
    funext x
    exact hg d x
  simpa only [hfit, htruth] using hr (code d)

-- All indexed rates used by the oracle score follow from the single rate
-- family in FiniteBinDMLRegime. Restricting shares preserves that family exactly.
-- @node: binary_component_rates_to_oracle_rates
/-- If [each encoded binary nuisance component has root integrated squared error
relative to the true record, at twice the sample index plus two, of smaller order
in probability than the inverse fourth root of that index](hyp:hr), then [the
same rates hold separately for the propensity scores, positive baseline levels,
success regressions, baseline set probabilities, policy set probabilities,
policy-supported shares at every regular index, full-interval weights, policy
weights, and tail weight](goal). -/
lemma binary_component_rates_to_oracle_rates (M : LatentIVModel Ω X Z)
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (L : LevelData Z X) (eh : ℕ → A → NuisanceBin L) (e0 : NuisanceBin L)
    (hr : FiniteNuisanceRates M μ (fun n a => binComponent L (eh n a)) (binComponent L e0)) :
    FiniteNuisanceRates M μ (fun n a => (eh n a).prop) e0.prop ∧
    FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev ∧
    FiniteNuisanceRates M μ (fun n a => (eh n a).P1) e0.P1 ∧
    FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) e0.piLev ∧
    FiniteNuisanceRates M μ (fun n a => (eh n a).tauLev) e0.tauLev ∧
    (∀ t, FiniteNuisanceRates M μ (fun n a => (restrictBinShares L (eh n a)).share t)
      ((restrictBinShares L e0).share t)) ∧
    FiniteNuisanceRates M μ (fun n a => (eh n a).gammaFull) e0.gammaFull ∧
    FiniteNuisanceRates M μ (fun n a => (eh n a).gamma) e0.gamma ∧
    FiniteNuisanceRates M μ (fun n a (_ : Unit) => (eh n a).gammaTail)
      (fun _ => e0.gammaTail) := by
  let z₀ : Z := Classical.choice inferInstance
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply nuisanceRates_of_encoded_coordinate M μ _ _ hr (fun z => (0, 0, 0, z))
    · intro n a z x; rfl
    · intro z x; rfl
  · apply nuisanceRates_of_encoded_coordinate M μ _ _ hr (fun k : PositiveIndex L.K => (1, k, 0, z₀))
    · intro n a k x; simp [binComponent, positiveValue, k.property]
    · intro k x; simp [binComponent, positiveValue, k.property]
  · apply nuisanceRates_of_encoded_coordinate M μ _ _ hr (fun k : PositiveIndex L.K => (2, k, 0, z₀))
    · intro n a k x; simp [binComponent, positiveValue, k.property]
    · intro k x; simp [binComponent, positiveValue, k.property]
  · apply nuisanceRates_of_encoded_coordinate M μ _ _ hr (fun k : PositiveIndex L.K => (3, k, 0, z₀))
    · intro n a k x; simp [binComponent, positiveValue, k.property]
    · intro k x; simp [binComponent, positiveValue, k.property]
  · apply nuisanceRates_of_encoded_coordinate M μ _ _ hr (fun t : RegularIndex L => (4, t.val.1, t.val.2, z₀))
    · intro n a t x; simp [binComponent, regularValue, t.property]
    · intro t x; simp [binComponent, regularValue, t.property]
  · intro t
    apply nuisanceRates_of_encoded_coordinate M μ _ _ hr (fun z => (5, t.val.1, t.val.2, z))
    · intro n a z x; simp [binComponent, restrictBinShares, t.property]
    · intro z x; simp [binComponent, restrictBinShares, t.property]
  · apply nuisanceRates_of_encoded_coordinate M μ _ _ hr (fun k : Fin L.K => (6, k, 0, z₀))
    · intro n a k x; simp [binComponent, fullValue, k.isLt]
    · intro k x; simp [binComponent, fullValue, k.isLt]
  · apply nuisanceRates_of_encoded_coordinate M μ _ _ hr (fun t : RegularIndex L => (7, t.val.1, t.val.2, z₀))
    · intro n a t x; simp [binComponent, regularValue, t.property]
    · intro t x; simp [binComponent, regularValue, t.property]
  · apply nuisanceRates_of_encoded_coordinate M μ _ _ hr (fun _ : Unit => (8, 0, 0, z₀))
    · intro n a t x; rfl
    · intro t x; rfl

end Papers.TbsPrteOptimalTransport

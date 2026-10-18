module
public import Papers.TbsPrteOptimalTransport.Helpers.JQuantileBands
public import Papers.TbsPrteOptimalTransport.Helpers.SharpnessIdentification
/-! Binary support and quantile bands of identified finite-instrument gap laws. -/
public section
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: finite_instrument_ae_sections
/-- Under [common instrument support](hyp:hSupport) and [a finite instrument
space with discrete topology](hyp:hf), if [a property holds for almost every
instrument-covariate pair](hyp:hp), then [for almost every covariate value it
holds at every instrument value](goal). -/
lemma finite_instrument_ae_sections (hSupport : CommonInstrumentSupport M)
    (hf : InstrumentFiniteReduction Z) (P : Z × X → Prop)
    (hp : ∀ᵐ zx ∂zxLaw M, P zx) : ∀ᵐ x ∂xLaw M, ∀ z, P (z, x) := by
  letI : DiscreteTopology Z := hf.2
  letI := M.instKernel_markov
  haveI : IsProbabilityMeasure (xLaw M) := Measure.isProbabilityMeasure_map M.measX.aemeasurable
  have hcomp : ((xLaw M) ⊗ₘ M.instKernel).map Prod.swap = zxLaw M := by
    unfold xLaw
    rw [Measure.compProd_congr M.instKernel_version,
      compProd_map_condDistrib M.measZ.aemeasurable,
      Measure.map_map measurable_swap (M.measX.prodMk M.measZ)]
    rfl
  have hpair : ∀ᵐ xz ∂(xLaw M) ⊗ₘ M.instKernel, P (xz.2, xz.1) := by
    have hp' : ∀ᵐ zx ∂((xLaw M) ⊗ₘ M.instKernel).map Prod.swap, P zx := hcomp ▸ hp
    exact ae_of_ae_map measurable_swap.aemeasurable hp'
  filter_upwards [Measure.ae_ae_of_ae_compProd hpair,
    instrument_singleton_pos M hSupport hf] with x hx hpos
  intro z
  exact ae_iff_of_countable.mp hx z (hpos z).ne'

-- @node: conditional_binary_response_supported
/-- If [observed outcomes are zero or one almost surely](hyp:hb), then [for
almost every instrument-covariate pair, the conditional joint law of the outcome
and treatment assigns zero mass to outcomes outside zero and one](goal). -/
lemma conditional_binary_response_supported (hb : OutcomeBinary M) :
    ∀ᵐ zx ∂zxLaw M,
      condDistrib (fun s => (M.Y s, M.W s)) (fun s => (M.Zv s, M.Xv s))
        M.law.toMeasure zx {yw | yw.1 ∉ ({0, 1} : Set ℝ)} = 0 := by
  have hmeas : Measurable (fun s => (M.Y s, M.W s)) := M.measY.prodMk M.measW
  have hset : MeasurableSet {yw : ℝ × ℝ | yw.1 ∈ ({0, 1} : Set ℝ)} := by
    exact (measurableSet_singleton (0 : ℝ) |>.union (measurableSet_singleton 1)).preimage
      measurable_fst
  have hj : ∀ᵐ a ∂M.law.toMeasure.map
      (fun s => ((M.Zv s, M.Xv s), (M.Y s, M.W s))),
      a.2.1 ∈ ({0, 1} : Set ℝ) := by
    apply (ae_map_iff ((M.measZ.prodMk M.measX).prodMk hmeas).aemeasurable
      (hset.preimage measurable_snd)).mpr
    simpa only [OutcomeBinary, mem_insert_iff, mem_singleton_iff, mem_ofPred_eq] using hb
  rw [← compProd_map_condDistrib hmeas.aemeasurable] at hj
  exact (Measure.ae_ae_of_ae_compProd hj).mono fun zx hx => ae_iff.mp hx

-- @node: positive_baseline_level_attained
/-- Under [invariant ordering of baseline and policy levels](hyp:hL), if
[the baseline index is at least one](hyp:hi) and [no greater than the number
of baseline gaps](hyp:hiK), then [at any covariate value some instrument attains
that indexed baseline propensity level](goal). -/
lemma positive_baseline_level_attained (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (x : X) (i : ℕ)
    (hi : 1 ≤ i) (hiK : i ≤ L.K) : ∃ z, M.prop z x = L.pLev i x := by
  have hlen := hL.2.2.2.1 x
  have hidx : i - 1 < (finiteLevels (fun z => M.prop z x)).length := by
    rw [hlen]
    omega
  have hm : (finiteLevels (fun z => M.prop z x)).getD (i-1) 0 ∈
      finiteLevels (fun z => M.prop z x) := by
    rw [List.getD_eq_getElem _ _ hidx]
    exact List.getElem_mem hidx
  obtain ⟨z, hz⟩ := (finiteLevels_mem (fun z => M.prop z x) (inferInstance : Finite Z) hm).1
  refine ⟨z, ?_⟩
  rw [hL.1 x i (by omega), pLevel, if_neg (by omega), if_pos (by omega)]
  exact hz

-- @node: discrete_gap_law_binary_supported
/-- Under [the structural assumptions](hyp:h), [a finite instrument space with
discrete topology](hyp:hf), [almost surely binary observed outcomes](hyp:hb),
and [invariant ordering of baseline and policy levels](hyp:hL), [for almost
every covariate value, every valid identified gap law assigns zero mass outside
the outcomes zero and one](goal). -/
lemma discrete_gap_law_binary_supported (h : StructuralAssumptions M)
    (hf : InstrumentFiniteReduction Z) (hb : OutcomeBinary M)
    (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) :
    ∀ᵐ x ∂xLaw M, ∀ k < L.K, discreteGapLaw M L k x ({0, 1} : Set ℝ)ᶜ = 0 := by
  have hslice := sharpness_canonical_instrument_slice M h.2.1 h.2.2.1
    h.2.2.2.2.1 h.2.2.2.1.2.1 h.2.2.2.1.1 true
  have hnull : ∀ᵐ zx ∂zxLaw M,
      canonSubmeasure M true zx.2 (M.prop zx.1 zx.2) ({0, 1} : Set ℝ)ᶜ = 0 := by
    filter_upwards [hslice, conditional_binary_response_supported M hb] with zx hx hn
    have hB : MeasurableSet ({0, 1} : Set ℝ)ᶜ :=
      (measurableSet_singleton (0 : ℝ) |>.union (measurableSet_singleton 1)).compl
    rw [hx, Measure.map_apply measurable_fst hB,
      Measure.restrict_apply (hB.preimage measurable_fst)]
    exact measure_mono_null inter_subset_left hn
  filter_upwards [finite_instrument_ae_sections M h.2.2.2.2.2.1 hf _ hnull] with x hx
  intro k hk
  obtain ⟨z, hz⟩ := positive_baseline_level_attained M q L hL x (k+1) (by omega) (by omega)
  have hn := hx z
  rw [hz] at hn
  rw [discreteGapLaw, Measure.smul_apply]
  have hsub : (canonSubmeasure M true x (L.pLev (k+1) x) -
      canonSubmeasure M true x (L.pLev k x)) ({0, 1} : Set ℝ)ᶜ = 0 :=
    le_zero_iff.mp ((Measure.sub_le _).trans_eq hn)
  rw [hsub, smul_zero]

-- @node: binary_band_affine_rescaling
/-- If [the lower baseline level is strictly below the upper baseline level](hyp:hab),
then [multiplying the positive part of the normalized upper policy rank minus
the larger of the normalized lower policy rank and one minus the binary success
probability by the baseline gap width equals the positive part of the upper
policy level minus the larger of the lower policy level and the upper baseline
level minus the gap width times the success probability](goal). -/
lemma binary_band_affine_rescaling (a b c d m : ℝ) (hab : a < b) :
    (b-a) * max 0 ((d-a)/(b-a) - max ((c-a)/(b-a)) (1-m)) =
      max 0 (d - max c (b - (b-a)*m)) := by
  have hw : 0 < b-a := sub_pos.mpr hab
  rw [mul_max_of_nonneg _ _ hw.le, mul_zero, mul_sub,
    mul_max_of_nonneg _ _ hw.le,
    mul_div_cancel₀ _ hw.ne', mul_div_cancel₀ _ hw.ne']
  have ht : (b-a) * (1-m) = (b-(b-a)*m)-a := by ring
  rw [ht, max_sub_sub_right]
  congr 1
  ring

-- @node: binary_discrete_Jband
/-- Under [the structural assumptions](hyp:h), [a finite instrument space with
discrete topology](hyp:hf), [almost surely binary observed outcomes](hyp:hb),
and [invariant ordering of baseline and policy levels](hyp:hL), for [a gap index
below the number of baseline gaps](hyp:hk), [a boundary index at least one](hyp:hj0)
and [within that gap's policy subdivision](hyp:hj), [almost everywhere in
covariates, the outcome quantile integral over the preceding policy band equals
the positive part of the upper policy level minus the larger of the lower
policy level and the upper baseline propensity minus the full-gap outcome
integral](goal). -/
lemma binary_discrete_Jband (h : StructuralAssumptions M)
    (hf : InstrumentFiniteReduction Z) (hb : OutcomeBinary M)
    (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (k j : ℕ)
    (hk : k < L.K) (hj0 : 1 ≤ j) (hj : j ≤ L.l k) :
    ∀ᵐ x ∂xLaw M, Jband M false L k (j-1) x =
      max 0 (L.qLev k j x - max (L.qLev k (j-1) x)
        (L.pLev (k+1) x - Jfull M L k x)) := by
  filter_upwards [discrete_gap_law_binary_supported M h hf hb q L hL] with x hx
  letI := discrete_gap_law_probability M M.prop q L hL k hk x
  have hinputs := hL.2.2.2.2.2.2.2.2.2.1
  have hr := (canonical_level_ranges M.prop q L (fun z x => (hinputs z x).1)
    (fun z x => (hinputs z x).2) hL).2.2
  have he := binary_law_quantile_band_integral (discreteGapLaw M L k x) (hx k hk)
    (kappa L k (j-1) x) (kappa L k j x)
    (hr x k (j-1) hk (by omega)).1 (hr x k j hk (by omega)).2
  unfold Jband
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.sub_add_cancel hj0]
  rw [integral_congr_ae ((level_gap_quantile_ae M L k x).restrict), he]
  exact binary_band_affine_rescaling _ _ _ _ _
    (hL.2.2.2.2.2.2.2.1 x k (k+1) (by omega) (by omega))

end Papers.TbsPrteOptimalTransport

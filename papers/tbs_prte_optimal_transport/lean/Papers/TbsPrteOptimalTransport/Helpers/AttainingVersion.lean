module
public import Papers.TbsPrteOptimalTransport.Helpers.RegionPartition
/-! A supported measurable version of the pasted attaining law. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.style.openClassical false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology ENNReal

-- @node: measurable_kernel_Iic_mass
/-- If [a threshold varies measurably with the conditioning value](hyp:hv),
[the probability assigned by a Markov kernel to outcomes at or below that threshold is measurable](goal). -/
@[fun_prop] lemma measurable_kernel_Iic_mass {B : Type*} [MeasurableSpace B]
    (K : Kernel B ℝ) [IsMarkovKernel K] (v : B → ℝ) (hv : Measurable v) :
    Measurable (fun b => (K b (Iic (v b))).toReal) := by
  apply Measurable.ennreal_toReal
  apply Kernel.measurable_kernel_prodMk_left
    (t := {br : B × ℝ | br.2 ≤ v br.1})
  exact measurableSet_le measurable_snd (hv.comp measurable_fst)

-- @node: measurable_kernel_Iio_mass
/-- If [a threshold varies measurably with the conditioning value](hyp:hv),
[the probability assigned by a Markov kernel to outcomes strictly below that threshold is measurable](goal). -/
@[fun_prop] lemma measurable_kernel_Iio_mass {B : Type*} [MeasurableSpace B]
    (K : Kernel B ℝ) [IsMarkovKernel K] (v : B → ℝ) (hv : Measurable v) :
    Measurable (fun b => (K b (Iio (v b))).toReal) := by
  apply Measurable.ennreal_toReal
  apply Kernel.measurable_kernel_prodMk_left
    (t := {br : B × ℝ | br.2 < v br.1})
  exact measurableSet_lt measurable_snd (hv.comp measurable_fst)

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z]
variable (M : LatentIVModel Ω X Z)

-- @node: measurable_gap_attaining_family
/-- Under [the structural assumptions](hyp:h), [propensity continuity on instrument components](hyp:hc),
and [finitely many instrument components](hyp:hfin), suppose [the target weight is measurable](hyp:hm),
[the quantile extension is jointly measurable, outcome-supported, and agrees with the gap quantiles on interior ranks](hyp:hQ),
and [the proposed decomposition has measurable gap endpoints](hyp:hend) and
[equals the conditional range decomposition almost everywhere](hyp:hD).
Then [there exists a family of Markov kernels, one per gap index, agreeing with the gap attaining laws at every unit-interval rank on each nonempty gap for almost every covariate value](goal). -/
lemma measurable_gap_attaining_family (h : StructuralAssumptions M)
    (hc : PropensityContinuousOnComponents M) (hfin : FiniteInstrumentComponents Z)
    (om : X → ℝ → ℝ) (hm : TargetWeightMeasurable om)
    (Q : X → ℕ → ℝ → ℝ) (hQ : RankKernelExtensionReading M Q)
    (D : X → RangeData)
    (hend : ∀ k, Measurable (fun x => (D x).gapLo k) ∧
      Measurable (fun x => (D x).gapHi k))
    (hD : D =ᵐ[xLaw M] CondRangeDecomposition M) :
    ∃ G : ℕ → Kernel (ℝ × X) ℝ, (∀ k, IsMarkovKernel (G k)) ∧
      ∀ᵐ x ∂xLaw M, ∀ k < (CondRangeDecomposition M x).count,
        (CondRangeDecomposition M x).gapLo k < (CondRangeDecomposition M x).gapHi k →
        ∀ u ∈ Icc (0 : ℝ) 1, G k (u, x) = gapAttainingLaw M om Q x k u := by
  let w : ℝ × X → ℝ := fun ux => om ux.2 (min 1 (max 0 ux.1))
  have hw : Measurable w := by
    exact hm.comp (measurable_snd.prodMk
      ((measurable_const.min (measurable_const.max measurable_fst)).subtype_mk
        (h := fun ux => ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩)))
  have hwu {u : ℝ} (x : X) (hu : u ∈ Icc (0 : ℝ) 1) : w (u, x) = om x u := by
    simp only [w, max_eq_right hu.1, min_eq_right hu.2]
  -- Normalize the uniform restriction to each measurable gap, then map its weights.
  let K := (Kernel.deterministic (fun ux : ℝ × X => w ux) hw)
  letI : IsMarkovKernel K := inferInstance
  choose L hL hLeq using fun k => exists_normalized_interval_kernel K
    (fun x => max 0 ((D x).gapLo k)) (fun x => min 1 ((D x).gapHi k))
    (measurable_const.max (hend k).1) (measurable_const.min (hend k).2) 0
  let R (k : ℕ) (ux : ℝ × X) (s : ℝ) :=
    (L k ux.2 (Iio (w ux))).toReal + s *
      ((L k ux.2 (Iic (w ux))).toReal - (L k ux.2 (Iio (w ux))).toReal)
  have hR (k : ℕ) : Measurable (fun uxs : (ℝ × X) × ℝ => R k uxs.1 uxs.2) := by
    letI := hL k
    have hh := measurable_kernel_Iic_mass ((L k).comap Prod.snd measurable_snd) w hw
    have hl := measurable_kernel_Iio_mass ((L k).comap Prod.snd measurable_snd) w hw
    dsimp only [R]
    exact (hl.comp measurable_fst).add (measurable_snd.mul
      ((hh.comp measurable_fst).sub (hl.comp measurable_fst)))
  have hmap (k : ℕ) : Measurable (fun uxs : (ℝ × X) × ℝ =>
      Q uxs.1.2 k (1 - R k uxs.1 uxs.2)) := by
    exact hQ.1.comp (measurable_fst.snd.prodMk
      (measurable_const.prodMk (measurable_const.sub (hR k))))
  let G (k : ℕ) : Kernel (ℝ × X) ℝ :=
    ⟨fun ux => Causalean.Stat.unifOI.map
      (fun s => Q ux.2 k (1 - R k ux s)), by
      have hh := (Measure.measurable_map _ (hmap k)).comp
        (Measurable.map_prodMk_left (ν := Causalean.Stat.unifOI) (α := ℝ × X))
      simpa only [Measure.map_map (hmap k) measurable_prodMk_left, Function.comp_def] using hh⟩
  refine ⟨G, fun k => ?_, ?_⟩
  · constructor
    intro ux
    exact Measure.isProbabilityMeasure_map
      ((hmap k).comp (measurable_const.prodMk measurable_id)).aemeasurable
  · filter_upwards [hD] with x hx
    intro k hk hab u hu
    have he := conditional_gap_endpoints M x k hk
    have hLe : L k x = weightLaw M om x k := by
      rw [hLeq]
      simp only [hx, max_eq_right he.1.1, min_eq_right he.2.2, if_pos hab]
      rw [weightLaw, gapUnif, uniformInterval, Measure.map_smul]
      congr 1
      rw [restrict_Ioo_eq_restrict_Ioc]
      let Kx := K.comap (fun t : ℝ => (t, x)) (by fun_prop)
      change (volume.restrict (Ioc _ _)).bind Kx = _
      change (volume.restrict (Ioc _ _)).bind (fun t => Measure.dirac (w (t, x))) = _
      have ht : Measurable (fun t : ℝ => w (t, x)) :=
        hw.comp (measurable_id.prodMk (measurable_const (a := x)))
      rw [Measure.bind_dirac_eq_map _ ht]
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact hwu x ⟨he.1.1.trans ht.1.le, ht.2.trans he.2.2⟩
    change Causalean.Stat.unifOI.map _ = _
    unfold gapAttainingLaw
    congr 1
    funext s
    congr 1
    dsimp only [R]
    rw [hLe, hwu x hu]
    rfl

-- @node: measurable_pasted_attaining_version
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
[propensity continuity on instrument components](hyp:hc), and [finitely many instrument components](hyp:hfin),
if [the target weight is measurable](hyp:hm) and
[the quantile extension is jointly measurable, outcome-supported, and agrees with the gap quantiles on interior ranks](hyp:hQ),
[there exists a Markov kernel agreeing with the pasted attaining law at every unit-interval rank for almost every covariate value](goal). -/
lemma measurable_pasted_attaining_version (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) (hc : PropensityContinuousOnComponents M)
    (hfin : FiniteInstrumentComponents Z) (om : X → ℝ → ℝ)
    (hm : TargetWeightMeasurable om) (Q : X → ℕ → ℝ → ℝ)
    (hQ : RankKernelExtensionReading M Q) :
    ∃ H : Kernel (ℝ × X) ℝ, IsMarkovKernel H ∧
      ∀ᵐ x ∂xLaw M, ∀ u ∈ Icc (0 : ℝ) 1,
        H (u, x) = pastedAttainingLaw M om Q x u := by
  classical
  obtain ⟨D, hcount, hend, hD⟩ := measurable_ordered_gap_law_version M h hc hfin
  obtain ⟨G, hG, hGeq⟩ := measurable_gap_attaining_family M h hc hfin om hm Q hQ D hend hD
  let w : ℝ × X → ℝ := fun ux => om ux.2 (min 1 (max 0 ux.1))
  have hw : Measurable w := by
    exact hm.comp (measurable_snd.prodMk
      ((measurable_const.min (measurable_const.max measurable_fst)).subtype_mk
        (h := fun ux => ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩)))
  have htail : Measurable (fun x => (D x).tailLo) := by
    have hends : Measurable (fun xk : X × ℕ => (D xk.1).gapLo xk.2) :=
      measurable_from_prod_countable_left fun k => (hend k).1
    have hcomp := hends.comp (measurable_id.prodMk hcount)
    convert hcomp using 1
    funext x
    by_cases hx : (D x).count = 0
    · simp only [Function.comp_def, id_eq, RangeData.tailLo, hx, if_true, RangeData.gapLo]
    · simp only [Function.comp_def, id_eq, RangeData.tailLo, hx, if_false, RangeData.gapLo]
  let F : ℝ × X → Measure ℝ := fun ux =>
    if ux.1 ∈ (D ux.2).tail then
      Measure.dirac (if 0 ≤ w ux then M.yMin else M.yMax)
    else outcomeKernel (latentMarginal M true) ux
  have hF : Measurable F := by
    have ht : MeasurableSet {ux : ℝ × X | ux.1 ∈ (D ux.2).tail} :=
      (measurableSet_lt (htail.comp measurable_snd) measurable_fst).inter
        (measurableSet_le measurable_fst measurable_const)
    have hy : Measurable (fun ux => if 0 ≤ w ux then M.yMin else M.yMax) :=
      Measurable.ite (measurableSet_le measurable_const hw) measurable_const measurable_const
    exact (Measure.measurable_dirac.comp hy).ite ht (Kernel.measurable _)
  have hFp (ux : ℝ × X) : IsProbabilityMeasure (F ux) := by
    dsimp only [F]
    split_ifs
    · infer_instance
    · infer_instance
    · exact (outcomeKernel_isMarkov (latentMarginal M true)).isProbabilityMeasure ux
  let good (k : ℕ) (ux : ℝ × X) :=
    k < (D ux.2).count ∧ ux.1 ∈ RangeDecomposition.gap (D ux.2) k
  have hgood (k : ℕ) : MeasurableSet {ux | good k ux} := by
    exact (measurableSet_lt measurable_const (hcount.comp measurable_snd)).inter
      (((measurableSet_lt ((hend k).1.comp measurable_snd) measurable_fst).inter
        (measurableSet_lt measurable_fst ((hend k).2.comp measurable_snd))).inter
        (measurableSet_Icc.preimage measurable_fst))
  let p (k : ℕ) (ux : ℝ × X) := good k ux ∨ (k = 0 ∧ ¬ ∃ j, good j ux)
  have hp (k : ℕ) : MeasurableSet {ux | p k ux} := by
    have hex : MeasurableSet {ux | ∃ j, good j ux} := by
      rw [ofPred_exists]
      exact MeasurableSet.iUnion hgood
    change MeasurableSet {ux | good k ux ∨ (k = 0 ∧ ¬ ∃ j, good j ux)}
    rw [ofPred_or, ofPred_and]
    apply (hgood k).union
    apply MeasurableSet.inter _ hex.compl
    by_cases hk : k = 0
    · have heq : (fun _ : ℝ × X => k = 0) = (Set.univ : Set (ℝ × X)) := by
        funext ux
        exact propext ⟨fun _ => trivial, fun _ => hk⟩
      rw [heq]
      exact MeasurableSet.univ
    · have heq : (fun _ : ℝ × X => k = 0) = (∅ : Set (ℝ × X)) := by
        funext ux
        exact propext ⟨fun h => (hk h).elim, fun h => h.elim⟩
      rw [heq]
      exact MeasurableSet.empty
  have hpExists (ux : ℝ × X) : ∃ k, p k ux := by
    by_cases hx : ∃ k, good k ux
    · obtain ⟨k, hk⟩ := hx
      exact ⟨k, Or.inl hk⟩
    · exact ⟨0, Or.inr ⟨rfl, hx⟩⟩
  let V (k : ℕ) (ux : ℝ × X) := if good k ux then G k ux else F ux
  have hV (k : ℕ) : Measurable (V k) := (G k).measurable.ite (hgood k) hF
  let H : Kernel (ℝ × X) ℝ :=
    ⟨fun ux => V (Nat.find (hpExists ux)) ux, Measurable.find hV hp hpExists⟩
  have hHp : IsMarkovKernel H := by
    constructor
    intro ux
    change IsProbabilityMeasure (V (Nat.find (hpExists ux)) ux)
    dsimp only [V]
    split_ifs
    · exact (hG _).isProbabilityMeasure ux
    · exact hFp ux
  refine ⟨H, hHp, ?_⟩
  filter_upwards [hD, hGeq, range_decomposition_valid M h hfin hc] with x hx hgx hv
  intro u hu
  by_cases hex : ∃ k, good k (u, x)
  · have hn : good (Nat.find (hpExists (u, x))) (u, x) := by
      rcases Nat.find_spec (hpExists (u, x)) with hn | hn
      · exact hn
      · exact False.elim (hn.2 hex)
    let j := Nat.find (hpExists (u, x))
    change good j (u, x) at hn
    have hk := hn.1
    have hmem := hn.2
    dsimp only [good] at hk hmem
    rw [hx] at hk hmem
    have hab : (CondRangeDecomposition M x).gapLo j <
        (CondRangeDecomposition M x).gapHi j := hmem.1.1.trans hmem.1.2
    change V j (u, x) = _
    dsimp only [V]
    rw [if_pos hn, hgx _ hk hab u hu]
    exact (pasted_attaining_law_on_gap M om Q x hv _ hk u hmem).symm
  · have hn : ¬ good (Nat.find (hpExists (u, x))) (u, x) := fun hn => hex ⟨_, hn⟩
    have hex' : ¬ ∃ k, k < (CondRangeDecomposition M x).count ∧
        u ∈ RangeDecomposition.gap (CondRangeDecomposition M x) k := by
      simpa only [good, hx] using hex
    change V (Nat.find (hpExists (u, x))) (u, x) = _
    dsimp only [V]
    rw [if_neg hn]
    dsimp only [F]
    rw [hx]
    simp only [w, max_eq_right hu.1, min_eq_right hu.2]
    unfold pastedAttainingLaw
    rw [dif_neg hex']

-- @node: exists_attaining_kernel_version
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
[measurability of the target weight](hyp:hm), [propensity continuity on instrument components](hyp:hc),
[finitely many instrument components](hyp:hfin), and
[a jointly measurable, outcome-supported extension agreeing with the gap quantiles on interior ranks](hyp:hQ),
[there exists a measurable Markov kernel supported on the outcome domain everywhere, agreeing almost everywhere with the pasted attaining law and, for almost every covariate value, with each attaining law throughout its gap](goal). -/
lemma exists_attaining_kernel_version (om : X → ℝ → ℝ) (Q : X → ℕ → ℝ → ℝ)
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (hm : TargetWeightMeasurable om) (hc : PropensityContinuousOnComponents M)
    (hfin : FiniteInstrumentComponents Z) (hQ : RankKernelExtensionReading M Q) :
    ∃ K : Kernel (ℝ × X) ℝ, IsAttainingKernelVersion M om Q K  := by
  classical
  obtain ⟨H, hH, hHeq⟩ := measurable_pasted_attaining_version M h he hc hfin om hm Q hQ
  letI := hH
  have hY : MeasurableSet M.Yset := h.2.2.2.2.2.2.1.measurableSet
  let K : Kernel (ℝ × X) ℝ :=
    ⟨fun ux => if H ux M.Ysetᶜ = 0 then H ux else Measure.dirac M.yMin,
      H.measurable.ite (measurableSet_eq_fun (H.measurable_coe hY.compl) measurable_const)
        measurable_const⟩
  have hKprob : IsMarkovKernel K := by
    constructor
    intro ux
    change IsProbabilityMeasure (if H ux M.Ysetᶜ = 0 then H ux else Measure.dirac M.yMin)
    split_ifs <;> infer_instance
  have hKsupport (ux : ℝ × X) : K ux M.Ysetᶜ = 0 := by
    change (if H ux M.Ysetᶜ = 0 then H ux else Measure.dirac M.yMin) M.Ysetᶜ = 0
    split_ifs with hs
    · exact hs
    · simp [Measure.dirac_apply, he.1.1]
  haveI : IsProbabilityMeasure (xLaw M) := Measure.isProbabilityMeasure_map M.measX.aemeasurable
  have hxeq : ∀ᵐ ux ∂Causalean.Stat.unifOI.prod (xLaw M),
      ∀ u ∈ Icc (0 : ℝ) 1, H (u, ux.2) = pastedAttainingLaw M om Q ux.2 u :=
    (measurePreserving_snd (μ := Causalean.Stat.unifOI) (ν := xLaw M)).quasiMeasurePreserving.ae hHeq
  have hgap := gap_attaining_law_supported M h om hm Q hQ
  have hxgap : ∀ᵐ ux ∂Causalean.Stat.unifOI.prod (xLaw M),
      ∀ k < (CondRangeDecomposition M ux.2).count,
        (CondRangeDecomposition M ux.2).gapLo k < (CondRangeDecomposition M ux.2).gapHi k →
        ∀ u, gapAttainingLaw M om Q ux.2 k u M.Ysetᶜ = 0 :=
    (measurePreserving_snd (μ := Causalean.Stat.unifOI) (ν := xLaw M)).quasiMeasurePreserving.ae hgap
  have hu : ∀ᵐ ux ∂Causalean.Stat.unifOI.prod (xLaw M), ux.1 ∈ Icc (0 : ℝ) 1 := by
    apply (measurePreserving_fst (μ := Causalean.Stat.unifOI) (ν := xLaw M)).quasiMeasurePreserving.ae
    exact (ae_restrict_mem measurableSet_Ioo).mono fun u hu => ⟨hu.1.le, hu.2.le⟩
  have hsupported : ∀ᵐ ux ∂Causalean.Stat.unifOI.prod (xLaw M), H ux M.Ysetᶜ = 0 := by
    filter_upwards [hxeq, hxgap, hu, latentOutcomeKernel_supported M h true] with ux hx hg hu hb
    rw [show ux = (ux.1, ux.2) from rfl, hx ux.1 hu]
    dsimp only [pastedAttainingLaw]
    split
    · rename_i hg'
      obtain ⟨hk, hmem⟩ := Classical.choose_spec hg'
      exact hg _ hk (hmem.1.1.trans hmem.1.2) ux.1
    · split_ifs
      · simp [Measure.dirac_apply, he.1.1]
      · simp [Measure.dirac_apply, he.2.1]
      · exact hb.2
  refine ⟨K, hKprob, hKsupport, ?_, ?_⟩
  · filter_upwards [hsupported, hxeq, hu] with ux hs hx hu
    change (if H ux M.Ysetᶜ = 0 then H ux else Measure.dirac M.yMin) = _
    rw [if_pos hs]
    exact hx ux.1 hu
  · filter_upwards [hHeq, hgap, range_decomposition_valid M h hfin hc] with x hx hg hv
    intro k hk u hu
    have he := conditional_gap_endpoints M x k hk
    have hunit : u ∈ Icc (0 : ℝ) 1 := hu.2
    have hHe : H (u, x) = gapAttainingLaw M om Q x k u :=
      (hx u hunit).trans (pasted_attaining_law_on_gap M om Q x hv k hk u hu)
    have hs : H (u, x) M.Ysetᶜ = 0 := by
      rw [hHe]
      exact hg k hk (hu.1.1.trans hu.1.2) u
    change (if H (u, x) M.Ysetᶜ = 0 then H (u, x) else Measure.dirac M.yMin) = _
    rw [if_pos hs, hHe]

-- @node: def:covariate-continuous-lower-bound-rank-kernel
/-- For [a latent instrumental-variable model](hyp:M), [a covariate-dependent target weight](hyp:om),
and [a family of extended gap quantiles](hyp:Q) with
[joint measurability, outcome support, and agreement with the lower quantiles on interior ranks](hyp:_hQ),
at [a covariate value](hyp:x), [a gap index in its conditional decomposition](hyp:k)
whose [endpoints are strictly ordered](hyp:_hk), and [a rank inside that gap](hyp:u),
[the attaining outcome law](goal) is the distribution obtained by evaluating the extended gap quantile at one minus the randomized rank of the target weight. -/
noncomputable def attainingKernel (om : X → ℝ → ℝ) (Q : X → ℕ → ℝ → ℝ)
    (_hQ : RankKernelExtensionReading M Q)
    (x : X) (k : Fin (CondRangeDecomposition M x).count)
    (_hk : (CondRangeDecomposition M x).gapLo k < (CondRangeDecomposition M x).gapHi k)
    (u : RangeDecomposition.gap (CondRangeDecomposition M x) k) : Measure ℝ :=
  Causalean.Stat.unifOI.map (fun s => Q x k (1 - randomizedRank M om x k u s))
  -- @realizes \pi_{1,x}^\star(gap pushforward for the fixed endpoint extension Q)

/-- For [a latent instrumental-variable model](hyp:M), [a covariate-dependent target weight](hyp:om),
and [a family of extended gap quantiles](hyp:Q), under [the structural assumptions](hyp:h),
[known outcome endpoints](hyp:he), [measurability of the target weight](hyp:hm),
[propensity continuity on instrument components](hyp:hc), [finitely many instrument components](hyp:hfin),
and [joint measurability, outcome support, and interior-quantile agreement of the extension](hyp:hQ),
[the completed attaining kernel](goal) selects a measurable Markov kernel supported on the outcome domain everywhere and satisfying the required agreement with the pasted and gap attaining laws. -/
noncomputable def completedAttainingKernel (om : X → ℝ → ℝ) (Q : X → ℕ → ℝ → ℝ)
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (hm : TargetWeightMeasurable om) (hc : PropensityContinuousOnComponents M)
    (hfin : FiniteInstrumentComponents Z) (hQ : RankKernelExtensionReading M Q) :
    {K : Kernel (ℝ × X) ℝ // IsAttainingKernelVersion M om Q K} :=
  ⟨Classical.choose (exists_attaining_kernel_version M om Q h he hm hc hfin hQ),
    Classical.choose_spec (exists_attaining_kernel_version M om Q h he hm hc hfin hQ)⟩


end Papers.TbsPrteOptimalTransport

module
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationBinaryDenominators
/-! Denominator-path cancellation for binary product scores and the final bin.

Only primitive residual integrability is required. The population numerators
remain fixed, and their centering is supplied by the constructed conditional law.
-/
public section
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false
set_option linter.style.longLine false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- Signed full-interval weights are allowed in the centering identity.
-- @node: population_binary_full_denominator_correction_zero
/-- If [the replacement baseline-class denominators are measurable](hyp:hpi), [the covariate
weight is measurable](hyp:hw), and [the weighted upper](hyp:hp) and [lower treated-success
residuals](hyp:hm) with those denominators are integrable, then [their weighted difference
is integrable and has population mean zero](goal). -/
lemma population_binary_full_denominator_correction_zero
    (L : LevelData Z X) (pi : PositiveIndex L.K → X → ℝ)
    (hpi : ∀ a, Measurable (pi a)) (k : ℕ)
    (w : X → ℝ) (hw : Measurable w)
    (hp : Integrable (fun o : Obs X Z => w o.1 * RP L {eta0Bin M L with piLev := pi} (k+1) o)
      (observationLaw M))
    (hm : Integrable (fun o : Obs X Z => w o.1 * RP L {eta0Bin M L with piLev := pi} k o)
      (observationLaw M)) :
    Integrable (fun o : Obs X Z => w o.1 *
      (RP L {eta0Bin M L with piLev := pi} (k+1) o - RP L {eta0Bin M L with piLev := pi} k o))
      (observationLaw M) ∧
    (∫ o : Obs X Z, w o.1 *
      (RP L {eta0Bin M L with piLev := pi} (k+1) o - RP L {eta0Bin M L with piLev := pi} k o)
      ∂observationLaw M) = 0 := by
  simp_rw [mul_sub]
  refine ⟨hp.sub' hm, ?_⟩
  rw [integral_sub hp hm,
    population_RP_denominator_weighted_integral_zero M L pi hpi (k+1) w hw hp,
    population_RP_denominator_weighted_integral_zero M L pi hpi k w hw hm, sub_self]

-- @node: population_binary_full_product_denominator_path_orthogonality
/-- Suppose [each baseline-class denominator along the path is measurable in covariates](hyp:hpi),
[the population full-interval weight is measurable](hyp:hw), [both weighted adjacent
treated-success residuals are integrable at every path value](hyp:hInt), and [the
full-interval product score at path value zero is integrable](hyp:hbase). Then [the
mean full-interval product score has derivative zero at zero along this denominator
path](goal). -/
lemma population_binary_full_product_denominator_path_orthogonality
    (L : LevelData Z X) (pi : ℝ → PositiveIndex L.K → X → ℝ)
    (hpi : ∀ t a, Measurable (pi t a)) (k : ℕ)
    (hw : Measurable (fullValue (eta0Bin M L).gammaFull k))
    (hInt : ∀ t : ℝ,
      Integrable (fun o : Obs X Z => fullValue (eta0Bin M L).gammaFull k o.1 *
        RP L {eta0Bin M L with piLev := pi t} (k+1) o) (observationLaw M) ∧
      Integrable (fun o : Obs X Z => fullValue (eta0Bin M L).gammaFull k o.1 *
        RP L {eta0Bin M L with piLev := pi t} k o) (observationLaw M))
    (hbase : Integrable (psiFullProdBin L {eta0Bin M L with piLev := pi 0} k)
      (observationLaw M)) :
    HasDerivAt (fun t : ℝ => ∫ o, psiFullProdBin L {eta0Bin M L with piLev := pi t} k o
      ∂observationLaw M) 0 0 := by
  let c := fun t (o : Obs X Z) => fullValue (eta0Bin M L).gammaFull k o.1 *
    (RP L {eta0Bin M L with piLev := pi t} (k+1) o -
      RP L {eta0Bin M L with piLev := pi t} k o)
  have hc : ∀ t, Integrable (c t) (observationLaw M) ∧
      (∫ o, c t o ∂observationLaw M) = 0 := by
    intro t
    exact population_binary_full_denominator_correction_zero M L (pi t) (hpi t) k
      (fullValue (eta0Bin M L).gammaFull k) hw (hInt t).1 (hInt t).2
  have hid : ∀ t o, psiFullProdBin L {eta0Bin M L with piLev := pi t} k o =
      psiFullProdBin L {eta0Bin M L with piLev := pi 0} k o + (c t o - c 0 o) := by
    intro t o
    dsimp only [psiFullProdBin, binFullJ, c]
    ring
  have heq : (fun t : ℝ => ∫ o, psiFullProdBin L {eta0Bin M L with piLev := pi t} k o
      ∂observationLaw M) =
      (fun _ : ℝ => ∫ o, psiFullProdBin L {eta0Bin M L with piLev := pi 0} k o
        ∂observationLaw M) := by
    funext t
    have hf : (fun o => psiFullProdBin L {eta0Bin M L with piLev := pi t} k o) =
        (fun o => psiFullProdBin L {eta0Bin M L with piLev := pi 0} k o + (c t o - c 0 o)) :=
      funext (hid t)
    rw [hf]
    rw [integral_add hbase ((hc t).1.sub' (hc 0).1),
      integral_sub (hc t).1 (hc 0).1, (hc t).2, (hc 0).2, sub_self, add_zero]
  rw [heq]
  exact hasDerivAt_const 0 _

-- The policy residual and plug-in term stay fixed under denominator updates.
-- @node: population_binary_tail_denominator_path_orthogonality
/-- Under [threshold crossing](hyp:h), [a positive number of baseline levels](hyp:hK),
and [invariant baseline and policy ordering](hyp:hOrder), suppose [the baseline-class
denominators are measurable in covariates at every path value](hyp:hpi), [the population
tail weight is measurable](hyp:hw), [the tail-weighted final baseline treatment
residual is integrable throughout the path](hyp:hInt), and [the tail score at path
value zero is integrable](hyp:hbase). Then [the mean tail score has derivative zero
at zero along this denominator path](goal). -/
lemma population_binary_tail_denominator_path_orthogonality
    (h : ThresholdCrossing M) (phi dphi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (pi : ℝ → PositiveIndex L.K → X → ℝ) (hpi : ∀ t a, Measurable (pi t a))
    (hw : Measurable (eta0Bin M L).gammaTail)
    (hInt : ∀ t : ℝ, Integrable (fun o : Obs X Z => (eta0Bin M L).gammaTail o.1 *
      Rp L {eta0Bin M L with piLev := pi t} L.K o) (observationLaw M))
    (hbase : Integrable (commonTailScore M phi dphi L (eta0Bin M L).prop
      (eta0Bin M L).pLev (pi 0) (eta0Bin M L).gammaTail) (observationLaw M)) :
    HasDerivAt (fun t : ℝ => ∫ o, commonTailScore M phi dphi L (eta0Bin M L).prop
      (eta0Bin M L).pLev (pi t) (eta0Bin M L).gammaTail o ∂observationLaw M) 0 0 := by
  have hk : L.K ≠ 0 := by unfold LevelCountPos at hK; omega
  let c := fun t (o : Obs X Z) => M.yMin * ((eta0Bin M L).gammaTail o.1 *
    Rp L {eta0Bin M L with piLev := pi t} L.K o)
  have ic : ∀ t, Integrable (c t) (observationLaw M) :=
    fun t => (hInt t).const_mul M.yMin
  have zc : ∀ t, (∫ o, c t o ∂observationLaw M) = 0 := by
    intro t
    rw [show c t = (fun o : Obs X Z => M.yMin * ((eta0Bin M L).gammaTail o.1 *
      Rp L {eta0Bin M L with piLev := pi t} L.K o)) from rfl, integral_const_mul,
      population_Rp_denominator_weighted_integral_zero M h (policyProp phi M.prop) L
        (pi t) (hpi t) hOrder L.K (eta0Bin M L).gammaTail hw (hInt t), mul_zero]
  have hid : ∀ t o, commonTailScore M phi dphi L (eta0Bin M L).prop
      (eta0Bin M L).pLev (pi t) (eta0Bin M L).gammaTail o =
      commonTailScore M phi dphi L (eta0Bin M L).prop
        (eta0Bin M L).pLev (pi 0) (eta0Bin M L).gammaTail o - (c t o - c 0 o) := by
    intro t o
    simp only [commonTailScore, c, Rp, if_neg hk, div_eq_mul_inv]
    ring
  have heq : (fun t : ℝ => ∫ o, commonTailScore M phi dphi L (eta0Bin M L).prop
      (eta0Bin M L).pLev (pi t) (eta0Bin M L).gammaTail o ∂observationLaw M) =
      (fun _ : ℝ => ∫ o, commonTailScore M phi dphi L (eta0Bin M L).prop
        (eta0Bin M L).pLev (pi 0) (eta0Bin M L).gammaTail o ∂observationLaw M) := by
    funext t
    have hf : (fun o => commonTailScore M phi dphi L (eta0Bin M L).prop
        (eta0Bin M L).pLev (pi t) (eta0Bin M L).gammaTail o) =
        (fun o => commonTailScore M phi dphi L (eta0Bin M L).prop
          (eta0Bin M L).pLev (pi 0) (eta0Bin M L).gammaTail o - (c t o - c 0 o)) :=
      funext (hid t)
    rw [hf]
    rw [integral_sub hbase ((ic t).sub' (ic 0)), integral_sub (ic t) (ic 0),
      zc t, zc 0, sub_self, sub_zero]
  rw [heq]
  exact hasDerivAt_const 0 _

-- Product inheritance uses the fixed gamma prefactor and a fixed indicator
-- residual; only the already-centered component correction depends on pi/tau.
-- @node: population_binary_regular_product_denominator_path_orthogonality
/-- Under [threshold crossing](hyp:h), [measurability of the policy derivative at the true
propensity](hyp:hdphi), and [invariant level ordering](hyp:hOrder), suppose [baseline-class](hyp:hpi)
and [policy-class denominators](hyp:htau) are measurable in covariates throughout
their paths, and the population [regular weight](hyp:hw), [interior-boundary indicator](hyp:hD),
[dominance indicator](hyp:hE), and [active-set indicator](hyp:hI) are measurable. If
[the six weight-multiplied treated-success, treatment, and policy residuals are
integrable throughout the paths](hyp:hInt), [the weighted positive-part term is
integrable](hyp:hh), and [the positive-part term multiplied by the policy-union
indicator minus its population weight is integrable](hyp:hCorr), then [the mean
regular product score has derivative zero at zero along these denominator paths](goal). -/
lemma population_binary_regular_product_denominator_path_orthogonality
    (h : ThresholdCrossing M) (phi dphi : Z → X → ℝ → ℝ)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (L : LevelData Z X) (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (pi : ℝ → PositiveIndex L.K → X → ℝ) (tau : ℝ → RegularIndex L → X → ℝ)
    (hpi : ∀ t a, Measurable (pi t a)) (htau : ∀ t a, Measurable (tau t a))
    (k j : ℕ) (hw : Measurable (regularValue (eta0Bin M L).gamma k j))
    (hD : Measurable (Dbd phi L (eta0Bin M L) k j))
    (hE : Measurable (Edom phi L (eta0Bin M L) k j))
    (hI : Measurable (Iact phi L (eta0Bin M L) k j))
    (hInt : ∀ t : ℝ,
      let et := {eta0Bin M L with piLev := pi t, tauLev := tau t}
      let w := regularValue (eta0Bin M L).gamma k j
      Integrable (fun o : Obs X Z => w o.1 * RP L et (k+1) o) (observationLaw M) ∧
      Integrable (fun o : Obs X Z => w o.1 * RP L et k o) (observationLaw M) ∧
      Integrable (fun o : Obs X Z => w o.1 * Rp L et (k+1) o) (observationLaw M) ∧
      Integrable (fun o : Obs X Z => w o.1 * Rp L et k o) (observationLaw M) ∧
      Integrable (fun o : Obs X Z => w o.1 * RqBin dphi L et k j o) (observationLaw M) ∧
      Integrable (fun o : Obs X Z => w o.1 * RqBin dphi L et k (j-1) o) (observationLaw M))
    (hh : Integrable (fun o : Obs X Z => regularValue (eta0Bin M L).gamma k j o.1 *
      hMinus phi L (eta0Bin M L) k j o.1) (observationLaw M))
    (hCorr : Integrable (fun o : Obs X Z => hMinus phi L (eta0Bin M L) k j o.1 *
      (indicator (o.2.1 ∈ policyUnion L k j) - regularValue (eta0Bin M L).gamma k j o.1))
      (observationLaw M)) :
    HasDerivAt (fun t : ℝ => ∫ o, psiProdBin phi dphi L
      {eta0Bin M L with piLev := pi t, tauLev := tau t} k j o ∂observationLaw M) 0 0 := by
  let w := regularValue (eta0Bin M L).gamma k j
  let c := fun o : Obs X Z => hMinus phi L (eta0Bin M L) k j o.1 *
    (indicator (o.2.1 ∈ policyUnion L k j) - w o.1)
  have hd := population_binary_component_denominator_path_orthogonality M h phi dphi hdphi
    L hOrder pi tau hpi htau k j w hw hD hE hI hInt hh
  have hi : ∀ t : ℝ, Integrable (fun o : Obs X Z => w o.1 * binScoreComponents phi dphi L
      {eta0Bin M L with piLev := pi t, tauLev := tau t} k j o) (observationLaw M) := by
    intro t
    obtain ⟨iPp, iPm, ipp, ipm, iqp, iqm⟩ := hInt t
    have hz := (population_binary_denominator_component_correction_zero M h phi dphi hdphi
      L (pi t) (tau t) (hpi t) (htau t) hOrder k j w hw hD hE hI
      iPp iPm ipp ipm iqp iqm).1
    have hid : (fun o : Obs X Z => w o.1 * binScoreComponents phi dphi L
        {eta0Bin M L with piLev := pi t, tauLev := tau t} k j o) =
        (fun o => w o.1 * hMinus phi L (eta0Bin M L) k j o.1 + w o.1 *
          (binScoreComponents phi dphi L {eta0Bin M L with piLev := pi t, tauLev := tau t} k j o -
            hMinus phi L (eta0Bin M L) k j o.1)) := by
      funext o
      ring
    rw [hid]
    exact hh.fun_add hz
  have heq : (fun t : ℝ => ∫ o, psiProdBin phi dphi L
      {eta0Bin M L with piLev := pi t, tauLev := tau t} k j o ∂observationLaw M) =
      (fun t : ℝ => (∫ o : Obs X Z, w o.1 * binScoreComponents phi dphi L
        {eta0Bin M L with piLev := pi t, tauLev := tau t} k j o ∂observationLaw M) +
        ∫ o, c o ∂observationLaw M) := by
    funext t
    change (∫ o : Obs X Z, w o.1 * binScoreComponents phi dphi L
      {eta0Bin M L with piLev := pi t, tauLev := tau t} k j o + c o ∂observationLaw M) = _
    exact integral_add (hi t) hCorr
  rw [heq]
  exact hd.add_const (∫ o, c o ∂observationLaw M)

-- @node: population_binary_total_denominator_path_orthogonality
/-- Under [threshold crossing](hyp:h), [measurability of the policy derivative at the true
propensity](hyp:hdphi), [a positive baseline level count](hyp:hK), and [invariant level
ordering](hyp:hOrder), assume [baseline-class](hyp:hpi) and [policy-class denominator
paths](hyp:htau) are measurable in covariates, and the population [full-interval weights](hyp:hwFull),
[regular weights](hyp:hwReg), [tail weight](hyp:hwTail), and [all three regular branch
indicators](hyp:hBranch) are measurable on their index ranges. If [the full-interval
weighted treated-success residuals](hyp:hFullInt), [the six weighted residuals for
each regular subinterval](hyp:hRegInt), and [the tail-weighted final treatment residual](hyp:hTailInt)
are integrable throughout the paths, [the regular weighted positive-part terms and
their policy-union indicator corrections are integrable](hyp:hRegFixed), and [all
full-interval, regular, and tail scores are integrable throughout the paths](hyp:hScoreInt),
then [the mean total binary score has derivative zero at zero along the joint
denominator paths](goal). -/
lemma population_binary_total_denominator_path_orthogonality
    (h : ThresholdCrossing M) (phi dphi : Z → X → ℝ → ℝ)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (pi : ℝ → PositiveIndex L.K → X → ℝ) (tau : ℝ → RegularIndex L → X → ℝ)
    (hpi : ∀ t a, Measurable (pi t a)) (htau : ∀ t a, Measurable (tau t a))
    (hwFull : ∀ k < L.K, Measurable (fullValue (eta0Bin M L).gammaFull k))
    (hwReg : ∀ k < L.K, ∀ j ∈ Finset.Icc 1 (L.l k),
      Measurable (regularValue (eta0Bin M L).gamma k j))
    (hwTail : Measurable (eta0Bin M L).gammaTail)
    (hBranch : ∀ k < L.K, ∀ j ∈ Finset.Icc 1 (L.l k),
      Measurable (Dbd phi L (eta0Bin M L) k j) ∧
      Measurable (Edom phi L (eta0Bin M L) k j) ∧
      Measurable (Iact phi L (eta0Bin M L) k j))
    (hFullInt : ∀ t : ℝ, ∀ k < L.K,
      Integrable (fun o : Obs X Z => fullValue (eta0Bin M L).gammaFull k o.1 *
        RP L {eta0Bin M L with piLev := pi t} (k+1) o) (observationLaw M) ∧
      Integrable (fun o : Obs X Z => fullValue (eta0Bin M L).gammaFull k o.1 *
        RP L {eta0Bin M L with piLev := pi t} k o) (observationLaw M))
    (hRegInt : ∀ t : ℝ, ∀ k < L.K, ∀ j ∈ Finset.Icc 1 (L.l k),
      let et := {eta0Bin M L with piLev := pi t, tauLev := tau t}
      let w := regularValue (eta0Bin M L).gamma k j
      Integrable (fun o : Obs X Z => w o.1 * RP L et (k+1) o) (observationLaw M) ∧
      Integrable (fun o : Obs X Z => w o.1 * RP L et k o) (observationLaw M) ∧
      Integrable (fun o : Obs X Z => w o.1 * Rp L et (k+1) o) (observationLaw M) ∧
      Integrable (fun o : Obs X Z => w o.1 * Rp L et k o) (observationLaw M) ∧
      Integrable (fun o : Obs X Z => w o.1 * RqBin dphi L et k j o) (observationLaw M) ∧
      Integrable (fun o : Obs X Z => w o.1 * RqBin dphi L et k (j-1) o) (observationLaw M))
    (hRegFixed : ∀ k < L.K, ∀ j ∈ Finset.Icc 1 (L.l k),
      Integrable (fun o : Obs X Z => regularValue (eta0Bin M L).gamma k j o.1 *
        hMinus phi L (eta0Bin M L) k j o.1) (observationLaw M) ∧
      Integrable (fun o : Obs X Z => hMinus phi L (eta0Bin M L) k j o.1 *
        (indicator (o.2.1 ∈ policyUnion L k j) - regularValue (eta0Bin M L).gamma k j o.1))
        (observationLaw M))
    (hTailInt : ∀ t : ℝ, Integrable (fun o : Obs X Z => (eta0Bin M L).gammaTail o.1 *
      Rp L {eta0Bin M L with piLev := pi t} L.K o) (observationLaw M))
    (hScoreInt : ∀ t : ℝ,
      let et := {eta0Bin M L with piLev := pi t, tauLev := tau t}
      (∀ k < L.K, Integrable (psiFullProdBin L et k) (observationLaw M) ∧
        ∀ j ∈ Finset.Icc 1 (L.l k), Integrable (psiProdBin phi dphi L et k j) (observationLaw M)) ∧
      Integrable (commonTailScore M phi dphi L et.prop et.pLev et.piLev et.gammaTail)
        (observationLaw M)) :
    HasDerivAt (fun t : ℝ => ∫ o, psiBin M phi dphi L hK o
      {eta0Bin M L with piLev := pi t, tauLev := tau t} ∂observationLaw M) 0 0 := by
  let et := fun t => {eta0Bin M L with piLev := pi t, tauLev := tau t}
  have hf : ∀ k ∈ Finset.range L.K,
      HasDerivAt (fun t : ℝ => ∫ o, psiFullProdBin L (et t) k o ∂observationLaw M) 0 0 := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    exact population_binary_full_product_denominator_path_orthogonality M L pi hpi k
      (hwFull k hk') (fun t => hFullInt t k hk') ((hScoreInt 0).1 k hk').1
  have hr : ∀ k ∈ Finset.range L.K, ∀ j ∈ Finset.Icc 1 (L.l k),
      HasDerivAt (fun t : ℝ => ∫ o, psiProdBin phi dphi L (et t) k j o ∂observationLaw M) 0 0 := by
    intro k hk j hj
    have hk' := Finset.mem_range.mp hk
    obtain ⟨hD, hE, hI⟩ := hBranch k hk' j hj
    exact population_binary_regular_product_denominator_path_orthogonality M h phi dphi hdphi
      L hOrder pi tau hpi htau k j (hwReg k hk' j hj) hD hE hI
      (fun t => hRegInt t k hk' j hj) (hRegFixed k hk' j hj).1 (hRegFixed k hk' j hj).2
  have ht := population_binary_tail_denominator_path_orthogonality M h phi dphi L hK hOrder
    pi hpi hwTail hTailInt (hScoreInt 0).2
  have hsum : HasDerivAt (fun t : ℝ => ∑ k ∈ Finset.range L.K,
      ((∫ o, psiFullProdBin L (et t) k o ∂observationLaw M) +
        ∑ j ∈ Finset.Icc 1 (L.l k), ∫ o, psiProdBin phi dphi L (et t) k j o ∂observationLaw M)) 0 0 := by
    have hk : ∀ k ∈ Finset.range L.K, HasDerivAt (fun t : ℝ =>
        (∫ o, psiFullProdBin L (et t) k o ∂observationLaw M) +
          ∑ j ∈ Finset.Icc 1 (L.l k), ∫ o, psiProdBin phi dphi L (et t) k j o ∂observationLaw M) 0 0 := by
      intro k hk
      have hj := HasDerivAt.fun_sum (hr k hk)
      have hj' : HasDerivAt (fun t : ℝ => ∑ j ∈ Finset.Icc 1 (L.l k),
          ∫ o, psiProdBin phi dphi L (et t) k j o ∂observationLaw M) 0 0 := by
        simpa only [Finset.sum_const_zero] using hj
      simpa only [add_zero] using (hf k hk).fun_add hj'
    simpa only [Finset.sum_const_zero] using HasDerivAt.fun_sum hk
  have heq : (fun t : ℝ => ∫ o, psiBin M phi dphi L hK o (et t) ∂observationLaw M) =
      (fun t : ℝ => (∑ k ∈ Finset.range L.K,
        ((∫ o, psiFullProdBin L (et t) k o ∂observationLaw M) +
          ∑ j ∈ Finset.Icc 1 (L.l k), ∫ o, psiProdBin phi dphi L (et t) k j o ∂observationLaw M)) +
        ∫ o, commonTailScore M phi dphi L (et t).prop (et t).pLev (et t).piLev (et t).gammaTail o
          ∂observationLaw M) := by
    funext t
    have ir : ∀ k ∈ Finset.range L.K, Integrable
        (fun o => ∑ j ∈ Finset.Icc 1 (L.l k), psiProdBin phi dphi L (et t) k j o)
        (observationLaw M) := by
      intro k hk
      exact integrable_finsetSum _ ((hScoreInt t).1 k (Finset.mem_range.mp hk)).2
    have ia : ∀ k ∈ Finset.range L.K, Integrable
        (fun o => psiFullProdBin L (et t) k o +
          ∑ j ∈ Finset.Icc 1 (L.l k), psiProdBin phi dphi L (et t) k j o)
        (observationLaw M) := by
      intro k hk
      exact ((hScoreInt t).1 k (Finset.mem_range.mp hk)).1.fun_add (ir k hk)
    dsimp only [psiBin]
    rw [integral_add (integrable_finsetSum _ ia) (hScoreInt t).2,
      integral_finsetSum _ ia]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [integral_add ((hScoreInt t).1 k (Finset.mem_range.mp hk)).1 (ir k hk),
      integral_finsetSum _ ((hScoreInt t).1 k (Finset.mem_range.mp hk)).2]
  change HasDerivAt (fun t : ℝ => ∫ o, psiBin M phi dphi L hK o (et t) ∂observationLaw M) 0 0
  rw [heq]
  simpa only [add_zero] using hsum.fun_add ht

end Papers.TbsPrteOptimalTransport

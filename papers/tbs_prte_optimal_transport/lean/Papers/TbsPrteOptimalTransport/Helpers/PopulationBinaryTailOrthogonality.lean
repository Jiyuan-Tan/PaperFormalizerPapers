module
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationBinaryAdmissibility
/-! Final-bin weight cancellation for the complete population binary score. -/
public section
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

-- @node: binary_tail_weight_direction_regular
/-- If [a binary nuisance perturbation is admissible around a nuisance specification](hyp:hd),
[its final-bin weight perturbation is measurable and has a nonnegative, finite
almost-sure bound under the covariate distribution](goal). -/
lemma binary_tail_weight_direction_regular (L : LevelData Z X) (eta del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr eta) (.inr del)) :
    Measurable del.gammaTail ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ x ∂xLaw M, ‖del.gammaTail x‖ ≤ C := by
  obtain ⟨r, hr, hpath⟩ := hd.admissible
  have h0 := hpath 0 (by simpa using hr)
  have ht := hpath (r / 2) (by rw [abs_of_pos (by positivity)]; linarith)
  rcases h0 with ⟨_, _, _, _, _, _, _, _, _, _, _, hg0, hmg0⟩
  rcases ht with ⟨_, _, _, _, _, _, _, _, _, _, _, hgt, hmgt⟩
  have hm0 : Measurable eta.gammaTail := by
    have hm : Measurable (fun x => eta.gammaTail x + 0 * del.gammaTail x) := hmg0
    simpa only [zero_mul, add_zero] using hm
  have hmt : Measurable (fun x => eta.gammaTail x + (r / 2) * del.gammaTail x) := hmgt
  constructor
  · have hid : del.gammaTail = fun x =>
        ((eta.gammaTail x + (r / 2) * del.gammaTail x) - eta.gammaTail x) / (r / 2) := by
      funext x
      field_simp
      <;> ring
    rw [hid]
    exact (hmt.sub hm0).div_const _
  · refine ⟨4 / r, by positivity, ?_⟩
    filter_upwards [hg0, hgt] with x hx0 hxt
    change eta.gammaTail x + 0 * del.gammaTail x ∈ Icc (0 : ℝ) 1 at hx0
    change eta.gammaTail x + (r / 2) * del.gammaTail x ∈ Icc (0 : ℝ) 1 at hxt
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · rw [← neg_div, div_le_iff₀ hr]
      nlinarith [hx0.1, hx0.2, hxt.1, hxt.2]
    · apply (le_div_iff₀ hr).2
      nlinarith [hx0.1, hx0.2, hxt.1, hxt.2]

-- All regular and full-interval scores are unchanged by this update.
-- @node: binary_total_tail_weight_path
/-- With [a positive baseline level count](hyp:hK), [adding a scalar multiple of a
covariate function to the final-bin weight changes the complete binary score by
minus that scalar times the lower outcome endpoint, the covariate function, and
the final baseline treatment residual correction, at every observation](goal). -/
lemma binary_total_tail_weight_path (phi dphi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (hK : LevelCountPos L.K) (eta : NuisanceBin L)
    (d : X → ℝ) (o : Obs X Z) (t : ℝ) :
    psiBin M phi dphi L hK o
      {eta with gammaTail := fun x => eta.gammaTail x + t * d x} =
    psiBin M phi dphi L hK o eta - t * (M.yMin * (d o.1 * Rp L eta L.K o)) := by
  have hk : L.K ≠ 0 := by unfold LevelCountPos at hK; omega
  have hfull : ∀ k, psiFullProdBin L
      {eta with gammaTail := fun x => eta.gammaTail x + t * d x} k o =
      psiFullProdBin L eta k o := fun _ => rfl
  have hreg : ∀ k j, psiProdBin phi dphi L
      {eta with gammaTail := fun x => eta.gammaTail x + t * d x} k j o =
      psiProdBin phi dphi L eta k j o := fun _ _ => rfl
  simp only [psiBin, hfull, hreg, commonTailScore, Rp, if_neg hk, div_eq_mul_inv]
  ring

-- The final level residual is centered by the structural treatment equation.
-- @node: population_binary_total_tail_weight_integral_path
/-- Under [the threshold-crossing treatment model](hyp:h), [a positive baseline level
count](hyp:hK), and [covariate-invariant ordering of baseline and policy levels](hyp:hOrder),
suppose [the final-bin weight perturbation is measurable](hyp:hd), [its product with
the final baseline treatment residual correction is integrable](hyp:hi), and [the
unperturbed population binary score is integrable](hyp:hbase). Then [adding any scalar
multiple of that perturbation to the final-bin weight leaves the expected complete
binary score equal to its population value](goal). -/
lemma population_binary_total_tail_weight_integral_path (h : ThresholdCrossing M)
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (d : X → ℝ) (hd : Measurable d)
    (hi : Integrable (fun o : Obs X Z => d o.1 * Rp L (eta0Bin M L) L.K o)
      (observationLaw M))
    (hbase : Integrable (fun o => psiBin M phi dphi L hK o (eta0Bin M L))
      (observationLaw M)) (t : ℝ) :
    (∫ o, psiBin M phi dphi L hK o
      {eta0Bin M L with gammaTail := fun x => (eta0Bin M L).gammaTail x + t * d x}
      ∂observationLaw M) =
    ∫ o, psiBin M phi dphi L hK o (eta0Bin M L) ∂observationLaw M := by
  have hz := population_Rp_weighted_integral_zero M h (policyProp phi M.prop) L hOrder
    L.K d hd hi
  simp_rw [binary_total_tail_weight_path]
  rw [integral_sub hbase ((hi.const_mul M.yMin).const_mul t),
    integral_const_mul, integral_const_mul, hz, mul_zero, mul_zero, sub_zero]

-- No extra regularity premise: overlap and admissibility supply it here.
-- @node: population_binary_total_tail_weight_orthogonality_of_admissible
/-- Under [the threshold-crossing treatment model](hyp:h), suppose [the policy is a
valid policy map](hyp:hphi), [its derivative at baseline propensities is jointly
measurable](hyp:hdphi), [the derivative bound is nonnegative](hyp:hB), and [the derivative's
absolute value never exceeds that bound](hyp:hb). With [a positive baseline level
count](hyp:hK), [covariate-invariant ordering of baseline and policy levels](hyp:hOrder),
[measurable baseline levels](hyp:hlev), [baseline overlap](hyp:hov), [policy-level
overlap](hyp:hpol), [almost-surely binary outcomes](hyp:hy), and [an admissible nuisance
perturbation at the population specification](hyp:hd), [the expected complete binary
score has derivative zero at zero when only the final-bin weight is varied linearly
in that direction](goal). -/
lemma population_binary_total_tail_weight_orthogonality_of_admissible
    (h : ThresholdCrossing M) (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ z x, |dphi z x (M.prop z x)| ≤ B)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (hlev : ∀ k, Measurable (L.pLev k)) (cpi : ℝ)
    (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (hy : OutcomeBinaryAE M) (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del)) :
    HasDerivAt (fun t : ℝ => ∫ o, psiBin M phi dphi L hK o
      {eta0Bin M L with gammaTail := fun x =>
        (eta0Bin M L).gammaTail x + t * del.gammaTail x} ∂observationLaw M) 0 0 := by
  have he := binary_admissible_direction_origin M L (eta0Bin M L) del hd
  obtain ⟨hm, C, hC, hbound⟩ := binary_tail_weight_direction_regular M L (eta0Bin M L) del hd
  have hi := population_binary_weighted_Rp_integrable M L cpi hov he L.K
    del.gammaTail hm C hbound
  have hbase := (population_binary_score_mean_of_overlap M h phi dphi hphi hdphi
    B hB hb L hK hOrder hlev cpi hov hpol hy he).1
  have heq : (fun t : ℝ => ∫ o, psiBin M phi dphi L hK o
      {eta0Bin M L with gammaTail := fun x =>
        (eta0Bin M L).gammaTail x + t * del.gammaTail x} ∂observationLaw M) =
      (fun _ : ℝ => ∫ o, psiBin M phi dphi L hK o (eta0Bin M L)
        ∂observationLaw M) := by
    funext t
    exact population_binary_total_tail_weight_integral_path M h phi dphi L hK hOrder
      del.gammaTail hm hi hbase t
  rw [heq]
  exact hasDerivAt_const 0 _

end Papers.TbsPrteOptimalTransport

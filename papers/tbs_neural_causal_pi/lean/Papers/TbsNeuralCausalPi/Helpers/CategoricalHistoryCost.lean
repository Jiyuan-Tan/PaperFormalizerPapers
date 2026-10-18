module
public import Papers.TbsNeuralCausalPi.Helpers.CategoricalHistoryKernel
/-! # Integrated categorical propensities and their history transport cost

Propensities are integrated over the actual non-Gumbel block law. Outside the
carrying domain they are replaced by the first vertex of the simplex.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
    {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
    {C : Fin b → Set (Fin n)}

/-- [The distance between structural inputs formed from two histories and the
same exogenous noise is at most the distance between those histories](goal). -/
-- @node: structuralInput_dist_same_noise_le
lemma structuralInput_dist_same_noise_le (M : EuclideanSCM kind dims)
    (i : Fin n) (v w : Joint kind) (u : Exogenous kind dims) :
    dist (structuralInput M i v u) (structuralInput M i w u) ≤ dist v w := by
  simp only [PiLp.dist_eq_of_L1, structuralInput, WithLp.ofLp_toLp,
    Fintype.sum_sum_type, dist_self, Finset.sum_const_zero, add_zero]
  let f : (Σ p : {p // p ∈ M.dag.parents i}, Fin (valueDim (kind p.val))) →
      (Σ j, Fin (valueDim (kind j))) := fun p => ⟨p.1.val, p.2⟩
  have hf : Function.Injective f := by
    rintro ⟨⟨p,hp⟩,j⟩ ⟨⟨q,hq⟩,l⟩ h
    cases h
    rfl
  change (∑ x, (fun j => dist (v.ofLp j) (w.ofLp j)) (f x)) ≤ _
  rw [← Finset.sum_image (s := Finset.univ) (g := f)
    (f := fun j => dist (v.ofLp j) (w.ofLp j)) hf.injOn]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => dist_nonneg)

/-- At [a node with k categorical labels](hyp:hi), [the canonical propensity
vector is jointly measurable in the history and the exogenous block values](goal). -/
-- @node: canonicalCategoricalPropensity_joint_measurable
@[fun_prop] lemma canonicalCategoricalPropensity_joint_measurable
    (M : CanonicalSCM kind dims dag G C) (i : Fin n) (k : ℕ)
    (hi : kind i = Sum.inr k) :
    Measurable (fun z : Joint kind × (∀ a, L1Vec (dims a)) =>
      canonicalCategoricalPropensity M i k hi z.1 z.2) := by
  first | fun_prop | skip
  unfold canonicalCategoricalPropensity
  have hx : Measurable (fun z : Joint kind × (∀ a, L1Vec (dims a)) =>
      structuralInput M.toEuclideanSCM i z.1 (blocksExogenous z.2)) := by fun_prop
  have hm := (M.structuralMeasurable i).comp hx
  fun_prop

/-- For [a canonical model](hyp:M), [a node i](hyp:i), [a category count k](hyp:k),
[the specification that node i has k categorical labels](hyp:hi), [a history v](hyp:v),
and [a label j](hyp:j), the [integrated propensity of label j](goal) is its
canonical propensity averaged over the product of the model's exogenous block laws. -/
-- @node: canonicalIntegratedPropensity
def canonicalIntegratedPropensity
    (M : CanonicalSCM kind dims dag G C) (i : Fin n) (k : ℕ)
    (hi : kind i = Sum.inr k) (v : Joint kind) (j : Fin k) : ℝ :=
  ∫ z, (canonicalCategoricalPropensity M i k hi v z).ofLp j
    ∂(Measure.pi (fun a => (M.blockLaw a : Measure (L1Vec (dims a)))))

/-- At [a node with k categorical labels](hyp:hi), [the integrated propensity
of each fixed label is a measurable function of the history](goal). -/
-- @node: canonicalIntegratedPropensity_measurable
@[fun_prop] lemma canonicalIntegratedPropensity_measurable
    (M : CanonicalSCM kind dims dag G C) (i : Fin n) (k : ℕ)
    (hi : kind i = Sum.inr k) (j : Fin k) :
    Measurable (fun v => canonicalIntegratedPropensity M i k hi v j) := by
  unfold canonicalIntegratedPropensity
  have hm : Measurable (fun z : Joint kind × (∀ a, L1Vec (dims a)) =>
      (canonicalCategoricalPropensity M i k hi z.1 z.2).ofLp j) :=
    (measurable_pi_apply j).comp
      (scm_ofLp_measurable.comp (canonicalCategoricalPropensity_joint_measurable M i k hi))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

/-- At [a node with k categorical labels](hyp:hi) and [topological position r](hyp:hr),
if [the history is admissible after the first r nodes have been visited](hyp:hv),
then [the integrated propensities are nonnegative and sum to one](goal). -/
-- @node: canonicalIntegratedPropensity_mem_simplex
lemma canonicalIntegratedPropensity_mem_simplex
    (M : CanonicalSCM kind dims dag G C) (i : Fin n) (k : ℕ)
    (hi : kind i = Sum.inr k) (r : ℕ) (hr : dag.topoOrder i = r)
    (v : Joint kind) (hv : v ∈ visitedHistoryDomain (dag := dag) r) :
    canonicalIntegratedPropensity M i k hi v ∈ probabilitySimplex k := by
  apply integral_simplex_mem _ _ (canonicalCategoricalPropensity_measurable M i k hi v)
  apply Filter.Eventually.of_forall
  intro z
  exact M.simplex i k hi _
    (structuralInput_mem_domain_of_visitedHistory M.toEuclideanSCM i r hr v hv
      (blocksExogenous z)).1

/-- At [a node with k categorical labels](hyp:hi), suppose [the model's
categorical propensities satisfy the Lipschitz condition](hyp:hprop) with
[nonnegative constant L](hyp:L). If [the node has topological position r](hyp:hr),
[v is an admissible history after r visits](hyp:hv), and [w is also admissible
after r visits](hyp:hw), then [the sum of absolute differences of their integrated
propensities is at most L times the distance between the histories](goal). -/
-- @node: canonicalIntegratedPropensity_dist_le
lemma canonicalIntegratedPropensity_dist_le
    (M : CanonicalSCM kind dims dag G C) (i : Fin n) (k : ℕ)
    (hi : kind i = Sum.inr k) (L : ℝ≥0)
    (hprop : CategoricalPropensityLipschitz M.toEuclideanSCM M.f L)
    (r : ℕ) (hr : dag.topoOrder i = r) (v w : Joint kind)
    (hv : v ∈ visitedHistoryDomain (dag := dag) r)
    (hw : w ∈ visitedHistoryDomain (dag := dag) r) :
    (∑ j, |canonicalIntegratedPropensity M i k hi v j -
      canonicalIntegratedPropensity M i k hi w j|) ≤ (L : ℝ) * dist v w := by
  let B := Measure.pi (fun a => (M.blockLaw a : Measure (L1Vec (dims a))))
  let p := canonicalCategoricalPropensity M i k hi v
  let q := canonicalCategoricalPropensity M i k hi w
  have hp : Measurable p := by fun_prop
  have hq : Measurable q := by fun_prop
  have hps : ∀ᵐ z ∂B, (p z).ofLp ∈ probabilitySimplex k := by
    apply Filter.Eventually.of_forall
    intro z
    exact M.simplex i k hi _
      (structuralInput_mem_domain_of_visitedHistory M.toEuclideanSCM i r hr v hv
        (blocksExogenous z)).1
  have hqs : ∀ᵐ z ∂B, (q z).ofLp ∈ probabilitySimplex k := by
    apply Filter.Eventually.of_forall
    intro z
    exact M.simplex i k hi _
      (structuralInput_mem_domain_of_visitedHistory M.toEuclideanSCM i r hr w hw
        (blocksExogenous z)).1
  have hpi j := simplex_coordinate_integrable B p hp hps j
  have hqi j := simplex_coordinate_integrable B q hq hqs j
  have hpoint (z) : (∑ j, |(p z).ofLp j - (q z).ofLp j|) ≤ (L : ℝ) * dist v w := by
    have h := (hprop.1 i k hi).dist_le_mul _
      (structuralInput_mem_domain_of_visitedHistory M.toEuclideanSCM i r hr v hv
        (blocksExogenous z)) _
      (structuralInput_mem_domain_of_visitedHistory M.toEuclideanSCM i r hr w hw
        (blocksExogenous z))
    have he : (∑ j, |(p z).ofLp j - (q z).ofLp j|) =
        dist (M.f i (structuralInput M.toEuclideanSCM i v (blocksExogenous z)))
          (M.f i (structuralInput M.toEuclideanSCM i w (blocksExogenous z))) := by
      rw [PiLp.dist_eq_of_L1]
      dsimp [p, q, canonicalCategoricalPropensity]
      convert
        (Function.Bijective.sum_comp
          (show Function.Bijective (Fin.cast (congrArg outputDim hi).symm) from
            ⟨Fin.cast_injective _, fun j => ⟨Fin.cast (congrArg outputDim hi) j, by simp⟩⟩)
          (fun j => dist
            ((M.f i (structuralInput M.toEuclideanSCM i v (blocksExogenous z))).ofLp j)
            ((M.f i (structuralInput M.toEuclideanSCM i w (blocksExogenous z))).ofLp j))) using 1
      · congr 1
    rw [he]
    exact h.trans (mul_le_mul_of_nonneg_left
      (structuralInput_dist_same_noise_le M.toEuclideanSCM i v w (blocksExogenous z)) L.coe_nonneg)
  calc
    _ = ∑ j, |∫ z, (p z).ofLp j - (q z).ofLp j ∂B| := by
      simp only [integral_sub (hpi _) (hqi _)]
      rfl
    _ ≤ ∑ j, ∫ z, |(p z).ofLp j - (q z).ofLp j| ∂B :=
      Finset.sum_le_sum fun j _ => abs_integral_le_integral_abs
    _ = ∫ z, ∑ j, |(p z).ofLp j - (q z).ofLp j| ∂B :=
      (integral_finsetSum _ (fun j _ => ((hpi j).sub (hqi j)).abs)).symm
    _ ≤ ∫ _z, (L : ℝ) * dist v w ∂B :=
      integral_mono (integrable_finsetSum _ (fun j _ => ((hpi j).sub (hqi j)).abs))
        (integrable_const _) hpoint
    _ = _ := by simp [B]

/-- For [a canonical model](hyp:M), [a node i](hyp:i), [a category count k](hyp:k),
[the specification that node i has k categorical labels](hyp:hi), [a history v](hyp:v),
and [a label j](hyp:j), the [totalized propensity of label j](goal) equals its
integrated propensity on the admissible history domain and otherwise equals one
for the first label and zero for every other label. -/
-- @node: canonicalTotalPropensity
def canonicalTotalPropensity
    (M : CanonicalSCM kind dims dag G C) (i : Fin n) (k : ℕ)
    (hi : kind i = Sum.inr k) (v : Joint kind) (j : Fin k) : ℝ :=
  if v ∈ visitedHistoryDomain (dag := dag) (dag.topoOrder i) then
    canonicalIntegratedPropensity M i k hi v j else if j.val = 0 then 1 else 0

/-- At [a node with k categorical labels](hyp:hi), [each fixed label's totalized
propensity is a measurable function of the history](goal). -/
-- @node: canonicalTotalPropensity_measurable
@[fun_prop] lemma canonicalTotalPropensity_measurable
    (M : CanonicalSCM kind dims dag G C) (i : Fin n) (k : ℕ)
    (hi : kind i = Sum.inr k) (j : Fin k) :
    Measurable (fun v => canonicalTotalPropensity M i k hi v j) := by
  unfold canonicalTotalPropensity
  exact Measurable.ite (visitedHistoryDomain_measurableSet _)
    (by fun_prop) measurable_const

/-- At [a node with k categorical labels](hyp:hi), [the totalized propensities
are nonnegative and sum to one at every history](goal). -/
-- @node: canonicalTotalPropensity_mem_simplex
lemma canonicalTotalPropensity_mem_simplex
    (M : CanonicalSCM kind dims dag G C) (i : Fin n) (k : ℕ)
    (hi : kind i = Sum.inr k) (v : Joint kind) :
    canonicalTotalPropensity M i k hi v ∈ probabilitySimplex k := by
  by_cases hv : v ∈ visitedHistoryDomain (dag := dag) (dag.topoOrder i)
  · have he : canonicalTotalPropensity M i k hi v =
        canonicalIntegratedPropensity M i k hi v := by
      funext j
      simp only [canonicalTotalPropensity, hv, if_true]
    rw [he]
    exact
      canonicalIntegratedPropensity_mem_simplex M i k hi _ rfl v hv
  · have hk := M.positive_categories i k hi
    refine ⟨fun j => by simp [canonicalTotalPropensity, hv]; positivity, ?_⟩
    simp only [canonicalTotalPropensity, hv, if_false]
    rw [Finset.sum_eq_single (⟨0,hk⟩ : Fin k)]
    · simp
    · intro j _ hj
      have : j.val ≠ 0 := by intro h; apply hj; exact Fin.ext h
      simp [this]
    · simp

/-- At [a node with k categorical labels](hyp:hi), if [the intervention leaves
the node untouched](hyp:hti) and [the history is admissible at the node's
topological position](hyp:hv), then [the actual history transition is the
categorical kernel that draws from the totalized propensities and replaces that
node's history coordinate with the selected label](goal). -/
-- @node: canonicalNodeHistoryKernel_eq_total_categorical
lemma canonicalNodeHistoryKernel_eq_total_categorical
    (M : CanonicalSCM kind dims dag G C) (i : Fin n) (k : ℕ)
    (hi : kind i = Sum.inr k) (t : Intervention kind) (hti : t i = none)
    (v : Joint kind) (hv : v ∈ visitedHistoryDomain (dag := dag) (dag.topoOrder i)) :
    canonicalNodeHistoryKernel M i t v =
      categoricalEncodedKernel (canonicalTotalPropensity M i k hi)
        (canonicalTotalPropensity_measurable M i k hi)
        (fun v j => categoricalHistoryReplacement i v j)
        (fun j => categoricalHistoryReplacement_measurable i j) v := by
  rw [canonicalNodeHistoryKernel_categorical_law M i k hi t hti _ rfl v hv]
  simp only [categoricalEncodedKernel, Kernel.coe_mk, canonicalTotalPropensity, hv, if_true,
    canonicalIntegratedPropensity]

/-- At [a node with k categorical labels](hyp:hi), [replacing its coordinate in
two histories by labels a and c gives a distance at most the original history
distance, plus k minus one if the labels differ and zero if they agree](goal). -/
-- @node: categoricalHistoryReplacement_dist_le
lemma categoricalHistoryReplacement_dist_le (i : Fin n) (k : ℕ)
    (hi : kind i = Sum.inr k) (v w : Joint kind) (a c : Fin k) :
    dist (categoricalHistoryReplacement i v a) (categoricalHistoryReplacement i w c) ≤
      dist v w + if a = c then (0 : ℝ) else ((k-1 : ℕ) : ℝ) := by
  rw [PiLp.dist_eq_of_L1, PiLp.dist_eq_of_L1, Fintype.sum_sigma, Fintype.sum_sigma]
  calc
    _ ≤ ∑ j, ((∑ l : Fin (valueDim (kind j)), dist (v.ofLp ⟨j,l⟩) (w.ofLp ⟨j,l⟩)) +
        if j = i then (if a = c then (0 : ℝ) else ((k-1 : ℕ) : ℝ)) else 0) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : j = i
      · subst j
        simp only [categoricalHistoryReplacement, WithLp.ofLp_toLp, if_true]
        have hdim : valueDim (kind i) = 1 := by simp [hi, valueDim]
        have hs : (∑ _l : Fin (valueDim (kind i)),
            dist (a.val + 1 : ℝ) (c.val + 1 : ℝ)) = dist (a.val + 1 : ℝ) (c.val + 1 : ℝ) := by
          simp [hdim]
        rw [hs]
        apply le_add_of_nonneg_of_le (Finset.sum_nonneg (fun _ _ => dist_nonneg))
        by_cases hac : a = c
        · simp [hac]
        · simpa only [hac, if_false, Real.dist_eq] using categorical_label_diameter_le a c
      · simp only [categoricalHistoryReplacement, WithLp.ofLp_toLp, hj, if_false, add_zero]
        exact le_rfl
    _ = _ := by rw [Finset.sum_add_distrib]; simp

/-- For [a canonical model](hyp:M), [a node i](hyp:i), [a category count k](hyp:k),
and [the specification that node i has k categorical labels](hyp:hi), the
[categorical history coupling kernel](goal) maximally couples the totalized label
propensities at two histories and replaces the node's coordinate in each history
with its coupled label. -/
-- @node: canonicalCategoricalHistoryCoupling
def canonicalCategoricalHistoryCoupling
    (M : CanonicalSCM kind dims dag G C) (i : Fin n) (k : ℕ)
    (hi : kind i = Sum.inr k) : Kernel (Joint kind × Joint kind) (Joint kind × Joint kind) :=
  categoricalEncodedCouplingKernel (canonicalTotalPropensity M i k hi)
    (canonicalTotalPropensity M i k hi)
    (canonicalTotalPropensity_measurable M i k hi)
    (canonicalTotalPropensity_measurable M i k hi)
    (fun v j => categoricalHistoryReplacement i v j)
    (fun v j => categoricalHistoryReplacement i v j)
    (fun j => categoricalHistoryReplacement_measurable i j)
    (fun j => categoricalHistoryReplacement_measurable i j)

/-- At [a node with k categorical labels](hyp:hi), if [the first intervention
leaves the node untouched](hyp:hti), [the second intervention does too](hyp:hti'),
[v is admissible at the node's topological position](hyp:hv), and [w is also
admissible there](hyp:hw), then [the explicit categorical history kernel is a
probability coupling of the two actual intervened history transitions](goal). -/
-- @node: canonicalCategoricalHistoryCoupling_coupling
lemma canonicalCategoricalHistoryCoupling_coupling
    (M : CanonicalSCM kind dims dag G C) (i : Fin n) (k : ℕ)
    (hi : kind i = Sum.inr k) (t t' : Intervention kind)
    (hti : t i = none) (hti' : t' i = none) (v w : Joint kind)
    (hv : v ∈ visitedHistoryDomain (dag := dag) (dag.topoOrder i))
    (hw : w ∈ visitedHistoryDomain (dag := dag) (dag.topoOrder i)) :
    canonicalCategoricalHistoryCoupling M i k hi (v,w) ∈
      couplings (canonicalNodeHistoryKernel M i t v) (canonicalNodeHistoryKernel M i t' w) := by
  rw [canonicalNodeHistoryKernel_eq_total_categorical M i k hi t hti v hv,
    canonicalNodeHistoryKernel_eq_total_categorical M i k hi t' hti' w hw]
  exact categoricalEncodedCouplingKernel_coupling _ _ _ _ _ _ _ _
    (canonicalTotalPropensity_mem_simplex M i k hi)
    (canonicalTotalPropensity_mem_simplex M i k hi) (v,w)

/-- At [a node with k categorical labels](hyp:hi), suppose [the categorical
propensities satisfy the Lipschitz condition](hyp:hprop) with [nonnegative
constant L](hyp:L). For [a history v admissible at the node's topological
position](hyp:hv) and [a history w admissible there](hyp:hw), [the expected
distance under the categorical history coupling is at most one plus half of
k minus one times L, multiplied by the distance between v and w](goal). -/
-- @node: canonicalCategoricalHistoryCoupling_cost_le
lemma canonicalCategoricalHistoryCoupling_cost_le
    (M : CanonicalSCM kind dims dag G C) (i : Fin n) (k : ℕ)
    (hi : kind i = Sum.inr k) (L : ℝ≥0)
    (hprop : CategoricalPropensityLipschitz M.toEuclideanSCM M.f L)
    (v w : Joint kind)
    (hv : v ∈ visitedHistoryDomain (dag := dag) (dag.topoOrder i))
    (hw : w ∈ visitedHistoryDomain (dag := dag) (dag.topoOrder i)) :
    (∫⁻ z, edist z.1 z.2 ∂canonicalCategoricalHistoryCoupling M i k hi (v,w)) ≤
      ENNReal.ofReal (1 + (k-1 : ℕ) / 2 * (L : ℝ)) * edist v w := by
  have hp := canonicalIntegratedPropensity_dist_le M i k hi L hprop _ rfl v w hv hw
  calc
    _ ≤ ENNReal.ofReal (dist v w + (k-1 : ℕ) / 2 *
        ∑ j, |canonicalTotalPropensity M i k hi v j -
          canonicalTotalPropensity M i k hi w j|) :=
      categoricalEncodedCouplingKernel_cost_le _ _ _ _ _ _ _ _ (v,w)
        (canonicalTotalPropensity_mem_simplex M i k hi v)
        (canonicalTotalPropensity_mem_simplex M i k hi w) _ _
        (categoricalHistoryReplacement_dist_le i k hi v w)
    _ ≤ ENNReal.ofReal ((1 + (k-1 : ℕ) / 2 * (L : ℝ)) * dist v w) := by
      apply ENNReal.ofReal_le_ofReal
      simp only [canonicalTotalPropensity, hv, hw, if_true]
      nlinarith [mul_le_mul_of_nonneg_left hp (show (0 : ℝ) ≤ (k-1 : ℕ) / 2 by positivity)]
    _ = _ := by rw [ENNReal.ofReal_mul (by positivity), edist_dist]


end
end Papers.TbsNeuralCausalPi

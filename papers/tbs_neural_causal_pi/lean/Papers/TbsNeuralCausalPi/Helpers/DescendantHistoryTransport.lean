module
public import Papers.TbsNeuralCausalPi.Helpers.LocalHistoryCoupling
public import Papers.TbsNeuralCausalPi.Helpers.DoseResponseNonDescendant
/-! # Lipschitz transport for the descendant simulation

Local couplings of the actual transitions are iterated over active nodes.
Projection onto the scalar outcome then controls the descendant means.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.style.longLine false
set_option linter.unusedVariables false
variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
  {C : Fin b → Set (Fin n)}

/-- Assume [no hidden confounding](hyp:hnoconf), [joint independence of the
named latent inputs](hyp:hind), [a nonnegative regularity constant](hyp:L),
[continuous mechanisms Lipschitz with that constant](hyp:hcont), and
[categorical propensities Lipschitz with that constant](hyp:hprop). For
[two collections of node values](hyp:x,y) whose assignments on the chosen
node set are [admissible for the first collection](hyp:ht) and [admissible for
the second](hyp:ht'), if [a scalar summary is Lipschitz with constant one](hyp:hf)
and [integrable under the first intervened simulation](hyp:hfi) and
[under the second](hyp:hfj), then [the absolute difference of its interventional
means is at most the history expansion factor raised to the number of nodes,
times the sum of distances between the assigned values](goal). -/
-- @node: canonical_assignment_mean_transport
lemma canonical_assignment_mean_transport
    (M : CanonicalSCM kind dims dag G C) (hnoconf : NoHiddenConfounding G)
    (hind : LatentBlocksIndependent M.toEuclideanSCM) (L : ℝ≥0)
    (hcont : ContinuousMechanismsLipschitz M.toEuclideanSCM L)
    (hprop : CategoricalPropensityLipschitz M.toEuclideanSCM M.f L)
    (S : Finset (Fin n)) (x y : ∀ i, L1Vec (valueDim (kind i)))
    (ht : AdmissibleIntervention kind (fun i => if i ∈ S then some (x i) else none))
    (ht' : AdmissibleIntervention kind (fun i => if i ∈ S then some (y i) else none))
    (f : Joint kind → ℝ) (hf : LipschitzWith 1 f)
    (hfi : Integrable (fun u => f (intervenedEval M.toEuclideanSCM
      (fun i => if i ∈ S then some (x i) else none) u)) M.latentLaw)
    (hfj : Integrable (fun u => f (intervenedEval M.toEuclideanSCM
      (fun i => if i ∈ S then some (y i) else none) u)) M.latentLaw) :
    |(∫ u, f (intervenedEval M.toEuclideanSCM
        (fun i => if i ∈ S then some (x i) else none) u) ∂M.latentLaw) -
      ∫ u, f (intervenedEval M.toEuclideanSCM
        (fun i => if i ∈ S then some (y i) else none) u) ∂M.latentLaw| ≤
      (historyExpansion kind L : ℝ)^n * ∑ i ∈ S, dist (x i) (y i) := by
  let F := intervenedEval M.toEuclideanSCM (fun i => if i ∈ S then some (x i) else none)
  let H := intervenedEval M.toEuclideanSCM (fun i => if i ∈ S then some (y i) else none)
  have hF : Measurable F := by
    first | fun_prop | exact evalSteps_measurable M.toEuclideanSCM _ (n*n+n)
  have hH : Measurable H := by
    first | fun_prop | exact evalSteps_measurable M.toEuclideanSCM _ (n*n+n)
  have hfm : Integrable f (M.latentLaw.map F) :=
    (integrable_map_measure hf.continuous.aestronglyMeasurable hF.aemeasurable).2 hfi
  have hfn : Integrable f (M.latentLaw.map H) :=
    (integrable_map_measure hf.continuous.aestronglyMeasurable hH.aemeasurable).2 hfj
  have hW := canonical_assignment_history_transport M hnoconf hind L hcont hprop S x y ht ht'
  have hcost : (historyExpansion kind L : ℝ≥0∞)^n * ∑ i ∈ S, edist (x i) (y i) =
      ENNReal.ofReal ((historyExpansion kind L : ℝ)^n * ∑ i ∈ S, dist (x i) (y i)) := by
    simp_rw [edist_dist]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => dist_nonneg),
      ← ENNReal.coe_pow, ← ENNReal.ofReal_coe_nnreal,
      ← ENNReal.ofReal_mul (by positivity)]
    rfl
  rw [hcost] at hW
  have hp := (Toolkit.Foundations.MeasureTheory.lipschitzContrast_le_wasserstein1
    hf hfm hfn).trans hW
  have hn := (Toolkit.Foundations.MeasureTheory.lipschitzContrast_le_wasserstein1
    hf.neg hfm.neg hfn.neg).trans hW
  have hR : 0 ≤ (historyExpansion kind L : ℝ)^n * ∑ i ∈ S, dist (x i) (y i) := by positivity
  have hp' := (ENNReal.ofReal_le_ofReal_iff hR).mp hp
  have hn' := (ENNReal.ofReal_le_ofReal_iff hR).mp hn
  simp only [Toolkit.Foundations.MeasureTheory.lipschitzContrast, Pi.neg_apply, integral_neg,
    integral_map hF.aemeasurable hf.continuous.aestronglyMeasurable,
    integral_map hH.aemeasurable hf.continuous.aestronglyMeasurable] at hp' hn'
  exact abs_le.mpr ⟨by linarith, hp'⟩

-- @node: descendantMean_lipschitz
/-- For [a scalar treatment](hyp:hT), [a scalar outcome](hyp:hY), and
[a nonnegative regularity constant](hyp:L), assume [jointly independent
named latent inputs](hyp:hind), [no hidden confounding](hyp:hnoconf),
[continuous mechanisms Lipschitz with that constant](hyp:hcont), [categorical
propensities Lipschitz with that constant](hyp:hprop), and [the given uniform
bound on variables](hyp:hbound). Then [for any two admissible joint vectors
and any two admissible treatment doses, the absolute difference of descendant
means is bounded by the dose Lipschitz constant times the sum of the distance
between joint vectors and the absolute dose difference](goal). -/
lemma descendantMean_lipschitz (M : CanonicalSCM kind dims dag G C) (T Y : Fin n)
    (hT : valueDim (kind T) = 1) (hY : valueDim (kind Y) = 1) (K : ℝ) (L : ℝ≥0)
    (hind : LatentBlocksIndependent M.toEuclideanSCM) (hnoconf : NoHiddenConfounding G)
    (hcont : ContinuousMechanismsLipschitz M.toEuclideanSCM L)
    (hprop : CategoricalPropensityLipschitz M.toEuclideanSCM M.f L)
    (hbound : VariablesBoundedAt M.toEuclideanSCM K) :
    ∀ a a' : Joint kind, admissibleJoint a → admissibleJoint a' → ∀ t t' : ℝ,
      AdmissibleIntervention kind (singleIntervention T t) →
      AdmissibleIntervention kind (singleIntervention T t') →
      |descendantMean M T Y hY a t-descendantMean M T Y hY a' t'| ≤
        doseLip kind L * (dist a a' + |t-t'|) := by
  intro a a' ha ha' t t' ht ht'
  let S := insert T (nonDescendantNodes (dag := dag) T)
  let x : ∀ i, L1Vec (valueDim (kind i)) := fun i =>
    if i = T then WithLp.toLp 1 (fun _ => t) else WithLp.toLp 1 (fun j => a.ofLp ⟨i,j⟩)
  let y : ∀ i, L1Vec (valueDim (kind i)) := fun i =>
    if i = T then WithLp.toLp 1 (fun _ => t') else WithLp.toLp 1 (fun j => a'.ofLp ⟨i,j⟩)
  have hassign (v : Joint kind) (s : ℝ) :
      (fun i => if i ∈ S then some (if i = T then WithLp.toLp 1 (fun _ => s) else
        WithLp.toLp 1 (fun j => v.ofLp ⟨i,j⟩)) else none) =
      (fun i => if i = T then some (WithLp.toLp 1 (fun _ => s)) else
        if i ∈ nonDescendantNodes (dag := dag) T then
          some (WithLp.toLp 1 (fun j => v.ofLp ⟨i,j⟩)) else none) := by
    funext i
    by_cases hi : i = T <;> simp [S, hi]
  have hadm (v : Joint kind) (hv : admissibleJoint v) (s : ℝ)
      (hs : AdmissibleIntervention kind (singleIntervention T s)) :
      AdmissibleIntervention kind (fun i => if i ∈ S then some
        (if i = T then WithLp.toLp 1 (fun _ => s) else
          WithLp.toLp 1 (fun j => v.ofLp ⟨i,j⟩)) else none) := by
    rw [hassign]
    intro i z hz
    by_cases hi : i = T
    · exact hs i z (by simpa [singleIntervention, hi] using hz)
    · by_cases hn : i ∈ nonDescendantNodes (dag := dag) T
      · exact hv i z (by simpa [hi, hn] using hz)
      · simp [hi, hn] at hz
  have hxi : Integrable (fun u => scalarOutcome Y hY (intervenedEval M.toEuclideanSCM
      (fun i => if i ∈ S then some (x i) else none) u)) M.latentLaw :=
    interventional_scalarOutcome_integrable M.toEuclideanSCM L hcont K hbound _ (hadm a ha t ht) Y hY
  have hyi : Integrable (fun u => scalarOutcome Y hY (intervenedEval M.toEuclideanSCM
      (fun i => if i ∈ S then some (y i) else none) u)) M.latentLaw :=
    interventional_scalarOutcome_integrable M.toEuclideanSCM L hcont K hbound _ (hadm a' ha' t' ht') Y hY
  have h := canonical_assignment_mean_transport M hnoconf hind L hcont hprop S x y
    (hadm a ha t ht) (hadm a' ha' t' ht') (scalarOutcome Y hY)
    (scalarOutcome_lipschitz Y hY) hxi hyi
  have hsum : (∑ i ∈ S, dist (x i) (y i)) ≤ dist a a' + |t-t'| := by
    have hnot : T ∉ nonDescendantNodes (dag := dag) T := by simp [nonDescendantNodes]
    rw [Finset.sum_insert hnot]
    have hTdist : dist (x T) (y T) = |t-t'| := by
      simp [x, y, PiLp.dist_eq_of_L1, hT, Real.dist_eq]
    rw [hTdist]
    have hsub : (∑ i ∈ nonDescendantNodes (dag := dag) T, dist (x i) (y i)) ≤ dist a a' := by
      rw [PiLp.dist_eq_of_L1, Fintype.sum_sigma]
      calc
        _ = ∑ i ∈ nonDescendantNodes (dag := dag) T,
            ∑ j, dist (a.ofLp ⟨i,j⟩) (a'.ofLp ⟨i,j⟩) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hne : i ≠ T := (Finset.mem_filter.mp hi).2.1
          simp only [x, y, hne, if_false, PiLp.dist_eq_of_L1]
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => Finset.sum_nonneg fun _ _ => dist_nonneg)
    linarith
  have hpow : (historyExpansion kind L : ℝ)^n = doseLip kind L := by
    change (1 + (L : ℝ) * categoricalFactor kind)^n = ((L : ℝ) * categoricalFactor kind+1)^n
    congr 1
    ring
  have hfinal := h.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
  dsimp only [x, y] at hfinal
  rw [hassign, hassign, hpow] at hfinal
  exact hfinal


end
end Papers.TbsNeuralCausalPi

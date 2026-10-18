module
public import Papers.TbsNeuralCausalPi.Setup.Optimization
public import Papers.TbsNeuralCausalPi.Setup.Assumptions.Model
public import Papers.TbsNeuralCausalPi.Helpers.StructuralApprox
public import Papers.TbsNeuralCausalPi.Helpers.NetworkClipping
public import Papers.TbsNeuralCausalPi.Helpers.StructuralNormalization
public import Papers.TbsNeuralCausalPi.Helpers.InterventionalMoments
public import Papers.TbsNeuralCausalPi.Helpers.DoseResponseNonDescendant
public import Papers.TbsNeuralCausalPi.Helpers.RegressionCongruence
public import Mathlib.Topology.MetricSpace.Lipschitz
/-! # Bounded-box reduction for uniformly bounded interventions

The box is derived from the fixed model and intervention bound. Projection keeps
categorical labels unchanged. The resulting model has the original latent laws,
and its structural maps admit uniform neural approximation on their full domains.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.cdot false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedTactic false
open MeasureTheory
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)} {C : Fin b → Set (Fin n)}

/-- For [a canonical causal model M](hyp:M), [a nonnegative radius B](hyp:B),
[a node i](hyp:i), and [a structural input x at that node](hyp:x), [the structural
box projection](goal) clamps each coordinate of x to the interval from −B to B. -/
-- @node: structuralBoxProjection
def structuralBoxProjection (M : CanonicalSCM kind dims dag G C) (B : ℝ≥0) (i : Fin n)
    (x : Input kind dims dag C i) : Input kind dims dag C i :=
  WithLp.toLp 1 (fun j => max (-(B : ℝ)) (min (x.ofLp j) B))

-- @node: structuralBoxProjection_measurable
/-- For [a nonnegative box radius B](hyp:B), [clamping the structural input
coordinates at node i of model M to the box of radius B is measurable](goal). -/
@[fun_prop] lemma structuralBoxProjection_measurable
    (M : CanonicalSCM kind dims dag G C) (B : ℝ≥0) (i : Fin n) :
    Measurable (structuralBoxProjection M B i) := by
  unfold structuralBoxProjection
  fun_prop

-- @node: structuralBoxProjection_lipschitz
/-- For [a nonnegative box radius B](hyp:B), [clamping structural input
coordinates at node i of model M to the box of radius B is 1-Lipschitz in the
sum-of-absolute-differences metric](goal). -/
lemma structuralBoxProjection_lipschitz
    (M : CanonicalSCM kind dims dag G C) (B : ℝ≥0) (i : Fin n) :
    LipschitzWith 1 (structuralBoxProjection M B i) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, PiLp.dist_eq_of_L1, Real.dist_eq]
  exact Finset.sum_le_sum (fun j _ =>
    coordinateClamp_coordinate_dist (-(B : ℝ)) B (x.ofLp j) (y.ofLp j))

/-- For [a nonnegative box radius B](hyp:B), if [every categorical node's number
of labels is at most B](hyp:hlabels) and [x is admissible at node i](hyp:hx),
[clamping x to the box of radius B preserves admissibility](goal). -/
-- @node: structuralBoxProjection_mem_domain
lemma structuralBoxProjection_mem_domain
    (M : CanonicalSCM kind dims dag G C) (B : ℝ≥0)
    (hlabels : ∀ i k, kind i = Sum.inr k → (k : ℝ) ≤ B)
    (i : Fin n) (x : Input kind dims dag C i) (hx : x ∈ M.domain i) :
    structuralBoxProjection M B i x ∈ M.domain i := by
  refine ⟨?_, Set.mem_univ _⟩
  intro p k hk
  obtain ⟨label, hlabel⟩ := hx.1 p k hk
  refine ⟨label, ?_⟩
  intro j
  change max (-(B : ℝ)) (min (x.ofLp (.inl ⟨p, j⟩)) B) = _
  rw [hlabel j]
  have hupper : ((label.val + 1 : ℕ) : ℝ) ≤ B :=
    (by exact_mod_cast label.isLt : ((label.val + 1 : ℕ) : ℝ) ≤ k).trans
      (hlabels p.val k hk)
  rw [min_eq_left hupper, max_eq_right ((neg_nonpos.mpr B.coe_nonneg).trans (Nat.cast_nonneg _))]

-- @node: boxTruncatedSCM_simplex
/-- For [a nonnegative box radius B](hyp:B), if [every categorical node's number
of labels is at most B](hyp:hlabels), [at every categorical node, evaluating the
original propensity map after clamping any admissible input to the box gives
a probability vector over that node's categories](goal). -/
lemma boxTruncatedSCM_simplex
    (M : CanonicalSCM kind dims dag G C) (B : ℝ≥0)
    (hlabels : ∀ i k, kind i = Sum.inr k → (k : ℝ) ≤ B) :
    ∀ i k (h : kind i = Sum.inr k) x,
      x ∈ admissibleStructuralInputs kind dims dag (canonicalIncidence C) i →
      (fun j : Fin k => (M.f i (structuralBoxProjection M B i x)).ofLp
        (Fin.cast (congrArg outputDim h).symm j)) ∈ probabilitySimplex k := by
  intro i k h x hx
  exact M.simplex i k h _ (structuralBoxProjection_mem_domain M B hlabels i x
    ⟨hx, Set.mem_univ _⟩).1

/-- Given [a canonical causal model M](hyp:M), [a nonnegative box radius B](hyp:B),
and [the requirement that every categorical node's number of labels is at most B](hyp:hlabels),
[the box-truncated model](goal) composes each structural map with coordinate
clamping to the box of radius B, retaining the model's categorical positivity,
latent component structure, and latent block laws. Its structural maps remain
measurable and its categorical outputs remain probability vectors. -/
-- @node: boxTruncatedSCM
def boxTruncatedSCM (M : CanonicalSCM kind dims dag G C) (B : ℝ≥0)
    (hlabels : ∀ i k, kind i = Sum.inr k → (k : ℝ) ≤ B) :
    CanonicalSCM kind dims dag G C :=
  { categoricalPositive := M.categoricalPositive
    component := M.component
    exhaustive := M.exhaustive
    distinct := M.distinct
    f := fun i => M.f i ∘ structuralBoxProjection M B i
    structuralMeasurable := fun i =>
      (M.structuralMeasurable i).comp (structuralBoxProjection_measurable M B i)
    blockLaw := M.blockLaw
    simplex := boxTruncatedSCM_simplex M B hlabels }

/-- For [a nonnegative Lipschitz bound L](hyp:L) and [a nonnegative box radius B](hyp:B),
if [every categorical node's number of labels is at most B](hyp:hlabels) and
[the original model's structural maps are L-Lipschitz on their admissible domains](hyp:hclass),
[the box-truncated model's structural maps are also L-Lipschitz on their
admissible domains](goal). -/
-- @node: boxTruncatedSCM_regular
lemma boxTruncatedSCM_regular
    (M : CanonicalSCM kind dims dag G C) (L : ℝ≥0) (B : ℝ≥0)
    (hlabels : ∀ i k, kind i = Sum.inr k → (k : ℝ) ≤ B)
    (hclass : M ∈ canonicalClass (domainLipClass M L)) :
    let MB := boxTruncatedSCM M B hlabels
    MB ∈ canonicalClass (domainLipClass MB L) := by
  dsimp only
  intro i x hx y hy
  exact (hclass i (structuralBoxProjection_mem_domain M B hlabels i x hx)
    (structuralBoxProjection_mem_domain M B hlabels i y hy)).trans
      (mul_le_mul le_rfl (by simpa using
        (structuralBoxProjection_lipschitz M B i).edist_le_mul x y) bot_le bot_le)

/-- For [a nonnegative Lipschitz bound L](hyp:L), suppose [the continuous
mechanisms are L-Lipschitz](hyp:hcont) and [the intervention coordinate bound H
is nonnegative](hyp:hH). Then [there is a common nonnegative coordinate bound Q
for every evaluation stage up to N, every admissible intervention whose assigned
coordinates have absolute value at most H, and every latent input whose
non-Gumbel block coordinates have absolute value at most K](goal). -/
-- @node: evalSteps_uniform_bounded_interventions
lemma evalSteps_uniform_bounded_interventions (M : EuclideanSCM kind dims)
    (L : ℝ≥0) (hcont : ContinuousMechanismsLipschitz M L)
    (K H : ℝ) (hH : 0 ≤ H) (N : ℕ) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ r ≤ N, ∀ t : LawIntervention kind,
      (∀ i v, t.val i = some v → ∀ j, |v.ofLp j| ≤ H) →
      ∀ u : Exogenous kind dims, (∀ k j, |(blockProjection k u).ofLp j| ≤ K) →
      ∀ i j, |(evalSteps M t.val u r).ofLp ⟨i,j⟩| ≤ Q := by
  induction N with
  | zero =>
    refine ⟨0, le_rfl, ?_⟩
    intro r hr t ht u hu i j
    have : r = 0 := by omega
    subst r
    simp [evalSteps]
  | succ N ih =>
    obtain ⟨Q, hQ, hbound⟩ := ih
    choose B hB hnode using fun i => nodeValue_bounded_on_coordinate_boxes M L hcont i Q K
    let Q' := max Q (max H (∑ i, B i))
    refine ⟨Q', hQ.trans (le_max_left _ _), ?_⟩
    intro r hr t ht u hu i j
    by_cases hrN : r ≤ N
    · exact (hbound r hrN t ht u hu i j).trans (le_max_left _ _)
    · have he : r = N + 1 := by omega
      subst r
      simp only [evalSteps, WithLp.ofLp_toLp]
      by_cases hi : M.dag.topoOrder i = N
      · simp only [hi, if_true]
        cases he : t.val i with
        | some v =>
          simp only [Option.getD_some]
          exact (ht i v he j).trans ((le_max_left _ _).trans (le_max_right _ _))
        | none =>
          simp only [Option.getD_none]
          have hn := hnode i _ u (evalSteps_structuralInput_mem_domain M t.val t.property u i N hi)
            (hbound N le_rfl t ht u hu) hu j
          have hsum := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => hB k)
            (Finset.mem_univ i)
          exact hn.trans (hsum.trans ((le_max_right _ _).trans (le_max_right _ _)))
      · simp only [hi, if_false]
        exact (hbound N le_rfl t ht u hu i j).trans (le_max_left _ _)

/-- If [node i is continuous with d coordinates](hyp:hi), [the continuous
mechanism extracted from the canonical model equals its structural map at i](goal). -/
-- @node: canonical_continuousMap_eq
lemma canonical_continuousMap_eq (M : CanonicalSCM kind dims dag G C)
    (i : Fin n) (d : ℕ) (hi : kind i = .inl d) :
    M.toEuclideanSCM.continuousMap i = M.f i := by
  have h (κ : NodeKind) (hk : ∀ k, κ = .inr k → 0 < k)
      (w : L1Vec (outputDim κ)) (hκ : κ = .inl d) :
      (match (generalizing := false) h : κ with
      | .inl d => WithLp.toLp 1 (fun j =>
          (cast (congrArg ObservedValue h) (canonicalSelector κ hk w 0)).ofLp j)
      | .inr _ => 0) = w := by
    subst κ
    rfl
  funext x
  have hm : M.toEuclideanSCM.f i x 0 =
      canonicalSelector (kind i) (M.positive_categories i) (M.f i x) 0 :=
    (canonicalSelector_eq (kind i) (M.positive_categories i) _ _).symm
  unfold EuclideanSCM.continuousMap
  rw [hm]
  exact h (kind i) (M.positive_categories i) (M.f i x) hi

/-- For [a nonnegative box radius B](hyp:B), if [every coordinate of x has
absolute value at most B](hyp:hx), [the structural box projection leaves x unchanged](goal). -/
-- @node: structuralBoxProjection_eq_self
lemma structuralBoxProjection_eq_self (M : CanonicalSCM kind dims dag G C)
    (B : ℝ≥0) (i : Fin n) (x : Input kind dims dag C i) (hx : x ∈ inputCube B i) :
    structuralBoxProjection M B i x = x := by
  apply WithLp.ofLp_injective
  funext j
  change max (-(B : ℝ)) (min (x.ofLp j) B) = x.ofLp j
  rw [min_eq_left (abs_le.mp (hx j)).2, max_eq_right (abs_le.mp (hx j)).1]

/-- For [a nonnegative box radius B](hyp:B), suppose [every categorical node's
number of labels is at most B](hyp:hlabels) and [the structural input at node i
formed from the joint values v and latent input u lies in the box of radius B](hyp:hx).
Then [the original and box-truncated models produce the same value at node i
from v and u](goal). -/
-- @node: boxTruncatedSCM_nodeValue_eq
lemma boxTruncatedSCM_nodeValue_eq (M : CanonicalSCM kind dims dag G C)
    (B : ℝ≥0) (hlabels : ∀ i k, kind i = Sum.inr k → (k : ℝ) ≤ B)
    (i : Fin n) (v : Joint kind) (u : Exogenous kind dims)
    (hx : structuralInput M.toEuclideanSCM i v u ∈ inputCube B i) :
    nodeValue (boxTruncatedSCM M B hlabels).toEuclideanSCM i v u =
      nodeValue M.toEuclideanSCM i v u := by
  have hf := structuralBoxProjection_eq_self M B i _ hx
  have hm : canonicalMechanism (boxTruncatedSCM M B hlabels) i
      (structuralInput M.toEuclideanSCM i v u) (categoricalNoise i u) =
      canonicalMechanism M i (structuralBoxProjection M B i
        (structuralInput M.toEuclideanSCM i v u)) (categoricalNoise i u) := rfl
  rw [hf] at hm
  have hleft : nodeValue (boxTruncatedSCM M B hlabels).toEuclideanSCM i v u =
      observedValueEmbedding (kind i) ((boxTruncatedSCM M B hlabels).toEuclideanSCM.f i
        (structuralInput (boxTruncatedSCM M B hlabels).toEuclideanSCM i v u) (categoricalNoise i u)) :=
    (observedValueEmbedding_eq _ _).symm
  have hright : nodeValue M.toEuclideanSCM i v u =
      observedValueEmbedding (kind i) (M.toEuclideanSCM.f i
        (structuralInput M.toEuclideanSCM i v u) (categoricalNoise i u)) :=
    (observedValueEmbedding_eq _ _).symm
  rw [hleft, hright]
  convert congrArg (observedValueEmbedding (kind i)) hm using 1 <;>
    simp only [CanonicalSCM.toEuclideanSCM, structuralInput, boxTruncatedSCM]
  congr 2
  apply WithLp.ofLp_injective
  funext j
  rcases j with ⟨p,j⟩ | ⟨k,j⟩ <;> rfl

/-- For [a nonnegative box radius B](hyp:B), if [every categorical node's number
of labels is at most B](hyp:hlabels) and [every structural input used by the
original model before evaluation stage N lies in the box of radius B](hyp:hinputs),
[the original and box-truncated models have identical joint values at stage N
under intervention t and latent input u](goal). -/
-- @node: boxTruncatedSCM_evalSteps_eq
lemma boxTruncatedSCM_evalSteps_eq (M : CanonicalSCM kind dims dag G C)
    (B : ℝ≥0) (hlabels : ∀ i k, kind i = Sum.inr k → (k : ℝ) ≤ B)
    (t : Intervention kind) (u : Exogenous kind dims) (N : ℕ)
    (hinputs : ∀ r < N, ∀ i, dag.topoOrder i = r →
      structuralInput M.toEuclideanSCM i (evalSteps M.toEuclideanSCM t u r) u ∈ inputCube B i) :
    evalSteps (boxTruncatedSCM M B hlabels).toEuclideanSCM t u N =
      evalSteps M.toEuclideanSCM t u N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    have he := ih (fun r hr => hinputs r (by omega))
    apply WithLp.ofLp_injective
    funext ⟨i,j⟩
    simp only [evalSteps, WithLp.ofLp_toLp]
    change (if dag.topoOrder i = N then _ else _) =
      (if dag.topoOrder i = N then _ else _)
    rw [he]
    by_cases hi : dag.topoOrder i = N
    · simp only [hi, if_true]
      rw [boxTruncatedSCM_nodeValue_eq M B hlabels i _ u (hinputs N (by omega) i hi)]
    · simp only [hi, if_false]

/-- For [a nonnegative Lipschitz bound L](hyp:L), suppose [the structural maps
are L-Lipschitz on their admissible domains](hyp:hclass), [the observed and
non-Gumbel latent variables are bounded by K](hyp:hbound), and [R is positive](hyp:hR).
Then [there is a positive box radius B at least K and R containing all categorical
labels such that, for every admissible intervention assigning continuous values
of maximum absolute coordinate at most R, all final structural inputs lie in
that box almost surely and box truncation preserves its interventional law;
it also preserves the observational law and the variable bound K](goal). -/
-- @node: truncate_interventionalLaw_eq
lemma truncate_interventionalLaw_eq
    (M : CanonicalSCM kind dims dag G C) (L : ℝ≥0) (K R : ℝ)
    (hclass : M ∈ canonicalClass (domainLipClass M L))
    (hbound : VariablesBoundedAt M.toEuclideanSCM K) (hR : 0 < R) :
    ∃ B : ℝ≥0, 0 < B ∧ K ≤ B ∧ R ≤ B ∧
      ∃ hlabels : ∀ i k, kind i = Sum.inr k → (k : ℝ) ≤ B,
      let MB := boxTruncatedSCM M B hlabels
      (∀ t : LawIntervention kind,
        (∀ i d, kind i = Sum.inl d → ∀ v, t.val i = some v → ‖v.ofLp‖ ≤ R) →
        (∀ᵐ u ∂M.latentLaw, ∀ i,
          structuralInput M.toEuclideanSCM i
            (intervenedEval M.toEuclideanSCM t.val u) u ∈ inputCube B i) ∧
        interventionalLaw M.toEuclideanSCM t = interventionalLaw MB.toEuclideanSCM t) ∧
      observationalLaw M.toEuclideanSCM = observationalLaw MB.toEuclideanSCM ∧
      VariablesBoundedAt MB.toEuclideanSCM K := by
  have hcont : ContinuousMechanismsLipschitz M.toEuclideanSCM L := by
    intro i d hi
    rw [canonical_continuousMap_eq M i d hi]
    exact hclass i
  let H : ℝ := R + ∑ i : Fin n, (noiseDim (kind i) : ℝ)
  have hH : 0 ≤ H := add_nonneg hR.le (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _))
  have htH (t : LawIntervention kind)
      (ht : ∀ i d, kind i = Sum.inl d → ∀ v, t.val i = some v → ‖v.ofLp‖ ≤ R) :
      ∀ i v, t.val i = some v → ∀ j, |v.ofLp j| ≤ H := by
    intro i v hv j
    have hcases : (∃ d, kind i = .inl d) ∨ (∃ k, kind i = .inr k) := by
      cases kind i with
      | inl d => exact Or.inl ⟨d, rfl⟩
      | inr k => exact Or.inr ⟨k, rfl⟩
    rcases hcases with ⟨d, hi⟩ | ⟨k, hi⟩
    ·
      have hRj : |v.ofLp j| ≤ R := (show |v.ofLp j| ≤ ‖v.ofLp‖ by simpa using norm_le_pi_norm v.ofLp j).trans (ht i d hi v hv)
      exact hRj.trans (le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)))
    · have hadm := t.property i v hv
      have hcat : ∃ label : Fin k, ∀ j, v.ofLp j = (label.val + 1 : ℕ) := by
        split at hadm
        · rename_i d hd
          simp [hi] at hd
        · rename_i k' hk'
          have he : k' = k := Sum.inr.inj (hk'.symm.trans hi)
          subst k'
          exact hadm
      obtain ⟨label, hlabel⟩ := hcat
      rw [hlabel j, abs_of_nonneg (Nat.cast_nonneg _)]
      have hk : (k : ℝ) ≤ ∑ i : Fin n, (noiseDim (kind i) : ℝ) := by
        have hs := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) =>
          (Nat.cast_nonneg (noiseDim (kind i)) : (0 : ℝ) ≤ _)) (Finset.mem_univ i)
        simpa only [hi, noiseDim] using hs
      exact (by exact_mod_cast Nat.succ_le_of_lt label.isLt : ((label.val + 1 : ℕ) : ℝ) ≤ k).trans
        (hk.trans (le_add_of_nonneg_left hR.le))
  obtain ⟨Q, hQ, hsteps⟩ := evalSteps_uniform_bounded_interventions
    M.toEuclideanSCM L hcont K H hH (n*n+n)
  let B : ℝ≥0 := ⟨1 + |K| + H + Q, by positivity⟩
  have hBK : K ≤ B := by change K ≤ 1 + |K| + H + Q; linarith [le_abs_self K]
  have hBH : H ≤ B := by change H ≤ 1 + |K| + H + Q; linarith [abs_nonneg K]
  have hBQ : Q ≤ B := by change Q ≤ 1 + |K| + H + Q; linarith [abs_nonneg K]
  have hlabels : ∀ i k, kind i = Sum.inr k → (k : ℝ) ≤ B := by
    intro i k hi
    have hs := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) =>
      (Nat.cast_nonneg (noiseDim (kind i)) : (0 : ℝ) ≤ _)) (Finset.mem_univ i)
    have hk : (k : ℝ) ≤ H := by dsimp [H]; simpa only [hi, noiseDim] using hs.trans (le_add_of_nonneg_left hR.le)
    exact hk.trans hBH
  have hBR : R ≤ B := (le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _))).trans hBH
  have heval (t : LawIntervention kind)
      (ht : ∀ i d, kind i = Sum.inl d → ∀ v, t.val i = some v → ‖v.ofLp‖ ≤ R)
      (u : Exogenous kind dims) (hu : ∀ k j, |(blockProjection k u).ofLp j| ≤ K) :
      intervenedEval (boxTruncatedSCM M B hlabels).toEuclideanSCM t.val u =
        intervenedEval M.toEuclideanSCM t.val u := by
    apply boxTruncatedSCM_evalSteps_eq
    intro r hr i hi j
    rcases j with ⟨p,j⟩ | ⟨k,j⟩
    · exact (hsteps r hr.le t (htH t ht) u hu p.val j).trans hBQ
    · exact (hu k.val j).trans hBK
  have hlaw (t : LawIntervention kind)
      (ht : ∀ i d, kind i = Sum.inl d → ∀ v, t.val i = some v → ‖v.ofLp‖ ≤ R) :
      interventionalLaw M.toEuclideanSCM t =
        interventionalLaw (boxTruncatedSCM M B hlabels).toEuclideanSCM t := by
    apply Measure.map_congr
    filter_upwards [hbound.2] with u hu
    exact (heval t ht u hu.2).symm
  have hnone : ∀ i d, kind i = Sum.inl d → ∀ v,
      (noIntervention kind).val i = some v → ‖v.ofLp‖ ≤ R := by
    intro i d hi v hv
    cases hv
  refine ⟨B, by change 0 < 1 + |K| + H + Q; positivity, hBK, hBR, hlabels, ?_,
    hlaw (noIntervention kind) hnone, hbound.1, ?_⟩
  · intro t ht
    refine ⟨?_, hlaw t ht⟩
    filter_upwards [hbound.2] with u hu i j
    rcases j with ⟨p,j⟩ | ⟨k,j⟩
    · exact (hsteps _ le_rfl t (htH t ht) u hu.2 p.val j).trans hBQ
    · exact (hu.2 k.val j).trans hBK
  · filter_upwards [hbound.2] with u hu
    have he := heval (noIntervention kind) hnone u hu.2
    change intervenedEval (boxTruncatedSCM M B hlabels).toEuclideanSCM (fun _ => none) u = _ at he
    rw [he]
    exact hu

/-- For [a nonnegative box radius B](hyp:B), suppose [every categorical node's
number of labels is at most B](hyp:hlabels), [K is at most B](hyp:hKB), and
[the observed and non-Gumbel latent variables are bounded by K](hyp:hbound).
Then [almost surely, box truncation preserves the observational evaluation and
fixes every original structural input under coordinate projection](goal). -/
-- @node: boxTruncatedSCM_observational_eval_eq
lemma boxTruncatedSCM_observational_eval_eq
    (M : CanonicalSCM kind dims dag G C) (B : ℝ≥0) (K : ℝ)
    (hlabels : ∀ i k, kind i = Sum.inr k → (k : ℝ) ≤ B) (hKB : K ≤ B)
    (hbound : VariablesBoundedAt M.toEuclideanSCM K) :
    ∀ᵐ u ∂M.latentLaw,
      intervenedEval (boxTruncatedSCM M B hlabels).toEuclideanSCM (fun _ => none) u =
        intervenedEval M.toEuclideanSCM (fun _ => none) u ∧
      ∀ i, structuralBoxProjection M B i (structuralInputRV M.toEuclideanSCM i u) =
        structuralInputRV M.toEuclideanSCM i u := by
  filter_upwards [hbound.2] with u hu
  have hfinal (i : Fin n) : structuralInputRV M.toEuclideanSCM i u ∈ inputCube B i := by
    rintro (⟨p,j⟩ | ⟨k,j⟩)
    · exact (hu.1 p.val j).trans hKB
    · exact (hu.2 k.val j).trans hKB
  refine ⟨?_, fun i => structuralBoxProjection_eq_self M B i _ (hfinal i)⟩
  apply boxTruncatedSCM_evalSteps_eq
  intro r hr i hi
  rintro (⟨p,j⟩ | ⟨k,j⟩)
  · change |(evalSteps M.toEuclideanSCM (fun _ => none) u r).ofLp ⟨p.val,j⟩| ≤ B
    rw [evalSteps_coordinate_eq_intervenedEval M.toEuclideanSCM _ u p.val r (by
      rw [← hi]
      exact dag.topoOrder_lt _ _ (dag.mem_parents.mp p.property)) j]
    exact (hu.1 p.val j).trans hKB
  · exact (hu.2 k.val j).trans hKB

-- @node: boxTruncatedSCM_atoms
/-- For [nonnegative Lipschitz and box bounds L and B](hyp:L,B), suppose
[every categorical node's number of labels is at most B](hyp:hlabels), [K is at
most B](hyp:hKB), [the structural maps are L-Lipschitz on admissible domains](hyp:hclass),
[latent blocks are independent](hyp:hind), [latent noise has the Gumbel decomposition](hyp:hdecomp),
[categorical mechanisms have the Gumbel argmax representation](hyp:hcat),
[continuous mechanisms are L-Lipschitz](hyp:hcont), [categorical propensities are
L-Lipschitz](hyp:hprop), and [observed and non-Gumbel latent variables are bounded
by K](hyp:hbound). Then [the box-truncated model retains latent block independence,
the Gumbel decomposition and argmax representation, both Lipschitz properties,
the variable bound K, and exactly the same latent law](goal). -/
lemma boxTruncatedSCM_atoms
    (M : CanonicalSCM kind dims dag G C) (L B : ℝ≥0) (K : ℝ)
    (hlabels : ∀ i k, kind i = Sum.inr k → (k : ℝ) ≤ B) (hKB : K ≤ B)
    (hclass : M ∈ canonicalClass (domainLipClass M L))
    (hind : LatentBlocksIndependent M.toEuclideanSCM)
    (hdecomp : LatentGumbelDecomposition M.toEuclideanSCM)
    (hcat : CategoricalGumbelArgmax M.toEuclideanSCM M.f)
    (hcont : ContinuousMechanismsLipschitz M.toEuclideanSCM L)
    (hprop : CategoricalPropensityLipschitz M.toEuclideanSCM M.f L)
    (hbound : VariablesBoundedAt M.toEuclideanSCM K) :
    let MB := boxTruncatedSCM M B hlabels
    LatentBlocksIndependent MB.toEuclideanSCM ∧
      LatentGumbelDecomposition MB.toEuclideanSCM ∧
      CategoricalGumbelArgmax MB.toEuclideanSCM MB.f ∧
      ContinuousMechanismsLipschitz MB.toEuclideanSCM L ∧
      CategoricalPropensityLipschitz MB.toEuclideanSCM MB.f L ∧
      VariablesBoundedAt MB.toEuclideanSCM K ∧ MB.latentLaw = M.latentLaw := by
  let MB := boxTruncatedSCM M B hlabels
  let := M.latentLaw_probability
  have he := boxTruncatedSCM_observational_eval_eq M B K hlabels hKB hbound
  have hs (i : Fin n) : structuralInputRV M.toEuclideanSCM i =ᵐ[M.latentLaw]
      structuralInputRV MB.toEuclideanSCM i := by
    filter_upwards [he] with u hu
    unfold structuralInputRV
    rw [hu.1]
    apply WithLp.ofLp_injective
    funext c
    rcases c with ⟨p,j⟩ | ⟨k,j⟩ <;> rfl
  have hp (i : Fin n) : (fun u => M.f i (structuralInputRV M.toEuclideanSCM i u))
      =ᵐ[M.latentLaw] (fun u => MB.f i (structuralInputRV MB.toEuclideanSCM i u)) := by
    filter_upwards [he, hs i] with u hu hsu
    change _ = M.f i (structuralBoxProjection M B i _)
    rw [← hsu, hu.2 i]
  have hlabel (i : Fin n) (k : ℕ) (hi : kind i = .inr k) (x : Input kind dims dag C i)
      (g : L1Vec k) :
      MB.toEuclideanSCM.categoricalLabel i k hi x g =
        M.toEuclideanSCM.categoricalLabel i k hi (structuralBoxProjection M B i x) g := rfl
  have hregTransfer (i : Fin n) (k : ℕ) (hi : kind i = .inr k) (j : Fin k)
      (w w' : Input kind dims dag C i → ℝ) (hw' : Measurable w')
      (hw : (fun u => w (structuralInputRV M.toEuclideanSCM i u)) =ᵐ[M.latentLaw]
        (fun u => w' (structuralInputRV MB.toEuclideanSCM i u)))
      (hreg : (fun u => w (structuralInputRV M.toEuclideanSCM i u)) =ᵐ[M.latentLaw]
        M.latentLaw[fun u => if M.toEuclideanSCM.categoricalLabel i k hi
          (structuralInputRV M.toEuclideanSCM i u)
          (WithLp.toLp 1 (fun j => (categoricalNoise i u).ofLp
            (Fin.cast (congrArg noiseDim hi).symm j))) = j then (1:ℝ) else 0 |
          MeasurableSpace.comap (structuralInputRV M.toEuclideanSCM i) (borel _)]) :
      (fun u => w' (structuralInputRV MB.toEuclideanSCM i u)) =ᵐ[MB.latentLaw]
        MB.latentLaw[fun u => if MB.toEuclideanSCM.categoricalLabel i k hi
          (structuralInputRV MB.toEuclideanSCM i u)
          (WithLp.toLp 1 (fun j => (categoricalNoise i u).ofLp
            (Fin.cast (congrArg noiseDim hi).symm j))) = j then (1:ℝ) else 0 |
          MeasurableSpace.comap (structuralInputRV MB.toEuclideanSCM i) (borel _)] := by
    have hsm (N : CanonicalSCM kind dims dag G C) :
        Measurable (structuralInputRV N.toEuclideanSCM i) := by
      first | fun_prop | skip
      unfold structuralInputRV intervenedEval
      fun_prop
    have hym : Measurable (fun u => if M.toEuclideanSCM.categoricalLabel i k hi
        (structuralInputRV M.toEuclideanSCM i u)
        (WithLp.toLp 1 (fun j => (categoricalNoise i u).ofLp
          (Fin.cast (congrArg noiseDim hi).symm j))) = j then (1:ℝ) else 0) := by
      first | fun_prop | skip
      have hcast (κ κ' : NodeKind) (h : κ = κ') :
          Measurable (cast (congrArg ObservedValue h)) := by
        subst κ'
        exact measurable_id
      have hc : Measurable (fun u => M.toEuclideanSCM.categoricalLabel i k hi
          (structuralInputRV M.toEuclideanSCM i u)
          (WithLp.toLp 1 (fun j => (categoricalNoise i u).ofLp
            (Fin.cast (congrArg noiseDim hi).symm j)))) := by
        unfold EuclideanSCM.categoricalLabel
        exact (hcast _ _ hi).comp ((M.toEuclideanSCM.structuralMeasurable i).comp
          ((hsm M).prodMk (by fun_prop)))
      exact Measurable.ite (hc (measurableSet_singleton j)) measurable_const measurable_const
    apply regression_version_congr_ae M.latentLaw _ _ (hsm M) (hsm MB) (hs i)
      _ _ (Integrable.of_bound hym.aestronglyMeasurable 1 (by
        filter_upwards [] with u
        split_ifs <;> norm_num)) _ w w' hw' hw hreg
    filter_upwards [he, hs i] with u hu hsu
    erw [hlabel, ← hsu, hu.2 i]
  have hregular := boxTruncatedSCM_regular M L B hlabels hclass
  refine ⟨hind, hdecomp, ?_, ?_, ?_, ?_, rfl⟩
  · refine ⟨?_, ?_, ?_, hcat.2.2.2⟩
    · intro i k hi x hx
      exact hcat.1 i k hi _ (structuralBoxProjection_mem_domain M B hlabels i x hx)
    · intro i k hi j
      apply hregTransfer i k hi j
        (fun x => (M.f i x).ofLp (Fin.cast (congrArg outputDim hi).symm j) /
          ∑ l, (M.f i x).ofLp l)
        (fun x => (MB.f i x).ofLp (Fin.cast (congrArg outputDim hi).symm j) /
          ∑ l, (MB.f i x).ofLp l)
      · have hm (j : Fin (outputDim (kind i))) : Measurable (fun x => (MB.f i x).ofLp j) :=
          (measurable_pi_apply j).comp (scm_ofLp_measurable.comp (MB.structuralMeasurable i))
        exact (hm _).div (Finset.measurable_sum _ (fun j _ => hm j))
      · filter_upwards [hp i] with u hu
        rw [hu]
      · exact hcat.2.1 i k hi j
    · intro i k hi x hx
      exact hcat.2.2.1 i k hi _ (structuralBoxProjection_mem_domain M B hlabels i x hx)
  · intro i d hi
    rw [canonical_continuousMap_eq MB i d hi]
    exact hregular i
  · refine ⟨?_, ?_⟩
    · intro i k hi
      exact hregular i
    · intro i k hi j
      apply hregTransfer i k hi j
        (fun x => (M.f i x).ofLp (Fin.cast (congrArg outputDim hi).symm j))
        (fun x => (MB.f i x).ofLp (Fin.cast (congrArg outputDim hi).symm j))
      · exact (measurable_pi_apply _).comp
          (scm_ofLp_measurable.comp (MB.structuralMeasurable i))
      · filter_upwards [hp i] with u hu
        rw [hu]
      · exact hprop.2 i k hi j
  · refine ⟨hbound.1, ?_⟩
    filter_upwards [he, hbound.2] with u hu hb
    change (∀ i j, |nodeCoordinate (intervenedEval MB.toEuclideanSCM (fun _ => none) u) i j| ≤ K) ∧ _
    rw [hu.1]
    exact hb

end
end Papers.TbsNeuralCausalPi

module
public import Papers.TbsNeuralCausalPi.Helpers.CounterexampleConditional
public import Papers.TbsNeuralCausalPi.Helpers.CanonicalCategoricalTransition
public import Papers.TbsNeuralCausalPi.Helpers.EvaluationKernels
/-! # Conditional propensities of arbitrary canonical models

Independence from the current intrinsic Gumbels identifies conditional label
probabilities on the actual structural-input law, including zero weights.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- Under [a probability law](hyp:μ), let [a random input](hyp:x) and
[a random noise vector](hyp:G) [be measurable](hyp:hx,hG), [be independent](hyp:hind),
and let [the noise have the standard product Gumbel law](hyp:hlaw). If
[a propensity map](hyp:p) [is measurable](hyp:hp), [its values at the random
input lie in the probability simplex almost surely](hyp:hps), and
[the number of categories is positive](hyp:hk), then for [a category](hyp:j),
[its propensity equals almost surely the conditional probability that the
canonical selector chooses it, given the random input](goal). -/
-- @node: canonicalSelector_condExp_of_indep
lemma canonicalSelector_condExp_of_indep
    {Ω X : Type*} {k : ℕ} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (x : Ω → X) (G : Ω → Fin k → ℝ) (hx : Measurable x) (hG : Measurable G)
    (hind : IndepFun x G μ) (hlaw : μ.map G = gumbelInputs k)
    (p : X → L1Vec k) (hp : Measurable p)
    (hps : ∀ᵐ u ∂μ, (p (x u)).ofLp ∈ probabilitySimplex k)
    (hk : ∀ m, Sum.inr k = (Sum.inr m : NodeKind) → 0 < m) (j : Fin k) :
    (fun u => (p (x u)).ofLp j) =ᵐ[μ]
      μ[fun u => if canonicalSelector (.inr k) hk (p (x u)) (WithLp.toLp 1 (G u)) = j
        then (1 : ℝ) else 0 | MeasurableSpace.comap x inferInstance] := by
  let sel : X × (Fin k → ℝ) → Fin k := fun v =>
    canonicalSelector (.inr k) hk (p v.1) (WithLp.toLp 1 v.2)
  have hs : Measurable sel := by
    apply firstArgmax_getD_measurable
    intro l
    fun_prop
  let F := fun v => if sel v = j then (1 : ℝ) else 0
  have hF : Measurable F :=
    Measurable.ite (hs (measurableSet_singleton j)) measurable_const measurable_const
  have h := counterexample_condExp_of_indep μ x G hx hG hind F hF
    (fun v => by dsimp [F]; split <;> norm_num)
  have hi (v : X) (hv : (p v).ofLp ∈ probabilitySimplex k) : (∫ w, F (v,w) ∂gumbelInputs k) = (p v).ofLp j := by
    have hs' : Measurable (fun w : Fin k → ℝ => sel (v,w)) := hs.comp measurable_prodMk_left
    have hm := congrArg (fun nu : Measure (Fin k) => nu {j})
      (canonicalSelector_categorical_law hk (p v) hv)
    change ((gumbelInputs k).map (fun w => sel (v,w))) {j} = _ at hm
    rw [Measure.map_apply hs' (measurableSet_singleton j)] at hm
    simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ (measurableSet_singleton j)] at hm
    simp only [Set.mem_singleton_iff, Set.indicator_apply, Pi.one_apply, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hm
    have hFeq : (fun w => F (v,w)) =
        {w | sel (v,w) = j}.indicator (fun _ => (1 : ℝ)) := by
      funext w
      simp [F, Set.indicator]
    have hI := integral_indicator_one (μ := gumbelInputs k)
      (hs' (measurableSet_singleton j))
    have hI' : (∫ w, {w | sel (v,w) = j}.indicator (fun _ => (1 : ℝ)) w
        ∂gumbelInputs k) = (gumbelInputs k).real ((fun w => sel (v,w)) ⁻¹' {j}) := by
      simpa only [Pi.one_def, Set.preimage, Set.mem_singleton_iff] using hI
    rw [hFeq, hI']
    exact (congrArg ENNReal.toReal hm).trans (ENNReal.toReal_ofReal (hv.1 j))
  rw [hlaw] at h
  have heq : (fun u => F (x u,G u)) = (fun u =>
      if canonicalSelector (.inr k) hk (p (x u)) (WithLp.toLp 1 (G u)) = j
        then (1 : ℝ) else 0) := by
    funext u
    dsimp only [F, sel]
    split_ifs <;> rfl
  rw [heq] at h
  filter_upwards [h.symm, hps] with u hu hp
  exact (hi (x u) hp).symm.trans hu


variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
  {C : Fin b → Set (Fin n)}

/-- For [a Euclidean causal model](hyp:M), [a node](hyp:i), and
[an exogenous realization](hyp:u), [the observational structural input at
that node lies in its declared domain](goal). -/
-- @node: structuralInputRV_mem_domain
lemma structuralInputRV_mem_domain (M : EuclideanSCM kind dims)
    (i : Fin n) (u : Exogenous kind dims) : structuralInputRV M i u ∈ M.domain i := by
  rw [counterexample_structuralInputRV_eq_visit]
  exact structuralInput_mem_domain_of_visitedHistory M i _ rfl _
    (evalSteps_mem_visitedHistoryDomain M _ (noIntervention_admissible kind) u _) u

/-- For [a canonical causal model](hyp:M), [a node](hyp:i), and
[a category count](hyp:k) with [the node categorical of that size](hyp:hi),
the propensity for [a category](hyp:j) [equals almost surely the conditional
probability of that category under the actual intrinsic noise, given the
node's observational structural input](goal). -/
-- @node: canonical_propensity_conditional_probability
lemma canonical_propensity_conditional_probability
    (M : CanonicalSCM kind dims dag G C) (i : Fin n) (k : ℕ)
    (hi : kind i = Sum.inr k) (j : Fin k) :
    (fun u => (M.f i (structuralInputRV M.toEuclideanSCM i u)).ofLp
      (Fin.cast (congrArg outputDim hi).symm j)) =ᵐ[M.latentLaw]
      M.latentLaw[fun u => if M.toEuclideanSCM.categoricalLabel i k hi
        (structuralInputRV M.toEuclideanSCM i u)
        (WithLp.toLp 1 (fun l => (categoricalNoise i u).ofLp
          (Fin.cast (congrArg noiseDim hi).symm l))) = j
        then (1 : ℝ) else 0 |
          MeasurableSpace.comap (structuralInputRV M.toEuclideanSCM i) (borel _)] := by
  letI := M.latentLaw_probability
  let X := structuralInputRV M.toEuclideanSCM i
  let noise := fun (u : Exogenous kind dims) (l : Fin k) =>
    (categoricalNoise i u).ofLp (Fin.cast (congrArg noiseDim hi).symm l)
  let p := fun x : StructuralInput kind dims dag (canonicalIncidence C) i =>
    WithLp.toLp 1 (fun l : Fin k => (M.f i x).ofLp
      (Fin.cast (congrArg outputDim hi).symm l))
  have hx : Measurable X := by
    change Measurable (fun u => structuralInput M.toEuclideanSCM i
      (evalSteps M.toEuclideanSCM (fun _ => none) u (n*n+n)) u)
    fun_prop
  have hnoise : Measurable noise := by
    dsimp only [noise]
    fun_prop
  have hp : Measurable p := by
    dsimp only [p]
    have hm := M.structuralMeasurable i
    fun_prop
  have hind : IndepFun X noise M.latentLaw := by
    have he : X = fun u => structuralInput M.toEuclideanSCM i
        (evalSteps M.toEuclideanSCM (fun _ => none) u (dag.topoOrder i)) u :=
      funext (counterexample_structuralInputRV_eq_visit M.toEuclideanSCM i)
    rw [he]
    exact structuralInput_evalSteps_indep_current_gumbels M.toEuclideanSCM
      (canonical_latent_blocks_independent M) i (fun _ => none) k hi
  have hps : ∀ᵐ u ∂M.latentLaw, (p (X u)).ofLp ∈ probabilitySimplex k := by
    apply ae_of_all
    intro u
    exact M.simplex i k hi (X u) (structuralInputRV_mem_domain M.toEuclideanSCM i u).1
  have h := canonicalSelector_condExp_of_indep M.latentLaw X noise hx hnoise hind
    (canonical_categorical_noise_law M i k hi) p hp hps
    (fun m hm => M.positive_categories i m (hi.trans hm)) j
  convert h using 1
  apply congrArg (fun f : Exogenous kind dims → ℝ =>
    M.latentLaw[f | MeasurableSpace.comap X (borel _)])
  funext u
  rw [canonicalMechanism_categoricalLabel_eq M i k hi]
  simp [p, X, noise, canonicalSelector, Fin.cast]

/-- For [a canonical causal model](hyp:M) and [a nonnegative Lipschitz
constant](hyp:L), if [every structural map is Lipschitz with that constant
on its declared domain](hyp:hL), then [the categorical propensities satisfy
the corresponding Lipschitz regularity and equal the actual conditional
label probabilities](goal). -/
-- @node: canonical_categoricalPropensityLipschitz_of_structural
lemma canonical_categoricalPropensityLipschitz_of_structural
    (M : CanonicalSCM kind dims dag G C) (L : ℝ≥0)
    (hL : ∀ i, LipschitzOnWith L (M.f i) (M.domain i)) :
    CategoricalPropensityLipschitz M.toEuclideanSCM M.f L := by
  refine ⟨fun i k hi => hL i, ?_⟩
  intro i k hi j
  exact canonical_propensity_conditional_probability M i k hi j

/-- For [a canonical causal model](hyp:M) and [a nonnegative Lipschitz
constant](hyp:L), if [every structural map is Lipschitz with that constant
on its declared domain](hyp:hL), then [the continuous mechanisms are
Lipschitz with the same constant on their declared domains](goal). -/
-- @node: canonical_continuousMechanismsLipschitz_of_structural
lemma canonical_continuousMechanismsLipschitz_of_structural
    (M : CanonicalSCM kind dims dag G C) (L : ℝ≥0)
    (hL : ∀ i, LipschitzOnWith L (M.f i) (M.domain i)) :
    ContinuousMechanismsLipschitz M.toEuclideanSCM L := by
  intro i d hi
  have he := funext (canonical_continuousMap_eq_weights M i d hi)
  rw [he]
  exact hL i

/-- For [output and Lipschitz budgets](hyp:K,L) and [a neural causal candidate](hyp:R),
if [the candidate satisfies the output and structural regularity restrictions](hyp:hR),
then [its continuous mechanisms and categorical propensities both satisfy
the prescribed Lipschitz regularity, with propensities equal to conditional
label probabilities](goal). -/
-- @node: restrictedCandidate_mechanism_regularity
lemma restrictedCandidate_mechanism_regularity
    {counts : Fin b → ℕ} {F0 : StructuralClass kind dims dag C}
    {F1 : GeneratorClass dims counts} (K L : ℝ≥0)
    (R : NCMIn kind dims dag G C counts F0 F1) (hR : restrictedCandidate K L R) :
    ContinuousMechanismsLipschitz R.canonical.toEuclideanSCM L ∧
      CategoricalPropensityLipschitz R.canonical.toEuclideanSCM R.canonical.f L := by
  exact ⟨canonical_continuousMechanismsLipschitz_of_structural R.canonical L
    (fun i => (hR i).1),
    canonical_categoricalPropensityLipschitz_of_structural R.canonical L
      (fun i => (hR i).1)⟩

/-- For [output and Lipschitz budgets](hyp:K,L), [a neural causal candidate](hyp:R)
that [satisfies the output and regularity restrictions](hyp:hR), and
[a node](hyp:i) with [a specified continuous dimension](hyp:d) such that
[the node has that continuous type](hyp:hi), [the norm of its canonical
structural output is bounded by the output budget throughout its declared
domain](goal). -/
lemma restrictedCandidate_continuous_output_bound
    {counts : Fin b → ℕ} {F0 : StructuralClass kind dims dag C}
    {F1 : GeneratorClass dims counts} (K L : ℝ≥0)
    (R : NCMIn kind dims dag G C counts F0 F1) (hR : restrictedCandidate K L R)
    (i : Fin n) (d : ℕ) (hi : kind i = Sum.inl d) :
    ∀ x ∈ R.canonical.domain i, ‖R.canonical.f i x‖ ≤ K := by
  rw [R.continuousEq i d hi]
  exact (hR i).2.1 d hi

end
end Papers.TbsNeuralCausalPi

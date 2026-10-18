module
public import Papers.TbsNeuralCausalPi.Helpers.CategoricalSelectorLaw
/-! # The categorical transition under the actual canonical input law

The non-Gumbel blocks retain their prescribed product law, independently of
the node's intrinsic Gumbels. Thus the canonical selector law applies to the
actual structural mechanism, including simplex boundary points.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section

/-- If [a coordinate selection](hyp:f) [is injective](hyp:hf), then
[selecting those coordinates from independent standard Gumbels gives the
standard product Gumbel law of the selected dimension](goal). -/
-- @node: gumbelInputs_map_injection
lemma gumbelInputs_map_injection {I : Type*} [Fintype I] {k : ℕ}
    (f : Fin k → I) (hf : Function.Injective f) :
    (Measure.pi (fun _ : I => gumbelLaw)).map (fun G j => G (f j)) = gumbelInputs k := by
  let := gumbelLaw_probability
  have hind : iIndepFun (fun i : I => fun G : I → ℝ => G i)
      (Measure.pi (fun _ : I => gumbelLaw)) :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have h := (iIndepFun_iff_map_fun_eq_pi_map
    (fun j : Fin k => (measurable_pi_apply (f j)).aemeasurable)).mp (hind.precomp hf)
  simpa only [gumbelInputs, (measurePreserving_eval (fun _ : I => gumbelLaw) _).map_eq] using h

variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
    {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
    {C : Fin b → Set (Fin n)}

/-- For [a canonical causal model](hyp:M) and [a node](hyp:i), [the joint law
of all non-Gumbel latent blocks and that node's intrinsic Gumbels is the
product of the prescribed block laws and the standard product Gumbel law](goal). -/
-- @node: canonical_blocks_node_gumbels_joint_law
lemma canonical_blocks_node_gumbels_joint_law
    (M : CanonicalSCM kind dims dag G C) (i : Fin n) :
    M.latentLaw.map (fun u => (fun j => blockProjection j u,
      fun l => (categoricalNoise i u).ofLp l)) =
      (Measure.pi (fun j => (M.blockLaw j : Measure (L1Vec (dims j))))).prod
        (gumbelInputs (noiseDim (kind i))) := by
  let := gumbelLaw_probability
  let B := Measure.pi (fun j => (M.blockLaw j : Measure (L1Vec (dims j))))
  let N := Measure.pi (fun _ : Σ j, Fin (noiseDim (kind j)) => gumbelLaw)
  let pack : (∀ j, L1Vec (dims j)) × ((Σ j, Fin (noiseDim (kind j))) → ℝ) →
      Exogenous kind dims := fun z => WithLp.toLp 1 (fun c => match c with
        | .inl ⟨j,k⟩ => (z.1 j).ofLp k
        | .inr k => z.2 k)
  have hpack : Measurable pack := by
    apply scm_toLp_measurable.comp
    apply measurable_pi_lambda
    rintro (⟨j,k⟩ | k) <;> dsimp [pack] <;> fun_prop
  have hread : Measurable (fun u : Exogenous kind dims =>
      (fun j => blockProjection j u, fun l => (categoricalNoise i u).ofLp l)) := by
    first | fun_prop | fun_prop [blockProjection, categoricalNoise]
  change ((B.prod N).map pack).map _ = _
  rw [Measure.map_map hread hpack]
  have he : (fun u : Exogenous kind dims =>
      (fun j => blockProjection j u, fun l => (categoricalNoise i u).ofLp l)) ∘ pack =
      Prod.map id (fun z l => z ⟨i,l⟩) := by
    funext z
    apply Prod.ext
    · funext j
      apply WithLp.ofLp_injective
      rfl
    · rfl
  rw [he, ← Measure.map_prod_map B N measurable_id (by fun_prop), Measure.map_id]
  congr 1
  exact gumbelInputs_map_injection (fun l => (⟨i,l⟩ : Σ j, Fin (noiseDim (kind j))))
    (by intro a b h; simpa using h)

/-- The [exogenous vector reconstructed from latent blocks](goal) takes
[an array of non-Gumbel block values](hyp:z), [copies each block coordinate](step:1),
and [sets every intrinsic-noise coordinate to zero](step:2). -/
-- @node: blocksExogenous
def blocksExogenous (z : ∀ j, L1Vec (dims j)) : Exogenous kind dims :=
  WithLp.toLp 1 (fun c => match c with
    | .inl ⟨j,k⟩ => (z j).ofLp k
    | .inr _ => 0)

-- @node: blocksExogenous_measurable
/-- [Reconstructing an exogenous vector from non-Gumbel blocks with zero
intrinsic noise is a measurable operation](goal). -/
@[fun_prop] lemma blocksExogenous_measurable :
    Measurable (blocksExogenous (kind := kind) (dims := dims)) := by
  apply scm_toLp_measurable.comp
  apply measurable_pi_lambda
  rintro (⟨j,k⟩ | k) <;> dsimp [blocksExogenous] <;> fun_prop

/-- For [a Euclidean causal model](hyp:M), [a node](hyp:i), [an observed
history](hyp:v), and [an exogenous vector](hyp:u), [reconstructing the exogenous
vector from its non-Gumbel blocks and setting intrinsic noise to zero leaves
the node's structural input unchanged](goal). -/
-- @node: structuralInput_blocksExogenous
lemma structuralInput_blocksExogenous (M : EuclideanSCM kind dims)
    (i : Fin n) (v : Joint kind) (u : Exogenous kind dims) :
    structuralInput M i v (blocksExogenous (fun j => blockProjection j u)) =
      structuralInput M i v u := by
  apply WithLp.ofLp_injective
  funext c
  rcases c with ⟨p,k⟩ | ⟨j,k⟩ <;> rfl

/-- For [a canonical causal model](hyp:M) and [a node](hyp:i) with
[a specified number of categories](hyp:k), if [the node has that categorical
type](hyp:hi), then [all non-Gumbel blocks and the node's reindexed intrinsic
noise have the product of the prescribed block laws and that many independent
standard Gumbel laws](goal). -/
-- @node: canonical_blocks_categorical_gumbels_joint_law
lemma canonical_blocks_categorical_gumbels_joint_law
    (M : CanonicalSCM kind dims dag G C) (i : Fin n) (k : ℕ)
    (hi : kind i = Sum.inr k) :
    M.latentLaw.map (fun u => (fun j => blockProjection j u,
      fun l : Fin k => (categoricalNoise i u).ofLp
        (Fin.cast (congrArg noiseDim hi).symm l))) =
      (Measure.pi (fun j => (M.blockLaw j : Measure (L1Vec (dims j))))).prod
        (gumbelInputs k) := by
  let := gumbelInputs_probability (noiseDim (kind i))
  let R : (∀ j, L1Vec (dims j)) × (Fin (noiseDim (kind i)) → ℝ) →
      (∀ j, L1Vec (dims j)) × (Fin k → ℝ) :=
    Prod.map id (fun g l => g (Fin.cast (congrArg noiseDim hi).symm l))
  have hR : Measurable R := by fun_prop
  have hread : Measurable (fun u : Exogenous kind dims =>
      (fun j => blockProjection j u, fun l => (categoricalNoise i u).ofLp l)) := by
    first | fun_prop | fun_prop [blockProjection, categoricalNoise]
  have h := congrArg (fun mu => mu.map R) (canonical_blocks_node_gumbels_joint_law M i)
  rw [Measure.map_map hR hread] at h
  have hnoise : (gumbelInputs (noiseDim (kind i))).map
      (fun g l => g (Fin.cast (congrArg noiseDim hi).symm l)) = gumbelInputs k :=
    gumbelInputs_map_injection _ (Fin.cast_injective _)
  have hprod := Measure.map_prod_map
    (Measure.pi (fun j => (M.blockLaw j : Measure (L1Vec (dims j)))))
    (gumbelInputs (noiseDim (kind i))) measurable_id
    (show Measurable (fun g l => g (Fin.cast (congrArg noiseDim hi).symm l)) by fun_prop)
  rw [Measure.map_id, hnoise] at hprod
  exact h.trans hprod.symm

/-- For [a canonical causal model](hyp:M), [a node](hyp:i), and
[a category count](hyp:k) such that [the node is categorical with that count](hyp:hi),
at [a structural input](hyp:x) and [a Gumbel vector](hyp:g), [the categorical
label equals the canonical extended-log selector applied to the reindexed
structural weights and the same Gumbel vector](goal). -/
-- @node: canonicalMechanism_categoricalLabel_eq
lemma canonicalMechanism_categoricalLabel_eq
    (M : CanonicalSCM kind dims dag G C) (i : Fin n) (k : ℕ)
    (hi : kind i = Sum.inr k)
    (x : StructuralInput kind dims dag (canonicalIncidence C) i) (g : L1Vec k) :
    M.toEuclideanSCM.categoricalLabel i k hi x g =
      canonicalSelector (.inr k) (fun m hm => M.positive_categories i m (hi.trans hm))
        (WithLp.toLp 1 (fun j => (M.f i x).ofLp
          (Fin.cast (congrArg outputDim hi).symm j))) g := by
  change cast (congrArg ObservedValue hi)
    (canonicalMechanism M i x _) = _
  have he (g' : L1Vec (noiseDim (kind i))) : canonicalMechanism M i x g' =
      canonicalSelector (kind i) (M.positive_categories i) (M.f i x) g' :=
    (canonicalSelector_eq (kind i) (M.positive_categories i) (M.f i x) g').symm
  exact (congrArg (cast (congrArg ObservedValue hi)) (he _)).trans
    (canonicalSelector_categoricalLabel (kind i) (M.positive_categories i) k hi (M.f i x) g)

/-- The [categorical propensity vector](goal) for [a canonical causal model](hyp:M),
[a node](hyp:i), and [a category count](hyp:k), with [the node identified as
categorical with that count](hyp:hi), evaluates the structural weights at
[a fixed observed history](hyp:v) and [an array of non-Gumbel block values](hyp:z),
then reindexes the weights by category. -/
-- @node: canonicalCategoricalPropensity
def canonicalCategoricalPropensity
    (M : CanonicalSCM kind dims dag G C) (i : Fin n) (k : ℕ)
    (hi : kind i = Sum.inr k) (v : Joint kind) (z : ∀ j, L1Vec (dims j)) : L1Vec k :=
  WithLp.toLp 1 (fun j =>
    (M.f i (structuralInput M.toEuclideanSCM i v (blocksExogenous z))).ofLp
      (Fin.cast (congrArg outputDim hi).symm j))

-- @node: canonicalCategoricalPropensity_measurable
/-- For [a canonical causal model](hyp:M), [a node](hyp:i), and
[a category count](hyp:k) with [the node categorical of that size](hyp:hi),
at [a fixed observed history](hyp:v), [the categorical propensity is measurable
as a function of the non-Gumbel blocks](goal). -/
@[fun_prop] lemma canonicalCategoricalPropensity_measurable
    (M : CanonicalSCM kind dims dag G C) (i : Fin n) (k : ℕ)
    (hi : kind i = Sum.inr k) (v : Joint kind) :
    Measurable (canonicalCategoricalPropensity M i k hi v) := by
  first | fun_prop | skip
  unfold canonicalCategoricalPropensity
  have hinput : Measurable (fun z : ∀ j, L1Vec (dims j) =>
      structuralInput M.toEuclideanSCM i v (blocksExogenous z)) :=
    (structuralInput_measurable M.toEuclideanSCM i).comp
      (measurable_const.prodMk blocksExogenous_measurable)
  have hweights := (M.structuralMeasurable i).comp hinput
  fun_prop

/-- For [a canonical causal model](hyp:M), [a node](hyp:i), and
[a category count](hyp:k) with [the node categorical of that size](hyp:hi),
fix [an observed history](hyp:v) for which [every exogenous realization gives
a structural input in the declared domain](hyp:hinput). Then [the node's
categorical label law is the discrete distribution whose category masses
are the propensities integrated over the prescribed product law of the
non-Gumbel blocks](goal). -/
-- @node: canonical_categorical_label_law
lemma canonical_categorical_label_law
    (M : CanonicalSCM kind dims dag G C) (i : Fin n) (k : ℕ)
    (hi : kind i = Sum.inr k) (v : Joint kind)
    (hinput : ∀ u, structuralInput M.toEuclideanSCM i v u ∈ M.domain i) :
    M.latentLaw.map (fun u => M.toEuclideanSCM.categoricalLabel i k hi
      (structuralInput M.toEuclideanSCM i v u)
      (WithLp.toLp 1 (fun j => (categoricalNoise i u).ofLp
        (Fin.cast (congrArg noiseDim hi).symm j)))) =
      ∑ j, ENNReal.ofReal (∫ z,
        (canonicalCategoricalPropensity M i k hi v z).ofLp j
          ∂(Measure.pi (fun a => (M.blockLaw a : Measure (L1Vec (dims a)))))) •
            Measure.dirac j := by
  let B := Measure.pi (fun a => (M.blockLaw a : Measure (L1Vec (dims a))))
  let p := canonicalCategoricalPropensity M i k hi v
  let hk := fun m hm => M.positive_categories i m (hi.trans hm)
  let F : (∀ j, L1Vec (dims j)) × (Fin k → ℝ) → Fin k :=
    fun z => canonicalSelector (.inr k) hk (p z.1) (WithLp.toLp 1 z.2)
  have hF : Measurable F := by
    apply firstArgmax_getD_measurable
    intro j
    fun_prop
  have hread : Measurable (fun u : Exogenous kind dims =>
      (fun j => blockProjection j u, fun l : Fin k =>
        (categoricalNoise i u).ofLp (Fin.cast (congrArg noiseDim hi).symm l))) := by
    first | fun_prop | fun_prop [blockProjection, categoricalNoise]
  have he (u : Exogenous kind dims) :
      M.toEuclideanSCM.categoricalLabel i k hi (structuralInput M.toEuclideanSCM i v u)
        (WithLp.toLp 1 (fun j => (categoricalNoise i u).ofLp
          (Fin.cast (congrArg noiseDim hi).symm j))) =
        F (fun j => blockProjection j u, fun l =>
          (categoricalNoise i u).ofLp (Fin.cast (congrArg noiseDim hi).symm l)) := by
    apply (canonicalMechanism_categoricalLabel_eq M i k hi _ _).trans
    dsimp [F, p, canonicalCategoricalPropensity]
    congr 2
  have hps : ∀ᵐ z ∂B, (p z).ofLp ∈ probabilitySimplex k := by
    apply Filter.Eventually.of_forall
    intro z
    exact M.simplex i k hi _ (hinput (blocksExogenous z)).1
  calc
    _ = (M.latentLaw.map (fun u => (fun j => blockProjection j u,
        fun l : Fin k => (categoricalNoise i u).ofLp
          (Fin.cast (congrArg noiseDim hi).symm l)))).map F := by
      rw [Measure.map_map hF hread]
      congr 1
      funext u
      exact he u
    _ = (B.prod (gumbelInputs k)).map F := by
      rw [canonical_blocks_categorical_gumbels_joint_law M i k hi]
    _ = _ := privateBlock_canonicalSelector_mixture B hk p
      (canonicalCategoricalPropensity_measurable M i k hi v) hps id

end
end Papers.TbsNeuralCausalPi

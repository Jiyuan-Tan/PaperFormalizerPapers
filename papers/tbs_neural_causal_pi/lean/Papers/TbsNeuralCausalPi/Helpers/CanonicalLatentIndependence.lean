module
public import Papers.TbsNeuralCausalPi.Helpers.CanonicalCategoricalTransition
public import Mathlib.Probability.Independence.InfinitePi
/-! # Independence supplied by the canonical latent construction

Grouping intrinsic Gumbels by node identifies the prescribed latent law with
an independent product of the named blocks. This derives fresh-noise properties
for comparison models directly from their canonical construction.
-/
@[expose] public section
open MeasureTheory ProbabilityTheory
namespace Papers.TbsNeuralCausalPi
set_option linter.style.longLine false
noncomputable section
variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
 {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)} {C : Fin b → Set (Fin n)}
-- @node: canonical_gumbel_family_law
/-- [Grouping independent scalar Gumbel draws by node gives the product of the nodewise Gumbel-vector laws](goal). -/
lemma canonical_gumbel_family_law :
    (Measure.pi (fun _ : Σ i, Fin (noiseDim (kind i)) => gumbelLaw)).map
      (fun g i => WithLp.toLp 1 (fun l => g ⟨i,l⟩)) =
    Measure.pi (fun i : Fin n => (gumbelInputs (noiseDim (kind i))).map (WithLp.toLp 1)) := by
  let := gumbelLaw_probability
  let : ∀ i : Fin n, IsProbabilityMeasure (gumbelInputs (noiseDim (kind i))) :=
    fun i => gumbelInputs_probability _
  let : ∀ i : Fin n, IsProbabilityMeasure ((gumbelInputs (noiseDim (kind i))).map (WithLp.toLp 1)) :=
    fun i => Measure.isProbabilityMeasure_map scm_toLp_measurable.aemeasurable
  have hc := Measure.infinitePi_map_piCurry (fun (i : Fin n) (_ : Fin (noiseDim (kind i))) => gumbelLaw)
  simp only [Measure.infinitePi_eq_pi] at hc
  have hm : Measurable (fun g : ∀ i : Fin n, Fin (noiseDim (kind i)) → ℝ =>
      fun i => WithLp.toLp 1 (g i)) := by fun_prop
  simp only [gumbelInputs] at *
  rw [← Measure.pi_map_pi (fun i => (scm_toLp_measurable (I := Fin (noiseDim (kind i)))).aemeasurable),
    ← hc, Measure.map_map hm (MeasurableEquiv.piCurry (fun i (_ : Fin (noiseDim (kind i))) => ℝ)).measurable]
  rfl

-- @node: canonicalNamedLatentLaw
/-- For [a canonical structural causal model](hyp:M) with [a given number of nodes](hyp:n), [a given number of non-Gumbel blocks](hyp:b), [node types](hyp:kind), [block dimensions](hyp:dims), [a directed causal graph](hyp:dag), [a bidirected graph](hyp:G), and [component memberships](hyp:C), the [named latent marginal law](goal) at [a block or node index](hyp:j) is [the prescribed block law for a non-Gumbel block](step:1), or [the standard Gumbel-vector law for a node's intrinsic noise](step:2). -/
def canonicalNamedLatentLaw (M : CanonicalSCM kind dims dag G C)
    (j : Fin b ⊕ Fin n) : Measure (L1Vec (fullLatentDim kind dims j)) :=
  match j with
  | .inl j => (M.blockLaw j : Measure (L1Vec (dims j)))
  | .inr i => (gumbelInputs (noiseDim (kind i))).map (WithLp.toLp 1)

-- @node: canonicalNamedLatentLaw_probability
/-- [Every named latent marginal of a canonical structural causal model is a probability measure](goal). -/
lemma canonicalNamedLatentLaw_probability (M : CanonicalSCM kind dims dag G C)
    (j : Fin b ⊕ Fin n) : IsProbabilityMeasure (canonicalNamedLatentLaw M j) := by
  cases j with
  | inl j => exact (M.blockLaw j).prop
  | inr i =>
    change IsProbabilityMeasure ((gumbelInputs (noiseDim (kind i))).map (WithLp.toLp 1))
    let := gumbelInputs_probability (noiseDim (kind i))
    exact Measure.isProbabilityMeasure_map scm_toLp_measurable.aemeasurable

-- @node: restoreNamedLatents
/-- For [a given number of nodes](hyp:n), [a given number of blocks](hyp:b), [node types](hyp:kind), and [block dimensions](hyp:dims), [restoring the exogenous vector](goal) from [a family of named latent vectors](hyp:z) places [each non-Gumbel block coordinate in its original position](step:1) and [each intrinsic node-noise coordinate in its original position](step:2). -/
def restoreNamedLatents
    (z : ∀ j, L1Vec (fullLatentDim kind dims j)) : Exogenous kind dims :=
  WithLp.toLp 1 (fun c => match c with
    | .inl ⟨j,l⟩ => (z (.inl j)).ofLp l
    | .inr ⟨i,l⟩ => (z (.inr i)).ofLp l)

-- @node: restoreNamedLatents_measurable
/-- [Reassembling named latent vectors into the full exogenous vector is measurable](goal). -/
@[fun_prop] lemma restoreNamedLatents_measurable :
    Measurable (restoreNamedLatents (kind := kind) (dims := dims)) := by
  first | fun_prop | skip
  apply scm_toLp_measurable.comp
  apply measurable_pi_lambda
  rintro (⟨j,l⟩ | ⟨i,l⟩) <;> fun_prop [restoreNamedLatents]

-- @node: canonical_latentLaw_eq_named_product
/-- [The latent law of a canonical structural causal model equals the product of its named latent marginals followed by reassembly into the full exogenous vector](goal). -/
lemma canonical_latentLaw_eq_named_product (M : CanonicalSCM kind dims dag G C) :
    M.latentLaw = (Measure.pi (canonicalNamedLatentLaw M)).map restoreNamedLatents := by
  let := gumbelLaw_probability
  let : ∀ j, IsProbabilityMeasure (canonicalNamedLatentLaw M j) :=
    canonicalNamedLatentLaw_probability M
  let B := Measure.pi (fun j => (M.blockLaw j : Measure (L1Vec (dims j))))
  let N := Measure.pi (fun _ : Σ i, Fin (noiseDim (kind i)) => gumbelLaw)
  let group := fun g : (Σ i, Fin (noiseDim (kind i))) → ℝ =>
    fun i => WithLp.toLp 1 (fun l => g ⟨i,l⟩)
  have hg : Measurable group := by fun_prop
  let split := MeasurableEquiv.sumPiEquivProdPi
    (fun j => L1Vec (fullLatentDim kind dims j))
  have hs := (measurePreserving_sumPiEquivProdPi (canonicalNamedLatentLaw M)).map_eq
  have hprod : (B.prod N).map (Prod.map id group) =
      (Measure.pi (canonicalNamedLatentLaw M)).map split := by
    rw [← Measure.map_prod_map B N measurable_id hg, Measure.map_id,
      canonical_gumbel_family_law]
    exact hs.symm
  have hr : Measurable (restoreNamedLatents (kind := kind) (dims := dims) ∘ split.symm) :=
    restoreNamedLatents_measurable.comp split.symm.measurable
  have heq : (restoreNamedLatents (kind := kind) (dims := dims) ∘ split.symm) ∘
      Prod.map id group = (fun z => WithLp.toLp 1 (fun c => match c with
        | .inl ⟨j,l⟩ => (z.1 j).ofLp l
        | .inr c => z.2 c)) := by
    funext z
    apply WithLp.ofLp_injective
    funext c
    cases c <;> rfl
  calc
    M.latentLaw = ((B.prod N).map (Prod.map id group)).map
        (restoreNamedLatents ∘ split.symm) := by
      change (B.prod N).map _ = _
      erw [Measure.map_map hr (measurable_id.prodMap hg), heq]
      rfl
    _ = ((Measure.pi (canonicalNamedLatentLaw M)).map split).map
        (restoreNamedLatents ∘ split.symm) :=
      congrArg (fun mu => mu.map (restoreNamedLatents ∘ split.symm)) hprod
    _ = _ := by
      rw [Measure.map_map hr split.measurable]
      congr 1

-- @node: canonical_latent_blocks_independent
/-- [All named latent blocks of a canonical structural causal model, including intrinsic node noises, are jointly independent](goal). -/
lemma canonical_latent_blocks_independent (M : CanonicalSCM kind dims dag G C) :
    LatentBlocksIndependent M.toEuclideanSCM := by
  let : ∀ j, IsProbabilityMeasure (canonicalNamedLatentLaw M j) :=
    canonicalNamedLatentLaw_probability M
  let read := fun u j => namedLatent M.toEuclideanSCM j u
  have hm (j) : Measurable (namedLatent M.toEuclideanSCM j) := by
    first | fun_prop | cases j <;> fun_prop [namedLatent, blockProjection, categoricalNoise]
  have he : read ∘ restoreNamedLatents = id := by
    funext z j
    cases j <;> rfl
  have hjoint : M.latentLaw.map read = Measure.pi (canonicalNamedLatentLaw M) := by
    rw [canonical_latentLaw_eq_named_product, Measure.map_map
      (measurable_pi_lambda _ hm) restoreNamedLatents_measurable, he, Measure.map_id]
  let := M.latentLaw_probability
  change iIndepFun (namedLatent M.toEuclideanSCM) M.latentLaw
  apply (iIndepFun_iff_map_fun_eq_pi_map (fun j => (hm j).aemeasurable)).2
  change M.latentLaw.map read = _
  rw [hjoint]
  congr 1
  funext j
  have h := congrArg (fun mu => mu.map (fun z => z j)) hjoint
  rw [Measure.map_map (measurable_pi_apply j) (measurable_pi_lambda _ hm),
    (measurePreserving_eval (canonicalNamedLatentLaw M) j).map_eq] at h
  exact h.symm
/-- If [a node is categorical with k alternatives](hyp:hi), then [its intrinsic noise coordinates under the canonical latent law have the law of k independent standard Gumbel draws](goal). -/
-- @node: canonical_categorical_noise_law
lemma canonical_categorical_noise_law (M : CanonicalSCM kind dims dag G C)
    (i : Fin n) (k : ℕ) (hi : kind i = .inr k) :
    M.latentLaw.map (fun u (l : Fin k) => (categoricalNoise i u).ofLp
      (Fin.cast (congrArg noiseDim hi).symm l)) = gumbelInputs k := by
  let := gumbelInputs_probability k
  have h := congrArg (fun mu => mu.map Prod.snd)
    (canonical_blocks_categorical_gumbels_joint_law M i k hi)
  have hr : Measurable (fun u : Exogenous kind dims =>
      (fun j => blockProjection j u, fun l : Fin k =>
        (categoricalNoise i u).ofLp (Fin.cast (congrArg noiseDim hi).symm l))) := by
    first | fun_prop | fun_prop [blockProjection, categoricalNoise]
  rw [Measure.map_map measurable_snd hr, Measure.map_snd_prod,
    measure_univ, one_smul] at h
  exact h

end
end Papers.TbsNeuralCausalPi

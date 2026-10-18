module
public import Papers.TbsNeuralCausalPi.Helpers.CanonicalMechanisms
/-! # Transport of regrouped inputs and categorical mechanisms

The regrouping commutes with structural inputs and preserves intrinsic noise.
At an admissible input the original categorical mechanism and its normalized
canonical replacement agree almost everywhere, including zero simplex weights.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
noncomputable section
set_option linter.style.whitespace false

variable {n b b' : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dims' : Fin b' → ℕ}

/-- If [regrouping preserves every intrinsic categorical noise coordinate](hyp:hg),
then [each node has the same categorical noise before and after regrouping](goal). -/
-- @node: canonical_regrouping_categoricalNoise
lemma canonical_regrouping_categoricalNoise
    (merge : Exogenous kind dims → Exogenous kind dims')
    (hg : ∀ u i k, (merge u).ofLp (.inr ⟨i,k⟩) = u.ofLp (.inr ⟨i,k⟩))
    (i : Fin n) (u : Exogenous kind dims) :
    categoricalNoise i (merge u) = categoricalNoise i u := by
  apply WithLp.ofLp_injective
  funext k
  exact hg u i k

/-- Given [bijections between canonical block coordinates and their grouped original coordinates](hyp:coords),
[an assignment of each node's original latent blocks to canonical blocks available to that node](hyp:locate),
and [a continuous linear projection from each canonical structural input space to the original one](hyp:pi),
suppose [regrouping rearranges the exogenous block coordinates according to
the given coordinate bijections](hyp:hm), [the input projection preserves parent
coordinates](hyp:hp), and [it recovers each original latent coordinate from its
assigned canonical block](hyp:hl). Then [projecting the canonical structural input
formed from the regrouped noise gives the original structural input](goal). -/
-- @node: canonical_regrouping_structuralInput
lemma canonical_regrouping_structuralInput
    (M : EuclideanSCM kind dims) (C : Fin b' → Set (Fin n))
    (groups : Fin b' → Finset (Fin b))
    (coords : ∀ c, Fin (dims' c) ≃ (Σ j : {j // j ∈ groups c}, Fin (dims j)))
    (merge : Exogenous kind dims → Exogenous kind dims')
    (hm : ∀ u c k, (merge u).ofLp (.inl ⟨c,k⟩) =
      u.ofLp (.inl ⟨(coords c k).1.val, (coords c k).2⟩))
    (locate : ∀ i (j : {j // j ∈ M.incidence i}),
      {c // c ∈ canonicalIncidence C i ∧ j.val ∈ groups c})
    (pi : ∀ i, StructuralInput kind dims' M.dag (canonicalIncidence C) i →L[ℝ]
      StructuralInput kind dims M.dag M.incidence i)
    (hp : ∀ i x p k, (pi i x).ofLp (.inl ⟨p,k⟩) = x.ofLp (.inl ⟨p,k⟩))
    (hl : ∀ i x j k, (pi i x).ofLp (.inr ⟨j,k⟩) =
      x.ofLp (.inr ⟨⟨(locate i j).val, (locate i j).property.1⟩,
        (coords (locate i j).val).symm ⟨⟨j.val, (locate i j).property.2⟩, k⟩⟩))
    (N : CanonicalSCM kind dims' M.dag (causalGraph M).2 C)
    (i : Fin n) (v : Joint kind) (u : Exogenous kind dims) :
    pi i (structuralInput N.toEuclideanSCM i v (merge u)) =
      structuralInput M i v u := by
  apply WithLp.ofLp_injective
  funext q
  rcases q with ⟨p,k⟩ | ⟨j,k⟩
  · exact hp i _ p k
  · dsimp only [CanonicalSCM.toEuclideanSCM, structuralInput]
    rw [hl]
    change (merge u).ofLp (.inl _) = u.ofLp (.inl ⟨j.val,k⟩)
    rw [hm, Equiv.apply_symm_apply]

/-- At [a node with k categorical labels](hyp:hi), [the canonical model's
categorical label equals the canonical selector applied to its structural weights
and the given noise vector](goal). -/
-- @node: canonical_categoricalLabel_eq_selector
lemma canonical_categoricalLabel_eq_selector
    {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
    {C : Fin b' → Set (Fin n)} (N : CanonicalSCM kind dims' dag G C)
    (i : Fin n) (k : ℕ) (hi : kind i = Sum.inr k)
    (x : StructuralInput kind dims' dag (canonicalIncidence C) i) (g : L1Vec k) :
    N.toEuclideanSCM.categoricalLabel i k hi x g =
      canonicalSelector (.inr k) (fun m hm => N.categoricalPositive i m (hi.trans hm))
        (WithLp.toLp 1 (fun j => (N.f i x).ofLp
          (Fin.cast (congrArg outputDim hi).symm j))) g := by
  have h (κ : NodeKind) (hk : ∀ m, κ = .inr m → 0 < m)
      (w : L1Vec (outputDim κ)) (hκ : κ = .inr k) :
      cast (congrArg ObservedValue hκ)
        (canonicalSelector κ hk w (WithLp.toLp 1 (fun j =>
          g.ofLp (Fin.cast (congrArg noiseDim hκ) j)))) =
      canonicalSelector (.inr k) (fun m hm => hk m (hκ.trans hm))
        (WithLp.toLp 1 (fun j => w.ofLp
          (Fin.cast (congrArg outputDim hκ).symm j))) g := by
    subst κ
    rfl
  unfold EuclideanSCM.categoricalLabel
  change cast (congrArg ObservedValue hi) (canonicalMechanism N i x _) = _
  rw [show canonicalMechanism N i x _ =
    canonicalSelector (kind i) (N.positive_categories i) (N.f i x) _ from
      (canonicalSelector_eq _ _ _ _).symm]
  exact h (kind i) (N.positive_categories i) (N.f i x) hi

/-- If [the original model uses Gumbel argmax with the given weights](hyp:hcat),
[the node has k categorical labels](hyp:hi), [the original input is admissible](hyp:hx),
and [the canonical weights at the comparison input are the normalized original
weights](hyp:hf), then [the original and canonical labels agree almost surely
when driven by the same independent standard Gumbel noises](goal). -/
-- @node: canonical_regrouped_categoricalLabel_ae
lemma canonical_regrouped_categoricalLabel_ae
    (M : EuclideanSCM kind dims) (p : MechanismWeights M)
    (hcat : CategoricalGumbelArgmax M p) (C : Fin b' → Set (Fin n))
    (N : CanonicalSCM kind dims' M.dag (causalGraph M).2 C)
    (i : Fin n) (k : ℕ) (hi : kind i = Sum.inr k)
    (x : StructuralInput kind dims M.dag M.incidence i) (hx : x ∈ M.domain i)
    (y : StructuralInput kind dims' M.dag (canonicalIncidence C) i)
    (hf : N.f i y = WithLp.toLp 1 (fun j =>
      (p i x).ofLp j / ∑ l, (p i x).ofLp l)) :
    (fun g : Fin k → ℝ => M.categoricalLabel i k hi x (WithLp.toLp 1 g)) =ᵐ[gumbelInputs k]
      (fun g => N.toEuclideanSCM.categoricalLabel i k hi y (WithLp.toLp 1 g)) := by
  filter_upwards [categoricalLabel_ae_normalized_selector M p hcat i k hi x hx] with g hg
  rw [hg, canonical_categoricalLabel_eq_selector, hf]
  rfl

/-- Suppose [the original mechanism is Gumbel argmax](hyp:hcat), [the node has k
categorical labels](hyp:hi), [the original input depends measurably on the retained
index](hyp:hx), [the canonical input does too](hyp:hy), [the original input is
admissible almost surely under the index law](hyp:hd), and [the canonical weights
are almost surely the normalized original weights](hyp:hf). Then [the joint laws
of the retained index and output label coincide for the original and canonical
models under independent Gumbel noise](goal).

Retaining the index gives the joint law needed for history transport. -/
-- @node: canonical_regrouped_categoricalLabel_joint_law
lemma canonical_regrouped_categoricalLabel_joint_law
    {Z : Type*} [MeasurableSpace Z] (rho : Measure Z)
    (M : EuclideanSCM kind dims) (p : MechanismWeights M)
    (hcat : CategoricalGumbelArgmax M p) (C : Fin b' → Set (Fin n))
    (N : CanonicalSCM kind dims' M.dag (causalGraph M).2 C)
    (i : Fin n) (k : ℕ) (hi : kind i = Sum.inr k)
    (x : Z → StructuralInput kind dims M.dag M.incidence i) (hx : Measurable x)
    (y : Z → StructuralInput kind dims' M.dag (canonicalIncidence C) i)
    (hy : Measurable y) (hd : ∀ᵐ z ∂rho, x z ∈ M.domain i)
    (hf : ∀ᵐ z ∂rho, N.f i (y z) = WithLp.toLp 1 (fun j =>
      (p i (x z)).ofLp j / ∑ l, (p i (x z)).ofLp l)) :
    (rho.prod (gumbelInputs k)).map (fun z =>
      (z.1, M.categoricalLabel i k hi (x z.1) (WithLp.toLp 1 z.2))) =
    (rho.prod (gumbelInputs k)).map (fun z =>
      (z.1, N.toEuclideanSCM.categoricalLabel i k hi (y z.1) (WithLp.toLp 1 z.2))) := by
  have hF : Measurable (fun z : Z × (Fin k → ℝ) =>
      M.categoricalLabel i k hi (x z.1) (WithLp.toLp 1 z.2)) := by fun_prop
  have hG : Measurable (fun z : Z × (Fin k → ℝ) =>
      N.toEuclideanSCM.categoricalLabel i k hi (y z.1) (WithLp.toLp 1 z.2)) := by
    exact (categoricalLabel_joint_measurable N.toEuclideanSCM i k hi).comp
      ((hy.comp measurable_fst).prodMk (scm_toLp_measurable.comp measurable_snd))
  let := gumbelInputs_probability k
  have he : (fun z : Z × (Fin k → ℝ) =>
      M.categoricalLabel i k hi (x z.1) (WithLp.toLp 1 z.2)) =ᵐ[rho.prod (gumbelInputs k)]
      (fun z => N.toEuclideanSCM.categoricalLabel i k hi (y z.1) (WithLp.toLp 1 z.2)) := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hF hG)).2
    filter_upwards [hd, hf] with z hz hzf
    exact canonical_regrouped_categoricalLabel_ae M p hcat C N i k hi (x z) hz (y z) hzf
  apply Measure.map_congr
  filter_upwards [he] with z hz
  exact congrArg (fun label : Fin k => (z.1, label)) hz

end
end Papers.TbsNeuralCausalPi

module
public import Papers.TbsNeuralCausalPi.Helpers.ApproximationSelectorStep
/-! # Transport with approximation error on the true carrying set

The restricted candidate is Lipschitz on all admissible histories. Its local
approximation error is needed only on the bounded histories of the true law.
The comparison law may visit other admissible categorical prefixes.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
open scoped NNReal ENNReal
noncomputable section

/-- If [S is contained in T](hyp:hST), [the true law is concentrated on S](hyp:hmu),
[the comparison law is concentrated on T](hyp:hnu), and [f is measurable](hyp:hf)
and [g is measurable](hyp:hg), then, for [a nonnegative constant A](hyp:A) such that
[g is A-Lipschitz on T](hyp:hLip) and [an extended nonnegative error E](hyp:E) such that
[f and g differ by at most E on S](hyp:herror), [the Wasserstein distance between
their output laws is at most A times the input Wasserstein distance plus E](goal). -/
-- @node: approximation_wasserstein_map_perturbation_left_le
lemma approximation_wasserstein_map_perturbation_left_le
    {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (S T : Set X) (hST : S ⊆ T)
    (hmu : ∀ᵐ x ∂mu, x ∈ S) (hnu : ∀ᵐ x ∂nu, x ∈ T)
    (f g : X → Y) (hf : Measurable f) (hg : Measurable g)
    (A : ℝ≥0) (hLip : LipschitzOnWith A g T) (E : ℝ≥0∞)
    (herror : ∀ x ∈ S, edist (f x) (g x) ≤ E) :
    wasserstein1 (mu.map f) (nu.map g) ≤ (A : ℝ≥0∞) * wasserstein1 mu nu + E := by
  apply approximation_wasserstein_map_cross_bound mu nu S T hmu hnu f g hf hg A E
  intro x hx y hy
  calc
    edist (f x) (g y) ≤ edist (f x) (g x) + edist (g x) (g y) := edist_triangle _ _ _
    _ ≤ E + (A : ℝ≥0∞) * edist x y := add_le_add (herror x hx) (hLip (hST hx) hy)
    _ = _ := add_comm _ _

/-- Suppose [S is contained in T](hyp:hST), [the true history law is concentrated on S](hyp:hmu),
[the comparison history law is concentrated on T](hyp:hnu), [f is measurable](hyp:hf),
and [g is measurable](hyp:hg). For [a nonnegative constant L](hyp:L), if
[g is L-Lipschitz on T](hyp:hLip), [appending the d-dimensional outputs gives
Wasserstein distance at most 1 + L times the history distance plus d times the
uniform coordinate error between f and g on S](goal). -/
-- @node: approximation_continuous_history_step_left
lemma approximation_continuous_history_step_left
    {h d : ℕ} (mu nu : Measure (L1Vec h))
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (S T : Set (L1Vec h)) (hST : S ⊆ T)
    (hmu : ∀ᵐ x ∂mu, x ∈ S) (hnu : ∀ᵐ x ∂nu, x ∈ T)
    (f g : L1Vec h → L1Vec d) (hf : Measurable f) (hg : Measurable g)
    (L : ℝ≥0) (hLip : LipschitzOnWith L g T) :
    wasserstein1
      (mu.map (fun x => WithLp.toLp 1 (Sum.elim x.ofLp (f x).ofLp)))
      (nu.map (fun x => WithLp.toLp 1 (Sum.elim x.ofLp (g x).ofLp))) ≤
      ((1 + L : ℝ≥0) : ℝ≥0∞) * wasserstein1 mu nu +
        (d : ℝ≥0∞) * supDistOn S f g := by
  let F : L1Vec h → WithLp 1 ((Fin h ⊕ Fin d) → ℝ) :=
    fun x => WithLp.toLp 1 (Sum.elim x.ofLp (f x).ofLp)
  let G : L1Vec h → WithLp 1 ((Fin h ⊕ Fin d) → ℝ) :=
    fun x => WithLp.toLp 1 (Sum.elim x.ofLp (g x).ofLp)
  have hF : Measurable F := by
    apply (PiLp.continuous_toLp 1 _).measurable.comp
    apply measurable_pi_lambda
    intro i
    cases i <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> fun_prop
  have hG : Measurable G := by
    apply (PiLp.continuous_toLp 1 _).measurable.comp
    apply measurable_pi_lambda
    intro i
    cases i <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> fun_prop
  have hGLip : LipschitzOnWith (1 + L) G T := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hdist : dist (G x) (G y) = dist x y + dist (g x) (g y) := by
      simp only [G, PiLp.dist_eq_of_L1, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
    rw [hdist]
    calc
      dist x y + dist (g x) (g y) ≤ dist x y + (L : ℝ) * dist x y :=
        add_le_add le_rfl (hLip.dist_le_mul x hx y hy)
      _ = _ := by simp only [NNReal.coe_add, NNReal.coe_one]; ring
  apply approximation_wasserstein_map_perturbation_left_le mu nu S T hST hmu hnu F G hF hG
    (1 + L) hGLip ((d : ℝ≥0∞) * supDistOn S f g)
  intro x hx
  have heq : edist (F x) (G x) = edist (f x) (g x) := by
    simp [F, G, PiLp.edist_eq_of_L1, Fintype.sum_sum_type]
  rw [heq]
  exact approximation_edist_le_dim_supDistOn S f g hx

/-- Suppose [S is contained in T](hyp:hST), [the true law is concentrated on S](hyp:hmu),
[the comparison law is concentrated on T](hyp:hnu), [p is measurable](hyp:hp),
[q is measurable](hyp:hq), [p always gives probability vectors](hyp:hps), [q always gives
probability vectors](hyp:hqs), and [each category's encoding is measurable in the history](hyp:hv).
For [nonnegative constants L and D](hyp:L,D), if [q is L-Lipschitz on T](hyp:hLip)
and [encoding two histories costs at most their distance, plus D when their categories differ](hyp:hcost),
[the encoded output Wasserstein distance is at most 1 + DL/2 times the input
distance plus kD/2 times the uniform propensity error on S](goal). -/
-- @node: categorical_encoded_history_step_left
lemma categorical_encoded_history_step_left
    {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    {k : ℕ} (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (S T : Set X) (hST : S ⊆ T)
    (hmu : ∀ᵐ x ∂mu, x ∈ S) (hnu : ∀ᵐ x ∂nu, x ∈ T)
    (p q : X → L1Vec k) (hp : Measurable p) (hq : Measurable q)
    (hps : ∀ x, (p x).ofLp ∈ probabilitySimplex k)
    (hqs : ∀ x, (q x).ofLp ∈ probabilitySimplex k)
    (v : X → Fin k → Y) (hv : ∀ i, Measurable (fun x => v x i))
    (L D : ℝ≥0) (hLip : LipschitzOnWith L q T)
    (hcost : ∀ x ∈ S, ∀ y ∈ T, ∀ i j,
      dist (v x i) (v y j) ≤ dist x y + if i = j then 0 else (D : ℝ)) :
    wasserstein1
      (mu.bind (categoricalEncodedKernel (fun x => (p x).ofLp) (by fun_prop) v hv))
      (nu.bind (categoricalEncodedKernel (fun x => (q x).ofLp) (by fun_prop) v hv)) ≤
      ((1 + D * L / 2 : ℝ≥0) : ℝ≥0∞) * wasserstein1 mu nu +
        ((k * D / 2 : ℝ≥0) : ℝ≥0∞) * supDistOn S p q := by
  let pm := fun i => (show Measurable (fun x => (p x).ofLp i) by fun_prop)
  let qm := fun i => (show Measurable (fun x => (q x).ofLp i) by fun_prop)
  apply approximation_wasserstein_bind_cross_bound_on mu nu S T hmu hnu
    _ _ (categoricalEncodedCouplingKernel _ _ pm qm v v hv hv)
    (categoricalEncodedCouplingKernel_coupling _ _ pm qm v v hv hv hps hqs)
  intro z hx hy
  let e : ℝ := ‖(p z.1 - q z.1).ofLp‖
  have he : 0 ≤ e := norm_nonneg _
  have hsup : ENNReal.ofReal e ≤ supDistOn S p q :=
    le_iSup_of_le (⟨z.1, hx⟩ : S) le_rfl
  have hlocal : dist (p z.1) (q z.1) ≤ (k : ℝ) * e := by
    rw [PiLp.dist_eq_of_L1]
    calc
      _ ≤ ∑ _i : Fin k, e := by
        apply Finset.sum_le_sum
        intro i _
        exact norm_le_pi_norm ((p z.1 - q z.1).ofLp) i
      _ = _ := by simp
  have hprop : dist (p z.1) (q z.2) ≤ (L : ℝ) * dist z.1 z.2 + k * e := by
    have h := (dist_triangle (p z.1) (q z.1) (q z.2)).trans
      (add_le_add hlocal (hLip.dist_le_mul _ (hST hx) _ hy))
    linarith
  calc
    _ ≤ ENNReal.ofReal (dist z.1 z.2 + (D : ℝ) / 2 *
        ∑ i, |(p z.1).ofLp i - (q z.2).ofLp i|) :=
      categoricalEncodedCouplingKernel_cost_le _ _ pm qm v v hv hv z
        (hps z.1) (hqs z.2) _ _ (hcost _ hx _ hy)
    _ ≤ ENNReal.ofReal ((1 + (D : ℝ) * L / 2) * dist z.1 z.2 +
        (k : ℝ) * D / 2 * e) := by
      apply ENNReal.ofReal_le_ofReal
      have h := mul_le_mul_of_nonneg_left hprop (show 0 ≤ (D : ℝ) / 2 by positivity)
      rw [PiLp.dist_eq_of_L1] at h
      simp only [Real.dist_eq] at h
      nlinarith
    _ = ((1 + D * L / 2 : ℝ≥0) : ℝ≥0∞) * edist z.1 z.2 +
        ((k * D / 2 : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal e := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), edist_dist]
      congr 2
      · simpa only [NNReal.coe_add, NNReal.coe_one, NNReal.coe_mul, NNReal.coe_div,
          NNReal.coe_ofNat] using (@ENNReal.ofReal_coe_nnreal (1 + D * L / 2))
      · simpa only [NNReal.coe_mul, NNReal.coe_div, NNReal.coe_ofNat, NNReal.coe_natCast]
          using (@ENNReal.ofReal_coe_nnreal (k * D / 2))
    _ ≤ _ := by gcongr

/-- Suppose [there is at least one category](hyp:hk), [T is measurable](hyp:hT),
[S is contained in T](hyp:hST), [the true law is concentrated on S](hyp:hmu), and
[the comparison law is concentrated on T](hyp:hnu). If [p is measurable](hyp:hp),
[q is measurable](hyp:hq), [p gives probability vectors on T](hyp:hps),
[q gives probability vectors on T](hyp:hqs),
and [each category's encoding is measurable in the history](hyp:hv), then for
[nonnegative constants L and D](hyp:L,D), assuming [q is L-Lipschitz on T](hyp:hLip)
and [encoding costs at most the history distance plus D for unequal categories](hyp:hcost),
[the output laws formed by extending both propensities outside T have Wasserstein
distance at most 1 + DL/2 times the input distance plus kD/2 times the uniform
propensity error on S](goal). -/
-- @node: categorical_encoded_history_step_left_on
lemma categorical_encoded_history_step_left_on
    {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    {k : ℕ} (hk : 0 < k)
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (S T : Set X) (hT : MeasurableSet T) (hST : S ⊆ T)
    (hmu : ∀ᵐ x ∂mu, x ∈ S) (hnu : ∀ᵐ x ∂nu, x ∈ T)
    (p q : X → L1Vec k) (hp : Measurable p) (hq : Measurable q)
    (hps : ∀ x ∈ T, (p x).ofLp ∈ probabilitySimplex k)
    (hqs : ∀ x ∈ T, (q x).ofLp ∈ probabilitySimplex k)
    (v : X → Fin k → Y) (hv : ∀ i, Measurable (fun x => v x i))
    (L D : ℝ≥0) (hLip : LipschitzOnWith L q T)
    (hcost : ∀ x ∈ S, ∀ y ∈ T, ∀ i j,
      dist (v x i) (v y j) ≤ dist x y + if i = j then 0 else (D : ℝ)) :
    wasserstein1
      (mu.bind (categoricalEncodedKernel
        (fun x => (approximationTotalPropensity T p x).ofLp) (by fun_prop) v hv))
      (nu.bind (categoricalEncodedKernel
        (fun x => (approximationTotalPropensity T q x).ofLp) (by fun_prop) v hv)) ≤
      ((1 + D * L / 2 : ℝ≥0) : ℝ≥0∞) * wasserstein1 mu nu +
        ((k * D / 2 : ℝ≥0) : ℝ≥0∞) * supDistOn S p q := by
  have heq : supDistOn S (approximationTotalPropensity T p)
      (approximationTotalPropensity T q) = supDistOn S p q := by
    unfold supDistOn
    congr 1
    funext x
    rw [approximationTotalPropensity_eq T p (hST x.property),
      approximationTotalPropensity_eq T q (hST x.property)]
  have h := categorical_encoded_history_step_left mu nu S T hST hmu hnu
    (approximationTotalPropensity T p) (approximationTotalPropensity T q)
    (by fun_prop) (by fun_prop)
    (approximationTotalPropensity_simplex hk T p hps)
    (approximationTotalPropensity_simplex hk T q hqs) v hv L D
    (approximationTotalPropensity_lipschitzOn T q L hLip) hcost
  rwa [heq] at h

/-- Suppose [the categorical node has a positive number of categories](hyp:hk),
[T is measurable](hyp:hT), [S is contained in T](hyp:hST), [the true law is
concentrated on S](hyp:hmu), and [the comparison law is concentrated on T](hyp:hnu).
If [p is measurable](hyp:hp), [q is measurable](hyp:hq),
[p gives probability vectors on T](hyp:hps), [q gives probability vectors on T](hyp:hqs),
and [each category's encoding is measurable](hyp:hv),
then for [nonnegative constants L and D](hyp:L,D), assuming [q is L-Lipschitz on T](hyp:hLip)
and [encoding costs at most the history distance plus D for unequal categories](hyp:hcost),
[the Gumbel-selected encoded output laws have Wasserstein distance at most
1 + DL/2 times the input distance plus kD/2 times the uniform propensity error on S](goal). -/
-- @node: approximation_selector_history_step_left
lemma approximation_selector_history_step_left
    {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    {k : ℕ} (hk : ∀ m, Sum.inr k = (Sum.inr m : NodeKind) → 0 < m)
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (S T : Set X) (hT : MeasurableSet T) (hST : S ⊆ T)
    (hmu : ∀ᵐ x ∂mu, x ∈ S) (hnu : ∀ᵐ x ∂nu, x ∈ T)
    (p q : X → L1Vec k) (hp : Measurable p) (hq : Measurable q)
    (hps : ∀ x ∈ T, (p x).ofLp ∈ probabilitySimplex k)
    (hqs : ∀ x ∈ T, (q x).ofLp ∈ probabilitySimplex k)
    (v : X → Fin k → Y) (hv : ∀ i, Measurable (fun x => v x i))
    (L D : ℝ≥0) (hLip : LipschitzOnWith L q T)
    (hcost : ∀ x ∈ S, ∀ y ∈ T, ∀ i j,
      dist (v x i) (v y j) ≤ dist x y + if i = j then 0 else (D : ℝ)) :
    wasserstein1
      ((mu.prod (gumbelInputs k)).map (fun z =>
        v z.1 (canonicalSelector (.inr k) hk (p z.1) (WithLp.toLp 1 z.2))))
      ((nu.prod (gumbelInputs k)).map (fun z =>
        v z.1 (canonicalSelector (.inr k) hk (q z.1) (WithLp.toLp 1 z.2)))) ≤
      ((1 + D * L / 2 : ℝ≥0) : ℝ≥0∞) * wasserstein1 mu nu +
        ((k * D / 2 : ℝ≥0) : ℝ≥0∞) * supDistOn S p q := by
  rw [approximation_selector_map_eq_bind hk mu T hT (hmu.mono fun _ hx => hST hx)
      p hp hps v hv,
    approximation_selector_map_eq_bind hk nu T hT hnu q hq hqs v hv]
  exact categorical_encoded_history_step_left_on (hk k rfl) mu nu S T hT hST hmu hnu
    p q hp hq hps hqs v hv L D hLip hcost

end
end Papers.TbsNeuralCausalPi

module
public import Papers.TbsNeuralCausalPi.Helpers.CategoricalSelectorLaw
/-! # Actual Gumbel transitions in the approximation recurrence

Propensities need only lie in the closed simplex on the histories carrying the
laws. Totalization off that domain supplies Markov transitions, and integrating
the actual selector gives the categorical step with the structural sup error.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

-- @node: approximationTotalPropensity
/-- For [a carrying domain S](hyp:S), [a propensity function p](hyp:p), and
[an input x](hyp:x), the [totalized propensity](goal) equals p at x inside S
and otherwise assigns probability one to the first category and zero to the others. -/
def approximationTotalPropensity {X : Type*} {k : ℕ}
    (S : Set X) (p : X → L1Vec k) (x : X) : L1Vec k :=
  if x ∈ S then p x else WithLp.toLp 1 (fun j => if j.val = 0 then 1 else 0)

-- @node: approximationTotalPropensity_eq
/-- If [x belongs to the carrying domain S](hyp:hx), then [the totalized
propensity at x equals the original propensity at x](goal). -/
lemma approximationTotalPropensity_eq {X : Type*} {k : ℕ}
    (S : Set X) (p : X → L1Vec k) {x : X} (hx : x ∈ S) :
    approximationTotalPropensity S p x = p x := by
  simp only [approximationTotalPropensity, hx, if_true]

-- @node: approximationTotalPropensity_measurable
/-- If [the carrying domain S is measurable](hyp:hS) and [the propensity p is
measurable](hyp:hp), then [the totalized propensity is measurable](goal). -/
@[fun_prop] lemma approximationTotalPropensity_measurable
    {X : Type*} [MeasurableSpace X] {k : ℕ}
    (S : Set X) (hS : MeasurableSet S) (p : X → L1Vec k) (hp : Measurable p) :
    Measurable (approximationTotalPropensity S p) := by
  first | fun_prop | exact hp.ite hS measurable_const

-- @node: approximationTotalPropensity_simplex
/-- If [there is at least one category](hyp:hk) and [p is a probability vector
at every input in S](hyp:hp), then [the totalized propensity is a probability
vector at every input](goal). -/
lemma approximationTotalPropensity_simplex {X : Type*} {k : ℕ} (hk : 0 < k)
    (S : Set X) (p : X → L1Vec k)
    (hp : ∀ x ∈ S, (p x).ofLp ∈ probabilitySimplex k) (x : X) :
    (approximationTotalPropensity S p x).ofLp ∈ probabilitySimplex k := by
  by_cases hx : x ∈ S
  · rw [approximationTotalPropensity_eq S p hx]
    exact hp x hx
  · simp only [approximationTotalPropensity, hx, if_false, WithLp.ofLp_toLp]
    refine ⟨fun j => by dsimp only; split_ifs <;> norm_num, ?_⟩
    have he (j : Fin k) : (j.val = 0) ↔ j = ⟨0,hk⟩ := by
      constructor
      · exact fun h => Fin.ext h
      · intro h; subst j; rfl
    simp_rw [he]
    simp

-- @node: approximationTotalPropensity_lipschitzOn
/-- For [a nonnegative Lipschitz constant L](hyp:L), if [p is L-Lipschitz on S](hyp:hp), then [its totalized propensity is
also L-Lipschitz on S](goal). -/
lemma approximationTotalPropensity_lipschitzOn
    {X : Type*} [PseudoMetricSpace X] {k : ℕ} (S : Set X)
    (p : X → L1Vec k) (L : ℝ≥0) (hp : LipschitzOnWith L p S) :
    LipschitzOnWith L (approximationTotalPropensity S p) S := by
  intro x hx y hy
  simpa only [approximationTotalPropensity_eq S p hx,
    approximationTotalPropensity_eq S p hy] using hp hx hy

-- @node: approximationTotalPropensity_supDistOn
/-- [The supremum distance on S between the totalized propensities of p and q
equals the supremum distance on S between p and q themselves](goal). -/
lemma approximationTotalPropensity_supDistOn {X : Type*} {k : ℕ}
    (S : Set X) (p q : X → L1Vec k) :
    supDistOn S (approximationTotalPropensity S p) (approximationTotalPropensity S q) =
      supDistOn S p q := by
  unfold supDistOn
  congr 1
  funext x
  rw [approximationTotalPropensity_eq S p x.property,
    approximationTotalPropensity_eq S q x.property]

-- @node: categorical_encoded_history_step_on
/-- Suppose [the number k of categories is positive](hyp:hk), [S is measurable](hyp:hS),
[the first history law assigns full mass to S](hyp:hmu), [the second history
law assigns full mass to S](hyp:hnu), [p and q are measurable propensities](hyp:hp,hq),
[p is probability-valued on S](hyp:hps), [q is probability-valued on S](hyp:hqs),
and [the encoded output for each label is measurable in the history](hyp:hv).
For [nonnegative constants L and D](hyp:L,D), assume [p is L-Lipschitz on S](hyp:hLip)
and [encoded outputs are separated by at most the history distance plus D
when the labels differ, with no extra cost when they agree](hyp:hcost).
Then [the Wasserstein-1 distance between the encoded categorical transition
laws using totalized propensities is at most 1 + DL/2 times the history-law
distance plus kD/2 times the supremum propensity distance on S](goal). -/
lemma categorical_encoded_history_step_on
    {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    {k : ℕ} (hk : 0 < k)
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (S : Set X) (hS : MeasurableSet S)
    (hmu : ∀ᵐ x ∂mu, x ∈ S) (hnu : ∀ᵐ x ∂nu, x ∈ S)
    (p q : X → L1Vec k) (hp : Measurable p) (hq : Measurable q)
    (hps : ∀ x ∈ S, (p x).ofLp ∈ probabilitySimplex k)
    (hqs : ∀ x ∈ S, (q x).ofLp ∈ probabilitySimplex k)
    (v : X → Fin k → Y) (hv : ∀ i, Measurable (fun x => v x i))
    (L D : ℝ≥0) (hLip : LipschitzOnWith L p S)
    (hcost : ∀ x ∈ S, ∀ y ∈ S, ∀ i j,
      dist (v x i) (v y j) ≤ dist x y + if i = j then 0 else (D : ℝ)) :
    wasserstein1
      (mu.bind (categoricalEncodedKernel
        (fun x => (approximationTotalPropensity S p x).ofLp) (by fun_prop) v hv))
      (nu.bind (categoricalEncodedKernel
        (fun x => (approximationTotalPropensity S q x).ofLp) (by fun_prop) v hv)) ≤
      ((1 + D * L / 2 : ℝ≥0) : ℝ≥0∞) * wasserstein1 mu nu +
        ((k * D / 2 : ℝ≥0) : ℝ≥0∞) * supDistOn S p q := by
  have h := categorical_encoded_history_step mu nu S hmu hnu
    (approximationTotalPropensity S p) (approximationTotalPropensity S q)
    (by fun_prop) (by fun_prop)
    (approximationTotalPropensity_simplex hk S p hps)
    (approximationTotalPropensity_simplex hk S q hqs) v hv L D
    (approximationTotalPropensity_lipschitzOn S p L hLip) hcost
  rwa [approximationTotalPropensity_supDistOn] at h

-- @node: approximation_selector_map_eq_bind
/-- Suppose [the categorical node has a positive number of categories](hyp:hk),
[S is measurable](hyp:hS), [the history law assigns full mass to S](hyp:hmu),
[p is measurable](hyp:hp), [p is probability-valued on S](hyp:hps), and
[the encoded output for each label is measurable in the history](hyp:hv).
Then [the output law obtained by applying the Gumbel selector to independent
histories and Gumbel inputs equals the mixture, over the history law, of
the encoded categorical laws with totalized propensity p](goal). -/
lemma approximation_selector_map_eq_bind
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {k : ℕ}
    (hk : ∀ m, Sum.inr k = (Sum.inr m : NodeKind) → 0 < m)
    (mu : Measure X) [IsProbabilityMeasure mu]
    (S : Set X) (hS : MeasurableSet S) (hmu : ∀ᵐ x ∂mu, x ∈ S)
    (p : X → L1Vec k) (hp : Measurable p)
    (hps : ∀ x ∈ S, (p x).ofLp ∈ probabilitySimplex k)
    (v : X → Fin k → Y) (hv : ∀ i, Measurable (fun x => v x i)) :
    (mu.prod (gumbelInputs k)).map (fun z =>
      v z.1 (canonicalSelector (.inr k) hk (p z.1) (WithLp.toLp 1 z.2))) =
      mu.bind (categoricalEncodedKernel
        (fun x => (approximationTotalPropensity S p x).ofLp) (by fun_prop) v hv) := by
  let F : X × (Fin k → ℝ) → Y := fun z =>
    v z.1 (canonicalSelector (.inr k) hk (p z.1) (WithLp.toLp 1 z.2))
  have hselector : Measurable (fun z : X × (Fin k → ℝ) =>
      canonicalSelector (.inr k) hk (p z.1) (WithLp.toLp 1 z.2)) := by
    apply firstArgmax_getD_measurable
    intro j
    fun_prop
  have hF : Measurable F := by
    have hv' : Measurable (fun z : X × Fin k => v z.1 z.2) :=
      measurable_from_prod_countable_left hv
    have hs' : Measurable (fun z : X × (Fin k → ℝ) =>
        (canonicalSelector (.inr k) hk (p z.1) (WithLp.toLp 1 z.2) : Fin k)) := hselector
    exact hv'.comp (measurable_fst.prodMk hs')
  let := gumbelInputs_probability k
  ext s hs
  rw [Measure.map_apply hF hs, Measure.prod_apply (hs.preimage hF),
    Measure.bind_apply hs (categoricalEncodedKernel
      (fun x => (approximationTotalPropensity S p x).ofLp) (by fun_prop) v hv).aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [hmu] with x hx
  have he := canonicalSelector_encoded_law hk (p x) (hps x hx) (v x)
  have hm : Measurable (fun g => F (x,g)) := hF.comp measurable_prodMk_left
  change (gumbelInputs k) ((fun g => F (x,g)) ⁻¹' s) = _
  rw [← Measure.map_apply hm hs]
  change ((gumbelInputs k).map (fun g =>
    v x (canonicalSelector (.inr k) hk (p x) (WithLp.toLp 1 g)))) s = _
  exact (congrArg (fun m : Measure Y => m s) he).trans (by
    simp only [categoricalEncodedKernel, Kernel.coe_mk,
      approximationTotalPropensity_eq S p hx])

-- @node: approximation_selector_history_step
/-- Suppose [the categorical node has a positive number k of categories](hyp:hk),
[S is measurable](hyp:hS), [the first history law assigns full mass to S](hyp:hmu),
[the second history law assigns full mass to S](hyp:hnu), [p and q are measurable](hyp:hp,hq),
[p is probability-valued on S](hyp:hps), [q is probability-valued on S](hyp:hqs),
and [the encoded output for each label is measurable in the history](hyp:hv).
For [nonnegative constants L and D](hyp:L,D), assume [p is L-Lipschitz on S](hyp:hLip)
and [encoded outputs differ by at most the history distance plus D for
unequal labels, with no extra cost for equal labels](hyp:hcost).
Then [the Wasserstein-1 distance between the two Gumbel-selected output laws
is at most 1 + DL/2 times the history-law distance plus kD/2 times the
supremum propensity distance on S](goal). -/
lemma approximation_selector_history_step
    {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    {k : ℕ} (hk : ∀ m, Sum.inr k = (Sum.inr m : NodeKind) → 0 < m)
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (S : Set X) (hS : MeasurableSet S)
    (hmu : ∀ᵐ x ∂mu, x ∈ S) (hnu : ∀ᵐ x ∂nu, x ∈ S)
    (p q : X → L1Vec k) (hp : Measurable p) (hq : Measurable q)
    (hps : ∀ x ∈ S, (p x).ofLp ∈ probabilitySimplex k)
    (hqs : ∀ x ∈ S, (q x).ofLp ∈ probabilitySimplex k)
    (v : X → Fin k → Y) (hv : ∀ i, Measurable (fun x => v x i))
    (L D : ℝ≥0) (hLip : LipschitzOnWith L p S)
    (hcost : ∀ x ∈ S, ∀ y ∈ S, ∀ i j,
      dist (v x i) (v y j) ≤ dist x y + if i = j then 0 else (D : ℝ)) :
    wasserstein1
      ((mu.prod (gumbelInputs k)).map (fun z =>
        v z.1 (canonicalSelector (.inr k) hk (p z.1) (WithLp.toLp 1 z.2))))
      ((nu.prod (gumbelInputs k)).map (fun z =>
        v z.1 (canonicalSelector (.inr k) hk (q z.1) (WithLp.toLp 1 z.2)))) ≤
      ((1 + D * L / 2 : ℝ≥0) : ℝ≥0∞) * wasserstein1 mu nu +
        ((k * D / 2 : ℝ≥0) : ℝ≥0∞) * supDistOn S p q := by
  rw [approximation_selector_map_eq_bind hk mu S hS hmu p hp hps v hv,
    approximation_selector_map_eq_bind hk nu S hS hnu q hq hqs v hv]
  exact categorical_encoded_history_step_on (hk k rfl) mu nu S hS hmu hnu
    p q hp hq hps hqs v hv L D hLip hcost

-- @node: approximation_categorical_selector_history_step
/-- Suppose [the categorical node has a positive number k of categories](hyp:hk),
[S is measurable](hyp:hS), [the first history law assigns full mass to S](hyp:hmu),
[the second history law assigns full mass to S](hyp:hnu), [p and q are measurable](hyp:hp,hq),
[p is probability-valued on S](hyp:hps), and [q is probability-valued on S](hyp:hqs).
For [a nonnegative constant L](hyp:L), assume [p is L-Lipschitz on S](hyp:hLip).
Then [appending the Gumbel-selected numeric label from 1 through k gives
output laws whose Wasserstein-1 distance is at most 1 + (k − 1)L/2 times
the history-law distance plus k(k − 1)/2 times the supremum propensity
distance on S](goal). -/
lemma approximation_categorical_selector_history_step
    {h k : ℕ} (hk : ∀ m, Sum.inr k = (Sum.inr m : NodeKind) → 0 < m)
    (mu nu : Measure (L1Vec h)) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (S : Set (L1Vec h)) (hS : MeasurableSet S)
    (hmu : ∀ᵐ x ∂mu, x ∈ S) (hnu : ∀ᵐ x ∂nu, x ∈ S)
    (p q : L1Vec h → L1Vec k) (hp : Measurable p) (hq : Measurable q)
    (hps : ∀ x ∈ S, (p x).ofLp ∈ probabilitySimplex k)
    (hqs : ∀ x ∈ S, (q x).ofLp ∈ probabilitySimplex k)
    (L : ℝ≥0) (hLip : LipschitzOnWith L p S) :
    let v := fun (x : L1Vec h) (i : Fin k) =>
      WithLp.toLp 1 (Sum.elim x.ofLp (fun _ : Unit => (i.val + 1 : ℝ)))
    wasserstein1
      ((mu.prod (gumbelInputs k)).map (fun z =>
        v z.1 (canonicalSelector (.inr k) hk (p z.1) (WithLp.toLp 1 z.2))))
      ((nu.prod (gumbelInputs k)).map (fun z =>
        v z.1 (canonicalSelector (.inr k) hk (q z.1) (WithLp.toLp 1 z.2)))) ≤
      ((1 + (k-1 : ℕ) * L / 2 : ℝ≥0) : ℝ≥0∞) * wasserstein1 mu nu +
        ((k * (k-1 : ℕ) / 2 : ℝ≥0) : ℝ≥0∞) * supDistOn S p q := by
  dsimp only
  apply approximation_selector_history_step hk mu nu S hS hmu hnu p q hp hq hps hqs
    (fun x i => WithLp.toLp 1 (Sum.elim x.ofLp
      (fun _ : Unit => (i.val + 1 : ℝ)))) (by fun_prop) L (k-1 : ℕ) hLip
  intro x hx y hy i j
  simp only [PiLp.dist_eq_of_L1, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Fintype.sum_unique]
  by_cases hij : i = j
  · simp [hij]
  · simp only [hij, if_false]
    exact add_le_add le_rfl (categorical_label_diameter_le i j)

end
end Papers.TbsNeuralCausalPi

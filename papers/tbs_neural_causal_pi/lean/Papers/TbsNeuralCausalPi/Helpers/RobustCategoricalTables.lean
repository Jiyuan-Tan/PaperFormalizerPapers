module
public import Papers.TbsNeuralCausalPi.Helpers.RobustCategoricalRace
public import Mathlib.MeasureTheory.Integral.Bochner.Set
/-! # Ambiguity bounds for latent-dependent categorical tables

Integrating the robust race estimate over the non-Gumbel latent law gives a
bound for each table prefix. A finite union bound then controls all prefixes,
even when different prefixes reuse the same categorical noise vector.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

-- @node: measurableSet_robustCategoricalWinner_random
/-- If [the category weights depend measurably on the underlying state](hyp:hq)
and [the noise vector also depends measurably on that state](hyp:hG), then
[the event that label i is a robust winner at the given tolerance is measurable](goal). -/
lemma measurableSet_robustCategoricalWinner_random
    {X : Type*} [MeasurableSpace X] {n : ℕ}
    (q G : X → Fin n → ℝ) (hq : Measurable q) (hG : Measurable G)
    (a : ℝ) (i : Fin n) :
    MeasurableSet {x | RobustCategoricalWinner (q x) a (G x) i} := by
  first | fun_prop | skip
  simp only [RobustCategoricalWinner, Set.setOf_and, Set.setOf_forall]
  apply MeasurableSet.inter (measurableSet_lt (by fun_prop) (by fun_prop))
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro hji
  have heq : {x | 0 < q x j + a →
      Real.log (q x j + a) + G x j < Real.log (q x i - a) + G x i} =
      {x | 0 < q x j + a}ᶜ ∪
        {x | Real.log (q x j + a) + G x j < Real.log (q x i - a) + G x i} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_compl_iff, imp_iff_not_or]
  rw [heq]
  exact (measurableSet_lt (by fun_prop) (by fun_prop)).compl.union
    (measurableSet_lt (by fun_prop) (by fun_prop))

-- @node: gumbel_no_robust_label_product_probability_le
/-- If [the category weights depend measurably on a latent state](hyp:hq),
[are nonnegative at every state](hyp:hpos), [sum to one at every state](hyp:hsum),
and [the tolerance a is nonnegative](hyp:ha), then [under the product of any
latent probability law and independent standard Gumbel noise, the probability
of having no robust winning label is at most twice the number of labels times a](goal). -/
lemma gumbel_no_robust_label_product_probability_le
    {X : Type*} [MeasurableSpace X] {n : ℕ}
    (nu : Measure X) [IsProbabilityMeasure nu]
    (q : X → Fin n → ℝ) (hq : Measurable q)
    (hpos : ∀ x j, 0 ≤ q x j) (hsum : ∀ x, ∑ j, q x j = 1)
    (a : ℝ) (ha : 0 ≤ a) :
    (nu.prod (gumbelInputs n))
      {z | ¬ ∃ i, RobustCategoricalWinner (q z.1) a z.2 i} ≤
        ENNReal.ofReal (2 * n * a) := by
  letI := gumbelInputs_probability n
  have hm : MeasurableSet {z : X × (Fin n → ℝ) |
      ¬ ∃ i, RobustCategoricalWinner (q z.1) a z.2 i} := by
    simpa only [Set.compl_iUnion, Set.compl_setOf, Set.iInter_setOf, not_exists, Function.comp_apply] using
      (MeasurableSet.iUnion fun i => measurableSet_robustCategoricalWinner_random
        (q ∘ Prod.fst) Prod.snd (by fun_prop) (by fun_prop) a i).compl
  rw [Measure.prod_apply hm]
  calc
    _ ≤ ∫⁻ _x, ENNReal.ofReal (2 * n * a) ∂nu := by
      apply lintegral_mono
      intro x
      exact gumbel_no_robust_label_probability_le (q x) a (hpos x) (hsum x) ha
    _ = _ := by simp

/-- Suppose [the latent vector is measurable](hyp:hU), [the noise vector is
measurable](hyp:hG), [they are independent](hyp:hind), and [the noise has the
independent standard Gumbel law](hyp:hlaw). If [the weights depend measurably
on the latent vector](hyp:hq), [are everywhere nonnegative](hyp:hpos),
[sum to one at every latent state](hyp:hsum), and [the tolerance a is
nonnegative](hyp:ha), then [the probability that no label is a robust winner
is at most twice the number of labels times a](goal). -/
-- @node: gumbel_no_robust_label_independent_probability_le
lemma gumbel_no_robust_label_independent_probability_le
    {Omega X : Type*} [MeasurableSpace Omega] [MeasurableSpace X] {n : ℕ}
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (U : Omega → X) (G : Omega → Fin n → ℝ)
    (hU : Measurable U) (hG : Measurable G) (hind : IndepFun U G mu)
    (hlaw : mu.map G = gumbelInputs n)
    (q : X → Fin n → ℝ) (hq : Measurable q)
    (hpos : ∀ x j, 0 ≤ q x j) (hsum : ∀ x, ∑ j, q x j = 1)
    (a : ℝ) (ha : 0 ≤ a) :
    mu {w | ¬ ∃ i, RobustCategoricalWinner (q (U w)) a (G w) i} ≤
      ENNReal.ofReal (2 * n * a) := by
  letI := Measure.isProbabilityMeasure_map (μ := mu) hU.aemeasurable
  have hm : MeasurableSet {z : X × (Fin n → ℝ) |
      ¬ ∃ i, RobustCategoricalWinner (q z.1) a z.2 i} := by
    simpa only [Set.compl_iUnion, Set.compl_setOf, Set.iInter_setOf, not_exists, Function.comp_apply] using
      (MeasurableSet.iUnion fun i => measurableSet_robustCategoricalWinner_random
        (q ∘ Prod.fst) Prod.snd (by fun_prop) (by fun_prop) a i).compl
  have hprod := hind.map_prod_eq_prod_map_map hU.aemeasurable hG.aemeasurable
  rw [hlaw] at hprod
  have h := gumbel_no_robust_label_product_probability_le (mu.map U) q hq hpos hsum a ha
  rw [← hprod, Measure.map_apply (hU.prodMk hG) hm] at h
  exact h

-- @node: CategoricalTableAmbiguity
/-- Given [the number of labels at each table prefix](hyp:size), [a latent
vector U](hyp:U), [noise vectors for the prefixes](hyp:G), [latent-dependent
category weights for the prefixes](hyp:q), [a tolerance a](hyp:a), and
[an outcome w of the underlying experiment](hyp:w), [table ambiguity](goal)
means that at least one prefix has no robust winning label at that outcome. -/
def CategoricalTableAmbiguity {Omega X I : Type*} (size : I → ℕ)
    (U : Omega → X) (G : ∀ p, Omega → Fin (size p) → ℝ)
    (q : ∀ p, X → Fin (size p) → ℝ) (a : ℝ) (w : Omega) : Prop :=
  ∃ p, ¬ ∃ i, RobustCategoricalWinner (q p (U w)) a (G p w) i

-- @node: measurableSet_categoricalTableAmbiguity
/-- Given [a noise vector for each table prefix](hyp:G) and
[category weights for each prefix as functions of the latent state](hyp:q),
if [the latent vector is measurable](hyp:hU), [every prefix noise vector
is measurable](hyp:hG), and [every prefix's category weights are measurable
functions of the latent state](hyp:hq), then [the ambiguity event for the
finite collection of table prefixes is measurable](goal). -/
lemma measurableSet_categoricalTableAmbiguity
    {Omega X I : Type*} [MeasurableSpace Omega] [MeasurableSpace X] [Fintype I]
    (size : I → ℕ) (U : Omega → X) (G : ∀ p, Omega → Fin (size p) → ℝ)
    (q : ∀ p, X → Fin (size p) → ℝ)
    (hU : Measurable U) (hG : ∀ p, Measurable (G p))
    (hq : ∀ p, Measurable (q p)) (a : ℝ) :
    MeasurableSet {w | CategoricalTableAmbiguity size U G q a w} := by
  simp only [CategoricalTableAmbiguity, Set.setOf_exists]
  apply MeasurableSet.iUnion
  intro p
  simpa only [Set.compl_iUnion, Set.compl_setOf, Set.iInter_setOf, not_exists, Function.comp_apply] using
    (MeasurableSet.iUnion fun i => measurableSet_robustCategoricalWinner_random
      (q p ∘ U) (G p) (by fun_prop) (hG p) a i).compl

/-- For [prefix noise vectors G](hyp:G) and [latent-dependent prefix weights
q](hyp:q), suppose [the latent vector is measurable](hyp:hU), [each noise
vector is measurable](hyp:hG), [each is independent of the latent vector](hyp:hind),
and [each has the independent standard Gumbel law for its number of labels](hyp:hlaw).
If [each prefix's weights are measurable](hyp:hq), [nonnegative everywhere](hyp:hpos),
[sum to one at every latent state](hyp:hsum), and [the tolerance a is
nonnegative](hyp:ha), then [the probability of table ambiguity is at most
twice the total number of labels across all prefixes times a](goal). -/
-- @node: categoricalTableAmbiguity_probability_le
lemma categoricalTableAmbiguity_probability_le
    {Omega X I : Type*} [MeasurableSpace Omega] [MeasurableSpace X] [Fintype I]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (size : I → ℕ) (U : Omega → X) (G : ∀ p, Omega → Fin (size p) → ℝ)
    (q : ∀ p, X → Fin (size p) → ℝ)
    (hU : Measurable U) (hG : ∀ p, Measurable (G p))
    (hind : ∀ p, IndepFun U (G p) mu) (hlaw : ∀ p, mu.map (G p) = gumbelInputs (size p))
    (hq : ∀ p, Measurable (q p)) (hpos : ∀ p x j, 0 ≤ q p x j)
    (hsum : ∀ p x, ∑ j, q p x j = 1) (a : ℝ) (ha : 0 ≤ a) :
    mu {w | CategoricalTableAmbiguity size U G q a w} ≤
      ENNReal.ofReal (2 * (∑ p, (size p : ℝ)) * a) := by
  classical
  calc
    _ = mu (⋃ p, {w | ¬ ∃ i, RobustCategoricalWinner (q p (U w)) a (G p w) i}) := by
      congr 1
      ext w
      simp [CategoricalTableAmbiguity]
    _ ≤ ∑ p, mu {w | ¬ ∃ i, RobustCategoricalWinner (q p (U w)) a (G p w) i} :=
      measure_iUnion_fintype_le _ _
    _ ≤ ∑ p, ENNReal.ofReal (2 * size p * a) := Finset.sum_le_sum fun p _ =>
      gumbel_no_robust_label_independent_probability_le mu U (G p) hU (hG p)
        (hind p) (hlaw p) (q p) (hq p) (hpos p) (hsum p) a ha
    _ = _ := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun p _ => by positivity)]
      congr 1
      simp only [Finset.mul_sum, Finset.sum_mul]

/-- For [prefix noise vectors G](hyp:G) and [latent-dependent prefix weights
q](hyp:q), if [the latent vector is measurable](hyp:hU), [each noise vector
is measurable](hyp:hG), and [each prefix's weights are measurable](hyp:hq),
then [the real-valued indicator of table ambiguity is integrable under the
underlying probability law](goal). -/
-- @node: categoricalTableAmbiguity_indicator_integrable
lemma categoricalTableAmbiguity_indicator_integrable
    {Omega X I : Type*} [MeasurableSpace Omega] [MeasurableSpace X] [Fintype I]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (size : I → ℕ) (U : Omega → X) (G : ∀ p, Omega → Fin (size p) → ℝ)
    (q : ∀ p, X → Fin (size p) → ℝ)
    (hU : Measurable U) (hG : ∀ p, Measurable (G p))
    (hq : ∀ p, Measurable (q p)) (a : ℝ) :
    Integrable ({w | CategoricalTableAmbiguity size U G q a w}.indicator
      (fun _ => (1 : ℝ))) mu := by
  exact (integrable_const 1).indicator
    (measurableSet_categoricalTableAmbiguity size U G q hU hG hq a)

-- @node: categoricalTableAmbiguity_expectation_le
/-- For [prefix noise vectors G](hyp:G) and [latent-dependent prefix weights
q](hyp:q), suppose [the latent vector is measurable](hyp:hU), [each noise
vector is measurable](hyp:hG), [each is independent of the latent vector](hyp:hind),
and [each has the independent standard Gumbel law for its number of labels](hyp:hlaw).
If [the prefix weights are measurable](hyp:hq), [nonnegative everywhere](hyp:hpos),
[sum to one at every latent state](hyp:hsum), and [the tolerance a is
nonnegative](hyp:ha), then [the expected ambiguity indicator is at most twice
the total number of labels across all prefixes times a](goal). -/
lemma categoricalTableAmbiguity_expectation_le
    {Omega X I : Type*} [MeasurableSpace Omega] [MeasurableSpace X] [Fintype I]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (size : I → ℕ) (U : Omega → X) (G : ∀ p, Omega → Fin (size p) → ℝ)
    (q : ∀ p, X → Fin (size p) → ℝ)
    (hU : Measurable U) (hG : ∀ p, Measurable (G p))
    (hind : ∀ p, IndepFun U (G p) mu) (hlaw : ∀ p, mu.map (G p) = gumbelInputs (size p))
    (hq : ∀ p, Measurable (q p)) (hpos : ∀ p x j, 0 ≤ q p x j)
    (hsum : ∀ p x, ∑ j, q p x j = 1) (a : ℝ) (ha : 0 ≤ a) :
    (∫ w, {w | CategoricalTableAmbiguity size U G q a w}.indicator
      (fun _ => (1 : ℝ)) w ∂mu) ≤ 2 * (∑ p, (size p : ℝ)) * a := by
  have hi := integral_indicator_one (μ := mu)
    (measurableSet_categoricalTableAmbiguity size U G q hU hG hq a)
  simp only [Pi.one_def] at hi
  rw [hi]
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (categoricalTableAmbiguity_probability_le mu size U G q hU hG hind hlaw
      hq hpos hsum a ha)
  simpa only [measureReal_def, ENNReal.toReal_ofReal (by positivity :
    0 ≤ 2 * (∑ p, (size p : ℝ)) * a)] using h

/-- For [prefix noise vectors G](hyp:G) and [latent-dependent reference weights
q](hyp:q), suppose [all reference weights are nonnegative](hyp:hpos), [sum to
one at each prefix and latent state](hyp:hsum), [the tolerance a is
nonnegative](hyp:ha), and [every prefix has at least one label](hyp:hk).
At [an outcome with no table ambiguity](hyp:hgood), if [the proposed weights
at a chosen prefix are nonnegative](hyp:hr), [sum to one](hyp:hrsum), and
[differ from the reference weights by at most a in every coordinate](hyp:hnear),
then [the canonical selector returns the same label for the proposed and
reference weights using that prefix's common noise vector](goal). -/
-- @node: categoricalTable_noAmbiguity_selector_agreement
lemma categoricalTable_noAmbiguity_selector_agreement
    {Omega X I : Type*} (size : I → ℕ)
    (U : Omega → X) (G : ∀ p, Omega → Fin (size p) → ℝ)
    (q : ∀ p, X → Fin (size p) → ℝ)
    (hpos : ∀ p x j, 0 ≤ q p x j) (hsum : ∀ p x, ∑ j, q p x j = 1)
    (a : ℝ) (ha : 0 ≤ a)
    (hk : ∀ p m, Sum.inr (size p) = (Sum.inr m : NodeKind) → 0 < m)
    (w : Omega) (hgood : ¬ CategoricalTableAmbiguity size U G q a w)
    (p : I) (r : Fin (size p) → ℝ) (hr : ∀ j, 0 ≤ r j) (hrsum : ∑ j, r j = 1)
    (hnear : ∀ j, |r j - q p (U w) j| ≤ a) :
    canonicalSelector (.inr (size p)) (hk p) (WithLp.toLp 1 r) (WithLp.toLp 1 (G p w)) =
      canonicalSelector (.inr (size p)) (hk p)
        (WithLp.toLp 1 (q p (U w))) (WithLp.toLp 1 (G p w)) := by
  have hex : ∃ i, RobustCategoricalWinner (q p (U w)) a (G p w) i := by
    by_contra h
    exact hgood ⟨p, h⟩
  obtain ⟨i, hi⟩ := hex
  exact (robustCategoricalWinner_canonicalSelector _ r a ha hr hrsum hnear _ i hi (hk p)).trans
    (robustCategoricalWinner_canonicalSelector _ _ a ha (hpos p (U w)) (hsum p (U w))
      (fun j => by simpa using ha) _ i hi (hk p)).symm

end
end Papers.TbsNeuralCausalPi

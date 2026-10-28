module
public import Papers.OaiGraphDecompositionsIntegral.Helpers.Tests
public import Causalean.Stat.FiniteDesign.ProductMeasure

/-! # Bernoulli marginal and smoothing identities for neighborhood tests -/

@[expose] public section

open Causalean.Experimentation.DesignBased MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Papers.OaiGraphDecompositionsIntegral

attribute [local instance] Classical.propDecidable

-- @node: productMeasure_E_comp_injective
/-- If [the coordinate selection is injective](hyp:hf), then [the expected value
of any statistic of the selected Bernoulli coordinates equals its expected value
under the Bernoulli product distribution on the smaller index set](goal). -/
lemma productMeasure_E_comp_injective {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (r : ℝ) (f : J → I) (hf : Function.Injective f)
    (g : (J → Bool) → ℝ) :
    (productMeasure I r).E (fun z => g (fun j => z (f j))) =
      (productMeasure J r).E g := by
  let : MeasurableSpace Bool := ⊤
  let D := coinDesign (max 0 (min r 1)) (le_max_left 0 (min r 1))
    (max_le zero_le_one (min_le_right r 1))
  change (prodDesign (fun _ : I => D)).E _ = (prodDesign (fun _ : J => D)).E _
  have hm : (prodDesign (fun _ : I => D)).toMeasure.map (fun z j => z (f j)) =
      (prodDesign (fun _ : J => D)).toMeasure := by
    rw [(iIndepFun_prodDesign_eval (fun _ : I => D)).precomp hf |>.map_fun_eq_pi_map
      (fun _ => (measurable_of_finite _).aemeasurable)]
    simp_rw [prodDesign_toMeasure_eq_pi]
    congr 1
    funext j
    exact (measurePreserving_eval (fun _ : I => D.toMeasure) (f j)).map_eq
  rw [← FiniteDesign.integral_toMeasure, ← FiniteDesign.integral_toMeasure, ← hm,
    integral_map (measurable_of_finite _).aemeasurable
      (measurable_of_finite _).aestronglyMeasurable]

-- @node: unionDensity_mem_Icc
/-- If [r is nonnegative](hyp:hr0) and [at most one](hyp:hr1), then
[the union density, one minus the square of one minus r, lies between zero and one](goal). -/
lemma unionDensity_mem_Icc {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    unionDensity r ∈ Set.Icc 0 1 := by
  dsimp [unionDensity]
  constructor <;> nlinarith [sq_nonneg (1 - r)]

-- @node: productMeasure_E_union
/-- If [r is nonnegative](hyp:hr0) and [at most one](hyp:hr1), then [the expected
value of any statistic of the union of two independent Bernoulli-r subsets equals
its expectation under independent inclusion with probability one minus the square
of one minus r](goal). -/
lemma productMeasure_E_union {Y : Type} [Fintype Y] [DecidableEq Y]
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (g : (Y → Bool) → ℝ) :
    (productMeasure Y r).E (fun a => (productMeasure Y r).E
      (fun b => g (fun y => a y || b y))) =
        (productMeasure Y (unionDensity r)).E g := by
  -- Expand the arbitrary statistic in centered monomials. Each coordinate
  -- then reduces to two independent coin draws, whose union has bias tau.
  obtain ⟨c, hc⟩ := exists_centeredMonomial_expansion (fun _ : Y => unionDensity r) g
  have ht := unionDensity_mem_Icc hr0 hr1
  rw [show g = (fun z => ∑ S ∈ (Finset.univ : Finset Y).powerset,
    c S * centeredMonomial (fun _ : Y => unionDensity r) S z) from funext hc]
  simp_rw [FiniteDesign.E_sum, FiniteDesign.E_const_mul]
  apply Finset.sum_congr rfl
  intro S _
  congr 1
  have hmon (a : Y → Bool) :
      (productMeasure Y r).E (fun b => centeredMonomial
        (fun _ : Y => unionDensity r) S (fun y => a y || b y)) =
      ∏ y : Y, (coinDesign r hr0 hr1).E
        (fun b => if y ∈ S then (if a y || b then 1 else 0) - unionDensity r else 1) := by
    change (Toolkit.Foundations.Probability.bernoulliCube Y r).E _ = _
    rw [Toolkit.Foundations.Probability.bernoulliCube_eq r hr0 hr1]
    change (prodDesign (fun _ : Y => coinDesign r hr0 hr1)).E _ = _
    rw [← FiniteDesign.E_prod_prod]
    apply FiniteDesign.E_congr
    intro b
    simp [centeredMonomial, treatInd, Finset.prod_ite_mem]
  have hright : (productMeasure Y (unionDensity r)).E
      (centeredMonomial (fun _ : Y => unionDensity r) S) =
      ∏ y : Y, (coinDesign (unionDensity r) ht.1 ht.2).E
        (fun b => if y ∈ S then (if b then 1 else 0) - unionDensity r else 1) := by
    change (Toolkit.Foundations.Probability.bernoulliCube Y (unionDensity r)).E _ = _
    rw [Toolkit.Foundations.Probability.bernoulliCube_eq _ ht.1 ht.2]
    change (prodDesign (fun _ : Y => coinDesign (unionDensity r) ht.1 ht.2)).E _ = _
    rw [← FiniteDesign.E_prod_prod]
    apply FiniteDesign.E_congr
    intro b
    simp [centeredMonomial, treatInd, Finset.prod_ite_mem]
  rw [hright]
  simp_rw [hmon]
  change (Toolkit.Foundations.Probability.bernoulliCube Y r).E _ = _
  rw [Toolkit.Foundations.Probability.bernoulliCube_eq r hr0 hr1]
  change (prodDesign (fun _ : Y => coinDesign r hr0 hr1)).E _ = _
  rw [FiniteDesign.E_prod_prod (fun _ : Y => coinDesign r hr0 hr1)
    (fun y a => (coinDesign r hr0 hr1).E
      (fun b => if y ∈ S then (if a || b then 1 else 0) - unionDensity r else 1))]
  apply Finset.prod_congr rfl
  intro y _
  simp_rw [coinDesign_E]
  by_cases hy : y ∈ S <;> simp [hy, unionDensity]
  all_goals ring

-- @node: neighborhoodEdge
/-- For [a vertex set Y](hyp:Y), [a vertex w](hyp:w) [outside Y](hyp:hw),
and [a vertex y in Y](hyp:y), [the neighborhood edge](goal) is the unordered
edge joining w to y. -/
def neighborhoodEdge {n : ℕ} (Y : Finset (Fin n)) (w : Fin n) (hw : w ∉ Y)
    (y : ↥Y) : KEdge n :=
  ⟨s(w, y.val), by
    simpa using (show w ≠ y.val from fun h => hw (h ▸ y.property))⟩

-- @node: neighborhoodEdge_injective
/-- If [w lies outside Y](hyp:hw), then [distinct vertices of Y give distinct
unordered edges joining them to w](goal). -/
lemma neighborhoodEdge_injective {n : ℕ} (Y : Finset (Fin n)) (w : Fin n)
    (hw : w ∉ Y) : Function.Injective (neighborhoodEdge Y w hw) := by
  intro a b h
  have h' := congrArg Subtype.val h
  simp only [neighborhoodEdge, Sym2.eq_iff] at h'
  rcases h' with h' | h'
  · exact Subtype.ext h'.2
  · exact (hw (h'.1 ▸ b.property)).elim

-- @node: neighborhoodIn_hostGraph
/-- If [w lies outside Y](hyp:hw), then [its neighbors in Y in the host graph
are exactly those vertices whose edge to w has a true edge indicator](goal). -/
lemma neighborhoodIn_hostGraph {n : ℕ} (Y : Finset (Fin n)) (w : Fin n)
    (hw : w ∉ Y) (z : KEdge n → Bool) :
    neighborhoodIn Y (hostGraph z) w = toFinset' (fun y => z (neighborhoodEdge Y w hw y)) := by
  ext y
  have hne : w ≠ y.val := fun h => hw (h ▸ y.property)
  simp only [neighborhoodIn, toFinset', Finset.mem_filter, Finset.mem_univ, true_and,
    hostGraph, SimpleGraph.fromEdgeSet_adj, Set.mem_ofPred_eq]
  simp [neighborhoodEdge, hne]

-- @node: smoothedTest_mean
/-- If [r is nonnegative](hyp:hr0) and [at most one](hyp:hr1), then [the mean
smoothed satisfaction probability for a Bernoulli-r subset equals the satisfaction
probability at the union density, one minus the square of one minus r](goal). -/
lemma smoothedTest_mean {Y : Type} [Fintype Y] [DecidableEq Y]
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (Q : Finset (Finset Y)) :
    (productMeasure Y r).E (fun a => smoothedTest Y r Q (toFinset' a)) = xQ r Q := by
  have hunion (a b : Y → Bool) :
      toFinset' a ∪ toFinset' b = toFinset' (fun y => a y || b y) := by
    ext y
    simp [toFinset']
  change (productMeasure Y r).E (fun a => (productMeasure Y r).E
    (fun b => if Satisfies Q (toFinset' a ∪ toFinset' b) then 1 else 0)) =
      (productMeasure Y (unionDensity r)).E
        (fun a => if Satisfies Q (toFinset' a) then 1 else 0)
  simpa only [FiniteDesign.ind, hunion] using
    productMeasure_E_union r hr0 hr1
      (fun a => if Satisfies Q (toFinset' a) then 1 else 0)

/-- If [the source density lies between zero and one](hyp:hr), then [the amplified
density, one minus the thirty-second power of one minus the source density,
also lies between zero and one](goal). -/
lemma targetDensity_unitInterval {r : ℝ} (hr : r ∈ Set.Icc 0 1) :
    targetDensity r ∈ Set.Icc 0 1 := by
  unfold targetDensity
  constructor
  · exact sub_nonneg.mpr (pow_le_one₀ (by linarith [hr.2]) (by linarith [hr.1]))
  · exact sub_le_self _ (by positivity)

-- @node: neighborhood_smoothedTest_mean
/-- If [w lies outside Y](hyp:hw), [r is nonnegative](hyp:hr0), and [r is at most
one](hyp:hr1), then [the expected smoothed test of w's neighbors in Y in a
Bernoulli-r host equals the requirement family's satisfaction probability at the
union density](goal). -/
lemma neighborhood_smoothedTest_mean {n : ℕ} (Y : Finset (Fin n)) (w : Fin n)
    (hw : w ∉ Y) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (Q : Finset (Finset ↥Y)) :
    (randomHost n r ⟨hr0, hr1⟩).E (fun z => smoothedTest ↥Y r Q
      (neighborhoodIn Y (hostGraph z) w)) = xQ r Q := by
  simp_rw [neighborhoodIn_hostGraph Y w hw]
  change (productMeasure (KEdge n) r).E _ = _
  rw [productMeasure_E_comp_injective r _ (neighborhoodEdge_injective Y w hw)
    (fun a => smoothedTest ↥Y r Q (toFinset' a))]
  exact smoothedTest_mean r hr0 hr1 Q

-- @node: neighborhood_indicator_mean
/-- If [w lies outside Y](hyp:hw) and [r lies between zero and one](hyp:hr), then
[the expected indicator that w's neighbors in Y satisfy the requirement family
in a host sampled at the amplified density equals that family's satisfaction
probability at the amplified density](goal). -/
lemma neighborhood_indicator_mean {n : ℕ} (Y : Finset (Fin n)) (w : Fin n)
    (hw : w ∉ Y) (r : ℝ) (hr : r ∈ Set.Icc 0 1)
    (Q : Finset (Finset ↥Y)) :
    (randomHost n (targetDensity r) (targetDensity_unitInterval hr)).E (fun z =>
      FiniteDesign.ind (fun a => Satisfies Q (neighborhoodIn Y (hostGraph a) w)) z) =
        xStarQ r Q := by
  simp_rw [FiniteDesign.ind, neighborhoodIn_hostGraph Y w hw]
  change (productMeasure (KEdge n) (targetDensity r)).E _ = _
  rw [productMeasure_E_comp_injective _ _ (neighborhoodEdge_injective Y w hw)
    (fun a => if Satisfies Q (toFinset' a) then 1 else 0)]
  rfl

-- @node: neighborhood_statistics_independent
/-- If [r lies between zero and one](hyp:hr), then [applying any fixed real-valued
statistic to the neighborhoods in Y of vertices outside Y gives a mutually
independent family under the Bernoulli-r random host distribution](goal). -/
lemma neighborhood_statistics_independent {n : ℕ} (Y : Finset (Fin n)) (r : ℝ)
    (hr : r ∈ Set.Icc 0 1)
    (F : Finset ↥Y → ℝ) :
    iIndepFun (fun (w : ↥(Finset.univ \ Y)) z =>
      F (neighborhoodIn Y (hostGraph z) w.val)) (randomHost n r hr).toMeasure := by
  let : MeasurableSpace Bool := ⊤
  let edge (w : ↥(Finset.univ \ Y)) :=
    neighborhoodEdge Y w.val (Finset.mem_sdiff.mp w.property).2
  let block (w : ↥(Finset.univ \ Y)) := Finset.univ.image (edge w)
  change iIndepFun _ (prodDesign (fun _ : KEdge n =>
    coinDesign (max 0 (min r 1)) (le_max_left _ _)
      (max_le zero_le_one (min_le_right _ _)))).toMeasure
  apply iIndepFun_prodDesign_of_pairwise_disjoint_blocks _ block
  · intro w v hwv
    apply Finset.disjoint_left.mpr
    intro e hew hev
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hew
    obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hev
    have he := congrArg Subtype.val (ha.trans hb.symm)
    simp only [edge, neighborhoodEdge, Sym2.eq_iff] at he
    rcases he with he | he
    · exact hwv (Subtype.ext he.1)
    · exact (Finset.mem_sdiff.mp w.property).2 (he.1 ▸ b.property)
  · intro w z z' hz
    congr 1
    rw [neighborhoodIn_hostGraph Y w.val (Finset.mem_sdiff.mp w.property).2,
      neighborhoodIn_hostGraph Y w.val (Finset.mem_sdiff.mp w.property).2]
    congr 1
    funext y
    exact hz (edge w y) (Finset.mem_image.mpr ⟨y, Finset.mem_univ _, rfl⟩)

end Papers.OaiGraphDecompositionsIntegral

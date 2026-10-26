module
public import Papers.OaiSharpThresholdMonotone.Helpers.Fourier

/-! # Fourier mass and pivotal influence under arbitrary edge restrictions -/

public section

open scoped BigOperators
open Causalean.Experimentation.DesignBased

namespace Papers.OaiSharpThresholdMonotone

variable {n : ℕ}

-- @node: exteriorBernoulliLaw_eq
/-- For [a free edge set](hyp:F), [an edge probability](hyp:p), and [a distribution on exterior assignments](hyp:ν),
if [the edge probability lies strictly between zero and one](hyp:hp) and
[the distribution of assignments outside the free edge set is independent Bernoulli
with that probability](hyp:hν), then [this distribution equals the standard product
Bernoulli distribution on those exterior edges](goal). -/
lemma exteriorBernoulliLaw_eq (F : Finset (GraphEdge n)) (p : ℝ)
    (ν : FiniteDesign ({e // e ∉ F} → Bool)) (hp : BiasInterior p)
    (hν : ExteriorBernoulliLaw F p ν) : ν = biasedLaw {e // e ∉ F} p := by
  have heq : ν.p = (biasedLaw {e // e ∉ F} p).p := by
    funext y
    rw [hν y]
    simp only [biasedLaw_eq_bernoulliDesign p ⟨hp.1.le, hp.2.le⟩,
      bernoulliDesign, prodDesign_p, coinDesign]
    apply Finset.prod_congr rfl
    intro a _
    cases y a <;> rfl
  have extLaw (D D' : FiniteDesign ({e // e ∉ F} → Bool))
      (h : D.p = D'.p) : D = D' := by
    rcases D with ⟨w, hw, hs⟩
    rcases D' with ⟨w', hw', hs'⟩
    dsimp at h
    subst w'
    rfl
  exact extLaw _ _ heq

-- @node: biasedLaw_E_mergeAssignment
/-- For [a free edge set](hyp:F), [an edge probability](hyp:p), and [a real-valued graph function](hyp:g),
when [the edge probability lies strictly between zero and one](hyp:hp),
[averaging a real-valued graph function first over the free edges and then over the
exterior edges, independently with that probability, equals its expectation under
the full product Bernoulli distribution](goal). -/
lemma biasedLaw_E_mergeAssignment (F : Finset (GraphEdge n)) (p : ℝ)
    (hp : BiasInterior p) (g : GraphConfig n → ℝ) :
    (biasedLaw {e // e ∉ F} p).E (fun y =>
      (biasedLaw {e // e ∈ F} p).E (fun x => g (mergeAssignment F x y))) =
        (biasedLaw (GraphEdge n) p).E g := by
  classical
  let e : (({a // a ∉ F} → Bool) × ({a // a ∈ F} → Bool)) ≃ GraphConfig n :=
    { toFun := fun z => mergeAssignment F z.2 z.1
      invFun := fun x => (fun a => x a.val, fun a => x a.val)
      left_inv := by
        intro z
        apply Prod.ext <;> funext a <;> simp [mergeAssignment, a.property]
      right_inv := by
        intro x
        funext a
        by_cases ha : a ∈ F <;> simp [mergeAssignment, ha] }
  have hw (z : ({a // a ∉ F} → Bool) × ({a // a ∈ F} → Bool)) :
      (biasedLaw (GraphEdge n) p).p (e z) =
        (biasedLaw {a // a ∉ F} p).p z.1 * (biasedLaw {a // a ∈ F} p).p z.2 := by
    simp only [biasedLaw_eq_bernoulliDesign p ⟨hp.1.le, hp.2.le⟩,
      bernoulliDesign, prodDesign_p, coinDesign]
    rw [← Fintype.prod_subtype_mul_prod_subtype (fun a => a ∈ F)]
    have hin (a : {a // a ∈ F}) : e z a.val = z.2 a := by
      simp [e, mergeAssignment, a.property]
    have hout (a : {a // a ∉ F}) : e z a.val = z.1 a := by
      simp [e, mergeAssignment, a.property]
    simp only [hin, hout]
    simp only [mul_comm, Finset.univ_eq_attach]
    congr 1
    apply Finset.prod_congr
    · ext a
      simp
    · intro a _
      rfl
  unfold FiniteDesign.E
  rw [← e.sum_comp, Fintype.sum_prod_type]
  simp_rw [hw, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  dsimp [e]
  ring

-- @node: fourierChar_mergeAssignment
/-- For [a free edge set](hyp:F), [a bias parameter](hyp:p), [an interior Fourier index](hyp:A),
[an exterior Fourier index](hyp:D), [an interior assignment](hyp:x), and [an exterior assignment](hyp:y),
[the biased Fourier character indexed by the union of an interior edge set and
an exterior edge set, evaluated on the merged assignment, is the product of the
respective interior and exterior Fourier characters](goal). -/
lemma fourierChar_mergeAssignment (F : Finset (GraphEdge n)) (p : ℝ)
    (A : Finset {a // a ∈ F}) (D : Finset {a // a ∉ F})
    (x : {a // a ∈ F} → Bool) (y : {a // a ∉ F} → Bool) :
    fourierChar p (A.image Subtype.val ∪ D.image Subtype.val) (mergeAssignment F x y) =
      fourierChar p A x * fourierChar p D y := by
  classical
  have hdis : Disjoint (A.image Subtype.val) (D.image Subtype.val) := by
    rw [Finset.disjoint_left]
    intro a ha hd
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨c, _, hc⟩ := Finset.mem_image.mp hd
    exact c.property (hc ▸ b.property)
  simp only [fourierChar, Finset.prod_union hdis,
    Finset.prod_image Subtype.val_injective.injOn]
  congr 1
  · apply Finset.prod_congr rfl
    intro a _
    simp [coordChar, mergeAssignment, a.property]
  · apply Finset.prod_congr rfl
    intro a _
    simp [coordChar, mergeAssignment, a.property]

-- @node: restricted_fourierCoeff_exterior_coeff
/-- For [a free edge set](hyp:F), [an edge probability](hyp:p), [a Boolean graph function](hyp:f),
[an interior Fourier index](hyp:A), and [an exterior Fourier index](hyp:D),
if [the edge probability lies strictly between zero and one](hyp:hp), then
[the exterior Fourier coefficient of an interior Fourier coefficient of the
restricted function equals the original graph function's Fourier coefficient
indexed by the union of the interior and exterior edge sets](goal). -/
lemma restricted_fourierCoeff_exterior_coeff (F : Finset (GraphEdge n)) (p : ℝ)
    (hp : BiasInterior p) (f : GraphConfig n → Bool)
    (A : Finset {a // a ∈ F}) (D : Finset {a // a ∉ F}) :
    fourierCoeffR p (fun y => fourierCoeff p (restrictFn f F y) A) D =
      graphFourierCoeff p f (A.image Subtype.val ∪ D.image Subtype.val) := by
  simp only [graphFourierCoeff, fourierCoeff, fourierCoeffR]
  rw [← biasedLaw_E_mergeAssignment (n := n) F p hp]
  simp only [fourierChar_mergeAssignment]
  apply FiniteDesign.E_congr
  intro y
  rw [← FiniteDesign.E_mul_const]
  apply FiniteDesign.E_congr
  intro x
  simp only [boolValue, restrictFn]
  split <;> simp_all

-- @node: restricted_fourierCoeff_expansion
/-- For [a free edge set](hyp:F), [an edge probability](hyp:p), [a Boolean graph function](hyp:f),
[a fixed exterior assignment](hyp:y), and [an interior Fourier index consisting of free edges](hyp:A), when
[the edge probability lies strictly between zero and one](hyp:hp), [the restricted
function's Fourier coefficient at a fixed exterior assignment equals the sum over
all exterior indices of the original coefficient at the combined index multiplied
by the exterior Fourier character at that assignment](goal). -/
lemma restricted_fourierCoeff_expansion (F : Finset (GraphEdge n)) (p : ℝ)
    (hp : BiasInterior p) (f : GraphConfig n → Bool)
    (y : {e // e ∉ F} → Bool) (A : Finset {e // e ∈ F}) :
    fourierCoeff p (restrictFn f F y) A =
      ∑ D : Finset {e // e ∉ F}, -- @realizes D(exterior Fourier index)
        graphFourierCoeff p f (A.image Subtype.val ∪ D.image Subtype.val) * fourierChar p D y :=
  by
    have hex := congrFun (fourier_expansion p hp
      (fun y => fourierCoeff p (restrictFn f F y) A)) y
    simpa only [fourierExpansion, restricted_fourierCoeff_exterior_coeff F p hp] using hex

-- @node: averaged_restricted_fourierCoeff_sq
/-- For [a free edge set](hyp:F), [an edge probability](hyp:p), [a Boolean graph function](hyp:f),
and [an interior Fourier index](hyp:A), if [the edge probability lies strictly between zero and one](hyp:hp), then
[the expected squared Fourier coefficient of the restricted function, averaging
over independent Bernoulli exterior assignments, equals the sum of squared original
Fourier coefficients over all extensions of its interior index](goal). -/
lemma averaged_restricted_fourierCoeff_sq (F : Finset (GraphEdge n)) (p : ℝ)
    (hp : BiasInterior p) (f : GraphConfig n → Bool) (A : Finset {e // e ∈ F}) :
    (biasedLaw {e // e ∉ F} p).E (fun y => fourierCoeff p (restrictFn f F y) A ^ 2) =
      ∑ D : Finset {e // e ∉ F},
        graphFourierCoeff p f (A.image Subtype.val ∪ D.image Subtype.val) ^ 2 := by
  rw [secondMoment_eq_sum_fourierCoeffR_sq p hp]
  simp only [restricted_fourierCoeff_exterior_coeff F p hp]

-- @node: averaged_restricted_coordInfluence
/-- For [a free edge set](hyp:F), [an edge probability](hyp:p), [a Boolean graph function](hyp:f),
and [an edge in the free set](hyp:e), if [the edge probability lies strictly between zero and one](hyp:hp), then
[the influence of a free edge in the restricted function, averaged over independent
Bernoulli exterior assignments, equals that edge's influence in the original
graph function](goal). -/
lemma averaged_restricted_coordInfluence (F : Finset (GraphEdge n)) (p : ℝ)
    (hp : BiasInterior p) (f : GraphConfig n → Bool) (e : {e // e ∈ F}) :
    (biasedLaw {e // e ∉ F} p).E
      (fun y => coordInfluence p (restrictFn f F y) e) = edgeInfluence p f e.val := by
  classical
  have hm (x : {a // a ∈ F} → Bool) (y : {a // a ∉ F} → Bool) (b : Bool) :
      mergeAssignment F (coordinateReplace e x b) y =
        coordinateReplace e.val (mergeAssignment F x y) b := by
    funext a
    by_cases ha : a ∈ F
    · by_cases hae : a = e.val
      · subst a
        simp [mergeAssignment, e.property, coordinateReplace,
          Causalean.Mathlib.Probability.PoissonAddOnePoincare.coordinateReplace]
      · have hsub : (⟨a, ha⟩ : {a // a ∈ F}) ≠ e := by
          intro h
          exact hae (congrArg Subtype.val h)
        simp [mergeAssignment, ha, coordinateReplace,
          Causalean.Mathlib.Probability.PoissonAddOnePoincare.coordinateReplace,
          hae, hsub]
    · have hae : a ≠ e.val := by
        intro h
        exact ha (h ▸ e.property)
      simp [mergeAssignment, ha, coordinateReplace,
        Causalean.Mathlib.Probability.PoissonAddOnePoincare.coordinateReplace, hae]
  rw [edgeInfluence_eq_coordInfluence, ← difference_secondMoment_eq_influence]
  simp_rw [← difference_secondMoment_eq_influence]
  have hd (x : {a // a ∈ F} → Bool) (y : {a // a ∉ F} → Bool) :
      coordDiff (restrictFn f F y) e x = coordDiff f e.val (mergeAssignment F x y) := by
    simp only [coordDiff, coordDiffR, boolValue, restrictFn, hm]
  calc
    _ = (biasedLaw {a // a ∉ F} p).E (fun y =>
        (biasedLaw {a // a ∈ F} p).E (fun x =>
          coordDiff f e.val (mergeAssignment F x y) ^ 2)) := by
      apply FiniteDesign.E_congr
      intro y
      apply FiniteDesign.E_congr
      intro x
      rw [hd]
    _ = _ := biasedLaw_E_mergeAssignment (n := n) F p hp
      (fun z => coordDiff f e.val z ^ 2)

-- @node: lem:restriction
/-- For [an edge probability](hyp:p), [a restriction cutoff](hyp:k), [a Boolean graph function](hyp:f),
[a free edge set](hyp:F), and [an exterior assignment distribution](hyp:ν),
suppose [the edge probability lies strictly between zero and one](hyp:hp),
[the graph function is Boolean-valued](hyp:hf), [the chosen edges form a free edge
set](hyp:hF), [the exterior assignment has the independent Bernoulli law at that
probability](hyp:hν), and [the cutoff is positive](hyp:hk). Then [the expected
restricted Fourier mass on nonempty indices of size at most the cutoff equals the
original Fourier mass on indices whose intersection with the free set has that
size range, and the expected total restricted influence equals the sum of original
influences over the free edges](goal). -/
lemma restriction_mass_and_influence (p k : ℝ) (f : GraphConfig n → Bool)
    (F : Finset (GraphEdge n)) (ν : FiniteDesign ({e // e ∉ F} → Bool))
    (hp : BiasInterior p) (hf : BooleanGraphFunction f) (hF : FreeEdgeSet F)
    (hν : ExteriorBernoulliLaw F p ν) (hk : PositiveCutoff k) :
    ν.E (fun y => ∑ A ∈ Finset.univ.filter
      (fun A : Finset {e // e ∈ F} => 1 ≤ A.card ∧ (A.card : ℝ) ≤ k),
        fourierCoeff p (restrictFn f F y) A ^ 2) =
      ∑ S ∈ Finset.univ.filter
        (fun S : Finset (GraphEdge n) => 1 ≤ (S ∩ F).card ∧ ((S ∩ F).card : ℝ) ≤ k),
        graphFourierCoeff p f S ^ 2 ∧
    ν.E (fun y => totalCoordInfluence p (restrictFn f F y)) =
      ∑ e ∈ F, edgeInfluence p f e := by
  classical
  rw [exteriorBernoulliLaw_eq F p ν hp hν]
  constructor
  · let e : (Finset {a // a ∈ F} × Finset {a // a ∉ F}) ≃ Finset (GraphEdge n) :=
      { toFun := fun z => z.1.image Subtype.val ∪ z.2.image Subtype.val
        invFun := fun S => (S.subtype (fun a => a ∈ F), S.subtype (fun a => a ∉ F))
        left_inv := by
          intro z
          apply Prod.ext <;> ext a <;>
            simp [Finset.mem_subtype, a.property]
        right_inv := by
          intro S
          ext a
          by_cases ha : a ∈ F <;> simp [Finset.mem_subtype, ha] }
    have hc (A : Finset {a // a ∈ F}) (D : Finset {a // a ∉ F}) :
        ((A.image Subtype.val ∪ D.image Subtype.val) ∩ F).card = A.card := by
      have hi : (A.image Subtype.val ∪ D.image Subtype.val) ∩ F =
          A.image Subtype.val := by
        ext a
        constructor
        · intro ha
          rcases Finset.mem_union.mp (Finset.mem_inter.mp ha).1 with hA | hD
          · exact hA
          · obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hD
            exact False.elim (b.property (Finset.mem_inter.mp ha).2)
        · intro ha
          obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
          exact Finset.mem_inter.mpr
            ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨b, hb, rfl⟩), b.property⟩
      rw [hi, Finset.card_image_of_injective _ Subtype.val_injective]
    simp_rw [FiniteDesign.E_sum, averaged_restricted_fourierCoeff_sq F p hp]
    rw [Finset.sum_filter, Finset.sum_filter, ← e.sum_comp]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro A _
    dsimp [e]
    simp_rw [hc]
    by_cases hA : 1 ≤ A.card ∧ (A.card : ℝ) ≤ k <;> simp [hA]
  · simp only [totalCoordInfluence, FiniteDesign.E_sum,
      averaged_restricted_coordInfluence F p hp]
    exact (Finset.sum_subtype F (fun _ => Iff.rfl) (edgeInfluence p f)).symm


end Papers.OaiSharpThresholdMonotone

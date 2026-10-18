module
public import Papers.TbsNeuralCausalPi.Helpers.SimplexTableGrid
public import Papers.TbsNeuralCausalPi.Helpers.RobustCategoricalTables
public import Mathlib.Tactic
/-! # Simplex rounding and simultaneous categorical table agreement

The rounded propensity tables remain measurable and simplex-valued. The same
private Gumbel draws select the original and rounded labels outside a single
ambiguity event whose probability is bounded by the total coordinate mesh.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory ProbabilityTheory
open scoped ENNReal

-- @node: categoricalTable_simplex_rounding_agreement
/-- Given [a family of Gumbel input vectors indexed by prefixes](hyp:G),
[simplex-valued propensity tables](hyp:q), and [fallback probability vectors
for rounding](hyp:p0), suppose [the shared covariate is measurable](hyp:hU),
[each input vector is measurable](hyp:hG), [each input vector is independent
of the covariate](hyp:hind), [each input vector has the prescribed Gumbel
distribution](hyp:hlaw), [each propensity table is measurable](hyp:hq),
[the rounding resolution is positive](hyp:hR), and [every categorical
output size is positive](hyp:hk). After simplex rounding at that resolution,
[the ambiguity event is measurable, has probability at most twice the total
number of coordinates divided by the resolution, and outside it the original
and rounded categorical selectors agree simultaneously at every prefix when
using the same Gumbel inputs](goal).

No propensity coordinate needs to be strictly positive, and different prefixes
may share noise. -/
lemma categoricalTable_simplex_rounding_agreement
    {Omega X I : Type*} [MeasurableSpace Omega] [MeasurableSpace X] [Fintype I]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (size : I → ℕ) (U : Omega → X) (G : ∀ p, Omega → Fin (size p) → ℝ)
    (q : ∀ p, X → probabilitySimplex (size p))
    (p0 : ∀ p, probabilitySimplex (size p))
    (hU : Measurable U) (hG : ∀ p, Measurable (G p))
    (hind : ∀ p, IndepFun U (G p) mu)
    (hlaw : ∀ p, mu.map (G p) = gumbelInputs (size p))
    (hq : ∀ p, Measurable (q p)) {R : ℕ} (hR : 0 < R)
    (hk : ∀ p m, Sum.inr (size p) = (Sum.inr m : NodeKind) → 0 < m) :
    let rounded := fun p x => (simplexRound (p0 p) R (q p x)).val
    let bad := {w | CategoricalTableAmbiguity size U G rounded (R : ℝ)⁻¹ w}
    MeasurableSet bad ∧
      mu bad ≤ ENNReal.ofReal (2 * (∑ p, (size p : ℝ)) * (R : ℝ)⁻¹) ∧
      ∀ w ∉ bad, ∀ p,
        canonicalSelector (.inr (size p)) (hk p)
          (WithLp.toLp 1 (q p (U w)).val) (WithLp.toLp 1 (G p w)) =
        canonicalSelector (.inr (size p)) (hk p)
          (WithLp.toLp 1 (rounded p (U w))) (WithLp.toLp 1 (G p w)) := by
  dsimp only
  let rounded := fun p x => (simplexRound (p0 p) R (q p x)).val
  have hm : ∀ p, Measurable (rounded p) := by
    intro p
    fun_prop
  have hpos : ∀ p x j, 0 ≤ rounded p x j :=
    fun p x => (simplexRound (p0 p) R (q p x)).property.1
  have hsum : ∀ p x, ∑ j, rounded p x j = 1 :=
    fun p x => (simplexRound (p0 p) R (q p x)).property.2
  have ha : 0 ≤ (R : ℝ)⁻¹ := by positivity
  refine ⟨measurableSet_categoricalTableAmbiguity size U G rounded hU hG hm _,
    categoricalTableAmbiguity_probability_le mu size U G rounded hU hG hind hlaw
      hm hpos hsum _ ha, ?_⟩
  intro w hgood p
  apply categoricalTable_noAmbiguity_selector_agreement size U G rounded hpos hsum
    _ ha hk w hgood p (q p (U w)).val (q p (U w)).property.1 (q p (U w)).property.2
  intro i
  rw [abs_sub_comm]
  exact (simplexRound_coordinate_error (p0 p) hR (q p (U w)) i).le

end Papers.TbsNeuralCausalPi

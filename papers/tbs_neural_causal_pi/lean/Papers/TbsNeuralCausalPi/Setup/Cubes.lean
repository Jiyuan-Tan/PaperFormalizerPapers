module
public import Papers.TbsNeuralCausalPi.Setup.Notation
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection.Definitions
public import Causalean.Mathlib.Topology.SpaceFillingCurve.CurveCells
/-! # Closed coordinate boxes and dyadic parameter intervals -/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
open MeasureTheory
noncomputable section
/-- In [a specified dimension](hyp:d), an [axis-aligned closed box](goal) is described by lower and upper coordinate bounds, with each lower bound at most its corresponding upper bound. -/
structure Box (d : ℕ) where -- @realizes \mathcal{C}(axis-aligned closed coordinate box represented by ordered corners)
  lower : Fin d → ℝ
  upper : Fin d → ℝ
  ordered : ∀ j, lower j ≤ upper j
/-- The [set of points in a closed box](goal), for [a given box](hyp:b), consists of the points whose coordinates lie between the corresponding lower and upper bounds, including both endpoints. -/
def Box.carrier {d : ℕ} (b : Box d) : Set (Fin d → ℝ) :=
  {x | ∀ j, x j ∈ Set.Icc (b.lower j) (b.upper j)}
/-- The [Euclidean diameter](goal) of [a closed coordinate box](hyp:b) is the square root of the sum of its squared side lengths. -/
def boxDiam {d : ℕ} (b : Box d) : ℝ := Real.sqrt (∑ j, (b.upper j-b.lower j)^2)
/-- For [a collection of coordinate boxes](hyp:boxes), with [positive dimension](hyp:_hd), [at least one box](hyp:_hm), and [strictly positive side lengths in every box](hyp:_hpos), the [edge ratio](goal) is the largest absolute side length in the collection divided by the smallest. -/
def edgeRatio {d m : ℕ} (boxes : Fin m → Box d) -- @realizes R(largest edge length divided by smallest over a nonempty positive-edge collection)
    (_hd : 0 < d) (_hm : 0 < m) (_hpos : ∀ k j, (boxes k).lower j < (boxes k).upper j) : ℝ :=
  sSup (Set.range (fun p : Fin m × Fin d => |(boxes p.1).upper p.2 - (boxes p.1).lower p.2|)) /
  sInf (Set.range (fun p : Fin m × Fin d => |(boxes p.1).upper p.2 - (boxes p.1).lower p.2|))

/-- For [a specified dimension](hyp:d), the [pair of box metrics](goal) consists of the Euclidean box diameter and the ratio of the largest to the smallest side length across a nonempty collection with positive dimension and positive side lengths. -/
-- @node: def:prop-holder-curve-cube-metrics
def cubeMetrics (d : ℕ) :
    (Box d → ℝ) × (∀ (m : ℕ) (boxes : Fin m → Box d),
      0 < d → 0 < m → (∀ k j, (boxes k).lower j < (boxes k).upper j) → ℝ) :=
  (boxDiam, fun _ boxes hd hm hpos => edgeRatio boxes hd hm hpos)

/-- For [a spatial dimension](hyp:d) and [a refinement level](hyp:n), a [cell word](goal) is a sequence of that many child indices, each chosen from the two-to-the-dimension possible children. -/
abbrev CellWord (d n : ℕ) := Fin n → Fin (2 ^ d)
/-- For [a cell’s refinement word](hyp:w) and [a child index](hyp:j), the [child’s refinement word](goal) appends that index to the end of the parent word. -/
def childWord {d n : ℕ} (w : CellWord d n) (j : Fin (2 ^ d)) : CellWord d (n+1) :=
  Fin.lastCases j w
-- @node: def:hilbert-partitions
/-- For [a spatial dimension](hyp:d) and [cells indexed by level and refinement word](hyp:cells), the [nested box-partition property](goal) requires that [the level-zero cell is the closed unit cube](step:1), [each cell is the union of its children](step:2), [each cell is a closed coordinate box](step:3), and [distinct cells at the same level have disjoint interiors](step:4). -/
structure HasPropertyStar (d : ℕ) (cells : ∀ n, CellWord d n → Set (Fin d → ℝ)) : Prop where -- @realizes \mathcal{C}_n(closed coordinate cells indexed by refinement words with a union-of-children identity)
  zero : ∀ w, cells 0 w = {x | ∀ j, x j ∈ Set.Icc (0:ℝ) 1}
  refinement : ∀ n w, cells n w = ⋃ j, cells (n+1) (childWord w j)
  coordinateCuts : ∀ n w, ∃ b : Box d, cells n w = b.carrier
  interiorsDisjoint : ∀ n (w w' : CellWord d n), cells n w ≠ cells n w' →
    Disjoint (interior (cells n w)) (interior (cells n w')) -- @realizes \mathcal{C}_n(distinct closed coordinate cells have disjoint ambient interiors, including degenerate cells)

-- @node: def:prop-holder-curve-cube-construction
/-- For [a dimension](hyp:d) and [a refinement level](hyp:n), the [dyadic cube collection](goal) contains all closed coordinate cubes with endpoints at consecutive multiples of two to the negative level inside the unit cube. -/
def dyadicCubeCollection (d n : ℕ) : Set (Set (Fin d → ℝ)) :=
  Set.range (fun a : Fin d → Fin (2^n) =>
    {x | ∀ j, x j ∈ Set.Icc ((a j : ℝ)/(2^n : ℝ)) (((a j : ℝ)+1)/(2^n : ℝ))})
/-- In [a specified dimension](hyp:d), the [cube Lebesgue measure](goal) is ordinary coordinate-space volume restricted to the closed unit cube. -/
def cubeLebesgue (d : ℕ) : Measure (Fin d → ℝ) :=
  volume.restrict {x | ∀ j, x j ∈ Set.Icc (0:ℝ) 1}
-- @node: def:prop-holder-curve-interval-construction
/-- The [dyadic time-cell function](goal) assigns to a dimension, a refinement level, and a traversal rank the closed interval from that rank divided by two to the product of dimension and level to the next rank divided by the same denominator. -/
abbrev dyadicTimeCell := Causalean.Mathlib.Topology.SpaceFillingCurve.dyadicTimeCell -- @realizes \mathcal{I}_n(closed uniform dyadic time cells ordered by traversal rank)
-- @node: def:prop-holder-curve-lebesgue-measure
/-- The [curve parameter measure](goal) is Lebesgue measure restricted to the closed unit interval. -/
abbrev curveLebesgue : Measure ℝ :=
  Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection.uniformMeasure
end
end Papers.TbsNeuralCausalPi

module
public import Papers.TbsNeuralCausalPi.Setup.CitedResults
public import Papers.TbsNeuralCausalPi.Helpers.EuclideanModulus
public import Mathlib.Topology.MetricSpace.Lipschitz
/-! # Lipschitz chart coordinates realized by canonical structural maps

A single continuous node with one private block realizes a scalar Lipschitz
function. This derives the chart specialization from the structural gate,
without assuming the general continuous-function approximation proposition.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped NNReal
noncomputable section
attribute [local instance] Classical.propDecidable

-- @node: scalarGateDAG
/-- The [directed acyclic graph for the scalar gate](goal) has one node and no
edges. -/
def scalarGateDAG : Causalean.Graph.DAG (Fin 1) :=
  ⟨fun _ _ => False, inferInstance, fun _ h => by
    cases h with
    | single h => exact h
    | tail _ h => exact h⟩

-- @node: scalarGateComponents
/-- For [the sole block index](hyp:_), the [scalar gate's component](goal) is
the set containing its only node. -/
def scalarGateComponents (_ : Fin 1) : Set (Fin 1) := Set.univ

-- @node: scalarGateComponent
/-- [The singleton node set is a maximal clique, and hence a confounded
component, in the undirected graph with no edges](goal). -/
lemma scalarGateComponent : IsC2Component (⊥ : SimpleGraph (Fin 1)) Set.univ := by
  constructor
  refine ⟨?_, fun _ _ _ => Set.subset_univ _⟩
  rw [SimpleGraph.isClique_bot_iff]
  intro x _ y _
  exact Subsingleton.elim _ _

-- @node: scalarGateInputCard
/-- With [a private noise block of dimension d](hyp:d), [the scalar gate's
node](hyp:i) has [exactly d scalar input coordinates, counting both parent
values and incident noise blocks](goal). -/
lemma scalarGateInputCard (d : ℕ) (i : Fin 1) :
    Fintype.card (Sum
      (Σ p : {p // p ∈ scalarGateDAG.parents i}, Fin (valueDim (Sum.inl 1)))
      (Σ j : {j // j ∈ canonicalIncidence scalarGateComponents i}, Fin d)) = d := by
  rw [Fintype.card_sum, Fintype.card_sigma, Fintype.card_sigma]
  simp [scalarGateDAG, Causalean.Graph.DAG.parents, canonicalIncidence,
    scalarGateComponents]

-- @node: scalarGateCoordinates
/-- For [noise dimension d](hyp:d) and [the scalar gate's node](hyp:i), the
[coordinate vector of its structural input](goal) rewrites [the input containing
parent values and incident noise coordinates](hyp:x) as a d-dimensional real
vector with the sum norm, using the canonical enumeration of input coordinates. -/
def scalarGateCoordinates (d : ℕ) (i : Fin 1)
    (x : StructuralInput (fun _ : Fin 1 => Sum.inl 1) (fun _ : Fin 1 => d)
      scalarGateDAG (canonicalIncidence scalarGateComponents) i) : L1Vec d :=
  WithLp.toLp 1 (fun k => x.ofLp ((Fintype.equivFin _).symm
    (Fin.cast (scalarGateInputCard d i).symm k)))

-- @node: scalarGateCoordinates_measurable
/-- For [noise dimension d](hyp:d) and [the scalar gate's node](hyp:i),
[the conversion from structural inputs to d-dimensional coordinate vectors is
measurable](goal). -/
@[fun_prop] lemma scalarGateCoordinates_measurable (d : ℕ) (i : Fin 1) :
    Measurable (scalarGateCoordinates d i) := by
  unfold scalarGateCoordinates
  fun_prop

-- @node: scalarGateSCM
/-- Given [noise dimension d](hyp:d), [a real-valued function g on
d-dimensional vectors](hyp:g), and [measurability of g](hyp:hg), the
[canonical scalar structural causal model](goal) has one continuous node,
one private d-dimensional noise block concentrated at zero, and a structural
equation that applies g to the block's coordinate vector. -/
def scalarGateSCM (d : ℕ) (g : L1Vec d → ℝ) (hg : Measurable g) :
    CanonicalSCM (fun _ : Fin 1 => Sum.inl 1) (fun _ : Fin 1 => d)
      scalarGateDAG (⊥ : SimpleGraph (Fin 1)) scalarGateComponents where
  categoricalPositive := by intros; contradiction
  component := fun _ => scalarGateComponent
  exhaustive := fun s hs => ⟨0, by
    apply Set.Subset.antisymm
    · exact hs.maximalClique.2 scalarGateComponent.maximalClique.1 (Set.subset_univ s)
    · exact Set.subset_univ s⟩
  distinct := fun _ _ _ => Subsingleton.elim _ _
  f := fun i x => WithLp.toLp 1 (fun _ => g (scalarGateCoordinates d i x))
  structuralMeasurable := by
    intro i
    fun_prop
  blockLaw := fun _ => ⟨Measure.dirac 0, inferInstance⟩
  simplex := by intros; contradiction

-- @node: scalarGateSCM_inputSize
/-- For [noise dimension d](hyp:d) and [a scalar function g](hyp:g) that
[is measurable](hyp:hg), [the unique node of the associated scalar structural
causal model has input dimension d](goal). -/
lemma scalarGateSCM_inputSize (d : ℕ) (g : L1Vec d → ℝ) (hg : Measurable g) :
    structuralInputSize (scalarGateSCM d g hg).toEuclideanSCM 0 = d :=
  scalarGateInputCard d 0

-- @node: scalarGateSCM_coordinate
/-- For [noise dimension d](hyp:d), [a scalar function g](hyp:g) that
[is measurable](hyp:hg), and [a d-dimensional vector x](hyp:x),
[encoding x as a structural input and evaluating the scalar model's unique
node gives the one-dimensional vector whose entry is g evaluated at x](goal). -/
lemma scalarGateSCM_coordinate (d : ℕ) (g : L1Vec d → ℝ) (hg : Measurable g)
    (x : L1Vec d) :
    (scalarGateSCM d g hg).f 0
      (structuralFiniteCoordinates (scalarGateSCM d g hg).toEuclideanSCM 0
        (WithLp.toLp 1 (fun k => x.ofLp (Fin.cast (scalarGateSCM_inputSize d g hg) k)))) =
      WithLp.toLp 1 (fun _ => g x) := by
  change WithLp.toLp 1 (fun _ => g _) = _
  congr 1
  funext j
  congr 1
  apply PiLp.ext
  intro k
  simp only [scalarGateCoordinates, structuralFiniteCoordinates, WithLp.ofLp_toLp]
  change x.ofLp (Fin.cast (scalarGateInputCard d 0)
    ((Fintype.equivFin _ ) ((Fintype.equivFin _).symm
      (Fin.cast (scalarGateInputCard d 0).symm k)))) = x.ofLp k
  rw [Equiv.apply_symm_apply]
  rfl

/-- If [two scalar functions agree on the closed unit cube](hyp:h),
[their Euclidean moduli of continuity are equal at every radius r](goal). -/
-- @node: euclidModulus_congr_on_cube
lemma euclidModulus_congr_on_cube {d : ℕ} {f g : L1Vec d → ℝ}
    (h : Set.EqOn f g (unitCube d)) (r : ℝ) :
    euclidModulus f r = euclidModulus g r := by
  unfold euclidModulus
  congr 1
  ext a
  constructor
  · rintro ⟨x, hx, y, hy, hxy, ha⟩
    exact ⟨x, hx, y, hy, hxy, by rw [← h hx, ← h hy]; exact ha⟩
  · rintro ⟨x, hx, y, hy, hxy, ha⟩
    exact ⟨x, hx, y, hy, hxy, by rw [h hx, h hy]; exact ha⟩

/-- Assuming [the structural-map neural approximation bound](hyp:hgate),
[every positive dimension d admits positive constants a and c such that any
scalar function Lipschitz on the closed unit cube can, at every depth at least
one, be approximated there by a ReLU network of width at most 2d + 10, with
absolute error at most a times its Euclidean modulus of continuity at radius
c times depth to the power −2/d](goal).

Only a Lipschitz function is extended, and its cube modulus is unchanged. -/
-- @node: yarotskyStructural_scalar_lipschitz_modulus
lemma yarotskyStructural_scalar_lipschitz_modulus (hgate : YarotskyStructuralApprox) :
    ∀ d : ℕ, 0 < d → ∃ a c : ℝ, 0 < a ∧ 0 < c ∧
      ∀ (f : L1Vec d → ℝ) (L : ℝ≥0), LipschitzOnWith L f (unitCube d) →
        ∀ depth : ℕ, 1 ≤ depth → ∃ q : ReLUNet d 1 (2*d+10) depth,
          ∀ x ∈ unitCube d, |f x - (q.eval x).ofLp 0| ≤
            a * euclidModulus f (c * (depth : ℝ) ^ (-(2 : ℝ) / d)) := by
  intro d hd
  obtain ⟨a, c, ha, hc, happ⟩ := hgate d hd
  refine ⟨a, c, ha, hc, ?_⟩
  intro f L hf depth hdepth
  obtain ⟨g, hg, heq⟩ := hf.extend_real
  let M := scalarGateSCM d g hg.continuous.measurable
  have hcoord := scalarGateSCM_coordinate d g hg.continuous.measurable
  have hLip : LipschitzOnWith L
      (fun x : L1Vec d => M.f 0
        (structuralFiniteCoordinates M.toEuclideanSCM 0
          (WithLp.toLp 1 (fun k => x.ofLp (Fin.cast
            (scalarGateSCM_inputSize d g hg.continuous.measurable) k)))))
      (unitCube d) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [hcoord x, hcoord y]
    simpa only [PiLp.dist_eq_of_L1, WithLp.ofLp_toLp, outputDim, Fin.sum_univ_one] using
      hg.dist_le_mul x y
  obtain ⟨q, hq⟩ := happ 1 1 (fun _ => Sum.inl 1) (fun _ => d)
    scalarGateDAG ⊥ scalarGateComponents M 0
    (scalarGateSCM_inputSize d g hg.continuous.measurable) L hLip
    ⟨0, by change 0 < 1; decide⟩ depth hdepth
  have hq' : ∀ x ∈ unitCube d, |g x - (q.eval x).ofLp 0| ≤
      a * euclidModulus g (c * (depth : ℝ) ^ (-(2 : ℝ) / d)) := by
    simpa only [M, scalarGateSCM_coordinate, WithLp.ofLp_toLp] using hq
  refine ⟨q, ?_⟩
  intro x hx
  rw [heq hx, euclidModulus_congr_on_cube heq]
  exact hq' x hx

/-- Assuming [the structural-map neural approximation bound](hyp:hgate),
[every positive dimension d admits positive constants a and c, uniform over
Lipschitz homeomorphic charts from the closed unit cube onto compact sets and
over their coordinates, such that each chart coordinate has a ReLU
approximation of width at most 12d at every depth at least one, with error at
most a times its Euclidean modulus of continuity at radius c times depth to
the power −2/d](goal). -/
-- @node: yarotskyCoordinate_of_structural
lemma yarotskyCoordinate_of_structural (hgate : YarotskyStructuralApprox) :
    YarotskyCoordinateApprox := by
  intro d hd
  obtain ⟨a, c, ha, hc, happ⟩ := yarotskyStructural_scalar_lipschitz_modulus hgate d hd
  refine ⟨a, c, ha, hc, ?_⟩
  intro D S hS f L hf j depth hdepth
  let F : L1Vec d → ℝ := fun x => if hx : x ∈ unitCube d then
    (f ⟨x, hx⟩).val.ofLp j else 0
  have hF (x : unitCube d) : F x.val = (f x).val.ofLp j := by
    simp only [F, dif_pos x.property]
  have hLip : LipschitzOnWith L F (unitCube d) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [hF ⟨x, hx⟩, hF ⟨y, hy⟩]
    exact (PiLp.dist_apply_le (f ⟨x, hx⟩).val (f ⟨y, hy⟩).val j).trans
      (hf.dist_le_mul ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨q, hq⟩ := happ F L hLip depth hdepth
  have hwidth : 2*d+10 ≤ 12*d := by omega
  exact ⟨{ q with widths := fun l hl => (q.widths l hl).trans hwidth }, hq⟩

end
end Papers.TbsNeuralCausalPi

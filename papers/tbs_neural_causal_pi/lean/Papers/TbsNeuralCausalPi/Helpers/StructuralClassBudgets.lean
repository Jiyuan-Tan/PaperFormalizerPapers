module
public import Papers.TbsNeuralCausalPi.Helpers.StructuralBoxBudgets
public import Papers.TbsNeuralCausalPi.Setup.Optimization
/-! # Structural networks in the optimization coordinates

Finite coordinate reindexing preserves the one-norm, clipping fixes bounded
outputs, and the interpolation budgets produce members of the actual
structural network class.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open scoped NNReal
noncomputable section
variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
  {C : Fin b → Set (Fin n)}

-- @node: structuralCoordinatesEquiv
/-- For [a number of nodes](hyp:n), [a number of latent blocks](hyp:b),
[node types](hyp:kind), [latent dimensions](hyp:dims), [a causal directed
acyclic graph](hyp:dag), [an undirected graph](hyp:G), [latent incidence
sets](hyp:C), [a canonical causal model with this structure](hyp:M), and [a node](hyp:i), the
[structural coordinate isometry](goal) reindexes the finite input vector as
parent and latent coordinates while preserving the one-norm. -/
def structuralCoordinatesEquiv (M : CanonicalSCM kind dims dag G C) (i : Fin n) :
    L1Vec (structuralInputSize M.toEuclideanSCM i) ≃ₗᵢ[ℝ] Input kind dims dag C i :=
  LinearIsometryEquiv.piLpCongrLeft 1 ℝ ℝ (Fintype.equivFin _).symm

-- @node: structuralCoordinatesEquiv_apply
/-- For [a canonical causal model](hyp:M), [a node](hyp:i), and [an input
vector](hyp:x), [the structural coordinate isometry agrees with the finite
coordinate reindexing](goal). -/
lemma structuralCoordinatesEquiv_apply (M : CanonicalSCM kind dims dag G C)
    (i : Fin n) (x : L1Vec (structuralInputSize M.toEuclideanSCM i)) :
    structuralCoordinatesEquiv M i x = structuralFiniteCoordinates M.toEuclideanSCM i x := rfl

-- @node: structuralCoordinatesEquiv_mem_inputCube
/-- For [a canonical causal model](hyp:M), [a node](hyp:i), [a cube
radius](hyp:K), and [an input vector](hyp:x), [the reindexed vector belongs
to the structural input cube exactly when the original vector belongs to
the finite coordinate cube of that radius](goal). -/
lemma structuralCoordinatesEquiv_mem_inputCube (M : CanonicalSCM kind dims dag G C)
    (i : Fin n) (K : ℝ) (x : L1Vec (structuralInputSize M.toEuclideanSCM i)) :
    structuralCoordinatesEquiv M i x ∈ inputCube K i ↔
      x ∈ boundedCube (structuralInputSize M.toEuclideanSCM i) K := by
  constructor
  · intro hx j
    obtain ⟨k, rfl⟩ := (Fintype.equivFin
      (Sum (Σ p : {p // p ∈ M.toEuclideanSCM.dag.parents i}, Fin (valueDim (kind p)))
        (Σ j : {j // j ∈ M.toEuclideanSCM.incidence i}, Fin (dims j)))).surjective j
    exact hx k
  · intro hx j
    exact hx (Fintype.equivFin _ j)

-- @node: structural_network_in_classN
/-- For [a canonical causal model](hyp:M), [a clipping radius and Lipschitz
budget](hyp:K,L), [a width and depth factor](hyp:W,c), [a node](hyp:i), and
[a ReLU network with that width and the prescribed logarithmic depth](hyp:q),
if [its evaluation has the required Lipschitz bound](hyp:hLip), then
[reindexing its inputs and clipping its outputs gives a member of the
structural network class with zero slack](goal). -/
lemma structural_network_in_classN (M : CanonicalSCM kind dims dag G C)
    (K L : ℝ≥0) (W c : ℕ) (i : Fin n)
    (q : ReLUNet (structuralInputSize M.toEuclideanSCM i) (outputDim (kind i)) W
      (c * ⌈1 + Real.log (maxInDim M.toEuclideanSCM)⌉₊))
    (hLip : LipschitzWith L q.eval) :
    (fun x => truncK K (q.eval ((structuralCoordinatesEquiv M i).symm x))) ∈
      structuralClassN M K L (fun _ => W) c 0 i := by
  refine ⟨q, hLip, ?_⟩
  intro x
  simp only [← structuralCoordinatesEquiv_apply, LinearIsometryEquiv.symm_apply_apply]

-- @node: structural_truncK_eq_self
/-- For [a clipping radius](hyp:K), if [a vector lies in the coordinate cube
of that radius](hyp:hx), then [clipping leaves the vector unchanged](goal). -/
lemma structural_truncK_eq_self {d : ℕ} (K : ℝ) {x : L1Vec d}
    (hx : x ∈ boundedCube d K) : truncK K x = x :=
  coordinateClamp_fixes (-K) K x (fun j => abs_le.mp (hx j))

-- @node: structural_truncK_eq_self_of_norm_le
/-- For [a clipping radius](hyp:K), if [a vector's one-norm is at most that
radius](hyp:hx), then [clipping leaves the vector unchanged](goal). -/
lemma structural_truncK_eq_self_of_norm_le {d : ℕ} (K : ℝ) {x : L1Vec d}
    (hx : ‖x‖ ≤ K) : truncK K x = x := by
  apply structural_truncK_eq_self
  intro j
  exact (PiLp.norm_apply_le x j).trans hx

-- @node: structural_simplex_mem_boundedCube
/-- If [a vector is a probability vector](hyp:hx) and [the cube radius is
at least one](hyp:hK), then [the vector lies in that coordinate cube](goal). -/
lemma structural_simplex_mem_boundedCube {d : ℕ} {x : L1Vec d}
    (hx : x.ofLp ∈ probabilitySimplex d) {K : ℝ} (hK : 1 ≤ K) :
    x ∈ boundedCube d K := by
  intro j
  rw [abs_of_nonneg (hx.1 j)]
  exact ((Finset.single_le_sum (fun l _ => hx.1 l) (Finset.mem_univ j)).trans_eq hx.2).trans hK

/-- For [a canonical causal model](hyp:M), [a node](hyp:i), [a cube
radius](hyp:K), and [two structural functions](hyp:f,g), [their extended
uniform coordinate error on the structural cube equals the error of their
reindexed versions on the finite coordinate cube](goal). -/
-- @node: structural_supDistOn_coordinates
lemma structural_supDistOn_coordinates (M : CanonicalSCM kind dims dag G C)
    (i : Fin n) (K : ℝ) (f g : Input kind dims dag C i → L1Vec (outputDim (kind i))) :
    supDistOn (inputCube K i) f g =
      supDistOn (boundedCube (structuralInputSize M.toEuclideanSCM i) K)
        (f ∘ structuralCoordinatesEquiv M i) (g ∘ structuralCoordinatesEquiv M i) := by
  unfold supDistOn
  apply le_antisymm
  · apply iSup_le
    intro x
    let y := (structuralCoordinatesEquiv M i).symm x.val
    have he : structuralCoordinatesEquiv M i y = x.val :=
      (structuralCoordinatesEquiv M i).apply_symm_apply x.val
    have hy : y ∈ boundedCube (structuralInputSize M.toEuclideanSCM i) K :=
      (structuralCoordinatesEquiv_mem_inputCube M i K y).mp (he.symm ▸ x.property)
    calc
      _ = ENNReal.ofReal ‖((f ∘ structuralCoordinatesEquiv M i) y -
          (g ∘ structuralCoordinatesEquiv M i) y).ofLp‖ := by
        simp only [Function.comp_apply, he]
      _ ≤ _ := le_iSup_of_le ⟨y, hy⟩ le_rfl
  · apply iSup_le
    intro x
    exact le_iSup_of_le
      ⟨structuralCoordinatesEquiv M i x.val,
        (structuralCoordinatesEquiv_mem_inputCube M i K x.val).mpr x.property⟩ le_rfl

/-- For [a canonical causal model](hyp:M) and [a nonnegative cube
radius](hyp:K), suppose [the radius is positive](hyp:hK), [the maximum input
dimension is positive](hyp:hD), and [nodewise target sets](hyp:target) are
[convex](hyp:hconv) and [contained in the output cubes](hyp:hbox). Then
[there are positive common depth and width thresholds and an error constant
such that every family with a common Lipschitz bound mapping the input cubes
into these targets admits structural network approximations at every larger
width and depth factor; the approximations retain the Lipschitz bound and
targets globally, and their summed uniform error is at most the error
constant times the Lipschitz bound times width raised to minus the reciprocal
of the maximum input dimension](goal). -/
-- @node: structural_classN_convex_budgets
lemma structural_classN_convex_budgets (M : CanonicalSCM kind dims dag G C)
    (K : ℝ≥0) (hK : 0 < K) (hD : 0 < maxInDim M.toEuclideanSCM)
    (target : ∀ i, Set (L1Vec (outputDim (kind i))))
    (hconv : ∀ i, Convex ℝ (target i))
    (hbox : ∀ i, target i ⊆ boundedCube (outputDim (kind i)) K) :
    ∃ c0 B : ℕ, 0 < c0 ∧ 0 < B ∧ ∃ A : ℝ, 0 < A ∧
      ∀ c : ℕ, c0 ≤ c → ∀ W : ℕ, B ≤ W →
      ∀ (L : ℝ≥0) (f : ∀ i, Input kind dims dag C i → L1Vec (outputDim (kind i))),
        (∀ i, LipschitzOnWith L (f i) (inputCube K i)) →
        (∀ i, Set.MapsTo (f i) (inputCube K i) (target i)) →
        ∃ fhat : ∀ i, Input kind dims dag C i → L1Vec (outputDim (kind i)),
          (∀ i, fhat i ∈ structuralClassN M K L (fun _ => W) c 0 i) ∧
          (∀ i, LipschitzWith L (fhat i)) ∧
          (∀ i x, fhat i x ∈ target i) ∧
          (∑ i, supDistOn (inputCube K i) (f i) (fhat i)) ≤
            ENNReal.ofReal (A * L * (W : ℝ)^(-(1:ℝ)/maxInDim M.toEuclideanSCM)) := by
  classical
  obtain ⟨c0, B, hc0, hB, A, hA, happ⟩ := structural_networks_boundedCube_budgets
    (structuralInputSize M.toEuclideanSCM) (fun i => outputDim (kind i))
    (maxInDim M.toEuclideanSCM) hD
    (fun i => Finset.le_sup (f := structuralInputSize M.toEuclideanSCM) (Finset.mem_univ i))
    target hconv K hK
  refine ⟨c0, B, hc0, hB, A, hA, ?_⟩
  intro c hc W hW L f hf ht
  have hf' (i : Fin n) : LipschitzOnWith L
      (f i ∘ structuralCoordinatesEquiv M i)
      (boundedCube (structuralInputSize M.toEuclideanSCM i) K) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    calc
      _ ≤ L * dist (structuralCoordinatesEquiv M i x) (structuralCoordinatesEquiv M i y) :=
        (hf i).dist_le_mul _ ((structuralCoordinatesEquiv_mem_inputCube M i K x).mpr hx)
          _ ((structuralCoordinatesEquiv_mem_inputCube M i K y).mpr hy)
      _ = _ := by rw [(structuralCoordinatesEquiv M i).dist_map]
  obtain ⟨q, hLip, htarget, herr⟩ := happ c hc W hW L
    (fun i => f i ∘ structuralCoordinatesEquiv M i) hf'
    (fun i x hx => ht i ((structuralCoordinatesEquiv_mem_inputCube M i K x).mpr hx))
  let fhat := fun i => (q i).eval ∘ (structuralCoordinatesEquiv M i).symm
  have hfix (i : Fin n) (x : L1Vec (structuralInputSize M.toEuclideanSCM i)) :
      truncK K ((q i).eval x) = (q i).eval x :=
    structural_truncK_eq_self K (hbox i (htarget i x))
  refine ⟨fhat, ?_, ?_, ?_, ?_⟩
  · intro i
    have heq : fhat i = fun x =>
        truncK K ((q i).eval ((structuralCoordinatesEquiv M i).symm x)) := by
      funext x
      exact (hfix i _).symm
    rw [heq]
    exact structural_network_in_classN M K L W c i (q i) (hLip i)
  · intro i
    simpa only [mul_one] using (hLip i).comp (structuralCoordinatesEquiv M i).symm.lipschitz
  · intro i x
    exact htarget i _
  · simpa only [structural_supDistOn_coordinates M, fhat, Function.comp_def,
      LinearIsometryEquiv.symm_apply_apply] using herr

/-- For [a canonical causal model](hyp:M) and [a nonnegative cube
radius](hyp:K), assume [the radius is positive](hyp:hK), [the maximum input
dimension is positive](hyp:hD), and [the radius is at least one whenever a
categorical node is present](hyp:hcatK). Then [positive common depth and
width thresholds and an error constant exist so that every family with a
common Lipschitz bound, continuous output norms bounded by the radius, and
categorical probability outputs on the input cubes has structural network
approximations at all larger budgets, retaining these bounds globally and
having summed uniform error at most the constant times the Lipschitz bound
times width raised to minus the reciprocal of the maximum input dimension;
categorical outputs have positive total mass and normalization leaves them
unchanged](goal). -/
-- @node: structural_classN_mixed_budgets
lemma structural_classN_mixed_budgets (M : CanonicalSCM kind dims dag G C)
    (K : ℝ≥0) (hK : 0 < K) (hD : 0 < maxInDim M.toEuclideanSCM)
    (hcatK : ∀ i, (kind i).isRight = true → (1 : ℝ) ≤ K) :
    ∃ c0 B : ℕ, 0 < c0 ∧ 0 < B ∧ ∃ A : ℝ, 0 < A ∧
      ∀ c : ℕ, c0 ≤ c → ∀ W : ℕ, B ≤ W →
      ∀ (L : ℝ≥0) (f : ∀ i, Input kind dims dag C i → L1Vec (outputDim (kind i))),
        (∀ i, LipschitzOnWith L (f i) (inputCube K i)) →
        (∀ i, (kind i).isLeft = true → ∀ x ∈ inputCube K i, ‖f i x‖ ≤ K) →
        (∀ i, (kind i).isRight = true → ∀ x ∈ inputCube K i,
          (f i x).ofLp ∈ probabilitySimplex (outputDim (kind i))) →
        ∃ fhat : ∀ i, Input kind dims dag C i → L1Vec (outputDim (kind i)),
          (∀ i, fhat i ∈ structuralClassN M K L (fun _ => W) c 0 i) ∧
          (∀ i, LipschitzWith L (fhat i)) ∧
          (∀ i, (kind i).isLeft = true → ∀ x, ‖fhat i x‖ ≤ K) ∧
          (∀ i, (kind i).isRight = true → ∀ x,
            (fhat i x).ofLp ∈ probabilitySimplex (outputDim (kind i))) ∧
          (∀ i, (kind i).isRight = true → ∀ x,
            0 < ∑ j, (fhat i x).ofLp j) ∧
          (∀ i, (kind i).isRight = true →
            (fun x => WithLp.toLp 1 (fun j => (fhat i x).ofLp j /
              ∑ l, (fhat i x).ofLp l)) = fhat i) ∧
          (∑ i, supDistOn (inputCube K i) (f i) (fhat i)) ≤
            ENNReal.ofReal (A * L * (W : ℝ)^(-(1:ℝ)/maxInDim M.toEuclideanSCM)) := by
  classical
  let target := fun i => if (kind i).isLeft then
    Metric.closedBall (0 : L1Vec (outputDim (kind i))) K
    else {p : L1Vec (outputDim (kind i)) | p.ofLp ∈ probabilitySimplex (outputDim (kind i))}
  have hconv (i) : Convex ℝ (target i) := by
    dsimp only [target]
    split
    · exact convex_closedBall _ _
    · exact (convex_stdSimplex ℝ (Fin (outputDim (kind i)))).linear_preimage
        (WithLp.linearEquiv 1 ℝ (Fin (outputDim (kind i)) → ℝ)).toLinearMap
  have hbox (i) : target i ⊆ boundedCube (outputDim (kind i)) K := by
    intro p hp
    dsimp only [target] at hp
    split at hp
    · have hn : ‖p‖ ≤ K := by simpa only [Metric.mem_closedBall, dist_zero_right] using hp
      intro j
      exact (PiLp.norm_apply_le p j).trans hn
    · apply structural_simplex_mem_boundedCube hp
      apply hcatK i
      cases h : kind i <;> simp_all
  obtain ⟨c0, B, hc0, hB, A, hA, happ⟩ :=
    structural_classN_convex_budgets M K hK hD target hconv hbox
  refine ⟨c0, B, hc0, hB, A, hA, ?_⟩
  intro c hc W hW L f hf hcont hcat
  have ht (i) : Set.MapsTo (f i) (inputCube K i) (target i) := by
    intro x hx
    dsimp only [target]
    split
    · simpa only [Metric.mem_closedBall, dist_zero_right] using hcont i ‹_› x hx
    · apply hcat i _ x hx
      cases h : kind i <;> simp_all
  obtain ⟨fhat, hclass, hLip, htarget, herr⟩ := happ c hc W hW L f hf ht
  have hs (i) (hi : (kind i).isRight = true) (x : Input kind dims dag C i) :
      (fhat i x).ofLp ∈ probabilitySimplex (outputDim (kind i)) := by
    have hleft : (kind i).isLeft = false := by cases h : kind i <;> simp_all
    simpa only [target, hleft, Bool.false_eq_true, ↓reduceIte, Set.mem_ofPred_eq]
      using htarget i x
  refine ⟨fhat, hclass, hLip, ?_, hs, ?_, ?_, herr⟩
  · intro i hi x
    simpa only [target, hi, ↓reduceIte, Metric.mem_closedBall, dist_zero_right]
      using htarget i x
  · intro i hi x
    rw [(hs i hi x).2]
    norm_num
  · intro i hi
    funext x
    exact structural_normalized_simplex_eq_self (hs i hi x)

end
end Papers.TbsNeuralCausalPi

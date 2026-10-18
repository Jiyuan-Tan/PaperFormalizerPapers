module
public import Papers.TbsNeuralCausalPi.Helpers.BorsukUlam
/-! # The classical dimension bound for an embedded cube

The odd-map theorem follows from signed-coordinate labels and the finite
antipodal chain obstruction. The cube reduction uses an embedded sphere.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi

/-- [The cube embedding dimension bound](goal) says that a continuous injection
of a closed unit cube into a real vector space requires the cube's dimension
to be no greater than the ambient dimension. -/
abbrev CubeEmbeddingDimensionBound : Sort 0 :=
  ∀ (q d : ℕ) (f : unitCube q → L1Vec d),
    Continuous f → Function.Injective f → q ≤ d

/-- If [every continuous odd map from a unit sphere of dimension d into real
d-space has a zero, for every dimension d](hyp:hzero), then [a continuous injection
of a closed unit cube into real space cannot lower dimension](goal). -/
-- @node: cube_embedding_dimension_bound_of_odd_zero
lemma cube_embedding_dimension_bound_of_odd_zero
    (hzero : ∀ d (g : Metric.sphere (0 : Fin (d + 1) → ℝ) 1 → L1Vec d),
      Continuous g → (∀ x, g (-x) = -g x) → ∃ x, g x = 0) :
    CubeEmbeddingDimensionBound := by
  intro q d f hf hinj
  by_contra hdim
  have hdq : d + 1 ≤ q := by omega
  let e := sphereCubeEmbedding hdq
  let g := fun x => f (e x) - f (e (-x))
  have hg : Continuous g := by
    fun_prop
  have hodd : ∀ x, g (-x) = -g x := by
    intro x
    simp [g, neg_sub]
  obtain ⟨x, hx⟩ := hzero d g hg hodd
  have heq : e x = e (-x) := hinj (sub_eq_zero.mp hx)
  exact sphere_ne_antipode x (sphereCubeEmbedding_injective hdq heq)

-- @node: cube_embedding_dimension_bound
/-- [A continuous injection of a closed unit cube into a real vector space
requires the cube's dimension to be no greater than the ambient dimension](goal). -/
lemma cube_embedding_dimension_bound : CubeEmbeddingDimensionBound := by
  exact cube_embedding_dimension_bound_of_odd_zero sphere_odd_exists_zero

-- @node: cube_chart_dimension_le_ambient
/-- Given [a homeomorphism from a closed unit cube onto a subset of real
d-space](hyp:chart), [the cube's dimension is at most d](goal). -/
lemma cube_chart_dimension_le_ambient
    {q d : ℕ} {S : Set (L1Vec d)}
    (chart : homeoClass (unitCube q) S) : q ≤ d :=
  cube_embedding_dimension_bound q d (fun x => (chart x).val)
    (continuous_subtype_val.comp chart.continuous)
    (Subtype.val_injective.comp chart.injective)

end Papers.TbsNeuralCausalPi

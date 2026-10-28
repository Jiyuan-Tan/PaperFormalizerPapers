module

public import Papers.OaiBoundDyadicTriangular.Helpers.MatrixHessian
public import Papers.OaiBoundDyadicTriangular.Helpers.TraceBlocks
public import Papers.OaiBoundDyadicTriangular.Helpers.TraceSpectral
public import Papers.OaiBoundDyadicTriangular.Helpers.TraceCoordinates
public import Papers.OaiBoundDyadicTriangular.Helpers.MatrixSylvester
public import Papers.OaiBoundDyadicTriangular.Helpers.TraceEmbeddings

/-! # Dimension-independent cubic trace estimate -/

public section

open Matrix

namespace Papers.OaiBoundDyadicTriangular

variable {H₀ H₁ H₂ : Type*} [Fintype H₀] [DecidableEq H₀]
  [Fintype H₁] [DecidableEq H₁] [Fintype H₂] [DecidableEq H₂]

-- @node: rowGram_mulVec_eq_zero_iff
/-- [A vector is annihilated by the Gram matrix formed by the transpose of R
times R if and only if it is annihilated by R itself](goal). -/
lemma rowGram_mulVec_eq_zero_iff {ι κ : Type*} [Fintype ι] [Fintype κ]
    (R : Matrix ι κ ℝ) (x : κ → ℝ) :
    rowGram R *ᵥ x = 0 ↔ R *ᵥ x = 0 := by
  simpa only [rowGram, conjTranspose_eq_transpose_of_trivial] using
    Matrix.conjTranspose_mul_self_mulVec_eq_zero R x

-- @node: rowPerturbation_supportedOn
/-- [The matrix given by the transpose of R times D times R annihilates every
vector in the kernel of the Gram matrix given by the transpose of R times
R](goal). -/
lemma rowPerturbation_supportedOn {ι κ : Type*} [Fintype ι] [Fintype κ]
    (R : Matrix ι κ ℝ) (D : Matrix ι ι ℝ) :
    SupportedOn (rowGram R) (rowPerturbation R D) := by
  constructor
  intro x hx
  have hRx := (rowGram_mulVec_eq_zero_iff R x).mp hx
  simp only [rowPerturbation, ← Matrix.mulVec_mulVec, hRx, Matrix.mulVec_zero]

-- @node: rowPerturbation_isSymm
/-- If [D is symmetric](hyp:hD), then [the transpose of R times D times R is
symmetric](goal). -/
lemma rowPerturbation_isSymm {ι κ : Type*} [Fintype ι] [Fintype κ]
    (R : Matrix ι κ ℝ) (D : Matrix ι ι ℝ) (hD : D.IsSymm) :
    (rowPerturbation R D).IsSymm := by
  change (R.transpose * D * R).transpose = R.transpose * D * R
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hD]
  exact (Matrix.mul_assoc _ _ _).symm

-- @node: rowPerturbation_order_bounds
/-- If [the identity minus D is positive semidefinite](hyp:hMinus) and [the
identity plus D is positive semidefinite](hyp:hPlus), then [both the difference
and the sum of the Gram matrix of R and the matrix given by the transpose of R
times D times R are positive semidefinite](goal). -/
lemma rowPerturbation_order_bounds {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] (R : Matrix ι κ ℝ) (D : Matrix ι ι ℝ)
    (hMinus : (1 - D).PosSemidef) (hPlus : (1 + D).PosSemidef) :
    (rowGram R - rowPerturbation R D).PosSemidef ∧
      (rowGram R + rowPerturbation R D).PosSemidef := by
  constructor
  · simpa only [conjTranspose_eq_transpose_of_trivial, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_one, rowGram, rowPerturbation] using
      hMinus.conjTranspose_mul_mul_same R
  · simpa only [conjTranspose_eq_transpose_of_trivial, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_one, rowGram, rowPerturbation] using
      hPlus.conjTranspose_mul_mul_same R

/-- If [M is symmetric](hyp:hM), [P is symmetric](hyp:hP), and [P squared equals
P](hyp:hIdem), then [M times P times M equals the Gram matrix of P times
M](goal). -/
-- @node: projection_commonGram_eq
lemma projection_commonGram_eq {ι : Type*} [Fintype ι]
    (M P : Matrix ι ι ℝ) (hM : M.IsSymm) (hP : P.IsSymm)
    (hIdem : P * P = P) :
    M * P * M = rowGram (P * M) := by
  simp only [rowGram, Matrix.transpose_mul, hM.eq, hP.eq]
  rw [← Matrix.mul_assoc, Matrix.mul_assoc M P P, hIdem]

/-- If [M is symmetric](hyp:hM), [P is symmetric](hyp:hP), [P squared equals
P](hyp:hIdem), and [P commutes with D](hyp:hComm), then [M times P times D times
M equals the transpose of P times M, multiplied by D and then by P times
M](goal). -/
-- @node: projection_commonPerturbation_eq
lemma projection_commonPerturbation_eq {ι : Type*} [Fintype ι]
    (M P D : Matrix ι ι ℝ) (hM : M.IsSymm) (hP : P.IsSymm)
    (hIdem : P * P = P) (hComm : P * D = D * P) :
    M * P * D * M = rowPerturbation (P * M) D := by
  have hPD : P * D * P = P * D := by
    rw [hComm, Matrix.mul_assoc, hIdem]
  simp only [rowPerturbation, Matrix.transpose_mul, hM.eq, hP.eq]
  simp only [← Matrix.mul_assoc]
  rw [Matrix.mul_assoc M P D, Matrix.mul_assoc M (P * D) P, hPD]

-- @node: projection_commonPerturbation_supported
/-- If [M is symmetric](hyp:hM), [P is symmetric](hyp:hP), [P squared equals
P](hyp:hIdem), and [P commutes with D](hyp:hComm), then [M times P times D times
M annihilates every vector in the kernel of M times P times M](goal). -/
lemma projection_commonPerturbation_supported {ι : Type*} [Fintype ι]
    (M P D : Matrix ι ι ℝ) (hM : M.IsSymm) (hP : P.IsSymm)
    (hIdem : P * P = P) (hComm : P * D = D * P) :
    SupportedOn (M * P * M) (M * P * D * M) := by
  rw [projection_commonGram_eq M P hM hP hIdem,
    projection_commonPerturbation_eq M P D hM hP hIdem hComm]
  exact rowPerturbation_supportedOn _ _

-- @node: projection_commonPerturbation_isSymm
/-- If [M is symmetric](hyp:hM), [P is symmetric](hyp:hP), [D is
symmetric](hyp:hD), and [P commutes with D](hyp:hComm), then [M times P times D
times M is symmetric](goal). -/
lemma projection_commonPerturbation_isSymm {ι : Type*} [Fintype ι]
    (M P D : Matrix ι ι ℝ) (hM : M.IsSymm) (hP : P.IsSymm)
    (hD : D.IsSymm) (hComm : P * D = D * P) :
    (M * P * D * M).IsSymm := by
  change (M * P * D * M).transpose = M * P * D * M
  simp only [Matrix.transpose_mul, hM.eq, hP.eq, hD.eq, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc D P M, ← hComm, Matrix.mul_assoc]

-- @node: commonGram_posSemidef
/-- If [M is symmetric](hyp:hM) and [P is positive semidefinite](hyp:hP), then
[M times P times M is positive semidefinite](goal). -/
lemma commonGram_posSemidef {ι : Type*} [Fintype ι]
    (M P : Matrix ι ι ℝ) (hM : M.IsSymm) (hP : P.PosSemidef) :
    (M * P * M).PosSemidef := by
  simpa only [conjTranspose_eq_transpose_of_trivial, hM.eq] using
    hP.conjTranspose_mul_mul_same M

-- @node: commonGram_le_square
/-- If [M is symmetric](hyp:hM) and [the identity minus P is positive
semidefinite](hyp:hP), then [M times P times M is bounded above by M squared
in the positive semidefinite order](goal). -/
lemma commonGram_le_square {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M P : Matrix ι ι ℝ) (hM : M.IsSymm) (hP : (1 - P).PosSemidef) :
    OrderComparison (M * P * M) (M * M) 1 := by
  have h := commonGram_posSemidef M (1 - P) hM hP
  simpa only [OrderComparison, one_smul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_one] using h

-- @node: commonPerturbation_sum
/-- If [the three matrices P₀, P₁, and P₂ sum to the identity](hyp:hSum), then
[the sum of M times each of these matrices times D times M equals M times D
times M](goal). -/
lemma commonPerturbation_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M P₀ P₁ P₂ D : Matrix ι ι ℝ) (hSum : P₀ + P₁ + P₂ = 1) :
    M * P₀ * D * M + M * P₁ * D * M + M * P₂ * D * M = M * D * M := by
  have h := congrArg (fun X => M * X * D * M) hSum
  simpa only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one] using h

/-- Suppose [M is symmetric](hyp:hM), [D is symmetric](hyp:hD), and three
matrices P are [positive semidefinite](hyp:hP), [have positive semidefinite
complements relative to the identity](hyp:hComplement), [equal their own
squares](hyp:hIdem), [commute with D](hyp:hComm), and [sum to the
identity](hyp:hSum). Then [the supported Hessian form at M squared in direction
M times D times M is at most three times the sum of the supported Hessian forms
at M times each P times M in the corresponding directions M times P times D
times M](goal).

This is equation (common-form). -/
-- @node: commonForm_comparison
lemma commonForm_comparison {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M D : Matrix ι ι ℝ) (hM : M.IsSymm) (hD : D.IsSymm)
    (P : Fin 3 → Matrix ι ι ℝ)
    (hP : ∀ v, (P v).PosSemidef) (hComplement : ∀ v, (1 - P v).PosSemidef)
    (hIdem : ∀ v, P v * P v = P v) (hComm : ∀ v, P v * D = D * P v)
    (hSum : P 0 + P 1 + P 2 = 1) :
    let hA := fun v => (commonGram_posSemidef M (P v) hM (hP v)).isHermitian
    let hSquare : (M * M).IsHermitian := by
      simpa only [Matrix.mul_one] using
        (commonGram_posSemidef M 1 hM Matrix.PosSemidef.one).isHermitian
    hessForm (M * M) hSquare (M * D * M) ≤
      3 * ∑ v : Fin 3, hessForm (M * P v * M) (hA v) (M * P v * D * M) := by
  dsimp only
  have hSquare : (M * M).PosSemidef := by
    simpa only [Matrix.mul_one] using
      commonGram_posSemidef M 1 hM Matrix.PosSemidef.one
  have hEach (v : Fin 3) :
      hessForm (M * M) hSquare.isHermitian (M * P v * D * M) ≤
        hessForm (M * P v * M)
          (commonGram_posSemidef M (P v) hM (hP v)).isHermitian
          (M * P v * D * M) := by
    have hSymm := Matrix.isHermitian_iff_isSymm.mp (hP v).isHermitian
    have hSupported := projection_commonPerturbation_supported M (P v) D
      hM hSymm (hIdem v) (hComm v)
    have hOrder := (hessForm_order (M * P v * M) (M * M)
      (M * P v * D * M) 1
      ⟨commonGram_posSemidef M (P v) hM (hP v), hSquare⟩ (by norm_num [OrderFactor])
      (commonGram_le_square M (P v) hM (hComplement v))
      ⟨projection_commonPerturbation_isSymm M (P v) D hM hSymm hD (hComm v),
        hSupported.annihilates⟩).2
    simpa only [Real.one_rpow, one_mul] using hOrder
  have hThree := hessForm_add_three_le (M * M) hSquare.isHermitian
    (M * P 0 * D * M) (M * P 1 * D * M) (M * P 2 * D * M)
  rw [commonPerturbation_sum M (P 0) (P 1) (P 2) D hSum] at hThree
  apply hThree.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  rw [Fin.sum_univ_three]
  exact add_le_add (add_le_add (hEach 0) (hEach 1)) (hEach 2)

-- @node: prop:trace
/-- If [the three vertex matrices D₀, D₁, and D₂ are symmetric](hyp:hSymmetry)
and [each lies between minus the identity and the identity in the positive
semidefinite order](hyp:hContraction), then [each vertex perturbation
annihilates the kernel of its row Gram matrix, and the absolute trace of the
alternating product D₀, W₀, D₁, W₁, D₂, W₂ is at most five thirds of the sum
of the three supported Hessian forms at those Gram matrices in those
perturbation directions](goal).

Each vertex row matrix joins its outgoing edge matrix to the transpose of its
incoming edge matrix. Its Gram matrix is its transpose times itself, and its
perturbation is its transpose times the vertex matrix times itself. -/
theorem abs_trace_le_hessForm_sum
    (W₀ : Matrix H₀ H₁ ℝ) (W₁ : Matrix H₁ H₂ ℝ) (W₂ : Matrix H₂ H₀ ℝ)
    (D₀ : Matrix H₀ H₀ ℝ) (D₁ : Matrix H₁ H₁ ℝ) (D₂ : Matrix H₂ H₂ ℝ)
    (hSymmetry : TraceSymmetry D₀ D₁ D₂) (hContraction : TraceContraction D₀ D₁ D₂) :
    let R₀ := rowStar W₀ W₂
    let R₁ := rowStar W₁ W₀
    let R₂ := rowStar W₂ W₁
    (SupportedOn (rowGram R₀) (rowPerturbation R₀ D₀) ∧
     SupportedOn (rowGram R₁) (rowPerturbation R₁ D₁) ∧
     SupportedOn (rowGram R₂) (rowPerturbation R₂ D₂)) ∧
    |(D₀ * W₀ * D₁ * W₁ * D₂ * W₂).trace| ≤ (5 / 3 : ℝ) *
      (hessForm (rowGram R₀) (rowGram_isHermitian R₀) (rowPerturbation R₀ D₀) +
       hessForm (rowGram R₁) (rowGram_isHermitian R₁) (rowPerturbation R₁ D₁) +
       hessForm (rowGram R₂) (rowGram_isHermitian R₂) (rowPerturbation R₂ D₂)) := by
  refine ⟨⟨rowPerturbation_supportedOn _ _, rowPerturbation_supportedOn _ _,
    rowPerturbation_supportedOn _ _⟩, ?_⟩
  let M := offDiagonalBlocks W₀ W₂.transpose W₀.transpose W₂ W₁ W₁.transpose
  let D := vertexDiagonal D₀ D₁ D₂
  let hM : M.IsHermitian :=
    Matrix.isHermitian_iff_isSymm.mpr (triangleBlocks_isSymm W₀ W₁ W₂)
  let E := Unitary.conjStarAlgAut ℝ _ (star hM.eigenvectorUnitary) D
  let m := hM.eigenvalues
  let Q := ∑ i, ∑ j, |m i| ^ 2 * |m j| ^ 2 / (|m i| + |m j|) * E i j ^ 2
  have hCubic : 6 * |(D₀ * W₀ * D₁ * W₁ * D₂ * W₂).trace| ≤ 5 * Q :=
    triangle_trace_le_spectral_Q W₀ W₁ W₂ D₀ D₁ D₂ hSymmetry hContraction
  have hSpectral := hessForm_square_sandwich_eq_spectral M D hM
    (vertexDiagonal_isSymm D₀ D₁ D₂ hSymmetry)
  change hessForm (M * M) (hermitian_square_posSemidef M hM).isHermitian
    (M * D * M) = (3 / 2 : ℝ) * Q at hSpectral
  -- Identify each vertex form under permutation and extension by zero,
  -- then apply the common-form comparison from the paper's order lemma.
  have hComparison :
      hessForm (M * M) (hermitian_square_posSemidef M hM).isHermitian (M * D * M) ≤ 3 *
      (hessForm (rowGram (rowStar W₀ W₂)) (rowGram_isHermitian _)
          (rowPerturbation (rowStar W₀ W₂) D₀) +
       hessForm (rowGram (rowStar W₁ W₀)) (rowGram_isHermitian _)
          (rowPerturbation (rowStar W₁ W₀) D₁) +
       hessForm (rowGram (rowStar W₂ W₁)) (rowGram_isHermitian _)
          (rowPerturbation (rowStar W₂ W₁) D₂)) := by
    have hc := commonForm_comparison M D
      (Matrix.isHermitian_iff_isSymm.mp hM)
      (vertexDiagonal_isSymm D₀ D₁ D₂ hSymmetry)
      vertexProjection vertexProjection_posSemidef vertexProjection_complement_posSemidef
      vertexProjection_idempotent (fun v => vertexProjection_commute v D₀ D₁ D₂)
      vertexProjection_sum
    simp only [Fin.sum_univ_three] at hc
    rw [hessForm_vertex0 W₀ W₁ W₂ D₀ D₁ D₂ hSymmetry,
      hessForm_vertex1 W₀ W₁ W₂ D₀ D₁ D₂ hSymmetry,
      hessForm_vertex2 W₀ W₁ W₂ D₀ D₁ D₂ hSymmetry] at hc
    exact hc
  rw [hSpectral] at hComparison
  linarith

end Papers.OaiBoundDyadicTriangular

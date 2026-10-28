module

public import Papers.OaiBoundDyadicTriangular.Basic
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Atom coordinates, weighted edge matrices, and energies

The atom scale is carried explicitly. Statements using atom constructions carry
m ≤ k, and statements using Haar diagonals carry m + 1 ≤ k.
-/

@[expose] public section

open MeasureTheory Matrix Polynomial
open scoped BigOperators

namespace Papers.OaiBoundDyadicTriangular

-- @node: rectangular_mul_pow
/-- For real rectangular matrices R and S of compatible opposite shapes and a natural
number n, [R times the n-th power of SR equals the n-th power of RS times R](goal). -/
lemma rectangular_mul_pow {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (R : Matrix ι κ ℝ) (S : Matrix κ ι ℝ) (n : ℕ) :
    R * (S * R) ^ n = (R * S) ^ n * R := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, ← Matrix.mul_assoc R,
      ← Matrix.mul_assoc, ← pow_succ]

-- @node: trace_mul_aeval_rectangular
/-- For real rectangular matrices R and S of compatible opposite shapes and a real
polynomial p, [the trace of SR times p evaluated at SR equals the trace of RS times
p evaluated at RS](goal). -/
lemma trace_mul_aeval_rectangular {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (R : Matrix ι κ ℝ) (S : Matrix κ ι ℝ)
    (p : ℝ[X]) :
    ((S * R) * aeval (S * R) p).trace = ((R * S) * aeval (R * S) p).trace := by
  have hp (n : ℕ) : ((S * R) * (S * R) ^ n).trace =
      ((R * S) * (R * S) ^ n).trace := by
    calc
      _ = (S * (R * (S * R) ^ n)).trace := by rw [Matrix.mul_assoc]
      _ = ((R * (S * R) ^ n) * S).trace := Matrix.trace_mul_comm _ _
      _ = (((R * S) ^ n * R) * S).trace := by rw [rectangular_mul_pow]
      _ = ((R * S) ^ (n + 1)).trace := by rw [Matrix.mul_assoc, ← pow_succ]
      _ = _ := by rw [pow_succ']
  induction p using Polynomial.induction_on' with
  | add p q ihp ihq => simp only [map_add, Matrix.mul_add, Matrix.trace_add, ihp, ihq]
  | monomial n r =>
    simp only [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      Matrix.mul_smul, Matrix.trace_smul, hp]

-- @node: trace_cfc_gram
/-- For a real rectangular matrix R and a real function f, if [f vanishes at zero](hyp:hf),
then [applying f spectrally to the column and row Gram matrices of R gives equal
traces](goal). -/
lemma trace_cfc_gram {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (R : Matrix ι κ ℝ) (f : ℝ → ℝ) (hf : f 0 = 0) :
    (cfc f (R.transpose * R)).trace = (cfc f (R * R.transpose)).trace := by
  classical
  have hA : (R.transpose * R).IsHermitian := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      Matrix.isHermitian_conjTranspose_mul_self R
  have hB : (R * R.transpose).IsHermitian := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      Matrix.isHermitian_mul_conjTranspose_self R
  let s : Finset ℝ := (spectrum ℝ (R.transpose * R)).toFinite.toFinset ∪
    (spectrum ℝ (R * R.transpose)).toFinite.toFinset
  let p : ℝ[X] := Lagrange.interpolate s id (fun x => f x / x)
  have hEval (x : ℝ) (hx : x ∈ s) : x * p.eval x = f x := by
    have he : p.eval x = f x / x :=
      Lagrange.eval_interpolate_at_node (fun x => f x / x) (fun _ _ _ _ h => h) hx
    rw [he]
    by_cases h : x = 0
    · simp [h, hf]
    · exact mul_div_cancel₀ (f x) h
  have hLeft : cfc f (R.transpose * R) =
      (R.transpose * R) * aeval (R.transpose * R) p := by
    calc
      _ = cfc (fun x => x * p.eval x) (R.transpose * R) := by
        apply cfc_congr
        intro x hx
        exact (hEval x (Finset.mem_union_left _ (by simpa using hx))).symm
      _ = _ := by rw [cfc_mul .., cfc_id' .., cfc_polynomial ..]
  have hRight : cfc f (R * R.transpose) =
      (R * R.transpose) * aeval (R * R.transpose) p := by
    calc
      _ = cfc (fun x => x * p.eval x) (R * R.transpose) := by
        apply cfc_congr
        intro x hx
        exact (hEval x (Finset.mem_union_right _ (by simpa using hx))).symm
      _ = _ := by rw [cfc_mul .., cfc_id' .., cfc_polynomial ..]
  rw [hLeft, hRight]
  exact trace_mul_aeval_rectangular R R.transpose p

-- @node: matrixEnergy_gram
/-- For any real rectangular matrix R, [its column and row Gram matrices have the
same three-halves trace energy](goal). -/
lemma matrixEnergy_gram {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (R : Matrix ι κ ℝ) :
    matrixEnergy (R.transpose * R) = matrixEnergy (R * R.transpose) := by
  apply trace_cfc_gram
  norm_num


/-- For [a parent scale k and an atom scale m](hyp:k,m), the [atom index set](goal)
consists of the natural numbers below two raised to the nonnegative part of k minus m.

@realizes H_v(Euclidean atom space of dimension two to the scale difference)
-/
abbrev Atom (k m : ℤ) := Fin (2 ^ (k - m).toNat)

-- @node: def:atom-spaces
/-- For [a parent scale k and an atom scale m](hyp:k,m), [a triple of interval indices](hyp:n),
[a vertex](hyp:v), and [an atom within its parent interval](hyp:i), the [global atom
index](goal) is the vertex's interval index times the number of atoms per parent,
plus the atom's index within that parent.

@realizes H_v(orthonormal coordinates indexed by scale-m atoms in a scale-k interval)
-/
def atomIndex (k m : ℤ) (n : Fin 3 → ℕ) (v : Fin 3) (i : Atom k m) : ℕ :=
  2 ^ (k - m).toNat * n v + i.val

-- @node: def:atom-weights
/-- For [a parent scale k and an atom scale m](hyp:k,m), the [normalized atom
weight](goal) is two raised to m minus k.

@realizes w_v(i)(normalized mass two to the power m minus k for every atom)
-/
noncomputable def atomWeight (k m : ℤ) : ℝ := (2 : ℝ) ^ (m - k)

/-- For [one of the three vertices](hyp:v), the [next vertex](goal) is its cyclic
successor, with the third vertex followed by the first. -/
def nextVertex (v : Fin 3) : Fin 3 := v + 1

/-- For [three real functions of two coordinates](hyp:F), [a parent scale k and an
atom scale m](hyp:k,m), [a triple of interval indices](hyp:n), [an edge's starting
vertex](hyp:v), and [atoms at that vertex and its cyclic successor](hyp:i,j), the
[atom value](goal) evaluates the corresponding function at the two atoms' left endpoints.
-/
noncomputable def atomValue (F : Fin 3 → ℝ × ℝ → ℝ) (k m : ℤ)
    (n : Fin 3 → ℕ) (v : Fin 3) (i j : Atom k m) : ℝ :=
  F v ((2 : ℝ)^m * atomIndex k m n v i,
    (2 : ℝ)^m * atomIndex k m n (nextVertex v) j)

-- @node: def:weighted-edge
/-- For [three input functions](hyp:F), [a parent scale k and an atom scale m](hyp:k,m),
[a triple of interval indices](hyp:n), and [an edge's starting vertex](hyp:v), the
[weighted edge matrix](goal) has entries equal to the sampled atom values times the
square root of the product of the two atom weights.

@realizes W_v(atom-weighted input matrix from vertex v+1 to vertex v)
-/
noncomputable def weightedEdge (F : Fin 3 → ℝ × ℝ → ℝ) (k m : ℤ)
    (n : Fin 3 → ℕ) (v : Fin 3) : Matrix (Atom k m) (Atom k m) ℝ :=
  fun i j => Real.sqrt (atomWeight k m * atomWeight k m) * atomValue F k m n v i j

/-- For [three input functions](hyp:F), [a parent scale k and an atom scale m](hyp:k,m),
[a triple of interval indices](hyp:n), and [a vertex](hyp:v), the [vertex row
matrix](goal) joins its outgoing weighted edge matrix and the transpose of its
incoming weighted edge matrix side by side. -/
noncomputable def atomRowStar (F : Fin 3 → ℝ × ℝ → ℝ) (k m : ℤ)
    (n : Fin 3 → ℕ) (v : Fin 3) : Matrix (Atom k m) (Atom k m ⊕ Atom k m) ℝ :=
  rowStar (weightedEdge F k m n v) (weightedEdge F k m n (v + 2))

/-- For [three input functions](hyp:F), [a parent scale k and an atom scale m](hyp:k,m),
[a triple of interval indices](hyp:n), and [a vertex](hyp:v), the [vertex energy](goal)
is the three-halves trace energy of the column Gram matrix of its vertex row matrix.

@realizes e_v(\mathbf I)(three-halves trace energy of the vertex Gram operator)
-/
noncomputable def vertexEnergy (F : Fin 3 → ℝ × ℝ → ℝ) (k m : ℤ)
    (n : Fin 3 → ℕ) (v : Fin 3) : ℝ := matrixEnergy (rowGram (atomRowStar F k m n v))

-- @node: def:local-energy
/-- For [three input functions](hyp:F), [a parent scale k and an atom scale m](hyp:k,m),
and [a triple of interval indices](hyp:n), the [local energy](goal) is the sum of
the energies at the three vertices.

@realizes e(\mathbf I)(sum of the three vertex energies)
-/
noncomputable def localEnergy (F : Fin 3 → ℝ × ℝ → ℝ) (k m : ℤ)
    (n : Fin 3 → ℕ) : ℝ := ∑ v : Fin 3, vertexEnergy F k m n v

-- @node: vertexEnergy_eq_row_mul_adjoint
/-- If [the atom scale m is no larger than the parent scale k](hyp:hk), then
[the vertex energy equals the three-halves trace energy of the vertex row matrix
times its transpose](goal). -/
lemma vertexEnergy_eq_row_mul_adjoint (F : Fin 3 → ℝ × ℝ → ℝ) (k m : ℤ)
    (n : Fin 3 → ℕ) (v : Fin 3) (hk : TotalScale k m) :
    vertexEnergy F k m n v =
      matrixEnergy (atomRowStar F k m n v * (atomRowStar F k m n v).transpose) := by
  exact matrixEnergy_gram (atomRowStar F k m n v)

/-- For [a parent scale k and an atom scale m](hyp:k,m), [a triple of interval
indices](hyp:n), and [a vertex](hyp:v), the [Haar diagonal matrix](goal) has the
parent interval's Haar sign at each atom's left endpoint on its diagonal, and zeros elsewhere.

@realizes D_v(diagonal matrix of parent Haar-sign values on its atoms)
-/
noncomputable def haarDiag (k m : ℤ) (n : Fin 3 → ℕ) (v : Fin 3) :
    Matrix (Atom k m) (Atom k m) ℝ :=
  Matrix.diagonal (fun i => haarSign k (n v) ((2 : ℝ)^m * atomIndex k m n v i))

-- @node: def:local-trace
/-- For [three input functions](hyp:F), [a parent scale k and an atom scale m](hyp:k,m),
and [a triple of interval indices](hyp:n), the [local trace](goal) is the trace of
the product alternating Haar diagonal matrices and weighted edge matrices around
the three vertices in cyclic order.

@realizes \tau(\mathbf I)(trace of alternating Haar diagonals and weighted edges)
-/
noncomputable def localTrace (F : Fin 3 → ℝ × ℝ → ℝ) (k m : ℤ)
    (n : Fin 3 → ℕ) : ℝ :=
  (haarDiag k m n 0 * weightedEdge F k m n 0 *
   haarDiag k m n 1 * weightedEdge F k m n 1 *
   haarDiag k m n 2 * weightedEdge F k m n 2).trace

-- @node: def:trace-integral
/-- For [three input functions](hyp:F), [a parent scale k and an atom scale m](hyp:k,m),
and [a triple of interval indices](hyp:n), the [normalized trace form](goal) is
the local trace multiplied by two raised to twice k. -/
noncomputable def traceNormalizedForm (F : Fin 3 → ℝ × ℝ → ℝ) (k m : ℤ)
    (n : Fin 3 → ℕ) : ℝ := (2 : ℝ)^(2*k) * localTrace F k m n

-- @node: def:energy-increment
/-- For [three input functions](hyp:F), [a parent scale k and an atom scale m](hyp:k,m),
and [a parent triple of interval indices](hyp:n), the [energy increment](goal) is
one quarter of the sum of the children's local energies at scale k minus one,
less the parent's local energy at scale k.

@realizes \delta(\mathbf I)(uniform four-child energy average minus parent energy)
-/
noncomputable def energyIncrement (F : Fin 3 → ℝ × ℝ → ℝ) (k m : ℤ)
    (n : Fin 3 → ℕ) : ℝ :=
  (1 / 4 : ℝ) * (∑ n' ∈ children n, localEnergy F (k - 1) m n') -
    localEnergy F k m n

-- @node: def:total-energy
/-- For [three input functions](hyp:F) and [a parent scale k and an atom scale m](hyp:k,m),
the [total energy](goal) sums the local energy over all admissible interval triples,
with each term weighted by two raised to twice k.

@realizes J_k(weighted sum over all admissible triples at scale k)
-/
noncomputable def totalEnergy (F : Fin 3 → ℝ × ℝ → ℝ) (k m : ℤ) : ℝ :=
  ∑' n : admissibleSet, (2 : ℝ)^(2*k) * localEnergy F k m n.val

end Papers.OaiBoundDyadicTriangular

module

public import Papers.OaiBoundDyadicTriangular.Helpers.AtomCompact
public import Papers.OaiBoundDyadicTriangular.Helpers.AtomIntegral

/-! # Bounds and telescoping for the weighted total energy -/

public section

open MeasureTheory
open scoped BigOperators

namespace Papers.OaiBoundDyadicTriangular

-- @node: matrixEnergy_eq_sum_eigenvalues
/-- For [a finite real square matrix](hyp:P) that [is symmetric](hyp:hP),
[its matrix energy equals the sum of its eigenvalues raised to the power three halves](goal). -/
lemma matrixEnergy_eq_sum_eigenvalues {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℝ) (hP : P.IsHermitian) :
    matrixEnergy P = ∑ i, hP.eigenvalues i ^ (3 / 2 : ℝ) := by
  rw [matrixEnergy, hP.cfc_eq, Matrix.IsHermitian.cfc,
    Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self,
    one_mul, Matrix.trace_diagonal]
  rfl

-- @node: matrixEnergy_nonneg
/-- For [a finite real square matrix](hyp:P) that [is positive semidefinite](hyp:hP),
[its matrix energy is nonnegative](goal). -/
lemma matrixEnergy_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℝ) (hP : P.PosSemidef) : 0 ≤ matrixEnergy P := by
  rw [matrixEnergy_eq_sum_eigenvalues P hP.isHermitian]
  exact Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hP.eigenvalues_nonneg i) _

-- @node: matrixEnergy_le_trace_rpow
/-- For [a finite real square matrix](hyp:P) that [is positive semidefinite](hyp:hP),
[its matrix energy is at most its trace raised to the power three halves](goal). -/
lemma matrixEnergy_le_trace_rpow {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℝ) (hP : P.PosSemidef) :
    matrixEnergy P ≤ P.trace ^ (3 / 2 : ℝ) := by
  have hp (i : ι) := hP.eigenvalues_nonneg i
  have ht : P.trace = ∑ i, hP.isHermitian.eigenvalues i := by
    simpa using hP.isHermitian.trace_eq_sum_eigenvalues
  have hsplit (x : ℝ) (hx : 0 ≤ x) :
      x ^ (3 / 2 : ℝ) = x * x ^ (1 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add_of_nonneg hx (by norm_num) (by norm_num), Real.rpow_one]
  rw [matrixEnergy_eq_sum_eigenvalues P hP.isHermitian, hsplit _ hP.trace_nonneg]
  calc
    _ = ∑ i, hP.isHermitian.eigenvalues i *
        hP.isHermitian.eigenvalues i ^ (1 / 2 : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      exact hsplit _ (hp i)
    _ ≤ ∑ i, hP.isHermitian.eigenvalues i * P.trace ^ (1 / 2 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hp i)
      apply Real.rpow_le_rpow (hp i) _ (by norm_num)
      rw [ht]
      exact Finset.single_le_sum (fun j _ => hp j) (Finset.mem_univ i)
    _ = _ := by rw [← Finset.sum_mul, ← ht]

-- @node: rowStar_mul_transpose
/-- Given [a real matrix with finitely many columns](hyp:W) and
[a real matrix with finitely many rows whose columns match the first matrix's rows](hyp:V),
[concatenating the first matrix with the transpose of the second and multiplying by
the transpose of that concatenation gives the sum of the first matrix times its
transpose and the second matrix's transpose times the second matrix](goal). -/
lemma rowStar_mul_transpose {ι κ η : Type*} [Fintype κ] [Fintype η]
    (W : Matrix ι κ ℝ) (V : Matrix η ι ℝ) :
    rowStar W V * (rowStar W V).transpose = W * W.transpose + V.transpose * V := by
  rw [rowStar, Matrix.transpose_fromCols, Matrix.transpose_transpose,
    Matrix.fromCols_mul_fromRows]

-- @node: vertexEnergy_le_incident_trace_rpow
/-- For [three real functions of two variables](hyp:F), [a comparison scale](hyp:k),
[an atom scale](hyp:m), [three dyadic interval indices](hyp:n), and
[a vertex of the triangle](hyp:v), [the vertex energy is at most the sum of the
traces of the two incident weighted edge Gram matrices, raised to the power three halves](goal). -/
lemma vertexEnergy_le_incident_trace_rpow (F : Fin 3 → ℝ × ℝ → ℝ) (k m : ℤ)
    (n : Fin 3 → ℕ) (v : Fin 3) :
    vertexEnergy F k m n v ≤
      ((weightedEdge F k m n v * (weightedEdge F k m n v).transpose).trace +
        ((weightedEdge F k m n (v + 2)).transpose *
          weightedEdge F k m n (v + 2)).trace) ^ (3 / 2 : ℝ) := by
  have hGram : (atomRowStar F k m n v *
      (atomRowStar F k m n v).transpose).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose (atomRowStar F k m n v)
  calc
    _ = matrixEnergy (atomRowStar F k m n v *
        (atomRowStar F k m n v).transpose) := matrixEnergy_gram _
    _ ≤ _ := matrixEnergy_le_trace_rpow _ hGram
    _ = _ := by rw [atomRowStar, rowStar_mul_transpose, Matrix.trace_add]

-- @node: add_three_halves_le
/-- For [a real number a](hyp:a) and [a real number b](hyp:b), if
[a is nonnegative](hyp:ha) and [b is nonnegative](hyp:hb), then
[(a + b) raised to the power three halves is at most the square root of two
times the sum of a and b each raised to the power three halves](goal). -/
lemma add_three_halves_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ (3 / 2 : ℝ) ≤
      Real.sqrt 2 * (a ^ (3 / 2 : ℝ) + b ^ (3 / 2 : ℝ)) := by
  have h := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg
    (s := Finset.univ) (f := ![a, b]) (p := (3 / 2 : ℝ)) (by norm_num)
    (by intro i _; fin_cases i <;> simp [ha, hb])
  norm_num [Fin.sum_univ_two, Real.sqrt_eq_rpow] at h ⊢
  exact h

-- @node: vertexEnergy_le_incident_edge_mass
/-- For [three real functions of two variables](hyp:F), [a comparison scale](hyp:k),
[an atom scale](hyp:m), [three dyadic interval indices](hyp:n), and
[a triangle vertex](hyp:v), [the vertex energy is at most the square root of two
times the sum of the traces of its two incident weighted edge Gram matrices,
each trace raised to the power three halves](goal). -/
lemma vertexEnergy_le_incident_edge_mass (F : Fin 3 → ℝ × ℝ → ℝ) (k m : ℤ)
    (n : Fin 3 → ℕ) (v : Fin 3) :
    vertexEnergy F k m n v ≤ Real.sqrt 2 *
      (((weightedEdge F k m n v * (weightedEdge F k m n v).transpose).trace) ^
          (3 / 2 : ℝ) +
        (((weightedEdge F k m n (v + 2)).transpose *
          weightedEdge F k m n (v + 2)).trace) ^ (3 / 2 : ℝ)) := by
  apply (vertexEnergy_le_incident_trace_rpow F k m n v).trans
  apply add_three_halves_le
  · have h := (Matrix.posSemidef_self_mul_conjTranspose
        (weightedEdge F k m n v)).trace_nonneg
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using h
  · have h := (Matrix.posSemidef_conjTranspose_mul_self
        (weightedEdge F k m n (v + 2))).trace_nonneg
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using h

-- @node: localEnergy_le_edge_mass_sum
/-- For [three real functions of two variables](hyp:F), [a comparison scale](hyp:k),
[an atom scale](hyp:m), and [three dyadic interval indices](hyp:n),
[the local energy is at most twice the square root of two times the sum over
the three weighted edges of their Gram traces raised to the power three halves](goal). -/
lemma localEnergy_le_edge_mass_sum (F : Fin 3 → ℝ × ℝ → ℝ) (k m : ℤ)
    (n : Fin 3 → ℕ) :
    localEnergy F k m n ≤ 2 * Real.sqrt 2 *
      ∑ v : Fin 3, ((weightedEdge F k m n v *
        (weightedEdge F k m n v).transpose).trace) ^ (3 / 2 : ℝ) := by
  calc
    _ ≤ ∑ v : Fin 3, Real.sqrt 2 *
        (((weightedEdge F k m n v * (weightedEdge F k m n v).transpose).trace) ^
            (3 / 2 : ℝ) +
          (((weightedEdge F k m n (v + 2)).transpose *
            weightedEdge F k m n (v + 2)).trace) ^ (3 / 2 : ℝ)) := by
      exact Finset.sum_le_sum fun v _ => vertexEnergy_le_incident_edge_mass F k m n v
    _ = _ := by
      simp only [Matrix.trace_mul_comm (weightedEdge F k m n _).transpose]
      simp only [Fin.sum_univ_three]
      simp only [show (0 : Fin 3) + 2 = 2 from rfl,
        show (1 : Fin 3) + 2 = 0 from rfl,
        show (2 : Fin 3) + 2 = 1 from rfl]
      ring

-- @node: localEnergy_le_atomCubeMass_sum
/-- For [three real functions of two variables](hyp:F), [a comparison scale](hyp:k),
[an atom scale](hyp:m), and [three dyadic interval indices](hyp:n), if
[the comparison scale is at least the atom scale](hyp:hk), then
[the local energy is at most twice the square root of two times the sum of
the three atom cube masses](goal). -/
lemma localEnergy_le_atomCubeMass_sum (F : Fin 3 → ℝ × ℝ → ℝ) (k m : ℤ)
    (n : Fin 3 → ℕ) (hk : TotalScale k m) :
    localEnergy F k m n ≤ 2 * Real.sqrt 2 * ∑ v : Fin 3, atomCubeMass F k m n v := by
  apply (localEnergy_le_edge_mass_sum F k m n).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Finset.sum_le_sum fun v _ => weightedEdge_mass_le_atom_cubes F k m n v hk

-- @node: totalEnergy_le_atomCubeMass_sum
/-- For [three real functions of two variables](hyp:F), [a comparison scale](hyp:k),
and [an atom scale](hyp:m), suppose [the comparison scale is at least the atom scale](hyp:hk)
and [each function vanishes outside a bounded square in the nonnegative quadrant](hyp:hCompact).
Then [the total energy is at most twice the square root of two times the sum over
admissible interval triples of the three atom cube masses, weighted by two raised
to twice the comparison scale](goal). -/
lemma totalEnergy_le_atomCubeMass_sum (F : Fin 3 → ℝ × ℝ → ℝ) (k m : ℤ)
    (hk : TotalScale k m) (hCompact : StepCompact F) :
    totalEnergy F k m ≤ 2 * Real.sqrt 2 *
      ∑' n : admissibleSet, (2 : ℝ) ^ (2 * k) * ∑ v : Fin 3, atomCubeMass F k m n.val v := by
  have hs : Summable (fun n : admissibleSet => ∑ v : Fin 3, atomCubeMass F k m n.val v) := by
    apply summable_sum
    intro v _
    exact summable_of_hasFiniteSupport (atomCubeMass_hasFiniteSupport F k m hCompact v)
  calc
    _ ≤ ∑' n : admissibleSet, (2 : ℝ) ^ (2 * k) *
        (2 * Real.sqrt 2 * ∑ v : Fin 3, atomCubeMass F k m n.val v) := by
      change (∑' n : admissibleSet, (2 : ℝ) ^ (2 * k) * localEnergy F k m n.val) ≤ _
      exact Summable.tsum_le_tsum
        (fun n : admissibleSet =>
          mul_le_mul_of_nonneg_left (localEnergy_le_atomCubeMass_sum F k m n.val hk)
            (by positivity))
        ((localEnergy_summable F k m hCompact).mul_left ((2 : ℝ) ^ (2 * k)))
        ((hs.mul_left (2 * Real.sqrt 2)).mul_left ((2 : ℝ) ^ (2 * k)))
    _ = _ := by
      simp_rw [mul_left_comm ((2 : ℝ) ^ (2 * k)) (2 * Real.sqrt 2)]
      rw [tsum_mul_left]

-- @node: vertexEnergy_nonneg
/-- For [three real functions of two variables](hyp:F), [a comparison scale](hyp:k),
[an atom scale](hyp:m), [three dyadic interval indices](hyp:n), and
[a triangle vertex](hyp:v), [the vertex energy is nonnegative](goal). -/
lemma vertexEnergy_nonneg (F : Fin 3 → ℝ × ℝ → ℝ) (k m : ℤ)
    (n : Fin 3 → ℕ) (v : Fin 3) : 0 ≤ vertexEnergy F k m n v := by
  apply matrixEnergy_nonneg
  simpa only [rowGram, Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_conjTranspose_mul_self (atomRowStar F k m n v)

-- @node: localEnergy_nonneg
/-- For [three real functions of two variables](hyp:F), [a comparison scale](hyp:k),
[an atom scale](hyp:m), and [three dyadic interval indices](hyp:n),
[the local energy is nonnegative](goal). -/
lemma localEnergy_nonneg (F : Fin 3 → ℝ × ℝ → ℝ) (k m : ℤ)
    (n : Fin 3 → ℕ) : 0 ≤ localEnergy F k m n := by
  exact Finset.sum_nonneg fun v _ => vertexEnergy_nonneg F k m n v

-- @node: totalEnergy_nonneg
/-- For [three real functions of two variables](hyp:F), [a comparison scale](hyp:k),
and [an atom scale](hyp:m), [the total energy is nonnegative](goal). -/
lemma totalEnergy_nonneg (F : Fin 3 → ℝ × ℝ → ℝ) (k m : ℤ) :
    0 ≤ totalEnergy F k m := by
  apply tsum_nonneg
  intro n
  exact mul_nonneg (by positivity) (localEnergy_nonneg F k m n.val)

-- @node: totalEnergy_telescope
/-- For [three real functions of two variables](hyp:F), [a comparison scale](hyp:k),
and [an atom scale](hyp:m), if [each function vanishes outside a bounded square
in the nonnegative quadrant](hyp:hCompact), then [the sum of the energy increments
over admissible interval triples, weighted by two raised to twice the comparison
scale, equals the total energy at the preceding scale minus that at the comparison scale](goal). -/
lemma totalEnergy_telescope (F : Fin 3 → ℝ × ℝ → ℝ) (k m : ℤ)
    (hCompact : StepCompact F) :
    (∑' n : admissibleSet, (2 : ℝ) ^ (2 * k) * energyIncrement F k m n.val) =
      totalEnergy F (k - 1) m - totalEnergy F k m := by
  have hs := localEnergy_summable F k m hCompact
  have hc := summable_children_and_tsum (localEnergy F (k - 1) m)
    (localEnergy_summable F (k - 1) m hCompact)
  have hw : (2 : ℝ) ^ (2 * k) * (1 / 4 : ℝ) = (2 : ℝ) ^ (2 * (k - 1)) := by
    rw [show 2 * (k - 1) = 2 * k - 2 by ring, zpow_sub₀ (by norm_num)]
    norm_num
    ring
  calc
    _ = ((2 : ℝ) ^ (2 * k) * (1 / 4 : ℝ)) *
          (∑' n : admissibleSet, ∑ c ∈ children n.val, localEnergy F (k - 1) m c) -
        (2 : ℝ) ^ (2 * k) * (∑' n : admissibleSet, localEnergy F k m n.val) := by
      simp only [energyIncrement, mul_sub, ← mul_assoc]
      rw [(hc.1.mul_left _).tsum_sub (hs.mul_left _), tsum_mul_left, tsum_mul_left]
    _ = _ := by rw [hw, hc.2, totalEnergy, totalEnergy, tsum_mul_left, tsum_mul_left]

-- @node: lem:total
/-- For [three real functions of two variables](hyp:F), [a comparison scale](hyp:k),
and [an atom scale](hyp:m), assume [each function is bounded on the nonnegative quadrant](hyp:hBounded),
[each vanishes there outside a bounded square](hyp:hCompact), and
[each is constant on every dyadic atom rectangle at the atom scale](hyp:hAtoms).
Then [whenever the comparison scale is at least the atom scale, the total energy
is nonnegative and at most twice the square root of two times the sum of the cubes
of the three L³ norms on the quadrant; whenever the comparison scale is at least
one greater than the atom scale, the sum of the energy increments over admissible
interval triples, weighted by two raised to twice the comparison scale, equals
the total energy at the preceding scale minus that at the comparison scale](goal). -/
lemma totalEnergy_bound_and_telescope (F : Fin 3 → ℝ × ℝ → ℝ) (k m : ℤ)
    (hBounded : StepBounded F) (hCompact : StepCompact F) (hAtoms : StepAtoms F m) :
    (TotalScale k m →
      0 ≤ totalEnergy F k m ∧
      totalEnergy F k m ≤ 2 * Real.sqrt 2 *
        ∑ v : Fin 3, (eLpNorm (F v) 3 quadrantMeasure).toReal ^ 3) ∧
    (TotalTelescopeScale k m →
      (∑' n : admissibleSet, (2 : ℝ)^(2*k) * energyIncrement F k m n.val) =
        totalEnergy F (k - 1) m - totalEnergy F k m) := by
  constructor
  · intro hScale
    refine ⟨totalEnergy_nonneg F k m, ?_⟩
    apply (totalEnergy_le_atomCubeMass_sum F k m hScale hCompact).trans
    rw [weighted_atomCubeMass_sum_eq_gridCubeMass_sum F k m hCompact]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Finset.sum_le_sum fun v _ =>
      (gridCubeMass_eq_eLpNorm_cube F m hCompact hAtoms v).le
  · intro hScale
    exact totalEnergy_telescope F k m hCompact

end Papers.OaiBoundDyadicTriangular

module

public import Papers.OaiNearInclusionsVon.TNear
public import Papers.OaiNearInclusionsVon.Helpers.Clock

/-! The clock–shift specialization and its vanishing gaps. -/

@[expose] public section

set_option linter.style.longLine false

namespace Papers.OaiNearInclusionsVon


open Filter
open scoped Topology

/-- For [a clock index n](hyp:n), [the auxiliary Hilbert space](goal) is the
completed tensor product of two free-group square-summable spaces and complex n-space. -/
noncomputable abbrev mainL (n : ClockNat) := Lsp (ClockSpace n) -- @realizes L_n(clock–shift tensor space)
/-- For [a clock index n](hyp:n), [the main Hilbert space](goal) consists of
square-summable families, indexed by the product group, of vectors in the auxiliary Hilbert space. -/
noncomputable abbrev mainH (n : ClockNat) := Hsp (ClockSpace n) -- @realizes H_n(four copies of K tensor complex n-space)
/-- For [a clock index n](hyp:n), [the common identity operator](goal) leaves
every vector of the main Hilbert space unchanged. -/
noncomputable def mainIdentity (n : ClockNat) : mainH n →L[ℂ] mainH n := 1 -- @realizes I_{H_n}(common identity)

/-- For [Laurent coefficients A](hyp:A) and [a clock index n](hyp:n),
[the first specialized operator family](goal) substitutes the clock unitary
into the Laurent series acting on the first free-group factor. -/
noncomputable def mainA (A : LaurentData) (n : ClockNat) :=
  matrixRepA A (clockU n) -- @realizes a_n(clock substitution)
/-- For [Laurent coefficients A](hyp:A) and [a clock index n](hyp:n),
[the second specialized operator family](goal) substitutes the shift unitary
into the Laurent series acting on the second free-group factor. -/
noncomputable def mainB (A : LaurentData) (n : ClockNat) :=
  matrixRepB A (shiftV n) -- @realizes b_n(shift substitution)
/-- For [Laurent coefficients A](hyp:A) and [a clock index n](hyp:n),
[the specialized product family](goal) multiplies the clock-substituted first
operator by the shift-substituted second operator at each pair of group elements. -/
noncomputable def mainF (A : LaurentData) (n : ClockNat) :=
  prodMap A (clockU n) (shiftV n) -- @realizes f_n(ordered product specialization)

/-- If [the circle representations and Laurent coefficients satisfy the circle-family
conditions](hyp:hπ), [every clock–shift product operator has norm at most the
square of the total coefficient bound S₀](goal). -/
-- @node: mainBlockBound
lemma mainBlockBound (π : CircleRep) (A : LaurentData) (hπ : IsCircleFamily π A) (n : ClockNat) :
    ∀ x : ProdGrp, ‖prodMap A (clockU n) (shiftV n) x‖ ≤ S0 ^ 2 := by
  exact prodMap_norm_bound π A hπ (clockU n) (shiftV n)
    ⟨clockU_mem_unitary n, shiftV_mem_unitary n⟩

/-- Given [circle representations π](hyp:π), [Laurent coefficients A](hyp:A),
[their circle-family conditions](hyp:hπ), and [a clock index n](hyp:n),
[the diagonal unitary](goal) acts at each product-group coordinate by the
corresponding clock–shift product operator. -/
noncomputable def mainW (π : CircleRep) (A : LaurentData) (hπ : IsCircleFamily π A) (n : ClockNat) :=
  diagUnitary A (clockU n) (shiftV n) (mainBlockBound π A hπ n) -- @realizes W_n(diagonal unitary specialization)

-- @node: def:main-sequence
/-- Given [circle representations π](hyp:π), [Laurent coefficients A](hyp:A),
[their circle-family conditions](hyp:hπ), and [a clock index n](hyp:n),
[the source von Neumann algebra](goal) is the amplified left regular algebra
conjugated by the diagonal clock–shift unitary. -/
noncomputable def mainSource (π : CircleRep) (A : LaurentData) (hπ : IsCircleFamily π A)
    (n : ClockNat) : VonNeumannAlgebra (mainH n) :=
  sourceAlg A (clockU n) (shiftV n) (mainBlockBound π A hπ n) -- @realizes M_n(clock–shift source algebra)
/-- For [a clock index n](hyp:n), [the target von Neumann algebra](goal) consists
of the operators on the main Hilbert space commuting with the amplified right regular representation. -/
noncomputable def mainTarget (n : ClockNat) : VonNeumannAlgebra (mainH n) :=
  targetAlg (D := ClockSpace n) -- @realizes N_n(clock–shift target algebra)

/-- Given [circle representations π](hyp:π), [Laurent coefficients A](hyp:A),
[their circle-family conditions](hyp:hπ), and [a clock index n](hyp:n),
[the near-inclusion gap](goal) measures how far the source algebra's unit ball
lies from the target algebra in operator norm. -/
noncomputable def mainGap (π : CircleRep) (A : LaurentData) (hπ : IsCircleFamily π A)
    (n : ClockNat) : ℝ :=
  nearInclusionGap (mainSource π A hπ n : Set (mainH n →L[ℂ] mainH n))
    (mainTarget n : Set (mainH n →L[ℂ] mainH n))

-- @node: mainGap_le
/-- If [the representations and coefficients satisfy the circle-family conditions](hyp:hπ),
[the source-to-target near-inclusion gap at each clock index is at most the
fixed near-inclusion constant times the clock–shift commutator scale](goal). -/
lemma mainGap_le (π : CircleRep) (A : LaurentData) (hπ : IsCircleFamily π A)
    (n : ClockNat) : mainGap π A hπ n ≤ nearC * nuN n := by
  letI : NeZero n.val := ⟨by have := n.property; unfold ClockIndex at this; omega⟩
  have hUV : NearUnitaryPair (clockU n) (shiftV n) :=
    ⟨inferInstance, inferInstance, clockU_mem_unitary n, shiftV_mem_unitary n⟩
  exact (near_inclusion_bound π A hπ (clockU n) (shiftV n) hUV
    (matrixRepsAbsConv_of_circleFamily π A hπ (clockU n) (shiftV n)
      (clockU_mem_unitary n) (shiftV_mem_unitary n))).2.1

-- @node: mainGap_tendsto_zero
/-- If [the representations and coefficients satisfy the circle-family conditions](hyp:hπ),
[the source-to-target near-inclusion gap converges to zero as the clock index grows](goal). -/
lemma mainGap_tendsto_zero (π : CircleRep) (A : LaurentData) (hπ : IsCircleFamily π A) :
    Tendsto (mainGap π A hπ) atTop (𝓝 0) := by
  apply squeeze_zero
    (fun n => nearInclusionGap_nonneg (mainSource π A hπ n) (mainTarget n))
    (mainGap_le π A hπ)
  simpa only [mul_zero] using nuN_tendsto_zero.const_mul nearC

/-- If [the representations and coefficients satisfy the circle-family conditions](hyp:hπ),
[the near-inclusion gap is bounded at every clock index by the fixed near-inclusion
constant times the commutator scale, and both this bound and the gap converge to zero](goal). -/
theorem mainGap_bound_and_limit (π : CircleRep) (A : LaurentData) (hπ : IsCircleFamily π A) :
    (∀ n : ClockNat, mainGap π A hπ n ≤ nearC * nuN n) ∧
      Tendsto (fun n : ClockNat => nearC * nuN n) atTop (𝓝 0) ∧
      Tendsto (mainGap π A hπ) atTop (𝓝 0) := by
  refine ⟨mainGap_le π A hπ, ?_, mainGap_tendsto_zero π A hπ⟩
  simpa only [mul_zero] using nuN_tendsto_zero.const_mul nearC

-- The core classifies this proof-valued construction as a `def`.
set_option linter.defProp false in
/-- Given [circle representations π](hyp:π), [Laurent coefficients A](hyp:A),
and [their circle-family conditions](hyp:hπ), [the vanishing-gap construction](goal)
certifies that [the gap is bounded at every clock index by the fixed near-inclusion
constant times the commutator scale](step:1), [this upper bound converges to zero](step:2),
and [the gap itself converges to zero](step:3). -/
-- @node: def:vanishing-gap
def vanishingGap (π : CircleRep) (A : LaurentData) (hπ : IsCircleFamily π A) :
    (∀ n : ClockNat, mainGap π A hπ n ≤ nearC * nuN n) ∧
      Tendsto (fun n : ClockNat => nearC * nuN n) atTop (𝓝 0) ∧
      Tendsto (mainGap π A hπ) atTop (𝓝 0) :=
  mainGap_bound_and_limit π A hπ

end Papers.OaiNearInclusionsVon

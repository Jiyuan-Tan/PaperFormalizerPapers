module

public import Mathlib.Analysis.VonNeumannAlgebra.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! The one-sided unit-ball gap and commutants. -/

@[expose] public section

set_option linter.style.longLine false

namespace Papers.OaiNearInclusionsVon


-- @env: S1
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] -- @realizes H(complex Hilbert space)

-- @node: def:gamma
/-- For [two sets M and N of bounded operators](hyp:M,N) on [a complex Hilbert
space H](hyp:H), the [one-sided near-inclusion gap from M to N](goal) is the supremum,
over operators in M of norm at most one, of their operator-norm distance to N. -/
noncomputable def nearInclusionGap (M N : Set (H →L[ℂ] H)) : ℝ :=
  ⨆ x : {x // x ∈ M ∧ ‖x‖ ≤ 1}, Metric.infDist (x : H →L[ℂ] H) N -- @realizes \gamma(supremum of distances on the source unit ball)

/-- On [a complex Hilbert space H](hyp:H), the [common identity operator](goal) is
the bounded operator that fixes every vector. -/
noncomputable def hilbertIdentity : H →L[ℂ] H := 1 -- @realizes I_H(common identity)

-- @node: def:commutant-notation
/-- For [a set S of bounded operators](hyp:S) on [a complex Hilbert space H](hyp:H),
the [commutant of S](goal) is the set of bounded operators commuting with every member
of S. -/
noncomputable abbrev commutant (S : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H) := Set.centralizer S

-- @node: centralizer_is_double_closed
/-- For [a set S of bounded operators on a complex Hilbert space](hyp:S),
[the set of operators commuting with every element of S and every adjoint of an
element of S equals its own double commutant](goal). -/
lemma centralizer_is_double_closed (S : Set (H →L[ℂ] H)) :
    Set.centralizer (Set.centralizer
      (StarSubalgebra.centralizer ℂ S : Set (H →L[ℂ] H))) =
      (StarSubalgebra.centralizer ℂ S : Set (H →L[ℂ] H)) := by
  rw [StarSubalgebra.coe_centralizer, Set.centralizer_centralizer_centralizer]

/-- For [a set S of bounded operators](hyp:S) on [a complex Hilbert space H](hyp:H),
the [von Neumann algebra commutant associated with S](goal) consists of all bounded
operators commuting with every element of S and with every adjoint of an element of S. -/
noncomputable def commutantVN (S : Set (H →L[ℂ] H)) : VonNeumannAlgebra H :=
  ⟨StarSubalgebra.centralizer ℂ S, centralizer_is_double_closed S⟩

-- @node: nearInclusionGap_nonneg
/-- For [two von Neumann algebras M and N on the same complex Hilbert space](hyp:M,N),
[the one-sided near-inclusion gap from M to N is nonnegative](goal). -/
lemma nearInclusionGap_nonneg (M N : VonNeumannAlgebra H) :
    0 ≤ nearInclusionGap (M : Set (H →L[ℂ] H)) (N : Set (H →L[ℂ] H)) := by
  unfold nearInclusionGap
  have hbound : BddAbove (Set.range (fun x : {x // x ∈ M ∧ ‖x‖ ≤ 1} =>
      Metric.infDist (x : H →L[ℂ] H) (N : Set (H →L[ℂ] H)))) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact (Metric.infDist_le_dist_of_mem N.zero_mem).trans (by simpa using x.property.2)
  exact (Metric.infDist_nonneg (x := (0 : H →L[ℂ] H)) (s := (N : Set _))).trans
    (le_ciSup hbound ⟨0, M.zero_mem, by simp⟩)

-- @node: nearInclusionGap_le_of_forall
/-- For [two von Neumann algebras M and N on the same complex Hilbert space](hyp:M,N)
and [a real error bound c](hyp:c), if [c is nonnegative](hyp:hc) and
[every operator in M of norm at most one lies within operator-norm distance c of
some operator in N](hyp:h), then [the one-sided near-inclusion gap from M to N is
at most c](goal). -/
lemma nearInclusionGap_le_of_forall (M N : VonNeumannAlgebra H) (c : ℝ)
    (hc : 0 ≤ c)
    (h : ∀ x ∈ M, ‖x‖ ≤ 1 → ∃ y ∈ N, ‖x - y‖ ≤ c) :
    nearInclusionGap (M : Set (H →L[ℂ] H)) (N : Set (H →L[ℂ] H)) ≤ c := by
  unfold nearInclusionGap
  haveI : Nonempty {x : H →L[ℂ] H // x ∈ M ∧ ‖x‖ ≤ 1} :=
    ⟨⟨0, M.zero_mem, by simp⟩⟩
  apply ciSup_le
  intro x
  obtain ⟨y, hy, hxy⟩ := h x x.property.1 x.property.2
  exact (Metric.infDist_le_dist_of_mem hy).trans (by simpa only [dist_eq_norm] using hxy)

end Papers.OaiNearInclusionsVon

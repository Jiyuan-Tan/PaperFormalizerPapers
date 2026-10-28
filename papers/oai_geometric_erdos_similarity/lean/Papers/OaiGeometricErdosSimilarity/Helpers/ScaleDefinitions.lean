module
public import Papers.OaiGeometricErdosSimilarity.Helpers.Routing

/-! # Scale breakpoints, endpoints, and finite representative sets -/

@[expose] public section

namespace Papers.OaiGeometricErdosSimilarity

open Causalean.Experimentation.DesignBased
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {q p : ℝ} {M d g r0 n0 : ℕ}

-- @node: def:scale-count
/-- For [branching count M](hyp:M), [ratio q](hyp:q), and [window length r](hyp:r),
[the scale-count bound is 4 plus twice (M minus 1) times r times
(1 plus twice the grid constant times q to the power minus 2r)](goal). -/
noncomputable def scaleCount (M : ℕ) (q : ℝ) (r : ℕ) : ℝ :=
  -- @realizes D_{M,q}(r)(explicit finite scale-count bound)
  4 + 2 * ((M : ℝ) - 1) * r * (1 + 2 * gridConst q * q ^ (-(2 * (r : ℤ))))

/-- For [ratio q](hyp:q), [branching count M, depth d, gap g, base length r0,
and starting index n0](hyp:M,d,g,r0,n0), [internal vertex U](hyp:U), and
[center x](hyp:x), [the scale breakpoints are the scales between one and two
for which some local point in a nonfinal child's window lies on the grid at that child's
block endpoint](goal). -/
noncomputable def scaleBreakpoints (q : ℝ) (M d g r0 n0 : ℕ)
    (U : InternalVertex M d) (x : ℝ) : Set ℝ :=
  {t | t ∈ Set.Icc (1 : ℝ) 2 ∧ ∃ a ∈ localIndexPairs q M d g r0 n0 U,
    localPoint x t q a.2 ∈ gridLattice q (blockEndpoint q M d g r0 n0 (localEdge U a.1))}

-- @node: scaleBreakpoints_finite
/-- If [q lies strictly between zero and one](hyp:hq), [the scale breakpoints
at any internal vertex U and center x form a finite set](goal). -/
lemma scaleBreakpoints_finite (hq : QDomain q) (U : InternalVertex M d) (x : ℝ) :
    (scaleBreakpoints q M d g r0 n0 U x).Finite := by
  have hpair (a : Fin M × ℕ) :
      {t : ℝ | t ∈ Set.Icc (1 : ℝ) 2 ∧
        localPoint x t q a.2 ∈ gridLattice q
          (blockEndpoint q M d g r0 n0 (localEdge U a.1))}.Finite := by
    let N := gridResolution q (blockEndpoint q M d g r0 n0 (localEdge U a.1))
    have hN : (0 : ℝ) < N := by exact_mod_cast gridResolution_pos q _
    have hv : 0 < q ^ a.2 := pow_pos hq.1 _
    apply ((Set.finite_Icc _ _).image
      (fun k : ℤ => ((k : ℝ) / N - x) / q ^ a.2)).subset
    intro t ht
    obtain ⟨ht, k, hk⟩ := ht
    change x + t * q ^ a.2 = (k : ℝ) / N at hk
    have heq : (k : ℝ) = (N : ℝ) * (x + t * q ^ a.2) := by
      rw [hk]
      field_simp
    have hlo : (N : ℝ) * (x + q ^ a.2) ≤ (k : ℝ) := by
      rw [heq]
      exact mul_le_mul_of_nonneg_left (by nlinarith [ht.1]) hN.le
    have hhi : (k : ℝ) ≤ (N : ℝ) * (x + 2 * q ^ a.2) := by
      rw [heq]
      exact mul_le_mul_of_nonneg_left (by nlinarith [ht.2]) hN.le
    have hklo : ⌊(N : ℝ) * (x + q ^ a.2)⌋ ≤ k := by
      exact_mod_cast (Int.floor_le _).trans hlo
    have hkhi : k ≤ ⌈(N : ℝ) * (x + 2 * q ^ a.2)⌉ := by
      exact_mod_cast hhi.trans (Int.le_ceil _)
    refine ⟨k, ⟨hklo, hkhi⟩, ?_⟩
    dsimp only
    rw [← hk]
    simp [hv.ne']
  apply ((localIndexPairs q M d g r0 n0 U).finite_toSet.biUnion
    (fun a _ => hpair a)).subset
  intro t ht
  obtain ⟨ht, a, ha, hlat⟩ := ht
  exact Set.mem_iUnion₂.mpr ⟨a, ha, ht, hlat⟩

/-- For [ratio q](hyp:q), [branching count M, depth d, gap g, base length r0,
and starting index n0](hyp:M,d,g,r0,n0), with [q strictly between zero and
one](hyp:hq), [internal vertex U](hyp:U), and [center x](hyp:x),
[the scale endpoints are the finite set consisting of
one, two, and all scale breakpoints](goal). -/
noncomputable def scaleEndpoints (hq : QDomain q) (U : InternalVertex M d)
    (x : ℝ) : Finset ℝ :=
  {1, 2} ∪ (scaleBreakpoints_finite (g := g) (r0 := r0) (n0 := n0) hq U x).toFinset

/-- For [ratio q](hyp:q), [branching count M, depth d, gap g, base length r0,
and starting index n0](hyp:M,d,g,r0,n0), with [q strictly between zero and
one](hyp:hq), [internal vertex U](hyp:U), and [center x](hyp:x),
[the representative scales](goal) are obtained by
[forming the finite set E of scale endpoints](step:1) and
[retaining E together with the midpoint between each pair of consecutive
elements of E](step:2). -/
noncomputable def scaleRepresentatives (hq : QDomain q) (U : InternalVertex M d)
    (x : ℝ) : Finset ℝ :=
  -- @realizes \mathcal T_{x,\xi}(finite representatives fixed by x and U)
  let E := scaleEndpoints (g := g) (r0 := r0) (n0 := n0) hq U x
  E ∪ ((E.product E).filter (fun ab => ab.1 < ab.2 ∧
    ¬ ∃ c ∈ E, ab.1 < c ∧ c < ab.2)).image (fun ab => (ab.1 + ab.2) / 2)

end Papers.OaiGeometricErdosSimilarity

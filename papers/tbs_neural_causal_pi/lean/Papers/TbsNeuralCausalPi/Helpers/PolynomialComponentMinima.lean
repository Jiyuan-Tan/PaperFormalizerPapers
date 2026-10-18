module
public import Papers.TbsNeuralCausalPi.Helpers.PolynomialCompactHypersurface
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
/-! # Component minima of compact polynomial hypersurfaces

Every component of a compact zero set has a coordinate minimizer. Distinct
components have distinct minimizers, and every differentiable curve in the
zero set through such a minimizer is stationary in that coordinate. This
is the extremum step of the critical-point approach to component counting;
no bound on the number of critical points is asserted.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi

-- @node: compact_connectedComponentIn_exists_min
/-- If [a set is compact](hyp:hs), [x belongs to it](hyp:hx), and [a real-valued
function is continuous on it](hyp:hf), then [the connected component containing
x contains a point that minimizes the function on that point's component](goal). -/
lemma compact_connectedComponentIn_exists_min {X : Type*}
    [TopologicalSpace X] [T2Space X] {s : Set X} (hs : IsCompact s)
    {x : X} (hx : x ∈ s) (f : X → ℝ) (hf : ContinuousOn f s) :
    ∃ y ∈ connectedComponentIn s x,
      IsMinOn f (connectedComponentIn s y) y := by
  have hclosure : closure (connectedComponentIn s x) ⊆ s :=
    hs.isClosed.closure_subset_iff.mpr (connectedComponentIn_subset s x)
  have hclosed : IsClosed (connectedComponentIn s x) := by
    apply isClosed_of_closure_subset
    exact isPreconnected_connectedComponentIn.closure.subset_connectedComponentIn
      (subset_closure (mem_connectedComponentIn hx)) hclosure
  have hc := hs.of_isClosed_subset hclosed (connectedComponentIn_subset s x)
  obtain ⟨y, hy, hmin⟩ := hc.exists_isMinOn ⟨x, mem_connectedComponentIn hx⟩
    (hf.mono (connectedComponentIn_subset s x))
  refine ⟨y, hy, ?_⟩
  rwa [connectedComponentIn_eq hy] at hmin

-- @node: polynomialComponentMinima
/-- For [a polynomial Q](hyp:Q) and [a coordinate v](hyp:v), the
[set of component minima](goal) consists of points that [are zeros of Q](step:1)
and [minimize coordinate v on their connected component of the zero set](step:2). -/
def polynomialComponentMinima {V : Type*} (Q : MvPolynomial V ℝ) (v : V) :
    Set (V → ℝ) :=
  {a | MvPolynomial.eval a Q = 0 ∧
    IsMinOn (fun x => x v) (connectedComponentIn {x | MvPolynomial.eval x Q = 0} a) a}

-- @node: polynomialComponentMinima_exists
/-- If [the zero set of Q is compact](hyp:hQ) and [a is a zero of Q](hyp:ha),
then [the connected component containing a contains a point minimizing the
chosen coordinate on its component](goal). -/
lemma polynomialComponentMinima_exists {V : Type*} (Q : MvPolynomial V ℝ)
    (hQ : IsCompact {a | MvPolynomial.eval a Q = 0}) (v : V)
    {a : V → ℝ} (ha : MvPolynomial.eval a Q = 0) :
    ∃ y ∈ connectedComponentIn {x | MvPolynomial.eval x Q = 0} a,
      y ∈ polynomialComponentMinima Q v := by
  obtain ⟨y, hy, hmin⟩ := compact_connectedComponentIn_exists_min hQ ha
    (fun x => x v) (by fun_prop)
  exact ⟨y, hy, ⟨connectedComponentIn_subset {x | MvPolynomial.eval x Q = 0} a hy, hmin⟩⟩

-- @node: polynomialComponentMinima_carries_components
/-- If [the zero set of Q is compact](hyp:hQ), then [the components containing
minima of a chosen coordinate are exactly all the connected components of
the zero set](goal). -/
lemma polynomialComponentMinima_carries_components {V : Type*}
    (Q : MvPolynomial V ℝ) (hQ : IsCompact {a | MvPolynomial.eval a Q = 0}) (v : V) :
    (fun a => connectedComponentIn {x | MvPolynomial.eval x Q = 0} a) ''
        polynomialComponentMinima Q v =
      (fun a => connectedComponentIn {x | MvPolynomial.eval x Q = 0} a) ''
        {a | MvPolynomial.eval a Q = 0} := by
  apply Set.Subset.antisymm
  · exact Set.image_mono (fun _ ha => ha.1)
  · rintro _ ⟨a, ha, rfl⟩
    obtain ⟨y, hy, hm⟩ := polynomialComponentMinima_exists Q hQ v ha
    exact ⟨y, hm, (connectedComponentIn_eq hy).symm⟩

-- @node: polynomial_zero_components_encard_le_minima
/-- If [the zero set of Q is compact](hyp:hQ), then [the number of its connected
components is at most the number of points minimizing a chosen coordinate on
their component, allowing either number to be infinite](goal). -/
lemma polynomial_zero_components_encard_le_minima {V : Type*}
    (Q : MvPolynomial V ℝ) (hQ : IsCompact {a | MvPolynomial.eval a Q = 0}) (v : V) :
    ((fun a => connectedComponentIn {x | MvPolynomial.eval x Q = 0} a) ''
      {a | MvPolynomial.eval a Q = 0}).encard ≤ (polynomialComponentMinima Q v).encard := by
  rw [← polynomialComponentMinima_carries_components Q hQ v]
  exact Set.encard_image_le _ _

-- @node: polynomial_zero_curve_mem_component
/-- If [r is positive](hyp:hr), [a curve is continuous on the open interval
from −r to r](hyp:hγ), [the curve lies in the zero set of Q throughout that
interval](hyp:hzero), and [t belongs to that interval](hyp:ht), then
[the curve at t lies in the connected component of the zero set containing
the curve at zero](goal). -/
lemma polynomial_zero_curve_mem_component {V : Type*}
    (Q : MvPolynomial V ℝ) {γ : ℝ → V → ℝ} {r : ℝ} (hr : 0 < r)
    (hγ : ContinuousOn γ (Set.Ioo (-r) r))
    (hzero : ∀ t ∈ Set.Ioo (-r) r, MvPolynomial.eval (γ t) Q = 0)
    {t : ℝ} (ht : t ∈ Set.Ioo (-r) r) :
    γ t ∈ connectedComponentIn {x | MvPolynomial.eval x Q = 0} (γ 0) := by
  have h0 : (0 : ℝ) ∈ Set.Ioo (-r) r := ⟨neg_lt_zero.mpr hr, hr⟩
  have hp := isPreconnected_Ioo.image γ hγ
  exact hp.subset_connectedComponentIn (Set.mem_image_of_mem γ h0)
    (by rintro _ ⟨s, hs, rfl⟩; exact hzero s hs)
    (Set.mem_image_of_mem γ ht)

-- @node: polynomialComponentMinima_curve_localMin
/-- If [a minimizes coordinate v on its component of the zero set of Q](hyp:ha),
[r is positive](hyp:hr), [a curve is continuous between −r and r](hyp:hγ),
[passes through a at time zero](hyp:hγ0), and [stays in the zero set on that
open interval](hyp:hzero), then [coordinate v along the curve has a local
minimum at time zero](goal). -/
lemma polynomialComponentMinima_curve_localMin {V : Type*}
    (Q : MvPolynomial V ℝ) (v : V) {a : V → ℝ}
    (ha : a ∈ polynomialComponentMinima Q v)
    {γ : ℝ → V → ℝ} {r : ℝ} (hr : 0 < r)
    (hγ : ContinuousOn γ (Set.Ioo (-r) r)) (hγ0 : γ 0 = a)
    (hzero : ∀ t ∈ Set.Ioo (-r) r, MvPolynomial.eval (γ t) Q = 0) :
    IsLocalMin (fun t => γ t v) 0 := by
  have hmin : IsMinOn (fun t => γ t v) (Set.Ioo (-r) r) 0 := by
    intro t ht
    change γ 0 v ≤ γ t v
    rw [hγ0]
    apply ha.2
    rw [← hγ0]
    exact polynomial_zero_curve_mem_component Q hr hγ hzero ht
  exact hmin.isLocalMin (isOpen_Ioo.mem_nhds ⟨neg_lt_zero.mpr hr, hr⟩)

-- @node: polynomialComponentMinima_curve_derivative_zero
/-- If [a minimizes coordinate v on its component of the zero set of Q](hyp:ha),
[r is positive](hyp:hr), [a curve is continuous on the open interval from −r
to r](hyp:hγ), [passes through a at time zero](hyp:hγ0), [stays in the zero
set on that interval](hyp:hzero), and [its coordinate v has derivative δ at
zero](hyp:hd), then [δ is zero](goal). -/
lemma polynomialComponentMinima_curve_derivative_zero {V : Type*}
    (Q : MvPolynomial V ℝ) (v : V) {a : V → ℝ}
    (ha : a ∈ polynomialComponentMinima Q v)
    {γ : ℝ → V → ℝ} {r δ : ℝ} (hr : 0 < r)
    (hγ : ContinuousOn γ (Set.Ioo (-r) r)) (hγ0 : γ 0 = a)
    (hzero : ∀ t ∈ Set.Ioo (-r) r, MvPolynomial.eval (γ t) Q = 0)
    (hd : HasDerivAt (fun t => γ t v) δ 0) : δ = 0 := by
  exact (polynomialComponentMinima_curve_localMin Q v ha hr hγ hγ0 hzero).hasDerivAt_eq_zero hd

-- @node: strictPolynomialSignPattern_component_minima_reduction
/-- If [every polynomial in the family has total degree at most d](hyp:hd),
then [there is a polynomial Q in the same variables, of total degree at most
twice the number of polynomials times d plus two, with compact zero set and
at least as many component minima of coordinate v as there are strict sign
patterns where all original polynomials are nonzero](goal). -/
lemma strictPolynomialSignPattern_component_minima_reduction {I V : Type*}
    [Fintype I] [Finite V] (v : V) (p : I → MvPolynomial V ℝ) (d : ℕ)
    (hd : ∀ i, (p i).totalDegree ≤ d) :
    ∃ Q : MvPolynomial V ℝ,
      Q.totalDegree ≤ 2 * Fintype.card I * d + 2 ∧
      IsCompact {a | MvPolynomial.eval a Q = 0} ∧
      (strictPolynomialSignPattern p '' polynomialNonzeroDomain p).encard ≤
        (polynomialComponentMinima Q v).encard := by
  let : Nonempty V := ⟨v⟩
  obtain ⟨Q, hdegree, hcompact, hcount⟩ :=
    strictPolynomialSignPattern_compact_hypersurface_reduction p d hd
  exact ⟨Q, hdegree, hcompact,
    hcount.trans (polynomial_zero_components_encard_le_minima Q hcompact v)⟩

-- @node: polynomialComparisonPattern_component_minima_reduction
/-- If [every polynomial in the family has total degree at most d](hyp:hd),
then [there is a polynomial Q in one additional variable, of total degree at
most four times the number of polynomials times the larger of d and one,
plus two, whose zero set is compact and has at least as many component minima
of the added coordinate as there are weak and strict comparison patterns of
the original family](goal). -/
lemma polynomialComparisonPattern_component_minima_reduction {I V : Type*}
    [Fintype I] [Finite V] (p : I → MvPolynomial V ℝ) (d : ℕ)
    (hd : ∀ i, (p i).totalDegree ≤ d) :
    ∃ Q : MvPolynomial (Option V) ℝ,
      Q.totalDegree ≤ 4 * Fintype.card I * max d 1 + 2 ∧
      IsCompact {a | MvPolynomial.eval a Q = 0} ∧
      (Set.range (polynomialComparisonPattern p)).encard ≤
        (polynomialComponentMinima Q none).encard := by
  obtain ⟨Q, hdegree, hcompact, hcount⟩ :=
    polynomialComparisonPattern_compact_hypersurface_reduction p d hd
  exact ⟨Q, hdegree, hcompact,
    hcount.trans (polynomial_zero_components_encard_le_minima Q hcompact none)⟩

end Papers.TbsNeuralCausalPi

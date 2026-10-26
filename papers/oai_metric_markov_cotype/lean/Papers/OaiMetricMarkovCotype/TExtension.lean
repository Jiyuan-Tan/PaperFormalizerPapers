module
public import Papers.OaiMetricMarkovCotype.Helpers.HilbertMarkov
public import Papers.OaiMetricMarkovCotype.Helpers.EllOneDual
public import Papers.OaiMetricMarkovCotype.TMain

/-! # Conditional Lipschitz extension from Hilbert spaces to real ℓ₁

The universal extension result explicitly takes the disclosed Mendel–Naor gate.
-/

@[expose] public section

noncomputable section
namespace Papers.OaiMetricMarkovCotype

universe u

-- @env: S4
variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]
-- @realizes \mathcal H(real inner product space, completed by HilbertSource)

-- @node: ass:extension-hilbert-source
/-- For [a real inner product space 𝓗](hyp:𝓗), [the Hilbert source condition](goal)
means that every Cauchy sequence in the space converges. -/
def HilbertSource (𝓗 : Type u) [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] : Prop :=
  CompleteSpace 𝓗

-- @node: ass:extension-subset
/-- For [a subset S of the source space](hyp:S), [the extension domain condition](goal)
requires only that S be contained in the whole source space, so every subset,
including the empty subset, qualifies. -/
def ExtensionDomain {𝓗 : Type u} (S : Set 𝓗) : Prop :=
  S ⊆ Set.univ -- @realizes S(arbitrary subset, including the empty subset)

-- @node: ass:extension-map
/-- For a subset of [a real inner product space 𝓗](hyp:𝓗) and [a map f from
that subset to real ℓ₁](hyp:f), [the Lipschitz condition](goal) means that there
exists a finite nonnegative constant bounding every output distance by that
constant times the corresponding input distance. -/
def LipschitzIntoEllOne {S : Set 𝓗} (f : S → RealEllOne) : Prop :=
  ∃ L : NNReal, LipschitzWith L f -- @realizes f(Lipschitz map on the subset into real ell one)

/-- If [the real inner product space is complete](hyp:_h_hilbert), then
[it has Markov type two with constant one](goal). -/
-- @node: hasMarkovTypeTwo_hilbert
lemma hasMarkovTypeTwo_hilbert (_h_hilbert : HilbertSource 𝓗) :
    HasMarkovTypeTwo 𝓗 1 := by
  refine ⟨by norm_num, ?_⟩
  intro n t _ _ π A hπ hA hrev u
  simpa only [one_pow, one_mul] using
    hilbert_finite_chain_markov_type_bound π A hπ hA hrev u t

/-- [Real ℓ₁ is linearly isometric to the continuous dual of the real sequences
that converge to zero, equipped with the supremum norm](goal).

This identification is proved on the paper side rather than borrowed from the
Mendel–Naor extension theorem. -/
-- @node: realEllOne_isDual_cZero
lemma realEllOne_isDual_cZero :
    Nonempty (RealEllOne ≃ₗᵢ[ℝ] StrongDual ℝ (ZeroAtInftyContinuousMap ℕ ℝ)) := by
  exact ⟨LinearIsometryEquiv.ofSurjective ellOneDualIsometry ellOneDualIsometry_surjective⟩

-- @node: thm:extension
/-- Assuming [the Mendel–Naor extension principle for dual Banach targets](hyp:h_of_gate),
[there is a universal finite nonnegative factor K such that every Lipschitz map
from any subset of any real Hilbert space into real ℓ₁ extends to the whole
Hilbert space, agrees with the original map on its domain, and has Lipschitz
constant at most K times the original Lipschitz constant](goal). -/
theorem lipschitz_extension_hilbert_to_ellOne
    (h_of_gate : MendelNaorExtension.{u}) :
    ∃ K : ℝ, 0 ≤ K ∧ -- @realizes K(universal finite nonnegative real factor)
      ∀ (𝓗 : Type u) [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗],
        HilbertSource 𝓗 →
        ∀ (S : Set 𝓗), ExtensionDomain S →
        ∀ f : S → RealEllOne, LipschitzIntoEllOne f →
        ∃ F : 𝓗 → RealEllOne, -- @realizes F(extension on the entire source Hilbert space)
          (∀ x : S, F x = f x) ∧ lipConst F ≤ ENNReal.ofReal K * lipConst f := by
  obtain ⟨K₀, hK₀, h_extend⟩ := h_of_gate
  have h_extend := h_extend realEllOne_isDual_cZero
  have hC : 0 < 12 * Real.sqrt 21 := by positivity
  refine ⟨K₀ * 1 * (12 * Real.sqrt 21), mul_nonneg (mul_nonneg hK₀ (by norm_num)) hC.le, ?_⟩
  intro 𝓗 _ _ h_hilbert S _ f hf
  let : CompleteSpace 𝓗 := h_hilbert
  exact h_extend 𝓗 1 (12 * Real.sqrt 21) (by norm_num)
    (hasMarkovTypeTwo_hilbert h_hilbert) hC hasMetricMarkovCotypeTwo_realEllOne S f hf

end Papers.OaiMetricMarkovCotype

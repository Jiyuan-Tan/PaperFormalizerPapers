module
public import Papers.OaiGraphDecompositionsIntegral.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-! # Quantities used in the star-forest proof

These concrete formulas also record the local meanings of the paper's symbols.
No estimates about these quantities are assumed.
-/

@[expose] public section

open Causalean.Experimentation.DesignBased

namespace Papers.OaiGraphDecompositionsIntegral

variable {V : Type} [Fintype V]

/-- For [a graph J](hyp:J) and [a host order n](hyp:n), [the star threshold q](goal)
is the expectation threshold for containing J in a host with n vertices.
@realizes q_J(abbreviation q(J;n), with positivity derived in the edged case) -/
noncomputable def starQ (J : SimpleGraph V) (n : ℕ) : ℝ := expectationThreshold J n

/-- For [a graph J](hyp:J) [that is a star forest](hyp:_hstar) and
[a leaf count ell](hyp:ell) [of at least one](hyp:_hell), [the star multiplicity](goal)
is the number of connected components with ell plus one vertices.
@realizes \ell(positive natural leaf count)
@realizes m_\ell(number of components with ell leaves) -/
noncomputable def starMultiplicity (J : SimpleGraph V) (_hstar : IsStarForest J)
    (ell : ℕ) (_hell : 1 ≤ ell) : ℕ := by
  classical
  exact (Finset.univ.filter
    (fun C : J.ConnectedComponent => C.supp.toFinset.card = ell + 1)).card

/-- For [a host order n](hyp:n), [a leaf count ell](hyp:ell), and
[a component count m](hyp:m), [the star copy counting bound](goal) is
n raised to the exponent m times the sum of ell and one, divided by the product
of ell factorial raised to m and m factorial.
@realizes C_\ell(counting formula n^(m(ell+1))/((ell!)^m m!)) -/
noncomputable def starCopyCountBound (n ell m : ℕ) : ℝ :=
  (n : ℝ) ^ (m * (ell + 1)) / ((ell.factorial : ℝ) ^ m * m.factorial)

/-- For [a host order n](hyp:n), [the available leaf count](goal) is the integer
part of n divided by three.
@realizes b'(available-leaf bound floor(n/3)) -/
def availableLeaves (n : ℕ) : ℕ := n / 3

/-- For [a number of trials b](hyp:b) and [a success parameter p](hyp:p),
[the binomial design](goal) is the joint law of b independent binary trials,
with p clamped to the unit interval as their success probability.
@realizes \Bin(binomial count as the number of successes among b independent bits) -/
noncomputable def binomialDesign (b : ℕ) (p : ℝ) : FiniteDesign (Fin b → Bool) :=
  productMeasure (Fin b) p

/-- For [a host order n](hyp:n), [a trial success parameter p](hyp:p), and
[a required number of leaves ell](hyp:ell), [the star trial success probability](goal)
is the probability of at least ell successes among the available leaf trials.
@realizes u_\ell(probability Bin(floor(n/3),p) is at least ell) -/
noncomputable def starTrialSuccess (n : ℕ) (p : ℝ) (ell : ℕ) : ℝ := by
  classical
  exact (binomialDesign (availableLeaves n) p).Pr (fun z => ell ≤ (toFinset' z).card)

/-- For [a host order n](hyp:n) and [a success parameter p](hyp:p),
[the star binomial mean](goal) is the available leaf count multiplied by p.
@realizes \mu(binomial mean b' p) -/
def starBinomialMean (n : ℕ) (p : ℝ) : ℝ := (availableLeaves n : ℝ) * p

/-- Under [a measure law](hyp:law), [the expected trial count](goal) of
[a natural-valued random trial count T](hyp:T) is its nonnegative integral,
allowing an infinite expectation.
@realizes \E(expectation under a specified probability law)
@realizes T(natural-valued random total count of center trials, including failures) -/
noncomputable def expectedTrialCount {Ω : Type} [MeasurableSpace Ω]
    (law : MeasureTheory.Measure Ω) (T : Ω → ℕ) : ENNReal :=
  ∫⁻ ω, (T ω : ENNReal) ∂law

end Papers.OaiGraphDecompositionsIntegral

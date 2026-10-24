module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.BigOperators.Field

/-! Leading terms of the finite cycle products in the forest-state argument. -/

public section

namespace OaiPairedStatesHamiltonian

open Filter Topology
open scoped BigOperators

-- @node: exp_weight_gap_tendsto
/-- [As a nonzero real scale approaches zero, the difference between the
exponentials of the scale times two real weights, divided by the scale,
converges to the first weight minus the second](goal). -/
lemma exp_weight_gap_tendsto (a b : ℝ) :
    Tendsto (fun x : ℝ => (Real.exp (x * a) - Real.exp (x * b)) / x)
      (𝓝[≠] 0) (𝓝 (a - b)) := by
  have ha := (Real.hasDerivAt_exp (0 * a)).comp 0 ((hasDerivAt_id 0).mul_const a)
  have hb := (Real.hasDerivAt_exp (0 * b)).comp 0 ((hasDerivAt_id 0).mul_const b)
  simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using (ha.sub hb).tendsto_slope_zero

-- @node: cycle_product_leading_term
/-- [For a finite family of pairs of real weights, the product of their scaled
exponential differences, divided by the scale raised to the number of pairs,
converges to the product of the weight differences as the nonzero real scale
approaches zero](goal). -/
lemma cycle_product_leading_term {ι : Type*} (s : Finset ι) (a b : ι → ℝ) :
    Tendsto (fun x : ℝ =>
      (∏ i ∈ s, (Real.exp (x * a i) - Real.exp (x * b i))) / x ^ s.card)
      (𝓝[≠] 0) (𝓝 (∏ i ∈ s, (a i - b i))) := by
  simpa only [Finset.prod_div_distrib, Finset.prod_const] using
    tendsto_finsetProd s (fun i _ => exp_weight_gap_tendsto (a i) (b i))

-- @node: leading_term_at_lower_order
/-- Suppose [the lower nonnegative integer order is at most the upper
order](hyp:hmn) and [a real function divided by the scale to the upper order
converges to a real coefficient as the nonzero scale approaches zero](hyp:hf).
Then [division by the scale to the lower order gives a limit equal to that
coefficient when the orders coincide, and zero otherwise](goal). -/
lemma leading_term_at_lower_order (f : ℝ → ℝ) (k : ℝ) (m n : ℕ)
    (hmn : m ≤ n)
    (hf : Tendsto (fun x => f x / x ^ n) (𝓝[≠] 0) (𝓝 k)) :
    Tendsto (fun x => f x / x ^ m) (𝓝[≠] 0)
      (𝓝 (if n = m then k else 0)) := by
  by_cases h : n = m
  · subst n
    simpa using hf
  · have hp : Tendsto (fun x : ℝ => x ^ (n - m)) (𝓝[≠] 0) (𝓝 0) := by
      simpa [Nat.ne_of_gt (show 0 < n - m by omega)] using
        (tendsto_id.mono_left
          (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)).pow (n - m)
    have heq : (fun x => f x / x ^ m) =ᶠ[𝓝[≠] 0]
        (fun x => (f x / x ^ n) * x ^ (n - m)) := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hx' : x ≠ 0 := hx
      have hn : n = m + (n - m) := by omega
      rw [show x ^ n = x ^ m * x ^ (n - m) by rw [← pow_add, ← hn]]
      field_simp
    simpa [h] using (hf.mul hp).congr' heq.symm

-- @node: minimum_order_phase_sum_tendsto
/-- Suppose [each order in a finite family is at least a common nonnegative
integer order](hyp:hm) and [each real function divided by the scale to its own
order converges to its real coefficient as the nonzero scale approaches
zero](hyp:hf). Then [the sum of these functions weighted by powers of a common
complex number, divided by the scale to the common order, converges to that
complex number to the common order times the sum of coefficients whose orders
equal the common order](goal). -/
lemma minimum_order_phase_sum_tendsto {γ : Type*} (s : Finset γ) (z : ℂ)
    (n : γ → ℕ) (f : γ → ℝ → ℝ) (k : γ → ℝ) (m : ℕ)
    (hm : ∀ g ∈ s, m ≤ n g)
    (hf : ∀ g ∈ s,
      Tendsto (fun x => f g x / x ^ n g) (𝓝[≠] 0) (𝓝 (k g))) :
    Tendsto (fun x : ℝ =>
      (∑ g ∈ s, z ^ n g * (f g x : ℂ)) / (x : ℂ) ^ m)
      (𝓝[≠] 0)
      (𝓝 (z ^ m * ((∑ g ∈ s with n g = m, k g : ℝ) : ℂ))) := by
  classical
  have hterm (g : γ) (hg : g ∈ s) :
      Tendsto (fun x : ℝ => z ^ n g * ((f g x / x ^ m : ℝ) : ℂ))
        (𝓝[≠] 0) (𝓝 (if n g = m then z ^ m * (k g : ℂ) else 0)) := by
    have h := (Complex.continuous_ofReal.tendsto _).comp
      (leading_term_at_lower_order (f g) (k g) m (n g) (hm g hg) (hf g hg))
    have ht := h.const_mul (z ^ n g)
    by_cases he : n g = m
    · simpa [he, Function.comp_def] using ht
    · simpa [he, Function.comp_def] using ht
  have hsum := tendsto_finsetSum s hterm
  have hfun (x : ℝ) :
      (∑ g ∈ s, z ^ n g * (f g x : ℂ)) / (x : ℂ) ^ m =
        ∑ g ∈ s, z ^ n g * ((f g x / x ^ m : ℝ) : ℂ) := by
    simp only [Finset.sum_div, Complex.ofReal_div, Complex.ofReal_pow, mul_div_assoc]
  simp_rw [← hfun] at hsum
  simpa only [← Finset.sum_filter, ← Finset.mul_sum, ← Complex.ofReal_sum] using hsum

-- @node: exists_nonzero_minimum_order_phase_sum
/-- Suppose [a finite family is nonempty](hyp:hs), [the common complex weight
is nonzero](hyp:hz), [every leading real coefficient is positive](hyp:hk), and
[each real function divided by the scale to its nonnegative integer order
converges to its coefficient as the nonzero scale approaches zero](hyp:hf).
Then [at some real scale, the sum of these functions weighted by the complex
weight raised to their respective orders is nonzero](goal). -/
lemma exists_nonzero_minimum_order_phase_sum {γ : Type*} (s : Finset γ)
    (hs : s.Nonempty) (z : ℂ) (hz : z ≠ 0) (n : γ → ℕ) (f : γ → ℝ → ℝ) (k : γ → ℝ)
    (hk : ∀ g ∈ s, 0 < k g)
    (hf : ∀ g ∈ s,
      Tendsto (fun x => f g x / x ^ n g) (𝓝[≠] 0) (𝓝 (k g))) :
    ∃ x : ℝ, (∑ g ∈ s, z ^ n g * (f g x : ℂ)) ≠ 0 := by
  classical
  obtain ⟨g, hg, hmin⟩ := Finset.exists_min_image s n hs
  have hfilter : (s.filter (fun h => n h = n g)).Nonempty :=
    ⟨g, Finset.mem_filter.mpr ⟨hg, rfl⟩⟩
  have hpositive : 0 < ∑ h ∈ s with n h = n g, k h :=
    Finset.sum_pos (fun h hh => hk h (Finset.mem_filter.mp hh).1) hfilter
  have hne : z ^ n g * ((∑ h ∈ s with n h = n g, k h : ℝ) : ℂ) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hz)
      (Complex.ofReal_ne_zero.mpr (ne_of_gt hpositive))
  have hlim := minimum_order_phase_sum_tendsto s z n f k (n g) hmin hf
  obtain ⟨x, hx⟩ := (hlim.eventually (eventually_ne_nhds hne)).exists
  refine ⟨x, ?_⟩
  intro heq
  exact hx (by rw [heq, zero_div])

-- @node: exists_nonzero_exp_cycle_sum
/-- Suppose [the finite family of groups is nonempty](hyp:hs), [the common
complex weight is nonzero](hyp:hz), and [in every cycle of every group the first
real weight strictly exceeds the second](hyp:hgap). Then [at some real scale,
the sum over groups of the complex weight raised to the number of cycles,
times the exponential of the scaled group weight, times the product of the
cycles' scaled exponential differences, is nonzero](goal). -/
lemma exists_nonzero_exp_cycle_sum {γ ι : Type*} (s : Finset γ) (hs : s.Nonempty)
    (cycles : γ → Finset ι) (a b : γ → ι → ℝ) (w : γ → ℝ)
    (z : ℂ) (hz : z ≠ 0)
    (hgap : ∀ g ∈ s, ∀ i ∈ cycles g, b g i < a g i) :
    ∃ x : ℝ, (∑ g ∈ s, z ^ (cycles g).card *
      ((Real.exp (x * w g) *
        ∏ i ∈ cycles g, (Real.exp (x * a g i) - Real.exp (x * b g i)) : ℝ) : ℂ)) ≠ 0 := by
  apply exists_nonzero_minimum_order_phase_sum s hs z hz
    (fun g => (cycles g).card)
    (fun g x => Real.exp (x * w g) *
      ∏ i ∈ cycles g, (Real.exp (x * a g i) - Real.exp (x * b g i)))
    (fun g => ∏ i ∈ cycles g, (a g i - b g i))
  · intro g hg
    exact Finset.prod_pos (fun i hi => sub_pos.mpr (hgap g hg i hi))
  · intro g hg
    have hexp : Tendsto (fun x : ℝ => Real.exp (x * w g)) (𝓝[≠] 0) (𝓝 1) := by
      have hc : ContinuousAt (fun x : ℝ => Real.exp (x * w g)) 0 := by fun_prop
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    simpa only [one_mul, mul_div_assoc] using
      hexp.mul (cycle_product_leading_term (cycles g) (a g) (b g))

end OaiPairedStatesHamiltonian

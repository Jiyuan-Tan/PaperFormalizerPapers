module
public import Papers.OaiGraphDecompositionsIntegral.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Deterministic quantities in the assembly and layering arguments -/

@[expose] public section

namespace Papers.OaiGraphDecompositionsIntegral

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The [assembly splitting factor](goal) is the constant 1000.

@realizes M(absolute degeneracy splitting factor 1000) -/
def assemblySplittingFactor : ℕ := 1000

/-- The [assembly block count](goal) is the constant 1000.

@realizes B(absolute vertex-block count 1000) -/
def assemblyBlockCount : ℕ := 1000

/-- For [a graph H](hyp:H) and [a host size n](hyp:n), the [initial high-degree
set](goal) consists of the vertices of H whose degrees exceed the square root of n.

@realizes Y_0(initial set of vertices of degree greater than sqrt n) -/
noncomputable def initialHighDegreeSet (H : SimpleGraph V) (n : ℕ) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => Real.sqrt n < (H.degree v : ℝ))

/-- For [a vertex set Y](hyp:Y) and [an initial vertex set Y₀](hyp:Y₀), the
[added vertex count](goal) is the number of vertices in Y that are absent from Y₀.

@realizes a(number of vertices added to Y_0 during closure) -/
def addedVertexCount (Y Y₀ : Finset V) : ℕ := (Y \ Y₀).card

/-- For [a host size n](hyp:n) and [a layer count t](hyp:t) [that is positive](hyp:_ht),
the [layer slack](goal) is the integer part of n divided by four times t.

@realizes b(bin slack floor(n/(4t)))
@realizes t(positive count of independent-set layers) -/
def layerSlack (n t : ℕ) (_ht : 0 < t) : ℕ := n / (4 * t)

/-- For [a finite set U of host vertices](hyp:U), the [Hall test size](goal)
is the number of vertices in U.

@realizes u(cardinality of the locally tested Hall set U) -/
def hallTestSize {n : ℕ} (U : Finset (Fin n)) : ℕ := U.card

/-- For [a bin of host vertices](hyp:bin), [a test set U](hyp:U), and [a
candidate forbidden set W](hyp:W), the [Hall forbidden-set condition](goal)
requires that [U is nonempty](step:1), [W is contained in the bin](step:2),
and [W has exactly one fewer vertex than U](step:3).

@realizes W(forbidden candidates inside the current bin, one fewer than U) -/
def HallForbiddenSet {n : ℕ} (bin U W : Finset (Fin n)) : Prop :=
  U.Nonempty ∧ W ⊆ bin ∧ W.card + 1 = U.card

/-- For [a first embedding cutoff N₁](hyp:N₁), [a second embedding cutoff N₂](hyp:N₂),
[a third embedding cutoff N₃](hyp:N₃), and [a proposed assembly cutoff n₀](hyp:n₀),
the [assembly cutoff condition](goal) requires [n₀ to be at least two](step:1),
[at least N₁](step:2), [at least N₂](step:3), and [at least N₃](step:4), and
[for every n at least n₀, eight times the natural logarithm of n divided by
the natural logarithm of two, multiplied by the square root of n, to be at
most n to the power two thirds; that power to be at most n/4; and twice the
ceiling of n divided by the assembly block count to be at most n/100](step:5).

@realizes n_0(absolute assembly cutoff, at least two and above all embedding cutoffs) -/
def AssemblyCutoff (N₁ N₂ N₃ n₀ : ℕ) : Prop :=
  2 ≤ n₀ ∧ N₁ ≤ n₀ ∧ N₂ ≤ n₀ ∧ N₃ ≤ n₀ ∧
  ∀ n : ℕ, n₀ ≤ n →
    (8 * naturalLog n / naturalLog 2) * Real.sqrt n ≤ (n : ℝ) ^ ((2 : ℝ) / 3) ∧
    (n : ℝ) ^ ((2 : ℝ) / 3) ≤ (n : ℝ) / 4 ∧
    (2 : ℝ) * (⌈(n : ℝ) / assemblyBlockCount⌉ : ℤ) ≤ (n : ℝ) / 100

/-- [There exists a cutoff at least two and at least N₁, N₂, and N₃, beyond
which eight times the natural logarithm of n divided by the natural logarithm
of two, multiplied by the square root of n, is at most n to the power two
thirds, that power is at most n/4, and twice the ceiling of n divided by the
assembly block count is at most n/100](goal). -/
-- @node: assembly_cutoff_exists
lemma assembly_cutoff_exists (N₁ N₂ N₃ : ℕ) :
    ∃ n₀ : ℕ, AssemblyCutoff N₁ N₂ N₃ n₀ := by
  have hlog₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : ∀ᶠ x : ℝ in Filter.atTop,
      Real.log x / x ^ ((1 : ℝ) / 6) ≤ Real.log 2 / 8 :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 6)).tendsto_div_nhds_zero
      |>.eventually_le_const (by positivity)
  have hpow : ∀ᶠ x : ℝ in Filter.atTop, 4 ≤ x ^ ((1 : ℝ) / 3) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).eventually_ge_atTop 4
  have hreal : ∀ᶠ x : ℝ in Filter.atTop,
      (8 * Real.log x / Real.log 2) * Real.sqrt x ≤ x ^ ((2 : ℝ) / 3) ∧
      x ^ ((2 : ℝ) / 3) ≤ x / 4 ∧
      (2 : ℝ) * (⌈x / assemblyBlockCount⌉ : ℤ) ≤ x / 100 := by
    filter_upwards [hlog, hpow, Filter.eventually_ge_atTop (250 : ℝ)] with x hl hp hx
    have hxpos : 0 < x := by linarith
    have hsmall : 8 * Real.log x / Real.log 2 ≤ x ^ ((1 : ℝ) / 6) := by
      have := (div_le_iff₀ (Real.rpow_pos_of_pos hxpos _)).mp hl
      apply (div_le_iff₀ hlog₂).mpr
      nlinarith
    have hsum : x ^ ((1 : ℝ) / 6) * Real.sqrt x = x ^ ((2 : ℝ) / 3) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hxpos]
      norm_num
    have hprod : x ^ ((2 : ℝ) / 3) * x ^ ((1 : ℝ) / 3) = x := by
      rw [← Real.rpow_add hxpos]
      norm_num
    refine ⟨?_, ?_, ?_⟩
    · calc
        (8 * Real.log x / Real.log 2) * Real.sqrt x ≤
            x ^ ((1 : ℝ) / 6) * Real.sqrt x :=
          mul_le_mul_of_nonneg_right hsmall (Real.sqrt_nonneg _)
        _ = _ := hsum
    · have hnonneg : 0 ≤ x ^ ((2 : ℝ) / 3) := Real.rpow_nonneg hxpos.le _
      nlinarith
    · have hc := Int.ceil_lt_add_one (x / assemblyBlockCount)
      norm_num [assemblyBlockCount] at hc ⊢
      linarith
  have hnat := (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun n : ℕ => (n : ℝ))
      Filter.atTop Filter.atTop).eventually hreal
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hnat
  refine ⟨max 2 (max N₁ (max N₂ (max N₃ N))), ?_⟩
  refine ⟨by omega, by omega, by omega, by omega, ?_⟩
  intro n hn
  exact hN n (by omega)

end Papers.OaiGraphDecompositionsIntegral

module
public import Papers.TbsNeuralCausalPi.Helpers.StructuralScalarExtension
/-! # Exact binary simplex extensions

A binary propensity is determined by one coordinate. Its one-norm distance
is twice the distance of that coordinate, so scalar extension and interval
clipping preserve the original vector Lipschitz constant, including at zeros.
-/
public section
namespace Papers.TbsNeuralCausalPi
open scoped NNReal

-- @node: binary_simplex_second_coordinate
/-- If [p is a probability vector with two coordinates](hyp:hp), then
[its second coordinate equals one minus its first coordinate](goal). -/
lemma binary_simplex_second_coordinate {p : L1Vec 2}
    (hp : p.ofLp ∈ probabilitySimplex 2) : p.ofLp 1 = 1 - p.ofLp 0 := by
  have h := hp.2
  simp only [Fin.sum_univ_two] at h
  linarith

-- @node: binary_simplex_dist
/-- If [p is a probability vector with two coordinates](hyp:hp) and [q is
also a probability vector with two coordinates](hyp:hq), then [their one-norm
distance is twice the absolute difference
between their first coordinates](goal). -/
lemma binary_simplex_dist {p q : L1Vec 2}
    (hp : p.ofLp ∈ probabilitySimplex 2) (hq : q.ofLp ∈ probabilitySimplex 2) :
    dist p q = 2 * |p.ofLp 0 - q.ofLp 0| := by
  rw [PiLp.dist_eq_of_L1, Fin.sum_univ_two]
  simp only [Real.dist_eq, binary_simplex_second_coordinate hp,
    binary_simplex_second_coordinate hq]
  rw [show 1 - p.ofLp 0 - (1 - q.ofLp 0) = -(p.ofLp 0 - q.ofLp 0) by ring,
    abs_neg]
  ring

-- @node: structural_binary_simplex_extension
/-- If [the output dimension is two](hyp:hd), [f is L-Lipschitz on s in
the one-norm](hyp:hf), and [f takes values in the closed probability simplex
on s](hyp:hs), then [there is a globally L-Lipschitz extension that is
probability-valued everywhere and agrees with f on s](goal).

Zero probability coordinates are allowed. -/
lemma structural_binary_simplex_extension {X : Type*} [PseudoMetricSpace X]
    {d : ℕ} (hd : d = 2) {s : Set X} {f : X → L1Vec d} {L : ℝ≥0}
    (hf : LipschitzOnWith L f s)
    (hs : ∀ x ∈ s, (f x).ofLp ∈ probabilitySimplex d) :
    ∃ g : X → L1Vec d, LipschitzWith L g ∧
      (∀ x, (g x).ofLp ∈ probabilitySimplex d) ∧ Set.EqOn g f s := by
  subst d
  have hc : LipschitzOnWith (L / 2) (fun x => (f x).ofLp 0) s := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have h := hf.dist_le_mul x hx y hy
    rw [binary_simplex_dist (hs x hx) (hs y hy)] at h
    simp only [Real.dist_eq, NNReal.coe_div, NNReal.coe_ofNat]
    nlinarith
  obtain ⟨a, ha, heq⟩ := hc.extend_real
  let r := fun x => max 0 (min (a x) 1)
  have hr : LipschitzWith (L / 2) r := (ha.min_const 1).const_max 0
  have hr0 (x) : 0 ≤ r x := le_max_left _ _
  have hr1 (x) : r x ≤ 1 := max_le (by norm_num) (min_le_right _ _)
  let g := fun x => WithLp.toLp 1 (fun j : Fin 2 => if j = 0 then r x else 1 - r x)
  have hg (x) : (g x).ofLp ∈ probabilitySimplex 2 := by
    constructor
    · intro j
      fin_cases j <;> simp [g, hr0, sub_nonneg.mpr (hr1 x)]
    · simp [g, Fin.sum_univ_two]
  refine ⟨g, ?_, hg, ?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [binary_simplex_dist (hg x) (hg y)]
    have h := hr.dist_le_mul x y
    simp only [Real.dist_eq, NNReal.coe_div, NNReal.coe_ofNat] at h
    change 2 * |r x - r y| ≤ _
    nlinarith
  · intro x hx
    have h0 : r x = (f x).ofLp 0 := by
      dsimp only [r]
      rw [← heq hx]
      have hb : (f x).ofLp 0 ≤ 1 := by
        have hsum := binary_simplex_second_coordinate (hs x hx)
        linarith [(hs x hx).1 1]
      rw [min_eq_left hb, max_eq_right ((hs x hx).1 0)]
    apply PiLp.ext
    intro j
    fin_cases j
    · simpa [g] using h0
    · simpa [g, h0] using (binary_simplex_second_coordinate (hs x hx)).symm

-- @node: canonical_binary_structural_extension
/-- In [a canonical structural causal model M](hyp:M), consider [a node
i](hyp:i) [with two categorical outcomes](hyp:hi) and [a nonnegative
Lipschitz bound L](hyp:L). If [the node's mechanism is L-Lipschitz on its
full structural input domain](hyp:hf), then [there is a globally L-Lipschitz
extension to the entire ambient input space that takes values in the closed
probability simplex everywhere and agrees with the mechanism on its full
structural input domain](goal). -/
lemma canonical_binary_structural_extension
    {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
    {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
    {C : Fin b → Set (Fin n)}
    (M : CanonicalSCM kind dims dag G C) (i : Fin n) (hi : kind i = Sum.inr 2)
    (L : ℝ≥0) (hf : LipschitzOnWith L (M.f i) (M.domain i none)) :
    ∃ g : Input kind dims dag C i → L1Vec (outputDim (kind i)),
      LipschitzWith L g ∧
      (∀ x, (g x).ofLp ∈ probabilitySimplex (outputDim (kind i))) ∧
      Set.EqOn g (M.f i) (M.domain i none) := by
  have hd : outputDim (kind i) = 2 := congrArg outputDim hi
  apply structural_binary_simplex_extension hd hf
  intro x hx
  have hs := M.simplex i 2 hi x hx.1
  constructor
  · intro j
    exact hs.1 (Fin.cast hd j)
  · exact ((Equiv.sum_comp (finCongr hd.symm) _).symm).trans hs.2

end Papers.TbsNeuralCausalPi

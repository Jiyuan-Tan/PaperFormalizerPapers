module
public import Papers.TbsNeuralCausalPi.Helpers.DeepReLUApprox
public import Papers.TbsNeuralCausalPi.Helpers.ParallelNetworks
/-! # Vector chart approximation for the wide generator

Scalar Yarotsky approximants are widened to one common budget and assembled
in parallel. The coordinate error gives the paper's dimension factor in the
one-norm error.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open scoped NNReal

-- @node: ReLUNet.widen
/-- For [a ReLU network](hyp:q) and [a new width budget at least as large as
its current budget](hyp:hW), [the widened network](goal) uses the same layers,
weights, and biases under the larger budget. -/
def ReLUNet.widen {k o W W' L : ℕ} (q : ReLUNet k o W L)
    (hW : W ≤ W') : ReLUNet k o W' L :=
  { q with widths := fun l hl => (q.widths l hl).trans hW }

-- @node: ReLUNet.widen_eval
/-- When [the new width budget is at least the old one](hyp:hW),
[widening a ReLU network leaves its input-output function unchanged](goal). -/
lemma ReLUNet.widen_eval {k o W W' L : ℕ} (q : ReLUNet k o W L)
    (hW : W ≤ W') : (q.widen hW).eval = q.eval := rfl

-- @node: yarotsky_vector_chart_approx
/-- Assuming [the scalar Yarotsky coordinate approximation result](hyp:hgate),
for [a positive cube dimension](hyp:hd) and a chart [with nonnegative
Lipschitz bound L](hyp:L,hLip), [there exist a positive integer width factor c
and a positive constant A such that every depth at least one admits a parallel
ReLU approximation of width equal to the output dimension times c times the cube
dimension, with coordinate error at most A times depth to the power minus two
over the cube dimension, and total one-norm error at most the output dimension
times that bound](goal). -/
lemma yarotsky_vector_chart_approx
    (hgate : YarotskyCoordinateApprox) {D d : ℕ} (hd : 0 < d)
    {C : Set (L1Vec D)} (f : homeoClass (unitCube d) C)
    (L : ℝ≥0) (hLip : LipschitzWith L f) :
    ∃ c : ℕ, 0 < c ∧ ∃ A : ℝ, 0 < A ∧
      ∀ depth : ℕ, 1 ≤ depth → ∃ q : ReLUNet d D (D * (c * d)) depth,
        (∀ x : unitCube d, ∀ j : Fin D,
          |(f x).val.ofLp j - (q.eval x.val).ofLp j| ≤
            A * (depth : ℝ) ^ (-(2 : ℝ) / d)) ∧
        ∀ x : unitCube d, ‖(f x).val - q.eval x.val‖ ≤
          (D : ℝ) * A * (depth : ℝ) ^ (-(2 : ℝ) / d) := by
  classical
  obtain ⟨widthFactor, _hwidth, hwidthFactor, hgate⟩ := yarotskyCoordinate_chart hgate
  choose A hA hq using hgate D d hd C f L hLip
  let c : Fin D → ℕ := fun _ => widthFactor
  let cmax : ℕ := 1 + ∑ j, c j
  let Amax : ℝ := 1 + ∑ j, A j
  have hcmax : 0 < cmax := by dsimp [cmax]; omega
  have hAmax : 0 < Amax := by
    have hs : 0 ≤ ∑ j, A j := Finset.sum_nonneg (fun j _ => (hA j).le)
    dsimp [Amax]
    linarith
  have hc_le (j : Fin D) : c j ≤ cmax := by
    have h := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => Nat.zero_le (c i))
      (Finset.mem_univ j)
    dsimp [cmax]
    omega
  have hA_le (j : Fin D) : A j ≤ Amax := by
    have h := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => (hA i).le)
      (Finset.mem_univ j)
    dsimp [Amax]
    linarith
  refine ⟨cmax, hcmax, Amax, hAmax, ?_⟩
  intro depth hdepth
  choose q herror using fun j => hq j depth hdepth
  let r : Fin D → ReLUNet d 1 (cmax * d) depth :=
    fun j => (q j).widen (Nat.mul_le_mul_right d (hc_le j))
  obtain ⟨Q, hQ⟩ := relu_parallel_stack_constructed r
  have herr (x : unitCube d) (j : Fin D) :
      |(f x).val.ofLp j - (Q.eval x.val).ofLp j| ≤
        Amax * (depth : ℝ) ^ (-(2 : ℝ) / d) := by
    rw [hQ]
    change |(f x).val.ofLp j - ((q j).eval x.val).ofLp 0| ≤ _
    exact (herror j x).trans (mul_le_mul_of_nonneg_right (hA_le j)
      (Real.rpow_nonneg (Nat.cast_nonneg depth) _))
  refine ⟨Q, herr, ?_⟩
  intro x
  calc
    ‖(f x).val - Q.eval x.val‖ =
        ∑ j : Fin D, |(f x).val.ofLp j - (Q.eval x.val).ofLp j| := by
      simp only [PiLp.norm_eq_of_L1, PiLp.sub_apply, Real.norm_eq_abs]
    _ ≤ ∑ _j : Fin D, Amax * (depth : ℝ) ^ (-(2 : ℝ) / d) :=
      Finset.sum_le_sum (fun j _ => herr x j)
    _ = (D : ℝ) * Amax * (depth : ℝ) ^ (-(2 : ℝ) / d) := by
      simp [mul_assoc]


/-- Assuming [the scalar Yarotsky coordinate approximation result](hyp:hgate),
for [a positive cube dimension](hyp:hd) and a chart [with nonnegative Lipschitz
bound L](hyp:L,hLip), [there is a positive constant A such that every depth at
least one admits a ReLU approximation of width equal to the output dimension
times the universal scalar width factor times the cube dimension, with coordinate
error at most A times depth to the power minus two over the cube dimension and
one-norm error at most the output dimension times that bound](goal). -/
lemma yarotsky_vector_chart_approx_explicit
    (hgate : YarotskyCoordinateApprox) {D d : ℕ} (hd : 0 < d)
    {C : Set (L1Vec D)} (f : homeoClass (unitCube d) C)
    (L : ℝ≥0) (hLip : LipschitzWith L f) :
    ∃ A : ℝ, 0 < A ∧
      ∀ depth : ℕ, 1 ≤ depth → ∃ q : ReLUNet d D (D * (deepFirstWidthFactor * d)) depth,
        (∀ x : unitCube d, ∀ j : Fin D,
          |(f x).val.ofLp j - (q.eval x.val).ofLp j| ≤
            A * (depth : ℝ) ^ (-(2 : ℝ) / d)) ∧
        ∀ x : unitCube d, ‖(f x).val - q.eval x.val‖ ≤
          (D : ℝ) * A * (depth : ℝ) ^ (-(2 : ℝ) / d) := by
  classical
  obtain ⟨widthFactor, hwidth, hwidthFactor, hgate⟩ := yarotskyCoordinate_chart hgate
  subst widthFactor
  choose A hA hq using hgate D d hd C f L hLip
  let Amax : ℝ := 1 + ∑ j, A j
  have hAmax : 0 < Amax := by
    have hs : 0 ≤ ∑ j, A j := Finset.sum_nonneg (fun j _ => (hA j).le)
    dsimp [Amax]
    linarith
  have hA_le (j : Fin D) : A j ≤ Amax := by
    have h := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => (hA i).le)
      (Finset.mem_univ j)
    dsimp [Amax]
    linarith
  refine ⟨Amax, hAmax, ?_⟩
  intro depth hdepth
  choose q herror using fun j => hq j depth hdepth
  obtain ⟨Q, hQ⟩ := relu_parallel_stack_constructed q
  have herr (x : unitCube d) (j : Fin D) :
      |(f x).val.ofLp j - (Q.eval x.val).ofLp j| ≤
        Amax * (depth : ℝ) ^ (-(2 : ℝ) / d) := by
    rw [hQ]
    exact (herror j x).trans (mul_le_mul_of_nonneg_right (hA_le j)
      (Real.rpow_nonneg (Nat.cast_nonneg depth) _))
  refine ⟨Q, herr, ?_⟩
  intro x
  calc
    ‖(f x).val - Q.eval x.val‖ =
        ∑ j : Fin D, |(f x).val.ofLp j - (Q.eval x.val).ofLp j| := by
      simp only [PiLp.norm_eq_of_L1, PiLp.sub_apply, Real.norm_eq_abs]
    _ ≤ ∑ _j : Fin D, Amax * (depth : ℝ) ^ (-(2 : ℝ) / d) :=
      Finset.sum_le_sum (fun j _ => herr x j)
    _ = (D : ℝ) * Amax * (depth : ℝ) ^ (-(2 : ℝ) / d) := by
      simp [mul_assoc]

end Papers.TbsNeuralCausalPi

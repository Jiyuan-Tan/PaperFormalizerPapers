module
public import Papers.TbsNeuralCausalPi.Helpers.BoxReduction
public import Papers.TbsNeuralCausalPi.Helpers.AffineNetworkInputs
public import Papers.TbsNeuralCausalPi.Helpers.WideGeneratorSupport
/-! # Global structural network approximation on a derived box -/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.cdot false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
open MeasureTheory
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)} {C : Fin b → Set (Fin n)}

/-- Given [a canonical causal model M](hyp:M), [a node i](hyp:i), [a ReLU network q
with that node's input and output dimensions](hyp:q), and [a structural input x
at i](hyp:x), [the network output on structural inputs](goal) is obtained by
enumerating x's coordinates as a finite vector and evaluating q on that vector. -/
-- @node: networkOnStructuralInput
def networkOnStructuralInput (M : CanonicalSCM kind dims dag G C) (i : Fin n)
    {W L : ℕ} (q : ReLUNet (structuralInputSize M.toEuclideanSCM i)
      (outputDim (kind i)) W L) (x : Input kind dims dag C i) : L1Vec (outputDim (kind i)) :=
  q.eval (WithLp.toLp 1 (fun j => x.ofLp ((Fintype.equivFin _).symm j)))

-- @node: structuralFiniteCoordinates_dist
/-- [Reindexing two finite input vectors x and y as structural inputs at node i
of model M preserves their sum-of-absolute-differences distance](goal). -/
lemma structuralFiniteCoordinates_dist (M : CanonicalSCM kind dims dag G C) (i : Fin n)
    (x y : L1Vec (structuralInputSize M.toEuclideanSCM i)) :
    dist (structuralFiniteCoordinates M.toEuclideanSCM i x)
      (structuralFiniteCoordinates M.toEuclideanSCM i y) = dist x y := by
  simp only [PiLp.dist_eq_of_L1, structuralFiniteCoordinates, WithLp.ofLp_toLp]
  exact Equiv.sum_comp (Fintype.equivFin
    (Sum (Σ p : {p // p ∈ M.toEuclideanSCM.dag.parents i}, Fin (valueDim (kind p)))
      (Σ j : {j // j ∈ M.toEuclideanSCM.incidence i}, Fin (dims j))))
    (fun j => dist (x.ofLp j) (y.ofLp j))

/-- For [nonnegative Lipschitz and box bounds L and B](hyp:L,B), assume
[every categorical node's number of labels is at most B](hyp:hlabels), [each
structural map is L-Lipschitz on its admissible domain](hyp:hclass), [the
structural Yarotsky approximation assumption holds](hyp:hgate), and [node i has
positive input dimension](hyp:hd). Then [there is a positive constant A such
that every depth parameter at least one admits a ReLU network of width
equal to the output dimension multiplied by the sum of twice the input dimension
and ten, and depth two greater than that parameter, whose coordinate errors
against the truncated mechanism are uniformly at most A times the depth
parameter raised to minus two divided by the input dimension on all admissible
inputs](goal). -/
-- @node: box_structural_vector_approx
lemma box_structural_vector_approx
    (M : CanonicalSCM kind dims dag G C) (L B : ℝ≥0)
    (hlabels : ∀ i k, kind i = Sum.inr k → (k : ℝ) ≤ B)
    (hclass : ∀ i, LipschitzOnWith L (M.f i) (M.domain i))
    (hgate : YarotskyStructuralApprox) (i : Fin n)
    (hd : 0 < structuralInputSize M.toEuclideanSCM i) :
    ∃ A : ℝ, 0 < A ∧ ∀ depth : ℕ, 1 ≤ depth →
      ∃ q : ReLUNet (structuralInputSize M.toEuclideanSCM i)
        (outputDim (kind i))
        (outputDim (kind i) * (2*structuralInputSize M.toEuclideanSCM i+10)) (depth+2),
        ∀ x ∈ M.domain i, ∀ j,
          |((boxTruncatedSCM M B hlabels).f i x).ofLp j -
            (networkOnStructuralInput M i q x).ofLp j| ≤
              A * (depth : ℝ)^(-(2 : ℝ)/structuralInputSize M.toEuclideanSCM i) := by
  classical
  let coord := structuralFiniteCoordinates M.toEuclideanSCM i
  let S := {x | coord x ∈ M.domain i}
  have hscalar (j : Fin (outputDim (kind i))) :
      LipschitzOnWith L (fun x => (M.f i (coord x)).ofLp j) S := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    calc
      _ ≤ dist (M.f i (coord x)) (M.f i (coord y)) := PiLp.dist_apply_le _ _ j
      _ ≤ L * dist (coord x) (coord y) := (hclass i).dist_le_mul _ hx _ hy
      _ = _ := by rw [structuralFiniteCoordinates_dist]
  choose g hg heq using fun j => (hscalar j).extend_real
  choose A hA happ using fun j => yarotsky_scalar_clipped_box hgate hd (g j) L B (hg j)
  let Amax : ℝ := 1 + ∑ j, A j
  have hAmax : 0 < Amax := by
    have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => (hA j).le)
    dsimp [Amax]; linarith
  have hAle (j) : A j ≤ Amax := by
    have := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => (hA j).le)
      (Finset.mem_univ j)
    dsimp [Amax]; linarith
  refine ⟨Amax, hAmax, ?_⟩
  intro depth hdepth
  choose q hq using fun j => happ j depth hdepth
  obtain ⟨Q, hQ⟩ := relu_parallel_stack_constructed q
  refine ⟨Q, ?_⟩
  intro x hx j
  let y : L1Vec (structuralInputSize M.toEuclideanSCM i) :=
    WithLp.toLp 1 (fun r => x.ofLp ((Fintype.equivFin _).symm r))
  have hcoord : coord (coordinateClamp (-(B : ℝ)) B y) = structuralBoxProjection M B i x := by
    apply PiLp.ext
    intro r
    simp only [coord, structuralFiniteCoordinates, coordinateClamp, structuralBoxProjection,
      WithLp.ofLp_toLp, y, CanonicalSCM.toEuclideanSCM, Equiv.symm_apply_apply]
  have hyS : coordinateClamp (-(B : ℝ)) B y ∈ S := by
    change coord _ ∈ M.domain i
    rw [hcoord]
    exact structuralBoxProjection_mem_domain M B hlabels i x hx
  have he : (networkOnStructuralInput M i Q x).ofLp j = ((q j).eval y).ofLp 0 := hQ y j
  rw [he]
  change |(M.f i (structuralBoxProjection M B i x)).ofLp j - _| ≤ _
  rw [← hcoord]
  have hj := heq j hyS
  dsimp only at hj
  rw [hj]
  exact (hq j y).trans (mul_le_mul_of_nonneg_right (hAle j) (by positivity))

/-- If [the coordinate error tolerance eps is nonnegative](hyp:heps), [p is a
probability vector with d coordinates](hyp:hp), [all coordinates of q are
nonnegative](hyp:hq0), [q has positive total mass](hyp:hqpos), and [each coordinate
of q differs from p by at most eps](hyp:herr), [normalizing q by its total mass
gives error at most 2(d + 1)eps in coordinate j](goal). -/
-- @node: structural_normalized_coordinate_error_le_all
lemma structural_normalized_coordinate_error_le_all {d : ℕ} {eps : ℝ}
    {p q : Fin d → ℝ} (heps : 0 ≤ eps) (hp : p ∈ probabilitySimplex d)
    (hq0 : ∀ j, 0 ≤ q j) (hqpos : 0 < ∑ j, q j)
    (herr : ∀ j, |q j-p j| ≤ eps) (j : Fin d) :
    |q j/(∑ l, q l)-p j| ≤ 2*(d+1)*eps := by
  by_cases hsmall : (d : ℝ)*eps ≤ 1/2
  · exact structural_normalized_coordinate_error_le heps hp herr hsmall j
  · have hnorm := canonical_normalized_mem_simplex q hq0 hqpos
    have hp1 : p j ≤ 1 :=
      (Finset.single_le_sum (fun l _ => hp.1 l) (Finset.mem_univ j)).trans_eq hp.2
    have hq1 : q j/(∑ l, q l) ≤ 1 :=
      (Finset.single_le_sum (fun l _ => hnorm.1 l) (Finset.mem_univ j)).trans_eq hnorm.2
    have hdiff : |q j/(∑ l, q l)-p j| ≤ 1 := abs_le.mpr
      ⟨by linarith [hp.1 j, hnorm.1 j], by linarith [hp.1 j, hnorm.1 j]⟩
    exact hdiff.trans (by nlinarith)

/-- If [the input dimension d is positive](hyp:hd) and [the depth is at least
six](hyp:hdepth), [the depth minus three raised to minus two divided by d is at
most four times the depth raised to that same power](goal). -/
-- @node: structural_reserved_depth_rate_le
lemma structural_reserved_depth_rate_le {d depth : ℕ} (hd : 0 < d) (hdepth : 6 ≤ depth) :
    ((depth-3 : ℕ) : ℝ) ^ (-(2 : ℝ)/d) ≤ 4*(depth : ℝ)^(-(2 : ℝ)/d) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdepthR : (6 : ℝ) ≤ depth := by exact_mod_cast hdepth
  have hsub : ((depth-3 : ℕ) : ℝ) = (depth : ℝ)-3 := by
    rw [Nat.cast_sub (by omega : 3 ≤ depth)]; norm_num
  have hpower : (2 : ℝ)^((2 : ℝ)/d) ≤ 4 := by
    calc
      _ ≤ (2 : ℝ)^(2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num)
        ((div_le_iff₀ (by positivity : (0 : ℝ) < d)).2 (by linarith))
      _ = 4 := by norm_num
  calc
    _ ≤ ((depth : ℝ)/2)^(-(2 : ℝ)/d) := by
      apply Real.rpow_le_rpow_of_nonpos (by positivity)
      · rw [hsub]; linarith
      · exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (Nat.cast_nonneg d)
    _ = (depth : ℝ)^(-(2 : ℝ)/d) * (2 : ℝ)^((2 : ℝ)/d) := by
      rw [Real.div_rpow (Nat.cast_nonneg depth) (by norm_num),
        show -(2 : ℝ)/d = -((2 : ℝ)/d) by ring,
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      simp only [div_inv_eq_mul]
    _ ≤ (depth : ℝ)^(-(2 : ℝ)/d) * 4 :=
      mul_le_mul_of_nonneg_left hpower (by positivity)
    _ = _ := by ring

/-- For [nonnegative Lipschitz and box bounds L and B](hyp:L,B), assume
[every categorical node's number of labels is at most B](hyp:hlabels), [the
model's structural maps are L-Lipschitz on admissible domains](hyp:hclass),
[the structural Yarotsky approximation assumption holds](hyp:hgate), and
[node i has positive input dimension](hyp:hd). Then [there is a positive constant
A such that every depth parameter at least one admits a ReLU network of depth
three greater than that parameter and width the larger of the output dimension
and the output dimension multiplied by the sum of twice the input dimension
and ten; its categorical outputs are nonnegative with positive total mass, and,
after categorical normalization, its uniform coordinate error against the
truncated mechanism is at most A times the depth parameter raised to minus two
divided by the input dimension](goal). -/
-- @node: box_structural_node_at_depth
lemma box_structural_node_at_depth
    (M : CanonicalSCM kind dims dag G C) (L B : ℝ≥0)
    (hlabels : ∀ i k, kind i = Sum.inr k → (k : ℝ) ≤ B)
    (hclass : M ∈ canonicalClass (domainLipClass M L))
    (hgate : YarotskyStructuralApprox) (i : Fin n)
    (hd : 0 < structuralInputSize M.toEuclideanSCM i) :
    ∃ A : ℝ, 0 < A ∧ ∀ depth : ℕ, 1 ≤ depth →
      ∃ q : ReLUNet (structuralInputSize M.toEuclideanSCM i) (outputDim (kind i))
        (max (outputDim (kind i)*(2*structuralInputSize M.toEuclideanSCM i+10))
          (outputDim (kind i))) (depth+3),
      (∀ k, kind i = Sum.inr k → ∀ x ∈ M.domain i,
        (∀ j, 0 ≤ (networkOnStructuralInput M i q x).ofLp j) ∧
          0 < ∑ j, (networkOnStructuralInput M i q x).ofLp j) ∧
      supDistOn (M.domain i) ((boxTruncatedSCM M B hlabels).f i)
        (fun x => if (kind i).isRight then WithLp.toLp 1
          (fun j => (networkOnStructuralInput M i q x).ofLp j /
            ∑ l, (networkOnStructuralInput M i q x).ofLp l)
          else networkOnStructuralInput M i q x) ≤
        ENNReal.ofReal (A*(depth : ℝ)^(-(2 : ℝ)/structuralInputSize M.toEuclideanSCM i)) := by
  classical
  obtain ⟨A, hA, happ⟩ := box_structural_vector_approx M L B hlabels hclass hgate i hd
  refine ⟨2*(outputDim (kind i)+1)*A, by positivity, ?_⟩
  intro depth hdepth
  obtain ⟨q, hq⟩ := happ depth hdepth
  let eps := A*(depth : ℝ)^(-(2 : ℝ)/structuralInputSize M.toEuclideanSCM i)
  have heps : 0 < eps := by dsimp [eps]; positivity
  by_cases hcat : (kind i).isRight = false
  · obtain ⟨d, hi⟩ : ∃ d, kind i = Sum.inl d := by
      cases h : kind i <;> simp_all
    obtain ⟨r, hr⟩ := relu_pad_one q (by omega)
    let Q : ReLUNet _ _
        (max (outputDim (kind i)*(2*structuralInputSize M.toEuclideanSCM i+10))
          (outputDim (kind i))) (depth+3) := r.widen (le_max_left _ _)
    have hQ (x) : networkOnStructuralInput M i Q x = networkOnStructuralInput M i q x := by
      dsimp only [networkOnStructuralInput, Q]
      rw [ReLUNet.widen_eval, hr]
    refine ⟨Q, ?_, ?_⟩
    · intro k hk; rw [hi] at hk; cases hk
    · simp only [hcat, Bool.false_eq_true, if_false]
      apply iSup_le
      intro x
      apply ENNReal.ofReal_le_ofReal
      apply (pi_norm_le_iff_of_nonneg (by positivity)).2
      intro j
      simp only [PiLp.sub_apply, Real.norm_eq_abs, hQ]
      have herr := hq x.val x.property j
      exact herr.trans (by dsimp [eps] at heps ⊢; nlinarith)
  · obtain ⟨k, hi⟩ : ∃ k, kind i = Sum.inr k := by
      cases h : kind i <;> simp_all
    have hout : 0 < outputDim (kind i) := by
      simpa only [hi, outputDim] using M.categoricalPositive i k hi
    obtain ⟨r, hr⟩ := relu_structuralPositiveFloor q eps
    let Q : ReLUNet _ _
        (max (outputDim (kind i)*(2*structuralInputSize M.toEuclideanSCM i+10))
          (outputDim (kind i))) (depth+3) := r
    have hQ (x) : networkOnStructuralInput M i Q x =
        structuralPositiveFloor eps (networkOnStructuralInput M i q x) := by
      dsimp only [networkOnStructuralInput, Q]
      rw [hr]; rfl
    have hmass (x) : (∀ j, 0 ≤ (networkOnStructuralInput M i Q x).ofLp j) ∧
        0 < ∑ j, (networkOnStructuralInput M i Q x).ofLp j := by
      rw [hQ]
      exact structuralPositiveFloor_mass_pos hout heps _
    have hp (x) (hx : x ∈ M.domain i) :
        ((boxTruncatedSCM M B hlabels).f i x).ofLp ∈ probabilitySimplex (outputDim (kind i)) := by
      have h := (boxTruncatedSCM M B hlabels).simplex i k hi x hx.1
      have hdim : outputDim (kind i) = k := congrArg outputDim hi
      constructor
      · intro j
        exact h.1 (Fin.cast hdim j)
      · calc
          _ = ∑ j : Fin k, ((boxTruncatedSCM M B hlabels).f i x).ofLp
              (Fin.cast hdim.symm j) := (Equiv.sum_comp (finCongr hdim.symm) _).symm
          _ = 1 := h.2
    refine ⟨Q, fun _ _ x _ => hmass x, ?_⟩
    simp only [Bool.eq_true_of_not_eq_false hcat, if_true]
    apply iSup_le
    intro x
    apply ENNReal.ofReal_le_ofReal
    apply (pi_norm_le_iff_of_nonneg (by positivity)).2
    intro j
    have herr (j) : |(networkOnStructuralInput M i Q x.val).ofLp j -
        ((boxTruncatedSCM M B hlabels).f i x.val).ofLp j| ≤ eps := by
      rw [hQ]
      exact structuralPositiveFloor_error_le (hp x.val x.property).1
        (fun j => by simpa only [abs_sub_comm] using hq x.val x.property j) j
    have hn := structural_normalized_coordinate_error_le_all heps.le (hp x.val x.property)
      (hmass x.val).1 (hmass x.val).2 herr j
    simpa only [PiLp.sub_apply, WithLp.ofLp_toLp, Real.norm_eq_abs, abs_sub_comm,
      eps, mul_assoc] using hn

-- @node: canonical_simplex_ofLp
/-- If [node i has k categories](hyp:hi) and [x is an admissible structural
input at i](hyp:hx), [the canonical model's structural output at x is a
probability vector indexed by the node's output coordinates](goal). -/
lemma canonical_simplex_ofLp (M : CanonicalSCM kind dims dag G C)
    (i : Fin n) (k : ℕ) (hi : kind i = Sum.inr k)
    (x : Input kind dims dag C i) (hx : x ∈ M.domain i) :
    (M.f i x).ofLp ∈ probabilitySimplex (outputDim (kind i)) := by
  have h := M.simplex i k hi x hx.1
  have hdim : outputDim (kind i) = k := congrArg outputDim hi
  constructor
  · intro j; exact h.1 (Fin.cast hdim j)
  · calc
      _ = ∑ j : Fin k, (M.f i x).ofLp (Fin.cast hdim.symm j) :=
        (Equiv.sum_comp (finCongr hdim.symm) _).symm
      _ = 1 := h.2

/-- For [nonnegative Lipschitz and box bounds L and B](hyp:L,B), assume
[every categorical node's number of labels is at most B](hyp:hlabels), [the
model's structural maps are L-Lipschitz on admissible domains](hyp:hclass),
[the maximum input dimension is positive](hyp:hdin), and [the structural Yarotsky
approximation assumption holds](hyp:hgate). Then [there is a positive constant A
such that every requested depth at least six admits a network for node i of
that depth and width twelve times the maximum input dimension times the maximum
output dimension, with nonnegative categorical outputs of positive mass and,
after categorical normalization, uniform coordinate error against the truncated
mechanism at most A times depth raised to minus two divided by the maximum
input dimension](goal). -/
-- @node: box_structural_node_budget
lemma box_structural_node_budget
    (M : CanonicalSCM kind dims dag G C) (L B : ℝ≥0)
    (hlabels : ∀ i k, kind i = Sum.inr k → (k : ℝ) ≤ B)
    (hclass : M ∈ canonicalClass (domainLipClass M L))
    (hdin : 0 < maxInDim M.toEuclideanSCM)
    (hgate : YarotskyStructuralApprox) (i : Fin n) :
    ∃ A : ℝ, 0 < A ∧ ∀ L0 : ℕ, 6 ≤ L0 →
      ∃ q : ReLUNet (structuralInputSize M.toEuclideanSCM i) (outputDim (kind i))
        (12*maxInDim M.toEuclideanSCM*maxOutDim M.toEuclideanSCM) L0,
      (∀ k, kind i = Sum.inr k → ∀ x ∈ M.domain i,
        (∀ j, 0 ≤ (networkOnStructuralInput M i q x).ofLp j) ∧
          0 < ∑ j, (networkOnStructuralInput M i q x).ofLp j) ∧
      supDistOn (M.domain i) ((boxTruncatedSCM M B hlabels).f i)
        (fun x => if (kind i).isRight then WithLp.toLp 1
          (fun j => (networkOnStructuralInput M i q x).ofLp j /
            ∑ l, (networkOnStructuralInput M i q x).ofLp l)
          else networkOnStructuralInput M i q x) ≤
        ENNReal.ofReal (A*(L0 : ℝ)^(-(2 : ℝ)/maxInDim M.toEuclideanSCM)) := by
  classical
  by_cases hd : 0 < structuralInputSize M.toEuclideanSCM i
  · obtain ⟨A, hA, happ⟩ := box_structural_node_at_depth M L B hlabels hclass hgate i hd
    refine ⟨4*A, by positivity, ?_⟩
    intro L0 hL0
    obtain ⟨q, hmass, herr⟩ := happ (L0-3) (by omega)
    have hdmax : structuralInputSize M.toEuclideanSCM i ≤ maxInDim M.toEuclideanSCM :=
      Finset.le_sup (Finset.mem_univ i)
    have homax : outputDim (kind i) ≤ maxOutDim M.toEuclideanSCM :=
      Finset.le_sup (f := fun i : Fin n => outputDim (kind i)) (Finset.mem_univ i)
    have hwidth : max (outputDim (kind i)*(2*structuralInputSize M.toEuclideanSCM i+10))
        (outputDim (kind i)) ≤ 12*maxInDim M.toEuclideanSCM*maxOutDim M.toEuclideanSCM := by
      have h : outputDim (kind i)*(2*structuralInputSize M.toEuclideanSCM i+10) ≤
          12*maxInDim M.toEuclideanSCM*maxOutDim M.toEuclideanSCM := by
        calc
          _ ≤ outputDim (kind i)*(12*structuralInputSize M.toEuclideanSCM i) :=
            Nat.mul_le_mul_left _ (by omega)
          _ ≤ maxOutDim M.toEuclideanSCM*(12*maxInDim M.toEuclideanSCM) :=
            Nat.mul_le_mul homax (Nat.mul_le_mul_left 12 hdmax)
          _ = _ := by ring
      apply max_le h
      exact (Nat.le_mul_of_pos_right _ (by omega)).trans h
    let Q : ReLUNet _ _ (12*maxInDim M.toEuclideanSCM*maxOutDim M.toEuclideanSCM) L0 :=
      { q.widen hwidth with depth := q.depth.trans (by omega) }
    have hQ : Q.eval = q.eval := rfl
    have hraw (x) : networkOnStructuralInput M i Q x = networkOnStructuralInput M i q x := by
      dsimp only [networkOnStructuralInput]; rw [hQ]
    refine ⟨Q, by simpa only [hraw] using hmass, ?_⟩
    simp only [hraw]
    refine herr.trans (ENNReal.ofReal_le_ofReal ?_)
    have hrate : (L0 : ℝ)^(-(2 : ℝ)/structuralInputSize M.toEuclideanSCM i) ≤
        (L0 : ℝ)^(-(2 : ℝ)/maxInDim M.toEuclideanSCM) := by
      apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ L0 by omega))
      apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < structuralInputSize M.toEuclideanSCM i)
        (by positivity : (0 : ℝ) < maxInDim M.toEuclideanSCM)).2
      have : (structuralInputSize M.toEuclideanSCM i : ℝ) ≤ maxInDim M.toEuclideanSCM :=
        by exact_mod_cast hdmax
      nlinarith
    calc
      _ ≤ A*(4*(L0 : ℝ)^(-(2 : ℝ)/structuralInputSize M.toEuclideanSCM i)) :=
        mul_le_mul_of_nonneg_left (structural_reserved_depth_rate_le hd hL0) hA.le
      _ ≤ (4*A)*(L0 : ℝ)^(-(2 : ℝ)/maxInDim M.toEuclideanSCM) := by
        nlinarith
  · have hd0 : structuralInputSize M.toEuclideanSCM i = 0 := by omega
    have hall (x y : Input kind dims dag C i) : x = y := by
      apply PiLp.ext
      intro r
      have hempty := Fintype.card_eq_zero_iff.mp hd0
      exact (hempty.false r).elim
    let MB := boxTruncatedSCM M B hlabels
    refine ⟨1, by norm_num, ?_⟩
    intro L0 hL0
    let q : ReLUNet (structuralInputSize M.toEuclideanSCM i) (outputDim (kind i))
        (12*maxInDim M.toEuclideanSCM*maxOutDim M.toEuclideanSCM) L0 :=
      { zeroNet _ _ _ _ with outputBias := (MB.f i 0).ofLp }
    have hq (y) : q.eval y = MB.f i 0 := by
      apply PiLp.ext
      intro j
      simp [q, ReLUNet.eval, zeroNet]
    have hraw (x) : networkOnStructuralInput M i q x = MB.f i x := by
      dsimp only [networkOnStructuralInput]
      rw [hq, hall x 0]
    have hp (x) (hx : x ∈ M.domain i) (k) (hi : kind i = Sum.inr k) :
        (MB.f i x).ofLp ∈ probabilitySimplex (outputDim (kind i)) :=
      canonical_simplex_ofLp MB i k hi x hx
    refine ⟨q, ?_, ?_⟩
    · intro k hi x hx
      rw [hraw]
      exact ⟨(hp x hx k hi).1, by rw [(hp x hx k hi).2]; norm_num⟩
    · have heq (x) (hx : x ∈ M.domain i) :
          (if (kind i).isRight then WithLp.toLp 1
            (fun j => (networkOnStructuralInput M i q x).ofLp j /
              ∑ l, (networkOnStructuralInput M i q x).ofLp l)
            else networkOnStructuralInput M i q x) = MB.f i x := by
        rw [hraw]
        split_ifs with hc
        · obtain ⟨k, hi⟩ : ∃ k, kind i = Sum.inr k := by
            cases h : kind i <;> simp_all
          exact structural_normalized_simplex_eq_self (hp x hx k hi)
        · rfl
      apply iSup_le
      intro x
      simp only [heq x.val x.property]
      change ENNReal.ofReal ‖(MB.f i x.val - MB.f i x.val).ofLp‖ ≤ _
      simp only [sub_self, WithLp.ofLp_zero, norm_zero, ENNReal.ofReal_zero]
      exact bot_le

/-- For [nonnegative Lipschitz and box bounds L and B](hyp:L,B), assume
[every categorical node's number of labels is at most B](hyp:hlabels), [the
model's structural maps are L-Lipschitz on admissible domains](hyp:hclass),
[the maximum input dimension is positive](hyp:hdin), and [the structural Yarotsky
approximation assumption holds](hyp:hYarotskyStructural_of_gate). Then [there
are a positive error constant A, a positive integer width factor, and a depth
threshold at least one such that every depth at least the threshold admits
networks for all nodes with that depth and width equal to the factor times the
maximum input and output dimensions; their categorical outputs are nonnegative
with positive mass, and, after categorical normalization, all mechanisms
approximate the truncated model uniformly on admissible inputs within A times
depth raised to minus two divided by the maximum input dimension](goal). -/
-- @node: box_structural_approx
lemma box_structural_approx
    (M : CanonicalSCM kind dims dag G C) (L B : ℝ≥0)
    (hlabels : ∀ i k, kind i = Sum.inr k → (k : ℝ) ≤ B)
    (hclass : M ∈ canonicalClass (domainLipClass M L))
    (hdin : 0 < maxInDim M.toEuclideanSCM)
    (hYarotskyStructural_of_gate : YarotskyStructuralApprox) :
    ∃ A : ℝ, 0 < A ∧ ∃ c0 B0 : ℕ, 0 < c0 ∧ 1 ≤ B0 ∧
      ∀ L0 : ℕ, B0 ≤ L0 →
      ∃ q : ∀ i, ReLUNet (structuralInputSize M.toEuclideanSCM i) (outputDim (kind i))
        (c0 * maxInDim M.toEuclideanSCM * maxOutDim M.toEuclideanSCM) L0,
      let raw := fun i => networkOnStructuralInput M i (q i)
      (∀ i k, kind i = Sum.inr k → ∀ x ∈ M.domain i,
        (∀ j, 0 ≤ (raw i x).ofLp j) ∧ 0 < ∑ j, (raw i x).ofLp j) ∧
      ∀ i, supDistOn (M.domain i) ((boxTruncatedSCM M B hlabels).f i)
        (fun x => if (kind i).isRight then
          WithLp.toLp 1 (fun j => (raw i x).ofLp j / ∑ l, (raw i x).ofLp l)
          else raw i x) ≤
        ENNReal.ofReal (A * (L0 : ℝ)^(-(2 : ℝ) / maxInDim M.toEuclideanSCM)) := by
  classical
  choose A hA happ using fun i => box_structural_node_budget M L B hlabels hclass hdin
    hYarotskyStructural_of_gate i
  let Amax : ℝ := 1 + ∑ i, A i
  have hAmax : 0 < Amax := by
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => (hA i).le)
    dsimp [Amax]; linarith
  refine ⟨Amax, hAmax, 12, 6, by norm_num, by norm_num, ?_⟩
  intro L0 hL0
  choose q hmass herr using fun i => happ i L0 hL0
  refine ⟨q, hmass, ?_⟩
  intro i
  refine (herr i).trans (ENNReal.ofReal_le_ofReal ?_)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => (hA i).le)
    (Finset.mem_univ i)
  dsimp [Amax]; linarith


/-- For [nonnegative Lipschitz and box bounds L and B](hyp:L,B), assume
[every categorical node's number of labels is at most B](hyp:hlabels), [the
model's structural maps are L-Lipschitz on admissible domains](hyp:hclass),
[the maximum input dimension is positive](hyp:hdin), and [the structural Yarotsky
approximation assumption holds](hyp:hYarotskyStructural_of_gate). Then [there
are a positive error constant A and a depth threshold at least one such that
every depth at least the threshold admits networks for all nodes with that
depth and width equal to the fixed deep structural width factor times the
maximum input and output dimensions; categorical outputs are nonnegative with
positive mass, and, after categorical normalization, all mechanisms approximate
the truncated model uniformly on admissible inputs within A times depth raised
to minus two divided by the maximum input dimension](goal). -/
lemma box_structural_approx_explicit
    (M : CanonicalSCM kind dims dag G C) (L B : ℝ≥0)
    (hlabels : ∀ i k, kind i = Sum.inr k → (k : ℝ) ≤ B)
    (hclass : M ∈ canonicalClass (domainLipClass M L))
    (hdin : 0 < maxInDim M.toEuclideanSCM)
    (hYarotskyStructural_of_gate : YarotskyStructuralApprox) :
    ∃ A : ℝ, 0 < A ∧ ∃ B0 : ℕ, 1 ≤ B0 ∧
      ∀ L0 : ℕ, B0 ≤ L0 →
      ∃ q : ∀ i, ReLUNet (structuralInputSize M.toEuclideanSCM i) (outputDim (kind i))
        (deepStructuralWidthFactor * maxInDim M.toEuclideanSCM * maxOutDim M.toEuclideanSCM) L0,
      let raw := fun i => networkOnStructuralInput M i (q i)
      (∀ i k, kind i = Sum.inr k → ∀ x ∈ M.domain i,
        (∀ j, 0 ≤ (raw i x).ofLp j) ∧ 0 < ∑ j, (raw i x).ofLp j) ∧
      ∀ i, supDistOn (M.domain i) ((boxTruncatedSCM M B hlabels).f i)
        (fun x => if (kind i).isRight then
          WithLp.toLp 1 (fun j => (raw i x).ofLp j / ∑ l, (raw i x).ofLp l)
          else raw i x) ≤
        ENNReal.ofReal (A * (L0 : ℝ)^(-(2 : ℝ) / maxInDim M.toEuclideanSCM)) := by
  classical
  choose A hA happ using fun i => box_structural_node_budget M L B hlabels hclass hdin
    hYarotskyStructural_of_gate i
  let Amax : ℝ := 1 + ∑ i, A i
  have hAmax : 0 < Amax := by
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => (hA i).le)
    dsimp [Amax]; linarith
  refine ⟨Amax, hAmax, 6, by norm_num, ?_⟩
  intro L0 hL0
  choose q hmass herr using fun i => happ i L0 hL0
  refine ⟨q, hmass, ?_⟩
  intro i
  refine (herr i).trans (ENNReal.ofReal_le_ofReal ?_)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => (hA i).le)
    (Finset.mem_univ i)
  dsimp [Amax]; linarith

end
end Papers.TbsNeuralCausalPi

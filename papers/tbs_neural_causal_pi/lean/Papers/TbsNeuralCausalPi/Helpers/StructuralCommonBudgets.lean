module
public import Papers.TbsNeuralCausalPi.Helpers.StructuralFixedDepth
public import Papers.TbsNeuralCausalPi.Helpers.HilbertCurve
/-! # Common structural network budgets

The interpolation construction supplies a single depth factor and width
threshold for a finite family, including constant zero-input mechanisms.
Convex-hull containment retains both simplex and continuous output bounds.
-/
public section
namespace Papers.TbsNeuralCausalPi
set_option linter.style.longLine false
open scoped NNReal
noncomputable section

/-- If [the input or output dimension is zero](hyp:h), then for [any target
function](hyp:f), [nonnegative Lipschitz budget](hyp:L), and [width and
depth](hyp:W,depth), [there is a ReLU network of those dimensions and budgets
that equals the function everywhere, satisfies the Lipschitz bound, and
takes values in the convex hull of the function's unit-cube image](goal). -/
-- @node: structural_constant_approximation
lemma structural_constant_approximation {d k : ℕ} (h : d = 0 ∨ k = 0)
    (f : L1Vec d → L1Vec k) (L : ℝ≥0) (W depth : ℕ) :
    ∃ q : ReLUNet d k W depth,
      LipschitzWith L q.eval ∧
      (∀ x, q.eval x ∈ convexHull ℝ (f '' unitCube d)) ∧
      ∀ x, q.eval x = f x := by
  have hf (x : L1Vec d) : f x = f 0 := by
    rcases h with rfl | rfl
    · congr 1
      exact Subsingleton.elim _ _
    · exact Subsingleton.elim _ _
  refine ⟨constantNet d W depth (f 0), ?_, ?_, ?_⟩
  · have he : (constantNet d W depth (f 0)).eval = fun _ => f 0 := by
      funext x; exact constantNet_eval _ _ _ _ _
    rw [he]
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [dist_self]
    positivity
  · intro x
    rw [constantNet_eval]
    apply subset_convexHull ℝ
    refine ⟨0, ?_, rfl⟩
    intro j
    simp
  · intro x
    rw [constantNet_eval, hf x]

/-- For [any input dimension](hyp:d), [there is a positive constant depending
only on that dimension such that every function with a given Lipschitz bound
on the unit cube, in any output dimension, admits a ReLU approximation at
every width at least that constant, with depth equal to the ceiling of the
constant times one plus the logarithm of the larger of one and the input
dimension; the network retains the Lipschitz bound globally, stays in the
convex hull of the target's unit-cube image, and has one-norm error at most
the constant times the Lipschitz bound times width raised to minus the
reciprocal of that larger dimension](goal). -/
-- @node: relu_fixedDepth_lipschitz_approx_all_dims
lemma relu_fixedDepth_lipschitz_approx_all_dims (d : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (k : ℕ) (L : ℝ≥0) (f : L1Vec d → L1Vec k),
      LipschitzOnWith L f (unitCube d) →
      ∀ W : ℕ, c ≤ W →
        ∃ q : ReLUNet d k W (⌈c * (1+Real.log (max 1 d : ℕ))⌉₊),
          LipschitzWith L q.eval ∧
          (∀ x, q.eval x ∈ convexHull ℝ (f '' unitCube d)) ∧
          ∀ x ∈ unitCube d,
            ‖q.eval x-f x‖ ≤ c * L * (W : ℝ) ^ (-(1:ℝ)/max 1 d) := by
  by_cases hd : d = 0
  · refine ⟨1, by norm_num, ?_⟩
    intro k L f hf W hW
    obtain ⟨q, hLip, hconv, heq⟩ :=
      structural_constant_approximation (Or.inl hd) f L W
        (⌈(1 : ℝ) * (1 + Real.log (max 1 d : ℕ))⌉₊)
    refine ⟨q, hLip, hconv, ?_⟩
    intro x hx
    rw [heq, sub_self, norm_zero]
    positivity
  · obtain ⟨c, hc, happ⟩ := relu_fixedDepth_lipschitz_approx d (by omega)
    refine ⟨c, hc, ?_⟩
    intro k L f hf W hW
    by_cases hk : k = 0
    · obtain ⟨q, hLip, hconv, heq⟩ :=
        structural_constant_approximation (Or.inr hk) f L W
          (⌈c * (1 + Real.log (max 1 d : ℕ))⌉₊)
      refine ⟨q, hLip, hconv, ?_⟩
      intro x hx
      rw [heq, sub_self, norm_zero]
      positivity
    · have hm : max 1 d = d := max_eq_right (by omega)
      rw [hm]
      exact happ k (by omega) L f hf W hW

/-- For [finite families of input and output dimensions](hyp:din,dout) and
[a common dimension bound](hyp:D) that is [positive](hyp:hD) and
[bounds every input dimension](hyp:hdim), [positive common depth and width
thresholds and an error constant exist so that every family with a common
Lipschitz bound on the unit cubes admits ReLU networks at all larger budgets,
with depth given by the depth factor times the ceiling of one plus the
logarithm of the dimension bound; the networks retain the Lipschitz bound
globally, stay in the respective convex hulls of the target images, and have
nodewise one-norm error at most the error constant times the Lipschitz bound
times width raised to minus the reciprocal of the dimension bound](goal). -/
-- @node: structural_networks_common_budgets
lemma structural_networks_common_budgets {I : Type*} [Fintype I]
    (din dout : I → ℕ) (D : ℕ) (hD : 0 < D) (hdim : ∀ i, din i ≤ D) :
    ∃ c0 B : ℕ, 0 < c0 ∧ 0 < B ∧ ∃ A : ℝ, 0 < A ∧
      ∀ c : ℕ, c0 ≤ c → ∀ W : ℕ, B ≤ W →
      ∀ (L : ℝ≥0) (f : ∀ i, L1Vec (din i) → L1Vec (dout i)),
        (∀ i, LipschitzOnWith L (f i) (unitCube (din i))) →
        ∃ q : ∀ i, ReLUNet (din i) (dout i) W
          (c * ⌈1 + Real.log D⌉₊),
          (∀ i, LipschitzWith L (q i).eval) ∧
          (∀ i x, (q i).eval x ∈ convexHull ℝ (f i '' unitCube (din i))) ∧
          ∀ i x, x ∈ unitCube (din i) →
            ‖(q i).eval x - f i x‖ ≤ A * L * (W : ℝ)^(-(1:ℝ)/D) := by
  classical
  choose a ha happ using fun i => relu_fixedDepth_lipschitz_approx_all_dims (din i)
  let C : ℕ := 1 + ∑ i, ⌈a i⌉₊
  let A : ℝ := 1 + ∑ i, a i
  have hapos (i : I) : 0 < ⌈a i⌉₊ := Nat.ceil_pos.mpr (ha i)
  have hCpos : 0 < C := by dsimp [C]; omega
  have haC (i : I) : a i ≤ C := by
    have hs := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => Nat.zero_le ⌈a j⌉₊)
      (Finset.mem_univ i)
    exact (Nat.le_ceil (a i)).trans (by exact_mod_cast (show ⌈a i⌉₊ ≤ C by dsimp [C]; omega))
  have haA (i : I) : a i ≤ A := by
    have hs := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => (ha j).le)
      (Finset.mem_univ i)
    dsimp [A]; linarith
  have hA : 0 < A := by
    have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => (ha j).le)
    dsimp [A]; linarith
  refine ⟨C, C, hCpos, hCpos, A, hA, ?_⟩
  intro c hc W hW L f hf
  have hdepth (i : I) : ⌈a i * (1 + Real.log (max 1 (din i) : ℕ))⌉₊ ≤
      c * ⌈1 + Real.log D⌉₊ := by
    apply Nat.ceil_le.mpr
    have hlog : 1 + Real.log (max 1 (din i) : ℕ) ≤ 1 + Real.log D := by
      apply add_le_add_right
      apply Real.log_le_log (by positivity)
      exact_mod_cast max_le hD (hdim i)
    have hlogpos : 0 ≤ 1 + Real.log (max 1 (din i) : ℕ) := by
      have : 0 ≤ Real.log (max 1 (din i) : ℕ) := Real.log_nonneg (by exact_mod_cast (le_max_left 1 (din i)))
      linarith
    calc
      a i * (1 + Real.log (max 1 (din i) : ℕ)) ≤ (c : ℝ) * (1 + Real.log (max 1 (din i) : ℕ)) :=
        mul_le_mul_of_nonneg_right ((haC i).trans (by exact_mod_cast hc)) hlogpos
      _ ≤ (c : ℝ) * (1 + Real.log D) := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg c)
      _ ≤ (c : ℝ) * ⌈1 + Real.log D⌉₊ :=
        mul_le_mul_of_nonneg_left (Nat.le_ceil _) (Nat.cast_nonneg c)
      _ = _ := by simp
  choose Q hLip hconv herr using fun i => happ i (dout i) L (f i) (hf i) W
    ((haC i).trans (by exact_mod_cast hW))
  have hdepthpos (i : I) : 0 < ⌈a i * (1 + Real.log (max 1 (din i) : ℕ))⌉₊ := by
    apply Nat.ceil_pos.mpr
    apply mul_pos (ha i)
    have : 0 ≤ Real.log (max 1 (din i) : ℕ) := Real.log_nonneg (by exact_mod_cast (le_max_left 1 (din i)))
    linarith
  choose q hq using fun i => relu_pad_depth (Q i) (hdepthpos i) (hdepth i)
  refine ⟨q, ?_, ?_, ?_⟩
  · intro i; rw [hq i]; exact hLip i
  · intro i x; rw [hq i]; exact hconv i x
  · intro i x hx
    rw [hq i]
    refine (herr i x hx).trans ?_
    have hrate := wide_component_rate_le (show 0 < max 1 (din i) by omega)
      (max_le hD (hdim i)) (show (1 : ℝ) ≤ W by exact_mod_cast hCpos.trans_le hW)
      (show (0 : ℝ) ≤ 1 by norm_num)
    calc
      a i * L * (W : ℝ)^(-(1:ℝ)/max 1 (din i)) ≤
          A * L * (W : ℝ)^(-(1:ℝ)/max 1 (din i)) := by gcongr; exact haA i
      _ ≤ A * L * (W : ℝ)^(-(1:ℝ)/D) := mul_le_mul_of_nonneg_left hrate (by positivity)

end
/-- For [a vector-valued function](hyp:f) and [a real bound](hyp:K), if
[the function's one-norm is bounded on the unit cube](hyp:hf) and
[a vector belongs to the convex hull of its unit-cube image](hyp:hy), then
[that vector's one-norm satisfies the same bound](goal). -/
-- @node: structural_convexHull_norm_le
lemma structural_convexHull_norm_le {d k : ℕ} (f : L1Vec d → L1Vec k)
    (K : ℝ) (hf : ∀ x ∈ unitCube d, ‖f x‖ ≤ K)
    {y : L1Vec k} (hy : y ∈ convexHull ℝ (f '' unitCube d)) : ‖y‖ ≤ K := by
  have hs : f '' unitCube d ⊆ Metric.closedBall (0 : L1Vec k) K := by
    rintro z ⟨x, hx, rfl⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using hf x hx
  have hmem := convexHull_min hs (convex_closedBall (0 : L1Vec k) K) hy
  simpa only [Metric.mem_closedBall, dist_zero_right] using hmem

/-- For [a vector-valued function](hyp:f), if [its unit-cube values are
probability vectors](hyp:hf) and [a vector belongs to the convex hull of
those values](hyp:hy), then [that vector is also a probability vector](goal). -/
-- @node: structural_convexHull_simplex
lemma structural_convexHull_simplex {d k : ℕ} (f : L1Vec d → L1Vec k)
    (hf : ∀ x ∈ unitCube d, (f x).ofLp ∈ stdSimplex ℝ (Fin k))
    {y : L1Vec k} (hy : y ∈ convexHull ℝ (f '' unitCube d)) :
    y.ofLp ∈ stdSimplex ℝ (Fin k) := by
  have hc : Convex ℝ {z : L1Vec k | z.ofLp ∈ stdSimplex ℝ (Fin k)} :=
    (convex_stdSimplex ℝ (Fin k)).linear_preimage
      (WithLp.linearEquiv 1 ℝ (Fin k → ℝ)).toLinearMap
  exact convexHull_min (by rintro z ⟨x, hx, rfl⟩; exact hf x hx) hc hy

/-- For [finite families of input and output dimensions](hyp:din,dout),
[a common dimension bound](hyp:D) that is [positive](hyp:hD) and
[bounds every input dimension](hyp:hdim), and [nodewise output target
sets](hyp:target) that are [convex](hyp:htarget), [positive common depth and
width thresholds and an error constant exist so that every family with a
common Lipschitz bound mapping the unit cubes into those targets admits
ReLU approximations at all larger budgets, with depth equal to the depth
factor times the ceiling of one plus the logarithm of the dimension bound;
the networks retain the Lipschitz bound and target membership globally and
have nodewise error at most the error constant times the Lipschitz bound
times width raised to minus the reciprocal of the dimension bound](goal). -/
-- @node: structural_networks_common_budgets_convex
lemma structural_networks_common_budgets_convex {I : Type*} [Fintype I]
    (din dout : I → ℕ) (D : ℕ) (hD : 0 < D) (hdim : ∀ i, din i ≤ D)
    (target : ∀ i, Set (L1Vec (dout i))) (htarget : ∀ i, Convex ℝ (target i)) :
    ∃ c0 B : ℕ, 0 < c0 ∧ 0 < B ∧ ∃ A : ℝ, 0 < A ∧
      ∀ c : ℕ, c0 ≤ c → ∀ W : ℕ, B ≤ W →
      ∀ (L : ℝ≥0) (f : ∀ i, L1Vec (din i) → L1Vec (dout i)),
        (∀ i, LipschitzOnWith L (f i) (unitCube (din i))) →
        (∀ i, Set.MapsTo (f i) (unitCube (din i)) (target i)) →
        ∃ q : ∀ i, ReLUNet (din i) (dout i) W (c * ⌈1 + Real.log D⌉₊),
          (∀ i, LipschitzWith L (q i).eval) ∧
          (∀ i x, (q i).eval x ∈ target i) ∧
          ∀ i x, x ∈ unitCube (din i) →
            ‖(q i).eval x - f i x‖ ≤ A * L * (W : ℝ)^(-(1:ℝ)/D) := by
  obtain ⟨c0, B, hc0, hB, A, hA, happ⟩ :=
    structural_networks_common_budgets din dout D hD hdim
  refine ⟨c0, B, hc0, hB, A, hA, ?_⟩
  intro c hc W hW L f hf hmaps
  obtain ⟨q, hLip, hconv, herr⟩ := happ c hc W hW L f hf
  refine ⟨q, hLip, ?_, herr⟩
  intro i x
  exact convexHull_min (Set.image_subset_iff.mpr (hmaps i)) (htarget i) (hconv i x)

/-- For [a finite family of target functions](hyp:f) and [ReLU
networks](hyp:q), suppose [each network's one-norm error on its unit cube is
at most a common constant times the Lipschitz budget times width raised to
minus the reciprocal of the dimension bound](hyp:herr). For [nodewise input
vectors](hyp:x) that [belong to their unit cubes](hyp:hx), [the sum of the
one-norm errors is at most the number of nodes times that common error
bound](goal). -/
-- @node: structural_networks_sum_error_le
lemma structural_networks_sum_error_le {I : Type*} [Fintype I]
    {din dout : I → ℕ} {D W depth : ℕ} {A : ℝ} {L : ℝ≥0}
    (f : ∀ i, L1Vec (din i) → L1Vec (dout i))
    (q : ∀ i, ReLUNet (din i) (dout i) W depth)
    (herr : ∀ i x, x ∈ unitCube (din i) →
      ‖(q i).eval x - f i x‖ ≤ A * L * (W : ℝ)^(-(1:ℝ)/D))
    (x : ∀ i, L1Vec (din i)) (hx : ∀ i, x i ∈ unitCube (din i)) :
    (∑ i, ‖(q i).eval (x i) - f i (x i)‖) ≤
      (Fintype.card I : ℝ) * A * L * (W : ℝ)^(-(1:ℝ)/D) := by
  calc
    _ ≤ ∑ _i : I, A * L * (W : ℝ)^(-(1:ℝ)/D) :=
      Finset.sum_le_sum (fun i _ => herr i (x i) (hx i))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- For [an input set](hyp:S) and [two vector-valued functions](hyp:f,g),
if [an error bound is nonnegative](hyp:he) and [their one-norm difference is
at most that bound throughout the set](hyp:herr), then [their extended
uniform coordinate error on the set is at most that same bound](goal). -/
-- @node: structural_supDistOn_le_of_norm_error
lemma structural_supDistOn_le_of_norm_error {X : Type*} {k : ℕ}
    (S : Set X) (f g : X → L1Vec k) {e : ℝ} (he : 0 ≤ e)
    (herr : ∀ x ∈ S, ‖g x - f x‖ ≤ e) :
    supDistOn S f g ≤ ENNReal.ofReal e := by
  apply iSup_le
  intro x
  apply ENNReal.ofReal_le_ofReal
  apply (pi_norm_le_iff_of_nonneg he).mpr
  intro j
  have hc := PiLp.norm_apply_le (g x.val - f x.val) j
  have heq : ‖(f x.val - g x.val).ofLp j‖ = ‖(g x.val - f x.val).ofLp j‖ := by
    simpa only [PiLp.sub_apply] using norm_sub_rev ((f x.val).ofLp j) ((g x.val).ofLp j)
  rw [heq]
  exact hc.trans (herr x.val x.property)

/-- Suppose [the common error constant is nonnegative](hyp:hA). For
[a finite family of target functions](hyp:f) and [ReLU networks](hyp:q), if
[each network's one-norm error on its unit cube is at most the constant times
the Lipschitz budget times width raised to minus the reciprocal of the
dimension bound](hyp:herr), then [the sum of their extended uniform
coordinate errors is at most the number of nodes times that common
bound](goal). -/
-- @node: structural_networks_sum_supDistOn_le
lemma structural_networks_sum_supDistOn_le {I : Type*} [Fintype I]
    {din dout : I → ℕ} {D W depth : ℕ} {A : ℝ} (hA : 0 ≤ A) {L : ℝ≥0}
    (f : ∀ i, L1Vec (din i) → L1Vec (dout i))
    (q : ∀ i, ReLUNet (din i) (dout i) W depth)
    (herr : ∀ i x, x ∈ unitCube (din i) →
      ‖(q i).eval x - f i x‖ ≤ A * L * (W : ℝ)^(-(1:ℝ)/D)) :
    (∑ i, supDistOn (unitCube (din i)) (f i) (q i).eval) ≤
      ENNReal.ofReal ((Fintype.card I : ℝ) * A * L * (W : ℝ)^(-(1:ℝ)/D)) := by
  have he : 0 ≤ A * L * (W : ℝ)^(-(1:ℝ)/D) := by positivity
  calc
    _ ≤ ∑ _i : I, ENNReal.ofReal (A * L * (W : ℝ)^(-(1:ℝ)/D)) :=
      Finset.sum_le_sum (fun i _ =>
        structural_supDistOn_le_of_norm_error _ _ _ he (herr i))
    _ = ENNReal.ofReal (∑ _i : I, A * L * (W : ℝ)^(-(1:ℝ)/D)) :=
      (ENNReal.ofReal_sum_of_nonneg (fun _ _ => he)).symm
    _ = _ := by congr 1; simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end Papers.TbsNeuralCausalPi

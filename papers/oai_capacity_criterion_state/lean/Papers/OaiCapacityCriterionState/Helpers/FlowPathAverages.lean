module

public import Papers.OaiCapacityCriterionState.Helpers.FlowProfileExperiments

/-! # Reindexing finite descendant losses as flow path averages

Deleting the first letters of a reversed tree word selects its ancestor.
The identities below retain the exact propagation coefficient and use only
finite conservation, so early leaves require no separate pruning argument.
-/

@[expose] public section

open scoped BigOperators

namespace OaiCapacityCriterionState

-- @node: BoundedTree.sum_level_children_parent
/-- For any two vertex functions, [the sum over a level of the first function
times the sum of the second over children equals the sum over the next level
of the first function at the parent times the second at the child](goal). -/
lemma BoundedTree.sum_level_children_parent {B : ℕ} (T : BoundedTree B)
    (f g : List (Fin B) → ℝ) (i : ℕ) :
    (∑ v ∈ T.level i, f v * ∑ w ∈ T.children v, g w) =
      ∑ w ∈ T.level (i + 1), f (w.drop 1) * g w := by
  classical
  rw [T.sum_level_succ]
  apply Finset.sum_congr rfl
  intro v hv
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hw
  rfl

-- @node: BoundedTree.weightedDescendantSum_level_pair
/-- For vertex functions f and g and propagation weight c, [summing f times
the k-generation weighted descendant sum of g over level i equals c to the
power k times the sum over level i plus k of g times f at the ancestor
k generations earlier](goal). -/
lemma BoundedTree.weightedDescendantSum_level_pair {B : ℕ} (T : BoundedTree B)
    (c : ℝ) (f g : List (Fin B) → ℝ) (i k : ℕ) :
    (∑ v ∈ T.level i, f v * T.weightedDescendantSum c g k v) =
      c ^ k * ∑ u ∈ T.level (i + k), f (u.drop k) * g u := by
  classical
  induction k generalizing i f with
  | zero => simp [BoundedTree.weightedDescendantSum]
  | succ k ih =>
      simp only [BoundedTree.weightedDescendantSum]
      have hfactor : (∑ v ∈ T.level i,
          f v * (c * ∑ w ∈ T.children v, T.weightedDescendantSum c g k w)) =
          c * ∑ v ∈ T.level i,
            f v * ∑ w ∈ T.children v, T.weightedDescendantSum c g k w := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v hv
        ring
      rw [hfactor, T.sum_level_children_parent, ih]
      simp only [List.drop_drop]
      rw [show i + 1 + k = i + (k + 1) by omega]
      simp only [show k + 1 = 1 + k by omega, pow_add, pow_one]
      ring

-- @node: BoundedTree.conserved_level_ancestor_sum
/-- If [the child masses sum to their parent mass at every tree
vertex](hyp:hq), then [the mass-weighted sum at level i plus k of any function
evaluated at the ancestor k generations earlier equals the mass-weighted sum
of that function at level i](goal). -/
lemma BoundedTree.conserved_level_ancestor_sum {B : ℕ} (T : BoundedTree B)
    (q f : List (Fin B) → ℝ)
    (hq : ∀ v ∈ T.verts, ∑ w ∈ T.children v, q w = q v) (i k : ℕ) :
    (∑ u ∈ T.level (i + k), q u * f (u.drop k)) =
      ∑ v ∈ T.level i, q v * f v := by
  classical
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show i + (k + 1) = (i + k) + 1 by omega, T.sum_level_succ]
      have hstep : (∑ v ∈ T.level (i + k),
          ∑ w ∈ T.children v, q w * f (w.drop (k + 1))) =
          ∑ v ∈ T.level (i + k), q v * f (v.drop k) := by
        apply Finset.sum_congr rfl
        intro v hv
        calc
          _ = ∑ w ∈ T.children v, q w * f (v.drop k) := by
            apply Finset.sum_congr rfl
            intro w hw
            obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hw
            rfl
          _ = _ := by
            rw [← Finset.sum_mul, hq v ((T.mem_level_iff v _).mp hv).1]
      rw [hstep, ih]

-- @node: flowVertexMass
/-- For [a bounded tree](hyp:T), [an edge-mass assignment](hyp:theta), and
[a vertex v](hyp:v), the [vertex flow mass](goal) is [the total outgoing flow
mass when v is the root](step:1) and [the assigned edge mass at v
otherwise](step:2). -/
noncomputable def flowVertexMass {B : ℕ} (T : BoundedTree B)
    (theta : List (Fin B) → ℝ) (v : List (Fin B)) : ℝ :=
  if v = [] then flowMass T theta else theta v

-- @node: flowVertexMass_conserved
/-- If [the edge masses form a flow](hyp:htheta) and [v belongs to the
tree](hyp:hv), then [the sum of the vertex flow masses at the children of v
equals the vertex flow mass at v, including when v is the root](goal). -/
lemma flowVertexMass_conserved {B : ℕ} (T : BoundedTree B)
    (theta : List (Fin B) → ℝ) (htheta : IsFlow T theta)
    (v : List (Fin B)) (hv : v ∈ T.verts) :
    (∑ w ∈ T.children v, flowVertexMass T theta w) = flowVertexMass T theta v := by
  classical
  have hsum : (∑ w ∈ T.children v, flowVertexMass T theta w) =
      ∑ w ∈ T.children v, theta w := by
    apply Finset.sum_congr rfl
    intro w hw
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hw
    simp only [flowVertexMass, List.cons_ne_nil, if_false]
  rw [hsum]
  by_cases hnil : v = []
  · subst v; rfl
  · rw [flowVertexMass, if_neg hnil]
    exact (htheta.2.2 v hv hnil).symm

-- @node: flowVertexMass_eq_scaled_normalizedFlow
/-- If [λ lies strictly between zero and one](hyp:hlam), then [the vertex
flow mass at any vertex equals its normalized flow times λ squared raised
to the vertex depth](goal). -/
lemma flowVertexMass_eq_scaled_normalizedFlow {B : ℕ} (T : BoundedTree B)
    (lam : ℝ) (hlam : MainLambda lam) (theta : List (Fin B) → ℝ)
    (v : List (Fin B)) :
    flowVertexMass T theta v = sqParam lam ^ v.length * normalizedFlow T lam theta v := by
  by_cases hnil : v = []
  · subst v; simp [flowVertexMass, normalizedFlow]
  · simp only [flowVertexMass, normalizedFlow, if_neg hnil, normalizedEdgeFlow]
    field_simp [ne_of_gt (pow_pos (sqParam_mem_Ioo lam hlam).1 v.length)]

-- @node: flow_level_ancestor_average
/-- If [the edge masses form a flow](hyp:htheta), then [the vertex-mass-weighted
sum at level i plus k of a function evaluated at the ancestor k generations
earlier equals the vertex-mass-weighted sum of that function at level i](goal). -/
lemma flow_level_ancestor_average {B : ℕ} (T : BoundedTree B)
    (theta : List (Fin B) → ℝ) (htheta : IsFlow T theta)
    (f : List (Fin B) → ℝ) (i k : ℕ) :
    (∑ u ∈ T.level (i + k), flowVertexMass T theta u * f (u.drop k)) =
      ∑ v ∈ T.level i, flowVertexMass T theta v * f v := by
  exact T.conserved_level_ancestor_sum (flowVertexMass T theta) f
    (flowVertexMass_conserved T theta htheta) i k

-- @node: scaled_profile_weight_identity
/-- If [λ lies strictly between zero and one](hyp:hlam), then [multiplying
the ε-scaled normalized flow at a vertex by λ squared raised to its depth
gives ε times its vertex flow mass](goal). -/
lemma scaled_profile_weight_identity {B : ℕ} (T : BoundedTree B)
    (lam : ℝ) (hlam : MainLambda lam) (theta : List (Fin B) → ℝ)
    (eps : ℝ) (v : List (Fin B)) :
    sqParam lam ^ v.length * (eps * normalizedFlow T lam theta v) =
      eps * flowVertexMass T theta v := by
  rw [flowVertexMass_eq_scaled_normalizedFlow T lam hlam theta v]
  ring

-- @node: scaled_profile_descendant_pair_average
/-- If [λ lies strictly between zero and one](hyp:hlam), then [λ squared to
level i times the sum there of f times the k-generation descendant sum of
the ε-scaled normalized flow times g, propagated with weight λ cubed, equals
λ to the power k times the sum at level i plus k of ε times vertex flow
mass times f at the level-i ancestor times g at the descendant](goal). -/
lemma scaled_profile_descendant_pair_average {B : ℕ} (T : BoundedTree B)
    (lam : ℝ) (hlam : MainLambda lam) (theta : List (Fin B) → ℝ)
    (eps : ℝ) (f g : List (Fin B) → ℝ) (i k : ℕ) :
    sqParam lam ^ i * (∑ v ∈ T.level i, f v *
      T.weightedDescendantSum (lam ^ 3)
        (fun u => (eps * normalizedFlow T lam theta u) * g u) k v) =
      lam ^ k * ∑ u ∈ T.level (i + k),
        (eps * flowVertexMass T theta u) * f (u.drop k) * g u := by
  classical
  rw [T.weightedDescendantSum_level_pair]
  have hp : (lam ^ 3) ^ k = sqParam lam ^ k * lam ^ k := by
    rw [← mul_pow]
    congr 1
  rw [hp]
  have hrearrange : sqParam lam ^ i *
      (sqParam lam ^ k * lam ^ k * ∑ u ∈ T.level (i + k),
        f (u.drop k) * ((eps * normalizedFlow T lam theta u) * g u)) =
      lam ^ k * ∑ u ∈ T.level (i + k),
        (sqParam lam ^ (i + k) * (eps * normalizedFlow T lam theta u)) *
          f (u.drop k) * g u := by
    rw [pow_add]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    ring
  rw [hrearrange]
  congr 1
  apply Finset.sum_congr rfl
  intro u hu
  rw [← ((T.mem_level_iff u (i + k)).mp hu).2,
    scaled_profile_weight_identity T lam hlam theta eps u]

-- @node: scaled_profile_descendant_pair_terminal_average
/-- If [λ lies strictly between zero and one](hyp:hlam), [the edge masses form
a flow](hyp:htheta), and [level i plus k does not exceed the terminal depth
N](hyp:hdepth), then [λ squared to level i times the sum there of f times
the k-generation descendant sum of the ε-scaled normalized flow times g,
propagated with weight λ cubed, equals λ to the power k times the sum over
level N of ε times vertex flow mass times f at the level-i ancestor times
g at the level-(i plus k) ancestor](goal). -/
lemma scaled_profile_descendant_pair_terminal_average {B : ℕ} (T : BoundedTree B)
    (lam : ℝ) (hlam : MainLambda lam) (theta : List (Fin B) → ℝ)
    (htheta : IsFlow T theta) (eps : ℝ) (f g : List (Fin B) → ℝ)
    (i k N : ℕ) (hdepth : i + k ≤ N) :
    sqParam lam ^ i * (∑ v ∈ T.level i, f v *
      T.weightedDescendantSum (lam ^ 3)
        (fun u => (eps * normalizedFlow T lam theta u) * g u) k v) =
      lam ^ k * ∑ u ∈ T.level N,
        (eps * flowVertexMass T theta u) *
          f (u.drop (N - i)) * g (u.drop (N - (i + k))) := by
  classical
  rw [scaled_profile_descendant_pair_average T lam hlam theta eps]
  have h := flow_level_ancestor_average T theta htheta
    (fun u => f (u.drop k) * g u) (i + k) (N - (i + k))
  rw [Nat.add_sub_of_le hdepth] at h
  simp only [List.drop_drop] at h
  rw [show N - (i + k) + k = N - i by omega] at h
  have heq : (∑ u ∈ T.level (i + k),
      (eps * flowVertexMass T theta u) * f (u.drop k) * g u) =
      ∑ u ∈ T.level N, (eps * flowVertexMass T theta u) *
        f (u.drop (N - i)) * g (u.drop (N - (i + k))) := by
    calc
      _ = eps * ∑ u ∈ T.level (i + k),
          flowVertexMass T theta u * (f (u.drop k) * g u) := by
        simp only [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
      _ = eps * ∑ u ∈ T.level N, flowVertexMass T theta u *
          (f (u.drop (N - i)) * g (u.drop (N - (i + k)))) := by rw [h]
      _ = _ := by
        simp only [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
  rw [heq]

-- @node: flowVertexMass_nonneg
/-- If [the edge masses form a flow](hyp:htheta), then [the vertex flow mass
is nonnegative at every vertex](goal). -/
lemma flowVertexMass_nonneg {B : ℕ} (T : BoundedTree B)
    (theta : List (Fin B) → ℝ) (htheta : IsFlow T theta)
    (v : List (Fin B)) : 0 ≤ flowVertexMass T theta v := by
  unfold flowVertexMass
  split_ifs
  · exact flowMass_nonneg T theta htheta
  · exact htheta.1 v

-- @node: flowVertexMass_level_sum
/-- If [the edge masses form a flow](hyp:htheta), then [the sum of vertex
flow masses at any level equals the total outgoing flow mass at the root](goal). -/
lemma flowVertexMass_level_sum {B : ℕ} (T : BoundedTree B)
    (theta : List (Fin B) → ℝ) (htheta : IsFlow T theta) (N : ℕ) :
    (∑ v ∈ T.level N, flowVertexMass T theta v) = flowMass T theta := by
  have h := flow_level_ancestor_average T theta htheta (fun _ => 1) 0 N
  simpa [BoundedTree.level, flowVertexMass] using h

-- @node: flowVertexMass_pos_has_ray
/-- If [the edge masses form a flow](hyp:htheta), [v belongs to the
tree](hyp:hv), and [its vertex flow mass is strictly positive](hyp:hpos), then
[an infinite ray of the tree passes through v at its depth](goal). -/
lemma flowVertexMass_pos_has_ray {B : ℕ} (T : BoundedTree B)
    (theta : List (Fin B) → ℝ) (htheta : IsFlow T theta)
    (v : List (Fin B)) (hv : v ∈ T.verts) (hpos : 0 < flowVertexMass T theta v) :
    ∃ xi ∈ T.rays, rayPrefix xi v.length = v := by
  classical
  by_cases hnil : v = []
  · subst v
    change 0 < flowMass T theta at hpos
    obtain ⟨w, hw, hp⟩ := (Finset.sum_pos_iff_of_nonneg
      (fun w _ => htheta.1 w)).mp hpos
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨xi, hxi, _⟩ := IsFlow.exists_ray_through_positive T theta htheta
      (a :: []) (Finset.mem_filter.mp ha).2 (List.cons_ne_nil _ _) hp
    exact ⟨xi, hxi, rfl⟩
  · exact IsFlow.exists_ray_through_positive T theta htheta v hv hnil
      (by simpa only [flowVertexMass, if_neg hnil] using hpos)

-- @node: rayPrefix_drop_to_depth
/-- If [depth i does not exceed depth n](hyp:hi), then [deleting the first
n minus i letters of the reversed depth-n prefix of a sequence gives its
depth-i prefix](goal). -/
lemma rayPrefix_drop_to_depth {B : ℕ} (xi : ℕ → Fin B) (i n : ℕ) (hi : i ≤ n) :
    (rayPrefix xi n).drop (n - i) = rayPrefix xi i := by
  induction n with
  | zero =>
      have hi0 : i = 0 := by omega
      subst i
      rfl
  | succ n ih =>
      by_cases heq : i = n + 1
      · subst i; simp
      · have hin : i ≤ n := by omega
        rw [show n + 1 - i = (n - i) + 1 by omega]
        simpa only [rayPrefix, List.drop_succ_cons] using ih hin

-- @node: finite_triangle_sum_swap
/-- For any function of two nonnegative integer indices, [summing first over
i below N and then over k below N minus i gives the same result as summing
first over k below N and then over i below N minus k](goal). -/
lemma finite_triangle_sum_swap (f : ℕ → ℕ → ℝ) (N : ℕ) :
    (∑ i ∈ Finset.range N, ∑ k ∈ Finset.range (N - i), f i k) =
      ∑ k ∈ Finset.range N, ∑ i ∈ Finset.range (N - k), f i k := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (fun x => ⟨x.2, x.1⟩) (fun x => ⟨x.2, x.1⟩)
    ?_ ?_ (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) <;>
    simp only [Finset.mem_range, Sigma.forall, Finset.mem_sigma] <;> omega

-- @node: scaled_profile_kernel_reindex
/-- If [λ lies strictly between zero and one](hyp:hlam) and [the edge masses
form a flow](hyp:htheta), then [the sum over levels i below N of λ squared
to i times f paired with all descendant sums of the ε-scaled normalized
flow times g at distances k below N minus i, propagated with λ cubed, equals
the ε-scaled vertex-mass-weighted sum at level N of the path kernel that
sums λ to k times f at the depth-i ancestor times g at the depth-(i plus k)
ancestor over k below N and i below N minus k](goal). -/
lemma scaled_profile_kernel_reindex {B : ℕ} (T : BoundedTree B)
    (lam : ℝ) (hlam : MainLambda lam) (theta : List (Fin B) → ℝ)
    (htheta : IsFlow T theta) (eps : ℝ) (f g : List (Fin B) → ℝ) (N : ℕ) :
    (∑ i ∈ Finset.range N, sqParam lam ^ i * ∑ v ∈ T.level i,
      f v * ∑ k ∈ Finset.range (N - i), T.weightedDescendantSum (lam ^ 3)
        (fun u => (eps * normalizedFlow T lam theta u) * g u) k v) =
      ∑ u ∈ T.level N, (eps * flowVertexMass T theta u) *
        ∑ k ∈ Finset.range N, lam ^ k * ∑ i ∈ Finset.range (N - k),
          f (u.drop (N - i)) * g (u.drop (N - (i + k))) := by
  classical
  calc
    _ = ∑ i ∈ Finset.range N, ∑ k ∈ Finset.range (N - i),
        sqParam lam ^ i * ∑ v ∈ T.level i, f v *
          T.weightedDescendantSum (lam ^ 3)
            (fun u => (eps * normalizedFlow T lam theta u) * g u) k v := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = ∑ i ∈ Finset.range N, ∑ k ∈ Finset.range (N - i),
        lam ^ k * ∑ u ∈ T.level N, (eps * flowVertexMass T theta u) *
          f (u.drop (N - i)) * g (u.drop (N - (i + k))) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro k hk
      exact scaled_profile_descendant_pair_terminal_average T lam hlam theta htheta
        eps f g i k N (by simp only [Finset.mem_range] at *; omega)
    _ = _ := by
      rw [finite_triangle_sum_swap]
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intros
      ring

-- @node: scaled_profile_terminal_reindex
/-- If [λ lies strictly between zero and one](hyp:hlam) and [the edge masses
form a flow](hyp:htheta), then [the sum over levels i below N of λ squared
to i times f paired with the (N minus i)-generation descendant sum of the
ε-scaled normalized flow, propagated with λ cubed, equals the ε-scaled
vertex-mass-weighted sum at level N of f at each depth-i ancestor weighted
by λ to the power N minus i](goal). -/
lemma scaled_profile_terminal_reindex {B : ℕ} (T : BoundedTree B)
    (lam : ℝ) (hlam : MainLambda lam) (theta : List (Fin B) → ℝ)
    (htheta : IsFlow T theta) (eps : ℝ) (f : List (Fin B) → ℝ) (N : ℕ) :
    (∑ i ∈ Finset.range N, sqParam lam ^ i * ∑ v ∈ T.level i,
      f v * T.weightedDescendantSum (lam ^ 3)
        (fun u => eps * normalizedFlow T lam theta u) (N - i) v) =
      ∑ u ∈ T.level N, (eps * flowVertexMass T theta u) *
        ∑ i ∈ Finset.range N, lam ^ (N - i) * f (u.drop (N - i)) := by
  classical
  have heq (i : ℕ) (hi : i < N) :=
    scaled_profile_descendant_pair_terminal_average T lam hlam theta htheta
      eps f (fun _ => 1) i (N - i) N (by omega)
  simp only [mul_one] at heq
  calc
    _ = ∑ i ∈ Finset.range N, lam ^ (N - i) *
        ∑ u ∈ T.level N, (eps * flowVertexMass T theta u) * f (u.drop (N - i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact heq i (Finset.mem_range.mp hi)
    _ = _ := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intros
      ring

-- @node: scaled_profile_finite_path_bounds
/-- Suppose [λ lies strictly between zero and one](hyp:hlam), [the edge
masses form a flow](hyp:htheta), [every tree ray has path potential at most
one](hyp:hpotential), and [ε is nonnegative](hyp:heps). For [a tree vertex
v](hyp:hv) with [positive vertex flow mass](hyp:hpos), [the sum of squared
ε-scaled normalized flows along its ancestors, including the root and v,
is at most ε squared times the sum of squared total flow mass and one,
and each such scaled flow is at most ε times the sum of one and the total
flow mass](goal). -/
lemma scaled_profile_finite_path_bounds {B : ℕ} (T : BoundedTree B)
    (lam : ℝ) (hlam : MainLambda lam) (theta : List (Fin B) → ℝ)
    (htheta : IsFlow T theta)
    (hpotential : ∀ xi ∈ T.rays, pathPotential lam theta xi ≤ 1)
    (eps : ℝ) (heps : 0 ≤ eps) (v : List (Fin B)) (hv : v ∈ T.verts)
    (hpos : 0 < flowVertexMass T theta v) :
    (∑ i ∈ Finset.range (v.length + 1),
      (eps * normalizedFlow T lam theta (v.drop (v.length - i))) ^ 2) ≤
        (flowMass T theta ^ 2 + 1) * eps ^ 2 ∧
    ∀ i ≤ v.length, eps * normalizedFlow T lam theta (v.drop (v.length - i)) ≤
      (1 + flowMass T theta) * eps := by
  obtain ⟨xi, hxi, hprefix⟩ := flowVertexMass_pos_has_ray T theta htheta v hv hpos
  have hancestor (i : ℕ) (hi : i ≤ v.length) :
      v.drop (v.length - i) = rayPrefix xi i := by
    calc
      _ = (rayPrefix xi v.length).drop (v.length - i) :=
        congrArg (List.drop (v.length - i)) hprefix.symm
      _ = _ := rayPrefix_drop_to_depth xi i v.length hi
  refine ⟨?_, ?_⟩
  · calc
      _ = ∑ i ∈ Finset.range (v.length + 1),
          (eps * normalizedFlow T lam theta (rayPrefix xi i)) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hancestor i (by simp only [Finset.mem_range] at hi; omega)]
      _ ≤ _ := scaled_normalizedFlow_path_energy_le T lam theta eps xi
        (hpotential xi hxi) v.length
  · intro i hi
    rw [hancestor i hi]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right
      (normalizedFlow_ray_bound T lam hlam theta htheta hpotential xi hxi i) heps

-- @node: finite_path_shifted_terminal_bound
/-- If [R is nonnegative](hyp:hR), [λ is nonnegative](hyp:hlam), [λ is less
than one](hyp:hlam1), and [each of the first n values of X is at most
R](hyp:hX), then [their sum weighted by λ to the power n minus the index
is at most R divided by one minus λ](goal). -/
lemma finite_path_shifted_terminal_bound (X : ℕ → ℝ) (n : ℕ) (R lam : ℝ)
    (hR : 0 ≤ R) (hlam : 0 ≤ lam) (hlam1 : lam < 1)
    (hX : ∀ i < n, X i ≤ R) :
    (∑ i ∈ Finset.range n, lam ^ (n - i) * X i) ≤ R / (1 - lam) := by
  have heq : (∑ i ∈ Finset.range n, lam ^ (n - i) * X i) =
      lam * ∑ k ∈ Finset.range n, lam ^ k * X (n - 1 - k) := by
    rw [← Finset.sum_range_reflect (fun i => lam ^ (n - i) * X i) n,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [show n - (n - 1 - k) = k + 1 by simp only [Finset.mem_range] at hk; omega,
      pow_succ]
    ring
  rw [heq]
  calc
    _ ≤ lam * (R / (1 - lam)) := mul_le_mul_of_nonneg_left
      (finite_path_terminal_bound X n R lam hR hlam hlam1 hX) hlam
    _ ≤ R / (1 - lam) := mul_le_of_le_one_left
      (div_nonneg hR (sub_pos.mpr hlam1).le) hlam1.le

-- @node: scaled_profile_averaged_path_loss_bound
/-- If [λ lies strictly between zero and one](hyp:hlam), [the edge masses
form a flow](hyp:htheta), [every tree ray has path potential at most
one](hyp:hpotential), and [ε is nonnegative](hyp:heps), then [the level-N
sum weighted by ε times vertex flow mass of the ancestor-pair kernel
plus the terminal sum is at most ε times total flow mass times the sum of
the energy bound and the pointwise bound, divided by one minus λ; here the
profile is ε times normalized flow, the kernel sums profile products at
depths i and i plus k with weight λ to k for i plus k below N, the terminal
sum weights the depth-i profile by λ to N minus i for i below N, the energy
bound is ε squared times the sum of squared total flow mass and one, and
the pointwise bound is ε times the sum of one and total flow mass](goal). -/
lemma scaled_profile_averaged_path_loss_bound {B : ℕ} (T : BoundedTree B)
    (lam : ℝ) (hlam : MainLambda lam) (theta : List (Fin B) → ℝ)
    (htheta : IsFlow T theta)
    (hpotential : ∀ xi ∈ T.rays, pathPotential lam theta xi ≤ 1)
    (eps : ℝ) (heps : 0 ≤ eps) (N : ℕ) :
    let X := fun v => eps * normalizedFlow T lam theta v
    let E := (flowMass T theta ^ 2 + 1) * eps ^ 2
    let R := (1 + flowMass T theta) * eps
    (∑ u ∈ T.level N, (eps * flowVertexMass T theta u) *
      ((∑ k ∈ Finset.range N, lam ^ k * ∑ i ∈ Finset.range (N - k),
          X (u.drop (N - i)) * X (u.drop (N - (i + k)))) +
        ∑ i ∈ Finset.range N, lam ^ (N - i) * X (u.drop (N - i)))) ≤
      (eps * flowMass T theta) * (E / (1 - lam) + R / (1 - lam)) := by
  classical
  intro X E R
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hR : 0 ≤ R := mul_nonneg
    (by linarith [flowMass_nonneg T theta htheta]) heps
  calc
    _ ≤ ∑ u ∈ T.level N, (eps * flowVertexMass T theta u) *
        (E / (1 - lam) + R / (1 - lam)) := by
      apply Finset.sum_le_sum
      intro u hu
      by_cases hzero : flowVertexMass T theta u = 0
      · simp only [hzero, mul_zero, zero_mul, le_refl]
      have hpos : 0 < flowVertexMass T theta u :=
        lt_of_le_of_ne (flowVertexMass_nonneg T theta htheta u) (Ne.symm hzero)
      have hlen := ((T.mem_level_iff u N).mp hu).2
      obtain ⟨henergy, hbound⟩ := scaled_profile_finite_path_bounds T lam hlam theta
        htheta hpotential eps heps u ((T.mem_level_iff u N).mp hu).1 hpos
      rw [hlen] at henergy hbound
      apply mul_le_mul_of_nonneg_left _
        (mul_nonneg heps (flowVertexMass_nonneg T theta htheta u))
      apply add_le_add
      · apply finite_path_kernel_bound (fun i => X (u.drop (N - i))) N E lam
          hE hlam.1.le hlam.2
        exact (Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono (Nat.le_succ N)) (fun i _ _ => sq_nonneg _)).trans henergy
      · exact finite_path_shifted_terminal_bound (fun i => X (u.drop (N - i)))
          N R lam hR hlam.1.le hlam.2 (fun i hi => hbound i (by omega))
    _ = _ := by
      rw [← Finset.sum_mul, ← Finset.mul_sum, flowVertexMass_level_sum T theta htheta N]

-- @node: scaled_profile_descendant_loss_bound
/-- If [λ lies strictly between zero and one](hyp:hlam), [the edge masses
form a flow](hyp:htheta), [every tree ray has path potential at most
one](hyp:hpotential), and [ε is nonnegative](hyp:heps), then [for the profile
ε times normalized flow, the sum over levels i below N of λ squared to i
times the profile times the sum of its terminal descendant contribution
and all earlier squared-profile descendant contributions, propagated with
λ cubed, is at most ε times total flow mass times the sum of ε squared
times the sum of squared total flow mass and one and ε times the sum of one
and total flow mass, divided by one minus λ](goal). -/
lemma scaled_profile_descendant_loss_bound {B : ℕ} (T : BoundedTree B)
    (lam : ℝ) (hlam : MainLambda lam) (theta : List (Fin B) → ℝ)
    (htheta : IsFlow T theta)
    (hpotential : ∀ xi ∈ T.rays, pathPotential lam theta xi ≤ 1)
    (eps : ℝ) (heps : 0 ≤ eps) (N : ℕ) :
    let X := fun v => eps * normalizedFlow T lam theta v
    (∑ i ∈ Finset.range N, sqParam lam ^ i * ∑ v ∈ T.level i,
      X v * (T.weightedDescendantSum (lam ^ 3) X (N - i) v +
        ∑ k ∈ Finset.range (N - i),
          T.weightedDescendantSum (lam ^ 3) (fun u => X u ^ 2) k v)) ≤
      (eps * flowMass T theta) *
        (((flowMass T theta ^ 2 + 1) * eps ^ 2) / (1 - lam) +
          ((1 + flowMass T theta) * eps) / (1 - lam)) := by
  classical
  intro X
  have hterminal := scaled_profile_terminal_reindex T lam hlam theta htheta eps X N
  have hkernel := scaled_profile_kernel_reindex T lam hlam theta htheta eps X X N
  change _ = ∑ u ∈ T.level N, _ at hterminal
  have hsq : (fun u => (eps * normalizedFlow T lam theta u) * X u) =
      (fun u => X u ^ 2) := by funext u; dsimp only [X]; ring
  rw [hsq] at hkernel
  have heq : (∑ i ∈ Finset.range N, sqParam lam ^ i * ∑ v ∈ T.level i,
      X v * (T.weightedDescendantSum (lam ^ 3) X (N - i) v +
        ∑ k ∈ Finset.range (N - i),
          T.weightedDescendantSum (lam ^ 3) (fun u => X u ^ 2) k v)) =
      ∑ u ∈ T.level N, (eps * flowVertexMass T theta u) *
        ((∑ k ∈ Finset.range N, lam ^ k * ∑ i ∈ Finset.range (N - k),
          X (u.drop (N - i)) * X (u.drop (N - (i + k)))) +
          ∑ i ∈ Finset.range N, lam ^ (N - i) * X (u.drop (N - i))) := by
    simp only [mul_add, Finset.sum_add_distrib]
    rw [hterminal, hkernel]
    ring
  rw [heq]
  exact scaled_profile_averaged_path_loss_bound T lam hlam theta htheta hpotential eps heps N

-- @node: BoundedTree.weightedDescendantSum_mono
/-- If [the propagation weight c is nonnegative](hyp:hc) and [f is at most
g at every tree vertex](hyp:hfg), then [at every depth and tree vertex,
the weighted descendant sum of f is at most that of g](goal). -/
lemma BoundedTree.weightedDescendantSum_mono {B : ℕ} (T : BoundedTree B)
    (c : ℝ) (hc : 0 ≤ c) (f g : List (Fin B) → ℝ)
    (hfg : ∀ v ∈ T.verts, f v ≤ g v) :
    ∀ n v, v ∈ T.verts →
      T.weightedDescendantSum c f n v ≤ T.weightedDescendantSum c g n v := by
  classical
  intro n
  induction n with
  | zero => exact hfg
  | succ n ih =>
      intro v hv
      apply mul_le_mul_of_nonneg_left _ hc
      apply Finset.sum_le_sum
      intro w hw
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw
      exact ih _ (Finset.mem_filter.mp ha).2

-- @node: BoundedTree.weightedDescendantSum_mul_const
/-- For any real constant a, [the weighted descendant sum of a times a vertex
function equals a times the weighted descendant sum of that function](goal). -/
lemma BoundedTree.weightedDescendantSum_mul_const {B : ℕ} (T : BoundedTree B)
    (c a : ℝ) (f : List (Fin B) → ℝ) (n : ℕ) (v : List (Fin B)) :
    T.weightedDescendantSum c (fun u => a * f u) n v =
      a * T.weightedDescendantSum c f n v := by
  classical
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
      simp only [BoundedTree.weightedDescendantSum, ih, ← Finset.mul_sum]
      ring

-- @node: BoundedTree.weightedDescendantSum_envelope_step
/-- For any propagation weight c, initial values f, and vertex errors e,
[the (n plus one)-generation weighted descendant sum of f plus the sum of
weighted descendant errors from depths zero through n equals c times the
sum over children of their n-generation initial contribution plus their
errors from depths zero through n minus one, plus the error at the parent](goal). -/
lemma BoundedTree.weightedDescendantSum_envelope_step {B : ℕ} (T : BoundedTree B)
    (c : ℝ) (f e : List (Fin B) → ℝ) (n : ℕ) (v : List (Fin B)) :
    T.weightedDescendantSum c f (n + 1) v +
      (∑ k ∈ Finset.range (n + 1), T.weightedDescendantSum c e k v) =
        c * (∑ w ∈ T.children v, (T.weightedDescendantSum c f n w +
          ∑ k ∈ Finset.range n, T.weightedDescendantSum c e k w)) + e v := by
  classical
  rw [Finset.sum_range_succ']
  simp only [BoundedTree.weightedDescendantSum, Finset.sum_add_distrib, mul_add]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  ring

end OaiCapacityCriterionState

module

public import Papers.OaiCapacityCriterionState.Helpers.Trees

/-! # Converting recursively bounded labels to a flow

The edge coefficients scale the available child contribution to the desired parent
label. Multiplying these coefficients along paths gives the weights in the flow proof.
-/

@[expose] public section

open scoped BigOperators

namespace OaiCapacityCriterionState

variable {B : ℕ}

open Classical in
/-- For [a tree](hyp:T) with [branching bound](hyp:B), [a channel parameter](hyp:lam),
[real vertex labels](hyp:z), [a parent vertex](hyp:v), and [a candidate child](hyp:w),
the [edge coefficient](goal) first computes [the available supply as the sum over
children of the squared channel parameter times the child label divided by the
square root of one plus its square](step:1). It then [multiplies the parent label's
ratio to positive supply by the squared channel parameter divided by the square
root of one plus the candidate child's squared label, or returns zero if supply
is not positive](step:2).

@realizes d_{vw}(scale each child cap by the ratio of the parent label to available mass) -/
noncomputable def labelCoefficient (T : BoundedTree B) (lam : ℝ)
    (z : List (Fin B) → ℝ) (v w : List (Fin B)) : ℝ :=
  let supply := ∑ u ∈ T.children v, sqParam lam * z u / Real.sqrt (1 + z u ^ 2)
  if 0 < supply then
    (z v / supply) * (sqParam lam / Real.sqrt (1 + z w ^ 2))
  else 0

-- @node: labelCoefficient_spec
/-- Suppose [the tree is infinite with a positive branching bound](hyp:hT), [the
channel parameter lies strictly between zero and one](hyp:hlam), and [vertex labels
are nonnegative and bounded above by the sum of the squared channel parameter
times each child label divided by the square root of one plus its square](hyp:hz).
For [a vertex belonging to the tree](hyp:hv), [each child coefficient lies between
zero and the squared channel parameter divided by the square root of one plus the
child's squared label, and the parent label is the sum of child labels weighted
by these coefficients](goal). -/
lemma labelCoefficient_spec (T : BoundedTree B) (lam : ℝ) (z : List (Fin B) → ℝ)
    (hT : MainTree T) (hlam : MainLambda lam) (hz : FlowLabelRecursion T lam z)
    (v : List (Fin B)) (hv : v ∈ T.verts) :
    (∀ w ∈ T.children v, 0 ≤ labelCoefficient T lam z v w ∧
      labelCoefficient T lam z v w ≤
        sqParam lam / Real.sqrt (1 + z w ^ 2)) ∧ -- @realizes d_{vw}(coefficient range)
      z v = ∑ w ∈ T.children v, labelCoefficient T lam z v w * z w := by
  classical
  let supply := ∑ u ∈ T.children v, sqParam lam * z u / Real.sqrt (1 + z u ^ 2)
  have hzv := hz v hv
  have hr : 0 ≤ sqParam lam := sq_nonneg lam
  by_cases hs : 0 < supply
  · have hratio : 0 ≤ z v / supply := div_nonneg hzv.1 hs.le
    have hratio_le : z v / supply ≤ 1 := (div_le_one hs).2 hzv.2
    constructor
    · intro w hw
      have hcap : 0 ≤ sqParam lam / Real.sqrt (1 + z w ^ 2) :=
        div_nonneg hr (Real.sqrt_nonneg _)
      simp only [labelCoefficient, show (∑ u ∈ T.children v,
        sqParam lam * z u / Real.sqrt (1 + z u ^ 2)) = supply from rfl, if_pos hs]
      exact ⟨mul_nonneg hratio hcap, (mul_le_mul_of_nonneg_right hratio_le hcap).trans_eq
        (one_mul _)⟩
    · simp only [labelCoefficient, show (∑ u ∈ T.children v,
        sqParam lam * z u / Real.sqrt (1 + z u ^ 2)) = supply from rfl, if_pos hs]
      calc
        z v = (z v / supply) * supply := (div_mul_cancel₀ _ (ne_of_gt hs)).symm
        _ = ∑ w ∈ T.children v,
            (z v / supply * (sqParam lam / Real.sqrt (1 + z w ^ 2))) * z w := by
          dsimp [supply]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro w hw
          ring
  · have hz0 : z v = 0 := le_antisymm (hzv.2.trans (le_of_not_gt hs)) hzv.1
    simp only [labelCoefficient, show (∑ u ∈ T.children v,
      sqParam lam * z u / Real.sqrt (1 + z u ^ 2)) = supply from rfl, if_neg hs]
    constructor
    · intro w hw
      exact ⟨le_rfl, div_nonneg hr (Real.sqrt_nonneg _)⟩
    · simp [hz0]

/-- For [a tree](hyp:T) with [branching bound](hyp:B), [a channel parameter](hyp:lam),
and [real vertex labels](hyp:z), the [path weight of a vertex](goal) is [one at the
root](step:1) and [the parent's path weight times the coefficient of the edge to
the vertex elsewhere](step:2).

@realizes \ell_v(path-product weights with root weight one) -/
noncomputable def labelWeight (T : BoundedTree B) (lam : ℝ)
    (z : List (Fin B) → ℝ) : List (Fin B) → ℝ
  | [] => 1
  | a :: v => labelWeight T lam z v * labelCoefficient T lam z v (a :: v)

/-- For [a tree](hyp:T) with [branching bound](hyp:B), [a channel parameter](hyp:lam),
[real vertex labels](hyp:z), and [a vertex](hyp:v), the [scaled path weight](goal)
is its path weight multiplied by the squared channel parameter raised to the
negative vertex depth.

@realizes g_v(the path weight rescaled by r to minus the vertex depth) -/
noncomputable def scaledLabelWeight (T : BoundedTree B) (lam : ℝ)
    (z : List (Fin B) → ℝ) (v : List (Fin B)) : ℝ :=
  sqParam lam ^ (-(v.length : ℤ)) * labelWeight T lam z v

-- @node: label_weights_nonneg
/-- Suppose [the tree is infinite with a positive branching bound](hyp:hT), [the
channel parameter lies strictly between zero and one](hyp:hlam), and [vertex labels
are nonnegative and bounded above by the sum of the squared channel parameter
times each child label divided by the square root of one plus its square](hyp:hz).
At [any vertex belonging to the tree](hyp:hv), [both the path weight and its scaled
version are nonnegative](goal). -/
lemma label_weights_nonneg (T : BoundedTree B) (lam : ℝ) (z : List (Fin B) → ℝ)
    (hT : MainTree T) (hlam : MainLambda lam) (hz : FlowLabelRecursion T lam z)
    (v : List (Fin B)) (hv : v ∈ T.verts) :
    0 ≤ labelWeight T lam z v ∧ -- @realizes \ell_v(nonnegative finite path weight)
    0 ≤ scaledLabelWeight T lam z v := by -- @realizes g_v(nonnegative finite weight)
  have hweight : 0 ≤ labelWeight T lam z v := by
    induction v with
    | nil => exact zero_le_one
    | cons a v ih =>
      have hp := T.prefix_closed a v hv
      have hc : a :: v ∈ T.children v := by
        classical
        simp [BoundedTree.children, hv]
      exact mul_nonneg (ih hp) ((labelCoefficient_spec T lam z hT hlam hz v hp).1 _ hc).1
  exact ⟨hweight, mul_nonneg (zpow_nonneg (sq_nonneg lam) _) hweight⟩

-- @node: scaledLabelWeight_child
/-- If [the channel parameter lies strictly between zero and one](hyp:hlam), then
[the scaled path weight at a child times the squared channel parameter equals the
parent's scaled path weight times the coefficient of the edge to that child](goal).
-/
lemma scaledLabelWeight_child (T : BoundedTree B) (lam : ℝ)
    (z : List (Fin B) → ℝ) (hlam : MainLambda lam) (a : Fin B)
    (v : List (Fin B)) :
    scaledLabelWeight T lam z (a :: v) * sqParam lam =
      scaledLabelWeight T lam z v * labelCoefficient T lam z v (a :: v) := by
  have hr : sqParam lam ≠ 0 := pow_ne_zero _ (ne_of_gt hlam.1)
  simp only [scaledLabelWeight, labelWeight, List.length_cons, Nat.cast_add, Nat.cast_one]
  rw [neg_add, zpow_add₀ hr]
  simp only [zpow_neg_one]
  field_simp

-- @node: scaledLabelWeight_energy_step
/-- Suppose [the tree is infinite with a positive branching bound](hyp:hT), [the
channel parameter lies strictly between zero and one](hyp:hlam), and [vertex labels
are nonnegative and bounded above by the sum of the squared channel parameter
times each child label divided by the square root of one plus its square](hyp:hz).
If [the child belongs to the tree](hyp:hv), then [the squared product of its scaled
path weight and its label is at most the parent's squared scaled path weight minus
the child's squared scaled path weight](goal). -/
lemma scaledLabelWeight_energy_step (T : BoundedTree B) (lam : ℝ)
    (z : List (Fin B) → ℝ) (hT : MainTree T) (hlam : MainLambda lam)
    (hz : FlowLabelRecursion T lam z) (a : Fin B) (v : List (Fin B))
    (hv : a :: v ∈ T.verts) :
    (scaledLabelWeight T lam z (a :: v) * z (a :: v)) ^ 2 ≤
      scaledLabelWeight T lam z v ^ 2 - scaledLabelWeight T lam z (a :: v) ^ 2 := by
  have hp := T.prefix_closed a v hv
  have hc : a :: v ∈ T.children v := by
    classical
    simp [BoundedTree.children, hv]
  have hd := ((labelCoefficient_spec T lam z hT hlam hz v hp).1 _ hc).2
  have hg := (label_weights_nonneg T lam z hT hlam hz v hp).2
  have hgc := (label_weights_nonneg T lam z hT hlam hz (a :: v) hv).2
  have hr : 0 < sqParam lam := pow_pos hlam.1 _
  have hs : 0 < Real.sqrt (1 + z (a :: v) ^ 2) :=
    Real.sqrt_pos.2 (by positivity)
  have hd' := (le_div_iff₀ hs).mp hd
  have hrec := scaledLabelWeight_child T lam z hlam a v
  have hbound : scaledLabelWeight T lam z (a :: v) *
      Real.sqrt (1 + z (a :: v) ^ 2) ≤ scaledLabelWeight T lam z v := by
    apply (mul_le_mul_iff_right₀ hr).mp
    calc
      _ = scaledLabelWeight T lam z v *
          (labelCoefficient T lam z v (a :: v) * Real.sqrt (1 + z (a :: v) ^ 2)) := by
        calc
          _ = (scaledLabelWeight T lam z (a :: v) * sqParam lam) *
              Real.sqrt (1 + z (a :: v) ^ 2) := by ring
          _ = _ := by rw [hrec]; ring
      _ ≤ scaledLabelWeight T lam z v * sqParam lam :=
        mul_le_mul_of_nonneg_left hd' hg
      _ = _ := mul_comm _ _
  have hsq := (sq_le_sq₀ (mul_nonneg hgc hs.le) hg).2 hbound
  rw [mul_pow, Real.sq_sqrt (by positivity)] at hsq
  nlinarith

-- @node: lem:flow
/-- Suppose [the tree is infinite with a positive branching bound](hyp:hT), [the
channel parameter lies strictly between zero and one](hyp:hlam), and [vertex labels
are nonnegative and bounded above by the sum of the squared channel parameter
times each child label divided by the square root of one plus its square](hyp:hz).
Then [there exists a nonnegative flow supported on the tree, conserved at each
nonroot vertex, with total mass equal to the root label and path potential at
most one on every infinite ray; moreover, the root label is at most the tree's
3-capacity](goal). -/
lemma exists_flow_of_labels (T : BoundedTree B) (lam : ℝ) (z : List (Fin B) → ℝ)
    (hT : MainTree T) (hlam : MainLambda lam) (hz : FlowLabelRecursion T lam z) :
    (∃ theta : List (Fin B) → ℝ, IsFlow T theta ∧ flowMass T theta = z [] ∧
      ∀ xi ∈ T.rays, pathPotential lam theta xi ≤ 1) ∧
    ENNReal.ofReal (z []) ≤ capacity3 T lam := by
  classical
  let theta : List (Fin B) → ℝ := fun v =>
    if v ∈ T.verts then labelWeight T lam z v * z v else 0
  have hsum (v : List (Fin B)) (hv : v ∈ T.verts) :
      ∑ w ∈ T.children v, theta w = labelWeight T lam z v * z v := by
    conv_rhs => rw [(labelCoefficient_spec T lam z hT hlam hz v hv).2]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w hw
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw
    have ha' : a :: v ∈ T.verts := (Finset.mem_filter.mp ha).2
    simp only [theta, if_pos ha', labelWeight]
    ring
  have hflow : IsFlow T theta := by
    refine ⟨?_, ?_, ?_⟩
    · intro v
      dsimp [theta]
      split_ifs with hv
      · exact mul_nonneg (label_weights_nonneg T lam z hT hlam hz v hv).1 (hz v hv).1
      · exact le_rfl
    · intro v hv
      simp [theta, hv]
    · intro v hv hne
      simpa only [theta, if_pos hv] using (hsum v hv).symm
  have hmass : flowMass T theta = z [] := by
    simpa only [flowMass, labelWeight, one_mul] using hsum [] T.nil_mem
  have hpotential : ∀ xi ∈ T.rays, pathPotential lam theta xi ≤ 1 := by
    intro xi hxi
    have hlen (n : ℕ) : (rayPrefix xi n).length = n := by
      induction n with
      | zero => rfl
      | succ n ih => simp only [rayPrefix, List.length_cons, ih]
    have hterm (n : ℕ) :
        (lam ^ (-(2 * ((n + 1 : ℕ) : ℤ))) * theta (rayPrefix xi (n + 1))) ^ 2 =
          (scaledLabelWeight T lam z (rayPrefix xi (n + 1)) *
            z (rayPrefix xi (n + 1))) ^ 2 := by
      have hexp : sqParam lam ^ (-((rayPrefix xi (n + 1)).length : ℤ)) =
          lam ^ (-(2 * ((n + 1 : ℕ) : ℤ))) := by
        rw [hlen, show sqParam lam = lam ^ (2 : ℤ) by simp [sqParam], ← zpow_mul]
        congr 1
      simp only [theta, if_pos (hxi (n + 1)), scaledLabelWeight, hexp]
      ring
    have hfinite (n : ℕ) :
        ∑ i ∈ Finset.range n, (scaledLabelWeight T lam z (rayPrefix xi (i + 1)) *
          z (rayPrefix xi (i + 1))) ^ 2 ≤
            1 - scaledLabelWeight T lam z (rayPrefix xi n) ^ 2 := by
      induction n with
      | zero => simp [rayPrefix, scaledLabelWeight, labelWeight]
      | succ n ih =>
        rw [Finset.sum_range_succ]
        have hstep := scaledLabelWeight_energy_step T lam z hT hlam hz (xi n)
          (rayPrefix xi n) (hxi (n + 1))
        change (scaledLabelWeight T lam z (rayPrefix xi (n + 1)) *
          z (rayPrefix xi (n + 1))) ^ 2 ≤
          scaledLabelWeight T lam z (rayPrefix xi n) ^ 2 -
            scaledLabelWeight T lam z (rayPrefix xi (n + 1)) ^ 2 at hstep
        linarith
    unfold pathPotential
    apply ENNReal.tsum_le_of_sum_range_le
    intro n
    simp_rw [hterm]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _)]
    exact (ENNReal.ofReal_le_ofReal ((hfinite n).trans
      (sub_le_self _ (sq_nonneg _)))).trans_eq (by simp)
  constructor
  · exact ⟨theta, hflow, hmass, hpotential⟩
  · rw [← hmass]
    exact le_iSup_of_le theta (le_iSup_of_le hflow (le_iSup_of_le hpotential le_rfl))

end OaiCapacityCriterionState

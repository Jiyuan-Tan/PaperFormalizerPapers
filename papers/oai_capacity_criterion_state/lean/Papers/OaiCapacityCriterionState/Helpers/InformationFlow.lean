module

public import Papers.OaiCapacityCriterionState.Helpers.CompanionBounds
public import Papers.OaiCapacityCriterionState.Helpers.Flow
public import Mathlib.Algebra.BigOperators.Ring.List
public import Mathlib.Algebra.Order.BigOperators.Group.List

/-! # From companion information bounds to flow labels

The cubic transform is subadditive under finite products in the companion class.
After a channel step, a fixed positive rescaling of this transform satisfies the
nonlinear contraction appearing in the deterministic flow lemma.
-/

@[expose] public section

open MeasureTheory
open Filter Topology
open scoped BigOperators

namespace OaiCapacityCriterionState

-- @node: cubicInfoTransform
/-- For [a real information value](hyp:x), [the cubic information transform](goal)
adds one three-thousandth of its cube to the value itself. -/
noncomputable def cubicInfoTransform (x : ℝ) : ℝ := x + x ^ 3 / 3000

-- @node: cubicInfoScale
/-- For [a real contraction parameter](hyp:r), [the information scale](goal) is
one thousandth of one minus the square of that parameter. -/
noncomputable def cubicInfoScale (r : ℝ) : ℝ := (1 - r ^ 2) / 1000

-- @node: cubicInfoTransform_nonneg
/-- If [an information value is nonnegative](hyp:hx), [its cubic information
transform is nonnegative](goal). -/
lemma cubicInfoTransform_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ cubicInfoTransform x := by
  unfold cubicInfoTransform
  positivity

-- @node: cubicInfoTransform_pos
/-- If [an information value is positive](hyp:hx), [its cubic information
transform is positive](goal). -/
lemma cubicInfoTransform_pos {x : ℝ} (hx : 0 < x) :
    0 < cubicInfoTransform x := by
  unfold cubicInfoTransform
  positivity

-- @node: cubicInfoTransform_le_twice
/-- If [an information value lies between zero and three, inclusive](hyp:hx),
[its cubic information transform is at most twice the original value](goal). -/
lemma cubicInfoTransform_le_twice {x : ℝ} (hx : x ∈ Set.Icc 0 3) :
    cubicInfoTransform x ≤ 2 * x := by
  have hx0 := hx.1
  have hx3 := hx.2
  have hsq : x ^ 2 ≤ 9 := by nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx3)]
  have hcube := mul_le_mul_of_nonneg_right hsq hx.1
  unfold cubicInfoTransform
  nlinarith

-- @node: cubicInfoScale_pos
/-- If [the contraction parameter lies strictly between zero and one](hyp:hr),
[its information scale is positive](goal). -/
lemma cubicInfoScale_pos {r : ℝ} (hr : r ∈ Set.Ioo 0 1) :
    0 < cubicInfoScale r := by
  unfold cubicInfoScale
  nlinarith [mul_pos hr.1 (sub_pos.mpr hr.2)]

-- @node: cubicInfoTransform_channel_contraction
/-- If [the contraction parameter lies strictly between zero and one](hyp:hr) and
[the information value lies between zero and three, inclusive](hyp:hx), [the cubic
transform of their product is at most the parameter times the transform of the
information value, divided by the square root of one plus the square of the scaled
transform](goal). -/
lemma cubicInfoTransform_channel_contraction {r x : ℝ}
    (hr : r ∈ Set.Ioo 0 1) (hx : x ∈ Set.Icc 0 3) :
    cubicInfoTransform (r * x) ≤
      r * cubicInfoTransform x /
        Real.sqrt (1 + (cubicInfoScale r * cubicInfoTransform x) ^ 2) := by
  have hx0 := hx.1
  have hr0 := hr.1.le
  have hk := (cubicInfoScale_pos hr).le
  have hy := cubicInfoTransform_nonneg hx.1
  have ha := cubicInfoTransform_nonneg (mul_nonneg hr.1.le hx.1)
  have hyb := cubicInfoTransform_le_twice hx
  have hgap : r * cubicInfoTransform x - cubicInfoTransform (r * x) =
      r * (1 - r ^ 2) * x ^ 3 / 3000 := by
    unfold cubicInfoTransform
    ring
  have hd : 0 ≤ 1 - r ^ 2 := by
    have := cubicInfoScale_pos hr
    unfold cubicInfoScale at this
    linarith
  have ha_le : cubicInfoTransform (r * x) ≤ 2 * r * x := by
    have hsub : cubicInfoTransform (r * x) ≤ r * cubicInfoTransform x := by
      have : 0 ≤ r * (1 - r ^ 2) * x ^ 3 / 3000 := by positivity
      linarith
    exact hsub.trans (by nlinarith [mul_le_mul_of_nonneg_left hyb hr.1.le])
  have hkbound : 8 * cubicInfoScale r ^ 2 ≤ (1 - r ^ 2) / 3000 := by
    have hdd : (1 - r ^ 2) ^ 2 ≤ 1 - r ^ 2 := by
      nlinarith [mul_nonneg hd (sq_nonneg r)]
    unfold cubicInfoScale
    nlinarith
  have hz : cubicInfoScale r * cubicInfoTransform x ≤ cubicInfoScale r * (2 * x) :=
    mul_le_mul_of_nonneg_left hyb hk
  have hzsq : (cubicInfoScale r * cubicInfoTransform x) ^ 2 ≤
      (cubicInfoScale r * (2 * x)) ^ 2 :=
    (sq_le_sq₀ (mul_nonneg hk hy) (by positivity)).2 hz
  have hprod : cubicInfoTransform (r * x) *
      (cubicInfoScale r * cubicInfoTransform x) ^ 2 ≤
        r * (1 - r ^ 2) * x ^ 3 / 3000 := by
    calc
      _ ≤ (2 * r * x) * (cubicInfoScale r * (2 * x)) ^ 2 :=
        mul_le_mul ha_le hzsq (sq_nonneg _) (by positivity)
      _ = (r * x ^ 3) * (8 * cubicInfoScale r ^ 2) := by ring
      _ ≤ (r * x ^ 3) * ((1 - r ^ 2) / 3000) :=
        mul_le_mul_of_nonneg_left hkbound (by positivity)
      _ = _ := by ring
  have hsqrt : Real.sqrt (1 + (cubicInfoScale r * cubicInfoTransform x) ^ 2) ≤
      1 + (cubicInfoScale r * cubicInfoTransform x) ^ 2 := by
    have := Real.sqrt_one_add_le (x := (cubicInfoScale r * cubicInfoTransform x) ^ 2)
      (by nlinarith [sq_nonneg (cubicInfoScale r * cubicInfoTransform x)])
    nlinarith [sq_nonneg (cubicInfoScale r * cubicInfoTransform x)]
  apply (le_div_iff₀ (Real.sqrt_pos.2 (by positivity))).2
  calc
    _ ≤ cubicInfoTransform (r * x) *
        (1 + (cubicInfoScale r * cubicInfoTransform x) ^ 2) :=
      mul_le_mul_of_nonneg_left hsqrt ha
    _ ≤ r * cubicInfoTransform x := by nlinarith [hprod]

-- @node: companion_finite_product_bound
/-- Suppose [a class of experiment laws contains the uninformative law](hyp:hzero),
[is closed under combining two conditionally independent experiments](hyp:hstar),
and [the cubic transform of quadratic information for any such combination is at
most the sum of the two transformed informations](hyp:hsave). If [every law in a
finite list belongs to the class](hyp:hmus), [combining the list starting from the
uninformative law stays in the class and has transformed quadratic information at
most the sum of the list's transformed quadratic informations](goal). -/
lemma companion_finite_product_bound (C : Set (Measure (Fin 4 → ℝ)))
    (hzero : uninformativeLaw ∈ C)
    (hstar : ∀ mu ∈ C, ∀ nu ∈ C, starLaw mu nu ∈ C)
    (hsave : ∀ mu ∈ C, ∀ nu ∈ C,
      cubicInfoTransform (quadInfo (starLaw mu nu)) ≤
        cubicInfoTransform (quadInfo mu) + cubicInfoTransform (quadInfo nu))
    (mus : List (Measure (Fin 4 → ℝ))) (hmus : ∀ mu ∈ mus, mu ∈ C) :
    mus.foldr starLaw uninformativeLaw ∈ C ∧
      cubicInfoTransform (quadInfo (mus.foldr starLaw uninformativeLaw)) ≤
        (mus.map (fun mu => cubicInfoTransform (quadInfo mu))).sum := by
  induction mus with
  | nil =>
      refine ⟨hzero, ?_⟩
      simp only [List.foldr_nil, List.map_nil, List.sum_nil]
      rw [extreme_moments.2.1]
      norm_num [cubicInfoTransform]
  | cons mu mus ih =>
      have hm := hmus mu (by simp)
      obtain ⟨htail, hbound⟩ := ih (fun nu hnu => hmus nu (by simp [hnu]))
      refine ⟨hstar mu hm _ htail, ?_⟩
      simp only [List.foldr_cons, List.map_cons, List.sum_cons]
      exact (hsave mu hm _ htail).trans (add_le_add le_rfl hbound)

-- @node: companion_channel_product_label_bound
/-- Suppose [every member of a class is a posterior law](hyp:hC), [the class contains
the uninformative law](hyp:hzero), [channel updates with parameters between zero
and one inclusive preserve the class](hyp:hchannel), [combining conditionally
independent experiments preserves the class](hyp:hstar), and [the cubic transform
of quadratic information is subadditive under that combination](hyp:hsave).
If [the channel parameter lies strictly between zero and one](hyp:hlam) and
[every law in a finite list belongs to the class](hyp:hmus), [the scaled transformed
quadratic information after updating and combining the list is at most the sum,
over the original laws, of the squared channel parameter times each scaled
transformed information divided by the square root of one plus its square](goal). -/
lemma companion_channel_product_label_bound (C : Set (Measure (Fin 4 → ℝ)))
    (hC : ∀ mu ∈ C, IsPosteriorLaw mu)
    (hzero : uninformativeLaw ∈ C)
    (hchannel : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ mu ∈ C, channelStep t mu ∈ C)
    (hstar : ∀ mu ∈ C, ∀ nu ∈ C, starLaw mu nu ∈ C)
    (hsave : ∀ mu ∈ C, ∀ nu ∈ C,
      cubicInfoTransform (quadInfo (starLaw mu nu)) ≤
        cubicInfoTransform (quadInfo mu) + cubicInfoTransform (quadInfo nu))
    (lam : ℝ) (hlam : MainLambda lam)
    (mus : List (Measure (Fin 4 → ℝ))) (hmus : ∀ mu ∈ mus, mu ∈ C) :
    cubicInfoScale (sqParam lam) *
        cubicInfoTransform (quadInfo
          ((mus.map (channelStep lam)).foldr starLaw uninformativeLaw)) ≤
      (mus.map (fun mu => sqParam lam *
        (cubicInfoScale (sqParam lam) * cubicInfoTransform (quadInfo mu)) /
          Real.sqrt (1 +
            (cubicInfoScale (sqParam lam) * cubicInfoTransform (quadInfo mu)) ^ 2))).sum := by
  have hr := sqParam_mem_Ioo lam hlam
  have hk := (cubicInfoScale_pos hr).le
  have ht : IsChannelParameter lam := ⟨hlam.1.le, hlam.2.le⟩
  have hsmus : ∀ mu ∈ mus.map (channelStep lam), mu ∈ C := by
    intro mu hmu
    obtain ⟨nu, hnu, rfl⟩ := List.mem_map.mp hmu
    exact hchannel lam ht nu (hmus nu hnu)
  have hbound := (companion_finite_product_bound C hzero hstar hsave _ hsmus).2
  have hsingle (mu : Measure (Fin 4 → ℝ)) (hmu : mu ∈ mus) :
      cubicInfoScale (sqParam lam) * cubicInfoTransform (quadInfo (channelStep lam mu)) ≤
        sqParam lam * (cubicInfoScale (sqParam lam) * cubicInfoTransform (quadInfo mu)) /
          Real.sqrt (1 +
            (cubicInfoScale (sqParam lam) * cubicInfoTransform (quadInfo mu)) ^ 2) := by
    have hscale := congrArg Prod.fst (moments_channelStep lam ht mu (hC mu (hmus mu hmu)))
    change quadInfo (channelStep lam mu) = sqParam lam * quadInfo mu at hscale
    rw [hscale]
    have h := mul_le_mul_of_nonneg_left
      (cubicInfoTransform_channel_contraction hr
        (quadInfo_mem_Icc ⟨mu, hC mu (hmus mu hmu)⟩)) hk
    convert h using 1 <;> first | ring | rfl
  calc
    _ ≤ cubicInfoScale (sqParam lam) *
        ((mus.map (channelStep lam)).map
          (fun mu => cubicInfoTransform (quadInfo mu))).sum :=
      mul_le_mul_of_nonneg_left hbound hk
    _ = (mus.map (fun mu => cubicInfoScale (sqParam lam) *
        cubicInfoTransform (quadInfo (channelStep lam mu)))).sum := by
      rw [List.sum_map_mul_left]
      simp only [List.map_map, Function.comp_def]
    _ ≤ _ := List.sum_le_sum hsingle

-- @node: flow_labels_of_companion_experiment_limits
/-- Suppose [every member of an experiment class is a posterior law](hyp:hC),
[the uninformative law belongs to the class](hyp:hzero), [channel updates with
parameters between zero and one inclusive preserve the class](hyp:hchannel),
[combining conditionally independent experiments preserves the class](hyp:hstar),
and [the cubic transform of quadratic information is subadditive under combination](hyp:hsave).
If [the channel parameter lies strictly between zero and one](hyp:hlam),
[the experiment at every depth and tree vertex belongs to the class](hyp:hlaws),
[each next-depth experiment is obtained by channel-updating and combining the
current experiments at its children, starting from the uninformative law](hyp:hrec),
and [quadratic information at each vertex converges to its assigned real value](hyp:ha),
[the scaled cubic transforms of those limits are nonnegative vertex labels, each
bounded above by the sum over its children of the squared channel parameter times
the child's label divided by the square root of one plus that label's square](goal). -/
lemma flow_labels_of_companion_experiment_limits
    (C : Set (Measure (Fin 4 → ℝ)))
    (hC : ∀ mu ∈ C, IsPosteriorLaw mu)
    (hzero : uninformativeLaw ∈ C)
    (hchannel : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ mu ∈ C, channelStep t mu ∈ C)
    (hstar : ∀ mu ∈ C, ∀ nu ∈ C, starLaw mu nu ∈ C)
    (hsave : ∀ mu ∈ C, ∀ nu ∈ C,
      cubicInfoTransform (quadInfo (starLaw mu nu)) ≤
        cubicInfoTransform (quadInfo mu) + cubicInfoTransform (quadInfo nu))
    {B : ℕ} (T : BoundedTree B) (lam : ℝ) (hlam : MainLambda lam)
    (laws : ℕ → List (Fin B) → Measure (Fin 4 → ℝ))
    (hlaws : ∀ n v, v ∈ T.verts → laws n v ∈ C)
    (hrec : ∀ n v, v ∈ T.verts → laws (n + 1) v =
      (((T.children v).toList.map (laws n)).map (channelStep lam)).foldr
        starLaw uninformativeLaw)
    (a : List (Fin B) → ℝ)
    (ha : ∀ v ∈ T.verts, Tendsto (fun n => quadInfo (laws n v)) atTop (𝓝 (a v))) :
    FlowLabelRecursion T lam
      (fun v => cubicInfoScale (sqParam lam) * cubicInfoTransform (a v)) := by
  classical
  have hk := (cubicInfoScale_pos (sqParam_mem_Ioo lam hlam)).le
  have ha0 (v : List (Fin B)) (hv : v ∈ T.verts) : 0 ≤ a v :=
    ge_of_tendsto (ha v hv) (Eventually.of_forall fun n =>
      (quadInfo_mem_Icc ⟨laws n v, hC _ (hlaws n v hv)⟩).1)
  have hcont : Continuous (fun x : ℝ =>
      cubicInfoScale (sqParam lam) * cubicInfoTransform x) := by
    unfold cubicInfoTransform
    fun_prop
  have hz (v : List (Fin B)) (hv : v ∈ T.verts) :
      Tendsto (fun n => cubicInfoScale (sqParam lam) * cubicInfoTransform (quadInfo (laws n v)))
        atTop (𝓝 (cubicInfoScale (sqParam lam) * cubicInfoTransform (a v))) :=
    hcont.continuousAt.tendsto.comp (ha v hv)
  intro v hv
  refine ⟨mul_nonneg hk (cubicInfoTransform_nonneg (ha0 v hv)), ?_⟩
  have hfinite (n : ℕ) :
      cubicInfoScale (sqParam lam) * cubicInfoTransform (quadInfo (laws (n + 1) v)) ≤
        ∑ w ∈ T.children v,
          sqParam lam * (cubicInfoScale (sqParam lam) *
            cubicInfoTransform (quadInfo (laws n w))) /
              Real.sqrt (1 + (cubicInfoScale (sqParam lam) *
                cubicInfoTransform (quadInfo (laws n w))) ^ 2) := by
    rw [hrec n v hv]
    have hm : ∀ mu ∈ (T.children v).toList.map (laws n), mu ∈ C := by
      intro mu hmu
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hmu
      have hw' := Finset.mem_toList.mp hw
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw'
      exact hlaws n _ (Finset.mem_filter.mp hi).2
    have h := companion_channel_product_label_bound C hC hzero hchannel hstar hsave
      lam hlam _ hm
    simpa only [List.map_map, Function.comp_def, Finset.sum_map_toList] using h
  have hkernel : Continuous (fun z : ℝ => sqParam lam * z / Real.sqrt (1 + z ^ 2)) := by
    fun_prop (disch := intro z; exact ne_of_gt (Real.sqrt_pos.2 (by positivity)))
  have hright : Tendsto
      (fun n => ∑ w ∈ T.children v,
        sqParam lam * (cubicInfoScale (sqParam lam) *
          cubicInfoTransform (quadInfo (laws n w))) /
            Real.sqrt (1 + (cubicInfoScale (sqParam lam) *
              cubicInfoTransform (quadInfo (laws n w))) ^ 2)) atTop
      (𝓝 (∑ w ∈ T.children v,
        sqParam lam * (cubicInfoScale (sqParam lam) * cubicInfoTransform (a w)) /
          Real.sqrt (1 + (cubicInfoScale (sqParam lam) * cubicInfoTransform (a w)) ^ 2))) := by
    apply tendsto_finsetSum
    intro w hw
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
    exact hkernel.continuousAt.tendsto.comp (hz _ (Finset.mem_filter.mp hi).2)
  exact le_of_tendsto_of_tendsto
    ((hz v hv).comp (tendsto_add_atTop_nat 1)) hright (Eventually.of_forall hfinite)

-- @node: capacity_pos_of_companion_experiment_limits
/-- Suppose [every member of an experiment class is a posterior law](hyp:hC),
[the class contains the uninformative law](hyp:hzero), [channel updates with
parameters between zero and one inclusive preserve the class](hyp:hchannel),
[combining conditionally independent experiments preserves the class](hyp:hstar),
and [the cubic transform of quadratic information is subadditive under combination](hyp:hsave).
If [the tree is infinite with a strictly positive finite branching bound](hyp:hT),
[the channel parameter lies strictly between zero and one](hyp:hlam), [all experiments
at tree vertices belong to the class](hyp:hlaws), [each next-depth experiment combines
the channel-updated current experiments at its children, starting from the
uninformative law](hyp:hrec), [their quadratic informations converge at every vertex
to the assigned limits](hyp:ha), and [the root's limit is positive](hyp:hroot),
[the tree's order-three capacity is positive](goal). -/
theorem capacity_pos_of_companion_experiment_limits
    (C : Set (Measure (Fin 4 → ℝ)))
    (hC : ∀ mu ∈ C, IsPosteriorLaw mu)
    (hzero : uninformativeLaw ∈ C)
    (hchannel : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ mu ∈ C, channelStep t mu ∈ C)
    (hstar : ∀ mu ∈ C, ∀ nu ∈ C, starLaw mu nu ∈ C)
    (hsave : ∀ mu ∈ C, ∀ nu ∈ C,
      cubicInfoTransform (quadInfo (starLaw mu nu)) ≤
        cubicInfoTransform (quadInfo mu) + cubicInfoTransform (quadInfo nu))
    {B : ℕ} (T : BoundedTree B) (lam : ℝ) (hT : MainTree T) (hlam : MainLambda lam)
    (laws : ℕ → List (Fin B) → Measure (Fin 4 → ℝ))
    (hlaws : ∀ n v, v ∈ T.verts → laws n v ∈ C)
    (hrec : ∀ n v, v ∈ T.verts → laws (n + 1) v =
      (((T.children v).toList.map (laws n)).map (channelStep lam)).foldr
        starLaw uninformativeLaw)
    (a : List (Fin B) → ℝ)
    (ha : ∀ v ∈ T.verts, Tendsto (fun n => quadInfo (laws n v)) atTop (𝓝 (a v)))
    (hroot : 0 < a []) : 0 < capacity3 T lam := by
  have hlabels := flow_labels_of_companion_experiment_limits C hC hzero hchannel hstar hsave
    T lam hlam laws hlaws hrec a ha
  have hcapacity := (exists_flow_of_labels T lam _ hT hlam hlabels).2
  exact (ENNReal.ofReal_pos.mpr
    (mul_pos (cubicInfoScale_pos (sqParam_mem_Ioo lam hlam))
      (cubicInfoTransform_pos hroot))).trans_le hcapacity

-- @node: treeExperimentLaw
/-- For [a bounded tree](hyp:T) and [a channel parameter](hyp:lam), [the recursive
tree experiment law at a depth and vertex](goal) is [the fully revealing law at
depth zero](step:1); [at each subsequent depth it combines the channel-updated
previous-depth laws at the vertex's children, starting from the uninformative law](step:2). -/
noncomputable def treeExperimentLaw {B : ℕ} (T : BoundedTree B) (lam : ℝ) :
    ℕ → List (Fin B) → Measure (Fin 4 → ℝ)
  | 0, _ => revealingLaw
  | n + 1, v =>
      (((T.children v).toList.map (treeExperimentLaw T lam n)).map
        (channelStep lam)).foldr starLaw uninformativeLaw

-- @node: starLaw_foldr_mem
/-- If [a class contains the uninformative law](hyp:hzero), [is closed under
combining two conditionally independent experiments](hyp:hstar), and [contains
every law in a finite list](hyp:hmus), [combining that list starting from the
uninformative law produces a law in the class](goal). -/
lemma starLaw_foldr_mem (C : Set (Measure (Fin 4 → ℝ)))
    (hzero : uninformativeLaw ∈ C)
    (hstar : ∀ mu ∈ C, ∀ nu ∈ C, starLaw mu nu ∈ C)
    (mus : List (Measure (Fin 4 → ℝ))) (hmus : ∀ mu ∈ mus, mu ∈ C) :
    mus.foldr starLaw uninformativeLaw ∈ C := by
  induction mus with
  | nil => exact hzero
  | cons mu mus ih =>
      exact hstar mu (hmus mu (by simp)) _
        (ih (fun nu hnu => hmus nu (by simp [hnu])))

-- @node: treeExperimentLaw_mem
/-- If [a class contains the fully revealing law](hyp:hrevealing), [contains the
uninformative law](hyp:hzero), [is preserved by channel updates with parameters
between zero and one inclusive](hyp:hchannel), and [is closed under combining
conditionally independent experiments](hyp:hstar), then, for [a channel parameter
strictly between zero and one](hyp:hlam), [the recursive tree experiment law at
every depth and vertex address belongs to the class](goal). -/
lemma treeExperimentLaw_mem (C : Set (Measure (Fin 4 → ℝ)))
    (hrevealing : revealingLaw ∈ C) (hzero : uninformativeLaw ∈ C)
    (hchannel : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ mu ∈ C, channelStep t mu ∈ C)
    (hstar : ∀ mu ∈ C, ∀ nu ∈ C, starLaw mu nu ∈ C)
    {B : ℕ} (T : BoundedTree B) (lam : ℝ) (hlam : MainLambda lam)
    (n : ℕ) (v : List (Fin B)) : treeExperimentLaw T lam n v ∈ C := by
  induction n generalizing v with
  | zero => exact hrevealing
  | succ n ih =>
      apply starLaw_foldr_mem C hzero hstar
      intro mu hmu
      obtain ⟨nu, hnu, rfl⟩ := List.mem_map.mp hmu
      obtain ⟨w, _, rfl⟩ := List.mem_map.mp hnu
      exact hchannel lam ⟨hlam.1.le, hlam.2.le⟩ _ (ih w)

-- @node: capacity_pos_of_treeExperimentLaw_limits
/-- Assume [there exists a class of symmetric posterior laws containing the revealing
and uninformative laws, closed under channel updates and independent combination,
with the companion fourth-moment saving bound on combined quadratic information](hyp:hCompanion).
If [the tree is infinite with a strictly positive finite branching bound](hyp:hT),
[the channel parameter lies strictly between zero and one](hyp:hlam), [the quadratic
informations of the recursive tree experiments converge at every vertex to the
assigned limits](hyp:ha), and [the root's limit is positive](hyp:hroot), [the tree's
order-three capacity is positive](goal). -/
theorem capacity_pos_of_treeExperimentLaw_limits (hCompanion : CompanionMomentSaving)
    {B : ℕ} (T : BoundedTree B) (lam : ℝ) (hT : MainTree T) (hlam : MainLambda lam)
    (a : List (Fin B) → ℝ)
    (ha : ∀ v ∈ T.verts,
      Tendsto (fun n => quadInfo (treeExperimentLaw T lam n v)) atTop (𝓝 (a v)))
    (hroot : 0 < a []) : 0 < capacity3 T lam := by
  obtain ⟨C, hC, hrevealing, hzero, hchannel, hstar, hsave⟩ :=
    companion_class_cubic_saving hCompanion
  have hsave' : ∀ mu ∈ C, ∀ nu ∈ C,
      cubicInfoTransform (quadInfo (starLaw mu nu)) ≤
        cubicInfoTransform (quadInfo mu) + cubicInfoTransform (quadInfo nu) := by
    intro mu hmu nu hnu
    exact (hsave mu hmu nu hnu).2
  exact capacity_pos_of_companion_experiment_limits C (fun mu hmu => (hC mu hmu).1)
    hzero hchannel hstar hsave' T lam hT hlam (treeExperimentLaw T lam)
    (fun n v _ => treeExperimentLaw_mem C hrevealing hzero hchannel hstar T lam hlam n v)
    (fun _ _ _ => rfl) a ha hroot

end OaiCapacityCriterionState

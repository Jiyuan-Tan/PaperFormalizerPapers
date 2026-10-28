module

public import Papers.OaiNearInclusionsVon.Helpers.Amplification

/-! Algebraic identities for the concrete Hilbert-space amplification and diagonal maps. -/

@[expose] public section

namespace Papers.OaiNearInclusionsVon

variable {I E : Type*} [DecidableEq I]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- For [an index set](hyp:I), [a complex Hilbert space](hyp:E), and
[a fixed vector in that space](hyp:v), the [bounded elementary-tensor map](goal)
sends each scalar square-summable sequence to the vector-valued sequence obtained
by multiplying the fixed vector by each scalar coordinate. -/
-- @node: lpTensorRight
noncomputable def lpTensorRight (v : E) :
    lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => E) 2 :=
  lp.mapCLM 2 (fun _ : I => (ContinuousLinearMap.id ℂ ℂ).smulRight v)
    (norm_nonneg _) (fun _ => le_rfl)

omit [DecidableEq I] [CompleteSpace E] in
/-- For [a fixed vector](hyp:v), [a scalar square-summable sequence](hyp:x), and
[an index](hyp:i), [the elementary-tensor map at that index equals the scalar
coordinate times the fixed vector](goal). -/
-- @node: lpTensorRight_apply
lemma lpTensorRight_apply (v : E) (x : lp (fun _ : I => ℂ) 2) (i : I) :
    lpTensorRight v x i = x i • v := rfl

omit [CompleteSpace E] in
/-- For [a vector](hyp:v) and [an index](hyp:j), [the elementary-tensor map sends
the scalar sequence equal to one at that index and zero elsewhere to the
vector-valued sequence equal to that vector at the same index and zero elsewhere](goal). -/
-- @node: lpTensorRight_single
lemma lpTensorRight_single (v : E) (j : I) :
    lpTensorRight v (lp.single 2 j 1) = lp.single 2 j v := by
  ext i
  by_cases h : j = i <;> simp [lpTensorRight_apply, lp.single_apply, h]

/-- For [a bounded linear operator on scalar square-summable sequences](hyp:X),
[a vector](hyp:v), and [a scalar square-summable sequence](hyp:x), [applying the
amplification to their elementary tensor gives the elementary tensor of the
transformed scalar sequence with the same vector](goal). -/
-- @node: amplify_tensorRight
lemma amplify_tensorRight (X : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2)
    (v : E) (x : lp (fun _ : I => ℂ) 2) :
    amplify X (lpTensorRight v x) = lpTensorRight v (X x) := by
  have h : amplify X ∘L lpTensorRight v = lpTensorRight v ∘L X := by
    apply lp.ext_continuousLinearMap (by norm_num)
    intro j
    ext i
    simp only [ContinuousLinearMap.comp_apply, lp.singleContinuousLinearMap_apply,
      lpTensorRight_single,
      (amplify_spec X).1, lpTensorRight_apply]
  exact DFunLike.congr_fun h x

/-- [The amplification of the identity on scalar square-summable sequences is
the identity on vector-valued square-summable sequences](goal). -/
-- @node: amplify_one
lemma amplify_one :
    amplify (E := E) (1 : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2) = 1 := by
  apply lp.ext_continuousLinearMap (by norm_num)
  intro j
  ext v i
  simp only [ContinuousLinearMap.comp_apply, lp.singleContinuousLinearMap_apply,
    (amplify_spec (1 : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2)).1,
    one_apply_eq_self]
  by_cases h : j = i <;> simp [lp.single_apply, h]

/-- For [two bounded linear operators on scalar square-summable sequences](hyp:X,Y),
[the amplification of their composition equals the composition of their
amplifications in the same order](goal). -/
-- @node: amplify_mul
lemma amplify_mul (X Y : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2) :
    amplify (E := E) (X * Y) = amplify X * amplify Y := by
  apply lp.ext_continuousLinearMap (by norm_num)
  intro j
  ext v i
  have hY : amplify Y (lp.single 2 j v) = lpTensorRight v (Y (lp.single 2 j 1)) := by
    ext k
    exact (amplify_spec Y).1 k j v
  simp only [ContinuousLinearMap.comp_apply, lp.singleContinuousLinearMap_apply,
    mul_apply_eq_comp, hY, amplify_tensorRight, lpTensorRight_apply,
    (amplify_spec (X * Y)).1]

/-- For [a bounded linear operator on scalar square-summable sequences](hyp:X)
and [a row and a column index](hyp:i,j), [the corresponding matrix entry of its
adjoint is the complex conjugate of the original operator's entry with the
indices interchanged](goal). -/
-- @node: lp_scalar_star_entry
lemma lp_scalar_star_entry
    (X : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2) (i j : I) :
    star X (lp.single 2 j 1) i = star (X (lp.single 2 i 1) j) := by
  have h := ContinuousLinearMap.adjoint_inner_right X (lp.single 2 i 1) (lp.single 2 j 1)
  simpa [ContinuousLinearMap.star_eq_adjoint, lp.inner_single_left,
    lp.inner_single_right, RCLike.inner_apply] using h

/-- For [a bounded linear operator on scalar square-summable sequences](hyp:X),
[amplifying its adjoint gives the adjoint of its amplification](goal). -/
-- @node: amplify_star
lemma amplify_star (X : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2) :
    amplify (E := E) (star X) = star (amplify (E := E) X) := by
  apply lp.ext_continuousLinearMap (by norm_num)
  intro j
  apply ContinuousLinearMap.ext
  intro v
  apply lp.ext
  funext i
  apply ext_inner_left ℂ
  intro u
  change inner ℂ u (amplify (star X) (lp.single 2 j v) i) =
    inner ℂ u (star (amplify X) (lp.single 2 j v) i)
  have h := ContinuousLinearMap.adjoint_inner_right (amplify (E := E) X)
    (lp.single 2 i u) (lp.single 2 j v)
  simp only [← ContinuousLinearMap.star_eq_adjoint, lp.inner_single_left,
    lp.inner_single_right, (amplify_spec X).1] at h
  rw [h, (amplify_spec (star X)).1, lp_scalar_star_entry]
  simp [inner_smul_left, inner_smul_right]

/-- For [a bounded linear operator on scalar square-summable sequences](hyp:X),
if [the operator is unitary](hyp:hX), then [its amplification on vector-valued
square-summable sequences is unitary](goal). -/
-- @node: amplify_mem_unitary
lemma amplify_mem_unitary
    (X : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2)
    (hX : X ∈ unitary _) :
    amplify (E := E) X ∈ unitary (lp (fun _ : I => E) 2 →L[ℂ] lp (fun _ : I => E) 2) := by
  apply Unitary.mem_iff.mpr
  constructor
  · rw [← amplify_star, ← amplify_mul, Unitary.star_mul_self_of_mem hX, amplify_one]
  · rw [← amplify_star, ← amplify_mul, Unitary.mul_star_self_of_mem hX, amplify_one]

/-- For [two bounded linear operators on scalar square-summable sequences](hyp:X,Y),
[the amplification of their sum equals the sum of their amplifications](goal). -/
-- @node: amplify_add
lemma amplify_add (X Y : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2) :
    amplify (E := E) (X + Y) = amplify X + amplify Y := by
  apply lp.ext_continuousLinearMap (by norm_num)
  intro j
  ext v i
  simp [(amplify_spec _).1, add_smul]

/-- For [a complex scalar](hyp:c) and [a bounded linear operator on scalar
square-summable sequences](hyp:X), [amplifying the scalar multiple of the operator
equals that scalar times its amplification](goal). -/
-- @node: amplify_smul
lemma amplify_smul (c : ℂ)
    (X : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2) :
    amplify (E := E) (c • X) = c • amplify X := by
  apply lp.ext_continuousLinearMap (by norm_num)
  intro j
  ext v i
  simp [(amplify_spec _).1, smul_smul]

omit [DecidableEq I] in
/-- For [an indexed family of bounded linear operators on the Hilbert space](hyp:F),
if [a common norm bound is nonnegative](hyp:hK) and [each operator's norm is at most
that bound](hyp:hF), then [the adjoint of the operator acting coordinate by coordinate
is the operator acting coordinate by coordinate with the adjoint family](goal). -/
-- @node: lpMap_star
lemma lpMap_star (F : I → E →L[ℂ] E) {K : ℝ}
    (hK : 0 ≤ K) (hF : ∀ i, ‖F i‖ ≤ K) :
    star (lp.mapCLM 2 F hK hF) =
      lp.mapCLM 2 (fun i => star (F i)) hK (fun i => by simpa using hF i) := by
  symm
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro i
  exact ContinuousLinearMap.adjoint_inner_left (F i) (y i) (x i)

omit [DecidableEq I] in
/-- For [an indexed family of bounded linear operators on the Hilbert space](hyp:F),
if [a common norm bound is nonnegative](hyp:hK), [every operator's norm is at most
that bound](hyp:hF), and [every operator in the family is unitary](hyp:hU), then
[the operator acting coordinate by coordinate on vector-valued square-summable
sequences is unitary](goal). -/
-- @node: lpMap_mem_unitary
lemma lpMap_mem_unitary (F : I → E →L[ℂ] E) {K : ℝ}
    (hK : 0 ≤ K) (hF : ∀ i, ‖F i‖ ≤ K) (hU : ∀ i, F i ∈ unitary _) :
    lp.mapCLM 2 F hK hF ∈ unitary (lp (fun _ : I => E) 2 →L[ℂ] lp (fun _ : I => E) 2) := by
  apply Unitary.mem_iff.mpr
  rw [lpMap_star]
  constructor
  · ext x i
    change (star (F i) * F i) (x i) = x i
    rw [Unitary.star_mul_self_of_mem (hU i), one_apply_eq_self]
  · ext x i
    change (F i * star (F i)) (x i) = x i
    rw [Unitary.mul_star_self_of_mem (hU i), one_apply_eq_self]

/-- For [a bounded linear operator on scalar square-summable sequences](hyp:X)
and [a bounded linear operator on the Hilbert space](hyp:T), [the amplification
of the scalar operator commutes with applying the Hilbert-space operator to
every coordinate](goal). -/
-- @node: amplify_commute_lpMap
lemma amplify_commute_lpMap
    (X : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2) (T : E →L[ℂ] E) :
    Commute (amplify (E := E) X)
      (lp.mapCLM 2 (fun _ : I => T) (norm_nonneg T) (fun _ => le_rfl)) := by
  change amplify X * _ = _ * amplify X
  apply lp.ext_continuousLinearMap (by norm_num)
  intro j
  ext v i
  have hsingle : lp.mapCLM 2 (fun _ : I => T) (norm_nonneg T) (fun _ => le_rfl)
      (lp.single 2 j v) = lp.single 2 j (T v) := by
    ext k
    by_cases h : j = k <;> simp [lp.single_apply, h]
  simp only [ContinuousLinearMap.comp_apply, lp.singleContinuousLinearMap_apply,
    mul_apply_eq_comp, hsingle, (amplify_spec X).1]
  change (X (lp.single 2 j 1) i) • T v = T (amplify X (lp.single 2 j v) i)
  rw [(amplify_spec X).1, map_smul]

end Papers.OaiNearInclusionsVon

module

public import Papers.OaiNearInclusionsVon.Helpers.AmplificationAlgebra
public import Mathlib.Analysis.Normed.Module.RCLike.Real

/-! Scalar slices recover the bicommutant of an amplified family of operators. -/

@[expose] public section

namespace Papers.OaiNearInclusionsVon

variable {I E : Type*} [DecidableEq I]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

-- @node: lpScalarSlice
/-- For [coordinates indexed by I](hyp:I), [a complex Hilbert space E](hyp:E), and
[a fixed vector v in E](hyp:v), the [scalar slice](goal) takes the inner product
with v in each coordinate of a square-summable E-valued sequence. -/
noncomputable def lpScalarSlice (v : E) :
    lp (fun _ : I => E) 2 →L[ℂ] lp (fun _ : I => ℂ) 2 :=
  lp.mapCLM 2 (fun _ : I => innerSL ℂ v) (norm_nonneg _) (fun _ => le_rfl)

-- @node: lpScalarSlice_apply
omit [DecidableEq I] [CompleteSpace E] in
/-- For [a slicing vector v](hyp:v), [a square-summable vector-valued sequence x](hyp:x),
and [a coordinate i](hyp:i), [the scalar slice at i is the inner product of v with
the i-th coordinate of x](goal). -/
lemma lpScalarSlice_apply (v : E) (x : lp (fun _ : I => E) 2) (i : I) :
    lpScalarSlice v x i = inner ℂ v (x i) := rfl

-- @node: lpScalarSlice_single
omit [CompleteSpace E] in
/-- For [vectors v and w](hyp:v,w) and [a coordinate j](hyp:j), [slicing the sequence
supported at j with value w gives the scalar sequence supported at j with value
equal to the inner product of v and w](goal). -/
lemma lpScalarSlice_single (v w : E) (j : I) :
    lpScalarSlice v (lp.single 2 j w) = lp.single 2 j (inner ℂ v w) := by
  ext i
  by_cases h : j = i <;> simp [lpScalarSlice_apply, lp.single_apply, h]

-- @node: lpScalarSlice_amplify
/-- For [a bounded operator X on scalar square-summable sequences](hyp:X) and
[a slicing vector v](hyp:v), [slicing after the amplification of X equals applying
X after slicing](goal). -/
lemma lpScalarSlice_amplify
    (X : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2) (v : E) :
    lpScalarSlice v ∘L amplify X = X ∘L lpScalarSlice v := by
  apply lp.ext_continuousLinearMap (by norm_num)
  intro j
  apply ContinuousLinearMap.ext
  intro w
  apply lp.ext
  funext i
  simp only [ContinuousLinearMap.comp_apply, lp.singleContinuousLinearMap_apply,
    lpScalarSlice_apply, (amplify_spec X).1, inner_smul_right,
    lpScalarSlice_single]
  have hs : (lp.single 2 j (inner ℂ v w) : lp (fun _ : I => ℂ) 2) = (inner ℂ v w) • lp.single 2 j 1 := by
    ext k
    by_cases h : j = k <;> simp [lp.single_apply, h]
  rw [hs, map_smul]
  simp [mul_comm]

-- @node: lpScalarSlice_tensorRight
omit [DecidableEq I] [CompleteSpace E] in
/-- For [vectors v and w](hyp:v,w) and [a scalar square-summable sequence x](hyp:x),
[slicing the tensor of x with w multiplies x by the inner product of v and w](goal). -/
lemma lpScalarSlice_tensorRight (v w : E) (x : lp (fun _ : I => ℂ) 2) :
    lpScalarSlice v (lpTensorRight w x) = (inner ℂ v w) • x := by
  ext i
  simp [lpScalarSlice_apply, lpTensorRight_apply, inner_smul_right, mul_comm]

-- @node: amplify_injective
/-- When the second Hilbert factor is nonzero, [distinct bounded operators have
distinct amplifications](goal). -/
lemma amplify_injective [Nontrivial E] :
    Function.Injective (amplify (I := I) (E := E)) := by
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  intro X Y h
  apply lp.ext_continuousLinearMap (by norm_num)
  intro j
  apply ContinuousLinearMap.ext
  intro c
  apply lp.ext
  funext i
  have hh := congrArg (fun T => T (lp.single 2 j v) i) h
  simp only [(amplify_spec X).1, (amplify_spec Y).1] at hh
  have he := (smul_left_injective ℂ hv) hh
  have hs : (lp.single 2 j c : lp (fun _ : I => ℂ) 2) = c • lp.single 2 j 1 := by
    ext k
    by_cases h : j = k <;> simp [lp.single_apply, h]
  simp only [ContinuousLinearMap.comp_apply, lp.singleContinuousLinearMap_apply,
    hs, map_smul, lp.coeFn_smul, Pi.smul_apply, he]

-- @node: operatorScalarSlice
/-- For [coordinates indexed by I](hyp:I), [a complex Hilbert space E](hyp:E),
[a bounded operator Y on E-valued square-summable sequences](hyp:Y), and
[vectors v and w in E](hyp:v,w), the [operator scalar slice](goal) tensors a scalar
sequence with w, applies Y, and then takes the inner product with v in each coordinate. -/
noncomputable def operatorScalarSlice
    (Y : lp (fun _ : I => E) 2 →L[ℂ] lp (fun _ : I => E) 2) (v w : E) :=
  lpScalarSlice v ∘L Y ∘L lpTensorRight w

-- @node: operatorScalarSlice_commute
/-- For [a scalar-sequence operator X](hyp:X) and [a vector-sequence operator Y](hyp:Y),
if [the amplification of X commutes with Y](hyp:h), then for [any slicing vectors
v and w](hyp:v,w), [X commutes with the corresponding scalar slice of Y](goal). -/
lemma operatorScalarSlice_commute
    (X : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2)
    (Y : lp (fun _ : I => E) 2 →L[ℂ] lp (fun _ : I => E) 2)
    (h : Commute (amplify X) Y) (v w : E) :
    Commute X (operatorScalarSlice Y v w) := by
  apply ContinuousLinearMap.ext
  intro x
  change X (lpScalarSlice v (Y (lpTensorRight w x))) =
    lpScalarSlice v (Y (lpTensorRight w (X x)))
  have hs := DFunLike.congr_fun (lpScalarSlice_amplify X v) (Y (lpTensorRight w x))
  simp only [ContinuousLinearMap.comp_apply] at hs
  rw [← hs, ← amplify_tensorRight]
  exact congrArg (lpScalarSlice v) (DFunLike.congr_fun h.eq (lpTensorRight w x))

-- @node: amplify_commute_of_scalarSlices
/-- For [a scalar-sequence operator X](hyp:X) and [a vector-sequence operator Y](hyp:Y),
if [X commutes with every scalar slice of Y](hyp:h), then [the amplification of X
commutes with Y](goal). -/
lemma amplify_commute_of_scalarSlices
    (X : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2)
    (Y : lp (fun _ : I => E) 2 →L[ℂ] lp (fun _ : I => E) 2)
    (h : ∀ v w : E, Commute X (operatorScalarSlice Y v w)) :
    Commute (amplify X) Y := by
  apply lp.ext_continuousLinearMap (by norm_num)
  intro j
  apply ContinuousLinearMap.ext
  intro w
  apply lp.ext
  funext i
  apply ext_inner_left ℂ
  intro v
  have hc := congrArg (fun T => T (lp.single 2 j 1) i) (h v w).eq
  simp only [mul_apply_eq_comp, operatorScalarSlice, ContinuousLinearMap.comp_apply,
    lpTensorRight_single] at hc
  have hs := congrArg (fun z => z i)
    (DFunLike.congr_fun (lpScalarSlice_amplify X v) (Y (lp.single 2 j w)))
  simp only [ContinuousLinearMap.comp_apply] at hs
  change lpScalarSlice v (amplify X (Y (lp.single 2 j w))) i =
    lpScalarSlice v (Y (amplify X (lp.single 2 j w))) i
  rw [hs, hc]
  rw [← amplify_tensorRight, lpTensorRight_single]

-- @node: eq_amplify_of_commute_fibers
/-- On a nonzero second Hilbert factor, if [a bounded vector-sequence operator Z](hyp:Z)
[commutes with every bounded operator applied identically in each coordinate](hyp:h),
then [Z is the amplification of some bounded scalar-sequence operator](goal). -/
lemma eq_amplify_of_commute_fibers [Nontrivial E]
    (Z : lp (fun _ : I => E) 2 →L[ℂ] lp (fun _ : I => E) 2)
    (h : ∀ T : E →L[ℂ] E,
      Commute Z (lp.mapCLM 2 (fun _ : I => T) (norm_nonneg T) (fun _ => le_rfl))) :
    ∃ X, Z = amplify (E := E) X := by
  obtain ⟨v, hv⟩ := exists_norm_eq E (show (0 : ℝ) ≤ 1 by norm_num)
  have hvv : inner ℂ v v = 1 := by simp [inner_self_eq_norm_sq_to_K, hv]
  let X := operatorScalarSlice Z v v
  refine ⟨X, ?_⟩
  apply lp.ext_continuousLinearMap (by norm_num)
  intro j
  apply ContinuousLinearMap.ext
  intro w
  apply lp.ext
  funext i
  have hc := congrArg (fun T => T (lp.single 2 j v) i)
    (h (InnerProductSpace.rankOne ℂ w v)).eq
  have he : lp.mapCLM 2 (fun _ : I => InnerProductSpace.rankOne ℂ w v)
      (norm_nonneg _) (fun _ => le_rfl) (lp.single 2 j v) = lp.single 2 j w := by
    ext k
    by_cases hj : j = k <;> simp [lp.single_apply, hj, hv]
  simp only [mul_apply_eq_comp, he, lp.mapCLM_apply_coe,
    InnerProductSpace.rankOne_apply] at hc
  change Z (lp.single 2 j w) i = amplify X (lp.single 2 j w) i
  rw [(amplify_spec X).1]
  simpa only [X, operatorScalarSlice, ContinuousLinearMap.comp_apply,
    lpTensorRight_single, lpScalarSlice_apply] using hc

-- @node: amplification_bicommutant
/-- For [an arbitrary family S of bounded scalar-sequence operators](hyp:S) and a
nonzero second Hilbert factor, [the bicommutant of the amplified family equals the
amplification of the bicommutant of S](goal). -/
lemma amplification_bicommutant [Nontrivial E]
    (S : Set (lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2)) :
    Set.centralizer (Set.centralizer (amplify (E := E) '' S)) =
      amplify (E := E) '' Set.centralizer (Set.centralizer S) := by
  ext Z
  constructor
  · intro hZ
    obtain ⟨X, rfl⟩ := eq_amplify_of_commute_fibers Z (fun T => by
      apply Commute.symm
      apply hZ
      rintro _ ⟨s, hs, rfl⟩
      exact (amplify_commute_lpMap s T).eq)
    refine ⟨X, ?_, rfl⟩
    intro R hR
    apply amplify_injective (E := E)
    rw [amplify_mul, amplify_mul]
    apply hZ
    rintro _ ⟨s, hs, rfl⟩
    rw [← amplify_mul, ← amplify_mul, hR s hs]
  · rintro ⟨X, hX, rfl⟩
    intro Y hY
    apply Commute.symm
    apply amplify_commute_of_scalarSlices
    intro v w
    apply Commute.symm
    apply hX
    intro s hs
    exact (operatorScalarSlice_commute s Y (hY _ ⟨s, hs, rfl⟩) v w).eq

-- @node: centralizer_image_mulEquiv
/-- For [a multiplication-preserving bijection e of a multiplicative system to itself](hyp:e)
and [a subset S of that system](hyp:S), [the centralizer of the image of S is the
image of the centralizer of S](goal). -/
lemma centralizer_image_mulEquiv {R : Type*} [Mul R] (e : R ≃* R) (S : Set R) :
    Set.centralizer (e '' S) = e '' Set.centralizer S := by
  ext z
  constructor
  · intro hz
    refine ⟨e.symm z, ?_, e.apply_symm_apply z⟩
    intro s hs
    apply e.injective
    simp only [map_mul, e.apply_symm_apply]
    exact hz (e s) ⟨s, hs, rfl⟩
  · rintro ⟨z, hz, rfl⟩ y ⟨s, hs, rfl⟩
    rw [← map_mul, ← map_mul, hz s hs]

-- @node: unitaryConjugation
/-- For [coordinates indexed by I](hyp:I), [a complex Hilbert space E](hyp:E), and
[a bounded operator W on E-valued square-summable sequences](hyp:W) that
[is unitary](hyp:hW), [unitary conjugation](goal) is the multiplication-preserving
bijection sending each operator X to W times X times the adjoint of W. -/
noncomputable def unitaryConjugation
    (W : lp (fun _ : I => E) 2 →L[ℂ] lp (fun _ : I => E) 2)
    (hW : W ∈ unitary _) :
    (lp (fun _ : I => E) 2 →L[ℂ] lp (fun _ : I => E) 2) ≃*
      (lp (fun _ : I => E) 2 →L[ℂ] lp (fun _ : I => E) 2) where
  toFun X := W * X * star W
  invFun X := star W * X * W
  left_inv X := by
    simp only [mul_assoc, ← mul_assoc (star W) W,
      Unitary.star_mul_self_of_mem hW, one_mul, mul_one]
  right_inv X := by
    simp only [mul_assoc, ← mul_assoc W (star W),
      Unitary.mul_star_self_of_mem hW, one_mul, mul_one]
  map_mul' X Y := by
    simp only [mul_assoc, ← mul_assoc (star W) W,
      Unitary.star_mul_self_of_mem hW, one_mul]

-- @node: conjugated_amplification_bicommutant
/-- For [a family S of bounded scalar-sequence operators](hyp:S) and
[a bounded vector-sequence operator W](hyp:W) that [is unitary](hyp:hW), with a
nonzero second Hilbert factor, [the bicommutant of the W-conjugated amplified family
consists exactly of the W-conjugated amplifications of operators in the bicommutant
of S](goal). -/
lemma conjugated_amplification_bicommutant [Nontrivial E]
    (S : Set (lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2))
    (W : lp (fun _ : I => E) 2 →L[ℂ] lp (fun _ : I => E) 2)
    (hW : W ∈ unitary _) :
    Set.centralizer (Set.centralizer
      ((fun X => W * amplify (E := E) X * star W) '' S)) =
      {Z | ∃ X ∈ Set.centralizer (Set.centralizer S),
        Z = W * amplify (E := E) X * star W} := by
  let e := unitaryConjugation W hW
  have he : (fun X => W * amplify (E := E) X * star W) '' S =
      e '' (amplify (E := E) '' S) := by
    exact (Set.image_image e (amplify (E := E)) S).symm
  rw [he, centralizer_image_mulEquiv, centralizer_image_mulEquiv,
    amplification_bicommutant]
  ext Z
  constructor
  · rintro ⟨_, ⟨X, hX, rfl⟩, rfl⟩
    exact ⟨X, hX, rfl⟩
  · rintro ⟨X, hX, rfl⟩
    exact ⟨amplify X, ⟨X, hX, rfl⟩, rfl⟩

end Papers.OaiNearInclusionsVon

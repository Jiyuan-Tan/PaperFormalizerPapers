module

public import Papers.OaiPairedStatesHamiltonian.Helpers.GlobalGradients
public import Mathlib.Algebra.BigOperators.Pi

/-! Restricting an orthogonal gradient decomposition to retained coordinates.
The face potentials are exactly those constant across the discarded coordinates. -/

@[expose] public section
namespace OaiPairedStatesHamiltonian

set_option linter.style.openClassical false
open Classical
attribute [local instance] propDecidable
set_option linter.style.openClassical false
set_option backward.isDefEq.respectTransparency false

variable {E X Y Z : Type} [Fintype E] [DecidableEq E]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [AddCommGroup Z] [Module ℝ Z]

-- @node: restrictedGradientMap
/-- Given [a linear map from the first potential space to real coordinates](hyp:A),
[a linear map from the second potential space to those coordinates](hyp:B),
[a linear map into the second potential space](hyp:C), and [a retained coordinate set](hyp:S),
the [restricted gradient map](goal) adds the first coordinate vector to the second coordinate
vector obtained after mapping the other input into the second potential space, and retains only
coordinates in the selected set. -/
noncomputable def restrictedGradientMap (A : X →ₗ[ℝ] (E → ℝ))
    (B : Y →ₗ[ℝ] (E → ℝ)) (C : Z →ₗ[ℝ] Y) (S : Set E) :
    (X × Z) →ₗ[ℝ] (S → ℝ) where
  toFun x e := A x.1 e.val + B (C x.2) e.val
  map_add' x y := by ext e; simp; ring
  map_smul' c x := by ext e; simp; ring

-- @node: finite_functional_coordinates
/-- [A real linear functional on a finite coordinate space evaluates any vector as the sum
of its coordinates times the functional's values on the corresponding unit coordinate vectors](goal). -/
lemma finite_functional_coordinates (L : (E → ℝ) →ₗ[ℝ] ℝ) (x : E → ℝ) :
    L x = ∑ e, x e * L (Pi.single e 1) := by
  conv_lhs => rw [pi_eq_sum_univ' x]
  simp only [map_sum, map_smul, smul_eq_mul]

-- @node: restrictedGradientMap_surjective
/-- Suppose [every coordinate vector is a sum of images of the two linear maps](hyp:hfull),
[these two images are orthogonal under the sum of coordinate products](hyp:horth), and
[every second-space potential whose image vanishes outside the retained set comes from the
third potential space](hyp:hfactor). Then [every real vector on the retained coordinates is
the restriction of the sum of a first-map image and a second-map image obtained through the
third-space map](goal). -/
lemma restrictedGradientMap_surjective (A : X →ₗ[ℝ] (E → ℝ))
    (B : Y →ₗ[ℝ] (E → ℝ)) (C : Z →ₗ[ℝ] Y) (S : Set E)
    (hfull : ∀ z : E → ℝ, ∃ a b, z = A a + B b)
    (horth : ∀ a b, (∑ e, A a e * B b e) = 0)
    (hfactor : ∀ b, (∀ e, e ∉ S → B b e = 0) → ∃ c, C c = b) :
    Function.Surjective (restrictedGradientMap A B C S) := by
  let F := restrictedGradientMap A B C S
  apply LinearMap.dualMap_injective_iff.mp
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro L hL
  have annihilate (a : X × Z) : L (F a) = 0 := congrArg (fun f => f a) hL
  let res : (E → ℝ) →ₗ[ℝ] (S → ℝ) :=
    { toFun := fun z e => z e.val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let L' : (E → ℝ) →ₗ[ℝ] ℝ := L.comp res
  let z : E → ℝ := fun e => L' (Pi.single e 1)
  have hzoutside (e : E) (he : e ∉ S) : z e = 0 := by
    have hz : res (Pi.single e 1) = 0 := by
      ext j
      simp only [res, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
      apply Pi.single_eq_of_ne
      intro h
      exact he (h ▸ j.property)
    change L (res (Pi.single e 1)) = 0
    rw [hz, map_zero]
  obtain ⟨a, b, hab⟩ := hfull z
  have hAa : L' (A a) = 0 := by
    simpa only [L', res, LinearMap.comp_apply, F, restrictedGradientMap, LinearMap.coe_mk, AddHom.coe_mk,
      Prod.fst, Prod.snd, map_zero, Pi.zero_apply, add_zero] using annihilate (a, 0)
  have haa : (∑ e, (A a e) ^ 2) = 0 := by
    have h := finite_functional_coordinates L' (A a)
    change L' (A a) = ∑ e, A a e * z e at h
    rw [hAa] at h
    have hterms : (∑ e, A a e * z e) =
        (∑ e, (A a e) ^ 2) + ∑ e, A a e * B b e := by
      rw [hab]
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, pow_two]
    rw [hterms, horth, add_zero] at h
    exact h.symm
  have hAz : A a = 0 := by
    ext e
    exact sq_eq_zero_iff.mp
      ((Finset.sum_eq_zero_iff_of_nonneg (fun e _ => sq_nonneg (A a e))).mp haa e
        (Finset.mem_univ _))
  have hzb : z = B b := by simpa only [hAz, zero_add] using hab
  obtain ⟨c, hc⟩ := hfactor b (fun e he => by rw [← hzb]; exact hzoutside e he)
  have hLz : L' z = 0 := by
    have h := annihilate (0, c)
    simpa only [L', res, LinearMap.comp_apply, F, restrictedGradientMap, LinearMap.coe_mk, AddHom.coe_mk,
      Prod.fst, Prod.snd, hc, map_zero, Pi.zero_apply, zero_add, hzb] using h
  have hzz : (∑ e, (z e) ^ 2) = 0 := by
    have h := finite_functional_coordinates L' z
    change L' z = ∑ e, z e * z e at h
    simpa only [hLz, ← pow_two] using h.symm
  have hz : z = 0 := by
    ext e
    exact sq_eq_zero_iff.mp
      ((Finset.sum_eq_zero_iff_of_nonneg (fun e _ => sq_nonneg (z e))).mp hzz e
        (Finset.mem_univ _))
  have hL' (x : E → ℝ) : L' x = 0 := by
    rw [finite_functional_coordinates L' x]
    change (∑ e, x e * z e) = 0
    simp only [hz, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  apply LinearMap.ext
  intro x
  let extx : E → ℝ := fun e => if he : e ∈ S then x ⟨e, he⟩ else 0
  have hext : res extx = x := by ext e; exact dif_pos e.property
  have h := hL' extx
  change L (res extx) = 0 at h
  simpa only [hext, LinearMap.zero_apply] using h

end OaiPairedStatesHamiltonian

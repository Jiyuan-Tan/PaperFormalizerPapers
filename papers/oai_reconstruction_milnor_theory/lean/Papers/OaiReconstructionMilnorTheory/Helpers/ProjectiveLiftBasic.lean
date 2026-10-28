module

public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.LinearAlgebra.Projectivization.Subspace
public import Mathlib.LinearAlgebra.Projectivization.Collinear
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.Data.Fin.VecNotation

/-! # Semilinear lifts of projective collineations -/

@[expose] public section

namespace Papers.OaiReconstructionMilnorTheory

-- @env: S6
variable (H : Type*) [Field H] -- @realizes H(source scalar field)
variable (C : Type*) [Field C] -- @realizes C(target scalar field)
variable (E : Type*) [AddCommGroup E] [Module H E] -- @realizes E(H-vector space)
variable (E' : Type*) [AddCommGroup E'] [Module C E'] -- @realizes E'(C-vector space)

-- @node: ass:projective-lift-spaces
/-- For [scalar fields H](hyp:H) and [C](hyp:C) and [an H-vector space E](hyp:E)
and [a C-vector space E′](hyp:E'), the [projective lifting dimension condition](goal)
requires [E to be finite dimensional over H](step:1), [E′ to be finite dimensional
over C](step:2), [E to have dimension at least three](step:3), and [E′ to have
dimension at least three](step:4). -/
def ProjectiveLiftSpaces : Prop :=
  FiniteDimensional H E ∧ -- @realizes E(finite-dimensional over H)
  FiniteDimensional C E' ∧ -- @realizes E'(finite-dimensional over C)
  3 ≤ Module.finrank H E ∧ -- @realizes E(dimension at least three)
  3 ≤ Module.finrank C E' -- @realizes E'(dimension at least three)

variable {H C E E'}

-- @node: ass:projective-lift-bijection
/-- For [a map ψ between the two projective spaces](hyp:ψ), the
[projective line bijection condition](goal) requires [ψ to be bijective](step:1)
and [the points of every two-dimensional source subspace to map onto the points
of some two-dimensional target subspace](step:2). -/
def ProjectiveLiftBijection (ψ : Projectivization H E → Projectivization C E') : Prop :=
  Function.Bijective ψ ∧ -- @realizes \psi(projective bijection)
  ∀ W : Submodule H E, Module.finrank H W = 2 →
    ∃ W' : Submodule C E', Module.finrank C W' = 2 ∧
      ψ '' {x | x.submodule ≤ W} = {y | y.submodule ≤ W'} -- @realizes \psi(maps lines onto lines)

-- @node: projective_scalar_compare
/-- If [an additive map sends each vector to a scalar multiple of itself](hyp:hf),
[x and y are linearly independent over C](hyp:hxy), and [the map multiplies x by a](hyp:ha)
and [y by b](hyp:hb), then [a equals b](goal). -/
lemma projective_scalar_compare (f : E' →+ E')
    (hf : ∀ v, ∃ a : C, f v = a • v) {x y : E'}
    (hxy : LinearIndependent C ![x, y]) {a b : C}
    (ha : f x = a • x) (hb : f y = b • y) : a = b := by
  obtain ⟨c, hc⟩ := hf (x + y)
  have heq : (a - c) • x + (b - c) • y = 0 := by
    rw [sub_smul, sub_smul]
    calc
      a • x - c • x + (b • y - c • y) =
          (a • x + b • y) - (c • x + c • y) := by abel
      _ = 0 := by rw [← ha, ← hb, ← map_add, ← smul_add, hc, sub_self]
  obtain ⟨hac, hbc⟩ := LinearIndependent.pair_iff.mp hxy (a - c) (b - c) heq
  exact (sub_eq_zero.mp hac).trans (sub_eq_zero.mp hbc).symm

-- @node: projective_additive_scalar
/-- If [the finite-dimensional target space has dimension at least two over C](hyp:hd)
and [an additive map sends every vector to a scalar multiple of itself](hyp:hf),
then [one scalar multiplies every vector to give its image under the map](goal). -/
lemma projective_additive_scalar [FiniteDimensional C E']
    (hd : 2 ≤ Module.finrank C E') (f : E' →+ E')
    (hf : ∀ v, ∃ a : C, f v = a • v) :
    ∃ c : C, ∀ v, f v = c • v := by
  classical
  obtain ⟨u, hu⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (show 0 < Module.finrank C E' by omega)
  obtain ⟨c, hc⟩ := hf u
  have hspan : Submodule.span C {u} ≠ ⊤ := by
    intro h
    have heq := finrank_span_singleton (K := C) hu
    rw [h, finrank_top] at heq
    omega
  obtain ⟨w, hw⟩ : ∃ w : E', w ∉ Submodule.span C {u} := by
    by_contra! h
    exact hspan (top_unique (fun x _ => h x))
  have huw : LinearIndependent C ![u, w] :=
    (LinearIndependent.pair_iff' hu).mpr (by
      intro a ha
      exact hw (ha ▸ Submodule.smul_mem _ a (Submodule.mem_span_singleton_self u)))
  obtain ⟨d, hdw⟩ := hf w
  have hcd : c = d := projective_scalar_compare f hf huw hc hdw
  refine ⟨c, fun v => ?_⟩
  by_cases hv : v = 0
  · simp [hv]
  obtain ⟨a, ha⟩ := hf v
  by_cases huv : LinearIndependent C ![u, v]
  · rw [ha, ← projective_scalar_compare f hf huv hc ha]
  · have huv' : ∃ t : C, t • u = v := by
      simpa only [LinearIndependent.pair_iff' hu, not_forall, not_not] using huv
    obtain ⟨t, ht⟩ := huv'
    have hvw : LinearIndependent C ![v, w] :=
      (LinearIndependent.pair_iff' hv).mpr (by
        intro b hb
        exact hw (by
          rw [← hb, ← ht]
          exact Submodule.smul_mem _ b
            (Submodule.smul_mem _ t (Submodule.mem_span_singleton_self u))))
    have had : a = d := projective_scalar_compare f hf hvw ha hdw
    rw [ha, had, ← hcd]

-- @node: projective_lift_unique
/-- Suppose [the target space has dimension at least two over C](hyp:hd),
[S respects scalar multiplication through the field isomorphism σ](hyp:hS),
[S′ respects scalar multiplication through σ′](hyp:hS'), [S sends every
nonzero vector into its image line under ψ](hyp:hproj), and [S′ sends every
nonzero vector into its image line under ψ](hyp:hproj').
Then [σ′ equals σ and S′ is S multiplied by one nonzero scalar in C](goal). -/
lemma projective_lift_unique [FiniteDimensional C E']
    (hd : 2 ≤ Module.finrank C E')
    (ψ : Projectivization H E → Projectivization C E')
    (σ σ' : H ≃+* C) (S S' : E ≃+ E')
    (hS : ∀ (a : H) v, S (a • v) = σ a • S v)
    (hS' : ∀ (a : H) v, S' (a • v) = σ' a • S' v)
    (hproj : ∀ v (hv : v ≠ 0), S v ∈ (ψ (Projectivization.mk H v hv)).submodule)
    (hproj' : ∀ v (hv : v ≠ 0), S' v ∈ (ψ (Projectivization.mk H v hv)).submodule) :
    σ' = σ ∧ ∃ c : Cˣ, ∀ v, S' v = (c : C) • S v := by
  let T : E' ≃+ E' := S.symm.trans S'
  have hlines (w : E') : ∃ a : C, T w = a • w := by
    by_cases hw : w = 0
    · exact ⟨0, by simp [hw]⟩
    let v := S.symm w
    have hv : v ≠ 0 := by
      intro h
      exact hw (by simpa [v] using congrArg S h)
    have hSv : S v ≠ 0 := fun h => hv (S.injective (h.trans S.map_zero.symm))
    have hline := eq_span_singleton_of_mem_of_finrank_eq_one
      (Projectivization.finrank_submodule (ψ (Projectivization.mk H v hv)))
      (hproj v hv) hSv
    have hmem := hproj' v hv
    rw [hline, Submodule.mem_span_singleton] at hmem
    obtain ⟨a, ha⟩ := hmem
    exact ⟨a, by simpa [T, v] using ha.symm⟩
  obtain ⟨c, hc⟩ := projective_additive_scalar hd T.toAddMonoidHom hlines
  obtain ⟨w, hw⟩ := Module.finrank_pos_iff_exists_ne_zero.mp
    (show 0 < Module.finrank C E' by omega)
  have hc0 : c ≠ 0 := by
    intro h
    have hTw : T w = 0 := by simpa [h] using hc w
    exact hw (T.injective (hTw.trans T.map_zero.symm))
  have hscalar (v : E) : S' v = c • S v := by simpa [T] using hc (S v)
  have hSv : S (S.symm w) ≠ 0 := by simpa using hw
  have hσ : σ' = σ := by
    ext a
    have heq : (σ' a * c) • S (S.symm w) = (c * σ a) • S (S.symm w) := by
      calc
        (σ' a * c) • S (S.symm w) = σ' a • S' (S.symm w) := by
          rw [hscalar, smul_smul]
        _ = S' (a • S.symm w) := (hS' a _).symm
        _ = c • S (a • S.symm w) := hscalar _
        _ = (c * σ a) • S (S.symm w) := by rw [hS, smul_smul]
    have heq' : σ' a * c = σ a * c := by
      apply (smul_left_injective C hSv)
      simpa only [mul_comm c] using heq
    exact mul_right_cancel₀ hc0 heq'
  exact ⟨hσ, Units.mk0 c hc0, hscalar⟩

end Papers.OaiReconstructionMilnorTheory

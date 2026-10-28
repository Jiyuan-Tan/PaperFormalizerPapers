module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.l2Space

/-! # Concrete operators on Hilbert direct sums

Reindexing, uniformly bounded diagonal action, and swapping two countable coordinates.
Reindexing and diagonal action preserve square summability and have the expected norm bounds.
-/

@[expose] public section

namespace Papers.OaiNearInclusionsVon.ReusedTree

variable {I : Type*} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
/-- For [an index set I](hyp:I), [a complex inner product space V](hyp:V), and
[a permutation e of I](hyp:e), [the reindexing operator](goal) sends each
square-summable V-valued family to the family whose coordinate at x is the original
coordinate at e applied to x. -/
noncomputable def reindexOp (e : I ≃ I) :
    lp (fun _ : I => V) 2 →L[ℂ] lp (fun _ : I => V) 2 :=
  LinearMap.mkContinuous
    { toFun := fun v => ⟨fun x => v (e x), by
        apply memℓp_gen
        exact e.summable_iff.mpr ((lp.memℓp v).summable (by norm_num))⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl } 1 (by
        intro v
        simp only [one_mul]
        apply le_of_eq
        rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ENNReal).toReal),
          lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ENNReal).toReal)]
        congr 1
        exact e.tsum_eq (fun x => ‖v x‖ ^ (2 : ENNReal).toReal))
/-- For [a permutation e of the index set](hyp:e) and [a square-summable family
v](hyp:v), [reindexing v along e preserves its norm](goal). -/
lemma reindexOp_norm (e : I ≃ I) (v : lp (fun _ : I => V) 2) :
    ‖reindexOp e v‖ = ‖v‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ENNReal).toReal),
    lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ENNReal).toReal)]
  congr 1
  exact e.tsum_eq (fun x => ‖v x‖ ^ (2 : ENNReal).toReal)
/-- For [a permutation e of the index set](hyp:e), [the operator reindexing
square-summable families along e is unitary](goal). -/
lemma reindexOp_mem_unitary [CompleteSpace V] (e : I ≃ I) :
    reindexOp (V := V) e ∈ unitary (lp (fun _ : I => V) 2 →L[ℂ]
      lp (fun _ : I => V) 2) := by
  let u : (lp (fun _ : I => V) 2 →L[ℂ] lp (fun _ : I => V) 2)ˣ :=
    { val := reindexOp e
      inv := reindexOp e.symm
      val_inv := by ext v x; change v (e.symm (e x)) = v x; rw [e.symm_apply_apply]
      inv_val := by ext v x; change v (e (e.symm x)) = v x; rw [e.apply_symm_apply] }
  apply IsUnit.mem_unitary_of_star_mul_self ⟨u, rfl⟩
  rw [ContinuousLinearMap.star_eq_adjoint]
  exact (reindexOp (V := V) e).norm_map_iff_adjoint_comp_self.mp
    (reindexOp_norm (V := V) e)
/-- For [an index set I](hyp:I), [a complex inner product space V](hyp:V),
[a family T of bounded operators on V indexed by I](hyp:T), and [a real bound
C](hyp:C) such that [every operator in T has norm at most C](hyp:hT), [the diagonal
operator](goal) applies the corresponding member of T to each coordinate of a
square-summable V-valued family. -/
noncomputable def diagOp (T : I → V →L[ℂ] V) (C : ℝ)
    (hT : ∀ x, ‖T x‖ ≤ C) :
    lp (fun _ : I => V) 2 →L[ℂ] lp (fun _ : I => V) 2 :=
  LinearMap.mkContinuous
    { toFun := fun v => ⟨fun x => T x (v x), by
        apply ((lp.memℓp v).norm.const_mul |C|).mono
        intro x
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right ((hT x).trans (le_abs_self C)) (norm_nonneg _))⟩
      map_add' := by intros; ext x; exact map_add (T x) _ _
      map_smul' := by intros; ext x; exact (T x).map_smul _ _ } C (by
        intro v
        classical
        cases isEmpty_or_nonempty I with
        | inl h =>
          have hv : v = 0 := Subsingleton.elim _ _
          subst v
          simp only [LinearMap.coe_mk, map_zero, norm_zero, mul_zero]
          exact le_rfl
        | inr h =>
          have hC : 0 ≤ C := (norm_nonneg (T (Classical.arbitrary I))).trans (hT _)
          calc
            _ ≤ ‖(C : ℂ) • v‖ := lp.norm_mono (by norm_num) (fun x => by
              change ‖T x (v x)‖ ≤ ‖(C : ℂ) • v x‖
              simpa [lp.coeFn_smul, Pi.smul_apply, norm_smul, Complex.norm_real,
                abs_of_nonneg hC] using
                (ContinuousLinearMap.le_opNorm (T x) (v x)).trans
                  (mul_le_mul_of_nonneg_right (hT x) (norm_nonneg _)))
            _ = C * ‖v‖ := by rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg hC])
/-- Let [T be a bounded operator on square-summable families](hyp:T) and [x be a
family of bounded coordinate operators](hyp:x). If [T applies x at each
coordinate](hyp:hT), then for [a square-summable family v](hyp:v) and [an index
n](hyp:n), [the n-th coordinate of the adjoint of T applied to v is the adjoint
of the n-th coordinate operator applied to the n-th coordinate of v](goal). -/
lemma diagonal_star_apply [CompleteSpace V]
    (T : lp (fun _ : I => V) 2 →L[ℂ] lp (fun _ : I => V) 2)
    (x : I → V →L[ℂ] V) (hT : ∀ v n, (T v) n = x n (v n))
    (v : lp (fun _ : I => V) 2) (n : I) :
    (star T v) n = star (x n) (v n) := by
  classical
  have hs (w : V) : T (lp.single 2 n w) = lp.single 2 n (x n w) := by
    ext i
    rw [hT]
    by_cases hi : i = n
    · subst i; simp
    · simp [lp.single_apply, hi]
  apply ext_inner_left ℂ
  intro w
  rw [← lp.inner_single_left n w (star T v), ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right, hs, lp.inner_single_left,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
/-- For [a unitary operator U on a complete complex inner product space](hyp:U),
[the operator norm of U is at most one](goal). -/
lemma unitary_norm_le_one [CompleteSpace V] (U : unitary (V →L[ℂ] V)) :
    ‖(U : V →L[ℂ] V)‖ ≤ 1 := by
  cases subsingleton_or_nontrivial (V →L[ℂ] V) with
  | inl h => simp [Subsingleton.elim (U : V →L[ℂ] V) 0]
  | inr h => exact le_of_eq (CStarRing.norm_coe_unitary U)

/-- For [an index set I](hyp:I), [a complex Hilbert space V](hyp:V), and [a family
U of unitary operators on V indexed by I](hyp:U), [the unitary diagonal
operator](goal) applies the corresponding member of U to each coordinate of a
square-summable V-valued family. -/
noncomputable def diagUnitaryOp [CompleteSpace V] (U : I → unitary (V →L[ℂ] V)) :
    lp (fun _ : I => V) 2 →L[ℂ] lp (fun _ : I => V) 2 :=
  diagOp (fun x => (U x : V →L[ℂ] V)) 1 (fun x => unitary_norm_le_one (U x))
/-- For [a family U of unitary coordinate operators](hyp:U), [a square-summable
family v](hyp:v), and [an index x](hyp:x), [the x-th coordinate of the adjoint
diagonal action on v equals the adjoint of the unitary at x applied to the x-th
coordinate of v](goal). -/
lemma diagUnitaryOp_star_apply [CompleteSpace V] (U : I → unitary ((V →L[ℂ] V)))
    (v : lp (fun _ : I => V) 2) (x : I) :
    (star (diagUnitaryOp U) v) x = star (U x : (V →L[ℂ] V)) (v x) := by
  exact diagonal_star_apply _ (fun x => (U x : (V →L[ℂ] V))) (by intros; rfl) v x
/-- For [a family U of unitary coordinate operators](hyp:U), [the diagonal
operator applying U coordinate by coordinate to square-summable families is
unitary](goal). -/
lemma diagUnitaryOp_mem_unitary [CompleteSpace V] (U : I → unitary ((V →L[ℂ] V))) :
    diagUnitaryOp U ∈ unitary ((lp (fun _ : I => V) 2 →L[ℂ] lp (fun _ : I => V) 2)) := by
  rw [Unitary.mem_iff]
  constructor
  · ext v x
    change (star (diagUnitaryOp U) (diagUnitaryOp U v)) x = v x
    rw [diagUnitaryOp_star_apply]
    change (star (U x : (V →L[ℂ] V)) * (U x : (V →L[ℂ] V))) (v x) = v x
    rw [Unitary.coe_star_mul_self]
    rfl
  · ext v x
    change (U x : (V →L[ℂ] V)) ((star (diagUnitaryOp U) v) x) = v x
    rw [diagUnitaryOp_star_apply]
    change ((U x : (V →L[ℂ] V)) * star (U x : (V →L[ℂ] V))) (v x) = v x
    rw [Unitary.mul_star_self_of_mem (U x).property]
    rfl
/-- For [an index set I](hyp:I), [a complex inner product space V](hyp:V), and
[a bounded operator T on V](hyp:T), [the constant diagonal operator](goal) applies
T to every coordinate of a square-summable V-valued family indexed by I. -/
noncomputable def constantDiagOp (T : V →L[ℂ] V) :
    lp (fun _ : I => V) 2 →L[ℂ] lp (fun _ : I => V) 2 :=
  diagOp (fun _ => T) ‖T‖ (fun _ => le_rfl)
/-- For [a square-summable family v of square-summable complex families](hyp:v),
[the squared absolute values of its entries are summable over all pairs of
indices](goal). -/
lemma hilbertSum_summable_coordinates (v : lp (fun _ : I => lp (fun _ : I => ℂ) 2) 2) :
    Summable (fun p : I × I => ‖v p.1 p.2‖ ^ (2 : ENNReal).toReal) := by
  apply (summable_prod_of_nonneg (fun p => by positivity)).2
  refine ⟨fun i => (lp.memℓp (v i)).summable (by norm_num), ?_⟩
  have h := (lp.memℓp v).summable (by norm_num : 0 < (2 : ENNReal).toReal)
  simpa only [← lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal)] using h
/-- For [a square-summable family v of square-summable complex families](hyp:v)
and [a column index i](hyp:i), [the entries in column i form a square-summable
complex family](goal). -/
lemma hilbertSum_column_mem (v : lp (fun _ : I => lp (fun _ : I => ℂ) 2) 2) (i : I) :
    Memℓp (fun j => v j i) 2 := by
  apply memℓp_gen
  exact (hilbertSum_summable_coordinates v).prod_symm.prod_factor i
/-- For [a square-summable family v of square-summable complex families](hyp:v),
[exchanging its two indices gives another square-summable family of
square-summable complex families](goal). -/
lemma hilbertSum_swap_mem (v : lp (fun _ : I => lp (fun _ : I => ℂ) 2) 2) :
    Memℓp (fun i => (⟨fun j => v j i, hilbertSum_column_mem v i⟩ :
      lp (fun _ : I => ℂ) 2)) 2 := by
  apply memℓp_gen
  simp_rw [lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal)]
  exact (summable_prod_of_nonneg (fun p => by positivity)).1
    (hilbertSum_summable_coordinates v).prod_symm |>.2
/-- For [an index set I](hyp:I), [the coordinate-swap operator](goal) exchanges
the two indices of a square-summable family of square-summable complex families
indexed by I. -/
noncomputable def swapOp (I : Type*) :
    lp (fun _ : I => lp (fun _ : I => ℂ) 2) 2 →L[ℂ]
      lp (fun _ : I => lp (fun _ : I => ℂ) 2) 2 :=
  LinearMap.mkContinuous
    { toFun := fun v => ⟨fun x => ⟨fun y => v y x, hilbertSum_column_mem v x⟩,
        hilbertSum_swap_mem v⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl } 1 (by
        intro v
        rw [one_mul]
        apply le_of_eq
        rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ENNReal).toReal),
          lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ENNReal).toReal)]
        congr 1
        simp_rw [lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal)]
        exact (hilbertSum_summable_coordinates v).tsum_comm)

end Papers.OaiNearInclusionsVon.ReusedTree

module
public import Papers.TbsNeuralCausalPi.Helpers.EmpiricalCovers
/-! # Product covers with centers in the vector class

Coordinate covers may have incompatible centers. Choose a vector from each
nonempty product ball; the resulting internal cover costs a factor of two
in radius and no factor in cardinality.
-/
public section
namespace Papers.TbsNeuralCausalPi
open scoped ENNReal NNReal
noncomputable section

/-- If [the number d of coordinates is positive](hyp:hd) and
[r is positive](hyp:hr), [the strict internal covering number of a set of
m-by-d arrays in sum absolute distance at radius r is at most the product
of the strict internal covering numbers of its coordinate projections
at radius r/(2d)](goal). -/
-- @node: strictCoveringNumber_vector_le_product
lemma strictCoveringNumber_vector_le_product {m d : ℕ} (hd : 0 < d)
    {r : ℝ} (hr : 0 < r) (S : Set (WithLp 1 (Fin m × Fin d → ℝ))) :
    strictCoveringNumber (ENNReal.ofReal r) S ≤
      ∏ j : Fin d, strictCoveringNumber (ENNReal.ofReal (r / (2*d)))
        ((fun v : WithLp 1 (Fin m × Fin d → ℝ) =>
          WithLp.toLp 1 (fun ij : Fin m × Fin 1 => v.ofLp (ij.1, j))) '' S) := by
  classical
  let : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let proj (j : Fin d) (v : WithLp 1 (Fin m × Fin d → ℝ)) :
      WithLp 1 (Fin m × Fin 1 → ℝ) :=
    WithLp.toLp 1 (fun ij => v.ofLp (ij.1, j))
  let s := r / (2*d)
  have hs : 0 < s := div_pos hr (by positivity)
  have hmin (j : Fin d) : ∃ C : Set (WithLp 1 (Fin m × Fin 1 → ℝ)),
      C ⊆ proj j '' S ∧
      SetRel.IsCover {p | edist p.1 p.2 < ENNReal.ofReal s} (proj j '' S) C ∧
      C.encard = strictCoveringNumber (ENNReal.ofReal s) (proj j '' S) := by
    let T := {C : Set (WithLp 1 (Fin m × Fin 1 → ℝ)) // C ⊆ proj j '' S ∧
      SetRel.IsCover {p | edist p.1 p.2 < ENNReal.ofReal s} (proj j '' S) C}
    have : Nonempty T := ⟨⟨proj j '' S, Set.Subset.rfl, by
      intro v hv
      exact ⟨v, hv, by simpa using (ENNReal.ofReal_pos.mpr hs)⟩⟩⟩
    obtain ⟨C, hC⟩ := ENat.exists_eq_iInf (fun C : T => C.val.encard)
    exact ⟨C.val, C.property.1, C.property.2, hC⟩
  choose C hsub hcover hcard using hmin
  let good (c : Fin d → WithLp 1 (Fin m × Fin 1 → ℝ)) :=
    ∃ v ∈ S, ∀ j, dist (proj j v) (c j) < s
  let rep (c : Fin d → WithLp 1 (Fin m × Fin 1 → ℝ)) :
      WithLp 1 (Fin m × Fin d → ℝ) :=
    if h : good c then h.choose else 0
  have hrep (c) (hc : good c) : rep c ∈ S ∧
      ∀ j, dist (proj j (rep c)) (c j) < s := by
    dsimp only [rep]
    rw [dif_pos hc]
    exact hc.choose_spec
  let T := {c ∈ Set.pi Set.univ C | good c}
  have hinternal : rep '' T ⊆ S := by
    rintro _ ⟨c, hc, rfl⟩
    exact (hrep c hc.2).1
  have hvector : SetRel.IsCover {p | edist p.1 p.2 < ENNReal.ofReal r}
      S (rep '' T) := by
    intro v hv
    have hchoose (j : Fin d) : ∃ w ∈ C j, dist (proj j v) w < s := by
      obtain ⟨w, hw, hdw⟩ := hcover j (Set.mem_image_of_mem (proj j) hv)
      change edist (proj j v) w < ENNReal.ofReal s at hdw
      rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff hs] at hdw
      exact ⟨w, hw, hdw⟩
    choose c hc hdist using hchoose
    have hgood : good c := ⟨v, hv, hdist⟩
    have hcT : c ∈ T := ⟨by simpa only [Set.mem_pi, Set.mem_univ, forall_true_left] using hc,
      hgood⟩
    refine ⟨rep c, Set.mem_image_of_mem rep hcT, ?_⟩
    change edist v (rep c) < ENNReal.ofReal r
    rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff hr]
    have hcoord (j : Fin d) : dist (proj j v) (proj j (rep c)) < 2*s := by
      calc
        _ ≤ dist (proj j v) (c j) + dist (c j) (proj j (rep c)) := dist_triangle _ _ _
        _ < s+s := add_lt_add (hdist j) (by
          simpa only [dist_comm] using (hrep c hgood).2 j)
        _ = 2*s := by ring
    have hid : dist v (rep c) = ∑ j, dist (proj j v) (proj j (rep c)) := by
      simp only [PiLp.dist_eq_of_L1, proj, Fintype.sum_prod_type,
        Fin.sum_univ_one]
      exact Finset.sum_comm
    rw [hid]
    calc
      _ < ∑ _j : Fin d, 2*s := Finset.sum_lt_sum_of_nonempty
        (Finset.univ_nonempty) (fun j _ => hcoord j)
      _ = r := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        dsimp [s]
        field_simp
  calc
    _ ≤ (rep '' T).encard := iInf_le_of_le ⟨rep '' T, hinternal, hvector⟩ le_rfl
    _ ≤ T.encard := Set.encard_image_le _ _
    _ ≤ (Set.pi Set.univ C).encard := Set.encard_le_encard (fun _ hc => hc.1)
    _ = ∏ j, strictCoveringNumber (ENNReal.ofReal s) (proj j '' S) := by
      rw [Set.encard_pi_eq_prod_encard]
      simp_rw [hcard]

/-- If [the output dimension d is positive](hyp:hd) and [r is positive](hyp:hr),
[the worst-case unnormalized empirical covering number of a vector function
class on m observations at radius r is at most the product of the corresponding
scalar coordinate covering numbers at radius r/(2d)](goal). -/
-- @node: empiricalL1CoveringNumber_le_coordinate_product
lemma empiricalL1CoveringNumber_le_coordinate_product {X : Type*} {d : ℕ}
    (hd : 0 < d) {r : ℝ} (hr : 0 < r) (F : Set (X → L1Vec d)) (m : ℕ) :
    empiricalL1CoveringNumber (ENNReal.ofReal r) F m ≤
      ∏ j : Fin d, empiricalL1CoveringNumber (ENNReal.ofReal (r/(2*d)))
        ((fun g : X → ℝ => fun x => WithLp.toLp 1 (fun _ : Fin 1 => g x)) ''
          ((fun f : X → L1Vec d => fun x => (f x).ofLp j) '' F)) m := by
  classical
  unfold empiricalL1CoveringNumber
  apply iSup_le
  intro x
  refine (strictCoveringNumber_vector_le_product hd hr _).trans ?_
  apply Finset.prod_le_prod'
  intro j _
  refine le_trans ?_ (le_iSup _ x)
  apply le_of_eq
  congr 1
  ext w
  constructor
  · rintro ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    exact ⟨_, ⟨_, ⟨f, hf, rfl⟩, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨_, ⟨f, hf, rfl⟩, rfl⟩, rfl⟩
    exact ⟨_, ⟨f, hf, rfl⟩, rfl⟩

end
end Papers.TbsNeuralCausalPi

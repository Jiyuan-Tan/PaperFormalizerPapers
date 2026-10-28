module

public import Papers.OaiNearInclusionsVon.Helpers.MainSequence

/-! The representation associated with an implementing unitary and its uniform error. -/

@[expose] public section

namespace Papers.OaiNearInclusionsVon

set_option maxHeartbeats 800000

open Filter
open scoped Topology

-- @node: mainNearUnitaryPair
/-- [The clock and shift operators are unitary operators on a nonzero,
finite-dimensional complex Hilbert space](goal). -/
lemma mainNearUnitaryPair (n : ClockNat) : NearUnitaryPair (clockU n) (shiftV n) := by
  letI : NeZero n.val := ⟨by have := n.property; unfold ClockIndex at this; omega⟩
  exact ⟨inferInstance, inferInstance, clockU_mem_unitary n, shiftV_mem_unitary n⟩

-- @node: mainZ
/-- Given [circle representations π](hyp:π), [Laurent coefficients A](hyp:A),
[their circle-family conditions](hyp:hπ), [a clock index n](hyp:n), and
[a product-group element g](hyp:g), [the source representation operator at g](goal)
is amplified left translation by g conjugated by the diagonal clock–shift unitary. -/
noncomputable def mainZ (π : CircleRep) (A : LaurentData) (hπ : IsCircleFamily π A)
    (n : ClockNat) (g : ProdGrp) : mainH n →L[ℂ] mainH n :=
  mainW π A hπ n * lamAmp g * star (mainW π A hπ n)

-- @node: mainW_mem_unitary
/-- If [the representations and coefficients satisfy the circle-family conditions](hyp:hπ),
[the diagonal clock–shift operator is unitary](goal). -/
lemma mainW_mem_unitary (π : CircleRep) (A : LaurentData) (hπ : IsCircleFamily π A)
    (n : ClockNat) : mainW π A hπ n ∈ unitary _ :=
  diagUnitary_mem_unitary π A hπ _ _ (mainNearUnitaryPair n) _

-- @node: mainZ_mem_unitary
/-- If [the representations and coefficients satisfy the circle-family conditions](hyp:hπ),
[each source representation operator is unitary](goal). -/
lemma mainZ_mem_unitary (π : CircleRep) (A : LaurentData) (hπ : IsCircleFamily π A)
    (n : ClockNat) (g : ProdGrp) : mainZ π A hπ n g ∈ unitary _ :=
  (unitary _).mul_mem ((unitary _).mul_mem (mainW_mem_unitary π A hπ n)
    (lpReindex_mem_unitary _)) (Unitary.star_mem (mainW_mem_unitary π A hπ n))

-- @node: mainZ_mem_source
/-- If [the representations and coefficients satisfy the circle-family conditions](hyp:hπ),
[each source representation operator belongs to the source von Neumann algebra](goal). -/
lemma mainZ_mem_source (π : CircleRep) (A : LaurentData) (hπ : IsCircleFamily π A)
    (n : ClockNat) (g : ProdGrp) : mainZ π A hπ n g ∈ mainSource π A hπ n := by
  change mainZ π A hπ n g ∈
    (sourceAlg A (clockU n) (shiftV n) (mainBlockBound π A hπ n) : Set _)
  rw [sourceAlg_carrier π A hπ _ _ (mainNearUnitaryPair n)]
  exact ⟨lamReg g, lamReg_mem_bicommutant g, by
    simp only [mainZ, mainW, lamAmp_eq_amplify]⟩

-- @node: mainZ_one
/-- If [the representations and coefficients satisfy the circle-family conditions](hyp:hπ),
[the source representation sends the group identity to the identity operator](goal). -/
lemma mainZ_one (π : CircleRep) (A : LaurentData) (hπ : IsCircleFamily π A)
    (n : ClockNat) : mainZ π A hπ n 1 = 1 := by
  have h1 : lamAmp (D := ClockSpace n) 1 = 1 := by
    apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext y
    simp only [lamAmp, lpReindex_apply, Equiv.coe_mulLeft, inv_one, one_mul,
      one_apply_eq_self]
  rw [mainZ, h1, mul_one, Unitary.mul_star_self_of_mem (mainW_mem_unitary π A hπ n)]

-- @node: mainZ_mul
/-- If [the representations and coefficients satisfy the circle-family conditions](hyp:hπ),
[the source operator at a product of two group elements equals the product of
their source operators in the same order](goal). -/
lemma mainZ_mul (π : CircleRep) (A : LaurentData) (hπ : IsCircleFamily π A)
    (n : ClockNat) (g h : ProdGrp) :
    mainZ π A hπ n (g * h) = mainZ π A hπ n g * mainZ π A hπ n h := by
  have hmul : lamAmp (D := ClockSpace n) (g * h) = lamAmp g * lamAmp h := by
    ext x y
    simp [lamAmp, lpReindex_apply, mul_apply_eq_comp, mul_assoc]
  simp only [mainZ, hmul, mul_assoc,
    ← mul_assoc (star (mainW π A hπ n)) (mainW π A hπ n),
    Unitary.star_mul_self_of_mem (mainW_mem_unitary π A hπ n), one_mul]

-- @node: mainSigmaOp
/-- Given [circle representations π](hyp:π), [Laurent coefficients A](hyp:A),
[their circle-family conditions](hyp:hπ), [a clock index n](hyp:n),
[an operator u on the main Hilbert space](hyp:u), and [a product-group element g](hyp:g),
[the combined operator at g](goal) is the source operator at g conjugated by u
and its adjoint, followed by amplified right translation by g. -/
noncomputable def mainSigmaOp (π : CircleRep) (A : LaurentData)
    (hπ : IsCircleFamily π A) (n : ClockNat) (u : mainH n →L[ℂ] mainH n)
    (g : ProdGrp) : mainH n →L[ℂ] mainH n :=
  (u * mainZ π A hπ n g * star u) * rhoAmp g

-- @node: mainSigmaOp_mem_unitary
/-- If [the representations and coefficients satisfy the circle-family conditions](hyp:hπ)
and [the conjugating operator u is unitary](hyp:hu),
[the combined operator at every group element is unitary](goal). -/
lemma mainSigmaOp_mem_unitary (π : CircleRep) (A : LaurentData)
    (hπ : IsCircleFamily π A) (n : ClockNat) (u : mainH n →L[ℂ] mainH n)
    (hu : u ∈ unitary _) (g : ProdGrp) : mainSigmaOp π A hπ n u g ∈ unitary _ :=
  (unitary _).mul_mem ((unitary _).mul_mem
    ((unitary _).mul_mem hu (mainZ_mem_unitary π A hπ n g)) (Unitary.star_mem hu))
    (lpReindex_mem_unitary _)

-- @node: mainSigmaOp_mul
/-- If [the representations and coefficients satisfy the circle-family conditions](hyp:hπ),
[u is unitary](hyp:hu), and [conjugation by u sends every source-algebra operator
into the target algebra](hyp:hi), [the combined operator at a product of group
elements equals the product of their combined operators in the same order](goal). -/
lemma mainSigmaOp_mul (π : CircleRep) (A : LaurentData)
    (hπ : IsCircleFamily π A) (n : ClockNat) (u : mainH n →L[ℂ] mainH n)
    (hu : u ∈ unitary _)
    (hi : ∀ x ∈ mainSource π A hπ n, u * x * star u ∈ mainTarget n)
    (g h : ProdGrp) :
    mainSigmaOp π A hπ n u (g * h) =
      mainSigmaOp π A hπ n u g * mainSigmaOp π A hπ n u h := by
  have hc : rhoAmp g * (u * mainZ π A hπ n h * star u) =
      (u * mainZ π A hπ n h * star u) * rhoAmp g := by
    have ht := hi _ (mainZ_mem_source π A hπ n h)
    change _ ∈ (targetAlg (D := ClockSpace n) : Set (mainH n →L[ℂ] mainH n)) at ht
    rw [targetAlg_carrier] at ht
    exact ht _ ⟨g, rfl⟩
  have hr : rhoAmp (D := ClockSpace n) (g * h) = rhoAmp g * rhoAmp h := by
    ext x y
    simp [rhoAmp, lpReindex_apply, mul_apply_eq_comp, mul_assoc]
  simp only [mainSigmaOp, mainZ_mul, hr]
  calc
    _ = (u * mainZ π A hπ n g * star u) *
        (u * mainZ π A hπ n h * star u) * (rhoAmp g * rhoAmp h) := by
      simp only [mul_assoc, ← mul_assoc (star u) u,
        Unitary.star_mul_self_of_mem hu, one_mul]
    _ = _ := (show Commute (u * mainZ π A hπ n h * star u) (rhoAmp g)
      from hc.symm).mul_mul_mul_comm _ _

-- @node: mainSigma
/-- Given [circle representations π](hyp:π), [Laurent coefficients A](hyp:A),
[their circle-family conditions](hyp:hπ), [a clock index n](hyp:n),
[an operator u on the main Hilbert space](hyp:u), [unitarity of u](hyp:hu), and
[the inclusion of the source algebra in the target algebra after conjugation by u](hyp:hi),
[the resulting unitary group representation](goal) assigns to each group element
its source operator conjugated by u, multiplied by its amplified right translation. -/
noncomputable def mainSigma (π : CircleRep) (A : LaurentData)
    (hπ : IsCircleFamily π A) (n : ClockNat) (u : mainH n →L[ℂ] mainH n)
    (hu : u ∈ unitary _)
    (hi : ∀ x ∈ mainSource π A hπ n, u * x * star u ∈ mainTarget n) :
    ProdGrp →* unitary (mainH n →L[ℂ] mainH n) where
  toFun g := ⟨mainSigmaOp π A hπ n u g, mainSigmaOp_mem_unitary π A hπ n u hu g⟩
  map_one' := by
    apply Subtype.ext
    have hr : rhoAmp (D := ClockSpace n) 1 = 1 := by
      apply ContinuousLinearMap.ext
      intro x
      apply lp.ext
      funext y
      simp only [rhoAmp, lpReindex_apply, Equiv.coe_mulRight, mul_one,
        one_apply_eq_self]
    simp only [mainSigmaOp, mainZ_one, hr, mul_one, OneMemClass.coe_one,
      Unitary.mul_star_self_of_mem hu]
  map_mul' g h := Subtype.ext (mainSigmaOp_mul π A hπ n u hu hi g h)

-- @node: unitary_conjugation_error_le
/-- If [u is unitary](hyp:hu) and [x is unitary](hyp:hx),
[conjugating x by u changes it in operator norm by at most twice the distance
from u to the identity](goal). -/
lemma unitary_conjugation_error_le {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (u x : H →L[ℂ] H) (hu : u ∈ unitary _) (hx : x ∈ unitary _) :
    ‖u * x * star u - x‖ ≤ 2 * ‖u - 1‖ := by
  have he : u * x * star u - x = (u - 1) * x * star u + x * (star u - 1) := by
    noncomm_ring
  have hs : ‖star u - 1‖ = ‖u - 1‖ := by
    simpa only [star_sub, star_one] using norm_star (u - 1)
  rw [he]
  calc
    _ ≤ ‖(u - 1) * x * star u‖ + ‖x * (star u - 1)‖ := norm_add_le _ _
    _ = 2 * ‖u - 1‖ := by
      rw [CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem hu),
        CStarRing.norm_mul_mem_unitary _ hx, CStarRing.norm_mem_unitary_mul _ hx, hs]
      ring

/-- Suppose [u is unitary](hyp:hu), [Z is unitary](hyp:hZ), [ρ is unitary](hyp:hρ),
[ρ commutes with F](hyp:hc), and [Z differs from the product of l and F in
operator norm by at most β](hyp:hb). Then [the product of the u-conjugate of Z
and ρ differs from the product of l, ρ, and F by at most β plus twice the
distance from u to the identity](goal). -/
-- @node: unitary_product_comparison_error_le
lemma unitary_product_comparison_error_le {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (u Z l ρ F : H →L[ℂ] H) (β : ℝ)
    (hu : u ∈ unitary _) (hZ : Z ∈ unitary _) (hρ : ρ ∈ unitary _)
    (hc : Commute ρ F) (hb : ‖Z - l * F‖ ≤ β) :
    ‖(u * Z * star u) * ρ - (l * ρ) * F‖ ≤ β + 2 * ‖u - 1‖ := by
  have he : (l * ρ) * F = (l * F) * ρ := by
    rw [mul_assoc, hc.eq, ← mul_assoc]
  calc
    _ = ‖(u * Z * star u) * ρ - (l * F) * ρ‖ :=
      congrArg (fun X => ‖(u * Z * star u) * ρ - X‖) he
    _ = ‖(u * Z * star u - l * F) * ρ‖ := congrArg norm (sub_mul _ _ _).symm
    _ = ‖u * Z * star u - l * F‖ := CStarRing.norm_mul_mem_unitary _ hρ
    _ ≤ ‖u * Z * star u - Z‖ + ‖Z - l * F‖ := by
      simpa only [dist_eq_norm] using dist_triangle (u * Z * star u) Z (l * F)
    _ ≤ 2 * ‖u - 1‖ + β := add_le_add (unitary_conjugation_error_le _ _ hu hZ) hb
    _ = _ := add_comm _ _

-- @node: mainFAmp
/-- For [Laurent coefficients A](hyp:A), [a clock index n](hyp:n), and
[a product-group element g](hyp:g), [the amplified clock–shift product operator](goal)
applies the specialized product operator at g to every product-group coordinate. -/
noncomputable def mainFAmp (A : LaurentData) (n : ClockNat) (g : ProdGrp) :
    mainH n →L[ℂ] mainH n :=
  lp.mapCLM 2 (fun _ : ProdGrp => mainF A n g) (norm_nonneg _) (fun _ => le_rfl)

-- @node: mainSigma_error_le
/-- If [the representations and coefficients satisfy the circle-family conditions](hyp:hπ)
and [u is unitary](hyp:hu), [the combined operator at g differs from the product
of amplified left translation, amplified right translation, and the amplified
clock–shift product at g by at most the fixed near-inclusion constant times the
commutator scale plus twice the distance from u to the identity](goal). -/
lemma mainSigma_error_le (π : CircleRep) (A : LaurentData)
    (hπ : IsCircleFamily π A) (n : ClockNat) (u : mainH n →L[ℂ] mainH n)
    (hu : u ∈ unitary _) (g : ProdGrp) :
    ‖mainSigmaOp π A hπ n u g -
      (lamAmp g * rhoAmp g) * mainFAmp A n g‖ ≤
        nearC * nuN n + 2 * ‖u - 1‖ := by
  have hc : Commute (rhoAmp (D := ClockSpace n) g) (mainFAmp A n g) := by
    apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext y
    change rhoAmp g (mainFAmp A n g x) y = mainFAmp A n g (rhoAmp g x) y
    rw [rhoAmp, lpReindex_apply]
    change mainF A n g (x (y * g)) = mainF A n g (rhoAmp g x y)
    rw [rhoAmp, lpReindex_apply]
    rfl
  have hb : ‖mainZ π A hπ n g - lamAmp g * mainFAmp A n g‖ ≤ nearC * nuN n :=
    near_group_reordering_bound π A hπ (clockU n) (shiftV n) (mainNearUnitaryPair n)
      (mainBlockBound π A hπ n) g
  exact unitary_product_comparison_error_le u (mainZ π A hπ n g)
    (lamAmp g) (rhoAmp g) (mainFAmp A n g) (nearC * nuN n)
    hu (mainZ_mem_unitary π A hπ n g) (lpReindex_mem_unitary _) hc hb

-- @node: mainSigma_error_tendsto_zero
/-- If [the selected clock indices increase strictly](hyp:hφ),
[u is a sequence of operators on the corresponding main Hilbert spaces](hyp:u),
and [their distances from the identity tend to zero](hyp:hu), [the sum of the
fixed near-inclusion constant times the selected commutator scale and twice
the distance from u to the identity tends to zero](goal). -/
lemma mainSigma_error_tendsto_zero (φ : ℕ → ClockNat) (hφ : StrictMono φ)
    (u : ∀ k, mainH (φ k) →L[ℂ] mainH (φ k))
    (hu : Tendsto (fun k => ‖u k - 1‖) atTop (𝓝 0)) :
    Tendsto (fun k => nearC * nuN (φ k) + 2 * ‖u k - 1‖) atTop (𝓝 0) := by
  let : Nonempty ClockNat := ⟨φ 0⟩
  have hφnat : StrictMono (fun k => (φ k).val) := hφ
  have ht : Tendsto φ atTop atTop := by
    apply tendsto_atTop.2
    intro b
    exact (hφnat.tendsto_atTop.eventually (eventually_ge_atTop b.val))
  simpa using ((nuN_tendsto_zero.comp ht).const_mul nearC).add (hu.const_mul 2)

end Papers.OaiNearInclusionsVon

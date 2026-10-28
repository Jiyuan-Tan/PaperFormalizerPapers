module

public import Papers.OaiNearInclusionsVon.Helpers.CornerCommutation
public import Papers.OaiNearInclusionsVon.Helpers.CornerPolar
public import Papers.OaiNearInclusionsVon.Helpers.CornerSpectral
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.Normed.Ring.Units

/-! Invertibility and quadratic convergence of transferred finite-corner operators. -/

public section

set_option linter.style.longLine false

namespace Papers.OaiNearInclusionsVon

open Filter
open scoped Topology

variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℂ (H n)] [∀ n, CompleteSpace (H n)]

/-- For [operator sequences E₁ and E₂](hyp:E₁,E₂) and [unitary candidates
R₁ and R₂](hyp:R₁,R₂), suppose [E₁ and E₂ are commuting orthogonal
projections](hyp:hE) and [R₁ and R₂ are unitary and each commutes with
both projections](hyp:hR). Then [the restriction of R₁ to the common
range preserves the norm of every vector](goal). -/
-- @node: cornerRestrict_norm_map
lemma cornerRestrict_norm_map
    (E₁ E₂ R₁ R₂ : ∀ n, H n →L[ℂ] H n)
    (hE : CornerProjections E₁ E₂) (hR : CornerUnitaries E₁ E₂ R₁ R₂)
    (n : ℕ) (x : cornerRange E₁ E₂ n) :
    ‖cornerRestrict E₁ E₂ R₁ n x‖ = ‖x‖ := by
  change ‖(cornerRestrict E₁ E₂ R₁ n x : H n)‖ = ‖(x : H n)‖
  rw [(cornerRestrict_apply E₁ E₂ R₁ R₂ hE hR n x).1]
  exact (R₁ n).norm_map_of_mem_unitary (hR n).1 x

/-- For [operator sequences E₁ and E₂](hyp:E₁,E₂) and [unitary candidates
R₁ and R₂](hyp:R₁,R₂), suppose [E₁ and E₂ are commuting orthogonal
projections](hyp:hE) and [R₁ and R₂ are unitary and each commutes with
both projections](hyp:hR). At any index with finite-dimensional common
range, [the restriction of R₁ to that range is unitary](goal). -/
-- @node: cornerRestrict_mem_unitary
lemma cornerRestrict_mem_unitary
    (E₁ E₂ R₁ R₂ : ∀ n, H n →L[ℂ] H n)
    (hE : CornerProjections E₁ E₂) (hR : CornerUnitaries E₁ E₂ R₁ R₂)
    (n : ℕ) [FiniteDimensional ℂ (cornerRange E₁ E₂ n)] :
    cornerRestrict E₁ E₂ R₁ n ∈ unitary _ := by
  let f : cornerRange E₁ E₂ n →ₗᵢ[ℂ] cornerRange E₁ E₂ n :=
    { (cornerRestrict E₁ E₂ R₁ n).toLinearMap with
      norm_map' := cornerRestrict_norm_map E₁ E₂ R₁ R₂ hE hR n }
  let e := LinearIsometryEquiv.ofSurjective f
    (LinearMap.injective_iff_surjective.mp f.injective)
  exact (Unitary.linearIsometryEquiv.symm e).property

/-- If [R is unitary](hyp:hR) and [the norm distance from C to R is less
than one](hyp:hC), then [C is invertible](goal). -/
-- @node: corner_isUnit_of_dist_unitary_lt_one
lemma corner_isUnit_of_dist_unitary_lt_one {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K]
    (C R : K →L[ℂ] K) (hR : R ∈ unitary _) (hC : ‖C - R‖ < 1) :
    IsUnit C := by
  have hid : 1 - star R * C = star R * (R - C) := by
    rw [mul_sub, Unitary.star_mul_self_of_mem hR]
  have hsmall : ‖1 - star R * C‖ < 1 := by
    rw [hid, CStarRing.norm_mem_unitary_mul _ (Unitary.star_mem hR), norm_sub_rev]
    exact hC
  have hnormalized : IsUnit (star R * C) := by
    simpa only [sub_sub_cancel] using isUnit_one_sub_of_norm_lt_one hsmall
  have hunit : IsUnit R := Unitary.isUnit_coe (U := ⟨R, hR⟩)
  simpa only [← mul_assoc, Unitary.mul_star_self_of_mem hR, one_mul] using
    hunit.mul hnormalized

/-- For [operator sequences C and R on possibly varying Hilbert spaces](hyp:C,R),
if [every R is unitary](hyp:hR) and [the norm distance from C to R tends
to zero](hyp:hC), then [C is eventually invertible](goal). -/
-- @node: corner_eventually_isUnit_of_error_tendsto
lemma corner_eventually_isUnit_of_error_tendsto
    (C R : ∀ n, H n →L[ℂ] H n) (hR : ∀ n, R n ∈ unitary _)
    (hC : Tendsto (fun n => ‖C n - R n‖) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, IsUnit (C n) := by
  have hsmall := hC.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [hsmall] with n hn
  exact corner_isUnit_of_dist_unitary_lt_one (C n) (R n) (hR n) hn

/-- For [operator sequences C and R on possibly varying Hilbert spaces](hyp:C,R),
if [every R is unitary](hyp:hR) and [the norm distance from C to R tends
to zero](hyp:hC), then [the norm distance from the adjoint of C times C
to the identity tends to zero](goal). -/
-- @node: corner_star_mul_sub_one_tendsto
lemma corner_star_mul_sub_one_tendsto
    (C R : ∀ n, H n →L[ℂ] H n) (hR : ∀ n, R n ∈ unitary _)
    (hC : Tendsto (fun n => ‖C n - R n‖) atTop (𝓝 0)) :
    Tendsto (fun n => ‖star (C n) * C n - 1‖) atTop (𝓝 0) := by
  simpa only [one_mul] using
    corner_star_mul_error_tendsto (fun n => 1) R C
      (fun n => IsStarProjection.one _) hR (fun n => Commute.one_right _) (by
        simpa only [one_mul] using hC)

/-- For [corner operators E₁ and E₂](hyp:E₁,E₂), [unitary candidates
R₁ and R₂](hyp:R₁,R₂), [approximating operators T](hyp:T), and
[identifying operators J](hyp:J), suppose [E₁ and E₂ are commuting
orthogonal projections](hyp:hE), [their common ranges are nonzero and
finite-dimensional](hyp:hD), and [R₁ and R₂ are unitary and each
commutes with both projections](hyp:hR). If [J is eventually unitary](hyp:hJ),
[T approaches E₁ times R₁ in norm](hyp:hT), and [J approaches the
identity in norm](hyp:hJI), then [the conjugate of T by the adjoint of J,
compressed to the common range, is eventually invertible and its adjoint
times itself approaches the identity in norm](goal). -/
-- @node: cornerRestrict_transferred_regular
lemma cornerRestrict_transferred_regular
    (E₁ E₂ R₁ R₂ T J : ∀ n, H n →L[ℂ] H n)
    (hE : CornerProjections E₁ E₂) (hD : CornerDimension E₁ E₂)
    (hR : CornerUnitaries E₁ E₂ R₁ R₂)
    (hJ : ∀ᶠ n in atTop, J n ∈ unitary _)
    (hT : Tendsto (fun n => ‖T n - E₁ n * R₁ n‖) atTop (𝓝 0))
    (hJI : Tendsto (fun n => ‖J n - 1‖) atTop (𝓝 0)) :
    let : ∀ n, FiniteDimensional ℂ (cornerRange E₁ E₂ n) := fun n => (hD n).2
    let C := fun n => cornerRestrict E₁ E₂ (fun m => star (J m) * T m * J m) n
    (∀ᶠ n in atTop, IsUnit (C n)) ∧
      Tendsto (fun n => ‖star (C n) * C n - 1‖) atTop (𝓝 0) := by
  let : ∀ n, FiniteDimensional ℂ (cornerRange E₁ E₂ n) := fun n => (hD n).2
  let C := fun n => cornerRestrict E₁ E₂ (fun m => star (J m) * T m * J m) n
  have herr := cornerRestrict_transport_error_tendsto E₁ E₂ R₁ R₂ T J hE hR hJ hT hJI
  have hunit := fun n => cornerRestrict_mem_unitary E₁ E₂ R₁ R₂ hE hR n
  exact ⟨corner_eventually_isUnit_of_error_tendsto C _ hunit herr,
    corner_star_mul_sub_one_tendsto C _ hunit herr⟩

/-- For [operator sequences P and E](hyp:P,E), suppose [each P is an
orthogonal projection](hyp:hP), [each E is an orthogonal projection](hyp:hE),
and [the norm distance from P to E tends to zero](hyp:hPE). Then
[the polar normalization of the intertwiner given by P times E plus the
product of their complementary projections is eventually unitary,
conjugates E to P, and approaches the identity in norm](goal). -/
-- @node: cornerIntertwiner_polar_identification
lemma cornerIntertwiner_polar_identification (P E : ∀ n, H n →L[ℂ] H n)
    (hP : ∀ n, IsStarProjection (P n)) (hE : ∀ n, IsStarProjection (E n))
    (hPE : Tendsto (fun n => ‖P n - E n‖) atTop (𝓝 0)) :
    let J := fun n => cornerPolar (cornerIntertwiner (P n) (E n))
    (∀ᶠ n in atTop, J n ∈ unitary _ ∧ J n * E n * star (J n) = P n) ∧
      Tendsto (fun n => ‖J n - 1‖) atTop (𝓝 0) := by
  let S := fun n => cornerIntertwiner (P n) (E n)
  have hu := cornerIntertwiner_eventually_isUnit P E hE hPE
  have herr := cornerIntertwiner_error_tendsto P E hE hPE
  have hsq := corner_star_mul_sub_one_tendsto S (fun n => 1)
    (fun n => one_mem (unitary _)) herr
  constructor
  · filter_upwards [hu] with n hn
    exact ⟨cornerPolar_mem_unitary (S n) hn,
      cornerPolar_conjugates (S n) (E n) (P n) hn
        (cornerIntertwiner_mul_projection (P n) (E n)
          (hP n).isIdempotentElem (hE n).isIdempotentElem)
        (cornerIntertwiner_star_mul_commute (P n) (E n) (hP n) (hE n))⟩
  · exact cornerPolar_error_tendsto S (fun n => 1)
      (fun n => one_mem (unitary _)) hu herr hsq

/-- For [corner operators E₁ and E₂](hyp:E₁,E₂), [unitary candidates R₁ and R₂](hyp:R₁,R₂),
[approximating operators T₁ and T₂](hyp:T₁,T₂), [projection candidates Q₁ and Q₂](hyp:Q₁,Q₂),
[identifying operators J](hyp:J), and [two sequences of von Neumann algebras](hyp:A₁,A₂),
suppose [E₁ and E₂ are commuting orthogonal projections](hyp:hE),
[their common ranges are nonzero and finite-dimensional](hyp:hD),
[R₁ and R₂ are unitary and each commutes with both projections](hyp:hR),
and [the two algebras commute element by element](hyp:hA).
Assume [each T belongs to its corresponding algebra and approaches the
corresponding product of E and R in norm](hyp:hT), [Q₁ and Q₂ are eventually
orthogonal projections in their respective algebras](hyp:hQ),
[J is eventually unitary and intertwines the common projection with the
product of Q₁ and Q₂](hyp:hJ), and [J approaches the identity in norm](hyp:hJI).
Then [there exist two operator sequences on the common ranges that are
eventually commuting unitaries and approach the respective restrictions
of R₁ and R₂ in norm](goal). -/
-- @node: corner_commuting_approximants_of_identification
lemma corner_commuting_approximants_of_identification
    (E₁ E₂ R₁ R₂ T₁ T₂ Q₁ Q₂ J : ∀ n, H n →L[ℂ] H n)
    (A₁ A₂ : ∀ n, VonNeumannAlgebra (H n))
    (hE : CornerProjections E₁ E₂) (hD : CornerDimension E₁ E₂)
    (hR : CornerUnitaries E₁ E₂ R₁ R₂) (hA : CornerAlgebras A₁ A₂)
    (hT : CornerApproximation A₁ A₂ T₁ T₂ E₁ E₂ R₁ R₂)
    (hQ : ∀ᶠ n in atTop, IsStarProjection (Q₁ n) ∧ IsStarProjection (Q₂ n) ∧
      Q₁ n ∈ A₁ n ∧ Q₂ n ∈ A₂ n)
    (hJ : ∀ᶠ n in atTop, J n ∈ unitary _ ∧
      J n * cornerProj E₁ E₂ n = (Q₁ n * Q₂ n) * J n)
    (hJI : Tendsto (fun n => ‖J n - 1‖) atTop (𝓝 0)) :
    let : ∀ n, FiniteDimensional ℂ (cornerRange E₁ E₂ n) := fun n => (hD n).2
    ∃ Rhat₁ Rhat₂ : ∀ n, cornerRange E₁ E₂ n →L[ℂ] cornerRange E₁ E₂ n,
      (∀ᶠ n in atTop, Rhat₁ n ∈ unitary _ ∧ Rhat₂ n ∈ unitary _ ∧
        Commute (Rhat₁ n) (Rhat₂ n)) ∧
      Tendsto (fun n => ‖Rhat₁ n - cornerRestrict E₁ E₂ R₁ n‖) atTop (𝓝 0) ∧
      Tendsto (fun n => ‖Rhat₂ n - cornerRestrict E₁ E₂ R₂ n‖) atTop (𝓝 0) := by
  let : ∀ n, FiniteDimensional ℂ (cornerRange E₁ E₂ n) := fun n => (hD n).2
  let C₁ := fun n => cornerRestrict E₁ E₂ (fun m => star (J m) * T₁ m * J m) n
  let C₂ := fun n => cornerRestrict E₁ E₂ (fun m => star (J m) * T₂ m * J m) n
  have hRs : CornerUnitaries E₁ E₂ R₂ R₁ := fun n =>
    ⟨(hR n).2.1, (hR n).1, (hR n).2.2.2.2.1, (hR n).2.2.2.2.2,
      (hR n).2.2.1, (hR n).2.2.2.1⟩
  have hR₁ := fun n => cornerRestrict_mem_unitary E₁ E₂ R₁ R₂ hE hR n
  have hR₂ := fun n => cornerRestrict_mem_unitary E₁ E₂ R₂ R₁ hE hRs n
  have herr := cornerRestrict_transport_errors_tendsto E₁ E₂ R₁ R₂ T₁ T₂ J
    hE hR (hJ.mono fun _ hn => hn.1) hT.2.1 hT.2.2 hJI
  have hu₁ := corner_eventually_isUnit_of_error_tendsto C₁ _ hR₁ herr.1
  have hu₂ := corner_eventually_isUnit_of_error_tendsto C₂ _ hR₂ herr.2
  have hsq₁ := corner_star_mul_sub_one_tendsto C₁ _ hR₁ herr.1
  have hsq₂ := corner_star_mul_sub_one_tendsto C₂ _ hR₂ herr.2
  refine ⟨fun n => cornerPolar (C₁ n), fun n => cornerPolar (C₂ n), ?_,
    cornerPolar_error_tendsto C₁ _ hR₁ hu₁ herr.1 hsq₁,
    cornerPolar_error_tendsto C₂ _ hR₂ hu₂ herr.2 hsq₂⟩
  filter_upwards [hQ, hJ, hu₁, hu₂] with n hqn hjn hcn₁ hcn₂
  have hc := cornerRestrict_transferred_commute E₁ E₂ Q₁ Q₂ T₁ T₂ J A₁ A₂ hE hA n
    hqn.1 hqn.2.1 hqn.2.2.1 hqn.2.2.2 (hT.1 n).1 (hT.1 n).2 hjn.1 hjn.2
  refine ⟨cornerPolar_mem_unitary (C₁ n) hcn₁,
    cornerPolar_mem_unitary (C₂ n) hcn₂, cornerPolar_commute (C₁ n) (C₂ n) hc.1 ?_⟩
  simpa only [star_star] using hc.2.star_star

/-- For [corner operators E₁ and E₂](hyp:E₁,E₂), [unitary candidates R₁ and R₂](hyp:R₁,R₂),
[approximating operators T₁ and T₂](hyp:T₁,T₂), and [two sequences of von Neumann
algebras](hyp:A₁,A₂), suppose [E₁ and E₂ are commuting orthogonal projections](hyp:hE),
[their common ranges are nonzero and finite-dimensional](hyp:hD),
[R₁ and R₂ are unitary and each commutes with both projections](hyp:hR), and
[the two algebras commute element by element](hyp:hA). If [each T belongs to
its corresponding algebra and approaches the corresponding product of E
and R in norm](hyp:hT), then [there exist two operator sequences on the
common ranges that are eventually commuting unitaries and approach the
respective restrictions of R₁ and R₂ in norm](goal). -/
-- @node: lem:corner
lemma corner_commuting_approximants
    (E₁ E₂ R₁ R₂ T₁ T₂ : ∀ n, H n →L[ℂ] H n)
    (A₁ A₂ : ∀ n, VonNeumannAlgebra (H n))
    (hE : CornerProjections E₁ E₂) (hD : CornerDimension E₁ E₂)
    (hR : CornerUnitaries E₁ E₂ R₁ R₂) (hA : CornerAlgebras A₁ A₂)
    (hT : CornerApproximation A₁ A₂ T₁ T₂ E₁ E₂ R₁ R₂) :
    let : ∀ n, FiniteDimensional ℂ (cornerRange E₁ E₂ n) := fun n => (hD n).2
    ∃ Rhat₁ Rhat₂ : ∀ n, cornerRange E₁ E₂ n →L[ℂ] cornerRange E₁ E₂ n,
      (∀ᶠ n in atTop, Rhat₁ n ∈ unitary _ ∧ Rhat₂ n ∈ unitary _ ∧ Commute (Rhat₁ n) (Rhat₂ n)) ∧ -- @realizes \widehat R_{1n}(eventual first unitary) @realizes \widehat R_{2n}(eventual commuting second unitary)
      Tendsto (fun n => ‖Rhat₁ n - cornerRestrict E₁ E₂ R₁ n‖) atTop (𝓝 0) ∧
      Tendsto (fun n => ‖Rhat₂ n - cornerRestrict E₁ E₂ R₂ n‖) atTop (𝓝 0) := by
  have hd₁ : Tendsto (fun n => ‖star (T₁ n) * T₁ n - E₁ n‖) atTop (𝓝 0) :=
    corner_star_mul_error_tendsto E₁ R₁ T₁ (fun n => (hE n).1)
      (fun n => (hR n).1) (fun n => (hR n).2.2.1) hT.2.1
  have hd₂ : Tendsto (fun n => ‖star (T₂ n) * T₂ n - E₂ n‖) atTop (𝓝 0) :=
    corner_star_mul_error_tendsto E₂ R₂ T₂ (fun n => (hE n).2.1)
      (fun n => (hR n).2.1) (fun n => (hR n).2.2.2.2.2) hT.2.2
  obtain ⟨Q₁, hQ₁, hQE₁⟩ := corner_spectral_projections T₁ E₁ A₁
    (fun n => (hE n).1) (fun n => (hT.1 n).1) hd₁
  obtain ⟨Q₂, hQ₂, hQE₂⟩ := corner_spectral_projections T₂ E₂ A₂
    (fun n => (hE n).2.1) (fun n => (hT.1 n).2) hd₂
  let P := fun n => Q₁ n * Q₂ n
  have hP : ∀ n, IsStarProjection (P n) := fun n =>
    (hQ₁ n).1.mul (hQ₂ n).1 (hA n _ (hQ₁ n).2 _ (hQ₂ n).2)
  have hEP : ∀ n, IsStarProjection (cornerProj E₁ E₂ n) := fun n =>
    (hE n).1.mul (hE n).2.1 (hE n).2.2
  have hPE : Tendsto (fun n => ‖P n - cornerProj E₁ E₂ n‖) atTop (𝓝 0) :=
    corner_product_projection_error_tendsto Q₁ Q₂ E₁ E₂
      (fun n => (hQ₁ n).1) (fun n => (hE n).2.1) hQE₁ hQE₂
  let J := fun n => cornerPolar (cornerIntertwiner (P n) (cornerProj E₁ E₂ n))
  have hJ := cornerIntertwiner_polar_identification P (cornerProj E₁ E₂) hP hEP hPE
  apply corner_commuting_approximants_of_identification E₁ E₂ R₁ R₂ T₁ T₂ Q₁ Q₂ J
    A₁ A₂ hE hD hR hA hT (Eventually.of_forall fun n =>
      ⟨(hQ₁ n).1, (hQ₂ n).1, (hQ₁ n).2, (hQ₂ n).2⟩) _ hJ.2
  filter_upwards [hJ.1] with n hn
  refine ⟨hn.1, ?_⟩
  calc
    J n * cornerProj E₁ E₂ n =
        (J n * cornerProj E₁ E₂ n * star (J n)) * J n := by
      rw [mul_assoc (J n * cornerProj E₁ E₂ n),
        Unitary.star_mul_self_of_mem hn.1, mul_one]
    _ = (Q₁ n * Q₂ n) * J n := by rw [hn.2]


end Papers.OaiNearInclusionsVon

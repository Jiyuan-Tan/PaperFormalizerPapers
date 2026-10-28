module

public import Papers.OaiNearInclusionsVon.TCircle
public import Papers.OaiNearInclusionsVon.Helpers.MainFactorAlgebras
public import Papers.OaiNearInclusionsVon.Helpers.MainJointLimits
public import Papers.OaiNearInclusionsVon.Helpers.MainSeparation
public import Papers.OaiNearInclusionsVon.Helpers.MainWeakCompact
public import Papers.OaiNearInclusionsVon.Helpers.MainCornerModel

/-! Vanishing one-sided gaps without small unitary implementations. -/

public section

set_option linter.style.longLine false
set_option maxSynthPendingDepth 32

namespace Papers.OaiNearInclusionsVon


open Filter
open scoped Topology

/-- [The norm of twice X minus Y equals twice the norm of X minus one
half of Y](goal). -/
-- @node: double_sub_half_norm
lemma double_sub_half_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X Y : E) : ‖X + X - Y‖ = 2 * ‖X - (1 / 2 : ℝ) • Y‖ := by
  have hid : X + X - Y = (2 : ℝ) • (X - (1 / 2 : ℝ) • Y) := by
    rw [smul_sub, smul_smul]
    norm_num
    rw [two_smul]
  rw [hid, norm_smul]
  norm_num

set_option maxHeartbeats 800000 in
/-- [There exist a positive constant ε₀ and a circle family with Laurent
coefficients such that all the constructed Hilbert spaces are separable,
the one-sided gaps from the source algebras to the target algebras converge
to zero, and, for all sufficiently large indices, every unitary that
conjugates the source algebra into the target algebra has operator-norm
distance at least ε₀ from the identity](goal). -/
-- @node: thm:main
theorem near_inclusion_not_implemented_by_small_unitaries :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ -- @realizes \varepsilon_0(positive absolute constant outside all indices and unitaries)
    ∃ (π : CircleRep) (A : LaurentData) (hπ : IsCircleFamily π A),
      (∀ n, TopologicalSpace.SeparableSpace (mainH n)) ∧
      Tendsto (mainGap π A hπ) atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, ∀ u ∈ unitary (mainH n →L[ℂ] mainH n), -- @realizes u(unitary on H_n)
        (∀ x ∈ mainSource π A hπ n, u * x * star u ∈ mainTarget n) → -- @realizes u(implements source inclusion in target)
          ε₀ ≤ ‖u - 1‖ := by
  obtain ⟨π, A, hπ⟩ := circle_family_exists
  have hno : ∀ (φ : ℕ → ClockNat) (u : ∀ k, mainH (φ k) →L[ℂ] mainH (φ k)),
      StrictMono φ → (∀ k, u k ∈ unitary _) →
      (∀ k, ∀ x ∈ mainSource π A hπ (φ k), u k * x * star (u k) ∈ mainTarget (φ k)) →
      ¬ Tendsto (fun k => ‖u k - 1‖) atTop (𝓝 0) := by
    intro φ u hφ hu hi hd
    let σ := fun k => mainSigma π A hπ (φ k) (u k) (hu k) (hi k)
    let A₁ := fun k => unitaryRepVN (unitaryRep_firstFactor (σ k))
    let A₂ := fun k => unitaryRepVN (unitaryRep_secondFactor (σ k))
    have hcomm (k : ℕ) (X Y : mainH (φ k) →L[ℂ] mainH (φ k))
        (hX : X ∈ A₁ k) (hY : Y ∈ A₂ k) : Commute X Y :=
      unitaryRep_factor_algebras_commute (σ k) X Y hX hY
    have herr (k : ℕ) (g : ProdGrp) :
        ‖(σ k g : mainH (φ k) →L[ℂ] mainH (φ k)) -
          (lamAmp g * rhoAmp g) * mainFAmp A (φ k) g‖ ≤
            nearC * nuN (φ k) + 2 * ‖u k - 1‖ :=
      mainSigma_error_le π A hπ (φ k) (u k) (hu k) g
    have hβ : Tendsto (fun k => nearC * nuN (φ k) + 2 * ‖u k - 1‖) atTop (𝓝 0) :=
      mainSigma_error_tendsto_zero φ hφ u hd
    have hlim₁ (k : ℕ) (ξ η : mainH (φ k)) :
        Tendsto (fun j => inner ℂ ξ
          ((lamAmp (gen j, 1) * rhoAmp (gen j, 1) * mainFAmp A (φ k) (gen j, 1) :
            mainH (φ k) →L[ℂ] mainH (φ k)) η)) atTop
          (𝓝 (inner ℂ ξ ((tParam • (mainCornerE1 (φ k) * mainCornerR1 (φ k))) η))) :=
      main_jointLimitA_tendsto_wot π A hπ (φ k) ξ η
    have hlim₂ (k : ℕ) (ξ η : mainH (φ k)) :
        Tendsto (fun j => inner ℂ ξ
          ((lamAmp (1, gen j) * rhoAmp (1, gen j) * mainFAmp A (φ k) (1, gen j) :
            mainH (φ k) →L[ℂ] mainH (φ k)) η)) atTop
          (𝓝 (inner ℂ ξ ((tParam • (mainCornerE2 (φ k) * mainCornerR2 (φ k))) η))) :=
      main_jointLimitB_tendsto_wot π A hπ (φ k) ξ η
    have hcluster₁ (k : ℕ) : ∃ B : mainH (φ k) →L[ℂ] mainH (φ k),
        B ∈ A₁ k ∧ ‖B - tParam • (mainCornerE1 (φ k) * mainCornerR1 (φ k))‖ ≤
          nearC * nuN (φ k) + 2 * ‖u k - 1‖ := by
      apply exists_vonNeumann_cluster_close (H := mainH (φ k)) (A₁ k)
        (fun j => (σ k (gen j, 1) : mainH (φ k) →L[ℂ] mainH (φ k)))
        (fun j => (lamAmp (gen j, 1) * rhoAmp (gen j, 1)) * mainFAmp A (φ k) (gen j, 1))
      · intro j
        apply (σ k (gen j, 1) : mainH (φ k) →L[ℂ] mainH (φ k)).opNorm_le_bound zero_le_one
        intro x
        simpa only [one_mul] using
          ((σ k (gen j, 1) : mainH (φ k) →L[ℂ] mainH (φ k)).norm_map_of_mem_unitary
            (σ k (gen j, 1)).property x).le
      · intro j
        exact unitaryRepVN_mem (unitaryRep_firstFactor (σ k)) (gen j)
      · exact fun j => herr k (gen j, 1)
      · exact fun x y => hlim₁ k y x
    have hcluster₂ (k : ℕ) : ∃ B : mainH (φ k) →L[ℂ] mainH (φ k),
        B ∈ A₂ k ∧ ‖B - tParam • (mainCornerE2 (φ k) * mainCornerR2 (φ k))‖ ≤
          nearC * nuN (φ k) + 2 * ‖u k - 1‖ := by
      apply exists_vonNeumann_cluster_close (H := mainH (φ k)) (A₂ k)
        (fun j => (σ k (1, gen j) : mainH (φ k) →L[ℂ] mainH (φ k)))
        (fun j => (lamAmp (1, gen j) * rhoAmp (1, gen j)) * mainFAmp A (φ k) (1, gen j))
      · intro j
        apply (σ k (1, gen j) : mainH (φ k) →L[ℂ] mainH (φ k)).opNorm_le_bound zero_le_one
        intro x
        simpa only [one_mul] using
          ((σ k (1, gen j) : mainH (φ k) →L[ℂ] mainH (φ k)).norm_map_of_mem_unitary
            (σ k (1, gen j)).property x).le
      · intro j
        exact unitaryRepVN_mem (unitaryRep_secondFactor (σ k)) (gen j)
      · exact fun j => herr k (1, gen j)
      · exact fun x y => hlim₂ k y x
    choose B₁ hB₁ he₁ using hcluster₁
    choose B₂ hB₂ he₂ using hcluster₂
    have hscaled (B C : ∀ k, mainH (φ k) →L[ℂ] mainH (φ k))
        (he : ∀ k, ‖B k - tParam • C k‖ ≤ nearC * nuN (φ k) + 2 * ‖u k - 1‖) :
        Tendsto (fun k => ‖B k + B k - C k‖) atTop (𝓝 0) := by
      apply squeeze_zero (fun _ => norm_nonneg _)
        (fun k => show ‖B k + B k - C k‖ ≤
          2 * (nearC * nuN (φ k) + 2 * ‖u k - 1‖) from by
            calc
              ‖B k + B k - C k‖ = 2 * ‖B k - tParam • C k‖ := by
                simpa only [tParam] using double_sub_half_norm (B k) (C k)
              _ ≤ _ := mul_le_mul_of_nonneg_left (he k) (by norm_num))
      simpa only [mul_zero] using hβ.const_mul 2
    obtain ⟨Uhat, Vhat, hUV, hlim⟩ :
        ∃ (Uhat Vhat : ∀ k, ClockSpace (φ k) →L[ℂ] ClockSpace (φ k)),
          (∀ k, Uhat k ∈ unitary _ ∧ Vhat k ∈ unitary _ ∧ Commute (Uhat k) (Vhat k)) ∧
          Tendsto (fun k => ‖Uhat k - clockU (φ k)‖ + ‖Vhat k - shiftV (φ k)‖)
            atTop (𝓝 0) := by
      apply mainCorner_commuting_approximants φ A₁ A₂
        (fun k => B₁ k + B₁ k) (fun k => B₂ k + B₂ k)
      · exact fun k X hX Y hY => hcomm k X Y hX hY
      · exact ⟨fun k => ⟨(A₁ k).add_mem (hB₁ k) (hB₁ k), (A₂ k).add_mem (hB₂ k) (hB₂ k)⟩,
          hscaled B₁ (fun k => mainCornerE1 (φ k) * mainCornerR1 (φ k)) he₁,
          hscaled B₂ (fun k => mainCornerE2 (φ k) * mainCornerR2 (φ k)) he₂⟩
    exact clock_shift_not_near_commuting.2.2 ⟨φ, Uhat, Vhat, hφ, hUV, hlim⟩
  have hres : ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ n in atTop,
      ∀ u ∈ unitary (mainH n →L[ℂ] mainH n),
        (∀ x ∈ mainSource π A hπ n, u * x * star u ∈ mainTarget n) → ε ≤ ‖u - 1‖ := by
    with_reducible exact main_eventual_separation_of_no_subsequence π A hπ hno
  obtain ⟨ε, hε, hsep⟩ := hres
  refine ⟨ε, hε, π, A, hπ, ?_, ?_, ?_⟩
  · exact mainH_separableSpace
  · exact mainGap_tendsto_zero π A hπ
  · exact hsep

end Papers.OaiNearInclusionsVon

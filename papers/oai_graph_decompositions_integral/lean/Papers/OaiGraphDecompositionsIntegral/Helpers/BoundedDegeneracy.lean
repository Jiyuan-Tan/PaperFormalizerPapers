module
public import Papers.OaiGraphDecompositionsIntegral.Helpers.ThresholdMonotonicity
public import Papers.OaiGraphDecompositionsIntegral.Helpers.BlockPartition
public import Papers.OaiGraphDecompositionsIntegral.Helpers.AssemblyQuantities
public import Papers.OaiGraphDecompositionsIntegral.TStars

/-! # Threshold assembly for the bounded-degeneracy branch

Split into forests, split by depth parity, and then split by unordered
endpoint-block pairs. The star theorem and expectation-threshold
monotonicity give the threshold estimate for every resulting piece.
-/

public section

namespace Papers.OaiGraphDecompositionsIntegral

-- @node: bounded_degeneracy_threshold_partition
/-- [There is an absolute cutoff of at least two such that, for every host order
n above it and every graph H on at most n vertices with degeneracy at most a
positive integer d, H has a partition into subgraphs indexed by d choices, two
choices, and an unordered pair of assembly blocks; each piece has containment
threshold at most twice the star constant A times the expectation threshold
of H](goal). -/
lemma bounded_degeneracy_threshold_partition :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ (V : Type) [Fintype V] [DecidableEq V] (H : SimpleGraph V)
        (d : ℕ), 0 < d → degeneracy H ≤ d → Fintype.card V ≤ n →
      ∃ P : (Fin d × Fin 2) × Sym2 (Fin assemblyBlockCount) → SimpleGraph V,
        (∀ i, P i ≤ H) ∧
        (∀ e ∈ H.edgeSet, ∃! i, e ∈ (P i).edgeSet) ∧
        ∀ i, containmentThreshold (P i) n ≤
          2 * starConstA * expectationThreshold H n := by
  classical
  obtain ⟨N₃, hstars⟩ := stars
  obtain ⟨N, hN⟩ := assembly_cutoff_exists 0 0 N₃
  refine ⟨N, hN.1, ?_⟩
  intro n hn V _ _ H d hdpos hd hsize
  let c : ℕ := ⌈(n : ℝ) / assemblyBlockCount⌉₊
  have hB : (0 : ℝ) < assemblyBlockCount := by norm_num [assemblyBlockCount]
  have hcapacity : Fintype.card V ≤ assemblyBlockCount * c := by
    apply hsize.trans
    have hc := (div_le_iff₀ hB).mp (Nat.le_ceil ((n : ℝ) / assemblyBlockCount))
    have : (n : ℝ) ≤ (assemblyBlockCount : ℝ) * c := by dsimp [c]; nlinarith
    exact_mod_cast this
  obtain ⟨P, hP, hpart, hstar, hsupport⟩ :=
    small_support_star_partition H d assemblyBlockCount c hdpos hd hcapacity
  refine ⟨P, hP, hpart, ?_⟩
  have hceil : (c : ℝ) = (⌈(n : ℝ) / assemblyBlockCount⌉ : ℤ) :=
    natCast_ceil_eq_intCast_ceil (by positivity)
  have hsmall : (2 : ℝ) * c ≤ (n : ℝ) / 100 := by
    rw [hceil]
    exact (hN.2.2.2.2 n hn).2.2
  intro i
  have hs : StarsSupport (P i) n := by
    change ((nonisolated (P i)).card : ℝ) ≤ (n : ℝ) / 100
    have hc : ((nonisolated (P i)).card : ℝ) ≤ 2 * (c : ℝ) := by
      exact_mod_cast hsupport i
    exact hc.trans hsmall
  have ht := (hstars n (hN.2.2.2.1.trans hn) V (P i)
    (by change Finite V; infer_instance) (hstar i) hsize hs).1
  calc
    containmentThreshold (P i) n ≤ 2 * starConstA * expectationThreshold (P i) n := ht
    _ ≤ 2 * starConstA * expectationThreshold H n :=
      mul_le_mul_of_nonneg_left (expectationThreshold_mono (hP i) n hsize)
        (by unfold starConstA; positivity)

end Papers.OaiGraphDecompositionsIntegral

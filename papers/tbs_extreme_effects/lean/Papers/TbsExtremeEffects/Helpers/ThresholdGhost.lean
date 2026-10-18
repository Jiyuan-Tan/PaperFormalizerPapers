module
public import Papers.TbsExtremeEffects.Helpers.ThresholdSignedMoments
public import Causalean.Stat.EmpiricalProcess.Countable.ProductSwap
public import Mathlib.Analysis.Convex.Integral

/-! The square ghost-sample comparison for strict threshold processes.
Paired iid swaps preserve the law, and splitting each signed difference
contributes two copies of the single-sample square maximum. -/

@[expose] public section
noncomputable section
namespace Papers.TbsExtremeEffects
open MeasureTheory
open scoped BigOperators
open Causalean.Stat.EmpiricalProcess.Countable

/-- For [two score samples](hyp:R), [their marks](hyp:z), [the second score sample](hyp:R'), [its marks](hyp:z'), [a lower threshold](hyp:ell), [a threshold above it](hyp:ht), and [a sign assignment](hyp:s), [the squared difference of their signed threshold sums is bounded by twice their signed square-maxima](goal). -/
-- @node: threshold_signed_difference_square_le
lemma threshold_signed_difference_square_le {n : ℕ}
    (R z R' z' : Fin n → ℝ) (ell t : ℝ) (ht : ell ≤ t) (s : Fin n → Bool) :
    ((∑ i : Fin n, if t < R i then (if s i then (1 : ℝ) else -1) * z i else 0) -
      (∑ i : Fin n, if t < R' i then (if s i then (1 : ℝ) else -1) * z' i else 0)) ^ 2 ≤
      2 * (thresholdSignedSquareMax R z ell s + thresholdSignedSquareMax R' z' ell s) := by
  have hx := (thresholdSignedSquareMax_properties R z ell).2.1 s t ht
  have hy := (thresholdSignedSquareMax_properties R' z' ell).2.1 s t ht
  nlinarith [sq_nonneg
    ((∑ i : Fin n, if t < R i then (if s i then (1 : ℝ) else -1) * z i else 0) +
      (∑ i : Fin n, if t < R' i then (if s i then (1 : ℝ) else -1) * z' i else 0))]

/-- [The ghost square maximum](goal) for [a score](hyp:R), [a mark](hyp:f), [a lower threshold](hyp:ell), and [a pair of samples](hyp:p) is the largest squared difference between their strict-threshold sums over all thresholds above that lower bound. -/
-- @node: thresholdGhostSquareMax
def thresholdGhostSquareMax {Ω : Type*} {n : ℕ} (R f : Ω → ℝ) (ell : ℝ)
    (p : (Fin n → Ω) × (Fin n → Ω)) : ℝ :=
  ⨆ t : Set.Ici ell,
    ((∑ i : Fin n, if t.1 < R (p.1 i) then f (p.1 i) else 0) -
      (∑ i : Fin n, if t.1 < R (p.2 i) then f (p.2 i) else 0)) ^ 2

/-- After [a paired sample](hyp:p) is swapped according to [a sign assignment](hyp:s), its [ghost square maximum](goal) is at most twice the sum of the two original signed square-maxima, for [the score](hyp:R), [mark](hyp:f), and [lower threshold](hyp:ell). -/
-- @node: thresholdGhostSquareMax_swap_le
lemma thresholdGhostSquareMax_swap_le {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (R f : Ω → ℝ) (ell : ℝ) (p : (Fin n → Ω) × (Fin n → Ω))
    (s : Fin n → Bool) :
    thresholdGhostSquareMax R f ell (pairedSampleSwap s p) ≤
      2 * (thresholdSignedSquareMax (R ∘ p.1) (f ∘ p.1) ell s +
        thresholdSignedSquareMax (R ∘ p.2) (f ∘ p.2) ell s) := by
  let : Nonempty (Set.Ici ell) := ⟨⟨ell, Set.mem_Ici.mpr le_rfl⟩⟩
  apply ciSup_le
  intro t
  have hswap :
      (∑ i : Fin n, if t.1 < R ((pairedSampleSwap s p).1 i)
        then f ((pairedSampleSwap s p).1 i) else 0) -
      (∑ i : Fin n, if t.1 < R ((pairedSampleSwap s p).2 i)
        then f ((pairedSampleSwap s p).2 i) else 0) =
      (∑ i : Fin n, if t.1 < R (p.1 i) then
        (if s i then (1 : ℝ) else -1) * f (p.1 i) else 0) -
      (∑ i : Fin n, if t.1 < R (p.2 i) then
        (if s i then (1 : ℝ) else -1) * f (p.2 i) else 0) := by
    simp only [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    cases h : s i <;> simp [pairedSampleSwap, h] <;> split_ifs <;> ring
  rw [hswap]
  exact threshold_signed_difference_square_le
    (R ∘ p.1) (f ∘ p.1) (R ∘ p.2) (f ∘ p.2) ell t.1 t.2 s

/-- For [a score](hyp:R), [a mark](hyp:f), [a lower threshold](hyp:ell), and [a pair of samples](hyp:p), the squared differences defining the ghost maximum have [a finite upper bound](goal). -/
-- @node: thresholdGhostSquareMax_bddAbove
lemma thresholdGhostSquareMax_bddAbove {Ω : Type*} {n : ℕ} (R f : Ω → ℝ)
    (ell : ℝ) (p : (Fin n → Ω) × (Fin n → Ω)) :
    BddAbove (Set.range (fun t : Set.Ici ell =>
      ((∑ i : Fin n, if t.1 < R (p.1 i) then f (p.1 i) else 0) -
        (∑ i : Fin n, if t.1 < R (p.2 i) then f (p.2 i) else 0)) ^ 2)) := by
  refine ⟨2 * (thresholdSignedSquareMax (R ∘ p.1) (f ∘ p.1) ell (fun _ => true) +
    thresholdSignedSquareMax (R ∘ p.2) (f ∘ p.2) ell (fun _ => true)), ?_⟩
  rintro _ ⟨t, rfl⟩
  simpa only [Function.comp_apply, if_true, one_mul] using
    threshold_signed_difference_square_le
      (R ∘ p.1) (f ∘ p.1) (R ∘ p.2) (f ∘ p.2) ell t.1 t.2 (fun _ => true)

/-- [The ghost square maximum](goal) of [a score](hyp:R), [a mark](hyp:f), [a lower threshold](hyp:ell), and [a pair of samples](hyp:p) is nonnegative. -/
-- @node: thresholdGhostSquareMax_nonneg
lemma thresholdGhostSquareMax_nonneg {Ω : Type*} {n : ℕ} (R f : Ω → ℝ)
    (ell : ℝ) (p : (Fin n → Ω) × (Fin n → Ω)) :
    0 ≤ thresholdGhostSquareMax R f ell p :=
  (sq_nonneg _).trans (le_ciSup (thresholdGhostSquareMax_bddAbove R f ell p)
    (⟨ell, Set.mem_Ici.mpr le_rfl⟩ : Set.Ici ell))

-- @node: measurable_thresholdGhostSquareMax
/-- If [the score is measurable](hyp:hR) and [the mark is measurable](hyp:hf), then [the ghost square maximum](goal), formed above [the lower threshold](hyp:ell), is measurable as a function of the paired sample. -/
@[fun_prop]
lemma measurable_thresholdGhostSquareMax {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (R f : Ω → ℝ) (ell : ℝ) (hR : Measurable R) (hf : Measurable f) :
    Measurable (thresholdGhostSquareMax (n := n) R f ell) := by
  classical
  obtain ⟨D, hD, hDT, _, hApprox⟩ :=
    exists_countable_oneSided_skeleton true (Set.Ici ell)
  let : Countable D := hD.to_subtype
  let F := fun (p : (Fin n → Ω) × (Fin n → Ω)) (t : ℝ) =>
    ((∑ i : Fin n, if t < R (p.1 i) then f (p.1 i) else 0) -
      (∑ i : Fin n, if t < R (p.2 i) then f (p.2 i) else 0)) ^ 2
  have hEq (p : (Fin n → Ω) × (Fin n → Ω)) :
      thresholdGhostSquareMax R f ell p = ⨆ t : D, F p t.1 := by
    have hBdd := thresholdGhostSquareMax_bddAbove R f ell p
    have hBddD : BddAbove (Set.range (fun t : D => F p t.1)) := by
      obtain ⟨B, hB⟩ := hBdd
      refine ⟨B, ?_⟩
      rintro _ ⟨t, rfl⟩
      exact hB ⟨⟨t.1, hDT t.2⟩, rfl⟩
    obtain ⟨s0, hs0, _⟩ := hApprox ell (Set.mem_Ici.mpr le_rfl)
    let : Nonempty D := ⟨⟨s0 0, hs0 0⟩⟩
    let : Nonempty (Set.Ici ell) := ⟨⟨ell, Set.mem_Ici.mpr le_rfl⟩⟩
    apply le_antisymm
    · apply ciSup_le
      intro t
      obtain ⟨v, hvD, hv⟩ := hApprox t.1 t.2
      have hLim : Filter.Tendsto (fun k => F p (v k)) Filter.atTop (nhds (F p t.1)) := by
        have hpoint (x : Ω) : Filter.Tendsto
            (fun k => if v k < R x then f x else 0) Filter.atTop
            (nhds (if t.1 < R x then f x else 0)) := by
          simpa only [← strict_threshold_eq_affine_closed] using
            thresholdFunction_tendsto true R f (-f) v t.1 hv x
        exact ((tendsto_finsetSum _ (fun i _ => hpoint (p.1 i))).sub
          (tendsto_finsetSum _ (fun i _ => hpoint (p.2 i)))).pow 2
      exact le_of_tendsto hLim (Filter.Eventually.of_forall
        (fun k => le_ciSup hBddD (⟨v k, hvD k⟩ : D)))
    · exact ciSup_le (fun t => le_ciSup hBdd (⟨t.1, hDT t.2⟩ : Set.Ici ell))
  rw [show thresholdGhostSquareMax (n := n) R f ell =
    (fun p => ⨆ t : D, F p t.1) from funext hEq]
  apply Measurable.iSup
  intro t
  dsimp only [F]
  have hm : Measurable (fun x : Ω => if t.1 < R x then f x else 0) :=
    Measurable.ite (measurableSet_lt measurable_const hR) hf measurable_const
  exact ((Finset.measurable_fun_sum _ (fun i _ =>
    hm.comp ((measurable_pi_apply i).comp measurable_fst))).sub
    (Finset.measurable_fun_sum _ (fun i _ =>
      hm.comp ((measurable_pi_apply i).comp measurable_snd)))).pow_const 2

/-- If [the ghost maximum is integrable](hyp:hGhost) and [every signed square maximum is integrable](hyp:hSigned), then [its integral for the distribution, score, mark, and lower threshold is at most four times the integral of the sign-averaged signed square maximum](goal). -/
-- @node: integral_thresholdGhostSquareMax_le_signed
lemma integral_thresholdGhostSquareMax_le_signed {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ}
    (R f : Ω → ℝ) (ell : ℝ)
    (hGhost : Integrable (thresholdGhostSquareMax (n := n) R f ell)
      ((Measure.pi (fun _ : Fin n => μ)).prod (Measure.pi (fun _ : Fin n => μ))))
    (hSigned : ∀ s : Fin n → Bool, Integrable
      (fun x : Fin n → Ω => thresholdSignedSquareMax (R ∘ x) (f ∘ x) ell s)
      (Measure.pi (fun _ : Fin n => μ))) :
    (∫ p, thresholdGhostSquareMax (n := n) R f ell p
      ∂((Measure.pi (fun _ : Fin n => μ)).prod (Measure.pi (fun _ : Fin n => μ)))) ≤
      4 * ∫ x : Fin n → Ω,
        signAverage (thresholdSignedSquareMax (R ∘ x) (f ∘ x) ell)
        ∂Measure.pi (fun _ : Fin n => μ) := by
  classical
  let ν := Measure.pi (fun _ : Fin n => μ)
  have hfixed (s : Fin n → Bool) :
      (∫ p, thresholdGhostSquareMax (n := n) R f ell p ∂ν.prod ν) ≤
        4 * ∫ x : Fin n → Ω, thresholdSignedSquareMax (R ∘ x) (f ∘ x) ell s ∂ν := by
    have hswap := pairedSampleSwap_measurePreserving μ s
    rw [← hswap.integral_comp' (thresholdGhostSquareMax R f ell)]
    calc
      _ ≤ ∫ p : (Fin n → Ω) × (Fin n → Ω),
          2 * (thresholdSignedSquareMax (R ∘ p.1) (f ∘ p.1) ell s +
            thresholdSignedSquareMax (R ∘ p.2) (f ∘ p.2) ell s) ∂ν.prod ν :=
        integral_mono
          (hswap.integrable_comp_emb (pairedSampleSwap s).measurableEmbedding |>.mpr hGhost)
          ((((hSigned s).comp_fst ν).add ((hSigned s).comp_snd ν)).const_mul 2)
          (fun p => thresholdGhostSquareMax_swap_le R f ell p s)
      _ = _ := by
        rw [integral_const_mul,
          integral_add ((hSigned s).comp_fst ν) ((hSigned s).comp_snd ν),
          integral_fun_fst (fun x : Fin n → Ω =>
            thresholdSignedSquareMax (R ∘ x) (f ∘ x) ell s),
          integral_fun_snd (fun x : Fin n → Ω =>
            thresholdSignedSquareMax (R ∘ x) (f ∘ x) ell s)]
        simp only [probReal_univ, one_smul]
        ring
  have havg := signAverage_mono
    (fun _ : Fin n → Bool => ∫ p, thresholdGhostSquareMax R f ell p ∂ν.prod ν)
    (fun s => 4 * ∫ x : Fin n → Ω,
      thresholdSignedSquareMax (R ∘ x) (f ∘ x) ell s ∂ν) hfixed
  have hconst (c : ℝ) : signAverage (fun _ : Fin n → Bool => c) = c := by
    simp [signAverage, Fintype.card_fin, Fintype.card_bool]
  have hlin : signAverage (fun s => 4 * ∫ x : Fin n → Ω,
      thresholdSignedSquareMax (R ∘ x) (f ∘ x) ell s ∂ν) =
      4 * ∫ x : Fin n → Ω,
        signAverage (thresholdSignedSquareMax (R ∘ x) (f ∘ x) ell) ∂ν := by
    unfold signAverage
    rw [integral_div, integral_finsetSum _ (fun s _ => hSigned s)]
    rw [← Finset.mul_sum]
    ring
  rw [hconst, hlin] at havg
  exact havg

/-- If [the score is measurable](hyp:hR), [the mark is measurable](hyp:hf), and [the thresholded squared-mark energy is integrable](hyp:hEnergy), then [the ghost square maximum is integrable and has the stated four-times sign-average integral bound](goal) for [the distribution](hyp:μ), [score](hyp:R), [mark](hyp:f), and [lower threshold](hyp:ell). -/
-- @node: threshold_ghost_square_comparison_of_energy
lemma threshold_ghost_square_comparison_of_energy {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ}
    (R f : Ω → ℝ) (ell : ℝ) (hR : Measurable R) (hf : Measurable f)
    (hEnergy : Integrable (fun x : Fin n → Ω =>
      ∑ i : Fin n, if ell < R (x i) then f (x i) ^ 2 else 0)
      (Measure.pi (fun _ : Fin n => μ))) :
    Integrable (thresholdGhostSquareMax (n := n) R f ell)
      ((Measure.pi (fun _ : Fin n => μ)).prod (Measure.pi (fun _ : Fin n => μ))) ∧
    (∫ p, thresholdGhostSquareMax (n := n) R f ell p
      ∂((Measure.pi (fun _ : Fin n => μ)).prod (Measure.pi (fun _ : Fin n => μ)))) ≤
      4 * ∫ x : Fin n → Ω,
        signAverage (thresholdSignedSquareMax (R ∘ x) (f ∘ x) ell)
        ∂Measure.pi (fun _ : Fin n => μ) := by
  classical
  let ν := Measure.pi (fun _ : Fin n => μ)
  let S := fun (x : Fin n → Ω) s =>
    thresholdSignedSquareMax (R ∘ x) (f ∘ x) ell s
  have hSmeas (s) : Measurable (fun x => S x s) := by
    exact measurable_thresholdSignedSquareMax (fun x => R ∘ x) (fun x => f ∘ x)
      ell s (fun i => hR.comp (measurable_pi_apply i))
      (fun i => hf.comp (measurable_pi_apply i))
  have hAvgMeas : Measurable (fun x => signAverage (S x)) := by
    unfold signAverage
    fun_prop
  have hAvg := (integral_thresholdSignedSquareMax_le_energy ν
    (fun x => R ∘ x) (fun x => f ∘ x) ell hAvgMeas.aestronglyMeasurable hEnergy).1
  have hSigned (s) : Integrable (fun x => S x s) ν := by
    apply (hAvg.const_mul ((2 : ℝ) ^ n)).mono' (hSmeas s).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg
      ((thresholdSignedSquareMax_properties (R ∘ x) (f ∘ x) ell).1 s)]
    have hle : S x s ≤ ∑ u : Fin n → Bool, S x u :=
      Finset.single_le_sum
        (fun u _ => (thresholdSignedSquareMax_properties (R ∘ x) (f ∘ x) ell).1 u)
        (Finset.mem_univ s)
    simpa only [signAverage, mul_div_cancel₀ _ (by positivity : (2 : ℝ) ^ n ≠ 0)] using hle
  have hGhost : Integrable (thresholdGhostSquareMax (n := n) R f ell) (ν.prod ν) := by
    apply (((hSigned (fun _ => true)).comp_fst ν).add
      ((hSigned (fun _ => true)).comp_snd ν)).const_mul 2 |>.mono'
        (measurable_thresholdGhostSquareMax R f ell hR hf).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro p
    rw [Real.norm_eq_abs, abs_of_nonneg (thresholdGhostSquareMax_nonneg R f ell p)]
    have hid : pairedSampleSwap (fun _ : Fin n => true) p = p := by ext i <;> rfl
    simpa only [hid, S, Pi.add_apply] using
      thresholdGhostSquareMax_swap_le R f ell p (fun _ => true)
  exact ⟨hGhost, integral_thresholdGhostSquareMax_le_signed μ R f ell hGhost hSigned⟩

/-- If [the threshold lies above the lower bound](hyp:ht), [the thresholded mark is integrable](hyp:hMark), and [the conditional ghost maximum is integrable](hyp:hGhost), then [the squared centered threshold sum for the sample is bounded by the expected ghost square maximum](goal). -/
-- @node: threshold_centered_square_le_ghost
lemma threshold_centered_square_le_ghost {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ}
    (R f : Ω → ℝ) (ell t : ℝ) (ht : ell ≤ t) (x : Fin n → Ω)
    (hMark : Integrable (fun y => if t < R y then f y else 0) μ)
    (hGhost : Integrable (fun y : Fin n → Ω => thresholdGhostSquareMax R f ell (x, y))
      (Measure.pi (fun _ : Fin n => μ))) :
    ((∑ i : Fin n, if t < R (x i) then f (x i) else 0) -
      (n : ℝ) * ∫ y, (if t < R y then f y else 0) ∂μ) ^ 2 ≤
      ∫ y : Fin n → Ω, thresholdGhostSquareMax R f ell (x, y)
        ∂Measure.pi (fun _ : Fin n => μ) := by
  let ν := Measure.pi (fun _ : Fin n => μ)
  let g : (Fin n → Ω) → ℝ := fun y =>
    (∑ i : Fin n, if t < R (x i) then f (x i) else 0) -
      ∑ i : Fin n, if t < R (y i) then f (y i) else 0
  have hSum : Integrable
      (fun y : Fin n → Ω => ∑ i : Fin n, if t < R (y i) then f (y i) else 0) ν :=
    integrable_finsetSum _ (fun i _ =>
      integrable_comp_eval (μ := fun _ : Fin n => μ) (i := i) hMark)
  have hg : Integrable g ν := (integrable_const _).sub hSum
  have hCenter : ∫ y, g y ∂ν =
      (∑ i : Fin n, if t < R (x i) then f (x i) else 0) -
        (n : ℝ) * ∫ y, (if t < R y then f y else 0) ∂μ := by
    rw [integral_sub (integrable_const _) hSum, integral_const,
      integral_finsetSum _ (fun i _ =>
        integrable_comp_eval (μ := fun _ : Fin n => μ) (i := i) hMark)]
    simp only [probReal_univ, one_smul,
      integral_comp_eval (μ := fun _ : Fin n => μ) hMark.aestronglyMeasurable, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hDom (y : Fin n → Ω) : g y ^ 2 ≤ thresholdGhostSquareMax R f ell (x, y) :=
    le_ciSup (thresholdGhostSquareMax_bddAbove R f ell (x, y))
      (⟨t, Set.mem_Ici.mpr ht⟩ : Set.Ici ell)
  have hg2 : Integrable (fun y => g y ^ 2) ν := by
    apply hGhost.mono' (hg.aestronglyMeasurable.pow 2)
    exact Filter.Eventually.of_forall (fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hDom y)
  have hJensen : (∫ y, g y ∂ν) ^ 2 ≤ ∫ y, g y ^ 2 ∂ν := by
    have hc : ConvexOn ℝ Set.univ (fun a : ℝ => a ^ 2) :=
      (show Even (2 : ℕ) from ⟨1, rfl⟩).convexOn_pow
    exact hc.map_integral_le (continuous_id.pow 2).continuousOn isClosed_univ
      (Filter.Eventually.of_forall (fun _ => Set.mem_univ _)) hg hg2
  rw [← hCenter]
  exact hJensen.trans (integral_mono hg2 hGhost hDom)

/-- If [the score is measurable](hyp:hR), [the mark is measurable](hyp:hf), [all thresholded marks are integrable](hyp:hMark), and [the thresholded squared-mark energy is integrable](hyp:hEnergy), then for [the distribution](hyp:μ), [score](hyp:R), [mark](hyp:f), and [lower threshold](hyp:ell) there exists [a measurable nonnegative integrable envelope](goal) with the stated expectation bound that dominates every centered threshold square almost surely. -/
-- @node: threshold_square_symmetrization_envelope
lemma threshold_square_symmetrization_envelope {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ}
    (R f : Ω → ℝ) (ell : ℝ) (hR : Measurable R) (hf : Measurable f)
    (hMark : ∀ t ≥ ell, Integrable (fun y => if t < R y then f y else 0) μ)
    (hEnergy : Integrable (fun x : Fin n → Ω =>
      ∑ i : Fin n, if ell < R (x i) then f (x i) ^ 2 else 0)
      (Measure.pi (fun _ : Fin n => μ))) :
    ∃ H : (Fin n → Ω) → ℝ, Measurable H ∧
      Integrable H (Measure.pi (fun _ : Fin n => μ)) ∧
      (∀ x, 0 ≤ H x) ∧
      (∫ x, H x ∂Measure.pi (fun _ : Fin n => μ)) ≤
        4 * ∫ x : Fin n → Ω,
          signAverage (thresholdSignedSquareMax (R ∘ x) (f ∘ x) ell)
          ∂Measure.pi (fun _ : Fin n => μ) ∧
      ∀ᵐ x ∂Measure.pi (fun _ : Fin n => μ), ∀ t ≥ ell,
        ((∑ i : Fin n, if t < R (x i) then f (x i) else 0) -
          (n : ℝ) * ∫ y, (if t < R y then f y else 0) ∂μ) ^ 2 ≤ H x := by
  let ν := Measure.pi (fun _ : Fin n => μ)
  obtain ⟨hGhostInt, hGhostBound⟩ :=
    threshold_ghost_square_comparison_of_energy μ R f ell hR hf hEnergy
  let H : (Fin n → Ω) → ℝ := fun x =>
    ∫ y, thresholdGhostSquareMax R f ell (x, y) ∂ν
  refine ⟨H, ?_, hGhostInt.integral_prod_left, ?_, ?_, ?_⟩
  · have hm := (measurable_thresholdGhostSquareMax (n := n) R f ell hR hf).stronglyMeasurable
    exact hm.integral_prod_right'.measurable
  · intro x
    exact integral_nonneg (fun y => thresholdGhostSquareMax_nonneg R f ell (x, y))
  · rw [← integral_prod _ hGhostInt]
    exact hGhostBound
  · filter_upwards [hGhostInt.prod_right_ae] with x hx
    intro t ht
    exact threshold_centered_square_le_ghost μ R f ell t ht x (hMark t ht) hx

end Papers.TbsExtremeEffects

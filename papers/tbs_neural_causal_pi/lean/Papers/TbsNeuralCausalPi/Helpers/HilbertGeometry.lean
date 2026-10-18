module
public import Papers.TbsNeuralCausalPi.Setup.Cubes
public import Causalean.Mathlib.Topology.SpaceFillingCurve.CurveGeometry
public import Mathlib.Topology.MetricSpace.Holder
/-! # One-norm geometry of the localized Hilbert curve

The traversal library gives a squared Euclidean modulus. Cauchy–Schwarz
converts it to the paper's one-norm Hölder bound while retaining localization.
-/
public section
namespace Papers.TbsNeuralCausalPi
open scoped NNReal ENNReal
open Causalean.Mathlib.Topology.SpaceFillingCurve

/-- For a localized Hilbert curve, suppose [the dimension is at least
two](hyp:hd), [the first parameter lies in the closed unit interval](hyp:hs),
and [the second parameter also lies in that interval](hyp:ht). Then [the
one-norm distance between the curve values is at most four times the
dimension times the absolute parameter difference raised to the reciprocal
of the dimension](goal). -/
-- @node: localizedHilbert_l1_dist_le
lemma localizedHilbert_l1_dist_le {d : ℕ} {T : DyadicTraversal d}
    (H : LocalizedCubeMap d T) (hd : 2 ≤ d) {s t : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    dist (WithLp.toLp 1 (H.toFun s)) (WithLp.toLp 1 (H.toFun t)) ≤
      4 * (d : ℝ) * |s-t| ^ ((1 : ℝ) / d) := by
  have hcs : (∑ j, |H.toFun s j - H.toFun t j|) ^ 2 ≤
      (d : ℝ) * sqEuclideanDist (H.toFun s) (H.toFun t) := by
    simpa [sqEuclideanDist, sq_abs, mul_comm] using
      (Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
        (fun j : Fin d => |H.toFun s j - H.toFun t j|) (fun _ => (1 : ℝ)))
  have hmod := H.modulus hd hs ht
  have hpow : (|s-t| ^ ((1 : ℝ) / d)) ^ 2 = |s-t| ^ ((2 : ℝ) / d) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg (s-t))]
    congr 1
    ring
  have hnonneg : 0 ≤ |s-t| ^ ((1 : ℝ) / d) := Real.rpow_nonneg (abs_nonneg _) _
  have hsq := mul_le_mul_of_nonneg_left hmod (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
  have hsquares : (∑ j, |H.toFun s j - H.toFun t j|) ^ 2 ≤
      (4 * (d : ℝ) * |s-t| ^ ((1 : ℝ) / d)) ^ 2 := by
    calc
      _ ≤ (d : ℝ) * (16 * d * |s-t| ^ ((2 : ℝ) / d)) := hcs.trans hsq
      _ = _ := by rw [← hpow]; ring
  rw [PiLp.dist_eq_of_L1]
  simp only [Real.dist_eq]
  exact (sq_le_sq₀ (Finset.sum_nonneg (fun j _ => abs_nonneg _))
    (by positivity)).mp hsquares

/-- If [the dimension is at least two](hyp:hd), then [the localized Hilbert
curve on the closed unit interval is Hölder in the one-norm metric, with
constant four times the dimension and exponent the reciprocal of the
dimension](goal). -/
-- @node: localizedHilbert_holderOnWith
lemma localizedHilbert_holderOnWith {d : ℕ} {T : DyadicTraversal d}
    (H : LocalizedCubeMap d T) (hd : 2 ≤ d) :
    HolderOnWith (4 * (d : ℝ≥0)) ((d : ℝ≥0)⁻¹)
      (fun t => WithLp.toLp 1 (H.toFun t)) (Set.Icc (0 : ℝ) 1) := by
  intro s hs t ht
  have hh := localizedHilbert_l1_dist_le H hd hs ht
  have hh' := ENNReal.ofReal_le_ofReal hh
  simpa [edist_dist, Real.dist_eq, ENNReal.ofReal_mul, ENNReal.ofReal_rpow_of_nonneg,
    NNReal.coe_inv, one_div] using hh'

end Papers.TbsNeuralCausalPi

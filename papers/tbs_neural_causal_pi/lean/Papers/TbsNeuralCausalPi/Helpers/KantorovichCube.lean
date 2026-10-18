module
public import Papers.TbsNeuralCausalPi.Setup.Notation
public import Causalean.PO.ID.Partial.LP.ConicDuality
public import Toolkit.Foundations.MeasureTheory.KantorovichRubinstein
/-! # Kantorovich comparison on a compact one-norm cube -/
public section
namespace Papers.TbsNeuralCausalPi
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
open MeasureTheory
open scoped ENNReal NNReal
-- @node: wasserstein1_eq_toolkit
/-- For any two measures, [the paper's first Wasserstein transport cost equals
the toolkit's first Wasserstein transport cost](goal). -/
lemma wasserstein1_eq_toolkit {X : Type*} [MeasurableSpace X]
    [PseudoEMetricSpace X] [BorelSpace X] (mu nu : Measure X) :
    wasserstein1 mu nu = Toolkit.Foundations.MeasureTheory.wasserstein1 mu nu := by
  rfl

/-- For any two measures, [their first Wasserstein transport cost equals the
infimum, over all probability couplings with those marginals, of the expected
extended distance between the two coordinates](goal). -/
lemma wasserstein1_eq_couplings {X : Type*} [MeasurableSpace X]
    [PseudoEMetricSpace X] [BorelSpace X] (mu nu : Measure X) :
    wasserstein1 mu nu = ⨅ pi : couplings mu nu, ∫⁻ z, edist z.1 z.2 ∂pi.val := by
  unfold wasserstein1 couplings Toolkit.Foundations.MeasureTheory.wasserstein1
  apply le_antisymm
  · refine le_iInf fun pi => ?_
    exact iInf_le_of_le pi.val (iInf_le_of_le
      ⟨pi.property.1, pi.property.2.1, pi.property.2.2⟩ le_rfl)
  · refine le_iInf fun pi => le_iInf fun hpi => ?_
    exact iInf_le_of_le ⟨pi, hpi.isProbabilityMeasure, hpi.map_fst, hpi.map_snd⟩ le_rfl

-- @node: boundedCube_isCompact
/-- In any finite dimension and for any real coordinate bound, [the set of vectors
whose coordinates are all bounded in absolute value by that bound is compact
under the one-norm metric](goal). -/
lemma boundedCube_isCompact (d : ℕ) (K : ℝ) : IsCompact (boundedCube d K) := by
  have hc := (isCompact_univ_pi (fun _ : Fin d => isCompact_Icc (a := -K) (b := K))).image
    (PiLp.continuous_toLp (p := (1 : ENNReal)) (β := fun _ : Fin d => ℝ))
  convert hc using 1
  ext x
  simp only [boundedCube, Set.mem_ofPred_eq, abs_le, Set.mem_image]
  constructor
  · intro hx
    exact ⟨x.ofLp, fun j _ => hx j, WithLp.toLp_ofLp 1 x⟩
  · rintro ⟨y, hy, rfl⟩
    exact fun j => hy j (Set.mem_univ j)

-- @node: wasserstein1_le_sup_lipschitz_cube
/-- If [the cube radius is nonnegative](hyp:hK), [the first probability law gives
the cube full mass](hyp:hmu), and [the second probability law gives the cube full
mass](hyp:hnu), [their first Wasserstein transport cost is at most the supremum
of the nonnegative parts of the first law's expectation minus the second law's
expectation, over real functions that are one-Lipschitz on the cube in the
one-norm metric and vanish at zero](goal). -/
lemma wasserstein1_le_sup_lipschitz_cube {d : ℕ} (K : ℝ) (hK : 0 ≤ K)
    (mu nu : ProbabilityMeasure (L1Vec d))
    (hmu : (mu : Measure (L1Vec d)) (boundedCube d K) = 1)
    (hnu : (nu : Measure (L1Vec d)) (boundedCube d K) = 1) :
    wasserstein1 (mu : Measure (L1Vec d)) (nu : Measure (L1Vec d)) ≤
      ⨆ h : {h : L1Vec d → ℝ // LipschitzOnWith 1 h (boundedCube d K) ∧ h 0 = 0}, -- @realizes \mathcal{H}_\delta(one-Lipschitz test class anchored at zero; finite nets are chosen in the empirical proof)
        ENNReal.ofReal ((∫ x : L1Vec d, h.val x ∂(mu : Measure (L1Vec d))) -
          ∫ x : L1Vec d, h.val x ∂(nu : Measure (L1Vec d))) := by
  classical
  let : BorelSpace (L1Vec d) := ⟨rfl⟩
  let C := boundedCube d K
  have hC : IsCompact C := boundedCube_isCompact d K
  let : CompactSpace C := isCompact_iff_compactSpace.mp hC
  let m := (mu : Measure (L1Vec d)).comap ((↑) : C → L1Vec d)
  let n := (nu : Measure (L1Vec d)).comap ((↑) : C → L1Vec d)
  let : IsProbabilityMeasure m :=
    (Toolkit.Foundations.MeasureTheory.probability_comap_subtype _ C hC.measurableSet hmu).1
  let : IsProbabilityMeasure n :=
    (Toolkit.Foundations.MeasureTheory.probability_comap_subtype _ C hC.measurableSet hnu).1
  rw [wasserstein1_eq_toolkit,
    Toolkit.Foundations.MeasureTheory.wasserstein1_eq_iSup_lipschitzOn _ _ C hC hmu hnu]
  refine iSup_le fun f => ?_
  let g : L1Vec d → ℝ := fun x => f.val x - f.val 0
  have hg : LipschitzOnWith 1 g C := by
    intro x hx y hy
    simpa only [g, edist_dist, Real.dist_eq, sub_sub_sub_cancel_right] using
      f.property hx hy
  have hcontrast : Toolkit.Foundations.MeasureTheory.lipschitzContrast
      (mu : Measure (L1Vec d)) (nu : Measure (L1Vec d)) g =
      Toolkit.Foundations.MeasureTheory.lipschitzContrast
        (mu : Measure (L1Vec d)) (nu : Measure (L1Vec d)) f.val := by
    rw [Toolkit.Foundations.MeasureTheory.lipschitzContrast_eq_subtype_comap
      _ _ C hC.measurableSet hmu hnu g,
      Toolkit.Foundations.MeasureTheory.lipschitzContrast_eq_subtype_comap
      _ _ C hC.measurableSet hmu hnu f.val]
    have hm : Integrable (fun x : C => f.val x.val) m :=
      f.property.to_restrict.continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hn : Integrable (fun x : C => f.val x.val) n :=
      f.property.to_restrict.continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    change (∫ x : C, f.val x.val - f.val 0 ∂m) -
      (∫ x : C, f.val x.val - f.val 0 ∂n) =
      (∫ x : C, f.val x.val ∂m) - (∫ x : C, f.val x.val ∂n)
    simp only [
      integral_sub hm (integrable_const (f.val 0)),
      integral_sub hn (integrable_const (f.val 0)), integral_const,
      probReal_univ, one_smul]
    ring
  rw [← hcontrast]
  exact le_iSup_of_le ⟨g, hg, sub_self _⟩ le_rfl
end Papers.TbsNeuralCausalPi

module
public import Papers.TbsNeuralCausalPi.Setup.Cubes
public import Papers.TbsNeuralCausalPi.Setup.Networks
public import Papers.TbsNeuralCausalPi.Setup.Assumptions.Generators
public import Mathlib.Topology.MetricSpace.Holder
public import Papers.TbsNeuralCausalPi.Helpers.HilbertSection
public import Papers.TbsNeuralCausalPi.Helpers.HilbertReparameterization
public import Papers.TbsNeuralCausalPi.Helpers.HilbertQuantile
public import Papers.TbsNeuralCausalPi.Helpers.OneDimensionalCurve
public import Papers.TbsNeuralCausalPi.Helpers.HilbertGeometry
public import Papers.TbsNeuralCausalPi.Helpers.HilbertMeasure
/-! # Coherent Hilbert order and measure-representing Hölder curves -/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
open MeasureTheory
open scoped NNReal

/-- If [a curve is continuous on the closed unit interval](hyp:hgamma) and
[sends the uniform interval law to a measure](hyp:hmap), then [every point of
the curve on that interval, including its endpoints, belongs to the support
of that measure](goal). -/
-- @node: continuous_representing_curve_mapsTo_support
lemma continuous_representing_curve_mapsTo_support {D : ℕ}
    (P : Measure (L1Vec D)) (gamma : ℝ → L1Vec D)
    (hgamma : ContinuousOn gamma (Set.Icc (0 : ℝ) 1))
    (hmap : curveLebesgue.map gamma = P) :
    Set.MapsTo gamma (Set.Icc (0 : ℝ) 1) (measureSupport P) := by
  let : BorelSpace (L1Vec D) := ⟨rfl⟩
  intro t ht U hU hmem
  have hpos := continuous_interval_map_open_pos gamma hgamma ht U hU hmem
  rw [show volume.restrict (Set.Icc (0 : ℝ) 1) = curveLebesgue from rfl, hmap] at hpos
  exact ne_of_gt hpos

/-- For [a subdivision level](hyp:n) and [an integer grid address in each
coordinate](hyp:a), the [dyadic grid cube](goal) consists of the points whose
coordinates lie between the address divided by two to that level and the next
integer divided by the same quantity, including both endpoints. -/
-- @node: dyadicGridCube
def dyadicGridCube {d : ℕ} (n : ℕ) (a : Fin d → Fin (2^n)) : Set (Fin d → ℝ) :=
  {x | ∀ r, x r ∈ Set.Icc ((a r : ℝ) / (2^n : ℝ))
    (((a r : ℝ) + 1) / (2^n : ℝ))}

-- @node: dyadicGrid_forward_face
/-- If [one grid address is exactly one step ahead of another in a chosen
coordinate](hyp:hstep) and [the addresses agree in every other
coordinate](hyp:hsame), then [their closed dyadic cubes have a nonempty
intersection equal to a face with the chosen coordinate fixed and every other
coordinate ranging over a closed interval of length two to the negative
subdivision level](goal). -/
lemma dyadicGrid_forward_face {d n : ℕ} (a b : Fin d → Fin (2^n)) (k : Fin d)
    (hstep : (a k).val + 1 = (b k).val)
    (hsame : ∀ r, r ≠ k → a r = b r) :
    (dyadicGridCube n a ∩ dyadicGridCube n b).Nonempty ∧
      ∃ c : ℝ, ∃ l u : Fin d → ℝ,
        (∀ r, r ≠ k → u r - l r = (2^n : ℝ)⁻¹) ∧
        dyadicGridCube n a ∩ dyadicGridCube n b =
          {x | x k = c ∧ ∀ r, r ≠ k → x r ∈ Set.Icc (l r) (u r)} := by
  let q : ℝ := 2^n
  let c : ℝ := ((a k : ℝ) + 1) / q
  let l : Fin d → ℝ := fun r => (a r : ℝ) / q
  let u : Fin d → ℝ := fun r => ((a r : ℝ) + 1) / q
  have hq : 0 < q := by dsimp [q]; positivity
  have hb : (b k : ℝ) = (a k : ℝ) + 1 := by exact_mod_cast hstep.symm
  have hlu (r : Fin d) : l r ≤ u r := by
    dsimp [l, u]
    exact div_le_div_of_nonneg_right (by linarith) hq.le
  have heq : dyadicGridCube n a ∩ dyadicGridCube n b =
      {x | x k = c ∧ ∀ r, r ≠ k → x r ∈ Set.Icc (l r) (u r)} := by
    ext x
    constructor
    · intro hx
      have ha := hx.1 k
      have hh := hx.2 k
      change (a k : ℝ) / q ≤ x k ∧ x k ≤ c at ha
      change (b k : ℝ) / q ≤ x k ∧ x k ≤ ((b k : ℝ) + 1) / q at hh
      rw [hb] at hh
      exact ⟨le_antisymm ha.2 hh.1, fun r _ => hx.1 r⟩
    · rintro ⟨hx, hr⟩
      constructor
      · intro r
        by_cases hk : r = k
        · subst r
          change l k ≤ x k ∧ x k ≤ u k
          rw [hx]
          exact ⟨hlu k, le_rfl⟩
        · exact hr r hk
      · intro r
        by_cases hk : r = k
        · subst r
          change (b k : ℝ) / q ≤ x k ∧ x k ≤ ((b k : ℝ) + 1) / q
          rw [hx, hb]
          refine ⟨le_rfl, ?_⟩
          exact div_le_div_of_nonneg_right (by linarith) hq.le
        · rw [← hsame r hk]
          exact hr r hk
  constructor
  · rw [heq]
    refine ⟨Function.update l k c, ?_, ?_⟩
    · simp
    · intro r hr
      simpa [Function.update_of_ne hr] using (show l r ∈ Set.Icc (l r) (u r) from
        ⟨le_rfl, hlu r⟩)
  · refine ⟨c, l, u, ?_, heq⟩
    intro r _
    dsimp [u, l, q]
    ring


-- @node: lem:hilbert
/-- Given [a family of cells indexed by refinement level and cell word](hyp:cells),
suppose [this family has the prescribed initial cube,
refinement, and disjoint-interior properties](hyp:hstar) and [in positive dimension its
cells at each level are exactly the dyadic cubes](hyp:hdyadic). Then [at every
level the dyadic addresses admit a bijective ordering that enumerates exactly
these cells, groups each consecutive block of two to the dimension many finer
cells under its coarser parent, and makes consecutive cubes meet in a nonempty
face whose free coordinate intervals have the grid side length](goal). -/
lemma hilbert_ordering (d : ℕ) (cells : ∀ n, CellWord d n → Set (Fin d → ℝ))
    (hstar : HasPropertyStar d cells)
    (hdyadic : 0 < d → ∀ n, Set.range (cells n) = dyadicCubeCollection d n) :
    ∃ O : ∀ n, Fin (2^(d*n)) ≃ (Fin d → Fin (2^n)), -- @realizes O_n(dyadic addresses encoded as lattice coordinates; each coordinate's binary digits give the cell word)
      (∀ n, Set.range (fun i => dyadicGridCube n (O n i)) = Set.range (cells n)) ∧
      (∀ n (i : Fin (2^(d*(n+1)))) (j : Fin (2^(d*n))),
        i.val / 2^d = j.val → ∀ r : Fin d, (O (n+1) i r).val / 2 = (O n j r).val) ∧
      ∀ n (i j : Fin (2^(d*n))), j.val = i.val+1 →
        (dyadicGridCube n (O n i) ∩ dyadicGridCube n (O n j)).Nonempty ∧
          ∃ k : Fin d, ∃ a : ℝ, ∃ l u : Fin d → ℝ,
            (∀ r, r ≠ k → u r - l r = (2^n : ℝ)⁻¹) ∧
              dyadicGridCube n (O n i) ∩ dyadicGridCube n (O n j) =
                {x | x k = a ∧ ∀ r, r ≠ k → x r ∈ Set.Icc (l r) (u r)} := by
  classical
  by_cases hd : 0 < d
  · obtain ⟨T⟩ := Causalean.Mathlib.Topology.SpaceFillingCurve.exists_dyadicTraversal d hd
    let O : ∀ n, Fin (2^(d*n)) ≃ (Fin d → Fin (2^n)) :=
      fun n => Equiv.ofBijective (T.cell n) (T.bijective n)
    refine ⟨O, ?_, ?_, ?_⟩
    · intro n
      rw [hdyadic hd n]
      change Set.range (fun i => dyadicGridCube n (O n i)) = Set.range (dyadicGridCube n)
      ext S
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨O n i, rfl⟩
      · rintro ⟨a, rfl⟩
        exact ⟨(O n).symm a, by simp⟩
    · intro n i j hij r
      exact T.nested n j i hij r
    · intro n i j hij
      obtain ⟨k, hstep, hsame⟩ := T.adjacent n i j hij
      rcases hstep with hforward | hreverse
      · obtain ⟨hne, c, l, u, hlength, hface⟩ :=
          dyadicGrid_forward_face (T.cell n i) (T.cell n j) k hforward hsame
        exact ⟨hne, k, c, l, u, hlength, hface⟩
      · obtain ⟨hne, c, l, u, hlength, hface⟩ :=
          dyadicGrid_forward_face (T.cell n j) (T.cell n i) k hreverse
            (fun r hr => (hsame r hr).symm)
        rw [Set.inter_comm] at hne hface
        exact ⟨hne, k, c, l, u, hlength, hface⟩
  · have hd0 : d = 0 := by omega
    subst d
    have hcells : ∀ n (w : CellWord 0 n), cells n w = Set.univ := by
      intro n
      induction n with
      | zero =>
          intro w
          rw [hstar.zero w]
          ext x
          simp
      | succ n ih =>
          intro w
          let v : CellWord 0 n := fun k => w k.castSucc
          have hw : childWord v 0 = w := by
            ext k
            refine Fin.lastCases ?_ (fun j => ?_) k
            · simp [childWord]
            · simp [childWord, v]
          have h := hstar.refinement n v
          rw [ih v] at h
          have hc (j : Fin (2^0)) : childWord v j = w := by
            have hj : j = 0 := by
              apply Fin.ext
              have hj := j.isLt
              norm_num at hj
              omega
            simpa only [hj] using hw
          simp_rw [hc] at h
          ext x
          constructor
          · intro _
            exact Set.mem_univ x
          · intro hx
            rw [h] at hx
            obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
            exact hj
    let O : ∀ n, Fin (2^(0*n)) ≃ (Fin 0 → Fin (2^n)) := fun n =>
      Equiv.ofBijective (fun _ k => Fin.elim0 k) ⟨by
        intro i j _
        apply Fin.ext
        have hi := i.isLt
        have hj := j.isLt
        simp at hi hj
        omega, by
        intro a
        refine ⟨⟨0, by simp⟩, ?_⟩
        ext k
        exact Fin.elim0 k⟩
    refine ⟨O, ?_, ?_, ?_⟩
    · intro n
      ext S
      constructor
      · rintro ⟨i, rfl⟩
        refine ⟨fun _ => 0, ?_⟩
        rw [hcells]
        ext x
        simp [dyadicGridCube]
      · rintro ⟨w, rfl⟩
        refine ⟨⟨0, by simp⟩, ?_⟩
        rw [hcells]
        ext x
        simp [dyadicGridCube]
    · intro n i j hij r
      exact Fin.elim0 r
    · intro n i j hij
      have hi := i.isLt
      have hj := j.isLt
      simp at hi hj
      omega
/-- A set homeomorphic to the zero-dimensional unit cube [consists of exactly
one point](goal). -/
-- @node: zeroDim_chart_singleton
lemma zeroDim_chart_singleton {D : ℕ} {K : Set (L1Vec D)}
    (f : homeoClass (unitCube 0) K) : ∃ c : L1Vec D, K = {c} := by
  let z : unitCube 0 := ⟨0, fun j => Fin.elim0 j⟩
  refine ⟨(f z).val, ?_⟩
  ext x
  constructor
  · intro hx
    have hz : f.symm ⟨x, hx⟩ = z := Subsingleton.elim _ _
    have heq := congrArg (fun y : unitCube 0 => (f y).val) hz
    simpa only [f.apply_symm_apply, Set.mem_singleton_iff] using heq
  · intro hx
    have heq : x = (f z).val := Set.mem_singleton_iff.mp hx
    exact heq ▸ (f z).property

/-- If [a probability law assigns mass one to a single point](hyp:hc), then
[it is the Dirac law at that point](goal). -/
-- @node: probability_eq_dirac_of_singleton_mass
lemma probability_eq_dirac_of_singleton_mass {D : ℕ}
    (P : ProbabilityMeasure (L1Vec D)) (c : L1Vec D)
    (hc : (P : Measure (L1Vec D)) {c} = 1) :
    (P : Measure (L1Vec D)) = Measure.dirac c := by
  let : BorelSpace (L1Vec D) := ⟨rfl⟩
  have hae : (fun x : L1Vec D => x) =ᵐ[(P : Measure (L1Vec D))] (fun _ => c) := by
    filter_upwards [(mem_ae_iff_prob_eq_one (measurableSet_singleton c)).2 hc] with x hx
    exact Set.mem_singleton_iff.mp hx
  calc
    (P : Measure (L1Vec D)) = (P : Measure (L1Vec D)).map id := Measure.map_id.symm
    _ = (P : Measure (L1Vec D)).map (fun _ => c) := Measure.map_congr hae
    _ = Measure.dirac c := by simp

/-- For [an input dimension](hyp:din), [a width budget](hyp:W), [a depth
budget](hyp:L), and [an output vector](hyp:c), the [constant ReLU network](goal)
is the zero network with its output bias replaced by that vector. -/
-- @node: constantNet
noncomputable def constantNet (din W L : ℕ) {dout : ℕ} (c : L1Vec dout) :
    ReLUNet din dout W L :=
  { zeroNet din dout W L with outputBias := c.ofLp }

-- @node: constantNet_eval
/-- [The constant ReLU network returns its prescribed output vector at every
input, for any input dimension and width and depth budgets](goal). -/
lemma constantNet_eval (din W L : ℕ) {dout : ℕ} (c : L1Vec dout)
    (x : L1Vec din) : (constantNet din W L c).eval x = c := by
  apply PiLp.ext
  intro j
  simp [ReLUNet.eval, constantNet, zeroNet]

/-- [Every ReLU network with zero output dimension returns the zero vector
at every input](goal). -/
-- @node: zeroOutputNet_eval
lemma zeroOutputNet_eval (din W L : ℕ) (q : ReLUNet din 0 W L)
    (x : L1Vec din) : q.eval x = 0 := Subsingleton.elim _ _

/-- If a component has a chart from the zero-dimensional cube and [a
probability law assigns mass one to that component](hyp:hmass), then [for any
two width and depth budgets there are two ReLU blocks: the first maps the
one-dimensional unit cube into the zero-dimensional cube, the second maps that
cube into the component, and their composition sends every probability input
law to the component law exactly](goal). -/
-- @node: exists_zeroDim_component_blocks
lemma exists_zeroDim_component_blocks {D : ℕ}
    (mu : ProbabilityMeasure (L1Vec D)) {K : Set (L1Vec D)}
    (chart : homeoClass (unitCube 0) K)
    (hmass : (mu : Measure (L1Vec D)) K = 1)
    (W1 L1 W2 L2 : ℕ) :
    ∃ g1 : ReLUNet 1 0 W1 L1, ∃ g2 : ReLUNet 0 D W2 L2,
      Set.MapsTo g1.eval (unitCube 1) (unitCube 0) ∧
      Set.MapsTo g2.eval (unitCube 0) K ∧
      (∀ rho : ProbabilityMeasure (L1Vec 1),
        (rho : Measure (L1Vec 1)).map (g2.eval ∘ g1.eval) =
          (mu : Measure (L1Vec D))) := by
  obtain ⟨c, hK⟩ := zeroDim_chart_singleton chart
  have hc : (mu : Measure (L1Vec D)) {c} = 1 := by
    simpa only [hK] using hmass
  have hmu := probability_eq_dirac_of_singleton_mass mu c hc
  refine ⟨zeroNet 1 0 W1 L1, constantNet 0 W2 L2 c, ?_, ?_, ?_⟩
  · intro x hx j
    exact Fin.elim0 j
  · intro x hx
    rw [constantNet_eval, hK]
    exact Set.mem_singleton c
  · intro rho
    have heval : (constantNet 0 W2 L2 c).eval ∘ (zeroNet 1 0 W1 L1).eval =
        fun _ => c := by
      funext x
      exact constantNet_eval 0 W2 L2 c _
    rw [heval, hmu, Measure.map_const]
    simp

/-- For [a nonnegative chart Lipschitz bound](hyp:L), suppose [a probability
law satisfies the lower-bound domination condition on a set charted by the
zero-dimensional cube, with that Lipschitz bound](hyp:hdomination). Then
[there is a curve continuous on the closed unit interval, taking values in
the law's support there, that sends the uniform interval law to the given
probability law](goal). -/
-- @node: exists_measure_representing_curve_zeroDim
lemma exists_measure_representing_curve_zeroDim {D : ℕ}
    (P : ProbabilityMeasure (L1Vec D)) (K : Set (L1Vec D)) (L : ℝ≥0)
    (hdomination : LowerBoundDomination (d := 0) (P : Measure (L1Vec D)) K L) :
    ∃ gamma : ℝ → L1Vec D, ContinuousOn gamma (Set.Icc 0 1) ∧
      Set.MapsTo gamma (Set.Icc 0 1) (measureSupport (P : Measure (L1Vec D))) ∧
      curveLebesgue.map gamma = (P : Measure (L1Vec D)) := by
  obtain ⟨f, Cf, hf⟩ := hdomination
  obtain ⟨c, hK⟩ := zeroDim_chart_singleton f
  have hc : (P : Measure (L1Vec D)) {c} = 1 := by
    simpa only [hK] using hf.2.1
  have hP := probability_eq_dirac_of_singleton_mass P c hc
  refine ⟨fun _ => c, ?_, ?_, ?_⟩
  · fun_prop
  · intro t ht U hU hcU hzero
    have hle : (P : Measure (L1Vec D)) {c} ≤ (P : Measure (L1Vec D)) U :=
      measure_mono (Set.singleton_subset_iff.mpr hcU)
    rw [hc, hzero] at hle
    exact one_ne_zero (le_antisymm hle bot_le)
  · rw [hP, Measure.map_const]
    simp [curveLebesgue,
      Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection.uniformMeasure,
      Real.volume_Icc]

/-- For [a nonnegative chart Lipschitz bound](hyp:L), suppose [a probability
law satisfies the lower-bound domination condition on a set charted by the
one-dimensional cube, with that Lipschitz bound](hyp:hdomination). Then
[there is a continuous curve on the closed unit interval with values in the
law's support that sends the uniform interval law to the given law and has
a finite Hölder constant with exponent one](goal). -/
-- @node: exists_measure_representing_holder_curve_oneDim
lemma exists_measure_representing_holder_curve_oneDim {D : ℕ}
    (P : ProbabilityMeasure (L1Vec D)) (K : Set (L1Vec D)) (L : ℝ≥0)
    (hdomination : LowerBoundDomination (d := 1) (P : Measure _) K L) :
    ∃ gamma : ℝ → L1Vec D, ContinuousOn gamma (Set.Icc 0 1) ∧
      Set.MapsTo gamma (Set.Icc 0 1) (measureSupport (P : Measure _)) ∧
      curveLebesgue.map gamma = (P : Measure _) ∧
      (0 < (1 : ℕ) → ∃ A : ℝ≥0,
        HolderOnWith A (((1 : ℕ) : ℝ≥0)⁻¹) gamma (Set.Icc 0 1)) := by
  obtain ⟨gamma, A, hLip, hmem, hmap⟩ :=
    exists_oneDim_measure_representing_lipschitz_curve P K L hdomination
  refine ⟨gamma, hLip.continuousOn,
    continuous_representing_curve_mapsTo_support (P : Measure _) gamma
      hLip.continuousOn hmap, hmap, ?_⟩
  intro _
  refine ⟨A, ?_⟩
  simpa using hLip.holderOnWith

-- @node: prop:holder-curve
/-- For [a nonnegative chart Lipschitz bound](hyp:L), suppose [a probability
law satisfies lower-bound domination on a set charted by the unit cube with
that bound](hyp:hdomination), and [such a dominating chart can be chosen so
that, in positive dimension, the law pulled back to the cube gives its
boundary zero mass](hyp:hboundary). Then [there is a curve continuous on the
closed unit interval, taking values in the law's support and sending the
uniform interval law to that law; in positive dimension it is Hölder with
exponent the reciprocal of the cube dimension and some finite constant](goal). -/
lemma exists_measure_representing_holder_curve {D d : ℕ}
    (P : ProbabilityMeasure (L1Vec D)) (K : Set (L1Vec D))
    (L : ℝ≥0)
    (hdomination : LowerBoundDomination (d := d) (P : Measure (L1Vec D)) K L)
    (hboundary : PullbackVanishesOnBoundary (d := d) (P : Measure (L1Vec D)) K L) :
    ∃ gamma : ℝ → L1Vec D, ContinuousOn gamma (Set.Icc 0 1) ∧ -- @realizes \gamma(one continuous measure-representing curve, with the cube pullback as a specialization)
      Set.MapsTo gamma (Set.Icc 0 1) (measureSupport (P : Measure (L1Vec D))) ∧
      curveLebesgue.map gamma = (P : Measure (L1Vec D)) ∧
      (0 < d → ∃ A : ℝ≥0, HolderOnWith A ((d : ℝ≥0)⁻¹) gamma (Set.Icc 0 1)) := by
  by_cases hd : d = 0
  · subst d
    obtain ⟨gamma, hcontinuous, hsupport, hmap⟩ :=
      exists_measure_representing_curve_zeroDim P K L hdomination
    exact ⟨gamma, hcontinuous, hsupport, hmap, fun h => (Nat.lt_irrefl 0 h).elim⟩
  · by_cases hd1 : d = 1
    · subst d
      exact exists_measure_representing_holder_curve_oneDim P K L hdomination
    · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
      obtain ⟨chart, Cf, hdom⟩ := hdomination
      obtain ⟨zeta, A, hholder, hmem, hmap⟩ :=
        exists_component_pullback_holder_curve_ge_two (by omega) P chart L Cf hdom
      let gamma := chartForward chart ∘ zeta
      have hr : 0 < (d : ℝ≥0)⁻¹ := by positivity
      have hgamma : HolderOnWith (L * A) ((d : ℝ≥0)⁻¹) gamma (Set.Icc (0 : ℝ) 1) := by
        simpa only [NNReal.coe_one, NNReal.rpow_one, one_mul] using
          (chartForward_lipschitzOn chart L hdom.2.2.2.1).holderOnWith.comp hholder hmem
      have hpush : curveLebesgue.map gamma = (P : Measure _) := by
        have hzeta : AEMeasurable zeta curveLebesgue := by
          first | fun_prop | exact (hholder.continuousOn hr).aemeasurable measurableSet_Icc
        rw [show gamma = chartForward chart ∘ zeta from rfl,
          ← AEMeasurable.map_map_of_aemeasurable
            (chartForward_measurable chart).aemeasurable hzeta, hmap]
        exact chartForward_map_pullback P chart hdom.1 hdom.2.1
      exact ⟨gamma, hgamma.continuousOn hr,
        continuous_representing_curve_mapsTo_support (P : Measure _) gamma
          (hgamma.continuousOn hr) hpush, hpush, fun _ => ⟨L * A, hgamma⟩⟩

/-- For a probability law and a chart from the zero-dimensional cube to a
component, [there is a continuous curve on the closed unit interval with
values in that cube whose distribution under the uniform interval law equals
the probability law pulled back through the chart inverse](goal). -/
-- @node: exists_component_pullback_curve_zeroDim
lemma exists_component_pullback_curve_zeroDim {D : ℕ}
    (mu : ProbabilityMeasure (L1Vec D)) {K : Set (L1Vec D)}
    (chart : homeoClass (unitCube 0) K) :
    ∃ gamma : ℝ → L1Vec 0, ContinuousOn gamma (Set.Icc 0 1) ∧
      Set.MapsTo gamma (Set.Icc 0 1) (unitCube 0) ∧
      curveLebesgue.map gamma = (mu : Measure _).map (chartInverse chart) := by
  have hinverse : chartInverse chart = fun _ => (0 : L1Vec 0) := Subsingleton.elim _ _
  refine ⟨fun _ => 0, ?_, ?_, ?_⟩
  · fun_prop
  · intro t ht j
    exact Fin.elim0 j
  · rw [hinverse, Measure.map_const, Measure.map_const]
    simp [curveLebesgue,
      Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection.uniformMeasure,
      Real.volume_Icc]

/-- Suppose [the cube dimension is positive](hyp:hd). For [a nonnegative
chart Lipschitz bound](hyp:L), assume [the component is compact, carries the
whole probability law, and has a chart with that Lipschitz bound under which
the law dominates cube Lebesgue measure by the positive specified domination
constant](hyp:hdom). Then [there is a curve into the unit cube on the closed
unit interval, Hölder with exponent the reciprocal of the dimension and some
finite constant, whose distribution under the uniform interval law is the
component law pulled back through the chart inverse](goal). -/
-- @node: exists_component_pullback_holder_curve
lemma exists_component_pullback_holder_curve {D d : ℕ}
    (hd : 0 < d) (mu : ProbabilityMeasure (L1Vec D)) {K : Set (L1Vec D)}
    (chart : homeoClass (unitCube d) K) (L : ℝ≥0) (Cf : ℝ)
    (hdom : lowerBoundDominationAt (mu : Measure _) K chart L Cf) :
    ∃ gamma : ℝ → L1Vec d, ∃ A : ℝ≥0,
      HolderOnWith A ((d : ℝ≥0)⁻¹) gamma (Set.Icc (0 : ℝ) 1) ∧
      Set.MapsTo gamma (Set.Icc (0 : ℝ) 1) (unitCube d) ∧
      curveLebesgue.map gamma = (mu : Measure _).map (chartInverse chart) := by
  by_cases hd1 : d = 1
  · subst d
    obtain ⟨gamma, A, hLip, hmem, hmap⟩ :=
      exists_oneDim_component_pullback_curve mu chart L Cf hdom
    exact ⟨gamma, A, by simpa using hLip.holderOnWith, hmem, hmap⟩
  · exact exists_component_pullback_holder_curve_ge_two (by omega) mu chart L Cf hdom

/-- [Taking the sole coordinate of a uniformly distributed point in the
one-dimensional unit cube gives the uniform law on the closed unit
interval](goal). -/
-- @node: uniformCubeLaw_oneDimCoordinate
lemma uniformCubeLaw_oneDimCoordinate :
    (uniformCubeLaw 1).map oneDimCoordinate = curveLebesgue := by
  rw [uniformCubeLaw, Measure.map_map oneDimCoordinate_measurable (by fun_prop)]
  exact (measurePreserving_funUnique curveLebesgue (Fin 1)).map_eq

/-- For [a nonnegative Hölder constant](hyp:A) and [a nonnegative
exponent](hyp:r), suppose [the exponent is positive](hyp:hr), [a curve obeys
the corresponding Hölder bound on the closed unit interval](hyp:hholder),
and [its values there lie in the unit cube](hyp:hmem). Then [applying the
curve to the sole coordinate of a one-dimensional input gives a continuous
map between the unit cubes, preserves the curve's distribution under uniform
input, and bounds each output-coordinate difference by the Hölder constant
times the input one-norm distance raised to that exponent](goal). -/
-- @node: holder_curve_scalar_network_input
lemma holder_curve_scalar_network_input {d : ℕ}
    (gamma : ℝ → L1Vec d) (A r : ℝ≥0) (hr : 0 < r)
    (hholder : HolderOnWith A r gamma (Set.Icc (0 : ℝ) 1))
    (hmem : Set.MapsTo gamma (Set.Icc (0 : ℝ) 1) (unitCube d)) :
    ContinuousOn (gamma ∘ oneDimCoordinate) (unitCube 1) ∧
      Set.MapsTo (gamma ∘ oneDimCoordinate) (unitCube 1) (unitCube d) ∧
      (uniformCubeLaw 1).map (gamma ∘ oneDimCoordinate) = curveLebesgue.map gamma ∧
      ∀ x ∈ unitCube 1, ∀ y ∈ unitCube 1, ∀ j : Fin d,
        |((gamma ∘ oneDimCoordinate) x).ofLp j -
          ((gamma ∘ oneDimCoordinate) y).ofLp j| ≤
            (A : ℝ) * ‖x-y‖ ^ (r : ℝ) := by
  have hcoordinate : Continuous oneDimCoordinate := by
    unfold oneDimCoordinate
    fun_prop
  have hc : Set.MapsTo oneDimCoordinate (unitCube 1) (Set.Icc (0 : ℝ) 1) :=
    fun x hx => hx 0
  refine ⟨(hholder.continuousOn hr).comp hcoordinate.continuousOn hc,
    hmem.comp hc, ?_, ?_⟩
  · have hga : AEMeasurable gamma ((uniformCubeLaw 1).map oneDimCoordinate) := by
      rw [uniformCubeLaw_oneDimCoordinate]
      exact (hholder.continuousOn hr).aemeasurable measurableSet_Icc
    rw [← AEMeasurable.map_map_of_aemeasurable hga
      oneDimCoordinate_measurable.aemeasurable, uniformCubeLaw_oneDimCoordinate]
  · intro x hx y hy j
    calc
      _ = dist ((gamma (oneDimCoordinate x)).ofLp j)
          ((gamma (oneDimCoordinate y)).ofLp j) := (Real.dist_eq _ _).symm
      _ ≤ dist (gamma (oneDimCoordinate x)) (gamma (oneDimCoordinate y)) :=
        PiLp.dist_apply_le _ _ j
      _ ≤ (A : ℝ) * dist (oneDimCoordinate x) (oneDimCoordinate y) ^ (r : ℝ) :=
        hholder.dist_le (hc hx) (hc hy)
      _ ≤ (A : ℝ) * ‖x-y‖ ^ (r : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ A.coe_nonneg
        apply Real.rpow_le_rpow dist_nonneg _ r.coe_nonneg
        exact (PiLp.dist_apply_le x y 0).trans_eq (dist_eq_norm x y)

/-- Suppose [the component cube has positive dimension](hyp:hd). For [a
nonnegative chart Lipschitz bound](hyp:L), assume [the component is compact,
has probability one, and its chart has that Lipschitz bound and makes the
law dominate cube Lebesgue measure by the specified positive
constant](hyp:hdom). Then [there is a continuous map from the one-dimensional
unit cube into the component cube whose uniform-input law is the component
law pulled back through the chart inverse, and whose coordinate differences
are bounded by a common finite constant times the input one-norm distance
raised to the reciprocal of the component dimension](goal). -/
-- @node: exists_component_network_input_curve
lemma exists_component_network_input_curve {D d : ℕ}
    (hd : 0 < d) (mu : ProbabilityMeasure (L1Vec D)) {K : Set (L1Vec D)}
    (chart : homeoClass (unitCube d) K) (L : ℝ≥0) (Cf : ℝ)
    (hdom : lowerBoundDominationAt (mu : Measure _) K chart L Cf) :
    ∃ gamma : L1Vec 1 → L1Vec d, ∃ A : ℝ≥0,
      ContinuousOn gamma (unitCube 1) ∧
      Set.MapsTo gamma (unitCube 1) (unitCube d) ∧
      (uniformCubeLaw 1).map gamma = (mu : Measure _).map (chartInverse chart) ∧
      ∀ x ∈ unitCube 1, ∀ y ∈ unitCube 1, ∀ j : Fin d,
        |(gamma x).ofLp j - (gamma y).ofLp j| ≤
          (A : ℝ) * ‖x-y‖ ^ (1 / (d : ℝ)) := by
  obtain ⟨gamma, A, hholder, hmem, hmap⟩ :=
    exists_component_pullback_holder_curve hd mu chart L Cf hdom
  have hr : 0 < (d : ℝ≥0)⁻¹ := by positivity
  obtain ⟨hcont, hcube, hlaw, hmod⟩ :=
    holder_curve_scalar_network_input gamma A ((d : ℝ≥0)⁻¹) hr hholder hmem
  refine ⟨gamma ∘ oneDimCoordinate, A, hcont, hcube, hlaw.trans hmap, ?_⟩
  simpa only [NNReal.coe_inv, NNReal.coe_natCast, one_div] using hmod

/-- For [a nonnegative chart Lipschitz bound](hyp:L), suppose [a component is
compact, has probability one, and its chosen chart has that Lipschitz bound
and makes the law dominate cube Lebesgue measure by the specified positive
constant](hyp:hdom). If [in positive dimension the law pulled back through
that chart gives the cube boundary zero mass](hyp:hboundary), then [there
is a continuous curve on the closed unit interval with values in the
component cube that sends the uniform interval law to this pulled-back
law](goal). -/
-- @node: exists_component_pullback_curve
lemma exists_component_pullback_curve {D d : ℕ}
    (mu : ProbabilityMeasure (L1Vec D)) (K : Set (L1Vec D))
    (chart : homeoClass (unitCube d) K) (L : ℝ≥0) (Cf : ℝ)
    (hdom : lowerBoundDominationAt (mu : Measure _) K chart L Cf)
    (hboundary : 0 < d → ((mu : Measure _).map (chartInverse chart))
      (frontier (unitCube d)) = 0) :
    ∃ gamma : ℝ → L1Vec d, ContinuousOn gamma (Set.Icc 0 1) ∧
      Set.MapsTo gamma (Set.Icc 0 1) (unitCube d) ∧ -- @realizes \gamma_i(continuous curve from the unit interval into the component cube)
      curveLebesgue.map gamma = (mu : Measure _).map (chartInverse chart) := by -- @realizes \gamma_i(push-forward is the normalized component law pulled back through its chart)
  by_cases hd : d = 0
  · subst d
    exact exists_component_pullback_curve_zeroDim mu chart
  · obtain ⟨gamma, A, hholder, hmem, hmap⟩ :=
      exists_component_pullback_holder_curve (Nat.pos_of_ne_zero hd) mu chart L Cf hdom
    exact ⟨gamma, hholder.continuousOn (by positivity), hmem, hmap⟩
end Papers.TbsNeuralCausalPi

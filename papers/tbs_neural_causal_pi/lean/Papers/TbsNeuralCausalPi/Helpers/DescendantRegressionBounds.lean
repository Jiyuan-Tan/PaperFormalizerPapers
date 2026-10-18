module
public import Papers.TbsNeuralCausalPi.Helpers.DescendantHistoryTransport
public import Papers.TbsNeuralCausalPi.Helpers.DescendantRegressionVersion
public import Papers.TbsNeuralCausalPi.Helpers.DoseResponseMarginals
/-! # Bounds for the actual descendant regression on observational inputs

The covariates use only non-descendants and the treatment. Keeping their
coordinate costs separate from the outcome gives the constants in the
Wasserstein test-function argument without counting a coordinate twice.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory Filter
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.style.longLine false
set_option linter.unusedVariables false
variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
  {C : Fin b → Set (Fin n)}

/-- For [a scalar outcome Y](hyp:hY), [zeroing all observed coordinates outside
the non-descendants of treatment leaves the descendant simulation mean
unchanged at any fixed dose](goal). -/
-- @node: descendantMean_projection_eq
lemma descendantMean_projection_eq (M : CanonicalSCM kind dims dag G C)
    (T Y : Fin n) (hY : valueDim (kind Y) = 1) (v : Joint kind) (t : ℝ) :
    descendantMean M T Y hY (nonDescendantProjection (dag := dag) T v) t =
      descendantMean M T Y hY v t := by
  unfold descendantMean
  congr 1
  funext u
  congr 2
  funext i
  by_cases hi : i = T
  · simp only [hi, if_true]
  · simp only [hi, if_false]
    by_cases hs : i ∈ nonDescendantNodes (dag := dag) T
    · simp [hs, nonDescendantProjection]
    · simp [hs]

/-- Suppose [treatment is scalar](hyp:hT) and [outcome is scalar](hyp:hY), with
[a nonnegative constant L](hyp:L), [independent latent blocks](hyp:hind),
[no hidden confounding](hyp:hnoconf), [L-Lipschitz continuous mechanisms](hyp:hcont),
[L-Lipschitz categorical propensities](hyp:hprop), and [variables bounded at K](hyp:hbound).
For [an admissible observation v](hyp:hv) and [an admissible observation w](hyp:hw),
[the absolute difference of their descendant regression means is at most
the dose Lipschitz constant times the sum of coordinate distances over
treatment and its non-descendants](goal). -/
-- @node: descendant_regression_distance_le
lemma descendant_regression_distance_le
    (M : CanonicalSCM kind dims dag G C) (T Y : Fin n)
    (hT : valueDim (kind T) = 1) (hY : valueDim (kind Y) = 1)
    (K : ℝ) (L : ℝ≥0) (hind : LatentBlocksIndependent M.toEuclideanSCM)
    (hnoconf : NoHiddenConfounding G)
    (hcont : ContinuousMechanismsLipschitz M.toEuclideanSCM L)
    (hprop : CategoricalPropensityLipschitz M.toEuclideanSCM M.f L)
    (hbound : VariablesBoundedAt M.toEuclideanSCM K)
    (v w : Joint kind) (hv : admissibleJoint v) (hw : admissibleJoint w) :
    |descendantMean M T Y hY v (scalarOutcome T hT v) -
      descendantMean M T Y hY w (scalarOutcome T hT w)| ≤
      doseLip kind L * ∑ i ∈ insert T (nonDescendantNodes (dag := dag) T),
        ∑ j, dist (v.ofLp ⟨i,j⟩) (w.ofLp ⟨i,j⟩) := by
  let S := insert T (nonDescendantNodes (dag := dag) T)
  let x := fun i => WithLp.toLp 1 (fun j => v.ofLp ⟨i,j⟩)
  let y := fun i => WithLp.toLp 1 (fun j => w.ofLp ⟨i,j⟩)
  have hadm (a : Joint kind) (ha : admissibleJoint a) :
      AdmissibleIntervention kind (fun i => if i ∈ S then
        some (WithLp.toLp 1 (fun j => a.ofLp ⟨i,j⟩)) else none) := by
    intro i z hz
    by_cases hi : i ∈ S
    · exact ha i z (by simpa only [hi, if_true] using hz)
    · simp [hi] at hz
  have hencode (a : Joint kind) :
      (fun i => if i ∈ S then some (WithLp.toLp 1 (fun j => a.ofLp ⟨i,j⟩)) else none) =
      (fun i => if i = T then some (WithLp.toLp 1 (fun _ => scalarOutcome T hT a)) else
        if i ∈ nonDescendantNodes (dag := dag) T then
          some (WithLp.toLp 1 (fun j => a.ofLp ⟨i,j⟩)) else none) := by
    funext i
    by_cases hi : i = T
    · subst i
      simp only [S, Finset.mem_insert_self, if_true]
      congr 2
      funext j
      have hj : j = Fin.cast hT.symm ⟨0, Nat.zero_lt_succ 0⟩ := by
        apply Fin.ext
        have := j.isLt
        simp only [Fin.val_cast]
        omega
      rw [hj]
      rfl
    · simp [S, hi]
  have hxi := interventional_scalarOutcome_integrable M.toEuclideanSCM L hcont K hbound
    _ (hadm v hv) Y hY
  have hyi := interventional_scalarOutcome_integrable M.toEuclideanSCM L hcont K hbound
    _ (hadm w hw) Y hY
  have h := canonical_assignment_mean_transport M hnoconf hind L hcont hprop S x y
    (hadm v hv) (hadm w hw) (scalarOutcome Y hY) (scalarOutcome_lipschitz Y hY) hxi hyi
  have hpow : (historyExpansion kind L : ℝ)^n = doseLip kind L := by
    change (1 + (L : ℝ) * categoricalFactor kind)^n = ((L : ℝ) * categoricalFactor kind+1)^n
    congr 1
    ring
  dsimp only [x, y] at h
  rw [hencode, hencode, hpow] at h
  simpa only [PiLp.dist_eq_of_L1, descendantMean, S] using h

/-- If [treatment is scalar](hyp:hT) and [outcome is scalar](hyp:hY), with [a nonnegative
constant L](hyp:L), [independent latent blocks](hyp:hind), [no hidden confounding](hyp:hnoconf),
[L-Lipschitz continuous mechanisms](hyp:hcont), [L-Lipschitz categorical
propensities](hyp:hprop), and [variables bounded at K](hyp:hbound), then
[the descendant regression evaluated at each observation's treatment is
Lipschitz with the dose Lipschitz constant on the admissible coordinate box
bounded by K](goal). -/
-- @node: descendant_regression_lipschitzOn
lemma descendant_regression_lipschitzOn
    (M : CanonicalSCM kind dims dag G C) (T Y : Fin n)
    (hT : valueDim (kind T) = 1) (hY : valueDim (kind Y) = 1)
    (K : ℝ) (L : ℝ≥0) (hind : LatentBlocksIndependent M.toEuclideanSCM)
    (hnoconf : NoHiddenConfounding G)
    (hcont : ContinuousMechanismsLipschitz M.toEuclideanSCM L)
    (hprop : CategoricalPropensityLipschitz M.toEuclideanSCM M.f L)
    (hbound : VariablesBoundedAt M.toEuclideanSCM K) :
    LipschitzOnWith ⟨doseLip kind L, (by linarith [one_le_doseLip (kind := kind) L])⟩
      (fun v => descendantMean M T Y hY v (scalarOutcome T hT v))
      {v : Joint kind | (∀ j, |v.ofLp j| ≤ K) ∧ admissibleJoint v} := by
  apply LipschitzOnWith.of_dist_le_mul
  intro v hv w hw
  rw [Real.dist_eq]
  apply (descendant_regression_distance_le M T Y hT hY K L hind hnoconf hcont hprop hbound
    v w hv.2 hw.2).trans
  apply mul_le_mul_of_nonneg_left _ (by linarith [one_le_doseLip (kind := kind) L])
  rw [PiLp.dist_eq_of_L1, Fintype.sum_sigma]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun _ _ _ => Finset.sum_nonneg fun _ _ => dist_nonneg)

/-- If [treatment is scalar](hyp:hT) and [outcome is scalar](hyp:hY), with [a nonnegative
constant L](hyp:L), [independent latent blocks](hyp:hind), [no hidden confounding](hyp:hnoconf),
[L-Lipschitz continuous mechanisms](hyp:hcont), [L-Lipschitz categorical
propensities](hyp:hprop), and [variables bounded at K](hyp:hbound), then
[the descendant regression at the observed treatment has absolute value
at most K almost everywhere under the observational law](goal). -/
-- @node: descendant_regression_ae_abs_le
lemma descendant_regression_ae_abs_le
    (M : CanonicalSCM kind dims dag G C) (T Y : Fin n)
    (hT : valueDim (kind T) = 1) (hY : valueDim (kind Y) = 1)
    (K : ℝ) (L : ℝ≥0) (hind : LatentBlocksIndependent M.toEuclideanSCM)
    (hnoconf : NoHiddenConfounding G)
    (hcont : ContinuousMechanismsLipschitz M.toEuclideanSCM L)
    (hprop : CategoricalPropensityLipschitz M.toEuclideanSCM M.f L)
    (hbound : VariablesBoundedAt M.toEuclideanSCM K) :
    ∀ᵐ v ∂observationalLaw M.toEuclideanSCM,
      |descendantMean M T Y hY v (scalarOutcome T hT v)| ≤ K := by
  have hreg := descendantMean_regression_version M T Y hY hT K L hind hnoconf hcont hprop hbound
  have hy : ∀ᵐ v ∂observationalLaw M.toEuclideanSCM, |scalarOutcome Y hY v| ≤ K := by
    apply (ae_map_iff (evalSteps_measurable M.toEuclideanSCM _ _).aemeasurable
      (measurableSet_le ((scalarOutcome_lipschitz Y hY).continuous.measurable.abs) measurable_const)).2
    filter_upwards [hbound.2] with u hu
    exact hu.1 Y _
  have hc := ae_bdd_abs_condExp_of_ae_bdd_abs
    (m := MeasurableSpace.comap (fun v => (nonDescendantProjection (dag := dag) T v,
      scalarOutcome T hT v)) (borel _)) hy
  filter_upwards [hreg, hc] with v hv hb
  rw [descendantMean_projection_eq] at hv
  rw [hv]
  exact hb

/-- If [treatment is scalar](hyp:hT) and [outcome is scalar](hyp:hY), with [a nonnegative
constant L](hyp:L), [independent latent blocks](hyp:hind), [no hidden confounding](hyp:hnoconf),
[L-Lipschitz continuous mechanisms](hyp:hcont), [L-Lipschitz categorical
propensities](hyp:hprop), and [variables bounded at K](hyp:hbound), then
[at every admissible observation whose coordinates have absolute value at
most K, the descendant regression at its treatment has absolute value at
most K multiplied by the sum of one and twice the total coordinate dimension
times the dose Lipschitz constant](goal). -/
-- @node: descendant_regression_abs_le
lemma descendant_regression_abs_le
    (M : CanonicalSCM kind dims dag G C) (T Y : Fin n)
    (hT : valueDim (kind T) = 1) (hY : valueDim (kind Y) = 1)
    (K : ℝ) (L : ℝ≥0) (hind : LatentBlocksIndependent M.toEuclideanSCM)
    (hnoconf : NoHiddenConfounding G)
    (hcont : ContinuousMechanismsLipschitz M.toEuclideanSCM L)
    (hprop : CategoricalPropensityLipschitz M.toEuclideanSCM M.f L)
    (hbound : VariablesBoundedAt M.toEuclideanSCM K) :
    ∀ v : Joint kind, (∀ j, |v.ofLp j| ≤ K) → admissibleJoint v →
      |descendantMean M T Y hY v (scalarOutcome T hT v)| ≤
        K * (1 + 2 * (∑ i, valueDim (kind i)) * doseLip kind L) := by
  letI := M.toEuclideanSCM.probability
  haveI : IsProbabilityMeasure (observationalLaw M.toEuclideanSCM) :=
    Measure.isProbabilityMeasure_map (evalSteps_measurable M.toEuclideanSCM _ _).aemeasurable
  have hcarry : ∀ᵐ v ∂observationalLaw M.toEuclideanSCM,
      (∀ j, |v.ofLp j| ≤ K) ∧ admissibleJoint v :=
    (ae_mem_iff_measure_eq (admissibleJoint_box_isCompact (kind := kind) K).measurableSet.nullMeasurableSet).2
      (by simpa using observationalLaw_admissibleJoint_box M.toEuclideanSCM K hbound)
  obtain ⟨a, ha, hab⟩ := (hcarry.and
    (descendant_regression_ae_abs_le M T Y hT hY K L hind hnoconf hcont hprop hbound)).exists
  intro v hv hadm
  have hd : dist v a ≤ 2 * K * (∑ i, valueDim (kind i)) := by
    rw [PiLp.dist_eq_of_L1]
    calc
      _ ≤ ∑ _j : Σ i, Fin (valueDim (kind i)), 2 * K := by
        apply Finset.sum_le_sum
        intro j _
        rw [Real.dist_eq]
        exact (abs_sub _ _).trans (by linarith [hv j, ha.1 j])
      _ = _ := by simp [Fintype.card_sigma]; ring
  have hLip := descendant_regression_lipschitzOn M T Y hT hY K L hind hnoconf hcont hprop hbound
  have hdiff := hLip.dist_le_mul v ⟨hv, hadm⟩ a ha
  rw [Real.dist_eq] at hdiff
  have hL0 : 0 ≤ doseLip kind L := by linarith [one_le_doseLip (kind := kind) L]
  have := abs_add_le
    (descendantMean M T Y hY v (scalarOutcome T hT v) -
      descendantMean M T Y hY a (scalarOutcome T hT a))
    (descendantMean M T Y hY a (scalarOutcome T hT a))
  simp only [sub_add_cancel] at this
  calc
    _ ≤ doseLip kind L * dist v a + K := this.trans (add_le_add hdiff hab)
    _ ≤ doseLip kind L * (2 * K * (∑ i, valueDim (kind i))) + K :=
      add_le_add (mul_le_mul_of_nonneg_left hd hL0) le_rfl
    _ = _ := by ring

/-- If [Y is scalar](hyp:hY), [differs from treatment T](hyp:hne), and [is a
descendant of T](hyp:hpath), then [the sum of coordinate distances over
treatment and its non-descendants, plus the absolute outcome difference,
is at most the distance between the full observations](goal). -/
-- @node: descendant_covariate_outcome_cost_le
lemma descendant_covariate_outcome_cost_le (T Y : Fin n)
    (hY : valueDim (kind Y) = 1) (hne : Y ≠ T) (hpath : dag.isAncestor T Y)
    (v w : Joint kind) :
    (∑ i ∈ insert T (nonDescendantNodes (dag := dag) T),
      ∑ j, dist (v.ofLp ⟨i,j⟩) (w.ofLp ⟨i,j⟩)) +
      |scalarOutcome Y hY v - scalarOutcome Y hY w| ≤ dist v w := by
  let S := insert T (nonDescendantNodes (dag := dag) T)
  have hnot : Y ∉ S := by simp [S, nonDescendantNodes, hne, hpath]
  have hcoord : |scalarOutcome Y hY v - scalarOutcome Y hY w| ≤
      ∑ j, dist (v.ofLp ⟨Y,j⟩) (w.ofLp ⟨Y,j⟩) := by
    rw [← Real.dist_eq]
    exact Finset.single_le_sum (f := fun j => dist (v.ofLp ⟨Y,j⟩) (w.ofLp ⟨Y,j⟩))
      (fun _ _ => dist_nonneg) (Finset.mem_univ (Fin.cast hY.symm ⟨0, Nat.zero_lt_succ 0⟩))
  calc
    _ ≤ (∑ i ∈ S, ∑ j, dist (v.ofLp ⟨i,j⟩) (w.ofLp ⟨i,j⟩)) +
        ∑ j, dist (v.ofLp ⟨Y,j⟩) (w.ofLp ⟨Y,j⟩) := add_le_add le_rfl hcoord
    _ = ∑ i ∈ insert Y S, ∑ j, dist (v.ofLp ⟨i,j⟩) (w.ofLp ⟨i,j⟩) := by
      rw [Finset.sum_insert hnot, add_comm]
    _ ≤ dist v w := by
      rw [PiLp.dist_eq_of_L1, Fintype.sum_sigma]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => Finset.sum_nonneg fun _ _ => dist_nonneg)

/-- Suppose [treatment is scalar](hyp:hT) and [outcome is scalar](hyp:hY), [the outcome
differs from treatment](hyp:hne) and [is its descendant](hyp:hpath). For
[a nonnegative constant L](hyp:L), assume [independent latent blocks in
the original model](hyp:hind) and [independent latent blocks in the comparison model](hyp:hindhat),
[no hidden confounding](hyp:hnoconf), [L-Lipschitz continuous mechanisms in
the original model](hyp:hcont) and [L-Lipschitz continuous mechanisms in the comparison model](hyp:hconthat),
[L-Lipschitz categorical propensities in the original model](hyp:hprop) and
[L-Lipschitz categorical propensities in the comparison model](hyp:hprophat),
and [variables bounded at K in the original model](hyp:hbound) and
[variables bounded at K in the comparison model](hyp:hboundhat).
Then [the comparison-minus-original
regression gap multiplied by the outcome is Lipschitz on the admissible
K-box with constant 2 B times the maximum of Ly and one, where Ly is the
dose Lipschitz constant and B is K multiplied by the sum of one and twice
the total coordinate dimension times Ly](goal). -/
-- @node: descendant_regression_outcome_test_lipschitzOn
lemma descendant_regression_outcome_test_lipschitzOn
    (M Mhat : CanonicalSCM kind dims dag G C) (T Y : Fin n)
    (hT : valueDim (kind T) = 1) (hY : valueDim (kind Y) = 1)
    (hne : Y ≠ T) (hpath : dag.isAncestor T Y)
    (K : ℝ) (L : ℝ≥0) (hind : LatentBlocksIndependent M.toEuclideanSCM)
    (hindhat : LatentBlocksIndependent Mhat.toEuclideanSCM)
    (hnoconf : NoHiddenConfounding G)
    (hcont : ContinuousMechanismsLipschitz M.toEuclideanSCM L)
    (hconthat : ContinuousMechanismsLipschitz Mhat.toEuclideanSCM L)
    (hprop : CategoricalPropensityLipschitz M.toEuclideanSCM M.f L)
    (hprophat : CategoricalPropensityLipschitz Mhat.toEuclideanSCM Mhat.f L)
    (hbound : VariablesBoundedAt M.toEuclideanSCM K)
    (hboundhat : VariablesBoundedAt Mhat.toEuclideanSCM K) :
    let Ly : ℝ≥0 := ⟨doseLip kind L, by linarith [one_le_doseLip (kind := kind) L]⟩
    let B : ℝ≥0 := ⟨K * (1 + 2 * (∑ i, valueDim (kind i)) * doseLip kind L), by
      have := hbound.1
      have := one_le_doseLip (kind := kind) L
      positivity⟩
    LipschitzOnWith (2 * B * max Ly 1)
      (fun v => (descendantMean Mhat T Y hY v (scalarOutcome T hT v) -
        descendantMean M T Y hY v (scalarOutcome T hT v)) * scalarOutcome Y hY v)
      {v : Joint kind | (∀ j, |v.ofLp j| ≤ K) ∧ admissibleJoint v} := by
  dsimp only
  let Ly := doseLip kind L
  let B := K * (1 + 2 * (∑ i, valueDim (kind i)) * Ly)
  let f := fun v => descendantMean M T Y hY v (scalarOutcome T hT v)
  let fh := fun v => descendantMean Mhat T Y hY v (scalarOutcome T hT v)
  have hL0 : 0 ≤ Ly := by dsimp [Ly]; linarith [one_le_doseLip (kind := kind) L]
  have hK0 : 0 ≤ K := hbound.1.le
  have hKB : K ≤ B := by
    dsimp [B]
    nlinarith [mul_nonneg (by positivity : 0 ≤ 2 * (∑ i, valueDim (kind i)) * Ly) hbound.1.le]
  have hB0 : 0 ≤ B := hbound.1.le.trans hKB
  have hb (v : Joint kind) (hv : (∀ j, |v.ofLp j| ≤ K) ∧ admissibleJoint v) :
      |fh v - f v| ≤ 2 * B := by
    have hm := descendant_regression_abs_le M T Y hT hY K L hind hnoconf hcont hprop hbound v hv.1 hv.2
    have hh := descendant_regression_abs_le Mhat T Y hT hY K L hindhat hnoconf hconthat hprophat hboundhat v hv.1 hv.2
    exact (abs_sub _ _).trans (by dsimp [fh, f, B, Ly] at *; linarith)
  apply LipschitzOnWith.of_dist_le_mul
  intro v hv w hw
  let r := ∑ i ∈ insert T (nonDescendantNodes (dag := dag) T),
    ∑ j, dist (v.ofLp ⟨i,j⟩) (w.ofLp ⟨i,j⟩)
  let z := |scalarOutcome Y hY v - scalarOutcome Y hY w|
  have hr : 0 ≤ r := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => dist_nonneg
  have hz : 0 ≤ z := abs_nonneg _
  have hd : |(fh v - f v) - (fh w - f w)| ≤ 2 * Ly * r := by
    have hm := descendant_regression_distance_le M T Y hT hY K L hind hnoconf hcont hprop hbound v w hv.2 hw.2
    have hh := descendant_regression_distance_le Mhat T Y hT hY K L hindhat hnoconf hconthat hprophat hboundhat v w hv.2 hw.2
    have heq : (fh v - f v) - (fh w - f w) = (fh v - fh w) - (f v - f w) := by ring
    rw [heq]
    exact (abs_sub _ _).trans (by dsimp [fh, f, Ly, r] at *; linarith)
  have hy : |scalarOutcome Y hY w| ≤ K := hw.1 _
  have hsplit : (fh v - f v) * scalarOutcome Y hY v -
      (fh w - f w) * scalarOutcome Y hY w =
      (fh v - f v) * (scalarOutcome Y hY v - scalarOutcome Y hY w) +
        scalarOutcome Y hY w * ((fh v - f v) - (fh w - f w)) := by ring
  change dist ((fh v - f v) * scalarOutcome Y hY v)
    ((fh w - f w) * scalarOutcome Y hY w) ≤ _
  rw [Real.dist_eq, hsplit]
  calc
    _ ≤ |fh v - f v| * z + |scalarOutcome Y hY w| * |(fh v - f v) - (fh w - f w)| := by
      simpa only [abs_mul] using abs_add_le
        ((fh v - f v) * (scalarOutcome Y hY v - scalarOutcome Y hY w))
        (scalarOutcome Y hY w * ((fh v - f v) - (fh w - f w)))
    _ ≤ (2 * B) * z + K * (2 * Ly * r) := by
      gcongr
      exact hb v hv
    _ ≤ (2 * B) * z + B * (2 * Ly * r) := by gcongr
    _ = (2 * B) * (z + Ly * r) := by ring
    _ ≤ (2 * B) * (max Ly 1 * z + max Ly 1 * r) := by
      gcongr
      · exact le_mul_of_one_le_left hz (le_max_right _ _)
      · exact le_max_left _ _
    _ = (2 * B * max Ly 1) * (r + z) := by ring
    _ ≤ (2 * B * max Ly 1) * dist v w := by
      gcongr
      exact descendant_covariate_outcome_cost_le T Y hY hne hpath v w
    _ = _ := by rfl

/-- Suppose [treatment is scalar](hyp:hT) and [outcome is scalar](hyp:hY), [the outcome
differs from treatment](hyp:hne) and [is its descendant](hyp:hpath). For
[a nonnegative constant L](hyp:L), assume [independent latent blocks in the
original model](hyp:hind) and [independent latent blocks in the comparison model](hyp:hindhat), [no hidden
confounding](hyp:hnoconf), [L-Lipschitz continuous mechanisms in the original
model](hyp:hcont) and [L-Lipschitz continuous mechanisms in the comparison model](hyp:hconthat),
[L-Lipschitz categorical propensities in the original model](hyp:hprop) and
[L-Lipschitz categorical propensities in the comparison model](hyp:hprophat),
and [variables bounded at K in the original model](hyp:hbound) and
[variables bounded at K in the comparison model](hyp:hboundhat). Then
[the mean squared difference of their descendant regressions
under the original observational law is at most the dose comparison constant
for K and L times the Wasserstein distance between their observational laws](goal). -/
-- @node: descendant_regression_gap_le_wasserstein
lemma descendant_regression_gap_le_wasserstein
    (M Mhat : CanonicalSCM kind dims dag G C) (T Y : Fin n)
    (hT : valueDim (kind T) = 1) (hY : valueDim (kind Y) = 1)
    (hne : Y ≠ T) (hpath : dag.isAncestor T Y)
    (K : ℝ) (L : ℝ≥0) (hind : LatentBlocksIndependent M.toEuclideanSCM)
    (hindhat : LatentBlocksIndependent Mhat.toEuclideanSCM)
    (hnoconf : NoHiddenConfounding G)
    (hcont : ContinuousMechanismsLipschitz M.toEuclideanSCM L)
    (hconthat : ContinuousMechanismsLipschitz Mhat.toEuclideanSCM L)
    (hprop : CategoricalPropensityLipschitz M.toEuclideanSCM M.f L)
    (hprophat : CategoricalPropensityLipschitz Mhat.toEuclideanSCM Mhat.f L)
    (hbound : VariablesBoundedAt M.toEuclideanSCM K)
    (hboundhat : VariablesBoundedAt Mhat.toEuclideanSCM K) :
    (∫ v, (descendantMean M T Y hY v (scalarOutcome T hT v) -
      descendantMean Mhat T Y hY v (scalarOutcome T hT v))^2
        ∂observationalLaw M.toEuclideanSCM) ≤
      doseCW kind L ⟨K, hbound.1.le⟩ *
        (wasserstein1 (observationalLaw Mhat.toEuclideanSCM)
          (observationalLaw M.toEuclideanSCM)).toReal := by
  letI : BorelSpace (Joint kind) := ⟨rfl⟩
  letI := M.toEuclideanSCM.probability
  letI := Mhat.toEuclideanSCM.probability
  haveI : IsProbabilityMeasure (observationalLaw M.toEuclideanSCM) :=
    Measure.isProbabilityMeasure_map (evalSteps_measurable M.toEuclideanSCM _ _).aemeasurable
  haveI : IsProbabilityMeasure (observationalLaw Mhat.toEuclideanSCM) :=
    Measure.isProbabilityMeasure_map (evalSteps_measurable Mhat.toEuclideanSCM _ _).aemeasurable
  let nu : ProbabilityMeasure (Joint kind) := ⟨observationalLaw M.toEuclideanSCM, inferInstance⟩
  let mu : ProbabilityMeasure (Joint kind) := ⟨observationalLaw Mhat.toEuclideanSCM, inferInstance⟩
  let S := {v : Joint kind | (∀ j, |v.ofLp j| ≤ K) ∧ admissibleJoint v}
  have hS : IsCompact S := admissibleJoint_box_isCompact K
  have hnu : (nu : Measure (Joint kind)) S = 1 :=
    observationalLaw_admissibleJoint_box M.toEuclideanSCM K hbound
  have hmu : (mu : Measure (Joint kind)) S = 1 :=
    observationalLaw_admissibleJoint_box Mhat.toEuclideanSCM K hboundhat
  let Ly : ℝ≥0 := ⟨doseLip kind L, by linarith [one_le_doseLip (kind := kind) L]⟩
  let B : ℝ≥0 := ⟨K * (1 + 2 * (∑ i, valueDim (kind i)) * Ly), by
    have := hbound.1
    positivity⟩
  let f := fun v => descendantMean M T Y hY v (scalarOutcome T hT v)
  let fh := fun v => descendantMean Mhat T Y hY v (scalarOutcome T hT v)
  let d := fun v => fh v - f v
  let g := fun v => d v * scalarOutcome Y hY v
  let H := fun v => d v * fh v
  let F := fun v => d v * f v
  have hf : Measurable f := by dsimp [f]; fun_prop [scalarOutcome]
  have hfh : Measurable fh := by dsimp [fh]; fun_prop [scalarOutcome]
  have hfm := descendant_regression_lipschitzOn M T Y hT hY K L hind hnoconf hcont hprop hbound
  have hfhm := descendant_regression_lipschitzOn Mhat T Y hT hY K L hindhat hnoconf hconthat hprophat hboundhat
  have hb (v : Joint kind) (hv : v ∈ S) : |f v| ≤ B ∧ |fh v| ≤ B :=
    ⟨descendant_regression_abs_le M T Y hT hY K L hind hnoconf hcont hprop hbound v hv.1 hv.2,
      descendant_regression_abs_le Mhat T Y hT hY K L hindhat hnoconf hconthat hprophat hboundhat v hv.1 hv.2⟩
  have hd (v : Joint kind) (hv : v ∈ S) : |d v| ≤ 2 * B :=
    (abs_sub _ _).trans (by linarith [(hb v hv).1, (hb v hv).2])
  have hdLip : LipschitzOnWith (2 * Ly) d S := by
    simpa only [two_mul] using hfhm.sub hfm
  have hgLip : LipschitzOnWith (2 * B * max Ly 1) g S :=
    descendant_regression_outcome_test_lipschitzOn M Mhat T Y hT hY hne hpath K L
      hind hindhat hnoconf hcont hconthat hprop hprophat hbound hboundhat
  have hHLip : LipschitzOnWith (4 * Ly * B) H S := by
    apply LipschitzOnWith.of_dist_le_mul
    intro v hv w hw
    have hh : |fh v - fh w| ≤ Ly * dist v w := by
      simpa only [Real.dist_eq] using hfhm.dist_le_mul v hv w hw
    have hdd : |d v - d w| ≤ (2 * Ly) * dist v w := by
      simpa only [Real.dist_eq, NNReal.coe_mul, NNReal.coe_ofNat] using hdLip.dist_le_mul v hv w hw
    have heq : H v - H w = d v * (fh v - fh w) + fh w * (d v - d w) := by dsimp [H]; ring
    rw [Real.dist_eq, heq]
    calc
      _ ≤ |d v| * |fh v - fh w| + |fh w| * |d v - d w| := by
        simpa only [abs_mul] using abs_add_le (d v * (fh v - fh w)) (fh w * (d v - d w))
      _ ≤ (2 * B) * (Ly * dist v w) + B * ((2 * Ly) * dist v w) := by
        gcongr
        · exact hd v hv
        · exact (hb w hw).2
      _ = _ := by simp only [NNReal.coe_mul, NNReal.coe_ofNat]; ring
  have hi (rho : ProbabilityMeasure (Joint kind)) (hrho : (rho : Measure (Joint kind)) S = 1)
      (u : Joint kind → ℝ) (hu : Measurable u) (c : ℝ) (huB : ∀ v ∈ S, |u v| ≤ c) :
      Integrable u (rho : Measure (Joint kind)) := by
    apply Integrable.of_bound hu.aestronglyMeasurable c
    have hcarry := (ae_mem_iff_measure_eq hS.measurableSet.nullMeasurableSet).2
      (show (rho : Measure (Joint kind)) S = (rho : Measure (Joint kind)) Set.univ by simpa using hrho)
    filter_upwards [hcarry] with v hv
    simpa only [Real.norm_eq_abs] using huB v hv
  have hiY (rho : ProbabilityMeasure (Joint kind)) (hrho : (rho : Measure (Joint kind)) S = 1) :
      Integrable (scalarOutcome Y hY) (rho : Measure (Joint kind)) :=
    hi rho hrho _ (by fun_prop [scalarOutcome]) K (fun v hv => hv.1 _)
  have hig (rho : ProbabilityMeasure (Joint kind)) (hrho : (rho : Measure (Joint kind)) S = 1) :
      Integrable g (rho : Measure (Joint kind)) :=
    integrable_of_lipschitzOn_compact_carrying (rho : Measure (Joint kind)) S hS hrho g _ hgLip
  have hiH : Integrable H (nu : Measure (Joint kind)) :=
    integrable_of_lipschitzOn_compact_carrying (nu : Measure (Joint kind)) S hS hnu H _ hHLip
  have hiF : Integrable F (nu : Measure (Joint kind)) := by
    apply hi nu hnu F (by dsimp [F, d]; fun_prop) (2 * B * B)
    intro v hv
    dsimp only [F]
    rw [abs_mul]
    exact mul_le_mul (hd v hv) (hb v hv).1 (abs_nonneg _) (by positivity)
  let s : Joint kind → Joint kind × ℝ := fun v =>
    (nonDescendantProjection (dag := dag) T v, scalarOutcome T hT v)
  let a : Joint kind × ℝ → ℝ := fun z =>
    descendantMean Mhat T Y hY z.1 z.2 - descendantMean M T Y hY z.1 z.2
  have hs : Measurable s := by dsimp [s]; fun_prop [scalarOutcome]
  have ha : Measurable a := by dsimp [a]; fun_prop
  have hreg := descendantMean_regression_version M T Y hY hT K L hind hnoconf hcont hprop hbound
  have hregh := descendantMean_regression_version Mhat T Y hY hT K L hindhat hnoconf hconthat hprophat hboundhat
  rw [← (inferInstance : BorelSpace (Joint kind × ℝ)).measurable_eq] at hreg hregh
  have hgm : (∫ v, g v ∂(mu : Measure (Joint kind))) = ∫ v, H v ∂(mu : Measure (Joint kind)) := by
    have h := regression_weighted_outcome_integral (mu : Measure (Joint kind)) s (scalarOutcome Y hY) hs
      a (fun z => descendantMean Mhat T Y hY z.1 z.2) ha (hiY mu hmu)
      (by simpa only [a, s, descendantMean_projection_eq] using hig mu hmu) hregh
    simpa only [a, s, descendantMean_projection_eq] using h
  have hgn : (∫ v, g v ∂(nu : Measure (Joint kind))) = ∫ v, F v ∂(nu : Measure (Joint kind)) := by
    have h := regression_weighted_outcome_integral (nu : Measure (Joint kind)) s (scalarOutcome Y hY) hs
      a (fun z => descendantMean M T Y hY z.1 z.2) ha (hiY nu hnu)
      (by simpa only [a, s, descendantMean_projection_eq] using hig nu hnu) hreg
    simpa only [a, s, descendantMean_projection_eq] using h
  have hgc := regression_compact_support_contrast_le mu nu S hS hmu hnu g _ hgLip
  have hhc := regression_compact_support_contrast_le mu nu S hS hmu hnu (fun v => -H v) _ hHLip.neg
  simp only [integral_neg] at hhc
  rw [hgm, hgn] at hgc
  have hsquare : (∫ v, (f v - fh v)^2 ∂(nu : Measure (Joint kind))) =
      (∫ v, H v ∂(nu : Measure (Joint kind))) - ∫ v, F v ∂(nu : Measure (Joint kind)) := by
    rw [← integral_sub hiH hiF]
    apply integral_congr_ae
    exact Eventually.of_forall (fun v => by dsimp [H, F, d]; ring)
  change (∫ v, (f v - fh v)^2 ∂(nu : Measure (Joint kind))) ≤ _
  rw [hsquare]
  have hc : doseCW kind L ⟨K, hbound.1.le⟩ = (4 * Ly * B + 2 * B * max Ly 1 : ℝ≥0) := by
    rfl
  rw [hc]
  change (∫ v, H v ∂(nu : Measure (Joint kind))) - (∫ v, F v ∂(nu : Measure (Joint kind))) ≤
    ((4 * Ly * B + 2 * B * max Ly 1 : ℝ≥0) : ℝ) *
      (wasserstein1 (mu : Measure (Joint kind)) (nu : Measure (Joint kind))).toReal
  simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_ofNat] at hgc hhc ⊢
  linarith only [hgc, hhc]

/-- For [a scalar outcome Y](hyp:hY), if [two observations agree in every
coordinate of every non-descendant of treatment](hyp:h), then [their
descendant simulation means agree at any common fixed dose](goal). -/
-- @node: descendantMean_eq_of_covariates_eq
lemma descendantMean_eq_of_covariates_eq (M : CanonicalSCM kind dims dag G C)
    (T Y : Fin n) (hY : valueDim (kind Y) = 1) (v w : Joint kind) (t : ℝ)
    (h : ∀ i ∈ nonDescendantNodes (dag := dag) T, ∀ j, v.ofLp ⟨i,j⟩ = w.ofLp ⟨i,j⟩) :
    descendantMean M T Y hY v t = descendantMean M T Y hY w t := by
  unfold descendantMean
  congr 1
  funext u
  congr 2
  funext i
  by_cases hi : i = T
  · simp [hi]
  · simp only [hi, if_false]
    by_cases hs : i ∈ nonDescendantNodes (dag := dag) T
    · simp only [hs, if_true]
      congr 2
      funext j
      exact h i hs j
    · simp [hs]

/-- Suppose [treatment is scalar](hyp:hT) and [outcome is scalar](hyp:hY), with
[a nonnegative constant L](hyp:L), [independent latent blocks](hyp:hind),
[no hidden confounding](hyp:hnoconf), [L-Lipschitz continuous mechanisms](hyp:hcont),
[L-Lipschitz categorical propensities](hyp:hprop), and [variables bounded
at K](hyp:hbound). At [an admissible intervention dose t](hyp:ht), [the
descendant mean as a function of the non-descendant covariates is Lipschitz
with the dose Lipschitz constant on the projection of the admissible K-box](goal). -/
-- @node: descendantMean_section_lipschitzOn
lemma descendantMean_section_lipschitzOn
    (M : CanonicalSCM kind dims dag G C) (T Y : Fin n)
    (hT : valueDim (kind T) = 1) (hY : valueDim (kind Y) = 1)
    (K : ℝ) (L : ℝ≥0) (hind : LatentBlocksIndependent M.toEuclideanSCM)
    (hnoconf : NoHiddenConfounding G)
    (hcont : ContinuousMechanismsLipschitz M.toEuclideanSCM L)
    (hprop : CategoricalPropensityLipschitz M.toEuclideanSCM M.f L)
    (hbound : VariablesBoundedAt M.toEuclideanSCM K)
    (t : ℝ) (ht : AdmissibleIntervention kind (singleIntervention T t)) :
    LipschitzOnWith ⟨doseLip kind L, by linarith [one_le_doseLip (kind := kind) L]⟩
      (fun a => descendantMean M T Y hY a t)
      ((nonDescendantProjection (dag := dag) T) ''
        {v : Joint kind | (∀ j, |v.ofLp j| ≤ K) ∧ admissibleJoint v}) := by
  apply LipschitzOnWith.of_dist_le_mul
  rintro a ⟨v, hv, rfl⟩ a' ⟨w, hw, rfl⟩
  let z : Joint kind := WithLp.toLp 1 (fun ⟨i,j⟩ =>
    if i ∈ nonDescendantNodes (dag := dag) T then v.ofLp ⟨i,j⟩ else w.ofLp ⟨i,j⟩)
  have hz : admissibleJoint z := by
    intro i x hx
    by_cases hi : i ∈ nonDescendantNodes (dag := dag) T
    · exact hv.2 i x (by simpa [z, hi] using hx)
    · exact hw.2 i x (by simpa [z, hi] using hx)
  have hmean : descendantMean M T Y hY z t = descendantMean M T Y hY v t := by
    apply descendantMean_eq_of_covariates_eq
    intro i hi j
    simp [z, hi]
  have hdist : dist z w = dist (nonDescendantProjection (dag := dag) T v)
      (nonDescendantProjection (dag := dag) T w) := by
    simp only [PiLp.dist_eq_of_L1]
    apply Finset.sum_congr rfl
    rintro ⟨i,j⟩ _
    dsimp [z, nonDescendantProjection]
    by_cases hi : i ∈ nonDescendantNodes (dag := dag) T <;> simp [hi]
  have h := descendantMean_lipschitz M T Y hT hY K L hind hnoconf hcont hprop hbound
    z w hz hw.2 t t ht ht
  rw [hmean, hdist] at h
  rw [Real.dist_eq, descendantMean_projection_eq, descendantMean_projection_eq]
  simp only [sub_self, abs_zero, add_zero] at h
  exact h

end
end Papers.TbsNeuralCausalPi

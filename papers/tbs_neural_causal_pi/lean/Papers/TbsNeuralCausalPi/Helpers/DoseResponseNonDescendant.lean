module
public import Papers.TbsNeuralCausalPi.Helpers.DoseResponseRegression
/-! # The non-descendant case of the dose-response comparison

Interventions leave an ancestor-closed set of untreated coordinates unchanged.
For an outcome in this set, weak transport duality bounds the constant response gap.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
open scoped ENNReal NNReal
noncomputable section
variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}

/-- If [a set of nodes contains every parent of each of its members](hyp:hS)
and [two interventions assign the same values on that set](hyp:ht), then
[at every evaluation stage, the two interventions produce identical coordinates
on that set for the same latent realization](goal). -/
-- @node: evalSteps_eq_on_parent_closed
lemma evalSteps_eq_on_parent_closed (M : EuclideanSCM kind dims)
    (S : Set (Fin n)) (hS : ∀ i ∈ S, ∀ p ∈ M.dag.parents i, p ∈ S)
    (t t' : Intervention kind) (ht : ∀ i ∈ S, t i = t' i)
    (u : Exogenous kind dims) (r : ℕ) :
    ∀ i ∈ S, ∀ j, (evalSteps M t u r).ofLp ⟨i,j⟩ =
      (evalSteps M t' u r).ofLp ⟨i,j⟩ := by
  induction r with
  | zero => intro i hi j; rfl
  | succ r ih =>
    intro i hi j
    have hx : structuralInput M i (evalSteps M t u r) u =
        structuralInput M i (evalSteps M t' u r) u := by
      unfold structuralInput
      congr 1
      funext c
      rcases c with ⟨p,j⟩ | ⟨k,j⟩
      · exact ih p.val (hS i hi p.val p.property) j
      · rfl
    have hn : nodeValue M i (evalSteps M t u r) u =
        nodeValue M i (evalSteps M t' u r) u := by
      unfold nodeValue
      rw [hx]
    simp only [evalSteps, WithLp.ofLp_toLp]
    split_ifs
    · rw [ht i hi, hn]
    · exact ih i hi j

/-- If [the outcome differs from the treatment](hyp:hne) and [there is no
directed path from the treatment to the outcome](hyp:hpath), then [every outcome
coordinate under a treatment intervention equals its value without intervention,
for the same latent realization](goal). -/
-- @node: intervenedEval_eq_of_nonDescendant
lemma intervenedEval_eq_of_nonDescendant (M : EuclideanSCM kind dims)
    (T Y : Fin n) (hne : Y ≠ T) (hpath : ¬ M.dag.isAncestor T Y)
    (t : ℝ) (u : Exogenous kind dims) (j : Fin (valueDim (kind Y))) :
    (intervenedEval M (singleIntervention T t) u).ofLp ⟨Y,j⟩ =
      (intervenedEval M (fun _ => none) u).ofLp ⟨Y,j⟩ := by
  let S : Set (Fin n) := {i | i ≠ T ∧ ¬ M.dag.isAncestor T i}
  have hS : ∀ i ∈ S, ∀ p ∈ M.dag.parents i, p ∈ S := by
    intro i hi p hp
    have he := M.dag.mem_parents.mp hp
    refine ⟨?_, ?_⟩
    · intro hpT
      subst p
      exact hi.2 (.edge he)
    · intro hpi
      exact hi.2 (.trans hpi he)
  exact evalSteps_eq_on_parent_closed M S hS (singleIntervention T t) (fun _ => none)
    (fun i hi => by simp [singleIntervention, hi.1]) u (n*n+n) Y ⟨hne,hpath⟩ j

/-- If [the outcome is scalar](hyp:hY), [differs from the treatment](hyp:hne),
and [is not reachable by a directed path from the treatment](hyp:hpath), then
[its mean under any treatment dose equals its observational mean](goal). -/
-- @node: meanOutcome_eq_observational_of_nonDescendant
lemma meanOutcome_eq_observational_of_nonDescendant (M : EuclideanSCM kind dims)
    (T Y : Fin n) (hY : valueDim (kind Y) = 1)
    (hne : Y ≠ T) (hpath : ¬ M.dag.isAncestor T Y) (t : ℝ) :
    meanOutcome M T Y hY t = ∫ v, scalarOutcome Y hY v ∂observationalLaw M := by
  have hm : Measurable (scalarOutcome Y hY : Joint kind → ℝ) := by
    fun_prop [scalarOutcome]
  rw [observationalLaw, interventionalLaw, integral_map (by fun_prop) hm.aestronglyMeasurable]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u =>
    intervenedEval_eq_of_nonDescendant M T Y hne hpath t u _

/-- If [the outcome has one numerical coordinate](hyp:hY), then [extracting
that outcome from the joint observation is one-Lipschitz for the sum of absolute
coordinate differences](goal). -/
-- @node: scalarOutcome_lipschitz
lemma scalarOutcome_lipschitz (Y : Fin n) (hY : valueDim (kind Y) = 1) :
    LipschitzWith 1 (scalarOutcome Y hY : Joint kind → ℝ) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  simp only [NNReal.coe_one, one_mul, scalarOutcome, Real.dist_eq, PiLp.dist_eq_of_L1]
  exact Finset.single_le_sum (fun c _ => abs_nonneg (v.ofLp c - w.ofLp c)) (Finset.mem_univ _)

/-- If [the model's variables are bounded in absolute value by K](hyp:hb),
then [its observational law assigns probability one to the joint observations
whose numerical coordinates all have absolute value at most K](goal). -/
-- @node: observationalLaw_bounded_coordinates
lemma observationalLaw_bounded_coordinates (M : EuclideanSCM kind dims)
    (K : ℝ) (hb : VariablesBoundedAt M K) :
    (observationalLaw M) {v | ∀ c, |v.ofLp c| ≤ K} = 1 := by
  letI := M.probability
  have hm : Measurable (intervenedEval M (fun _ => none)) := by
    first | fun_prop | exact evalSteps_measurable M _ _
  have hS : MeasurableSet {v : Joint kind | ∀ c, |v.ofLp c| ≤ K} := by
    have : {v : Joint kind | ∀ c, |v.ofLp c| ≤ K} =
        ⋂ c, {v : Joint kind | |v.ofLp c| ≤ K} := by ext v; simp
    rw [this]
    exact MeasurableSet.iInter fun c => measurableSet_le (by fun_prop) measurable_const
  change (M.latentLaw.map (intervenedEval M (fun _ => none))) _ = 1
  rw [Measure.map_apply hm hS]
  have he : ∀ᵐ u ∂M.latentLaw,
      intervenedEval M (fun _ => none) u ∈ {v : Joint kind | ∀ c, |v.ofLp c| ≤ K} := by
    filter_upwards [hb.2] with u hu
    rintro ⟨i,j⟩
    exact hu.1 i j
  simpa using (ae_mem_iff_measure_eq (hS.preimage hm).nullMeasurableSet).1 he

/-- [The set of joint observations with every numerical coordinate bounded
in absolute value by K is compact](goal). -/
-- @node: joint_coordinate_box_isCompact
lemma joint_coordinate_box_isCompact (K : ℝ) :
    IsCompact {v : Joint kind | ∀ c, |v.ofLp c| ≤ K} := by
  have hc := (isCompact_univ_pi
    (fun _ : Σ i, Fin (valueDim (kind i)) => isCompact_Icc (a := -K) (b := K))).image
      (PiLp.continuous_toLp 1 _)
  convert hc using 1
  ext v
  simp only [Set.mem_setOf_eq, abs_le, Set.mem_image]
  constructor
  · intro hv
    exact ⟨v.ofLp, by simpa only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc] using hv, WithLp.toLp_ofLp 1 v⟩
  · rintro ⟨x,hx,rfl⟩
    simpa only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc] using hx

/-- If [the outcome is scalar](hyp:hY), [the first model's variables are bounded
by K](hyp:hb), and [the second model's variables are bounded by K](hyp:hbh), then
[the absolute difference between the observational outcome means is at most
the Wasserstein distance of order one between the observational laws](goal). -/
-- @node: observational_outcome_mean_gap_le
lemma observational_outcome_mean_gap_le (M Mhat : EuclideanSCM kind dims)
    (Y : Fin n) (hY : valueDim (kind Y) = 1) (K : ℝ)
    (hb : VariablesBoundedAt M K) (hbh : VariablesBoundedAt Mhat K) :
    |(∫ v, scalarOutcome Y hY v ∂observationalLaw M) -
      ∫ v, scalarOutcome Y hY v ∂observationalLaw Mhat| ≤
      (wasserstein1 (observationalLaw Mhat) (observationalLaw M)).toReal := by
  letI : BorelSpace (Joint kind) := ⟨rfl⟩
  letI := M.probability
  letI := Mhat.probability
  haveI : IsProbabilityMeasure (observationalLaw M) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  haveI : IsProbabilityMeasure (observationalLaw Mhat) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  let mu : ProbabilityMeasure (Joint kind) := ⟨observationalLaw Mhat, inferInstance⟩
  let nu : ProbabilityMeasure (Joint kind) := ⟨observationalLaw M, inferInstance⟩
  have hc := joint_coordinate_box_isCompact (kind := kind) K
  have hm := observationalLaw_bounded_coordinates M K hb
  have hh := observationalLaw_bounded_coordinates Mhat K hbh
  have hpos := regression_compact_support_contrast_le mu nu _ hc hh hm
    (scalarOutcome Y hY) 1 (scalarOutcome_lipschitz Y hY).lipschitzOnWith
  have hneg := regression_compact_support_contrast_le mu nu _ hc hh hm
    (fun v => -scalarOutcome Y hY v) 1 (scalarOutcome_lipschitz Y hY).neg.lipschitzOnWith
  simp only [integral_neg, NNReal.coe_one, one_mul] at hpos hneg
  dsimp [mu, nu] at hpos hneg
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- For [any nonnegative mechanism regularity constant L](hyp:L), [the
propagated dose Lipschitz coefficient is at least one](goal). -/
-- @node: one_le_doseLip
lemma one_le_doseLip (L : ℝ≥0) : 1 ≤ doseLip kind L := by
  have hD : 0 ≤ categoricalFactor kind := (by norm_num : (0 : ℝ) ≤ 1).trans
    (le_max_left _ _)
  unfold doseLip
  exact one_le_pow₀ (by nlinarith [mul_nonneg L.coe_nonneg hD])

/-- For [a nonnegative mechanism regularity constant L](hyp:L) and [a
nonnegative variable bound K](hyp:K), [the transport coefficient in the
dose-response bound is nonnegative](goal). -/
-- @node: doseCW_nonneg
lemma doseCW_nonneg (L K : ℝ≥0) : 0 ≤ doseCW kind L K := by
  have hL := (by norm_num : (0 : ℝ) ≤ 1).trans (one_le_doseLip (kind := kind) L)
  unfold doseCW
  positivity

/-- If [the outcome is scalar](hyp:hY), [differs from the treatment](hyp:hne),
and [is not a descendant of the treatment](hyp:hpath), while [the first model's
variables are bounded by K](hyp:hb) and [the second model's variables are bounded
by K](hyp:hbh), then [the squared dose-response difference integrated over the
closed dose interval under the reference probability law is at most the squared
observational Wasserstein distance of order one times the reference probability
of that interval](goal). -/
-- @node: nonDescendant_dose_response_gap_le
lemma nonDescendant_dose_response_gap_le
    {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
    {C : Fin b → Set (Fin n)} (M Mhat : CanonicalSCM kind dims dag G C)
    (K : ℝ) (T Y : Fin n) (hY : valueDim (kind Y) = 1)
    (hne : Y ≠ T) (hpath : ¬ dag.isAncestor T Y)
    (hb : VariablesBoundedAt M.toEuclideanSCM K)
    (hbh : VariablesBoundedAt Mhat.toEuclideanSCM K)
    (P : ProbabilityMeasure ℝ) (t1 t2 : ℝ) :
    (∫ t in Set.Icc t1 t2,
      (meanOutcome M.toEuclideanSCM T Y hY t -
        meanOutcome Mhat.toEuclideanSCM T Y hY t)^2 ∂(P : Measure ℝ)) ≤
      (wasserstein1 (observationalLaw Mhat.toEuclideanSCM)
        (observationalLaw M.toEuclideanSCM)).toReal^2 *
        ((P : Measure ℝ) (Set.Icc t1 t2)).toReal := by
  have hg := observational_outcome_mean_gap_le M.toEuclideanSCM Mhat.toEuclideanSCM Y hY K hb hbh
  have hs := (sq_le_sq₀ (abs_nonneg _) ENNReal.toReal_nonneg).2 hg
  rw [sq_abs] at hs
  simp_rw [meanOutcome_eq_observational_of_nonDescendant
    M.toEuclideanSCM T Y hY hne hpath,
    meanOutcome_eq_observational_of_nonDescendant Mhat.toEuclideanSCM T Y hY hne hpath]
  simpa [integral_const, smul_eq_mul, mul_comm, ProbabilityMeasure.coeFn_def, ENNReal.toReal] using
    mul_le_mul_of_nonneg_left hs
      (show 0 ≤ ((P : Measure ℝ).restrict (Set.Icc t1 t2)).real Set.univ from measureReal_nonneg)

/-- If [the intervention assigns the vector v to a node](hyp:hv) and [the
evaluation stage is after that node's position in the topological order](hyp:hr),
then [each coordinate of that node at this stage equals the corresponding
coordinate of v](goal). -/
-- @node: evalSteps_assigned_coordinate
lemma evalSteps_assigned_coordinate (M : EuclideanSCM kind dims)
    (t : Intervention kind) (u : Exogenous kind dims) (i : Fin n)
    (v : L1Vec (valueDim (kind i))) (hv : t i = some v)
    (r : ℕ) (hr : M.dag.topoOrder i < r) (j : Fin (valueDim (kind i))) :
    (evalSteps M t u r).ofLp ⟨i,j⟩ = v.ofLp j := by
  induction r with
  | zero => omega
  | succ r ih =>
    by_cases hi : M.dag.topoOrder i = r
    · simp only [evalSteps, WithLp.ofLp_toLp, hi, if_true, hv, Option.getD_some]
    · simpa only [evalSteps, WithLp.ofLp_toLp, hi, if_false] using ih (by omega)

/-- If [the evaluation stage is after a node's position in the topological
order](hyp:hr), then [each coordinate of that node equals its value immediately
after the node was evaluated](goal). -/
-- @node: evalSteps_coordinate_after_visit
lemma evalSteps_coordinate_after_visit (M : EuclideanSCM kind dims)
    (t : Intervention kind) (u : Exogenous kind dims) (i : Fin n)
    (r : ℕ) (hr : M.dag.topoOrder i < r) (j : Fin (valueDim (kind i))) :
    (evalSteps M t u r).ofLp ⟨i,j⟩ =
      (evalSteps M t u (M.dag.topoOrder i + 1)).ofLp ⟨i,j⟩ := by
  induction r with
  | zero => omega
  | succ r ih =>
    by_cases hi : M.dag.topoOrder i = r
    · rw [hi]
    · simpa only [evalSteps, WithLp.ofLp_toLp, hi, if_false] using ih (by omega)

/-- If [the evaluation stage is after a node's position in the topological
order](hyp:hr), then [each coordinate of that node already equals its value in
the completed intervention evaluation](goal). -/
-- @node: evalSteps_coordinate_eq_intervenedEval
lemma evalSteps_coordinate_eq_intervenedEval (M : EuclideanSCM kind dims)
    (t : Intervention kind) (u : Exogenous kind dims) (i : Fin n)
    (r : ℕ) (hr : M.dag.topoOrder i < r) (j : Fin (valueDim (kind i))) :
    (evalSteps M t u r).ofLp ⟨i,j⟩ = (intervenedEval M t u).ofLp ⟨i,j⟩ := by
  exact (evalSteps_coordinate_after_visit M t u i r hr j).trans
    (evalSteps_coordinate_after_visit M t u i (n*n+n)
      (scm_topoOrder_lt_horizon M i) j).symm

/-- If [at each node a modified intervention either keeps the original
assignment or assigns that node its value in the completed original evaluation
for the given latent realization](hyp:ht), then [the modified and original
interventions produce the same joint vector at every evaluation stage](goal). -/
-- @node: evalSteps_eq_of_factual_assignments
lemma evalSteps_eq_of_factual_assignments (M : EuclideanSCM kind dims)
    (t t' : Intervention kind) (u : Exogenous kind dims)
    (ht : ∀ i, t' i = t i ∨ t' i = some
      (WithLp.toLp 1 (fun j => (intervenedEval M t u).ofLp ⟨i,j⟩))) (r : ℕ) :
    evalSteps M t' u r = evalSteps M t u r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    apply WithLp.ofLp_injective
    funext ⟨i,j⟩
    simp only [evalSteps, WithLp.ofLp_toLp, ih]
    by_cases hi : M.dag.topoOrder i = r
    · simp only [hi, if_true]
      rcases ht i with h | h
      · rw [h]
      · rw [h, Option.getD_some, WithLp.ofLp_toLp]
        have he := evalSteps_coordinate_eq_intervenedEval M t u i (r+1) (by omega) j
        simpa only [evalSteps, WithLp.ofLp_toLp, hi, if_true] using he.symm
    · simp only [hi, if_false]

/-- If [at each node a modified intervention either keeps the original
assignment or assigns that node its value in the completed original evaluation
for the given latent realization](hyp:ht), then [the completed evaluations of
the two interventions are identical](goal). -/
-- @node: intervenedEval_eq_of_factual_assignments
lemma intervenedEval_eq_of_factual_assignments (M : EuclideanSCM kind dims)
    (t t' : Intervention kind) (u : Exogenous kind dims)
    (ht : ∀ i, t' i = t i ∨ t' i = some
      (WithLp.toLp 1 (fun j => (intervenedEval M t u).ofLp ⟨i,j⟩))) :
    intervenedEval M t' u = intervenedEval M t u :=
  evalSteps_eq_of_factual_assignments M t t' u ht (n*n+n)

/-- If two latent realizations agree, at every node left unassigned by the
intervention, on [all coordinates of its incident latent blocks](hyp:hblocks)
and [its categorical noise](hyp:hnoise), then [they produce identical joint
vectors at every stage of intervention evaluation](goal). -/
-- @node: evalSteps_eq_of_unassigned_noise_eq
lemma evalSteps_eq_of_unassigned_noise_eq (M : EuclideanSCM kind dims)
    (t : Intervention kind) (u u' : Exogenous kind dims)
    (hblocks : ∀ i, t i = none → ∀ k ∈ M.incidence i, ∀ j,
      u.ofLp (.inl ⟨k,j⟩) = u'.ofLp (.inl ⟨k,j⟩))
    (hnoise : ∀ i, t i = none → categoricalNoise i u = categoricalNoise i u') (r : ℕ) :
    evalSteps M t u r = evalSteps M t u' r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    apply WithLp.ofLp_injective
    funext ⟨i,j⟩
    by_cases hi : M.dag.topoOrder i = r
    · cases ht : t i with
      | none =>
        have hx : structuralInput M i (evalSteps M t u r) u =
            structuralInput M i (evalSteps M t u' r) u' := by
          apply WithLp.ofLp_injective
          funext c
          rcases c with ⟨p,k⟩ | ⟨k,l⟩
          · simp only [structuralInput, WithLp.ofLp_toLp, ih]
          · exact hblocks i ht k.val k.property l
        have hn : nodeValue M i (evalSteps M t u r) u =
            nodeValue M i (evalSteps M t u' r) u' := by
          unfold nodeValue
          rw [hx, hnoise i ht]
        simp only [evalSteps, WithLp.ofLp_toLp, hi, if_true, ht, Option.getD_none, hn]
      | some v =>
        simp only [evalSteps, WithLp.ofLp_toLp, hi, if_true, ht, Option.getD_some]
    · simp only [evalSteps, WithLp.ofLp_toLp, hi, if_false, ih]

/-- If two latent realizations agree, at every strict descendant of the
treatment other than the treatment itself, on [all coordinates of its incident
latent blocks](hyp:hblocks) and [its categorical noise](hyp:hnoise), then
[assigning the treatment its chosen dose and fixing its non-descendants to the
given covariate vector produces identical completed evaluations for the two
latent realizations](goal). -/
-- @node: descendantEval_eq_of_private_noise_eq
lemma descendantEval_eq_of_private_noise_eq
    {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
    {C : Fin b → Set (Fin n)} (M : CanonicalSCM kind dims dag G C)
    (T : Fin n) (a : Joint kind) (t : ℝ) (u u' : Exogenous kind dims)
    (hblocks : ∀ i, i ≠ T → dag.isAncestor T i →
      ∀ k ∈ canonicalIncidence C i, ∀ j,
        u.ofLp (.inl ⟨k,j⟩) = u'.ofLp (.inl ⟨k,j⟩))
    (hnoise : ∀ i, i ≠ T → dag.isAncestor T i →
      categoricalNoise i u = categoricalNoise i u') :
    let assignment : Intervention kind := fun i =>
      if i = T then some (WithLp.toLp 1 (fun _ => t)) else
        if i ∈ nonDescendantNodes (dag := dag) T then
          some (WithLp.toLp 1 (fun j => a.ofLp ⟨i,j⟩)) else none
    intervenedEval M.toEuclideanSCM assignment u =
      intervenedEval M.toEuclideanSCM assignment u' := by
  intro assignment
  have hfree (i : Fin n) (hi : assignment i = none) :
      i ≠ T ∧ dag.isAncestor T i := by
    have hiT : i ≠ T := by
      intro heq
      subst i
      simp [assignment] at hi
    refine ⟨hiT, ?_⟩
    by_contra hpath
    have hs : i ∈ nonDescendantNodes (dag := dag) T := by
      simp [nonDescendantNodes, hiT, hpath]
    simp [assignment, hiT, hs] at hi
  apply evalSteps_eq_of_unassigned_noise_eq
  · intro i hi
    exact hblocks i (hfree i hi).1 (hfree i hi).2
  · intro i hi
    exact hnoise i (hfree i hi).1 (hfree i hi).2

/-- [For any dose and latent realization, assigning that dose to the treatment
and fixing its non-descendants to their observational values produces the same
joint vector as intervening on the treatment alone](goal). -/
-- @node: descendantEval_eq_singleIntervention
lemma descendantEval_eq_singleIntervention
    {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
    {C : Fin b → Set (Fin n)} (M : CanonicalSCM kind dims dag G C)
    (T : Fin n) (t : ℝ) (u : Exogenous kind dims) :
    intervenedEval M.toEuclideanSCM
      (fun i => if i = T then some (WithLp.toLp 1 (fun _ => t)) else
        if i ∈ nonDescendantNodes (dag := dag) T then
          some (WithLp.toLp 1 (fun j =>
            (nonDescendantProjection (dag := dag) T
              (intervenedEval M.toEuclideanSCM (fun _ => none) u)).ofLp ⟨i,j⟩))
        else none) u =
      intervenedEval M.toEuclideanSCM (singleIntervention T t) u := by
  apply intervenedEval_eq_of_factual_assignments
  intro i
  by_cases hi : i = T
  · left
    simp [hi, singleIntervention]
  · by_cases hs : i ∈ nonDescendantNodes (dag := dag) T
    · right
      simp only [hi, if_false, hs, if_true, Option.some.injEq]
      apply WithLp.ofLp_injective
      funext j
      simp only [WithLp.ofLp_toLp, nonDescendantProjection, hs, if_true]
      have hmem : i ≠ T ∧ ¬ dag.isAncestor T i := by
        simpa only [nonDescendantNodes, Finset.mem_filter, Finset.mem_univ,
          true_and] using hs
      exact (intervenedEval_eq_of_nonDescendant M.toEuclideanSCM T i
        hmem.1 hmem.2 t u j).symm
    · left
      simp [hi, hs, singleIntervention]

/-- If [the treatment is scalar](hyp:hT), then [assigning it its realized
observational value and fixing its non-descendants to their observational
values reproduces the entire observational vector for the same latent
realization](goal). -/
-- @node: descendantEval_eq_observational
lemma descendantEval_eq_observational
    {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
    {C : Fin b → Set (Fin n)} (M : CanonicalSCM kind dims dag G C)
    (T : Fin n) (hT : valueDim (kind T) = 1) (u : Exogenous kind dims) :
    let v := intervenedEval M.toEuclideanSCM (fun _ => none) u
    intervenedEval M.toEuclideanSCM
      (fun i => if i = T then some (WithLp.toLp 1 (fun _ => scalarOutcome T hT v)) else
        if i ∈ nonDescendantNodes (dag := dag) T then
          some (WithLp.toLp 1 (fun j =>
            (nonDescendantProjection (dag := dag) T v).ofLp ⟨i,j⟩)) else none) u = v := by
  dsimp only
  apply intervenedEval_eq_of_factual_assignments
  intro i
  by_cases hi : i = T
  · subst i
    right
    simp only [if_true, Option.some.injEq]
    apply WithLp.ofLp_injective
    funext j
    simp only [WithLp.ofLp_toLp, scalarOutcome]
    have hj : Fin.cast hT.symm ⟨0, Nat.zero_lt_succ 0⟩ = j := by
      apply Fin.ext
      simp only [Fin.val_cast]
      have := j.isLt
      omega
    rw [hj]
  · by_cases hs : i ∈ nonDescendantNodes (dag := dag) T
    · right
      simp only [hi, if_false, hs, if_true, nonDescendantProjection, WithLp.ofLp_toLp]
    · left
      simp [hi, hs]

/-- If [the treatment is scalar](hyp:hT), then [its own mean response to an
intervention assigning dose t equals t](goal). -/
-- @node: meanOutcome_self_intervention
lemma meanOutcome_self_intervention (M : EuclideanSCM kind dims)
    (T : Fin n) (hT : valueDim (kind T) = 1) (t : ℝ) :
    meanOutcome M T T hT t = t := by
  letI := M.probability
  have he (u : Exogenous kind dims) :
      scalarOutcome T hT (intervenedEval M (singleIntervention T t) u) = t := by
    exact evalSteps_assigned_coordinate M (singleIntervention T t) u T
      (WithLp.toLp 1 (fun _ => t)) (by simp [singleIntervention]) (n*n+n)
      (scm_topoOrder_lt_horizon M T) _
  simp only [meanOutcome, he, integral_const, probReal_univ, one_smul]

end
end Papers.TbsNeuralCausalPi

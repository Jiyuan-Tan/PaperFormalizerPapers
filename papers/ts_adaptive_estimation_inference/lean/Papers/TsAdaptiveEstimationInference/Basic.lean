module
public import Causalean.Stat.Sample
public import Causalean.Stat.Concentration.Covering.EmpiricalPseudoMetric
public import Causalean.Estimation.NPIV.Operator.Complexification
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2
public import Mathlib.MeasureTheory.Function.FactorsThrough
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Data.Finset.Sort
/-! Population and sampling conventions for adaptive inverse problems. -/
@[expose] public section
set_option linter.style.longLine false

namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

/-- A general closed-subspace population problem. No solution or range condition is part of this data. -/
-- @node: def:spaces
structure IVWorld (𝒲 𝒳 𝒵 : Type*) [MeasurableSpace 𝒲]
    [MeasurableSpace 𝒳] [MeasurableSpace 𝒵] where
  law : Measure 𝒲 -- @realizes W(population law on the observation domain)
  probability : IsProbabilityMeasure law
  xOf : 𝒲 → 𝒳 -- @realizes X(measurable observation input)
  zOf : 𝒲 → 𝒵 -- @realizes Z(measurable observation input)
  measurable_x : Measurable xOf -- @realizes X(measurability)
  measurable_z : Measurable zOf -- @realizes Z(measurability)
  Hbar : ClosedSubmodule ℝ (Lp ℝ 2 law) -- @realizes \tilde{\mathcal H}(closed L2 subspace)
  Qbar : ClosedSubmodule ℝ (Lp ℝ 2 law) -- @realizes \tilde{\mathcal Q}(closed L2 subspace)
  Hmeas : Hbar.toSubmodule ≤ lpMeas ℝ ℝ (.comap xOf inferInstance) 2 law
    -- @realizes \tilde{\mathcal H}(functions of X)
  Qmeas : Qbar.toSubmodule ≤ lpMeas ℝ ℝ (.comap zOf inferInstance) 2 law
    -- @realizes \tilde{\mathcal Q}(functions of Z)
  -- The supplied functions are the empirical problem's data. The explicit owner
  -- envelope is checked on this SAME family, never inferred from L2 coherence.
  -- A spiked a.e.-equal family that breaks the envelope is a different problem
  -- outside that hypothesis; no optimizer or empirical supremum is transported.
  primalRealization : Hbar.toSubmodule → 𝒳 → ℝ -- @realizes \mathcal H(supplied primal function representatives)
  dualRealization : Qbar.toSubmodule → 𝒵 → ℝ -- @realizes \mathcal F(supplied critic function representatives)
  primal_measurable : ∀ h, Measurable (primalRealization h)
  dual_measurable : ∀ q, Measurable (dualRealization q)
  primal_coherent : ∀ h, (fun w => primalRealization h (xOf w)) =ᵐ[law]
    ((h : Lp ℝ 2 law) : 𝒲 → ℝ)
  dual_coherent : ∀ q, (fun w => dualRealization q (zOf w)) =ᵐ[law]
    ((q : Lp ℝ 2 law) : 𝒲 → ℝ)
  H : Set Hbar.toSubmodule -- @realizes \mathcal H(hypothesis class in the primal subspace)
  Q : Set Qbar.toSubmodule -- @realizes \mathcal Q(dual hypothesis class)
  F : Set Qbar.toSubmodule -- @realizes \mathcal F(adversarial test class)
  S : Set Hbar.toSubmodule -- @realizes \mathcal S(dual test class)
  m : Qbar.toSubmodule →ₗ[ℝ] (𝒲 → ℝ) -- @realizes m(linear moment map)
  mt : Hbar.toSubmodule →ₗ[ℝ] (𝒲 → ℝ) -- @realizes \tilde m(linear target map)
  measurable_m : ∀ q, Measurable (m q)
  measurable_mt : ∀ h, Measurable (mt h)
  integrable_m : ∀ q, Integrable (m q) law
  integrable_mt : ∀ h, Integrable (mt h) law
  momentFunctional : StrongDual ℝ Qbar.toSubmodule
  targetFunctional : Hbar.toSubmodule →ₗ[ℝ] ℝ
  momentFunctional_eq : ∀ q, momentFunctional q = ∫ w, m q w ∂law
  targetFunctional_eq : ∀ h, targetFunctional h = ∫ w, mt h w ∂law
  Y : 𝒲 → ℝ -- @realizes Y(real outcome)
  measurable_Y : Measurable Y

attribute [instance] IVWorld.probability

-- @env: S1
variable {𝒲 𝒳 𝒵 : Type*} [MeasurableSpace 𝒲]
  [MeasurableSpace 𝒳] [MeasurableSpace 𝒵] (V : IVWorld 𝒲 𝒳 𝒵)

/-- For [the population problem](hyp:V), [the primal Hilbert subspace is complete](goal). -/
noncomputable instance primalComplete : CompleteSpace V.Hbar.toSubmodule :=
  V.Hbar.isClosed.completeSpace_coe

/-- For [the population problem](hyp:V), [the dual Hilbert subspace is complete](goal). -/
noncomputable instance dualComplete : CompleteSpace V.Qbar.toSubmodule :=
  V.Qbar.isClosed.completeSpace_coe

/-- The [canonical observation](goal) associated with [an observation value](hyp:w) is that value itself. -/
def observation (w : 𝒲) : 𝒲 := w -- @realizes W(canonical observation)

-- @node: primal_version_exists
/-- For [a primal Hilbert-space element](hyp:h), [there exists a measurable function of the covariates that agrees almost everywhere with that element under the population law](goal). -/
lemma primal_version_exists (h : V.Hbar.toSubmodule) :
    ∃ f : 𝒳 → ℝ, Measurable f ∧ (fun w => f (V.xOf w)) =ᵐ[V.law]
      ((h : Lp ℝ 2 V.law) : 𝒲 → ℝ) := by
  exact ⟨V.primalRealization h, V.primal_measurable h, V.primal_coherent h⟩

-- @node: dual_version_exists
/-- For a dual Hilbert-space element, [there exists a measurable function of the instruments that agrees almost everywhere with that element under the population law](goal). -/
lemma dual_version_exists (q : V.Qbar.toSubmodule) :
    ∃ f : 𝒵 → ℝ, Measurable f ∧ (fun w => f (V.zOf w)) =ᵐ[V.law]
      ((q : Lp ℝ 2 V.law) : 𝒲 → ℝ) := by
  exact ⟨V.dualRealization q, V.dual_measurable q, V.dual_coherent q⟩

/-- For [the population problem](hyp:V) and [a primal Hilbert-space element](hyp:h), [its covariate version](goal) is the measurable covariate function supplied by the problem, which represents that element almost everywhere. -/
def primalVersion (h : V.Hbar.toSubmodule) : 𝒳 → ℝ := V.primalRealization h

/-- For [the population problem](hyp:V) and [a dual Hilbert-space element](hyp:q), [its instrument version](goal) is the measurable instrument function supplied by the problem, which represents that element almost everywhere. -/
def dualVersion (q : V.Qbar.toSubmodule) : 𝒵 → ℝ := V.dualRealization q

/-- [The algorithm's initial function](goal) assigns zero to every input. -/
def algorithmicZero {A : Type*} : A → ℝ := 0

/-- [The measurable covariate function representing the zero element of the primal square-integrable function space is zero with probability one under the population observation law](goal). -/
lemma primalVersion_zero_ae :
    (fun w => primalVersion V 0 (V.xOf w)) =ᵐ[V.law] (algorithmicZero : 𝒲 → ℝ) := by
  exact (V.primal_coherent 0).trans (Lp.coeFn_zero ℝ 2 V.law)

/-- [The measurable instrument function representing the zero element of the dual square-integrable function space is zero with probability one under the population observation law](goal). -/
lemma dualVersion_zero_ae :
    (fun w => dualVersion V 0 (V.zOf w)) =ᵐ[V.law] (algorithmicZero : 𝒲 → ℝ) := by
  exact (V.dual_coherent 0).trans (Lp.coeFn_zero ℝ 2 V.law)

-- @node: def:operator
/-- For [the population problem](hyp:V), [the projected conditional-expectation operator](goal) takes a primal element's conditional expectation given the instruments and projects it orthogonally onto the dual subspace. -/
noncomputable def projCondExpOp : V.Hbar.toSubmodule →L[ℝ] V.Qbar.toSubmodule :=
  V.Qbar.toSubmodule.orthogonalProjectionOnto.comp
    ((lpMeas ℝ ℝ (.comap V.zOf inferInstance) 2 V.law).subtypeL.comp
      ((condExpL2 ℝ ℝ V.measurable_z.comap_le).comp V.Hbar.toSubmodule.subtypeL))
  -- @realizes \mathcal T(projected conditional expectation)

-- @node: def:adjoint
/-- For [the population problem](hyp:V), [the adjoint operator](goal) is the Hilbert-space adjoint of the projected conditional-expectation operator, mapping the dual subspace to the primal subspace. -/
noncomputable def adjointOp : V.Qbar.toSubmodule →L[ℝ] V.Hbar.toSubmodule := (projCondExpOp V).adjoint
  -- @realizes \mathcal T^*(Hilbert adjoint)

-- @node: def:riesz-moment
/-- For [the population problem](hyp:V), [the moment representer](goal) is the unique dual Hilbert-space element whose inner product with any dual element equals that element's expected moment. -/
noncomputable def momentRepresenter : V.Qbar.toSubmodule :=
  (InnerProductSpace.toDual ℝ V.Qbar.toSubmodule).symm V.momentFunctional
  -- @realizes r_0(Riesz representer of the moment expectation)

-- @node: ass:range
/-- For [the population problem](hyp:V), [the range condition](goal) requires that some primal element is mapped to the moment representer by the projected conditional-expectation operator. -/
def RangeCondition : Prop := ∃ h : V.Hbar.toSubmodule, projCondExpOp V h = momentRepresenter V
  -- @realizes \mathcal R(\mathcal T)(membership of the moment representer in the operator range)

/-- Given [a continuous linear operator](hyp:T), [a target element](hyp:r), and [a candidate solution](hyp:h), [the minimum-norm solution property](goal) requires that [the operator maps the candidate to the target](step:1) and [the candidate's norm is no larger than that of any other solution](step:2). -/
def IsMinNormSolution {H Q : Type*} [NormedAddCommGroup H] [NormedAddCommGroup Q]
    [NormedSpace ℝ H] [NormedSpace ℝ Q] (T : H →L[ℝ] Q) (r : Q) (h : H) : Prop :=
  T h = r ∧ ∀ u, T u = r → ‖h‖ ≤ ‖u‖

/-- For [a continuous linear operator](hyp:T) and [a target element](hyp:r), [the minimum-norm inverse value](goal) is a chosen minimum-norm solution when one exists, and zero otherwise. -/
noncomputable def minimumNormInverse {H Q : Type*} [NormedAddCommGroup H]
    [NormedAddCommGroup Q] [NormedSpace ℝ H] [NormedSpace ℝ Q]
    (T : H →L[ℝ] Q) (r : Q) : H :=
  @dite _ (∃ h, IsMinNormSolution T r h) (Classical.propDecidable _)
    (fun e => e.choose) (fun _ => 0)

-- @node: def:lin-inv-prob
/-- For [the population problem](hyp:V), [the selected primal solution](goal) is a chosen minimum-norm solution of the projected conditional-expectation equation with the moment representer as target, or zero if no minimum-norm solution exists. -/
noncomputable def minNormSolution : V.Hbar.toSubmodule :=
  minimumNormInverse (projCondExpOp V) (momentRepresenter V)
  -- @realizes h_0(minimum-norm solution when the range condition holds)

-- @node: minNormSolution_spec
/-- If [the moment representer belongs to the range of the projected conditional-expectation operator](hyp:hRange), then [the selected primal solution solves that equation and has norm no larger than any other solution](goal). -/
lemma minNormSolution_spec (hRange : RangeCondition V) :
    IsMinNormSolution (projCondExpOp V) (momentRepresenter V) (minNormSolution V) := by
  classical
  obtain ⟨h, hh⟩ := hRange
  let K := (projCondExpOp V).ker
  have : CompleteSpace K := (projCondExpOp V).isClosed_ker.completeSpace_coe
  have hex : ∃ v, IsMinNormSolution (projCondExpOp V) (momentRepresenter V) v := by
    refine ⟨h - K.starProjection h, ?_, ?_⟩
    · have hk : projCondExpOp V (K.starProjection h) = 0 :=
        K.starProjection_apply_mem h
      rw [map_sub, hk, sub_zero, hh]
    · intro u hu
      have hdiff : h - u ∈ K := by
        change projCondExpOp V (h - u) = 0
        rw [map_sub, hh, hu, sub_self]
      have hproj : Kᗮ.starProjection (h - u) = 0 := by
        apply LinearMap.mem_ker.mp
        rw [Submodule.ker_starProjection]
        exact K.le_orthogonal_orthogonal hdiff
      have heq : Kᗮ.starProjection h = Kᗮ.starProjection u :=
        sub_eq_zero.mp (by simpa only [map_sub] using hproj)
      rw [← K.starProjection_orthogonal_val, heq]
      exact Kᗮ.norm_starProjection_apply_le u
  unfold minNormSolution minimumNormInverse
  rw [dif_pos hex]
  exact hex.choose_spec

/-- For [the population problem](hyp:V), [the normal operator on the primal subspace](goal) applies the projected conditional-expectation operator followed by its adjoint. -/
noncomputable def normalOp : V.Hbar.toSubmodule →L[ℝ] V.Hbar.toSubmodule :=
  (adjointOp V).comp (projCondExpOp V) -- @realizes \mathcal A(T* T)

/-- For [the population problem](hyp:V), [the ambient normal operator](goal) projects a population square-integrable function onto the primal subspace, applies the normal operator, and regards the result as a population square-integrable function. -/
noncomputable def ambientNormalOp : Lp ℝ 2 V.law →L[ℝ] Lp ℝ 2 V.law :=
  V.Hbar.toSubmodule.subtypeL.comp
    ((normalOp V).comp V.Hbar.toSubmodule.orthogonalProjectionOnto)

/-- For [the population problem](hyp:V) and [a real-valued spectral function](hyp:f), [the spectral operator on the primal subspace](goal) applies that function to the ambient normal operator through the real continuous functional calculus, then projects the result onto the primal subspace. -/
noncomputable def spectralOp (f : ℝ → ℝ) : V.Hbar.toSubmodule →L[ℝ] V.Hbar.toSubmodule :=
  V.Hbar.toSubmodule.orthogonalProjectionOnto.comp
    ((Causalean.Estimation.NPIV.Complexification.realCFC (ambientNormalOp V) f).comp
      V.Hbar.toSubmodule.subtypeL)

-- @node: ass:source-condition
/-- For [the population problem](hyp:V), [a source exponent](hyp:β), and [a primal source element](hyp:w₀), [the source condition](goal) requires [a positive exponent](step:1) and [that the selected solution is the source element transformed by the spectral function taking the nonnegative part to half that exponent](step:2). -/
def BetaSourceCondition (β : ℝ) (w₀ : V.Hbar.toSubmodule) : Prop :=
  0 < β ∧ minNormSolution V = spectralOp V (fun x => (max x 0) ^ (β / 2)) w₀
  -- @realizes \beta(positive source exponent)
  -- @realizes w_0(chosen source witness without a norm restriction)

-- @node: ass:closeness-deepiv
/-- For [the population problem](hyp:V), [the hypothesis-class membership condition](goal) requires that the selected minimum-norm solution belongs to the primal hypothesis class. -/
def H0MemHypothesisClass : Prop := minNormSolution V ∈ V.H

-- @env: S2
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)

/-- For [the population problem](hyp:V) and [a measure on the sampling space](hyp:P), [an analysis sample](goal) is an infinite sequence of independent, identically distributed observations on that space, each with the population law. -/
abbrev AnalysisSample := Causalean.Stat.IIDSample Ω 𝒲 P V.law

/-- For [the population problem](hyp:V), [the sampling measure](hyp:P), and [an independent, identically distributed analysis sample](hyp:sample), [the sample zero event](goal) is the complement of a measurable hull of the outcomes where some observation has a nonzero supplied primal or dual zero-coordinate version. -/
noncomputable def sampleZeroEvent (sample : AnalysisSample V P) : Set Ω :=
  (toMeasurable P {ω | ¬ ∀ i : ℕ,
    primalVersion V 0 (V.xOf (sample.Z i ω)) = 0 ∧
    dualVersion V 0 (V.zOf (sample.Z i ω)) = 0})ᶜ

/-- [The sample zero event, defined as the complement of a measurable hull of failures of simultaneous zero evaluation, is measurable](goal). -/
lemma sampleZeroEvent_measurable (sample : AnalysisSample V P) :
    MeasurableSet (sampleZeroEvent V P sample) :=
  (measurableSet_toMeasurable _ _).compl

/-- [Almost every sampling outcome belongs to the sample zero event](goal). -/
lemma sampleZeroEvent_ae (sample : AnalysisSample V P) :
    ∀ᵐ ω ∂P, ω ∈ sampleZeroEvent V P sample := by
  have hall : ∀ᵐ ω ∂P, ∀ i : ℕ,
      primalVersion V 0 (V.xOf (sample.Z i ω)) = 0 ∧
      dualVersion V 0 (V.zOf (sample.Z i ω)) = 0 := by
    apply ae_all_iff.mpr
    intro i
    apply ae_of_ae_map (μ := P)
      (p := fun w => primalVersion V 0 (V.xOf w) = 0 ∧ dualVersion V 0 (V.zOf w) = 0)
      (sample.meas i).aemeasurable
    rw [sample.map_eq i]
    exact (primalVersion_zero_ae V).and (dualVersion_zero_ae V)
  change ∀ᵐ ω ∂P, ω ∈ (toMeasurable P _)ᶜ
  rw [ae_iff]
  simpa only [Set.mem_compl_iff, not_not, Set.ofPred_mem_eq,
    measure_toMeasurable] using (show P {ω | ¬ ∀ i : ℕ,
      primalVersion V 0 (V.xOf (sample.Z i ω)) = 0 ∧
      dualVersion V 0 (V.zOf (sample.Z i ω)) = 0} = 0 from hall)

/-- If [a sampling outcome belongs to the sample zero event](hyp:hω), then at any observation index [both the supplied primal and dual zero-coordinate versions evaluate to zero](goal). -/
lemma sampleZeroEvent_spec (sample : AnalysisSample V P) {ω : Ω}
    (hω : ω ∈ sampleZeroEvent V P sample) (i : ℕ) :
    primalVersion V 0 (V.xOf (sample.Z i ω)) = 0 ∧
      dualVersion V 0 (V.zOf (sample.Z i ω)) = 0 := by
  have h : ∀ i : ℕ, primalVersion V 0 (V.xOf (sample.Z i ω)) = 0 ∧
      dualVersion V 0 (V.zOf (sample.Z i ω)) = 0 := by
    by_contra hn
    exact hω (subset_toMeasurable P _ hn)
  exact h i

/-- Four disjoint blocks of size n, as prescribed by the sampling setup. -/
structure SampleSplit where
  pre : ℕ → Finset ℕ -- @realizes I_{\mathrm{pre}}(preliminary indices)
  fit : ℕ → Finset ℕ -- @realizes I_{\mathrm{fit}}(fitting indices)
  cal : ℕ → Finset ℕ -- @realizes I_{\mathrm{cal}}(calibration indices)
  eval : ℕ → Finset ℕ
  card_pre : ∀ n, (pre n).card = n
  card_fit : ∀ n, (fit n).card = n -- @realizes n(each analysis block has natural-number size n)
  card_cal : ∀ n, (cal n).card = n
  card_eval : ∀ n, (eval n).card = n
  disjoint : ∀ n, List.Pairwise Disjoint [pre n, fit n, cal n, eval n]

/-- For [the population problem](hyp:V), [the sampling measure](hyp:P), [an analysis sample](hyp:sample), [a finite block of observation indices](hyp:I), [a real-valued observation function](hyp:f), and [a sampling outcome](hyp:ω), [the block average](goal) is the sum of the function's observed values divided by the block size, with value zero for an empty block. -/
noncomputable def blockAverage (sample : AnalysisSample V P) (I : Finset ℕ)
    (f : 𝒲 → ℝ) (ω : Ω) : ℝ :=
  (I.card : ℝ)⁻¹ * ∑ i ∈ I, f (sample.Z i ω)

-- @node: def:norms
/-- For [the population problem](hyp:V), [the sampling measure](hyp:P), [an analysis sample](hyp:sample), [a finite block of observation indices](hyp:I), [a real-valued observation function](hyp:f), and [a sampling outcome](hyp:ω), [the empirical norm](goal) is the square root of the average squared function values over that block, with value zero for an empty block. -/
noncomputable def empNorm (sample : AnalysisSample V P) (I : Finset ℕ)
    (f : 𝒲 → ℝ) (ω : Ω) : ℝ :=
  Causalean.Stat.Concentration.empiricalNorm
    (fun i : Fin I.card => sample.Z (I.orderEmbOfFin rfl i) ω) f

-- @node: empNorm_eq
/-- [The empirical norm of a function on a finite observation block equals the square root of the block average of its squared values](goal). -/
lemma empNorm_eq (sample : AnalysisSample V P) (I : Finset ℕ)
    (f : 𝒲 → ℝ) (ω : Ω) :
    empNorm V P sample I f ω =
      Real.sqrt (blockAverage V P sample I (fun w => f w ^ 2) ω) := by
  have hsum : (∑ i : Fin I.card, f (sample.Z (I.orderEmbOfFin rfl i) ω) ^ 2) =
      ∑ i ∈ I, f (sample.Z i ω) ^ 2 := by
    conv_rhs => rw [← I.map_orderEmbOfFin_univ rfl, Finset.sum_map]
    rfl
  simp only [empNorm, Causalean.Stat.Concentration.empiricalNorm, blockAverage,
    one_div, hsum]

/-- For [an input distribution](hyp:law) and [a real-valued input function](hyp:f), [the population L¹ norm](goal) is the integral of the function's absolute value under that distribution. -/
noncomputable def inputL1Norm {A : Type*} [MeasurableSpace A] (law : Measure A)
    (f : A → ℝ) : ℝ := ∫ x, |f x| ∂law

/-- For [an input distribution](hyp:law) and [a real-valued input function](hyp:f), [the population L² norm](goal) is the square root of the integral of the function's square under that distribution. -/
noncomputable def inputL2Norm {A : Type*} [MeasurableSpace A] (law : Measure A)
    (f : A → ℝ) : ℝ := Real.sqrt (∫ x, f x ^ 2 ∂law)

-- @node: inputL2Norm_of_version
/-- If [the input map is measurable](hyp:hx), [the real-valued input function is measurable](hyp:hg), and [the function evaluated through that map agrees almost everywhere with a given population L² element](hyp:hfg), then [the function's L² norm under the induced input distribution equals the norm of that element](goal). -/
lemma inputL2Norm_of_version {A D : Type*} [MeasurableSpace A] [MeasurableSpace D]
    (law : Measure A) (x : A → D) (hx : Measurable x)
    (f : Lp ℝ 2 law) (g : D → ℝ) (hg : Measurable g)
    (hfg : (fun a => g (x a)) =ᵐ[law] (f : A → ℝ)) :
    inputL2Norm (law.map x) g = ‖f‖ := by
  unfold inputL2Norm
  rw [integral_map hx.aemeasurable (by fun_prop)]
  rw [integral_congr_ae (hfg.mono fun a ha => congrArg (fun t : ℝ => t ^ 2) ha)]
  have hsq := real_inner_self_eq_norm_sq f
  rw [L2.inner_def] at hsq
  simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs] at hsq
  rw [hsq, Real.sqrt_sq (norm_nonneg _)]

/-- For [the population problem](hyp:V) and [a primal element](hyp:h), [the primal population L² norm](goal) is its Hilbert-space norm. -/
noncomputable def primalL2Norm (h : V.Hbar.toSubmodule) : ℝ := ‖h‖
/-- For [the population problem](hyp:V) and [a dual element](hyp:q), [the dual population L² norm](goal) is its Hilbert-space norm. -/
noncomputable def dualL2Norm (q : V.Qbar.toSubmodule) : ℝ := ‖q‖
-- keep: Realizes the primal population L1 convention in def:norms alongside its L2 companion; retained as part of that reviewed norm interface.
/-- For [the population problem](hyp:V) and [a primal element](hyp:h), [the primal population L¹ norm](goal) is the integral of the absolute value of its supplied covariate version under the covariate distribution. -/
noncomputable def primalL1Norm (h : V.Hbar.toSubmodule) : ℝ :=
  inputL1Norm (V.law.map V.xOf) (primalVersion V h)
-- keep: Realizes the exchanged population L1 convention in def:norms alongside its L2 companion; retained as part of that reviewed norm interface.
/-- For [the population problem](hyp:V) and [a dual element](hyp:q), [the dual population L¹ norm](goal) is the integral of the absolute value of its supplied instrument version under the instrument distribution. -/
noncomputable def dualL1Norm (q : V.Qbar.toSubmodule) : ℝ :=
  inputL1Norm (V.law.map V.zOf) (dualVersion V q)

-- @node: primalL2Norm_eq
/-- For [a primal element](hyp:h), [its population L² norm equals the L² norm of its supplied covariate version under the covariate distribution](goal). -/
lemma primalL2Norm_eq (h : V.Hbar.toSubmodule) :
    primalL2Norm V h = inputL2Norm (V.law.map V.xOf) (primalVersion V h) := by
  exact (inputL2Norm_of_version V.law V.xOf V.measurable_x
    (h : Lp ℝ 2 V.law) (primalVersion V h) (V.primal_measurable h)
    (V.primal_coherent h)).symm

-- @node: dualL2Norm_eq
/-- [A dual element's population L² norm equals the L² norm of its supplied instrument version under the instrument distribution](goal). -/
lemma dualL2Norm_eq (q : V.Qbar.toSubmodule) :
    dualL2Norm V q = inputL2Norm (V.law.map V.zOf) (dualVersion V q) := by
  exact (inputL2Norm_of_version V.law V.zOf V.measurable_z
    (q : Lp ℝ 2 V.law) (dualVersion V q) (V.dual_measurable q)
    (V.dual_coherent q)).symm

-- @node: def:critical-radius-product-classes
/-- Given [a class of functions on the first input space](hyp:H) and [a class of functions on the second input space](hyp:F), [their product class](goal) consists of all functions on input pairs obtained by multiplying one function from each class. -/
def productClass {A B : Type*} (H : Set (A → ℝ)) (F : Set (B → ℝ)) :
    Set (A × B → ℝ) := {g | ∃ h ∈ H, ∃ f ∈ F, g = fun x => h x.1 * f x.2}

/-- For [the population problem](hyp:V), [the moment image class](goal) consists of the observation functions obtained by applying the moment map to members of the adversarial test class. -/
def momentImageClass : Set (𝒲 → ℝ) := {g | ∃ f ∈ V.F, g = V.m f}

/-- Given [a class of real-valued functions](hyp:F), [its difference class](goal) consists of all pointwise differences of two functions in the class. -/
def differenceClass {A : Type*} (F : Set (A → ℝ)) : Set (A → ℝ) :=
  {g | ∃ f ∈ F, ∃ f' ∈ F, g = f - f'}

/-- Given [a class of real-valued functions](hyp:F), [its star hull](goal) consists of all functions obtained by multiplying a member of the class by a scalar between zero and one, inclusive. -/
def starClass {A : Type*} (F : Set (A → ℝ)) : Set (A → ℝ) :=
  {g | ∃ a ∈ Set.Icc (0 : ℝ) 1, ∃ f ∈ F, g = a • f}

/-- For [a function class](hyp:F), [a sample size](hyp:n), [the corresponding input observations](hyp:x), and [a Boolean sign assignment, with true representing plus one and false minus one](hyp:ε), [the signed supremum](goal) is the supremum over the class of the absolute signed sample average, allowing an infinite value. -/
noncomputable def signedSupremum {A : Type*} [MeasurableSpace A]
    (F : Set (A → ℝ)) (n : ℕ) (x : Fin n → A) (ε : Fin n → Bool) : ℝ≥0∞ :=
  ⨆ f : F, ENNReal.ofReal |(n : ℝ)⁻¹ * ∑ i,
    (if ε i then (1 : ℝ) else -1) * f.1 (x i)|

/-- For [an input distribution](hyp:law), [a function class](hyp:F), and [a sample size](hyp:n), [the expected Rademacher complexity](goal) averages the signed supremum over all equally likely sign assignments and integrates over independent inputs with that common distribution, allowing an infinite value. -/
noncomputable def expectedRademacher {A : Type*} [MeasurableSpace A]
    (law : Measure A) (F : Set (A → ℝ)) (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ x : Fin n → A, (2 ^ n : ℝ≥0∞)⁻¹ *
    ∑ ε : Fin n → Bool, signedSupremum F n x ε ∂Measure.pi (fun _ => law)

-- @node: def:critical-radius
/-- For [an input distribution](hyp:law), [a function class](hyp:F), [a sample size](hyp:n), and [a candidate radius](hyp:δ), [the critical-radius bound](goal) requires that [the radius is strictly positive](step:1) and [the expected Rademacher complexity of the star hull of the difference class, restricted to functions with population L² norm at most that radius, is at most the radius squared](step:2). -/
noncomputable def IsCriticalRadiusBound {A : Type*} [MeasurableSpace A]
    (law : Measure A) (F : Set (A → ℝ)) (n : ℕ) (δ : ℝ) : Prop :=
  0 < δ ∧ expectedRademacher law
    {f ∈ starClass (differenceClass F) | eLpNorm f 2 law ≤ ENNReal.ofReal δ} n ≤
      ENNReal.ofReal (δ ^ 2)

-- @node: ass:calibration-valid-bounds
/-- Given [a calibrated radius sequence](hyp:δ), [a calibrated projected-error sequence](hyp:ν), [a baseline radius sequence](hyp:baseδ), [a baseline projected-error sequence](hyp:baseν), [a radius multiplier](hyp:κδ), [a projected-error multiplier](hyp:κν), and [a required multiplier threshold](hyp:required), [valid calibration](goal) means that [the radius multiplier is at least one](step:1), [the projected-error multiplier is at least one](step:2), [the radius multiplier meets the required threshold](step:3), [the projected-error multiplier meets the required threshold](step:4), [the calibrated radius equals its multiplier times its baseline at every sample size](step:5), and [the calibrated projected error equals its multiplier times its baseline at every sample size](step:6). -/
def CalibratedValidBounds (δ ν baseδ baseν : ℕ → ℝ) (κδ κν required : ℝ) : Prop :=
  1 ≤ κδ ∧ 1 ≤ κν ∧ required ≤ κδ ∧ required ≤ κν ∧
  (∀ n, δ n = κδ * baseδ n) ∧ (∀ n, ν n = κν * baseν n)

-- @node: ass:calibration-source-independence
/-- For [a policy assigning a pair of multipliers to four population bounds and a sample size, penalty, and source exponent](hyp:multipliers), [source-free calibration](goal) means that, at any fixed population bounds, the pair is identical for every positive sample size, positive penalty, and positive source exponent.

Public results realize
this dependency directly: they bind a map of population bounds, evaluate its
pair of multipliers, and only then quantify over source data. No pointwise
equality to an independently supplied pair is used as a hypothesis. -/
def CalibrationSourceFree
    (multipliers : (ℝ × ℝ × ℝ × ℝ) → (ℕ × ℝ × ℝ) → ℝ × ℝ) : Prop :=
  ∀ bounds n n' lam lam' β β',
    0 < n → 0 < n' → 0 < lam → 0 < lam' → 0 < β → 0 < β' →
      multipliers bounds (n, lam, β) = multipliers bounds (n', lam', β')

-- @node: ass:calibration-before-fitting
/-- For [a deterministic radius sequence](hyp:δ) and [a deterministic projected-error sequence](hyp:ν), [deterministic calibration](goal) requires that [every radius is nonnegative](step:1) and [every projected-error bound is nonnegative](step:2). -/
def CalibrationDeterministic (δ ν : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ δ n) ∧ -- @realizes \delta_n(deterministic nonnegative sequence fixed before fitting)
  (∀ n, 0 ≤ ν n) -- @realizes \nu_n(deterministic nonnegative projected-error sequence)

-- @node: ass:exist-lambda-deepiv-zero-case
/-- For [the population problem](hyp:V), [the zero-solution case](goal) means that the selected minimum-norm primal solution is zero. -/
def ZeroSolutionCase : Prop := minNormSolution V = 0

-- @node: ass:deepiv-rate-zero-case
/-- For [the population problem](hyp:V), [the zero-solution case used in the rate result](goal) means that the selected minimum-norm primal solution is zero. -/
def ZeroSolutionCaseRate : Prop := ZeroSolutionCase V

-- @node: ass:exist-lambda-iter-rdiv-zero-case
/-- For [the population problem](hyp:V), [the zero-solution case used in the iterative result](goal) means that the selected minimum-norm primal solution is zero. -/
def ZeroSolutionCaseIter : Prop := ZeroSolutionCase V

-- @node: projCondExpOp_norm_le_one
/-- [The projected conditional-expectation operator has operator norm at most one](goal). -/
lemma projCondExpOp_norm_le_one : ‖projCondExpOp V‖ ≤ 1 := by
  apply (projCondExpOp V).opNorm_le_bound (by norm_num : (0 : ℝ) ≤ 1)
  intro h
  simp only [one_mul]
  exact (V.Qbar.toSubmodule.norm_orthogonalProjectionOnto_apply_le _).trans
    (norm_condExpL2_le V.measurable_z.comap_le (h : Lp ℝ 2 V.law))

-- @node: primalVersion_spec
/-- For [a primal Hilbert-space element](hyp:h), [its supplied covariate function is measurable and, when evaluated at the observed covariates, agrees almost everywhere under the population law with that element](goal). -/
lemma primalVersion_spec (h : V.Hbar.toSubmodule) :
    Measurable (primalVersion V h) ∧
      (fun w => primalVersion V h (V.xOf w)) =ᵐ[V.law]
        ((h : Lp ℝ 2 V.law) : 𝒲 → ℝ) := by
  exact ⟨V.primal_measurable h, V.primal_coherent h⟩

-- @node: dualVersion_spec
/-- For [a dual Hilbert-space element](hyp:q), [its supplied instrument function is measurable and, when evaluated at the observed instruments, agrees almost everywhere under the population law with that element](goal). -/
lemma dualVersion_spec (q : V.Qbar.toSubmodule) :
    Measurable (dualVersion V q) ∧
      (fun w => dualVersion V q (V.zOf w)) =ᵐ[V.law]
        ((q : Lp ℝ 2 V.law) : 𝒲 → ℝ) := by
  exact ⟨V.dual_measurable q, V.dual_coherent q⟩


end Papers.TsAdaptiveEstimationInference

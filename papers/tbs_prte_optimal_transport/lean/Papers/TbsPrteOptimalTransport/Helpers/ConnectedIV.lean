module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLProcedure
public import Papers.TbsPrteOptimalTransport.Helpers.Attainment
public import Causalean.Mathlib.Analysis.ClipInterval
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.SpecialFunctions.Sigmoid
/-! Connected propensity support, boundary law and the three-split plug-in estimator. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]
variable (M : LatentIVModel Ω X Z)
variable (zeroLaw : X → {ν : ProbabilityMeasure ℝ // ν.toMeasure M.Ysetᶜ = 0})
-- @env: S5
variable (μ : Measure A) (S : ObservedSample M μ)
-- @node: ass:connected-instrument-domain
/-- For [an instrument domain](hyp:Z), [instrument connectedness](goal) means that the domain is nonempty and cannot be separated into two disjoint nonempty open sets. -/
def InstrumentConnected (Z : Type*) [TopologicalSpace Z] : Prop := ConnectedSpace Z
-- @node: ass:continuous-reduction-connected
/-- For [an instrument domain](hyp:Z), [the connected-domain reduction condition](goal) requires that the domain be connected and nonempty. -/
def InstrumentConnectedReduction (Z : Type*) [TopologicalSpace Z] : Prop := InstrumentConnected Z
/-- Given [a propensity function](hyp:p) and [a covariate value](hyp:x), [the lower propensity endpoint](goal) is the infimum of propensity values over all instruments at that covariate value. -/
noncomputable def pLow (p : Z → X → ℝ) (x : X) := sInf (range (fun z => p z x)) -- @realizes \underline{p}(infimum of conditional propensity values)

/-- Given [a propensity function](hyp:p) and [a covariate value](hyp:x), [the upper propensity endpoint](goal) is the supremum of propensity values over all instruments at that covariate value. -/
noncomputable def pHigh (p : Z → X → ℝ) (x : X) := sSup (range (fun z => p z x)) -- @realizes \overline{p}(supremum of conditional propensity values)

-- @node: propensity_support_endpoints
/-- If [all values of the propensity function lie between zero and one](hyp:hp), then [at every covariate value both its infimum and supremum over instruments lie between zero and one, and the infimum does not exceed the supremum](goal). -/
lemma propensity_support_endpoints (p : Z → X → ℝ)
    (hp : ∀ z x, p z x ∈ Icc (0 : ℝ) 1) (x : X) :
    pLow p x ∈ Icc (0 : ℝ) 1 ∧ pHigh p x ∈ Icc (0 : ℝ) 1 ∧
      pLow p x ≤ pHigh p x := by
  have hne : (range (fun z => p z x)).Nonempty := range_nonempty _
  have hlo : BddBelow (range (fun z => p z x)) :=
    ⟨0, by rintro _ ⟨z, rfl⟩; exact (hp z x).1⟩
  have hhi : BddAbove (range (fun z => p z x)) :=
    ⟨1, by rintro _ ⟨z, rfl⟩; exact (hp z x).2⟩
  have horder : pLow p x ≤ pHigh p x := csInf_le_csSup hne hlo hhi
  have hlow : 0 ≤ pLow p x :=
    le_csInf hne (by rintro _ ⟨z, rfl⟩; exact (hp z x).1)
  have hhigh : pHigh p x ≤ 1 :=
    csSup_le hne (by rintro _ ⟨z, rfl⟩; exact (hp z x).2)
  exact ⟨⟨hlow, horder.trans hhigh⟩, ⟨hlow.trans horder, hhigh⟩, horder⟩

/-- Given [a propensity function](hyp:p), [a policy propensity](hyp:q), [an instrument value](hyp:z), and [a covariate value](hyp:x), [the clamped policy](goal) takes the maximum of the policy propensity and the lower propensity endpoint, then the minimum of that result and the upper endpoint. -/
noncomputable def clampPolicy (p q : Z → X → ℝ) (z : Z) (x : X) := min (pHigh p x) (max (pLow p x) (q z x))
  -- @realizes q^{\mathrm{tr}}(policy projected onto conditional support)
-- @node: def:connected-propensity-setup
/-- For [a propensity function](hyp:p) and [a policy propensity](hyp:q), [the connected-support setup](goal) is the triple consisting of the lower endpoint function, the upper endpoint function, and the policy clamped between those endpoints. -/
noncomputable def connectedSetup (p q : Z → X → ℝ) := (pLow p, pHigh p, clampPolicy p q)
-- @node: def:connected-g1
/-- For [a latent instrument model](hyp:M), [a propensity threshold](hyp:t), and [a covariate value](hyp:x), [the canonical treated regression](goal) is the outcome integral against the canonical treated submeasure at that threshold and covariate value. -/
noncomputable def g1 (t : ℝ) (x : X) := g1Canon M t x -- @realizes g_1(canonical treated regression)
-- @node: def:boundary-treated-law
/-- For [a latent instrument model](hyp:M), [a covariate-indexed choice of outcome-supported fallback probability laws](hyp:zeroLaw), and [a covariate value](hyp:x), [the treated boundary law](goal) is [the canonical treated submeasure at the lower propensity endpoint divided by that endpoint when it is positive](step:1), and [the fallback law otherwise](step:2). -/
noncomputable def boundaryLaw (x : X) : Measure ℝ :=
  if 0 < pLow M.prop x then (ENNReal.ofReal (pLow M.prop x))⁻¹ • canonSubmeasure M true x (pLow M.prop x)
  else (zeroLaw x).val.toMeasure
  -- @realizes \mu_{1,\underline p\mid x}(normalized canonical boundary submeasure; arbitrary zero branch)
/-- For [a latent instrument model](hyp:M), [fallback outcome laws](hyp:zeroLaw), [a covariate value](hyp:x), and [a quantile rank](hyp:t), [the boundary quantile](goal) equals [the model's lower outcome endpoint at rank zero](step:1), [its upper outcome endpoint at rank one](step:2), and [the treated boundary law's quantile at every other rank](step:3). -/
noncomputable def boundaryQuantile (x : X) (t : ℝ) :=
  if t = 0 then M.yMin else if t = 1 then M.yMax else
    Causalean.Stat.quantile (boundaryLaw M zeroLaw x) t
  -- @realizes Q_{1,\underline p\mid x}(single lower generalized inverse)
-- @node: ass:pin-38
/-- For [a latent instrument model](hyp:M) and [fallback outcome laws](hyp:zeroLaw), [the boundary lower-inverse condition](goal) requires that, for almost every covariate value, every rank strictly between zero and one has boundary quantile equal to the infimum of outcome thresholds whose boundary-law mass within the outcome domain and below that threshold reaches the rank. -/
def BoundaryQuantileLowerInverse' : Prop :=
  ∀ᵐ x ∂xLaw M, ∀ t ∈ Ioo (0:ℝ) 1, boundaryQuantile M zeroLaw x t =
    sInf {y : ℝ | t ≤ ((boundaryLaw M zeroLaw x) (M.Yset ∩ Iic y)).toReal}
-- @node: ass:pin-60
/-- For [a latent instrument model](hyp:M) and [fallback outcome laws](hyp:zeroLaw), [the endpoint-pinned boundary inverse condition](goal) requires, at almost every covariate value with positive lower propensity endpoint, [that each interior-rank boundary quantile be the infimum of thresholds whose boundary-law mass within the outcome domain and below the threshold reaches that rank](step:1), [that the rank-zero quantile equal the lower outcome endpoint](step:2), and [that the rank-one quantile equal the upper outcome endpoint](step:3). -/
def BoundaryQuantileLowerInverseEndpoint : Prop :=
  ∀ᵐ x ∂xLaw M, 0 < pLow M.prop x →
    (∀ t ∈ Ioo (0 : ℝ) 1, boundaryQuantile M zeroLaw x t =
      sInf {y : ℝ | t ≤ ((boundaryLaw M zeroLaw x) (M.Yset ∩ Iic y)).toReal}) ∧
    boundaryQuantile M zeroLaw x 0 = M.yMin ∧
    boundaryQuantile M zeroLaw x 1 = M.yMax

-- @node: boundaryQuantile_eq_quantile_of_mem_Ioo
/-- If [a rank lies strictly between zero and one](hyp:ht), then [the boundary quantile at any covariate value equals the ordinary quantile of the treated boundary law at that rank](goal). -/
lemma boundaryQuantile_eq_quantile_of_mem_Ioo (x : X) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    boundaryQuantile M zeroLaw x t = Causalean.Stat.quantile (boundaryLaw M zeroLaw x) t := by
  have ht0 : t ≠ 0 := ne_of_gt ht.1
  have ht1 : t ≠ 1 := ne_of_lt ht.2
  simp only [boundaryQuantile, if_neg ht0, if_neg ht1]

-- @node: boundaryQuantile_ae_quantile
/-- [At every covariate value, the boundary quantile and the ordinary quantile of the treated boundary law agree for almost every rank under the uniform probability measure on the open unit interval](goal). -/
lemma boundaryQuantile_ae_quantile (x : X) :
    boundaryQuantile M zeroLaw x =ᵐ[Causalean.Stat.unifOI]
      Causalean.Stat.quantile (boundaryLaw M zeroLaw x) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact boundaryQuantile_eq_quantile_of_mem_Ioo M zeroLaw x ht

/-- For [a latent instrument model](hyp:M), [fallback outcome laws](hyp:zeroLaw), [a choice of upper rather than lower bound](hyp:upper), [a policy propensity](hyp:q), and [an instrument-covariate pair](hyp:zx), [the connected-support bound integrand](goal) uses [the pair's instrument value](step:1), [its covariate value](step:2), and [the lower propensity endpoint at that covariate value](step:3). It adds the negative boundary-quantile integral from the smaller of the policy propensity and lower endpoint to that endpoint (zero when the endpoint is nonpositive), the treated-regression change at the clamped policy, and the positive excess above the upper endpoint times the selected outcome endpoint; the boundary rank is reversed for the upper bound. -/
noncomputable def connectedInt (upper : Bool) (q : Z → X → ℝ) (zx : Z × X) :=
  let z := zx.1; let x := zx.2; let low := pLow M.prop x
  (if 0 < low then -(∫ v in Ioc (min low (q z x)) low,
    boundaryQuantile M zeroLaw x (if upper then 1-v/low else v/low)) else 0) +
  g1 M (clampPolicy M.prop q z x) x - g1 M (M.prop z x) x +
  (if upper then M.yMax else M.yMin) * max 0 (q z x - pHigh M.prop x)
/-- For [a latent instrument model](hyp:M), [fallback outcome laws](hyp:zeroLaw), [a choice of upper rather than lower bound](hyp:upper), and [a policy propensity](hyp:q), [the connected-support bound value](goal) is the integral of the corresponding bound integrand over the joint instrument-covariate distribution. -/
noncomputable def connectedValue (upper : Bool) (q : Z → X → ℝ) := ∫ zx, connectedInt M zeroLaw upper q zx ∂zxLaw M
-- @node: connectedInt_zero_choice_invariant
/-- For [another covariate-indexed family of outcome-supported fallback probability laws](hyp:other), [the connected-support bound integrand equals the integrand computed with that alternative family, for either bound, every policy propensity, and every instrument-covariate pair](goal). -/
lemma connectedInt_zero_choice_invariant
    (other : X → {ν : ProbabilityMeasure ℝ // ν.toMeasure M.Ysetᶜ = 0})
    (upper : Bool) (q : Z → X → ℝ) (zx : Z × X) :
    connectedInt M zeroLaw upper q zx = connectedInt M other upper q zx := by
  unfold connectedInt
  by_cases hl : 0 < pLow M.prop zx.2
  · simp only [if_pos hl, boundaryQuantile, boundaryLaw]
  · simp only [if_neg hl]

-- @node: ass:continuous-split-proportions
/-- For [a sampling measure](hyp:μ), [three sample-split rules](hyp:I), and [three proposed limiting proportions](hyp:rho), [the split-proportion condition](goal) requires [each split to contain only indices among the first sample-size observations, almost surely at each sample size](step:1), and [each limiting proportion to lie strictly between zero and one, with the corresponding split's size divided by sample size converging to it almost surely](step:2). -/
def SplitProportions (I : Fin 3 → SampleSplit A) (rho : Fin 3 → ℝ) : Prop :=
  (∀ n, ∀ᵐ a ∂μ, ∀ j : Fin 3, I j n a ⊆ Finset.range n) ∧ -- @realizes I_0(first-stage indices contained in the n-observation index set) @realizes I_1(regression and boundary-law indices contained in the n-observation index set) @realizes I_2(evaluation indices contained in the n-observation index set)
  ∀ j, rho j ∈ Ioo (0:ℝ) 1 ∧ ∀ᵐ a ∂μ, -- @realizes \rho_j(positive limiting proportions for each split)
    Tendsto (fun n => ((I j n a).card : ℝ) / n) atTop (𝓝 (rho j))


/-- For [a latent instrument model](hyp:M), [a sampling measure](hyp:μ), [an observed sample](hyp:S), and [three sample-split rules](hyp:I), [a three-way partition](goal) requires [measurable split selection at every sample size](step:1), [almost-sure pairwise disjointness and coverage of exactly the first sample-size indices](step:2), and [independence of the joint split selection from those observations](step:3). -/
def ThreeWayPartition (I : Fin 3 → SampleSplit A) : Prop :=
  (∀ n j, Measurable (I j n)) ∧
  (∀ n, ∀ᵐ a ∂μ, (∀ j k : Fin 3, j ≠ k → Disjoint (I j n a) (I k n a)) ∧
    (I 0 n a ∪ I 1 n a ∪ I 2 n a = Finset.range n)) ∧
  (∀ n, IndepFun (fun a => fun j => I j n a) (fun a => fun i : Fin n => S.Z i a) μ)
-- @node: def:continuous-rates-estimated-boundary-law
/-- Given [a fitted quantile function indexed by sample size, sample realization, and covariates](hyp:Q), [a sample size](hyp:n), [a sample realization](hyp:a), and [a covariate value](hyp:x), [the fitted boundary law](goal) is the image of the uniform measure on the open unit interval under that fitted quantile function. -/
noncomputable def boundaryLawHat (Q : ℕ → A → X → ℝ → ℝ) (n : ℕ) (a : A) (x : X) :=
  Causalean.Stat.unifOI.map (Q n a x)
  -- @realizes \hat\mu_{1,\underline p\mid x}(law induced by the fitted quantile)
/-- For [a quantile function](hyp:Q) and [a rank cutoff](hyp:t), [the quantile primitive](goal) is its integral over ranks greater than zero and at most that cutoff. -/
noncomputable def quantilePrimitive (Q : ℝ → ℝ) (t : ℝ) := ∫ s in Ioc 0 t, Q s
/-- Given [a grid size](hyp:N) [that is positive](hyp:_hN), [a sequence of grid values](hyp:v), and [an evaluation rank](hyp:t), [the interpolated value](goal) is [the initial grid value at nonpositive ranks](step:1), [the final grid value at ranks at least one](step:2), and [the linear blend between adjacent grid values in the rank's grid cell at interior ranks](step:3). The cell index is the smaller of the grid size minus one and the floor of rank times grid size; the blend weight is rank times grid size minus that index. -/
noncomputable def interpolate (N : ℕ) (_hN : 0 < N) (v : ℕ → ℝ) (t : ℝ) :=
  if t ≤ 0 then v 0 else if 1 ≤ t then v N else
    let m := min (N-1) (Nat.floor (t * N))
    let a := t * N - m
    (1-a) * v m + a * v (m+1)

/-- For [a grid size](hyp:N) [that is positive](hyp:_hN), [a quantile function](hyp:Q), and [a number of grid cells](hyp:m), [the cumulative grid value](goal) is the trapezoidal sum over those cells on the equally spaced grid with spacing one divided by the grid size. -/
noncomputable def cumulativeGrid (N : ℕ) (_hN : 0 < N) (Q : ℝ → ℝ) (m : ℕ) :=
  (2 * (N : ℝ))⁻¹ * ∑ i ∈ Finset.range m, (Q ((i:ℝ)/N) + Q (((i+1:ℕ):ℝ)/N))
/-- Given [a grid size](hyp:N) [that is positive](hyp:hN), [a quantile function](hyp:Q), and [an evaluation rank](hyp:t), [the interpolated cumulative quantile](goal) linearly interpolates its cumulative trapezoidal grid values, using the first or last grid value outside the unit interval. -/
noncomputable def interpCumQuantile (N : ℕ) (hN : 0 < N) (Q : ℝ → ℝ) (t : ℝ) :=
  interpolate N hN (cumulativeGrid N hN Q) t
  -- @realizes \widehat C(grid trapezoid values and off-grid linear interpolation)

/-- For [a latent instrument model](hyp:M), [a choice of upper rather than lower bound](hyp:upper), [a policy transformation](hyp:phi), [a fitted propensity](hyp:p), [a fitted treated regression](hyp:g), [a fitted cumulative quantile](hyp:C), and [an observation](hyp:o), [the fitted bound contribution](goal) uses [the observation's instrument](step:1), [its covariates](step:2), [the fitted lower propensity endpoint](step:3), and [the transformed fitted propensity](step:4). For a positive lower endpoint, its boundary term is minus that endpoint times the cumulative quantile at one minus the cutoff for the upper bound, or minus that endpoint times the difference between cumulative quantiles at one and at the cutoff for the lower bound, where the cutoff is the smaller of one and policy propensity divided by the endpoint; otherwise this term is zero. It adds the fitted-regression change from the original to the clamped policy propensity and the positive excess above the fitted upper endpoint times the selected outcome endpoint. -/
noncomputable def fittedInt (upper : Bool) (phi : Z → X → ℝ → ℝ) -- @realizes \hat\tau_i(cutoff only evaluated when the fitted lower endpoint is positive)
    (p : Z → X → ℝ) (g : ℝ → X → ℝ) (C : X → ℝ → ℝ) (o : Obs X Z) :=
  let z := o.2.1; let x := o.1; let low := pLow p x; let q := phi z x (p z x)
  (if 0 < low then let tau := min 1 (q / low)
    if upper then -low * C x (1-tau) else -low * (C x 1 - C x tau) else 0) +
  g (clampPolicy p (policyProp phi p) z x) x - g (p z x) x +
  (if upper then M.yMax else M.yMin) * max 0 (q - pHigh p x)
  -- @realizes \hat\psi_1(first quantile contribution with explicit zero branch)
  -- @realizes \hat\psi_2(regression contribution)
  -- @realizes \hat\psi_3(tail contribution)

/-- For [a latent instrument model](hyp:M), [a sampling measure](hyp:μ), [an observed sample](hyp:S), [an evaluation split](hyp:I₂), [a policy transformation](hyp:phi), [fitted propensities](hyp:p), [fitted treated regressions](hyp:g), [fitted cumulative quantiles](hyp:C), [a choice of upper rather than lower bound](hyp:upper), [a sample size](hyp:n), and [a sample realization](hyp:a) [whose evaluation split is nonempty](hyp:h), [the unrestricted plug-in average](goal) is the arithmetic mean of the fitted bound contributions over that split. -/
noncomputable def unrestrictedPlugInAverage (I₂ : SampleSplit A) (phi : Z → X → ℝ → ℝ)
    (p : ℕ → A → Z → X → ℝ) (g : ℕ → A → ℝ → X → ℝ) (C : ℕ → A → X → ℝ → ℝ)
    (upper : Bool) (n : ℕ) (a : A) (h : (I₂ n a).Nonempty) :=
  splitMean M S I₂ (fun n a => fittedInt M upper phi (p n a) (g n a) (C n a)) n a h
  -- @realizes \hat{\underline{\theta}}_{\omega,1}(mean of the three fitted contributions)
/-- For [a propensity function](hyp:p), [a policy propensity](hyp:q), [one of three component indices](hyp:j), and [an instrument-covariate pair](hyp:zx), [the selected endpoint map](goal) returns [the lower propensity endpoint for index zero](step:1), [the smaller of that endpoint and the policy propensity for index one](step:2), or [the positive part of the policy propensity's excess over the upper endpoint for index two](step:3). -/
noncomputable def endpointMap (p : Z → X → ℝ) (q : Z → X → ℝ) (j : Fin 3) (zx : Z × X) := -- @realizes \Lambda(one of the three population boundary and tail maps)
  if j = 0 then pLow p zx.2 else if j = 1 then min (pLow p zx.2) (q zx.1 zx.2)
    else max 0 (q zx.1 zx.2 - pHigh p zx.2)

/-- For [a latent instrument model](hyp:M) and [a policy transformation](hyp:phi), [the population endpoint maps](goal) are the lower-endpoint, truncated lower-endpoint, and upper-tail maps evaluated using the model's propensity and its policy-transformed propensity. -/
noncomputable def populationEndpointMap (phi : Z → X → ℝ → ℝ) := -- @realizes \Lambda(population endpoint and tail maps at population inputs)
  endpointMap M.prop (policyProp phi M.prop)

/-- For [a policy transformation](hyp:phi) and [propensity fits indexed by sample size and sample realization](hyp:pHat), [the fitted endpoint maps](goal) are the lower-endpoint, truncated lower-endpoint, and upper-tail maps computed from each fitted propensity and its policy transformation. -/
noncomputable def fittedEndpointMap (phi : Z → X → ℝ → ℝ) -- @realizes \hat\Lambda(corresponding fitted endpoint and tail maps)
    (pHat : ℕ → A → Z → X → ℝ) :=
  fun n a => endpointMap (pHat n a) (policyProp phi (pHat n a))

/-- [The logistic index function](goal) maps a real index to one divided by one plus the exponential of its negative. -/
noncomputable abbrev logisticIndex := Real.sigmoid -- @realizes \Lambda(logistic function in the simulation context)

-- @node: logistic_index_range
/-- [The logistic index function takes every real input to a value strictly between zero and one](goal). -/
lemma logistic_index_range (t : ℝ) : logisticIndex t ∈ Ioo (0 : ℝ) 1 := by
  exact ⟨Real.sigmoid_pos t, Real.sigmoid_lt_one t⟩ -- @realizes \Lambda(logistic-function range (0,1))

-- @node: endpoint_maps_range
/-- If [the propensity function takes values between zero and one](hyp:hp) and [the policy propensity also takes values between zero and one](hyp:hq), then [all three endpoint maps take values between zero and one at every instrument-covariate pair](goal). -/
lemma endpoint_maps_range (p q : Z → X → ℝ)
    (hp : ∀ z x, p z x ∈ Icc (0 : ℝ) 1) (hq : ∀ z x, q z x ∈ Icc (0 : ℝ) 1) :
    ∀ j zx, endpointMap p q j zx ∈ Icc (0 : ℝ) 1  := by
  intro j zx
  have he := propensity_support_endpoints p hp zx.2
  have hq' := hq zx.1 zx.2
  unfold endpointMap
  split_ifs with h0 h1
  · exact he.1
  · exact ⟨le_min he.1.1 hq'.1, (min_le_left _ _).trans he.1.2⟩
  · exact ⟨le_max_left _ _, max_le zero_le_one (by linarith [he.2.1.1, hq'.2])⟩


-- @node: population_endpoint_maps_range
/-- If [the policy transformation is jointly measurable on the unit propensity interval and preserves that interval](hyp:hphi), then [all three population endpoint maps take values between zero and one at every instrument-covariate pair](goal). -/
lemma population_endpoint_maps_range (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi) : -- @realizes \Lambda(population maps in [0,1] using intrinsic propensity range and the policy-map range)
    ∀ j zx, populationEndpointMap M phi j zx ∈ Icc (0 : ℝ) 1 := by
  exact endpoint_maps_range M.prop (policyProp phi M.prop) M.rangeProp
    (fun z x => hphi.2 z x _ (M.rangeProp z x))

-- @node: fitted_endpoint_maps_range
/-- If [every fitted propensity lies between zero and one for every sample size, sample realization, instrument, and covariate value](hyp:hp) and [the policy transformation is jointly measurable on the unit propensity interval and preserves that interval](hyp:hphi), then [all three fitted endpoint maps lie between zero and one at every sample size, sample realization, and instrument-covariate pair](goal). -/
lemma fitted_endpoint_maps_range (phi : Z → X → ℝ → ℝ) -- @realizes \hat\Lambda(fitted maps in [0,1] under fitted-propensity and policy ranges)
    (pHat : ℕ → A → Z → X → ℝ) (hp : ∀ n a z x, pHat n a z x ∈ Icc (0 : ℝ) 1)
    (hphi : IsPolicyMap phi) :
    ∀ n a j zx, fittedEndpointMap phi pHat n a j zx ∈ Icc (0 : ℝ) 1 := by
  intro n a
  exact endpoint_maps_range (pHat n a) (policyProp phi (pHat n a)) (hp n a)
    (fun z x => hphi.2 z x _ (hp n a z x))

/-- For [a sampling measure](hyp:μ), [a random error sequence](hyp:error), and [a deterministic rate sequence](hyp:rate), [boundedness at that rate](goal) requires [nonnegative rates at every sample size](step:1) and [that, for every positive tolerance, some positive constant makes the probability of absolute error strictly exceeding that constant times the rate eventually no greater than the tolerance](step:2).

The strict exceedance event includes the exact zero-error, zero-rate case. -/
def BoundedAtRate (error : ℕ → A → ℝ) (rate : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ rate n) ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ᶠ n in atTop, μ {a | C * rate n < |error n a|} ≤ ENNReal.ofReal ε

-- @node: ass:continuous-rates-endpoints
/-- For [a latent instrument model](hyp:M), [a sampling measure](hyp:μ), [a policy transformation](hyp:phi), [fitted propensities](hyp:pHat), and [an endpoint error rate](hyp:re), [the endpoint-map rate condition](goal) requires [nonnegativity of the rate](step:1), [convergence of the rate to zero](step:2), and [boundedness at that rate of each of the three fitted endpoint maps' integrated absolute errors relative to its population counterpart, integrating over the joint instrument-covariate law](step:3). -/
def EndpointMapRates (phi : Z → X → ℝ → ℝ) (pHat : ℕ → A → Z → X → ℝ) (re : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ re n) ∧ Tendsto re atTop (𝓝 0) ∧ ∀ j : Fin 3, -- @realizes r_{e,n}(vanishing endpoint-map error rate)
    BoundedAtRate μ (fun n a => ∫ zx,
      |endpointMap (pHat n a) (policyProp phi (pHat n a)) j zx -
        endpointMap M.prop (policyProp phi M.prop) j zx| ∂zxLaw M) re

-- @node: ass:continuous-rates-regression
/-- For [a latent instrument model](hyp:M), [a sampling measure](hyp:μ), [a policy transformation](hyp:phi), [fitted propensities](hyp:pHat), [fitted treated regressions](hyp:gHat), and [a regression error rate](hyp:rg), [the regression-target rate condition](goal) requires [that each fitted regression at every unit-interval index lie between the smaller of zero and the lower outcome endpoint and the larger of zero and the upper outcome endpoint](step:1), and [that the joint instrument-covariate integral of the sum of absolute regression errors at the clamped policy and original propensity indices be bounded at that rate, using fitted indices for the fitted regression and population indices for the canonical regression](step:2). -/
def RegressionTargetRate (phi : Z → X → ℝ → ℝ) (pHat : ℕ → A → Z → X → ℝ)
    (gHat : ℕ → A → ℝ → X → ℝ) (rg : ℕ → ℝ) : Prop := -- @realizes \hat g_1(fitted regression carrier)
  (∀ n a t x, t ∈ Icc (0 : ℝ) 1 → gHat n a t x ∈ Icc (min 0 M.yMin) (max 0 M.yMax)) ∧ -- @realizes \hat g_1(clipped regression range)
  BoundedAtRate μ (fun n a => ∫ zx,
    (|gHat n a (clampPolicy (pHat n a) (policyProp phi (pHat n a)) zx.1 zx.2) zx.2 -
      g1 M (clampPolicy M.prop (policyProp phi M.prop) zx.1 zx.2) zx.2| +
     |gHat n a (pHat n a zx.1 zx.2) zx.2 - g1 M (M.prop zx.1 zx.2) zx.2|) ∂zxLaw M) rg
  -- @realizes r_{g,n}(regression error at both target indices)
-- @node: ass:continuous-rates-regression-vanishes
/-- For [a regression error rate sequence](hyp:rg), [the vanishing regression-rate condition](goal) requires [nonnegativity at every sample size](step:1) and [convergence to zero as sample size grows](step:2). -/
def RegressionRateVanishes (rg : ℕ → ℝ) : Prop := (∀ n, 0 ≤ rg n) ∧ Tendsto rg atTop (𝓝 0)
-- @node: ass:continuous-rates-boundary-law
/-- For [a latent instrument model](hyp:M), [fallback outcome laws](hyp:zeroLaw), [a sampling measure](hyp:μ), [fitted boundary quantiles](hyp:QHat), and [a boundary-law error rate](hyp:rmu), [the boundary-law rate condition](goal) requires boundedness at that rate of the covariate integral of the distance between fitted and population boundary laws, weighted by the lower propensity endpoint. The distance is the integral of absolute differences between the laws' quantiles over ranks strictly between zero and one. -/
def BoundaryLawRate (QHat : ℕ → A → X → ℝ → ℝ) (rmu : ℕ → ℝ) : Prop :=
  BoundedAtRate μ (fun n a => ∫ x, pLow M.prop x *
    quantileDistanceIntegral (boundaryLawHat QHat n a x) (boundaryLaw M zeroLaw x) ∂xLaw M) rmu
  -- @realizes r_{\mu,n}(lower-endpoint weighted Wasserstein error)
-- @node: ass:continuous-rates-boundary-vanishes
/-- For [a boundary-law error rate sequence](hyp:rmu), [the vanishing boundary-rate condition](goal) requires [nonnegativity at every sample size](step:1) and [convergence to zero as sample size grows](step:2). -/
def BoundaryRateVanishes (rmu : ℕ → ℝ) : Prop := (∀ n, 0 ≤ rmu n) ∧ Tendsto rmu atTop (𝓝 0)
/-- For [a latent instrument model](hyp:M), [a sampling measure](hyp:μ), [an observed sample](hyp:S), [a first training split](hyp:I₀), [a second training split](hyp:I₁), and [a fitted predictor indexed by sample size, sample realization, and prediction input](hyp:f), [joint labeled-training measurability](goal) requires that, at every sample size, the predictor be jointly measurable in the pair of labeled training views and its prediction input. -/
def LabeledTrainingPredictorMeasurable {B : Type*} [MeasurableSpace B]
    (I₀ I₁ : SampleSplit A) (f : ℕ → A → B → ℝ) : Prop :=
  ∀ n, Measurable[MeasurableSpace.prod
    (MeasurableSpace.comap (fun a => (trainingView M S I₀ n a, trainingView M S I₁ n a))
      inferInstance) inferInstance] (Function.uncurry (f n))
/-- For [a latent instrument model](hyp:M), [a sampling measure](hyp:μ), [an observed sample](hyp:S), [a first-stage training split](hyp:I₀), and [a fitted predictor indexed by sample size, sample realization, and prediction input](hyp:f), [first-stage training measurability](goal) requires that, at every sample size, the predictor be jointly measurable in the labeled first-stage training view alone and its prediction input. -/
abbrev I0TrainingPredictorMeasurable {B : Type*} [MeasurableSpace B]
    (I₀ : SampleSplit A) (f : ℕ → A → B → ℝ) : Prop :=
  TrainingPredictorMeasurable M S I₀ f

/-- For [a latent instrument model](hyp:M), [a sampling measure](hyp:μ), [an observed sample](hyp:S), [three split rules](hyp:I), [fitted propensities](hyp:pHat), [fitted treated regressions](hyp:gHat), and [fitted boundary quantiles](hyp:QHat), [the joint-training fit condition](goal) requires [a three-way partition](step:1), [propensity measurability from both labeled training views](step:2), [treated-regression measurability from both views on unit-interval indices](step:3), and [boundary-quantile measurability from both views on unit-interval ranks](step:4). It also requires, at each sample size, [joint measurability of propensity in sample realization, instrument, and covariates](step:5), [joint measurability of regression in sample realization, unit-interval index, and covariates](step:6), [joint measurability of quantile in sample realization, covariates, and unit-interval rank](step:7), [propensity values between zero and one](step:8), [nondecreasing quantiles on interior ranks](step:9), and [quantiles between the model's outcome endpoints at every unit-interval rank](step:10). -/
def ConnectedJointFitScope (I : Fin 3 → SampleSplit A) (pHat : ℕ → A → Z → X → ℝ)
    (gHat : ℕ → A → ℝ → X → ℝ) (QHat : ℕ → A → X → ℝ → ℝ) : Prop :=
  ThreeWayPartition M μ S I ∧
  LabeledTrainingPredictorMeasurable M μ S (I 0) (I 1)
    (fun n a (zx : Z × X) => pHat n a zx.1 zx.2) ∧
  LabeledTrainingPredictorMeasurable M μ S (I 0) (I 1)
    (fun n a (tx : Icc (0 : ℝ) 1 × X) => gHat n a tx.1.val tx.2) ∧
  LabeledTrainingPredictorMeasurable M μ S (I 0) (I 1)
    (fun n a (xt : X × Icc (0 : ℝ) 1) => QHat n a xt.1 xt.2.val) ∧
  (∀ n, Measurable (fun a_z_x : A × Z × X => pHat n a_z_x.1 a_z_x.2.1 a_z_x.2.2)) ∧
  (∀ n, Measurable (fun a_t_x : A × Icc (0 : ℝ) 1 × X => gHat n a_t_x.1 a_t_x.2.1.val a_t_x.2.2)) ∧
  (∀ n, Measurable (fun a_x_t : A × X × Icc (0 : ℝ) 1 => QHat n a_x_t.1 a_x_t.2.1 a_x_t.2.2.val)) ∧
  (∀ n a z x, pHat n a z x ∈ Icc (0:ℝ) 1) ∧
  (∀ n a x, MonotoneOn (QHat n a x) (Ioo 0 1)) ∧
  (∀ n a x t, t ∈ Icc (0:ℝ) 1 → QHat n a x t ∈ Icc M.yMin M.yMax)

/-- For [a latent instrument model](hyp:M), [a sampling measure](hyp:μ), [an observed sample](hyp:S), [three split rules](hyp:I), [fitted propensities](hyp:pHat), [fitted treated regressions](hyp:gHat), and [fitted boundary quantiles](hyp:QHat), [the paper's fit condition](goal) requires [a three-way partition](step:1), [propensity measurability from the labeled first training view alone](step:2), [treated-regression measurability from both labeled training views on unit-interval indices](step:3), and [boundary-quantile measurability from both views on unit-interval ranks](step:4). It also requires, at each sample size, [joint measurability of propensity in sample realization, instrument, and covariates](step:5), [joint measurability of regression in sample realization, unit-interval index, and covariates](step:6), [joint measurability of quantile in sample realization, covariates, and unit-interval rank](step:7), [propensity values between zero and one](step:8), [nondecreasing quantiles on interior ranks](step:9), and [quantiles between the model's outcome endpoints at every unit-interval rank](step:10). -/
def ConnectedFitScope (I : Fin 3 → SampleSplit A) (pHat : ℕ → A → Z → X → ℝ)
    (gHat : ℕ → A → ℝ → X → ℝ) (QHat : ℕ → A → X → ℝ → ℝ) : Prop :=
  ThreeWayPartition M μ S I ∧
  I0TrainingPredictorMeasurable M μ S (I 0)
    (fun n a (zx : Z × X) => pHat n a zx.1 zx.2) ∧ -- @realizes \hat p(measurable with respect to the labeled I0 training view alone)
  LabeledTrainingPredictorMeasurable M μ S (I 0) (I 1)
    (fun n a (tx : Icc (0 : ℝ) 1 × X) => gHat n a tx.1.val tx.2) ∧
  LabeledTrainingPredictorMeasurable M μ S (I 0) (I 1)
    (fun n a (xt : X × Icc (0 : ℝ) 1) => QHat n a xt.1 xt.2.val) ∧
  (∀ n, Measurable (fun a_z_x : A × Z × X => pHat n a_z_x.1 a_z_x.2.1 a_z_x.2.2)) ∧
  (∀ n, Measurable (fun a_t_x : A × Icc (0 : ℝ) 1 × X => gHat n a_t_x.1 a_t_x.2.1.val a_t_x.2.2)) ∧
  (∀ n, Measurable (fun a_x_t : A × X × Icc (0 : ℝ) 1 => QHat n a_x_t.1 a_x_t.2.1 a_x_t.2.2.val)) ∧
  (∀ n a z x, pHat n a z x ∈ Icc (0:ℝ) 1) ∧ -- @realizes \hat p(fitted propensity range)
  (∀ n a x, MonotoneOn (QHat n a x) (Ioo 0 1)) ∧
  (∀ n a x t, t ∈ Icc (0:ℝ) 1 → QHat n a x t ∈ Icc M.yMin M.yMax) -- @realizes \widehat Q_{1,\underline p\mid x}(free fitted quantile clipped on its rank domain)
-- @node: ConnectedFitScope.toJoint
/-- If [the fitted propensity uses only the first labeled training view and all fits satisfy the paper's partition, measurability, monotonicity, and range conditions](hyp:hFit), then [the same fits satisfy the joint-training fit condition, which permits the propensity to use both labeled training views](goal). -/
lemma ConnectedFitScope.toJoint (I : Fin 3 → SampleSplit A)
    (pHat : ℕ → A → Z → X → ℝ) (gHat : ℕ → A → ℝ → X → ℝ)
    (QHat : ℕ → A → X → ℝ → ℝ)
    (hFit : ConnectedFitScope M μ S I pHat gHat QHat) :
    ConnectedJointFitScope M μ S I pHat gHat QHat := by
  refine ⟨hFit.1, ?_, hFit.2.2⟩
  intro n
  have hview : Measurable[MeasurableSpace.comap
      (fun a => (trainingView M S (I 0) n a, trainingView M S (I 1) n a))
      inferInstance] (trainingView M S (I 0) n) := by
    exact (comap_measurable
      (fun a => (trainingView M S (I 0) n a, trainingView M S (I 1) n a))).fst
  have hid : Measurable[MeasurableSpace.comap
      (fun a => (trainingView M S (I 0) n a, trainingView M S (I 1) n a))
      inferInstance, MeasurableSpace.comap (trainingView M S (I 0) n) inferInstance]
      (id : A → A) := measurable_comap_iff.mpr hview
  exact (hFit.2.1 n).comp ((hid.comp measurable_fst).prodMk measurable_snd)

/-- Given [a policy transformation](hyp:phi) and [fitted propensity functions indexed by sample size and sample realization](hyp:p), [the fitted policy propensity](goal) applies the transformation to the fitted propensity at each instrument and covariate value. -/
noncomputable def fittedPolicy (phi : Z → X → ℝ → ℝ) (p : ℕ → A → Z → X → ℝ) :=
  fun n a => policyProp phi (p n a)
  -- @realizes \hat q(policy map applied to fitted propensity)
/-- Given [fitted propensity functions](hyp:p), [a sample size](hyp:n), [a sample realization](hyp:a), and [an observation](hyp:o), [the observation's fitted propensity](goal) is the fitted propensity evaluated at its instrument and covariates. -/
noncomputable def fittedPropensityObservation (p : ℕ → A → Z → X → ℝ) (n : ℕ) (a : A) (o : Obs X Z) := -- @realizes \hat P(fitted propensity at observation Z,X)
  p n a o.2.1 o.1

/-- Given [fitted propensity functions indexed by sample size and sample realization](hyp:p), [the fitted lower endpoint function](goal) takes, at each covariate value, the infimum of fitted propensity values over all instruments. -/
noncomputable def fittedLowerEndpoint (p : ℕ → A → Z → X → ℝ) := fun n a => pLow (p n a) -- @realizes \hat{\underline p}(infimum of fitted propensity values)

/-- Given [fitted propensity functions indexed by sample size and sample realization](hyp:p), [the fitted upper endpoint function](goal) takes, at each covariate value, the supremum of fitted propensity values over all instruments. -/
noncomputable def fittedUpperEndpoint (p : ℕ → A → Z → X → ℝ) := fun n a => pHigh (p n a) -- @realizes \hat{\overline p}(supremum of fitted propensity values)

/-- Given [a policy transformation](hyp:phi) and [fitted propensity functions indexed by sample size and sample realization](hyp:p), [the fitted truncated policy](goal) clamps the transformed fitted propensity between the fitted lower and upper propensity endpoints at each covariate value. -/
noncomputable def fittedTruncatedPolicy (phi : Z → X → ℝ → ℝ) (p : ℕ → A → Z → X → ℝ) :=
  fun n a => clampPolicy (p n a) (policyProp phi (p n a))
  -- @realizes \hat q^{\mathrm{tr}}(fitted policy clamped to fitted support)
/-- For [a latent instrument model](hyp:M), [fitted quantiles](hyp:Q), and [fitted cumulative quantiles](hyp:C), [the cumulative-fit condition](goal) requires [joint measurability of quantiles in sample realization, covariates, and unit-interval rank at every sample size](step:1), [nondecreasing quantiles on the closed unit interval](step:2), [quantiles between the model's outcome endpoints on that interval](step:3), and [cumulative quantiles that either equal the exact quantile integrals everywhere on that interval or equal their linearly interpolated trapezoidal approximations on positive grids whose sizes depend only on sample size](step:4). -/
def CumulativeFit (Q C : ℕ → A → X → ℝ → ℝ) : Prop :=
  (∀ n, Measurable (fun axt : A × X × Icc (0 : ℝ) 1 => Q n axt.1 axt.2.1 axt.2.2.val)) ∧
  (∀ n a x, MonotoneOn (Q n a x) (Icc (0 : ℝ) 1)) ∧
  (∀ n a x t, t ∈ Icc (0 : ℝ) 1 → Q n a x t ∈ Icc M.yMin M.yMax) ∧
  ((∀ n a x t, t ∈ Icc (0 : ℝ) 1 → C n a x t = quantilePrimitive (Q n a x) t) ∨
   ∃ N : ℕ → ℕ, ∃ hN : ∀ n, 0 < N n,
     ∀ n a x t, t ∈ Icc (0 : ℝ) 1 → C n a x t = interpCumQuantile (N n) (hN n) (Q n a x) t)
-- @node: def:estimator-continuous-instrument
/-- For [a latent instrument model](hyp:M), [a sampling measure](hyp:μ), [an observed sample](hyp:S), [an evaluation split](hyp:I₂), [a policy transformation](hyp:phi), [fitted propensities](hyp:p), [fitted treated regressions](hyp:g), [fitted boundary quantiles](hyp:Q), and [fitted cumulative quantiles](hyp:C), assume [the policy transformation is jointly measurable on unit-interval propensities and preserves that interval](hyp:_hPolicy), [all fitted propensities lie between zero and one](hyp:_hp), [the fitted regression on unit-interval indices lies between the smaller of zero and the lower outcome endpoint and the larger of zero and the upper outcome endpoint](hyp:_hg), and [the quantiles and cumulative quantiles satisfy the cumulative-fit condition](hyp:_hC). Given [a choice of upper rather than lower bound](hyp:upper), [a sample size](hyp:n), and [a sample realization](hyp:a) [with a nonempty evaluation split](hyp:h), [the plug-in estimator](goal) is the arithmetic mean of the fitted bound contributions over that split. -/
noncomputable def plugInEstimator (I₂ : SampleSplit A) (phi : Z → X → ℝ → ℝ)
    (p : ℕ → A → Z → X → ℝ) (g : ℕ → A → ℝ → X → ℝ)
    (Q C : ℕ → A → X → ℝ → ℝ)
    (_hPolicy : IsPolicyMap phi)
    (_hp : ∀ n a z x, p n a z x ∈ Icc (0 : ℝ) 1)
    (_hg : ∀ n a t x, t ∈ Icc (0 : ℝ) 1 → g n a t x ∈ Icc (min 0 M.yMin) (max 0 M.yMax))
    (_hC : CumulativeFit M Q C) (upper : Bool) (n : ℕ) (a : A) (h : (I₂ n a).Nonempty) :=
  unrestrictedPlugInAverage M μ S I₂ phi p g C upper n a h
  -- @realizes \hat{\underline{\theta}}_{\omega,1}(average on clipped nuisances and specified cumulative quantile fit)
-- @node: fitted_support_endpoints
/-- If [every fitted propensity lies between zero and one](hyp:hp), then [at every sample size, sample realization, and covariate value, both fitted propensity endpoints lie between zero and one and the lower endpoint does not exceed the upper endpoint](goal). -/
lemma fitted_support_endpoints (p : ℕ → A → Z → X → ℝ) -- @realizes \hat{\underline p}(fitted lower endpoints in [0,1]) @realizes \hat{\overline p}(fitted upper endpoints in [0,1])
    (hp : ∀ n a z x, p n a z x ∈ Icc (0 : ℝ) 1) :
    ∀ n a x, pLow (p n a) x ∈ Icc (0 : ℝ) 1 ∧
      pHigh (p n a) x ∈ Icc (0 : ℝ) 1 ∧ pLow (p n a) x ≤ pHigh (p n a) x := by
  intro n a x
  exact propensity_support_endpoints (p n a) (hp n a) x


-- @node: population_support_endpoints
/-- [At every covariate value, both population propensity endpoints lie between zero and one, and the lower endpoint does not exceed the upper endpoint](goal). -/
lemma population_support_endpoints : -- @realizes \underline{p}(population lower endpoints in [0,1]) @realizes \overline{p}(population upper endpoints in [0,1])
    ∀ x, pLow M.prop x ∈ Icc (0 : ℝ) 1 ∧ pHigh M.prop x ∈ Icc (0 : ℝ) 1 ∧
      pLow M.prop x ≤ pHigh M.prop x := by
  intro x
  exact propensity_support_endpoints M.prop M.rangeProp x


-- @node: fittedPropensityObservation_range
/-- If [all fitted propensities lie between zero and one](hyp:hp), then [the fitted propensity evaluated at any observation lies between zero and one for every sample size and sample realization](goal). -/
lemma fittedPropensityObservation_range (p : ℕ → A → Z → X → ℝ) -- @realizes \hat P(fitted propensity observation in [0,1])
    (hp : ∀ n a z x, p n a z x ∈ Icc (0 : ℝ) 1) :
    ∀ n a o, fittedPropensityObservation p n a o ∈ Icc (0 : ℝ) 1 := by
  intro n a o
  exact hp n a o.2.1 o.1

-- @node: boundary_quantile_supported
/-- If [the model satisfies the structural assumptions of potential-outcome support, consistency, instrument exogeneity, threshold crossing, uniform resistance, common instrument support, and compact domains](hyp:h), and [the designated outcome endpoints are the least and greatest outcomes in the domain](hyp:he), then [for almost every covariate value, every boundary quantile at a rank strictly between zero and one lies in the outcome domain](goal). -/
lemma boundary_quantile_supported (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M) :
    ∀ᵐ x ∂xLaw M, ∀ t ∈ Ioo (0 : ℝ) 1, boundaryQuantile M zeroLaw x t ∈ M.Yset := by
  filter_upwards [canonical_submeasure_supported M h true,
    canonical_submeasure_mass M h true] with x hs hm
  have hx := population_support_endpoints M x
  have hprob : IsProbabilityMeasure (boundaryLaw M zeroLaw x) := by
    by_cases hp : 0 < pLow M.prop x
    · constructor
      rw [boundaryLaw, if_pos hp, Measure.smul_apply, hm _ hx.1]
      simp only [Bool.true_eq, ↓reduceIte, smul_eq_mul]
      exact ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr hp)
        ENNReal.ofReal_ne_top
    · rw [boundaryLaw, if_neg hp]
      exact (zeroLaw x).val.property
  have hsupport : boundaryLaw M zeroLaw x M.Ysetᶜ = 0 := by
    by_cases hp : 0 < pLow M.prop x
    · rw [boundaryLaw, if_pos hp, Measure.smul_apply, hs _ hx.1, smul_zero]
    · rw [boundaryLaw, if_neg hp]
      exact (zeroLaw x).property
  intro t ht
  rw [boundaryQuantile_eq_quantile_of_mem_Ioo M zeroLaw x ht]
  exact quantile_mem_closed_of_supported _ M.Yset h.2.2.2.2.2.2.1.isClosed
    hsupport t ht
  -- @realizes Q_{1,\underline p\mid x}(boundary quantile takes values in the outcome domain)

-- @node: split_proportions_sum
/-- Under probability sampling, if [the three sample splits form a measurable partition independent of the observations](hyp:hPartition) and [their sizes divided by sample size converge almost surely to proportions strictly between zero and one, with all split indices contained in the sample](hyp:hProportions), then [the three limiting proportions sum to one](goal). -/
lemma split_proportions_sum [IsProbabilityMeasure μ] -- @realizes \rho_j(three limiting split proportions sum to one)
    (I : Fin 3 → SampleSplit A) (rho : Fin 3 → ℝ)
    (hPartition : ThreeWayPartition M μ S I) (hProportions : SplitProportions μ I rho) :
    ∑ j, rho j = 1 := by
  have hpart := ae_all_iff.mpr hPartition.2.1
  have hlim : ∀ᵐ a ∂μ, ∀ j : Fin 3,
      Tendsto (fun n => ((I j n a).card : ℝ) / n) atTop (𝓝 (rho j)) :=
    ae_all_iff.mpr (fun j => (hProportions.2 j).2)
  obtain ⟨a, ha, hla⟩ := (hpart.and hlim).exists
  have hcard (n : ℕ) : (I 0 n a).card + ((I 1 n a).card + (I 2 n a).card) = n := by
    have hd := (ha n).1
    have h01 := hd 0 1 (by decide)
    have h02 := hd 0 2 (by decide)
    have h12 := hd 1 2 (by decide)
    have hc := congrArg Finset.card (ha n).2
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨h02, h12⟩),
      Finset.card_union_of_disjoint h01, Finset.card_range] at hc
    omega
  have hsum : Tendsto (fun n => ((I 0 n a).card : ℝ) / n +
      (((I 1 n a).card : ℝ) / n + ((I 2 n a).card : ℝ) / n))
      atTop (𝓝 (rho 0 + (rho 1 + rho 2))) :=
    (hla 0).add ((hla 1).add (hla 2))
  have hone : Tendsto (fun n => ((I 0 n a).card : ℝ) / n +
      (((I 1 n a).card : ℝ) / n + ((I 2 n a).card : ℝ) / n))
      atTop (𝓝 (1 : ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    rw [← add_div, ← add_div]
    have hc : (I 0 n a).card + ((I 1 n a).card + (I 2 n a).card : ℝ) = (n : ℝ) := by
      exact_mod_cast hcard n
    rw [hc, div_self (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))]
  have heq := tendsto_nhds_unique hsum hone
  simpa [Fin.sum_univ_succ] using heq

-- @node: fitted_cutoff_range
/-- If [the propensity function takes values between zero and one](hyp:hp), [the policy transformation is jointly measurable on unit-interval propensities and preserves that interval](hyp:hphi), and [the lower propensity endpoint at the chosen covariate value is positive](hyp:hlow), then [the smaller of one and the policy propensity divided by that endpoint lies between zero and one, and equals one whenever the policy propensity is at least that endpoint](goal). -/
lemma fitted_cutoff_range (phi : Z → X → ℝ → ℝ) (p : Z → X → ℝ) -- @realizes \hat\tau_i(cutoff lies in [0,1] on its positive-denominator domain and equals one above the boundary)
    (hp : ∀ z x, p z x ∈ Icc (0 : ℝ) 1) (hphi : IsPolicyMap phi)
    (z : Z) (x : X) (hlow : 0 < pLow p x) :
    min 1 (phi z x (p z x) / pLow p x) ∈ Icc (0 : ℝ) 1 ∧
    (pLow p x ≤ phi z x (p z x) → min 1 (phi z x (p z x) / pLow p x) = 1) := by
  have hq := hphi.2 z x _ (hp z x)
  refine ⟨⟨le_min zero_le_one (div_nonneg hq.1 hlow.le), min_le_left _ _⟩, ?_⟩
  intro hle
  exact min_eq_left ((le_div_iff₀ hlow).mpr (by simpa using hle))


end Papers.TbsPrteOptimalTransport

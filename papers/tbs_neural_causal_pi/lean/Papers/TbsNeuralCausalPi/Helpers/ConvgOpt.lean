module
public import Papers.TbsNeuralCausalPi.Setup.Optimization
public import Papers.TbsNeuralCausalPi.Setup.Assumptions.Auxiliary
/-! # Limits of constrained optimization values -/
public section
namespace Papers.TbsNeuralCausalPi
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
noncomputable section
attribute [local instance] Classical.propDecidable

variable {M : Type*} [MetricSpace M]

-- @node: convgOpt_constraint_lipschitz
/-- If the constraints are [approximately Lipschitz with constant Lg](hyp:Lg,hLip),
[uniformly approximate the limiting constraint with nonnegative approximating constraints](hyp:herror),
and [the approximation errors](hyp:hdelta) and [Lipschitz slacks](hyp:htau) converge to zero,
then [the limiting constraint is Lipschitz with constant Lg on S](goal). -/
lemma convgOpt_constraint_lipschitz (S : Set M) (gn : ℕ → M → ℝ)
    (g : M → ℝ) (delta tau : ℕ → ℝ) (Lg : ℝ≥0)
    (hLip : ApproxLipschitzConstraints S gn Lg tau)
    (herror : UniformConstraintError S gn g delta)
    (hdelta : Tendsto delta atTop (𝓝 0)) (htau : Tendsto tau atTop (𝓝 0)) :
    LipschitzOnWith Lg g S := by
  apply LipschitzOnWith.of_dist_le_mul
  intro a ha b hb
  have hbound : ∀ r, |g a - g b| ≤ Lg * dist a b + tau r + 2 * delta r := by
    intro r
    have h₁ := (abs_le.mp (herror.2 r a ha).1)
    have h₂ := (abs_le.mp (herror.2 r b hb).1)
    have h₃ := abs_le.mp (hLip r a ha b hb)
    apply abs_le.mpr
    constructor <;> linarith
  have ht : Tendsto (fun r => (Lg : ℝ) * dist a b + tau r + 2 * delta r)
      atTop (𝓝 ((Lg : ℝ) * dist a b)) := by
    simpa using (tendsto_const_nhds.add htau).add (tendsto_const_nhds.mul hdelta)
  simpa only [Real.dist_eq] using ge_of_tendsto' ht hbound

-- @node: convgOpt_constraint_nonneg
/-- If [nonnegative constraints uniformly approximate g on S](hyp:herror) and
[their error bounds converge to zero](hyp:hdelta), then [g is nonnegative throughout S](goal). -/
lemma convgOpt_constraint_nonneg (S : Set M) (gn : ℕ → M → ℝ)
    (g : M → ℝ) (delta : ℕ → ℝ)
    (herror : UniformConstraintError S gn g delta)
    (hdelta : Tendsto delta atTop (𝓝 0)) : ∀ a ∈ S, 0 ≤ g a := by
  intro a ha
  have hbound : ∀ r, -delta r ≤ g a := by
    intro r
    have h := herror.2 r a ha
    have hu := (abs_le.mp h.1).2
    linarith [h.2]
  exact le_of_tendsto' (by simpa using hdelta.neg) hbound

-- @node: convgOpt_recovery_sequence
/-- Suppose [every approximating parameter set lies in S](hyp:hTheta),
[g is Lipschitz on S with constant Lg](hyp:Lg,hLip),
[the nonnegative constraints uniformly approximate g](hyp:herror), and
[the compact subset T of S is approximable by these parameter sets within the given errors](hyp:happrox),
with [errors converging to zero](hyp:heps). For [a point in T](hyp:ha)
[where g vanishes](hyp:hga), [there is a sequence of feasible approximating points converging to that point](goal). -/
lemma convgOpt_recovery_sequence (Theta : ℕ → Set M) (S T : Set M)
    (gn : ℕ → M → ℝ) (g : M → ℝ) (eps delta : ℕ → ℝ) (Lg : ℝ≥0)
    (hTheta : ∀ r, Theta r ⊆ S) (hLip : LipschitzOnWith Lg g S)
    (herror : UniformConstraintError S gn g delta)
    (happrox : CompactSubsetApproximableAt Theta S T eps)
    (heps : Tendsto eps atTop (𝓝 0)) {a : M} (ha : a ∈ T) (hga : g a = 0) :
    ∃ x : ℕ → M, (∀ r, x r ∈ convgOptFeasible Theta gn Lg eps delta r) ∧
      Tendsto x atTop (𝓝 a) := by
  choose x hx hdist using fun r => happrox.2.2 r a ha
  refine ⟨x, ?_, ?_⟩
  · intro r
    refine ⟨hx r, ?_⟩
    have hg := hLip.dist_le_mul (x r) (hTheta r (hx r)) a (happrox.2.1 ha)
    rw [Real.dist_eq, hga, sub_zero] at hg
    have he := (abs_le.mp (herror.2 r (x r) (hTheta r (hx r))).1).2
    have hm := mul_le_mul_of_nonneg_left (hdist r) Lg.coe_nonneg
    linarith [le_abs_self (g (x r))]
  · apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero (fun r => dist_nonneg) hdist heps

-- @node: convgOpt_limsup_le_point
/-- Suppose [the approximating parameter sets lie in S](hyp:hTheta), [S is compact](hyp:hcompact),
[the objective is continuous on S](hyp:hf), [g is Lipschitz on S with constant Lg](hyp:Lg,hLip),
and [the nonnegative constraints uniformly approximate g](hyp:herror).
If [the compact subset T of S is approximable within the given errors](hyp:happrox)
and [those errors tend to zero](hyp:heps), then for [any point in T](hyp:ha)
[where g vanishes](hyp:hga), [the upper limit of the approximate optimal values is at most its objective value](goal). -/
lemma convgOpt_limsup_le_point (Theta : ℕ → Set M) (S T : Set M)
    (f g : M → ℝ) (gn : ℕ → M → ℝ) (eps delta : ℕ → ℝ) (Lg : ℝ≥0)
    (hTheta : ∀ r, Theta r ⊆ S) (hcompact : IsCompact S) (hf : ContinuousOn f S)
    (hLip : LipschitzOnWith Lg g S) (herror : UniformConstraintError S gn g delta)
    (happrox : CompactSubsetApproximableAt Theta S T eps)
    (heps : Tendsto eps atTop (𝓝 0)) {a : M} (ha : a ∈ T) (hga : g a = 0) :
    limsup (fun r => (convgOptValue f Theta gn Lg eps delta r : EReal)) atTop ≤
      (f a : EReal) := by
  obtain ⟨x, hx, hxt⟩ := convgOpt_recovery_sequence Theta S T gn g eps delta Lg
    hTheta hLip herror happrox heps ha hga
  have hbounded : ∀ r, BddBelow (f '' convgOptFeasible Theta gn Lg eps delta r) := by
    intro r
    exact (hcompact.bddBelow_image hf).mono (Set.image_mono (fun z hz => hTheta r hz.1))
  have hle : ∀ r, (convgOptValue f Theta gn Lg eps delta r : EReal) ≤ (f (x r) : EReal) := by
    intro r
    exact_mod_cast (csInf_le (hbounded r) (Set.mem_image_of_mem f (hx r)))
  have hft : Tendsto (fun r => (f (x r) : EReal)) atTop (𝓝 (f a : EReal)) :=
    continuous_coe_real_ereal.continuousAt.tendsto.comp
      ((hf a (happrox.2.1 ha)).tendsto.comp
        (tendsto_nhdsWithin_iff.mpr ⟨hxt, Filter.Eventually.of_forall
          (fun r => hTheta r (hx r).1)⟩))
  exact (limsup_le_limsup (Filter.Eventually.of_forall hle)).trans_eq hft.limsup_eq

-- @node: convgOpt_cluster_feasible
/-- If [g is continuous on S](hyp:hg) and [nonnegative there](hyp:hgnonneg),
[every point of a sequence belongs to S](hyp:hx), and [its constraint values are bounded above by beta](hyp:hbound)
with [beta converging to zero](hyp:hbeta), then at [a point of S](hyp:ha)
[to which the sequence converges](hyp:hxt), [g vanishes](goal). -/
lemma convgOpt_cluster_feasible (S : Set M) (g : M → ℝ) (x : ℕ → M)
    (beta : ℕ → ℝ) (hg : ContinuousOn g S) (hgnonneg : ∀ a ∈ S, 0 ≤ g a)
    (hx : ∀ r, x r ∈ S) (hbound : ∀ r, g (x r) ≤ beta r)
    (hbeta : Tendsto beta atTop (𝓝 0)) {a : M} (ha : a ∈ S)
    (hxt : Tendsto x atTop (𝓝 a)) : g a = 0 := by
  have hgt : Tendsto (fun r => g (x r)) atTop (𝓝 (g a)) :=
    (hg a ha).tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hxt, Filter.Eventually.of_forall hx⟩)
  have hz : Tendsto (fun r => g (x r)) atTop (𝓝 0) :=
    squeeze_zero (fun r => hgnonneg _ (hx r)) hbound hbeta
  exact tendsto_nhds_unique hgt hz

-- @node: convgOpt_eventually_lower
/-- Suppose [S is compact](hyp:hcompact), [the objective](hyp:hf) and [constraint](hyp:hg)
are continuous on S, [the constraint is nonnegative there](hyp:hgnonneg),
[a sequence stays in S](hyp:hx), and [its constraint values are bounded above by beta](hyp:hbound),
where [beta tends to zero](hyp:hbeta). For [any number strictly below the optimum subject to a zero constraint in S](hyp:hc),
[the sequence's objective values eventually exceed that number](goal). -/
lemma convgOpt_eventually_lower (S : Set M) (f g : M → ℝ) (x : ℕ → M)
    (beta : ℕ → ℝ) (hcompact : IsCompact S) (hf : ContinuousOn f S)
    (hg : ContinuousOn g S) (hgnonneg : ∀ a ∈ S, 0 ≤ g a)
    (hx : ∀ r, x r ∈ S) (hbound : ∀ r, g (x r) ≤ beta r)
    (hbeta : Tendsto beta atTop (𝓝 0)) {c : ℝ}
    (hc : c < convgOptLimitValue f S g) : ∀ᶠ r in atTop, c < f (x r) := by
  by_contra h
  have hfreq : ∃ᶠ r in atTop, f (x r) ≤ c := by
    simpa only [Filter.Frequently, not_le] using h
  obtain ⟨s, hs, hbad⟩ := extraction_of_frequently_atTop hfreq
  obtain ⟨a, ha, t, ht, hxt⟩ := hcompact.tendsto_subseq (fun r => hx (s r))
  have hst : Tendsto (s ∘ t) atTop atTop := hs.tendsto_atTop.comp ht.tendsto_atTop
  have hga : g a = 0 := convgOpt_cluster_feasible S g (x ∘ (s ∘ t))
    (beta ∘ (s ∘ t)) hg hgnonneg (fun r => hx _) (fun r => hbound _)
    (hbeta.comp hst) ha hxt
  have hft : Tendsto (fun r => f (x (s (t r)))) atTop (𝓝 (f a)) :=
    (hf a ha).tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hxt, Filter.Eventually.of_forall (fun r => hx _)⟩)
  have hfac : f a ≤ c := le_of_tendsto' hft (fun r => hbad (t r))
  have hbdd : BddBelow (f '' convgOptFeasibleInf S g) :=
    (hcompact.bddBelow_image hf).mono (Set.image_mono (fun z hz => hz.1))
  have hmin : convgOptLimitValue f S g ≤ f a :=
    csInf_le hbdd (Set.mem_image_of_mem f ⟨ha, hga⟩)
  exact (not_lt_of_ge (hmin.trans hfac)) hc

-- @node: convgOpt_le_liminf_sequence
/-- If [S is compact](hyp:hcompact), [the objective](hyp:hf) and [constraint](hyp:hg)
are continuous on S, [the constraint is nonnegative on S](hyp:hgnonneg),
[a sequence stays in S](hyp:hx), and [its constraint values are bounded above by beta](hyp:hbound)
with [beta tending to zero](hyp:hbeta), then [the optimum subject to a zero constraint in S is at most the lower limit of the sequence's objective values](goal). -/
lemma convgOpt_le_liminf_sequence (S : Set M) (f g : M → ℝ) (x : ℕ → M)
    (beta : ℕ → ℝ) (hcompact : IsCompact S) (hf : ContinuousOn f S)
    (hg : ContinuousOn g S) (hgnonneg : ∀ a ∈ S, 0 ≤ g a)
    (hx : ∀ r, x r ∈ S) (hbound : ∀ r, g (x r) ≤ beta r)
    (hbeta : Tendsto beta atTop (𝓝 0)) :
    (convgOptLimitValue f S g : EReal) ≤ liminf (fun r => (f (x r) : EReal)) atTop := by
  apply (le_liminf_iff).mpr
  intro y hy
  induction y using EReal.rec with
  | bot => exact Filter.Eventually.of_forall (fun r => by simp)
  | top => exact False.elim (not_lt_of_ge le_top hy)
  | coe c =>
    have hc : c < convgOptLimitValue f S g := by exact_mod_cast hy
    filter_upwards [convgOpt_eventually_lower S f g x beta hcompact hf hg
      hgnonneg hx hbound hbeta hc] with r hr
    exact_mod_cast hr

-- @node: prop:convg-opt
/-- Under [nested approximation sets, vanishing positive error schedules, and continuous objectives and constraints](hyp:hsetting),
[compactness of the limiting parameter set](hyp:hcompact),
[approximate Lipschitz bounds with constant Lg](hyp:Lg,hLip),
[uniform approximation of the limiting constraint by nonnegative constraints](hyp:herror),
[approximation of a compact comparison subset](hyp:happrox),
[nonempty zero-constraint sets in both limiting sets](hyp:hnonempty), and
[attainment of each finite optimum](hyp:hattain),
[the lower limit of the finite optimal values is bounded below by the optimum on the full limiting set, and their upper limit is bounded above by the optimum on the comparison subset](goal). -/
lemma convgOpt_limits_mem (Theta : ℕ → Set M) (ThetaInf tildeTheta : Set M)
    (eps delta tau : ℕ → ℝ) (f g : M → ℝ) (gn : ℕ → M → ℝ) (Lg : ℝ≥0)
    (hsetting : ConvgOptSetting Theta ThetaInf eps delta tau f gn)
    (hcompact : ThetaInfCompact ThetaInf)
    (hLip : ApproxLipschitzConstraints ThetaInf gn Lg tau)
    (herror : UniformConstraintError ThetaInf gn g delta)
    (happrox : CompactSubsetApproximableAt Theta ThetaInf tildeTheta eps)
    (hnonempty : LimitFeasibleNonempty ThetaInf tildeTheta g)
    (hattain : FiniteProblemsAttained Theta gn Lg eps delta f) :
    (convgOptLimitValue f ThetaInf g : EReal) ≤
      liminf (fun r => (convgOptValue f Theta gn Lg eps delta r : EReal)) atTop ∧
    limsup (fun r => (convgOptValue f Theta gn Lg eps delta r : EReal)) atTop ≤
      (convgOptLimitValue f tildeTheta g : EReal) := by
  rcases hsetting with ⟨hnested, hclosure, hpos, heps, hdelta, htau, hf, hgn⟩
  have hTheta : ∀ r, Theta r ⊆ ThetaInf :=
    fun r => (hnested r).1.trans (hnested r).2
  have hg := convgOpt_constraint_lipschitz ThetaInf gn g delta tau Lg hLip herror hdelta htau
  have hgnonneg := convgOpt_constraint_nonneg ThetaInf gn g delta herror hdelta
  constructor
  · choose x hx hmin using hattain
    have hval : ∀ r, convgOptValue f Theta gn Lg eps delta r = f (x r) := by
      intro r
      exact (hmin r).isGLB (hx r) |>.csInf_eq ⟨f (x r), Set.mem_image_of_mem f (hx r)⟩
    have hxS : ∀ r, x r ∈ ThetaInf := fun r => hTheta r (hx r).1
    have hbound : ∀ r, g (x r) ≤ (Lg : ℝ) * eps r + 2 * delta r := by
      intro r
      have he := (abs_le.mp (herror.2 r (x r) (hxS r)).1).1
      linarith [(hx r).2]
    have hbeta : Tendsto (fun r => (Lg : ℝ) * eps r + 2 * delta r) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul heps).add (tendsto_const_nhds.mul hdelta)
    simp_rw [hval]
    exact convgOpt_le_liminf_sequence ThetaInf f g x
      (fun r => (Lg : ℝ) * eps r + 2 * delta r) hcompact hf hg.continuousOn
      hgnonneg hxS hbound hbeta
  · have hgT : ContinuousOn g tildeTheta := hg.continuousOn.mono happrox.2.1
    have hclosed : IsClosed (convgOptFeasibleInf tildeTheta g) :=
      happrox.1.isClosed.isClosed_eq hgT continuousOn_const
    have hcompactT : IsCompact (convgOptFeasibleInf tildeTheta g) :=
      happrox.1.of_isClosed_subset hclosed (fun a ha => ha.1)
    obtain ⟨a, ha, hmin⟩ := hcompactT.exists_isMinOn hnonempty.2
      (hf.mono (fun a ha => happrox.2.1 ha.1))
    have hval : convgOptLimitValue f tildeTheta g = f a :=
      hmin.isGLB ha |>.csInf_eq ⟨f a, Set.mem_image_of_mem f ha⟩
    rw [hval]
    exact convgOpt_limsup_le_point Theta ThetaInf tildeTheta f g gn eps delta Lg
      hTheta hcompact hf hg herror happrox heps ha.1 ha.2

-- @node: convgOpt_limits_mem_of_proj
/-- Given [projections from each finite parameter space to the limiting space](hyp:p)
and [a real-valued constraint on each finite parameter space](hyp:cn),
suppose [the limiting parameter set is compact](hyp:hcompact), [the objective is continuous there](hyp:hf),
[the limiting constraint is Lipschitz with constant Lg](hyp:Lg,hg) and [nonnegative there](hyp:hgnonneg),
[all projected parameters belong to that set](hyp:hp), and
[finite constraints approximate the constraint at each projection within delta](hyp:herror).
If [the comparison point belongs to the limiting set and has zero constraint](hyp:htheta),
[it can be approximated by projections within eps](hyp:happrox),
[eps and delta are nonnegative and the finite tolerance covers their Lipschitz error](hyp:hpos),
and [eps](hyp:heps), [delta](hyp:hdelta), and [the finite tolerance](hyp:halpha) tend to zero,
then [the lower limit of finite infima is at least the limiting zero-constraint optimum, and their upper limit is at most the comparison point's objective value](goal). -/
lemma convgOpt_limits_mem_of_proj (R : ℕ → Type*) (p : ∀ r, R r → M)
    (ThetaInf : Set M) (f g : M → ℝ) (cn : ∀ r, R r → ℝ)
    (eps delta alpha : ℕ → ℝ) (Lg : ℝ≥0) (theta : M)
    (hcompact : IsCompact ThetaInf) (hf : ContinuousOn f ThetaInf)
    (hg : LipschitzOnWith Lg g ThetaInf) (hgnonneg : ∀ a ∈ ThetaInf, 0 ≤ g a)
    (hp : ∀ r x, p r x ∈ ThetaInf)
    (herror : ∀ r x, |cn r x-g (p r x)| ≤ delta r)
    (htheta : theta ∈ ThetaInf ∧ g theta = 0)
    (happrox : ∀ r, ∃ x : R r, dist (p r x) theta ≤ eps r)
    (hpos : ∀ r, 0 ≤ eps r ∧ 0 ≤ delta r ∧ Lg * eps r + delta r ≤ alpha r)
    (heps : Tendsto eps atTop (𝓝 0)) (hdelta : Tendsto delta atTop (𝓝 0))
    (halpha : Tendsto alpha atTop (𝓝 0)) :
    ((sInf (f '' {a ∈ ThetaInf | g a = 0}) : ℝ) : EReal) ≤
      liminf (fun r => ⨅ x : R r, ⨅ (_h : cn r x ≤ alpha r), (f (p r x) : EReal)) atTop ∧
    limsup (fun r => ⨅ x : R r, ⨅ (_h : cn r x ≤ alpha r), (f (p r x) : EReal)) atTop ≤
      (f theta : EReal) := by
  choose x hx using happrox
  have hxFeas : ∀ r, cn r (x r) ≤ alpha r := by
    intro r
    have hlip := hg.dist_le_mul (p r (x r)) (hp r (x r)) theta htheta.1
    rw [Real.dist_eq, htheta.2, sub_zero] at hlip
    have he := (abs_le.mp (herror r (x r))).2
    have hm := mul_le_mul_of_nonneg_left (hx r) Lg.coe_nonneg
    linarith [(hpos r).2.2, le_abs_self (g (p r (x r)))]
  have hgBound : ∀ r y, cn r y ≤ alpha r → g (p r y) ≤ alpha r + delta r := by
    intro r y hy
    have he := (abs_le.mp (herror r y)).1
    linarith
  constructor
  · have hminExists : ∀ r, ∃ a ∈ {a ∈ ThetaInf | g a ≤ alpha r + delta r},
        IsMinOn f {a ∈ ThetaInf | g a ≤ alpha r + delta r} a := by
      intro r
      have hclosed : IsClosed {a ∈ ThetaInf | g a ≤ alpha r + delta r} :=
        hcompact.isClosed.isClosed_le hg.continuousOn continuousOn_const
      have hc : IsCompact {a ∈ ThetaInf | g a ≤ alpha r + delta r} :=
        hcompact.of_isClosed_subset hclosed (fun a ha => ha.1)
      exact hc.exists_isMinOn ⟨p r (x r), hp r (x r), hgBound r (x r) (hxFeas r)⟩
        (hf.mono (fun a ha => ha.1))
    choose z hz hmin using hminExists
    have hzlim := convgOpt_le_liminf_sequence ThetaInf f g z (fun r => alpha r + delta r)
      hcompact hf hg.continuousOn hgnonneg (fun r => (hz r).1) (fun r => (hz r).2)
      (by simpa using halpha.add hdelta)
    refine hzlim.trans (liminf_le_liminf (Filter.Eventually.of_forall ?_))
    intro r
    refine le_iInf (fun y => le_iInf (fun hy => ?_))
    exact_mod_cast hmin r ⟨hp r y, hgBound r y hy⟩
  · have hxt : Tendsto (fun r => p r (x r)) atTop (𝓝 theta) :=
      tendsto_iff_dist_tendsto_zero.mpr (squeeze_zero (fun r => dist_nonneg) hx heps)
    have hft : Tendsto (fun r => (f (p r (x r)) : EReal)) atTop (𝓝 (f theta : EReal)) :=
      continuous_coe_real_ereal.continuousAt.tendsto.comp
        ((hf theta htheta.1).tendsto.comp (tendsto_nhdsWithin_iff.mpr
          ⟨hxt, Filter.Eventually.of_forall (fun r => hp r (x r))⟩))
    refine (limsup_le_limsup (Filter.Eventually.of_forall (fun r => ?_))).trans_eq hft.limsup_eq
    exact iInf_le_of_le (x r) (iInf_le_of_le (hxFeas r) le_rfl)

end
end Papers.TbsNeuralCausalPi

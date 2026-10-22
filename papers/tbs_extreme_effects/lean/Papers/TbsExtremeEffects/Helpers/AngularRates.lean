module
public import Papers.TbsExtremeEffects.Helpers.ProductBounds

/-! The literal angular specialization of both fixed-threshold displays. -/

@[expose] public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory
noncomputable section
variable {q d : ℕ} {M : ExtremeModel q d}

/-- The [angular term](goal) for a [model](hyp:M), [tail parameters](hyp:tp), [angular-rate constant](hyp:CW), [logarithmic exponent](hyp:k), and [threshold](hyp:t) is `2L` times the displayed two-term rate. -/
def angularTerm (M : ExtremeModel q d) (tp : TailParams) (CW k t : ℝ) : ℝ :=
  2 * M.L * CW * ((Real.log t) ^ k * t ^ (-min 1 M.beta) +
    t ^ (-(M.beta * tp.s / (1 - 2 * tp.s))))

/-- For [a model](hyp:M) with [tail parameters](hyp:tp) under [asymptotic homogeneity](hyp:hHom), and for [a rate constant](hyp:CW), [a logarithmic exponent](hyp:k) and [a starting threshold](hyp:tW): [if the angular Wasserstein distance obeys the displayed two-term rate from the starting threshold onward, then at every threshold no smaller than it the angular error multiplied by `2L` is bounded by `2L` times that rate](goal). -/
-- @node: angular_term_le
lemma angular_term_le (M : ExtremeModel q d) (tp : TailParams)
    (hHom : AsymptoticHomogeneity M) (CW k tW : ℝ) :
    AngularRateBound M tp CW k tW → ∀ t, tW ≤ t →
      2 * M.L * angularW1 M t ≤
        2 * M.L * CW * (Real.log t) ^ k * t ^ (-min 1 M.beta) +
        2 * M.L * CW * t ^ (-(M.beta * tp.s / (1 - 2 * tp.s))) := by
  intro hAngular t ht
  have hL : 0 ≤ M.L := hHom.2.2.2.1
  have h := mul_le_mul_of_nonneg_left (hAngular.2.2.2 t ht)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hL)
  convert h using 1 <;> first | rfl | ring

-- @node: angular_term_bound
/-- Given [asymptotic homogeneity](hyp:hHom), an [angular Wasserstein rate bound](hyp:hAngular), and a [threshold beyond its starting point](hyp:ht), the [scaled angular error is bounded by the angular term](goal). -/
lemma angular_term_bound (M : ExtremeModel q d) (tp : TailParams)
    (hHom : AsymptoticHomogeneity M) {CW k tW t : ℝ}
    (hAngular : AngularRateBound M tp CW k tW) (ht : tW ≤ t) :
    2 * M.L * angularW1 M t ≤ angularTerm M tp CW k t := by
  have h := angular_term_le M tp hHom CW k tW hAngular t ht
  unfold angularTerm
  convert h using 1 <;> first | rfl | ring

/-- The [first-factor error rate with angular control](goal) for a [model](hyp:M), [experiment](hyp:E), [estimator kind](hyp:kind), [tail parameters](hyp:tp), [rate constants](hyp:CW,k,c,Cgb,a0), [nuisance-rate functions](hyp:Rp,Rg,Ralpha), [sample size](hyp:n), [threshold and confidence level](hyp:t,delta), [envelope](hyp:B), and [sample point](hyp:w) first [sets the tail-index rate](step:1), then [sets the combined outcome bound](step:2), and [forms the displayed sum](step:3). -/
def rateFirstFactorErrorAngular (E : NeteExperiment M) (kind : EstimatorKind)
    (tp : TailParams) (CW k c Cgb a0 : ℝ) (Rp Rg Ralpha : ℕ → ℝ → ℝ)
    (n : ℕ) (t delta : ℝ) (B : E.Om → ℝ) (w : E.Om) : ℝ :=
  let a := Ralpha n (delta / 12)
  let Gt := Cgb + eBar M t
  rateSamplingError E kind n t delta B w +
    (match kind with
     | .dr => (2 / c) * Rp (n / 2) (delta / 12) * Rg (trainCount E n t w) (delta / 12)
     | .ipw => (2 * Gt / c) * Rp (n / 2) (delta / 12)) +
    2 * eBar M t + angularTerm M tp CW k t +
    (2 * Gt / c) * (t ^ a - 1 + (4 / (M.beta - a0)) * a * t ^ a)

/-- The [simplified angular error rate](goal) for a [model](hyp:M), [experiment](hyp:E), [estimator kind](hyp:kind), [tail parameters](hyp:tp), [rate constants](hyp:CW,k,V,Cg,delta), [nuisance-rate functions](hyp:Rp,Rg,Ralpha), [sample size](hyp:n), [threshold](hyp:t), and [sample point](hyp:w) is the displayed reduced bound. -/
def simplifiedRateAngular (E : NeteExperiment M) (kind : EstimatorKind)
    (tp : TailParams) (CW k V Cg delta : ℝ) (Rp Rg Ralpha : ℕ → ℝ → ℝ) (n : ℕ) (t : ℝ) (w : E.Om) :=
  Real.sqrt (V / (delta * n * tailProb M t)) +
  (match kind with
    | .dr => Rp (n / 2) (delta / 12) * Rg (trainCount E n t w) (delta / 12)
    | .ipw => Rp (n / 2) (delta / 12)) +
  eBar M t + angularTerm M tp CW k t + Ralpha n (delta / 12) * Real.log t +
    hillErrorBound M Cg delta n

/-- The [angular product-success event](goal) for a [model](hyp:M), [experiment](hyp:E), [tail parameters](hyp:tp), [constants](hyp:CW,k,c,Cgb,a0,C,Cg,V,delta), [nuisance-rate functions](hyp:Rp,Rg,Ralpha), [sample size](hyp:n), [threshold](hyp:t), [two envelopes](hyp:Bdr,Bipw), and [sample point](hyp:w) requires: [enough tail observations](step:1), [the doubly robust error bound](step:2), [the inverse-probability-weighted error bound](step:3), and [the conditional simplified bounds](step:4). -/
def ProductSuccessAngular (E : NeteExperiment M)
    (tp : TailParams) (CW k c Cgb a0 C Cg V delta : ℝ) (Rp Rg Ralpha : ℕ → ℝ → ℝ)
    (n : ℕ) (t : ℝ) (Bdr Bipw : E.Om → ℝ) (w : E.Om) : Prop :=
  (n : ℝ) * tailProb M t / 4 ≤ evalCount E n t w ∧
  (|thetaHatDR E n t (delta / 6) w - thetaNETE M| ≤
    |muHat E n (delta / 6) w| *
      rateFirstFactorErrorAngular E .dr tp CW k c Cgb a0 Rp Rg Ralpha n t delta Bdr w +
      |etaTarget M| * radialError E Cg delta Ralpha n w) ∧
  (|thetaHatIPW E n t (delta / 6) w - thetaNETE M| ≤
    |muHat E n (delta / 6) w| *
      rateFirstFactorErrorAngular E .ipw tp CW k c Cgb a0 Rp Rg Ralpha n t delta Bipw w +
      |etaTarget M| * radialError E Cg delta Ralpha n w) ∧
  (secondMomentsOnNuisance E n t (delta / 12) Rp Rg Ralpha V → Real.exp 1 ≤ t →
    Ralpha n (delta / 12) * Real.log t ≤ 1 →
    radialQ M Cg delta Ralpha n ≤ radialH M / 2 →
      (|thetaHatDR E n t (delta / 6) w - thetaNETE M| ≤
        C * simplifiedRateAngular E .dr tp CW k V Cg delta Rp Rg Ralpha n t w) ∧
      (|thetaHatIPW E n t (delta / 6) w - thetaNETE M| ≤
        C * simplifiedRateAngular E .ipw tp CW k V Cg delta Rp Rg Ralpha n t w))

/-- If [the leading constant is positive](hyp:hC), [the angular error has its angular-term bound](hyp:hAngular), and [the original product-success event holds](hyp:h), then the [angular product-success event holds on the same sample](goal). -/
-- @node: productSuccess_angular
lemma productSuccess_angular (E : NeteExperiment M) (tp : TailParams)
    (CW k c Cgb a0 C Cg V delta : ℝ) (Rp Rg Ralpha : ℕ → ℝ → ℝ)
    (n : ℕ) (t : ℝ) (Bdr Bipw : E.Om → ℝ) (w : E.Om)
    (hC : 0 < C) (hAngular : 2 * M.L * angularW1 M t ≤ angularTerm M tp CW k t)
    (h : ProductSuccess E c Cgb a0 C Cg V delta Rp Rg Ralpha n t Bdr Bipw w) :
    ProductSuccessAngular E tp CW k c Cgb a0 C Cg V delta Rp Rg Ralpha
      n t Bdr Bipw w := by
  have hFirst (kind : EstimatorKind) (B : E.Om → ℝ) :
      rateFirstFactorError E kind c Cgb a0 Rp Rg Ralpha n t delta B w ≤
        rateFirstFactorErrorAngular E kind tp CW k c Cgb a0 Rp Rg Ralpha
          n t delta B w := by
    unfold rateFirstFactorError rateFirstFactorErrorAngular etaRemainder
    dsimp only
    cases kind <;> dsimp only <;> linarith only [hAngular]
  have hSimple (kind : EstimatorKind) :
      simplifiedRate E kind V Cg delta Rp Rg Ralpha n t w ≤
        simplifiedRateAngular E kind tp CW k V Cg delta Rp Rg Ralpha n t w := by
    unfold simplifiedRate simplifiedRateAngular
    cases kind <;> dsimp only <;> linarith only [hAngular]
  refine ⟨h.1, h.2.1.trans ?_, h.2.2.1.trans ?_, ?_⟩
  · exact add_le_add (mul_le_mul_of_nonneg_left (hFirst .dr Bdr) (abs_nonneg _)) (le_refl _)
  · exact add_le_add (mul_le_mul_of_nonneg_left (hFirst .ipw Bipw) (abs_nonneg _)) (le_refl _)
  · intro hMom ht ha hQ
    obtain ⟨hDR, hIPW⟩ := h.2.2.2 hMom ht ha hQ
    exact ⟨hDR.trans (mul_le_mul_of_nonneg_left (hSimple .dr) hC.le),
      hIPW.trans (mul_le_mul_of_nonneg_left (hSimple .ipw) hC.le)⟩

end
end Papers.TbsExtremeEffects

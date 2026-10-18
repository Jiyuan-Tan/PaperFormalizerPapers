module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLBinaryBranchRates
/-! Bounded fitted product weights preserve the binary hinge's quadratic bias.
The remainder retains the fitted active indicators, including fitted ties. -/
public section

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Filter
open scoped Topology

-- @node: binary_hinge_weighted_component_energy_bound
/-- Suppose [the separation constant is positive](hyp:hc), [the weight bound is nonnegative](hyp:hW), [the reference upper endpoint is measurable](hyp:hq), [the reference lower endpoint is measurable](hyp:hl), [the reference boundary is measurable](hyp:hb), [the fitted upper endpoint is measurable](hyp:hqh), [the fitted lower endpoint is measurable](hyp:hlh), and [the fitted boundary is measurable](hyp:hbh). If [the weight is measurable](hyp:hw), [its absolute value is almost everywhere bounded by the weight bound](hyp:hwb), [the upper-endpoint error has a finite second moment](hyp:heq), [the lower-endpoint error has a finite second moment](hyp:hel), [the boundary error has a finite second moment](hyp:heb), and [the reference endpoint gap and both absolute boundary-to-endpoint gaps are at least the separation constant almost everywhere](hyp:hgap), [the weighted fitted binary hinge remainder is integrable and its absolute mean is at most 78 times the weight bound divided by the separation constant times the sum of the three integrated squared errors](goal). -/
lemma binary_hinge_weighted_component_energy_bound {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (q l b qh lh bh w : X → ℝ) (c W : ℝ)
    (hc : 0 < c) (hW : 0 ≤ W)
    (hq : Measurable q) (hl : Measurable l) (hb : Measurable b)
    (hqh : Measurable qh) (hlh : Measurable lh) (hbh : Measurable bh)
    (hw : Measurable w) (hwb : ∀ᵐ x ∂ν, ‖w x‖ ≤ W)
    (heq : MemLp (fun x => qh x - q x) 2 ν)
    (hel : MemLp (fun x => lh x - l x) 2 ν)
    (heb : MemLp (fun x => bh x - b x) 2 ν)
    (hgap : ∀ᵐ x ∂ν, c ≤ q x - l x ∧ c ≤ |b x - l x| ∧ c ≤ |b x - q x|) :
    Integrable (fun x => w x * binaryFittedHingeRemainder
      (q x) (l x) (b x) (qh x) (lh x) (bh x)) ν ∧
    |∫ x, w x * binaryFittedHingeRemainder
      (q x) (l x) (b x) (qh x) (lh x) (bh x) ∂ν| ≤
      (78 * W / c) * ((∫ x, (qh x - q x) ^ 2 ∂ν) +
        (∫ x, (lh x - l x) ^ 2 ∂ν) + ∫ x, (bh x - b x) ^ 2 ∂ν) := by
  let R := fun x => binaryFittedHingeRemainder
    (q x) (l x) (b x) (qh x) (lh x) (bh x)
  let E := fun x => |qh x - q x| + |lh x - l x| + |bh x - b x|
  obtain ⟨he, henergy⟩ := integral_sq_abs_sum_three_le ν _ _ _ heq hel heb
  have hi : Integrable R ν :=
    (binary_hinge_component_energy_bound ν q l b qh lh bh c hc
      hq hl hb hqh hlh hbh heq hel heb hgap).1
  have hiw : Integrable (fun x => w x * R x) ν := hi.bdd_mul hw.aestronglyMeasurable hwb
  have hid : Integrable (fun x => (W * (26 / c)) * E x ^ 2) ν :=
    he.integrable_sq.const_mul _
  have hbound : ∀ᵐ x ∂ν, |w x * R x| ≤ (W * (26 / c)) * E x ^ 2 := by
    filter_upwards [hgap, hwb] with x hg hwx
    have hqE : |qh x - q x| ≤ E x := by
      dsimp only [E]
      linarith [abs_nonneg (qh x - q x), abs_nonneg (lh x - l x), abs_nonneg (bh x - b x)]
    have hlE : |lh x - l x| ≤ E x := by
      dsimp only [E]
      linarith [abs_nonneg (qh x - q x), abs_nonneg (lh x - l x), abs_nonneg (bh x - b x)]
    have hbE : |bh x - b x| ≤ E x := by
      dsimp only [E]
      linarith [abs_nonneg (qh x - q x), abs_nonneg (lh x - l x), abs_nonneg (bh x - b x)]
    have hR : |R x| ≤ (26 / c) * E x ^ 2 := by
      simpa only [R, binaryFittedHingeRemainder, add_sub_cancel] using
        binary_hinge_fitted_score_remainder hc hg.1 hg.2.1 hg.2.2 hqE hlE hbE
    rw [abs_mul]
    calc
      _ ≤ W * ((26 / c) * E x ^ 2) :=
        mul_le_mul (by simpa only [Real.norm_eq_abs] using hwx) hR (abs_nonneg _) hW
      _ = _ := by ring
  refine ⟨hiw, ?_⟩
  calc
    _ ≤ ∫ x, |w x * R x| ∂ν := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x => w x * R x)
    _ ≤ ∫ x, (W * (26 / c)) * E x ^ 2 ∂ν := integral_mono_ae hiw.abs hid hbound
    _ = (W * (26 / c)) * ∫ x, E x ^ 2 ∂ν := integral_const_mul _ _
    _ ≤ (W * (26 / c)) * (3 * ((∫ x, (qh x - q x) ^ 2 ∂ν) +
        (∫ x, (lh x - l x) ^ 2 ∂ν) + ∫ x, (bh x - b x) ^ 2 ∂ν)) :=
      mul_le_mul_of_nonneg_left henergy (by positivity)
    _ = _ := by ring

-- A changing fitted weight is allowed: only its known clipping range enters.
-- @node: binary_hinge_weighted_root_n_negligible
/-- Suppose [the separation constant is positive](hyp:hc), [the weight bound is nonnegative](hyp:hW), [the reference upper endpoint is measurable](hyp:hq), [the reference lower endpoint is measurable](hyp:hl), [the reference boundary is measurable](hyp:hb), [every fitted upper endpoint is measurable](hyp:hqh), [every fitted lower endpoint is measurable](hyp:hlh), [every fitted boundary is measurable](hyp:hbh), [every fitted weight is measurable](hyp:hw), and [the fitted weights are uniformly bounded in absolute value almost everywhere](hyp:hwb). If [every upper-endpoint error has a finite second moment](hyp:heq), [every lower-endpoint error has a finite second moment](hyp:hel), [every boundary error has a finite second moment](hyp:heb), [the reference endpoint gap and both absolute boundary-to-endpoint gaps are bounded below by the separation constant almost everywhere](hyp:hgap), and [the upper-endpoint, lower-endpoint, and boundary L2 errors are each negligible in probability relative to the inverse fourth root of twice the half-sample size](hyp:hrq,hrl,hrb), [the weighted fitted binary hinge remainder mean multiplied by the square root of the half-sample size converges to zero in probability](goal). -/
lemma binary_hinge_weighted_root_n_negligible {A X : Type*}
    [MeasurableSpace A] [MeasurableSpace X] (μ : Measure A) (ν : Measure X)
    (q l b : X → ℝ) (qh lh bh w : ℕ → A → X → ℝ) (c W : ℝ)
    (hc : 0 < c) (hW : 0 ≤ W)
    (hq : Measurable q) (hl : Measurable l) (hb : Measurable b)
    (hqh : ∀ n a, Measurable (qh n a)) (hlh : ∀ n a, Measurable (lh n a))
    (hbh : ∀ n a, Measurable (bh n a)) (hw : ∀ n a, Measurable (w n a))
    (hwb : ∀ n a, ∀ᵐ x ∂ν, ‖w n a x‖ ≤ W)
    (heq : ∀ n a, MemLp (fun x => qh n a x - q x) 2 ν)
    (hel : ∀ n a, MemLp (fun x => lh n a x - l x) 2 ν)
    (heb : ∀ n a, MemLp (fun x => bh n a x - b x) 2 ν)
    (hgap : ∀ᵐ x ∂ν, c ≤ q x - l x ∧ c ≤ |b x - l x| ∧ c ≤ |b x - q x|)
    (hrq : Causalean.Stat.IsLittleOp
      (fun n a => Real.sqrt (∫ x, (qh n a x - q x) ^ 2 ∂ν))
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ)) μ)
    (hrl : Causalean.Stat.IsLittleOp
      (fun n a => Real.sqrt (∫ x, (lh n a x - l x) ^ 2 ∂ν))
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ)) μ)
    (hrb : Causalean.Stat.IsLittleOp
      (fun n a => Real.sqrt (∫ x, (bh n a x - b x) ^ 2 ∂ν))
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ)) μ) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n + 1 : ℕ) : ℝ) * ∫ x, w n a x *
        binaryFittedHingeRemainder (q x) (l x) (b x)
          (qh n a x) (lh n a x) (bh n a x) ∂ν) atTop (fun _ _ => 0) := by
  have he := dml_three_component_energies_isLittleOp μ ν
    (fun n a x => qh n a x - q x) (fun n a x => lh n a x - l x)
    (fun n a x => bh n a x - b x) hrq hrl hrb
  apply dml_root_n_bias_tendsto_probability
  apply Causalean.Stat.IsLittleOp.of_abs_le_const_mul
    (by positivity : 0 < 78 * W / c + 1) he
  intro n a
  have hbnd := (binary_hinge_weighted_component_energy_bound ν q l b
    (qh n a) (lh n a) (bh n a) (w n a) c W hc hW hq hl hb
    (hqh n a) (hlh n a) (hbh n a) (hw n a) (hwb n a)
    (heq n a) (hel n a) (heb n a) hgap).2
  apply hbnd.trans
  have hE : 0 ≤ (∫ x, (qh n a x - q x) ^ 2 ∂ν) +
      (∫ x, (lh n a x - l x) ^ 2 ∂ν) + ∫ x, (bh n a x - b x) ^ 2 ∂ν := by
    positivity
  rw [abs_of_nonneg hE]
  exact mul_le_mul_of_nonneg_right (by linarith) hE

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]

-- The weight is the fitted regular-interval product coefficient. Its
-- measurability and unit bound follow from the nuisance clipping predicate.
-- @node: hMinus_fitted_product_remainder_energy_bound
/-- Suppose [the fitted binary nuisances are admissible](hyp:he1), [the separation constant is positive](hyp:hc), [the reference pooled upper policy level is measurable](hyp:hq0), [the reference pooled lower policy level is measurable](hyp:hl0), [the reference treatment-minus-success-increment boundary is measurable](hyp:hb0), [the fitted pooled upper policy level is measurable](hyp:hq1), [the fitted pooled lower policy level is measurable](hyp:hl1), and [the fitted treatment-minus-success-increment boundary is measurable](hyp:hb1). If [the upper-level error has a finite second moment](hyp:heq), [the lower-level error has a finite second moment](hyp:hel), [the boundary error has a finite second moment](hyp:heb), and [the reference policy-level gap and both absolute boundary-to-policy-level gaps are at least the separation constant almost everywhere](hyp:hgap), [the lower hinge change minus its affine correction using fitted active, boundary, and dominance indicators, multiplied by the fitted regular weight, is integrable and has absolute mean at most 78 divided by the separation constant times the sum of those three integrated squared errors](goal). -/
lemma hMinus_fitted_product_remainder_energy_bound (M : LatentIVModel Ω X Z)
    (phi : Z → X → ℝ → ℝ) (L : LevelData Z X) (e0 e1 : NuisanceBin L)
    (he1 : BinAdmissible M L e1) (k j : ℕ) (c : ℝ) (hc : 0 < c)
    (hq0 : Measurable (pooledQBin phi L e0 k j))
    (hl0 : Measurable (pooledQBin phi L e0 k (j - 1)))
    (hb0 : Measurable (fun x => positiveValue e0.pLev (k + 1) x - binFullJ L e0 k x))
    (hq1 : Measurable (pooledQBin phi L e1 k j))
    (hl1 : Measurable (pooledQBin phi L e1 k (j - 1)))
    (hb1 : Measurable (fun x => positiveValue e1.pLev (k + 1) x - binFullJ L e1 k x))
    (heq : MemLp (fun x => pooledQBin phi L e1 k j x - pooledQBin phi L e0 k j x)
      2 (xLaw M))
    (hel : MemLp (fun x => pooledQBin phi L e1 k (j - 1) x -
      pooledQBin phi L e0 k (j - 1) x) 2 (xLaw M))
    (heb : MemLp (fun x => (positiveValue e1.pLev (k + 1) x - binFullJ L e1 k x) -
      (positiveValue e0.pLev (k + 1) x - binFullJ L e0 k x)) 2 (xLaw M))
    (hgap : ∀ᵐ x ∂xLaw M,
      c ≤ pooledQBin phi L e0 k j x - pooledQBin phi L e0 k (j - 1) x ∧
      c ≤ |positiveValue e0.pLev (k + 1) x - binFullJ L e0 k x -
        pooledQBin phi L e0 k (j - 1) x| ∧
      c ≤ |positiveValue e0.pLev (k + 1) x - binFullJ L e0 k x -
        pooledQBin phi L e0 k j x|) :
    let R := fun x => hMinus phi L e1 k j x - hMinus phi L e0 k j x -
      (Iact phi L e1 k j x * (pooledQBin phi L e1 k j x - pooledQBin phi L e0 k j x) -
        Dbd phi L e1 k j x * ((positiveValue e1.pLev (k + 1) x - binFullJ L e1 k x) -
          (positiveValue e0.pLev (k + 1) x - binFullJ L e0 k x)) -
        Edom phi L e1 k j x * Iact phi L e1 k j x *
          (pooledQBin phi L e1 k (j - 1) x - pooledQBin phi L e0 k (j - 1) x))
    Integrable (fun x => regularValue e1.gamma k j x * R x) (xLaw M) ∧
    |∫ x, regularValue e1.gamma k j x * R x ∂xLaw M| ≤ (78 / c) *
      ((∫ x, (pooledQBin phi L e1 k j x - pooledQBin phi L e0 k j x) ^ 2 ∂xLaw M) +
        (∫ x, (pooledQBin phi L e1 k (j - 1) x -
          pooledQBin phi L e0 k (j - 1) x) ^ 2 ∂xLaw M) +
        ∫ x, ((positiveValue e1.pLev (k + 1) x - binFullJ L e1 k x) -
          (positiveValue e0.pLev (k + 1) x - binFullJ L e0 k x)) ^ 2 ∂xLaw M) := by
  have hw : Measurable (regularValue e1.gamma k j) := by
    first | fun_prop | skip
    unfold regularValue
    split_ifs
    · exact (he1.2.2.2.2.2.1 _).2
    · fun_prop
  have hwb : ∀ᵐ x ∂xLaw M, ‖regularValue e1.gamma k j x‖ ≤ 1 := by
    unfold regularValue
    split_ifs with hi
    · filter_upwards [he1.2.2.2.2.1 ⟨(k,j), hi⟩] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg hx.2.1]
      exact hx.2.2
    · simp
  have h := binary_hinge_weighted_component_energy_bound (xLaw M)
    (pooledQBin phi L e0 k j) (pooledQBin phi L e0 k (j - 1))
    (fun x => positiveValue e0.pLev (k + 1) x - binFullJ L e0 k x)
    (pooledQBin phi L e1 k j) (pooledQBin phi L e1 k (j - 1))
    (fun x => positiveValue e1.pLev (k + 1) x - binFullJ L e1 k x)
    (regularValue e1.gamma k j) c 1 hc zero_le_one
    hq0 hl0 hb0 hq1 hl1 hb1 hw hwb heq hel heb hgap
  simpa only [hMinus_binaryFittedHingeRemainder_eq, mul_one] using h

end Papers.TbsPrteOptimalTransport

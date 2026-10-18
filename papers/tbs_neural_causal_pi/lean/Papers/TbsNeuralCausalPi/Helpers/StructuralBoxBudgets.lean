module
public import Papers.TbsNeuralCausalPi.Helpers.StructuralCommonBudgets
public import Papers.TbsNeuralCausalPi.Helpers.AffineNetworkInputs
public import Papers.TbsNeuralCausalPi.Helpers.StructuralNormalization
/-! # Structural interpolation budgets on physical input boxes

Affine changes of input preserve network width and depth. Rescaling the
Lipschitz budget in both directions retains the original global constant,
and convex output constraints survive unchanged.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open scoped NNReal
noncomputable section

-- @node: structuralAffineInput
/-- For [a scalar scale](hyp:a), [a scalar translation](hyp:t), and [an input
vector](hyp:x), [the affine input transformation](goal) multiplies every
coordinate by the scale and adds the translation. -/
def structuralAffineInput {d : ℕ} (a t : ℝ) (x : L1Vec d) : L1Vec d :=
  WithLp.toLp 1 (fun j => a * x.ofLp j + t)

-- @node: structuralAffineInput_dist
/-- [Applying the same scalar affine transformation to two vectors multiplies
their distance in the sum-of-absolute-differences metric by the absolute
value of the scale](goal). -/
lemma structuralAffineInput_dist {d : ℕ} (a t : ℝ) (x y : L1Vec d) :
    dist (structuralAffineInput a t x) (structuralAffineInput a t y) =
      |a| * dist x y := by
  simp only [PiLp.dist_eq_of_L1, structuralAffineInput,
    Real.dist_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [show a * x.ofLp j + t - (a * y.ofLp j + t) =
    a * (x.ofLp j - y.ofLp j) by ring, abs_mul]

-- @node: structuralAffineInput_inverse
/-- If [the affine scale is nonzero](hyp:ha), [applying the reciprocal scale
and the negative translation divided by the original scale after the original
affine transformation recovers the input vector](goal). -/
lemma structuralAffineInput_inverse {d : ℕ} {a : ℝ} (ha : a ≠ 0)
    (t : ℝ) (x : L1Vec d) :
    structuralAffineInput a⁻¹ (-t / a) (structuralAffineInput a t x) = x := by
  apply PiLp.ext
  intro j
  change a⁻¹ * (a * x.ofLp j + t) + -t / a = x.ofLp j
  field_simp
  ring

/-- [Precomposing a ReLU network with a scalar affine input transformation can
be represented by a ReLU network with the same input dimension, output
dimension, width budget, and hidden depth](goal). -/
-- @node: relu_structuralAffineInput
lemma relu_structuralAffineInput {d k W depth : ℕ}
    (q : ReLUNet d k W depth) (a t : ℝ) :
    ∃ Q : ReLUNet d k W depth, Q.eval = q.eval ∘ structuralAffineInput a t := by
  obtain ⟨Q, hQ⟩ := relu_affine_precomp q (diagonalWeight d a) (fun _ => t)
  refine ⟨Q, ?_⟩
  funext x
  rw [hQ]
  congr 1
  apply PiLp.ext
  intro j
  simp only [WithLp.ofLp_toLp, diagonalWeight_sum, structuralAffineInput]

/-- Suppose [the common input-dimension bound is positive](hyp:hD), [all input
dimensions are at most that bound](hyp:hdim), and [the prescribed output
sets](hyp:target) [are convex](hyp:htarget). Then [positive depth and width
thresholds and a positive error constant exist such that, above those
thresholds, every family of functions that is Lipschitz and takes values in
the prescribed sets on any common positively scaled and translated unit
cube admits ReLU approximations of the chosen width and depth equal to the
chosen depth factor times the ceiling of one plus the logarithm of the
dimension bound; the approximations globally retain the Lipschitz bound and
output constraints, with error on each cube at most the constant times the
Lipschitz bound times the scale times width to the power minus the reciprocal
of the dimension bound](goal). -/
-- @node: structural_networks_affine_box_budgets
lemma structural_networks_affine_box_budgets {I : Type*} [Fintype I]
    (din dout : I → ℕ) (D : ℕ) (hD : 0 < D) (hdim : ∀ i, din i ≤ D)
    (target : ∀ i, Set (L1Vec (dout i))) (htarget : ∀ i, Convex ℝ (target i)) :
    ∃ c0 B : ℕ, 0 < c0 ∧ 0 < B ∧ ∃ A : ℝ, 0 < A ∧
      ∀ c : ℕ, c0 ≤ c → ∀ W : ℕ, B ≤ W →
      ∀ (a : ℝ≥0), 0 < a → ∀ (t : ℝ) (L : ℝ≥0)
        (f : ∀ i, L1Vec (din i) → L1Vec (dout i)),
        (∀ i, LipschitzOnWith L (f i)
          (structuralAffineInput a t '' unitCube (din i))) →
        (∀ i, Set.MapsTo (f i) (structuralAffineInput a t '' unitCube (din i))
          (target i)) →
        ∃ q : ∀ i, ReLUNet (din i) (dout i) W (c * ⌈1 + Real.log D⌉₊),
          (∀ i, LipschitzWith L (q i).eval) ∧
          (∀ i x, (q i).eval x ∈ target i) ∧
          ∀ i x, x ∈ structuralAffineInput a t '' unitCube (din i) →
            ‖(q i).eval x - f i x‖ ≤ A * L * a * (W : ℝ)^(-(1:ℝ)/D) := by
  obtain ⟨c0, B, hc0, hB, A, hA, happ⟩ :=
    structural_networks_common_budgets_convex din dout D hD hdim target htarget
  refine ⟨c0, B, hc0, hB, A, hA, ?_⟩
  intro c hc W hW a ha t L f hf hmaps
  have haR : (0 : ℝ) < a := ha
  let F := fun i => f i ∘ structuralAffineInput a t
  have hF (i) : LipschitzOnWith (L * a) (F i) (unitCube (din i)) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    calc
      _ ≤ L * dist (structuralAffineInput a t x) (structuralAffineInput a t y) :=
        (hf i).dist_le_mul _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      _ = _ := by
        rw [structuralAffineInput_dist, abs_of_pos haR]
        simp only [NNReal.coe_mul]
        ring
  obtain ⟨Q, hLip, htargetQ, herr⟩ := happ c hc W hW (L * a) F hF
    (fun i x hx => hmaps i ⟨x, hx, rfl⟩)
  choose q hq using fun i => relu_structuralAffineInput (Q i) (a : ℝ)⁻¹ (-t / a)
  refine ⟨q, ?_, ?_, ?_⟩
  · intro i
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [hq i]
    calc
      _ ≤ (L * a : ℝ≥0) * dist (structuralAffineInput (a : ℝ)⁻¹ (-t/a) x)
          (structuralAffineInput (a : ℝ)⁻¹ (-t/a) y) := (hLip i).dist_le_mul _ _
      _ = _ := by
        rw [structuralAffineInput_dist, abs_of_pos (inv_pos.mpr haR)]
        simp only [NNReal.coe_mul]
        field_simp
  · intro i x
    rw [hq i]
    exact htargetQ i _
  · intro i x hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [hq i]
    simp only [Function.comp_apply, structuralAffineInput_inverse (ne_of_gt haR)]
    simpa only [F, Function.comp_apply, NNReal.coe_mul, mul_assoc] using herr i y hy

/-- For [a nonnegative box radius](hyp:K) [that is positive](hyp:hK), [the image
of the unit cube under scaling by twice the radius and translation by minus
the radius is exactly the centered box with that radius](goal). -/
-- @node: structuralAffineInput_image_unitCube
lemma structuralAffineInput_image_unitCube (d : ℕ) (K : ℝ≥0) (hK : 0 < K) :
    structuralAffineInput (2 * (K : ℝ)) (-(K : ℝ)) '' unitCube d =
      boundedCube d K := by
  have hKR : (0 : ℝ) < K := hK
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩ j
    have hj := hy j
    change |2 * (K : ℝ) * y.ofLp j + -(K : ℝ)| ≤ K
    exact abs_le.mpr ⟨by nlinarith [hj.1], by nlinarith [hj.2]⟩
  · intro hx
    let y : L1Vec d := WithLp.toLp 1 (fun j => (x.ofLp j + K) / (2 * K))
    refine ⟨y, ?_, ?_⟩
    · intro j
      obtain ⟨hl, hu⟩ := abs_le.mp (hx j)
      change 0 ≤ (x.ofLp j + K) / (2 * K) ∧ (x.ofLp j + K) / (2 * K) ≤ 1
      exact ⟨div_nonneg (by linarith) (by positivity),
        (div_le_one (by positivity)).mpr (by linarith)⟩
    · apply PiLp.ext
      intro j
      change 2 * (K : ℝ) * ((x.ofLp j + K) / (2 * K)) + -(K : ℝ) = x.ofLp j
      field_simp
      ring

/-- Suppose [the common input-dimension bound is positive](hyp:hD), [all input
dimensions are at most that bound](hyp:hdim), [the prescribed output sets](hyp:target)
[are convex](hyp:htarget), and [the nonnegative box radius](hyp:K) [is positive](hyp:hK).
Then [positive depth and width thresholds and a positive error constant exist
such that, above those thresholds, every family of functions that is Lipschitz
and takes values in the prescribed sets on the centered boxes admits ReLU
approximations of the chosen width and depth equal to the chosen depth factor
times the ceiling of one plus the logarithm of the dimension bound; these
approximations globally retain the Lipschitz bound and output constraints,
and the sum of uniform coordinate errors on the boxes is at most the constant
times the Lipschitz bound times width to the power minus the reciprocal of
the dimension bound](goal). -/
-- @node: structural_networks_boundedCube_budgets
lemma structural_networks_boundedCube_budgets {I : Type*} [Fintype I]
    (din dout : I → ℕ) (D : ℕ) (hD : 0 < D) (hdim : ∀ i, din i ≤ D)
    (target : ∀ i, Set (L1Vec (dout i))) (htarget : ∀ i, Convex ℝ (target i))
    (K : ℝ≥0) (hK : 0 < K) :
    ∃ c0 B : ℕ, 0 < c0 ∧ 0 < B ∧ ∃ A : ℝ, 0 < A ∧
      ∀ c : ℕ, c0 ≤ c → ∀ W : ℕ, B ≤ W →
      ∀ (L : ℝ≥0) (f : ∀ i, L1Vec (din i) → L1Vec (dout i)),
        (∀ i, LipschitzOnWith L (f i) (boundedCube (din i) K)) →
        (∀ i, Set.MapsTo (f i) (boundedCube (din i) K) (target i)) →
        ∃ q : ∀ i, ReLUNet (din i) (dout i) W (c * ⌈1 + Real.log D⌉₊),
          (∀ i, LipschitzWith L (q i).eval) ∧
          (∀ i x, (q i).eval x ∈ target i) ∧
          (∑ i, supDistOn (boundedCube (din i) K) (f i) (q i).eval) ≤
            ENNReal.ofReal (A * L * (W : ℝ)^(-(1:ℝ)/D)) := by
  obtain ⟨c0, B, hc0, hB, E, hE, happ⟩ :=
    structural_networks_affine_box_budgets din dout D hD hdim target htarget
  refine ⟨c0, B, hc0, hB, (Fintype.card I + 1 : ℝ) * E * (2 * K), by positivity, ?_⟩
  intro c hc W hW L f hf hmaps
  have hbox (i : I) := structuralAffineInput_image_unitCube (din i) K hK
  obtain ⟨q, hLip, htargetQ, herr⟩ := happ c hc W hW (2 * K) (by positivity) (-(K : ℝ)) L f
    (fun i => by simpa only [NNReal.coe_mul, NNReal.coe_ofNat, hbox i] using hf i)
    (fun i => by simpa only [NNReal.coe_mul, NNReal.coe_ofNat, hbox i] using hmaps i)
  have he : 0 ≤ E * L * (2 * K) * (W : ℝ)^(-(1:ℝ)/D) := by positivity
  have herr' (i : I) (x : L1Vec (din i)) (hx : x ∈ boundedCube (din i) K) :
      ‖(q i).eval x - f i x‖ ≤ E * L * (2 * K) * (W : ℝ)^(-(1:ℝ)/D) := by
    simpa only [NNReal.coe_mul, NNReal.coe_ofNat] using
      herr i x (by simpa only [NNReal.coe_mul, NNReal.coe_ofNat, hbox i] using hx)
  refine ⟨q, hLip, htargetQ, ?_⟩
  calc
    _ ≤ ∑ _i : I, ENNReal.ofReal (E * L * (2 * K) * (W : ℝ)^(-(1:ℝ)/D)) :=
      Finset.sum_le_sum (fun i _ => structural_supDistOn_le_of_norm_error _ _ _ he (herr' i))
    _ = ENNReal.ofReal ((Fintype.card I : ℝ) *
        (E * L * (2 * K) * (W : ℝ)^(-(1:ℝ)/D))) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => he)]
      simp
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by nlinarith)

/-- Suppose [the common input-dimension bound is positive](hyp:hD), [all input
dimensions are at most that bound](hyp:hdim), and [the nonnegative box
radius](hyp:K) [is positive](hyp:hK). Then [positive depth and width thresholds
and a positive error constant exist such that, above those thresholds, every
Lipschitz family with probability-vector outputs on the centered boxes admits
ReLU approximations of the chosen width and depth equal to the chosen depth
factor times the ceiling of one plus the logarithm of the dimension bound;
the networks globally retain the Lipschitz bound and probability-vector
outputs, have positive total output mass, equal their own normalized outputs,
retain the Lipschitz bound after normalization, and have summed uniform
coordinate error on the boxes at most the constant times the Lipschitz bound
times width to the power minus the reciprocal of the dimension bound](goal). -/
-- @node: structural_networks_boundedCube_simplex
lemma structural_networks_boundedCube_simplex {I : Type*} [Fintype I]
    (din dout : I → ℕ) (D : ℕ) (hD : 0 < D) (hdim : ∀ i, din i ≤ D)
    (K : ℝ≥0) (hK : 0 < K) :
    ∃ c0 B : ℕ, 0 < c0 ∧ 0 < B ∧ ∃ A : ℝ, 0 < A ∧
      ∀ c : ℕ, c0 ≤ c → ∀ W : ℕ, B ≤ W →
      ∀ (L : ℝ≥0) (f : ∀ i, L1Vec (din i) → L1Vec (dout i)),
        (∀ i, LipschitzOnWith L (f i) (boundedCube (din i) K)) →
        (∀ i x, x ∈ boundedCube (din i) K →
          (f i x).ofLp ∈ probabilitySimplex (dout i)) →
        ∃ q : ∀ i, ReLUNet (din i) (dout i) W (c * ⌈1 + Real.log D⌉₊),
          (∀ i, LipschitzWith L (q i).eval) ∧
          (∀ i x, ((q i).eval x).ofLp ∈ probabilitySimplex (dout i)) ∧
          (∀ i x, 0 < ∑ j, ((q i).eval x).ofLp j) ∧
          (∀ i x, WithLp.toLp 1 (fun j => ((q i).eval x).ofLp j /
            ∑ l, ((q i).eval x).ofLp l) = (q i).eval x) ∧
          (∀ i, LipschitzWith L (fun x => WithLp.toLp 1 (fun j =>
            ((q i).eval x).ofLp j / ∑ l, ((q i).eval x).ofLp l))) ∧
          (∑ i, supDistOn (boundedCube (din i) K) (f i) (q i).eval) ≤
            ENNReal.ofReal (A * L * (W : ℝ)^(-(1:ℝ)/D)) := by
  let target := fun i => {p : L1Vec (dout i) | p.ofLp ∈ probabilitySimplex (dout i)}
  have hconv (i) : Convex ℝ (target i) :=
    (convex_stdSimplex ℝ (Fin (dout i))).linear_preimage
      (WithLp.linearEquiv 1 ℝ (Fin (dout i) → ℝ)).toLinearMap
  obtain ⟨c0, B, hc0, hB, A, hA, happ⟩ :=
    structural_networks_boundedCube_budgets din dout D hD hdim target hconv K hK
  refine ⟨c0, B, hc0, hB, A, hA, ?_⟩
  intro c hc W hW L f hf hs
  obtain ⟨q, hLip, hp, herr⟩ := happ c hc W hW L f hf hs
  have heq (i) (x : L1Vec (din i)) :
      WithLp.toLp 1 (fun j => ((q i).eval x).ofLp j /
        ∑ l, ((q i).eval x).ofLp l) = (q i).eval x :=
    structural_normalized_simplex_eq_self (hp i x)
  refine ⟨q, hLip, hp, ?_, heq, ?_, herr⟩
  · intro i x
    rw [(hp i x).2]
    norm_num
  · intro i
    simpa only [heq] using hLip i

end
end Papers.TbsNeuralCausalPi

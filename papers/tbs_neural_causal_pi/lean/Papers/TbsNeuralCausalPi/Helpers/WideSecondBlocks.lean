module
public import Papers.TbsNeuralCausalPi.Helpers.WideGenerator
/-! # Common-budget second blocks for the wide generator

Two layers are reserved for clipping. The other layers retain a fixed fraction
of the depth budget. Zero-dimensional charts are represented exactly.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
open scoped NNReal ENNReal
noncomputable section

/-- For [input dimension k](hyp:k), [width W](hyp:W), [depth](hyp:depth), and
[output vector v](hyp:v), the [constant ReLU network](goal) is the zero network
with its output bias replaced by v. -/
-- @node: constantReLUNet
def constantReLUNet (k W depth : ℕ) {d : ℕ} (v : L1Vec d) : ReLUNet k d W depth :=
  { zeroNet k d W depth with outputBias := v.ofLp }

-- @node: constantReLUNet_eval
/-- For [input dimension k](hyp:k), [width W](hyp:W), [depth](hyp:depth), and
[output vector v](hyp:v), [the constant ReLU network returns v at every input](goal). -/
lemma constantReLUNet_eval (k W depth : ℕ) {d : ℕ} (v : L1Vec d) :
    (constantReLUNet k W depth v).eval = fun _ => v := by
  funext x
  apply PiLp.ext
  intro j
  simp [constantReLUNet, ReLUNet.eval, zeroNet]

/-- If [q is positive](hyp:hq) and [the depth is at least four](hyp:hdepth), then
[the depth minus two raised to the power $-2/q$ is at most four times the
depth raised to that power](goal). -/
-- @node: wide_reserved_depth_rate_le
lemma wide_reserved_depth_rate_le {q depth : ℕ} (hq : 0 < q) (hdepth : 4 ≤ depth) :
    ((depth-2 : ℕ) : ℝ) ^ (-(2 : ℝ) / q) ≤
      4 * (depth : ℝ) ^ (-(2 : ℝ) / q) := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hdepthR : (4 : ℝ) ≤ depth := by exact_mod_cast hdepth
  have hsub : ((depth-2 : ℕ) : ℝ) = (depth : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ depth)]
    norm_num
  have hpower : (2 : ℝ) ^ ((2 : ℝ) / q) ≤ 4 := by
    calc
      _ ≤ (2 : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num)
          ((div_le_iff₀ (by linarith : (0 : ℝ) < q)).2 (by linarith))
      _ = 4 := by norm_num
  calc
    _ ≤ ((depth : ℝ) / 2) ^ (-(2 : ℝ) / q) := by
      apply Real.rpow_le_rpow_of_nonpos (by positivity)
      · rw [hsub]; linarith
      · exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (Nat.cast_nonneg q)
    _ = (depth : ℝ) ^ (-(2 : ℝ) / q) * (2 : ℝ) ^ ((2 : ℝ) / q) := by
      rw [Real.div_rpow (Nat.cast_nonneg depth) (by norm_num),
        show -(2 : ℝ) / q = -((2 : ℝ) / q) by ring,
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      simp only [div_inv_eq_mul]
    _ ≤ (depth : ℝ) ^ (-(2 : ℝ) / q) * 4 :=
      mul_le_mul_of_nonneg_left hpower (Real.rpow_nonneg (Nat.cast_nonneg depth) _)
    _ = _ := by ring

/-- Given [a homeomorphism f from the q-dimensional unit cube onto S](hyp:f),
[a nonnegative constant L](hyp:L), [L-Lipschitz continuity of f](hyp:hf),
[a box radius K](hyp:K) that [is nonnegative](hyp:hK), [containment of S in that
box](hyp:hbox), and [the coordinate approximation theorem](hyp:hgate), [there
are a positive integer c and a positive constant A such that every depth at least
four admits a ReLU network of width $cd\max(1,q)$ and exactly that depth, whose
outputs stay in the box and whose uniform chart error is at most $A\,\mathrm{depth}^{-2/q}$
when q is positive; when q is zero the error is zero and the cube maps into S](goal). -/
-- @node: exists_wide_relu_second_block
lemma exists_wide_relu_second_block {d q : ℕ} {S : Set (L1Vec d)}
    (f : homeoClass (unitCube q) S) (L : ℝ≥0) (hf : LipschitzWith L f)
    (K : ℝ) (hK : 0 ≤ K) (hbox : S ⊆ boundedCube d K)
    (hgate : YarotskyCoordinateApprox) :
    ∃ c : ℕ, 0 < c ∧ ∃ A : ℝ, 0 < A ∧
      ∀ depth : ℕ, 4 ≤ depth → ∃ Q : ReLUNet q d (c * d * max 1 q) depth,
        (∀ x, Q.eval x ∈ boundedCube d K) ∧
        (q = 0 → Set.MapsTo Q.eval (unitCube q) S) ∧
        ∀ x : unitCube q, ‖(f x).val-Q.eval x.val‖ ≤
          if 0 < q then A * (depth : ℝ) ^ (-(2 : ℝ) / q) else 0 := by
  classical
  by_cases hq : 0 < q
  · obtain ⟨c, hc, A, hA, happrox⟩ :=
      yarotsky_vector_chart_approx_bounded hgate hq f L hf K hK hbox
    refine ⟨c+1, by omega, 1 + 4 * d * A, by positivity, ?_⟩
    intro depth hdepth
    obtain ⟨Q, hbounded, hcoord, herr⟩ := happrox (depth-2) (by omega)
    have hwidth : max (d * (c*q)) d ≤ (c+1) * d * max 1 q := by
      rw [show max 1 q = q from max_eq_right hq]
      apply max_le
      · nlinarith
      · calc
          d = 1 * d * 1 := by ring
          _ ≤ (c+1) * d * q :=
            Nat.mul_le_mul (Nat.mul_le_mul_right d (by omega : 1 ≤ c+1)) hq
    have hdeq : depth-2+2 = depth := by omega
    let R : ReLUNet q d ((c+1) * d * max 1 q) depth :=
      { Q.widen hwidth with depth := Q.depth.trans hdeq }
    have hR : R.eval = Q.eval := rfl
    refine ⟨R, ?_, ?_, ?_⟩
    · simpa only [hR] using hbounded
    · intro hzero
      omega
    · intro x
      rw [hR, if_pos hq]
      calc
        _ ≤ (d : ℝ) * A * ((depth-2 : ℕ) : ℝ) ^ (-(2 : ℝ) / q) := herr x
        _ ≤ (d : ℝ) * A * (4 * (depth : ℝ) ^ (-(2 : ℝ) / q)) := by
          gcongr
          exact wide_reserved_depth_rate_le hq hdepth
        _ ≤ (1 + 4 * d * A) * (depth : ℝ) ^ (-(2 : ℝ) / q) := by
          nlinarith [Real.rpow_nonneg (Nat.cast_nonneg depth) (-(2 : ℝ) / q)]
  · have hzero : q = 0 := by omega
    subst q
    have hcube : (0 : L1Vec 0) ∈ unitCube 0 := by
      intro j
      exact Fin.elim0 j
    let v : L1Vec d := (f ⟨0, hcube⟩).val
    have hv : v ∈ S := (f ⟨0, hcube⟩).property
    have heq (x : unitCube 0) : (f x).val = v := by
      have hx : x = ⟨0, hcube⟩ := Subtype.ext (Subsingleton.elim _ _)
      exact congrArg (fun y => (f y).val) hx
    refine ⟨1, zero_lt_one, 1, zero_lt_one, ?_⟩
    intro depth hdepth
    refine ⟨constantReLUNet 0 (1*d*max 1 0) depth v, ?_, ?_, ?_⟩
    · intro x
      rw [constantReLUNet_eval]
      exact hbox hv
    · intro _ x hx
      rw [constantReLUNet_eval]
      exact hv
    · intro x
      rw [constantReLUNet_eval, heq x, if_neg hq, sub_self, norm_zero]

/-- Given [homeomorphisms f from each component's unit cube onto its image](hyp:f),
[a common nonnegative constant L](hyp:L), [L-Lipschitz continuity of all charts](hyp:hf),
[a box radius K](hyp:K) that [is nonnegative](hyp:hK), [containment of all images
in that box](hyp:hbox), and [the coordinate approximation theorem](hyp:hgate),
[there are a positive integer c and a positive constant A such that every depth
at least four admits component ReLU networks of common width $cd\max(1,D)$
and exactly that depth, where D is the largest component dimension; all outputs
stay in the box, zero-dimensional cubes map into their images, and uniform chart
errors are at most $A\,\mathrm{depth}^{-2/\max(1,D)}$ if D is positive and zero otherwise](goal). -/
-- @node: exists_wide_relu_second_blocks
lemma exists_wide_relu_second_blocks {d N : ℕ}
    {S : Fin N → Set (L1Vec d)} {dC : Fin N → ℕ}
    (f : ∀ i, homeoClass (unitCube (dC i)) (S i))
    (L : ℝ≥0) (hf : ∀ i, LipschitzWith L (f i))
    (K : ℝ) (hK : 0 ≤ K) (hbox : ∀ i, S i ⊆ boundedCube d K)
    (hgate : YarotskyCoordinateApprox) :
    ∃ c : ℕ, 0 < c ∧ ∃ A : ℝ, 0 < A ∧
      ∀ depth : ℕ, 4 ≤ depth →
        ∃ Q : ∀ i, ReLUNet (dC i) d (c * d * max 1 (Finset.univ.sup dC)) depth,
          (∀ i x, (Q i).eval x ∈ boundedCube d K) ∧
          (∀ i, dC i = 0 → Set.MapsTo (Q i).eval (unitCube (dC i)) (S i)) ∧
          ∀ i, ∀ x : unitCube (dC i), ‖((f i) x).val-(Q i).eval x.val‖ ≤
            if 0 < Finset.univ.sup dC then
              A * (depth : ℝ) ^ (-(2 : ℝ) / max 1 (Finset.univ.sup dC)) else 0 := by
  classical
  choose c hc A hA hq using fun i =>
    exists_wide_relu_second_block (f i) L (hf i) K hK (hbox i) hgate
  let cmax : ℕ := 1 + ∑ i, c i
  let Amax : ℝ := 1 + ∑ i, A i
  have hcmax : 0 < cmax := by dsimp [cmax]; omega
  have hAmax : 0 < Amax := by
    have hs := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => (hA i).le)
    dsimp [Amax]
    linarith
  have hcle (i : Fin N) : c i ≤ cmax := by
    have hs := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => Nat.zero_le (c j))
      (Finset.mem_univ i)
    dsimp [cmax]
    omega
  have hAle (i : Fin N) : A i ≤ Amax := by
    have hs := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => (hA j).le)
      (Finset.mem_univ i)
    dsimp [Amax]
    linarith
  have hdim (i : Fin N) : max 1 (dC i) ≤ max 1 (Finset.univ.sup dC) :=
    max_le_max_left 1 (Finset.le_sup (Finset.mem_univ i))
  refine ⟨cmax, hcmax, Amax, hAmax, ?_⟩
  intro depth hdepth
  choose Q hbounded hzero herr using fun i => hq i depth hdepth
  let R := fun i => (Q i).widen
    (Nat.mul_le_mul (Nat.mul_le_mul_right d (hcle i)) (hdim i))
  refine ⟨R, hbounded, hzero, ?_⟩
  intro i x
  change ‖((f i) x).val-(Q i).eval x.val‖ ≤ _
  by_cases hi : 0 < dC i
  · have hsup : 0 < Finset.univ.sup dC :=
      hi.trans_le (Finset.le_sup (Finset.mem_univ i))
    rw [if_pos hsup]
    have he := herr i x
    rw [if_pos hi] at he
    refine he.trans ?_
    apply mul_le_mul (hAle i)
      (wide_component_rate_le hi
        ((Finset.le_sup (Finset.mem_univ i)).trans (le_max_right _ _))
        (by exact_mod_cast (show 1 ≤ depth by omega)) (by norm_num : (0 : ℝ) ≤ 2))
      (Real.rpow_nonneg (Nat.cast_nonneg depth) _) hAmax.le
  · have he := herr i x
    rw [if_neg hi] at he
    refine he.trans ?_
    split_ifs <;> positivity

/-- If [each component image has an L-Lipschitz homeomorphism from its unit
cube](hyp:hcharts), then [there is a positive radius K whose coordinate box
contains every component image](goal). -/
-- @node: exists_component_bounding_box
lemma exists_component_bounding_box {d N : ℕ}
    {S : Fin N → Set (L1Vec d)} {dC : Fin N → ℕ} {L : ℝ≥0}
    (hcharts : ComponentsLipschitzHomeomorphic S dC L) :
    ∃ K : ℝ, 0 < K ∧ ∀ i, S i ⊆ boundedCube d K := by
  obtain ⟨B, hB⟩ :=
    (isCompact_iUnion (fun i => component_isCompact hcharts i)).exists_bound_of_continuousOn
      (f := fun x : L1Vec d => x) continuous_id.continuousOn
  refine ⟨max 1 B, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro i x hx j
  calc
    |x.ofLp j| = ‖x.ofLp j‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖x‖ := PiLp.norm_apply_le x j
    _ ≤ B := hB x (Set.mem_iUnion.mpr ⟨i, hx⟩)
    _ ≤ max 1 B := le_max_right _ _

/-- If [all component images admit L-Lipschitz homeomorphisms from their unit
cubes](hyp:hcharts) and [the coordinate approximation theorem holds](hyp:hgate),
then [one can choose such charts, a positive radius K whose box contains all component images, a positive
integer c, and a positive constant A, so that every depth at least four admits
component ReLU networks of common width $cd\max(1,D)$ and exactly that depth,
where D is the largest component dimension; their outputs stay in the box,
zero-dimensional cubes map into their images, and uniform chart errors are at
most $A\,\mathrm{depth}^{-2/\max(1,D)}$ for positive D and zero otherwise](goal). -/
-- @node: exists_wide_relu_bounded_second_blocks
lemma exists_wide_relu_bounded_second_blocks {d N : ℕ}
    {S : Fin N → Set (L1Vec d)} {dC : Fin N → ℕ} {L : ℝ≥0}
    (hcharts : ComponentsLipschitzHomeomorphic S dC L)
    (hgate : YarotskyCoordinateApprox) :
    ∃ f : ∀ i, homeoClass (unitCube (dC i)) (S i),
      (∀ i, LipschitzWith L (f i)) ∧
      ∃ K : ℝ, 0 < K ∧ (∀ i, S i ⊆ boundedCube d K) ∧
      ∃ c : ℕ, 0 < c ∧ ∃ A : ℝ, 0 < A ∧
        ∀ depth : ℕ, 4 ≤ depth →
          ∃ Q : ∀ i, ReLUNet (dC i) d (c * d * max 1 (Finset.univ.sup dC)) depth,
            (∀ i x, (Q i).eval x ∈ boundedCube d K) ∧
            (∀ i, dC i = 0 → Set.MapsTo (Q i).eval (unitCube (dC i)) (S i)) ∧
            ∀ i, ∀ x : unitCube (dC i), ‖((f i) x).val-(Q i).eval x.val‖ ≤
              if 0 < Finset.univ.sup dC then
                A * (depth : ℝ) ^ (-(2 : ℝ) / max 1 (Finset.univ.sup dC)) else 0 := by
  classical
  obtain ⟨K, hK, hbox⟩ := exists_component_bounding_box hcharts
  choose f hf using hcharts
  refine ⟨f, hf, K, hK, hbox, ?_⟩
  exact exists_wide_relu_second_blocks f L hf K hK.le hbox hgate

/-- Given [a probability law P](hyp:P), [component sets S](hyp:S), [component
dimensions](hyp:dC), and [a nonnegative chart constant L](hyp:L), suppose [the support
of P is the union of the distinct sets S, each a connected component of that support](hyp:hsupp), [each component admits an
L-Lipschitz unit-cube chart](hyp:hcharts), [the quantized generation theorem
holds](hyp:hPerekrestenko_of_gate), and [the coordinate approximation theorem
holds](hyp:hYarotskyCoordinate_of_gate). Then [charts, positive architecture and
error constants, a positive box radius containing all component images, and a budget threshold at least four can
be chosen so that for every width budget W and depth budget H at least the threshold and every positive temperature,
a three-part generator exists with first-block depth $c_1\max(1,D)$ and
second-block width $c_2d\max(1,D)$, where D is the largest component dimension;
its weights equal the component masses, its first blocks map into the chart
cubes with Wasserstein error at most $A_1W^{-1/\max(1,D)}$ for positive-dimensional
components, and its second blocks stay in the box and approximate the charts
within $A_2H^{-2/\max(1,D)}$ for positive D, with exact, image-valued outputs
on zero-dimensional charts and zero error when D is zero](goal). -/
-- @node: exists_wide_relu_generator_blocks
lemma exists_wide_relu_generator_blocks {d N : ℕ}
    (P : ProbabilityMeasure (L1Vec d)) (S : Fin N → Set (L1Vec d))
    (dC : Fin N → ℕ) (L : ℝ≥0)
    (hsupp : SupportFiniteComponents (P : Measure _) S)
    (hcharts : ComponentsLipschitzHomeomorphic S dC L)
    (hPerekrestenko_of_gate : PerekrestenkoQuantizedGeneration)
    (hYarotskyCoordinate_of_gate : YarotskyCoordinateApprox) :
    ∃ f : ∀ i, homeoClass (unitCube (dC i)) (S i),
      (∀ i, LipschitzWith L (f i)) ∧
      ∃ c1 c2 : ℕ, 0 < c1 ∧ 0 < c2 ∧
      ∃ A1 A2 K : ℝ, 0 < A1 ∧ 0 < A2 ∧ 0 < K ∧
      (∀ i, S i ⊆ boundedCube d K) ∧
      ∃ B : ℕ, 4 ≤ B ∧ ∀ W1 L2 : ℕ, B ≤ W1 → B ≤ L2 →
        ∀ tau : ℝ, 0 < tau →
          ∃ Q : ThreePartGenerator N d dC W1 (c1 * max 1 (Finset.univ.sup dC))
              (c2 * d * max 1 (Finset.univ.sup dC)) L2 tau,
            (∀ i, Q.p i = ((P : Measure _) (S i)).toReal) ∧
            (∀ i, Set.MapsTo (Q.g1 i).eval (unitCube 1) (unitCube (dC i))) ∧
            (∀ i x, (Q.g2 i).eval x ∈ boundedCube d K) ∧
            (∀ i, dC i = 0 → Set.MapsTo (Q.g2 i).eval (unitCube (dC i)) (S i)) ∧
            (∀ i, 0 < dC i → wasserstein1
              ((ProbabilityTheory.cond (P : Measure _) (S i)).map (chartInverse (f i)))
              ((uniformCubeLaw 1).map (Q.g1 i).eval) ≤
                ENNReal.ofReal (A1 * (W1 : ℝ) ^ (-(1 : ℝ) / max 1 (Finset.univ.sup dC)))) ∧
            ∀ i, ∀ x : unitCube (dC i), ‖((f i) x).val-(Q.g2 i).eval x.val‖ ≤
              if 0 < Finset.univ.sup dC then
                A2 * (L2 : ℝ) ^ (-(2 : ℝ) / max 1 (Finset.univ.sup dC)) else 0 := by
  classical
  obtain ⟨f, hf, K, hK, hbox, c2, hc2, A2, hA2, hsecond⟩ :=
    exists_wide_relu_bounded_second_blocks hcharts hYarotskyCoordinate_of_gate
  obtain ⟨c1, hc1, A1, hA1, B, hB, hfirst⟩ :=
    exists_wide_relu_first_blocks P S dC L hsupp hcharts f hf hPerekrestenko_of_gate
  have hp := support_component_real_masses P hsupp hcharts
  refine ⟨f, hf, c1, c2, hc1, hc2, A1, A2, K, hA1, hA2, hK, hbox,
    max 4 B, le_max_left _ _, ?_⟩
  intro W1 L2 hW hL tau htau
  obtain ⟨g1, hcube, hgen⟩ := hfirst W1 ((le_max_right _ _).trans hW)
  obtain ⟨g2, hbounded, hzero, herror⟩ := hsecond L2 ((le_max_left _ _).trans hL)
  let Q : ThreePartGenerator N d dC W1 (c1 * max 1 (Finset.univ.sup dC))
      (c2 * d * max 1 (Finset.univ.sup dC)) L2 tau :=
    { g1 := g1, g2 := g2, p := fun i => ((P : Measure _) (S i)).toReal,
      weights := ⟨fun i => (hp.1 i).le, hp.2⟩,
      positiveWeights := hp.1, temperature := htau }
  exact ⟨Q, fun i => rfl, hcube, hbounded, hzero, hgen, herror⟩


/-- Given [a homeomorphism f from the q-dimensional unit cube onto S](hyp:f),
[a nonnegative constant L](hyp:L), [L-Lipschitz continuity of f](hyp:hf),
[a box radius K](hyp:K) that [is nonnegative](hyp:hK), [containment of S in that
box](hyp:hbox), and [the coordinate approximation theorem](hyp:hgate), [there
is a positive constant A such that every depth at least four admits a ReLU
network of width $13d\max(1,q)$ and exactly that depth, with all outputs in the
box and uniform chart error at most $A\,\mathrm{depth}^{-2/q}$ for positive q;
for zero q the error is zero and the unit cube maps into S](goal). -/
lemma exists_wide_relu_second_block_explicit {d q : ℕ} {S : Set (L1Vec d)}
    (f : homeoClass (unitCube q) S) (L : ℝ≥0) (hf : LipschitzWith L f)
    (K : ℝ) (hK : 0 ≤ K) (hbox : S ⊆ boundedCube d K)
    (hgate : YarotskyCoordinateApprox) :
    ∃ A : ℝ, 0 < A ∧
      ∀ depth : ℕ, 4 ≤ depth → ∃ Q : ReLUNet q d (deepSecondWidthFactor * d * max 1 q) depth,
        (∀ x, Q.eval x ∈ boundedCube d K) ∧
        (q = 0 → Set.MapsTo Q.eval (unitCube q) S) ∧
        ∀ x : unitCube q, ‖(f x).val-Q.eval x.val‖ ≤
          if 0 < q then A * (depth : ℝ) ^ (-(2 : ℝ) / q) else 0 := by
  classical
  by_cases hq : 0 < q
  · obtain ⟨A, hA, happrox⟩ :=
      yarotsky_vector_chart_approx_bounded_explicit hgate hq f L hf K hK hbox
    refine ⟨1 + 4 * d * A, by positivity, ?_⟩
    intro depth hdepth
    obtain ⟨Q, hbounded, hcoord, herr⟩ := happrox (depth-2) (by omega)
    have hwidth : max (d * (deepFirstWidthFactor*q)) d ≤ deepSecondWidthFactor * d * max 1 q := by
      rw [show max 1 q = q from max_eq_right hq]
      change max (d * (12*q)) d ≤ 13 * d * q
      apply max_le
      · nlinarith
      · calc
          d = 1 * d * 1 := by ring
          _ ≤ 13 * d * q :=
            Nat.mul_le_mul (Nat.mul_le_mul_right d (by norm_num : 1 ≤ 13)) hq
    have hdeq : depth-2+2 = depth := by omega
    let R : ReLUNet q d (deepSecondWidthFactor * d * max 1 q) depth :=
      { Q.widen hwidth with depth := Q.depth.trans hdeq }
    have hR : R.eval = Q.eval := rfl
    refine ⟨R, ?_, ?_, ?_⟩
    · simpa only [hR] using hbounded
    · intro hzero
      omega
    · intro x
      rw [hR, if_pos hq]
      calc
        _ ≤ (d : ℝ) * A * ((depth-2 : ℕ) : ℝ) ^ (-(2 : ℝ) / q) := herr x
        _ ≤ (d : ℝ) * A * (4 * (depth : ℝ) ^ (-(2 : ℝ) / q)) := by
          gcongr
          exact wide_reserved_depth_rate_le hq hdepth
        _ ≤ (1 + 4 * d * A) * (depth : ℝ) ^ (-(2 : ℝ) / q) := by
          nlinarith [Real.rpow_nonneg (Nat.cast_nonneg depth) (-(2 : ℝ) / q)]
  · have hzero : q = 0 := by omega
    subst q
    have hcube : (0 : L1Vec 0) ∈ unitCube 0 := by
      intro j
      exact Fin.elim0 j
    let v : L1Vec d := (f ⟨0, hcube⟩).val
    have hv : v ∈ S := (f ⟨0, hcube⟩).property
    have heq (x : unitCube 0) : (f x).val = v := by
      have hx : x = ⟨0, hcube⟩ := Subtype.ext (Subsingleton.elim _ _)
      exact congrArg (fun y => (f y).val) hx
    refine ⟨1, zero_lt_one, ?_⟩
    intro depth hdepth
    refine ⟨constantReLUNet 0 (deepSecondWidthFactor*d*max 1 0) depth v, ?_, ?_, ?_⟩
    · intro x
      rw [constantReLUNet_eval]
      exact hbox hv
    · intro _ x hx
      rw [constantReLUNet_eval]
      exact hv
    · intro x
      rw [constantReLUNet_eval, heq x, if_neg hq, sub_self, norm_zero]


/-- Given [homeomorphisms f from each component's unit cube onto its image](hyp:f),
[a common nonnegative constant L](hyp:L), [L-Lipschitz continuity of all charts](hyp:hf),
[a box radius K](hyp:K) that [is nonnegative](hyp:hK), [containment of all images
in that box](hyp:hbox), and [the coordinate approximation theorem](hyp:hgate),
[there is a positive constant A such that every depth at least four admits
component ReLU networks of common width $13d\max(1,D)$ and exactly that depth,
where D is the largest component dimension; all outputs stay in the box,
zero-dimensional cubes map into their images, and uniform chart errors are at
most $A\,\mathrm{depth}^{-2/\max(1,D)}$ for positive D and zero otherwise](goal). -/
lemma exists_wide_relu_second_blocks_explicit {d N : ℕ}
    {S : Fin N → Set (L1Vec d)} {dC : Fin N → ℕ}
    (f : ∀ i, homeoClass (unitCube (dC i)) (S i))
    (L : ℝ≥0) (hf : ∀ i, LipschitzWith L (f i))
    (K : ℝ) (hK : 0 ≤ K) (hbox : ∀ i, S i ⊆ boundedCube d K)
    (hgate : YarotskyCoordinateApprox) :
    ∃ A : ℝ, 0 < A ∧
      ∀ depth : ℕ, 4 ≤ depth →
        ∃ Q : ∀ i, ReLUNet (dC i) d (deepSecondWidthFactor * d * max 1 (Finset.univ.sup dC)) depth,
          (∀ i x, (Q i).eval x ∈ boundedCube d K) ∧
          (∀ i, dC i = 0 → Set.MapsTo (Q i).eval (unitCube (dC i)) (S i)) ∧
          ∀ i, ∀ x : unitCube (dC i), ‖((f i) x).val-(Q i).eval x.val‖ ≤
            if 0 < Finset.univ.sup dC then
              A * (depth : ℝ) ^ (-(2 : ℝ) / max 1 (Finset.univ.sup dC)) else 0 := by
  classical
  choose A hA hq using fun i =>
    exists_wide_relu_second_block_explicit (f i) L (hf i) K hK (hbox i) hgate
  let Amax : ℝ := 1 + ∑ i, A i
  have hAmax : 0 < Amax := by
    have hs := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => (hA i).le)
    dsimp [Amax]
    linarith
  have hAle (i : Fin N) : A i ≤ Amax := by
    have hs := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => (hA j).le)
      (Finset.mem_univ i)
    dsimp [Amax]
    linarith
  have hdim (i : Fin N) : max 1 (dC i) ≤ max 1 (Finset.univ.sup dC) :=
    max_le_max_left 1 (Finset.le_sup (Finset.mem_univ i))
  refine ⟨Amax, hAmax, ?_⟩
  intro depth hdepth
  choose Q hbounded hzero herr using fun i => hq i depth hdepth
  let R := fun i => (Q i).widen
    (Nat.mul_le_mul_left (deepSecondWidthFactor * d) (hdim i))
  refine ⟨R, hbounded, hzero, ?_⟩
  intro i x
  change ‖((f i) x).val-(Q i).eval x.val‖ ≤ _
  by_cases hi : 0 < dC i
  · have hsup : 0 < Finset.univ.sup dC :=
      hi.trans_le (Finset.le_sup (Finset.mem_univ i))
    rw [if_pos hsup]
    have he := herr i x
    rw [if_pos hi] at he
    refine he.trans ?_
    apply mul_le_mul (hAle i)
      (wide_component_rate_le hi
        ((Finset.le_sup (Finset.mem_univ i)).trans (le_max_right _ _))
        (by exact_mod_cast (show 1 ≤ depth by omega)) (by norm_num : (0 : ℝ) ≤ 2))
      (Real.rpow_nonneg (Nat.cast_nonneg depth) _) hAmax.le
  · have he := herr i x
    rw [if_neg hi] at he
    refine he.trans ?_
    split_ifs <;> positivity

end
end Papers.TbsNeuralCausalPi

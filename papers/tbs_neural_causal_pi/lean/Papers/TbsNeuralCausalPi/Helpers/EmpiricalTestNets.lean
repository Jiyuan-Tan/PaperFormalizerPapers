module
public import Papers.TbsNeuralCausalPi.Setup.CitedResults
public import Papers.TbsNeuralCausalPi.Helpers.KantorovichCube
/-! # Finite test nets from quantization patterns

Choose one original test per occupied pattern of quantized grid values.
The Lipschitz bound extends agreement on a spatial grid to uniform agreement.
-/
public section
namespace Papers.TbsNeuralCausalPi
set_option linter.style.longLine false
set_option linter.style.whitespace false

/-- If [each of the d coordinates of x has absolute value at most K](hyp:hx),
[the sum of their absolute values is at most dK](goal). -/
-- @node: boundedCube_norm_le
lemma boundedCube_norm_le {d : ℕ} {K : ℝ} {x : L1Vec d}
    (hx : x ∈ boundedCube d K) : ‖x‖ ≤ (d : ℝ) * K := by
  rw [PiLp.norm_eq_of_L1]
  calc
    (∑ j, ‖x.ofLp j‖) ≤ ∑ _j : Fin d, K := by
      apply Finset.sum_le_sum
      intro j _
      exact hx j
    _ = _ := by simp

/-- If [K is nonnegative](hyp:hK), [h is one-Lipschitz on the cube with
coordinate bound K in sum absolute distance](hyp:hh), [h vanishes at zero](hyp:hzero),
and [x lies in that cube](hyp:hx), [the absolute value of h(x) is at most dK](goal). -/
-- @node: anchored_cube_test_abs_le
lemma anchored_cube_test_abs_le {d : ℕ} {K : ℝ} (hK : 0 ≤ K)
    {h : L1Vec d → ℝ} (hh : LipschitzOnWith 1 h (boundedCube d K))
    (hzero : h 0 = 0) {x : L1Vec d} (hx : x ∈ boundedCube d K) :
    |h x| ≤ (d : ℝ) * K := by
  have h0 : (0 : L1Vec d) ∈ boundedCube d K := by
    intro j
    simpa using hK
  have hdist := hh.dist_le_mul x hx 0 h0
  simpa only [Real.dist_eq, hzero, sub_zero, NNReal.coe_one, one_mul, dist_zero_right, Real.norm_eq_abs]
    using hdist.trans (by simpa using boundedCube_norm_le hx)


/-- For a class H and a coding into finitely many patterns,
[there is a finite set of representatives belonging to H, with size at most
the number of possible patterns, such that every member of H has the same
code as some representative](goal). -/
-- @node: empirical_pattern_representatives
lemma empirical_pattern_representatives {T P : Type*} [Fintype P]
    (H : Set T) (code : T → P) :
    ∃ R : Finset T, (∀ g ∈ R, g ∈ H) ∧ R.card ≤ Fintype.card P ∧
      ∀ h ∈ H, ∃ g ∈ R, code h = code g := by
  classical
  let Occupied := {p : P // ∃ h ∈ H, code h = p}
  let rep : Occupied → T := fun p => Classical.choose p.property
  have hrep (p : Occupied) : rep p ∈ H ∧ code (rep p) = p.val :=
    Classical.choose_spec p.property
  refine ⟨Finset.univ.image rep, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hg
    exact (hrep p).1
  · exact (Finset.card_image_le).trans (by
      simpa only [Finset.card_univ] using Fintype.card_subtype_le
        (fun p : P => ∃ h ∈ H, code h = p))
  · intro h hh
    let p : Occupied := ⟨code h, h, hh, rfl⟩
    exact ⟨rep p, Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩, (hrep p).2.symm⟩

/-- If [all grid points lie in S](hyp:hgrid), [every point of S is within
the mesh distance of a grid point](hyp:hcover), [h is one-Lipschitz on S](hyp:hh),
[g is one-Lipschitz on S](hyp:hg), and [their absolute difference at every
grid point is at most the bin width](hyp:hclose), [their absolute difference
everywhere on S is at most twice the mesh distance plus the bin width](goal). -/
-- @node: empirical_grid_uniform_error_le
lemma empirical_grid_uniform_error_le {X I : Type*} [PseudoMetricSpace X]
    {S : Set X} (grid : I → X) {mesh bin : ℝ}
    (hgrid : ∀ i, grid i ∈ S)
    (hcover : ∀ x ∈ S, ∃ i, dist x (grid i) ≤ mesh)
    {h g : X → ℝ} (hh : LipschitzOnWith 1 h S) (hg : LipschitzOnWith 1 g S)
    (hclose : ∀ i, |h (grid i) - g (grid i)| ≤ bin) :
    ∀ x ∈ S, |h x - g x| ≤ 2 * mesh + bin := by
  intro x hx
  obtain ⟨i, hi⟩ := hcover x hx
  have hleft : |h x - h (grid i)| ≤ mesh := by
    have hd := hh.dist_le_mul x hx (grid i) (hgrid i)
    simp only [Real.dist_eq, NNReal.coe_one, one_mul] at hd
    exact hd.trans hi
  have hright : |g (grid i) - g x| ≤ mesh := by
    rw [abs_sub_comm]
    have hd := hg.dist_le_mul x hx (grid i) (hgrid i)
    simp only [Real.dist_eq, NNReal.coe_one, one_mul] at hd
    exact hd.trans hi
  calc
    _ = |(h x - h (grid i)) + (h (grid i) - g (grid i)) +
        (g (grid i) - g x)| := by congr 1; ring
    _ ≤ |h x - h (grid i)| + |h (grid i) - g (grid i)| +
        |g (grid i) - g x| := (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ mesh + bin + mesh := add_le_add (add_le_add hleft (hclose i)) hright
    _ = _ := by ring

/-- If [the bin width is positive](hyp:hbin), [a is at least −R](hyp:ha),
[b is at least −R](hyp:hb), and [a + R and b + R fall in the same bin,
as measured by the natural-number floors of their ratios to the bin width](hyp:heq),
[the absolute difference between a and b is at most the bin width](goal). -/
-- @node: empirical_same_floor_bin_le
lemma empirical_same_floor_bin_le {a b R bin : ℝ} (hbin : 0 < bin)
    (ha : -R ≤ a) (hb : -R ≤ b)
    (heq : ⌊(a + R) / bin⌋₊ = ⌊(b + R) / bin⌋₊) : |a-b| ≤ bin := by
  have ha0 : 0 ≤ (a+R)/bin := div_nonneg (by linarith) hbin.le
  have hb0 : 0 ≤ (b+R)/bin := div_nonneg (by linarith) hbin.le
  have hal := (le_div_iff₀ hbin).mp (Nat.floor_le ha0)
  have hbl := (le_div_iff₀ hbin).mp (Nat.floor_le hb0)
  have hau := (div_lt_iff₀ hbin).mp (Nat.lt_floor_add_one ((a+R)/bin))
  have hbu := (div_lt_iff₀ hbin).mp (Nat.lt_floor_add_one ((b+R)/bin))
  rw [heq] at hal hau
  apply abs_le.mpr
  constructor <;> nlinarith

/-- Suppose [the bin width is positive](hyp:hbin), [the finite grid lies
in S](hyp:hgrid), [every point of S is within the mesh distance of the grid](hyp:hcover),
[all members of H are one-Lipschitz on S](hyp:hLip), and
[all their absolute values on S are bounded by R](hyp:hbound).
Then [there is a finite set of members of H with at most
(floor(2R/bin) + 1) raised to the number of grid points elements, such that
every member of H is uniformly within twice the mesh distance plus the
bin width of a representative on S](goal). -/
-- @node: empirical_lipschitz_grid_net
lemma empirical_lipschitz_grid_net {X : Type*} [PseudoMetricSpace X]
    {S : Set X} (H : Set (X → ℝ)) {I : Type*} [Fintype I] (grid : I → X)
    {R mesh bin : ℝ} (hbin : 0 < bin)
    (hgrid : ∀ i, grid i ∈ S)
    (hcover : ∀ x ∈ S, ∃ i, dist x (grid i) ≤ mesh)
    (hLip : ∀ h ∈ H, LipschitzOnWith 1 h S)
    (hbound : ∀ h ∈ H, ∀ x ∈ S, |h x| ≤ R) :
    ∃ T : Finset (X → ℝ), (∀ g ∈ T, g ∈ H) ∧
      T.card ≤ (⌊2*R/bin⌋₊ + 1)^(Fintype.card I) ∧
      ∀ h ∈ H, ∃ g ∈ T, ∀ x ∈ S, |h x - g x| ≤ 2*mesh + bin := by
  classical
  let bins := ⌊2*R/bin⌋₊ + 1
  let code : H → (I → Fin bins) := fun h i =>
    ⟨⌊(h.val (grid i)+R)/bin⌋₊, by
      have hb := (abs_le.mp (hbound h.val h.property (grid i) (hgrid i))).2
      have hle : (h.val (grid i)+R)/bin ≤ 2*R/bin :=
        div_le_div_of_nonneg_right (by linarith) hbin.le
      exact Nat.lt_succ_of_le (Nat.floor_mono hle)⟩
  obtain ⟨T, hT, hcard, hnet⟩ := empirical_pattern_representatives
    (Set.univ : Set H) code
  refine ⟨T.image Subtype.val, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp hg
    exact g.property
  · exact Finset.card_image_le.trans (hcard.trans (by
      simp only [Fintype.card_fun, Fintype.card_fin]; exact le_rfl))
  · intro h hh
    obtain ⟨g, hg, heq⟩ := hnet ⟨h, hh⟩ (Set.mem_univ _)
    refine ⟨g.val, Finset.mem_image.mpr ⟨g, hg, rfl⟩, ?_⟩
    apply empirical_grid_uniform_error_le grid hgrid hcover (hLip h hh) (hLip g.val g.property)
    intro i
    apply empirical_same_floor_bin_le hbin
      (abs_le.mp (hbound h hh (grid i) (hgrid i))).1
      (abs_le.mp (hbound g.val g.property (grid i) (hgrid i))).1
    exact congrArg Fin.val (congrFun heq i)

/-- If [K is nonnegative](hyp:hK) and [the grid step is positive](hyp:hstep),
[there is a grid indexed by d-tuples of integers from zero to floor(2K/step),
all of whose points lie in the coordinate-bounded cube, such that every
point in the cube is within d times the step in sum absolute distance
of a grid point](goal). -/
-- @node: empirical_boundedCube_grid
lemma empirical_boundedCube_grid (d : ℕ) {K step : ℝ}
    (hK : 0 ≤ K) (hstep : 0 < step) :
    ∃ grid : (Fin d → Fin (⌊2*K/step⌋₊ + 1)) → L1Vec d,
      (∀ i, grid i ∈ boundedCube d K) ∧
      ∀ x ∈ boundedCube d K, ∃ i, dist x (grid i) ≤ d * step := by
  let grid : (Fin d → Fin (⌊2*K/step⌋₊ + 1)) → L1Vec d :=
    fun i => WithLp.toLp 1 (fun j => -K + step * (i j : ℝ))
  have hfloor : (⌊2*K/step⌋₊ : ℝ) ≤ 2*K/step :=
    Nat.floor_le (by positivity)
  have hmax : step * (⌊2*K/step⌋₊ : ℝ) ≤ 2*K := by
    have := (le_div_iff₀ hstep).mp hfloor
    nlinarith
  refine ⟨grid, ?_, ?_⟩
  · intro i j
    change ‖-K + step * (i j : ℝ)‖ ≤ K
    rw [Real.norm_eq_abs, abs_le]
    have hle : (i j : ℝ) ≤ (⌊2*K/step⌋₊ : ℝ) := by
      exact_mod_cast (Nat.le_of_lt_succ (i j).isLt)
    have hnonneg : 0 ≤ (i j : ℝ) := Nat.cast_nonneg _
    constructor <;> nlinarith
  · intro x hx
    let i : Fin d → Fin (⌊2*K/step⌋₊ + 1) := fun j =>
      ⟨⌊(x.ofLp j + K)/step⌋₊, by
        apply Nat.lt_succ_of_le
        apply Nat.floor_mono
        apply div_le_div_of_nonneg_right _ hstep.le
        have := (abs_le.mp (hx j)).2
        simpa only [Real.norm_eq_abs] using (by linarith : x.ofLp j + K ≤ 2*K)⟩
    refine ⟨i, ?_⟩
    rw [PiLp.dist_eq_of_L1]
    calc
      _ ≤ ∑ _j : Fin d, step := by
        apply Finset.sum_le_sum
        intro j _
        change dist (x.ofLp j) (-K + step * (⌊(x.ofLp j + K)/step⌋₊ : ℝ)) ≤ step
        rw [Real.dist_eq, abs_le]
        have hxlow : 0 ≤ (x.ofLp j + K)/step := by
          apply div_nonneg _ hstep.le
          have := (abs_le.mp (hx j)).1
          linarith
        have hl := (le_div_iff₀ hstep).mp (Nat.floor_le hxlow)
        have hu := (div_lt_iff₀ hstep).mp (Nat.lt_floor_add_one ((x.ofLp j + K)/step))
        constructor <;> nlinarith
      _ = _ := by simp

/-- If [K is nonnegative](hyp:hK) and [δ is positive](hyp:hdelta),
[there is a finite set of tests that vanish at zero and are one-Lipschitz
on the d-dimensional cube with coordinate bound K, containing at most
(floor(16dK/δ) + 1) raised to the power (floor(16K(d + 1)/δ) + 1)ᵈ tests,
such that every test with these properties is uniformly within δ/2 of
one of them on the cube](goal). -/
-- @node: exists_anchored_cube_test_net
lemma exists_anchored_cube_test_net (d : ℕ) {K delta : ℝ}
    (hK : 0 ≤ K) (hdelta : 0 < delta) :
    ∃ T : Finset (L1Vec d → ℝ),
      (∀ g ∈ T, LipschitzOnWith 1 g (boundedCube d K) ∧ g 0 = 0) ∧
      T.card ≤ (⌊16*d*K/delta⌋₊ + 1)^((⌊16*K*(d+1)/delta⌋₊ + 1)^d) ∧
      ∀ h : L1Vec d → ℝ, LipschitzOnWith 1 h (boundedCube d K) → h 0 = 0 →
        ∃ g ∈ T, ∀ x ∈ boundedCube d K, |h x - g x| ≤ delta/2 := by
  let step := delta / (8 * ((d : ℝ) + 1))
  have hstep : 0 < step := by dsimp [step]; positivity
  obtain ⟨grid, hgrid, hcover⟩ := empirical_boundedCube_grid d hK hstep
  let H := {h : L1Vec d → ℝ | LipschitzOnWith 1 h (boundedCube d K) ∧ h 0 = 0}
  obtain ⟨T, hT, hcard, hnet⟩ := empirical_lipschitz_grid_net H grid
    (by positivity : 0 < delta/8) hgrid hcover (fun h hh => hh.1)
    (fun h hh x hx => anchored_cube_test_abs_le hK hh.1 hh.2 hx)
  have hbins : 2 * ((d : ℝ)*K) / (delta/8) = 16*d*K/delta := by ring
  have hspatial : 2*K/step = 16*K*(d+1)/delta := by dsimp [step]; field_simp; ring
  have hcard' : T.card ≤
      (⌊16*d*K/delta⌋₊ + 1)^((⌊16*K*(d+1)/delta⌋₊ + 1)^d) := by
    simpa only [Fintype.card_fun, Fintype.card_fin, hbins, hspatial] using hcard
  refine ⟨T, hT, hcard', ?_⟩
  intro h hh hzero
  obtain ⟨g, hg, hclose⟩ := hnet h ⟨hh, hzero⟩
  refine ⟨g, hg, fun x hx => (hclose x hx).trans ?_⟩
  have hstepid : 8 * ((d : ℝ)+1) * step = delta := by
    dsimp [step]
    field_simp
  nlinarith [hstep.le]

end Papers.TbsNeuralCausalPi

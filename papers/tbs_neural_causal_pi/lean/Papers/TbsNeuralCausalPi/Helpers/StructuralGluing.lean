module
public import Papers.TbsNeuralCausalPi.Helpers.StructuralHatNetworks
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Topology.Order.DenselyOrdered
/-! # Gluing the structural interpolant without loss of Lipschitz constant

A finite closed cover gives a neighborhood on which each point and the center
belong to a common piece. Continuous induction along a segment then sums the
piecewise Lipschitz estimates with no factor depending on the number of pieces.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open Set Filter
open scoped Topology NNReal
noncomputable section

/-- If [each set in a finite family is closed](hyp:hs), then [sufficiently near
any point, every set in the family containing a nearby point also contains the
original point](goal). -/
-- @node: structural_finite_closed_cover_eventually
lemma structural_finite_closed_cover_eventually {X I : Type*}
    [TopologicalSpace X] [Finite I] (s : I → Set X)
    (hs : ∀ i, IsClosed (s i)) (x : X) :
    ∀ᶠ y in 𝓝 x, ∀ i, y ∈ s i → x ∈ s i := by
  classical
  apply eventually_all.mpr
  intro i
  by_cases hx : x ∈ s i
  · exact Filter.Eventually.of_forall (fun _ _ => hx)
  · have hn : ∀ᶠ y in 𝓝 x, y ∉ s i := (hs i).isOpen_compl.mem_nhds hx
    exact hn.mono (fun _ hy hi => (hy hi).elim)

/-- If [each set in a finite family is closed](hyp:hs), [the family covers the
domain](hyp:hcover), and [the function is Lipschitz on every set in the family](hyp:hf)
with [nonnegative constant L](hyp:L), then [sufficiently near any center, the
distance between the function values at a domain point and the center is at most
L times the distance between those points](goal). -/
-- @node: structural_finite_closed_cover_local_bound
lemma structural_finite_closed_cover_local_bound {X Y I : Type*}
    [PseudoMetricSpace X] [PseudoMetricSpace Y] [Finite I]
    (s : I → Set X) (hs : ∀ i, IsClosed (s i)) (S : Set X)
    (hcover : ∀ x ∈ S, ∃ i, x ∈ s i) (f : X → Y) (L : ℝ≥0)
    (hf : ∀ i, LipschitzOnWith L f (s i)) (x : X) :
    ∀ᶠ y in 𝓝 x, y ∈ S → dist (f y) (f x) ≤ L * dist y x := by
  filter_upwards [structural_finite_closed_cover_eventually s hs x] with y hy hS
  obtain ⟨i, hi⟩ := hcover y hS
  exact (hf i).dist_le_mul y hi x (hy i hi)

/-- If [a is at most b](hyp:hab), [the function is continuous on the closed
interval from a to b](hyp:hc), and [near each point of that interval its change
in distance is bounded by L times the input distance](hyp:hloc), for
[a nonnegative constant L](hyp:L), then [the distance between its endpoint
values is at most L times the interval length](goal). -/
-- @node: structural_interval_dist_le_of_local_bound
lemma structural_interval_dist_le_of_local_bound {Y : Type*} [PseudoMetricSpace Y]
    (f : ℝ → Y) (a b : ℝ) (hab : a ≤ b) (L : ℝ≥0)
    (hc : ContinuousOn f (Icc a b))
    (hloc : ∀ x ∈ Icc a b,
      ∀ᶠ y in 𝓝 x, y ∈ Icc a b → dist (f y) (f x) ≤ L * dist y x) :
    dist (f b) (f a) ≤ L * (b-a) := by
  let S : Set ℝ := {x | dist (f x) (f a) ≤ L * (x-a)}
  have hclosed : IsClosed (S ∩ Icc a b) := by
    rw [inter_comm]
    exact isClosed_Icc.isClosed_le
      (continuous_dist.comp_continuousOn (hc.prodMk continuousOn_const)) (by fun_prop)
  have ha : a ∈ S := by simp [S]
  have hsub : Icc a b ⊆ S := hclosed.Icc_subset_of_forall_exists_gt ha (by
    rintro x ⟨hx, hxab⟩ y hxy
    have hnb := hloc x (Ico_subset_Icc_self hxab)
    have hright : ∀ᶠ z in 𝓝[>] x, z ∈ Icc a b :=
      Icc_mem_nhdsGT_of_mem hxab
    obtain ⟨z, hzloc, hzab, hzx, hzy⟩ :=
      ((hnb.filter_mono nhdsWithin_le_nhds).and (hright.and (Ioc_mem_nhdsGT hxy))).exists
    refine ⟨z, ?_, hzx, hzy⟩
    change dist (f z) (f a) ≤ L * (z-a)
    calc
      dist (f z) (f a) ≤ dist (f z) (f x) + dist (f x) (f a) := dist_triangle _ _ _
      _ ≤ L * dist z x + L * (x-a) := add_le_add (hzloc hzab) hx
      _ = L * (z-a) := by rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hzx)]; ring)
  exact hsub (right_mem_Icc.mpr hab)


/-- If [a finite family consists of closed sets](hyp:hs), [the domain is
convex](hyp:hS), [the family covers the domain](hyp:hcover), [the function is
continuous on the domain](hyp:hc), and [it is Lipschitz on each set in the
family](hyp:hf) with [nonnegative constant L](hyp:L), then [it is Lipschitz
with the same constant L on the entire domain](goal). -/
-- @node: structural_lipschitzOn_finite_closed_cover
lemma structural_lipschitzOn_finite_closed_cover {X Y I : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [PseudoMetricSpace Y] [Finite I]
    (s : I → Set X) (hs : ∀ i, IsClosed (s i)) (S : Set X) (hS : Convex ℝ S)
    (hcover : ∀ x ∈ S, ∃ i, x ∈ s i) (f : X → Y) (L : ℝ≥0)
    (hc : ContinuousOn f S) (hf : ∀ i, LipschitzOnWith L f (s i)) :
    LipschitzOnWith L f S := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  let path : ℝ → X := AffineMap.lineMap x y
  have hp : Continuous path := (lipschitzWith_lineMap x y).continuous
  have hm : MapsTo path (Icc 0 1) S :=
    fun t ht => hS.segment_subset hx hy (lineMap_mem_segment ℝ x y ht)
  have hl : ∀ i, LipschitzOnWith (L * nndist x y) (f ∘ path) (path ⁻¹' s i) := by
    intro i
    exact (hf i).comp (lipschitzWith_lineMap x y).lipschitzOnWith
      (fun _ ht => ht)
  have he := structural_interval_dist_le_of_local_bound (f ∘ path) 0 1 (by norm_num)
    (L * nndist x y) (hc.comp hp.continuousOn hm)
    (fun t _ => structural_finite_closed_cover_local_bound (fun i => path ⁻¹' s i)
      (fun i => (hs i).preimage hp) (Icc 0 1)
      (fun t ht => hcover _ (hm ht)) (f ∘ path) (L * nndist x y) hl t)
  simpa [path, dist_comm] using he

/-- [Every finite real vector admits a permutation of its coordinates that
orders them from largest to smallest, allowing ties](goal). -/
-- @node: structural_exists_antitone_permutation
lemma structural_exists_antitone_permutation {d : ℕ} (x : L1Vec d) :
    ∃ p : Equiv.Perm (Fin d), Antitone (fun j => x.ofLp (p j)) := by
  exact ⟨Tuple.sort (fun j => OrderDual.toDual (x.ofLp j)),
    Tuple.monotone_sort (fun j => OrderDual.toDual (x.ofLp j))⟩

/-- For [a permutation p of the coordinate indices](hyp:p), the
[ordered simplex](goal) consists of vectors [in the unit cube](step:1) whose
[coordinates in the order p are nonincreasing](step:2). -/
-- @node: structuralOrderedSimplex
def structuralOrderedSimplex {d : ℕ} (p : Equiv.Perm (Fin d)) : Set (L1Vec d) :=
  {x | x ∈ unitCube d ∧ Antitone (fun j => x.ofLp (p j))}

/-- [The unit-cube simplex whose coordinates are nonincreasing in any fixed
permutation order is closed](goal). -/
-- @node: structuralOrderedSimplex_isClosed
lemma structuralOrderedSimplex_isClosed {d : ℕ} (p : Equiv.Perm (Fin d)) :
    IsClosed (structuralOrderedSimplex p) := by
  have hcube : IsClosed (unitCube d) := by
    have hh : IsClosed (⋂ j : Fin d, {x : L1Vec d | x.ofLp j ∈ Icc 0 1}) :=
      isClosed_iInter (fun j => isClosed_Icc.preimage (by fun_prop))
    convert hh using 1
    ext x
    simp [unitCube]
  have horder : IsClosed {x : L1Vec d | Antitone (fun j => x.ofLp (p j))} := by
    have hh : IsClosed (⋂ (a : Fin d) (b : Fin d) (_ : a ≤ b),
        {x : L1Vec d | x.ofLp (p b) ≤ x.ofLp (p a)}) :=
      isClosed_iInter (fun a => isClosed_iInter (fun b => isClosed_iInter
        (fun _ => isClosed_le (by fun_prop) (by fun_prop))))
    convert hh using 1
    ext x
    simp [Antitone]
  exact hcube.inter horder

/-- If [a vector lies in the unit cube](hyp:hx), then [there is a permutation
whose ordered simplex contains that vector](goal). -/
-- @node: structuralOrderedSimplex_cover
lemma structuralOrderedSimplex_cover {d : ℕ} {x : L1Vec d} (hx : x ∈ unitCube d) :
    ∃ p : Equiv.Perm (Fin d), x ∈ structuralOrderedSimplex p := by
  obtain ⟨p, hp⟩ := structural_exists_antitone_permutation x
  exact ⟨p, hx, hp⟩

/-- [The unit cube in any finite-dimensional real coordinate space with the
one-norm is convex](goal). -/
-- @node: structural_unitCube_convex
lemma structural_unitCube_convex (d : ℕ) : Convex ℝ (unitCube d) := by
  intro x hx y hy a b ha hb hab j
  change a * x.ofLp j + b * y.ofLp j ∈ Icc 0 1
  exact (convex_Icc (0 : ℝ) 1) (hx j) (hy j) ha hb hab

/-- If [the sampling set contains every vertex of the simplex ordered by p](hyp:hs)
and [the sampled function is Lipschitz on the unit cube](hyp:hf) with
[nonnegative constant L](hyp:L), then [its grid interpolant is Lipschitz with
constant L on that ordered simplex](goal). -/
-- @node: structuralGridInterpolant_lipschitzOn_simplex
lemma structuralGridInterpolant_lipschitzOn_simplex {d k : ℕ}
    (s : Finset (Fin d → ℤ)) (f : L1Vec d → L1Vec k)
    (p : Equiv.Perm (Fin d)) (hs : ∀ i, structuralGridVertex p i ∈ s)
    (L : ℝ≥0) (hf : LipschitzOnWith L f (unitCube d)) :
    LipschitzOnWith L (structuralGridInterpolant s f) (structuralOrderedSimplex p) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [structuralGridInterpolant_eq_kuhn s f p hs hx.1 hx.2,
    structuralGridInterpolant_eq_kuhn s f p hs hy.1 hy.2]
  exact (kuhnInterpolant_lipschitz f p L hf).dist_le_mul x y

/-- If [the sampling set contains every vertex of every ordered simplex](hyp:hs)
and [the sampled function is Lipschitz on the unit cube](hyp:hf) with
[nonnegative constant L](hyp:L), then [its grid interpolant is Lipschitz with
constant L on the entire unit cube](goal). -/
-- @node: structuralGridInterpolant_lipschitzOn_unitCube
lemma structuralGridInterpolant_lipschitzOn_unitCube {d k : ℕ}
    (s : Finset (Fin d → ℤ)) (f : L1Vec d → L1Vec k)
    (hs : ∀ (p : Equiv.Perm (Fin d)) i, structuralGridVertex p i ∈ s)
    (L : ℝ≥0) (hf : LipschitzOnWith L f (unitCube d)) :
    LipschitzOnWith L (structuralGridInterpolant s f) (unitCube d) := by
  exact structural_lipschitzOn_finite_closed_cover structuralOrderedSimplex
    structuralOrderedSimplex_isClosed (unitCube d) (structural_unitCube_convex d)
    (fun _ hx => structuralOrderedSimplex_cover hx) _ L
    (structuralGridInterpolant_continuous s f).continuousOn
    (fun p => structuralGridInterpolant_lipschitzOn_simplex s f p (hs p) L hf)


/-- For [dimension d](hyp:d) and [integer upper bound R](hyp:R), the
[finite cube grid](goal) is the set of integer vectors with every coordinate
between zero and R, inclusive. -/
-- @node: structuralCubeGrid
def structuralCubeGrid (d R : ℕ) : Finset (Fin d → ℤ) :=
  Finset.univ.image (fun v : Fin d → Fin (R+1) => fun j => ((v j).val : ℤ))

/-- [The integer grid in dimension d with coordinates between zero and R has
exactly (R + 1) to the power d points](goal). -/
-- @node: structuralCubeGrid_card
lemma structuralCubeGrid_card (d R : ℕ) :
    (structuralCubeGrid d R).card = (R+1)^d := by
  classical
  rw [structuralCubeGrid, Finset.card_image_of_injective]
  · simp
  · intro v w he
    funext j
    apply Fin.ext
    have hj : ((v j).val : ℤ) = ((w j).val : ℤ) := congrFun he j
    exact_mod_cast hj

/-- [An integer vector belongs to the cube grid if and only if each of its
coordinates is between zero and R, inclusive](goal). -/
-- @node: structuralCubeGrid_mem
lemma structuralCubeGrid_mem {d R : ℕ} (v : Fin d → ℤ) :
    v ∈ structuralCubeGrid d R ↔ ∀ j, 0 ≤ v j ∧ v j ≤ R := by
  classical
  constructor
  · intro hv
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hv
    intro j
    change 0 ≤ ((w j).val : ℤ) ∧ ((w j).val : ℤ) ≤ R
    exact ⟨by positivity, by exact_mod_cast Nat.le_of_lt_succ (w j).isLt⟩
  · intro hv
    let w : Fin d → Fin (R+1) := fun j => ⟨(v j).toNat, by
      have hh := (hv j).2
      have hz := (hv j).1
      omega⟩
    apply Finset.mem_image.mpr
    refine ⟨w, Finset.mem_univ _, ?_⟩
    funext j
    exact Int.toNat_of_nonneg (hv j).1

/-- For [dimension d](hyp:d) and [integer side length R](hyp:R), the
[grid cube](goal) is the set of real vectors whose coordinates all lie between
zero and R, inclusive. -/
-- @node: structuralGridCube
def structuralGridCube (d R : ℕ) : Set (L1Vec d) :=
  {x | ∀ j, x.ofLp j ∈ Icc 0 (R : ℝ)}

/-- [The real cube with each coordinate between zero and R is convex](goal). -/
-- @node: structuralGridCube_convex
lemma structuralGridCube_convex (d R : ℕ) : Convex ℝ (structuralGridCube d R) := by
  intro x hx y hy a b ha hb hab j
  change a * x.ofLp j + b * y.ofLp j ∈ Icc 0 (R : ℝ)
  exact (convex_Icc (0 : ℝ) (R : ℝ)) (hx j) (hy j) ha hb hab

/-- For [an integer vector v](hyp:v), the [integer cell based at v](goal)
consists of the real vectors whose displacement from v lies in the unit cube. -/
-- @node: structuralIntegerCell
def structuralIntegerCell {d : ℕ} (v : Fin d → ℤ) : Set (L1Vec d) :=
  {x | x - structuralGridPoint v ∈ unitCube d}

/-- [The unit cell based at any integer vector is closed](goal). -/
-- @node: structuralIntegerCell_isClosed
lemma structuralIntegerCell_isClosed {d : ℕ} (v : Fin d → ℤ) :
    IsClosed (structuralIntegerCell v) := by
  have hc : IsClosed (unitCube d) := by
    have hh : IsClosed (⋂ j : Fin d, {x : L1Vec d | x.ofLp j ∈ Icc 0 1}) :=
      isClosed_iInter (fun j => isClosed_Icc.preimage (by fun_prop))
    convert hh using 1
    ext x
    simp [unitCube]
  exact hc.preimage (by fun_prop)

/-- If [R is positive](hyp:hR) and [a real vector lies in the cube with
coordinates between zero and R](hyp:hx), then [it belongs to a unit cell whose
integer base coordinates are between zero and R minus one](goal). -/
-- @node: structuralGridCube_cell_cover
lemma structuralGridCube_cell_cover {d R : ℕ} (hR : 0 < R)
    {x : L1Vec d} (hx : x ∈ structuralGridCube d R) :
    ∃ v : Fin d → Fin R,
      x ∈ structuralIntegerCell (fun j => ((v j).val : ℤ)) := by
  classical
  have hfloor (j : Fin d) : 0 ≤ ⌊x.ofLp j⌋ := Int.floor_nonneg.mpr (hx j).1
  let v : Fin d → Fin R := fun j =>
    ⟨(min ⌊x.ofLp j⌋ ((R : ℤ)-1)).toNat, by
      have hh := hfloor j
      have hb : min ⌊x.ofLp j⌋ ((R : ℤ)-1) ≤ (R : ℤ)-1 := min_le_right _ _
      omega⟩
  refine ⟨v, ?_⟩
  intro j
  have hv : (((v j).val : ℤ) : ℝ) = (min ⌊x.ofLp j⌋ ((R : ℤ)-1) : ℤ) := by
    simp only [v]
    rw [Int.toNat_of_nonneg (le_min (hfloor j) (by omega))]
  change x.ofLp j - (((v j).val : ℤ) : ℝ) ∈ Icc 0 1
  rw [hv]
  by_cases hj : ⌊x.ofLp j⌋ ≤ (R : ℤ)-1
  · rw [min_eq_left hj]
    exact ⟨sub_nonneg.mpr (Int.floor_le _), by linarith [Int.lt_floor_add_one (x.ofLp j)]⟩
  · rw [min_eq_right (le_of_not_ge hj)]
    have hb : (R : ℝ) - 1 ≤ x.ofLp j := by
      have hh : (R : ℤ)-1 ≤ ⌊x.ofLp j⌋ := le_of_not_ge hj
      exact (by exact_mod_cast hh : (R : ℝ)-1 ≤ (⌊x.ofLp j⌋ : ℝ)).trans (Int.floor_le _)
    simp only [Int.cast_sub, Int.cast_natCast, Int.cast_one]
    exact ⟨sub_nonneg.mpr hb, by linarith [(hx j).2]⟩

/-- [Every unit cell whose integer base coordinates are between zero and
R minus one is contained in the cube with coordinates between zero and R](goal). -/
-- @node: structuralIntegerCell_subset_cube
lemma structuralIntegerCell_subset_cube {d R : ℕ} (v : Fin d → Fin R) :
    structuralIntegerCell (fun j => ((v j).val : ℤ)) ⊆ structuralGridCube d R := by
  intro x hx j
  have hj := hx j
  change x.ofLp j - (((v j).val : ℤ) : ℝ) ∈ Icc 0 1 at hj
  have hv0 : (0 : ℝ) ≤ ((v j).val : ℝ) := by positivity
  have hv1 : ((v j).val : ℝ) + 1 ≤ R := by exact_mod_cast (v j).isLt
  simp only [Int.cast_natCast] at hj
  exact ⟨by linarith [hj.1], by linarith [hj.2]⟩

/-- [Adding any ordered unit-simplex vertex to an integer base vector with
coordinates between zero and R minus one gives a point of the cube grid](goal). -/
-- @node: structuralCubeGrid_cell_vertices
lemma structuralCubeGrid_cell_vertices {d R : ℕ} (v : Fin d → Fin R)
    (p : Equiv.Perm (Fin d)) (i : Fin (d + 1)) :
    (fun j => ((v j).val : ℤ)) + structuralGridVertex p i ∈ structuralCubeGrid d R := by
  apply (structuralCubeGrid_mem _).mpr
  intro j
  change 0 ≤ ((v j).val : ℤ) + structuralGridVertex p i j ∧
    ((v j).val : ℤ) + structuralGridVertex p i j ≤ R
  have hv := (v j).isLt
  unfold structuralGridVertex
  split_ifs <;> constructor <;> omega

/-- If [the sampled function is Lipschitz on the cube with coordinates between
zero and R](hyp:hf) with [nonnegative constant L](hyp:L), then [its full-grid
interpolant is Lipschitz with constant L on any unit cell whose base coordinates
are between zero and R minus one](goal). -/
-- @node: structuralGridInterpolant_lipschitzOn_cell
lemma structuralGridInterpolant_lipschitzOn_cell {d k R : ℕ}
    (f : L1Vec d → L1Vec k) (L : ℝ≥0)
    (hf : LipschitzOnWith L f (structuralGridCube d R)) (v : Fin d → Fin R) :
    LipschitzOnWith L (structuralGridInterpolant (structuralCubeGrid d R) f)
      (structuralIntegerCell (fun j => ((v j).val : ℤ))) := by
  classical
  let w : Fin d → ℤ := fun j => (v j).val
  let g : L1Vec d → L1Vec k := fun z => f (structuralGridPoint w + z)
  let s := (structuralCubeGrid d R).image (fun u => u-w)
  have hg : LipschitzOnWith L g (unitCube d) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hm (z : L1Vec d) (hz : z ∈ unitCube d) :
        structuralGridPoint w + z ∈ structuralGridCube d R :=
      structuralIntegerCell_subset_cube v (by
        change structuralGridPoint w + z - structuralGridPoint w ∈ unitCube d
        simpa only [add_sub_cancel_left] using hz)
    simpa only [g, dist_add_left] using hf.dist_le_mul _ (hm x hx) _ (hm y hy)
  have hs : ∀ (p : Equiv.Perm (Fin d)) i, structuralGridVertex p i ∈ s := by
    intro p i
    exact Finset.mem_image.mpr ⟨w + structuralGridVertex p i,
      structuralCubeGrid_cell_vertices v p i, add_sub_cancel_left _ _⟩
  have hlocal := structuralGridInterpolant_lipschitzOn_unitCube s g hs L hg
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have he (z : L1Vec d) :
      structuralGridInterpolant (structuralCubeGrid d R) f z =
        structuralGridInterpolant s g (z - structuralGridPoint w) := by
    simpa only [add_sub_cancel] using
      structuralGridInterpolant_translate (structuralCubeGrid d R) f w
        (z - structuralGridPoint w)
  rw [he, he]
  simpa only [dist_sub_right] using hlocal.dist_le_mul _ hx _ hy

/-- If [R is positive](hyp:hR) and [the sampled function is Lipschitz on the
cube with coordinates between zero and R](hyp:hf) with [nonnegative constant
L](hyp:L), then [its full-grid interpolant is Lipschitz with constant L on
that entire cube](goal). -/
-- @node: structuralCubeGridInterpolant_lipschitzOn
lemma structuralCubeGridInterpolant_lipschitzOn {d k R : ℕ} (hR : 0 < R)
    (f : L1Vec d → L1Vec k) (L : ℝ≥0)
    (hf : LipschitzOnWith L f (structuralGridCube d R)) :
    LipschitzOnWith L (structuralGridInterpolant (structuralCubeGrid d R) f)
      (structuralGridCube d R) := by
  exact structural_lipschitzOn_finite_closed_cover
    (fun v : Fin d → Fin R => structuralIntegerCell (fun j => ((v j).val : ℤ)))
    (fun _ => structuralIntegerCell_isClosed _) _ (structuralGridCube_convex d R)
    (fun _ hx => structuralGridCube_cell_cover hR hx) _ L
    (structuralGridInterpolant_continuous _ _).continuousOn
    (structuralGridInterpolant_lipschitzOn_cell f L hf)


/-- If [R is positive](hyp:hR) and [the input lies in the cube with coordinates
between zero and R](hyp:hx), then [the full-grid interpolant at that input
belongs to the convex hull of the function's values on the cube](goal). -/
-- @node: structuralCubeGridInterpolant_mem_convexHull
lemma structuralCubeGridInterpolant_mem_convexHull {d k R : ℕ} (hR : 0 < R)
    (f : L1Vec d → L1Vec k) {x : L1Vec d} (hx : x ∈ structuralGridCube d R) :
    structuralGridInterpolant (structuralCubeGrid d R) f x ∈
      convexHull ℝ (f '' structuralGridCube d R) := by
  obtain ⟨v, hv⟩ := structuralGridCube_cell_cover hR hx
  obtain ⟨p, hp⟩ := structural_exists_antitone_permutation
    (x - structuralGridPoint (fun j => ((v j).val : ℤ)))
  let w : Fin d → ℤ := fun j => (v j).val
  have he := structuralGridInterpolant_cell (structuralCubeGrid d R) f w p
    (structuralCubeGrid_cell_vertices v p) hv hp
  rw [add_sub_cancel] at he
  rw [he]
  apply orderedSimplexInterpolant_mem_convex _ _ (fun j => hv (p j)) hp
    (convex_convexHull _ _)
  intro i
  exact subset_convexHull ℝ _ ⟨_, structuralIntegerCell_subset_cube v (by
    change structuralGridPoint w + kuhnVertex p i - structuralGridPoint w ∈ unitCube d
    simpa only [add_sub_cancel_left] using kuhnVertex_mem_unitCube p i), rfl⟩

/-- If [R is positive](hyp:hR), [the sampled function is Lipschitz on the cube
with coordinates between zero and R](hyp:hf) with [nonnegative constant L](hyp:L),
and [the input lies in that cube](hyp:hx), then [the one-norm error of its
full-grid interpolant at that input is at most L times the input dimension](goal). -/
-- @node: structuralCubeGridInterpolant_error
lemma structuralCubeGridInterpolant_error {d k R : ℕ} (hR : 0 < R)
    (f : L1Vec d → L1Vec k) (L : ℝ≥0)
    (hf : LipschitzOnWith L f (structuralGridCube d R))
    {x : L1Vec d} (hx : x ∈ structuralGridCube d R) :
    ‖structuralGridInterpolant (structuralCubeGrid d R) f x - f x‖ ≤ L * d := by
  obtain ⟨v, hv⟩ := structuralGridCube_cell_cover hR hx
  obtain ⟨p, hp⟩ := structural_exists_antitone_permutation
    (x - structuralGridPoint (fun j => ((v j).val : ℤ)))
  let w : Fin d → ℤ := fun j => (v j).val
  have he := structuralGridInterpolant_cell (structuralCubeGrid d R) f w p
    (structuralCubeGrid_cell_vertices v p) hv hp
  rw [add_sub_cancel] at he
  rw [he]
  have hg : LipschitzOnWith L (fun z => f (structuralGridPoint w + z)) (unitCube d) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro y hy z hz
    have hm (a : L1Vec d) (ha : a ∈ unitCube d) :
        structuralGridPoint w + a ∈ structuralGridCube d R :=
      structuralIntegerCell_subset_cube v (by
        change structuralGridPoint w + a - structuralGridPoint w ∈ unitCube d
        simpa only [add_sub_cancel_left] using ha)
    simpa only [dist_add_left] using hf.dist_le_mul _ (hm y hy) _ (hm z hz)
  simpa only [w, add_sub_cancel] using
    kuhnInterpolant_error (fun z => f (structuralGridPoint w + z)) p L hg hv hp

/-- If [a vector lies in the unit cube](hyp:hx), then [multiplying it by R
places it in the cube with coordinates between zero and R](goal). -/
-- @node: structural_smul_mem_gridCube
lemma structural_smul_mem_gridCube {d : ℕ} (R : ℕ)
    {x : L1Vec d} (hx : x ∈ unitCube d) :
    (R : ℝ) • x ∈ structuralGridCube d R := by
  intro j
  change (R : ℝ) * x.ofLp j ∈ Icc 0 (R : ℝ)
  exact ⟨mul_nonneg (Nat.cast_nonneg _) (hx j).1,
    (mul_le_mul_of_nonneg_left (hx j).2 (Nat.cast_nonneg _)).trans_eq (mul_one _)⟩

/-- If [R is positive](hyp:hR) and [a vector lies in the cube with coordinates
between zero and R](hyp:hx), then [dividing the vector by R places it in the
unit cube](goal). -/
-- @node: structural_inv_smul_mem_unitCube
lemma structural_inv_smul_mem_unitCube {d R : ℕ} (hR : 0 < R)
    {x : L1Vec d} (hx : x ∈ structuralGridCube d R) :
    (R : ℝ)⁻¹ • x ∈ unitCube d := by
  have hRr : (0 : ℝ) < R := by exact_mod_cast hR
  intro j
  change (R : ℝ)⁻¹ * x.ofLp j ∈ Icc 0 1
  exact ⟨mul_nonneg (inv_nonneg.mpr hRr.le) (hx j).1,
    (mul_le_mul_of_nonneg_left (hx j).2 (inv_nonneg.mpr hRr.le)).trans_eq
      (inv_mul_cancel₀ hRr.ne')⟩

/-- If [R is positive](hyp:hR) and [the function is Lipschitz on the unit
cube](hyp:hf) with [nonnegative constant L](hyp:L), then [evaluating the function
after dividing its input by R is Lipschitz with constant L divided by R on the
cube with coordinates between zero and R](goal). -/
-- @node: structural_rescaled_lipschitzOn
lemma structural_rescaled_lipschitzOn {d k R : ℕ} (hR : 0 < R)
    (f : L1Vec d → L1Vec k) (L : ℝ≥0) (hf : LipschitzOnWith L f (unitCube d)) :
    LipschitzOnWith (L * (R : ℝ≥0)⁻¹) (fun x => f ((R : ℝ)⁻¹ • x))
      (structuralGridCube d R) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have h := hf.dist_le_mul _ (structural_inv_smul_mem_unitCube hR hx)
    _ (structural_inv_smul_mem_unitCube hR hy)
  simpa [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (show (0 : ℝ) ≤ (R : ℝ)⁻¹ from
      inv_nonneg.mpr (Nat.cast_nonneg R)), mul_assoc] using h

/-- For [mesh denominator R](hyp:R), [a function f to approximate](hyp:f), and
[an input vector x](hyp:x), the [cube approximation at x](goal) evaluates the
full-grid interpolant of the values of f at grid points divided by R, at the
point obtained by clipping each coordinate of x to the unit interval and then
multiplying by R. -/
-- @node: structuralCubeApprox
def structuralCubeApprox {d k : ℕ} (R : ℕ) (f : L1Vec d → L1Vec k)
    (x : L1Vec d) : L1Vec k :=
  structuralGridInterpolant (structuralCubeGrid d R) (fun y => f ((R : ℝ)⁻¹ • y))
    ((R : ℝ) • coordinateClamp 0 1 x)

/-- If [R is positive](hyp:hR) and [the function is Lipschitz on the unit
cube](hyp:hf) with [nonnegative constant L](hyp:L), then [its clipped cube
approximation is globally Lipschitz with constant L](goal). -/
-- @node: structuralCubeApprox_lipschitz
lemma structuralCubeApprox_lipschitz {d k R : ℕ} (hR : 0 < R)
    (f : L1Vec d → L1Vec k) (L : ℝ≥0) (hf : LipschitzOnWith L f (unitCube d)) :
    LipschitzWith L (structuralCubeApprox R f) := by
  have hRr : (R : ℝ) ≠ 0 := by exact_mod_cast hR.ne'
  have hg := structuralCubeGridInterpolant_lipschitzOn hR _ _
    (structural_rescaled_lipschitzOn hR f L hf)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hm (x : L1Vec d) := structural_smul_mem_gridCube R
    (coordinateClamp_mapsTo 0 1 zero_le_one x)
  have h := hg.dist_le_mul _ (hm x) _ (hm y)
  have hc := (coordinateClamp_lipschitz (d := d) 0 1).dist_le_mul x y
  change dist (structuralCubeApprox R f x) (structuralCubeApprox R f y) ≤ _
  refine h.trans ?_
  rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg R)]
  simp only [NNReal.coe_mul, NNReal.coe_inv, NNReal.coe_natCast]
  rw [← mul_assoc, mul_assoc (L : ℝ), inv_mul_cancel₀ hRr, mul_one]
  exact mul_le_mul_of_nonneg_left
    (by simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using hc) L.coe_nonneg

/-- If [R is positive](hyp:hR), then [at every input the clipped cube
approximation belongs to the convex hull of the function's values on the unit
cube](goal). -/
-- @node: structuralCubeApprox_mem_convexHull
lemma structuralCubeApprox_mem_convexHull {d k R : ℕ} (hR : 0 < R)
    (f : L1Vec d → L1Vec k) (x : L1Vec d) :
    structuralCubeApprox R f x ∈ convexHull ℝ (f '' unitCube d) := by
  apply (convexHull_mono ?_) (structuralCubeGridInterpolant_mem_convexHull hR
    (fun y => f ((R : ℝ)⁻¹ • y))
    (structural_smul_mem_gridCube R (coordinateClamp_mapsTo 0 1 zero_le_one x)))
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨_, structural_inv_smul_mem_unitCube hR hy, rfl⟩

/-- If [R is positive](hyp:hR), [the function is Lipschitz on the unit
cube](hyp:hf) with [nonnegative constant L](hyp:L), and [the input lies in the
unit cube](hyp:hx), then [the one-norm error of the clipped cube approximation
at that input is at most L times the input dimension divided by R](goal). -/
-- @node: structuralCubeApprox_error
lemma structuralCubeApprox_error {d k R : ℕ} (hR : 0 < R)
    (f : L1Vec d → L1Vec k) (L : ℝ≥0) (hf : LipschitzOnWith L f (unitCube d))
    {x : L1Vec d} (hx : x ∈ unitCube d) :
    ‖structuralCubeApprox R f x - f x‖ ≤ L * d / R := by
  have hRr : (R : ℝ) ≠ 0 := by exact_mod_cast hR.ne'
  have hc : coordinateClamp 0 1 x = x := by
    apply PiLp.ext
    intro j
    change max 0 (min (x.ofLp j) 1) = x.ofLp j
    rw [min_eq_left (hx j).2, max_eq_right (hx j).1]
  have he := structuralCubeGridInterpolant_error hR _ _
    (structural_rescaled_lipschitzOn hR f L hf) (structural_smul_mem_gridCube R hx)
  simpa [structuralCubeApprox, hc, smul_smul, inv_mul_cancel₀ hRr, div_eq_mul_inv,
    mul_comm, mul_left_comm, mul_assoc] using he


/-- [The clipped cube approximation is exactly represented by a ReLU network
with width the maximum of d and (R + 1) to the power d times 6(d + 1) squared,
and depth the ceiling of the base-two logarithm of (d + 1) squared plus three](goal). -/
-- @node: structuralCubeApprox_network
lemma structuralCubeApprox_network (d k R : ℕ) (f : L1Vec d → L1Vec k) :
    ∃ Q : ReLUNet d k (max ((R+1)^d * (6*((d+1)*(d+1)))) d)
        (Nat.clog 2 ((d+1)*(d+1)) + 1 + 2),
      Q.eval = structuralCubeApprox R f := by
  obtain ⟨q, hq⟩ := structuralGridInterpolant_network (structuralCubeGrid d R)
    (fun y => f ((R : ℝ)⁻¹ • y))
  obtain ⟨r, hr⟩ := relu_affine_precomp q (diagonalWeight d (R : ℝ)) (fun _ => 0)
  obtain ⟨Q, hQ⟩ := relu_clamped_input r 0 1 zero_le_one
  have hw : max ((structuralCubeGrid d R).card * (6*((d+1)*(d+1)))) d ≤
      max ((R+1)^d * (6*((d+1)*(d+1)))) d := by rw [structuralCubeGrid_card]
  refine ⟨Q.widen hw, ?_⟩
  funext x
  rw [ReLUNet.widen_eval, hQ, Function.comp_apply, hr, hq]
  change structuralGridInterpolant _ _ _ = structuralGridInterpolant _ _ _
  congr 1
  apply PiLp.ext
  intro j
  simp [diagonalWeight_sum]

/-- If [R is positive](hyp:hR) and [the function is Lipschitz on the unit
cube](hyp:hf) with [nonnegative constant L](hyp:L), then [there exists a ReLU
network with width the maximum of d and (R + 1) to the power d times 6(d + 1)
squared, and depth the ceiling of the base-two logarithm of (d + 1) squared
plus three, that is globally Lipschitz with constant L, takes all its values
in the convex hull of the function's unit-cube values, and has one-norm error
at most L times d divided by R throughout the unit cube](goal). -/
-- @node: structural_lipschitz_approx_mesh
lemma structural_lipschitz_approx_mesh (d k R : ℕ) (hR : 0 < R)
    (L : ℝ≥0) (f : L1Vec d → L1Vec k)
    (hf : LipschitzOnWith L f (unitCube d)) :
    ∃ Q : ReLUNet d k (max ((R+1)^d * (6*((d+1)*(d+1)))) d)
        (Nat.clog 2 ((d+1)*(d+1)) + 1 + 2),
      LipschitzWith L Q.eval ∧
      (∀ x, Q.eval x ∈ convexHull ℝ (f '' unitCube d)) ∧
      ∀ x ∈ unitCube d, ‖Q.eval x - f x‖ ≤ L * d / R := by
  obtain ⟨Q, hQ⟩ := structuralCubeApprox_network d k R f
  refine ⟨Q, ?_, ?_, ?_⟩
  · rw [hQ]
    exact structuralCubeApprox_lipschitz hR f L hf
  · rw [hQ]
    exact structuralCubeApprox_mem_convexHull hR f
  · rw [hQ]
    exact fun _ hx => structuralCubeApprox_error hR f L hf hx

end
end Papers.TbsNeuralCausalPi

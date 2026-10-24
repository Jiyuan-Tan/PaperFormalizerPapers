module

public import Papers.OaiPairedStatesHamiltonian.Helpers.PairCycleLift
public import Papers.OaiPairedStatesHamiltonian.Helpers.CancelDelta
public import Papers.OaiPairedStatesHamiltonian.Helpers.ForestAsymptotics

/-! Cycle-by-cycle factorization of a group of ordered pairs. -/

@[expose] public section

namespace OaiPairedStatesHamiltonian

open Classical
attribute [local instance] propDecidable
set_option linter.style.openClassical false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

variable (T : SphereMap) (col : T.Face → Bool) (t0 : T.Face)

-- @node: pairTriangleOrbit
/-- For [a sphere map](hyp:T) with [a face coloring](hyp:col) and [a designated outer
face](hyp:t0), [an ordered pair of states](hyp:p) assigns to [each black non-outer
triangle](hyp:t) [the orbit of its first state's chosen vertex under the permutation
induced by the pair](goal). -/
noncomputable def pairTriangleOrbit (p : Pair T col t0) (t : blackNonOuter T col t0) :=
  orbitOf (pairPermutation T col t0 p.val.1 p.val.2) (p.val.1.val t)

-- @node: pairOrbit_sum_darts
/-- If [the map is a sphere triangulation](hyp:hT) and [adjacent faces have opposite
colors](hyp:hcol), [summing any additive dart-valued quantity over the paired darts
of the triangles in a permutation orbit gives the same result as summing that
quantity along the associated cycle](goal). -/
lemma pairOrbit_sum_darts (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col)
    (p : Pair T col t0) (k : orbitType (pairPermutation T col t0 p.val.1 p.val.2))
    {A : Type*} [AddCommMonoid A] (F : T.Dart → A) :
    (∑ t ∈ Finset.univ.filter (fun t => pairTriangleOrbit T col t0 p t = k),
      F (pairedDart T col t0 hT p.val.1 p.val.2 p.property t)) =
      ((pairCycleAt T col t0 hT hcol p k).val.map F).sum := by
  rw [← List.sum_toFinset _ ((pairCycleAt T col t0 hT hcol p k).property.2.of_map T.vert)]
  apply Finset.sum_bij (fun t _ => pairedDart T col t0 hT p.val.1 p.val.2 p.property t)
  · intro t ht
    exact List.mem_toFinset.mpr ((pairCycleAt_mem_iff T col t0 hT hcol p k _).mpr
      ⟨t, (Finset.mem_filter.mp ht).2, rfl⟩)
  · intro t ht u hu he
    exact pairedDart_injective T col t0 hT _ _ p.property he
  · intro d hd
    obtain ⟨t, ht, rfl⟩ := (pairCycleAt_mem_iff T col t0 hT hcol p k d).mp
      (List.mem_toFinset.mp hd)
    exact ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩, rfl⟩
  · intro t ht
    rfl

-- @node: pairOrbitDelta
/-- For [a sphere map](hyp:T), [a face coloring](hyp:col), [an outer face](hyp:t0),
and [a sphere triangulation structure](hyp:hT), the [phase increment of an
orbit](goal) of [an ordered pair of states](hyp:p), at [the selected permutation
orbit](hyp:k), is the sum of the normalized-coloring increments of the paired darts
supplied by its triangles. -/
noncomputable def pairOrbitDelta (hT : IsSphereTriangulation T) (p : Pair T col t0)
    (k : orbitType (pairPermutation T col t0 p.val.1 p.val.2)) : ℤ :=
  ∑ t ∈ Finset.univ.filter (fun t => pairTriangleOrbit T col t0 p t = k),
    delta T (normalizedColoring T col t0) (pairedDart T col t0 hT _ _ p.property t)

-- @node: pairOrbitWeight
/-- For [a sphere map](hyp:T) with [a face coloring](hyp:col) and [an outer
face](hyp:t0), the [orbit weight](goal) for [an ordered pair of states](hyp:p),
[triangle-vertex incidence weights](hyp:a), [a state](hyp:s), and [a permutation
orbit of the pair](hyp:k) is the sum, over triangles in that orbit, of the weights
at the vertices chosen by the state. -/
noncomputable def pairOrbitWeight (p : Pair T col t0) (a : IncidenceWeights T col t0)
    (s : State T col t0) (k : orbitType (pairPermutation T col t0 p.val.1 p.val.2)) : ℝ :=
  ∑ t ∈ Finset.univ.filter (fun t => pairTriangleOrbit T col t0 p t = k),
    a t ⟨(s.val t).val, s.property.incident t⟩

-- @node: pairCycleAt_paired
/-- If [the map is a sphere triangulation](hyp:hT) and [adjacent faces have opposite
colors](hyp:hcol), [every dart along the cycle associated with an orbit of an ordered
pair of states belongs to that pair's directed paired-edge set](goal). -/
lemma pairCycleAt_paired (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col)
    (p : Pair T col t0) (k : orbitType (pairPermutation T col t0 p.val.1 p.val.2)) :
    ∀ d ∈ (pairCycleAt T col t0 hT hcol p k).val,
      d ∈ pairedEdges T col t0 hT p.val.1 p.val.2 p.property := by
  intro d hd
  obtain ⟨t, ht, rfl⟩ := (pairCycleAt_mem_iff T col t0 hT hcol p k d).mp hd
  exact (pairedEdges_mem_iff T col t0 hT _ _ p.property _).mpr ⟨t, rfl⟩

-- @node: pairCycleAt_undirected
/-- If [the map is a sphere triangulation](hyp:hT) and [adjacent faces have opposite
colors](hyp:hcol), [the underlying edge of every dart along an orbit's associated
cycle belongs to the ordered pair's undirected paired-edge set](goal). -/
lemma pairCycleAt_undirected (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col)
    (p : Pair T col t0) (k : orbitType (pairPermutation T col t0 p.val.1 p.val.2)) :
    ∀ d ∈ (pairCycleAt T col t0 hT hcol p k).val,
      T.edgeOf d ∈ undirectedPairedEdges T col t0 hT p := by
  intro d hd
  exact Finset.mem_image.mpr ⟨d, pairCycleAt_paired T col t0 hT hcol p k d hd, rfl⟩

-- @node: pairOrbitDelta_eq
/-- If [the map is a sphere triangulation](hyp:hT) and [adjacent faces have opposite
colors](hyp:hcol), [an orbit's phase increment is minus three when its associated
cycle is counterclockwise relative to the outer face, and three otherwise](goal). -/
lemma pairOrbitDelta_eq (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col)
    (p : Pair T col t0) (k : orbitType (pairPermutation T col t0 p.val.1 p.val.2)) :
    pairOrbitDelta T col t0 hT p k =
      if T.IsCounterclockwise t0 (pairCycleAt T col t0 hT hcol p k) then -3 else 3 := by
  rw [pairOrbitDelta, pairOrbit_sum_darts T col t0 hT hcol]
  let choice : EdgeChoice T col t0 p.val.1 := fun t =>
    ⟨(p.val.2.val t).val, p.val.2.property.incident t,
      (pair_vertex_ne T col t0 _ _ p.property t).symm⟩
  have hC : ∀ d ∈ (pairCycleAt T col t0 hT hcol p k).val,
      d ∈ ChosenEdges T col t0 hT p.val.1 choice :=
    pairCycleAt_paired T col t0 hT hcol p k
  split_ifs with h
  · exact delta_sum_of_counterclockwise T hT col hcol t0 p.val.1 choice _ hC h
  · apply delta_sum_of_clockwise T hT col hcol t0 p.val.1 choice _ hC
    have hp := (T.cycle_sides_partition (pairCycleAt T col t0 hT hcol p k)).2
    have hm : t0 ∈ T.leftRegion (pairCycleAt T col t0 hT hcol p k) ∪
        T.rightRegion (pairCycleAt T col t0 hT hcol p k) := by rw [hp]; trivial
    exact hm.resolve_right h

-- @node: pairCycleIncidence_pairedDart_face
/-- If [the map is a sphere triangulation](hyp:hT), [adjacent faces have opposite
colors](hyp:hcol), and [the edge underlying a triangle's paired dart belongs to the
pair's undirected paired-edge set](hyp:hd), [the triangle recovered by the cycle
incidence construction from that dart is the original triangle](goal). -/
lemma pairCycleIncidence_pairedDart_face (hT : IsSphereTriangulation T)
    (hcol : PartitionColoring T col) (p : Pair T col t0) (t : blackNonOuter T col t0)
    (hd : T.edgeOf (pairedDart T col t0 hT _ _ p.property t) ∈
      undirectedPairedEdges T col t0 hT p) :
    (pairCycleIncidence T col t0 hT hcol p
      (pairedDart T col t0 hT _ _ p.property t) hd).1 = t := by
  obtain ⟨u, hu, he⟩ := pairCycleFace_edge T col t0 hT hcol p _ hd
  exact hu.trans (pairedDart_same_black_face T col t0 hT hcol p p t u he).symm

-- @node: pairOrbitWeight_eq_cycle_sum
/-- If [the map is a sphere triangulation](hyp:hT) and [adjacent faces have opposite
colors](hyp:hcol), [an orbit's weight in the second state equals the oriented weight
of its associated cycle, while its weight in the first state equals the oriented
weight of the reversed cycle, with the Boolean choice selecting the corresponding
equality](goal). -/
lemma pairOrbitWeight_eq_cycle_sum (hT : IsSphereTriangulation T)
    (hcol : PartitionColoring T col) (p : Pair T col t0) (a : IncidenceWeights T col t0)
    (k : orbitType (pairPermutation T col t0 p.val.1 p.val.2)) (b : Bool) :
    pairOrbitWeight T col t0 p a (if b then p.val.2 else p.val.1) k =
      if b then orientedPairCycleWeight T col t0 hT hcol a p
        (pairCycleAt T col t0 hT hcol p k) (pairCycleAt_undirected T col t0 hT hcol p k)
      else orientedPairCycleWeight T col t0 hT hcol a p
        (reverseCycle T (pairCycleAt T col t0 hT hcol p k))
        (reverseCycle_paired T col t0 hT p _ (pairCycleAt_undirected T col t0 hT hcol p k)) := by
  let C := pairCycleAt T col t0 hT hcol p k
  have hc := pairCycleAt_undirected T col t0 hT hcol p k
  have hm (t : blackNonOuter T col t0) (ht : t ∈ Finset.univ.filter
      (fun t => pairTriangleOrbit T col t0 p t = k)) :
      pairedDart T col t0 hT _ _ p.property t ∈ C.val :=
    (pairCycleAt_mem_iff T col t0 hT hcol p k _).mpr ⟨t, (Finset.mem_filter.mp ht).2, rfl⟩
  cases b
  all_goals
    simp only [Bool.false_eq_true, ↓reduceIte]
    first
    | rw [orientedPairCycleWeight_reverse_eq_sum T col t0 hT hcol a p C hc]
    | rw [orientedPairCycleWeight_eq_sum T col t0 hT hcol a p C hc]
    unfold pairOrbitWeight
    apply Finset.sum_bij (fun t ht => (⟨pairedDart T col t0 hT _ _ p.property t, hm t ht⟩ :
      {d // d ∈ C.val}))
    · intro t ht; exact Finset.mem_univ _
    · intro t ht u hu he
      exact pairedDart_injective T col t0 hT _ _ p.property (congrArg Subtype.val he)
    · intro d hd
      obtain ⟨t, ht, he⟩ := (pairCycleAt_mem_iff T col t0 hT hcol p k d.val).mp d.property
      exact ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩, Subtype.ext he⟩
    · intro t ht
      have hf := pairCycleIncidence_pairedDart_face T col t0 hT hcol p t
        (hc _ (hm t ht))
      have hs := pairedDart_spec T col t0 hT _ _ p.property t
      dsimp only
      congr 1
      · exact hf.symm
      · apply (Subtype.heq_iff_coe_eq (fun v => by
          rw [congrArg Subtype.val hf])).mpr
        first | exact hs.1.symm | exact hs.2.1.symm

-- @node: pairOrbitSign
/-- For [a sphere map](hyp:T), [a face coloring](hyp:col), [an outer face](hyp:t0),
[a sphere triangulation structure](hyp:hT), and [a coloring in which adjacent faces
have opposite colors](hyp:hcol), the [sign of an orbit](goal) of [an ordered pair of
states](hyp:p), at [the selected permutation orbit](hyp:k), is [minus one if its
cycle is counterclockwise relative to the outer face](step:1) and [one
otherwise](step:2). -/
noncomputable def pairOrbitSign (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col)
    (p : Pair T col t0) (k : orbitType (pairPermutation T col t0 p.val.1 p.val.2)) : ℤ :=
  if T.IsCounterclockwise t0 (pairCycleAt T col t0 hT hcol p k) then -1 else 1

-- @node: switchPair_deltaSum
/-- If [the map is a sphere triangulation](hyp:hT) and [adjacent faces have opposite
colors](hyp:hcol), [the total phase increment after switching a pair by Boolean
orbit choices is the sum of the original orbit increments, retaining an increment
for a true choice and negating it for a false choice](goal). -/
lemma switchPair_deltaSum (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col)
    (p : Pair T col t0)
    (b : orbitType (pairPermutation T col t0 p.val.1 p.val.2) → Bool) :
    letI := Fintype.ofFinite (orbitType (pairPermutation T col t0 p.val.1 p.val.2))
    pairDeltaSum T col t0 hT (switchPair T col t0 p b).val.1
      (switchPair T col t0 p b).val.2 (switchPair T col t0 p b).property =
      ∑ k, if b k then pairOrbitDelta T col t0 hT p k else -pairOrbitDelta T col t0 hT p k := by
  letI := Fintype.ofFinite (orbitType (pairPermutation T col t0 p.val.1 p.val.2))
  change (∑ t, delta T (normalizedColoring T col t0)
    (pairedDart T col t0 hT _ _ (switchPair T col t0 p b).property t)) = _
  rw [← Finset.sum_fiberwise Finset.univ (pairTriangleOrbit T col t0 p)]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [pairOrbitDelta, ← Finset.sum_neg_distrib]
  by_cases hb : b k = true <;> simp only [hb, ↓reduceIte]
  all_goals
    apply Finset.sum_congr rfl
    intro t ht
    have ht' := (Finset.mem_filter.mp ht).2
    rw [switchPair_dart]
    change delta T (normalizedColoring T col t0)
      (if b (pairTriangleOrbit T col t0 p t) then _ else _) = _
    rw [ht']
    simp only [hb, ↓reduceIte]
    try exact delta_edgeInv T _ (normalizedColoring_partition T col hcol t0) _

-- @node: switchPair_J
/-- If [the map is a sphere triangulation](hyp:hT) and [adjacent faces have opposite
colors](hyp:hcol), [the phase index of a pair switched by Boolean orbit choices is
the sum of the original orbit signs, retaining each sign for a true choice and
negating it for a false choice](goal). -/
lemma switchPair_J (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col)
    (p : Pair T col t0)
    (b : orbitType (pairPermutation T col t0 p.val.1 p.val.2) → Bool) :
    letI := Fintype.ofFinite (orbitType (pairPermutation T col t0 p.val.1 p.val.2))
    J T col t0 hT (switchPair T col t0 p b).val.1
      (switchPair T col t0 p b).val.2 (switchPair T col t0 p b).property =
      ∑ k, if b k then pairOrbitSign T col t0 hT hcol p k
        else -pairOrbitSign T col t0 hT hcol p k := by
  letI := Fintype.ofFinite (orbitType (pairPermutation T col t0 p.val.1 p.val.2))
  have h := three_mul_J T col t0 hT hcol _ _ (switchPair T col t0 p b).property
  rw [switchPair_deltaSum T col t0 hT hcol p b] at h
  have he : (∑ k, if b k then pairOrbitDelta T col t0 hT p k
      else -pairOrbitDelta T col t0 hT p k) =
      3 * ∑ k, if b k then pairOrbitSign T col t0 hT hcol p k
        else -pairOrbitSign T col t0 hT hcol p k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [pairOrbitDelta_eq T col t0 hT hcol p k]
    simp only [pairOrbitSign]
    split_ifs <;> norm_num
  linarith

-- @node: switchPair_omega
/-- [The total weight of the second state of a switched pair is the sum of the
original second state's orbit weights for true Boolean choices and the original
first state's orbit weights for false choices](goal). -/
lemma switchPair_omega (p : Pair T col t0) (a : IncidenceWeights T col t0)
    (b : orbitType (pairPermutation T col t0 p.val.1 p.val.2) → Bool) :
    letI := Fintype.ofFinite (orbitType (pairPermutation T col t0 p.val.1 p.val.2))
    omega T col t0 a (switchPair T col t0 p b).val.2 =
      ∑ k, if b k then pairOrbitWeight T col t0 p a p.val.2 k
        else pairOrbitWeight T col t0 p a p.val.1 k := by
  letI := Fintype.ofFinite (orbitType (pairPermutation T col t0 p.val.1 p.val.2))
  unfold omega
  rw [← Finset.sum_fiberwise Finset.univ (pairTriangleOrbit T col t0 p)]
  apply Finset.sum_congr rfl
  intro k hk
  unfold pairOrbitWeight
  by_cases hb : b k = true <;> simp only [hb, ↓reduceIte]
  all_goals
    apply Finset.sum_congr rfl
    intro t ht
    have ht' := (Finset.mem_filter.mp ht).2
    have he := (switchPair_endpoints T col t0 p b t).2
    change (switchPair T col t0 p b).val.2.val t =
      (if b (pairTriangleOrbit T col t0 p t) then p.val.2.val t else p.val.1.val t) at he
    rw [ht'] at he
    simp only [hb, Bool.false_eq_true, ↓reduceIte] at he
    congr 1
    apply Subtype.ext
    exact congrArg (fun v : nonRoot T t0 => v.val) he

-- @node: I_zpow_sum
/-- [The imaginary unit raised to a finite sum of integer exponents equals the
product of the imaginary unit raised to each exponent](goal). -/
lemma I_zpow_sum {ι : Type*} (s : Finset ι) (j : ι → ℤ) :
    Complex.I ^ (∑ i ∈ s, j i) = ∏ i ∈ s, Complex.I ^ j i := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih =>
    simp only [Finset.sum_cons, Finset.prod_cons, zpow_add₀ Complex.I_ne_zero, ih]

-- @node: boolean_phase_exp_sum
/-- [Summing over all Boolean selections the imaginary unit raised to the sum of
the selected signed integer phases, multiplied by the exponential of a real scale
times the sum of the selected weights, equals the product of the two-term sums
formed at each index: positive phase with the first weight, and negative phase
with the second weight](goal). -/
lemma boolean_phase_exp_sum {ι : Type*} [Fintype ι] (j : ι → ℤ) (u v : ι → ℝ) (x : ℝ) :
    (∑ b : ι → Bool,
      Complex.I ^ (∑ i, if b i then j i else -j i) *
        Complex.exp ((x * ∑ i, if b i then u i else v i : ℝ) : ℂ)) =
    ∏ i, (Complex.I ^ j i * Complex.exp ((x * u i : ℝ) : ℂ) +
      Complex.I ^ (-j i) * Complex.exp ((x * v i : ℝ) : ℂ)) := by
  classical
  have he (b : ι → Bool) :
      Complex.I ^ (∑ i, if b i then j i else -j i) *
        Complex.exp ((x * ∑ i, if b i then u i else v i : ℝ) : ℂ) =
      ∏ i, if b i then Complex.I ^ j i * Complex.exp ((x * u i : ℝ) : ℂ)
        else Complex.I ^ (-j i) * Complex.exp ((x * v i : ℝ) : ℂ) := by
    rw [I_zpow_sum, Finset.mul_sum, Complex.ofReal_sum, Complex.exp_sum,
      ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    cases b i <;> rfl
  simp_rw [he]
  have hp := Fintype.prod_sum (fun i (b : Bool) =>
    if b then Complex.I ^ j i * Complex.exp ((x * u i : ℝ) : ℂ)
      else Complex.I ^ (-j i) * Complex.exp ((x * v i : ℝ) : ℂ))
  simpa only [Fintype.sum_bool, ↓reduceIte, Bool.false_eq_true] using hp.symm

-- @node: pair_group_exp_product
/-- If [the map is a sphere triangulation](hyp:hT) and [adjacent faces have opposite
colors](hyp:hcol), [the sum over all ordered pairs with the reference pair's group
key of their phase factors times the exponentials of the scaled second-state
weights equals a product over the reference pair's orbits, each factor adding the
orbit's phase factor times its second-state weight exponential to the opposite
phase factor times its first-state weight exponential](goal). -/
lemma pair_group_exp_product (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col)
    (p : Pair T col t0) (a : IncidenceWeights T col t0) (x : ℝ) :
    letI := Fintype.ofFinite (orbitType (pairPermutation T col t0 p.val.1 p.val.2))
    (∑ q ∈ Finset.univ.filter (fun q => groupKey T col t0 hT q = groupKey T col t0 hT p),
      Complex.I ^ J T col t0 hT q.val.1 q.val.2 q.property *
        Complex.exp ((x * omega T col t0 a q.val.2 : ℝ) : ℂ)) =
      ∏ k, (Complex.I ^ pairOrbitSign T col t0 hT hcol p k *
          Complex.exp ((x * pairOrbitWeight T col t0 p a p.val.2 k : ℝ) : ℂ) +
        Complex.I ^ (-pairOrbitSign T col t0 hT hcol p k) *
          Complex.exp ((x * pairOrbitWeight T col t0 p a p.val.1 k : ℝ) : ℂ)) := by
  letI := Fintype.ofFinite (orbitType (pairPermutation T col t0 p.val.1 p.val.2))
  rw [← boolean_phase_exp_sum]
  rw [Finset.sum_subtype (F := inferInstance) (p := fun q => groupKey T col t0 hT q = groupKey T col t0 hT p)
    _ (fun q => by simp)]
  classical
  let e := pairGroupOrbitEquiv T col t0 hT hcol p
  apply Finset.sum_bij (fun q _ => e q)
  · intro q hq; simp only [Finset.mem_univ]
  · intro q hq r hr he; exact e.injective he
  · intro b hb; exact ⟨e.symm b, by simp only [Finset.mem_univ], e.apply_symm_apply b⟩
  intro q hmem
  have hq := congrArg Subtype.val (e.symm_apply_apply q)
  change switchPair T col t0 p (e q) = q.val at hq
  rw [← hq, switchPair_J T col t0 hT hcol p (e q), switchPair_omega]

-- @node: pairOrbitLarge
/-- For [a sphere map](hyp:T), [a face coloring](hyp:col), [an outer face](hyp:t0),
[a sphere triangulation structure](hyp:hT), and [a coloring in which adjacent faces
have opposite colors](hyp:hcol), the [designated large orbit weight](goal) for
[an ordered pair of states](hyp:p), [incidence weights](hyp:a), and [a permutation
orbit](hyp:k) is [the second state's orbit weight when the associated cycle is
counterclockwise relative to the outer face](step:1), and [the first state's orbit
weight otherwise](step:2). -/
noncomputable def pairOrbitLarge (hT : IsSphereTriangulation T)
    (hcol : PartitionColoring T col) (p : Pair T col t0) (a : IncidenceWeights T col t0)
    (k : orbitType (pairPermutation T col t0 p.val.1 p.val.2)) : ℝ :=
  if T.IsCounterclockwise t0 (pairCycleAt T col t0 hT hcol p k)
    then pairOrbitWeight T col t0 p a p.val.2 k else pairOrbitWeight T col t0 p a p.val.1 k

-- @node: pairOrbitSmall
/-- For [a sphere map](hyp:T), [a face coloring](hyp:col), [an outer face](hyp:t0),
[a sphere triangulation structure](hyp:hT), and [a coloring in which adjacent faces
have opposite colors](hyp:hcol), the [designated small orbit weight](goal) for
[an ordered pair of states](hyp:p), [incidence weights](hyp:a), and [a permutation
orbit](hyp:k) is [the first state's orbit weight when the associated cycle is
counterclockwise relative to the outer face](step:1), and [the second state's orbit
weight otherwise](step:2). -/
noncomputable def pairOrbitSmall (hT : IsSphereTriangulation T)
    (hcol : PartitionColoring T col) (p : Pair T col t0) (a : IncidenceWeights T col t0)
    (k : orbitType (pairPermutation T col t0 p.val.1 p.val.2)) : ℝ :=
  if T.IsCounterclockwise t0 (pairCycleAt T col t0 hT hcol p k)
    then pairOrbitWeight T col t0 p a p.val.1 k else pairOrbitWeight T col t0 p a p.val.2 k

-- @node: pairOrbit_weight_gap
/-- If [the map is a sphere triangulation](hyp:hT), [adjacent faces have opposite
colors](hyp:hcol), and [every counterclockwise cycle of the bounded spoke graph has
strictly positive signed spoke weight](hyp:hpos), [the designated small weight is
strictly less than the designated large weight for every orbit of an ordered pair
of states](goal). -/
lemma pairOrbit_weight_gap (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col)
    (p : Pair T col t0) (a : IncidenceWeights T col t0)
    (hpos : ∀ C : (spokeGraphBounded T col t0 hT hcol).Cycle,
      (spokeGraphBounded T col t0 hT hcol).IsCounterclockwise (spokeOuter T col t0 hT hcol) C →
        0 < signedSpokeWeight T col t0 hT hcol a C)
    (k : orbitType (pairPermutation T col t0 p.val.1 p.val.2)) :
    pairOrbitSmall T col t0 hT hcol p a k < pairOrbitLarge T col t0 hT hcol p a k := by
  let C := pairCycleAt T col t0 hT hcol p k
  have hc := pairCycleAt_undirected T col t0 hT hcol p k
  have hh := pairOrbitWeight_eq_cycle_sum T col t0 hT hcol p a k true
  have ht := pairOrbitWeight_eq_cycle_sum T col t0 hT hcol p a k false
  simp only [Bool.false_eq_true, ↓reduceIte] at hh ht
  have hw := pairedCycle_weight_comparison T col t0 hT hcol a hpos p C hc
  have hp := T.cycle_sides_partition C
  dsimp only [C] at hw hp
  by_cases h : T.IsCounterclockwise t0 (pairCycleAt T col t0 hT hcol p k)
  · have hn : ¬ T.IsClockwise t0 (pairCycleAt T col t0 hT hcol p k) := fun hc => Set.disjoint_left.mp hp.1 hc h
    simpa only [counterclockwiseCycleWeight, clockwiseCycleWeight, h, hn, ↓reduceIte,
      ← hh, ← ht, pairOrbitSmall, pairOrbitLarge] using hw
  · have hc : T.IsClockwise t0 (pairCycleAt T col t0 hT hcol p k) := by
      have hm : t0 ∈ T.leftRegion C ∪ T.rightRegion C := by rw [hp.2]; trivial
      exact hm.resolve_right h
    simpa only [counterclockwiseCycleWeight, clockwiseCycleWeight, h, hc, ↓reduceIte,
      ← hh, ← ht, pairOrbitSmall, pairOrbitLarge] using hw

-- @node: pair_group_exp_product_normalized
/-- If [the map is a sphere triangulation](hyp:hT) and [adjacent faces have opposite
colors](hyp:hcol), [the sum of phase factors times scaled second-state weight
exponentials over the reference pair's group equals minus the imaginary unit raised
to the number of its orbits, multiplied by the product over those orbits of the
large-weight exponential minus the small-weight exponential](goal). -/
lemma pair_group_exp_product_normalized (hT : IsSphereTriangulation T)
    (hcol : PartitionColoring T col) (p : Pair T col t0) (a : IncidenceWeights T col t0) (x : ℝ) :
    letI := Fintype.ofFinite (orbitType (pairPermutation T col t0 p.val.1 p.val.2))
    (∑ q ∈ Finset.univ.filter (fun q => groupKey T col t0 hT q = groupKey T col t0 hT p),
      Complex.I ^ J T col t0 hT q.val.1 q.val.2 q.property *
        Complex.exp ((x * omega T col t0 a q.val.2 : ℝ) : ℂ)) =
      (-Complex.I) ^ Fintype.card (orbitType (pairPermutation T col t0 p.val.1 p.val.2)) *
        ((∏ k, (Real.exp (x * pairOrbitLarge T col t0 hT hcol p a k) -
          Real.exp (x * pairOrbitSmall T col t0 hT hcol p a k)) : ℝ) : ℂ) := by
  letI := Fintype.ofFinite (orbitType (pairPermutation T col t0 p.val.1 p.val.2))
  rw [pair_group_exp_product T col t0 hT hcol p a x]
  have he : (-Complex.I) ^ Fintype.card (orbitType (pairPermutation T col t0 p.val.1 p.val.2)) =
      ∏ _k : orbitType (pairPermutation T col t0 p.val.1 p.val.2), (-Complex.I) := by simp
  rw [Complex.ofReal_prod, he, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k hk
  unfold pairOrbitSign pairOrbitLarge pairOrbitSmall
  split_ifs <;> simp only [neg_neg, zpow_neg, zpow_one, Complex.inv_I, Complex.ofReal_sub,
    Complex.ofReal_exp] <;> ring

-- @node: pair_group_positive_leading_term
/-- If [the map is a sphere triangulation](hyp:hT), [adjacent faces have opposite
colors](hyp:hcol), and [every counterclockwise cycle of the bounded spoke graph has
strictly positive signed spoke weight](hyp:hpos), [there exist a nonnegative integer
and a real function whose ratio to that power of its argument tends to a strictly
positive constant as the argument approaches zero through nonzero values, such that
the group's sum of phase factors times scaled second-state weight exponentials
equals minus the imaginary unit raised to that integer times the function, for
every real argument](goal). -/
lemma pair_group_positive_leading_term (hT : IsSphereTriangulation T)
    (hcol : PartitionColoring T col) (p : Pair T col t0) (a : IncidenceWeights T col t0)
    (hpos : ∀ C : (spokeGraphBounded T col t0 hT hcol).Cycle,
      (spokeGraphBounded T col t0 hT hcol).IsCounterclockwise (spokeOuter T col t0 hT hcol) C →
        0 < signedSpokeWeight T col t0 hT hcol a C) :
    ∃ (n : ℕ) (f : ℝ → ℝ) (k : ℝ), 0 < k ∧
      Filter.Tendsto (fun x => f x / x ^ n) (nhdsWithin 0 {0}ᶜ) (nhds k) ∧
      ∀ x, (∑ q ∈ Finset.univ.filter
        (fun q => groupKey T col t0 hT q = groupKey T col t0 hT p),
        Complex.I ^ J T col t0 hT q.val.1 q.val.2 q.property *
          Complex.exp ((x * omega T col t0 a q.val.2 : ℝ) : ℂ)) =
        (-Complex.I) ^ n * (f x : ℂ) := by
  letI := Fintype.ofFinite (orbitType (pairPermutation T col t0 p.val.1 p.val.2))
  let u := pairOrbitLarge T col t0 hT hcol p a
  let v := pairOrbitSmall T col t0 hT hcol p a
  refine ⟨Fintype.card (orbitType (pairPermutation T col t0 p.val.1 p.val.2)),
    fun x => ∏ i, (Real.exp (x * u i) - Real.exp (x * v i)),
    ∏ i, (u i - v i), ?_, ?_, ?_⟩
  · exact Finset.prod_pos (fun i hi => sub_pos.mpr
      (pairOrbit_weight_gap T col t0 hT hcol p a hpos i))
  · simpa only [Finset.card_univ] using cycle_product_leading_term Finset.univ u v
  · intro x
    exact pair_group_exp_product_normalized T col t0 hT hcol p a x

end OaiPairedStatesHamiltonian

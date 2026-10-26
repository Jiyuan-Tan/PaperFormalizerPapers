module
public import Papers.OaiSharpThresholdMonotone.Basic

/-! # Support vertices and a low-degree vertex of an edge support -/

@[expose] public section

open scoped BigOperators

namespace Papers.OaiSharpThresholdMonotone

variable {n : ℕ}

/-- On [a fixed number of labeled vertices](hyp:n), for [a finite set of graph edges](hyp:S)
that [is nonempty](hyp:_hS),
its [support size](goal) is its number of edges. -/
def supportSize (S : Finset (GraphEdge n)) (_hS : S.Nonempty) : ℕ :=
  S.card -- @realizes s(edge count restricted to nonempty supports)

/-- On [a fixed number of labeled vertices](hyp:n), for [a finite set of graph edges](hyp:S),
its [support vertices](goal) are
all vertices incident to at least one of those edges. -/
def supportVertices (S : Finset (GraphEdge n)) : Finset (Fin n) :=
  S.biUnion (fun e => e.val) -- @realizes V(S)(nonisolated support vertices)

/-- On [a fixed number of labeled vertices](hyp:n), for [a finite set of graph edges](hyp:S),
its [support vertex count](goal)
is the number of vertices incident to at least one of its edges. -/
def supportVertexCount (S : Finset (GraphEdge n)) : ℕ :=
  (supportVertices S).card -- @realizes v(number of nonisolated vertices)

/-- On [a fixed number of labeled vertices](hyp:n), for [a finite set of graph edges](hyp:S)
and [a vertex](hyp:u), the vertex's
[degree in the support](goal) is the number of edges in the set incident to it. -/
def supportDegree (S : Finset (GraphEdge n)) (u : Fin n) : ℕ :=
  (S.filter (fun e => u ∈ e.val)).card -- @realizes d_S(u)(degree in the support graph)

-- @node: support_card_le_choose
/-- For [a finite edge support](hyp:S), [the number of edges in the support is at most the number of unordered pairs
of its incident vertices](goal). -/
lemma support_card_le_choose (S : Finset (GraphEdge n)) :
    S.card ≤ (supportVertexCount S).choose 2 := by
  classical
  calc
    S.card = (S.image Subtype.val).card :=
      (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ ≤ ((supportVertices S).powersetCard 2).card := by
      apply Finset.card_le_card
      intro e he
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
      exact Finset.mem_powersetCard.mpr ⟨by
        intro u hu
        exact Finset.mem_biUnion.mpr ⟨a, ha, hu⟩, a.property⟩
    _ = _ := Finset.card_powersetCard _ _

-- @node: supportVertices_card_le
/-- For [a finite edge support](hyp:S), [the number of vertices incident to the support is at most twice its
number of edges](goal). -/
lemma supportVertices_card_le (S : Finset (GraphEdge n)) :
    (supportVertices S).card ≤ 2 * S.card := by
  calc
    (supportVertices S).card ≤ ∑ e ∈ S, e.val.card := Finset.card_biUnion_le
    _ = 2 * S.card := by
      have hc (e : GraphEdge n) : e.val.card = 2 := e.property
      simp [hc, mul_comm]

-- @node: sum_supportDegree
/-- For [a finite edge support](hyp:S), [the sum of degrees over the vertices incident to the support equals
twice the number of edges in that support](goal). -/
lemma sum_supportDegree (S : Finset (GraphEdge n)) :
    ∑ u ∈ supportVertices S, supportDegree S u = 2 * S.card := by
  classical
  unfold supportDegree
  simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  simp only [Finset.sum_const, smul_eq_mul, mul_one]
  rw [Finset.sum_comm]
  calc
    (∑ e ∈ S, ∑ u ∈ supportVertices S, if u ∈ e.val then 1 else 0) =
        ∑ e ∈ S, e.val.card := by
      apply Finset.sum_congr rfl
      intro e he
      rw [← Finset.sum_filter]
      have hfilter : (supportVertices S).filter (fun u => u ∈ e.val) = e.val := by
        ext u
        simp only [Finset.mem_filter, and_iff_right_iff_imp]
        intro hu
        exact Finset.mem_biUnion.mpr ⟨e, he, hu⟩
      simp [hfilter]
    _ = 2 * S.card := by
      have hc (e : GraphEdge n) : e.val.card = 2 := e.property
      simp [hc, mul_comm]

-- @node: exists_support_vertex_degree_le
/-- For [a finite edge support](hyp:S), if [the support contains at least one edge](hyp:hS), then [it has an incident
vertex whose degree is at least one, at most the average degree, and at most the
square root of twice the number of support edges](goal). -/
lemma exists_support_vertex_degree_le (S : Finset (GraphEdge n)) (hS : 1 ≤ S.card) :
    ∃ u ∈ supportVertices S, -- @realizes u(vertex chosen separately for each nonempty support)
      1 ≤ supportDegree S u ∧
      (supportDegree S u : ℝ) ≤ 2 * S.card / (supportVertexCount S : ℝ) ∧
      (supportDegree S u : ℝ) ≤ Real.sqrt (2 * S.card) := by
  classical
  obtain ⟨e, he⟩ := Finset.one_le_card.mp hS
  have hepos : 0 < e.val.card := by rw [e.property]; norm_num
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hepos
  have hV : (supportVertices S).Nonempty :=
    ⟨w, Finset.mem_biUnion.mpr ⟨e, he, hw⟩⟩
  have hvnat : 1 ≤ supportVertexCount S := Finset.one_le_card.mpr hV
  have hv : 0 < (supportVertexCount S : ℝ) := by exact_mod_cast hvnat
  have hsum : (∑ u ∈ supportVertices S, (supportDegree S u : ℝ)) =
      2 * S.card := by exact_mod_cast sum_supportDegree S
  -- Some support vertex has degree at most the average degree.
  have havg : (∑ u ∈ supportVertices S, (supportDegree S u : ℝ)) ≤
      ∑ _u ∈ supportVertices S, 2 * (S.card : ℝ) / supportVertexCount S := by
    rw [hsum, Finset.sum_const, nsmul_eq_mul]
    change _ ≤ (supportVertexCount S : ℝ) * _
    exact le_of_eq (by field_simp)
  obtain ⟨u, hu, hdu⟩ := Finset.exists_le_of_sum_le hV havg
  have hdpos : 1 ≤ supportDegree S u := by
    obtain ⟨a, ha, hua⟩ := Finset.mem_biUnion.mp hu
    exact Finset.one_le_card.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, hua⟩⟩
  -- A simple support has at most choose(v, 2) edges.
  have hcount : 2 * S.card ≤ supportVertexCount S * (supportVertexCount S - 1) := by
    have hc := support_card_le_choose S
    rw [Nat.choose_two_right] at hc
    omega
  have hcountR : 2 * (S.card : ℝ) ≤
      (supportVertexCount S : ℝ) * ((supportVertexCount S : ℝ) - 1) := by
    exact_mod_cast hcount
  have hsqrt : Real.sqrt (2 * (S.card : ℝ)) ≤ supportVertexCount S := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨hv.le, by nlinarith⟩
  have havgsqrt : 2 * (S.card : ℝ) / supportVertexCount S ≤
      Real.sqrt (2 * (S.card : ℝ)) := by
    apply (div_le_iff₀ hv).mpr
    have hsq := Real.sq_sqrt (show 0 ≤ 2 * (S.card : ℝ) by positivity)
    have hmul := mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg (2 * (S.card : ℝ)))
    nlinarith
  exact ⟨u, hu, hdpos, hdu, hdu.trans havgsqrt⟩

-- @node: captured_edges_eq_incident
/-- For [an edge support](hyp:S), [a selected vertex set](hyp:B), and [a chosen vertex](hyp:u),
if [the chosen vertex belongs to the support](hyp:hu) and [the selected vertex
set intersects the support vertices only at that vertex](hyp:hB), then [the number
of support edges incident to the selected set equals the support degree of the
chosen vertex](goal). -/
lemma captured_edges_eq_incident (S : Finset (GraphEdge n)) (B : Finset (Fin n))
    (u : Fin n) (hu : u ∈ supportVertices S) (hB : B ∩ supportVertices S = {u}) :
    (S ∩ freeEdges B).card = supportDegree S u := by
  classical
  unfold supportDegree
  congr 1
  ext e
  simp only [Finset.mem_inter, freeEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨he, v, hv⟩
    obtain ⟨hve, hvB⟩ := Finset.mem_inter.mp hv
    have hvS : v ∈ supportVertices S := Finset.mem_biUnion.mpr ⟨e, he, hve⟩
    have hvu : v = u := by
      have : v ∈ B ∩ supportVertices S := Finset.mem_inter.mpr ⟨hvB, hvS⟩
      simpa only [hB, Finset.mem_singleton] using this
    exact ⟨he, hvu ▸ hve⟩
  · rintro ⟨he, hue⟩
    have huB : u ∈ B := by
      have : u ∈ B ∩ supportVertices S := by rw [hB]; simp
      exact (Finset.mem_inter.mp this).1
    exact ⟨he, u, Finset.mem_inter.mpr ⟨hue, huB⟩⟩

end Papers.OaiSharpThresholdMonotone

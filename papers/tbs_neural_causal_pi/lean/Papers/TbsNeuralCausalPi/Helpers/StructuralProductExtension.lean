module
public import Papers.TbsNeuralCausalPi.Helpers.StructuralSliceExtension
/-! # Convex-range extension across finitely many categorical coordinates

Remove the categorical restrictions one coordinate at a time. The one-norm
splits exactly into the remaining coordinates and the selected coordinate,
so the finite-slice construction incurs no Lipschitz loss.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open scoped NNReal
noncomputable section
variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

-- @node: structuralCoordinateJoin
/-- For [a finite coordinate index set](hyp:ι), [a selected coordinate
i](hyp:i), and [a pair z consisting of the other coordinates and a real
number](hyp:z), the [joined vector](goal) keeps the other coordinates and
sets coordinate i to the real number plus one. -/
def structuralCoordinateJoin (i : ι)
    (z : WithLp 1 ((WithLp 1 ({j : ι // j ≠ i} → ℝ)) × ℝ)) :
    WithLp 1 (ι → ℝ) :=
  WithLp.toLp 1 (fun j => if h : j = i then z.snd + 1 else z.fst.ofLp ⟨j,h⟩)

-- @node: structuralCoordinateSplit
/-- For [a finite coordinate index set](hyp:ι), [a selected coordinate
i](hyp:i), and [a real vector x](hyp:x), the [split representation of x](goal)
is the pair consisting of all coordinates other than i and coordinate i
minus one. -/
def structuralCoordinateSplit (i : ι) (x : WithLp 1 (ι → ℝ)) :
    WithLp 1 ((WithLp 1 ({j : ι // j ≠ i} → ℝ)) × ℝ) :=
  WithLp.toLp 1 (WithLp.toLp 1 (fun j => x.ofLp j.val), x.ofLp i - 1)

-- @node: structuralCoordinateJoin_split
/-- For [any selected coordinate i](hyp:i) and [any real vector x](hyp:x),
[splitting off coordinate i, subtracting one from it, and then joining the
parts back together recovers x](goal). -/
lemma structuralCoordinateJoin_split (i : ι) (x : WithLp 1 (ι → ℝ)) :
    structuralCoordinateJoin i (structuralCoordinateSplit i x) = x := by
  apply PiLp.ext
  intro j
  by_cases h : j = i <;> simp [structuralCoordinateJoin, structuralCoordinateSplit, h]

-- @node: structuralCoordinateSplit_join
/-- For [any selected coordinate i](hyp:i) and [any pair z of the remaining
coordinates and a real number](hyp:z), [joining the pair with one added
at coordinate i and then splitting at i recovers z](goal). -/
lemma structuralCoordinateSplit_join (i : ι)
    (z : WithLp 1 ((WithLp 1 ({j : ι // j ≠ i} → ℝ)) × ℝ)) :
    structuralCoordinateSplit i (structuralCoordinateJoin i z) = z := by
  apply WithLp.ofLp_injective
  apply Prod.ext
  · apply PiLp.ext
    intro j
    simp [structuralCoordinateJoin, structuralCoordinateSplit, j.property]
  · simp [structuralCoordinateJoin, structuralCoordinateSplit]

-- @node: structuralCoordinateJoin_dist
/-- For [any selected coordinate i](hyp:i) and [any two pairs z and w of
the remaining coordinates and a real number](hyp:z,w), [joining each pair
with one added at coordinate i preserves their one-norm distance](goal). -/
lemma structuralCoordinateJoin_dist (i : ι)
    (z w : WithLp 1 ((WithLp 1 ({j : ι // j ≠ i} → ℝ)) × ℝ)) :
    dist (structuralCoordinateJoin i z) (structuralCoordinateJoin i w) = dist z w := by
  rw [PiLp.dist_eq_of_L1, structural_slice_prod_dist, PiLp.dist_eq_of_L1]
  rw [Fintype.sum_eq_sum_compl_add i]
  congr 1
  · simp only [structuralCoordinateJoin, WithLp.ofLp_toLp]
    rw [Finset.sum_subtype ({i}ᶜ) (by simp : ∀ j : ι, j ∈ ({i}ᶜ : Finset ι) ↔ j ≠ i)]
    apply Finset.sum_congr rfl
    intro j _
    simp [j.property]
  · simp [structuralCoordinateJoin]

-- @node: structuralCoordinateSplit_dist
/-- For [any selected coordinate i](hyp:i) and [any two real vectors x and
y](hyp:x,y), [splitting each vector into the other coordinates and coordinate
i minus one preserves their one-norm distance](goal). -/
lemma structuralCoordinateSplit_dist (i : ι) (x y : WithLp 1 (ι → ℝ)) :
    dist (structuralCoordinateSplit i x) (structuralCoordinateSplit i y) = dist x y := by
  rw [← structuralCoordinateJoin_dist i, structuralCoordinateJoin_split,
    structuralCoordinateJoin_split]

-- @node: structuralProductDomain
/-- For [a finite coordinate index set](hyp:ι), [a set s of selected
coordinates](hyp:s), and [nonnegative integer bounds k for the coordinates](hyp:k),
the [categorical product domain](goal) consists of real vectors whose coordinate
i belongs to {1, …, k(i) + 1} for every i in s; all other coordinates are free. -/
def structuralProductDomain (s : Finset ι) (k : ι → ℕ) : Set (WithLp 1 (ι → ℝ)) :=
  {x | ∀ i ∈ s, ∃ j : ℕ, j ≤ k i ∧ x.ofLp i = (j : ℝ) + 1}


-- @node: structural_product_extension_step
/-- For [a set s of restricted coordinates](hyp:s), [a coordinate i](hyp:i)
[outside s](hyp:hi), [integer category bounds k](hyp:k), and [a function
f](hyp:f), suppose [the output set S is convex](hyp:hS), [f is L-Lipschitz
where the coordinates in s together with i have values in their respective
ranges {1, …, k(j) + 1}](hyp:hf), and [f takes values in S on that
domain](hyp:hrange). Then [there is a function agreeing with f on that domain
which is L-Lipschitz and S-valued on the larger domain restricting only the
coordinates in s](goal). -/
lemma structural_product_extension_step (s : Finset ι) (i : ι) (hi : i ∉ s)
    (k : ι → ℕ) (f : WithLp 1 (ι → ℝ) → E) {L : ℝ≥0} {S : Set E}
    (hS : Convex ℝ S)
    (hf : LipschitzOnWith L f (structuralProductDomain (insert i s) k))
    (hrange : ∀ x ∈ structuralProductDomain (insert i s) k, f x ∈ S) :
    ∃ g : WithLp 1 (ι → ℝ) → E,
      LipschitzOnWith L g (structuralProductDomain s k) ∧
      (∀ x ∈ structuralProductDomain s k, g x ∈ S) ∧
      Set.EqOn g f (structuralProductDomain (insert i s) k) := by
  let T : Set (WithLp 1 ({j : ι // j ≠ i} → ℝ)) :=
    {x | ∀ j (hj : j ∈ s) (hji : j ≠ i),
      ∃ a : ℕ, a ≤ k j ∧ x.ofLp ⟨j,hji⟩ = (a : ℝ) + 1}
  have hcarry (z : WithLp 1 ((WithLp 1 ({j : ι // j ≠ i} → ℝ)) × ℝ)) :
      structuralCoordinateJoin i z ∈ structuralProductDomain s k ↔ z.fst ∈ T := by
    constructor
    · intro hz j hj hji
      simpa [structuralCoordinateJoin, hji] using hz j hj
    · intro hz j hj
      have hji : j ≠ i := fun h => hi (h ▸ hj)
      simpa [structuralCoordinateJoin, hji] using hz j hj hji
  have hfull (z : WithLp 1 ((WithLp 1 ({j : ι // j ≠ i} → ℝ)) × ℝ)) :
      structuralCoordinateJoin i z ∈ structuralProductDomain (insert i s) k ↔
        z.fst ∈ T ∧ ∃ a : ℕ, a ≤ k i ∧ z.snd = (a : ℝ) := by
    constructor
    · intro hz
      refine ⟨(hcarry z).mp (fun j hj => hz j (Finset.mem_insert_of_mem hj)), ?_⟩
      obtain ⟨a, ha, he⟩ := hz i (Finset.mem_insert_self _ _)
      refine ⟨a, ha, ?_⟩
      simpa [structuralCoordinateJoin] using he
    · rintro ⟨hz, a, ha, he⟩ j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact ⟨a, ha, by simp [structuralCoordinateJoin, he]⟩
      · exact (hcarry z).mpr hz j hj
  have hf' : LipschitzOnWith L (f ∘ structuralCoordinateJoin i)
      {z | z.fst ∈ T ∧ ∃ a : ℕ, a ≤ k i ∧ z.snd = (a : ℝ)} := by
    apply LipschitzOnWith.of_dist_le_mul
    intro z hz w hw
    simpa only [Function.comp_apply, structuralCoordinateJoin_dist] using
      hf.dist_le_mul _ ((hfull z).mpr hz) _ ((hfull w).mpr hw)
  obtain ⟨g, hg, hgS, heq⟩ := structural_finite_slice_extension_on (k i) T
    (f ∘ structuralCoordinateJoin i) hS hf'
    (fun z hz ha => hrange _ ((hfull z).mpr ⟨hz, ha⟩))
  have hsplit (x : WithLp 1 (ι → ℝ)) (hx : x ∈ structuralProductDomain s k) :
      (structuralCoordinateSplit i x).fst ∈ T := by
    apply (hcarry _).mp
    simpa only [structuralCoordinateJoin_split] using hx
  refine ⟨g ∘ structuralCoordinateSplit i, ?_, ?_, ?_⟩
  · apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa only [Function.comp_apply, structuralCoordinateSplit_dist] using
      hg.dist_le_mul _ (hsplit x hx) _ (hsplit y hy)
  · intro x hx
    exact hgS _ (hsplit x hx)
  · intro x hx
    have hm : structuralCoordinateJoin i (structuralCoordinateSplit i x) ∈
        structuralProductDomain (insert i s) k := by
      simpa only [structuralCoordinateJoin_split] using hx
    simpa only [Function.comp_apply, structuralCoordinateJoin_split] using
      heq ((hfull _).mp hm)

-- @node: structural_product_extension
/-- For [a set s of restricted coordinates](hyp:s), [integer category bounds
k](hyp:k), and [a function f](hyp:f), suppose [S is a convex output set](hyp:hS),
[f is L-Lipschitz on the domain where each coordinate i in s belongs to
{1, …, k(i) + 1}](hyp:hf), and [f takes values in S there](hyp:hrange).
Then [f has an L-Lipschitz extension to the entire ambient one-norm space
that takes values in S everywhere and agrees with f on that domain](goal). -/
lemma structural_product_extension (s : Finset ι) (k : ι → ℕ)
    (f : WithLp 1 (ι → ℝ) → E) {L : ℝ≥0} {S : Set E} (hS : Convex ℝ S)
    (hf : LipschitzOnWith L f (structuralProductDomain s k))
    (hrange : ∀ x ∈ structuralProductDomain s k, f x ∈ S) :
    ∃ g : WithLp 1 (ι → ℝ) → E, LipschitzWith L g ∧
      (∀ x, g x ∈ S) ∧ Set.EqOn g f (structuralProductDomain s k) := by
  induction s using Finset.induction_on generalizing f with
  | empty =>
    have he : structuralProductDomain (∅ : Finset ι) k = Set.univ := by
      ext x
      simp [structuralProductDomain]
    exact ⟨f, lipschitzOnWith_univ.mp (he ▸ hf), fun x => hrange x (by simp [he]),
      fun _ _ => rfl⟩
  | @insert i s hi ih =>
    obtain ⟨g, hg, hgS, heq⟩ := structural_product_extension_step s i hi k f hS hf hrange
    obtain ⟨G, hG, hGS, hGeq⟩ := ih g hg hgS
    refine ⟨G, hG, hGS, ?_⟩
    intro x hx
    exact (hGeq (fun j hj => hx j (Finset.mem_insert_of_mem hj))).trans (heq hx)

end
end Papers.TbsNeuralCausalPi

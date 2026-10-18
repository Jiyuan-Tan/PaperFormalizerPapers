module
public import Papers.TbsNeuralCausalPi.Helpers.PolynomialRootArrangement
public import Papers.TbsNeuralCausalPi.Helpers.PolynomialSignComponents
public import Mathlib.Topology.Homeomorph.Lemmas
/-! # Connected-component bounds for real polynomial arrangements

Finite root cuts give the one-dimensional component bounds used as base
cases for zero-set arrangements. These are actual connected components,
not merely sign vectors. No multivariate degree bound is assumed here.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
noncomputable section

-- @node: realSetComponents
/-- For [a subset of the real line](hyp:s), its [collection of connected components](goal) consists of the connected component containing each point of the subset. -/
def realSetComponents (s : Set ℝ) : Set (Set ℝ) :=
  (fun x => connectedComponentIn s x) '' s

-- @node: finite_root_cut_interval_subset_complement
/-- If [the first endpoint avoids a finite set of roots](hyp:hx), [the second endpoint also avoids it](hyp:hy), and [the numbers of roots at or below the two endpoints agree](hyp:hcut), then [the closed interval between the endpoints contains no roots from that set](goal). -/
lemma finite_root_cut_interval_subset_complement (s : Finset ℝ) {x y : ℝ}
    (hx : x ∉ s) (hy : y ∉ s)
    (hcut : (s.filter (· ≤ x)).card = (s.filter (· ≤ y)).card) :
    Set.uIcc x y ⊆ (s : Set ℝ)ᶜ := by
  classical
  have hc := finite_root_cut_eq_of_card_eq s x y hcut
  have ordered {a b : ℝ} (hab : a ≤ b) (ha : a ∉ s)
      (hc : s.filter (· ≤ a) = s.filter (· ≤ b)) :
      Set.Icc a b ⊆ (s : Set ℝ)ᶜ := by
    intro z hz hzs
    have hm : z ∈ s.filter (· ≤ b) := Finset.mem_filter.mpr ⟨hzs, hz.2⟩
    rw [← hc] at hm
    have hza := (Finset.mem_filter.mp hm).2
    exact ha ((le_antisymm hz.1 hza) ▸ hzs)
  rcases le_total x y with hxy | hyx
  · simpa only [Set.uIcc_of_le hxy] using ordered hxy hx hc
  · simpa only [Set.uIcc_of_ge hyx] using ordered hyx hy hc.symm

-- @node: finite_root_cut_component_eq
/-- If [the first point avoids a finite set of roots](hyp:hx), [the second point also avoids it](hyp:hy), and [the numbers of roots at or below the points agree](hyp:hcut), then [the points have the same connected component in the complement of the roots](goal). -/
lemma finite_root_cut_component_eq (s : Finset ℝ) {x y : ℝ}
    (hx : x ∉ s) (hy : y ∉ s)
    (hcut : (s.filter (· ≤ x)).card = (s.filter (· ≤ y)).card) :
    connectedComponentIn (s : Set ℝ)ᶜ x = connectedComponentIn (s : Set ℝ)ᶜ y := by
  apply connectedComponentIn_eq
  exact isPreconnected_uIcc.subset_connectedComponentIn Set.left_mem_uIcc
    (finite_root_cut_interval_subset_complement s hx hy hcut) Set.right_mem_uIcc

-- @node: realSetComponents_complement_finset_encard_le
/-- [Removing a finite set of points from the real line leaves at most one more connected component than the number of removed points](goal). -/
lemma realSetComponents_complement_finset_encard_le (s : Finset ℝ) :
    (realSetComponents (s : Set ℝ)ᶜ).encard ≤ (s.card + 1 : ℕ) := by
  classical
  let components := realSetComponents (s : Set ℝ)ᶜ
  have hw (v : components) : ∃ x : ℝ, x ∉ s ∧
      connectedComponentIn (s : Set ℝ)ᶜ x = v.val := v.property
  choose x hx hcomponent using hw
  let rank : components → ℕ := fun v => (s.filter (· ≤ x v)).card
  have hinj : Function.Injective rank := by
    intro v w h
    apply Subtype.ext
    exact (hcomponent v).symm.trans
      ((finite_root_cut_component_eq s (hx v) (hx w) h).trans (hcomponent w))
  calc
    components.encard ≤ (Set.range rank).encard := hinj.encard_range
    _ ≤ {k : ℕ | k < s.card + 1}.encard := Set.encard_mono (by
      rintro _ ⟨v, rfl⟩
      exact Nat.lt_succ_of_le (Finset.card_filter_le _ _))
    _ = (s.card + 1 : ℕ) := Set.Nat.encard_range _

-- @node: realSetComponents_encard_le
/-- [The number of connected components of a subset of the real line is at most the number of points in that subset](goal). -/
lemma realSetComponents_encard_le (s : Set ℝ) :
    (realSetComponents s).encard ≤ s.encard := Set.encard_image_le _ _

-- @node: univariate_nonzero_domain_eq_roots_complement
/-- If [every polynomial in a finite family is nonzero](hyp:hp), then [the points where all polynomials have nonzero values are exactly the complement of their combined set of real roots](goal). -/
lemma univariate_nonzero_domain_eq_roots_complement {I : Type*} [Fintype I]
    (p : I → Polynomial ℝ) (hp : ∀ i, p i ≠ 0) :
    {x | ∀ i, (p i).eval x ≠ 0} = (polynomialArrangementRoots p : Set ℝ)ᶜ := by
  classical
  ext x
  simp [polynomialArrangementRoots, hp]

-- @node: univariate_nonzero_components_encard_le
/-- For a finite family of real univariate polynomials, [the set where all polynomial values are nonzero has at most one plus the sum of their degrees connected components](goal), even if the family includes a zero polynomial. -/
lemma univariate_nonzero_components_encard_le {I : Type*} [Fintype I]
    (p : I → Polynomial ℝ) :
    (realSetComponents {x | ∀ i, (p i).eval x ≠ 0}).encard ≤
      (∑ i, (p i).natDegree : ℕ) + 1 := by
  classical
  by_cases hp : ∀ i, p i ≠ 0
  · rw [univariate_nonzero_domain_eq_roots_complement p hp]
    exact (realSetComponents_complement_finset_encard_le _).trans (by
      exact_mod_cast Nat.add_le_add_right (polynomialArrangementRoots_card_le p) 1)
  · obtain ⟨i, hi⟩ := not_forall.mp hp
    have hz : p i = 0 := not_not.mp hi
    have hempty : {x | ∀ j, (p j).eval x ≠ 0} = (∅ : Set ℝ) := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hx i (by simp [hz])
    rw [hempty]
    simp [realSetComponents]

-- @node: univariate_nonzero_components_encard_le_degree
/-- If [every polynomial in a finite family has degree at most d](hyp:hd), then [the set where all polynomial values are nonzero has at most the family size times d plus one connected components](goal). -/
lemma univariate_nonzero_components_encard_le_degree {I : Type*} [Fintype I]
    (p : I → Polynomial ℝ) (d : ℕ) (hd : ∀ i, (p i).natDegree ≤ d) :
    (realSetComponents {x | ∀ i, (p i).eval x ≠ 0}).encard ≤
      (Fintype.card I * d + 1 : ℕ) := by
  have hdeg : (∑ i, (p i).natDegree) ≤ Fintype.card I * d :=
    (Finset.sum_le_sum (fun i _ => hd i)).trans_eq (by simp)
  exact (univariate_nonzero_components_encard_le p).trans (by
    exact_mod_cast Nat.add_le_add_right hdeg 1)

-- @node: realSetComponents_univ
/-- [The collection of connected components of the entire real line consists only of the entire real line itself](goal). -/
lemma realSetComponents_univ : realSetComponents Set.univ = {Set.univ} := by
  ext s
  simp only [realSetComponents, Set.mem_image, Set.mem_univ, true_and,
    connectedComponentIn_univ, PreconnectedSpace.connectedComponent_eq_univ, Set.mem_singleton_iff]
  constructor
  · rintro ⟨x, hx⟩
    simpa using hx.symm
  · intro hs
    exact ⟨0, by simpa using hs.symm⟩

-- @node: univariate_zero_components_encard_le
/-- If [a real univariate polynomial is nonzero](hyp:hp), then [its zero set has at most its degree many connected components](goal). -/
lemma univariate_zero_components_encard_le (p : Polynomial ℝ) (hp : p ≠ 0) :
    (realSetComponents {x | p.eval x = 0}).encard ≤ (p.natDegree : ℕ) := by
  classical
  have hz : {x | p.eval x = 0} = (p.roots.toFinset : Set ℝ) := by
    ext x
    simp [Polynomial.mem_roots hp, Polynomial.IsRoot]
  calc
    (realSetComponents {x | p.eval x = 0}).encard ≤ {x | p.eval x = 0}.encard :=
      realSetComponents_encard_le _
    _ = (p.roots.toFinset.card : ℕ) := by rw [hz]; simp
    _ ≤ (p.natDegree : ℕ) := by
      exact_mod_cast (Multiset.toFinset_card_le p.roots).trans (Polynomial.card_roots' p)

-- @node: univariate_zero_intersection_components_encard_le
/-- If [a selected polynomial in a possibly infinite family is nonzero](hyp:hp), then [the common zero set of the family has at most the degree of that selected polynomial many connected components](goal). -/
lemma univariate_zero_intersection_components_encard_le {I : Type*}
    (p : I → Polynomial ℝ) (i : I) (hp : p i ≠ 0) :
    (realSetComponents {x | ∀ j, (p j).eval x = 0}).encard ≤ ((p i).natDegree : ℕ) := by
  classical
  have hs : {x | ∀ j, (p j).eval x = 0} ⊆ ((p i).roots.toFinset : Set ℝ) := by
    intro x hx
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr (hx i))
  calc
    (realSetComponents {x | ∀ j, (p j).eval x = 0}).encard ≤
        {x | ∀ j, (p j).eval x = 0}.encard := realSetComponents_encard_le _
    _ ≤ (((p i).roots.toFinset.card : ℕ) : ℕ∞) := by
      simpa using Set.encard_mono hs
    _ ≤ ((p i).natDegree : ℕ) := by
      exact_mod_cast (Multiset.toFinset_card_le (p i).roots).trans (Polynomial.card_roots' (p i))

-- @node: univariate_zero_intersection_components_encard_le_degree
/-- If [every polynomial in a possibly infinite family has degree at most d](hyp:hd), then [the common zero set has at most the larger of d and one connected components](goal). -/
lemma univariate_zero_intersection_components_encard_le_degree {I : Type*}
    (p : I → Polynomial ℝ) (d : ℕ) (hd : ∀ i, (p i).natDegree ≤ d) :
    (realSetComponents {x | ∀ j, (p j).eval x = 0}).encard ≤ (max d 1 : ℕ) := by
  classical
  by_cases hp : ∀ i, p i = 0
  · have hz : {x | ∀ j, (p j).eval x = 0} = (Set.univ : Set ℝ) := by simp [hp]
    rw [hz, realSetComponents_univ, Set.encard_singleton]
    exact_mod_cast (le_max_right d 1)
  · obtain ⟨i, hi⟩ := not_forall.mp hp
    exact (univariate_zero_intersection_components_encard_le p i hi).trans (by
      exact_mod_cast (hd i).trans (le_max_left d 1))

-- @node: unique_variable_nonzero_domain_image
/-- For polynomials in a single variable, [identifying a variable assignment with its sole coordinate sends the simultaneous nonzero domain exactly onto the set where the corresponding univariate polynomials are all nonzero](goal). -/
lemma unique_variable_nonzero_domain_image {I V : Type*} [Unique V]
    (p : I → MvPolynomial V ℝ) :
    (Homeomorph.piUnique (fun _ : V => ℝ)) '' polynomialNonzeroDomain p =
      {x | ∀ i, (MvPolynomial.uniqueAlgEquiv ℝ V (p i)).eval x ≠ 0} := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩ i
    change (MvPolynomial.uniqueAlgEquiv ℝ V (p i)).eval (a default) ≠ 0
    rw [unique_variable_polynomial_eval]
    exact ha i
  · intro hx
    refine ⟨fun _ => x, ?_, rfl⟩
    intro i
    rw [← unique_variable_polynomial_eval (p i) (fun _ : V => x)]
    exact hx i

-- @node: unique_variable_sign_components_encard_eq
/-- For a family of polynomials in a single variable, [the number of connected components of their simultaneous nonzero domain equals the number of connected components of the corresponding univariate nonzero domain on the real line](goal). -/
lemma unique_variable_sign_components_encard_eq {I V : Type*} [Unique V]
    (p : I → MvPolynomial V ℝ) :
    (polynomialSignComponents p).encard =
      (realSetComponents {x | ∀ i,
        (MvPolynomial.uniqueAlgEquiv ℝ V (p i)).eval x ≠ 0}).encard := by
  let e := Homeomorph.piUnique (fun _ : V => ℝ)
  have he : (fun s : Set (V → ℝ) => e '' s) '' polynomialSignComponents p =
      realSetComponents (e '' polynomialNonzeroDomain p) := by
    ext s
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨e a, ⟨a, ha, rfl⟩, (e.image_connectedComponentIn ha).symm⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨connectedComponentIn (polynomialNonzeroDomain p) a,
        ⟨a, ha, rfl⟩, e.image_connectedComponentIn ha⟩
  calc
    (polynomialSignComponents p).encard =
        ((fun s : Set (V → ℝ) => e '' s) '' polynomialSignComponents p).encard :=
      (e.injective.image_injective.encard_image _).symm
    _ = (realSetComponents (e '' polynomialNonzeroDomain p)).encard := congrArg Set.encard he
    _ = _ := by rw [show e '' polynomialNonzeroDomain p = _ from
      unique_variable_nonzero_domain_image p]

-- @node: polynomialSignComponents_encard_le_one_variable
/-- If [every polynomial in a finite family with one variable has total degree at most d](hyp:hd), then [their simultaneous nonzero domain has at most the family size times d plus one connected components](goal). -/
lemma polynomialSignComponents_encard_le_one_variable {I V : Type*}
    [Fintype I] [Unique V] (p : I → MvPolynomial V ℝ) (d : ℕ)
    (hd : ∀ i, (p i).totalDegree ≤ d) :
    (polynomialSignComponents p).encard ≤ (Fintype.card I * d + 1 : ℕ) := by
  rw [unique_variable_sign_components_encard_eq]
  exact univariate_nonzero_components_encard_le_degree _ d (fun i =>
    (unique_variable_polynomial_natDegree_le (p i)).trans (hd i))

end
end Papers.TbsNeuralCausalPi

module
public import Papers.TbsNeuralCausalPi.Helpers.AntipodalIncidence
/-! # Finite algebra for the antipodal parity obstruction

For a free involution on a finite basis, the kernel and image of `1 + T`
coincide over `ZMod 2`. An augmented chain ladder with successive boundaries
`(1 + T)c` therefore cannot have a zero final antipodal sum. The differential
and ladder in this theorem are actual inputs: constructing them on sphere
subdivisions and relating them to PL maps remain separate obligations.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi.Antipodal

-- @node: antipodalChainNorm
/-- For [a transformation of the index set](hyp:a), the [antipodal sum operator](goal)
is the linear operator on modulo-two weights that adds the weight at each index
to the weight at its transformed index. -/
def antipodalChainNorm {X : Type*} (a : X → X) :
    (X → ZMod 2) →ₗ[ZMod 2] (X → ZMod 2) where
  toFun w := fun x => w x + w (a x)
  map_add' w v := by
    funext x
    change (w x + v x) + (w (a x) + v (a x)) =
      (w x + w (a x)) + (v x + v (a x))
    ring
  map_smul' r w := by
    funext x
    change r * w x + r * w (a x) = r * (w x + w (a x))
    exact (mul_add _ _ _).symm

-- @node: antipodalChainNorm_apply
/-- [The antipodal sum of a weight function at an index equals its weight there
plus its weight at the transformed index, with addition modulo two](goal). -/
@[simp] lemma antipodalChainNorm_apply {X : Type*} (a : X → X)
    (w : X → ZMod 2) (x : X) :
    antipodalChainNorm a w x = w x + w (a x) := rfl

-- @node: antipodalChainNorm_sq_zero
/-- If [applying the index transformation twice returns every index to itself](hyp:ha),
then [applying the antipodal sum operator twice to any modulo-two weight function gives zero](goal). -/
lemma antipodalChainNorm_sq_zero {X : Type*} {a : X → X}
    (ha : Function.Involutive a) (w : X → ZMod 2) :
    antipodalChainNorm a (antipodalChainNorm a w) = 0 := by
  funext x
  simp only [antipodalChainNorm_apply, ha x, Pi.zero_apply]
  calc
    (w x + w (a x)) + (w (a x) + w x) =
        (w x + w x) + (w (a x) + w (a x)) := by ring
    _ = 0 := by rw [ZModModule.add_self, ZModModule.add_self, add_zero]

-- @node: antipodalChainNorm_kernel_subset_range
/-- On a finite index set, suppose [the index transformation applied twice is
the identity](hyp:ha) and [it fixes no index](hyp:hfree). If [a modulo-two weight
function has zero antipodal sum](hyp:hw), then [it is the antipodal sum of another
weight function](goal). -/
lemma antipodalChainNorm_kernel_subset_range {X : Type*} [Finite X]
    {a : X → X} (ha : Function.Involutive a) (hfree : ∀ x, a x ≠ x)
    (w : X → ZMod 2) (hw : antipodalChainNorm a w = 0) :
    ∃ v, antipodalChainNorm a v = w := by
  classical
  let := Fintype.ofFinite X
  let e := Fintype.equivFin X
  let v : X → ZMod 2 := fun x => if e x < e (a x) then w x else 0
  have hinv : ∀ x, w (a x) = w x := by
    intro x
    have hx : w x + w (a x) = 0 := congrFun hw x
    exact add_left_cancel (hx.trans (ZModModule.add_self (w x)).symm)
  refine ⟨v, ?_⟩
  funext x
  change v x + v (a x) = w x
  have hne : e x ≠ e (a x) := fun h => hfree x (e.injective h).symm
  by_cases h : e x < e (a x)
  · have hn : ¬ e (a x) < e x := not_lt.mpr (le_of_lt h)
    simp [v, ha x, h, hn]
  · have h' : e (a x) < e x := lt_of_le_of_ne (le_of_not_gt h) hne.symm
    simp [v, ha x, h, h', hinv]

-- @node: antipodalChainNorm_eq_zero_iff_mem_range
/-- On a finite index set, if [the transformation applied twice is the identity](hyp:ha)
and [it fixes no index](hyp:hfree), then [a modulo-two weight function has zero
antipodal sum if and only if it is the antipodal sum of another weight function](goal). -/
lemma antipodalChainNorm_eq_zero_iff_mem_range {X : Type*} [Finite X]
    {a : X → X} (ha : Function.Involutive a) (hfree : ∀ x, a x ≠ x)
    (w : X → ZMod 2) :
    antipodalChainNorm a w = 0 ↔ ∃ v, antipodalChainNorm a v = w := by
  constructor
  · exact antipodalChainNorm_kernel_subset_range ha hfree w
  · rintro ⟨v, rfl⟩
    exact antipodalChainNorm_sq_zero ha v

-- @node: modTwo_chain_ladder_bottom_decomposition
/-- For linear operators N and d on a vector space over the two-element field,
suppose [every vector annihilated by N is an image under N](hyp:hsplit),
[applying d twice gives zero](hyp:hdd), and [N commutes with d](hyp:hcomm).
If [each successive vector in a sequence through position n has boundary d equal
to N of the preceding vector](hyp:hc) and [N annihilates the vector at position n](hyp:htop),
then [the initial vector is a sum of an image under N and an image under d](goal). -/
lemma modTwo_chain_ladder_bottom_decomposition
    {C : Type*} [AddCommGroup C] [Module (ZMod 2) C]
    (N d : C →ₗ[ZMod 2] C)
    (hsplit : ∀ x, N x = 0 → ∃ y, N y = x)
    (hdd : ∀ x, d (d x) = 0) (hcomm : ∀ x, N (d x) = d (N x))
    (n : ℕ) (c : ℕ → C)
    (hc : ∀ i, i < n → d (c (i + 1)) = N (c i))
    (htop : N (c n) = 0) :
    ∃ a b, c 0 = N a + d b := by
  induction n generalizing c with
  | zero =>
      obtain ⟨a, ha⟩ := hsplit (c 0) htop
      exact ⟨a, 0, by rw [map_zero, add_zero, ha]⟩
  | succ n ih =>
      obtain ⟨a, b, hab⟩ := ih (fun i => c (i + 1))
        (fun i hi => hc (i + 1) (by omega)) htop
      have hz : N (c 0 + d a) = 0 := by
        calc
          N (c 0 + d a) = N (c 0) + N (d a) := N.map_add _ _
          _ = d (c 1) + d (N a) := by rw [hc 0 (by omega), hcomm]
          _ = d (N a + d b) + d (N a) := by rw [hab]
          _ = 0 := by rw [map_add, hdd, add_zero, ZModModule.add_self]
      obtain ⟨a', ha'⟩ := hsplit _ hz
      refine ⟨a', a, ?_⟩
      rw [ha', add_assoc, ZModModule.add_self, add_zero]

-- @node: modTwo_chain_ladder_norm_ne_zero
/-- For linear operators N and d and a linear scalar-valued augmentation over
the two-element field, suppose [every vector annihilated by N is an image under N](hyp:hsplit),
[applying d twice gives zero](hyp:hdd), [N commutes with d](hyp:hcomm),
[the augmentation vanishes on images under N](hyp:hεN), and [it vanishes on images
under d](hyp:hεd). If [each successive vector through position n has boundary d
equal to N of the preceding vector](hyp:hc) and [the initial vector has augmentation
one](hyp:hbottom), then [N of the vector at position n is nonzero](goal). -/
lemma modTwo_chain_ladder_norm_ne_zero
    {C : Type*} [AddCommGroup C] [Module (ZMod 2) C]
    (N d : C →ₗ[ZMod 2] C) (ε : C →ₗ[ZMod 2] ZMod 2)
    (hsplit : ∀ x, N x = 0 → ∃ y, N y = x)
    (hdd : ∀ x, d (d x) = 0) (hcomm : ∀ x, N (d x) = d (N x))
    (hεN : ∀ x, ε (N x) = 0) (hεd : ∀ x, ε (d x) = 0)
    (n : ℕ) (c : ℕ → C)
    (hc : ∀ i, i < n → d (c (i + 1)) = N (c i)) (hbottom : ε (c 0) = 1) :
    N (c n) ≠ 0 := by
  intro htop
  obtain ⟨a, b, hab⟩ := modTwo_chain_ladder_bottom_decomposition
    N d hsplit hdd hcomm n c hc htop
  have hz : ε (c 0) = 0 := by rw [hab, map_add, hεN, hεd, add_zero]
  exact zero_ne_one (hz.symm.trans hbottom)

-- @node: finite_antipodal_chain_ladder_norm_ne_zero
/-- On modulo-two weights over a finite index set, suppose [the index transformation
applied twice is the identity](hyp:ha), [it fixes no index](hyp:hfree),
[the linear boundary operator applied twice gives zero](hyp:hdd), and [the antipodal
sum operator commutes with the boundary](hyp:hcomm). If [a linear augmentation
is unchanged by transforming all indices](hyp:hεa), [vanishes on boundaries](hyp:hεd),
[each successive chain through position n has boundary equal to the antipodal sum
of the preceding chain](hyp:hc), and [the initial chain has augmentation one](hyp:hbottom),
then [the antipodal sum of the chain at position n is nonzero](goal). -/
lemma finite_antipodal_chain_ladder_norm_ne_zero
    {X : Type*} [Finite X] {a : X → X}
    (ha : Function.Involutive a) (hfree : ∀ x, a x ≠ x)
    (d : (X → ZMod 2) →ₗ[ZMod 2] (X → ZMod 2))
    (ε : (X → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (hdd : ∀ w, d (d w) = 0)
    (hcomm : ∀ w, antipodalChainNorm a (d w) = d (antipodalChainNorm a w))
    (hεa : ∀ w, ε (fun x => w (a x)) = ε w) (hεd : ∀ w, ε (d w) = 0)
    (n : ℕ) (c : ℕ → (X → ZMod 2))
    (hc : ∀ i, i < n → d (c (i + 1)) = antipodalChainNorm a (c i))
    (hbottom : ε (c 0) = 1) : antipodalChainNorm a (c n) ≠ 0 := by
  apply modTwo_chain_ladder_norm_ne_zero (antipodalChainNorm a) d ε
    (antipodalChainNorm_kernel_subset_range ha hfree) hdd hcomm ?_ hεd n c hc hbottom
  intro w
  change ε (w + (fun x => w (a x))) = 0
  rw [map_add, hεa, ZModModule.add_self]

-- @node: finite_antipodal_chain_map_top_ne_zero
/-- For modulo-two weights on source and target index sets, with the target finite,
suppose [the target index transformation applied twice is the identity](hyp:ha),
[it fixes no index](hyp:hfree), [the target boundary applied twice gives zero](hyp:hdd),
and [the target antipodal sum commutes with the target boundary](hyp:hcomm).
Assume [the target augmentation is invariant under transforming indices](hyp:hεa),
[vanishes on target boundaries](hyp:hεd), [the linear map from source to target
commutes with the respective boundaries](hyp:hFd), and [it carries the source
operator N to the target antipodal sum](hyp:hFN). If [each successive source chain
through position n has boundary equal to N of its predecessor](hyp:hc) and [the
image of the initial chain has augmentation one](hyp:hbottom), then [the image of
the chain at position n is nonzero](goal). -/
lemma finite_antipodal_chain_map_top_ne_zero
    {X Y : Type*} [Finite Y] {a : Y → Y}
    (ha : Function.Involutive a) (hfree : ∀ y, a y ≠ y)
    (N : (X → ZMod 2) →ₗ[ZMod 2] (X → ZMod 2))
    (dX : (X → ZMod 2) →ₗ[ZMod 2] (X → ZMod 2))
    (dY : (Y → ZMod 2) →ₗ[ZMod 2] (Y → ZMod 2))
    (ε : (Y → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (F : (X → ZMod 2) →ₗ[ZMod 2] (Y → ZMod 2))
    (hdd : ∀ w, dY (dY w) = 0)
    (hcomm : ∀ w, antipodalChainNorm a (dY w) = dY (antipodalChainNorm a w))
    (hεa : ∀ w, ε (fun y => w (a y)) = ε w) (hεd : ∀ w, ε (dY w) = 0)
    (hFd : ∀ w, dY (F w) = F (dX w))
    (hFN : ∀ w, F (N w) = antipodalChainNorm a (F w))
    (n : ℕ) (c : ℕ → (X → ZMod 2))
    (hc : ∀ i, i < n → dX (c (i + 1)) = N (c i))
    (hbottom : ε (F (c 0)) = 1) : F (c n) ≠ 0 := by
  have htop := finite_antipodal_chain_ladder_norm_ne_zero ha hfree dY ε
    hdd hcomm hεa hεd n (fun i => F (c i))
    (fun i hi => by rw [hFd, hc i hi, hFN]) hbottom
  intro hz
  exact htop (by rw [hz, map_zero])

-- @node: signedFacetChain_norm_eq_zero_iff_mem_range
/-- If [there is at least one coordinate](hyp:hn), then [a modulo-two weight
function on signed facets has zero antipodal sum if and only if it is the antipodal
sum of another weight function](goal), where the antipodal transformation reverses
every sign. -/
lemma signedFacetChain_norm_eq_zero_iff_mem_range {n : ℕ} (hn : 0 < n)
    (w : (Fin n → Bool) → ZMod 2) :
    antipodalChainNorm (fun σ i => !σ i) w = 0 ↔
      ∃ v, antipodalChainNorm (fun σ i => !σ i) v = w := by
  apply antipodalChainNorm_eq_zero_iff_mem_range
  · intro σ
    funext i
    exact Bool.not_not (σ i)
  · intro σ h
    exact signedFacet_ne_antipode hn σ (congrArg signedFacet h.symm)

-- @node: signedFacetChain_norm_hemisphere
/-- [The antipodal sum of the modulo-two indicator of facets having positive sign
at a designated coordinate is the function assigning weight one to every facet](goal). -/
lemma signedFacetChain_norm_hemisphere {n : ℕ} (j : Fin n) :
    antipodalChainNorm (fun σ i => !σ i)
      (fun σ => if σ j then 1 else 0) = (fun _ => 1) := by
  funext σ
  simp only [antipodalChainNorm_apply]
  by_cases h : σ j = true <;> simp [h]

end Papers.TbsNeuralCausalPi.Antipodal

module

public import Papers.OaiPairedStatesHamiltonian.Helpers.GraphClasses

/-! The two disclosed external logical gates. -/

@[expose] public section

namespace OaiPairedStatesHamiltonian

set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.unusedVariables false
open Classical
attribute [local instance] propDecidable


/-- [The cited Hamiltonicity equivalence](goal) says that every finite cubic, bipartite,
planar, three-vertex-connected graph has a Hamiltonian cycle if and only if every finite
cubic, three-vertex-connected, bipartite Pfaffian graph has a Hamiltonian cycle containing
all three edges of any given path on four vertices.

Maximilian Gorsky, Raphael Steiner, Sebastian Wiederrecht (2023),
*Matching theory and Barnette's conjecture*, Theorem 4.16, (i) iff (v),
handle GSW2023; arXiv:2202.11641v3, https://arxiv.org/html/2202.11641v3#S4.Thmthm16.
The source's six-way equivalence entails precisely this two-condition equivalence. -/
-- @node: lem:gsw2023-theorem-4-16
noncomputable def GSW2023Thm416 : Sort 0 :=
  (∀ n (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], MainDomain G → G.IsHamiltonian) ↔
  (∀ n (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    PfaffianPathsGraph G → PfaffianPathsBipartite G → IsP4Hamiltonian G)

/-- [The cited planar Pfaffian assertion](goal) says that every finite planar graph admits
a Pfaffian orientation.

Maximilian Gorsky, Raphael Steiner, Sebastian Wiederrecht (2023),
*Matching theory and Barnette's conjecture*, Theorem 4.6 (Kasteleyn),
handle GSW2023; arXiv:2202.11641v3, https://arxiv.org/html/2202.11641v3.
The source asserts that every planar graph is Pfaffian, without connectivity,
cubicity, or bipartiteness restrictions. -/
-- @node: lem:gsw2023-theorem-4-6
noncomputable def GSW2023Thm46 : Sort 0 :=
  ∀ n (G : SimpleGraph (Fin n)), IsPlanar G → IsPfaffian G


end OaiPairedStatesHamiltonian

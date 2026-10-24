# Correctness report — oai_paired_states_hamiltonian

**Verdict: NO ERROR FOUND**

**Paper: MINOR ISSUES — no main result is shown false or weakened**

Minor:

- Theorem 1.1: condition added (bookkeeping or a pinned reading)
- Lemma 2.1: condition added (bookkeeping or a pinned reading)
- Theorem 2.2: condition added (bookkeeping or a pinned reading)
- Proposition 3.1: condition added (bookkeeping or a pinned reading)
- Proposition 5.1: condition added (bookkeeping or a pinned reading)
- Lemma 5.2: condition added (bookkeeping or a pinned reading)
- Lemma 6.2: condition added (bookkeeping or a pinned reading)
- Corollary 7.1: condition added (bookkeeping or a pinned reading)
- Corollary 7.2: condition added (bookkeeping or a pinned reading)
- `ass:cancel-cyclic`: ambiguous; a reading was pinned
- `ass:edge-avoidance-domain`: ambiguous; a reading was pinned
- `def:paired-edges`: ambiguous; a reading was pinned
- `def:singleton-tree`: ambiguous; a reading was pinned
- `G`: notation ambiguous; a reading was pinned
- `T`: notation ambiguous; a reading was pinned
- `e_0`: notation ambiguous; a reading was pinned
- `v`: notation ambiguous; a reading was pinned
- `w`: notation ambiguous; a reading was pinned
- `a`: notation ambiguous; a reading was pinned
- `\omega`: notation ambiguous; a reading was pinned
- `D`: notation ambiguous; a reading was pinned
- `Z`: notation ambiguous; a reading was pinned
- `C`: notation ambiguous; a reading was pinned
- `\widetilde r`: notation ambiguous; a reading was pinned
- `U`: notation ambiguous; a reading was pinned
- `e`: notation ambiguous; a reading was pinned
- `G^*`: notation ambiguous; a reading was pinned
- `B`: notation ambiguous; a reading was pinned
- `W`: notation ambiguous; a reading was pinned
- `I`: notation ambiguous; a reading was pinned
- `h`: notation ambiguous; a reading was pinned
- `l`: notation ambiguous; a reading was pinned
- `b`: notation ambiguous; a reading was pinned
- `K`: notation ambiguous; a reading was pinned
- `d`: notation ambiguous; a reading was pinned
- `\sigma_j`: notation ambiguous; a reading was pinned

12 result(s) of the paper were examined. None was found wrong as printed. In Lean: 12 proved, 0 taken from the literature as cited, 0 not certified, 0 not formalized.

## What was wrong and what was done

No error was found in the results examined.

## Clarifications (not errors)

Nothing in this section is an error of the paper. Each item is something the paper determines but does not say, made explicit so that the statements can be read, and formalized, in one way.

**How a statement is read.**

- **Theorem 1.1.** $Q_s$ contains a simple undirected cycle.
- **Theorem 1.1.** For a fixed pair $(r,s)$, $D$ has edges $r(t)s(t)$ oriented from $r(t)$ to $s(t)$ for $t\in A$; grouping pairs by $D$ identifies pairs exactly when their underlying undirected edge sets coincide.
- **Theorem 1.1.** The one-vertex graph declared to be a tree has no edges.
- **Corollary 7.1.** $G$ is a finite simple undirected cubic bipartite planar $3$-vertex-connected graph, and $e\in E(G)$.

**Side conditions the proofs use without stating them.**

- **Theorem 1.1.** $M$ is finite.
- **Theorem 1.1.** $\abs{V(T)}<\infty$.

**Notation.**

- $G$: $G$ denotes a finite simple undirected graph. In Theorem~\ref{thm:main}, Corollary~\ref{cor:edge-avoidance}: $G$ is cubic, bipartite, planar, and $3$-vertex-connected; its sphere embedding is fixed for the dual construction in the proof. In Corollary~\ref{cor:pfaffian-paths}: $G$ is cubic, $3$-vertex-connected, Pfaffian, and bipartite; planarity is not assumed. In \cite[Theorem 4.16]{GSW2023}, used in the proof of Corollary~\ref{cor:pfaffian-paths}: In condition (i), $G$ ranges over cubic bipartite planar $3$-vertex-connected graphs; in condition (v), $G$ ranges over cubic $3$-vertex-connected Pfaffian bipartite graphs. In the application, $G$ belongs to the latter class. In \cite[Theorem 4.6]{GSW2023}, used in the proof of Corollary~\ref{cor:pfaffian-paths}: $G$ ranges over planar graphs; cubicity, bipartiteness, and $3$-vertex-connectivity are not restrictions on this assertion.
- $T$: $T$ is a connected simple sphere triangulation with at least four vertices and a $3$-cycle as every face boundary, with faces colored black and white so that every edge has one incident face of each color. In Proposition~\ref{prop:pairs}, Lemma~\ref{lem:root-components}, Lemma~\ref{lem:P-forest}: $T$ has no separating triangle. In Theorem~\ref{thm:main}: $T=G^*$ for the fixed sphere embedding of $G$, with its face coloring induced by the bipartition of $G$.
- $e_0$: $e_0$ denotes the prescribed edge of the facial triangle $t_0$. In Corollary~\ref{cor:edge-avoidance}: $e_0=e^*$, where $e^*$ is the dual of the prescribed edge $e\in E(G)$, and $t_0$ is chosen to contain $e^*$.
- $v$: $v$ denotes a vertex of the ambient graph, with $v\in V(t)$ whenever it indexes an incidence $(t,v)$. In Theorem~\ref{thm:partition}, Lemma~\ref{lem:disk}, Proposition~\ref{prop:forest-state}, Lemma~\ref{lem:cancel}, Lemma~\ref{lem:circulation}, Lemma~\ref{lem:P-forest}: The ambient vertex set is $V(T)$; in $\delta(v,w)$ the vertices $v,w$ are adjacent in $T$. In Corollary~\ref{cor:pfaffian-paths}, \cite[Theorem 4.16]{GSW2023}, used in the proof of Corollary~\ref{cor:pfaffian-paths}: The ambient vertex set is $V(G)$.
- $w$: The symbol $w$ is local notation reused for a white triangular-face count and for an endpoint of an edge of $T$. In Proposition~\ref{prop:pairs}: $w$ is the number of white triangular faces of the inherited sphere embedding of the component $K$ of $T[U]$ under consideration, where $K$ has at least four vertices. In Lemma~\ref{lem:disk}, Lemma~\ref{lem:cancel}, Lemma~\ref{lem:P-forest}: In the definition of $\delta(v,w)$, $w\in V(T)$ is adjacent to $v$.
- $a$: $a$ denotes either a real incidence-weight function $a(t,v)$, indexed by $t\in A$ and $v\in V(t)$, or a nonnegative integer root count, according to context. In Lemma~\ref{lem:cancel}: The incidence weights $a(t,v)$ are arbitrary real numbers. In Lemma~\ref{lem:circulation}: The incidence weights $a(t,v)$ are to be chosen so that every counterclockwise simple spoke cycle has strictly positive weight, with center-to-vertex traversal weighted by $a(t,v)$ and reverse traversal by $-a(t,v)$. In Proposition~\ref{prop:forest-state}: In the nonvanishing argument, the incidence weights $a(t,v)$ are fixed at a choice for which every counterclockwise simple spoke cycle has strictly positive signed weight. In Lemma~\ref{lem:root-components}: $a$ is the number of roots in the component under consideration, whose number of vertices is $q$.
- $\omega$: For a given assignment of real incidence weights $a(t,v)$, the real-valued state functional is $\omega(s)=\sum_{t\in A}a(t,s(t))$. In Proposition~\ref{prop:forest-state}: In the nonvanishing part of the proof, $\omega$ uses the fixed incidence weights supplied by Lemma~\ref{lem:circulation}, for which every counterclockwise simple spoke cycle has strictly positive weight.
- $D$: $D$ is the union of vertex-disjoint simple cycles on $X$ formed by the chosen edges, with the orientation supplied by a pair forgotten when grouping pairs; the pairs in a group are exactly the independent orientations of its cycles.
- $Z$: For a given assignment of real incidence weights $a(t,v)$, $Z$ is the function $Z:\mathbb{R}\longrightarrow\mathbb{C}$ defined by $Z(x)=\sum_{(r,s)\ {\rm pair}}\ii^{J(r,s)}\exp(x\omega(s))$, summing over all ordered pairs of states. In Proposition~\ref{prop:forest-state}: In the nonvanishing part of the proof, $Z$ uses the fixed incidence weights supplied by Lemma~\ref{lem:circulation}, for which every counterclockwise simple spoke cycle has strictly positive weight.
- $C$: $C$ denotes a simple cycle in the graph specified by its context. In Proposition~\ref{prop:forest-state}: $C$ is a component cycle of the undirected paired edge set $D$, with clockwise and counterclockwise orientations in the fixed plane embedding. In Corollary~\ref{cor:pfaffian-paths}, \cite[Theorem 4.16]{GSW2023}, used in the proof of Corollary~\ref{cor:pfaffian-paths}, \cite[Theorem 4.6]{GSW2023}, used in the proof of Corollary~\ref{cor:pfaffian-paths}: In the Pfaffian condition, $C$ ranges over even cycles of $G$ such that $G-V(C)$ has a perfect matching.
- $\widetilde r$: $\widetilde r$ is obtained from a partner $r$ of fixed $s$ by replacing $r(t)$ with $u(t)$ precisely on the triangles supplying a simple undirected cycle of $Q_s$ chosen using $s$ alone, leaving all other assignments unchanged.
- $U$: $U\subseteq V(T)$ is a vertex set, and $T[U]$ is the induced subgraph containing every edge of $T$ with both endpoints in $U$. In Proposition~\ref{prop:pairs}: In the density argument, $U=V(T)\setminus S$ and $U$ contains the three roots.
- $e$: The notation $e$ has a local meaning determined by its context. In Proposition~\ref{prop:pairs}: $e(U)=\abs{E(T[U])}$, where the argument uses $U=V(T)\setminus S$, containing the three roots. In Corollary~\ref{cor:edge-avoidance}: $e$ is an arbitrary prescribed edge of $G$, with $e\in E(G)$.
- $G^*$: $G^*$ denotes the sphere dual of $G$ with respect to the chosen sphere embedding.
- $B$: $B$ is the number of original black faces of $T$ in the region under consideration. In Lemma~\ref{lem:disk}: The region is the bounded disk of a simple directed cycle in the edges chosen using state $r$. In Lemma~\ref{lem:P-forest}: The region is the bounded disk of the hypothetical simple cycle in $P_0$, with its orientation supplied by state $s$. In Theorem~\ref{thm:partition}: The region is one side of the separating $3$-cycle used in the split, and $B$ counts its original black faces before the cap is added.
- $W$: $W$ is the number of original white faces of $T$ in the region under consideration. In Lemma~\ref{lem:disk}: The region is the bounded disk of a simple directed cycle in the edges chosen using state $r$. In Lemma~\ref{lem:P-forest}: The region is the bounded disk of the hypothetical simple cycle in $P_0$, with its orientation supplied by state $s$. In Theorem~\ref{thm:partition}: The region is one side of the separating $3$-cycle used in the split, and $W$ counts its original white faces before the cap is added.
- $I$: $I$ is the number of vertices strictly inside the bounded disk of the simple directed cycle in the edges chosen using state $r$.
- $h$: $h$ is the length of the simple cycle bounding the disk under consideration. In Lemma~\ref{lem:disk}: The cycle is a simple directed cycle in the edges chosen from the black triangles using state $r$. In Lemma~\ref{lem:P-forest}: The cycle is a hypothetical undirected simple cycle in $P_0$, directed by its prescribed orientation using state $s$.
- $l$: $l$ counts the boundary edges of the bounded disk of the simple cycle under consideration whose incident black face lies in that disk. In Lemma~\ref{lem:disk}: The cycle is a simple directed cycle in the edges chosen from the black triangles using state $r$. In Lemma~\ref{lem:P-forest}: The cycle is a hypothetical undirected simple cycle in $P_0$, directed by its prescribed orientation using state $s$.
- $b$: The notation $b(U)$ denotes the number of actual black faces of $T$ all of whose vertices belong to $U$, whereas the unadorned local scalar $b$ counts black triangular faces of the component $K$.
- $K$: $K$ denotes a connected component of $T[U]$ with its inherited sphere embedding. In Proposition~\ref{prop:pairs}: In the face-region calculation, $K$ has $p\ge4$ vertices.
- $d$: $d\ge4$ is the boundary length of the selected nontriangular face region of $K$, counted by edge-side incidences, so a bridge contributes twice.
- $\sigma_j$: For a nontriangular face region of boundary length $d$, $\sigma_j$ is $+1$ when the original face of $T$ incident to the region's $j$th boundary edge-side is black and $-1$ when it is white, for $1\le j\le d$, with repeated boundary occurrences counted separately.

## What was proved in Lean, and what was not

A result is proved in Lean when a Lean declaration reviewed as stating it has a complete proof using no axiom beyond the standard ones. For a corrected result, the corrected statement is the one formalized.

| Result | Formal status | Lean declaration | Axioms |
| --- | --- | --- | --- |
| Theorem 1.1 | proved in Lean, under 5 condition(s) made explicit | `OaiPairedStatesHamiltonian.isHamiltonian_of_mainDomain` (`TMain.lean:23`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Lemma 2.1 | proved in Lean, under 1 condition(s) made explicit | `OaiPairedStatesHamiltonian.SphereMap.dual_compl_spanning` (`Helpers/Duality.lean:42`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Theorem 2.2 | proved in Lean, under 5 condition(s) made explicit | `OaiPairedStatesHamiltonian.exists_tree_partition` (`TPartition.lean:29`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Proposition 3.1 | proved in Lean, under 1 condition(s) made explicit | `OaiPairedStatesHamiltonian.exists_pair_of_noSeparatingTriangle` (`Helpers/Pairs.lean:106`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Lemma 4.1 | proved in Lean | `OaiPairedStatesHamiltonian.delta_sum_of_simple_cycle` (`Helpers/Disk.lean:123`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Proposition 5.1 | proved in Lean, under 2 condition(s) made explicit | `OaiPairedStatesHamiltonian.exists_pair_qs_forest` (`Helpers/ForestState.lean:173`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Lemma 5.2 | proved in Lean, under 1 condition(s) made explicit | `OaiPairedStatesHamiltonian.sum_Z_terms_eq_zero_of_cyclic` (`Helpers/Cancel.lean:78`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Lemma 5.3 | proved in Lean | `OaiPairedStatesHamiltonian.exists_positive_spoke_weights` (`Helpers/Circulation.lean:391`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Lemma 6.1 | proved in Lean | `OaiPairedStatesHamiltonian.qs_component_contains_unique_root` (`Helpers/RootComponents.lean:44`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Lemma 6.2 | proved in Lean, under 4 condition(s) made explicit | `OaiPairedStatesHamiltonian.selectedSet_isForest` (`Helpers/PForest.lean:23`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Corollary 7.1 | proved in Lean, under 6 condition(s) made explicit | `OaiPairedStatesHamiltonian.exists_hamiltonian_avoiding_edge` (`TEdgeAvoidance.lean:24`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Corollary 7.2 | proved in Lean, given 2 cited result(s), under 5 condition(s) made explicit | `OaiPairedStatesHamiltonian.p4Hamiltonian_of_pfaffian` (`TPfaffianPaths.lean:53`) | the standard ones only (propext, Classical.choice, Quot.sound) |

**Taken from the literature, not proved here.**

- GSW2023, Theorem 4.16 — checked against arXiv:2202.11641 e-print (fetched by the runner; the arXiv version may differ from the published one)

  What Lean assumes for it: `OaiPairedStatesHamiltonian.GSW2023Thm416` (`Helpers/CitedGates.lean:28`)

  ```lean
  noncomputable def GSW2023Thm416 : Sort 0 :=
    (∀ n (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], MainDomain G → G.IsHamiltonian) ↔
    (∀ n (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      PfaffianPathsGraph G → PfaffianPathsBipartite G → IsP4Hamiltonian G)
  ```

  The passage of the proof:

  > Gorsky, Steiner, and Wiederrecht \cite[Theorem~4.16]{GSW2023} proved
  > the equivalence of Barnette's conjecture, their condition~(i), with
  > this \(P_4\)-Hamiltonicity statement, their condition~(v).
- GSW2023, Theorem 4.6 — checked against arXiv:2202.11641 e-print (fetched by the runner; the arXiv version may differ from the published one)

  What Lean assumes for it: `OaiPairedStatesHamiltonian.GSW2023Thm46` (`Helpers/CitedGates.lean:42`)

  ```lean
  noncomputable def GSW2023Thm46 : Sort 0 :=
    ∀ n (G : SimpleGraph (Fin n)), IsPlanar G → IsPfaffian G
  ```

  The passage of the proof:

  > Every planar graph is Pfaffian
  > \cite[Theorem~4.6]{GSW2023}, so the corollary includes the graphs of
  > Theorem~\ref{thm:main}, while also allowing nonplanar graphs.

The Lean development builds; it contains no `sorry`, `admit` or added axiom.

## The corrected paper

`bundle/corrected_paper/` holds the paper as it reads after the corrections, as plain source in the author's own class and layout, compiled to `bundle/corrected_paper/paper.pdf` (13 pages). `bundle/MATCH.md` sets each result beside its Lean declaration; `bundle/lean/` holds the Lean code.

The mechanical checks leave nothing open.

# Technical appendix

The records behind the report above, by the run's own identifiers.

- paper: `paper.tex` (source sha256 `f8d9d68f47f4793275f5b1ea167f683287c029f07e0848e424f89a696282abd1`)
- stage completed: `5`
- results in scope: 12

| bucket | count |
| --- | --- |
| verified | 3 |
| verified_with_bookkeeping | 8 |
| conditional | 1 |
| repaired | 0 |
| unresolved | 0 |
| not_checked | 0 |
| not_determined | 0 |
| refuted | 0 |

> This is a conditional report. A `verified` result is verified only up to the cited results it assumes, the substrate gates left assumed, and the conditions added during formalization — all listed in full below. `unresolved` means the formalization did not close; it is NOT a claim that the result is wrong. A `refuted` row is a result shown false by a positive witness with no confirmed repair; a `repaired` row was false as printed, and an independent referee confirmed its minimal repair. A `not_determined` row could not be checked as printed: the paper does not say enough to determine the claim, and no reading or repair was adopted; it is NOT a claim that the result is wrong.

## Results

### 1. `thm:main`

| field | value |
| --- | --- |
| bucket | `verified_with_bookkeeping` |
| source | `paper.tex:79-82` (`theorem`, label `thm:main`) |
| statement | \label{thm:main} Every finite simple undirected graph that is cubic, bipartite, planar, and \(3\)-vertex-connected has a Hamiltonian cycle. |
| appended hypothesis list | ass:main-domain |
| Lean | `TMain.lean:23` — `OaiPairedStatesHamiltonian.isHamiltonian_of_mainDomain` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | `ass:bk-1`, `ass:bk-2`, `ass:pin-1`, `ass:pin-3`, `ass:pin-4` |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 2. `lem:duality`

| field | value |
| --- | --- |
| bucket | `verified_with_bookkeeping` |
| source | `paper.tex:189-195` (`lemma`, label `lem:duality`) |
| statement | \label{lem:duality} Let \(M\) be a connected graph embedded on the sphere. The duals of the edges complementary to a spanning tree of \(M\) form a spanning tree of \(M^*\). More generally, the duals of the edges complementary to a spanning forest of \(M\) form a connected spanning subgraph of \(M^*\). |
| appended hypothesis list | ass:duality-embedding |
| Lean | `Helpers/Duality.lean:42` — `OaiPairedStatesHamiltonian.SphereMap.dual_compl_spanning` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness bookkeeping |
| added conditions | `ass:bk-1` |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 3. `thm:partition`

| field | value |
| --- | --- |
| bucket | `verified_with_bookkeeping` |
| source | `paper.tex:208-215` (`theorem`, label `thm:partition`) |
| statement | \label{thm:partition} Let \(T\) be a sphere triangulation whose faces are colored black and white so that each edge has one incident face of each color. For any facial triangle \(t_0\) and any edge \(e_0\) of \(t_0\), the vertex set admits a partition into two sets, each inducing a tree, such that the endpoints of \(e_0\) are in one set and the third vertex of \(t_0\) is in the other. |
| appended hypothesis list | ass:partition-coloring |
| Lean | `TPartition.lean:29` — `OaiPairedStatesHamiltonian.exists_tree_partition` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness bookkeeping |
| added conditions | `ass:bk-1`, `ass:bk-2`, `ass:pin-1`, `ass:pin-3`, `ass:pin-4` |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 4. `prop:pairs`

| field | value |
| --- | --- |
| bucket | `verified_with_bookkeeping` |
| source | `paper.tex:245-247` (`proposition`, label `prop:pairs`) |
| statement | \label{prop:pairs} If \(T\) has no separating triangle, then a pair of states exists. |
| appended hypothesis list | ass:pairs-no-separating |
| Lean | `Helpers/Pairs.lean:106` — `OaiPairedStatesHamiltonian.exists_pair_of_noSeparatingTriangle` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | `ass:pin-4` |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 5. Disk identity `lem:disk`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `paper.tex:362-368` (`lemma`, label `lem:disk`) |
| statement | \label{lem:disk} Let \(r\) be a state. In each \(t\in A\), choose one edge directed from \(r(t)\) to another vertex of \(t\). Every simple directed cycle in the chosen edges avoids the roots. Its \(\delta\)-sum is \(-3\) if it is counterclockwise, and \(3\) if it is clockwise. |
| Lean | `Helpers/Disk.lean:123` — `OaiPairedStatesHamiltonian.delta_sum_of_simple_cycle` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 6. `prop:forest-state`

| field | value |
| --- | --- |
| bucket | `verified_with_bookkeeping` |
| source | `paper.tex:413-416` (`proposition`, label `prop:forest-state`) |
| statement | \label{prop:forest-state} Whenever at least one pair exists, some pair \((r,s)\) has \(Q_s\) a forest. |
| appended hypothesis list | ass:pair-existence |
| Lean | `Helpers/ForestState.lean:173` — `OaiPairedStatesHamiltonian.exists_pair_qs_forest` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | `ass:pin-1`, `ass:pin-3` |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 7. `lem:cancel`

| field | value |
| --- | --- |
| bucket | `verified_with_bookkeeping` |
| source | `paper.tex:446-449` (`lemma`, label `lem:cancel`) |
| statement | \label{lem:cancel} For fixed \(s\) with cyclic \(Q_s\), the terms of \eqref{eq:Z} having second state \(s\) sum to zero. |
| appended hypothesis list | ass:cancel-cyclic |
| Lean | `Helpers/Cancel.lean:78` — `OaiPairedStatesHamiltonian.sum_Z_terms_eq_zero_of_cyclic` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | `ass:pin-1` |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 8. `lem:circulation`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `paper.tex:497-502` (`lemma`, label `lem:circulation`) |
| statement | \label{lem:circulation} There are real numbers \(a(t,v)\) on the spokes of \(H_0\) such that every counterclockwise simple spoke cycle has strictly positive weight, where center-to-vertex traversal has weight \(a(t,v)\) and reverse traversal its negative. |
| Lean | `Helpers/Circulation.lean:391` — `OaiPairedStatesHamiltonian.exists_positive_spoke_weights` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 9. `lem:root-components`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `paper.tex:603-606` (`lemma`, label `lem:root-components`) |
| statement | \label{lem:root-components} For a pair \((r,s)\) with \(Q_s\) a forest, every component of \(Q_s\) contains exactly one of the three roots. |
| appended hypothesis list | ass:root-forest, ass:trees-no-separating |
| Lean | `Helpers/RootComponents.lean:44` — `OaiPairedStatesHamiltonian.qs_component_contains_unique_root` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 10. lem:P-forest `lem:p-forest`

| field | value |
| --- | --- |
| bucket | `verified_with_bookkeeping` |
| source | `paper.tex:663-665` (`lemma`, label `lem:P-forest`) |
| statement | \label{lem:P-forest} The selected set \(P\) is a forest. |
| Lean | `Helpers/PForest.lean:23` — `OaiPairedStatesHamiltonian.selectedSet_isForest` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | `ass:bk-1`, `ass:pin-1`, `ass:pin-3`, `ass:pin-4` |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 11. cor:edge-avoidance `thm:edge-avoidance`

| field | value |
| --- | --- |
| bucket | `verified_with_bookkeeping` |
| source | `paper.tex:794-797` (`corollary`, label `cor:edge-avoidance`) |
| statement | \label{cor:edge-avoidance} For every graph \(G\) satisfying Theorem~\ref{thm:main} and every edge \(e\in E(G)\), there is a Hamiltonian cycle of \(G\) avoiding \(e\). |
| appended hypothesis list | ass:edge-avoidance-domain |
| Lean | `TEdgeAvoidance.lean:24` — `OaiPairedStatesHamiltonian.exists_hamiltonian_avoiding_edge` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | `ass:bk-1`, `ass:bk-2`, `ass:pin-1`, `ass:pin-2`, `ass:pin-3`, `ass:pin-4` |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 12. Prescribed paths in Pfaffian graphs `thm:pfaffian-paths`

| field | value |
| --- | --- |
| bucket | `conditional` |
| source | `paper.tex:812-818` (`corollary`, label `cor:pfaffian-paths`) |
| statement | \label{cor:pfaffian-paths} Let \(G\) be a finite simple undirected graph that is cubic, \(3\)-vertex-connected, Pfaffian, and bipartite. Every path on four vertices (three edges) in \(G\) is contained in a Hamiltonian cycle. In other words, \(G\) is \(P_4\)-Hamiltonian; in particular, it is Hamiltonian. |
| appended hypothesis list | ass:pfaffian-paths-graph, ass:pfaffian-paths-bipartite |
| Lean | `TPfaffianPaths.lean:53` — `OaiPairedStatesHamiltonian.p4Hamiltonian_of_pfaffian` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | `ass:bk-1`, `ass:bk-2`, `ass:pin-1`, `ass:pin-3`, `ass:pin-4` |
| cited results | `lem:gsw2023-theorem-4-16` (GSW2023, Theorem 4.16); `lem:gsw2023-theorem-4-6` (GSW2023, Theorem 4.6) |
| assumed substrate gates | — |
| findings | — |

## Corrected version

9 of 12 result(s) differ from the version you provided — 0 repaired, 0 with the proof completed (no error), 9 only with a side condition or reading made explicit; the others are as printed. The Lean formalization is of the corrected version.

### `thm:main` (`paper.tex:79-82`)

- as printed: \label{thm:main} Every finite simple undirected graph that is cubic, bipartite, planar, and \(3\)-vertex-connected has a Hamiltonian cycle.
- corrected: statement unchanged
- no error: only a side condition or reading the referee made explicit (see below)
- side condition added by the confirming referee `ass:bk-1`: $M$ is finite. — The Euler count and the connected graph characterization by its number of edges use finiteness.
- side condition added by the confirming referee `ass:bk-2`: $\abs{V(T)}<\infty$. — Induction on the vertex count and the applications of finite complementary forest duality require finiteness.
- side condition added by the confirming referee `ass:pin-1`: $Q_s$ contains a simple undirected cycle. — pins reading of ass:cancel-cyclic: The proof of Lemma~\ref{lem:cancel} begins by choosing a simple undirected cycle in $Q_s$, using $s$ alone.
- side condition added by the confirming referee `ass:pin-3`: For a fixed pair $(r,s)$, $D$ has edges $r(t)s(t)$ oriented from $r(t)$ to $s(t)$ for $t\in A$; grouping pairs by $D$ identifies pairs exactly when their underlying undirected edge sets coincide. — pins reading of def:paired-edges: The defining paragraph directs each edge from $r(t)$ to $s(t)$. The nonvanishing argument for Proposition~\ref{prop:forest-state} explicitly groups by the undirected edge set and identifies the group with independent orientations of its cycles.
- side condition added by the confirming referee `ass:pin-4`: The one-vertex graph declared to be a tree has no edges. — pins reading of def:singleton-tree: The setup defines forests by acyclicity, specifies that triangulations are simple, and separately permits loops only in intermediate plane graphs. These conventions identify the singleton tree as the edgeless graph.

### `lem:duality` (`paper.tex:189-195`)

- as printed: \label{lem:duality} Let \(M\) be a connected graph embedded on the sphere. The duals of the edges complementary to a spanning tree of \(M\) form a spanning tree of \(M^*\). More generally, the duals of the edges complementary to a spanning forest of \(M\) form a connected spanning subgraph of \(M^*\).
- corrected: statement unchanged
- no error: only a side condition or reading the referee made explicit (see below)
- side condition added by the confirming referee `ass:bk-1`: $M$ is finite. — The Euler count and the connected graph characterization by its number of edges use finiteness.

### `thm:partition` (`paper.tex:208-215`)

- as printed: \label{thm:partition} Let \(T\) be a sphere triangulation whose faces are colored black and white so that each edge has one incident face of each color. For any facial triangle \(t_0\) and any edge \(e_0\) of \(t_0\), the vertex set admits a partition into two sets, each inducing a tree, such that the endpoints of \(e_0\) are in one set and the third vertex of \(t_0\) is in the other.
- corrected: statement unchanged
- no error: only a side condition or reading the referee made explicit (see below)
- side condition added by the confirming referee `ass:bk-1`: $M$ is finite. — The Euler count and the connected graph characterization by its number of edges use finiteness.
- side condition added by the confirming referee `ass:bk-2`: $\abs{V(T)}<\infty$. — Induction on the vertex count and the applications of finite complementary forest duality require finiteness.
- side condition added by the confirming referee `ass:pin-1`: $Q_s$ contains a simple undirected cycle. — pins reading of ass:cancel-cyclic: The proof of Lemma~\ref{lem:cancel} begins by choosing a simple undirected cycle in $Q_s$, using $s$ alone.
- side condition added by the confirming referee `ass:pin-3`: For a fixed pair $(r,s)$, $D$ has edges $r(t)s(t)$ oriented from $r(t)$ to $s(t)$ for $t\in A$; grouping pairs by $D$ identifies pairs exactly when their underlying undirected edge sets coincide. — pins reading of def:paired-edges: The defining paragraph directs each edge from $r(t)$ to $s(t)$. The nonvanishing argument for Proposition~\ref{prop:forest-state} explicitly groups by the undirected edge set and identifies the group with independent orientations of its cycles.
- side condition added by the confirming referee `ass:pin-4`: The one-vertex graph declared to be a tree has no edges. — pins reading of def:singleton-tree: The setup defines forests by acyclicity, specifies that triangulations are simple, and separately permits loops only in intermediate plane graphs. These conventions identify the singleton tree as the edgeless graph.

### `prop:pairs` (`paper.tex:245-247`)

- as printed: \label{prop:pairs} If \(T\) has no separating triangle, then a pair of states exists.
- corrected: statement unchanged
- no error: only a side condition or reading the referee made explicit (see below)
- side condition added by the confirming referee `ass:pin-4`: The one-vertex graph declared to be a tree has no edges. — pins reading of def:singleton-tree: The setup defines forests by acyclicity, specifies that triangulations are simple, and separately permits loops only in intermediate plane graphs. These conventions identify the singleton tree as the edgeless graph.

### `prop:forest-state` (`paper.tex:413-416`)

- as printed: \label{prop:forest-state} Whenever at least one pair exists, some pair \((r,s)\) has \(Q_s\) a forest.
- corrected: statement unchanged
- no error: only a side condition or reading the referee made explicit (see below)
- side condition added by the confirming referee `ass:pin-1`: $Q_s$ contains a simple undirected cycle. — pins reading of ass:cancel-cyclic: The proof of Lemma~\ref{lem:cancel} begins by choosing a simple undirected cycle in $Q_s$, using $s$ alone.
- side condition added by the confirming referee `ass:pin-3`: For a fixed pair $(r,s)$, $D$ has edges $r(t)s(t)$ oriented from $r(t)$ to $s(t)$ for $t\in A$; grouping pairs by $D$ identifies pairs exactly when their underlying undirected edge sets coincide. — pins reading of def:paired-edges: The defining paragraph directs each edge from $r(t)$ to $s(t)$. The nonvanishing argument for Proposition~\ref{prop:forest-state} explicitly groups by the undirected edge set and identifies the group with independent orientations of its cycles.

### `lem:cancel` (`paper.tex:446-449`)

- as printed: \label{lem:cancel} For fixed \(s\) with cyclic \(Q_s\), the terms of \eqref{eq:Z} having second state \(s\) sum to zero.
- corrected: statement unchanged
- no error: only a side condition or reading the referee made explicit (see below)
- side condition added by the confirming referee `ass:pin-1`: $Q_s$ contains a simple undirected cycle. — pins reading of ass:cancel-cyclic: The proof of Lemma~\ref{lem:cancel} begins by choosing a simple undirected cycle in $Q_s$, using $s$ alone.

### `lem:p-forest` (`paper.tex:663-665`)

- as printed: \label{lem:P-forest} The selected set \(P\) is a forest.
- corrected: statement unchanged
- no error: only a side condition or reading the referee made explicit (see below)
- side condition added by the confirming referee `ass:bk-1`: $M$ is finite. — The Euler count and the connected graph characterization by its number of edges use finiteness.
- side condition added by the confirming referee `ass:pin-1`: $Q_s$ contains a simple undirected cycle. — pins reading of ass:cancel-cyclic: The proof of Lemma~\ref{lem:cancel} begins by choosing a simple undirected cycle in $Q_s$, using $s$ alone.
- side condition added by the confirming referee `ass:pin-3`: For a fixed pair $(r,s)$, $D$ has edges $r(t)s(t)$ oriented from $r(t)$ to $s(t)$ for $t\in A$; grouping pairs by $D$ identifies pairs exactly when their underlying undirected edge sets coincide. — pins reading of def:paired-edges: The defining paragraph directs each edge from $r(t)$ to $s(t)$. The nonvanishing argument for Proposition~\ref{prop:forest-state} explicitly groups by the undirected edge set and identifies the group with independent orientations of its cycles.
- side condition added by the confirming referee `ass:pin-4`: The one-vertex graph declared to be a tree has no edges. — pins reading of def:singleton-tree: The setup defines forests by acyclicity, specifies that triangulations are simple, and separately permits loops only in intermediate plane graphs. These conventions identify the singleton tree as the edgeless graph.

### `thm:edge-avoidance` (`paper.tex:794-797`)

- as printed: \label{cor:edge-avoidance} For every graph \(G\) satisfying Theorem~\ref{thm:main} and every edge \(e\in E(G)\), there is a Hamiltonian cycle of \(G\) avoiding \(e\).
- corrected: statement unchanged
- no error: only a side condition or reading the referee made explicit (see below)
- side condition added by the confirming referee `ass:bk-1`: $M$ is finite. — The Euler count and the connected graph characterization by its number of edges use finiteness.
- side condition added by the confirming referee `ass:bk-2`: $\abs{V(T)}<\infty$. — Induction on the vertex count and the applications of finite complementary forest duality require finiteness.
- side condition added by the confirming referee `ass:pin-1`: $Q_s$ contains a simple undirected cycle. — pins reading of ass:cancel-cyclic: The proof of Lemma~\ref{lem:cancel} begins by choosing a simple undirected cycle in $Q_s$, using $s$ alone.
- side condition added by the confirming referee `ass:pin-2`: $G$ is a finite simple undirected cubic bipartite planar $3$-vertex-connected graph, and $e\in E(G)$. — pins reading of ass:edge-avoidance-domain: Theorem~\ref{thm:main} states exactly these graph hypotheses; the proof of Corollary~\ref{cor:edge-avoidance} uses their dual triangulation and applies Theorem~\ref{thm:partition}.
- side condition added by the confirming referee `ass:pin-3`: For a fixed pair $(r,s)$, $D$ has edges $r(t)s(t)$ oriented from $r(t)$ to $s(t)$ for $t\in A$; grouping pairs by $D$ identifies pairs exactly when their underlying undirected edge sets coincide. — pins reading of def:paired-edges: The defining paragraph directs each edge from $r(t)$ to $s(t)$. The nonvanishing argument for Proposition~\ref{prop:forest-state} explicitly groups by the undirected edge set and identifies the group with independent orientations of its cycles.
- side condition added by the confirming referee `ass:pin-4`: The one-vertex graph declared to be a tree has no edges. — pins reading of def:singleton-tree: The setup defines forests by acyclicity, specifies that triangulations are simple, and separately permits loops only in intermediate plane graphs. These conventions identify the singleton tree as the edgeless graph.

### `thm:pfaffian-paths` (`paper.tex:812-818`)

- as printed: \label{cor:pfaffian-paths} Let \(G\) be a finite simple undirected graph that is cubic, \(3\)-vertex-connected, Pfaffian, and bipartite. Every path on four vertices (three edges) in \(G\) is contained in a Hamiltonian cycle. In other words, \(G\) is \(P_4\)-Hamiltonian; in particular, it is Hamiltonian.
- corrected: statement unchanged
- no error: only a side condition or reading the referee made explicit (see below)
- side condition added by the confirming referee `ass:bk-1`: $M$ is finite. — The Euler count and the connected graph characterization by its number of edges use finiteness.
- side condition added by the confirming referee `ass:bk-2`: $\abs{V(T)}<\infty$. — Induction on the vertex count and the applications of finite complementary forest duality require finiteness.
- side condition added by the confirming referee `ass:pin-1`: $Q_s$ contains a simple undirected cycle. — pins reading of ass:cancel-cyclic: The proof of Lemma~\ref{lem:cancel} begins by choosing a simple undirected cycle in $Q_s$, using $s$ alone.
- side condition added by the confirming referee `ass:pin-3`: For a fixed pair $(r,s)$, $D$ has edges $r(t)s(t)$ oriented from $r(t)$ to $s(t)$ for $t\in A$; grouping pairs by $D$ identifies pairs exactly when their underlying undirected edge sets coincide. — pins reading of def:paired-edges: The defining paragraph directs each edge from $r(t)$ to $s(t)$. The nonvanishing argument for Proposition~\ref{prop:forest-state} explicitly groups by the undirected edge set and identifies the group with independent orientations of its cycles.
- side condition added by the confirming referee `ass:pin-4`: The one-vertex graph declared to be a tree has no edges. — pins reading of def:singleton-tree: The setup defines forests by acyclicity, specifies that triangulations are simple, and separately permits loops only in intermediate plane graphs. These conventions identify the singleton tree as the edgeless graph.

## Suggestions to the authors

Not errors: readings the paper determines but does not state, and side conditions the proofs use silently.

- clarification (`ass:pin-1`, used by `thm:main`): $Q_s$ contains a simple undirected cycle. — pins reading of ass:cancel-cyclic: The proof of Lemma~\ref{lem:cancel} begins by choosing a simple undirected cycle in $Q_s$, using $s$ alone.
- clarification (`ass:pin-3`, used by `thm:main`): For a fixed pair $(r,s)$, $D$ has edges $r(t)s(t)$ oriented from $r(t)$ to $s(t)$ for $t\in A$; grouping pairs by $D$ identifies pairs exactly when their underlying undirected edge sets coincide. — pins reading of def:paired-edges: The defining paragraph directs each edge from $r(t)$ to $s(t)$. The nonvanishing argument for Proposition~\ref{prop:forest-state} explicitly groups by the undirected edge set and identifies the group with independent orientations of its cycles.
- clarification (`ass:pin-4`, used by `thm:main`): The one-vertex graph declared to be a tree has no edges. — pins reading of def:singleton-tree: The setup defines forests by acyclicity, specifies that triangulations are simple, and separately permits loops only in intermediate plane graphs. These conventions identify the singleton tree as the edgeless graph.
- clarification (`ass:pin-2`, used by `thm:edge-avoidance`): $G$ is a finite simple undirected cubic bipartite planar $3$-vertex-connected graph, and $e\in E(G)$. — pins reading of ass:edge-avoidance-domain: Theorem~\ref{thm:main} states exactly these graph hypotheses; the proof of Corollary~\ref{cor:edge-avoidance} uses their dual triangulation and applies Theorem~\ref{thm:partition}.
- `ass:cancel-cyclic`: pinned reading: $Q_s$ contains a simple undirected cycle. (The proof of Lemma~\ref{lem:cancel} begins by choosing a simple undirected cycle in $Q_s$, using $s$ alone.)
- `ass:edge-avoidance-domain`: pinned reading: $G$ is a finite simple undirected cubic bipartite planar $3$-vertex-connected graph, and $e\in E(G)$. (Theorem~\ref{thm:main} states exactly these graph hypotheses; the proof of Corollary~\ref{cor:edge-avoidance} uses their dual triangulation and applies Theorem~\ref{thm:partition}.)
- `def:paired-edges`: pinned reading: For a fixed pair $(r,s)$, $D$ has edges $r(t)s(t)$ oriented from $r(t)$ to $s(t)$ for $t\in A$; grouping pairs by $D$ identifies pairs exactly when their underlying undirected edge sets coincide. (The defining paragraph directs each edge from $r(t)$ to $s(t)$. The nonvanishing argument for Proposition~\ref{prop:forest-state} explicitly groups by the undirected edge set and identifies the group with independent orientations of its cycles.)
- `def:singleton-tree`: pinned reading: The one-vertex graph declared to be a tree has no edges. (The setup defines forests by acyclicity, specifies that triangulations are simple, and separately permits loops only in intermediate plane graphs. These conventions identify the singleton tree as the edgeless graph.)
- reading of the symbol `G`: $G$ denotes a finite simple undirected graph. In Theorem~\ref{thm:main}, Corollary~\ref{cor:edge-avoidance}: $G$ is cubic, bipartite, planar, and $3$-vertex-connected; its sphere embedding is fixed for the dual construction in the proof. In Corollary~\ref{cor:pfaffian-paths}: $G$ is cubic, $3$-vertex-connected, Pfaffian, and bipartite; planarity is not assumed. In \cite[Theorem 4.16]{GSW2023}, used in the proof of Corollary~\ref{cor:pfaffian-paths}: In condition (i), $G$ ranges over cubic bipartite planar $3$-vertex-connected graphs; in condition (v), $G$ ranges over cubic $3$-vertex-connected Pfaffian bipartite graphs. In the application, $G$ belongs to the latter class. In \cite[Theorem 4.6]{GSW2023}, used in the proof of Corollary~\ref{cor:pfaffian-paths}: $G$ ranges over planar graphs; cubicity, bipartiteness, and $3$-vertex-connectivity are not restrictions on this assertion. — The proof of Corollary~\ref{cor:pfaffian-paths} invokes the equivalence between conditions (i) and (v) in Lemma lem:gsw2023-theorem-4-16, and invokes the assertion that every planar graph is Pfaffian in Lemma lem:gsw2023-theorem-4-6.
- reading of the symbol `T`: $T$ is a connected simple sphere triangulation with at least four vertices and a $3$-cycle as every face boundary, with faces colored black and white so that every edge has one incident face of each color. In Proposition~\ref{prop:pairs}, Lemma~\ref{lem:root-components}, Lemma~\ref{lem:P-forest}: $T$ has no separating triangle. In Theorem~\ref{thm:main}: $T=G^*$ for the fixed sphere embedding of $G$, with its face coloring induced by the bipartition of $G$. — The sphere-triangulation convention preceding Lemma~\ref{lem:duality} specifies connectedness, simplicity, the minimum vertex count, and triangular boundaries; Theorem~\ref{thm:partition} specifies the coloring. The assumption before Proposition~\ref{prop:pairs} and the assumption opening Section~\ref{sec:trees} supply the separating-triangle restrictions. The proof of Theorem~\ref{thm:main} sets $T=G^*$.
- reading of the symbol `e_0`: $e_0$ denotes the prescribed edge of the facial triangle $t_0$. In Corollary~\ref{cor:edge-avoidance}: $e_0=e^*$, where $e^*$ is the dual of the prescribed edge $e\in E(G)$, and $t_0$ is chosen to contain $e^*$. — Theorem~\ref{thm:partition} prescribes any edge of the chosen facial triangle; the proof of Corollary~\ref{cor:edge-avoidance} chooses a dual facial triangle containing $e^*$ and explicitly prescribes $e_0=e^*$.
- reading of the symbol `v`: $v$ denotes a vertex of the ambient graph, with $v\in V(t)$ whenever it indexes an incidence $(t,v)$. In Theorem~\ref{thm:partition}, Lemma~\ref{lem:disk}, Proposition~\ref{prop:forest-state}, Lemma~\ref{lem:cancel}, Lemma~\ref{lem:circulation}, Lemma~\ref{lem:P-forest}: The ambient vertex set is $V(T)$; in $\delta(v,w)$ the vertices $v,w$ are adjacent in $T$. In Corollary~\ref{cor:pfaffian-paths}, \cite[Theorem 4.16]{GSW2023}, used in the proof of Corollary~\ref{cor:pfaffian-paths}: The ambient vertex set is $V(G)$. — The definition of $\delta$ uses adjacent vertices of $T$, the incidence-weight definition restricts $v$ to $V(t)$, and the final Pfaffian statements concern vertices of $G$.
- reading of the symbol `w`: The symbol $w$ is local notation reused for a white triangular-face count and for an endpoint of an edge of $T$. In Proposition~\ref{prop:pairs}: $w$ is the number of white triangular faces of the inherited sphere embedding of the component $K$ of $T[U]$ under consideration, where $K$ has at least four vertices. In Lemma~\ref{lem:disk}, Lemma~\ref{lem:cancel}, Lemma~\ref{lem:P-forest}: In the definition of $\delta(v,w)$, $w\in V(T)$ is adjacent to $v$. — Lines 290-304 introduce a component $K$ with at least four vertices and its black and white triangular-face counts. Lines 354-357 reuse $w$ as a vertex adjacent to $v$ in the definition of $\delta$.
- reading of the symbol `a`: $a$ denotes either a real incidence-weight function $a(t,v)$, indexed by $t\in A$ and $v\in V(t)$, or a nonnegative integer root count, according to context. In Lemma~\ref{lem:cancel}: The incidence weights $a(t,v)$ are arbitrary real numbers. In Lemma~\ref{lem:circulation}: The incidence weights $a(t,v)$ are to be chosen so that every counterclockwise simple spoke cycle has strictly positive weight, with center-to-vertex traversal weighted by $a(t,v)$ and reverse traversal by $-a(t,v)$. In Proposition~\ref{prop:forest-state}: In the nonvanishing argument, the incidence weights $a(t,v)$ are fixed at a choice for which every counterclockwise simple spoke cycle has strictly positive signed weight. In Lemma~\ref{lem:root-components}: $a$ is the number of roots in the component under consideration, whose number of vertices is $q$. — The incidence-weight definition assigns arbitrary real numbers to incidences. Lemma~\ref{lem:circulation} supplies weights with positive counterclockwise simple spoke-cycle sums, followed by the instruction to fix these weights for the remainder of the proof. The proof of Lemma~\ref{lem:root-components} independently introduces $a$ as a component's root count.
- reading of the symbol `\omega`: For a given assignment of real incidence weights $a(t,v)$, the real-valued state functional is $\omega(s)=\sum_{t\in A}a(t,s(t))$. In Proposition~\ref{prop:forest-state}: In the nonvanishing part of the proof, $\omega$ uses the fixed incidence weights supplied by Lemma~\ref{lem:circulation}, for which every counterclockwise simple spoke cycle has strictly positive weight. — Lines 423-427 define the functional using arbitrary real incidence weights. The paragraph introducing $H_0$, Lemma~\ref{lem:circulation}, and the subsequent sentence 'Fix these weights for the remainder of the proof.' specify the later choice.
- reading of the symbol `D`: $D$ is the union of vertex-disjoint simple cycles on $X$ formed by the chosen edges, with the orientation supplied by a pair forgotten when grouping pairs; the pairs in a group are exactly the independent orientations of its cycles. — The paragraph defining $D$ establishes its directed cycles on $X$; the nonvanishing argument explicitly groups pairs by their undirected edge set and identifies the independent orientation choices.
- reading of the symbol `Z`: For a given assignment of real incidence weights $a(t,v)$, $Z$ is the function $Z:\mathbb{R}\longrightarrow\mathbb{C}$ defined by $Z(x)=\sum_{(r,s)\ {\rm pair}}\ii^{J(r,s)}\exp(x\omega(s))$, summing over all ordered pairs of states. In Proposition~\ref{prop:forest-state}: In the nonvanishing part of the proof, $Z$ uses the fixed incidence weights supplied by Lemma~\ref{lem:circulation}, for which every counterclockwise simple spoke cycle has strictly positive weight. — Lines 419-442 introduce arbitrary real incidence weights and define the sum. Following Lemma~\ref{lem:circulation}, the sentence 'Fix these weights for the remainder of the proof.' specializes those weights for the nonvanishing argument.
- reading of the symbol `C`: $C$ denotes a simple cycle in the graph specified by its context. In Proposition~\ref{prop:forest-state}: $C$ is a component cycle of the undirected paired edge set $D$, with clockwise and counterclockwise orientations in the fixed plane embedding. In Corollary~\ref{cor:pfaffian-paths}, \cite[Theorem 4.16]{GSW2023}, used in the proof of Corollary~\ref{cor:pfaffian-paths}, \cite[Theorem 4.6]{GSW2023}, used in the proof of Corollary~\ref{cor:pfaffian-paths}: In the Pfaffian condition, $C$ ranges over even cycles of $G$ such that $G-V(C)$ has a perfect matching. — The definition of a Pfaffian orientation quantifies over even cycles $C$ for which $G-V(C)$ has a perfect matching; this definition also supplies the meaning of Pfaffian in Lemma lem:gsw2023-theorem-4-6.
- reading of the symbol `\widetilde r`: $\widetilde r$ is obtained from a partner $r$ of fixed $s$ by replacing $r(t)$ with $u(t)$ precisely on the triangles supplying a simple undirected cycle of $Q_s$ chosen using $s$ alone, leaving all other assignments unchanged. — The proof of Lemma~\ref{lem:cancel} explicitly chooses the cycle using $s$ alone and then defines the changed assignments.
- reading of the symbol `U`: $U\subseteq V(T)$ is a vertex set, and $T[U]$ is the induced subgraph containing every edge of $T$ with both endpoints in $U$. In Proposition~\ref{prop:pairs}: In the density argument, $U=V(T)\setminus S$ and $U$ contains the three roots. — Lines 182--184 define the induced subgraph for a vertex set $U$; line 278 specializes $U$ to $V(T)\setminus S$ and states that it contains the three roots.
- reading of the symbol `e`: The notation $e$ has a local meaning determined by its context. In Proposition~\ref{prop:pairs}: $e(U)=\abs{E(T[U])}$, where the argument uses $U=V(T)\setminus S$, containing the three roots. In Corollary~\ref{cor:edge-avoidance}: $e$ is an arbitrary prescribed edge of $G$, with $e\in E(G)$. — The density argument defines $e(U)$ at lines 278--280; Corollary~\ref{cor:edge-avoidance} subsequently quantifies over edges $e\in E(G)$.
- reading of the symbol `G^*`: $G^*$ denotes the sphere dual of $G$ with respect to the chosen sphere embedding. — The proof first fixes a sphere embedding of $G$ and then introduces "The sphere dual \(T=G^*\)" at lines 820 and 830.
- reading of the symbol `B`: $B$ is the number of original black faces of $T$ in the region under consideration. In Lemma~\ref{lem:disk}: The region is the bounded disk of a simple directed cycle in the edges chosen using state $r$. In Lemma~\ref{lem:P-forest}: The region is the bounded disk of the hypothetical simple cycle in $P_0$, with its orientation supplied by state $s$. In Theorem~\ref{thm:partition}: The region is one side of the separating $3$-cycle used in the split, and $B$ counts its original black faces before the cap is added. — Lines 373-376 define the black-face count in a cycle disk; lines 726-731 reuse it with state $s$; lines 793-799 reuse it for one side of a separating triangle before adding its cap.
- reading of the symbol `W`: $W$ is the number of original white faces of $T$ in the region under consideration. In Lemma~\ref{lem:disk}: The region is the bounded disk of a simple directed cycle in the edges chosen using state $r$. In Lemma~\ref{lem:P-forest}: The region is the bounded disk of the hypothetical simple cycle in $P_0$, with its orientation supplied by state $s$. In Theorem~\ref{thm:partition}: The region is one side of the separating $3$-cycle used in the split, and $W$ counts its original white faces before the cap is added. — Lines 373-376 define the white-face count in a cycle disk; lines 726-731 reuse it with state $s$; lines 793-799 reuse it for one side of a separating triangle before adding its cap.
- reading of the symbol `I`: $I$ is the number of vertices strictly inside the bounded disk of the simple directed cycle in the edges chosen using state $r$. — The statement and proof of Lemma~\ref{lem:disk}, particularly lines 370-376, identify the cycle, its bounded disk, and its strictly interior vertices.
- reading of the symbol `h`: $h$ is the length of the simple cycle bounding the disk under consideration. In Lemma~\ref{lem:disk}: The cycle is a simple directed cycle in the edges chosen from the black triangles using state $r$. In Lemma~\ref{lem:P-forest}: The cycle is a hypothetical undirected simple cycle in $P_0$, directed by its prescribed orientation using state $s$. — Lines 373-376 define $h$ as the cycle length; lines 726-731 explicitly reuse the disk data for the cycle in $P_0$.
- reading of the symbol `l`: $l$ counts the boundary edges of the bounded disk of the simple cycle under consideration whose incident black face lies in that disk. In Lemma~\ref{lem:disk}: The cycle is a simple directed cycle in the edges chosen from the black triangles using state $r$. In Lemma~\ref{lem:P-forest}: The cycle is a hypothetical undirected simple cycle in $P_0$, directed by its prescribed orientation using state $s$. — Lines 370-376 define the bounded disk and $l$ for a simple directed cycle in the chosen edges; lines 726-731 reuse these disk data for a cycle in $P_0$ with state $s$.
- reading of the symbol `b`: The notation $b(U)$ denotes the number of actual black faces of $T$ all of whose vertices belong to $U$, whereas the unadorned local scalar $b$ counts black triangular faces of the component $K$. — Lines 277-281 define $b(U)$; lines 291-304 introduce the component with $p\ge4$ and then reuse $b$ as its black triangular-face count. Lines 338-344 distinguish the actual-face count $b_{\rm act}$ when treating other components.
- reading of the symbol `K`: $K$ denotes a connected component of $T[U]$ with its inherited sphere embedding. In Proposition~\ref{prop:pairs}: In the face-region calculation, $K$ has $p\ge4$ vertices. — Lines 291--293 introduce $K$ with $p\ge4$ vertices; lines 337--344 subsequently handle smaller components separately.
- reading of the symbol `d`: $d\ge4$ is the boundary length of the selected nontriangular face region of $K$, counted by edge-side incidences, so a bridge contributes twice. — Lines 174--178 define face length by edge-side incidences, and lines 303--313 apply this convention to nontriangular regions, explicitly allowing repeated boundary edges.
- reading of the symbol `\sigma_j`: For a nontriangular face region of boundary length $d$, $\sigma_j$ is $+1$ when the original face of $T$ incident to the region's $j$th boundary edge-side is black and $-1$ when it is white, for $1\le j\le d$, with repeated boundary occurrences counted separately. — Lines 303--313 give $3(b'-w')=\sum_{j=1}^{d}\sigma_j$, explain cancellation of internal black/white sides, and explicitly include repeated boundary edges.
- added condition (`ass:bk-1`, `thm:main`): $M$ is finite. — The Euler count and the connected graph characterization by its number of edges use finiteness.
- added condition (`ass:bk-2`, `thm:main`): $\abs{V(T)}<\infty$. — Induction on the vertex count and the applications of finite complementary forest duality require finiteness.
- added condition (`ass:bk-1`, `lem:duality`): $M$ is finite. — The Euler count and the connected graph characterization by its number of edges use finiteness.
- added condition (`ass:bk-1`, `thm:partition`): $M$ is finite. — The Euler count and the connected graph characterization by its number of edges use finiteness.
- added condition (`ass:bk-2`, `thm:partition`): $\abs{V(T)}<\infty$. — Induction on the vertex count and the applications of finite complementary forest duality require finiteness.
- added condition (`ass:bk-1`, `lem:p-forest`): $M$ is finite. — The Euler count and the connected graph characterization by its number of edges use finiteness.
- added condition (`ass:bk-1`, `thm:edge-avoidance`): $M$ is finite. — The Euler count and the connected graph characterization by its number of edges use finiteness.
- added condition (`ass:bk-2`, `thm:edge-avoidance`): $\abs{V(T)}<\infty$. — Induction on the vertex count and the applications of finite complementary forest duality require finiteness.
- added condition (`ass:bk-1`, `thm:pfaffian-paths`): $M$ is finite. — The Euler count and the connected graph characterization by its number of edges use finiteness.
- added condition (`ass:bk-2`, `thm:pfaffian-paths`): $\abs{V(T)}<\infty$. — Induction on the vertex count and the applications of finite complementary forest duality require finiteness.

## Added conditions

| id | where | class | condition |
| --- | --- | --- | --- |
| `ass:bk-1` | `thm:main` | V1.5 bookkeeping | $M$ is finite. (The Euler count and the connected graph characterization by its number of edges use finiteness.) |
| `ass:bk-2` | `thm:main` | V1.5 bookkeeping | $\abs{V(T)}<\infty$. (Induction on the vertex count and the applications of finite complementary forest duality require finiteness.) |
| `ass:pin-1` | `thm:main` | V1.5 bookkeeping | $Q_s$ contains a simple undirected cycle. (pins reading of ass:cancel-cyclic: The proof of Lemma~\ref{lem:cancel} begins by choosing a simple undirected cycle in $Q_s$, using $s$ alone.) |
| `ass:pin-3` | `thm:main` | V1.5 bookkeeping | For a fixed pair $(r,s)$, $D$ has edges $r(t)s(t)$ oriented from $r(t)$ to $s(t)$ for $t\in A$; grouping pairs by $D$ identifies pairs exactly when their underlying undirected edge sets coincide. (pins reading of def:paired-edges: The defining paragraph directs each edge from $r(t)$ to $s(t)$. The nonvanishing argument for Proposition~\ref{prop:forest-state} explicitly groups by the undirected edge set and identifies the group with independent orientations of its cycles.) |
| `ass:pin-4` | `thm:main` | V1.5 bookkeeping | The one-vertex graph declared to be a tree has no edges. (pins reading of def:singleton-tree: The setup defines forests by acyclicity, specifies that triangulations are simple, and separately permits loops only in intermediate plane graphs. These conventions identify the singleton tree as the edgeless graph.) |
| `ass:bk-1` | `lem:duality` | V1.5 bookkeeping | $M$ is finite. (The Euler count and the connected graph characterization by its number of edges use finiteness.) |
| `ass:bk-1` | `thm:partition` | V1.5 bookkeeping | $M$ is finite. (The Euler count and the connected graph characterization by its number of edges use finiteness.) |
| `ass:bk-2` | `thm:partition` | V1.5 bookkeeping | $\abs{V(T)}<\infty$. (Induction on the vertex count and the applications of finite complementary forest duality require finiteness.) |
| `ass:pin-1` | `thm:partition` | V1.5 bookkeeping | $Q_s$ contains a simple undirected cycle. (pins reading of ass:cancel-cyclic: The proof of Lemma~\ref{lem:cancel} begins by choosing a simple undirected cycle in $Q_s$, using $s$ alone.) |
| `ass:pin-3` | `thm:partition` | V1.5 bookkeeping | For a fixed pair $(r,s)$, $D$ has edges $r(t)s(t)$ oriented from $r(t)$ to $s(t)$ for $t\in A$; grouping pairs by $D$ identifies pairs exactly when their underlying undirected edge sets coincide. (pins reading of def:paired-edges: The defining paragraph directs each edge from $r(t)$ to $s(t)$. The nonvanishing argument for Proposition~\ref{prop:forest-state} explicitly groups by the undirected edge set and identifies the group with independent orientations of its cycles.) |
| `ass:pin-4` | `thm:partition` | V1.5 bookkeeping | The one-vertex graph declared to be a tree has no edges. (pins reading of def:singleton-tree: The setup defines forests by acyclicity, specifies that triangulations are simple, and separately permits loops only in intermediate plane graphs. These conventions identify the singleton tree as the edgeless graph.) |
| `ass:pin-4` | `prop:pairs` | V1.5 bookkeeping | The one-vertex graph declared to be a tree has no edges. (pins reading of def:singleton-tree: The setup defines forests by acyclicity, specifies that triangulations are simple, and separately permits loops only in intermediate plane graphs. These conventions identify the singleton tree as the edgeless graph.) |
| `ass:pin-1` | `prop:forest-state` | V1.5 bookkeeping | $Q_s$ contains a simple undirected cycle. (pins reading of ass:cancel-cyclic: The proof of Lemma~\ref{lem:cancel} begins by choosing a simple undirected cycle in $Q_s$, using $s$ alone.) |
| `ass:pin-3` | `prop:forest-state` | V1.5 bookkeeping | For a fixed pair $(r,s)$, $D$ has edges $r(t)s(t)$ oriented from $r(t)$ to $s(t)$ for $t\in A$; grouping pairs by $D$ identifies pairs exactly when their underlying undirected edge sets coincide. (pins reading of def:paired-edges: The defining paragraph directs each edge from $r(t)$ to $s(t)$. The nonvanishing argument for Proposition~\ref{prop:forest-state} explicitly groups by the undirected edge set and identifies the group with independent orientations of its cycles.) |
| `ass:pin-1` | `lem:cancel` | V1.5 bookkeeping | $Q_s$ contains a simple undirected cycle. (pins reading of ass:cancel-cyclic: The proof of Lemma~\ref{lem:cancel} begins by choosing a simple undirected cycle in $Q_s$, using $s$ alone.) |
| `ass:bk-1` | `lem:p-forest` | V1.5 bookkeeping | $M$ is finite. (The Euler count and the connected graph characterization by its number of edges use finiteness.) |
| `ass:pin-1` | `lem:p-forest` | V1.5 bookkeeping | $Q_s$ contains a simple undirected cycle. (pins reading of ass:cancel-cyclic: The proof of Lemma~\ref{lem:cancel} begins by choosing a simple undirected cycle in $Q_s$, using $s$ alone.) |
| `ass:pin-3` | `lem:p-forest` | V1.5 bookkeeping | For a fixed pair $(r,s)$, $D$ has edges $r(t)s(t)$ oriented from $r(t)$ to $s(t)$ for $t\in A$; grouping pairs by $D$ identifies pairs exactly when their underlying undirected edge sets coincide. (pins reading of def:paired-edges: The defining paragraph directs each edge from $r(t)$ to $s(t)$. The nonvanishing argument for Proposition~\ref{prop:forest-state} explicitly groups by the undirected edge set and identifies the group with independent orientations of its cycles.) |
| `ass:pin-4` | `lem:p-forest` | V1.5 bookkeeping | The one-vertex graph declared to be a tree has no edges. (pins reading of def:singleton-tree: The setup defines forests by acyclicity, specifies that triangulations are simple, and separately permits loops only in intermediate plane graphs. These conventions identify the singleton tree as the edgeless graph.) |
| `ass:bk-1` | `thm:edge-avoidance` | V1.5 bookkeeping | $M$ is finite. (The Euler count and the connected graph characterization by its number of edges use finiteness.) |
| `ass:bk-2` | `thm:edge-avoidance` | V1.5 bookkeeping | $\abs{V(T)}<\infty$. (Induction on the vertex count and the applications of finite complementary forest duality require finiteness.) |
| `ass:pin-1` | `thm:edge-avoidance` | V1.5 bookkeeping | $Q_s$ contains a simple undirected cycle. (pins reading of ass:cancel-cyclic: The proof of Lemma~\ref{lem:cancel} begins by choosing a simple undirected cycle in $Q_s$, using $s$ alone.) |
| `ass:pin-2` | `thm:edge-avoidance` | V1.5 bookkeeping | $G$ is a finite simple undirected cubic bipartite planar $3$-vertex-connected graph, and $e\in E(G)$. (pins reading of ass:edge-avoidance-domain: Theorem~\ref{thm:main} states exactly these graph hypotheses; the proof of Corollary~\ref{cor:edge-avoidance} uses their dual triangulation and applies Theorem~\ref{thm:partition}.) |
| `ass:pin-3` | `thm:edge-avoidance` | V1.5 bookkeeping | For a fixed pair $(r,s)$, $D$ has edges $r(t)s(t)$ oriented from $r(t)$ to $s(t)$ for $t\in A$; grouping pairs by $D$ identifies pairs exactly when their underlying undirected edge sets coincide. (pins reading of def:paired-edges: The defining paragraph directs each edge from $r(t)$ to $s(t)$. The nonvanishing argument for Proposition~\ref{prop:forest-state} explicitly groups by the undirected edge set and identifies the group with independent orientations of its cycles.) |
| `ass:pin-4` | `thm:edge-avoidance` | V1.5 bookkeeping | The one-vertex graph declared to be a tree has no edges. (pins reading of def:singleton-tree: The setup defines forests by acyclicity, specifies that triangulations are simple, and separately permits loops only in intermediate plane graphs. These conventions identify the singleton tree as the edgeless graph.) |
| `ass:bk-1` | `thm:pfaffian-paths` | V1.5 bookkeeping | $M$ is finite. (The Euler count and the connected graph characterization by its number of edges use finiteness.) |
| `ass:bk-2` | `thm:pfaffian-paths` | V1.5 bookkeeping | $\abs{V(T)}<\infty$. (Induction on the vertex count and the applications of finite complementary forest duality require finiteness.) |
| `ass:pin-1` | `thm:pfaffian-paths` | V1.5 bookkeeping | $Q_s$ contains a simple undirected cycle. (pins reading of ass:cancel-cyclic: The proof of Lemma~\ref{lem:cancel} begins by choosing a simple undirected cycle in $Q_s$, using $s$ alone.) |
| `ass:pin-3` | `thm:pfaffian-paths` | V1.5 bookkeeping | For a fixed pair $(r,s)$, $D$ has edges $r(t)s(t)$ oriented from $r(t)$ to $s(t)$ for $t\in A$; grouping pairs by $D$ identifies pairs exactly when their underlying undirected edge sets coincide. (pins reading of def:paired-edges: The defining paragraph directs each edge from $r(t)$ to $s(t)$. The nonvanishing argument for Proposition~\ref{prop:forest-state} explicitly groups by the undirected edge set and identifies the group with independent orientations of its cycles.) |
| `ass:pin-4` | `thm:pfaffian-paths` | V1.5 bookkeeping | The one-vertex graph declared to be a tree has no edges. (pins reading of def:singleton-tree: The setup defines forests by acyclicity, specifies that triangulations are simple, and separately permits loops only in intermediate plane graphs. These conventions identify the singleton tree as the edgeless graph.) |

## Conditions assumed

### Cited results

| id | used by | citation | locator | checked against |
| --- | --- | --- | --- | --- |
| `lem:gsw2023-theorem-4-16` | `thm:pfaffian-paths` | GSW2023 | Theorem 4.16 | arXiv:2202.11641 e-print (fetched by the runner; the arXiv version may differ from the published one) |
| `lem:gsw2023-theorem-4-6` | `thm:pfaffian-paths` | GSW2023 | Theorem 4.6 | arXiv:2202.11641 e-print (fetched by the runner; the arXiv version may differ from the published one) |

`lem:gsw2023-theorem-4-16` (GSW2023, Theorem 4.16), invoked in the proof of `thm:pfaffian-paths`:

What Lean assumes for it: `OaiPairedStatesHamiltonian.GSW2023Thm416` (`Helpers/CitedGates.lean:28`)

```lean
noncomputable def GSW2023Thm416 : Sort 0 :=
  (∀ n (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], MainDomain G → G.IsHamiltonian) ↔
  (∀ n (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    PfaffianPathsGraph G → PfaffianPathsBipartite G → IsP4Hamiltonian G)
```

The passage of the proof:

> Gorsky, Steiner, and Wiederrecht \cite[Theorem~4.16]{GSW2023} proved
> the equivalence of Barnette's conjecture, their condition~(i), with
> this \(P_4\)-Hamiltonicity statement, their condition~(v).

`lem:gsw2023-theorem-4-6` (GSW2023, Theorem 4.6), invoked in the proof of `thm:pfaffian-paths`:

What Lean assumes for it: `OaiPairedStatesHamiltonian.GSW2023Thm46` (`Helpers/CitedGates.lean:42`)

```lean
noncomputable def GSW2023Thm46 : Sort 0 :=
  ∀ n (G : SimpleGraph (Fin n)), IsPlanar G → IsPfaffian G
```

The passage of the proof:

> Every planar graph is Pfaffian
> \cite[Theorem~4.6]{GSW2023}, so the corollary includes the graphs of
> Theorem~\ref{thm:main}, while also allowing nonplanar graphs.

### Deferred substrate gates

None: every substrate this run needed was built and proved.

## Unresolved / notes

- run-level `ass:cancel-cyclic`: [note, V1.5] pinned reading: $Q_s$ contains a simple undirected cycle. (The proof of Lemma~\ref{lem:cancel} begins by choosing a simple undirected cycle in $Q_s$, using $s$ alone.)
- run-level `ass:edge-avoidance-domain`: [note, V1.5] pinned reading: $G$ is a finite simple undirected cubic bipartite planar $3$-vertex-connected graph, and $e\in E(G)$. (Theorem~\ref{thm:main} states exactly these graph hypotheses; the proof of Corollary~\ref{cor:edge-avoidance} uses their dual triangulation and applies Theorem~\ref{thm:partition}.)
- run-level `def:paired-edges`: [note, V1.5] pinned reading: For a fixed pair $(r,s)$, $D$ has edges $r(t)s(t)$ oriented from $r(t)$ to $s(t)$ for $t\in A$; grouping pairs by $D$ identifies pairs exactly when their underlying undirected edge sets coincide. (The defining paragraph directs each edge from $r(t)$ to $s(t)$. The nonvanishing argument for Proposition~\ref{prop:forest-state} explicitly groups by the undirected edge set and identifies the group with independent orientations of its cycles.)
- run-level `def:singleton-tree`: [note, V1.5] pinned reading: The one-vertex graph declared to be a tree has no edges. (The setup defines forests by acyclicity, specifies that triangulations are simple, and separately permits loops only in intermediate plane graphs. These conventions identify the singleton tree as the edgeless graph.)
- run-level `symbol v`: [note, V1.5] symbol table corrected: space "$V(T)\text{ or }V(G)\text{, according to the ambient graph}$", def "$v$ denotes a vertex of the ambient graph; in an incidence $(t,v)$ it satisfies $v\in V(t)$." (The domain $V(T)$ is correct for the triangulation constructions but does not cover the later graph $G$, which need not be planar.)
- run-level `symbol w`: [note, V1.5] symbol table corrected: type "locally reused face count or vertex", space "$\mathbb{Z}_{\ge0}$ for the face count; $V(T)$ for the vertex", def "Locally, $w$ counts the white triangular faces of $K$ in the density argument; in $\delta(v,w)$, it denotes a vertex adjacent to $v$." (The recorded count describes the density argument but fails to cover the later vertex use. The two meanings are explicitly separated by their local contexts.)
- run-level `symbol a`: [note, V1.5] symbol table corrected: type "incidence weight function or root count", space "$\mathbb{R}^{\{(t,v):t\in A,\ v\in V(t)\}}\cup\mathbb{Z}_{\ge0}$", def "Assign a real number $a(t,v)$ to each incidence $t\in A$, $v\in V(t)$; in the component-counting argument, $a$ is the number of roots in a component." (The entry describes only the incidence-weight function and omits the later scalar root count. The weights are arbitrary for cancellation and chosen with positive spoke-cycle sums for nonvanishing; the root count is a separate local use.)
- run-level `symbol D`: [note, V1.5] symbol table corrected: def "$D$ consists of the edges joining $r(t)$ to $s(t)$ for $t\in A$. A pair directs these edges from $r(t)$ to $s(t)$; pairs are grouped by the underlying undirected edge set $D$." (The recorded definition retains the pair's direction throughout, whereas the nonvanishing argument uses the underlying undirected set as the group index.)
- run-level `symbol C`: [note, V1.5] symbol table corrected: space "$\{\text{cycles of }D\}\cup\{\text{even cycles of }G\}$", def "$C$ denotes a cycle of $D$ in the nonvanishing argument, and an even cycle of $G$ in the definition of a Pfaffian orientation." (The recorded domain omits the later even cycles of $G$. The existing distinction remains valid, and its Pfaffian scope also applies to the newly listed lemma.)
- run-level `symbol P`: [note, V1.5] symbol table corrected: def "Root the white-face tree formed by the duals of the deleted spokes $(t,s(t))$, $t\in A$, at the white triangle $y_0$ across $e_0$ from $t_0$. Assign every tree edge to its endpoint farther from $y_0$. For each deleted spoke $(t,s(t))$, select the edge of $t$ incident with $s(t)$ bordering its assigned white triangle. Finally select $e_0$. Denote the selected set by $P$." (The recorded definition identifies the construction only vaguely; it omits the assignment and incidence rule that determines which primal edges belong to $P$. The later assertion that $P$ is a forest does not redefine it.)
- run-level `symbol e`: [note, V1.5] symbol table corrected: type "locally overloaded notation: induced-edge count function or prescribed graph edge", space "$\mathbb{Z}_{\ge0}^{\mathcal{P}(V(T))}\cup E(G)$", def "The notation $e(U)$ denotes the number of edges in $T[U]$; later, $e\in E(G)$ denotes a prescribed edge of $G$." (The recorded function type and domain cover the density argument but exclude the later graph-edge meaning. These two uses are explicitly distinguished by context.)
- run-level `symbol B`: [note, V1.5] symbol table corrected: def "$B$ counts the original black faces of $T$ in the region under consideration." (The recorded definition restricts B to the directed-cycle disk. The later use counts original black faces on a side of the separating triangle and excludes the new cap.)
- run-level `symbol W`: [note, V1.5] symbol table corrected: def "$W$ counts the original white faces of $T$ in the region under consideration." (The recorded definition only covers a cycle disk. The later use counts original faces on a side of the separating triangle and excludes the new cap.)
- run-level `symbol b`: [note, V1.5] symbol table corrected: type "black-face count function, locally reused as a scalar triangular-face count", space "$\bigl(\mathcal{P}(V(T))\longrightarrow\mathbb{Z}_{\ge0}\bigr)\cup\mathbb{Z}_{\ge0}$", def "$b(U)$ is the number of actual black faces of $T$ all of whose vertices belong to $U$; locally, $b$ counts the black triangular faces of $K$." (The recorded function is correct for $b(U)$ but does not cover the scalar $b$ used in the component calculation. For the component under consideration, its triangular faces are exactly actual faces of T lying in K.)
- run-level `lem:gsw2023-theorem-4-16`: [note, V1.5] cited source checked: arXiv:2202.11641 e-print (fetched by the runner; the arXiv version may differ from the published one)
- run-level `lem:gsw2023-theorem-4-6`: [note, V1.5] cited source checked: arXiv:2202.11641 e-print (fetched by the runner; the arXiv version may differ from the published one)
- note on `ass:cancel-cyclic`: pinned reading: $Q_s$ contains a simple undirected cycle. (The proof of Lemma~\ref{lem:cancel} begins by choosing a simple undirected cycle in $Q_s$, using $s$ alone.)
- note on `ass:edge-avoidance-domain`: pinned reading: $G$ is a finite simple undirected cubic bipartite planar $3$-vertex-connected graph, and $e\in E(G)$. (Theorem~\ref{thm:main} states exactly these graph hypotheses; the proof of Corollary~\ref{cor:edge-avoidance} uses their dual triangulation and applies Theorem~\ref{thm:partition}.)
- note on `def:paired-edges`: pinned reading: For a fixed pair $(r,s)$, $D$ has edges $r(t)s(t)$ oriented from $r(t)$ to $s(t)$ for $t\in A$; grouping pairs by $D$ identifies pairs exactly when their underlying undirected edge sets coincide. (The defining paragraph directs each edge from $r(t)$ to $s(t)$. The nonvanishing argument for Proposition~\ref{prop:forest-state} explicitly groups by the undirected edge set and identifies the group with independent orientations of its cycles.)
- note on `def:singleton-tree`: pinned reading: The one-vertex graph declared to be a tree has no edges. (The setup defines forests by acyclicity, specifies that triangulations are simple, and separately permits loops only in intermediate plane graphs. These conventions identify the singleton tree as the edgeless graph.)
- note on `lem:gsw2023-theorem-4-16`: cited source checked: arXiv:2202.11641 e-print (fetched by the runner; the arXiv version may differ from the published one)
- note on `lem:gsw2023-theorem-4-6`: cited source checked: arXiv:2202.11641 e-print (fetched by the runner; the arXiv version may differ from the published one)
- note on `symbol a`: symbol table corrected: type "incidence weight function or root count", space "$\mathbb{R}^{\{(t,v):t\in A,\ v\in V(t)\}}\cup\mathbb{Z}_{\ge0}$", def "Assign a real number $a(t,v)$ to each incidence $t\in A$, $v\in V(t)$; in the component-counting argument, $a$ is the number of roots in a component." (The entry describes only the incidence-weight function and omits the later scalar root count. The weights are arbitrary for cancellation and chosen with positive spoke-cycle sums for nonvanishing; the root count is a separate local use.)
- note on `symbol b`: symbol table corrected: type "black-face count function, locally reused as a scalar triangular-face count", space "$\bigl(\mathcal{P}(V(T))\longrightarrow\mathbb{Z}_{\ge0}\bigr)\cup\mathbb{Z}_{\ge0}$", def "$b(U)$ is the number of actual black faces of $T$ all of whose vertices belong to $U$; locally, $b$ counts the black triangular faces of $K$." (The recorded function is correct for $b(U)$ but does not cover the scalar $b$ used in the component calculation. For the component under consideration, its triangular faces are exactly actual faces of T lying in K.)
- note on `symbol B`: symbol table corrected: def "$B$ counts the original black faces of $T$ in the region under consideration." (The recorded definition restricts B to the directed-cycle disk. The later use counts original black faces on a side of the separating triangle and excludes the new cap.)
- note on `symbol C`: symbol table corrected: space "$\{\text{cycles of }D\}\cup\{\text{even cycles of }G\}$", def "$C$ denotes a cycle of $D$ in the nonvanishing argument, and an even cycle of $G$ in the definition of a Pfaffian orientation." (The recorded domain omits the later even cycles of $G$. The existing distinction remains valid, and its Pfaffian scope also applies to the newly listed lemma.)
- note on `symbol D`: symbol table corrected: def "$D$ consists of the edges joining $r(t)$ to $s(t)$ for $t\in A$. A pair directs these edges from $r(t)$ to $s(t)$; pairs are grouped by the underlying undirected edge set $D$." (The recorded definition retains the pair's direction throughout, whereas the nonvanishing argument uses the underlying undirected set as the group index.)
- note on `symbol e`: symbol table corrected: type "locally overloaded notation: induced-edge count function or prescribed graph edge", space "$\mathbb{Z}_{\ge0}^{\mathcal{P}(V(T))}\cup E(G)$", def "The notation $e(U)$ denotes the number of edges in $T[U]$; later, $e\in E(G)$ denotes a prescribed edge of $G$." (The recorded function type and domain cover the density argument but exclude the later graph-edge meaning. These two uses are explicitly distinguished by context.)
- note on `symbol P`: symbol table corrected: def "Root the white-face tree formed by the duals of the deleted spokes $(t,s(t))$, $t\in A$, at the white triangle $y_0$ across $e_0$ from $t_0$. Assign every tree edge to its endpoint farther from $y_0$. For each deleted spoke $(t,s(t))$, select the edge of $t$ incident with $s(t)$ bordering its assigned white triangle. Finally select $e_0$. Denote the selected set by $P$." (The recorded definition identifies the construction only vaguely; it omits the assignment and incidence rule that determines which primal edges belong to $P$. The later assertion that $P$ is a forest does not redefine it.)
- note on `symbol v`: symbol table corrected: space "$V(T)\text{ or }V(G)\text{, according to the ambient graph}$", def "$v$ denotes a vertex of the ambient graph; in an incidence $(t,v)$ it satisfies $v\in V(t)$." (The domain $V(T)$ is correct for the triangulation constructions but does not cover the later graph $G$, which need not be planar.)
- note on `symbol w`: symbol table corrected: type "locally reused face count or vertex", space "$\mathbb{Z}_{\ge0}$ for the face count; $V(T)$ for the vertex", def "Locally, $w$ counts the white triangular faces of $K$ in the density argument; in $\delta(v,w)$, it denotes a vertex adjacent to $v$." (The recorded count describes the density argument but fails to cover the later vertex use. The two meanings are explicitly separated by their local contexts.)
- note on `symbol W`: symbol table corrected: def "$W$ counts the original white faces of $T$ in the region under consideration." (The recorded definition only covers a cycle disk. The later use counts original faces on a side of the separating triangle and excludes the new cap.)

### V1 lint warnings

- thm:main: thm:main references \ref{thm:partition} (thm:partition) but `depends_on` lacks ass:partition-coloring; V1.5 must confirm whether the paper assumes it or merely mentions it
- thm:main: thm:main references \ref{lem:duality} (lem:duality) but `depends_on` lacks ass:duality-embedding; V1.5 must confirm whether the paper assumes it or merely mentions it
- prop:pairs: depends on ass:partition-coloring which the environment never references; V1.5 must confirm the paper actually assumes it
- lem:disk: depends on ass:partition-coloring which the environment never references; V1.5 must confirm the paper actually assumes it
- prop:forest-state: depends on ass:partition-coloring which the environment never references; V1.5 must confirm the paper actually assumes it
- lem:cancel: lem:cancel references \ref{lem:disk} (lem:disk) but `depends_on` lacks def:disk-edge-choice; V1.5 must confirm whether the paper assumes it or merely mentions it
- lem:cancel: depends on ass:partition-coloring which the environment never references; V1.5 must confirm the paper actually assumes it
- lem:circulation: depends on ass:partition-coloring which the environment never references; V1.5 must confirm the paper actually assumes it
- lem:root-components: depends on ass:partition-coloring which the environment never references; V1.5 must confirm the paper actually assumes it
- lem:p-forest: lem:P-forest references \ref{lem:disk} (lem:disk) but `depends_on` lacks def:disk-edge-choice; V1.5 must confirm whether the paper assumes it or merely mentions it
- lem:p-forest: depends on ass:partition-coloring which the environment never references; V1.5 must confirm the paper actually assumes it
- thm:edge-avoidance: cor:edge-avoidance references \ref{thm:partition} (thm:partition) but `depends_on` lacks ass:partition-coloring; V1.5 must confirm whether the paper assumes it or merely mentions it
- thm:pfaffian-paths: cor:pfaffian-paths references \ref{thm:main} (thm:main) but `depends_on` lacks ass:main-domain; V1.5 must confirm whether the paper assumes it or merely mentions it

### Parser warnings

- referee fix applied — ass:pfaffian-paths-graph: slice extended to "Pfaffian,"

## Lean evidence

- build of the run barrel: **ok**
- source scan (sorry / admit / axiom): clean

| declaration | axioms |
| --- | --- |
| `OaiPairedStatesHamiltonian.isHamiltonian_of_mainDomain` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `OaiPairedStatesHamiltonian.SphereMap.dual_compl_spanning` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `OaiPairedStatesHamiltonian.exists_tree_partition` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `OaiPairedStatesHamiltonian.exists_pair_of_noSeparatingTriangle` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `OaiPairedStatesHamiltonian.delta_sum_of_simple_cycle` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `OaiPairedStatesHamiltonian.exists_pair_qs_forest` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `OaiPairedStatesHamiltonian.sum_Z_terms_eq_zero_of_cyclic` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `OaiPairedStatesHamiltonian.exists_positive_spoke_weights` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `OaiPairedStatesHamiltonian.qs_component_contains_unique_root` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `OaiPairedStatesHamiltonian.selectedSet_isForest` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `OaiPairedStatesHamiltonian.exists_hamiltonian_avoiding_edge` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `OaiPairedStatesHamiltonian.p4Hamiltonian_of_pfaffian` | clean — `propext`, `Classical.choice`, `Quot.sound` |

## Inputs

| artifact | status |
| --- | --- |
| `discovery/v1_scope.json` | present (12 environment(s)) |
| `discovery/v1_5_review.json` | present (verdict PASS) |
| `formalization/crosswalk_full.json` | present (1004 object(s)) |
| `graph.json` | present (1010 node(s)) |
| Lean evidence | collected (build ok, 0 scan issue(s), 985 declaration(s)) |

## Annotated paper

Annotated paper: `annotated/paper.tex` (29 annotation(s), 0 unlocated; index `annotated/ANNOTATIONS.md`); PDF: `annotated/paper.pdf`

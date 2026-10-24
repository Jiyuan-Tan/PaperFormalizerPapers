# The corrected paper and its Lean formalization — oai_paired_states_hamiltonian

For each result of the corrected paper: its statement, the Lean declaration that states it, whether that declaration is proved, and how the two statements correspond phrase by phrase. A result stated differently from the original paper is marked "corrected"; the report says what changed and why.

## Theorem 1.1

**Statement.** \label{thm:main} Every finite simple undirected graph that is cubic, bipartite, planar, and \(3\)-vertex-connected has a Hamiltonian cycle.

**Lean.** `OaiPairedStatesHamiltonian.isHamiltonian_of_mainDomain` — `lean/Papers/OaiPairedStatesHamiltonian/TMain.lean:23`

**Status.** proved in Lean, under 5 condition(s) made explicit. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| Every finite simple undirected graph that is cubic, bipartite, planar, | `G : SimpleGraph V`<br>`hG : MainDomain G` |
| and \(3\)-vertex-connected has a Hamiltonian cycle. | `hG : MainDomain G`<br>then `G.IsHamiltonian` |

Lean also declares what the paper leaves implicit (the objects and their types): `V : Type`, `Fintype V`, `DecidableEq V`, `DecidableRel G.Adj`.

Lean assumes conditions that the paper's text does not state: `hpin : SingletonTreeEdgeless`.

**Conditions and readings, and the Lean definitions that carry them.**

- side condition: $M$ is finite. → `FiniteMap` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/SphereMaps.lean:332`)
- side condition: $\abs{V(T)}<\infty$. → `FiniteVertices` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/SphereMaps.lean:336`)
- reading: $Q_s$ contains a simple undirected cycle. → `QsHasSimpleCycle` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/StatesCore.lean:154`)
- reading: For a fixed pair $(r,s)$, $D$ has edges $r(t)s(t)$ oriented from $r(t)$ to $s(t)$ for $t\in A$; grouping pairs by $D$ identifies pairs exactly when their underlying undirected edge sets coincide. → `PairedEdgesReading` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/StatesCore.lean:209`)
- reading: The one-vertex graph declared to be a tree has no edges. → `SingletonTreeEdgeless` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Forests.lean:65`)
- definition of the paper: All embeddings are on the sphere. After choosing an outer face we work in the plane, with the point at infinity in that face. → `outerFaceChoice` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/SphereMaps.lean:309`)
- condition of the paper: Every finite simple undirected graph that is cubic, bipartite, planar, and \(3\)-vertex-connected → `MainDomain` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/GraphClasses.lean:44`)
- definition of the paper: A \emph{spanning forest} is an acyclic spanning subgraph, with isolated vertices allowed. → `IsSpanningForest` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Forests.lean:27`)
- definition of the paper: For a vertex set \(U\), the induced subgraph \(T[U]\) contains every edge of \(T\) with both endpoints in \(U\). → `induce` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/InducedMaps.lean:22`)
- definition of the paper: A one-vertex graph is a tree. → `singletonTree` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Forests.lean:68`)

## Lemma 2.1

**Statement.** \label{lem:duality} Let \(M\) be a connected graph embedded on the sphere. The duals of the edges complementary to a spanning tree of \(M\) form a spanning tree of \(M^*\). More generally, the duals of the edges complementary to a spanning forest of \(M\) form a connected spanning subgraph of \(M^*\).

**Lean.** `OaiPairedStatesHamiltonian.SphereMap.dual_compl_spanning` — `lean/Papers/OaiPairedStatesHamiltonian/Helpers/Duality.lean:42`

**Status.** proved in Lean, under 1 condition(s) made explicit. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| Let \(M\) be a connected graph embedded on the sphere. | `M : SphereMap`<br>`hM : M.IsConnectedMap` |
| The duals of the edges complementary to a spanning tree of \(M\) form a spanning tree of \(M^*\). | `∀ S : Set M.Edge`<br>`M.IsSpanningTree S`<br>then `(M.dual hM).IsSpanningTree Sᶜ` |
| More generally, the duals of the edges complementary to a spanning forest of \(M\) form a connected spanning subgraph of \(M^*\). | `∀ S : Set M.Edge`<br>`IsSpanningForest M S`<br>then `((M.dual hM).spanningGraph Sᶜ).Connected` |

Lean assumes conditions that the paper's text does not state: `hfin : M.FiniteMap`.

**Conditions and readings, and the Lean definitions that carry them.**

- side condition: $M$ is finite. → `FiniteMap` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/SphereMaps.lean:332`)
- definition of the paper: All embeddings are on the sphere. After choosing an outer face we work in the plane, with the point at infinity in that face. → `outerFaceChoice` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/SphereMaps.lean:309`)
- definition of the paper: Face lengths count edge-side incidences: a bridge contributes twice to the length of its incident face. → `faceLength` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/SphereMaps.lean:303`)
- condition of the paper: \label{lem:duality} Let \(M\) be a connected graph embedded on the sphere. → `IsConnectedMap` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/SphereMaps.lean:326`)
- definition of the paper: A \emph{spanning forest} is an acyclic spanning subgraph, with isolated vertices allowed. → `IsSpanningForest` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Forests.lean:27`)
- definition of the paper: The plane graphs used for intermediate dual constructions may have loops or parallel edges, with their usual edge-side incidences; the triangulations themselves are simple. → `IntermediatePlaneGraph` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/SphereMaps.lean:245`)

## Theorem 2.2

**Statement.** \label{thm:partition} Let \(T\) be a sphere triangulation whose faces are colored black and white so that each edge has one incident face of each color. For any facial triangle \(t_0\) and any edge \(e_0\) of \(t_0\), the vertex set admits a partition into two sets, each inducing a tree, such that the endpoints of \(e_0\) are in one set and the third vertex of \(t_0\) is in the other.

**Lean.** `OaiPairedStatesHamiltonian.exists_tree_partition` — `lean/Papers/OaiPairedStatesHamiltonian/TPartition.lean:29`

**Status.** proved in Lean, under 5 condition(s) made explicit. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| Let \(T\) be a sphere triangulation whose faces are colored black and white so that each edge has one incident face of each color. | `T : SphereMap`<br>`hT : IsSphereTriangulation T`<br>`col : T.Face → Bool`<br>`hcol : PartitionColoring T col` |
| For any facial triangle \(t_0\) and any edge \(e_0\) of \(t_0\), the vertex set admits a partition into two sets, each inducing a tree, such that the endpoints of \(e_0\) are in one set and the third vertex of \(t_0\) is in the other. | `t0 : T.Face`<br>`e0 : T.Edge`<br>`he0 : T.edgeOnFace e0 t0`<br>then `∃ U : Set T.Vertex,`<br>then `(T.toSimpleGraph.induce U).IsTree`<br>then `(T.toSimpleGraph.induce Uᶜ).IsTree`<br>`∀ v ∈ T.edgeEndpoints e0`<br>then `v ∈ U`<br>`∀ v ∈ T.faceVertices t0`<br>`v ∉ T.edgeEndpoints e0`<br>then `v ∉ U` |

Lean assumes conditions that the paper's text does not state: `hfin : T.FiniteVertices`, `hpin : SingletonTreeEdgeless`.

**Conditions and readings, and the Lean definitions that carry them.**

- side condition: $M$ is finite. → `FiniteMap` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/SphereMaps.lean:332`)
- side condition: $\abs{V(T)}<\infty$. → `FiniteVertices` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/SphereMaps.lean:336`)
- reading: $Q_s$ contains a simple undirected cycle. → `QsHasSimpleCycle` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/StatesCore.lean:154`)
- reading: For a fixed pair $(r,s)$, $D$ has edges $r(t)s(t)$ oriented from $r(t)$ to $s(t)$ for $t\in A$; grouping pairs by $D$ identifies pairs exactly when their underlying undirected edge sets coincide. → `PairedEdgesReading` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/StatesCore.lean:209`)
- reading: The one-vertex graph declared to be a tree has no edges. → `SingletonTreeEdgeless` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Forests.lean:65`)
- definition of the paper: All embeddings are on the sphere. After choosing an outer face we work in the plane, with the point at infinity in that face. → `outerFaceChoice` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/SphereMaps.lean:309`)
- definition of the paper: Put \(t_0\) on the outer face and exchange the face colors if necessary to make it black. Its three vertices are called the \emph{roots}. → `roots` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Triangulation.lean:83`)
- definition of the paper: Let \(k\) be the number of black faces. → `blackFaceCount` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Triangulation.lean:88`)
- definition of the paper: \begin{equation}\label{eq:counts} \#\{\text{white faces}\}=k,\qquad \abs{E(T)}=3k,\qquad \abs{V(T)}=k+2. \end{equation} → `StandingCounts` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Triangulation.lean:99`)
- definition of the paper: Write \(A\) for the black faces other than \(t_0\), and \(X\) for the nonroot vertices. → `blackNonOuter` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Triangulation.lean:202`)
- definition of the paper: A \emph{state} is a bijection \(r:A\longrightarrow X\) with \(r(t)\in V(t)\), where \(V(t)\) is the vertex set of the triangle \(t\). → `IsState` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/StatesCore.lean:64`)
- definition of the paper: A \emph{pair} is an ordered pair of states \((r,s)\) such that \(r(t)\ne s(t)\) for every \(t\in A\). → `IsPair` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/StatesCore.lean:90`)
- definition of the paper: Let \(H\) be the sphere graph of incidence spokes from \emph{all} black centers, including \(t_0\), to their vertices. → `spokeGraphAll` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/SpokeMaps.lean:70`)
- definition of the paper: Delete the spokes \((t,s(t))\), \(t\in A\). → `deletedSpokes` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Selection.lean:240`)
- definition of the paper: Root this white-face tree at the white triangle \(y_0\) across \(e_0\) from \(t_0\). Assign every tree edge to its endpoint farther from \(y_0\). These endpoints use each white triangle except \(y_0\) exactly once. A spoke \((t,v)\) borders the white triangles across the two sides of \(t\) incident with \(v\). Thus for the deleted spoke \((t,s(t))\), select the edge of \(t\) incident with \(s(t)\) bordering its assigned white triangle. Finally select \(e_0\). Denote the selected set by \(P\), and put \(P_0=P\setminus\{e_0\}\). → `selectedSet` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Selection.lean:611`)
- definition of the paper: Orient each edge of \(P_0\) out from \(s(t)\) in the black triangle that supplied it. → `orientedP0` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Selection.lean:630`)
- condition of the paper: whose faces are colored black and white so that each edge has one incident face of each color. → `PartitionColoring` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Triangulation.lean:48`)
- definition of the paper: Thus \(\abs{A}=\abs{X}=k-1\). → `StateSetsCard` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Triangulation.lean:216`)
- definition of the paper: A \emph{sphere triangulation} here is connected and simple, has at least four vertices, and has a \(3\)-cycle as the boundary of every face. → `IsSphereTriangulation` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Triangulation.lean:41`)
- definition of the paper: A \emph{separating triangle} is a \(3\)-cycle with vertices strictly on both sides. → `IsSeparatingTriangle` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Triangulation.lean:255`)
- definition of the paper: A \emph{spanning forest} is an acyclic spanning subgraph, with isolated vertices allowed. → `IsSpanningForest` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Forests.lean:27`)
- definition of the paper: For a vertex set \(U\), the induced subgraph \(T[U]\) contains every edge of \(T\) with both endpoints in \(U\). → `induce` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/InducedMaps.lean:22`)
- definition of the paper: A one-vertex graph is a tree. → `singletonTree` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Forests.lean:68`)
- definition of the paper: By Propositions~\ref{prop:pairs} and \ref{prop:forest-state}, choose a pair \((r,s)\) with \(Q_s\) a forest. → `forestPair` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/ForestState.lean:206`)
- definition of the paper: Orient its edges from \(r(t)\) to the third vertex. → `orientedQs` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/States.lean:57`)

## Proposition 3.1

**Statement.** \label{prop:pairs} If \(T\) has no separating triangle, then a pair of states exists.

**Lean.** `OaiPairedStatesHamiltonian.exists_pair_of_noSeparatingTriangle` — `lean/Papers/OaiPairedStatesHamiltonian/Helpers/Pairs.lean:106`

**Status.** proved in Lean, under 1 condition(s) made explicit. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| If \(T\) has no separating triangle, | `hsep : PairsNoSeparatingTriangle T` |
| then a pair of states exists. | then `∃ r s : State T col t0, IsPair T col t0 r s` |

Lean also declares what the paper leaves implicit (the objects and their types): `T : SphereMap`, `col : T.Face → Bool`, `t0 : T.Face`.

Lean assumes conditions that the paper's text does not state: `hT : IsSphereTriangulation T`, `hcol : PartitionColoring T col`, `hpin : SingletonTreeEdgeless`.

**Conditions and readings, and the Lean definitions that carry them.**

- reading: The one-vertex graph declared to be a tree has no edges. → `SingletonTreeEdgeless` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Forests.lean:65`)
- condition of the paper: whose faces are colored black and white so that each edge has one incident face of each color. → `PartitionColoring` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Triangulation.lean:48`)
- definition of the paper: Put \(t_0\) on the outer face and exchange the face colors if necessary to make it black. Its three vertices are called the \emph{roots}. → `roots` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Triangulation.lean:83`)
- definition of the paper: Write \(A\) for the black faces other than \(t_0\), and \(X\) for the nonroot vertices. → `blackNonOuter` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Triangulation.lean:202`)
- definition of the paper: Let \(k\) be the number of black faces. → `blackFaceCount` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Triangulation.lean:88`)
- definition of the paper: \begin{equation}\label{eq:counts} \#\{\text{white faces}\}=k,\qquad \abs{E(T)}=3k,\qquad \abs{V(T)}=k+2. \end{equation} → `StandingCounts` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Triangulation.lean:99`)
- definition of the paper: A \emph{state} is a bijection \(r:A\longrightarrow X\) with \(r(t)\in V(t)\), where \(V(t)\) is the vertex set of the triangle \(t\). → `IsState` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/StatesCore.lean:64`)
- definition of the paper: A \emph{pair} is an ordered pair of states \((r,s)\) such that \(r(t)\ne s(t)\) for every \(t\in A\). → `IsPair` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/StatesCore.lean:90`)
- definition of the paper: Face lengths count edge-side incidences: a bridge contributes twice to the length of its incident face. → `faceLength` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/SphereMaps.lean:303`)
- condition of the paper: If \(T\) has no separating triangle → `PairsNoSeparatingTriangle` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Triangulation.lean:260`)
- definition of the paper: Thus \(\abs{A}=\abs{X}=k-1\). → `StateSetsCard` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Triangulation.lean:216`)
- definition of the paper: A \emph{sphere triangulation} here is connected and simple, has at least four vertices, and has a \(3\)-cycle as the boundary of every face. → `IsSphereTriangulation` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Triangulation.lean:41`)
- definition of the paper: All embeddings are on the sphere. After choosing an outer face we work in the plane, with the point at infinity in that face. → `outerFaceChoice` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/SphereMaps.lean:309`)
- definition of the paper: A \emph{separating triangle} is a \(3\)-cycle with vertices strictly on both sides. → `IsSeparatingTriangle` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Triangulation.lean:255`)
- definition of the paper: For a vertex set \(U\), the induced subgraph \(T[U]\) contains every edge of \(T\) with both endpoints in \(U\). → `induce` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/InducedMaps.lean:22`)
- definition of the paper: A one-vertex graph is a tree. → `singletonTree` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Forests.lean:68`)

## Lemma 4.1

**Statement.** \label{lem:disk} Let \(r\) be a state. In each \(t\in A\), choose one edge directed from \(r(t)\) to another vertex of \(t\). Every simple directed cycle in the chosen edges avoids the roots. Its \(\delta\)-sum is \(-3\) if it is counterclockwise, and \(3\) if it is clockwise.

**Lean.** `OaiPairedStatesHamiltonian.delta_sum_of_simple_cycle` — `lean/Papers/OaiPairedStatesHamiltonian/Helpers/Disk.lean:123`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| Let \(r\) be a state. | `r : State T col t0` |
| In each \(t\in A\), choose one edge directed from \(r(t)\) to another vertex of \(t\). | `choice : EdgeChoice T col t0 r` |
| Every simple directed cycle in the chosen edges avoids the roots. | `C : T.Cycle`<br>`hC : ∀ d ∈ C.val, d ∈ ChosenEdges T col t0 hT r choice`<br>`∀ d ∈ C.val`<br>then `T.vert d ∉ roots T t0` |
| Its \(\delta\)-sum is \(-3\) if it is counterclockwise, | `T.IsCounterclockwise t0 C`<br>then `(C.val.map (delta T (normalizedColoring T col t0))).sum = -3` |
| and \(3\) if it is clockwise. | `T.IsClockwise t0 C`<br>then `(C.val.map (delta T (normalizedColoring T col t0))).sum = 3` |

Lean also declares what the paper leaves implicit (the objects and their types): `T : SphereMap`, `col : T.Face → Bool`, `t0 : T.Face`.

Lean assumes conditions that the paper's text does not state: `hT : IsSphereTriangulation T`, `hcol : PartitionColoring T col`.

**Conditions and readings, and the Lean definitions that carry them.**

- condition of the paper: whose faces are colored black and white so that each edge has one incident face of each color. → `PartitionColoring` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Triangulation.lean:48`)
- definition of the paper: Put \(t_0\) on the outer face and exchange the face colors if necessary to make it black. Its three vertices are called the \emph{roots}. → `roots` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Triangulation.lean:83`)
- definition of the paper: Write \(A\) for the black faces other than \(t_0\), and \(X\) for the nonroot vertices. → `blackNonOuter` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Triangulation.lean:202`)
- definition of the paper: A \emph{state} is a bijection \(r:A\longrightarrow X\) with \(r(t)\in V(t)\), where \(V(t)\) is the vertex set of the triangle \(t\). → `IsState` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/StatesCore.lean:64`)
- definition of the paper: For adjacent vertices \(v,w\), define \(\delta(v,w)=1\) if the black face of their edge is on the left when the edge is traversed from \(v\) to \(w\), and \(\delta(v,w)=-1\) otherwise. → `delta` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/StatesCore.lean:110`)
- definition of the paper: In each \(t\in A\), choose one edge directed from \(r(t)\) to another vertex of \(t\). → `ChosenEdges` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/StatesCore.lean:125`)
- definition of the paper: A \emph{sphere triangulation} here is connected and simple, has at least four vertices, and has a \(3\)-cycle as the boundary of every face. → `IsSphereTriangulation` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Triangulation.lean:41`)
- definition of the paper: All embeddings are on the sphere. After choosing an outer face we work in the plane, with the point at infinity in that face. → `outerFaceChoice` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/SphereMaps.lean:309`)

## Proposition 5.1

**Statement.** \label{prop:forest-state} Whenever at least one pair exists, some pair \((r,s)\) has \(Q_s\) a forest.

**Lean.** `OaiPairedStatesHamiltonian.exists_pair_qs_forest` — `lean/Papers/OaiPairedStatesHamiltonian/Helpers/ForestState.lean:173`

**Status.** proved in Lean, under 2 condition(s) made explicit. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| Whenever at least one pair exists, some pair \((r,s)\) has \(Q_s\) a forest. | `hpairs : PairExists T col t0`<br>then `∃ r s : State T col t0,`<br>then `IsPair T col t0 r s`<br>then `QsForest T col t0 s` |

Lean also declares what the paper leaves implicit (the objects and their types): `T : SphereMap`, `col : T.Face → Bool`, `t0 : T.Face`.

Lean assumes conditions that the paper's text does not state: `hT : IsSphereTriangulation T`, `hcol : PartitionColoring T col`, `hpin : PairedEdgesReading T col t0 hT`.

**Conditions and readings, and the Lean definitions that carry them.**

- reading: $Q_s$ contains a simple undirected cycle. → `QsHasSimpleCycle` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/StatesCore.lean:154`)
- reading: For a fixed pair $(r,s)$, $D$ has edges $r(t)s(t)$ oriented from $r(t)$ to $s(t)$ for $t\in A$; grouping pairs by $D$ identifies pairs exactly when their underlying undirected edge sets coincide. → `PairedEdgesReading` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/StatesCore.lean:209`)
- condition of the paper: whose faces are colored black and white so that each edge has one incident face of each color. → `PartitionColoring` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Triangulation.lean:48`)
- definition of the paper: Put \(t_0\) on the outer face and exchange the face colors if necessary to make it black. Its three vertices are called the \emph{roots}. → `roots` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Triangulation.lean:83`)
- definition of the paper: A \emph{state} is a bijection \(r:A\longrightarrow X\) with \(r(t)\in V(t)\), where \(V(t)\) is the vertex set of the triangle \(t\). → `IsState` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/StatesCore.lean:64`)
- definition of the paper: A \emph{pair} is an ordered pair of states \((r,s)\) such that \(r(t)\ne s(t)\) for every \(t\in A\). → `IsPair` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/StatesCore.lean:90`)
- definition of the paper: For a state \(s\), let \(Q_s\) be the spanning subgraph of \(T\) consisting of the edge opposite \(s(t)\) in every \(t\in A\). → `Qs` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/StatesCore.lean:135`)
- definition of the paper: For now, assign a real number \(a(t,v)\) to each incidence \(t\in A\), \(v\in V(t)\) → `IncidenceWeights` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/StatesCore.lean:161`)
- definition of the paper: \[ \omega(s)=\sum_{t\in A}a(t,s(t)). \] → `omega` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/StatesCore.lean:167`)
- definition of the paper: For a pair, direct the edge in \(t\) from \(r(t)\) to \(s(t)\). Every vertex of \(X\) has one edge in and one out, so these edges form a union \(D\) of vertex-disjoint cycles on \(X\). → `pairedEdges` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/StatesCore.lean:184`)
- definition of the paper: \begin{equation}\label{eq:J} J(r,s)=\frac13\sum_{t\in A}\delta(r(t),s(t)) \quad\hbox{is an integer}. \end{equation} → `J` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/PairPhases.lean:39`)
- definition of the paper: For real \(x\), define the finite exponential sum \begin{equation}\label{eq:Z} Z(x)=\sum_{(r,s)\ {\rm pair}} \ii^{J(r,s)}\exp\bigl(x\omega(s)\bigr). \end{equation} → `Z` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/PairPhases.lean:111`)
- definition of the paper: Inside each bounded black triangle place a center and join it to the three vertices by disjoint incidence spokes. Let \(H_0\) be the resulting plane graph, allowing isolated vertices. → `spokeGraphBounded` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/SpokeMaps.lean:62`)
- definition of the paper: For a cycle \(C\) of \(D\), let \(L_+(C)\) be the sum of \(a(t,\mathrm{head})\) along its counterclockwise orientation, and \(L_-(C)\) the corresponding clockwise sum. → `cycleWeights` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/PairPhases.lean:232`)
- condition of the paper: Whenever at least one pair exists → `PairExists` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/StatesCore.lean:104`)
- definition of the paper: Thus \(\abs{A}=\abs{X}=k-1\). → `StateSetsCard` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Triangulation.lean:216`)
- definition of the paper: A \emph{sphere triangulation} here is connected and simple, has at least four vertices, and has a \(3\)-cycle as the boundary of every face. → `IsSphereTriangulation` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Triangulation.lean:41`)
- definition of the paper: All embeddings are on the sphere. After choosing an outer face we work in the plane, with the point at infinity in that face. → `outerFaceChoice` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/SphereMaps.lean:309`)

## Lemma 5.2

**Statement.** \label{lem:cancel} For fixed \(s\) with cyclic \(Q_s\), the terms of \eqref{eq:Z} having second state \(s\) sum to zero.

**Lean.** `OaiPairedStatesHamiltonian.sum_Z_terms_eq_zero_of_cyclic` — `lean/Papers/OaiPairedStatesHamiltonian/Helpers/Cancel.lean:78`

**Status.** proved in Lean, under 1 condition(s) made explicit. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| For fixed \(s\) with cyclic \(Q_s\), the terms of \eqref{eq:Z} having second state \(s\) sum to zero. | `s : State T col t0`<br>`hcyclic : QsCyclic T col t0 s`<br>`hpin : QsHasSimpleCycle T col t0 s`<br>then `(∑ r : {r : State T col t0 // IsPair T col t0 r s}, Complex.I ^ J T col t0 hT r.val s r.property * Complex.exp ((x * omega T col t0 a s : ℝ) : ℂ)) = 0` |

Lean also declares what the paper leaves implicit (the objects and their types): `T : SphereMap`, `col : T.Face → Bool`, `t0 : T.Face`, `a : IncidenceWeights T col t0`, `x : ℝ`.

Lean assumes conditions that the paper's text does not state: `hT : IsSphereTriangulation T`, `hcol : PartitionColoring T col`.

**Conditions and readings, and the Lean definitions that carry them.**

- reading: $Q_s$ contains a simple undirected cycle. → `QsHasSimpleCycle` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/StatesCore.lean:154`)
- condition of the paper: whose faces are colored black and white so that each edge has one incident face of each color. → `PartitionColoring` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Triangulation.lean:48`)
- definition of the paper: Put \(t_0\) on the outer face and exchange the face colors if necessary to make it black. Its three vertices are called the \emph{roots}. → `roots` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Triangulation.lean:83`)
- definition of the paper: A \emph{state} is a bijection \(r:A\longrightarrow X\) with \(r(t)\in V(t)\), where \(V(t)\) is the vertex set of the triangle \(t\). → `IsState` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/StatesCore.lean:64`)
- definition of the paper: A \emph{pair} is an ordered pair of states \((r,s)\) such that \(r(t)\ne s(t)\) for every \(t\in A\). → `IsPair` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/StatesCore.lean:90`)
- definition of the paper: For a state \(s\), let \(Q_s\) be the spanning subgraph of \(T\) consisting of the edge opposite \(s(t)\) in every \(t\in A\). → `Qs` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/StatesCore.lean:135`)
- definition of the paper: For adjacent vertices \(v,w\), define \(\delta(v,w)=1\) if the black face of their edge is on the left when the edge is traversed from \(v\) to \(w\), and \(\delta(v,w)=-1\) otherwise. → `delta` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/StatesCore.lean:110`)
- definition of the paper: For now, assign a real number \(a(t,v)\) to each incidence \(t\in A\), \(v\in V(t)\) → `IncidenceWeights` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/StatesCore.lean:161`)
- definition of the paper: \[ \omega(s)=\sum_{t\in A}a(t,s(t)). \] → `omega` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/StatesCore.lean:167`)
- definition of the paper: \begin{equation}\label{eq:J} J(r,s)=\frac13\sum_{t\in A}\delta(r(t),s(t)) \quad\hbox{is an integer}. \end{equation} → `J` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/PairPhases.lean:39`)
- definition of the paper: For real \(x\), define the finite exponential sum \begin{equation}\label{eq:Z} Z(x)=\sum_{(r,s)\ {\rm pair}} \ii^{J(r,s)}\exp\bigl(x\omega(s)\bigr). \end{equation} → `Z` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/PairPhases.lean:111`)
- condition of the paper: For fixed \(s\) with cyclic \(Q_s\) → `QsCyclic` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/StatesCore.lean:144`)
- definition of the paper: A \emph{sphere triangulation} here is connected and simple, has at least four vertices, and has a \(3\)-cycle as the boundary of every face. → `IsSphereTriangulation` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Triangulation.lean:41`)
- definition of the paper: All embeddings are on the sphere. After choosing an outer face we work in the plane, with the point at infinity in that face. → `outerFaceChoice` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/SphereMaps.lean:309`)

## Lemma 5.3

**Statement.** \label{lem:circulation} There are real numbers \(a(t,v)\) on the spokes of \(H_0\) such that every counterclockwise simple spoke cycle has strictly positive weight, where center-to-vertex traversal has weight \(a(t,v)\) and reverse traversal its negative.

**Lean.** `OaiPairedStatesHamiltonian.exists_positive_spoke_weights` — `lean/Papers/OaiPairedStatesHamiltonian/Helpers/Circulation.lean:391`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| There are real numbers \(a(t,v)\) on the spokes of \(H_0\) such that every counterclockwise simple spoke cycle has strictly positive weight, | then `∃ a : IncidenceWeights T col t0,`<br>`∀ C : (spokeGraphBounded T col t0 hT hcol).Cycle`<br>`(spokeGraphBounded T col t0 hT hcol).IsCounterclockwise (spokeOuter T col t0 hT hcol) C`<br>then `0 < signedSpokeWeight T col t0 hT hcol a C` |
| where center-to-vertex traversal has weight \(a(t,v)\) and reverse traversal its negative. | then `0 < signedSpokeWeight T col t0 hT hcol a C` |

Lean also declares what the paper leaves implicit (the objects and their types): `T : SphereMap`, `col : T.Face → Bool`, `t0 : T.Face`.

Lean assumes conditions that the paper's text does not state: `hT : IsSphereTriangulation T`, `hcol : PartitionColoring T col`.

**Conditions and readings, and the Lean definitions that carry them.**

- condition of the paper: whose faces are colored black and white so that each edge has one incident face of each color. → `PartitionColoring` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Triangulation.lean:48`)
- definition of the paper: All embeddings are on the sphere. After choosing an outer face we work in the plane, with the point at infinity in that face. → `outerFaceChoice` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/SphereMaps.lean:309`)
- definition of the paper: Face lengths count edge-side incidences: a bridge contributes twice to the length of its incident face. → `faceLength` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/SphereMaps.lean:303`)
- definition of the paper: Put \(t_0\) on the outer face and exchange the face colors if necessary to make it black. Its three vertices are called the \emph{roots}. → `roots` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Triangulation.lean:83`)
- definition of the paper: Inside each bounded black triangle place a center and join it to the three vertices by disjoint incidence spokes. Let \(H_0\) be the resulting plane graph, allowing isolated vertices. → `spokeGraphBounded` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/SpokeMaps.lean:62`)
- definition of the paper: For now, assign a real number \(a(t,v)\) to each incidence \(t\in A\), \(v\in V(t)\) → `IncidenceWeights` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/StatesCore.lean:161`)
- definition of the paper: A \emph{sphere triangulation} here is connected and simple, has at least four vertices, and has a \(3\)-cycle as the boundary of every face. → `IsSphereTriangulation` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Triangulation.lean:41`)
- definition of the paper: The plane graphs used for intermediate dual constructions may have loops or parallel edges, with their usual edge-side incidences; the triangulations themselves are simple. → `IntermediatePlaneGraph` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/SphereMaps.lean:245`)

## Lemma 6.1

**Statement.** \label{lem:root-components} For a pair \((r,s)\) with \(Q_s\) a forest, every component of \(Q_s\) contains exactly one of the three roots.

**Lean.** `OaiPairedStatesHamiltonian.qs_component_contains_unique_root` — `lean/Papers/OaiPairedStatesHamiltonian/Helpers/RootComponents.lean:44`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| For a pair \((r,s)\) with \(Q_s\) a forest, every component of \(Q_s\) contains exactly one of the three roots. | `r s : State T col t0`<br>`hpair : IsPair T col t0 r s`<br>`hforest : QsForest T col t0 s`<br>`∀ c : (Qs T col t0 s).ConnectedComponent`<br>then `∃! v : T.Vertex,`<br>then `v ∈ roots T t0`<br>then `(Qs T col t0 s).connectedComponentMk v = c` |

Lean also declares what the paper leaves implicit (the objects and their types): `T : SphereMap`, `col : T.Face → Bool`, `t0 : T.Face`.

Lean assumes conditions that the paper's text does not state: `hT : IsSphereTriangulation T`, `hcol : PartitionColoring T col`, `hsep : TreesNoSeparatingTriangle T`.

**Conditions and readings, and the Lean definitions that carry them.**

- condition of the paper: whose faces are colored black and white so that each edge has one incident face of each color. → `PartitionColoring` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Triangulation.lean:48`)
- definition of the paper: Put \(t_0\) on the outer face and exchange the face colors if necessary to make it black. Its three vertices are called the \emph{roots}. → `roots` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Triangulation.lean:83`)
- definition of the paper: Write \(A\) for the black faces other than \(t_0\), and \(X\) for the nonroot vertices. → `blackNonOuter` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Triangulation.lean:202`)
- definition of the paper: A \emph{state} is a bijection \(r:A\longrightarrow X\) with \(r(t)\in V(t)\), where \(V(t)\) is the vertex set of the triangle \(t\). → `IsState` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/StatesCore.lean:64`)
- definition of the paper: A \emph{pair} is an ordered pair of states \((r,s)\) such that \(r(t)\ne s(t)\) for every \(t\in A\). → `IsPair` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/StatesCore.lean:90`)
- definition of the paper: For a state \(s\), let \(Q_s\) be the spanning subgraph of \(T\) consisting of the edge opposite \(s(t)\) in every \(t\in A\). → `Qs` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/StatesCore.lean:135`)
- condition of the paper: with \(Q_s\) a forest → `QsForest` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/StatesCore.lean:149`)
- definition of the paper: A \emph{sphere triangulation} here is connected and simple, has at least four vertices, and has a \(3\)-cycle as the boundary of every face. → `IsSphereTriangulation` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Triangulation.lean:41`)
- definition of the paper: All embeddings are on the sphere. After choosing an outer face we work in the plane, with the point at infinity in that face. → `outerFaceChoice` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/SphereMaps.lean:309`)
- definition of the paper: A \emph{spanning forest} is an acyclic spanning subgraph, with isolated vertices allowed. → `IsSpanningForest` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Forests.lean:27`)
- definition of the paper: Orient its edges from \(r(t)\) to the third vertex. → `orientedQs` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/States.lean:57`)
- condition of the paper: Assume that \(T\) has no separating triangle. → `TreesNoSeparatingTriangle` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Triangulation.lean:264`)

## Lemma 6.2

**Statement.** \label{lem:P-forest} The selected set \(P\) is a forest.

**Lean.** `OaiPairedStatesHamiltonian.selectedSet_isForest` — `lean/Papers/OaiPairedStatesHamiltonian/Helpers/PForest.lean:23`

**Status.** proved in Lean, under 4 condition(s) made explicit. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| The selected set \(P\) is a forest. | then `IsSpanningForest T {e | e ∈ selectedSet T hT col hcol t0 (forestPair T hT col hcol hsep t0).2 e0 he0}` |

Lean also declares what the paper leaves implicit (the objects and their types): `T : SphereMap`, `col : T.Face → Bool`, `t0 : T.Face`, `e0 : T.Edge`.

Lean assumes conditions that the paper's text does not state: `hT : IsSphereTriangulation T`, `hcol : PartitionColoring T col`, `hsep : TreesNoSeparatingTriangle T`, `he0 : T.edgeOnFace e0 t0`.

**Conditions and readings, and the Lean definitions that carry them.**

- side condition: $M$ is finite. → `FiniteMap` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/SphereMaps.lean:332`)
- reading: $Q_s$ contains a simple undirected cycle. → `QsHasSimpleCycle` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/StatesCore.lean:154`)
- reading: For a fixed pair $(r,s)$, $D$ has edges $r(t)s(t)$ oriented from $r(t)$ to $s(t)$ for $t\in A$; grouping pairs by $D$ identifies pairs exactly when their underlying undirected edge sets coincide. → `PairedEdgesReading` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/StatesCore.lean:209`)
- reading: The one-vertex graph declared to be a tree has no edges. → `SingletonTreeEdgeless` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Forests.lean:65`)
- condition of the paper: whose faces are colored black and white so that each edge has one incident face of each color. → `PartitionColoring` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Triangulation.lean:48`)
- condition of the paper: Assume that \(T\) has no separating triangle. → `TreesNoSeparatingTriangle` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Triangulation.lean:264`)
- definition of the paper: Put \(t_0\) on the outer face and exchange the face colors if necessary to make it black. Its three vertices are called the \emph{roots}. → `roots` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Triangulation.lean:83`)
- definition of the paper: A \emph{state} is a bijection \(r:A\longrightarrow X\) with \(r(t)\in V(t)\), where \(V(t)\) is the vertex set of the triangle \(t\). → `IsState` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/StatesCore.lean:64`)
- definition of the paper: A \emph{pair} is an ordered pair of states \((r,s)\) such that \(r(t)\ne s(t)\) for every \(t\in A\). → `IsPair` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/StatesCore.lean:90`)
- definition of the paper: For a state \(s\), let \(Q_s\) be the spanning subgraph of \(T\) consisting of the edge opposite \(s(t)\) in every \(t\in A\). → `Qs` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/StatesCore.lean:135`)
- definition of the paper: Let \(H\) be the sphere graph of incidence spokes from \emph{all} black centers, including \(t_0\), to their vertices. → `spokeGraphAll` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/SpokeMaps.lean:70`)
- definition of the paper: Delete the spokes \((t,s(t))\), \(t\in A\). → `deletedSpokes` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Selection.lean:240`)
- definition of the paper: Root this white-face tree at the white triangle \(y_0\) across \(e_0\) from \(t_0\). Assign every tree edge to its endpoint farther from \(y_0\). These endpoints use each white triangle except \(y_0\) exactly once. A spoke \((t,v)\) borders the white triangles across the two sides of \(t\) incident with \(v\). Thus for the deleted spoke \((t,s(t))\), select the edge of \(t\) incident with \(s(t)\) bordering its assigned white triangle. Finally select \(e_0\). Denote the selected set by \(P\), and put \(P_0=P\setminus\{e_0\}\). → `selectedSet` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Selection.lean:611`)
- definition of the paper: Orient each edge of \(P_0\) out from \(s(t)\) in the black triangle that supplied it. → `orientedP0` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Selection.lean:630`)
- definition of the paper: For adjacent vertices \(v,w\), define \(\delta(v,w)=1\) if the black face of their edge is on the left when the edge is traversed from \(v\) to \(w\), and \(\delta(v,w)=-1\) otherwise. → `delta` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/StatesCore.lean:110`)
- definition of the paper: A \emph{sphere triangulation} here is connected and simple, has at least four vertices, and has a \(3\)-cycle as the boundary of every face. → `IsSphereTriangulation` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Triangulation.lean:41`)
- definition of the paper: All embeddings are on the sphere. After choosing an outer face we work in the plane, with the point at infinity in that face. → `outerFaceChoice` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/SphereMaps.lean:309`)
- definition of the paper: A \emph{separating triangle} is a \(3\)-cycle with vertices strictly on both sides. → `IsSeparatingTriangle` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Triangulation.lean:255`)
- definition of the paper: A \emph{spanning forest} is an acyclic spanning subgraph, with isolated vertices allowed. → `IsSpanningForest` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Forests.lean:27`)
- definition of the paper: Write \(A\) for the black faces other than \(t_0\), and \(X\) for the nonroot vertices. → `blackNonOuter` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Triangulation.lean:202`)
- definition of the paper: Let \(k\) be the number of black faces. → `blackFaceCount` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Triangulation.lean:88`)
- definition of the paper: \begin{equation}\label{eq:counts} \#\{\text{white faces}\}=k,\qquad \abs{E(T)}=3k,\qquad \abs{V(T)}=k+2. \end{equation} → `StandingCounts` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Triangulation.lean:99`)
- definition of the paper: By Propositions~\ref{prop:pairs} and \ref{prop:forest-state}, choose a pair \((r,s)\) with \(Q_s\) a forest. → `forestPair` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/ForestState.lean:206`)
- definition of the paper: Orient its edges from \(r(t)\) to the third vertex. → `orientedQs` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/States.lean:57`)

## Corollary 7.1

**Statement.** \label{cor:edge-avoidance} For every graph \(G\) satisfying Theorem~\ref{thm:main} and every edge \(e\in E(G)\), there is a Hamiltonian cycle of \(G\) avoiding \(e\).

**Lean.** `OaiPairedStatesHamiltonian.exists_hamiltonian_avoiding_edge` — `lean/Papers/OaiPairedStatesHamiltonian/TEdgeAvoidance.lean:24`

**Status.** proved in Lean, under 6 condition(s) made explicit. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| For every graph \(G\) satisfying Theorem~\ref{thm:main} and every edge \(e\in E(G)\), there is a Hamiltonian cycle of \(G\) avoiding \(e\). | `G : SimpleGraph V`<br>`e : Sym2 V`<br>`hG : EdgeAvoidanceDomain G e`<br>`hmain : MainDomain G`<br>`hpin : EdgeAvoidancePinned G e`<br>then `∃ a, ∃ C : G.Walk a a,`<br>then `C.IsHamiltonianCycle`<br>then `e ∉ C.edges` |

Lean also declares what the paper leaves implicit (the objects and their types): `V : Type`, `Fintype V`, `DecidableEq V`, `DecidableRel G.Adj`.

**Conditions and readings, and the Lean definitions that carry them.**

- side condition: $M$ is finite. → `FiniteMap` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/SphereMaps.lean:332`)
- side condition: $\abs{V(T)}<\infty$. → `FiniteVertices` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/SphereMaps.lean:336`)
- reading: $Q_s$ contains a simple undirected cycle. → `QsHasSimpleCycle` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/StatesCore.lean:154`)
- reading: $G$ is a finite simple undirected cubic bipartite planar $3$-vertex-connected graph, and $e\in E(G)$. → `EdgeAvoidancePinned` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/GraphClasses.lean:59`)
- reading: For a fixed pair $(r,s)$, $D$ has edges $r(t)s(t)$ oriented from $r(t)$ to $s(t)$ for $t\in A$; grouping pairs by $D$ identifies pairs exactly when their underlying undirected edge sets coincide. → `PairedEdgesReading` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/StatesCore.lean:209`)
- reading: The one-vertex graph declared to be a tree has no edges. → `SingletonTreeEdgeless` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Forests.lean:65`)
- condition of the paper: For every graph \(G\) satisfying Theorem~\ref{thm:main} and every edge \(e\in E(G)\) → `EdgeAvoidanceDomain` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/GraphClasses.lean:53`)
- condition of the paper: Every finite simple undirected graph that is cubic, bipartite, planar, and \(3\)-vertex-connected → `MainDomain` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/GraphClasses.lean:44`)

## Corollary 7.2

**Statement.** \label{cor:pfaffian-paths} Let \(G\) be a finite simple undirected graph that is cubic, \(3\)-vertex-connected, Pfaffian, and bipartite. Every path on four vertices (three edges) in \(G\) is contained in a Hamiltonian cycle. In other words, \(G\) is \(P_4\)-Hamiltonian; in particular, it is Hamiltonian.

**Lean.** `OaiPairedStatesHamiltonian.p4Hamiltonian_of_pfaffian` — `lean/Papers/OaiPairedStatesHamiltonian/TPfaffianPaths.lean:53`

**Status.** proved in Lean, given 2 cited result(s), under 5 condition(s) made explicit. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| Let \(G\) be a finite simple undirected graph that is cubic, \(3\)-vertex-connected, Pfaffian, | `G : SimpleGraph (Fin n)`<br>`hG : PfaffianPathsGraph G` |
| and bipartite. | `hbip : PfaffianPathsBipartite G` |
| Every path on four vertices (three edges) in \(G\) is contained in a Hamiltonian cycle. | then `IsP4Hamiltonian G` |
| In other words, \(G\) is \(P_4\)-Hamiltonian; | then `IsP4Hamiltonian G` |
| in particular, it is Hamiltonian. | then `G.IsHamiltonian` |

Lean also declares what the paper leaves implicit (the objects and their types): `n : ℕ`, `DecidableRel G.Adj`.

Lean assumes conditions that the paper's text does not state: `hGSW416_of_gate : GSW2023Thm416`, `hGSW46_of_gate : GSW2023Thm46`.

**Conditions and readings, and the Lean definitions that carry them.**

- side condition: $M$ is finite. → `FiniteMap` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/SphereMaps.lean:332`)
- side condition: $\abs{V(T)}<\infty$. → `FiniteVertices` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/SphereMaps.lean:336`)
- reading: $Q_s$ contains a simple undirected cycle. → `QsHasSimpleCycle` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/StatesCore.lean:154`)
- reading: For a fixed pair $(r,s)$, $D$ has edges $r(t)s(t)$ oriented from $r(t)$ to $s(t)$ for $t\in A$; grouping pairs by $D$ identifies pairs exactly when their underlying undirected edge sets coincide. → `PairedEdgesReading` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/StatesCore.lean:209`)
- reading: The one-vertex graph declared to be a tree has no edges. → `SingletonTreeEdgeless` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/Forests.lean:65`)
- definition of the paper: Recall that a graph \(G\) is \emph{Pfaffian} if its edges admit an orientation for which every even cycle \(C\) such that \(G-V(C)\) has a perfect matching has an odd number of edges directed along either cyclic traversal \cite[Section~4]{GSW2023}. → `IsPfaffian` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/GraphClasses.lean:80`)
- condition of the paper: Let \(G\) be a finite simple undirected graph that is cubic, \(3\)-vertex-connected, Pfaffian, → `PfaffianPathsGraph` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/GraphClasses.lean:86`)
- condition of the paper: and bipartite. → `PfaffianPathsBipartite` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/GraphClasses.lean:93`)

**Taken from the literature: GSW2023, Theorem 4.16.**

What Lean assumes for it: `OaiPairedStatesHamiltonian.GSW2023Thm416` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/CitedGates.lean:28`)

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

**Taken from the literature: GSW2023, Theorem 4.6.**

What Lean assumes for it: `OaiPairedStatesHamiltonian.GSW2023Thm46` (`lean/Papers/OaiPairedStatesHamiltonian/Helpers/CitedGates.lean:42`)

```lean
noncomputable def GSW2023Thm46 : Sort 0 :=
  ∀ n (G : SimpleGraph (Fin n)), IsPlanar G → IsPfaffian G
```

The passage of the proof:

> Every planar graph is Pfaffian
> \cite[Theorem~4.6]{GSW2023}, so the corollary includes the graphs of
> Theorem~\ref{thm:main}, while also allowing nonplanar graphs.

## Identifiers

| Result | run id | paper label | source | Lean declaration |
| --- | --- | --- | --- | --- |
| Theorem 1.1 | `thm:main` | `thm:main` | `paper.tex:79-82` | `OaiPairedStatesHamiltonian.isHamiltonian_of_mainDomain` |
| Lemma 2.1 | `lem:duality` | `lem:duality` | `paper.tex:189-195` | `OaiPairedStatesHamiltonian.SphereMap.dual_compl_spanning` |
| Theorem 2.2 | `thm:partition` | `thm:partition` | `paper.tex:208-215` | `OaiPairedStatesHamiltonian.exists_tree_partition` |
| Proposition 3.1 | `prop:pairs` | `prop:pairs` | `paper.tex:245-247` | `OaiPairedStatesHamiltonian.exists_pair_of_noSeparatingTriangle` |
| Lemma 4.1 | `lem:disk` | `lem:disk` | `paper.tex:362-368` | `OaiPairedStatesHamiltonian.delta_sum_of_simple_cycle` |
| Proposition 5.1 | `prop:forest-state` | `prop:forest-state` | `paper.tex:413-416` | `OaiPairedStatesHamiltonian.exists_pair_qs_forest` |
| Lemma 5.2 | `lem:cancel` | `lem:cancel` | `paper.tex:446-449` | `OaiPairedStatesHamiltonian.sum_Z_terms_eq_zero_of_cyclic` |
| Lemma 5.3 | `lem:circulation` | `lem:circulation` | `paper.tex:497-502` | `OaiPairedStatesHamiltonian.exists_positive_spoke_weights` |
| Lemma 6.1 | `lem:root-components` | `lem:root-components` | `paper.tex:603-606` | `OaiPairedStatesHamiltonian.qs_component_contains_unique_root` |
| Lemma 6.2 | `lem:p-forest` | `lem:P-forest` | `paper.tex:663-665` | `OaiPairedStatesHamiltonian.selectedSet_isForest` |
| Corollary 7.1 | `thm:edge-avoidance` | `cor:edge-avoidance` | `paper.tex:794-797` | `OaiPairedStatesHamiltonian.exists_hamiltonian_avoiding_edge` |
| Corollary 7.2 | `thm:pfaffian-paths` | `cor:pfaffian-paths` | `paper.tex:812-818` | `OaiPairedStatesHamiltonian.p4Hamiltonian_of_pfaffian` |

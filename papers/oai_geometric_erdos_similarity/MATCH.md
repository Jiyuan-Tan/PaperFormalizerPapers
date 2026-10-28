# The corrected paper and its Lean formalization — oai_geometric_erdos_similarity

For each result of the corrected paper: its statement, the Lean declaration that states it, whether that declaration is proved, and how the two statements correspond phrase by phrase. A result stated differently from the original paper is marked "corrected"; the report says what changed and why.

## Theorem 1.1

**Statement.** \label{thm:main} For every $q\in(0,1)$ and $\eta\in(0,1)$, there is a compact set $E_{q,\eta}\subseteq[0,1]$ with $m(E_{q,\eta})>1-\eta$ such that \[ \text{for every }x\in\R\text{ and }s\in\R\setminus\{0\}, \quad x+sq^n\notin E_{q,\eta}\text{ for some integer }n\ge1. \]

**Lean.** `Papers.OaiGeometricErdosSimilarity.exists_compact_avoiding_geometric_affine_copies` — `lean/Papers/OaiGeometricErdosSimilarity/TMain.lean:451`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| For every $q\in(0,1)$ | `q η : ℝ`<br>`hq0 : 0 < q`<br>`hq1 : q < 1` |
| and $\eta\in(0,1)$, there is a compact set $E_{q,\eta}\subseteq[0,1]$ with $m(E_{q,\eta})>1-\eta$ such that | `q η : ℝ`<br>`hη0 : 0 < η`<br>`hη1 : η < 1`<br>then `∃ E : Set ℝ,`<br>then `IsCompact E`<br>then `E ⊆ Set.Icc 0 1`<br>then `ENNReal.ofReal (1 - η) < lebesgueMeasure E` |
| \[ \text{for every }x\in\R\text{ and }s\in\R\setminus\{0\}, \quad | `∀ x : ℝ`<br>`∀ s : ℝ`<br>`s ≠ 0` |
| x+sq^n\notin E_{q,\eta}\text{ for some integer }n\ge1. \] | then `∃ n : ℕ,`<br>then `1 ≤ n`<br>then `x + s * q ^ n ∉ E` |

**Conditions and readings, and the Lean definitions that carry them.**

- definition of the paper: Let $m$ denote Lebesgue measure on $\R$. → `lebesgueMeasure` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:62`)
- definition of the paper: For $q\in(0,1)$, write \[ G_q=\{q^n:n\in\N,\ n\ge1\}. \] → `geometricProgression` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:72`)
- definition of the paper: For a measurable, $1$-periodic set $A\subseteq\R$, write \[ \rho(A)=m(A\cap[0,1)). \] → `periodicDensity` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:80`)
- definition of the paper: For each $k\in\Z$, put \[ p_k=\frac{\eta}{64}\,4^{-|k|} \] and choose $H_k$ from Proposition~\ref{prop:periodic} with $p=p_k$. Define \begin{equation}\label{eq:global-open} C=\bigcup_{k\in\Z}\bigl(2^kH_k\cup(-2^kH_k)\bigr), \qquad E_{q,\eta}=[0,1]\setminus C. \end{equation} → `avoidingSet` (`lean/Papers/OaiGeometricErdosSimilarity/TMain.lean:77`)

## Proposition 2.1

**Statement.** \label{prop:periodic} For every $p\in(0,1)$, there is an open $1$-periodic set $H\subseteq\R$ with $\rho(H)\le6p$ such that \begin{equation}\label{eq:periodic-hitting} \text{for every }x\in\R\text{ and }t\in[1,2], \quad x+tq^n\in H\text{ for some integer }n\ge1. \end{equation}

**Lean.** `Papers.OaiGeometricErdosSimilarity.exists_open_periodic_hitting_set` — `lean/Papers/OaiGeometricErdosSimilarity/TPeriodic.lean:588`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| For every $p\in(0,1)$, there is an open $1$-periodic set $H\subseteq\R$ with $\rho(H)\le6p$ such that | `p : ℝ`<br>`hp : TerminalProbabilityDomain p`<br>then `∃ H : Set ℝ,`<br>then `IsOpen H`<br>then `IsOnePeriodic H`<br>then `periodicDensity H ≤ 6 * p` |
| \begin{equation} \text{for every }x\in\R\text{ and }t\in[1,2], \quad | `∀ x t : ℝ`<br>`t ∈ Set.Icc (1 : ℝ) 2` |
| x+tq^n\in H\text{ for some integer }n\ge1. \end{equation} | then `∃ n : ℕ,`<br>then `1 ≤ n`<br>then `x + t * q ^ n ∈ H` |

Lean also declares what the paper leaves implicit (the objects and their types): `q : ℝ`.

Lean assumes conditions that the paper's text does not state: `hq : QDomain q`.

**Conditions and readings, and the Lean definitions that carry them.**

- condition of the paper: Fix $q\in(0,1)$ for the rest of the proof. → `QDomain` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:21`)
- definition of the paper: For a measurable, $1$-periodic set $A\subseteq\R$, write \[ \rho(A)=m(A\cap[0,1)). \] → `periodicDensity` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:80`)
- definition of the paper: For each integer $b\ge1$, put \[ c=\frac{4}{1-q},\qquad N_b=2^{\lceil\log_2(cq^{-b})\rceil},\qquad \Gamma_b=N_b^{-1}\Z. \] → `gridResolution` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:124`)
- definition of the paper: The periodic grid key of $z\in\R$ is $J_b(z)=\lfloor N_b\{z\}\rfloor$, where $\{z\}=z-\lfloor z\rfloor$. Thus the cells are closed on the left and open on the right, and a boundary point belongs to the cell on its right. → `gridKey` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:139`)
- definition of the paper: We have \begin{equation}\label{eq:grid-size} cq^{-b}\le N_b<2cq^{-b}. \end{equation} → `GridSizeComparison` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:170`)
- definition of the paper: All $N_b$ are powers of two and are nondecreasing in $b$. Consequently, if $b'\ge b$, then $N_{b'}/N_b$ is an integer and \[ J_b(z)=\left\lfloor\frac{J_{b'}(z)}{N_{b'}/N_b}\right\rfloor. \] → `GridNesting` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:218`)
- definition of the paper: Take a complete ordered $M$-ary tree of height $d$, with leaves of height $0$. Write $P_1,\ldots,P_M$ for the children of an internal vertex $P$, and $(P,i)$ for the edge from $P$ to $P_i$. Let $K$ be the total number of edges. Order the edges in preorder: for each $i=1,\ldots,M$, list $(P,i)$ and then all edges in the subtree rooted at $P_i$, in the same recursive order. → `TreeVertex` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/WindowDefinitions.lean:24`)
- definition of the paper: Assign an integer interval $W_e=[a_e,b_e]\cap\N$ to each edge, in preorder, leaving exactly $g$ unused indices between consecutive windows. All edges leaving a vertex of height $h$ receive a window of length $r_h$. For an edge with a nonleaf child, we make its window at least as long as the gap and the entire child subtree that follow it. To specify these lengths from the leaves upward, write $\sigma_h$ for the span, including gaps, of all windows in a subtree of height $h$. At height $1$ there are $M$ windows and $M-1$ gaps, so we set \[ r_1=r_0,\qquad \sigma_1=Mr_1+(M-1)g, \] and, for $2\le h\le d$, choose \[ r_h=\max\{r_0,g+\sigma_{h-1}\}. \] At height $h\ge2$ there are $M$ blocks, each comprising one outgoing window, a gap, and a child subtree. Another $M-1$ gaps separate these blocks, giving \[ \sigma_h=M(r_h+g+\sigma_{h-1})+(M-1)g. \] Choose the first starting index $n_0\ge1$ so that $2q^{n_0}\le1/4$, and place all subsequent windows with the prescribed lengths and gaps. Attach to each edge $e$ the grid indexed by its window endpoint $b_e$, and set \[ \mathcal N=\bigcup_e W_e. \] → `windowStart` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/WindowDefinitions.lean:220`)
- condition of the paper: fix \(p\in(0,1)\). → `TerminalProbabilityDomain` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:46`)
- definition of the paper: For each edge \(e=(P,i)\) with \(i<M\), let \[ S_e:\{0,\ldots,N_{b_e}-1\}\longrightarrow\{0,1\} \] be a table of independent fair bits. Child \(M\) is the default child and has no selector table. For each leaf \(L\), let \(b(L)\) be the window endpoint of its incoming edge, and let \[ T_L:\{0,\ldots,N_{b(L)}-1\}\longrightarrow\{0,1\} \] be a table of independent Bernoulli-\(p\) bits. All entries of all selector tables \(S_e\) and terminal tables \(T_L\) are mutually independent. There are finitely many entries, so they define a finite product probability space \(\Omega\), with probability \(\Prob\) and expectation \(\E\). Write \(\mathcal A\) for the sigma-field generated by all entries of all selector tables. → `tableLaw` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/TableDefinitions.lean:96`)
- definition of the paper: Given an outcome and \(z\in\R\), route \(z\) from the root as follows. At an internal vertex \(P\), choose the first child \(P_i\), \(i<M\), whose selector satisfies \(S_{(P,i)}(J_{b_{(P,i)}}(z))=1\). If all these values are zero, choose \(P_M\). Let \(L(z)\) denote the leaf reached and define \begin{equation} \label{eq:random-set} B=\bigl\{z\in\R: T_{L(z)}(J_{b(L(z))}(z))=1\bigr\}. \end{equation} → `randomSet` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/TableDefinitions.lean:254`)
- definition of the paper: For a fixed center \(x\in\R\), expose its addressed entry in \emph{every} selector table, including tables outside its route. Write \begin{equation} \label{eq:center-exposure} \mathcal F_x= \sigma\bigl(S_e(J_{b_e}(x)):e=(P,i),\ i<M\bigr) \subseteq\mathcal A. \end{equation} → `centerExposure` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/TableDefinitions.lean:284`)
- definition of the paper: Before conditioning on \(\mathcal F_x\), \begin{equation} \label{eq:no-default} \Prob\bigl(\text{the route of \(x\) has no default choice}\bigr) =(1-2^{1-M})^d. \end{equation} → `NoDefaultProbability` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/TableDefinitions.lean:485`)
- definition of the paper: Let $\mathcal S$ be the set of stable centers. → `IsStableCenter` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/WindowDefinitions.lean:341`)
- condition of the paper: for every window $W_e$ other than the first, writing $b'$ for the endpoint of its immediate predecessor, \[ (x,x+2q^{a_e}]\cap\Gamma_{b'}=\varnothing. \] → `StableCenterCondition` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/WindowDefinitions.lean:315`)
- definition of the paper: If that route uses a default child, let \(U\) be the first vertex where it does so. → `firstDefault` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/TableDefinitions.lean:449`)
- definition of the paper: Now fix a stable center \(x\) and an atom \(\xi\) on which \(U\) exists. Under this conditioning, \(U\) and its height \(h\) are fixed. Put \[ r=r_h,\qquad e_i=(U,i)\quad(1\le i<M),\qquad y_n(t)=x+tq^n\quad(t\in[1,2]). \] → `localIndices` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/Tables.lean:86`)
- definition of the paper: For \(i<M\), let \(L_i(z)\) be the leaf reached by routing \(z\) starting at the child \(U_i\); if this child is a leaf, take \(L_i(z)=U_i\). Define the local test \begin{equation} \label{eq:local-test} Q_i(z)=S_{e_i}(J_{b_{e_i}}(z))\, T_{L_i(z)}(J_{b(L_i(z))}(z)). \end{equation} → `localTest` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/Tables.lean:121`)
- definition of the paper: put $r=r_h$ and \begin{equation}\label{eq:scale-count} D_{M,q}(r)=4+2(M-1)r\bigl(1+2c q^{-2r}\bigr). \end{equation} → `scaleCount` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/ScaleDefinitions.lean:20`)

## Lemma 3.1

**Statement.** \label{lem:window-span} If $e=(P,i)$ leaves a vertex of height $h$, then \begin{equation}\label{eq:window-span} b_e^*-a_e+1\le2r_h. \end{equation}

**Lean.** `Papers.OaiGeometricErdosSimilarity.blockEndpoint_sub_windowStart_le` — `lean/Papers/OaiGeometricErdosSimilarity/Helpers/Windows.lean:145`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| If $e=(P,i)$ leaves a vertex of height $h$, | `e : TreeEdge M d`<br>`h : ℕ`<br>`he : WindowSpanHeight e h` |
| then \begin{equation} b_e^*-a_e+1\le2r_h. \end{equation} | then `blockEndpoint q M d g r0 n0 e + 1 ≤ windowStart q M d g r0 n0 e + 2 * windowLength M g r0 h` |

Lean also declares what the paper leaves implicit (the objects and their types): `M d : ℕ`, `q : ℝ`, `g r0 : ℕ`, `n0 : ℕ`.

Lean assumes conditions that the paper's text does not state: `hq : QDomain q`, `hM : BranchingDomain M`, `hd : DepthDomain d`, `hg : GapDomain g`, `hr : BaseLengthDomain r0`.

**Conditions and readings, and the Lean definitions that carry them.**

- condition of the paper: Fix $q\in(0,1)$ for the rest of the proof. → `QDomain` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:21`)
- condition of the paper: the integers $M\ge2$ → `BranchingDomain` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:26`)
- condition of the paper: $d\ge1$, → `DepthDomain` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:31`)
- condition of the paper: $g\ge1$, → `GapDomain` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:36`)
- condition of the paper: $r_0\ge1$ → `BaseLengthDomain` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:41`)
- definition of the paper: Take a complete ordered $M$-ary tree of height $d$, with leaves of height $0$. Write $P_1,\ldots,P_M$ for the children of an internal vertex $P$, and $(P,i)$ for the edge from $P$ to $P_i$. Let $K$ be the total number of edges. Order the edges in preorder: for each $i=1,\ldots,M$, list $(P,i)$ and then all edges in the subtree rooted at $P_i$, in the same recursive order. → `TreeVertex` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/WindowDefinitions.lean:24`)
- definition of the paper: Assign an integer interval $W_e=[a_e,b_e]\cap\N$ to each edge, in preorder, leaving exactly $g$ unused indices between consecutive windows. All edges leaving a vertex of height $h$ receive a window of length $r_h$. For an edge with a nonleaf child, we make its window at least as long as the gap and the entire child subtree that follow it. To specify these lengths from the leaves upward, write $\sigma_h$ for the span, including gaps, of all windows in a subtree of height $h$. At height $1$ there are $M$ windows and $M-1$ gaps, so we set \[ r_1=r_0,\qquad \sigma_1=Mr_1+(M-1)g, \] and, for $2\le h\le d$, choose \[ r_h=\max\{r_0,g+\sigma_{h-1}\}. \] At height $h\ge2$ there are $M$ blocks, each comprising one outgoing window, a gap, and a child subtree. Another $M-1$ gaps separate these blocks, giving \[ \sigma_h=M(r_h+g+\sigma_{h-1})+(M-1)g. \] Choose the first starting index $n_0\ge1$ so that $2q^{n_0}\le1/4$, and place all subsequent windows with the prescribed lengths and gaps. Attach to each edge $e$ the grid indexed by its window endpoint $b_e$, and set \[ \mathcal N=\bigcup_e W_e. \] → `windowStart` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/WindowDefinitions.lean:220`)
- definition of the paper: For $e=(P,i)$, let $b_e^*$ be the largest endpoint among $W_e$ and all windows in the subtree rooted at $P_i$. → `blockEndpoint` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/WindowDefinitions.lean:288`)
- condition of the paper: If $e=(P,i)$ leaves a vertex of height $h$, → `WindowSpanHeight` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/WindowDefinitions.lean:327`)

## Lemma 3.2

**Statement.** \label{lem:stability} The set $\mathcal S$ is measurable and $1$-periodic, and \[ \rho(\R\setminus\mathcal S)\le4Kc\,q^{g+1}. \] If $x\in\mathcal S$, $n\in W_e$, and $t\in[1,2]$, then every edge $f$ preceding $e$ in preorder satisfies \begin{equation}\label{eq:stable-keys} J_{b_f}(x+tq^n)=J_{b_f}(x). \end{equation}

**Lean.** `Papers.OaiGeometricErdosSimilarity.stableSet_measurable_density_and_keys` — `lean/Papers/OaiGeometricErdosSimilarity/Helpers/Stability.lean:332`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| The set $\mathcal S$ is measurable and $1$-periodic, | then `MeasurableSet (stableSet q M d g r0 n0)`<br>then `IsOnePeriodic (stableSet q M d g r0 n0)` |
| and \[ \rho(\R\setminus\mathcal S)\le4Kc\,q^{g+1}. \] | then `periodicDensity (stableSet q M d g r0 n0)ᶜ ≤ 4 * edgeCount M d * gridConst q * q ^ (g + 1)` |
| If $x\in\mathcal S$, | `∀ x`<br>`IsStableCenter q M d g r0 n0 x` |
| $n\in W_e$, | `n : ℕ`<br>`n ∈ windowSet q M d g r0 n0 e` |
| and $t\in[1,2]$, | `∀ t ∈ Set.Icc (1 : ℝ) 2` |
| then every edge $f$ preceding $e$ in preorder satisfies | `∀ f : TreeEdge M d`<br>`preorderLt f e` |
| \begin{equation} J_{b_f}(x+tq^n)=J_{b_f}(x). \end{equation} | then `gridKey q (windowEnd q M d g r0 n0 f) (x + t * q ^ n) = gridKey q (windowEnd q M d g r0 n0 f) x` |

Lean also declares what the paper leaves implicit (the objects and their types): `M d : ℕ`, `q : ℝ`, `g r0 : ℕ`, `n0 : ℕ`, `e : TreeEdge M d`.

Lean assumes conditions that the paper's text does not state: `hq : QDomain q`, `hM : BranchingDomain M`, `hd : DepthDomain d`, `hg : GapDomain g`, `hr : BaseLengthDomain r0`, `hn0 : 1 ≤ n0`.

**Conditions and readings, and the Lean definitions that carry them.**

- condition of the paper: Fix $q\in(0,1)$ for the rest of the proof. → `QDomain` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:21`)
- condition of the paper: the integers $M\ge2$ → `BranchingDomain` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:26`)
- condition of the paper: $d\ge1$, → `DepthDomain` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:31`)
- condition of the paper: $g\ge1$, → `GapDomain` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:36`)
- condition of the paper: $r_0\ge1$ → `BaseLengthDomain` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:41`)
- definition of the paper: Take a complete ordered $M$-ary tree of height $d$, with leaves of height $0$. Write $P_1,\ldots,P_M$ for the children of an internal vertex $P$, and $(P,i)$ for the edge from $P$ to $P_i$. Let $K$ be the total number of edges. Order the edges in preorder: for each $i=1,\ldots,M$, list $(P,i)$ and then all edges in the subtree rooted at $P_i$, in the same recursive order. → `TreeVertex` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/WindowDefinitions.lean:24`)
- definition of the paper: Assign an integer interval $W_e=[a_e,b_e]\cap\N$ to each edge, in preorder, leaving exactly $g$ unused indices between consecutive windows. All edges leaving a vertex of height $h$ receive a window of length $r_h$. For an edge with a nonleaf child, we make its window at least as long as the gap and the entire child subtree that follow it. To specify these lengths from the leaves upward, write $\sigma_h$ for the span, including gaps, of all windows in a subtree of height $h$. At height $1$ there are $M$ windows and $M-1$ gaps, so we set \[ r_1=r_0,\qquad \sigma_1=Mr_1+(M-1)g, \] and, for $2\le h\le d$, choose \[ r_h=\max\{r_0,g+\sigma_{h-1}\}. \] At height $h\ge2$ there are $M$ blocks, each comprising one outgoing window, a gap, and a child subtree. Another $M-1$ gaps separate these blocks, giving \[ \sigma_h=M(r_h+g+\sigma_{h-1})+(M-1)g. \] Choose the first starting index $n_0\ge1$ so that $2q^{n_0}\le1/4$, and place all subsequent windows with the prescribed lengths and gaps. Attach to each edge $e$ the grid indexed by its window endpoint $b_e$, and set \[ \mathcal N=\bigcup_e W_e. \] → `windowStart` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/WindowDefinitions.lean:220`)
- definition of the paper: For each integer $b\ge1$, put \[ c=\frac{4}{1-q},\qquad N_b=2^{\lceil\log_2(cq^{-b})\rceil},\qquad \Gamma_b=N_b^{-1}\Z. \] → `gridResolution` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:124`)
- definition of the paper: The periodic grid key of $z\in\R$ is $J_b(z)=\lfloor N_b\{z\}\rfloor$, where $\{z\}=z-\lfloor z\rfloor$. Thus the cells are closed on the left and open on the right, and a boundary point belongs to the cell on its right. → `gridKey` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:139`)
- definition of the paper: We have \begin{equation}\label{eq:grid-size} cq^{-b}\le N_b<2cq^{-b}. \end{equation} → `GridSizeComparison` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:170`)
- definition of the paper: All $N_b$ are powers of two and are nondecreasing in $b$. Consequently, if $b'\ge b$, then $N_{b'}/N_b$ is an integer and \[ J_b(z)=\left\lfloor\frac{J_{b'}(z)}{N_{b'}/N_b}\right\rfloor. \] → `GridNesting` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:218`)
- definition of the paper: Let $\mathcal S$ be the set of stable centers. → `IsStableCenter` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/WindowDefinitions.lean:341`)
- condition of the paper: for every window $W_e$ other than the first, writing $b'$ for the endpoint of its immediate predecessor, \[ (x,x+2q^{a_e}]\cap\Gamma_{b'}=\varnothing. \] → `StableCenterCondition` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/WindowDefinitions.lean:315`)
- definition of the paper: For a measurable, $1$-periodic set $A\subseteq\R$, write \[ \rho(A)=m(A\cap[0,1)). \] → `periodicDensity` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:80`)

## Lemma 3.3

**Statement.** \label{lem:separation} Fix an edge $e$, a center $x\in\R$, and a scale $t\in[1,2]$. The points \[ \{x\}\ \cup\ \{x+tq^n:n\in W_e\} \] have pairwise distinct keys under $J_{b_e}$. They also have pairwise distinct keys under every $J_b$ with $b\ge b_e$.

**Lean.** `Papers.OaiGeometricErdosSimilarity.gridKey_injective_on_translated_window` — `lean/Papers/OaiGeometricErdosSimilarity/Helpers/Windows.lean:249`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| Fix an edge $e$, a center $x\in\R$, | `e : TreeEdge M d`<br>`x t : ℝ` |
| and a scale $t\in[1,2]$. | `x t : ℝ`<br>`ht : SeparationParameters t` |
| The points \[ \{x\}\ \cup\ \{x+tq^n:n\in W_e\} \] | then `Function.Injective (fun u : Option {n // n ∈ windowSet q M d g r0 n0 e} => gridKey q b (sepPoint x t q u))` |
| have pairwise distinct keys under $J_{b_e}$. | — (no Lean counterpart recorded) |
| They also have pairwise distinct keys under every $J_b$ with $b\ge b_e$. | `∀ b : ℕ`<br>`windowEnd q M d g r0 n0 e ≤ b`<br>then `Function.Injective (fun u : Option {n // n ∈ windowSet q M d g r0 n0 e} => gridKey q b (sepPoint x t q u))` |

Lean also declares what the paper leaves implicit (the objects and their types): `M d : ℕ`, `q : ℝ`, `g r0 : ℕ`, `n0 : ℕ`.

Lean assumes conditions that the paper's text does not state: `hq : QDomain q`, `hM : BranchingDomain M`, `hd : DepthDomain d`, `hg : GapDomain g`, `hr : BaseLengthDomain r0`, `hn0 : 1 ≤ n0`, `hn0q : 2 * q ^ n0 ≤ 1 / 4`.

**Conditions and readings, and the Lean definitions that carry them.**

- condition of the paper: Fix $q\in(0,1)$ for the rest of the proof. → `QDomain` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:21`)
- condition of the paper: the integers $M\ge2$ → `BranchingDomain` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:26`)
- condition of the paper: $d\ge1$, → `DepthDomain` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:31`)
- condition of the paper: $g\ge1$, → `GapDomain` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:36`)
- condition of the paper: $r_0\ge1$ → `BaseLengthDomain` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:41`)
- definition of the paper: Take a complete ordered $M$-ary tree of height $d$, with leaves of height $0$. Write $P_1,\ldots,P_M$ for the children of an internal vertex $P$, and $(P,i)$ for the edge from $P$ to $P_i$. Let $K$ be the total number of edges. Order the edges in preorder: for each $i=1,\ldots,M$, list $(P,i)$ and then all edges in the subtree rooted at $P_i$, in the same recursive order. → `TreeVertex` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/WindowDefinitions.lean:24`)
- definition of the paper: Assign an integer interval $W_e=[a_e,b_e]\cap\N$ to each edge, in preorder, leaving exactly $g$ unused indices between consecutive windows. All edges leaving a vertex of height $h$ receive a window of length $r_h$. For an edge with a nonleaf child, we make its window at least as long as the gap and the entire child subtree that follow it. To specify these lengths from the leaves upward, write $\sigma_h$ for the span, including gaps, of all windows in a subtree of height $h$. At height $1$ there are $M$ windows and $M-1$ gaps, so we set \[ r_1=r_0,\qquad \sigma_1=Mr_1+(M-1)g, \] and, for $2\le h\le d$, choose \[ r_h=\max\{r_0,g+\sigma_{h-1}\}. \] At height $h\ge2$ there are $M$ blocks, each comprising one outgoing window, a gap, and a child subtree. Another $M-1$ gaps separate these blocks, giving \[ \sigma_h=M(r_h+g+\sigma_{h-1})+(M-1)g. \] Choose the first starting index $n_0\ge1$ so that $2q^{n_0}\le1/4$, and place all subsequent windows with the prescribed lengths and gaps. Attach to each edge $e$ the grid indexed by its window endpoint $b_e$, and set \[ \mathcal N=\bigcup_e W_e. \] → `windowStart` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/WindowDefinitions.lean:220`)
- definition of the paper: For each integer $b\ge1$, put \[ c=\frac{4}{1-q},\qquad N_b=2^{\lceil\log_2(cq^{-b})\rceil},\qquad \Gamma_b=N_b^{-1}\Z. \] → `gridResolution` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:124`)
- definition of the paper: The periodic grid key of $z\in\R$ is $J_b(z)=\lfloor N_b\{z\}\rfloor$, where $\{z\}=z-\lfloor z\rfloor$. Thus the cells are closed on the left and open on the right, and a boundary point belongs to the cell on its right. → `gridKey` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:139`)
- definition of the paper: We have \begin{equation}\label{eq:grid-size} cq^{-b}\le N_b<2cq^{-b}. \end{equation} → `GridSizeComparison` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:170`)
- definition of the paper: All $N_b$ are powers of two and are nondecreasing in $b$. Consequently, if $b'\ge b$, then $N_{b'}/N_b$ is an integer and \[ J_b(z)=\left\lfloor\frac{J_{b'}(z)}{N_{b'}/N_b}\right\rfloor. \] → `GridNesting` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:218`)
- condition of the paper: \label{lem:separation} Fix an edge $e$, a center $x\in\R$, and a scale $t\in[1,2]$. → `SeparationParameters` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/WindowDefinitions.lean:332`)

## Lemma 4.1

**Statement.** \label{lem:density} The random set \(B\) in \eqref{eq:random-set} satisfies \(\E\rho(B)=p\).

**Lean.** `Papers.OaiGeometricErdosSimilarity.expected_periodicDensity_randomSet_eq` — `lean/Papers/OaiGeometricErdosSimilarity/Helpers/Tables.lean:366`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| The random set \(B\) in \eqref{eq:random-set} satisfies \(\E\rho(B)=p\). | then `(tableLaw q M d g r0 n0 p).E (fun ω => periodicDensity (randomSet hM ω)) = p` |

Lean also declares what the paper leaves implicit (the objects and their types): `q : ℝ`, `M d g r0 n0 : ℕ`, `p : ℝ`.

Lean assumes conditions that the paper's text does not state: `hq : QDomain q`, `hM : BranchingDomain M`, `hd : DepthDomain d`, `hg : GapDomain g`, `hr : BaseLengthDomain r0`, `hp : TerminalProbabilityDomain p`.

**Conditions and readings, and the Lean definitions that carry them.**

- condition of the paper: Fix $q\in(0,1)$ for the rest of the proof. → `QDomain` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:21`)
- condition of the paper: the integers $M\ge2$ → `BranchingDomain` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:26`)
- condition of the paper: $d\ge1$, → `DepthDomain` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:31`)
- condition of the paper: $g\ge1$, → `GapDomain` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:36`)
- condition of the paper: $r_0\ge1$ → `BaseLengthDomain` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:41`)
- definition of the paper: Take a complete ordered $M$-ary tree of height $d$, with leaves of height $0$. Write $P_1,\ldots,P_M$ for the children of an internal vertex $P$, and $(P,i)$ for the edge from $P$ to $P_i$. Let $K$ be the total number of edges. Order the edges in preorder: for each $i=1,\ldots,M$, list $(P,i)$ and then all edges in the subtree rooted at $P_i$, in the same recursive order. → `TreeVertex` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/WindowDefinitions.lean:24`)
- definition of the paper: Assign an integer interval $W_e=[a_e,b_e]\cap\N$ to each edge, in preorder, leaving exactly $g$ unused indices between consecutive windows. All edges leaving a vertex of height $h$ receive a window of length $r_h$. For an edge with a nonleaf child, we make its window at least as long as the gap and the entire child subtree that follow it. To specify these lengths from the leaves upward, write $\sigma_h$ for the span, including gaps, of all windows in a subtree of height $h$. At height $1$ there are $M$ windows and $M-1$ gaps, so we set \[ r_1=r_0,\qquad \sigma_1=Mr_1+(M-1)g, \] and, for $2\le h\le d$, choose \[ r_h=\max\{r_0,g+\sigma_{h-1}\}. \] At height $h\ge2$ there are $M$ blocks, each comprising one outgoing window, a gap, and a child subtree. Another $M-1$ gaps separate these blocks, giving \[ \sigma_h=M(r_h+g+\sigma_{h-1})+(M-1)g. \] Choose the first starting index $n_0\ge1$ so that $2q^{n_0}\le1/4$, and place all subsequent windows with the prescribed lengths and gaps. Attach to each edge $e$ the grid indexed by its window endpoint $b_e$, and set \[ \mathcal N=\bigcup_e W_e. \] → `windowStart` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/WindowDefinitions.lean:220`)
- definition of the paper: For each integer $b\ge1$, put \[ c=\frac{4}{1-q},\qquad N_b=2^{\lceil\log_2(cq^{-b})\rceil},\qquad \Gamma_b=N_b^{-1}\Z. \] → `gridResolution` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:124`)
- definition of the paper: The periodic grid key of $z\in\R$ is $J_b(z)=\lfloor N_b\{z\}\rfloor$, where $\{z\}=z-\lfloor z\rfloor$. Thus the cells are closed on the left and open on the right, and a boundary point belongs to the cell on its right. → `gridKey` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:139`)
- definition of the paper: We have \begin{equation}\label{eq:grid-size} cq^{-b}\le N_b<2cq^{-b}. \end{equation} → `GridSizeComparison` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:170`)
- definition of the paper: All $N_b$ are powers of two and are nondecreasing in $b$. Consequently, if $b'\ge b$, then $N_{b'}/N_b$ is an integer and \[ J_b(z)=\left\lfloor\frac{J_{b'}(z)}{N_{b'}/N_b}\right\rfloor. \] → `GridNesting` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:218`)
- condition of the paper: fix \(p\in(0,1)\). → `TerminalProbabilityDomain` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:46`)
- definition of the paper: For each edge \(e=(P,i)\) with \(i<M\), let \[ S_e:\{0,\ldots,N_{b_e}-1\}\longrightarrow\{0,1\} \] be a table of independent fair bits. Child \(M\) is the default child and has no selector table. For each leaf \(L\), let \(b(L)\) be the window endpoint of its incoming edge, and let \[ T_L:\{0,\ldots,N_{b(L)}-1\}\longrightarrow\{0,1\} \] be a table of independent Bernoulli-\(p\) bits. All entries of all selector tables \(S_e\) and terminal tables \(T_L\) are mutually independent. There are finitely many entries, so they define a finite product probability space \(\Omega\), with probability \(\Prob\) and expectation \(\E\). Write \(\mathcal A\) for the sigma-field generated by all entries of all selector tables. → `tableLaw` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/TableDefinitions.lean:96`)
- definition of the paper: Given an outcome and \(z\in\R\), route \(z\) from the root as follows. At an internal vertex \(P\), choose the first child \(P_i\), \(i<M\), whose selector satisfies \(S_{(P,i)}(J_{b_{(P,i)}}(z))=1\). If all these values are zero, choose \(P_M\). Let \(L(z)\) denote the leaf reached and define \begin{equation} \label{eq:random-set} B=\bigl\{z\in\R: T_{L(z)}(J_{b(L(z))}(z))=1\bigr\}. \end{equation} → `randomSet` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/TableDefinitions.lean:254`)
- definition of the paper: For a fixed center \(x\in\R\), expose its addressed entry in \emph{every} selector table, including tables outside its route. Write \begin{equation} \label{eq:center-exposure} \mathcal F_x= \sigma\bigl(S_e(J_{b_e}(x)):e=(P,i),\ i<M\bigr) \subseteq\mathcal A. \end{equation} → `centerExposure` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/TableDefinitions.lean:284`)
- definition of the paper: For a measurable, $1$-periodic set $A\subseteq\R$, write \[ \rho(A)=m(A\cap[0,1)). \] → `periodicDensity` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:80`)

## Lemma 4.2

**Statement.** \label{lem:routing} Fix a stable center \(x\) and an atom \(\xi\) of \(\mathcal F_x\) on which the first default vertex \(U\) exists. For every outcome in \(\xi\), every \(i<M\), every \(n\in W_{e_i}\), and every \(t\in[1,2]\), the route of \(y_n(t)\) reaches \(U\) and rejects its children \(1,\ldots,i-1\). Consequently, \begin{equation} \label{eq:local-hit} Q_i(y_n(t))=1\quad\Longrightarrow\quad y_n(t)\in B. \end{equation}

**Lean.** `Papers.OaiGeometricErdosSimilarity.localTest_imp_mem_randomSet` — `lean/Papers/OaiGeometricErdosSimilarity/Helpers/LocalRouting.lean:307`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| Fix a stable center \(x\) and an atom \(\xi\) of \(\mathcal F_x\) on which the first default vertex \(U\) exists. | `x : ℝ`<br>`hx : StableCenterCondition q M d g r0 n0 x`<br>`ξ : NondefaultEdge M d → Bool`<br>`hξ : RoutingDefaultAtom q M d g r0 hM x ξ`<br>`U : InternalVertex M d`<br>`hU : firstDefault q M d g r0 hM x ξ = some U` |
| For every outcome in \(\xi\), every \(i<M\), every \(n\in W_{e_i}\), | `∀ ω : Outcome q M d g r0 n0`<br>`atomEvent q M d g r0 n0 x ξ ω`<br>`i : Fin M`<br>`hi : i.val + 1 < M`<br>`∀ n ∈ windowSet q M d g r0 n0 (localEdge U i)` |
| and every \(t\in[1,2]\), the route of \(y_n(t)\) reaches \(U\) and rejects its children \(1,\ldots,i-1\). | `∀ t ∈ Set.Icc (1 : ℝ) 2`<br>then `routeReaches hM ω (localPoint x t q n) U`<br>`∀ j : Fin M`<br>`j < i`<br>then `rejects ω (localPoint x t q n) (localEdge U j)` |
| Consequently, \begin{equation} Q_i(y_n(t))=1\quad\Longrightarrow\quad | `localTest hM ω U i hi (localPoint x t q n) = true` |
| y_n(t)\in B. \end{equation} | then `localPoint x t q n ∈ randomSet hM ω` |

Lean also declares what the paper leaves implicit (the objects and their types): `q : ℝ`, `M d g r0 n0 : ℕ`, `p : ℝ`.

Lean assumes conditions that the paper's text does not state: `hq : QDomain q`, `hM : BranchingDomain M`, `hd : DepthDomain d`, `hg : GapDomain g`, `hr : BaseLengthDomain r0`, `hp : TerminalProbabilityDomain p`.

**Conditions and readings, and the Lean definitions that carry them.**

- condition of the paper: Fix $q\in(0,1)$ for the rest of the proof. → `QDomain` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:21`)
- condition of the paper: the integers $M\ge2$ → `BranchingDomain` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:26`)
- condition of the paper: $d\ge1$, → `DepthDomain` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:31`)
- condition of the paper: $g\ge1$, → `GapDomain` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:36`)
- condition of the paper: $r_0\ge1$ → `BaseLengthDomain` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:41`)
- definition of the paper: Take a complete ordered $M$-ary tree of height $d$, with leaves of height $0$. Write $P_1,\ldots,P_M$ for the children of an internal vertex $P$, and $(P,i)$ for the edge from $P$ to $P_i$. Let $K$ be the total number of edges. Order the edges in preorder: for each $i=1,\ldots,M$, list $(P,i)$ and then all edges in the subtree rooted at $P_i$, in the same recursive order. → `TreeVertex` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/WindowDefinitions.lean:24`)
- definition of the paper: Assign an integer interval $W_e=[a_e,b_e]\cap\N$ to each edge, in preorder, leaving exactly $g$ unused indices between consecutive windows. All edges leaving a vertex of height $h$ receive a window of length $r_h$. For an edge with a nonleaf child, we make its window at least as long as the gap and the entire child subtree that follow it. To specify these lengths from the leaves upward, write $\sigma_h$ for the span, including gaps, of all windows in a subtree of height $h$. At height $1$ there are $M$ windows and $M-1$ gaps, so we set \[ r_1=r_0,\qquad \sigma_1=Mr_1+(M-1)g, \] and, for $2\le h\le d$, choose \[ r_h=\max\{r_0,g+\sigma_{h-1}\}. \] At height $h\ge2$ there are $M$ blocks, each comprising one outgoing window, a gap, and a child subtree. Another $M-1$ gaps separate these blocks, giving \[ \sigma_h=M(r_h+g+\sigma_{h-1})+(M-1)g. \] Choose the first starting index $n_0\ge1$ so that $2q^{n_0}\le1/4$, and place all subsequent windows with the prescribed lengths and gaps. Attach to each edge $e$ the grid indexed by its window endpoint $b_e$, and set \[ \mathcal N=\bigcup_e W_e. \] → `windowStart` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/WindowDefinitions.lean:220`)
- definition of the paper: For each integer $b\ge1$, put \[ c=\frac{4}{1-q},\qquad N_b=2^{\lceil\log_2(cq^{-b})\rceil},\qquad \Gamma_b=N_b^{-1}\Z. \] → `gridResolution` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:124`)
- definition of the paper: The periodic grid key of $z\in\R$ is $J_b(z)=\lfloor N_b\{z\}\rfloor$, where $\{z\}=z-\lfloor z\rfloor$. Thus the cells are closed on the left and open on the right, and a boundary point belongs to the cell on its right. → `gridKey` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:139`)
- definition of the paper: We have \begin{equation}\label{eq:grid-size} cq^{-b}\le N_b<2cq^{-b}. \end{equation} → `GridSizeComparison` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:170`)
- definition of the paper: All $N_b$ are powers of two and are nondecreasing in $b$. Consequently, if $b'\ge b$, then $N_{b'}/N_b$ is an integer and \[ J_b(z)=\left\lfloor\frac{J_{b'}(z)}{N_{b'}/N_b}\right\rfloor. \] → `GridNesting` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:218`)
- condition of the paper: fix \(p\in(0,1)\). → `TerminalProbabilityDomain` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:46`)
- definition of the paper: For each edge \(e=(P,i)\) with \(i<M\), let \[ S_e:\{0,\ldots,N_{b_e}-1\}\longrightarrow\{0,1\} \] be a table of independent fair bits. Child \(M\) is the default child and has no selector table. For each leaf \(L\), let \(b(L)\) be the window endpoint of its incoming edge, and let \[ T_L:\{0,\ldots,N_{b(L)}-1\}\longrightarrow\{0,1\} \] be a table of independent Bernoulli-\(p\) bits. All entries of all selector tables \(S_e\) and terminal tables \(T_L\) are mutually independent. There are finitely many entries, so they define a finite product probability space \(\Omega\), with probability \(\Prob\) and expectation \(\E\). Write \(\mathcal A\) for the sigma-field generated by all entries of all selector tables. → `tableLaw` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/TableDefinitions.lean:96`)
- definition of the paper: Given an outcome and \(z\in\R\), route \(z\) from the root as follows. At an internal vertex \(P\), choose the first child \(P_i\), \(i<M\), whose selector satisfies \(S_{(P,i)}(J_{b_{(P,i)}}(z))=1\). If all these values are zero, choose \(P_M\). Let \(L(z)\) denote the leaf reached and define \begin{equation} \label{eq:random-set} B=\bigl\{z\in\R: T_{L(z)}(J_{b(L(z))}(z))=1\bigr\}. \end{equation} → `randomSet` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/TableDefinitions.lean:254`)
- definition of the paper: For a fixed center \(x\in\R\), expose its addressed entry in \emph{every} selector table, including tables outside its route. Write \begin{equation} \label{eq:center-exposure} \mathcal F_x= \sigma\bigl(S_e(J_{b_e}(x)):e=(P,i),\ i<M\bigr) \subseteq\mathcal A. \end{equation} → `centerExposure` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/TableDefinitions.lean:284`)
- definition of the paper: Let $\mathcal S$ be the set of stable centers. → `IsStableCenter` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/WindowDefinitions.lean:341`)
- condition of the paper: for every window $W_e$ other than the first, writing $b'$ for the endpoint of its immediate predecessor, \[ (x,x+2q^{a_e}]\cap\Gamma_{b'}=\varnothing. \] → `StableCenterCondition` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/WindowDefinitions.lean:315`)
- definition of the paper: If that route uses a default child, let \(U\) be the first vertex where it does so. → `firstDefault` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/TableDefinitions.lean:449`)
- definition of the paper: Now fix a stable center \(x\) and an atom \(\xi\) on which \(U\) exists. Under this conditioning, \(U\) and its height \(h\) are fixed. Put \[ r=r_h,\qquad e_i=(U,i)\quad(1\le i<M),\qquad y_n(t)=x+tq^n\quad(t\in[1,2]). \] → `localIndices` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/Tables.lean:86`)
- definition of the paper: For \(i<M\), let \(L_i(z)\) be the leaf reached by routing \(z\) starting at the child \(U_i\); if this child is a leaf, take \(L_i(z)=U_i\). Define the local test \begin{equation} \label{eq:local-test} Q_i(z)=S_{e_i}(J_{b_{e_i}}(z))\, T_{L_i(z)}(J_{b(L_i(z))}(z)). \end{equation} → `localTest` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/Tables.lean:121`)
- condition of the paper: an atom \(\xi\) of \(\mathcal F_x\) on which the first default vertex \(U\) exists. → `RoutingDefaultAtom` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/Tables.lean:23`)

## Lemma 4.3

**Statement.** \label{lem:independent-tests} Fix a stable center \(x\) and an atom \(\xi\) of \(\mathcal F_x\) on which the first default vertex \(U\) exists. Let \(h\) be its height and \(r=r_h\), and define \(Q_i\) by \eqref{eq:local-test}. For every fixed \(t\in[1,2]\), \begin{equation} \label{eq:test-failure} \Prob\left( Q_i(y_n(t))=0\text{ for all }i<M,\ n\in W_{e_i} \,\middle|\,\xi\right) =(1-p/2)^{(M-1)r}. \end{equation}

**Lean.** `Papers.OaiGeometricErdosSimilarity.condPr_forall_localTest_false_eq` — `lean/Papers/OaiGeometricErdosSimilarity/Helpers/Routing.lean:620`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| Fix a stable center \(x\) and an atom \(\xi\) of \(\mathcal F_x\) on which the first default vertex \(U\) exists. | `x : ℝ`<br>`hx : StableCenterCondition q M d g r0 n0 x`<br>`ξ : NondefaultEdge M d → Bool`<br>`hξ : IndependentTestsDefaultAtom q M d g r0 hM x ξ`<br>`U : InternalVertex M d`<br>`hU : firstDefault q M d g r0 hM x ξ = some U` |
| Let \(h\) be its height and \(r=r_h\), | `h : ℕ`<br>`hh : vertexHeight U.val = h` |
| and define \(Q_i\) by \eqref{eq:local-test}. | — (no Lean counterpart recorded) |
| For every fixed \(t\in[1,2]\), | `t : ℝ`<br>`ht : t ∈ Set.Icc (1 : ℝ) 2` |
| \begin{equation} \Prob\left( Q_i(y_n(t))=0\text{ for all }i<M,\ n\in W_{e_i} \,\middle\|\,\xi\right) =(1-p/2)^{(M-1)r}. \end{equation} | then `condPr (tableLaw q M d g r0 n0 p) (allLocalTestsFail hM U x t) (atomEvent q M d g r0 n0 x ξ) = (1 - p / 2) ^ ((M - 1) * windowLength M g r0 h)` |

Lean also declares what the paper leaves implicit (the objects and their types): `q p : ℝ`, `M d g r0 n0 : ℕ`.

Lean assumes conditions that the paper's text does not state: `hq : QDomain q`, `hM : BranchingDomain M`, `hd : DepthDomain d`, `hg : GapDomain g`, `hr : BaseLengthDomain r0`, `hn0 : 1 ≤ n0`, `hn0q : 2 * q ^ n0 ≤ 1 / 4`, `hp : TerminalProbabilityDomain p`.

**Conditions and readings, and the Lean definitions that carry them.**

- condition of the paper: Fix $q\in(0,1)$ for the rest of the proof. → `QDomain` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:21`)
- condition of the paper: the integers $M\ge2$ → `BranchingDomain` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:26`)
- condition of the paper: $d\ge1$, → `DepthDomain` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:31`)
- condition of the paper: $g\ge1$, → `GapDomain` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:36`)
- condition of the paper: $r_0\ge1$ → `BaseLengthDomain` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:41`)
- definition of the paper: Take a complete ordered $M$-ary tree of height $d$, with leaves of height $0$. Write $P_1,\ldots,P_M$ for the children of an internal vertex $P$, and $(P,i)$ for the edge from $P$ to $P_i$. Let $K$ be the total number of edges. Order the edges in preorder: for each $i=1,\ldots,M$, list $(P,i)$ and then all edges in the subtree rooted at $P_i$, in the same recursive order. → `TreeVertex` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/WindowDefinitions.lean:24`)
- definition of the paper: Assign an integer interval $W_e=[a_e,b_e]\cap\N$ to each edge, in preorder, leaving exactly $g$ unused indices between consecutive windows. All edges leaving a vertex of height $h$ receive a window of length $r_h$. For an edge with a nonleaf child, we make its window at least as long as the gap and the entire child subtree that follow it. To specify these lengths from the leaves upward, write $\sigma_h$ for the span, including gaps, of all windows in a subtree of height $h$. At height $1$ there are $M$ windows and $M-1$ gaps, so we set \[ r_1=r_0,\qquad \sigma_1=Mr_1+(M-1)g, \] and, for $2\le h\le d$, choose \[ r_h=\max\{r_0,g+\sigma_{h-1}\}. \] At height $h\ge2$ there are $M$ blocks, each comprising one outgoing window, a gap, and a child subtree. Another $M-1$ gaps separate these blocks, giving \[ \sigma_h=M(r_h+g+\sigma_{h-1})+(M-1)g. \] Choose the first starting index $n_0\ge1$ so that $2q^{n_0}\le1/4$, and place all subsequent windows with the prescribed lengths and gaps. Attach to each edge $e$ the grid indexed by its window endpoint $b_e$, and set \[ \mathcal N=\bigcup_e W_e. \] → `windowStart` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/WindowDefinitions.lean:220`)
- definition of the paper: For each integer $b\ge1$, put \[ c=\frac{4}{1-q},\qquad N_b=2^{\lceil\log_2(cq^{-b})\rceil},\qquad \Gamma_b=N_b^{-1}\Z. \] → `gridResolution` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:124`)
- definition of the paper: The periodic grid key of $z\in\R$ is $J_b(z)=\lfloor N_b\{z\}\rfloor$, where $\{z\}=z-\lfloor z\rfloor$. Thus the cells are closed on the left and open on the right, and a boundary point belongs to the cell on its right. → `gridKey` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:139`)
- definition of the paper: We have \begin{equation}\label{eq:grid-size} cq^{-b}\le N_b<2cq^{-b}. \end{equation} → `GridSizeComparison` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:170`)
- definition of the paper: All $N_b$ are powers of two and are nondecreasing in $b$. Consequently, if $b'\ge b$, then $N_{b'}/N_b$ is an integer and \[ J_b(z)=\left\lfloor\frac{J_{b'}(z)}{N_{b'}/N_b}\right\rfloor. \] → `GridNesting` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:218`)
- condition of the paper: fix \(p\in(0,1)\). → `TerminalProbabilityDomain` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:46`)
- definition of the paper: For each edge \(e=(P,i)\) with \(i<M\), let \[ S_e:\{0,\ldots,N_{b_e}-1\}\longrightarrow\{0,1\} \] be a table of independent fair bits. Child \(M\) is the default child and has no selector table. For each leaf \(L\), let \(b(L)\) be the window endpoint of its incoming edge, and let \[ T_L:\{0,\ldots,N_{b(L)}-1\}\longrightarrow\{0,1\} \] be a table of independent Bernoulli-\(p\) bits. All entries of all selector tables \(S_e\) and terminal tables \(T_L\) are mutually independent. There are finitely many entries, so they define a finite product probability space \(\Omega\), with probability \(\Prob\) and expectation \(\E\). Write \(\mathcal A\) for the sigma-field generated by all entries of all selector tables. → `tableLaw` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/TableDefinitions.lean:96`)
- definition of the paper: Given an outcome and \(z\in\R\), route \(z\) from the root as follows. At an internal vertex \(P\), choose the first child \(P_i\), \(i<M\), whose selector satisfies \(S_{(P,i)}(J_{b_{(P,i)}}(z))=1\). If all these values are zero, choose \(P_M\). Let \(L(z)\) denote the leaf reached and define \begin{equation} \label{eq:random-set} B=\bigl\{z\in\R: T_{L(z)}(J_{b(L(z))}(z))=1\bigr\}. \end{equation} → `randomSet` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/TableDefinitions.lean:254`)
- definition of the paper: For a fixed center \(x\in\R\), expose its addressed entry in \emph{every} selector table, including tables outside its route. Write \begin{equation} \label{eq:center-exposure} \mathcal F_x= \sigma\bigl(S_e(J_{b_e}(x)):e=(P,i),\ i<M\bigr) \subseteq\mathcal A. \end{equation} → `centerExposure` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/TableDefinitions.lean:284`)
- definition of the paper: Let $\mathcal S$ be the set of stable centers. → `IsStableCenter` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/WindowDefinitions.lean:341`)
- condition of the paper: for every window $W_e$ other than the first, writing $b'$ for the endpoint of its immediate predecessor, \[ (x,x+2q^{a_e}]\cap\Gamma_{b'}=\varnothing. \] → `StableCenterCondition` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/WindowDefinitions.lean:315`)
- definition of the paper: If that route uses a default child, let \(U\) be the first vertex where it does so. → `firstDefault` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/TableDefinitions.lean:449`)
- definition of the paper: Now fix a stable center \(x\) and an atom \(\xi\) on which \(U\) exists. Under this conditioning, \(U\) and its height \(h\) are fixed. Put \[ r=r_h,\qquad e_i=(U,i)\quad(1\le i<M),\qquad y_n(t)=x+tq^n\quad(t\in[1,2]). \] → `localIndices` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/Tables.lean:86`)
- definition of the paper: For \(i<M\), let \(L_i(z)\) be the leaf reached by routing \(z\) starting at the child \(U_i\); if this child is a leaf, take \(L_i(z)=U_i\). Define the local test \begin{equation} \label{eq:local-test} Q_i(z)=S_{e_i}(J_{b_{e_i}}(z))\, T_{L_i(z)}(J_{b(L_i(z))}(z)). \end{equation} → `localTest` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/Tables.lean:121`)
- condition of the paper: an atom \(\xi\) of \(\mathcal F_x\) on which the first default vertex \(U\) exists. → `IndependentTestsDefaultAtom` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/Tables.lean:32`)

## Lemma 5.1

**Statement.** \label{lem:conditional-scales} Fix $p\in(0,1)$ and the construction parameters $M,d,g,r_0$ of Sections~\ref{sec:windows} and~\ref{sec:routing}. Let $x\in\mathcal S$ be a stable center, and let $\xi$ be an atom of the center-exposure field $\mathcal F_x$ on which the route of $x$ uses a default edge. If its first default occurs at a vertex $U$ of height $h$, put $r=r_h$ and \begin{equation}\label{eq:scale-count} D_{M,q}(r)=4+2(M-1)r\bigl(1+2c q^{-2r}\bigr). \end{equation} Then \begin{equation}\label{eq:conditional-scales} \Prob\!\left( \exists t\in[1,2]\ \forall n\in\mathcal N:\ x+tq^n\notin B\ \middle|\ \xi \right) \le D_{M,q}(r)e^{-p(M-1)r/2}. \end{equation}

**Lean.** `Papers.OaiGeometricErdosSimilarity.condPr_exists_scale_miss_le` — `lean/Papers/OaiGeometricErdosSimilarity/Helpers/Scales.lean:92`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| Fix $p\in(0,1)$ and the construction parameters $M,d,g,r_0$ of Sections~\ref{sec:windows} and~\ref{sec:routing}. | ≈ `q p : ℝ`<br>≈ `M d g r0 n0 : ℕ`<br>≈ `hM : BranchingDomain M`<br>≈ `hd : DepthDomain d`<br>≈ `hg : GapDomain g`<br>≈ `hr : BaseLengthDomain r0`<br>≈ `hp : TerminalProbabilityDomain p`<br>≈ `hpar : ConditionalScalesParameters p M d g r0` |
| Let $x\in\mathcal S$ be a stable center, | `x : ℝ`<br>`hx : StableCenterCondition q M d g r0 n0 x` |
| and let $\xi$ be an atom of the center-exposure field $\mathcal F_x$ on which the route of $x$ uses a default edge. | `ξ : NondefaultEdge M d → Bool`<br>`hξ : ConditionalScalesDefaultAtom q M d g r0 hM x ξ` |
| If its first default occurs at a vertex $U$ of height $h$, put $r=r_h$ and | `U : InternalVertex M d`<br>`h : ℕ`<br>`hUh : ConditionalScalesHeight q M d g r0 hM x ξ U h` |
| \begin{equation} D_{M,q}(r)=4+2(M-1)r\bigl(1+2c q^{-2r}\bigr). \end{equation} | — (no Lean counterpart recorded) |
| Then \begin{equation} \Prob\!\left( \exists t\in[1,2]\ \forall n\in\mathcal N:\ x+tq^n\notin B\ \middle\|\ \xi \right) \le D_{M,q}(r)e^{-p(M-1)r/2}. \end{equation} | then `condPr (tableLaw q M d g r0 n0 p) (fun ω => ∃ t ∈ Set.Icc (1 : ℝ) 2, ∀ n ∈ indexSet q M d g r0 n0, localPoint x t q n ∉ randomSet hM ω) (atomEvent q M d g r0 n0 x ξ) ≤ scaleCount M q (windowLength M g r0 h) * Real.exp (-(p * ((M : ℝ) - 1) * windowLength M g r0 h / 2))` |

A row marked ≈ was given these phrases with many rows of its result at once, not on its own.

Lean assumes conditions that the paper's text does not state: `hq : QDomain q`, `hn0 : 1 ≤ n0`, `hn0q : 2 * q ^ n0 ≤ 1 / 4`.

**Conditions and readings, and the Lean definitions that carry them.**

- condition of the paper: Fix $q\in(0,1)$ for the rest of the proof. → `QDomain` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:21`)
- condition of the paper: the integers $M\ge2$ → `BranchingDomain` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:26`)
- condition of the paper: $d\ge1$, → `DepthDomain` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:31`)
- condition of the paper: $g\ge1$, → `GapDomain` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:36`)
- condition of the paper: $r_0\ge1$ → `BaseLengthDomain` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:41`)
- definition of the paper: Take a complete ordered $M$-ary tree of height $d$, with leaves of height $0$. Write $P_1,\ldots,P_M$ for the children of an internal vertex $P$, and $(P,i)$ for the edge from $P$ to $P_i$. Let $K$ be the total number of edges. Order the edges in preorder: for each $i=1,\ldots,M$, list $(P,i)$ and then all edges in the subtree rooted at $P_i$, in the same recursive order. → `TreeVertex` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/WindowDefinitions.lean:24`)
- definition of the paper: Assign an integer interval $W_e=[a_e,b_e]\cap\N$ to each edge, in preorder, leaving exactly $g$ unused indices between consecutive windows. All edges leaving a vertex of height $h$ receive a window of length $r_h$. For an edge with a nonleaf child, we make its window at least as long as the gap and the entire child subtree that follow it. To specify these lengths from the leaves upward, write $\sigma_h$ for the span, including gaps, of all windows in a subtree of height $h$. At height $1$ there are $M$ windows and $M-1$ gaps, so we set \[ r_1=r_0,\qquad \sigma_1=Mr_1+(M-1)g, \] and, for $2\le h\le d$, choose \[ r_h=\max\{r_0,g+\sigma_{h-1}\}. \] At height $h\ge2$ there are $M$ blocks, each comprising one outgoing window, a gap, and a child subtree. Another $M-1$ gaps separate these blocks, giving \[ \sigma_h=M(r_h+g+\sigma_{h-1})+(M-1)g. \] Choose the first starting index $n_0\ge1$ so that $2q^{n_0}\le1/4$, and place all subsequent windows with the prescribed lengths and gaps. Attach to each edge $e$ the grid indexed by its window endpoint $b_e$, and set \[ \mathcal N=\bigcup_e W_e. \] → `windowStart` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/WindowDefinitions.lean:220`)
- definition of the paper: For each integer $b\ge1$, put \[ c=\frac{4}{1-q},\qquad N_b=2^{\lceil\log_2(cq^{-b})\rceil},\qquad \Gamma_b=N_b^{-1}\Z. \] → `gridResolution` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:124`)
- definition of the paper: The periodic grid key of $z\in\R$ is $J_b(z)=\lfloor N_b\{z\}\rfloor$, where $\{z\}=z-\lfloor z\rfloor$. Thus the cells are closed on the left and open on the right, and a boundary point belongs to the cell on its right. → `gridKey` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:139`)
- definition of the paper: We have \begin{equation}\label{eq:grid-size} cq^{-b}\le N_b<2cq^{-b}. \end{equation} → `GridSizeComparison` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:170`)
- definition of the paper: All $N_b$ are powers of two and are nondecreasing in $b$. Consequently, if $b'\ge b$, then $N_{b'}/N_b$ is an integer and \[ J_b(z)=\left\lfloor\frac{J_{b'}(z)}{N_{b'}/N_b}\right\rfloor. \] → `GridNesting` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:218`)
- condition of the paper: fix \(p\in(0,1)\). → `TerminalProbabilityDomain` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:46`)
- definition of the paper: For each edge \(e=(P,i)\) with \(i<M\), let \[ S_e:\{0,\ldots,N_{b_e}-1\}\longrightarrow\{0,1\} \] be a table of independent fair bits. Child \(M\) is the default child and has no selector table. For each leaf \(L\), let \(b(L)\) be the window endpoint of its incoming edge, and let \[ T_L:\{0,\ldots,N_{b(L)}-1\}\longrightarrow\{0,1\} \] be a table of independent Bernoulli-\(p\) bits. All entries of all selector tables \(S_e\) and terminal tables \(T_L\) are mutually independent. There are finitely many entries, so they define a finite product probability space \(\Omega\), with probability \(\Prob\) and expectation \(\E\). Write \(\mathcal A\) for the sigma-field generated by all entries of all selector tables. → `tableLaw` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/TableDefinitions.lean:96`)
- definition of the paper: Given an outcome and \(z\in\R\), route \(z\) from the root as follows. At an internal vertex \(P\), choose the first child \(P_i\), \(i<M\), whose selector satisfies \(S_{(P,i)}(J_{b_{(P,i)}}(z))=1\). If all these values are zero, choose \(P_M\). Let \(L(z)\) denote the leaf reached and define \begin{equation} \label{eq:random-set} B=\bigl\{z\in\R: T_{L(z)}(J_{b(L(z))}(z))=1\bigr\}. \end{equation} → `randomSet` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/TableDefinitions.lean:254`)
- definition of the paper: For a fixed center \(x\in\R\), expose its addressed entry in \emph{every} selector table, including tables outside its route. Write \begin{equation} \label{eq:center-exposure} \mathcal F_x= \sigma\bigl(S_e(J_{b_e}(x)):e=(P,i),\ i<M\bigr) \subseteq\mathcal A. \end{equation} → `centerExposure` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/TableDefinitions.lean:284`)
- definition of the paper: Let $\mathcal S$ be the set of stable centers. → `IsStableCenter` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/WindowDefinitions.lean:341`)
- condition of the paper: for every window $W_e$ other than the first, writing $b'$ for the endpoint of its immediate predecessor, \[ (x,x+2q^{a_e}]\cap\Gamma_{b'}=\varnothing. \] → `StableCenterCondition` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/WindowDefinitions.lean:315`)
- definition of the paper: If that route uses a default child, let \(U\) be the first vertex where it does so. → `firstDefault` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/TableDefinitions.lean:449`)
- definition of the paper: Now fix a stable center \(x\) and an atom \(\xi\) on which \(U\) exists. Under this conditioning, \(U\) and its height \(h\) are fixed. Put \[ r=r_h,\qquad e_i=(U,i)\quad(1\le i<M),\qquad y_n(t)=x+tq^n\quad(t\in[1,2]). \] → `localIndices` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/Tables.lean:86`)
- definition of the paper: For \(i<M\), let \(L_i(z)\) be the leaf reached by routing \(z\) starting at the child \(U_i\); if this child is a leaf, take \(L_i(z)=U_i\). Define the local test \begin{equation} \label{eq:local-test} Q_i(z)=S_{e_i}(J_{b_{e_i}}(z))\, T_{L_i(z)}(J_{b(L_i(z))}(z)). \end{equation} → `localTest` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/Tables.lean:121`)
- condition of the paper: \label{lem:conditional-scales} Fix $p\in(0,1)$ and the construction parameters $M,d,g,r_0$ of Sections~\ref{sec:windows} and~\ref{sec:routing}. → `ConditionalScalesParameters` (`lean/Papers/OaiGeometricErdosSimilarity/Basic.lean:56`)
- condition of the paper: let $\xi$ be an atom of the center-exposure field $\mathcal F_x$ on which the route of $x$ uses a default edge. → `ConditionalScalesDefaultAtom` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/Tables.lean:42`)
- condition of the paper: If its first default occurs at a vertex $U$ of height $h$, → `ConditionalScalesHeight` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/Tables.lean:53`)
- definition of the paper: For $e=(P,i)$, let $b_e^*$ be the largest endpoint among $W_e$ and all windows in the subtree rooted at $P_i$. → `blockEndpoint` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/WindowDefinitions.lean:288`)
- definition of the paper: put $r=r_h$ and \begin{equation}\label{eq:scale-count} D_{M,q}(r)=4+2(M-1)r\bigl(1+2c q^{-2r}\bigr). \end{equation} → `scaleCount` (`lean/Papers/OaiGeometricErdosSimilarity/Helpers/ScaleDefinitions.lean:20`)

## Identifiers

| Result | run id | paper label | source | Lean declaration |
| --- | --- | --- | --- | --- |
| Theorem 1.1 | `thm:main` | `thm:main` | `sections/01-introduction.tex:17-24` | `Papers.OaiGeometricErdosSimilarity.exists_compact_avoiding_geometric_affine_copies` |
| Proposition 2.1 | `prop:periodic` | `prop:periodic` | `sections/02-periodic.tex:12-19` | `Papers.OaiGeometricErdosSimilarity.exists_open_periodic_hitting_set` |
| Lemma 3.1 | `lem:window-span` | `lem:window-span` | `sections/03-windows.tex:76-81` | `Papers.OaiGeometricErdosSimilarity.blockEndpoint_sub_windowStart_le` |
| Lemma 3.2 | `lem:stability` | `lem:stability` | `sections/03-windows.tex:112-122` | `Papers.OaiGeometricErdosSimilarity.stableSet_measurable_density_and_keys` |
| Lemma 3.3 | `lem:separation` | `lem:separation` | `sections/03-windows.tex:155-162` | `Papers.OaiGeometricErdosSimilarity.gridKey_injective_on_translated_window` |
| Lemma 4.1 | `lem:density` | `lem:density` | `sections/04-routing.tex:48-52` | `Papers.OaiGeometricErdosSimilarity.expected_periodicDensity_randomSet_eq` |
| Lemma 4.2 | `lem:routing` | `lem:routing` | `sections/04-routing.tex:116-127` | `Papers.OaiGeometricErdosSimilarity.localTest_imp_mem_randomSet` |
| Lemma 4.3 | `lem:independent-tests` | `lem:independent-tests` | `sections/04-routing.tex:154-167` | `Papers.OaiGeometricErdosSimilarity.condPr_forall_localTest_false_eq` |
| Lemma 5.1 | `lem:conditional-scales` | `lem:conditional-scales` | `sections/05-scales.tex:11-30` | `Papers.OaiGeometricErdosSimilarity.condPr_exists_scale_miss_le` |

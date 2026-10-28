# Correctness report — oai_geometric_erdos_similarity

**Verdict: NO ERROR FOUND**

**Paper: MINOR ISSUES — no main result is shown false or weakened**

Minor:

- `n`: notation ambiguous; a reading was pinned
- `A`: notation ambiguous; a reading was pinned
- `x`: notation ambiguous; a reading was pinned
- `p`: notation ambiguous; a reading was pinned
- `t`: notation ambiguous; a reading was pinned
- `M`: notation ambiguous; a reading was pinned
- `d`: notation ambiguous; a reading was pinned
- `i`: notation ambiguous; a reading was pinned
- `g`: notation ambiguous; a reading was pinned
- `h`: notation ambiguous; a reading was pinned
- `r_0`: notation ambiguous; a reading was pinned
- `\sigma_h`: notation ambiguous; a reading was pinned
- `b`: notation ambiguous; a reading was pinned
- `\mathcal N`: notation ambiguous; a reading was pinned
- `b'`: notation ambiguous; a reading was pinned
- `L(z)`: notation ambiguous; a reading was pinned
- `B`: notation ambiguous; a reading was pinned
- `\xi`: notation ambiguous; a reading was pinned
- `U`: notation ambiguous; a reading was pinned
- `r`: notation ambiguous; a reading was pinned
- `e_i`: notation ambiguous; a reading was pinned
- `L_i(z)`: notation ambiguous; a reading was pinned
- `Q_i`: notation ambiguous; a reading was pinned
- `\mathcal T_{x,\xi}`: notation ambiguous; a reading was pinned
- `B^+`: notation ambiguous; a reading was pinned
- `R`: notation ambiguous; a reading was pinned
- `V`: notation ambiguous; a reading was pinned
- `\mathcal I`: notation ambiguous; a reading was pinned
- `A_{i,n}`: notation ambiguous; a reading was pinned
- `L_{i,n}`: notation ambiguous; a reading was pinned
- `\kappa_{i,n}`: notation ambiguous; a reading was pinned

9 result(s) of the paper were examined. None was found wrong as printed. In Lean: 9 proved, 0 taken from the literature as cited, 0 not certified, 0 not formalized.

## What was wrong and what was done

No error was found in the results examined.

## Clarifications (not errors)

Nothing in this section is an error of the paper. Each item is something the paper determines but does not say, made explicit so that the statements can be read, and formalized, in one way.

**Notation.**

- $n$: $n$ is a positive integer indexing the power $q^n$. In Lemma~\ref{lem:stability}, Lemma~\ref{lem:separation}: The translated points are indexed by $n\in W_e=[a_e,b_e]\cap\N$ for the edge $e$ under consideration. In Lemma~\ref{lem:routing}, Lemma~\ref{lem:independent-tests}: For each $1\le i<M$, the local tests use $n\in W_{e_i}$, where $e_i=(U,i)$ is fixed on $\xi$. In Lemma~\ref{lem:conditional-scales}: The simultaneous miss event ranges over $n\in\mathcal N=\bigcup_e W_e$; the local tests used in its proof range over $n\in W_{e_i}$ for each $1\le i<M$.
- $A$: $A$ denotes a subset of $\R$. In Theorem~\ref{thm:main}, Proposition~\ref{prop:periodic}, Lemma~\ref{lem:stability}, Lemma~\ref{lem:density}: As the argument of $\rho$, $A$ is Lebesgue-measurable and $1$-periodic, and $\rho(A)=m(A\cap[0,1))$.
- $x$: $x\in\R$ denotes the translation center in the affine points $x+sq^n$, or $x+tq^n$ for normalized dilation. In Lemma~\ref{lem:stability}: The assertion about earlier keys assumes $x\in\mathcal S$. In Lemma~\ref{lem:routing}, Lemma~\ref{lem:independent-tests}, Lemma~\ref{lem:conditional-scales}: $x\in\mathcal S$ is a stable center.
- $p$: $p\in(0,1)$ is the terminal-table Bernoulli parameter and the density budget used in the periodic construction. In Theorem~\ref{thm:main}: For each $k\in\Z$, the construction of $H_k$ uses $p=p_k=(\eta/64)4^{-|k|}$.
- $t$: $t\in[1,2]$ is the normalized dilation parameter in $x+tq^n$. In Lemma~\ref{lem:independent-tests}: The probability identity is evaluated for each $t$ fixed under the conditioning on $\xi$. In Lemma~\ref{lem:conditional-scales}: In the miss event, $t$ ranges existentially over $[1,2]$; each representative $t'\in\mathcal T_{x,\xi}$ used for the conditional probability bound is fixed on $\xi$ before remaining table entries are revealed.
- $M$: $M\ge2$ is a fixed integer giving the number of ordered children at each internal vertex of the complete tree. In Proposition~\ref{prop:periodic}: For the given $p\in(0,1)$ and $q\in(0,1)$, choose $M$ so that $\alpha:=p(M-1)/2>2\log(1/q)$.
- $d$: $d\ge1$ is the fixed integer height of the complete ordered $M$-ary tree. In Proposition~\ref{prop:periodic}: After choosing $M$, the height $d$ is chosen to satisfy $(1-2^{1-M})^d<p$.
- $i$: $i\in\{1,\ldots,M\}$ indexes the ordered children of an internal vertex. In Proposition~\ref{prop:periodic}, Lemma~\ref{lem:density}, Lemma~\ref{lem:routing}, Lemma~\ref{lem:independent-tests}, Lemma~\ref{lem:conditional-scales}: Selector-bearing edges and local tests have $1\le i<M$; child $M$ is the default child and has no selector table.
- $g$: $g\ge1$ is a fixed integer giving exactly the number of unused indices between consecutive windows in preorder. In Proposition~\ref{prop:periodic}: After fixing the tree with $K$ edges, $g$ is chosen to satisfy $4Kc q^{g+1}<p$.
- $h$: $h$ denotes vertex height in the complete tree of height $d$, with leaves of height $0$. In Lemma~\ref{lem:window-span}: $h$ is the height of the vertex from which $e$ leaves, so $1\le h\le d$. In Lemma~\ref{lem:routing}, Lemma~\ref{lem:independent-tests}, Lemma~\ref{lem:conditional-scales}: Where the local notation uses the first default vertex $U$, $h$ is its height, with $1\le h\le d$, and is fixed under conditioning on the center-exposure atom $\xi$.
- $r_0$: $r_0\ge1$ is a fixed integer construction parameter prescribing the lower bound for all window lengths $r_h$. In Proposition~\ref{prop:periodic}: The construction chooses $r_0=r_*$, where $D_{M,q}(r)e^{-p(M-1)r/2}<p$ for every integer $r\ge r_*$.
- $\sigma_h$: $\sigma_h$ is the deterministic span, including intervening gaps, of all windows in a subtree of height $h$, defined for $1\le h\le d$ by the stated recursion.
- $b$: $b$ ranges over the positive integers indexing $N_b$, $\Gamma_b$, and $J_b$. In Lemma~\ref{lem:separation}: In the proof's distance and cell-width estimates, $b=b_e$; the statement also considers every finer index $b\ge b_e$.
- $\mathcal N$: $\mathcal N=\bigcup_e W_e$ is the finite union over all edges of the constructed tree, consisting of positive integer indices beginning at $n_0\ge1$, where $2q^{n_0}\le1/4$. In Proposition~\ref{prop:periodic}: $\mathcal N$ is the finite index collection used to define $R$; the indices used to hit the open neighborhood $V$ may instead be any sufficiently large integers $n\ge1$.
- $b'$: $b'$ is a positive integer grid index, ranging over $b'\ge b$ in the nesting relation and denoting the endpoint of the immediate predecessor of $W_e$ in the stability condition for a noninitial window.
- $L(z)$: For each fixed $z\in\R$, $L(z)$ is the selector-dependent leaf reached from the root by the stated routing rule; it is $\mathcal A$-measurable and is fixed upon conditioning on $\mathcal A$.
- $B$: $B=\{z\in\R:T_{L(z)}(J_{b(L(z))}(z))=1\}$, with routing and terminal membership evaluated in the same table outcome, and each realization is $1$-periodic and a union of finitely many half-open grid cells per period. In Proposition~\ref{prop:periodic}: After the expectation estimates, one table outcome is fixed with $\rho(B^+)+\rho(R)\le5p$, and the subsequent construction uses its realization of $B$.
- $\xi$: $\xi$ is a fixed positive-probability atom of $\mathcal F_x$, specifying the addressed selector entry at $x$ in every selector table; conditioning on $\xi$ means conditioning on this event. In Lemma~\ref{lem:routing}, Lemma~\ref{lem:independent-tests}, Lemma~\ref{lem:conditional-scales}: $x$ is stable and $\xi$ admits a default choice on the route of $x$; its first default vertex $U$ and height $h$ are fixed on $\xi$.
- $U$: $U$ is the $\mathcal F_x$-determined first internal vertex at which the route of $x$ chooses the default child, defined only when that route has a default choice; on any atom $\xi$ admitting $U$, both $U$ and its height $h\in\{1,\ldots,d\}$ are fixed.
- $r$: $r$ is a positive integer length parameter. In Lemma~\ref{lem:routing}, Lemma~\ref{lem:independent-tests}, Lemma~\ref{lem:conditional-scales}: In the local notation for an atom $\xi$ admitting a first default vertex $U$ of height $h$, $r=r_h$; this length is fixed under the conditioning on $\xi$. In Proposition~\ref{prop:periodic}: In the threshold choice, $r$ ranges over all integers $r\ge r_*$; when the conditional scale estimate is applied on a center-exposure atom, its length argument is $r=r_h\ge r_*$.
- $e_i$: $e_i=(U,i)$, $1\le i<M$, denotes an outgoing nondefault edge of the first default vertex $U$ of the center $x$; these edges are defined when $U$ exists and are fixed on an atom $\xi$ of $\mathcal F_x$ admitting $U$.
- $L_i(z)$: For $z\in\R$ and $1\le i<M$, with $U$ fixed by an atom $\xi$ admitting a first default, $L_i(z)$ is the leaf obtained by routing $z$ from $U_i$ using the selectors in that child subtree, with $L_i(z)=U_i$ when $U_i$ is a leaf.
- $Q_i$: For a stable center $x$ and a fixed atom $\xi$ admitting a first default vertex $U$, $Q_i$ is the table-dependent binary function on $\R$ defined by \eqref{eq:local-test}, indexed by $1\le i<M$, with $e_i=(U,i)$ and routing for $L_i(z)$ starting at $U_i$.
- $\mathcal T_{x,\xi}$: $\mathcal T_{x,\xi}$ is a finite subset of $[1,2]$ determined solely by $x$, the deterministic windows and grids, and the first default vertex $U$ determined by $\xi$, and is fixed conditional on $\xi$ before any remaining table entries are revealed.
- $B^+$: For each table outcome, $B^+$ is an open $1$-periodic enlargement of that outcome's set $B$, satisfying $B\subseteq B^+$ and $\rho(B^+)\le\rho(B)+p$.
- $R$: For each table outcome and its chosen enlargement $B^+$, $R=\{x\in\R:\exists t\in[1,2]\ \forall n\in\mathcal N,\ x+tq^n\notin B^+\}$ is a closed $1$-periodic set of centers.
- $V$: $V$ is an open $1$-periodic superset of $R$, chosen after fixing a table outcome satisfying $\rho(B^+)+\rho(R)\le5p$, with $\rho(V)\le\rho(R)+p$.
- $\mathcal I$: $\mathcal I=\{(i,n):1\le i<M,\ n\in W_{e_i}\}$, with $e_i=(U,i)$ for the first-default vertex $U$, is fixed on each conditioning atom $\xi$ admitting a first default and has cardinality $(M-1)r_h$, where $h$ is the height of $U$.
- $A_{i,n}$: $A_{i,n}=S_{e_i}(J_{b_{e_i}}(y_n(t)))$ is defined for $1\le i<M$ and $n\in W_{e_i}$. In Lemma~\ref{lem:independent-tests}: For a stable center $x$, an atom $\xi$ of $\mathcal F_x$ admitting a first default, and a scale $t\in[1,2]$ fixed under this conditioning, the index set $\mathcal I=\{(i,n):1\le i<M,\ n\in W_{e_i}\}$ is fixed and has cardinality $(M-1)r_h$; its entries $A_{i,n}$ consult pairwise distinct selector entries, none exposed at $x$.
- $L_{i,n}$: For $1\le i<M$ and $n\in W_{e_i}$, $L_{i,n}=L_i(y_n(t))$ is the selector-dependent leaf reached by routing $y_n(t)$ from $U_i$. In Lemma~\ref{lem:independent-tests}: With $t$ fixed on $\xi$, conditioning further on $\mathcal A$ fixes $L_{i,n}$.
- $\kappa_{i,n}$: For $1\le i<M$ and $n\in W_{e_i}$, $\kappa_{i,n}=(L_i(y_n(t)),J_{b(L_i(y_n(t)))}(y_n(t)))$ is a selector-dependent terminal address. In Lemma~\ref{lem:independent-tests}: With $t$ fixed on $\xi$, conditioning further on $\mathcal A$ fixes $\kappa_{i,n}$.

## What was proved in Lean, and what was not

A result is proved in Lean when a Lean declaration reviewed as stating it has a complete proof using no axiom beyond the standard ones. For a corrected result, the corrected statement is the one formalized.

| Result | Formal status | Lean declaration | Axioms |
| --- | --- | --- | --- |
| Theorem 1.1 | proved in Lean | `Papers.OaiGeometricErdosSimilarity.exists_compact_avoiding_geometric_affine_copies` (`TMain.lean:451`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Proposition 2.1 | proved in Lean | `Papers.OaiGeometricErdosSimilarity.exists_open_periodic_hitting_set` (`TPeriodic.lean:588`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Lemma 3.1 | proved in Lean | `Papers.OaiGeometricErdosSimilarity.blockEndpoint_sub_windowStart_le` (`Helpers/Windows.lean:145`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Lemma 3.2 | proved in Lean | `Papers.OaiGeometricErdosSimilarity.stableSet_measurable_density_and_keys` (`Helpers/Stability.lean:332`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Lemma 3.3 | proved in Lean | `Papers.OaiGeometricErdosSimilarity.gridKey_injective_on_translated_window` (`Helpers/Windows.lean:249`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Lemma 4.1 | proved in Lean | `Papers.OaiGeometricErdosSimilarity.expected_periodicDensity_randomSet_eq` (`Helpers/Tables.lean:366`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Lemma 4.2 | proved in Lean | `Papers.OaiGeometricErdosSimilarity.localTest_imp_mem_randomSet` (`Helpers/LocalRouting.lean:307`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Lemma 4.3 | proved in Lean | `Papers.OaiGeometricErdosSimilarity.condPr_forall_localTest_false_eq` (`Helpers/Routing.lean:620`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Lemma 5.1 | proved in Lean | `Papers.OaiGeometricErdosSimilarity.condPr_exists_scale_miss_le` (`Helpers/Scales.lean:92`) | the standard ones only (propext, Classical.choice, Quot.sound) |

The Lean development builds; it contains no `sorry`, `admit` or added axiom.

## The corrected paper

`bundle/corrected_paper/` holds the paper as it reads after the corrections, as plain source in the author's own class and layout, compiled to `bundle/corrected_paper/main.pdf` (15 pages). `bundle/MATCH.md` sets each result beside its Lean declaration; `bundle/lean/` holds the Lean code.

The mechanical checks leave nothing open.

# Technical appendix

The records behind the report above, by the run's own identifiers.

- paper: `main.tex` (source sha256 `53b39e3044690d96ced06638f4208a69a1565795c54908fea299e71143c6511f`)
- stage completed: `5`
- results in scope: 9

| bucket | count |
| --- | --- |
| verified | 9 |
| verified_with_bookkeeping | 0 |
| conditional | 0 |
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
| bucket | `verified` |
| source | `sections/01-introduction.tex:17-24` (`theorem`, label `thm:main`) |
| statement | \label{thm:main} For every $q\in(0,1)$ and $\eta\in(0,1)$, there is a compact set $E_{q,\eta}\subseteq[0,1]$ with $m(E_{q,\eta})>1-\eta$ such that \[ \text{for every }x\in\R\text{ and }s\in\R\setminus\{0\}, \quad x+sq^n\notin E_{q,\eta}\text{ for some integer }n\ge1. \] |
| Lean | `TMain.lean:451` — `Papers.OaiGeometricErdosSimilarity.exists_compact_avoiding_geometric_affine_copies` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 2. `prop:periodic`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `sections/02-periodic.tex:12-19` (`proposition`, label `prop:periodic`) |
| statement | \label{prop:periodic} For every $p\in(0,1)$, there is an open $1$-periodic set $H\subseteq\R$ with $\rho(H)\le6p$ such that \begin{equation}\label{eq:periodic-hitting} \text{for every }x\in\R\text{ and }t\in[1,2], \quad x+tq^n\in H\text{ for some integer }n\ge1. \end{equation} |
| Lean | `TPeriodic.lean:588` — `Papers.OaiGeometricErdosSimilarity.exists_open_periodic_hitting_set` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 3. Span of an edge and its child subtree `lem:window-span`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `sections/03-windows.tex:76-81` (`lemma`, label `lem:window-span`) |
| statement | \label{lem:window-span} If $e=(P,i)$ leaves a vertex of height $h$, then \begin{equation}\label{eq:window-span} b_e^*-a_e+1\le2r_h. \end{equation} |
| appended hypothesis list | ass:window-span-height |
| Lean | `Helpers/Windows.lean:145` — `Papers.OaiGeometricErdosSimilarity.blockEndpoint_sub_windowStart_le` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 4. Stability and earlier keys `lem:stability`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `sections/03-windows.tex:112-122` (`lemma`, label `lem:stability`) |
| statement | \label{lem:stability} The set $\mathcal S$ is measurable and $1$-periodic, and \[ \rho(\R\setminus\mathcal S)\le4Kc\,q^{g+1}. \] If $x\in\mathcal S$, $n\in W_e$, and $t\in[1,2]$, then every edge $f$ preceding $e$ in preorder satisfies \begin{equation}\label{eq:stable-keys} J_{b_f}(x+tq^n)=J_{b_f}(x). \end{equation} |
| Lean | `Helpers/Stability.lean:332` — `Papers.OaiGeometricErdosSimilarity.stableSet_measurable_density_and_keys` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 5. Separation within one window `lem:separation`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `sections/03-windows.tex:155-162` (`lemma`, label `lem:separation`) |
| statement | \label{lem:separation} Fix an edge $e$, a center $x\in\R$, and a scale $t\in[1,2]$. The points \[ \{x\}\ \cup\ \{x+tq^n:n\in W_e\} \] have pairwise distinct keys under $J_{b_e}$. They also have pairwise distinct keys under every $J_b$ with $b\ge b_e$. |
| appended hypothesis list | ass:separation-parameters |
| Lean | `Helpers/Windows.lean:249` — `Papers.OaiGeometricErdosSimilarity.gridKey_injective_on_translated_window` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 6. Mean density `lem:density`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `sections/04-routing.tex:48-52` (`lemma`, label `lem:density`) |
| statement | \label{lem:density} The random set \(B\) in \eqref{eq:random-set} satisfies \(\E\rho(B)=p\). |
| Lean | `Helpers/Tables.lean:366` — `Papers.OaiGeometricErdosSimilarity.expected_periodicDensity_randomSet_eq` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | [note, F2.5] [statement-wrong] The referenced frozen window construction says only to choose n₀≥1 with 2q^n₀≤1/4, admitting an arbitrary admissible parameter or a selected construction; Lean selects ⌈log(1/8)/log q⌉₊+1. Edit the frozen setup to settle selection versus quantification before synchronizing all three targets. (rewind rejected by the orchestrator on lem:density: The setup in Section~\ref{sec:windows} already specifies $n_0\ge1$ and $2q^{n_0}\le1/4$, followed by the prescribed window placement. The later lemmas use that construction and do not require a unique logarithmic choice. The reviewer identified specialization in Lean, not a defect in the paper: expose every admissible $n_0$ in the window-dependent Lean API and thread the printed conditions. Use the logarithmic formula only as a proved internal witness when constructing the periodic hitting set. This preserves every printed statement and adds no main-result hypothesis; no source or frozen-text edit is warranted.) |

### 7. Preservation of routing `lem:routing`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `sections/04-routing.tex:116-127` (`lemma`, label `lem:routing`) |
| statement | \label{lem:routing} Fix a stable center \(x\) and an atom \(\xi\) of \(\mathcal F_x\) on which the first default vertex \(U\) exists. For every outcome in \(\xi\), every \(i<M\), every \(n\in W_{e_i}\), and every \(t\in[1,2]\), the route of \(y_n(t)\) reaches \(U\) and rejects its children \(1,\ldots,i-1\). Consequently, \begin{equation} \label{eq:local-hit} Q_i(y_n(t))=1\quad\Longrightarrow\quad y_n(t)\in B. \end{equation} |
| appended hypothesis list | ass:stable-center-condition, ass:routing-default-atom |
| Lean | `Helpers/LocalRouting.lean:307` — `Papers.OaiGeometricErdosSimilarity.localTest_imp_mem_randomSet` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 8. Independent tests `lem:independent-tests`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `sections/04-routing.tex:154-167` (`lemma`, label `lem:independent-tests`) |
| statement | \label{lem:independent-tests} Fix a stable center \(x\) and an atom \(\xi\) of \(\mathcal F_x\) on which the first default vertex \(U\) exists. Let \(h\) be its height and \(r=r_h\), and define \(Q_i\) by \eqref{eq:local-test}. For every fixed \(t\in[1,2]\), \begin{equation} \label{eq:test-failure} \Prob\left( Q_i(y_n(t))=0\text{ for all }i<M,\ n\in W_{e_i} \,\middle\|\,\xi\right) =(1-p/2)^{(M-1)r}. \end{equation} |
| appended hypothesis list | ass:stable-center-condition, ass:independent-tests-default-atom |
| Lean | `Helpers/Routing.lean:620` — `Papers.OaiGeometricErdosSimilarity.condPr_forall_localTest_false_eq` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 9. Conditional control of all normalized scales `lem:conditional-scales`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `sections/05-scales.tex:11-30` (`lemma`, label `lem:conditional-scales`) |
| statement | \label{lem:conditional-scales} Fix $p\in(0,1)$ and the construction parameters $M,d,g,r_0$ of Sections~\ref{sec:windows} and~\ref{sec:routing}. Let $x\in\mathcal S$ be a stable center, and let $\xi$ be an atom of the center-exposure field $\mathcal F_x$ on which the route of $x$ uses a default edge. If its first default occurs at a vertex $U$ of height $h$, put $r=r_h$ and \begin{equation}\label{eq:scale-count} D_{M,q}(r)=4+2(M-1)r\bigl(1+2c q^{-2r}\bigr). \end{equation} Then \begin{equation}\label{eq:conditional-scales} \Prob\!\left( \exists t\in[1,2]\ \forall n\in\mathcal N:\ x+tq^n\notin B\ \middle\|\ \xi \right) \le D_{M,q}(r)e^{-p(M-1)r/2}. \end{equation} |
| appended hypothesis list | ass:conditional-scales-parameters, ass:stable-center-condition, ass:conditional-scales-default-atom, ass:conditional-scales-height |
| Lean | `Helpers/Scales.lean:92` — `Papers.OaiGeometricErdosSimilarity.condPr_exists_scale_miss_le` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

## Suggestions to the authors

Not errors: readings the paper determines but does not state, and side conditions the proofs use silently.

- reading of the symbol `n`: $n$ is a positive integer indexing the power $q^n$. In Lemma~\ref{lem:stability}, Lemma~\ref{lem:separation}: The translated points are indexed by $n\in W_e=[a_e,b_e]\cap\N$ for the edge $e$ under consideration. In Lemma~\ref{lem:routing}, Lemma~\ref{lem:independent-tests}: For each $1\le i<M$, the local tests use $n\in W_{e_i}$, where $e_i=(U,i)$ is fixed on $\xi$. In Lemma~\ref{lem:conditional-scales}: The simultaneous miss event ranges over $n\in\mathcal N=\bigcup_e W_e$; the local tests used in its proof range over $n\in W_{e_i}$ for each $1\le i<M$. — The definition of $G_q$ specifies $n\ge1$; Lemmas~\ref{lem:stability} and~\ref{lem:separation} use one edge window, Lemmas~\ref{lem:routing} and~\ref{lem:independent-tests} use the local windows, and Lemma~\ref{lem:conditional-scales} uses $\mathcal N$ in its miss event.
- reading of the symbol `A`: $A$ denotes a subset of $\R$. In Theorem~\ref{thm:main}, Proposition~\ref{prop:periodic}, Lemma~\ref{lem:stability}, Lemma~\ref{lem:density}: As the argument of $\rho$, $A$ is Lebesgue-measurable and $1$-periodic, and $\rho(A)=m(A\cap[0,1))$. — The introduction begins with an unrestricted set $A\subseteq\R$ in the definition of measure universality. The paragraph defining $\rho$ explicitly restricts its argument to measurable, $1$-periodic sets.
- reading of the symbol `x`: $x\in\R$ denotes the translation center in the affine points $x+sq^n$, or $x+tq^n$ for normalized dilation. In Lemma~\ref{lem:stability}: The assertion about earlier keys assumes $x\in\mathcal S$. In Lemma~\ref{lem:routing}, Lemma~\ref{lem:independent-tests}, Lemma~\ref{lem:conditional-scales}: $x\in\mathcal S$ is a stable center. — The introductory affine-copy notation and Proposition~\ref{prop:periodic} allow every real center. Lemma~\ref{lem:stability} makes its earlier-key assertion conditional on stability, and the routing and conditional-testing arguments use stable centers.
- reading of the symbol `p`: $p\in(0,1)$ is the terminal-table Bernoulli parameter and the density budget used in the periodic construction. In Theorem~\ref{thm:main}: For each $k\in\Z$, the construction of $H_k$ uses $p=p_k=(\eta/64)4^{-\|k\|}$. — Proposition~\ref{prop:periodic} quantifies over $p\in(0,1)$; the terminal tables use this same parameter. The proof of Theorem~\ref{thm:main} explicitly applies the proposition with $p=p_k$.
- reading of the symbol `t`: $t\in[1,2]$ is the normalized dilation parameter in $x+tq^n$. In Lemma~\ref{lem:independent-tests}: The probability identity is evaluated for each $t$ fixed under the conditioning on $\xi$. In Lemma~\ref{lem:conditional-scales}: In the miss event, $t$ ranges existentially over $[1,2]$; each representative $t'\in\mathcal T_{x,\xi}$ used for the conditional probability bound is fixed on $\xi$ before remaining table entries are revealed. — Lemma~\ref{lem:independent-tests} specifies every fixed $t$, and the paragraph after its proof allows a scale fixed on the atom; the proof of Lemma~\ref{lem:conditional-scales} constructs $\mathcal T_{x,\xi}$ before revealing remaining table entries.
- reading of the symbol `M`: $M\ge2$ is a fixed integer giving the number of ordered children at each internal vertex of the complete tree. In Proposition~\ref{prop:periodic}: For the given $p\in(0,1)$ and $q\in(0,1)$, choose $M$ so that $\alpha:=p(M-1)/2>2\log(1/q)$. — Section~\ref{sec:windows} declares the construction integers arbitrary and fixed. The proof of Proposition~\ref{prop:periodic} then chooses $M$ to satisfy \eqref{eq:branching-choice}.
- reading of the symbol `d`: $d\ge1$ is the fixed integer height of the complete ordered $M$-ary tree. In Proposition~\ref{prop:periodic}: After choosing $M$, the height $d$ is chosen to satisfy $(1-2^{1-M})^d<p$. — Section~\ref{sec:windows} declares $d$ arbitrary and fixed and constructs the tree of height $d$. The proof of Proposition~\ref{prop:periodic} chooses $d$ to satisfy $(1-2^{1-M})^d<p$.
- reading of the symbol `i`: $i\in\{1,\ldots,M\}$ indexes the ordered children of an internal vertex. In Proposition~\ref{prop:periodic}, Lemma~\ref{lem:density}, Lemma~\ref{lem:routing}, Lemma~\ref{lem:independent-tests}, Lemma~\ref{lem:conditional-scales}: Selector-bearing edges and local tests have $1\le i<M$; child $M$ is the default child and has no selector table. — The ordered-tree construction gives all child indices; the random-table and routing definitions reserve child $M$ for the default choice and define selectors and local tests only for $i<M$.
- reading of the symbol `g`: $g\ge1$ is a fixed integer giving exactly the number of unused indices between consecutive windows in preorder. In Proposition~\ref{prop:periodic}: After fixing the tree with $K$ edges, $g$ is chosen to satisfy $4Kc q^{g+1}<p$. — Section~\ref{sec:windows} declares $g$ arbitrary and fixed and prescribes exactly $g$ unused indices. The proof of Proposition~\ref{prop:periodic} chooses it after fixing the tree so that $4Kc q^{g+1}<p$.
- reading of the symbol `h`: $h$ denotes vertex height in the complete tree of height $d$, with leaves of height $0$. In Lemma~\ref{lem:window-span}: $h$ is the height of the vertex from which $e$ leaves, so $1\le h\le d$. In Lemma~\ref{lem:routing}, Lemma~\ref{lem:independent-tests}, Lemma~\ref{lem:conditional-scales}: Where the local notation uses the first default vertex $U$, $h$ is its height, with $1\le h\le d$, and is fixed under conditioning on the center-exposure atom $\xi$. — The tree construction assigns leaves height zero. Lemma~\ref{lem:window-span} takes the height of the parent of an edge. The local notation and Lemmas~\ref{lem:independent-tests} and~\ref{lem:conditional-scales} take the height of the first default vertex fixed by $\xi$.
- reading of the symbol `r_0`: $r_0\ge1$ is a fixed integer construction parameter prescribing the lower bound for all window lengths $r_h$. In Proposition~\ref{prop:periodic}: The construction chooses $r_0=r_*$, where $D_{M,q}(r)e^{-p(M-1)r/2}<p$ for every integer $r\ge r_*$. — Section~\ref{sec:windows} declares $r_0$ arbitrary and fixed and defines the lengths using it. The proof of Proposition~\ref{prop:periodic} says to construct the windows with $r_0=r_*$.
- reading of the symbol `\sigma_h`: $\sigma_h$ is the deterministic span, including intervening gaps, of all windows in a subtree of height $h$, defined for $1\le h\le d$ by the stated recursion. — Section~\ref{sec:windows} introduces the subtree span at height one and recursively constructs the lengths and spans upward through height $d$.
- reading of the symbol `b`: $b$ ranges over the positive integers indexing $N_b$, $\Gamma_b$, and $J_b$. In Lemma~\ref{lem:separation}: In the proof's distance and cell-width estimates, $b=b_e$; the statement also considers every finer index $b\ge b_e$. — The grid construction begins "For each integer $b\ge1$". The separation statement considers every $b\ge b_e$, while its proof begins "Write $b=b_e$."
- reading of the symbol `\mathcal N`: $\mathcal N=\bigcup_e W_e$ is the finite union over all edges of the constructed tree, consisting of positive integer indices beginning at $n_0\ge1$, where $2q^{n_0}\le1/4$. In Proposition~\ref{prop:periodic}: $\mathcal N$ is the finite index collection used to define $R$; the indices used to hit the open neighborhood $V$ may instead be any sufficiently large integers $n\ge1$. — The window construction chooses the first starting index $n_0\ge1$, places subsequent windows with the prescribed lengths and gaps, and then defines the union over edges.
- reading of the symbol `b'`: $b'$ is a positive integer grid index, ranging over $b'\ge b$ in the nesting relation and denoting the endpoint of the immediate predecessor of $W_e$ in the stability condition for a noninitial window. — The grid discussion states "if $b'\ge b$" before the nesting identity; the stable-center definition separately specifies $b'$ as the predecessor endpoint.
- reading of the symbol `L(z)`: For each fixed $z\in\R$, $L(z)$ is the selector-dependent leaf reached from the root by the stated routing rule; it is $\mathcal A$-measurable and is fixed upon conditioning on $\mathcal A$. — The definition preceding \eqref{eq:random-set} specifies routing given an outcome and $z$; the proof of Lemma~\ref{lem:density} explicitly says that conditioning on $\mathcal A$ fixes the leaf and terminal address.
- reading of the symbol `B`: $B=\{z\in\R:T_{L(z)}(J_{b(L(z))}(z))=1\}$, with routing and terminal membership evaluated in the same table outcome, and each realization is $1$-periodic and a union of finitely many half-open grid cells per period. In Proposition~\ref{prop:periodic}: After the expectation estimates, one table outcome is fixed with $\rho(B^+)+\rho(R)\le5p$, and the subsequent construction uses its realization of $B$. — Equation~\eqref{eq:random-set} defines B given an outcome; its following paragraph states the periodicity and finite half-open-cell structure. The final construction later chooses one outcome.
- reading of the symbol `\xi`: $\xi$ is a fixed positive-probability atom of $\mathcal F_x$, specifying the addressed selector entry at $x$ in every selector table; conditioning on $\xi$ means conditioning on this event. In Lemma~\ref{lem:routing}, Lemma~\ref{lem:independent-tests}, Lemma~\ref{lem:conditional-scales}: $x$ is stable and $\xi$ admits a default choice on the route of $x$; its first default vertex $U$ and height $h$ are fixed on $\xi$. — The paragraph following \eqref{eq:center-exposure} states that every atom specifies these entries and has positive probability; the local construction and the hypotheses of Lemmas~\ref{lem:routing},~\ref{lem:independent-tests}, and~\ref{lem:conditional-scales} impose the first-default restriction.
- reading of the symbol `U`: $U$ is the $\mathcal F_x$-determined first internal vertex at which the route of $x$ chooses the default child, defined only when that route has a default choice; on any atom $\xi$ admitting $U$, both $U$ and its height $h\in\{1,\ldots,d\}$ are fixed. — The first-default definition states that the exposure determines the entire route, and the paragraph introducing the local indices explicitly fixes $U$ and its height under conditioning.
- reading of the symbol `r`: $r$ is a positive integer length parameter. In Lemma~\ref{lem:routing}, Lemma~\ref{lem:independent-tests}, Lemma~\ref{lem:conditional-scales}: In the local notation for an atom $\xi$ admitting a first default vertex $U$ of height $h$, $r=r_h$; this length is fixed under the conditioning on $\xi$. In Proposition~\ref{prop:periodic}: In the threshold choice, $r$ ranges over all integers $r\ge r_*$; when the conditional scale estimate is applied on a center-exposure atom, its length argument is $r=r_h\ge r_*$. — The local notation preceding Lemma~\ref{lem:independent-tests} sets $r=r_h$ after fixing the center-exposure atom; Lemma~\ref{lem:conditional-scales} repeats this convention. Equation~\eqref{eq:window-length-choice} instead quantifies over every integer $r\ge r_*$.
- reading of the symbol `e_i`: $e_i=(U,i)$, $1\le i<M$, denotes an outgoing nondefault edge of the first default vertex $U$ of the center $x$; these edges are defined when $U$ exists and are fixed on an atom $\xi$ of $\mathcal F_x$ admitting $U$. — The paragraph introducing the local indices fixes a stable center and an atom admitting $U$ before defining $e_i$; the proof of Lemma~\ref{lem:conditional-scales} explicitly recalls that these edges are fixed on the atom.
- reading of the symbol `L_i(z)`: For $z\in\R$ and $1\le i<M$, with $U$ fixed by an atom $\xi$ admitting a first default, $L_i(z)$ is the leaf obtained by routing $z$ from $U_i$ using the selectors in that child subtree, with $L_i(z)=U_i$ when $U_i$ is a leaf. — The local construction fixes $U$ on $\xi$ and defines routing from $U_i$; the proof of Lemma~\ref{lem:independent-tests} explicitly fixes the resulting leaves by conditioning on all selectors.
- reading of the symbol `Q_i`: For a stable center $x$ and a fixed atom $\xi$ admitting a first default vertex $U$, $Q_i$ is the table-dependent binary function on $\R$ defined by \eqref{eq:local-test}, indexed by $1\le i<M$, with $e_i=(U,i)$ and routing for $L_i(z)$ starting at $U_i$. — The local construction immediately before \eqref{eq:local-test} fixes the stable center, atom, first default vertex, and index range, and defines routing from the child.
- reading of the symbol `\mathcal T_{x,\xi}`: $\mathcal T_{x,\xi}$ is a finite subset of $[1,2]$ determined solely by $x$, the deterministic windows and grids, and the first default vertex $U$ determined by $\xi$, and is fixed conditional on $\xi$ before any remaining table entries are revealed. — The proof of Lemma~\ref{lem:conditional-scales} specifies the lattice boundary lists and explicitly states these dependencies and the order of revelation.
- reading of the symbol `B^+`: For each table outcome, $B^+$ is an open $1$-periodic enlargement of that outcome's set $B$, satisfying $B\subseteq B^+$ and $\rho(B^+)\le\rho(B)+p$. — The enlargement paragraph explicitly begins with each table outcome and enlarges its finitely many selected cells per period before defining R.
- reading of the symbol `R`: For each table outcome and its chosen enlargement $B^+$, $R=\{x\in\R:\exists t\in[1,2]\ \forall n\in\mathcal N,\ x+tq^n\notin B^+\}$ is a closed $1$-periodic set of centers. — The paragraph introducing equation~\eqref{eq:exceptional-centers} specifies the enlargement for each outcome; the following paragraph proves that R is closed and periodic.
- reading of the symbol `V`: $V$ is an open $1$-periodic superset of $R$, chosen after fixing a table outcome satisfying $\rho(B^+)+\rho(R)\le5p$, with $\rho(V)\le\rho(R)+p$. — The proof first chooses a table outcome with the stated density bound and then obtains $V$ by outer regularity on the circle.
- reading of the symbol `\mathcal I`: $\mathcal I=\{(i,n):1\le i<M,\ n\in W_{e_i}\}$, with $e_i=(U,i)$ for the first-default vertex $U$, is fixed on each conditioning atom $\xi$ admitting a first default and has cardinality $(M-1)r_h$, where $h$ is the height of $U$. — The proof of Lemma~\ref{lem:independent-tests} explicitly states that on $\xi$ the index set is fixed and has cardinality $(M-1)r$, with $r=r_h$.
- reading of the symbol `A_{i,n}`: $A_{i,n}=S_{e_i}(J_{b_{e_i}}(y_n(t)))$ is defined for $1\le i<M$ and $n\in W_{e_i}$. In Lemma~\ref{lem:independent-tests}: For a stable center $x$, an atom $\xi$ of $\mathcal F_x$ admitting a first default, and a scale $t\in[1,2]$ fixed under this conditioning, the index set $\mathcal I=\{(i,n):1\le i<M,\ n\in W_{e_i}\}$ is fixed and has cardinality $(M-1)r_h$; its entries $A_{i,n}$ consult pairwise distinct selector entries, none exposed at $x$. — The proof of Lemma~\ref{lem:independent-tests} defines the index set on $\xi$, fixes the scale, and identifies the distinct, unexposed selector entries consulted.
- reading of the symbol `L_{i,n}`: For $1\le i<M$ and $n\in W_{e_i}$, $L_{i,n}=L_i(y_n(t))$ is the selector-dependent leaf reached by routing $y_n(t)$ from $U_i$. In Lemma~\ref{lem:independent-tests}: With $t$ fixed on $\xi$, conditioning further on $\mathcal A$ fixes $L_{i,n}$. — The proof of Lemma~\ref{lem:independent-tests} defines $L_{i,n}$ immediately after conditioning on the selector sigma-field $\mathcal A$.
- reading of the symbol `\kappa_{i,n}`: For $1\le i<M$ and $n\in W_{e_i}$, $\kappa_{i,n}=(L_i(y_n(t)),J_{b(L_i(y_n(t)))}(y_n(t)))$ is a selector-dependent terminal address. In Lemma~\ref{lem:independent-tests}: With $t$ fixed on $\xi$, conditioning further on $\mathcal A$ fixes $\kappa_{i,n}$. — The proof of Lemma~\ref{lem:independent-tests} defines the pair index set and then conditions on $\mathcal A$ before defining the terminal addresses.

## Added conditions

None: no condition was added to the paper's own hypotheses.

## Conditions assumed

### Cited results

None: no result rests on a theorem imported from the literature.

### Deferred substrate gates

None: every substrate this run needed was built and proved.

## Unresolved / notes

- run-level `symbol E_{q,\eta}`: [note, V1.5] symbol table corrected: def "$E_{q,\eta}=[0,1]\setminus C$." (The recorded entry gives the required properties but omits the explicit complement definition used in the proof. The construction supplies the previously asserted existential witness, rather than changing its meaning.)
- run-level `symbol A`: [note, V1.5] symbol table corrected: type "set" (The introductory pattern $A$ need not be measurable. The later periodic-density notation uses the same letter for a measurable, $1$-periodic set; the recorded definition recognizes this distinction, but the recorded type does not.)
- run-level `symbol T_L`: [note, V1.5] symbol table corrected: type "random terminal table", def "For each leaf $L$, let $b(L)$ be the window endpoint of its incoming edge, and let $T_L:\{0,\ldots,N_{b(L)}-1\}\longrightarrow\{0,1\}$ be a table of independent Bernoulli-$p$ bits. All entries of all selector tables $S_e$ and terminal tables $T_L$ are mutually independent." (The recorded membership-table label omits the paper's defining random-table law. The domain is correct; the definition must specify independent Bernoulli-$p$ entries and their mutual independence with the other tables.)
- run-level `symbol W_e`: [note, V1.5] symbol table corrected: def "$W_e=[a_e,b_e]\cap\N$ is assigned to each edge in preorder, leaving exactly $g$ unused indices between consecutive windows. An edge leaving a vertex of height $h$ receives a window of length $r_h$, where $r_1=r_0$, $\sigma_1=Mr_1+(M-1)g$, and, for $2\le h\le d$, $r_h=\max\{r_0,g+\sigma_{h-1}\}$ and $\sigma_h=M(r_h+g+\sigma_{h-1})+(M-1)g$. The first window starts at a chosen $n_0\ge1$ satisfying $2q^{n_0}\le1/4$, and subsequent windows have the prescribed lengths and gaps." (The recorded interval notation is correct but omits the prescribed lengths, gaps, and starting-index condition that distinguish these windows from arbitrary preorder intervals. The later subtree-endpoint definition does not redefine them.)
- run-level `symbol b'`: [note, V1.5] symbol table corrected: type "grid index or preceding window endpoint", def "In grid nesting, $b'$ is an integer satisfying $b'\ge b$; in the stability condition for a noninitial window $W_e$, $b'$ is the endpoint of its immediate predecessor." (The recorded definition covers only the predecessor endpoint. The paper also uses the same notation for an arbitrary finer grid index; these are context-dependent uses rather than a change to the grid construction.)
- run-level `symbol S_e`: [note, V1.5] symbol table corrected: type "random selector table", def "For each edge $e=(P,i)$ with $1\le i<M$, $S_e:\{0,\ldots,N_{b_e}-1\}\longrightarrow\{0,1\}$ is a table of independent fair bits. Child $M$ is the default child and has no selector table. All entries of all selector tables $S_e$ and terminal tables $T_L$ are mutually independent." (The recorded domain is correct, but attachment to an edge alone omits the defining random-table law. The finite-table setting already records the exposure and conditional laws.)
- run-level `symbol \mathcal T_{x,\xi}`: [note, V1.5] symbol table corrected: def "For every $1\le i<M$ and $n\in W_{e_i}$, record all $t\in[1,2]$ for which $x+tq^n\in\Gamma_{b_{e_i}^*}$. Combine these lists, add $1$ and $2$, and retain the distinct values in increasing order. Let $\mathcal T_{x,\xi}$ consist of these values together with one midpoint between each consecutive pair." (The recorded definition leaves the boundary scales unspecified. The paper uses crossings of the child-subtree finest lattice, includes both endpoints, and adds midpoints; the representatives cannot depend on unrevealed table entries.)
- note on `lem:density`: [statement-wrong] The referenced frozen window construction says only to choose n₀≥1 with 2q^n₀≤1/4, admitting an arbitrary admissible parameter or a selected construction; Lean selects ⌈log(1/8)/log q⌉₊+1. Edit the frozen setup to settle selection versus quantification before synchronizing all three targets. (rewind rejected by the orchestrator on lem:density: The setup in Section~\ref{sec:windows} already specifies $n_0\ge1$ and $2q^{n_0}\le1/4$, followed by the prescribed window placement. The later lemmas use that construction and do not require a unique logarithmic choice. The reviewer identified specialization in Lean, not a defect in the paper: expose every admissible $n_0$ in the window-dependent Lean API and thread the printed conditions. Use the logarithmic formula only as a proved internal witness when constructing the periodic hitting set. This preserves every printed statement and adds no main-result hypothesis; no source or frozen-text edit is warranted.)
- note on `symbol \mathcal T_{x,\xi}`: symbol table corrected: def "For every $1\le i<M$ and $n\in W_{e_i}$, record all $t\in[1,2]$ for which $x+tq^n\in\Gamma_{b_{e_i}^*}$. Combine these lists, add $1$ and $2$, and retain the distinct values in increasing order. Let $\mathcal T_{x,\xi}$ consist of these values together with one midpoint between each consecutive pair." (The recorded definition leaves the boundary scales unspecified. The paper uses crossings of the child-subtree finest lattice, includes both endpoints, and adds midpoints; the representatives cannot depend on unrevealed table entries.)
- note on `symbol A`: symbol table corrected: type "set" (The introductory pattern $A$ need not be measurable. The later periodic-density notation uses the same letter for a measurable, $1$-periodic set; the recorded definition recognizes this distinction, but the recorded type does not.)
- note on `symbol b'`: symbol table corrected: type "grid index or preceding window endpoint", def "In grid nesting, $b'$ is an integer satisfying $b'\ge b$; in the stability condition for a noninitial window $W_e$, $b'$ is the endpoint of its immediate predecessor." (The recorded definition covers only the predecessor endpoint. The paper also uses the same notation for an arbitrary finer grid index; these are context-dependent uses rather than a change to the grid construction.)
- note on `symbol E_{q,\eta}`: symbol table corrected: def "$E_{q,\eta}=[0,1]\setminus C$." (The recorded entry gives the required properties but omits the explicit complement definition used in the proof. The construction supplies the previously asserted existential witness, rather than changing its meaning.)
- note on `symbol S_e`: symbol table corrected: type "random selector table", def "For each edge $e=(P,i)$ with $1\le i<M$, $S_e:\{0,\ldots,N_{b_e}-1\}\longrightarrow\{0,1\}$ is a table of independent fair bits. Child $M$ is the default child and has no selector table. All entries of all selector tables $S_e$ and terminal tables $T_L$ are mutually independent." (The recorded domain is correct, but attachment to an edge alone omits the defining random-table law. The finite-table setting already records the exposure and conditional laws.)
- note on `symbol T_L`: symbol table corrected: type "random terminal table", def "For each leaf $L$, let $b(L)$ be the window endpoint of its incoming edge, and let $T_L:\{0,\ldots,N_{b(L)}-1\}\longrightarrow\{0,1\}$ be a table of independent Bernoulli-$p$ bits. All entries of all selector tables $S_e$ and terminal tables $T_L$ are mutually independent." (The recorded membership-table label omits the paper's defining random-table law. The domain is correct; the definition must specify independent Bernoulli-$p$ entries and their mutual independence with the other tables.)
- note on `symbol W_e`: symbol table corrected: def "$W_e=[a_e,b_e]\cap\N$ is assigned to each edge in preorder, leaving exactly $g$ unused indices between consecutive windows. An edge leaving a vertex of height $h$ receives a window of length $r_h$, where $r_1=r_0$, $\sigma_1=Mr_1+(M-1)g$, and, for $2\le h\le d$, $r_h=\max\{r_0,g+\sigma_{h-1}\}$ and $\sigma_h=M(r_h+g+\sigma_{h-1})+(M-1)g$. The first window starts at a chosen $n_0\ge1$ satisfying $2q^{n_0}\le1/4$, and subsequent windows have the prescribed lengths and gaps." (The recorded interval notation is correct but omits the prescribed lengths, gaps, and starting-index condition that distinguish these windows from arbitrary preorder intervals. The later subtree-endpoint definition does not redefine them.)

### V1 lint warnings

- prop:periodic: prop:periodic references \ref{lem:conditional-scales} (lem:conditional-scales) but `depends_on` lacks ass:conditional-scales-parameters, ass:conditional-scales-default-atom, ass:conditional-scales-height; V1.5 must confirm whether the paper assumes it or merely mentions it
- lem:independent-tests: lem:independent-tests references \ref{lem:separation} (lem:separation) but `depends_on` lacks ass:separation-parameters; V1.5 must confirm whether the paper assumes it or merely mentions it
- lem:conditional-scales: lem:conditional-scales references \ref{lem:window-span} (lem:window-span) but `depends_on` lacks ass:window-span-height; V1.5 must confirm whether the paper assumes it or merely mentions it
- lem:conditional-scales: lem:conditional-scales references \ref{lem:routing} (lem:routing) but `depends_on` lacks ass:routing-default-atom; V1.5 must confirm whether the paper assumes it or merely mentions it
- lem:conditional-scales: lem:conditional-scales references \ref{lem:independent-tests} (lem:independent-tests) but `depends_on` lacks ass:independent-tests-default-atom; V1.5 must confirm whether the paper assumes it or merely mentions it
- prop:periodic: the proof of prop:periodic cites [Tom2015, Lemma 0.2] (prop:periodic/proof/3/2); the transcription reads the citation as a method or argument borrowed from the cited work, not its result and made no cited node for it (The proof credits open-neighborhood repair to Tom, then carries out the enlargement, exceptional-center estimate, outer-regularity repair, and hitting argument itself.). paper: "…for null sequences is explicit in Tom~\cite[Lemma~0.2]{Tom2015}; see also Chleb\'ik~\cite[Section~3,…"
- prop:periodic: the proof of prop:periodic cites [Chlebik2015, Proposition 1] (prop:periodic/proof/3/2); the transcription reads the citation as a comparison or a pointer to the cited work and made no cited node for it (This is a see-also reference for the open-neighborhood repair that the paper implements in full in the following paragraphs.). paper: "…see also Chleb\'ik~\cite[Section~3, final remark; Proposition~1(vi), (viii)]{Chlebik2015}. We implement it with open…"

## Lean evidence

- build of the run barrel: **ok**
- source scan (sorry / admit / axiom): clean

| declaration | axioms |
| --- | --- |
| `Papers.OaiGeometricErdosSimilarity.exists_compact_avoiding_geometric_affine_copies` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiGeometricErdosSimilarity.exists_open_periodic_hitting_set` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiGeometricErdosSimilarity.blockEndpoint_sub_windowStart_le` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiGeometricErdosSimilarity.stableSet_measurable_density_and_keys` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiGeometricErdosSimilarity.gridKey_injective_on_translated_window` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiGeometricErdosSimilarity.expected_periodicDensity_randomSet_eq` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiGeometricErdosSimilarity.localTest_imp_mem_randomSet` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiGeometricErdosSimilarity.condPr_forall_localTest_false_eq` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiGeometricErdosSimilarity.condPr_exists_scale_miss_le` | clean — `propext`, `Classical.choice`, `Quot.sound` |

## Inputs

| artifact | status |
| --- | --- |
| `discovery/v1_scope.json` | present (9 environment(s)) |
| `discovery/v1_5_review.json` | present (verdict PASS) |
| `formalization/crosswalk_full.json` | present (243 object(s)) |
| `graph.json` | present (246 node(s)) |
| Lean evidence | collected (build ok, 0 scan issue(s), 229 declaration(s)) |

## Annotated paper

Annotated paper: `annotated/main.tex` (31 annotation(s), 0 unlocated; index `annotated/ANNOTATIONS.md`); PDF: `annotated/main.pdf`
